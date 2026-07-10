#!/usr/bin/env python3
from __future__ import annotations
import json, sys
from pathlib import Path
from collections import defaultdict, deque

def validate_tactic(t):
    errors=[]; tid=t['tacticId']; nodes=t['nodes']; edges=t['transitions']
    ids=[n['nodeId'] for n in nodes]
    if len(ids)!=len(set(ids)): errors.append(f'{tid}: duplicate node IDs')
    for i,n in enumerate(nodes,1):
        expected=f'{tid}.N{i:02d}'
        if n['nodeNumber']!=i: errors.append(f'{tid}: nodeNumber {n["nodeNumber"]} at array position {i}')
        if n['nodeId']!=expected: errors.append(f'{tid}: expected {expected}, got {n["nodeId"]}')
        if not n['obligation']['contractSchemas']: errors.append(f'{n["nodeId"]}: no contract schema')
    idset=set(ids); edgeids=[]; out=defaultdict(list); inc=defaultdict(list)
    for i,e in enumerate(edges,1):
        edgeids.append(e['transitionId'])
        if e['transitionNumber']!=i: errors.append(f'{tid}: transition numbering gap at {e["transitionId"]}')
        if e['fromNodeId'] not in idset or e['toNodeId'] not in idset: errors.append(f'{e["transitionId"]}: unknown endpoint')
        out[e['fromNodeId']].append(e); inc[e['toNodeId']].append(e)
    if len(edgeids)!=len(set(edgeids)): errors.append(f'{tid}: duplicate transition IDs')
    # Reachability
    q=deque(t['entryNodeIds']); seen=set(q)
    while q:
        u=q.popleft()
        for e in out[u]:
            if e['toNodeId'] not in seen: seen.add(e['toNodeId']); q.append(e['toNodeId'])
    missing=idset-seen
    if missing: errors.append(f'{tid}: unreachable nodes {sorted(missing)}')
    # Sink types
    allowed={'certificate','consumer_handoff','scope_audit','audit_reject'}
    for n in nodes:
        if not out[n['nodeId']] and n['terminalRole'] not in allowed:
            errors.append(f'{n["nodeId"]}: untyped sink ({n["nodeType"]})')
    # Decisions and payload consumers
    for n in nodes:
        if n['nodeType']=='decision':
            declared={b['transitionId'] for b in n.get('branches',[])}
            actual={e['transitionId'] for e in out[n['nodeId']]}
            if declared!=actual: errors.append(f'{n["nodeId"]}: branch list does not equal outgoing transitions')
        if n['nodeType']=='payload_constructor':
            consumers=[]
            frontier=deque([n['nodeId']]); local_seen={n['nodeId']}
            while frontier:
                u=frontier.popleft()
                for e in out[u]:
                    v=e['toNodeId']; target=next(x for x in nodes if x['nodeId']==v)
                    if target['nodeType']=='consumer_handoff': consumers.append(target['consumer']['tacticId'])
                    elif v not in local_seen and target['nodeType'] not in ('certificate','scope_audit','audit_gate'):
                        local_seen.add(v); frontier.append(v)
            declared=[a['consumerTacticId'] for a in n['payload']['alternatives']]
            for ct in declared:
                if ct=='UNRESOLVED': errors.append(f'{n["nodeId"]}: unresolved consumer')
                elif ct not in consumers: errors.append(f'{n["nodeId"]}: declared consumer {ct} not reachable')
    # Cycles require S-Meas somewhere and S-Rest for operational loops.
    if t['cyclePolicy']['hasCycles']:
        for cyc,kind in zip(t['cyclePolicy']['cycles'],t['cyclePolicy']['cycleKinds']):
            contracts={c for n in nodes if n['nodeId'] in set(cyc) for c in n['obligation']['contractSchemas']}
            if kind=='execution_loop' and 'S-Meas' not in contracts: errors.append(f'{tid}: execution loop lacks S-Meas')
            if kind=='execution_loop' and 'S-Rest' not in contracts: errors.append(f'{tid}: execution loop lacks S-Rest')
    return errors

def main(path):
    data=json.loads(Path(path).read_text())
    tactics=data['tactics'] if data.get('artifactType')=='tacticLibrary' else [data]
    errors=[e for t in tactics for e in validate_tactic(t)]
    if errors:
        print('\n'.join(errors)); return 1
    print(f'OK: {len(tactics)} tactics, {sum(len(t["nodes"]) for t in tactics)} numbered nodes, {sum(len(t["transitions"]) for t in tactics)} transitions')
    return 0
if __name__=='__main__':
    raise SystemExit(main(sys.argv[1] if len(sys.argv)>1 else 'data/ct1-ct17.numbered.json'))
