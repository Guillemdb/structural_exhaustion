import { useState } from "react";

import type {
  CapabilityConcept,
  CapabilityRequirement,
  NodeRecord,
  ProvisionedRef,
  RouteRecord,
  TacticRecord,
  TransitionRecord,
} from "../types";
import { MathFormula } from "./MathFormula";
import { RouteList } from "./RouteList";

type TabName = "overview" | "contract" | "formal";

function RefList({ values, empty = "None" }: { values: ProvisionedRef[]; empty?: string }) {
  if (!values.length) return <p className="empty-copy">{empty}</p>;
  return (
    <ul className="ref-list">
      {values.map((value) => (
        <li key={`${value.provision}:${value.ref}`}>
          <code>{value.ref}</code>
          <span className="provision-badge">{value.provision.replaceAll("_", " ")}</span>
        </li>
      ))}
    </ul>
  );
}

function ContractSection({ title, values }: { title: string; values: ProvisionedRef[] }) {
  return (
    <section className="inspector-section">
      <h4>{title}</h4>
      <RefList values={values} />
    </section>
  );
}

function CapabilityDefinitions({
  values,
  concepts,
  reusedConceptIds = new Set<string>(),
}: {
  values: CapabilityRequirement[];
  concepts: CapabilityConcept[];
  reusedConceptIds?: ReadonlySet<string>;
}) {
  if (!values.length) return <p className="empty-copy">None</p>;
  const conceptsById = new Map(concepts.map((concept) => [concept.conceptId, concept]));

  return (
    <div className="capability-definition-list">
      {values.map((value) => {
        const concept = conceptsById.get(value.conceptId);
        if (!concept) {
          return (
            <div className="capability-definition capability-definition--unresolved" key={value.conceptId}>
              <code>{value.ref}</code>
              <span className="provision-badge">{value.provision.replaceAll("_", " ")}</span>
            </div>
          );
        }
        const conceptAnchor = `capability-concept-${concept.conceptId.replaceAll(/[^a-zA-Z0-9_-]/g, "-")}`;
        if (reusedConceptIds.has(concept.conceptId)) {
          return (
            <div className="capability-definition capability-definition--reused" key={concept.conceptId}>
              <span className="capability-definition__summary">
                <strong>{concept.presentation.label}</strong>
                <code>{concept.formalDeclaration.name}</code>
              </span>
              <span className="provision-badge">{value.provision.replaceAll("_", " ")}</span>
              <a href={`#${conceptAnchor}`}>Shared with base capability</a>
            </div>
          );
        }
        return (
          <details className="capability-definition" id={conceptAnchor} key={concept.conceptId}>
            <summary>
              <span className="capability-definition__summary">
                <strong>{concept.presentation.label}</strong>
                <code>{concept.formalDeclaration.name}</code>
              </span>
              <span className="provision-badge">{value.provision.replaceAll("_", " ")}</span>
            </summary>
            <div className="capability-definition__body">
              <section>
                <h5>Mathematical definition</h5>
                <MathFormula
                  value={concept.presentation.mathematicalDefinition}
                  label={`Mathematical definition of ${concept.presentation.label}`}
                />
              </section>
              <section>
                <h5>In plain words</h5>
                <p>{concept.presentation.plainExplanation}</p>
              </section>
              <section>
                <h5>Lean declaration</h5>
                <dl className="capability-definition__metadata">
                  <div><dt>Exact name</dt><dd><code>{concept.formalDeclaration.name}</code></dd></div>
                  <div><dt>Kind</dt><dd>{concept.formalDeclaration.kind}</dd></div>
                  <div><dt>Provision</dt><dd>{value.provision.replaceAll("_", " ")}</dd></div>
                </dl>
                <pre>{concept.formalDeclaration.type}</pre>
              </section>
            </div>
          </details>
        );
      })}
    </div>
  );
}

function EdgeList({ title, values }: { title: string; values: TransitionRecord[] | NodeRecord["formalContract"]["incomingEdges"] }) {
  return (
    <section className="inspector-section">
      <h4>{title}</h4>
      {values.length ? (
        <ul className="formal-edge-list">
          {values.map((edge) => (
            <li key={edge.edgeId}>
              <code>{edge.edgeId}</code>
              <span>{edge.sourceNode} → {edge.targetNode}</span>
            </li>
          ))}
        </ul>
      ) : (
        <p className="empty-copy">None</p>
      )}
    </section>
  );
}

function NodeInspector({ node }: { node: NodeRecord }) {
  const [tab, setTab] = useState<TabName>("overview");
  const automation = node.automation;
  return (
    <>
      <div className="inspector-heading">
        <span className={`kind-chip kind-chip--${node.nodeKind}`}>{node.nodeKind}</span>
        <h2>{node.presentation.label}</h2>
        <p>{node.presentation.summary}</p>
      </div>
      <div className="inspector-tabs" role="tablist" aria-label="Node information">
        {(["overview", "contract", "formal"] as TabName[]).map((name) => (
          <button
            type="button"
            role="tab"
            aria-selected={tab === name}
            className={tab === name ? "is-active" : ""}
            onClick={() => setTab(name)}
            key={name}
          >
            {name}
          </button>
        ))}
      </div>
      {tab === "overview" ? (
        <div className="inspector-body">
          <dl className="property-list">
            <div><dt>Ordinal</dt><dd>{node.ordinal}</dd></div>
            <div><dt>Execution</dt><dd>{automation.executionClass}</dd></div>
            <div><dt>Predecessor indexed</dt><dd>{node.formalContract.predecessorIndexed ? "Yes" : "No"}</dd></div>
            <div><dt>Generated outputs</dt><dd>{automation.generatedOutputs.length}</dd></div>
            <div><dt>Manual obligations</dt><dd>{automation.manualObligations.length}</dd></div>
          </dl>
          <ContractSection title="Generated outputs" values={automation.generatedOutputs} />
        </div>
      ) : null}
      {tab === "contract" ? (
        <div className="inspector-body">
          <ContractSection title="Author inputs" values={automation.authorInputs} />
          <ContractSection title="Inferred inputs" values={automation.inferredInputs} />
          <ContractSection title="Predecessor inputs" values={automation.predecessorInputs} />
          <ContractSection title="Framework-derived inputs" values={automation.derivedInputs} />
          <ContractSection title="Framework theorems" values={automation.frameworkTheorems} />
          <ContractSection title="Generated outputs" values={automation.generatedOutputs} />
          <section className="inspector-section">
            <h4>Manual obligations</h4>
            {automation.manualObligations.length ? (
              <ul>{automation.manualObligations.map((item) => <li key={item}>{item}</li>)}</ul>
            ) : <p className="empty-copy">None</p>}
          </section>
        </div>
      ) : null}
      {tab === "formal" ? (
        <div className="inspector-body">
          <section className="inspector-section">
            <h4>Constructor</h4>
            <pre>{node.constructor}</pre>
          </section>
          <section className="inspector-section">
            <h4>Source</h4>
            <code>{node.sourceFile}</code>
          </section>
          <EdgeList title="Incoming edges" values={node.formalContract.incomingEdges} />
          <EdgeList title="Outgoing edges" values={node.formalContract.outgoingEdges} />
        </div>
      ) : null}
    </>
  );
}

function EdgeInspector({ edge }: { edge: TransitionRecord }) {
  return (
    <>
      <div className="inspector-heading">
        <span className="kind-chip kind-chip--edge">typed edge</span>
        <h2>{edge.edgeId}</h2>
        <p>{edge.sourceNode} → {edge.targetNode}</p>
      </div>
      <div className="inspector-body">
        <dl className="property-list">
          <div><dt>Ordinal</dt><dd>{edge.ordinal}</dd></div>
          <div><dt>Provision</dt><dd>{edge.provision.replaceAll("_", " ")}</dd></div>
        </dl>
        <section className="inspector-section">
          <h4>Constructor</h4>
          <pre>{edge.constructor}</pre>
        </section>
        <section className="inspector-section">
          <h4>Lean type</h4>
          <pre>{edge.constructorType}</pre>
        </section>
      </div>
    </>
  );
}

function TacticInspector({
  tactic,
  inbound,
  outbound,
}: {
  tactic: TacticRecord;
  inbound: RouteRecord[];
  outbound: RouteRecord[];
}) {
  const describedConceptIds = new Set(
    tactic.capability.requiredDefinitions.map((requirement) => requirement.conceptId),
  );
  const capabilityProfiles = tactic.capabilityProfiles.map((profile) => {
    const reusedConceptIds = new Set(
      profile.requiredDefinitions
        .map((requirement) => requirement.conceptId)
        .filter((conceptId) => describedConceptIds.has(conceptId)),
    );
    profile.requiredDefinitions.forEach((requirement) => {
      describedConceptIds.add(requirement.conceptId);
    });
    return { profile, reusedConceptIds };
  });

  return (
    <>
      <div className="inspector-heading">
        <span className="kind-chip">{tactic.apiVersion}</span>
        <h2>{tactic.title}</h2>
        <p>{tactic.namespace}</p>
      </div>
      <div className="inspector-body">
        <dl className="property-list">
          <div><dt>Nodes</dt><dd>{tactic.nodes.length}</dd></div>
          <div><dt>Transitions</dt><dd>{tactic.transitions.length}</dd></div>
          <div><dt>Terminals</dt><dd>{tactic.terminals.length}</dd></div>
          <div><dt>Residual kinds</dt><dd>{tactic.residualKinds.length}</dd></div>
        </dl>
        <section className="inspector-section">
          <h4>Required definitions</h4>
          <CapabilityDefinitions
            values={tactic.capability.requiredDefinitions}
            concepts={tactic.capabilityConcepts}
          />
        </section>
        {capabilityProfiles.length ? (
          <section className="inspector-section">
            <h4>Capability profiles</h4>
            <div className="capability-profile-list">
              {capabilityProfiles.map(({ profile, reusedConceptIds }) => (
                <details className="capability-profile" key={profile.capabilityId}>
                  <summary>
                    <code>{profile.capabilityId}</code>
                    <span>{profile.requiredDefinitions.length} definitions</span>
                  </summary>
                  <div className="capability-profile__body">
                    <CapabilityDefinitions
                      values={profile.requiredDefinitions}
                      concepts={tactic.capabilityConcepts}
                      reusedConceptIds={reusedConceptIds}
                    />
                  </div>
                </details>
              ))}
            </div>
          </section>
        ) : null}
        <ContractSection title="Required instances" values={tactic.capability.requiredInstances} />
        <section className="inspector-section">
          <h4>Semantic residuals</h4>
          <div className="residual-list">
            {tactic.residualKinds.map((residual) => (
              <details key={residual.residualKindId}>
                <summary>{residual.residualKindId}</summary>
                <span>Context: {residual.inheritedContext}</span>
                <pre>{residual.leanType}</pre>
                <ul>
                  {residual.semanticFields.map((field) => (
                    <li key={field.fieldName}>
                      <strong>{field.fieldName}</strong>
                      <code>{field.leanType}</code>
                    </li>
                  ))}
                </ul>
              </details>
            ))}
          </div>
        </section>
        <section className="inspector-section">
          <h4>Registered routes</h4>
          <RouteList inbound={inbound} outbound={outbound} />
        </section>
      </div>
    </>
  );
}

export function Inspector({
  tactic,
  node,
  edge,
  inboundRoutes,
  outboundRoutes,
}: {
  tactic: TacticRecord;
  node?: NodeRecord;
  edge?: TransitionRecord;
  inboundRoutes: RouteRecord[];
  outboundRoutes: RouteRecord[];
}) {
  return (
    <aside className="inspector-panel" aria-label="Framework inspector">
      {node ? <NodeInspector node={node} /> : null}
      {edge ? <EdgeInspector edge={edge} /> : null}
      {!node && !edge ? (
        <TacticInspector tactic={tactic} inbound={inboundRoutes} outbound={outboundRoutes} />
      ) : null}
    </aside>
  );
}
