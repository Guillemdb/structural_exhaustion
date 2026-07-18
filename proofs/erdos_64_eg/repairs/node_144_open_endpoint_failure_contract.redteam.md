# Red-team audit: node [144] open endpoint failure

## Verdict

The local branch is fully normalized and activated.  Its global blocker-ledger
insertion remains correctly open because selected-slot provenance is absent.

## Checks

1. **No compatibility leakage.**  The branch never constructs
   `FanCompatible`, a Type-B profile, or a fan assignment.
2. **Exact four-case split.**  The classifier tests only whether the witnessed
   endpoint is the first literal shoulder; the negative case is converted to
   the second shoulder using the proved two-element shoulder theorem.
3. **Literal blocker carrier.**  `SharedCarrier` uses the identical ambient
   vertex as the foreign port's endpoint/buffer and as a member of the
   suppressed port's shoulder list.  It is not an abstract label.
4. **Suppression is graph-owned.**  Every field of
   `OpenPortSuppression.Setup` is derived from the raw port, deletion
   criticality, and the exact open proof.  The added shoulder chord is absent
   by the definition of `portType = open`.
5. **Critical chord use is proved.**  `ActivatedFailure.critical` comes from
   `criticalCycleFromMinimality`; its type includes the proof that the selected
   target cycle uses the one added chord.  Its `response` is definitionally the
   extracted predecessor path, with simplicity, endpoint avoidance, and exact
   accepted successor length.
6. **No ambient enumeration.**  Classification performs one local equality
   test.  Suppression transforms one proof-selected target cycle.  It does not
   enumerate graphs, cycles, paths, contexts, or response vectors.
7. **Root/after-edge provenance persists.**  Separate adapters retain the
   complete detailed high-separator objects, including the third or
   predecessor port.

## Rejected stronger route

The raw high-separator ports are incident ports, but the source does not prove
that they are the ports chosen by the excess selector.  Consequently it does
not provide `SurplusPortActivation.Slot` values, active-demand records, or
identities with the selected slots.  Treating the literal carrier as an entry
of `SurplusPairBlocker` without those identities would change the quantified
family and is invalid.

`ActivationFrontier` therefore retains the complete local result.
`SelectedSlotEntry` states exactly the missing consumer data: two selected
slots with the correct centers and endpoint identities.  Once this entry is
proved, the existing active-demand blocker scan is the appropriate downstream
consumer.

## Remaining residual

Prove selected-slot provenance for the two recovered raw ports, or route this
separator leaf to an earlier source that already carries those slots.  No
target-response equivalence beyond the exact single-port suppression response
is available or required at this boundary.
