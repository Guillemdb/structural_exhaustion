# Provision-tagged API resources

The former tactic-wide “static input” lists have been removed. They mixed
proof-author obligations with predecessor state, inferred instances, generic
search results, and generated audit objects.

Every node now exports a `Core.NodeAutomationContract`. Its references use the
following provenance classes:

- author supplied: `user_definition`, `user_operator`,
  `user_finite_enumeration`, `instance_bridge`, and optional verified
  optimizations;
- inferred or inherited: `typeclass_inferred` and
  `derived_from_predecessor`;
- framework derived: definitional construction, generic search, generic
  theorems, verified computation, policy selection, route generation, and
  audit generation.

Generated diagrams draw separate proof-instance, predecessor, and
framework-derived boxes. Two nodes share an input box only when the complete
ordered provision-tagged list is identical. Consequently each arrow is an
exact projection of a node API contract, while proof authors can still see the
much smaller list they must implement.
