# Phase 0 baseline

No baseline is frozen here yet. A real baseline must come from a named clean
commit after the ordered legacy build and validation commands in section 9 of
`HYPOSTRUCTURE_MIGRATION_GUIDE.md` pass without stale-hash mode.

To capture one, instantiate `manifest.template.json` as `manifest.json`, replace
every `null` with observed data, copy the listed artifacts into this directory,
and record their SHA-256 hashes. Direct node source hashes, `.olean` freshness,
public WebExport declarations, trusted axioms, and per-node work bounds belong
in the manifest as observed lists. Do not fill a missing value from a dirty or
stale generated tree.

Any later refresh requires a decision record identifying the old and new
baseline commits and the reason parity expectations changed.

