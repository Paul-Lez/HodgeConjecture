# Oka compatibility port

The Lean files in this directory are adapted from
[`chrisflav/oka`](https://github.com/chrisflav/oka) at commit
`441d02e06e68ba6ebeddd7e0e7240c766c3c3c09` for Mathlib `v4.33.1`.

`Other/Oka.lean` is the module boundary for the port. Its two root imports cover every Lean file in
this directory. The port imports only Mathlib and other modules below `Other.Oka`; project-specific
Hodge and Lefschetz code therefore remains downstream.

This is a compatibility port, not a byte-for-byte mirror. `FiniteStalk.lean` contains the
finite-stalk portion split from upstream's `ModulesStalkNakayama.lean`, and `lakefile.toml` sets
`maxSynthPendingDepth = 3` globally for the port's elaboration requirements.

Run `python3 scripts/check_oka_provenance.py` to check the revision markers, import boundary, and
umbrella coverage. The checker enforces those repository invariants; it does not compare the
ported source text with the upstream repository.
