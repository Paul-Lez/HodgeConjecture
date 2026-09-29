# Oka compatibility port

The Lean files in this directory are adapted from
[`chrisflav/oka`](https://github.com/chrisflav/oka) at commit
`441d02e06e68ba6ebeddd7e0e7240c766c3c3c09` for Mathlib `v4.33.1`.

`Other/Oka.lean` is the module boundary for the port. Its two root imports cover every Lean file in
this directory. The port imports only Mathlib and other modules below `Other.Oka`; project-specific
Hodge and Lefschetz code therefore remains downstream.

Run `python3 scripts/check_oka_provenance.py` to check the revision markers, import boundary, and
umbrella coverage.
