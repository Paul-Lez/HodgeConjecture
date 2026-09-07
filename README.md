# HodgeConjecture

Work in progress on stating the Hodge conjecture in Lean for the
[Formal Conjectures repository](https://github.com/google-deepmind/formal-conjectures).

For now this is an autoformalisation!

## Source layout

- `HodgeConjecture/Definitions`: constructions and definitions used to state the conjecture;
- `HodgeConjecture/Lemmas`: supporting results needed by those definitions;
- `HodgeConjecture/Other`: the remaining formalisation and prospective Mathlib material.

The public entry point `HodgeConjecture.lean` imports only the conjecture statement. The three
source layers also have `HodgeConjecture.Definitions`, `HodgeConjecture.Lemmas`, and
`HodgeConjecture.Other` umbrella modules.

The statement uses `CycleClassImage` for the intrinsic span of supported-image generators and
the cohomological unit in codimension zero. It has no Chow-group dependency. Import `CycleClass`
for the codimension-zero Chow map and its compatibility with this span. The optional
`SupportedCohomologyImage` module exposes supported-image membership through the existing
Betti comparison.
