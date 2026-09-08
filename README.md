# HodgeConjecture

Work in progress on stating the Hodge conjecture in Lean for the
[Formal Conjectures repository](https://github.com/google-deepmind/formal-conjectures).

For now this is an autoformalisation!

## Source layout

- `HodgeConjecture/Definitions`: definitions feeding the conjecture statement;
- `HodgeConjecture/Lemmas`: results needed to construct those definitions;
- `HodgeConjecture/Other`: all remaining definitions and results, including Borel–Moore homology,
  local fundamental classes, orientations, cap products, and comparison theorems.

Import `HodgeConjecture.Statement` for the statement and its dependencies. It has no dependency
on `Other`. The full-library entry point `HodgeConjecture.lean` aggregates all modules; the three
source layers also have their own umbrella modules.

Run `python3 scripts/check_import_layers.py` to check that every definition/lemma module is in
the statement's transitive import closure and that no `Other` module enters that closure.
This is a file-level check; placing individual declarations still requires mathematical judgment.

## Borel–Moore construction

`HodgeConjecture/Other/AlgebraicGeometry/SheafBorelMoore.lean` constructs the ambient comparison
`H_i^BM(Z ⊂ X; ℚ) ≃ H_Z^(2d-i)(X; ℚ)` by transporting an explicitly supplied derived orientation
isomorphism through an explicitly supplied support functor and its shift compatibility. The
cycle degree specialization is proved arithmetically. The general equivalence is derived at
the object level, rather than supplied as a homology-level Alexander-duality field.

The full geometric construction remains conditional on a dualizing complex with the normalized
complex orientation, the derived support functor, its comparison with the restriction cone,
the compactification/sheaf and costalk comparisons, and the local Thom-cap compatibility and
detection theorem. General global fundamental classes additionally require the puncture and
propagation inputs recorded in `CycleComponentGlobalFundamentalClass`; Chow descent requires
principal-divisor vanishing. The maximal-codimension component and its normalized point
comparison are constructed. No intrinsic compactification-independence theorem is claimed.

The closed-support Ext construction and compact-support colimit supplied by upstream are retained
in `Other`; comparison with the integer-graded restriction-cone model remains separate.

Verification: `lake build HodgeConjecture`, `python3 scripts/check_import_layers.py`,
`lake env lean scripts/AuditBorelMoore.lean`, and `git diff --check`. The Lean audit prints
axioms for the principal constructions and checks all declarations in the Borel–Moore tranche
against `propext`, `Classical.choice`, and `Quot.sound`.
