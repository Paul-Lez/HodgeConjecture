# Statement of the Hodge Conjecture

This repo is work in progress towards stating the Hodge conjecture in Lean for the
[Formal Conjectures project](https://github.com/google-deepmind/formal-conjectures).

The basis for this is a 50k lines of code autoformalisation due to Codex, of which 12k lines are
transitively used in the statement. The code is being cleaned up by
[Paul Lezeau](https://sites.google.com/view/paul-lezeau/home/),
[Yaël Dillies](https://www.su.se/english/profiles/y/yadi8568),
[Roktim Mascharak](https://roktimmascharak.github.io/) and
[Jack McCarthy](https://jackmccarthy.org/) during the Formal Conjectures workshop hosted
by Imperial College London 7-11 September 2026 thanks to a generous donation from Google DeepMind.

The short-term goal of this project is to be integrated to the Formal Conjectures repository.
The medium-term goal is for all the prerequisites to the conjecture to be upstreamed to
[Mathlib](https://github.com/leanprover-community/mathlib4).
The long-term goal is to have either a proof or a disproof of the Hodge conjecture in Mathlib.

The statement of the conjecture is in `HodgeConjecture/Statement.lean`.
The remaining content of the project is sorted into four folders:
- `HodgeConjecture/Mathlib`: Content that is on track to be upstreamed to Mathlib;
- `HodgeConjecture/Definitions`: Definitions used in the statement of the conjecture;
- `HodgeConjecture/Lemmas`: Supporting results needed by those definitions;
- `HodgeConjecture/Other`: Results that aren't needed to state the conjecture but whose truth
  increases likelihood that the conjecture is correctly formalised.

Import `HodgeConjecture.Statement` for the statement and its dependencies. It has no dependency
on `Other`. The full-library entry point `HodgeConjecture.lean` aggregates all modules.

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
