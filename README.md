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
Helpers outside that closure, including prospective Mathlib material, live in `Other`;
the check also rejects support-only helpers left in the local `Mathlib` directory.
It also checks that the full-library umbrella reaches every local module.
This is a file-level check; placing individual declarations still requires mathematical judgment.

## Borel–Moore construction

The constructed smooth-ambient route is in
`HodgeConjecture/Other/AlgebraicGeometry/ComplexSheafBorelMoore.lean`. It applies actual derived
closed-support sections to the actual relative singular-chain sheaf. The constructed complex
orientation identifies that derived sheaf with `ℚ_X[2d]`, yielding
`H_i^BM(Z ⊂ X; ℚ) ≃ H_Z^(2d-i)(X; ℚ)`, including singular closed supports. Neither the support
functor, orientation, nor a homology-level Alexander-duality equivalence is an input to this
route. The cycle-degree identity is proved, and the comparison to the repository's ordinary
rational cohomology includes the actual support-forgetting square and its cone signs.

`CycleComponentSheafClass.lean` constructs arbitrary-codimension component classes. Exact
normal-chart coclasses glue on the smooth locus. A finite smooth filtration proves the required
vanishing along the singular boundary, so the actual localization map has a proved inverse
giving the unique supported extension. The resulting class also determines a fundamental class
in the actual ambient sheaf Borel–Moore group through the constructed orientation duality.

`SheafCycleClass.lean` provides `sheafCycleClassOnCycles V p` on integral codimension-`p` cycles
and `rationalSheafCycleClassOnCycles V p` on their rational scalar extension. These functions
take only the dimensioned smooth projective complex variety and the codimension; no
fundamental-class, purity, extension, or duality data are supplied. They are noncomputable
Lean functions, with proved evaluation formulas for arbitrary finite integer and rational
linear combinations.

`CycleComponentPointClassNormalization.lean` proves that the general construction sends a
point component to the existing exactly normalized relative point coclass, transported by the
actual relative-to-injective comparison and positive inclusion into ordinary cohomology.
The proof uses local normalization and uniqueness of the supported extension; the general
map has no special point branch. Exact integer and rational multiplicity formulas follow.
`CycleComponentPointOrdinarySign.lean` further displays the actual positive raw-cochain
inclusion and proves the comparison with the older ordinary point-cycle API: the new integral
and rational point-cycle maps equal the **negative** of the corresponding legacy maps, whose
support-cone comparison has the opposite sign. Closed-point corollaries derive the codimension
from geometry and construct the needed analytic point. The old definitions have not been
changed or used to rescale the new fundamental classes.

These maps are on **cycles**, not Chow groups: rational-equivalence invariance still requires
principal-divisor vanishing. They are not yet substituted into `HodgeConjecture.Statement`.
The earlier conditional interfaces in `SheafBorelMoore.lean`, `CycleComponentGlobalFundamentalClass`,
and the compactification-based route remain available, but their additional data are not
arguments to the new cycle maps. No full dualizing universal property, six-functor formalism,
intrinsic compactification independence, or identification with the compactification-relative
Borel–Moore model is claimed.

The closed-support Ext construction and compact-support colimit supplied by upstream are retained
in `Other`; comparison with the integer-graded restriction-cone model remains separate.

Verification: `lake build HodgeConjecture`, `python3 scripts/check_import_layers.py`,
`lake env lean scripts/AuditBorelMoore.lean`, and `git diff --check`. The Lean audit prints
axioms for the principal constructions and checks all declarations in the Borel–Moore tranche
against `propext`, `Classical.choice`, and `Quot.sound`.
