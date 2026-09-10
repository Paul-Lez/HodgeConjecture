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
- `Other`: Results that aren't needed to state the conjecture but may be useful as sanity checks.

WIP formalisation guide: <https://paul-lez.github.io/HodgeConjecture/>.

## Lefschetz (1, 1) development

`Other/AlgebraicGeometry/LefschetzOneOne.lean` states the rational Lefschetz `(1, 1)` theorem
and proves it assuming `HodgeConjecture`. The unconditional proof is in progress: the holomorphic
exponential sequence, its connecting map, the vanishing of Hodge classes in `H²(𝒪)`, the
resulting unit-sheaf extensions and their invertible holomorphic section sheaves, and the
analytification functor on sheaves of modules are constructed in the `Holomorphic*` and
`Analytification*` files of `Other/AlgebraicGeometry`.
`Other/AlgebraicGeometry/LefschetzOneOneReduction.lean` states the remaining obligations
(integral denominator clearing, projective GAGA for line bundles, and the divisor/cycle-class
comparison) as explicit propositions and proves that they imply the theorem;
`Other/AlgebraicGeometry/IntegralDenominatorClearing.lean` reduces denominator clearing to finite
generation of `H²(X^an, ℤ)` through the integral singular comparison, and
`Other/AlgebraicGeometry/ProjectiveFiniteHomology.lean` proves that finiteness (compact manifolds are
neighbourhood retracts of Euclidean spaces), so only the line-bundle GAGA and divisor/cycle-class
obligations remain.
See [the Lefschetz handoff](docs/LEFSCHETZ_HANDOFF.md) for the status, file map and
verification commands.
