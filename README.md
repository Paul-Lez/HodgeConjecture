# Statement of the Hodge Conjecture

This repository formalizes the statement of the Hodge conjecture in Lean for the
[Formal Conjectures project](https://github.com/google-deepmind/formal-conjectures) and develops
supporting definitions and results.

During the initial stages of this work, autoformalisation tools were used extensively.
The bulk of the work is now directed towards cleaning up the code.
This project was started during the Formal Conjectures workshop hosted
by Imperial College London 7-11 September 2026 thanks to a generous donation from Google DeepMind.

See [full list of contributors](https://github.com/Paul-Lez/HodgeConjecture/graphs/contributors?all=1).

The short-term goal of this project is to be integrated into the Formal Conjectures repository.
The medium-term goal is for all the prerequisites to the conjecture to be upstreamed to
[Mathlib](https://github.com/leanprover-community/mathlib4).
The long-term goal is to have either a proof or a disproof of the Hodge conjecture in Mathlib.

The statement of the conjecture is in `HodgeConjecture/Statement.lean`.
The remaining content of the project is sorted into four folders:

- `HodgeConjecture/Mathlib`: Content that is on track to be upstreamed to Mathlib;
- `HodgeConjecture/Definitions`: Definitions used in the statement of the conjecture;
- `HodgeConjecture/Lemmas`: Supporting results needed by those definitions. If these aren't used in `Lemmas` then they should go in `Other`. This folder can also contain definitions that are only used in *proofs* of theorems that are needed to state the conjecture;
- `Other`: Proofs and supporting results that aren't needed to state the conjecture.

> [!WARNING]
> This formalisation is still a work in progress, and is still in the process of being reviewed and improved.

WIP formalisation guide: <https://paul-lez.github.io/HodgeConjecture/>.

## Lefschetz (1, 1) development

`HodgeConjecture/LefschetzOneOne.lean` contains the canonical rational Lefschetz `(1, 1)`
proposition, and `Other/AlgebraicGeometry/LefschetzOneOneStatement.lean` contains the stronger
explicit-cycle proposition. Their unconditional proofs are in
`Other/AlgebraicGeometry/LefschetzOneOneProof.lean`. The proof combines the holomorphic
exponential sequence, integral denominator clearing, the divisor–Chern comparison, and proper
GAGA for line bundles. It proves the rational codimension-one result, not the stronger integral
Picard/Chern-class formulation.

The adapted Oka dependency is isolated in
[PR230](https://github.com/Paul-Lez/HodgeConjecture/pull/230). The completed proper-GAGA step and
final theorem are in [PR228](https://github.com/Paul-Lez/HodgeConjecture/pull/228), stacked on
PR230 and the Lefschetz reduction in
[PR9](https://github.com/Paul-Lez/HodgeConjecture/pull/9).
See [the Lefschetz handoff](docs/LEFSCHETZ_HANDOFF.md) for the status, file map and
verification commands.
