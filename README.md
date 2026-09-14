# Statement of the Hodge Conjecture

This repo is work in progress towards stating the Hodge conjecture in Lean for the
[Formal Conjectures project](https://github.com/google-deepmind/formal-conjectures).

During the initial stages of this work, autoformalisation tools were used extensively.
The bulk of the work is now directed towards cleaning up the code.
This project was started during the Formal Conjectures workshop hosted
by Imperial College London 7-11 September 2026 thanks to a generous donation from Google DeepMind.

See [full list of contributors](https://github.com/Paul-Lez/HodgeConjecture/graphs/contributors?all=1).

The short-term goal of this project is to be integrated to the Formal Conjectures repository.
The medium-term goal is for all the prerequisites to the conjecture to be upstreamed to
[Mathlib](https://github.com/leanprover-community/mathlib4).
The long-term goal is to have either a proof or a disproof of the Hodge conjecture in Mathlib.

The statement of the conjecture is in `HodgeConjecture/Statement.lean`.
The remaining content of the project is sorted into four folders:

- `HodgeConjecture/Mathlib`: Content that is on track to be upstreamed to Mathlib;
- `HodgeConjecture/Definitions`: Definitions used in the statement of the conjecture;
- `HodgeConjecture/Lemmas`: Supporting results needed by those definitions. If these aren't used in `Lemmas` then they should go in `Other`. This folder can also contain definitions that are only used to in *proofs* of theorems that are needed to state the conjecture;
- `Other`: Results that aren't needed to state the conjecture but may be useful as sanity checks.

> [!WARNING]
> This formalisation is still a work in progress, and is still in the process of being reviewed and improved.

WIP formalisation guide: <https://paul-lez.github.io/HodgeConjecture/>.

Dependency graph of the statement: <https://paul-lez.github.io/HodgeConjecture/blueprint/dep_graph_document.html>.
It is a [leanblueprint](https://github.com/PatrickMassot/leanblueprint) document generated from the
compiled declarations: one node for each definition the statement transitively uses, with the
dependencies extracted from Lean. See [`scripts/BlueprintGraph.lean`](scripts/BlueprintGraph.lean)
for how to regenerate it and [`blueprint/`](blueprint/) for the sources.
