/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.GlobalSections
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Topology.Sheaves.Flasque

/-!
# Global sections of bounded-below exact flasque complexes

An exact bounded-below cochain complex of flasque sheaves remains exact after taking global
sections.  The proof is elementary: starting at the lower bound, the cycle sheaves are flasque
by induction through their short exact sequences.  Global sections are then exact on each of
those sequences.

This is the acyclic-complex lemma needed to compare a bounded-below flasque resolution with a
termwise-injective replacement.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
