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

public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClass
public import HodgeConjecture.Lemmas.LinearAlgebra.ComplexOrientation
public import HodgeConjecture.Mathlib.Topology.Category.TopPair
public import Mathlib.Analysis.Complex.Basic

/-!
# The standard complex local class

This file identifies `ℂ^p` with an ordered real coordinate space by listing the real and imaginary
part of each complex coordinate consecutively. It transports the explicit standard local cycle to
`H_{2p}(ℂ^p, ℂ^p ∖ {0}; R)`. Thus the complex orientation is constructed from complex coordinates
rather than supplied as data.
-/

open CategoryTheory

@[expose] public noncomputable section

namespace AlgebraicTopology.Singular

variable (R : Type*) [CommRing R]

/-- The orientation-ordered homeomorphism from complex coordinate space to real coordinate space.

This is the coordinate map of `Complex.piBasisOneI`, so it lists the real and imaginary part of
each complex coordinate consecutively; continuity in both directions comes from
`Basis.equivFunL`. -/
def complexRealHomeomorph (p : ℕ) : (Fin p → ℂ) ≃ₜ (Fin (p * 2) → ℝ) :=
  (Complex.piCoordCLE p).toHomeomorph

/-- The isomorphism of punctured pairs induced by ordered real and imaginary coordinates. -/
def standardComplexRealPairIso (p : ℕ) :
    standardPuncturedPair ℂ p ≅ standardPuncturedPair ℝ (p * 2) :=
  TopPair.isoOfSubset (complexRealHomeomorph p) fun _ =>
    not_congr (Complex.piCoordCLE p).map_eq_zero_iff

/-- `H_{2p}(ℂ^p, ℂ^p \ {0}; R) ≅ H_{2p}(ℝ^{2p}, ℝ^{2p} \ {0}; R)`, induced by the coordinate
homeomorphism `ℂ^p ≅ ℝ^{2p}`. -/
def standardComplexRealRelativeHomologyIso (p : ℕ) :
    -- `H_{2p}(ℂ^p, ℂ^p \ {0}; R) ≅ H_{2p}(ℝ^{2p}, ℝ^{2p} \ {0}; R)`.
    RelativeHomology R (standardPuncturedPair ℂ p) (p * 2) ≅
      RelativeHomology R (standardPuncturedPair ℝ (p * 2)) (p * 2) :=
  (relativeHomologyFunctor R (p * 2)).mapIso (standardComplexRealPairIso p)

/-- The generator of `H_{2p}(ℂ^p, ℂ^p \ {0}; R)` transported from the standard local class of
`ℝ^{2p}` through `ℂ^p ≅ ℝ^{2p}`. It fixes the complex orientation. -/
def standardComplexLocalClass (p : ℕ) :
    -- The complex-orientation generator of `H_{2p}(ℂ^p, ℂ^p \ {0}; R)`.
    RelativeHomology R (standardPuncturedPair ℂ p) (2 * p) :=
  (Nat.mul_comm p 2) ▸
    (standardComplexRealRelativeHomologyIso R p).inv.hom (standardLocalClass R (p * 2))

end AlgebraicTopology.Singular
