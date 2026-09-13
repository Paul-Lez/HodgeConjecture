/-
Copyright 2026 Paul Lezeau and The Formal Conjectures Authors.

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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Subdivision.AffineSmallPrism

/-!
This module is ported from Paul Lezeau's corresponding file in
`sphere-six-complex` pull request #49, under the Apache-2.0 license.

# Iterated affine subdivision on singular chains

This file packages finite iterates of geometric affine subdivision on full and cover-small
singular chains.  Every iterate is chain homotopic to the identity, and the small/full iterates
commute with the canonical inclusion.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory

namespace AlgebraicTopology.Singular

/-- Finite iteration of affine subdivision on all integral singular chains. -/
public noncomputable def affineSingularSubdivisionIterate (X : TopCat.{0}) :
    ℕ → ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ) ⟶
      (TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ))
  | 0 => 𝟙 _
  | m + 1 => affineSingularSubdivisionIterate X m ≫
      affineSingularSubdivisionChainMap X

@[simp]
public theorem affineSingularSubdivisionIterate_zero (X : TopCat.{0}) :
    affineSingularSubdivisionIterate X 0 = 𝟙 _ :=
  rfl

public theorem affineSingularSubdivisionIterate_succ
    (X : TopCat.{0}) (m : ℕ) :
    affineSingularSubdivisionIterate X (m + 1) =
      affineSingularSubdivisionIterate X m ≫
        affineSingularSubdivisionChainMap X :=
  rfl

/-- Every finite affine-subdivision iterate is chain homotopic to the identity. -/
public noncomputable def affineSingularSubdivisionIterateHomotopy
    (X : TopCat.{0}) : ∀ m : ℕ,
    Homotopy (affineSingularSubdivisionIterate X m)
      (𝟙 ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)))
  | 0 => Homotopy.refl _
  | m + 1 => by
      simpa [affineSingularSubdivisionIterate_succ] using
        (affineSingularSubdivisionIterateHomotopy X m).comp
          (affineSingularSubdivisionHomotopy X)

section Small

variable {iota : Type} (X : TopCat) (U : iota → Set X)

/-- Finite iteration of affine subdivision on cover-small chains. -/
public noncomputable def coverSmallAffineSubdivisionIterate :
    ℕ → (CoverSmallIntegralSingularChainComplex X U ⟶
      CoverSmallIntegralSingularChainComplex X U)
  | 0 => 𝟙 _
  | m + 1 => coverSmallAffineSubdivisionIterate m ≫
      coverSmallAffineSubdivisionChainMap X U

@[simp]
public theorem coverSmallAffineSubdivisionIterate_zero :
    coverSmallAffineSubdivisionIterate X U 0 = 𝟙 _ :=
  rfl

public theorem coverSmallAffineSubdivisionIterate_succ (m : ℕ) :
    coverSmallAffineSubdivisionIterate X U (m + 1) =
      coverSmallAffineSubdivisionIterate X U m ≫
        coverSmallAffineSubdivisionChainMap X U :=
  rfl

/-- Every cover-small affine-subdivision iterate is chain homotopic to the identity. -/
public noncomputable def coverSmallAffineSubdivisionIterateHomotopy :
    ∀ m : ℕ, Homotopy (coverSmallAffineSubdivisionIterate X U m)
      (𝟙 (CoverSmallIntegralSingularChainComplex X U))
  | 0 => Homotopy.refl _
  | m + 1 => by
      simpa [coverSmallAffineSubdivisionIterate_succ] using
        (coverSmallAffineSubdivisionIterateHomotopy m).comp
          (coverSmallAffineSubdivisionHomotopy X U)

/-- Small and full affine-subdivision iterates commute with the small-chain inclusion. -/
public theorem coverSmallAffineSubdivisionIterate_comp_inclusion : ∀ m : ℕ,
    coverSmallAffineSubdivisionIterate X U m ≫
        coverSmallIntegralSingularChainInclusion X U =
      coverSmallIntegralSingularChainInclusion X U ≫
        affineSingularSubdivisionIterate X m
  | 0 => by
      change (SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)) =
        SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
          (AddCommGrpCat.of ℤ) ≫ 𝟙 _
      simp
  | m + 1 => by
      let I := SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι
        (AddCommGrpCat.of ℤ)
      have hm := coverSmallAffineSubdivisionIterate_comp_inclusion m
      change coverSmallAffineSubdivisionIterate X U m ≫ I =
        I ≫ affineSingularSubdivisionIterate X m at hm
      have hA := coverSmallAffineSubdivisionChainMap_comp_inclusion X U
      change coverSmallAffineSubdivisionChainMap X U ≫ I =
        I ≫ affineSingularSubdivisionChainMap X at hA
      rw [coverSmallAffineSubdivisionIterate_succ,
        affineSingularSubdivisionIterate_succ]
      change (coverSmallAffineSubdivisionIterate X U m ≫
          coverSmallAffineSubdivisionChainMap X U) ≫ I =
        I ≫ (affineSingularSubdivisionIterate X m ≫
          affineSingularSubdivisionChainMap X)
      rw [Category.assoc, hA, ← Category.assoc, hm, Category.assoc]

end Small

end AlgebraicTopology.Singular
