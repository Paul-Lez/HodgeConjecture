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

public import HodgeConjecture.Definitions.AlgebraicTopology.Singular.RelativeCochainCone

/-!
# Relative singular cohomology as a cochain mapping cone

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Singular.RelativeCochainCone`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory Limits
open CategoryTheory.Pretriangulated

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

/-- A degreewise splitting of the dual cochain sequence.  The choice is harmless: the final
cohomology comparison is independent of finite-dimensionality. -/
def relativeDualCochainDegreewiseSplitting (X : TopPair.{u}) (z : ℤ) :
    ((relativeDualCochainShortComplexInt R X).map
      (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) z)).Splitting :=
  (((HomologicalComplex.shortExact_iff_degreewise_shortExact
    (relativeDualCochainShortComplexInt R X)).mp
      (relativeDualCochainShortComplexInt_shortExact R X)) z).splittingOfProjective

/-- The triangle attached to the degreewise split dual cochain sequence is distinguished. -/
lemma relativeDualCochainTriangle_distinguished (X : TopPair.{u}) :
    CochainComplex.trianglehOfDegreewiseSplit
        (relativeDualCochainShortComplexInt R X)
        (relativeDualCochainDegreewiseSplitting R X) ∈ distinguishedTriangles :=
  (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit _).mpr
    ⟨relativeDualCochainShortComplexInt R X,
      relativeDualCochainDegreewiseSplitting R X, ⟨Iso.refl _⟩⟩

/-- The rotated triangle of the dual short exact sequence agrees with the mapping-cone
triangle of singular-cochain restriction. -/
def relativeCochainConeTriangleIso (X : TopPair.{u}) :
    (CochainComplex.trianglehOfDegreewiseSplit
      (relativeDualCochainShortComplexInt R X)
      (relativeDualCochainDegreewiseSplitting R X)).rotate ≅
    CochainComplex.mappingCone.triangleh (relativeCochainRestrictionInt R X) :=
  isoTriangleOfIso₁₂
    (CochainComplex.trianglehOfDegreewiseSplit
      (relativeDualCochainShortComplexInt R X)
      (relativeDualCochainDegreewiseSplitting R X)).rotate
    (CochainComplex.mappingCone.triangleh (relativeCochainRestrictionInt R X))
    ((rotate_distinguished_triangle _).mp
      (relativeDualCochainTriangle_distinguished R X))
    (HomotopyCategory.mappingCone_triangleh_distinguished
      (relativeCochainRestrictionInt R X))
    (Iso.refl _) (Iso.refl _) (by
      change (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map
          (relativeDualCochainShortComplexInt R X).g =
        (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map
          (relativeCochainRestrictionInt R X)
      rw [relativeDualCochainShortComplexInt_g]
      rfl)

/-- The homotopy-category isomorphism from the shifted dual relative cochain complex to the
mapping cone of restriction. -/
def relativeDualShiftIsoCochainCone (X : TopPair.{u}) :
    (shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) (1 : ℤ)).obj
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj
          (relativeDualCochainShortComplexInt R X).X₁) ≅
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone (relativeCochainRestrictionInt R X)) :=
  Pretriangulated.Triangle.π₃.mapIso (relativeCochainConeTriangleIso R X)

/-- Cohomology of the cochain restriction cone in degree `n - 1` is the cohomology in degree
`n` of the integer-indexed dual relative cochain complex. -/
def relativeCochainConeHomologyIsoDualRelativeInt (X : TopPair.{u}) (n : ℕ) :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt R X)).homology
        ((n : ℤ) - 1) ≅
      (relativeDualCochainShortComplexInt R X).X₁.homology (n : ℤ) := by
  let Q := HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)
  let H (z : ℤ) := HomotopyCategory.homologyFunctor
    (ModuleCat.{u} R) (ComplexShape.up ℤ) z
  let C := CochainComplex.mappingCone (relativeCochainRestrictionInt R X)
  let D := (relativeDualCochainShortComplexInt R X).X₁
  have hn : (1 : ℤ) + ((n : ℤ) - 1) = (n : ℤ) := by lia
  exact
    (HomotopyCategory.homologyFunctorFactors
      (ModuleCat.{u} R) (ComplexShape.up ℤ) ((n : ℤ) - 1)).symm.app C ≪≫
    (H ((n : ℤ) - 1)).mapIso (relativeDualShiftIsoCochainCone R X).symm ≪≫
    (((H 0).shiftIso (1 : ℤ) ((n : ℤ) - 1) (n : ℤ) hn).app (Q.obj D)) ≪≫
    (HomotopyCategory.homologyFunctorFactors
      (ModuleCat.{u} R) (ComplexShape.up ℤ) (n : ℤ)).app D

/-- Relative singular cohomology is the degree-`n - 1` cohomology of the mapping cone of
restriction from ambient singular cochains to subspace singular cochains. -/
def relativeCochainConeCohomologyEquiv (X : TopPair.{u}) (n : ℕ) :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt R X)).homology
        ((n : ℤ) - 1) ≃ₗ[R]
      RelativeCohomology R X n :=
  (relativeCochainConeHomologyIsoDualRelativeInt R X n).toLinearEquiv.trans
    (((relativeChainFunctor R).obj X).linearDualCochainComplex.extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl).toLinearEquiv

end AlgebraicTopology.Singular

end

@[expose] public noncomputable section

open CategoryTheory Limits
open CategoryTheory.Pretriangulated

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R]

set_option backward.isDefEq.respectTransparency false in
/-- The cone comparison commutes with the connecting morphism which, in supported
cohomology, forgets support. -/
lemma relativeDualShiftIsoCochainCone_hom_comp_mor₃ (X : TopPair.{u}) :
    (relativeDualShiftIsoCochainCone R X).hom ≫
        (CochainComplex.mappingCone.triangleh
          (relativeCochainRestrictionInt R X)).mor₃ =
      (CochainComplex.trianglehOfDegreewiseSplit
        (relativeDualCochainShortComplexInt R X)
        (relativeDualCochainDegreewiseSplitting R X)).rotate.mor₃ := by
  change (relativeCochainConeTriangleIso R X).hom.hom₃ ≫
      (CochainComplex.mappingCone.triangleh
        (relativeCochainRestrictionInt R X)).mor₃ = _
  rw [← (relativeCochainConeTriangleIso R X).hom.comm₃]
  unfold relativeCochainConeTriangleIso
  rw [Pretriangulated.isoTriangleOfIso₁₂_hom_hom₁]
  simp

end AlgebraicTopology.Singular
