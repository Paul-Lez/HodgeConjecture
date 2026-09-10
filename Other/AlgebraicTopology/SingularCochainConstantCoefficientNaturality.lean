/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularCochainCoefficientBaseChange
public import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Constants and rational-to-complex singular cochains

Coefficient extension from `ℚ` to `ℂ` commutes with the augmentation which
includes locally constant functions into singular zero-cochains.  We package
the resulting square first for presheaves and then for sheaf complexes.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicTopology.Singular

/-- Coefficient extension on the constant coefficient presheaves. -/
def qToCConstantCoefficientPresheaf (X : TopCat) :
    constantCoefficientPresheaf ℚ X ⟶ constantCoefficientPresheaf ℂ X where
  app _ := AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom
  naturality _ _ _ := rfl

local instance openComplexChainsRatModule (X : TopCat)
    (U : (Opens X)ᵒᵖ) (n : ℕ) : Module ℚ (OpenChains ℂ X U n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

variable (X : TopCat)

/-- Extending the coefficients of a rational zero-chain commutes with its
augmentation. -/
lemma openZeroAugmentation_qToC_apply (X : TopCat) (U : (Opens X)ᵒᵖ)
    (c : OpenChains ℚ X U 0) :
    (openZeroAugmentation ℂ X U).hom
        (fieldToFieldOpenChainGroup ℚ ℂ X U 0 c) =
      algebraMap ℚ ℂ ((openZeroAugmentation ℚ X U).hom c) := by
  let f : OpenChains ℚ X U 0 ⟶ ModuleCat.of ℚ ℂ :=
    ModuleCat.ofHom
      ((openZeroAugmentation ℂ X U).hom.restrictScalars ℚ |>.comp
        (fieldToFieldOpenChainGroup ℚ ℂ X U 0))
  let g : OpenChains ℚ X U 0 ⟶ ModuleCat.of ℚ ℂ :=
    ModuleCat.ofHom
      ((Algebra.linearMap ℚ ℂ).comp (openZeroAugmentation ℚ X U).hom)
  have hfg : f = g := by
    apply SSet.chainComplex_hom_ext
    intro x
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    change (openZeroAugmentation ℂ X U).hom
        (fieldToFieldChainGroup ℚ ℂ
          ((Opens.toTopCat X).obj U.unop) 0
          (((TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)).ιChainComplex
            (R := ModuleCat.of ℚ ℚ) x).hom q)) =
      algebraMap ℚ ℂ
        ((openZeroAugmentation ℚ X U).hom
          (((TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)).ιChainComplex
            (R := ModuleCat.of ℚ ℚ) x).hom q))
    rw [fieldToFieldChainGroup_iota]
    rw [show (openZeroAugmentation ℂ X U).hom
          (((TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)).ιChainComplex
            (R := ModuleCat.of ℂ ℂ) x).hom
            (algebraMap ℚ ℂ q)) = algebraMap ℚ ℂ q by
      exact congrArg (fun k => k.hom (algebraMap ℚ ℂ q))
        (ιChainComplex_comp_simplicialZeroAugmentation ℂ
          (TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)) x)]
    rw [show (openZeroAugmentation ℚ X U).hom
          (((TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)).ιChainComplex
            (R := ModuleCat.of ℚ ℚ) x).hom q) = q by
      exact congrArg (fun k => k.hom q)
        (ιChainComplex_comp_simplicialZeroAugmentation ℚ
          (TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)) x)]
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hfg) c

/-- The inclusion of constants into singular zero-cochains commutes with
rational-to-complex coefficient extension. -/
theorem qToC_constantsToSingularCochainZero :
    qToCConstantCoefficientPresheaf X ≫
        constantsToSingularCochainZero ℂ X =
      constantsToSingularCochainZero ℚ X ≫
        qToCSingularCochainPresheaf X 0 := by
  apply NatTrans.ext
  funext U
  change AddCommGrpCat.ofHom (algebraMap ℚ ℂ).toAddMonoidHom ≫
      AddCommGrpCat.ofHom (constantSingularZeroCochain ℂ X U) =
    AddCommGrpCat.ofHom (constantSingularZeroCochain ℚ X U) ≫
      AddCommGrpCat.ofHom (qToCOpenCochains X U 0).toAddMonoidHom
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro q
  change ℚ at q
  simp only [ConcreteCategory.comp_apply]
  dsimp only [constantSingularZeroCochain]
  change (algebraMap ℚ ℂ q) • (openZeroAugmentation ℂ X U).hom =
    qToCOpenCochains X U 0
      (q • (openZeroAugmentation ℚ X U).hom)
  apply (fieldToFieldOpenChainGroup_isBaseChange ℚ ℂ X U 0).algHom_ext
  intro c
  rw [qToCOpenCochains_apply_qToCChain]
  simp only [LinearMap.smul_apply]
  rw [openZeroAugmentation_qToC_apply]
  change (algebraMap ℚ ℂ q) *
      algebraMap ℚ ℂ ((openZeroAugmentation ℚ X U).hom c) =
    algebraMap ℚ ℂ (q * (openZeroAugmentation ℚ X U).hom c)
  rw [map_mul]

/-- Coefficient extension on constant coefficient sheaves. -/
def qToCConstantCoefficientSheaf (X : TopCat) :
    constantCoefficientSheaf ℚ X ⟶ constantCoefficientSheaf ℂ X :=
  let J := Opens.grothendieckTopology X
  (presheafToSheaf J AddCommGrpCat).map
    (qToCConstantCoefficientPresheaf X)

/-- The constant-to-singular square after sheafification. -/
theorem qToC_constantsToSingularCochainZeroSheaf :
    qToCConstantCoefficientSheaf X ≫
        constantsToSingularCochainZeroSheaf ℂ X =
      constantsToSingularCochainZeroSheaf ℚ X ≫
        (qToCSingularCochainSheafComplex X).f 0 := by
  let J := Opens.grothendieckTopology X
  change (presheafToSheaf J AddCommGrpCat).map
      (qToCConstantCoefficientPresheaf X) ≫
      (presheafToSheaf J AddCommGrpCat).map
        (constantsToSingularCochainZero ℂ X) =
    (presheafToSheaf J AddCommGrpCat).map
        (constantsToSingularCochainZero ℚ X) ≫
      (presheafToSheaf J AddCommGrpCat).map
        (qToCSingularCochainPresheaf X 0)
  rw [← Functor.map_comp, ← Functor.map_comp,
    qToC_constantsToSingularCochainZero]

/-- Rational-to-complex coefficient extension as a map of the sheafified
singular-cochain complexes extended to integer degrees. -/
def qToCSingularCochainSheafComplexInt (X : TopCat) :
    (singularCochainSheafComplex ℚ X).extend
        ComplexShape.embeddingUpNat ⟶
      (singularCochainSheafComplex ℂ X).extend
        ComplexShape.embeddingUpNat :=
  HomologicalComplex.extendMap (qToCSingularCochainSheafComplex X)
    ComplexShape.embeddingUpNat

/-- The full constant-to-singular comparison square in integer degrees. -/
theorem qToC_constantsToSingularCochainSheafComplexInt :
    HomologicalComplex.extendMap
        ((CochainComplex.single₀
          (TopCat.Sheaf AddCommGrpCat X)).map
            (qToCConstantCoefficientSheaf X))
        ComplexShape.embeddingUpNat ≫
      HomologicalComplex.extendMap
        (constantsToSingularCochainSheafComplex ℂ X)
        ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap
        (constantsToSingularCochainSheafComplex ℚ X)
        ComplexShape.embeddingUpNat ≫
      qToCSingularCochainSheafComplexInt X := by
  rw [← HomologicalComplex.extendMap_comp]
  unfold qToCSingularCochainSheafComplexInt
  rw [← HomologicalComplex.extendMap_comp]
  congr 1
  ext
  change qToCConstantCoefficientSheaf X ≫
      constantsToSingularCochainZeroSheaf ℂ X =
    constantsToSingularCochainZeroSheaf ℚ X ≫
      (qToCSingularCochainSheafComplex X).f 0
  exact qToC_constantsToSingularCochainZeroSheaf (X := X)

end AlgebraicTopology.Singular
