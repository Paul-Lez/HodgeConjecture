/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.IntegralCohomology
public import Other.AlgebraicGeometry.AnalyticSheafCohomologyExt
public import Other.AlgebraicGeometry.HolomorphicFirstChernClassExactness
public import Other.AlgebraicGeometry.HolomorphicHodgeProjection

/-!
# Integral Hodge classes and the holomorphic exponential sequence

We compare the coefficient maps in the Hodge-filtration definition with the integer inclusion
in the exponential sequence. This connects the analytic vanishing result to the Chern-class
connecting map, for integral classes whose rational images have Hodge type `(1, 1)`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

variable (X : Over (Spec ↧ℂ))

attribute [local instance] analyticSheafExtHasDerivedCategory



/-- Extending integer coefficients through the rationals agrees with the direct complex map. -/
theorem integerToRationalToComplexConstantSheaf :
    integerToFieldConstantSheaf ℚ X 1 ≫ fieldToComplexConstantSheaf ℚ X =
      integerToFieldConstantSheaf ℂ X 1 := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))
  change (constantSheaf J AddCommGrpCat).map _ ≫
    (constantSheaf J AddCommGrpCat).map _ = (constantSheaf J AddCommGrpCat).map _
  rw [← Functor.map_comp]
  congr 1
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro n
  simp [zmultiplesAddHom]

set_option backward.isDefEq.respectTransparency false in
/-- The integer inclusion into holomorphic functions is induced by the usual complex constants. -/
theorem integerToComplexToHolomorphicSheaf (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    integerToFieldConstantSheaf ℂ X 1 ≫ complexConstantsToHolomorphicSheaf X d =
      integerConstantsToHolomorphicSheaf X d := by
  apply Sheaf.hom_ext
  change sheafifyMap _ ((Functor.const _).map
      (AddCommGrpCat.ofHom (zmultiplesAddHom ℂ 1))) ≫
    sheafifyLift _ (complexConstantsToHolomorphicPresheaf X d) _ =
      sheafifyLift _ (integerConstantsToHolomorphicPresheaf X d) _
  rw [sheafifyMap_sheafifyLift]
  congr 1
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro n
  change ℤ at n
  apply Subtype.ext
  funext x
  change n • (1 : ℂ) = (n : ℂ)
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The extended de Rham comparison followed by projection is the constant-function map. -/
theorem constantsToHolomorphicDeRhamComplexInt_comp_toFunctions
    [IsIntegral X.left] [Smooth X.hom] :
    constantsToHolomorphicDeRhamComplexInt X ≫ holomorphicDeRhamToFunctionsComplexInt X =
      analyticSheafComplexIntMap X (complexConstantsToHolomorphicSheaf X (dim X.left)) ≫
        (analyticSheafComplexIntIsoSingle X (holomorphicAdditiveSheaf X (dim X.left))).hom := by
  unfold constantsToHolomorphicDeRhamComplexInt holomorphicDeRhamToFunctionsComplexInt
  erw [← Category.assoc, ← HomologicalComplex.extendMap_comp,
    constantsToHolomorphicDeRhamComplex_comp_toFunctions]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient and de Rham maps give the integer inclusion from the exponential sequence. -/
theorem integerToRationalDeRhamToFunctions [IsIntegral X.left] [Smooth X.hom] :
    analyticSheafComplexIntMap X (integerToFieldConstantSheaf ℚ X 1) ≫
        fieldToHolomorphicDeRhamComplexInt ℚ X ≫ holomorphicDeRhamToFunctionsComplexInt X =
      analyticSheafComplexIntMap X (integerConstantsToHolomorphicSheaf X (dim X.left)) ≫
        (analyticSheafComplexIntIsoSingle X (holomorphicAdditiveSheaf X (dim X.left))).hom := by
  unfold fieldToHolomorphicDeRhamComplexInt
  rw [Category.assoc, constantsToHolomorphicDeRhamComplexInt_comp_toFunctions]
  change analyticSheafComplexIntMap X (integerToFieldConstantSheaf ℚ X 1) ≫
    analyticSheafComplexIntMap X (fieldToComplexConstantSheaf ℚ X) ≫
    analyticSheafComplexIntMap X (complexConstantsToHolomorphicSheaf X (dim X.left)) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, ← analyticSheafComplexIntMap_comp,
    ← analyticSheafComplexIntMap_comp, integerToRationalToComplexConstantSheaf,
    integerToComplexToHolomorphicSheaf]

set_option backward.isDefEq.respectTransparency false in
/-- An integral degree-two class whose rational image has Hodge type `(1, 1)` vanishes
after mapping to the second cohomology of holomorphic functions. -/
private theorem integralHodgeClass_toHolomorphicHypercohomology_eq_zero
    [IsIntegral X.left] [Smooth X.hom]
    (β : Hypercohomology X
      (analyticSheafComplexInt X (𝓒(↧(ComplexPoint X); ℤ))) 2)
    (hβ : (hypercohomologyAddEquivConstantCohomology ℚ X 2)
      (hypercohomologyMap X
        (analyticSheafComplexIntMap X (integerToFieldConstantSheaf ℚ X 1)) 2 β) ∈
      hodgeClasses ℚ X 1) :
    hypercohomologyMap X
      (analyticSheafComplexIntMap X (integerConstantsToHolomorphicSheaf X (dim X.left))) 2 β = 0 := by
  have hz := hodgeClass_one_toHolomorphicFunctionCohomology_eq_zero X _ hβ
  dsimp only [deRhamToHolomorphicFunctionCohomology, fieldToDeRhamCohomology,
    integralToRationalCohomology, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at hz
  rw [AddEquiv.symm_apply_apply] at hz
  erw [← hypercohomologyMap_comp_apply, ← hypercohomologyMap_comp_apply,
    integerToRationalDeRhamToFunctions, hypercohomologyMap_comp_apply] at hz
  apply hypercohomologyMap_injective_of_isIso X
    (L := holomorphicFunctionComplexInt X (dim X.left))
    (analyticSheafComplexIntIsoSingle X (holomorphicAdditiveSheaf X (dim X.left))).hom 2
  simpa only [map_zero] using hz

/-- An integral class of Hodge type `(1, 1)` maps to zero in holomorphic-function cohomology. -/
theorem integralHodgeClass_toHolomorphicCohomology_eq_zero [IsIntegral X.left] [Smooth X.hom]
    (α : H^2(X; ℤ))
    (hα : integralToRationalCohomology X 2 α ∈ hodgeClasses ℚ X 1) :
    Sheaf.H.map (integerConstantsToHolomorphicSheaf X (dim X.left)) 2 α =
      (0 : Sheaf.H (holomorphicAdditiveSheaf X (dim X.left)) 2) := by
  let β : Hypercohomology X
      (analyticSheafComplexInt X (𝓒(↧(ComplexPoint X); ℤ))) 2 :=
    (analyticSheafHypercohomologyAddEquiv X (𝓒(↧(ComplexPoint X); ℤ)) 2).symm α
  have hβ : integralToRationalCohomology X 2
      (analyticSheafHypercohomologyAddEquiv X (𝓒(↧(ComplexPoint X); ℤ)) 2 β) ∈
      hodgeClasses ℚ X 1 := by
    rw [AddEquiv.apply_symm_apply]
    exact hα
  have hβ' : (hypercohomologyAddEquivConstantCohomology ℚ X 2)
      (hypercohomologyMap X
        (analyticSheafComplexIntMap X (integerToFieldConstantSheaf ℚ X 1))
        ((2 : ℕ) : ℤ) β) ∈
      hodgeClasses ℚ X 1 := by
    rw [← integralToRationalCohomology_analyticSheafHypercohomologyAddEquiv X 2 β]
    exact hβ
  have hzero := integralHodgeClass_toHolomorphicHypercohomology_eq_zero X β hβ'
  calc
    Sheaf.H.map (integerConstantsToHolomorphicSheaf X (dim X.left)) 2 α =
        Sheaf.H.map (integerConstantsToHolomorphicSheaf X (dim X.left)) 2
          (analyticSheafHypercohomologyAddEquiv X
            (𝓒(↧(ComplexPoint X); ℤ)) 2 β) := by
      rw [AddEquiv.apply_symm_apply]
    _ = analyticSheafHypercohomologyAddEquiv X
          (holomorphicAdditiveSheaf X (dim X.left)) 2
          (hypercohomologyMap X
            (analyticSheafComplexIntMap X
              (integerConstantsToHolomorphicSheaf X (dim X.left))) 2 β) := by
      exact (analyticSheafHypercohomologyAddEquiv_naturality X
        (integerConstantsToHolomorphicSheaf X (dim X.left)) 2 β).symm
    _ = analyticSheafHypercohomologyAddEquiv X
          (holomorphicAdditiveSheaf X (dim X.left)) 2
          (0 : Hypercohomology X
            (analyticSheafComplexInt X (holomorphicAdditiveSheaf X (dim X.left))) 2) := by
      rw [hzero]
    _ = (0 : Sheaf.H (holomorphicAdditiveSheaf X (dim X.left)) 2) := map_zero _

set_option backward.isDefEq.respectTransparency false in
/-- The preceding vanishing statement in the Ext presentation used by the exponential sequence. -/
theorem integralHodgeClass_integerToHolomorphicSecondCohomology_eq_zero
    [IsIntegral X.left] [Smooth X.hom] (α : H^2(X; ℤ))
    (hα : integralToRationalCohomology X 2 α ∈ hodgeClasses ℚ X 1) :
    integerToHolomorphicSecondCohomology X (dim X.left)
      (sheafCohomologyEquivExt X 𝓒(↧(ComplexPoint X); ℤ) 2 α) = 0 := by
  have h := congrArg
    (sheafCohomologyEquivExt X (holomorphicAdditiveSheaf X (dim X.left)) 2)
    (integralHodgeClass_toHolomorphicCohomology_eq_zero X α hα)
  erw [sheafCohomologyEquivExt_naturality] at h
  change (sheafCohomologyEquivExt X 𝓒(↧(ComplexPoint X); ℤ) 2 α).comp
      (Abelian.Ext.mk₀ (integerConstantsToHolomorphicSheaf X (dim X.left))) (add_zero 2) = 0
  simpa only [map_zero] using h

/-- Every integral class whose rational image has Hodge type `(1, 1)` is in the image of
the Chern-class connecting map of the holomorphic exponential sequence. -/
theorem exists_holomorphicFirstChernClass_of_integral_hodgeClass [IsIntegral X.left] [Smooth X.hom]
    (α : H^2(X; ℤ))
    (hα : integralToRationalCohomology X 2 α ∈ hodgeClasses ℚ X 1) :
    ∃ β, holomorphicFirstChernClass X (dim X.left) β =
      sheafCohomologyEquivExt X 𝓒(↧(ComplexPoint X); ℤ) 2 α :=
  (exists_holomorphicFirstChernClass_iff X (dim X.left) _).mpr
    (integralHodgeClass_integerToHolomorphicSecondCohomology_eq_zero X α hα)

end AlgebraicGeometry.ComplexPoint
