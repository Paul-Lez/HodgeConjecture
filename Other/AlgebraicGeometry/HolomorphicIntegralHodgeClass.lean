/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticSheafCohomologyExt
public import Other.AlgebraicGeometry.HolomorphicFirstChernClass
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

variable (X : Over (Spec ↧ℂ))

local instance integralHodgeTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology

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
  simp [integerMultipleAddHom]

set_option backward.isDefEq.respectTransparency false in
/-- The integer inclusion into holomorphic functions is induced by the usual complex constants. -/
theorem integerToComplexToHolomorphicSheaf (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    integerToFieldConstantSheaf ℂ X 1 ≫ complexConstantsToHolomorphicSheaf X d =
      integerConstantsToHolomorphicSheaf X d := by
  apply Sheaf.hom_ext
  change sheafifyMap _ ((Functor.const _).map
      (AddCommGrpCat.ofHom (integerMultipleAddHom ℂ 1))) ≫
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
  change (n : ℂ) * 1 = (n : ℂ)
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
    integerToFieldConstantSheafComplexInt ℚ X 1 ≫
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

/-- Integral constant-sheaf cohomology in an integer degree. -/
abbrev IntegralCohomology (n : ℤ) :=
  Hypercohomology X (constantIntegerSheafComplexInt X) n

/-- The canonical change from integral to rational coefficients. -/
def integralToRationalCohomology (n : ℤ) :
    IntegralCohomology X n →+ FieldCohomology ℚ X n :=
  hypercohomologyMap X (integerToFieldConstantSheafComplexInt ℚ X 1) n

set_option backward.isDefEq.respectTransparency false in
/-- An integral degree-two class whose rational image has Hodge type `(1, 1)` vanishes
after mapping to the second cohomology of holomorphic functions. -/
theorem integralHodgeClass_toHolomorphicCohomology_eq_zero [IsIntegral X.left] [Smooth X.hom]
    (α : IntegralCohomology X 2)
    (hα : integralToRationalCohomology X 2 α ∈ hodgeClasses ℚ X 1) :
    hypercohomologyMap X
      (analyticSheafComplexIntMap X (integerConstantsToHolomorphicSheaf X (dim X.left))) 2 α = 0 := by
  apply hypercohomologyMap_injective_of_isIso X
    (analyticSheafComplexIntIsoSingle X (holomorphicAdditiveSheaf X (dim X.left))).hom 2
  erw [map_zero, ← hypercohomologyMap_comp_apply, ← integerToRationalDeRhamToFunctions,
    hypercohomologyMap_comp_apply, hypercohomologyMap_comp_apply]
  exact hodgeClass_one_toHolomorphicFunctionCohomology_eq_zero X _ hα

set_option backward.isDefEq.respectTransparency false in
/-- The preceding vanishing statement in the Ext presentation used by the exponential sequence. -/
theorem integralHodgeClass_integerToHolomorphicSecondCohomology_eq_zero
    [IsIntegral X.left] [Smooth X.hom] (α : IntegralCohomology X 2)
    (hα : integralToRationalCohomology X 2 α ∈ hodgeClasses ℚ X 1) :
    integerToHolomorphicSecondCohomology X (dim X.left)
      (analyticSheafCohomologyEquivExt X (constantIntegerSheaf X) 2 α) = 0 := by
  have h := congrArg
    (analyticSheafCohomologyEquivExt X (holomorphicAdditiveSheaf X (dim X.left)) 2)
    (integralHodgeClass_toHolomorphicCohomology_eq_zero X α hα)
  erw [analyticSheafCohomologyEquivExt_naturality, analyticSheafCohomologyEquivExt_zero] at h
  exact h

/-- Every integral class whose rational image has Hodge type `(1, 1)` is in the image of
the Chern-class connecting map of the holomorphic exponential sequence. -/
theorem exists_holomorphicFirstChernClass_of_integral_hodgeClass [IsIntegral X.left] [Smooth X.hom]
    (α : IntegralCohomology X 2)
    (hα : integralToRationalCohomology X 2 α ∈ hodgeClasses ℚ X 1) :
    ∃ β, holomorphicFirstChernClass X (dim X.left) β =
      analyticSheafCohomologyEquivExt X (constantIntegerSheaf X) 2 α :=
  (exists_holomorphicFirstChernClass_iff X (dim X.left) _).mpr
    (integralHodgeClass_integerToHolomorphicSecondCohomology_eq_zero X α hα)

end AlgebraicGeometry.ComplexPoint
