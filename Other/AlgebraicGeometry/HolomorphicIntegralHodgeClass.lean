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

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ)

local instance integralHodgeTopology : TopologicalSpace (ComplexPoint X s) := Point.analyticTopology

/-- Extending integer coefficients through the rationals agrees with the direct complex map. -/
theorem integerToRationalToComplexConstantSheaf :
    integerToFieldConstantSheaf ℚ s 1 ≫ fieldToComplexConstantSheaf ℚ s =
      integerToFieldConstantSheaf ℂ s 1 := by
  let J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X s))
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
theorem integerToComplexToHolomorphicSheaf (d : ℕ) [SmoothOfRelativeDimension d s] :
    integerToFieldConstantSheaf ℂ s 1 ≫ complexConstantsToHolomorphicSheaf s d =
      integerConstantsToHolomorphicSheaf s d := by
  apply Sheaf.hom_ext
  change sheafifyMap _ ((Functor.const _).map
      (AddCommGrpCat.ofHom (integerMultipleAddHom ℂ 1))) ≫
    sheafifyLift _ (complexConstantsToHolomorphicPresheaf s d) _ =
      sheafifyLift _ (integerConstantsToHolomorphicPresheaf s d) _
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
    [IsIntegral X] [Smooth s] :
    constantsToHolomorphicDeRhamComplexInt s ≫ holomorphicDeRhamToFunctionsComplexInt s =
      analyticSheafComplexIntMap s (complexConstantsToHolomorphicSheaf s (dim X)) ≫
        (analyticSheafComplexIntIsoSingle s (holomorphicAdditiveSheaf s (dim X))).hom := by
  unfold constantsToHolomorphicDeRhamComplexInt holomorphicDeRhamToFunctionsComplexInt
  erw [← Category.assoc, ← HomologicalComplex.extendMap_comp,
    constantsToHolomorphicDeRhamComplex_comp_toFunctions]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient and de Rham maps give the integer inclusion from the exponential sequence. -/
theorem integerToRationalDeRhamToFunctions [IsIntegral X] [Smooth s] :
    integerToFieldConstantSheafComplexInt ℚ s 1 ≫
        fieldToHolomorphicDeRhamComplexInt ℚ s ≫ holomorphicDeRhamToFunctionsComplexInt s =
      analyticSheafComplexIntMap s (integerConstantsToHolomorphicSheaf s (dim X)) ≫
        (analyticSheafComplexIntIsoSingle s (holomorphicAdditiveSheaf s (dim X))).hom := by
  unfold fieldToHolomorphicDeRhamComplexInt
  rw [Category.assoc, constantsToHolomorphicDeRhamComplexInt_comp_toFunctions]
  change analyticSheafComplexIntMap s (integerToFieldConstantSheaf ℚ s 1) ≫
    analyticSheafComplexIntMap s (fieldToComplexConstantSheaf ℚ s) ≫
    analyticSheafComplexIntMap s (complexConstantsToHolomorphicSheaf s (dim X)) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, ← analyticSheafComplexIntMap_comp,
    ← analyticSheafComplexIntMap_comp, integerToRationalToComplexConstantSheaf,
    integerToComplexToHolomorphicSheaf]

/-- Integral constant-sheaf cohomology in an integer degree. -/
abbrev IntegralCohomology (n : ℤ) :=
  Hypercohomology s (constantIntegerSheafComplexInt s) n

/-- The canonical change from integral to rational coefficients. -/
def integralToRationalCohomology (n : ℤ) :
    IntegralCohomology s n →+ FieldCohomology ℚ s n :=
  hypercohomologyMap s (integerToFieldConstantSheafComplexInt ℚ s 1) n

set_option backward.isDefEq.respectTransparency false in
/-- An integral degree-two class whose rational image has Hodge type `(1, 1)` vanishes
after mapping to the second cohomology of holomorphic functions. -/
theorem integralHodgeClass_toHolomorphicCohomology_eq_zero [IsIntegral X] [Smooth s]
    (α : IntegralCohomology s 2)
    (hα : integralToRationalCohomology s 2 α ∈ hodgeClasses ℚ s 1) :
    hypercohomologyMap s
      (analyticSheafComplexIntMap s (integerConstantsToHolomorphicSheaf s (dim X))) 2 α = 0 := by
  apply hypercohomologyMap_injective_of_isIso s
    (analyticSheafComplexIntIsoSingle s (holomorphicAdditiveSheaf s (dim X))).hom 2
  erw [map_zero, ← hypercohomologyMap_comp_apply, ← integerToRationalDeRhamToFunctions,
    hypercohomologyMap_comp_apply, hypercohomologyMap_comp_apply]
  exact hodgeClass_one_toHolomorphicFunctionCohomology_eq_zero s _ hα

set_option backward.isDefEq.respectTransparency false in
/-- The preceding vanishing statement in the Ext presentation used by the exponential sequence. -/
theorem integralHodgeClass_integerToHolomorphicSecondCohomology_eq_zero
    [IsIntegral X] [Smooth s] (α : IntegralCohomology s 2)
    (hα : integralToRationalCohomology s 2 α ∈ hodgeClasses ℚ s 1) :
    integerToHolomorphicSecondCohomology s (dim X)
      (analyticSheafCohomologyEquivExt s (constantIntegerSheaf s) 2 α) = 0 := by
  have h := congrArg
    (analyticSheafCohomologyEquivExt s (holomorphicAdditiveSheaf s (dim X)) 2)
    (integralHodgeClass_toHolomorphicCohomology_eq_zero s α hα)
  erw [analyticSheafCohomologyEquivExt_naturality, analyticSheafCohomologyEquivExt_zero] at h
  exact h

/-- Every integral class whose rational image has Hodge type `(1, 1)` is in the image of
the Chern-class connecting map of the holomorphic exponential sequence. -/
theorem exists_holomorphicFirstChernClass_of_integral_hodgeClass [IsIntegral X] [Smooth s]
    (α : IntegralCohomology s 2)
    (hα : integralToRationalCohomology s 2 α ∈ hodgeClasses ℚ s 1) :
    ∃ β, holomorphicFirstChernClass s (dim X) β =
      analyticSheafCohomologyEquivExt s (constantIntegerSheaf s) 2 α :=
  (exists_holomorphicFirstChernClass_iff s (dim X) _).mpr
    (integralHodgeClass_integerToHolomorphicSecondCohomology_eq_zero s α hα)

end AlgebraicGeometry.ComplexPoint
