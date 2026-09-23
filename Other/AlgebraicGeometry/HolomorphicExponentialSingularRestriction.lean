/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicExponentialSingularClass
public import Other.AlgebraicGeometry.BettiSupportConeComparison
public import Other.Algebra.Homology.SingleCocycleFactorization
/-!
# Restricting the exponential–winding comparison

The winding cocycle is composed with the fixed singular-to-injective resolution map
on the open complement. Termwise locality then factors it through the restricted unit
sheaf. The factorization is a strict cocycle identity; uniqueness in the derived
category identifies its negative with the restricted rational exponential class.

The relative comparison's second square consequently yields a positive winding
boundary representative in the rational support cone. Its passage to local supported
singular cohomology is a further comparison, not asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Localization TopologicalSpace Opposite
open CochainComplex.HomComplex
namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
local instance exponentialSingularRestrictionTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local instance exponentialSingularRestrictionDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)
variable [IsIntegral X.left] [Smooth X.hom]
variable (Ω : Opens (TopCat.of (ComplexPoint X)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The winding cocycle on the complement, factored through restricted units.
This is constructed from singular winding and the fixed resolution map, independently of Chern classes. -/
def restrictedSingularOneCocycle :
    Cocycle ((analyticSingleFunctor X).obj
      ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d)))
      (derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)) 1 :=
  (Cocycle.exists_precomp_single_eq
    (restrictionUnit Ω (holomorphicUnitSheaf X d))
    (derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)) 1
    (fun q => isOpenRestrictionLocal_derivedPushforward X Ω ((Ω : Set (ComplexPoint X))ᶜ)
      (compl_compl _).symm q (holomorphicUnitSheaf X d))
    ((holomorphicSingularOneCocycle X d).postcomp
      (naturalSingularResolutionRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
        Ω.isOpen.isClosed_compl))).choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The strict restriction square for the factored winding cocycle. -/
theorem restrictedSingularOneCocycle_precomp :
    (restrictedSingularOneCocycle X d Ω).precomp
      ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d))) =
    (holomorphicSingularOneCocycle X d).postcomp
      (naturalSingularResolutionRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
        Ω.isOpen.isClosed_compl) :=
  (Cocycle.exists_precomp_single_eq
    (restrictionUnit Ω (holomorphicUnitSheaf X d))
    (derivedPushforwardComplementConstantRationalComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)) 1
    (fun q => isOpenRestrictionLocal_derivedPushforward X Ω ((Ω : Set (ComplexPoint X))ᶜ)
      (compl_compl _).symm q (holomorphicUnitSheaf X d))
    ((holomorphicSingularOneCocycle X d).postcomp
      (naturalSingularResolutionRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
        Ω.isOpen.isClosed_compl))).choose_spec

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsIntegral X.left] [Smooth X.hom] in
private theorem smallShiftedHom_mk_comp_mk₀
    {A B D : CochainComplex (AnalyticAdditiveSheaf X) ℤ} {n : ℤ}
    (f : ShiftedHom A B n) (g : B ⟶ D) :
    (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) f).comp
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl g) (zero_add n) =
    SmallShiftedHom.mk (analyticQuasiIsomorphisms X) (f ≫ g⟦n⟧') := by
  apply (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  rw [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk, SmallShiftedHom.equiv_mk₀,
    SmallShiftedHom.equiv_mk, ShiftedHom.comp_mk₀]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc,
    Functor.commShiftIso_hom_naturality]

set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The restricted rational exponential class is negative winding in the fixed complement resolution. -/
theorem restrictedRationalChernShiftedHom_eq_singularCocycle :
    restrictedRationalChernShiftedHom X d Ω =
      SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (-Cocycle.equivHomShift.symm (restrictedSingularOneCocycle X d Ω)) := by
  apply (bijective_comp_restrictionUnit X Ω ((Ω : Set (ComplexPoint X))ᶜ)
    Ω.isOpen.isClosed_compl (compl_compl _).symm (holomorphicUnitSheaf X d) (1 : ℤ)).1
  change (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
    ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d)))).comp
    (restrictedRationalChernShiftedHom X d Ω) (add_zero (1 : ℤ)) =
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
      ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d)))).comp
      (SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (-Cocycle.equivHomShift.symm (restrictedSingularOneCocycle X d Ω))) (add_zero (1 : ℤ))
  let a := constantsToSingularCochainComplexInt X ℚ
  let b := naturalSingularResolutionRestriction X ((Ω : Set (ComplexPoint X))ᶜ)
    Ω.isOpen.isClosed_compl
  let η := (analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d))
  let β := Cocycle.equivHomShift.symm (holomorphicSingularOneCocycle X d)
  let βΩ := Cocycle.equivHomShift.symm (restrictedSingularOneCocycle X d Ω)
  have hab : a ≫ b = rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ) :=
    rationalToSingular_comp_naturalSingularResolutionRestriction X _ Ω.isOpen.isClosed_compl
  have hβ : η ≫ βΩ = β ≫ b⟦(1 : ℤ)⟧' := by
    have h := congrArg Cocycle.equivHomShift.symm (restrictedSingularOneCocycle_precomp X d Ω)
    simpa only [Cocycle.equivHomShift_symm_precomp, Cocycle.equivHomShift_symm_postcomp] using h
  have hR : SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
      (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)) =
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl a).comp
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl b) (add_zero (0 : ℤ)) := by
    rw [SmallShiftedHom.mk₀_comp_mk₀' (M := ℤ), hab]
  rw [restriction_comp_restrictedRationalChernShiftedHom X d Ω, hR]
  rw [← SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X) (rationalChernShiftedHom X d)
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl a)
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl b)
    (zero_add (1 : ℤ)) (zero_add 0) (by omega)]
  change ((rationalChernShiftedHom X d).comp
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
      (constantsToSingularCochainComplexInt X ℚ)) (zero_add (1 : ℤ))).comp _ (zero_add (1 : ℤ)) = _
  rw [rationalChernShiftedHom_comp_singularAugmentation]
  exact (smallShiftedHom_mk_comp_mk₀ X (-β) b).trans ((congrArg
    (SmallShiftedHom.mk (analyticQuasiIsomorphisms X))
    (show (-β) ≫ b⟦(1 : ℤ)⟧' = η ≫ (-βΩ) from by
      rw [Preadditive.neg_comp, Preadditive.comp_neg, hβ])).trans
    (SmallShiftedHom.mk₀_comp_mk (analyticQuasiIsomorphisms X) η (-βΩ)).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two minus signs in the rational cone boundary formula cancel.
The result is a positive winding boundary representative before conversion to supported injective homology. -/
theorem RelativeChernComparison.boundary_eq_singular
    (cmp : RelativeChernComparison X d Ω) :
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
      (CochainComplex.mappingCone.inr
        ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d))))).comp
      cmp.hom (add_zero (1 : ℤ)) =
    SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
      (Cocycle.equivHomShift.symm (restrictedSingularOneCocycle X d Ω) ≫
        (CochainComplex.mappingCone.inr
          (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)))⟦(1 : ℤ)⟧') := by
  rw [cmp.boundary_comm, cmp.restrictionClass_eq,
    restrictedRationalChernShiftedHom_eq_singularCocycle X d Ω]
  refine (smallShiftedHom_mk_comp_mk₀ X _ _).trans ?_
  congr 1
  simp only [Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
  rfl

end AlgebraicGeometry.ComplexPoint
