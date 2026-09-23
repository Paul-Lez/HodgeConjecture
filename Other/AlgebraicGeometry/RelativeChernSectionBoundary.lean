/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicExponentialIntrinsicWindingClass
public import Other.AlgebraicGeometry.ChernRelativeChartFormulaSplitting

/-!
# Evaluating the relative Chern boundary on an actual section

The boundary square of the existing relative Chern comparison, precomposed with
a morphism from the constant integer sheaf, gives the positive boundary of the
actual restricted singular cocycle in the prescribed hypercohomology model.
The sign of the subsequent support comparison is separate.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Localization TopologicalSpace Opposite
open CochainComplex.HomComplex
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
local instance sectionBoundaryDerivedCategory : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _
variable [IsIntegral X.left] [Smooth X.hom]
variable (Ω : Opens (TopCat.of (ComplexPoint X)))
/-- The boundary comparison on a concrete integer-input morphism is the actual
restricted singular cocycle boundary, with positive sign before support transport. -/
lemma RelativeChernComparison.boundary_eq_singular_on_section
    (cmp : RelativeChernComparison X d Ω)
    (s : constantIntegerSheaf X ⟶ (openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d)) :
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
      ((constantIntegerSheafComplexIntIsoSingle X).hom ≫
        (analyticSingleFunctor X).map s ≫
        CochainComplex.mappingCone.inr
          ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d))))).comp
      cmp.hom (add_zero (1 : ℤ)) =
    hypercohomologyMap X
      (CochainComplex.mappingCone.inr (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))) 1
      (SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        ((constantIntegerSheafComplexIntIsoSingle X).hom ≫
          Cocycle.equivHomShift.symm
            ((restrictedSingularOneCocycle X d Ω).precomp ((analyticSingleFunctor X).map s)))) := by
  let a := (constantIntegerSheafComplexIntIsoSingle X).hom ≫ (analyticSingleFunctor X).map s
  let k := CochainComplex.mappingCone.inr
    ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d)))
  let l := CochainComplex.mappingCone.inr
    (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))
  let β := Cocycle.equivHomShift.symm (restrictedSingularOneCocycle X d Ω)
  have hmk : SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl (a ≫ k) =
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl a).comp
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl k) (add_zero (0 : ℤ)) := by
    rw [SmallShiftedHom.mk₀_comp_mk₀' (M := ℤ)]
  change (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl (a ≫ k)).comp
    cmp.hom (add_zero (1 : ℤ)) = _
  rw [hmk, SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X)
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl a)
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl k) cmp.hom
    (add_zero (0 : ℤ)) (add_zero (1 : ℤ)) (by omega)]
  rw [cmp.boundary_eq_singular, SmallShiftedHom.mk₀_comp_mk]
  apply (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  simp only [hypercohomologyMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk,
    SmallShiftedHom.equiv_mk₀, ShiftedHom.comp_mk₀, Cocycle.equivHomShift_symm_precomp]
  simp only [ShiftedHom.map, CategoryTheory.Functor.map_comp, Category.assoc,
    Functor.commShiftIso_hom_naturality]
  dsimp only [a]
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
end AlgebraicGeometry.ComplexPoint
