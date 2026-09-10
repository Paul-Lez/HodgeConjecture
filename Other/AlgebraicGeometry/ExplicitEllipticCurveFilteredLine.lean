/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticGlobalOneForms
public import Other.AlgebraicGeometry.ExplicitEllipticCMDeRhamEigen
public import Other.AlgebraicGeometry.ExplicitEllipticCurveConnected

/-!
# The first filtered line of the explicit elliptic curve

On a connected analytification, the global invariant differential spans every
global holomorphic one-form.  The top-form/filtered comparison therefore makes
the entire first filtered source a single complex line.  After inclusion into
the full de Rham complex this becomes ordinary complex scalar multiplication.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

/-- Every class in the first filtered source is obtained from the explicit
class by the scalar endomorphism of the filtered de Rham complex. -/
theorem exists_curveFilteredClass_eq_scalarMap
    (alpha : FilteredDeRhamHypercohomology curveVariety 1 1) :
    ∃ c : ℂ,
      alpha = hypercohomologyMap curveVariety
        (hodgeFilteredDeRhamComplexScalar curveVariety 1 c) 1
        curveTopFilteredClass := by
  letI : ConnectedSpace (ComplexPoint curveAnalyticVariety) := by
    change ConnectedSpace (ComplexPoint curveVariety)
    infer_instance
  let e := topHolomorphicFormFilteredEquivOfDimension
    curveVariety 1 dim_curve_eq_one
  let w := e.symm alpha
  obtain ⟨c, hc⟩ := exists_curveGlobalOneForm_eq_smul w
  refine ⟨c, ?_⟩
  calc
    alpha = e w := (e.apply_symm_apply alpha).symm
    _ = e (curveGlobalHolomorphicDifferential_smul c) := congrArg e hc
    _ = hypercohomologyMap curveVariety
        (hodgeFilteredDeRhamComplexScalar curveVariety 1 c) 1
        curveTopFilteredClass := by
      exact topHolomorphicFormFilteredEquivOfDimension_scalar
        curveVariety 1 dim_curve_eq_one c
        curveGlobalHolomorphicDifferential

/-- Every degree-one class in the first Hodge filtration is a complex scalar
multiple of the de Rham class of the invariant differential. -/
theorem exists_curveFilteredToDeRham_eq_smul
    (alpha : FilteredDeRhamHypercohomology curveVariety 1 1) :
    ∃ c : ℂ,
      filteredToDeRhamCohomology curveVariety 1 1 alpha =
        c • filteredToDeRhamCohomology curveVariety 1 1
          curveTopFilteredClass := by
  obtain ⟨c, hα⟩ := exists_curveFilteredClass_eq_scalarMap alpha
  refine ⟨c, ?_⟩
  rw [hα]
  rw [deRham_complex_smul_eq]
  unfold filteredToDeRhamCohomology
  rw [← hypercohomologyMap_comp_apply,
    ← hypercohomologyMap_comp_apply]
  rw [hodgeFilteredDeRhamComplexScalar_comp_inclusion]

/-- The range defining `F¹H¹` on the explicit curve is the span of the
explicit invariant-differential class. -/
theorem curve_firstHodgeFiltration_eq_span
    :
    hodgeFiltration curveVariety 1 1 =
      (Submodule.span ℂ
        {filteredToDeRhamCohomology curveVariety 1 1
          curveTopFilteredClass}).toAddSubgroup := by
  ext x
  constructor
  · rintro ⟨alpha, rfl⟩
    obtain ⟨c, hc⟩ := exists_curveFilteredToDeRham_eq_smul alpha
    rw [hc]
    exact Submodule.smul_mem _ c
      (Submodule.subset_span (Set.mem_singleton _))
  · intro hx
    change x ∈ Submodule.span ℂ
      {filteredToDeRhamCohomology curveVariety 1 1
        curveTopFilteredClass} at hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    refine ⟨hypercohomologyMap curveVariety
      (hodgeFilteredDeRhamComplexScalar curveVariety 1 c) 1
      curveTopFilteredClass, ?_⟩
    rw [deRham_complex_smul_eq]
    unfold filteredToDeRhamCohomology
    rw [← hypercohomologyMap_comp_apply,
      ← hypercohomologyMap_comp_apply]
    rw [hodgeFilteredDeRhamComplexScalar_comp_inclusion]

end AlgebraicGeometry.ExplicitEllipticCandidate
