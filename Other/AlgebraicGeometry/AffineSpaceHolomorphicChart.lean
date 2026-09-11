/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AffineSpaceSmooth
public import Other.AlgebraicGeometry.PolynomialGrowthLiouville
public import Other.AlgebraicGeometry.ComplexAnalyticMaps

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Affine coordinates are a holomorphic chart on complex affine space

The repository's complex-manifold structure on `ComplexPoint X` is built from *étale* algebraic
coordinates chosen at each point.  For affine space there is a competing, tautological
identification `affineSpaceEquiv : ComplexPoint 𝔸ᴺ ≃ ℂᴺ`, and the two must be compared before any
explicit coordinate computation (such as the homogeneous charts of `ℙᴺ`) can be used with
`holomorphicFunctionSheaf`.

This file proves that evaluation of an arbitrary regular section in affine coordinates is
analytic — the global case is `evaluate_affineSpaceEquiv_symm_top` plus analyticity of polynomial
evaluation, and the general case follows by shrinking to a principal open and writing the section
as a quotient of global sections — and deduces that `affineSpaceEquiv.symm` is holomorphic.  Since
its inverse is holomorphic as well (its components are evaluations of regular functions), affine
coordinates are a holomorphic chart.
-/

@[expose] public noncomputable section

open CategoryTheory Filter Topology TopologicalSpace AlgebraicGeometry
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

open Point

/-- Complex affine space as an object over `Spec ℂ`. -/
abbrev affineSpaceOver (N : ℕ) : Over (Spec ↧ℂ) :=
  Over.mk (complexAffineSpace (Fin N) ↘ Spec ↧ℂ)

/-- Evaluation of a global regular function in affine coordinates is analytic: it is the
evaluation of the corresponding polynomial. -/
theorem analyticAt_evaluate_top_affineSpaceEquiv_symm {N : ℕ}
    (s : Γ(complexAffineSpace (Fin N), ⊤)) (w : Fin N → ℂ) :
    AnalyticAt ℂ
      (fun v : Fin N → ℂ ↦ evaluate ⊤ s ((affineSpaceEquiv (Fin N)).symm v)) w := by
  have h : (fun v : Fin N → ℂ ↦ evaluate ⊤ s ((affineSpaceEquiv (Fin N)).symm v)) =
      fun v : Fin N → ℂ ↦ MvPolynomial.eval v (affineGlobalPolynomial s) :=
    funext fun v ↦ evaluate_affineSpaceEquiv_symm_top s v
  rw [h]
  exact Complex.PolynomialGrowth.analyticOnNhd_eval (affineGlobalPolynomial s) w
    (Set.mem_univ w)

/-- Evaluation of an arbitrary regular section in affine coordinates is analytic wherever it is
defined. -/
theorem analyticAt_evaluate_affineSpaceEquiv_symm {N : ℕ}
    (V : (complexAffineSpace (Fin N)).Opens) (s : Γ(complexAffineSpace (Fin N), V))
    {w : Fin N → ℂ} (hw : (affineSpaceEquiv (Fin N)).symm w ∈ overOpen V) :
    AnalyticAt ℂ
      (fun v : Fin N → ℂ ↦ evaluate V s ((affineSpaceEquiv (Fin N)).symm v)) w := by
  obtain ⟨f, hfV, hwf⟩ :=
    (isAffineOpen_top (complexAffineSpace (Fin N))).exists_basicOpen_le
      ⟨((affineSpaceEquiv (Fin N)).symm w).underlying, hw⟩ trivial
  let t : Γ(complexAffineSpace (Fin N), (complexAffineSpace (Fin N)).basicOpen f) :=
    (complexAffineSpace (Fin N)).presheaf.map (homOfLE hfV).op s
  have : IsAffine (affineSpaceOver N).left :=
    inferInstanceAs (IsAffine (complexAffineSpace (Fin N)))
  obtain ⟨k, a, h⟩ :=
    exists_evaluate_affine_basicOpen_eq_div (X := affineSpaceOver N) f t
  have hfzero : evaluate ⊤ f ((affineSpaceEquiv (Fin N)).symm w) ≠ 0 :=
    (mem_overOpen_basicOpen_iff_evaluate_ne_zero
      (X := affineSpaceOver N) (U := ⊤) f _ trivial).mp hwf
  have hrat := (analyticAt_evaluate_top_affineSpaceEquiv_symm a w).div
    ((analyticAt_evaluate_top_affineSpaceEquiv_symm f w).pow k) (pow_ne_zero k hfzero)
  refine hrat.congr ?_
  have heventually : (affineSpaceEquiv (Fin N)).symm ⁻¹'
      overOpen ((complexAffineSpace (Fin N)).basicOpen f) ∈ 𝓝 w :=
    (isOpen_affineSpaceEquiv_symm_preimage_overOpen_basicOpen f).mem_nhds hwf
  filter_upwards [heventually] with v hv
  simp only [Pi.div_apply, Pi.pow_apply]
  exact ((Point.evaluate_res (X := affineSpaceOver N) hfV s _ hv).trans (h _ hv)).symm

/-! ### Affine coordinates are a holomorphic chart -/

/-- In the repository's complex-manifold structure, the inverse of the affine coordinate
identification is holomorphic. -/
theorem contMDiff_affineSpaceEquiv_symm (N : ℕ) :
    ContMDiff 𝓘(ℂ, Fin N → ℂ) 𝓘(ℂ, Fin N → ℂ) ω
      ((affineSpaceEquiv (Fin N)).symm :
        (Fin N → ℂ) → ComplexPoint (affineSpaceOver N)) := by
  intro w
  set A := affineSpaceOver N with hA
  set z : ComplexPoint A := (affineSpaceEquiv (Fin N)).symm w with hzdef
  have hz : z ∈ (localChart A N z).source := mem_localChart_source A N z
  have hcont : @ContinuousAt (Fin N → ℂ) (ComplexPoint A) inferInstance
      Point.analyticTopology (affineSpaceEquiv (Fin N)).symm w :=
    (continuous_affineSpaceEquiv_symm (Fin N)).continuousAt
  have heventually : (affineSpaceEquiv (Fin N)).symm ⁻¹' (localChart A N z).source ∈ 𝓝 w :=
    hcont ((localChart A N z).open_source.mem_nhds hz)
  have ha : AnalyticAt ℂ
      (fun v : Fin N → ℂ ↦ localChart A N z ((affineSpaceEquiv (Fin N)).symm v)) w := by
    refine AnalyticAt.pi fun i ↦ ?_
    have hmem := mem_coordinateNeighborhood_of_mem_localChart_source A N z z hz
    have hV : z ∈ overOpen (localEtaleCoordinates A N z).ambientCoordinateOpen := by
      simpa only [LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top]
        using hmem
    have hi := analyticAt_evaluate_affineSpaceEquiv_symm
      (localEtaleCoordinates A N z).ambientCoordinateOpen
      ((localEtaleCoordinates A N z).ambientCoordinateSection i) hV
    refine hi.congr ?_
    filter_upwards [heventually] with v hv
    exact (localChart_apply_component_eq_evaluate A N z _ hv i).symm
  rw [contMDiffAt_iff_of_mem_source (I := 𝓘(ℂ, Fin N → ℂ)) (I' := 𝓘(ℂ, Fin N → ℂ))
    (x := w) (y := z) (mem_chart_source _ w) hz]
  refine ⟨hcont, ?_⟩
  have htargetChart : chartAt (Fin N → ℂ) z = localChart A N z := rfl
  simpa [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, chartAt_self_eq, Function.comp_def, htargetChart] using
      ha.contDiffAt.contDiffWithinAt

end AlgebraicGeometry.ComplexPoint
