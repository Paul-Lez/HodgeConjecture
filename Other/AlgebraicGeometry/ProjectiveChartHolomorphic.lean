/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AffineSpaceHolomorphicChart
public import Other.AlgebraicGeometry.ProjectiveAnalytificationCharts
public import Other.AlgebraicGeometry.ProjectiveSpaceSmooth
public import Mathlib.Geometry.Manifold.ContMDiffMap

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# The homogeneous charts of `ℙᴺ(ℂ)` are holomorphic

`ProjectiveAnalytificationCharts.lean` produces the standard affine charts of `ℙᴺ(ℂ)^an` as
*homeomorphisms* `ℂᴺ ≃ₜ {x_i ≠ 0}`.  This file upgrades the chart map to a holomorphic map for the
repository's complex-manifold structure: it factors as

  `ℂᴺ → ℂ^{N+1} ≅ ComplexPoint 𝔸^{N+1} → ComplexPoint ℙᴺ`,

where the first map is the affine slice `x_i = 1` (analytic), the second is the affine coordinate
identification (holomorphic by `contMDiff_affineSpaceEquiv_symm`), and the third is induced by the
scheme morphism `chartAffineToProjectiveSpace i`, hence holomorphic by `contMDiff_analyticMap`.

Consequently a holomorphic function on `ℙᴺ(ℂ)^an` — a section of `holomorphicFunctionSheaf` —
pulls back along a homogeneous chart to an entire function on `ℂᴺ`, which is what
`Complex.PolynomialGrowth` needs.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexProjectiveSpace

/-- The affine slice `x_i = 1` is an analytic map `ℂᴺ → ℂ^{N+1}`. -/
theorem contMDiff_insertNth_one (N : ℕ) (i : Fin (N + 1)) :
    ContMDiff 𝓘(ℂ, Fin N → ℂ) 𝓘(ℂ, Fin (N + 1) → ℂ) ω
      fun z : Fin N → ℂ ↦ (i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) := by
  rw [contMDiff_iff_contDiff, contDiff_omega_iff_analyticOnNhd]
  intro x _
  refine AnalyticAt.pi fun k ↦ ?_
  refine Fin.succAboveCases i ?_ ?_ k
  · simpa only [Fin.insertNth_apply_same] using analyticAt_const (v := (1 : ℂ)) (x := x)
  · intro j
    have h := ((ContinuousLinearMap.proj j : (Fin N → ℂ) →L[ℂ] ℂ)).analyticAt x
    simp only [Fin.insertNth_apply_succAbove]
    exact h

/-- The homogeneous chart map `ℂᴺ → ℙᴺ(ℂ)^an` is holomorphic. -/
theorem contMDiff_projectivizationToComplexPoint_chartPoint (N : ℕ) (i : Fin (N + 1)) :
    ContMDiff 𝓘(ℂ, Fin N → ℂ) 𝓘(ℂ, Fin N → ℂ) ω
      fun z : Fin N → ℂ ↦ projectivizationToComplexPoint (chartPoint i z) := by
  have hmap := ComplexPoint.contMDiff_analyticMap
    (ComplexPoint.affineSpaceOver (N + 1))
    (Over.mk (ProjectiveSpace.toBase (Fin (N + 1)) (Spec ↧ℂ)))
    (Over.homMk (chartAffineToProjectiveSpace i) (chartAffineToProjectiveSpace_over i))
    (N + 1) N
  have hcomp := hmap.comp
    ((ComplexPoint.contMDiff_affineSpaceEquiv_symm (N + 1)).comp
      (contMDiff_insertNth_one N i))
  refine hcomp.congr fun z ↦ ?_
  have hne : (i.insertNth (1 : ℂ) z : CoordinateSpace N) i ≠ 0 := by
    simp [Fin.insertNth_apply_same]
  have hratios : vectorChartRatios i ⟨i.insertNth (1 : ℂ) z, hne⟩ = i.insertNth (1 : ℂ) z := by
    simp [vectorChartRatios, Fin.insertNth_apply_same]
  have h := chartVectorToComplexPoint_eq i ⟨i.insertNth (1 : ℂ) z, hne⟩
  rw [vectorChartToAffinePoint, Function.comp_apply, hratios] at h
  rw [chartPoint, projectivizationToComplexPoint_mk]
  exact h.symm

/-- **The bridge to the polynomial-growth Liouville theorem.**  A holomorphic function on
`ℙᴺ(ℂ)^an` pulls back along a homogeneous chart to an entire function on `ℂᴺ`. -/
theorem analyticOnNhd_comp_chartPoint (N : ℕ) (i : Fin (N + 1))
    {g : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (N + 1)) (Spec ↧ℂ))) → ℂ}
    (hg : ContMDiff 𝓘(ℂ, Fin N → ℂ) 𝓘(ℂ, ℂ) ω g) :
    AnalyticOnNhd ℂ
      (fun z : Fin N → ℂ ↦ g (projectivizationToComplexPoint (chartPoint i z))) Set.univ := by
  have hcomp : ContMDiff 𝓘(ℂ, Fin N → ℂ) 𝓘(ℂ, ℂ) ω
      fun z : Fin N → ℂ ↦ g (projectivizationToComplexPoint (chartPoint i z)) :=
    hg.comp (contMDiff_projectivizationToComplexPoint_chartPoint N i)
  rw [← contDiff_omega_iff_analyticOnNhd, ← contMDiff_iff_contDiff]
  exact hcomp

/-- The same statement for a bundled `C^ω` map, i.e. for a section of the repository's
holomorphic function sheaf on all of `ℙᴺ(ℂ)^an`. -/
theorem analyticOnNhd_contMDiffMap_comp_chartPoint (N : ℕ) (i : Fin (N + 1))
    (g : ContMDiffMap 𝓘(ℂ, Fin N → ℂ) 𝓘(ℂ, ℂ)
      (ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (N + 1)) (Spec ↧ℂ)))) ℂ ω) :
    AnalyticOnNhd ℂ
      (fun z : Fin N → ℂ ↦ g (projectivizationToComplexPoint (chartPoint i z))) Set.univ :=
  analyticOnNhd_comp_chartPoint N i g.contMDiff

/-- Projective space is projective over its base, via the identity closed immersion.  This makes
the compactness, Hausdorffness and path-connectedness results for analytifications of projective
schemes available on `ℙᴺ(ℂ)` itself. -/
def selfPresentation (N : ℕ) :
    ProjectiveSpace.Presentation (ProjectiveSpace.toBase (Fin (N + 1)) (Spec ↧ℂ)) where
  ambientDimension := N
  immersion := 𝟙 _
  isClosedImmersion := inferInstance
  immersion_toBase := Category.id_comp _

instance isProjective_projectiveSpace (N : ℕ) :
    IsProjective (Over.mk (ProjectiveSpace.toBase (Fin (N + 1)) (Spec ↧ℂ))).hom :=
  ⟨⟨selfPresentation N⟩⟩

/-- **The `H⁰` bridge.**  A holomorphic function on `ℙᴺ(ℂ)^an` whose pullback to a homogeneous
chart has polynomial growth of order `m` is, on that chart, a polynomial of total degree at most
`m`. -/
theorem exists_mvPolynomial_of_growth (N : ℕ) (i : Fin (N + 1)) {m : ℕ} {C : ℝ}
    {g : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (N + 1)) (Spec ↧ℂ))) → ℂ}
    (hg : ContMDiff 𝓘(ℂ, Fin N → ℂ) 𝓘(ℂ, ℂ) ω g)
    (hC : ∀ z : Fin N → ℂ,
      ‖g (projectivizationToComplexPoint (chartPoint i z))‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ P : MvPolynomial (Fin N) ℂ, P.totalDegree ≤ m ∧
      ∀ z, MvPolynomial.eval z P = g (projectivizationToComplexPoint (chartPoint i z)) :=
  Complex.PolynomialGrowth.exists_mvPolynomial_eq_of_growth
    (analyticOnNhd_comp_chartPoint N i hg) hC

end AlgebraicGeometry.ComplexProjectiveSpace
