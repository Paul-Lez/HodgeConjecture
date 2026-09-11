/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveTwistChartFrames
public import Other.AlgebraicGeometry.AnalytificationGenerates

/-!
# Analytic frames for the projective twists, and chart multipliers

(G2) gives an algebraic generating section of `𝒪(−n)` on each standard basic open `D₊(Xᵢ)`.
`analytificationGenerates` turns it into a generating section of `𝒪(−n)^an` on the corresponding
analytic open, which is the `i`-th homogeneous chart.  Consequently a morphism of analytified
twists is, on each chart, multiplication by a unique holomorphic function: the first step of the
chart dictionary needed for (G3).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexProjectiveSpace

open ComplexPoint

attribute [local instance] MvPolynomial.gradedAlgebra

variable (N n : ℕ) (i : Fin (N + 1))

/-- The algebraic frame of `𝒪(−n)` on the `i`-th standard basic open of `ℙᴺ`. -/
def algebraicChartFrame :
    Γ(ComplexPoint.ProjectiveTwist.algebraic (Other.ProjectiveChart.projectiveSpaceOver N)
        (Other.ProjectiveChart.projPresentation N) n,
      projectiveSpaceBasicOpen N (MvPolynomial.X i)) :=
  Scheme.Modules.resSection _ (projectiveSpaceBasicOpen_le_twistTrivializations N n i)
    (Scheme.Modules.unitIsoSection
      ((TauCeti.SheafOfModules.freePUnitIsoUnit _).symm ≪≫ (twistTrivializations N n).iso i))

theorem generates_algebraicChartFrame :
    Scheme.Modules.Generates (algebraicChartFrame N n i) :=
  (Scheme.Modules.generates_unitIsoSection _).restrict _

/-- The `i`-th homogeneous chart, as an open of the analytification of `ℙᴺ`. -/
def chartOpen : Opens (TopCat.of (ComplexPoint
    (Other.ProjectiveChart.projectiveSpaceOver N))) :=
  ComplexPoint.analyticOpen (Other.ProjectiveChart.projectiveSpaceOver N)
    (projectiveSpaceBasicOpen N (MvPolynomial.X i))

@[simp]
theorem coe_chartOpen :
    (chartOpen N i : Set (ComplexPoint (Other.ProjectiveChart.projectiveSpaceOver N))) =
      complexPointChartSet i :=
  overOpen_projectiveSpaceBasicOpen_X N i

/-- The analytic frame of `𝒪(−n)^an` on the `i`-th homogeneous chart. -/
def analyticChartFrame :
    (ComplexPoint.ProjectiveTwist.analytic (Other.ProjectiveChart.projectiveSpaceOver N) N
      (Other.ProjectiveChart.projPresentation N) n).val.obj (op (chartOpen N i)) :=
  ComplexPoint.analyticSection (Other.ProjectiveChart.projectiveSpaceOver N) N _ _
    (algebraicChartFrame N n i)

/-- **The analytic frame generates.**  `𝒪(−n)^an` is trivialised on each standard homogeneous
chart of `ℙᴺ(ℂ)^an`. -/
theorem holomorphicGenerates_analyticChartFrame :
    ComplexPoint.HolomorphicGenerates
      (M := ComplexPoint.ProjectiveTwist.analytic
        (Other.ProjectiveChart.projectiveSpaceOver N) N
        (Other.ProjectiveChart.projPresentation N) n)
      (analyticChartFrame N n i) :=
  ComplexPoint.analytificationGenerates (Other.ProjectiveChart.projectiveSpaceOver N) N
    _ _ _ (generates_algebraicChartFrame N n i)

/-- **Chart multipliers.**  A morphism of analytified twists on `ℙᴺ` is, on each standard chart,
multiplication by a unique holomorphic function. -/
theorem existsUnique_chartMultiplier (a b : ℕ)
    (φ : ComplexPoint.ProjectiveTwist.analytic (Other.ProjectiveChart.projectiveSpaceOver N) N
        (Other.ProjectiveChart.projPresentation N) a ⟶
      ComplexPoint.ProjectiveTwist.analytic (Other.ProjectiveChart.projectiveSpaceOver N) N
        (Other.ProjectiveChart.projPresentation N) b) :
    ∃! h : (holomorphicRingSheaf (Other.ProjectiveChart.projectiveSpaceOver N) N).obj.obj
        (op (chartOpen N i)),
      h • analyticChartFrame N b i = φ.val.app (op (chartOpen N i)) (analyticChartFrame N a i) := by
  have hb := holomorphicGenerates_analyticChartFrame N b i
  obtain ⟨h, hh⟩ := hb.bijective.surjective
    (φ.val.app (op (chartOpen N i)) (analyticChartFrame N a i))
  refine ⟨h, hh, fun h' hh' ↦ hb.bijective.injective ?_⟩
  exact hh'.trans hh.symm

/-! ### Reading chart sections as entire functions on `ℂᴺ` -/

/-- The homogeneous chart map, corestricted to the chart open. -/
def chartPointIn : (Fin N → ℂ) → chartOpen N i := fun z ↦
  ⟨projectivizationToComplexPoint (chartPoint i z), by
    have hmem : projectivizationToComplexPoint (chartPoint i z) ∈
        complexPointChartSet i := ⟨chartPoint i z, ⟨z, rfl⟩, rfl⟩
    rwa [← coe_chartOpen N i] at hmem⟩

@[simp]
theorem coe_chartPointIn (z : Fin N → ℂ) :
    (chartPointIn N i z : ComplexPoint (Other.ProjectiveChart.projectiveSpaceOver N)) =
      projectivizationToComplexPoint (chartPoint i z) := rfl

theorem contMDiff_chartPointIn :
    ContMDiff 𝓘(ℂ, Fin N → ℂ) 𝓘(ℂ, Fin N → ℂ) ω (chartPointIn N i) := by
  intro z
  have h := contMDiff_projectivizationToComplexPoint_chartPoint N i z
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (chartPointIn N i) Set.univ z).mp h

/-- **Chart sections are entire functions.**  A holomorphic function on the `i`-th homogeneous
chart of `ℙᴺ(ℂ)^an` becomes, in the chart coordinates, an entire function on `ℂᴺ`. -/
theorem analyticOnNhd_comp_chartPointIn {g : chartOpen N i → ℂ}
    (hg : ContMDiff 𝓘(ℂ, Fin N → ℂ) 𝓘(ℂ, ℂ) ω g) :
    AnalyticOnNhd ℂ (fun z : Fin N → ℂ ↦ g (chartPointIn N i z)) Set.univ := by
  have hcomp : ContMDiff 𝓘(ℂ, Fin N → ℂ) 𝓘(ℂ, ℂ) ω fun z ↦ g (chartPointIn N i z) :=
    hg.comp (contMDiff_chartPointIn N i)
  rw [← contDiff_omega_iff_analyticOnNhd, ← contMDiff_iff_contDiff]
  exact hcomp

/-- The same, for a bundled `C^ω` section of the holomorphic function sheaf on the chart. -/
theorem analyticOnNhd_contMDiffMap_comp_chartPointIn
    (g : ContMDiffMap 𝓘(ℂ, Fin N → ℂ) 𝓘(ℂ, ℂ) (chartOpen N i) ℂ ω) :
    AnalyticOnNhd ℂ (fun z : Fin N → ℂ ↦ g (chartPointIn N i z)) Set.univ :=
  analyticOnNhd_comp_chartPointIn N i g.contMDiff

end AlgebraicGeometry.ComplexProjectiveSpace
