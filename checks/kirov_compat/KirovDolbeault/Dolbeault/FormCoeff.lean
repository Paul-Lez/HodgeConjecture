/-
  The canonical-chart coefficient of a holomorphic 1-form, and the local residue of `ω·g`
  (Forster §17 building block, on the EASY-half / injectivity path of the D=0 Serre pairing).

  A holomorphic 1-form `α`, in the canonical chart `chartAt ℂ a`, reads `α = coeffAt α a (z) · dz`
  with `coeffAt α a` **analytic** — this is exactly `Montel.localRep` + its analyticity bridge
  `localRep_analyticOn_chartTarget` (already proven complete in the Montel development, so we reuse
  it rather than re-deriving the ω-smoothness ⟹ ℂ-analyticity manifold argument).

  On top of it we define the **local residue** `formFnResidue α g a` = the residue at `a` of the
  meromorphic 1-form `α·g` (holomorphic form times a function `g`), computed in the canonical chart,
  and prove it vanishes when `g`'s chart-pullback is holomorphic at `a` (so `α·g` has no pole there).
  Computing in the canonical chart is the trick that makes Forster's cover-independence of `Res_a`
  follow from `Res(holo)=0` alone, sidestepping the chart-independence change-of-variables lemma.

  Everything here is complete and depends on no unproved lemma.
-/
import KirovDolbeault.Montel.Compactness
import KirovDolbeault.Genus
import KirovDolbeault.Dolbeault.Residue

open scoped Manifold ContDiff Topology
open Complex Metric

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The coefficient of a holomorphic 1-form `α` read in the **canonical chart** at `a`: near `a`,
`α = coeffAt α a (z) · dz` in the coordinate `z = chartAt ℂ a`.  It is `Montel.localRep α a`
transported to the chart target; analytic by `coeffAt_analyticOn`. -/
noncomputable def coeffAt (α : HolomorphicOneForms X) (a : X) : ℂ → ℂ :=
  fun z => Jacobians.Montel.localRep α a ((chartAt ℂ a).symm z)

/-- `coeffAt α a` is analytic on the chart target (reuse of the Montel analyticity bridge). -/
theorem coeffAt_analyticOn (α : HolomorphicOneForms X) (a : X) :
    AnalyticOn ℂ (coeffAt α a) (chartAt ℂ a).target :=
  Jacobians.Montel.localRep_analyticOn_chartTarget α a

/-- `coeffAt α a` is analytic at the chart image of any point of the chart source. -/
theorem coeffAt_analyticAt (α : HolomorphicOneForms X) (a : X) {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) :
    AnalyticAt ℂ (coeffAt α a) z :=
  (coeffAt_analyticOn α a).analyticAt ((chartAt ℂ a).open_target.mem_nhds hz)

/-- The residue at `a` of the meromorphic 1-form `α·g` (a holomorphic form `α` times a function
`g : X → ℂ`), computed in the canonical chart: there `α·g = (coeffAt α a · (g ∘ chart.symm)) · dz`,
so the residue is `resAt` of that coefficient at the chart image of `a`. -/
noncomputable def formFnResidue (α : HolomorphicOneForms X) (g : X → ℂ) (a : X) : ℂ :=
  resAt (fun z => coeffAt α a z * g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)

/-- **`Res(holo) = 0`.**  If `g`'s chart-pullback is holomorphic at `a` (so `α·g` is holomorphic at
`a`, no pole), the local residue vanishes. -/
theorem formFnResidue_eq_zero_of_analyticAt (α : HolomorphicOneForms X) (g : X → ℂ) (a : X)
    (hg : AnalyticAt ℂ (fun z => g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)) :
    formFnResidue α g a = 0 := by
  have hmem : (chartAt ℂ a) a ∈ (chartAt ℂ a).target := (chartAt ℂ a).map_source (mem_chart_source ℂ a)
  -- the integrand is analytic at the chart image of `a`
  have hprod : AnalyticAt ℂ (fun z => coeffAt α a z * g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a) :=
    (coeffAt_analyticAt α a hmem).mul hg
  -- analytic at a point ⟹ holomorphic on a small ball ⟹ residue 0
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ z ∈ ball ((chartAt ℂ a) a) ρ,
      DifferentiableAt ℂ (fun z => coeffAt α a z * g ((chartAt ℂ a).symm z)) z := by
    have hev := hprod.eventually_analyticAt
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hball⟩ := hev
    exact ⟨ε, hε, fun z hz => (hball (mem_ball.mp hz)).differentiableAt⟩
  exact resAt_eq_zero_of_differentiableOn_ball hρ hball

/-- **A nonzero holomorphic 1-form has a nonzero coefficient at its own chart centre.**  Needed to
place the `dz/z` pole in Forster's §17.6 injectivity witness.  (The coefficient `localRep α a a` is
`α` paired with the unit coordinate tangent at `a`; that tangent spans the 1-dim fibre, so if every
such pairing vanished, `α` would be the zero section.) -/
theorem exists_localRep_self_ne_zero (α : HolomorphicOneForms X) (hα : α ≠ 0) :
    ∃ a : X, Jacobians.Montel.localRep α a a ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hα
  refine ContMDiffSection.ext (fun x => ?_)
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x with he
  have hxbase : x ∈ e.baseSet := mem_baseSet_trivializationAt ℂ _ x
  have hz : α.toFun x = 0 := by
    refine ContinuousLinearMap.ext (fun v => ?_)
    rw [ContinuousLinearMap.zero_apply]
    have hv : e.symmL ℂ x (e.continuousLinearMapAt ℂ x v) = v :=
      e.symmL_continuousLinearMapAt hxbase v
    set c := e.continuousLinearMapAt ℂ x v with hc
    have hsm : e.symmL ℂ x c = c • e.symmL ℂ x 1 := by
      have h2 := (e.symmL ℂ x).map_smul c (1 : ℂ)
      rwa [smul_eq_mul, mul_one] at h2
    calc α.toFun x v = α.toFun x (e.symmL ℂ x c) := by rw [hv]
      _ = α.toFun x (c • e.symmL ℂ x 1) := by rw [hsm]
      _ = c • α.toFun x (e.symmL ℂ x 1) := by rw [(α.toFun x).map_smul]
      _ = c • Jacobians.Montel.localRep α x x := rfl
      _ = 0 := by rw [hcon x, smul_zero]
  exact hz

/-- The coefficient at the chart centre is the centred local representative:
`coeffAt α a (chartAt a a) = localRep α a a`. -/
theorem coeffAt_chartCenter (α : HolomorphicOneForms X) (a : X) :
    coeffAt α a ((chartAt ℂ a) a) = Jacobians.Montel.localRep α a a := by
  simp only [coeffAt]
  rw [(chartAt ℂ a).left_inv (mem_chart_source ℂ a)]

/-- **Forster §17.6's injectivity witness.**  At a point `a` where the holomorphic form `α` has a
nonzero coefficient, there is a function `g` (the local principal part `1/(z·coeff)`) such that the
meromorphic 1-form `α·g` has a **simple pole at `a` with residue `1`**.  Combined with
`exists_localRep_self_ne_zero` (such an `a` exists for any `α ≠ 0`), this is the local heart of
`ι₀ : H⁰(X,Ω) → H¹(X,𝒪)*` being injective. -/
theorem exists_formFnResidue_eq_one_of_localRep_ne_zero (α : HolomorphicOneForms X) (a : X)
    (ha : Jacobians.Montel.localRep α a a ≠ 0) :
    ∃ g : X → ℂ, formFnResidue α g a = 1 := by
  set z₀ := (chartAt ℂ a) a with hz₀
  refine ⟨fun x => ((chartAt ℂ a) x - z₀)⁻¹ * (coeffAt α a ((chartAt ℂ a) x))⁻¹, ?_⟩
  unfold formFnResidue
  apply resAt_eq_of_eventuallyEq_sub_inv
  have htarget : (chartAt ℂ a).target ∈ 𝓝 z₀ :=
    (chartAt ℂ a).open_target.mem_nhds ((chartAt ℂ a).map_source (mem_chart_source ℂ a))
  have hcoeff_z0 : coeffAt α a z₀ ≠ 0 := by rw [coeffAt_chartCenter]; exact ha
  have hne : ∀ᶠ z in 𝓝 z₀, coeffAt α a z ≠ 0 :=
    ((coeffAt_analyticAt α a ((chartAt ℂ a).map_source (mem_chart_source ℂ a))).continuousAt).eventually_ne
      hcoeff_z0
  filter_upwards [nhdsWithin_le_nhds htarget, nhdsWithin_le_nhds hne, self_mem_nhdsWithin]
    with z hztarget hzne hz0
  have hz0' : z ≠ z₀ := by rwa [Set.mem_compl_iff, Set.mem_singleton_iff] at hz0
  have hsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hz0'
  -- `g ∘ chart.symm` at `z`, using the chart right-inverse on the target
  simp only [(chartAt ℂ a).right_inv hztarget]
  rw [one_mul, mul_left_comm, mul_inv_cancel₀ hzne, mul_one]

end Jacobians.Dolbeault
