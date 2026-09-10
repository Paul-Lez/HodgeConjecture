/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceCoherentFromMoving

/-!
# The moving-fibre coherence datum from a sheet system (Gate A, §VIII.3 — global index bijection)

`Jacobians.Dolbeault.FormTraceMovingFibre` proved the §VIII.3 monodromy heart: a `MovingCoherenceDatum`
yields the local self-coherence of the geometric trace, and is constructible from a
*continuously-varying index bijection* alone (`MovingCoherenceDatum.ofBijection`).  All germ /
`dz`-Jacobian content is discharged there; the residual is the **index bijection + section
identification + chart-pullback differentiability**.

This file discharges the *mechanical* half of that residual — the differentiability side-conditions —
by feeding the proved branched-cover sheet machinery (`Jacobians.LocalSheetSystem`, Forster §4.22) into
`MovingCoherenceDatum.ofBijection`.  The continuously-varying sections are the sheets `S.sheet i` of a
`LocalSheetSystem` for `f.holoRepr` off the critical set, which are `C^ω` two-sided local inverses; the
chart-transition differentiability is the analytic chart change of the `C^ω` atlas (proved inline,
`transition_analyticAt_overlap`); and the section identification (planar sheet ≈ manifold-section
chart-pullback) is the proved `FormTraceSheet.fibreTrace_sheet_eventuallyEq`.

What remains, after this file, is the *geometric* half: that the global selection `Φ` actually
**re-selects the moving fibre** — near each base value, `(Φ b').xs` enumerates the sheet values
`S.sheet · b'` via an index bijection `e : (Φ b').ι ≃ D.ι`.  That is the genuine §VIII.3 index
bijection (the branched cover's sheets permute continuously) and is carried as the single hypothesis
`hsel` of the constructor.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `transition_analyticAt_overlap` — the chart transition `chartAt z ∘ (chartAt y).symm` is analytic at
  any overlap point (inline, no heavy Čech import).
* `MovingCoherenceDatum.ofSheetSystem` — build a `MovingCoherenceDatum` at a base value `b₀` from a
  `LocalSheetSystem` for `f.holoRepr`, a reference fibre `D` enumerated by the sheets, and the diagonal
  re-selection agreement `hsel`.  Discharges every differentiability side-condition of
  `MovingCoherenceDatum.ofBijection` from the sheet smoothness + the analytic chart change.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4.22 (local sheet systems), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceMovingFibre

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormTraceGlobal
  Jacobians.Dolbeault.FormTraceSheet Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The analytic chart change at an overlap point (inline)

The chart transition `chartAt z ∘ (chartAt y).symm` is analytic at `chartAt y x` for any `x` in the
overlap of the two chart sources — the `C^ω`-atlas chart change.  This is the same statement as
`Jacobians.Dolbeault.transition_analyticAt_of_mem`, reproved inline to avoid importing the heavy Čech
machinery.  It supplies the chart-transition differentiability fields of `hbij`. -/

/-- **Chart transition analytic at an overlap point.**  For `x` in both chart sources `chartAt y` and
`chartAt z`, the transition `chartAt z ∘ (chartAt y).symm` is `AnalyticAt ℂ` at `chartAt y x`.  Chart
and inverse-chart are `C^ω` (`contMDiffOn_chart`/`contMDiffOn_chart_symm`); the composition is `C^ω`,
and `C^ω` ⇒ analytic. -/
theorem transition_analyticAt_overlap {y z x : X}
    (hxy : x ∈ (chartAt (H := ℂ) y).source) (hxz : x ∈ (chartAt (H := ℂ) z).source) :
    AnalyticAt ℂ ((chartAt (H := ℂ) z) ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) x) := by
  have hw_tgt : (chartAt (H := ℂ) y) x ∈ (chartAt (H := ℂ) y).target :=
    (chartAt (H := ℂ) y).map_source hxy
  have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) x) :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := y)) _ hw_tgt).contMDiffAt
      ((chartAt (H := ℂ) y).open_target.mem_nhds hw_tgt)
  have hey : (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) x) = x :=
    (chartAt (H := ℂ) y).left_inv hxy
  have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) z)
      ((chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) x)) := by
    rw [hey]
    exact ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := z)) _ hxz).contMDiffAt
      ((chartAt (H := ℂ) z).open_source.mem_nhds hxz)
  exact (contMDiffAt_iff_contDiffAt.1
    (ContMDiffAt.comp (I' := 𝓘(ℂ)) ((chartAt (H := ℂ) y) x) h2 h1)).analyticAt

/-- **Chart transition differentiable at an overlap point.**  The `DifferentiableAt ℂ` corollary of
`transition_analyticAt_overlap`. -/
theorem transition_differentiableAt_overlap {y z x : X}
    (hxy : x ∈ (chartAt (H := ℂ) y).source) (hxz : x ∈ (chartAt (H := ℂ) z).source) :
    DifferentiableAt ℂ (fun w => (chartAt (H := ℂ) z) ((chartAt (H := ℂ) y).symm w))
      ((chartAt (H := ℂ) y) x) :=
  (transition_analyticAt_overlap hxy hxz).differentiableAt

/-! ### The own-chart pullback of a smooth section is differentiable

A section `s : ℂ → X` that is `MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ω` at `b'`, read in its *own* canonical
chart at `s b'`, gives a `DifferentiableAt ℂ` planar function `z ↦ chartAt (s b') (s z)`.  This is the
`writtenInExtChartAt`-unfolding for the trivial complex model (`extChartAt 𝓘(ℂ) p = chartAt ℂ p`, source
chart `= id`).  It supplies the `hsP_diff` field of `hbij` from sheet smoothness. -/

/-- **The own-chart pullback of a `ContMDiffAt` section is `DifferentiableAt ℂ`.**  If `s : ℂ → X` is
`ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` at `b'`, then `z ↦ (chartAt ℂ (s b')) (s z)` is `DifferentiableAt ℂ` at `b'`.
The canonical chart `chartAt ℂ (s b')` is `C^ω` at `s b'` (`contMDiffOn_chart`), so the composite
`chartAt (s b') ∘ s` is `C^ω` at `b'`; for `ℂ → ℂ` maps `C^ω = ContDiffAt ℂ ω` (`contMDiffAt_iff_contDiffAt`),
which is `DifferentiableAt`.  Supplies the `hsP_diff` field of `hbij` from sheet smoothness. -/
theorem differentiableAt_chart_pullback_section {s : ℂ → X} {b' : ℂ}
    (hs : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω s b') :
    DifferentiableAt ℂ (fun z => (chartAt ℂ (s b')) (s z)) b' := by
  -- The chart at `s b'` is `C^ω` at `s b'` (its own source).
  have hchart : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ (s b')) (s b') :=
    ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := s b')) _ (mem_chart_source ℂ (s b'))).contMDiffAt
      ((chartAt ℂ (s b')).open_source.mem_nhds (mem_chart_source ℂ (s b')))
  -- Compose: `chartAt (s b') ∘ s` is `C^ω` at `b'`, a `ℂ → ℂ` map, hence `ContDiffAt ℂ ω`.
  have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (chartAt ℂ (s b')) (s z)) b' :=
    hchart.comp b' hs
  exact (contMDiffAt_iff_contDiffAt.1 hcomp).differentiableAt (by decide)

/-! ### The moving-fibre coherence datum from continuously-varying smooth sections

We now assemble `MovingCoherenceDatum.ofBijection` from continuously-varying *manifold* sections `sec :
D.ι → ℂ → X` of `f.holoRepr` (the sheets of a branched cover), discharging every differentiability
side-condition of `hbij` from section smoothness + the analytic chart change.  The single remaining
hypothesis is the genuine §VIII.3 index bijection: near `b₀`, the re-selected fibre `Φ b'` is enumerated
by the moving sections via a bijection `e : (Φ b').ι ≃ D.ι` with `(Φ b').xs i' = sec (e i') b'`.

The section-derivative match (the `hsheet_deriv` field) is *derived* here: by
`FormTraceSheet.fibreTrace_sheet_eventuallyEq`, the planar sheet of `fibreTrace ω₀ f (Φ b')` germ-equals
the chart-pullback `chart_{sec (e i') b'} ∘ sec (e i')` (both are right-inverses of the chart-pullback of
`f.holoRepr` through `(Φ b').xs i' = sec (e i') b'`), so their derivatives agree. -/

/-- **A moving-fibre coherence datum from continuously-varying smooth sections.**  Let `D :
FibreRegularData g f b₀`, and `sec : D.ι → ℂ → X` a family of manifold sections of `f.holoRepr` through
`D`'s fibre points: `sec i b₀ = D.xs i`, each `sec i` is `C^ω` at `b₀`, and `f.holoRepr (sec i b') = b'`
on a neighbourhood of `b₀`.  Assume the **§VIII.3 index bijection**: for `b'` near `b₀`, the re-selected
fibre `Φ b'` is enumerated by the moving sections — there is `e : (Φ b').ι ≃ D.ι` with `(Φ b').xs i' =
sec (e i') b'` for all `i'`, and each `sec i b'` lies in `chart_{D.xs i}.source` (the moving sections
stay near the fibre points).  Then `Φ` has a `MovingCoherenceDatum` at `b₀` with fixed fibre `D`.

*All* the germ / `dz`-Jacobian / differentiability content is discharged: the section-derivative match
via `fibreTrace_sheet_eventuallyEq`, the chart-pullback differentiability via
`differentiableAt_chart_pullback_section`, and the chart transitions via `transition_analyticAt_overlap`.
The caller supplies only the geometric re-selection bijection. -/
noncomputable def MovingCoherenceDatum.ofSheetSections
    {Φ : (b : ℂ) → FibreRegularData g f b} {b₀ : ℂ}
    (D : FibreRegularData g f b₀) (sec : D.ι → ℂ → X)
    (hbase : ∀ i, sec i b₀ = D.xs i)
    (hsmooth : ∀ i, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (sec i) b₀)
    (hsec : ∀ i, ∀ᶠ b' in 𝓝 b₀, f.holoRepr (sec i b') = b')
    (hsel : ∀ᶠ b' in 𝓝 b₀, ∃ e : (Φ b').ι ≃ D.ι,
      (∀ i', (Φ b').xs i' = sec (e i') b') ∧
      (∀ i, sec i b' ∈ (chartAt ℂ (D.xs i)).source)) :
    MovingCoherenceDatum ω₀ g f Φ b₀ := by
  refine MovingCoherenceDatum.ofBijection D sec hbase
    (fun i => (hsmooth i).continuousAt) hsec ?_
  -- The moving sections are `C^ω` (`ContMDiffAt` is an open condition) and are sections of `f.holoRepr`
  -- on a neighbourhood of `b₀`.  Bundle these per-`i` eventual facts with the re-selection `hsel`.
  have hsmooth_nhds : ∀ᶠ b' in 𝓝 b₀, ∀ i, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (sec i) b' :=
    eventually_all.mpr (fun i =>
      (contMDiffAt_iff_contMDiffAt_nhds (by decide : (ω : WithTop ℕ∞) ≠ ∞)).mp (hsmooth i))
  -- The section property holds eventually-eventually: near each `b'` close to `b₀`, `sec i` is a
  -- section of `f.holoRepr` on a neighbourhood of `b'` (the section set is open around `b₀`).
  have hsec_evev : ∀ᶠ b' in 𝓝 b₀, ∀ i, ∀ᶠ w in 𝓝 b', f.holoRepr (sec i w) = w :=
    eventually_all.mpr (fun i => eventually_eventually_nhds.mpr (hsec i))
  filter_upwards [hsel, hsmooth_nhds, hsec_evev] with b' hb'sel hb'smooth hb'sec
  obtain ⟨e, hxs, hmem⟩ := hb'sel
  -- For each fixed-frame index `i`, the chart-pullback `chart_{sec i b'} ∘ sec i` is the planar
  -- right-inverse of `φ_i = f.holoRepr ∘ chart_{D.xs i}.symm`... but we work in the chart at `sec i b'`.
  refine ⟨e, hxs, ?_, fun i => (hb'smooth i).continuousAt,
    fun i => differentiableAt_chart_pullback_section (hb'smooth i), hmem, ?_, ?_⟩
  · -- **The section-derivative match** (the `hsheet_deriv` field).  The planar sheet of `fibreTrace
    -- ω₀ f (Φ b')` germ-equals the chart-pullback `chart_{sec (e i') b'} ∘ sec (e i')`, so their
    -- derivatives at `b'` agree.
    intro i'
    -- The chart-pullback `s := chart_{sec (e i') b'} ∘ sec (e i')` is the right-inverse of the
    -- chart-pullback of `f.holoRepr` through `(Φ b').xs i' = sec (e i') b'`.
    obtain ⟨hrinv_base, hrinv_cont, hrinv_rinv⟩ :=
      chartPullback_section_rinv f (sec := sec (e i')) (b₀ := b') (x := sec (e i') b') rfl
        (hb'smooth (e i')).continuousAt (hb'sec (e i'))
    -- Apply `fibreTrace_sheet_eventuallyEq` with `D' = Φ b'`, sheet `i'`, section `s`; rewrite the
    -- fibre point `(Φ b').xs i' = sec (e i') b'` (`hxs i'`) so the right-inverse data matches.
    have hsheet := FormTraceSheet.fibreTrace_sheet_eventuallyEq ω₀ f (Φ b') i'
      (s := fun z => (chartAt ℂ (sec (e i') b')) (sec (e i') z))
      (by rw [hxs i']) hrinv_cont
      (by rw [hxs i']; exact hrinv_rinv)
    exact hsheet.deriv_eq
  · -- chart transition `chart_{D.xs i} ∘ chart_{sec i b'}.symm` differentiable at `chart_{sec i b'} (sec i b')`.
    intro i
    exact transition_differentiableAt_overlap (mem_chart_source ℂ (sec i b')) (hmem i)
  · -- chart transition `chart_{sec i b'} ∘ chart_{D.xs i}.symm` differentiable at `chart_{D.xs i} (sec i b')`.
    intro i
    exact transition_differentiableAt_overlap (hmem i) (mem_chart_source ℂ (sec i b'))

/-- **A moving-fibre coherence datum from a local sheet system.**  The `LocalSheetSystem`-packaged form
of `MovingCoherenceDatum.ofSheetSections`: a `LocalSheetSystem S` for `f.holoRepr` at `b₀` supplies the
moving sections `sec i := S.sheet (eD i)` (smooth + sections of `f.holoRepr` on `S.V ∋ b₀`) through the
reference fibre `D` (re-indexed by `eD : D.ι ≃ Fin S.n` with `D.xs i = S.sheet (eD i) b₀`), and the
caller supplies the §VIII.3 re-selection bijection `hsel`.  Produces the `MovingCoherenceDatum`. -/
noncomputable def MovingCoherenceDatum.ofLocalSheetSystem
    {Φ : (b : ℂ) → FibreRegularData g f b} {b₀ : ℂ}
    (S : Jacobians.LocalSheetSystem f.holoRepr b₀)
    (D : FibreRegularData g f b₀) (eD : D.ι ≃ Fin S.n)
    (hxsD : ∀ i, D.xs i = S.sheet (eD i) b₀)
    (hsel : ∀ᶠ b' in 𝓝 b₀, ∃ e : (Φ b').ι ≃ D.ι,
      (∀ i', (Φ b').xs i' = S.sheet (eD (e i')) b') ∧
      (∀ i, S.sheet (eD i) b' ∈ (chartAt ℂ (D.xs i)).source)) :
    MovingCoherenceDatum ω₀ g f Φ b₀ :=
  MovingCoherenceDatum.ofSheetSections D (fun i => S.sheet (eD i))
    (fun i => (hxsD i).symm)
    (fun i => (S.sheet_smooth (eD i)).contMDiffAt (S.isOpen_V.mem_nhds S.mem_V))
    (fun i => by filter_upwards [S.isOpen_V.mem_nhds S.mem_V] with b' hb'
      using S.sheet_section (eD i) b' hb')
    hsel

/-! ### The minimal remaining obligation, packaged: the global sheet selection

`MovingCoherenceDatum.ofSheetSections` discharges *all* the germ / differentiability content of the
per-value moving data, reducing it to the §VIII.3 **re-selection bijection** `hsel` plus the moving
sections.  We bundle the *whole* Gate-A input — the global selection `Φ`, the per-pole-value and
per-regular-value sheet sections with their re-selection bijections, the finite/∞ enumeration
bookkeeping, the `∞`-glue, junk-freeness, and the kirovGenus-`0` continuation — into one structure
`MovingSheetSelection`, and show it produces a `MovingCoherenceFamily` (hence Gate A `∑Res = 0`).

This is the honest minimal obligation: every field is either *proved* infrastructure or the genuine
residual (the continuously-varying sheet sections + re-selection bijections at each value, the `∞`-glue,
junk-freeness, and the kirovGenus-`0` vanishing).  The per-value moving data `Cfin`/`Creg` are *derived* from
the sheet sections via `ofSheetSections`. -/

/-- **A moving-fibre sheet selection** for `α = ω₀·g` over `poles`, relative to an adapted cover `hac`.
The Gate-A input with the per-value moving data presented in *sheet form*: at each pole-value `cs i` and
each regular value `z`, continuously-varying manifold sections `sec` of `f.holoRepr` (the branched-cover
sheets) through the fixed fibre, with the §VIII.3 re-selection bijection `hsel` (near the base value,
`Φ b'` is enumerated by the moving sections).  The remaining fields (finite/∞ enumeration, `∞`-glue,
junk-freeness, kirovGenus-`0`) carry over verbatim from `MovingCoherenceFamily`.  Produces a
`MovingCoherenceFamily` via `MovingCoherenceDatum.ofSheetSections`. -/
structure MovingSheetSelection (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (poles : Finset X) (hac : AdaptedCover ω₀ g f poles) where
  /-- The global fibre selection. -/
  Φ : (b : ℂ) → FibreRegularData g f b
  /-- The number of finite pole-values. -/
  m : ℕ
  /-- The finite pole-values (the `L`-centres). -/
  cs : Fin m → ℂ
  /-- A radius bounding the finite pole-values. -/
  ρ : ℝ
  /-- The finite pole-values lie inside `ball 0 ρ`. -/
  hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ
  /-- The finite pole-values are distinct. -/
  hcs_inj : Function.Injective cs
  /-- The finite pole-values, mapped to the sphere, are exactly the finite-value pole images. -/
  hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
    = (poles.image f.toRiemannSphere).erase OnePoint.infty
  /-- The `∞`-fibre regularity data. -/
  Dinf : InftyFibreData g f
  /-- The `∞`-fibre enumeration is injective. -/
  hxs_inj : Function.Injective Dinf.xs
  /-- Each `∞`-fibre point is a pole mapping to `∞`. -/
  hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty
  /-- The `∞`-fibre enumeration is surjective onto the `∞` fibre. -/
  hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a
  /-- **Per-pole-value moving sections**: manifold sections of `f.holoRepr` through the pole sub-fibre
  `fibreReg hac (cs i)`. -/
  secFin : ∀ i, (fibreReg hac (cs i)).ι → ℂ → X
  /-- Each pole-value section passes through the pole sub-fibre point at the base. -/
  hsecFin_base : ∀ i j, secFin i j (cs i) = (fibreReg hac (cs i)).xs j
  /-- Each pole-value section is `C^ω` at the base. -/
  hsecFin_smooth : ∀ i j, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (secFin i j) (cs i)
  /-- Each pole-value section is a section of `f.holoRepr` near the base. -/
  hsecFin_sec : ∀ i j, ∀ᶠ b' in 𝓝 (cs i), f.holoRepr (secFin i j b') = b'
  /-- **The §VIII.3 re-selection bijection at each pole-value** (against the pole sub-fibre). -/
  hselFin : ∀ i, ∀ᶠ b' in 𝓝 (cs i), ∃ e : (Φ b').ι ≃ (fibreReg hac (cs i)).ι,
    (∀ i', (Φ b').xs i' = secFin i (e i') b') ∧
    (∀ j, secFin i j b' ∈ (chartAt ℂ ((fibreReg hac (cs i)).xs j)).source)
  /-- **Per-regular-value reference fibre** off the centres. -/
  Dreg : ∀ z, z ∉ Finset.univ.image cs → FibreRegularData g f z
  /-- `g`'s chart-pullback is analytic at each fibre point of the regular reference fibre. -/
  hDreg_g : ∀ z (hz : z ∉ Finset.univ.image cs), ∀ i,
    AnalyticAt ℂ (fun w => g ((chartAt ℂ ((Dreg z hz).xs i)).symm w))
      ((chartAt ℂ ((Dreg z hz).xs i)) ((Dreg z hz).xs i))
  /-- **Per-regular-value moving sections** through the regular reference fibre. -/
  secReg : ∀ z (hz : z ∉ Finset.univ.image cs), (Dreg z hz).ι → ℂ → X
  /-- Each regular-value section passes through the regular fibre point at the base. -/
  hsecReg_base : ∀ z (hz : z ∉ Finset.univ.image cs) j, secReg z hz j z = (Dreg z hz).xs j
  /-- Each regular-value section is `C^ω` at the base. -/
  hsecReg_smooth : ∀ z (hz : z ∉ Finset.univ.image cs) j, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (secReg z hz j) z
  /-- Each regular-value section is a section of `f.holoRepr` near the base. -/
  hsecReg_sec : ∀ z (hz : z ∉ Finset.univ.image cs) j,
    ∀ᶠ b' in 𝓝 z, f.holoRepr (secReg z hz j b') = b'
  /-- **The §VIII.3 re-selection bijection at each regular value**. -/
  hselReg : ∀ z (hz : z ∉ Finset.univ.image cs), ∀ᶠ b' in 𝓝 z, ∃ e : (Φ b').ι ≃ (Dreg z hz).ι,
    (∀ i', (Φ b').xs i' = secReg z hz (e i') b') ∧
    (∀ j, secReg z hz j b' ∈ (chartAt ℂ ((Dreg z hz).xs j)).source)
  /-- **`∞` glue.** The reciprocal coefficient germ-equals the `∞`-fibre trace off `0`. -/
  hglue_inf : recipCoeff (valueChartTrace ω₀ f Φ)
    =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff
  /-- **Junk-freeness.** The remainder is continuous at each centre. -/
  hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
    (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
      (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
    ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTrace ω₀ f Φ - L.R) p
  /-- The kirovGenus-`0` analytic continuation of the reciprocal remainder. -/
  R₀ : ℂ → ℂ
  /-- `R₀` is analytic at `0`. -/
  hR₀_an : AnalyticAt ℂ R₀ 0
  /-- **Genus-`0` `∞`-vanishing.** `R₀` vanishes at `0`. -/
  hR₀0 : R₀ 0 = 0
  /-- The reciprocal remainder germ-equals `R₀` off `0`. -/
  hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
    recipCoeff (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] 0] R₀

/-- **A moving-fibre sheet selection yields a moving-fibre coherence family.**  The per-pole-value and
per-regular-value moving data are *derived* from the sheet sections via
`MovingCoherenceDatum.ofSheetSections` (the proved §VIII.3 self-coherence from the re-selection
bijection); the remaining fields carry over verbatim.  This wires the sheet-form Gate-A input to the
proved `MovingCoherenceFamily ⇒ ∑Res = 0` chain. -/
noncomputable def MovingSheetSelection.toMovingCoherenceFamily {hac : AdaptedCover ω₀ g f poles}
    (S : MovingSheetSelection ω₀ g f poles hac) :
    MovingCoherenceFamily ω₀ g f poles hac where
  Φ := S.Φ
  m := S.m
  cs := S.cs
  ρ := S.ρ
  hcs_ball := S.hcs_ball
  hcs_inj := S.hcs_inj
  hcenters_cs := S.hcenters_cs
  Dinf := S.Dinf
  hxs_inj := S.hxs_inj
  hxs_mem := S.hxs_mem
  hxs_surj := S.hxs_surj
  Cfin := fun i => MovingCoherenceDatum.ofSheetSections (fibreReg hac (S.cs i)) (S.secFin i)
    (S.hsecFin_base i) (S.hsecFin_smooth i) (S.hsecFin_sec i) (S.hselFin i)
  hCfin_D := fun _ => rfl
  Creg := fun z hz => MovingCoherenceDatum.ofSheetSections (S.Dreg z hz) (S.secReg z hz)
    (S.hsecReg_base z hz) (S.hsecReg_smooth z hz) (S.hsecReg_sec z hz) (S.hselReg z hz)
  hCreg_g := fun z hz => S.hDreg_g z hz
  hglue_inf := S.hglue_inf
  hcont_int := S.hcont_int
  R₀ := S.R₀
  hR₀_an := S.hR₀_an
  hR₀0 := S.hR₀0
  hR₀_eq := S.hR₀_eq

/-- **Gate A `∑Res = 0` from a moving-fibre sheet selection.**  Via
`MovingSheetSelection.toMovingCoherenceFamily` and the proved
`residueSum_eq_zero_of_movingCoherenceFamily`, a moving-fibre sheet selection closes Gate A's 1-form
residue theorem for `α = ω₀·g`.  This is the sheet-form §VIII.3 reduction of Gate A: every field is
either proved (the per-value self-coherence from the re-selection bijection, the kirovGenus-`0` vanishing) or
the precise residual (the continuously-varying sheets + re-selection bijections, the `∞`-glue,
junk-freeness). -/
theorem residueSum_eq_zero_of_movingSheetSelection (hac : AdaptedCover ω₀ g f poles)
    (S : MovingSheetSelection ω₀ g f poles hac) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_movingCoherenceFamily hac S.toMovingCoherenceFamily

/-! ### Non-vacuity of the moving-fibre sheet selection (end-to-end soundness)

The `MovingSheetSelection` obligation is *satisfiable*, not a disguised `False`: for the **empty pole
set** (`α = ω₀·g` globally holomorphic) the empty fibre selection assembles into a
`MovingSheetSelection` — no finite pole-values (the per-pole sheet fields vacuous), the per-regular-value
reference fibre is the empty fibre (`secReg` vacuous, the re-selection bijection the empty equiv), the
empty `∞`-trace, vacuous junk-freeness, and the vanishing kirovGenus-`0` continuation.  Its
`residueSum_eq_zero_of_movingSheetSelection` yields `∑Res = 0`, confirming the sheet-form reduction is
honest. -/

/-- **The empty moving sheet selection.**  For the empty pole set, the empty fibre selection assembles
into a `MovingSheetSelection`: per-regular-value empty fibre + empty sections + the empty re-selection
equiv, vacuous finite/∞-pole fields, and the vanishing kirovGenus-`0` continuation.  The honest non-vacuity
witness. -/
noncomputable def movingSheetSelection_empty (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    MovingSheetSelection ω₀ g f ∅ (adaptedCover_empty ω₀ g f hdiv) where
  Φ := fun p => emptyFibreRegularData g f p
  m := 0
  cs := Fin.elim0
  ρ := 0
  hcs_ball := fun i => i.elim0
  hcs_inj := fun i => i.elim0
  hcenters_cs := by simp
  Dinf := emptyInftyFibreData g f
  hxs_inj := fun i => i.elim
  hxs_mem := fun i => i.elim
  hxs_surj := fun a ha _ => absurd ha (Finset.notMem_empty a)
  secFin := fun i => i.elim0
  hsecFin_base := fun i => i.elim0
  hsecFin_smooth := fun i => i.elim0
  hsecFin_sec := fun i => i.elim0
  hselFin := fun i => i.elim0
  Dreg := fun z _ => emptyFibreRegularData g f z
  hDreg_g := fun z _ i => i.elim
  secReg := fun z _ => Empty.elim
  hsecReg_base := fun z _ j => j.elim
  hsecReg_smooth := fun z _ j => j.elim
  hsecReg_sec := fun z _ j => j.elim
  hselReg := fun z _ => by
    filter_upwards with b'
    -- `(Φ b').ι = Empty = (Dreg z hz).ι`; the empty equiv, with all per-point fields vacuous.
    exact ⟨Equiv.equivOfIsEmpty Empty Empty, fun i' => i'.elim, fun j => j.elim⟩
  hglue_inf := by
    rw [valueChartTrace_emptySelection ω₀ f, inftyFibreTrace_emptyData_traceCoeff ω₀ f,
      recipCoeff_zero]
  hcont_int := by
    intro L hLa _ p hp
    rw [hLa, Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0))] at hp
    exact absurd hp (Finset.notMem_empty p)
  R₀ := fun _ => 0
  hR₀_an := analyticAt_const
  hR₀0 := rfl
  hR₀_eq := by
    intro L hLa
    rw [valueChartTrace_emptySelection ω₀ f]
    have hLR0 : L.R = fun _ => (0 : ℂ) := by
      have hempty : (Finset.univ : Finset L.ι) = ∅ :=
        Finset.image_eq_empty.mp
          (by rw [hLa]; exact Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0)))
      funext z
      show (∑ p : L.ι, L.c p * (z - L.a p) ^ L.n p) = 0
      rw [hempty, Finset.sum_empty]
    rw [hLR0]
    filter_upwards with ζ
    show recipCoeff ((fun _ => (0 : ℂ)) - fun _ => (0 : ℂ)) ζ = (0 : ℂ)
    simp [recipCoeff]

/-- **Non-vacuity of the moving-fibre sheet Gate-A reduction.**  For the empty pole set the reduction
`residueSum_eq_zero_of_movingSheetSelection` is satisfiable via the empty sheet selection
(`movingSheetSelection_empty`), yielding `∑Res = 0`.  Confirms the sheet-form reduction is honest (not a
disguised `False`). -/
theorem residueSum_eq_zero_of_movingSheetSelection_holomorphic (ω₀ : HolomorphicOneForms X)
    (g : X → ℂ) (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_movingSheetSelection (adaptedCover_empty ω₀ g f hdiv)
    (movingSheetSelection_empty ω₀ g f hdiv)

end Jacobians.Dolbeault.FormTraceMovingFibre
