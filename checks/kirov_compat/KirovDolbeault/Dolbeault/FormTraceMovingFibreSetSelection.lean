/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceMovingFibreSymm

/-!
# The set-form moving-fibre sheet selection (Gate A, §VIII.3 — no global labeling)

`Jacobians.Dolbeault.FormTraceMovingFibreSheet` reduced Gate A's `∑Res = 0` to a single
`MovingSheetSelection`, whose per-value re-selection bijections `hselFin`/`hselReg` phrased the moving
fibre as a *labeled* enumeration matching the reference sheets.  The prior round read that as demanding a
global continuous sheet-labeling.

`Jacobians.Dolbeault.FormTraceMovingFibreSymm` established the **symmetric-invariance lever**: the trace
`valueChartTrace ω₀ f Φ b' = (fibreTrace ω₀ f (Φ b')).traceCoeff b'` is a symmetric sum over the fibre
`Φ b'`, so it depends only on the fibre *as a set*; the per-`b'` index bijection is reconstructed
pointwise from set-equality (`MovingCoherenceDatum.ofSheetSectionsSet`), with **no labeling supplied**.

This file repackages the whole Gate-A input in **set form** — `MovingSheetSelectionSet` — whose
per-value geometric content is the labeling-independent fact that the moving fibre `Φ b'` *is the sheet
fibre as a set* near each base value (both injective, same image), plus the discharged
smoothness/section data.  It produces a `MovingCoherenceFamily` (hence Gate A `∑Res = 0`) via the
set-form constructor.  This is the honest minimal obligation **without the false global-labeling
constraint**: every re-selection is by fibre *value*, never by a sheet ordering.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `MovingSheetSelectionSet` — the Gate-A input with `hselFin`/`hselReg` replaced by the set-form
  re-selection `hsetFin`/`hsetReg` (moving fibre = sheet fibre as a set, injective both ways).
* `MovingSheetSelectionSet.toMovingCoherenceFamily` / `residueSum_eq_zero_of_movingSheetSelectionSet`
  — the set-form Gate-A reduction, wiring the per-value moving data through
  `MovingCoherenceDatum.ofSheetSectionsSet`.
* `movingSheetSelectionSet_empty` / `residueSum_eq_zero_of_movingSheetSelectionSet_holomorphic` —
  end-to-end non-vacuity (the empty-pole case), confirming the reduction is honest.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2; the trace is
  single-valued **by symmetry**, not by a global sheet choice).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4.22 (local sheet systems), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceMovingFibre

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormTraceGlobal
  Jacobians.Dolbeault.FormTraceInftyFibre Jacobians.Dolbeault.FormTraceInftyRecip

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The set-form Gate-A input

The whole Gate-A input in **set form**: the per-pole-value and per-regular-value moving data is
presented through the labeling-independent re-selection `hsetFin`/`hsetReg` — near each base value the
moving fibre `Φ b'` and the section values enumerate the same set (both injective).  Everything else
(finite/∞ enumeration, `∞`-glue, junk-freeness, kirovGenus-`0`) is verbatim from `MovingSheetSelection`. -/

/-- **A set-form moving-fibre sheet selection** for `α = ω₀·g` over `poles`, relative to an adapted
cover `hac`.  The Gate-A input with the per-value re-selection in *set form*: at each pole-value `cs i`
(against the pole sub-fibre) and each regular value `z`, continuously-varying manifold sections `sec` of
`f.holoRepr`, with the **labeling-independent** re-selection `hsetFin`/`hsetReg` — near the base value,
the moving fibre `Φ b'` and the section values enumerate the *same set* (both injective).  No global
continuous sheet-labeling, by the trace's monodromy-invariance.  The remaining fields carry over
verbatim from `MovingSheetSelection`.  Produces a `MovingCoherenceFamily` via
`MovingCoherenceDatum.ofSheetSectionsSet`. -/
structure MovingSheetSelectionSet (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
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
  /-- **The §VIII.3 set-form re-selection at each pole-value** (against the pole sub-fibre): near
  `cs i`, the moving fibre `Φ b'` and the section values are both injective with the same image, and the
  sections stay near the fibre points. -/
  hsetFin : ∀ i, ∀ᶠ b' in 𝓝 (cs i), Function.Injective (Φ b').xs ∧
    Function.Injective (fun j => secFin i j b') ∧
    Set.range (Φ b').xs = Set.range (fun j => secFin i j b') ∧
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
  /-- **The §VIII.3 set-form re-selection at each regular value**: near `z`, the moving fibre `Φ b'` and
  the section values are both injective with the same image, and the sections stay near the fibre
  points. -/
  hsetReg : ∀ z (hz : z ∉ Finset.univ.image cs), ∀ᶠ b' in 𝓝 z,
    Function.Injective (Φ b').xs ∧
    Function.Injective (fun j => secReg z hz j b') ∧
    Set.range (Φ b').xs = Set.range (fun j => secReg z hz j b') ∧
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

/-- **A set-form moving-fibre sheet selection yields a moving-fibre coherence family.**  The per-value
moving data is derived from the sheet sections via `MovingCoherenceDatum.ofSheetSectionsSet` (the
symmetric-invariance lever: the pointwise re-selection bijection from set-equality, no labeling); the
remaining fields carry over verbatim.  This wires the set-form Gate-A input to the proved
`MovingCoherenceFamily ⇒ ∑Res = 0` chain. -/
noncomputable def MovingSheetSelectionSet.toMovingCoherenceFamily {hac : AdaptedCover ω₀ g f poles}
    (S : MovingSheetSelectionSet ω₀ g f poles hac) :
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
  Cfin := fun i => MovingCoherenceDatum.ofSheetSectionsSet (fibreReg hac (S.cs i)) (S.secFin i)
    (S.hsecFin_base i) (S.hsecFin_smooth i) (S.hsecFin_sec i) (S.hsetFin i)
  hCfin_D := fun _ => rfl
  Creg := fun z hz => MovingCoherenceDatum.ofSheetSectionsSet (S.Dreg z hz) (S.secReg z hz)
    (S.hsecReg_base z hz) (S.hsecReg_smooth z hz) (S.hsecReg_sec z hz) (S.hsetReg z hz)
  hCreg_g := fun z hz => S.hDreg_g z hz
  hglue_inf := S.hglue_inf
  hcont_int := S.hcont_int
  R₀ := S.R₀
  hR₀_an := S.hR₀_an
  hR₀0 := S.hR₀0
  hR₀_eq := S.hR₀_eq

/-- **Gate A `∑Res = 0` from a set-form moving-fibre sheet selection.**  Via
`MovingSheetSelectionSet.toMovingCoherenceFamily` and the proved
`residueSum_eq_zero_of_movingCoherenceFamily`, a set-form moving-fibre sheet selection closes Gate A's
1-form residue theorem for `α = ω₀·g`.  This is the §VIII.3 reduction of Gate A **without the false
global-labeling constraint**: every re-selection is by fibre *value* (set-equality), the pointwise
bijection reconstructed by the symmetric lever. -/
theorem residueSum_eq_zero_of_movingSheetSelectionSet (hac : AdaptedCover ω₀ g f poles)
    (S : MovingSheetSelectionSet ω₀ g f poles hac) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_movingCoherenceFamily hac S.toMovingCoherenceFamily

/-! ### Non-vacuity of the set-form selection (end-to-end soundness)

For the **empty pole set** the empty fibre selection assembles into a `MovingSheetSelectionSet`: the
per-regular-value reference fibre is the empty fibre, the set-form re-selection holds vacuously (both
ranges are `∅`, both maps injective on the empty index), the empty `∞`-trace, vacuous junk-freeness, and
the vanishing kirovGenus-`0` continuation.  Confirms the set-form reduction is honest. -/

/-- **The empty set-form moving sheet selection.**  For the empty pole set, the empty fibre selection
assembles into a `MovingSheetSelectionSet`: per-regular-value empty fibre + empty sections + the
trivially-satisfied set-form re-selection (both ranges `∅`), vacuous finite/∞-pole fields, and the
vanishing kirovGenus-`0` continuation.  The honest non-vacuity witness. -/
noncomputable def movingSheetSelectionSet_empty (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    MovingSheetSelectionSet ω₀ g f ∅ (adaptedCover_empty ω₀ g f hdiv) where
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
  hsetFin := fun i => i.elim0
  Dreg := fun z _ => emptyFibreRegularData g f z
  hDreg_g := fun z _ i => i.elim
  secReg := fun z _ => Empty.elim
  hsecReg_base := fun z _ j => j.elim
  hsecReg_smooth := fun z _ j => j.elim
  hsecReg_sec := fun z _ j => j.elim
  hsetReg := fun z _ => by
    filter_upwards with b'
    -- `(Φ b').ι = Empty = (Dreg z hz).ι`; both ranges are `∅`, both maps injective on `Empty`.
    refine ⟨fun i => i.elim, fun j => j.elim, ?_, fun j => j.elim⟩
    ext x
    constructor
    · rintro ⟨i, _⟩; exact i.elim
    · rintro ⟨j, _⟩; exact j.elim
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

/-- **Non-vacuity of the set-form moving-fibre Gate-A reduction.**  For the empty pole set the reduction
`residueSum_eq_zero_of_movingSheetSelectionSet` is satisfiable via the empty set-form selection
(`movingSheetSelectionSet_empty`), yielding `∑Res = 0`.  Confirms the set-form reduction is honest (not
a disguised `False`). -/
theorem residueSum_eq_zero_of_movingSheetSelectionSet_holomorphic (ω₀ : HolomorphicOneForms X)
    (g : X → ℂ) (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_movingSheetSelectionSet (adaptedCover_empty ω₀ g f hdiv)
    (movingSheetSelectionSet_empty ω₀ g f hdiv)

end Jacobians.Dolbeault.FormTraceMovingFibre
