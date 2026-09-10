/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Abel
import KirovDolbeault.MeromorphicNFRepair
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Geometry.Manifold.Complex

/-!
# Compact Liouville for meromorphic functions (non-Dolbeault)

A non-constant meromorphic function on a compact connected Riemann surface must have a pole.
This is the meromorphic corollary of holomorphic Liouville
(`MDifferentiable.exists_eq_const_of_compactSpace`): if `f` had no pole, then in every chart its
order is `≥ 0`, so `f` is (a removable-singularity repair of) a holomorphic function; on a compact
connected manifold that forces it to be constant, whence its order is `≡ 0`, contradicting
non-constancy.

## The removable-singularity repair

The repo's `MeromorphicFunction.toFun : X → ℂ` is only pinned up to its germ off each point: at an
isolated removable singularity it may carry an arbitrary "junk" value. Mathlib's order-based limit
theory (`tendsto_nhds_of_meromorphicOrderAt_nonneg`) shows that wherever the order is `≥ 0` the
function has a genuine limit along the punctured neighborhood. We therefore work with the
**limit repair**

  `holoRepr f x := limUnder (𝓝[≠] x) f.toFun`,

which discards the junk: it agrees with the normal-form representative
(`toMeromorphicNFAt`) in every chart, hence is analytic in every chart, hence globally
`MDifferentiable`. No manual gluing of per-chart germs is needed — the single global definition
`holoRepr` is analytic at every point by a per-chart computation.

## References

* Forster, *Lectures on Riemann Surfaces*, §§2, 10 (Liouville).
* Mathlib `Mathlib/Analysis/Meromorphic/Order.lean`, `Mathlib/Analysis/Meromorphic/NormalForm.lean`.
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Topology
open Filter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- `f` has a **single simple pole** at `P`: order `-1` at `P` and order `≥ 0`
elsewhere. (Defined here, rather than in `DegreeOneSphere`, so that both the
sphere endgame and the Riemann–Roch reduction can refer to it without a cyclic
import.) -/
def MeromorphicFunction.HasSingleSimplePole
    (f : MeromorphicFunction X) (P : X) : Prop :=
  f.orderAtPoint P = -1 ∧ ∀ x, x ≠ P → 0 ≤ f.orderAtPoint x

/-! ### The limit repair of a meromorphic function

(The chart-level helpers `untop₀_nonneg_iff`, `OpenPartialHomeomorph.tendsto_nhdsNE`,
`toMeromorphicNFAt_self_eq_limUnder`, and `MeromorphicAt.exists_isOpen_meromorphicOn` now live in
the shared `Jacobians.MeromorphicNFRepair`.) -/

/-- The **limit repair** of `f`: at each point, the limit of `f` along the punctured neighborhood.
Where the order of `f` is `≥ 0` this is a genuine value (Mathlib
`tendsto_nhds_of_meromorphicOrderAt_nonneg`), and it discards removable-singularity junk that
`f.toFun` may carry. -/
noncomputable def MeromorphicFunction.holoRepr (f : MeromorphicFunction X) (x : X) : ℂ :=
  limUnder (𝓝[≠] x) f.toFun

/-! ### A chart-independent characterization of "order `≥ 0`"

`orderAtPoint f x` is *defined* via the chart `chartAt x`, so comparing it to the order of the
pullback `f.toFun ∘ φ.symm` in a different chart `φ` needs chart-invariance of the order. We avoid
the (currently unproved) `orderAtPoint_chart_invariant` by characterizing nonnegativity of the order
in a manifestly chart-independent way: **`f` has a limit along the punctured neighborhood `𝓝[≠] x`**
(Mathlib `tendsto_nhds_iff_meromorphicOrderAt_nonneg`). Transferring a `Tendsto` statement through a
chart homeomorphism is elementary (`OpenPartialHomeomorph.tendsto_nhdsNE`,
`Jacobians.MeromorphicNFRepair`). -/

/-- The order of `f` at `x` is `≥ 0` iff `f.toFun` has a limit along the punctured neighborhood of
`x` — a manifestly chart-independent statement. -/
theorem MeromorphicFunction.orderAtPoint_nonneg_iff_tendsto
    (f : MeromorphicFunction X) (x : X) :
    0 ≤ f.orderAtPoint x ↔ ∃ c, Tendsto f.toFun (𝓝[≠] x) (𝓝 c) := by
  set φ := chartAt (H := ℂ) x with hφ
  have hxs : x ∈ φ.source := mem_chart_source ℂ x
  have hmero : MeromorphicAt (f.toFun ∘ φ.symm) (φ x) := f.meromorphic x
  -- bridge ℤ-order to WithTop-order, then to the punctured-limit of the pullback
  rw [show f.orderAtPoint x = (meromorphicOrderAt (f.toFun ∘ φ.symm) (φ x)).untop₀ from rfl,
    untop₀_nonneg_iff, ← tendsto_nhds_iff_meromorphicOrderAt_nonneg hmero]
  constructor
  · rintro ⟨c, hc⟩
    -- pullback has a limit at φ x  ⟹  f.toFun has a limit at x.
    -- Compose `f.toFun ∘ φ.symm` (limit at φx) with the forward chart `φ` (𝓝[≠]x → 𝓝[≠]φx).
    refine ⟨c, ?_⟩
    have htfwd : Tendsto φ (𝓝[≠] x) (𝓝[≠] (φ x)) := φ.tendsto_nhdsNE hxs
    have hcomp : Tendsto (f.toFun ∘ φ.symm ∘ φ) (𝓝[≠] x) (𝓝 c) := hc.comp htfwd
    refine hcomp.congr' ?_
    have hev : ∀ᶠ y in 𝓝 x, y ∈ φ.source := φ.open_source.mem_nhds hxs
    filter_upwards [mem_nhdsWithin_of_mem_nhds hev] with y hy
    simp [Function.comp, φ.left_inv hy]
  · rintro ⟨c, hc⟩
    -- f.toFun has a limit at x ⟹ pullback has a limit at φ x.
    -- Compose `f.toFun` (limit at x) with the inverse chart `φ.symm` (𝓝[≠]φx → 𝓝[≠]x).
    refine ⟨c, ?_⟩
    have hwt : φ x ∈ φ.target := φ.map_source hxs
    have htsymm : Tendsto φ.symm (𝓝[≠] (φ x)) (𝓝[≠] x) := by
      have := φ.symm.tendsto_nhdsNE (x := φ x) (by simpa using hwt)
      simpa [φ.left_inv hxs] using this
    exact hc.comp htsymm

/-! ### The repair is the normal-form representative, chart by chart

(`toMeromorphicNFAt_self_eq_limUnder` and `MeromorphicAt.exists_isOpen_meromorphicOn` now live in the
shared `Jacobians.MeromorphicNFRepair`.) -/

/-- **The local repair lemma.** On a small open neighborhood `V` of `φ x₀` (with `φ = chartAt x₀`),
the limit-repair `holoRepr`, read back through the chart, coincides with the normal-form
representative of the pullback `F = f.toFun ∘ φ.symm`. Concretely: for every `w ∈ V`,
`f.holoRepr (φ.symm w) = toMeromorphicNFOn F V w`.

This needs the order of `f` to be `≥ 0` only at `x₀` (the center); at the punctured points `F` is
analytic, so its order is automatically `≥ 0`. -/
theorem MeromorphicFunction.exists_holoRepr_eq_NFOn (f : MeromorphicFunction X) (x₀ : X)
    (h₀ : 0 ≤ f.orderAtPoint x₀) :
    ∃ V : Set ℂ, IsOpen V ∧ (chartAt (H := ℂ) x₀) x₀ ∈ V ∧
      ∃ (_hF : MeromorphicOn (f.toFun ∘ (chartAt (H := ℂ) x₀).symm) V),
        ∀ w ∈ V, f.holoRepr ((chartAt (H := ℂ) x₀).symm w) =
          toMeromorphicNFOn (f.toFun ∘ (chartAt (H := ℂ) x₀).symm) V w := by
  set φ := chartAt (H := ℂ) x₀ with hφ
  set F := f.toFun ∘ φ.symm with hFdef
  have hmero₀ : MeromorphicAt F (φ x₀) := f.meromorphic x₀
  obtain ⟨V₀, hV₀open, hzV₀, hFV₀, hana₀⟩ :=
    Jacobians.MeromorphicAt.exists_isOpen_meromorphicOn hmero₀
  -- Restrict to `φ.target` so that `φ.symm` is a genuine inverse on `V`.
  set V := V₀ ∩ φ.target with hVdef
  have hVopen : IsOpen V := hV₀open.inter φ.open_target
  have hzV : φ x₀ ∈ V := ⟨hzV₀, φ.map_source (mem_chart_source ℂ x₀)⟩
  have hFV : MeromorphicOn F V := fun w hw => hFV₀ w hw.1
  have hana : ∀ w ∈ V, w ≠ φ x₀ → AnalyticAt ℂ F w := fun w hw hwz => hana₀ w hw.1 hwz
  have hVtarget : V ⊆ φ.target := fun _ hw => hw.2
  refine ⟨V, hVopen, hzV, hFV, fun w hw => ?_⟩
  -- The order of F at w is ≥ 0: at the center from h₀ (def of orderAtPoint), else F is analytic.
  have hord_w : 0 ≤ meromorphicOrderAt F w := by
    by_cases hwz : w = φ x₀
    · subst hwz
      rw [show f.orderAtPoint x₀ = (meromorphicOrderAt F (φ x₀)).untop₀ from rfl,
        untop₀_nonneg_iff] at h₀
      exact h₀
    · -- w ≠ φ x₀ : F analytic at w (from the punctured-analyticity), so order ≥ 0
      exact (hana w hw hwz).meromorphicOrderAt_nonneg
  -- F has a limit c at w; that c is both the NFOn value and the holoRepr value.
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg (hFV w hw) hord_w
  -- NFOn value at w = NFAt value at w = c.
  have hNFOn : toMeromorphicNFOn F V w = c := by
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hFV hw]
    exact toMeromorphicNFAt_self_eq_limUnder (hFV w hw) hord_w hc
  rw [hNFOn]
  -- holoRepr value at φ.symm w = c : f.toFun has limit c at φ.symm w (transfer of hc).
  show limUnder (𝓝[≠] (φ.symm w)) f.toFun = c
  have hys : φ.symm w ∈ φ.source := φ.map_target (hVtarget hw)
  -- The punctured neighborhood of `φ.symm w` is NeBot: it receives `𝓝[≠] w` (NeBot in ℂ) under φ.symm.
  have htsymm : Tendsto φ.symm (𝓝[≠] w) (𝓝[≠] (φ.symm w)) := by
    have := φ.symm.tendsto_nhdsNE (x := w) (by simpa using hVtarget hw)
    simpa using this
  haveI hNeBot : (𝓝[≠] (φ.symm w)).NeBot := htsymm.neBot
  apply Filter.Tendsto.limUnder_eq
  -- transfer: compose `F = f.toFun ∘ φ.symm` (limit c at w) with forward chart φ at φ.symm w.
  have hfwd : Tendsto φ (𝓝[≠] (φ.symm w)) (𝓝[≠] (φ (φ.symm w))) := φ.tendsto_nhdsNE hys
  have hwr : φ (φ.symm w) = w := φ.right_inv (hVtarget hw)
  have hcomp : Tendsto (F ∘ φ) (𝓝[≠] (φ.symm w)) (𝓝 c) := by
    rw [← hwr] at hc; exact hc.comp hfwd
  refine hcomp.congr' ?_
  have hev : ∀ᶠ y in 𝓝 (φ.symm w), y ∈ φ.source := φ.open_source.mem_nhds hys
  filter_upwards [mem_nhdsWithin_of_mem_nhds hev] with y hy
  simp [hFdef, Function.comp, φ.left_inv hy]

/-- **Off-center, the chart pullback of `holoRepr` equals the normal-form representative.**
With NO order hypothesis at the center `x₀`: on the *punctured* neighborhood `𝓝[≠] (φ x₀)`
(`φ = chartAt x₀`), the limit-repair `holoRepr` read back through the chart agrees with the
normal-form representative `toMeromorphicNFAt F (φ x₀)` of the pullback `F = f.toFun ∘ φ.symm`.

Off the center, `F` is genuinely analytic (`MeromorphicAt.eventually_analyticAt`), so `f.toFun`
carries no junk and its punctured limit there is the analytic value `F w`; this equals `N w` since
the normal form agrees with `F` off the center. This is the punctured-neighborhood input that the
simple-pole analysis at a pole (where the center order is `< 0`, so `exists_holoRepr_eq_NFOn` does
not apply) consumes. -/
theorem MeromorphicFunction.holoRepr_chartPullback_eventuallyEq_NFAt
    (f : MeromorphicFunction X) (x₀ : X) :
    f.holoRepr ∘ (chartAt (H := ℂ) x₀).symm =ᶠ[𝓝[≠] ((chartAt (H := ℂ) x₀) x₀)]
      toMeromorphicNFAt (f.toFun ∘ (chartAt (H := ℂ) x₀).symm) ((chartAt (H := ℂ) x₀) x₀) := by
  set φ := chartAt (H := ℂ) x₀ with hφ
  set F := f.toFun ∘ φ.symm with hFdef
  have hxs : x₀ ∈ φ.source := mem_chart_source ℂ x₀
  have hmero : MeromorphicAt F (φ x₀) := f.meromorphic x₀
  -- `N =ᶠ[𝓝[≠] φx₀] F`.
  have hNF : F =ᶠ[𝓝[≠] (φ x₀)] toMeromorphicNFAt F (φ x₀) :=
    hmero.eq_nhdsNE_toMeromorphicNFAt
  -- `F` is analytic on a punctured neighborhood of `φ x₀`.
  have hana : ∀ᶠ w in 𝓝[≠] (φ x₀), AnalyticAt ℂ F w := hmero.eventually_analyticAt
  -- For `w` in the target (so `φ.symm` is a genuine inverse) and `F` analytic at `w`,
  -- `holoRepr (φ.symm w) = F w`.
  have htgt : ∀ᶠ w in 𝓝[≠] (φ x₀), w ∈ φ.target :=
    mem_nhdsWithin_of_mem_nhds (φ.open_target.mem_nhds (φ.map_source hxs))
  filter_upwards [hana, htgt, hNF] with w hwana hwtgt hwNF
  -- `holoRepr (φ.symm w) = F w`.
  have hval : f.holoRepr (φ.symm w) = F w := by
    show limUnder (𝓝[≠] (φ.symm w)) f.toFun = F w
    have hys : φ.symm w ∈ φ.source := φ.map_target hwtgt
    have htsymm : Tendsto φ.symm (𝓝[≠] w) (𝓝[≠] (φ.symm w)) := by
      have := φ.symm.tendsto_nhdsNE (x := w) (by simpa using hwtgt)
      simpa using this
    haveI : (𝓝[≠] (φ.symm w)).NeBot := htsymm.neBot
    apply Filter.Tendsto.limUnder_eq
    -- F is continuous at w (analytic), so F has limit F w along 𝓝[≠] w.
    have hFlim : Tendsto F (𝓝[≠] w) (𝓝 (F w)) :=
      hwana.continuousAt.continuousWithinAt.tendsto
    -- transfer to f.toFun along 𝓝[≠] (φ.symm w).
    have hwr : φ (φ.symm w) = w := φ.right_inv hwtgt
    have hfwd : Tendsto φ (𝓝[≠] (φ.symm w)) (𝓝[≠] w) := by
      have := φ.tendsto_nhdsNE hys; rwa [hwr] at this
    have hcomp : Tendsto (F ∘ φ) (𝓝[≠] (φ.symm w)) (𝓝 (F w)) := hFlim.comp hfwd
    refine hcomp.congr' ?_
    have hev : ∀ᶠ y in 𝓝 (φ.symm w), y ∈ φ.source := φ.open_source.mem_nhds hys
    filter_upwards [mem_nhdsWithin_of_mem_nhds hev] with y hy
    simp [hFdef, Function.comp, φ.left_inv hy]
  show f.holoRepr (φ.symm w) = toMeromorphicNFAt F (φ x₀) w
  rw [hval, hwNF]

/-- **The chart pullback of `holoRepr` is analytic at a point of nonnegative order.**
This is the local (pointwise) core of `mdifferentiable_holoRepr`, requiring `0 ≤ orderAtPoint`
*only at `x₀`* (not globally). Read back through the chart `φ = chartAt x₀`, the limit-repair
`holoRepr ∘ φ.symm` agrees near `φ x₀` with the analytic normal-form representative of the
pullback (`exists_holoRepr_eq_NFOn`), hence is `AnalyticAt ℂ`. -/
theorem MeromorphicFunction.analyticAt_holoRepr_chartPullback_of_orderNonneg
    (f : MeromorphicFunction X) {x₀ : X} (h₀ : 0 ≤ f.orderAtPoint x₀) :
    AnalyticAt ℂ (f.holoRepr ∘ (chartAt (H := ℂ) x₀).symm) ((chartAt (H := ℂ) x₀) x₀) := by
  set φ := chartAt (H := ℂ) x₀ with hφ
  obtain ⟨V, hVopen, hzV, hFV, hrepr⟩ := f.exists_holoRepr_eq_NFOn x₀ h₀
  -- NFOn is analytic at φ x₀ (its order there = order of F = orderAtPoint x₀ ≥ 0, and it's in NF).
  have hNFana : AnalyticAt ℂ (toMeromorphicNFOn (f.toFun ∘ φ.symm) V) (φ x₀) := by
    have hNF : MeromorphicNFAt (toMeromorphicNFOn (f.toFun ∘ φ.symm) V) (φ x₀) :=
      meromorphicNFOn_toMeromorphicNFOn (f.toFun ∘ φ.symm) V hzV
    have hord : meromorphicOrderAt (toMeromorphicNFOn (f.toFun ∘ φ.symm) V) (φ x₀) =
        meromorphicOrderAt (f.toFun ∘ φ.symm) (φ x₀) :=
      meromorphicOrderAt_congr (hFV.toMeromorphicNFOn_eq_self_on_nhdsNE hzV)
    have h₀' : 0 ≤ meromorphicOrderAt (f.toFun ∘ φ.symm) (φ x₀) := by
      rwa [show f.orderAtPoint x₀ =
        (meromorphicOrderAt (f.toFun ∘ φ.symm) (φ x₀)).untop₀ from rfl, untop₀_nonneg_iff] at h₀
    exact hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 (hord ▸ h₀')
  -- holoRepr ∘ φ.symm =ᶠ[𝓝 (φ x₀)] NFOn, so it's analytic at φ x₀.
  have hEq : f.holoRepr ∘ φ.symm =ᶠ[𝓝 (φ x₀)] toMeromorphicNFOn (f.toFun ∘ φ.symm) V := by
    filter_upwards [hVopen.mem_nhds hzV] with w hw using hrepr w hw
  exact hNFana.congr hEq.symm

/-- **The limit-repair is globally holomorphic.** If `f` has no pole (`∀ x, 0 ≤ orderAtPoint x`),
then `f.holoRepr : X → ℂ` is `MDifferentiable`. In each chart, `holoRepr` read back equals the
analytic normal-form representative of the pullback (`exists_holoRepr_eq_NFOn`), hence is analytic;
the chart bridge `mdifferentiableWithinAt_of_comp_extChartAt_symm` lifts this to the manifold. -/
theorem MeromorphicFunction.mdifferentiable_holoRepr (f : MeromorphicFunction X)
    (hpos : ∀ x, 0 ≤ f.orderAtPoint x) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.holoRepr := by
  intro x₀
  set φ := chartAt (H := ℂ) x₀ with hφ
  have hReprAna : AnalyticAt ℂ (f.holoRepr ∘ φ.symm) (φ x₀) :=
    f.analyticAt_holoRepr_chartPullback_of_orderNonneg (hpos x₀)
  -- Lift analyticity in the chart to MDifferentiableAt via the chart bridge.
  have hIM : IsManifold 𝓘(ℂ) 1 X := IsManifold.of_le le_top
  refine (mdifferentiableWithinAt_univ ..).mp ?_
  apply DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm
  -- match the goal: extChartAt for the trivial model 𝓘(ℂ) is the chart, range 𝓘(ℂ) = univ.
  have hdiff : DifferentiableWithinAt ℂ (f.holoRepr ∘ φ.symm) Set.univ (φ x₀) :=
    hReprAna.differentiableWithinAt
  have hextpt : (extChartAt 𝓘(ℂ) x₀) x₀ = φ x₀ := by simp [hφ, mfld_simps]
  have hextsymm : ⇑(extChartAt 𝓘(ℂ) x₀).symm = ⇑φ.symm := by
    funext z; simp [hφ, mfld_simps]
  rw [hextpt, hextsymm]
  apply hdiff.mono
  simp [Set.preimage_univ, mfld_simps]

/-! ### Liouville endgame: constant repair forces order `≡ 0` -/

/-- If the limit-repair `holoRepr` is **constant** (the conclusion of Liouville on a compact
connected manifold), then the order of `f` is `0` at every point. In each chart the pullback
`f.toFun ∘ φ.symm` agrees off the center with the normal-form representative, which equals the
constant `c`; the order of a constant is `0` (`⊤ ↦ 0` for `c = 0`, else `0`). -/
theorem MeromorphicFunction.orderAtPoint_eq_zero_of_holoRepr_const (f : MeromorphicFunction X)
    (hpos : ∀ x, 0 ≤ f.orderAtPoint x) {c : ℂ} (hconst : ∀ y, f.holoRepr y = c) (x : X) :
    f.orderAtPoint x = 0 := by
  set φ := chartAt (H := ℂ) x with hφ
  obtain ⟨V, hVopen, hzV, hFV, hrepr⟩ := f.exists_holoRepr_eq_NFOn x (hpos x)
  -- The pullback agrees off-center with the normal-form rep, which (on V, pushed back) is `c`.
  have hNFconst : ∀ w ∈ V, toMeromorphicNFOn (f.toFun ∘ φ.symm) V w = c := by
    intro w hw; rw [← hrepr w hw]; exact hconst _
  -- So `f.toFun ∘ φ.symm =ᶠ[𝓝[≠] φx] (fun _ => c)`.
  have hF_eq : (f.toFun ∘ φ.symm) =ᶠ[𝓝[≠] (φ x)] (fun _ => c) := by
    have h1 : toMeromorphicNFOn (f.toFun ∘ φ.symm) V =ᶠ[𝓝[≠] (φ x)] (f.toFun ∘ φ.symm) :=
      hFV.toMeromorphicNFOn_eq_self_on_nhdsNE hzV
    have h2 : (fun w => toMeromorphicNFOn (f.toFun ∘ φ.symm) V w) =ᶠ[𝓝[≠] (φ x)] (fun _ => c) := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hVopen.mem_nhds hzV)] with w hw
      exact hNFconst w hw
    exact h1.symm.trans h2
  -- The order of `f` at `x` is the order of the pullback, which equals the order of the constant `c`.
  show (meromorphicOrderAt (f.toFun ∘ φ.symm) (φ x)).untop₀ = 0
  rw [meromorphicOrderAt_congr hF_eq, meromorphicOrderAt_const]
  split <;> simp

/-- **[INPUT — compact Liouville (no Dolbeault)] PROVEN.** A non-constant meromorphic function on a
compact connected Riemann surface has a pole. Contrapositive: with no pole every order is `≥ 0`, so
the limit-repair `holoRepr` is globally holomorphic (`mdifferentiable_holoRepr`); by holomorphic
Liouville on the compact connected `X` (`MDifferentiable.exists_eq_const_of_compactSpace`) it is
constant, forcing every order to be `0` (`orderAtPoint_eq_zero_of_holoRepr_const`) — contradicting
non-constancy. -/
theorem MeromorphicFunction.exists_pole_of_nonconstant (f : MeromorphicFunction X)
    (hf : ∃ x, f.orderAtPoint x ≠ 0) : ∃ x, f.orderAtPoint x < 0 := by
  by_contra hno
  simp only [not_exists, not_lt] at hno
  -- no pole: every order ≥ 0
  have hpos : ∀ x, 0 ≤ f.orderAtPoint x := hno
  -- holoRepr is globally holomorphic, hence constant (compact connected Liouville)
  haveI hIM : IsManifold 𝓘(ℂ) 1 X := IsManifold.of_le le_top
  have hmdiff : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f.holoRepr := f.mdifferentiable_holoRepr hpos
  obtain ⟨c, hc_const⟩ := hmdiff.exists_eq_const_of_compactSpace
  have hc : ∀ y, f.holoRepr y = c := fun y => congrFun hc_const y
  -- then every order is 0, contradicting non-constancy
  obtain ⟨x, hx⟩ := hf
  exact hx (f.orderAtPoint_eq_zero_of_holoRepr_const hpos hc x)

end Jacobians
