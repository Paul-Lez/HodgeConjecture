/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Complex
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Chart-level helpers for the limit-repair of a meromorphic function

The repo's chart-read meromorphic functions are pinned only up to germ: at an isolated removable
singularity they may carry arbitrary "junk". The **limit repair** `limUnder (𝓝[≠] x) F` discards the
junk; where the order is `≥ 0` it agrees with the normal-form representative `toMeromorphicNFAt`,
hence is analytic.

These lemmas are purely about `ℂ → ℂ` (and `OpenPartialHomeomorph`), with **no** dependence on the
repo's `MeromorphicFunction` bundle or any manifold structure, so they are shared between
`MeromorphicLiouville` (compact Liouville) and `DolbeaultComparisonInverse` (the Čech → Dolbeault
glued-form operator's holomorphic representatives). Extracted from `MeromorphicLiouville`.
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Topology
open Filter

/-- The integer order `.untop₀` is `≥ 0` iff the raw `WithTop ℤ` order is `≥ 0`. (`⊤ ↦ 0 ≥ 0`.) -/
theorem untop₀_nonneg_iff {α : WithTop ℤ} : (0 : ℤ) ≤ α.untop₀ ↔ 0 ≤ α := by
  cases α with
  | top => simp
  | coe n => simp [WithTop.untop₀_coe]

/-- An open partial homeomorphism carries the punctured neighborhood of a source point to the
punctured neighborhood of its image: `Tendsto φ (𝓝[≠] x) (𝓝[≠] (φ x))` for `x ∈ φ.source`.
(Continuity gives the unpunctured limit; injectivity on the source removes the center.) -/
theorem _root_.OpenPartialHomeomorph.tendsto_nhdsNE {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] (φ : OpenPartialHomeomorph Y Z) {x : Y} (hx : x ∈ φ.source) :
    Tendsto φ (𝓝[{x}ᶜ] x) (𝓝[{φ x}ᶜ] (φ x)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact (φ.continuousAt hx).continuousWithinAt
  · have hev : ∀ᶠ y in 𝓝 x, y ∈ φ.source := φ.open_source.mem_nhds hx
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hev] with y hy hys
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
    exact fun hcontra => hy (φ.injOn hys hx hcontra)

/-- For a meromorphic function `F : ℂ → ℂ` whose order at `w` is `≥ 0`, the value of its
normal-form representative at the center equals the limit along `𝓝[≠] w`. -/
theorem toMeromorphicNFAt_self_eq_limUnder {F : ℂ → ℂ} {w c : ℂ}
    (hF : MeromorphicAt F w) (ho : 0 ≤ meromorphicOrderAt F w)
    (hc : Tendsto F (𝓝[≠] w) (𝓝 c)) :
    toMeromorphicNFAt F w w = c := by
  have hNF : MeromorphicNFAt (toMeromorphicNFAt F w) w := meromorphicNFAt_toMeromorphicNFAt
  have hord : meromorphicOrderAt (toMeromorphicNFAt F w) w = meromorphicOrderAt F w :=
    meromorphicOrderAt_congr hF.eq_nhdsNE_toMeromorphicNFAt.symm
  have hAna : AnalyticAt ℂ (toMeromorphicNFAt F w) w :=
    hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 (hord ▸ ho)
  have h1 : Tendsto (toMeromorphicNFAt F w) (𝓝[≠] w) (𝓝 (toMeromorphicNFAt F w w)) :=
    hAna.continuousAt.continuousWithinAt.tendsto
  have h2 : Tendsto (toMeromorphicNFAt F w) (𝓝[≠] w) (𝓝 c) :=
    hc.congr' hF.eq_nhdsNE_toMeromorphicNFAt
  exact tendsto_nhds_unique h1 h2

/-- From meromorphy of `F` *at* a point `z`, extract an **open neighborhood** `V ∋ z` on which `F`
is meromorphic, and moreover **analytic away from `z`**. (Mathlib `MeromorphicAt.eventually_analyticAt`:
`F` is analytic on a punctured neighborhood; together with meromorphy at `z` itself this is
meromorphy on a full open `V`.) -/
theorem MeromorphicAt.exists_isOpen_meromorphicOn {F : ℂ → ℂ} {z : ℂ} (hF : MeromorphicAt F z) :
    ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ MeromorphicOn F V ∧
      ∀ w ∈ V, w ≠ z → AnalyticAt ℂ F w := by
  obtain ⟨V, hVsub, hVopen, hzV⟩ := eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 hF.eventually_analyticAt)
  refine ⟨V, hVopen, hzV, fun w hw => ?_, fun w hw hwz => hVsub w hw hwz⟩
  by_cases hwz : w = z
  · exact hwz ▸ hF
  · exact (hVsub w hw hwz).meromorphicAt

/-- The **limit-repair** `w ↦ limUnder (𝓝[≠] w) F` of a function meromorphic with order `≥ 0` on an
open set `V` agrees pointwise with the normal-form representative `toMeromorphicNFOn F V`. -/
theorem limUnder_eq_toMeromorphicNFOn {F : ℂ → ℂ} {V : Set ℂ} (hF : MeromorphicOn F V)
    (hord : ∀ w ∈ V, 0 ≤ meromorphicOrderAt F w) {w : ℂ} (hw : w ∈ V) :
    limUnder (𝓝[≠] w) F = toMeromorphicNFOn F V w := by
  obtain ⟨c, hc⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg (hF w hw)).2 (hord w hw)
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hF hw,
    toMeromorphicNFAt_self_eq_limUnder (hF w hw) (hord w hw) hc, hc.limUnder_eq]

/-- The normal-form representative `toMeromorphicNFOn F V` is analytic at each point of `V` where the
order of `F` is `≥ 0` (normal form + nonneg order ⟹ analytic). -/
theorem analyticAt_toMeromorphicNFOn {F : ℂ → ℂ} {V : Set ℂ} (hF : MeromorphicOn F V)
    (hord : ∀ w ∈ V, 0 ≤ meromorphicOrderAt F w) {w₀ : ℂ} (hw₀ : w₀ ∈ V) :
    AnalyticAt ℂ (toMeromorphicNFOn F V) w₀ := by
  have hNF : MeromorphicNFAt (toMeromorphicNFOn F V) w₀ := meromorphicNFOn_toMeromorphicNFOn F V hw₀
  have hord' : 0 ≤ meromorphicOrderAt (toMeromorphicNFOn F V) w₀ := by
    rw [meromorphicOrderAt_congr (hF.toMeromorphicNFOn_eq_self_on_nhdsNE hw₀)]
    exact hord w₀ hw₀
  exact hNF.meromorphicOrderAt_nonneg_iff_analyticAt.1 hord'

end Jacobians
