/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! # Chart-local detour through a finite obstruction

Given an `OpenPartialHomeomorph φ : X → Y` (typical example: a chart `chartAt ℂ x`
on a charted space modelled on `ℂ`) and any **finite** `C ⊆ X`, we record two
pull-back helpers that move a `JoinedIn`-style path argument from the chart
codomain `Y` back to the manifold side `X`.

## Main results

* `OpenPartialHomeomorph.joinedIn_symm_image_of_target` — generic pull-back along
  the symmetric chart. If `φ p₀, φ q₀` are joined inside `φ.target ∩ T` for
  some `T : Set Y` and `p₀, q₀ ∈ φ.source`, then `p₀, q₀` are joined inside
  `φ.source ∩ φ ⁻¹' T`. The path is `φ.symm ∘ γ` of any chart-side path; the
  membership characterisation uses the standard identity
  `φ.symm '' (φ.target ∩ T) = φ.source ∩ φ ⁻¹' T`.

* `OpenPartialHomeomorph.chart_local_detour_of_pathConnected_complement` — the
  chip-specific corollary. If `C ⊆ X` is finite and the chart-image complement
  `φ.target \ φ '' (φ.source ∩ C)` is path-connected (the rank-`> 1` mathlib
  lemma `Set.Countable.isPathConnected_compl_of_one_lt_rank` provides this for
  charts whose target is the whole vector space), then any two points
  `p, q ∈ φ.source` with `p, q ∉ C` are joined inside `Cᶜ ∩ φ.source`.

These two lemmas together close the chart-local detour step in the broader
"connectivity globalization minus finitely many critical points" pipeline.

No `axiom`, no gaps. The mathematical content reduces to
`OpenPartialHomeomorph.image_eq_target_inter_inv_preimage` plus
`JoinedIn.map_continuousOn`.
-/

noncomputable section

open Set Function Filter
open scoped Topology

namespace Jacobians.Discharge

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Generic chart-side detour pull-back.**
If `φ : X → Y` is an open partial homeomorphism and two chart images
`φ p₀`, `φ q₀` are joined inside `φ.target ∩ T` (for some `T : Set Y`) with
`p₀, q₀ ∈ φ.source`, then `p₀` and `q₀` themselves are joined inside
`φ.source ∩ φ ⁻¹' T`. The path is the chart-pullback `φ.symm ∘ γ` of any
chart-side path; correctness of the target set uses the standard identity
`φ.symm '' (φ.target ∩ T) = φ.source ∩ φ ⁻¹' T`. -/
theorem joinedIn_symm_image_of_target
    (φ : _root_.OpenPartialHomeomorph X Y) (T : Set Y) {p₀ q₀ : X}
    (hp : p₀ ∈ φ.source) (hq : q₀ ∈ φ.source)
    (hjoin : JoinedIn (φ.target ∩ T) (φ p₀) (φ q₀)) :
    JoinedIn (φ.source ∩ φ ⁻¹' T) p₀ q₀ := by
  -- `φ.symm` is continuous on `φ.target`, hence on `φ.target ∩ T`.
  have hsymm_cont : ContinuousOn φ.symm (φ.target ∩ T) :=
    φ.continuousOn_symm.mono inter_subset_left
  -- Pull the path back along `φ.symm`. This gives a JoinedIn on the
  -- image `φ.symm '' (φ.target ∩ T)` between `φ.symm (φ p₀) = p₀` and
  -- `φ.symm (φ q₀) = q₀`.
  have hmap0 :=
    hjoin.map_continuousOn (f := φ.symm) hsymm_cont
  -- Endpoint cleanup: `φ.symm (φ p₀) = p₀` and `φ.symm (φ q₀) = q₀`.
  have hp_inv : φ.symm (φ p₀) = p₀ := φ.left_inv hp
  have hq_inv : φ.symm (φ q₀) = q₀ := φ.left_inv hq
  rw [hp_inv, hq_inv] at hmap0
  -- The set `φ.symm '' (φ.target ∩ T)` equals `φ.source ∩ φ ⁻¹' T`.
  -- Use `OpenPartialHomeomorph.symm.image_source_inter_eq'` (where
  -- `φ.symm.source = φ.target`, `(φ.symm).symm = φ`).
  have hset_eq : φ.symm '' (φ.target ∩ T) = φ.source ∩ φ ⁻¹' T := by
    -- `φ.symm '' (φ.symm.source ∩ T) = φ.symm.target ∩ φ.symm.symm ⁻¹' T`
    -- and `φ.symm.symm = φ`, `φ.symm.target = φ.source`,
    -- `φ.symm.source = φ.target`.
    have h := φ.symm.image_source_inter_eq' (s := T)
    -- `h : φ.symm '' (φ.symm.source ∩ T) = φ.symm.target ∩ (φ.symm).symm ⁻¹' T`
    -- All four substitutions are by `rfl` on the structure level.
    simpa [PartialEquiv.symm_source, PartialEquiv.symm_target] using h
  rw [hset_eq] at hmap0
  exact hmap0

/-- **Chart-local detour, finite obstruction.**
If `φ : X → Y` is an open partial homeomorphism, `C : Set X` is finite, and the
chart-image complement `φ.target \ φ '' (φ.source ∩ C)` is path-connected, then
any two points `p, q ∈ φ.source` with `p ∉ C`, `q ∉ C` are joined inside
`Cᶜ ∩ φ.source` (i.e. by a path entirely in `φ.source` avoiding `C`). -/
theorem chart_local_detour_of_pathConnected_complement
    (φ : _root_.OpenPartialHomeomorph X Y) {C : Set X} (_hC_fin : C.Finite)
    (hPC : IsPathConnected (φ.target \ φ '' (φ.source ∩ C)))
    {p q : X} (hp : p ∈ φ.source) (hq : q ∈ φ.source)
    (hp_notin : p ∉ C) (hq_notin : q ∉ C) :
    JoinedIn (Cᶜ ∩ φ.source : Set X) p q := by
  -- The chart images `φ p`, `φ q` lie in the path-connected complement.
  have hφp_target : φ p ∈ φ.target := φ.map_source hp
  have hφq_target : φ q ∈ φ.target := φ.map_source hq
  -- Injectivity on `φ.source` rules out `φ p ∈ φ '' (φ.source ∩ C)`.
  have inj_image : ∀ {z : X}, z ∈ φ.source ∩ C →
      ∀ {w : X}, w ∈ φ.source → φ z = φ w → z = w := by
    intro z hz w hw hzw
    have h1 : φ.symm (φ z) = z := φ.left_inv hz.1
    have h2 : φ.symm (φ w) = w := φ.left_inv hw
    calc z = φ.symm (φ z) := h1.symm
      _ = φ.symm (φ w) := by rw [hzw]
      _ = w := h2
  have hφp_notin : φ p ∉ φ '' (φ.source ∩ C) := by
    rintro ⟨z, hz, hz_eq⟩
    exact hp_notin (inj_image hz hp hz_eq ▸ hz.2)
  have hφq_notin : φ q ∉ φ '' (φ.source ∩ C) := by
    rintro ⟨z, hz, hz_eq⟩
    exact hq_notin (inj_image hz hq hz_eq ▸ hz.2)
  have hφp_mem : φ p ∈ φ.target \ φ '' (φ.source ∩ C) := ⟨hφp_target, hφp_notin⟩
  have hφq_mem : φ q ∈ φ.target \ φ '' (φ.source ∩ C) := ⟨hφq_target, hφq_notin⟩
  -- Path-connected complement gives a chart-side path.
  have hjoin_image : JoinedIn (φ.target \ φ '' (φ.source ∩ C)) (φ p) (φ q) :=
    hPC.joinedIn _ hφp_mem _ hφq_mem
  -- Reformulate as `JoinedIn (φ.target ∩ T)` with `T = (φ '' (φ.source ∩ C))ᶜ`.
  have hjoin_image' :
      JoinedIn (φ.target ∩ (φ '' (φ.source ∩ C))ᶜ) (φ p) (φ q) :=
    hjoin_image.mono (fun _ hy => ⟨hy.1, hy.2⟩)
  -- Generic pull-back gives JoinedIn on `φ.source ∩ φ ⁻¹' (φ '' (φ.source ∩ C))ᶜ`.
  have hpull :=
    joinedIn_symm_image_of_target (φ := φ)
      (T := (φ '' (φ.source ∩ C))ᶜ) hp hq hjoin_image'
  -- Show that target set is contained in `Cᶜ ∩ φ.source`.
  refine hpull.mono ?_
  intro y hy
  obtain ⟨hy_src, hy_pre⟩ := hy
  refine ⟨?_, hy_src⟩
  -- `hy_pre : y ∈ φ ⁻¹' (φ '' (φ.source ∩ C))ᶜ`, i.e. `φ y ∉ φ '' (φ.source ∩ C)`.
  -- Suppose `y ∈ C`. Then `⟨y, hy_src, ‹y ∈ C›⟩` shows `φ y ∈ φ '' (φ.source ∩ C)`,
  -- contradiction.
  intro hyC
  exact hy_pre ⟨y, ⟨hy_src, hyC⟩, rfl⟩

/-- **Specialisation to charts modelled on `ℂ` with full target `Set.univ`.**
For an open partial homeomorphism `φ : X → ℂ` whose target is the whole plane
`Set.univ` (e.g. a global complex chart), and any finite obstruction `C ⊆ X`,
two points `p, q ∈ φ.source \ C` are joined in `Cᶜ ∩ φ.source` by a path. The
path-connectedness of `ℂ \ φ '' (φ.source ∩ C)` is supplied by
`Set.Countable.isPathConnected_compl_of_one_lt_rank` together with
`Complex.rank_real_complex` (which gives `1 < Module.rank ℝ ℂ`). -/
theorem chart_local_detour_of_target_univ_complex
    (φ : _root_.OpenPartialHomeomorph X ℂ) (h_target : φ.target = Set.univ)
    {C : Set X} (hC_fin : C.Finite)
    {p q : X} (hp : p ∈ φ.source) (hq : q ∈ φ.source)
    (hp_notin : p ∉ C) (hq_notin : q ∉ C) :
    JoinedIn (Cᶜ ∩ φ.source : Set X) p q := by
  -- The image of `φ.source ∩ C` under `φ` is finite, hence countable.
  have h_img_fin : (φ '' (φ.source ∩ C)).Finite :=
    (hC_fin.inter_of_right φ.source).image φ
  have h_img_countable : (φ '' (φ.source ∩ C)).Countable := h_img_fin.countable
  -- `1 < Module.rank ℝ ℂ`.
  have h_rank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact_mod_cast (Nat.one_lt_two)
  -- Path-connectedness of the complement in the whole plane.
  have h_compl_pc : IsPathConnected ((φ '' (φ.source ∩ C))ᶜ : Set ℂ) :=
    h_img_countable.isPathConnected_compl_of_one_lt_rank h_rank
  -- Rewrite to `φ.target \ φ '' (φ.source ∩ C)` using `φ.target = univ`.
  have h_eq : φ.target \ φ '' (φ.source ∩ C) = (φ '' (φ.source ∩ C))ᶜ := by
    rw [h_target]; ext z; simp
  have hPC : IsPathConnected (φ.target \ φ '' (φ.source ∩ C)) := h_eq ▸ h_compl_pc
  exact chart_local_detour_of_pathConnected_complement
    (φ := φ) hC_fin hPC hp hq hp_notin hq_notin

end OpenPartialHomeomorph

end Jacobians.Discharge
