/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Card

set_option autoImplicit true

/-! # Fibre cardinality is locally constant from a Hurwitz-style patching package (ZZ153)

## What this file proves

Given `f : X → Y` and a *target point* `y₀ : Y` whose preimage `f ⁻¹' {y₀}`
admits a finite "Hurwitz patching package" `HurwitzPatchingData`:

* a finite indexing of the preimage `xs : Finset X` with `↑xs = f ⁻¹' {y₀}`;
* for each `x ∈ xs`, an open neighbourhood `U x` of `x`;
* the `U x` are pairwise disjoint;
* for each `x ∈ xs`, an open set `V x` of `Y` containing `y₀` such that
  `f` maps `U x` into `V x`, is *injective* on `U x`, and is *surjective*
  from `U x` onto `V x`;
* a *covering neighbourhood* `W` of `y₀` with `W ⊆ V x` for every `x ∈ xs`,
  satisfying `f ⁻¹' W ⊆ ⋃ x ∈ xs, U x` (every preimage of a point in `W`
  lies in one of the sheets).

Then for **every** `y ∈ W`, the fibre `f ⁻¹' {y}` has cardinality
`xs.card = (f ⁻¹' {y₀}).ncard`.

This is the *patching* content of the classical "regular value of a non-constant
analytic map between Riemann surfaces ⇒ fibre count is locally constant" fact.
The hypothesis `HurwitzPatchingData` is exactly what `analytic_local_normal_form`
(ZZ151, k = 1 at a regular value) plus the inverse function theorem deliver
when packaged across all preimages of `y₀` and the local sheets are intersected.

## Status

Purely topological / structural. No `axiom`, no gaps. Single new file. -/

@[expose] public section

open Set

namespace Jacobians.Discharge

universe u v

/-- **Hurwitz patching package** for `f : X → Y` at a target point `y₀ : Y`.

Bundles the data needed to conclude that `f` is, in a topological neighbourhood
of `f ⁻¹' {y₀}`, a disjoint union of `xs.card` homeomorphic sheets onto a
common neighbourhood of `y₀`. From this, the cardinality of `f ⁻¹' {y}` is
constant for `y` near `y₀` (and equals `xs.card`). -/
structure HurwitzPatchingData {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (y₀ : Y) where
  /-- Finite enumeration of the preimage `f ⁻¹' {y₀}`. -/
  xs : Finset X
  /-- A sheet `U x` around each preimage point `x ∈ xs`. -/
  U : X → Set X
  /-- Each sheet is open. -/
  U_open : ∀ x ∈ xs, IsOpen (U x)
  /-- Each sheet contains the corresponding preimage point. -/
  mem_U_self : ∀ x ∈ xs, x ∈ U x
  /-- Sheets indexed by distinct preimage points are disjoint. -/
  U_pairwiseDisjoint : ∀ x ∈ xs, ∀ x' ∈ xs, x ≠ x' → Disjoint (U x) (U x')
  /-- A common image neighbourhood `V x` for each sheet. -/
  V : X → Set Y
  /-- Each `V x` contains `y₀`. -/
  y₀_mem_V : ∀ x ∈ xs, y₀ ∈ V x
  /-- `f` is *injective* on each sheet `U x`. -/
  f_injOn : ∀ x ∈ xs, InjOn f (U x)
  /-- `f` is *surjective* from `U x` onto `V x`: every point of `V x` has a
      preimage in `U x`. -/
  f_surjOn : ∀ x ∈ xs, SurjOn f (U x) (V x)
  /-- A common open covering neighbourhood `W` of `y₀`. -/
  W : Set Y
  /-- `W` is open. -/
  W_open : IsOpen W
  /-- `W` contains `y₀`. -/
  y₀_mem_W : y₀ ∈ W
  /-- `W` lies inside every `V x`. -/
  W_subset_V : ∀ x ∈ xs, W ⊆ V x
  /-- Every preimage of a point in `W` lies in one of the sheets. -/
  preimage_W_subset : f ⁻¹' W ⊆ ⋃ x ∈ xs, U x

namespace HurwitzPatchingData

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y} {y₀ : Y}

/-- For `y ∈ h.W`, the cardinality of the fibre `f ⁻¹' {y}` equals `h.xs.card`. -/
lemma fibre_ncard_eq_xs_card_of_mem_W
    (h : HurwitzPatchingData f y₀)
    {y : Y} (hy : y ∈ h.W) :
    (f ⁻¹' {y}).ncard = h.xs.card := by
  classical
  -- For each x ∈ xs, choose the unique preimage in U x mapping to y.
  have h_choose : ∀ x ∈ h.xs, ∃ z, z ∈ h.U x ∧ f z = y := by
    intro x hx
    have hyVx : y ∈ h.V x := h.W_subset_V x hx hy
    obtain ⟨z, hzU, hzy⟩ := h.f_surjOn x hx hyVx
    exact ⟨z, hzU, hzy⟩
  -- Build the function picking the preimage in each sheet.
  let pick : (x : X) → x ∈ h.xs → X := fun x hx => (h_choose x hx).choose
  have pick_spec : ∀ (x : X) (hx : x ∈ h.xs),
      pick x hx ∈ h.U x ∧ f (pick x hx) = y := fun x hx => (h_choose x hx).choose_spec
  -- Build the Finset of preimages.
  let s : Finset X := h.xs.attach.image (fun a => pick a.1 a.2)
  -- Step 1: |s| = |h.xs|.
  have h_inj : Set.InjOn (fun a : {a // a ∈ h.xs} => pick a.1 a.2)
      (h.xs.attach : Set {a // a ∈ h.xs}) := by
    intro a _ b _ hab
    have hUa : pick a.1 a.2 ∈ h.U a.1 := (pick_spec a.1 a.2).1
    have hUb : pick b.1 b.2 ∈ h.U b.1 := (pick_spec b.1 b.2).1
    by_contra hne
    have hlab : a.1 ≠ b.1 := fun heq => hne (Subtype.ext heq)
    have hdisj : Disjoint (h.U a.1) (h.U b.1) :=
      h.U_pairwiseDisjoint a.1 a.2 b.1 b.2 hlab
    -- pick a = pick b ∈ U a and ∈ U b: contradicts disjointness.
    have hpa : pick a.1 a.2 ∈ h.U a.1 := hUa
    have hab' : pick a.1 a.2 = pick b.1 b.2 := hab
    have hpb : pick a.1 a.2 ∈ h.U b.1 := by rw [hab']; exact hUb
    exact Set.disjoint_left.mp hdisj hpa hpb
  have hs_card : s.card = h.xs.card := by
    have hcard_image : s.card = h.xs.attach.card :=
      Finset.card_image_of_injOn h_inj
    have : h.xs.attach.card = h.xs.card := Finset.card_attach
    omega
  -- Step 2: ↑s = f ⁻¹' {y}.
  have hs_eq : (s : Set X) = f ⁻¹' {y} := by
    ext z
    constructor
    · -- z ∈ s → f z = y
      intro hz
      simp only [s, Finset.coe_image, Finset.coe_attach, Set.mem_image,
        Set.mem_univ, true_and] at hz
      obtain ⟨a, ha_eq⟩ := hz
      have hfp : f (pick a.1 a.2) = y := (pick_spec a.1 a.2).2
      show f z = y
      rw [← ha_eq]; exact hfp
    · -- f z = y → z ∈ s
      intro hz
      have hzy : f z = y := hz
      have hzW : z ∈ f ⁻¹' h.W := by
        show f z ∈ h.W; rw [hzy]; exact hy
      have hz_in_union := h.preimage_W_subset hzW
      rw [Set.mem_iUnion₂] at hz_in_union
      obtain ⟨x, hxxs, hzUx⟩ := hz_in_union
      -- z is in U x. We need z = pick x hxxs (since both lie in U x and map to y).
      have hpick_in : pick x hxxs ∈ h.U x := (pick_spec x hxxs).1
      have hpick_y : f (pick x hxxs) = y := (pick_spec x hxxs).2
      have hz_eq : z = pick x hxxs := by
        apply h.f_injOn x hxxs hzUx hpick_in
        rw [hzy, hpick_y]
      -- so z is in s.
      simp only [s, Finset.coe_image, Finset.coe_attach, Set.mem_image,
        Set.mem_univ, true_and]
      exact ⟨⟨x, hxxs⟩, hz_eq.symm⟩
  -- Step 3: rewrite ncard.
  rw [← hs_eq, Set.ncard_coe_finset]
  exact hs_card

end HurwitzPatchingData

/-- **Local-constancy of fibre count from a pointwise Hurwitz package.**

Suppose for *every* `y₀ : Y` we are given a `HurwitzPatchingData f y₀`. Then
the fibre-cardinality function `fun y => (f ⁻¹' {y}).ncard` is locally constant
on `Y`.

The witness `h y₀` provides the open neighbourhood `(h y₀).W` of `y₀` on which
the fibre count is constantly `(h y₀).xs.card`, which equals
`(f ⁻¹' {y₀}).ncard`. -/
theorem fibreCard_isLocallyConstant_of_pointwiseHurwitz
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (h : ∀ y₀ : Y, HurwitzPatchingData f y₀) :
    IsLocallyConstant (fun y : Y => (f ⁻¹' {y}).ncard) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y₀
  have hW_mem : (h y₀).W ∈ nhds y₀ :=
    (h y₀).W_open.mem_nhds (h y₀).y₀_mem_W
  filter_upwards [hW_mem] with y hy
  have h_y : (f ⁻¹' {y}).ncard = (h y₀).xs.card :=
    (h y₀).fibre_ncard_eq_xs_card_of_mem_W hy
  have h_y₀ : (f ⁻¹' {y₀}).ncard = (h y₀).xs.card :=
    (h y₀).fibre_ncard_eq_xs_card_of_mem_W (h y₀).y₀_mem_W
  rw [h_y, h_y₀]

/-- **Local-constancy on a regular subset.**

Suppose `R : Set Y` and for *every* `y₀ ∈ R` we are given a
`HurwitzPatchingData f y₀`. Then the fibre-cardinality function (read from
the subtype) is locally constant on `R`. -/
theorem fibreCard_isLocallyConstant_on_subset_of_pointwiseHurwitz
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (R : Set Y)
    (h : ∀ y₀ ∈ R, HurwitzPatchingData f y₀) :
    IsLocallyConstant
      (fun y : (R : Set Y) => (f ⁻¹' {y.val}).ncard) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y₀
  let pkg := h y₀.val y₀.property
  have hW_amb : pkg.W ∈ nhds y₀.val := pkg.W_open.mem_nhds pkg.y₀_mem_W
  have hW_sub : ∀ᶠ y in nhds y₀, y.val ∈ pkg.W :=
    (continuous_subtype_val.tendsto y₀).eventually hW_amb
  filter_upwards [hW_sub] with y hy
  have h_y : (f ⁻¹' {y.val}).ncard = pkg.xs.card :=
    pkg.fibre_ncard_eq_xs_card_of_mem_W hy
  have h_y₀ : (f ⁻¹' {y₀.val}).ncard = pkg.xs.card :=
    pkg.fibre_ncard_eq_xs_card_of_mem_W pkg.y₀_mem_W
  rw [h_y, h_y₀]

end Jacobians.Discharge

end
