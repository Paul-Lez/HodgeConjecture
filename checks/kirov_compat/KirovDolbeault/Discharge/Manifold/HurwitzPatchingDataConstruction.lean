/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.FibreCardLocallyConstantFromNormalForm
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousOn

set_option autoImplicit true

/-! # Constructing `HurwitzPatchingData` at a regular value (ZZ157)

ZZ153 packaged the Hurwitz patching content of "regular value of a non-constant
analytic map between Riemann surfaces ⇒ fibre count is locally constant" into
the structure `HurwitzPatchingData f y₀`. This file constructs such a package
from purely topological inputs.

## Topological inputs (`LocalSheetData`)

At each preimage `x ∈ f ⁻¹' {y₀}`, we ask for:

* an open neighbourhood `U` of `x`,
* an open neighbourhood `V` of `y₀`,
* a *continuous local inverse* `g : Y → X` with `g (V) ⊆ U`, `LeftInvOn g f U`,
  `RightInvOn g f V`.

This is exactly the `OpenPartialHomeomorph`-shape data delivered by
`AnalyticAt.exists_local_biholomorphism` (ZZ152). From `LeftInvOn` and
`RightInvOn` we derive `InjOn f U` and `SurjOn f U V`, and from continuity of
`g` we derive that `f` restricted to `U` is an *open* map — which is exactly
what we need to shrink `U` and still have surjectivity onto a corresponding
shrunken `V`.

## Outputs

* `LocalSheetData` — the topological packaging of an analytic local
  biholomorphism.
* `exists_pairwiseDisjoint_open_of_finset` — finite-set ⇒ pairwise-disjoint
  open neighbourhoods in T2.
* `HurwitzPatchingData.ofLocalSheets` — the construction.

## Anti-cheat

* No `axiom`, no gaps.
* No signature change to any pre-existing definition or theorem.
* Adds one new file imported into the manifest.
-/

@[expose] public section

open Set Filter Topology

namespace Jacobians.Discharge

universe u v

/-- **Per-point local-sheet datum.** At a fibre point `x` of `f` over `y₀`,
the local-biholomorphism content packages into:

* an open neighbourhood `U` of `x`,
* an open neighbourhood `V` of `y₀`,
* a continuous local inverse `g : Y → X` with `g '' V ⊆ U`,
  `LeftInvOn g f U`, `RightInvOn g f V`.

In particular `f` is injective on `U` and surjective from `U` onto `V`. -/
structure LocalSheetData {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (y₀ : Y) (x : X) where
  /-- A neighbourhood `U` of `x`. -/
  U : Set X
  /-- `U` is open. -/
  U_open : IsOpen U
  /-- `x ∈ U`. -/
  mem_U : x ∈ U
  /-- A neighbourhood `V` of `y₀`. -/
  V : Set Y
  /-- `V` is open. -/
  V_open : IsOpen V
  /-- `y₀ ∈ V`. -/
  mem_V : y₀ ∈ V
  /-- `f` maps `U` into `V`. -/
  mapsTo : MapsTo f U V
  /-- A local inverse. -/
  g : Y → X
  /-- `g` continuous on `V`. -/
  g_continuousOn : ContinuousOn g V
  /-- `g` maps `V` into `U`. -/
  g_mapsTo : MapsTo g V U
  /-- `g` is a left inverse to `f` on `U`. -/
  leftInvOn : LeftInvOn g f U
  /-- `g` is a right inverse to `f` on `V`. -/
  rightInvOn : RightInvOn g f V

namespace LocalSheetData

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y} {y₀ : Y} {x : X}

/-- `f` is injective on `U`. -/
lemma injOn (s : LocalSheetData f y₀ x) : InjOn f s.U := s.leftInvOn.injOn

/-- `f` is surjective from `U` onto `V`. -/
lemma surjOn (s : LocalSheetData f y₀ x) : SurjOn f s.U s.V := by
  intro y hy
  refine ⟨s.g y, s.g_mapsTo hy, s.rightInvOn hy⟩

end LocalSheetData

/-- **Pairwise-disjoint open neighbourhoods of a finite set in a T2 space.**

For any `Finset X` in a T2 space, there is a function `W : X → Set X` such
that for every `x ∈ s`, `W x` is open and contains `x`, and `W x` and `W x'`
are disjoint for distinct `x, x' ∈ s`. -/
lemma exists_pairwiseDisjoint_open_of_finset
    {X : Type u} [TopologicalSpace X] [T2Space X] (s : Finset X) :
    ∃ W : X → Set X,
      (∀ x ∈ s, IsOpen (W x)) ∧
      (∀ x ∈ s, x ∈ W x) ∧
      (∀ x ∈ s, ∀ x' ∈ s, x ≠ x' → Disjoint (W x) (W x')) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun _ => Set.univ, ?_, ?_, ?_⟩
      · intros; exact isOpen_univ
      · intros _ hx; simp at hx
      · intros _ hx; simp at hx
  | insert a s ha ih =>
      obtain ⟨W₀, hW₀_open, hW₀_mem, hW₀_disj⟩ := ih
      -- For each x ∈ s, separate a from x.
      let sep : (x : X) → x ∈ s → {p : Set X × Set X //
          IsOpen p.1 ∧ IsOpen p.2 ∧ a ∈ p.1 ∧ x ∈ p.2 ∧ Disjoint p.1 p.2} :=
        fun x hx => by
          have hax : a ≠ x := fun h => ha (h ▸ hx)
          have htri := t2_separation hax
          refine ⟨(htri.choose, htri.choose_spec.choose), ?_, ?_, ?_, ?_, ?_⟩
          · exact htri.choose_spec.choose_spec.1
          · exact htri.choose_spec.choose_spec.2.1
          · exact htri.choose_spec.choose_spec.2.2.1
          · exact htri.choose_spec.choose_spec.2.2.2.1
          · exact htri.choose_spec.choose_spec.2.2.2.2
      let Afun : (x : X) → x ∈ s → Set X := fun x hx => (sep x hx).1.1
      let Bfun : (x : X) → x ∈ s → Set X := fun x hx => (sep x hx).1.2
      have hA_open : ∀ x (hx : x ∈ s), IsOpen (Afun x hx) := fun x hx => (sep x hx).2.1
      have hB_open : ∀ x (hx : x ∈ s), IsOpen (Bfun x hx) := fun x hx => (sep x hx).2.2.1
      have hA_mem : ∀ x (hx : x ∈ s), a ∈ Afun x hx := fun x hx => (sep x hx).2.2.2.1
      have hB_mem : ∀ x (hx : x ∈ s), x ∈ Bfun x hx := fun x hx => (sep x hx).2.2.2.2.1
      have hAB_disj : ∀ x (hx : x ∈ s), Disjoint (Afun x hx) (Bfun x hx) :=
        fun x hx => (sep x hx).2.2.2.2.2
      let W : X → Set X := fun y =>
        if y = a then ⋂ (p : {x // x ∈ s}), Afun p.1 p.2
        else if hy : y ∈ s then W₀ y ∩ Bfun y hy
        else Set.univ
      refine ⟨W, ?_, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with heq | hy_in_s
        · subst heq
          simp only [W, if_pos rfl]
          exact isOpen_iInter_of_finite (fun p => hA_open p.1 p.2)
        · have hya : y ≠ a := fun heq => ha (heq ▸ hy_in_s)
          simp only [W, if_neg hya, dif_pos hy_in_s]
          exact (hW₀_open y hy_in_s).inter (hB_open y hy_in_s)
      · intro y hy
        rcases Finset.mem_insert.mp hy with heq | hy_in_s
        · subst heq
          simp only [W, if_pos rfl]
          rw [mem_iInter]; intro p; exact hA_mem p.1 p.2
        · have hya : y ≠ a := fun heq => ha (heq ▸ hy_in_s)
          simp only [W, if_neg hya, dif_pos hy_in_s]
          exact ⟨hW₀_mem y hy_in_s, hB_mem y hy_in_s⟩
      · intro y hy y' hy' hne
        rcases Finset.mem_insert.mp hy with heq | hy_s
        · subst heq
          rcases Finset.mem_insert.mp hy' with heq' | hy'_s
          · exact (hne heq'.symm).elim
          · have hy'a : y' ≠ y := fun heq => ha (heq ▸ hy'_s)
            simp only [W, if_pos rfl, if_neg hy'a, dif_pos hy'_s]
            rw [Set.disjoint_left]
            intro z hzA hzWB
            have hzA_y' : z ∈ Afun y' hy'_s := mem_iInter.mp hzA ⟨y', hy'_s⟩
            have hzB : z ∈ Bfun y' hy'_s := hzWB.2
            exact Set.disjoint_left.mp (hAB_disj y' hy'_s) hzA_y' hzB
        · rcases Finset.mem_insert.mp hy' with heq' | hy'_s
          · subst heq'
            have hya : y ≠ y' := fun heq => ha (heq ▸ hy_s)
            simp only [W, if_neg hya, if_pos rfl, dif_pos hy_s]
            rw [Set.disjoint_left]
            intro z hzWB hzA
            have hzA_y : z ∈ Afun y hy_s := mem_iInter.mp hzA ⟨y, hy_s⟩
            have hzB : z ∈ Bfun y hy_s := hzWB.2
            exact Set.disjoint_left.mp (hAB_disj y hy_s) hzA_y hzB
          · have hya : y ≠ a := fun heq => ha (heq ▸ hy_s)
            have hy'a : y' ≠ a := fun heq => ha (heq ▸ hy'_s)
            simp only [W, if_neg hya, if_neg hy'a, dif_pos hy_s, dif_pos hy'_s]
            exact (hW₀_disj y hy_s y' hy'_s hne).mono inter_subset_left inter_subset_left

namespace HurwitzPatchingData

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]

/-- **Construction of `HurwitzPatchingData` from per-point local-sheet data.**

Given:
* `f : X → Y` continuous,
* `X` compact T2, `Y` T2,
* `y₀ : Y` and a *finite* fibre `f ⁻¹' {y₀}`,
* a `LocalSheetData f y₀ x` for every `x ∈ f ⁻¹' {y₀}`,

construct a `HurwitzPatchingData f y₀`. -/
noncomputable def ofLocalSheets
    [T2Space X] [CompactSpace X] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {y₀ : Y}
    (h_fib : (f ⁻¹' {y₀}).Finite)
    (sheets : ∀ x ∈ f ⁻¹' {y₀}, LocalSheetData f y₀ x) :
    HurwitzPatchingData f y₀ := by
  classical
  set xs : Finset X := h_fib.toFinset with hxs_def
  have hxs_coe : (xs : Set X) = f ⁻¹' {y₀} := by
    simp [hxs_def, Set.Finite.coe_toFinset]
  have hxs_mem : ∀ x ∈ xs, x ∈ f ⁻¹' {y₀} := fun x hx => by
    have : x ∈ (xs : Set X) := hx
    rw [hxs_coe] at this; exact this
  have hxs_fmem : ∀ x ∈ xs, f x = y₀ := fun x hx => by
    have : x ∈ f ⁻¹' {y₀} := hxs_mem x hx; simpa using this
  -- For each x ∈ xs, pick a local sheet (extend by junk to all X).
  let sheet : (x : X) → x ∈ xs → LocalSheetData f y₀ x :=
    fun x hx => sheets x (hxs_mem x hx)
  -- Step 1: pairwise-disjoint open neighbourhoods.
  have hWsep_ex := exists_pairwiseDisjoint_open_of_finset (X := X) xs
  let Wsep : X → Set X := hWsep_ex.choose
  have hWsep_spec := hWsep_ex.choose_spec
  have hWsep_open : ∀ x ∈ xs, IsOpen (Wsep x) := hWsep_spec.1
  have hWsep_mem : ∀ x ∈ xs, x ∈ Wsep x := hWsep_spec.2.1
  have hWsep_disj : ∀ x ∈ xs, ∀ x' ∈ xs, x ≠ x' → Disjoint (Wsep x) (Wsep x') :=
    hWsep_spec.2.2
  -- U x := (sheet x).U ∩ Wsep x.
  -- V x := preimage of U x under g, restricted to (sheet x).V — i.e.,
  -- V x := (sheet x).V ∩ (sheet x).g ⁻¹' (Wsep x).
  -- Since (sheet x).g_continuousOn : ContinuousOn g V and Wsep x is open,
  -- (sheet x).g ⁻¹' (Wsep x) is open *in V x ambient*; intersected with V it's
  -- still open in Y (because (sheet x).V is open and ContinuousOn pulls back).
  let U : (x : X) → x ∈ xs → Set X := fun x hx =>
    (sheet x hx).U ∩ Wsep x
  let V : (x : X) → x ∈ xs → Set Y := fun x hx =>
    (sheet x hx).V ∩ ((sheet x hx).g ⁻¹' (Wsep x))
  have U_open : ∀ x (hx : x ∈ xs), IsOpen (U x hx) :=
    fun x hx => (sheet x hx).U_open.inter (hWsep_open x hx)
  have U_mem : ∀ x (hx : x ∈ xs), x ∈ U x hx :=
    fun x hx => ⟨(sheet x hx).mem_U, hWsep_mem x hx⟩
  -- V x is open: (sheet x).V is open; ContinuousOn g V means there is open O
  -- in Y with V ∩ g ⁻¹' (Wsep x) = V ∩ O. Use `ContinuousOn.preimage_isOpen_of_open`?
  -- Cleaner: use `ContinuousOn.isOpen_preimage` (if available) or unfold:
  -- ContinuousOn g V ↔ ∀ open U₀, ∃ open O, V ∩ g ⁻¹' U₀ = V ∩ O.
  -- Mathlib: `ContinuousOn.preimage_open_of_open` or `IsOpen.preimage_inter_continuousOn`.
  have V_open : ∀ x (hx : x ∈ xs), IsOpen (V x hx) := by
    intro x hx
    have hcont : ContinuousOn (sheet x hx).g (sheet x hx).V := (sheet x hx).g_continuousOn
    have hWsep_op : IsOpen (Wsep x) := hWsep_open x hx
    -- `continuousOn_iff'`: ContinuousOn g s ↔ ∀ open t, ∃ u open,
    --   g ⁻¹' t ∩ s = u ∩ s.
    rw [continuousOn_iff'] at hcont
    obtain ⟨u, hu_open, hu_eq⟩ := hcont (Wsep x) hWsep_op
    show IsOpen ((sheet x hx).V ∩ (sheet x hx).g ⁻¹' Wsep x)
    -- (sheet x).V ∩ g ⁻¹' Wsep x = g ⁻¹' Wsep x ∩ (sheet x).V = u ∩ (sheet x).V
    rw [Set.inter_comm, hu_eq]
    exact hu_open.inter (sheet x hx).V_open
  have y₀_mem_V : ∀ x (hx : x ∈ xs), y₀ ∈ V x hx := by
    intro x hx
    refine ⟨(sheet x hx).mem_V, ?_⟩
    -- g(y₀) = x (since g(f x) = x via leftInvOn and f x = y₀)
    have hgy₀ : (sheet x hx).g y₀ = x := by
      have : (sheet x hx).g (f x) = x := (sheet x hx).leftInvOn (sheet x hx).mem_U
      rw [hxs_fmem x hx] at this; exact this
    show (sheet x hx).g y₀ ∈ Wsep x
    rw [hgy₀]; exact hWsep_mem x hx
  have mapsTo_U_V : ∀ x (hx : x ∈ xs), MapsTo f (U x hx) (V x hx) := by
    intro x hx z hz
    have hz_in_sheetU : z ∈ (sheet x hx).U := hz.1
    have hz_in_Wsep : z ∈ Wsep x := hz.2
    refine ⟨(sheet x hx).mapsTo hz_in_sheetU, ?_⟩
    -- g(f z) = z (from leftInvOn) ∈ Wsep x.
    show (sheet x hx).g (f z) ∈ Wsep x
    rw [(sheet x hx).leftInvOn hz_in_sheetU]
    exact hz_in_Wsep
  have injOn_f_U : ∀ x (hx : x ∈ xs), InjOn f (U x hx) := by
    intro x hx
    exact (sheet x hx).injOn.mono (fun z hz => hz.1)
  have surjOn_f_U_V : ∀ x (hx : x ∈ xs), SurjOn f (U x hx) (V x hx) := by
    intro x hx y hy
    have hy_V : y ∈ (sheet x hx).V := hy.1
    have hy_g : (sheet x hx).g y ∈ Wsep x := hy.2
    refine ⟨(sheet x hx).g y, ?_, ?_⟩
    · exact ⟨(sheet x hx).g_mapsTo hy_V, hy_g⟩
    · exact (sheet x hx).rightInvOn hy_V
  -- Pairwise disjointness
  have U_disj : ∀ x (hx : x ∈ xs) x' (hx' : x' ∈ xs), x ≠ x' →
      Disjoint (U x hx) (U x' hx') := by
    intro x hx x' hx' hne
    exact (hWsep_disj x hx x' hx' hne).mono inter_subset_right inter_subset_right
  -- Step 2: define the common open neighbourhood W.
  -- K := X \ ⋃_{x ∈ xs} U x is closed (complement of a finite union of opens),
  -- and X is compact so K is compact.
  -- f K is compact in Y, hence closed in T2 Y.
  -- y₀ ∉ f K because every preimage of y₀ is in xs and xs ⊆ ⋃ U x.
  -- W₀ := Y \ f K is open and contains y₀.
  -- W := W₀ ∩ ⋂_{x ∈ xs} V x.
  let UnionU : Set X := ⋃ x ∈ xs, U x ‹_›
  -- We define UnionU more carefully via attach to handle dependent membership.
  -- Use Finset.attach.
  let UnionU' : Set X := ⋃ (p : {a // a ∈ xs}), U p.1 p.2
  have UnionU'_open : IsOpen UnionU' :=
    isOpen_iUnion (fun p => U_open p.1 p.2)
  have xs_subset_UnionU' : (xs : Set X) ⊆ UnionU' := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact U_mem x hx
  have fibre_subset_UnionU' : f ⁻¹' {y₀} ⊆ UnionU' := by
    rw [← hxs_coe]; exact xs_subset_UnionU'
  let K : Set X := UnionU'ᶜ
  have K_closed : IsClosed K := UnionU'_open.isClosed_compl
  have K_compact : IsCompact K := K_closed.isCompact
  have fK_compact : IsCompact (f '' K) := K_compact.image hf
  have fK_closed : IsClosed (f '' K) := fK_compact.isClosed
  have y₀_notin_fK : y₀ ∉ f '' K := by
    rintro ⟨z, hzK, hzfy⟩
    have hz_fib : z ∈ f ⁻¹' {y₀} := by simpa using hzfy
    exact hzK (fibre_subset_UnionU' hz_fib)
  let W₀ : Set Y := (f '' K)ᶜ
  have W₀_open : IsOpen W₀ := fK_closed.isOpen_compl
  have y₀_mem_W₀ : y₀ ∈ W₀ := y₀_notin_fK
  let InterV : Set Y := ⋂ (p : {a // a ∈ xs}), V p.1 p.2
  have InterV_open : IsOpen InterV :=
    isOpen_iInter_of_finite (fun p => V_open p.1 p.2)
  have y₀_mem_InterV : y₀ ∈ InterV := by
    rw [mem_iInter]; intro p; exact y₀_mem_V p.1 p.2
  let W : Set Y := W₀ ∩ InterV
  have W_open : IsOpen W := W₀_open.inter InterV_open
  have y₀_mem_W : y₀ ∈ W := ⟨y₀_mem_W₀, y₀_mem_InterV⟩
  have W_subset_V : ∀ x (hx : x ∈ xs), W ⊆ V x hx := by
    intro x hx y hy
    have : y ∈ InterV := hy.2
    exact mem_iInter.mp this ⟨x, hx⟩
  -- Now assemble HurwitzPatchingData.
  refine
    { xs := xs
      U := fun x => if hx : x ∈ xs then U x hx else ∅
      U_open := ?U_open
      mem_U_self := ?mem_U_self
      U_pairwiseDisjoint := ?U_disj
      V := fun x => if hx : x ∈ xs then V x hx else Set.univ
      y₀_mem_V := ?y₀_mem_V
      f_injOn := ?f_injOn
      f_surjOn := ?f_surjOn
      W := W
      W_open := W_open
      y₀_mem_W := y₀_mem_W
      W_subset_V := ?W_subset_V
      preimage_W_subset := ?preimage_W_subset }
  · intro x hx
    show IsOpen (if hx : x ∈ xs then U x hx else ∅)
    rw [dif_pos hx]; exact U_open x hx
  · intro x hx
    show x ∈ (if hx : x ∈ xs then U x hx else ∅)
    rw [dif_pos hx]; exact U_mem x hx
  · intro x hx x' hx' hne
    show Disjoint (if hx : x ∈ xs then U x hx else ∅) (if hx' : x' ∈ xs then U x' hx' else ∅)
    rw [dif_pos hx, dif_pos hx']
    exact U_disj x hx x' hx' hne
  · intro x hx
    show y₀ ∈ (if hx : x ∈ xs then V x hx else Set.univ)
    rw [dif_pos hx]; exact y₀_mem_V x hx
  · intro x hx
    show InjOn f (if hx : x ∈ xs then U x hx else ∅)
    rw [dif_pos hx]; exact injOn_f_U x hx
  · intro x hx
    show SurjOn f (if hx : x ∈ xs then U x hx else ∅) (if hx : x ∈ xs then V x hx else Set.univ)
    rw [dif_pos hx, dif_pos hx]
    exact surjOn_f_U_V x hx
  · intro x hx
    show W ⊆ (if hx : x ∈ xs then V x hx else Set.univ)
    rw [dif_pos hx]
    intro y hy; exact W_subset_V x hx hy
  · -- preimage_W_subset : f ⁻¹' W ⊆ ⋃ x ∈ xs, (if hx : x ∈ xs then U x hx else ∅)
    intro z hz
    have hzfW₀ : f z ∈ W₀ := hz.1
    have hzK_neg : z ∉ K := fun hzK => hzfW₀ ⟨z, hzK, rfl⟩
    have hz_in_unionU' : z ∈ UnionU' := by
      by_contra h; exact hzK_neg h
    rw [show UnionU' = ⋃ (p : {a // a ∈ xs}), U p.1 p.2 from rfl] at hz_in_unionU'
    rw [mem_iUnion] at hz_in_unionU'
    obtain ⟨p, hzp⟩ := hz_in_unionU'
    rw [mem_iUnion₂]
    refine ⟨p.1, p.2, ?_⟩
    show z ∈ (if hx : p.1 ∈ xs then U p.1 hx else ∅)
    rw [dif_pos p.2]; exact hzp

end HurwitzPatchingData

end Jacobians.Discharge

end
