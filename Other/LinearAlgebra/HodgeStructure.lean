/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Lemmas.LinearAlgebra.HodgeStructure
public import Mathlib.Algebra.DirectSum.Module

/-!
# Pure rational Hodge structures

This file adds Hodge filtrations, direct-sum coordinates, and constructions to
`HodgeStructure.Pure`. It proves that the filtration determines the Hodge pieces and that
rational classes in the middle filtration step are Hodge classes.
-/

@[expose] public noncomputable section

open scoped DirectSum TensorProduct

universe u

namespace HodgeStructure

variable (V : Type u) [AddCommGroup V] [Module ℚ V]

/-- Complex conjugation on the complexification, as a conjugate-linear map. -/
def conjugateSemilinear : ℂ ⊗[ℚ] V →ₗ⋆[ℂ] ℂ ⊗[ℚ] V where
  toFun := conjugate V
  map_add' := map_add _
  map_smul' c x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z v => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp [hx, hy]

@[simp]
lemma conjugateSemilinear_apply (x : ℂ ⊗[ℚ] V) :
    conjugateSemilinear V x = conjugate V x := rfl

@[simp]
lemma conjugate_eq_zero_iff (x : ℂ ⊗[ℚ] V) : conjugate V x = 0 ↔ x = 0 :=
  ⟨fun h ↦ by simpa using congrArg (conjugate V) h, fun h ↦ by simp [h]⟩

namespace Pure

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {n : ℕ}

@[ext]
lemma ext {H K : Pure V n} (h : H.piece = K.piece) : H = K := by
  cases H
  cases K
  cases h
  rfl

/-- The Hodge pieces span the whole complexification. -/
lemma iSup_piece_eq_top (H : Pure V n) :
    ⨆ pq : ℕ × ℕ, H.piece pq.1 pq.2 = ⊤ :=
  H.isInternal.submodule_iSup_eq_top

/-- Membership in a conjugate Hodge piece, with conjugation moved to the other side. -/
lemma mem_piece_conjugate_iff (H : Pure V n) (p q : ℕ) (x : ℂ ⊗[ℚ] V) :
    x ∈ H.piece p q ↔ conjugate V x ∈ H.piece q p :=
  (H.conjugate_mem_iff q p x).symm

/-- The direct-sum coordinates of a pure Hodge structure. -/
def decomposition (H : Pure V n) :
    ℂ ⊗[ℚ] V ≃ₗ[ℂ] (⨁ pq : ℕ × ℕ, H.piece pq.1 pq.2) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun pq : ℕ × ℕ ↦ H.piece pq.1 pq.2)
    H.isInternal).symm

/-- A vector in one Hodge piece has only that direct-sum coordinate. -/
lemma decomposition_apply_of_mem (H : Pure V n) {pq : ℕ × ℕ}
    {x : ℂ ⊗[ℚ] V} (hx : x ∈ H.piece pq.1 pq.2) :
    H.decomposition x =
      DirectSum.lof ℂ (ℕ × ℕ) (fun ab ↦ H.piece ab.1 ab.2) pq ⟨x, hx⟩ :=
  H.decomposition.symm.injective (by
    rw [LinearEquiv.symm_apply_apply]
    change x = DirectSum.coeLinearMap (fun ab : ℕ × ℕ ↦ H.piece ab.1 ab.2)
      (DirectSum.lof ℂ (ℕ × ℕ) (fun ab ↦ H.piece ab.1 ab.2) pq ⟨x, hx⟩)
    simp)

/-! ### Sums of pieces -/

/-- Sum of the Hodge pieces indexed by a set of bidegrees. -/
def pieceSum (H : Pure V n) (s : Set (ℕ × ℕ)) : Submodule ℂ (ℂ ⊗[ℚ] V) :=
  ⨆ pq, ⨆ (_ : pq ∈ s), H.piece pq.1 pq.2

lemma pieceSum_mono (H : Pure V n) {s t : Set (ℕ × ℕ)} (hst : s ⊆ t) :
    H.pieceSum s ≤ H.pieceSum t :=
  iSup₂_le fun pq hpq ↦ le_iSup₂_of_le pq (hst hpq) le_rfl

lemma piece_le_pieceSum (H : Pure V n) {s : Set (ℕ × ℕ)} {pq : ℕ × ℕ}
    (hpq : pq ∈ s) : H.piece pq.1 pq.2 ≤ H.pieceSum s :=
  le_iSup₂_of_le pq hpq le_rfl

@[simp]
lemma pieceSum_empty (H : Pure V n) : H.pieceSum ∅ = ⊥ := by
  simp [pieceSum]

@[simp]
lemma pieceSum_univ (H : Pure V n) : H.pieceSum Set.univ = ⊤ := by
  simp [pieceSum, H.iSup_piece_eq_top]

lemma pieceSum_singleton (H : Pure V n) (pq : ℕ × ℕ) :
    H.pieceSum {pq} = H.piece pq.1 pq.2 := by
  simp [pieceSum]

lemma pieceSum_union (H : Pure V n) (s t : Set (ℕ × ℕ)) :
    H.pieceSum (s ∪ t) = H.pieceSum s ⊔ H.pieceSum t := by
  apply le_antisymm
  · exact iSup₂_le fun pq hpq ↦ hpq.elim
      (fun hs ↦ (H.piece_le_pieceSum hs).trans le_sup_left)
      (fun ht ↦ (H.piece_le_pieceSum ht).trans le_sup_right)
  · exact sup_le (H.pieceSum_mono Set.subset_union_left)
      (H.pieceSum_mono Set.subset_union_right)

/-- Bidegrees off the weight contribute nothing to a sum of pieces. -/
lemma pieceSum_inter_weight (H : Pure V n) (s : Set (ℕ × ℕ)) :
    H.pieceSum (s ∩ {pq | pq.1 + pq.2 = n}) = H.pieceSum s := by
  refine le_antisymm (H.pieceSum_mono Set.inter_subset_left) (iSup₂_le fun pq hpq ↦ ?_)
  by_cases h : pq.1 + pq.2 = n
  · exact H.piece_le_pieceSum ⟨hpq, h⟩
  · rw [H.piece_eq_bot_of_add_ne pq.1 pq.2 h]
    exact bot_le

lemma disjoint_pieceSum (H : Pure V n) {s t : Set (ℕ × ℕ)}
    (hst : Disjoint s t) : Disjoint (H.pieceSum s) (H.pieceSum t) :=
  H.isInternal.submodule_iSupIndep.disjoint_biSup_biSup hst

/-- Sums of pieces intersect as their index sets do. -/
lemma pieceSum_inf_pieceSum (H : Pure V n) (s t : Set (ℕ × ℕ)) :
    H.pieceSum s ⊓ H.pieceSum t = H.pieceSum (s ∩ t) := by
  have hs : H.pieceSum s = H.pieceSum (s ∩ t) ⊔ H.pieceSum (s \ t) := by
    rw [← H.pieceSum_union, Set.inter_union_sdiff]
  rw [hs, sup_inf_assoc_of_le _ (H.pieceSum_mono Set.inter_subset_right),
    (H.disjoint_pieceSum Set.disjoint_sdiff_left).eq_bot, sup_bot_eq]

/-- Conjugation carries the sum of the pieces indexed by `s` to the sum of the pieces indexed by
the swapped bidegrees. -/
lemma conjugate_mem_pieceSum (H : Pure V n) (s : Set (ℕ × ℕ)) {x : ℂ ⊗[ℚ] V}
    (hx : x ∈ H.pieceSum s) : conjugate V x ∈ H.pieceSum (Prod.swap ⁻¹' s) := by
  induction hx using Submodule.iSup_induction' with
  | mem pq x hx =>
    induction hx using Submodule.iSup_induction' with
    | mem hpq x hx =>
      exact H.piece_le_pieceSum (s := Prod.swap ⁻¹' s) (pq := (pq.2, pq.1))
        (by simpa using hpq) ((H.conjugate_mem_iff pq.2 pq.1 x).2 hx)
    | zero => simp
    | add x y _ _ hx hy => simpa using (H.pieceSum _).add_mem hx hy
  | zero => simp
  | add x y _ _ hx hy => simpa using (H.pieceSum _).add_mem hx hy

lemma conjugate_mem_pieceSum_iff (H : Pure V n) (s : Set (ℕ × ℕ)) (x : ℂ ⊗[ℚ] V) :
    conjugate V x ∈ H.pieceSum s ↔ x ∈ H.pieceSum (Prod.swap ⁻¹' s) := by
  refine ⟨fun hx ↦ by simpa using H.conjugate_mem_pieceSum s hx, fun hx ↦ ?_⟩
  simpa [Set.preimage_preimage] using H.conjugate_mem_pieceSum _ hx

/-! ### The Hodge filtration and its conjugate -/

/-- The Hodge filtration `F^p V_ℂ`, the sum of the pieces whose first index is at least `p`. -/
def filtration (H : Pure V n) (p : ℕ) : Submodule ℂ (ℂ ⊗[ℚ] V) :=
  ⨆ a : ℕ, ⨆ (_ : p ≤ a), ⨆ b : ℕ, H.piece a b

/-- The conjugate filtration `conj F^p`, the sum of the pieces whose second index is at least
`p`. -/
def conjugateFiltration (H : Pure V n) (p : ℕ) : Submodule ℂ (ℂ ⊗[ℚ] V) :=
  H.pieceSum {pq | p ≤ pq.2}

/-- A piece with first index at least `p` lies in `F^p`. -/
lemma piece_le_filtration (H : Pure V n) {p a b : ℕ} (ha : p ≤ a) :
    H.piece a b ≤ H.filtration p :=
  le_iSup_of_le a <| le_iSup_of_le ha <| le_iSup (fun b' ↦ H.piece a b') b

lemma filtration_eq_pieceSum (H : Pure V n) (p : ℕ) :
    H.filtration p = H.pieceSum {pq | p ≤ pq.1} := by
  apply le_antisymm
  · exact iSup_le fun a ↦ iSup_le fun ha ↦ iSup_le fun b ↦
      H.piece_le_pieceSum (s := {pq | p ≤ pq.1}) (pq := (a, b)) ha
  · exact iSup₂_le fun pq hpq ↦
      le_iSup_of_le pq.1 <| le_iSup_of_le hpq <| le_iSup (fun b ↦ H.piece pq.1 b) pq.2

lemma filtration_antitone (H : Pure V n) : Antitone H.filtration := fun _ _ hpq ↦ by
  rw [H.filtration_eq_pieceSum, H.filtration_eq_pieceSum]
  exact H.pieceSum_mono fun _ h ↦ hpq.trans h

@[simp]
lemma filtration_zero (H : Pure V n) : H.filtration 0 = ⊤ := by
  rw [H.filtration_eq_pieceSum]
  simp

/-- The filtration vanishes above the weight. -/
lemma filtration_eq_bot_of_lt (H : Pure V n) {p : ℕ} (hn : n < p) :
    H.filtration p = ⊥ := by
  rw [H.filtration_eq_pieceSum, ← H.pieceSum_inter_weight, ← H.pieceSum_empty]
  congr 1
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  omega

lemma mem_conjugateFiltration_iff (H : Pure V n) (p : ℕ) (x : ℂ ⊗[ℚ] V) :
    x ∈ H.conjugateFiltration p ↔ conjugate V x ∈ H.filtration p := by
  rw [conjugateFiltration, H.filtration_eq_pieceSum, H.conjugate_mem_pieceSum_iff]
  rfl

lemma conjugate_mem_filtration (H : Pure V n) (p : ℕ) {x : ℂ ⊗[ℚ] V}
    (hx : x ∈ H.filtration p) : conjugate V x ∈ H.conjugateFiltration p := by
  rw [H.mem_conjugateFiltration_iff, conjugate_conjugate]
  exact hx

/-- The conjugate filtration is the preimage of the filtration under conjugation. -/
lemma conjugateFiltration_eq_comap (H : Pure V n) (p : ℕ) :
    H.conjugateFiltration p = (H.filtration p).comap (conjugateSemilinear V) := by
  ext x
  exact H.mem_conjugateFiltration_iff p x

/-- The intersection of `F^p` and `conj F^q` is the `(p,q)` piece when `p + q = n`. In particular
the pieces are determined by the filtration. -/
lemma filtration_inf_conjugateFiltration_of_add_eq (H : Pure V n) {p q : ℕ} (hpq : p + q = n) :
    H.filtration p ⊓ H.conjugateFiltration q = H.piece p q := by
  rw [H.filtration_eq_pieceSum, conjugateFiltration, H.pieceSum_inf_pieceSum,
    ← H.pieceSum_inter_weight, show H.piece p q = H.pieceSum {(p, q)} from
      (H.pieceSum_singleton (p, q)).symm]
  congr 1
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  omega

/-- In weight `2p`, the middle filtration steps intersect in the `(p,p)` piece. -/
lemma filtration_inf_conjugateFiltration (p : ℕ) (H : Pure V (2 * p)) :
    H.filtration p ⊓ H.conjugateFiltration p = H.piece p p :=
  H.filtration_inf_conjugateFiltration_of_add_eq (two_mul p).symm

/-- The filtration and its conjugate are `n`-opposed: `F^p` and `conj F^{n+1-p}` are
complementary. -/
lemma isCompl_filtration_conjugateFiltration (H : Pure V n) (p : ℕ) :
    IsCompl (H.filtration p) (H.conjugateFiltration (n + 1 - p)) := by
  rw [H.filtration_eq_pieceSum, conjugateFiltration]
  constructor
  · rw [disjoint_iff, H.pieceSum_inf_pieceSum, ← H.pieceSum_inter_weight, ← H.pieceSum_empty]
    congr 1
    ext ⟨a, b⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    omega
  · rw [codisjoint_iff, ← H.pieceSum_union, ← H.pieceSum_inter_weight, ← H.pieceSum_univ,
      ← H.pieceSum_inter_weight Set.univ]
    congr 1
    ext ⟨a, b⟩
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, true_and]
    omega

/-! ### Rational Hodge classes -/

/-- The defining membership criterion for a rational Hodge class. -/
lemma mem_hodgeClasses_iff (p : ℕ) (H : Pure V (2 * p)) (x : V) :
    x ∈ hodgeClasses p H ↔ ofBase ℚ V x ∈ H.piece p p :=
  Iff.rfl

/-- Every rational Hodge class lies in the corresponding Hodge filtration after
complexification. -/
lemma ofBase_mem_filtration {p : ℕ} (H : Pure V (2 * p))
    {x : V} (hx : x ∈ hodgeClasses p H) :
    ofBase ℚ V x ∈ H.filtration p :=
  H.piece_le_filtration le_rfl hx

/-- For a rational vector in weight `2p`, membership in `F^p` is equivalent to membership in the
middle Hodge piece: conjugation fixes rational vectors, so `F^p` alone forces `F^p ⊓ conj F^p`.
Thus the filtration definition of rational Hodge classes agrees with the usual `(p,p)`
definition. -/
lemma ofBase_mem_filtration_iff (p : ℕ) (H : Pure V (2 * p)) (x : V) :
    ofBase ℚ V x ∈ H.filtration p ↔ ofBase ℚ V x ∈ H.piece p p := by
  rw [← H.filtration_inf_conjugateFiltration p, Submodule.mem_inf,
    H.mem_conjugateFiltration_iff, conjugate_ofBase, and_self]

/-- In weight `2p`, taking the inverse image of `F^p` along the rational lattice gives exactly
the usual rational `(p,p)` classes. -/
lemma filtration_comap_ofBase_eq_hodgeClasses (p : ℕ) (H : Pure V (2 * p)) :
    Submodule.comap (ofBase ℚ V) ((H.filtration p).restrictScalars ℚ) =
      hodgeClasses p H := by
  ext x
  exact H.ofBase_mem_filtration_iff p x

/-! ### Hodge structures from filtrations

The Hodge filtration determines a pure Hodge structure. A decreasing filtration whose
candidate pieces form a direct sum agrees with the resulting Hodge filtration up to the weight.
-/

/-- The candidate `(p,q)` piece of weight `n` cut out by a filtration `F`: `F^p ⊓ conj F^q` when
`p + q = n`, and zero otherwise. -/
def pieceOfFiltration (F : ℕ → Submodule ℂ (ℂ ⊗[ℚ] V)) (n p q : ℕ) :
    Submodule ℂ (ℂ ⊗[ℚ] V) :=
  if p + q = n then F p ⊓ (F q).comap (conjugateSemilinear V) else ⊥

variable {F : ℕ → Submodule ℂ (ℂ ⊗[ℚ] V)}

lemma pieceOfFiltration_of_add_eq {p q : ℕ} (hpq : p + q = n) :
    pieceOfFiltration F n p q = F p ⊓ (F q).comap (conjugateSemilinear V) :=
  if_pos hpq

lemma pieceOfFiltration_of_add_ne {p q : ℕ} (hpq : p + q ≠ n) :
    pieceOfFiltration F n p q = ⊥ :=
  if_neg hpq

lemma mem_pieceOfFiltration_iff {p q : ℕ} (hpq : p + q = n) {x : ℂ ⊗[ℚ] V} :
    x ∈ pieceOfFiltration F n p q ↔ x ∈ F p ∧ conjugate V x ∈ F q := by
  rw [pieceOfFiltration_of_add_eq hpq, Submodule.mem_inf, Submodule.mem_comap,
    conjugateSemilinear_apply]

/-- The pure Hodge structure from candidate pieces `F^p ⊓ conj F^q` that form a direct sum. -/
def ofFiltration (F : ℕ → Submodule ℂ (ℂ ⊗[ℚ] V)) (n : ℕ)
    (h : DirectSum.IsInternal fun pq : ℕ × ℕ ↦ pieceOfFiltration F n pq.1 pq.2) :
    Pure V n where
  piece := pieceOfFiltration F n
  piece_eq_bot_of_add_ne _ _ hpq := if_neg hpq
  isInternal := h
  conjugate_mem_iff p q x := by
    by_cases hpq : p + q = n
    · rw [mem_pieceOfFiltration_iff hpq, mem_pieceOfFiltration_iff (by omega), conjugate_conjugate,
        and_comm]
    · rw [pieceOfFiltration_of_add_ne hpq, pieceOfFiltration_of_add_ne (by omega)]
      simp

variable (h : DirectSum.IsInternal fun pq : ℕ × ℕ ↦ pieceOfFiltration F n pq.1 pq.2)

@[simp]
lemma piece_ofFiltration : (ofFiltration F n h).piece = pieceOfFiltration F n := rfl

lemma filtration_ofFiltration_le (hF : Antitone F) (p : ℕ) :
    (ofFiltration F n h).filtration p ≤ F p := by
  refine iSup_le fun a ↦ iSup_le fun ha ↦ iSup_le fun b ↦ ?_
  by_cases hab : a + b = n
  · rw [piece_ofFiltration, pieceOfFiltration_of_add_eq hab]
    exact inf_le_left.trans (hF ha)
  · rw [piece_ofFiltration, pieceOfFiltration_of_add_ne hab]
    exact bot_le

/-- Up to the weight, the Hodge filtration of `ofFiltration F n h` is `F`. Above the weight the
Hodge filtration vanishes while `F` need not: take `F` constant equal to `⊤` in weight `0`. -/
lemma filtration_ofFiltration (hF : Antitone F) {p : ℕ} (hp : p ≤ n) :
    (ofFiltration F n h).filtration p = F p := by
  set H := ofFiltration F n h
  refine le_antisymm (filtration_ofFiltration_le h hF p) fun x hx ↦ ?_
  have hsup : x ∈ H.filtration p ⊔ H.conjugateFiltration (n + 1 - p) := by
    rw [(H.isCompl_filtration_conjugateFiltration p).sup_eq_top]
    trivial
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hsup
  have hw₁ : w ∈ F p := by
    rw [← add_sub_cancel_left u w]
    exact (F p).sub_mem hx (filtration_ofFiltration_le h hF p hu)
  have hw₂ : conjugate V w ∈ F (n - p) :=
    hF (by omega : n - p ≤ n + 1 - p)
      (filtration_ofFiltration_le h hF _ ((H.mem_conjugateFiltration_iff _ w).1 hw))
  have hw₃ : w ∈ H.filtration p := by
    refine H.piece_le_filtration (a := p) (b := n - p) le_rfl ?_
    rw [piece_ofFiltration, pieceOfFiltration_of_add_eq (by omega)]
    exact ⟨hw₁, hw₂⟩
  have hw0 : w = 0 :=
    Submodule.disjoint_def.1 (H.isCompl_filtration_conjugateFiltration p).disjoint w hw₃ hw
  rw [hw0, add_zero]
  exact hu

/-- A pure Hodge structure whose filtration agrees with `F` up to the weight has the candidate
pieces of `F` as its pieces. -/
lemma piece_eq_pieceOfFiltration (H : Pure V n)
    (hH : ∀ p ≤ n, H.filtration p = F p) (p q : ℕ) :
    H.piece p q = pieceOfFiltration F n p q := by
  by_cases hpq : p + q = n
  · rw [pieceOfFiltration_of_add_eq hpq, ← H.filtration_inf_conjugateFiltration_of_add_eq hpq,
      H.conjugateFiltration_eq_comap, hH p (by omega), hH q (by omega)]
  · rw [pieceOfFiltration_of_add_ne hpq, H.piece_eq_bot_of_add_ne p q hpq]

/-- If `F` is the Hodge filtration of some pure Hodge structure of weight `n`, then its candidate
pieces form a direct sum. -/
lemma isInternal_pieceOfFiltration (H : Pure V n)
    (hH : ∀ p ≤ n, H.filtration p = F p) :
    DirectSum.IsInternal fun pq : ℕ × ℕ ↦ pieceOfFiltration F n pq.1 pq.2 := by
  have := H.isInternal
  simp_rw [H.piece_eq_pieceOfFiltration hH] at this
  exact this

/-- A pure Hodge structure is `ofFiltration` of its own Hodge filtration. -/
lemma eq_ofFiltration (H : Pure V n) (hH : ∀ p ≤ n, H.filtration p = F p) :
    H = ofFiltration F n (H.isInternal_pieceOfFiltration hH) :=
  Pure.ext (funext₂ (H.piece_eq_pieceOfFiltration hH))

/-- A pure Hodge structure is determined by its Hodge filtration. -/
lemma filtration_injective :
    Function.Injective (filtration : Pure V n → ℕ → Submodule ℂ (ℂ ⊗[ℚ] V)) :=
  fun H₁ H₂ hH ↦ (H₁.eq_ofFiltration (F := H₂.filtration) fun p _ ↦ congrFun hH p).trans
    (H₂.eq_ofFiltration fun _ _ ↦ rfl).symm

/-! ### Weight zero -/

variable (V) in
/-- The pure Hodge structure of weight `0` on `V`: everything has type `(0,0)`. -/
def weightZero : Pure V 0 where
  piece p q := if p + q = 0 then ⊤ else ⊥
  piece_eq_bot_of_add_ne _ _ hpq := if_neg hpq
  isInternal := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨fun pq ↦ ?_, eq_top_iff.2 (le_iSup_of_le (0, 0) (by simp))⟩
    dsimp only
    by_cases hpq : pq.1 + pq.2 = 0
    · have hbot : (⨆ ab, ⨆ (_ : ab ≠ pq),
          if ab.1 + ab.2 = 0 then (⊤ : Submodule ℂ (ℂ ⊗[ℚ] V)) else ⊥) = ⊥ :=
        iSup_eq_bot.2 fun ab ↦ iSup_eq_bot.2 fun hab ↦ if_neg fun h ↦ hab (by ext <;> omega)
      rw [hbot]
      exact disjoint_bot_right
    · rw [if_neg hpq]
      exact disjoint_bot_left
  conjugate_mem_iff p q x := by
    by_cases hpq : p + q = 0
    · rw [if_pos hpq, if_pos (by omega)]
      simp
    · rw [if_neg hpq, if_neg (by omega)]
      simp

@[simp]
lemma piece_weightZero (p q : ℕ) : (weightZero V).piece p q = if p + q = 0 then ⊤ else ⊥ := rfl

instance : Subsingleton (Pure V 0) :=
  ⟨fun H₁ H₂ ↦ filtration_injective (funext fun p ↦ by
    obtain rfl | hp := Nat.eq_zero_or_pos p
    · rw [filtration_zero, filtration_zero]
    · rw [filtration_eq_bot_of_lt H₁ hp, filtration_eq_bot_of_lt H₂ hp])⟩

end Pure

end HodgeStructure
