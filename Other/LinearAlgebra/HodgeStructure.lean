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

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Pure rational Hodge structures

A pure rational Hodge structure of weight `n` on a rational vector space `V` is a bigrading of the
complexification `ℂ ⊗[ℚ] V` by pieces `V^{p,q}`, zero unless `p + q = n`, which complex
conjugation exchanges. Conjugation acts on the first tensor factor, so it is conjugate-linear and
fixes every rational vector. This file defines the structure, its Hodge filtration
`F^p = ⨁_{a ≥ p} V^{a,b}`, its rational Hodge classes, and the classical facts relating them:

* `F^p ⊓ conj F^q = V^{p,q}` when `p + q = n`, so the pieces are recovered from the filtration, and a
  Hodge structure is determined by its filtration (`HodgeStructure.filtration_injective`);
* `F^p` and `conj F^{n+1-p}` are complementary (`HodgeStructure.isCompl_filtration_conjugateFiltration`);
* a rational vector lies in `V^{p,p}` as soon as it lies in `F^p`
  (`HodgeStructure.ofBase_mem_filtration_iff`);
* conversely, if the candidate pieces `F^p ⊓ conj F^q` of a decreasing filtration `F` form a
  direct sum, then `HodgeStructure.ofFiltration` is the Hodge structure with Hodge filtration `F`.

The statement of the Hodge conjecture does not use this file. Equipping the cohomology of a
smooth projective variety with a pure Hodge structure is the Hodge decomposition theorem, which
this repository does not prove. `Other.AlgebraicGeometry.HodgeDecomposition` takes that theorem
as a hypothesis and shows that the Hodge classes of the statement are then the rational
`(p,p)`-classes of the resulting Hodge structure.
-/

@[expose] public noncomputable section

open scoped DirectSum TensorProduct

universe u

namespace HodgeStructure

/-- The canonical map from a `K`-vector space to its complexification. -/
def ofBase (K : Type) [Field K] [Algebra K ℂ] (V : Type u) [AddCommGroup V] [Module K V] :
    V →ₗ[K] ℂ ⊗[K] V :=
  TensorProduct.mk K ℂ V 1

@[simp]
lemma ofBase_apply (K : Type) [Field K] [Algebra K ℂ] (V : Type u) [AddCommGroup V] [Module K V]
    (v : V) : ofBase K V v = 1 ⊗ₜ[K] v := rfl

variable (V : Type u) [AddCommGroup V] [Module ℚ V]

/-- Complex conjugation on a complexified rational vector space, as a conjugate-linear map. It
conjugates the scalar factor and fixes every rational vector. -/
def conjugate : ℂ ⊗[ℚ] V →ₗ⋆[ℂ] ℂ ⊗[ℚ] V where
  toFun := TensorProduct.map (Complex.conjAe.restrictScalars ℚ).toLinearMap LinearMap.id
  map_add' := map_add _
  map_smul' c x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z v => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp [hx, hy]

@[simp]
lemma conjugate_tmul (z : ℂ) (v : V) :
    conjugate V (z ⊗ₜ[ℚ] v) = Complex.conjAe z ⊗ₜ[ℚ] v := rfl

@[simp]
lemma conjugate_ofBase (v : V) : conjugate V (ofBase ℚ V v) = ofBase ℚ V v := by
  simp

@[simp]
lemma conjugate_conjugate (x : ℂ ⊗[ℚ] V) : conjugate V (conjugate V x) = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro z v
    simp
  · intro x y hx hy
    simp [hx, hy]

@[simp]
lemma conjugate_eq_zero_iff (x : ℂ ⊗[ℚ] V) : conjugate V x = 0 ↔ x = 0 :=
  ⟨fun h ↦ by simpa using congrArg (conjugate V) h, fun h ↦ by simp [h]⟩

end HodgeStructure

/-- A pure rational Hodge structure of weight `n` on `V`.

The pieces are indexed by pairs `(p,q)`. They form an internal direct sum, only pieces with
`p + q = n` can be nonzero, and complex conjugation exchanges the `(p,q)` and `(q,p)` pieces. -/
@[ext]
structure HodgeStructure (V : Type u) [AddCommGroup V] [Module ℚ V] (n : ℕ) where
  /-- The Hodge piece `V^{p,q}` inside `V_ℂ`. -/
  piece : ℕ → ℕ → Submodule ℂ (ℂ ⊗[ℚ] V)
  /-- Hodge pieces off the prescribed weight are zero. -/
  piece_eq_bot_of_add_ne : ∀ p q, p + q ≠ n → piece p q = ⊥
  /-- Every complexified vector has a unique finite decomposition into Hodge pieces. -/
  isInternal : DirectSum.IsInternal (fun pq : ℕ × ℕ ↦ piece pq.1 pq.2)
  /-- Complex conjugation exchanges bidegrees. -/
  conjugate_mem_iff : ∀ p q x, HodgeStructure.conjugate V x ∈ piece p q ↔ x ∈ piece q p

namespace HodgeStructure

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {n : ℕ}

/-- The Hodge pieces span the whole complexification. -/
lemma iSup_piece_eq_top (H : HodgeStructure V n) :
    ⨆ pq : ℕ × ℕ, H.piece pq.1 pq.2 = ⊤ :=
  H.isInternal.submodule_iSup_eq_top

/-- Membership in a conjugate Hodge piece, with conjugation moved to the other side. -/
lemma mem_piece_conjugate_iff (H : HodgeStructure V n) (p q : ℕ) (x : ℂ ⊗[ℚ] V) :
    x ∈ H.piece p q ↔ conjugate V x ∈ H.piece q p :=
  (H.conjugate_mem_iff q p x).symm

/-- The direct-sum coordinates of a pure Hodge structure. -/
def decomposition (H : HodgeStructure V n) :
    ℂ ⊗[ℚ] V ≃ₗ[ℂ] (⨁ pq : ℕ × ℕ, H.piece pq.1 pq.2) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun pq : ℕ × ℕ ↦ H.piece pq.1 pq.2)
    H.isInternal).symm

/-- A vector in one Hodge piece has only that direct-sum coordinate. -/
lemma decomposition_apply_of_mem (H : HodgeStructure V n) {pq : ℕ × ℕ}
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
def pieceSum (H : HodgeStructure V n) (s : Set (ℕ × ℕ)) : Submodule ℂ (ℂ ⊗[ℚ] V) :=
  ⨆ pq, ⨆ (_ : pq ∈ s), H.piece pq.1 pq.2

lemma pieceSum_mono (H : HodgeStructure V n) {s t : Set (ℕ × ℕ)} (hst : s ⊆ t) :
    H.pieceSum s ≤ H.pieceSum t :=
  iSup₂_le fun pq hpq ↦ le_iSup₂_of_le pq (hst hpq) le_rfl

lemma piece_le_pieceSum (H : HodgeStructure V n) {s : Set (ℕ × ℕ)} {pq : ℕ × ℕ}
    (hpq : pq ∈ s) : H.piece pq.1 pq.2 ≤ H.pieceSum s :=
  le_iSup₂_of_le pq hpq le_rfl

@[simp]
lemma pieceSum_empty (H : HodgeStructure V n) : H.pieceSum ∅ = ⊥ := by
  simp [pieceSum]

@[simp]
lemma pieceSum_univ (H : HodgeStructure V n) : H.pieceSum Set.univ = ⊤ := by
  simp [pieceSum, H.iSup_piece_eq_top]

lemma pieceSum_singleton (H : HodgeStructure V n) (pq : ℕ × ℕ) :
    H.pieceSum {pq} = H.piece pq.1 pq.2 := by
  simp [pieceSum]

lemma pieceSum_union (H : HodgeStructure V n) (s t : Set (ℕ × ℕ)) :
    H.pieceSum (s ∪ t) = H.pieceSum s ⊔ H.pieceSum t := by
  apply le_antisymm
  · exact iSup₂_le fun pq hpq ↦ hpq.elim
      (fun hs ↦ (H.piece_le_pieceSum hs).trans le_sup_left)
      (fun ht ↦ (H.piece_le_pieceSum ht).trans le_sup_right)
  · exact sup_le (H.pieceSum_mono Set.subset_union_left)
      (H.pieceSum_mono Set.subset_union_right)

/-- Bidegrees off the weight contribute nothing to a sum of pieces. -/
lemma pieceSum_inter_weight (H : HodgeStructure V n) (s : Set (ℕ × ℕ)) :
    H.pieceSum (s ∩ {pq | pq.1 + pq.2 = n}) = H.pieceSum s := by
  refine le_antisymm (H.pieceSum_mono Set.inter_subset_left) (iSup₂_le fun pq hpq ↦ ?_)
  by_cases h : pq.1 + pq.2 = n
  · exact H.piece_le_pieceSum ⟨hpq, h⟩
  · rw [H.piece_eq_bot_of_add_ne pq.1 pq.2 h]
    exact bot_le

lemma disjoint_pieceSum (H : HodgeStructure V n) {s t : Set (ℕ × ℕ)}
    (hst : Disjoint s t) : Disjoint (H.pieceSum s) (H.pieceSum t) :=
  H.isInternal.submodule_iSupIndep.disjoint_biSup_biSup hst

/-- Sums of pieces intersect as their index sets do. -/
lemma pieceSum_inf_pieceSum (H : HodgeStructure V n) (s t : Set (ℕ × ℕ)) :
    H.pieceSum s ⊓ H.pieceSum t = H.pieceSum (s ∩ t) := by
  have hs : H.pieceSum s = H.pieceSum (s ∩ t) ⊔ H.pieceSum (s \ t) := by
    rw [← H.pieceSum_union, Set.inter_union_sdiff]
  rw [hs, sup_inf_assoc_of_le _ (H.pieceSum_mono Set.inter_subset_right),
    (H.disjoint_pieceSum Set.disjoint_sdiff_left).eq_bot, sup_bot_eq]

/-- Conjugation carries the sum of the pieces indexed by `s` to the sum of the pieces indexed by
the swapped bidegrees. -/
lemma conjugate_mem_pieceSum (H : HodgeStructure V n) (s : Set (ℕ × ℕ)) {x : ℂ ⊗[ℚ] V}
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

lemma conjugate_mem_pieceSum_iff (H : HodgeStructure V n) (s : Set (ℕ × ℕ)) (x : ℂ ⊗[ℚ] V) :
    conjugate V x ∈ H.pieceSum s ↔ x ∈ H.pieceSum (Prod.swap ⁻¹' s) := by
  refine ⟨fun hx ↦ by simpa using H.conjugate_mem_pieceSum s hx, fun hx ↦ ?_⟩
  simpa [Set.preimage_preimage] using H.conjugate_mem_pieceSum _ hx

/-! ### The Hodge filtration and its conjugate -/

/-- The Hodge filtration `F^p V_ℂ`, the sum of the pieces whose first index is at least `p`. -/
def filtration (H : HodgeStructure V n) (p : ℕ) : Submodule ℂ (ℂ ⊗[ℚ] V) :=
  ⨆ a : ℕ, ⨆ (_ : p ≤ a), ⨆ b : ℕ, H.piece a b

/-- The conjugate filtration `conj F^p`, the sum of the pieces whose second index is at least
`p`. -/
def conjugateFiltration (H : HodgeStructure V n) (p : ℕ) : Submodule ℂ (ℂ ⊗[ℚ] V) :=
  H.pieceSum {pq | p ≤ pq.2}

/-- A piece with first index at least `p` lies in `F^p`. -/
lemma piece_le_filtration (H : HodgeStructure V n) {p a b : ℕ} (ha : p ≤ a) :
    H.piece a b ≤ H.filtration p :=
  le_iSup_of_le a <| le_iSup_of_le ha <| le_iSup (fun b' ↦ H.piece a b') b

lemma filtration_eq_pieceSum (H : HodgeStructure V n) (p : ℕ) :
    H.filtration p = H.pieceSum {pq | p ≤ pq.1} := by
  apply le_antisymm
  · exact iSup_le fun a ↦ iSup_le fun ha ↦ iSup_le fun b ↦
      H.piece_le_pieceSum (s := {pq | p ≤ pq.1}) (pq := (a, b)) ha
  · exact iSup₂_le fun pq hpq ↦
      le_iSup_of_le pq.1 <| le_iSup_of_le hpq <| le_iSup (fun b ↦ H.piece pq.1 b) pq.2

lemma filtration_antitone (H : HodgeStructure V n) : Antitone H.filtration := fun _ _ hpq ↦ by
  rw [H.filtration_eq_pieceSum, H.filtration_eq_pieceSum]
  exact H.pieceSum_mono fun _ h ↦ hpq.trans h

@[simp]
lemma filtration_zero (H : HodgeStructure V n) : H.filtration 0 = ⊤ := by
  rw [H.filtration_eq_pieceSum]
  simp

/-- The filtration vanishes above the weight. -/
lemma filtration_eq_bot_of_lt (H : HodgeStructure V n) {p : ℕ} (hn : n < p) :
    H.filtration p = ⊥ := by
  rw [H.filtration_eq_pieceSum, ← H.pieceSum_inter_weight, ← H.pieceSum_empty]
  congr 1
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  omega

lemma mem_conjugateFiltration_iff (H : HodgeStructure V n) (p : ℕ) (x : ℂ ⊗[ℚ] V) :
    x ∈ H.conjugateFiltration p ↔ conjugate V x ∈ H.filtration p := by
  rw [conjugateFiltration, H.filtration_eq_pieceSum, H.conjugate_mem_pieceSum_iff]
  rfl

lemma conjugate_mem_filtration (H : HodgeStructure V n) (p : ℕ) {x : ℂ ⊗[ℚ] V}
    (hx : x ∈ H.filtration p) : conjugate V x ∈ H.conjugateFiltration p := by
  rw [H.mem_conjugateFiltration_iff, conjugate_conjugate]
  exact hx

/-- The conjugate filtration is the preimage of the filtration under conjugation. -/
lemma conjugateFiltration_eq_comap (H : HodgeStructure V n) (p : ℕ) :
    H.conjugateFiltration p = (H.filtration p).comap (conjugate V) := by
  ext x
  exact H.mem_conjugateFiltration_iff p x

/-- The intersection of `F^p` and `conj F^q` is the `(p,q)` piece when `p + q = n`. In particular
the pieces are determined by the filtration. -/
lemma filtration_inf_conjugateFiltration (H : HodgeStructure V n) {p q : ℕ} (hpq : p + q = n) :
    H.filtration p ⊓ H.conjugateFiltration q = H.piece p q := by
  rw [H.filtration_eq_pieceSum, conjugateFiltration, H.pieceSum_inf_pieceSum,
    ← H.pieceSum_inter_weight, show H.piece p q = H.pieceSum {(p, q)} from
      (H.pieceSum_singleton (p, q)).symm]
  congr 1
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  omega

/-- The filtration and its conjugate are `n`-opposed: `F^p` and `conj F^{n+1-p}` are
complementary. -/
lemma isCompl_filtration_conjugateFiltration (H : HodgeStructure V n) (p : ℕ) :
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

/-- Rational Hodge classes of codimension `p`: rational vectors whose complexifications lie in
the middle Hodge piece `V^{p,p}`. -/
def hodgeClasses (p : ℕ) (H : HodgeStructure V (2 * p)) : Submodule ℚ V :=
  Submodule.comap (ofBase ℚ V) ((H.piece p p).restrictScalars ℚ)

/-- The defining membership criterion for a rational Hodge class. -/
lemma mem_hodgeClasses_iff (p : ℕ) (H : HodgeStructure V (2 * p)) (x : V) :
    x ∈ hodgeClasses p H ↔ ofBase ℚ V x ∈ H.piece p p :=
  Iff.rfl

/-- Every rational Hodge class lies in the corresponding Hodge filtration after
complexification. -/
lemma ofBase_mem_filtration {p : ℕ} (H : HodgeStructure V (2 * p))
    {x : V} (hx : x ∈ hodgeClasses p H) :
    ofBase ℚ V x ∈ H.filtration p :=
  H.piece_le_filtration le_rfl hx

/-- For a rational vector in weight `2p`, membership in `F^p` is equivalent to membership in the
middle Hodge piece: conjugation fixes rational vectors, so `F^p` alone forces `F^p ⊓ conj F^p`.
Thus the filtration definition of rational Hodge classes agrees with the usual `(p,p)`
definition. -/
lemma ofBase_mem_filtration_iff (p : ℕ) (H : HodgeStructure V (2 * p)) (x : V) :
    ofBase ℚ V x ∈ H.filtration p ↔ ofBase ℚ V x ∈ H.piece p p := by
  rw [← H.filtration_inf_conjugateFiltration (two_mul p).symm, Submodule.mem_inf,
    H.mem_conjugateFiltration_iff, conjugate_ofBase, and_self]

/-- In weight `2p`, taking the inverse image of `F^p` along the rational lattice gives exactly
the usual rational `(p,p)` classes. -/
lemma filtration_comap_ofBase_eq_hodgeClasses (p : ℕ) (H : HodgeStructure V (2 * p)) :
    Submodule.comap (ofBase ℚ V) ((H.filtration p).restrictScalars ℚ) =
      hodgeClasses p H := by
  ext x
  exact H.ofBase_mem_filtration_iff p x

/-! ### Hodge structures from filtrations

A pure Hodge structure is determined by its Hodge filtration, since `V^{p,q} = F^p ⊓ conj F^q`.
Conversely, a decreasing filtration `F` of `ℂ ⊗[ℚ] V` is the Hodge filtration of a pure Hodge
structure of weight `n` exactly when the candidate pieces `F^p ⊓ conj F^q`, `p + q = n`, form a
direct sum. The weight and conjugation axioms hold for these candidates automatically. -/

/-- The candidate `(p,q)` piece of weight `n` cut out by a filtration `F`: `F^p ⊓ conj F^q` when
`p + q = n`, and zero otherwise. -/
def pieceOfFiltration (F : ℕ → Submodule ℂ (ℂ ⊗[ℚ] V)) (n p q : ℕ) :
    Submodule ℂ (ℂ ⊗[ℚ] V) :=
  if p + q = n then F p ⊓ (F q).comap (conjugate V) else ⊥

variable {F : ℕ → Submodule ℂ (ℂ ⊗[ℚ] V)}

lemma pieceOfFiltration_of_add_eq {p q : ℕ} (hpq : p + q = n) :
    pieceOfFiltration F n p q = F p ⊓ (F q).comap (conjugate V) :=
  if_pos hpq

lemma pieceOfFiltration_of_add_ne {p q : ℕ} (hpq : p + q ≠ n) :
    pieceOfFiltration F n p q = ⊥ :=
  if_neg hpq

lemma mem_pieceOfFiltration_iff {p q : ℕ} (hpq : p + q = n) {x : ℂ ⊗[ℚ] V} :
    x ∈ pieceOfFiltration F n p q ↔ x ∈ F p ∧ conjugate V x ∈ F q := by
  rw [pieceOfFiltration_of_add_eq hpq, Submodule.mem_inf, Submodule.mem_comap]

/-- The pure Hodge structure of weight `n` whose Hodge filtration is `F`, given that the candidate
pieces `F^p ⊓ conj F^q` form a direct sum. -/
def ofFiltration (F : ℕ → Submodule ℂ (ℂ ⊗[ℚ] V)) (n : ℕ)
    (h : DirectSum.IsInternal fun pq : ℕ × ℕ ↦ pieceOfFiltration F n pq.1 pq.2) :
    HodgeStructure V n where
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
lemma piece_eq_pieceOfFiltration (H : HodgeStructure V n)
    (hH : ∀ p ≤ n, H.filtration p = F p) (p q : ℕ) :
    H.piece p q = pieceOfFiltration F n p q := by
  by_cases hpq : p + q = n
  · rw [pieceOfFiltration_of_add_eq hpq, ← H.filtration_inf_conjugateFiltration hpq,
      H.conjugateFiltration_eq_comap, hH p (by omega), hH q (by omega)]
  · rw [pieceOfFiltration_of_add_ne hpq, H.piece_eq_bot_of_add_ne p q hpq]

/-- If `F` is the Hodge filtration of some pure Hodge structure of weight `n`, then its candidate
pieces form a direct sum. -/
lemma isInternal_pieceOfFiltration (H : HodgeStructure V n)
    (hH : ∀ p ≤ n, H.filtration p = F p) :
    DirectSum.IsInternal fun pq : ℕ × ℕ ↦ pieceOfFiltration F n pq.1 pq.2 := by
  have := H.isInternal
  simp_rw [H.piece_eq_pieceOfFiltration hH] at this
  exact this

/-- A pure Hodge structure is `ofFiltration` of its own Hodge filtration. -/
lemma eq_ofFiltration (H : HodgeStructure V n) (hH : ∀ p ≤ n, H.filtration p = F p) :
    H = ofFiltration F n (H.isInternal_pieceOfFiltration hH) :=
  HodgeStructure.ext (funext₂ (H.piece_eq_pieceOfFiltration hH))

/-- A pure Hodge structure is determined by its Hodge filtration. -/
lemma filtration_injective :
    Function.Injective (filtration : HodgeStructure V n → ℕ → Submodule ℂ (ℂ ⊗[ℚ] V)) :=
  fun H₁ H₂ hH ↦ (H₁.eq_ofFiltration (F := H₂.filtration) fun p _ ↦ congrFun hH p).trans
    (H₂.eq_ofFiltration fun _ _ ↦ rfl).symm

/-! ### Weight zero -/

variable (V) in
/-- The pure Hodge structure of weight `0` on `V`: everything has type `(0,0)`. -/
def weightZero : HodgeStructure V 0 where
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

instance : Subsingleton (HodgeStructure V 0) :=
  ⟨fun H₁ H₂ ↦ filtration_injective (funext fun p ↦ by
    obtain rfl | hp := Nat.eq_zero_or_pos p
    · rw [filtration_zero, filtration_zero]
    · rw [filtration_eq_bot_of_lt H₁ hp, filtration_eq_bot_of_lt H₂ hp])⟩

end HodgeStructure
