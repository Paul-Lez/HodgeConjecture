/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Ordered cochains of the full simplex and monomially graded Čech complexes

Let `ι` be a type and `M` an additive group. An ordered `p`-cochain is a function
`x : (Fin (p + 1) → ι) → M`, and the differential is `(d x) i = ∑ₖ (-1) ^ k • x (i ∘ δₖ)`. This is
the Čech complex of a constant coefficient system for a cover indexed by `ι`, and it is the
"shape" of every Čech complex for the standard cover of projective space after decomposing
according to monomials.

The Čech complex of `O(d)` on `ℙⁿ` (algebraic or analytic) has components that are (spaces of)
Laurent series `∑ₐ cₐ xᵃ`, where on `⋂_{j ∈ I} Uⱼ` only monomials with *negative support*
`N(a) = {j | aⱼ < 0} ⊆ I` occur. We axiomatise this by an additive group `M` with a family of
orthogonal idempotents `π N : M →+ M` summing to the identity, indexed by `N : Finset ι`
(`SimplexCochain.Grading`); a cochain is *admissible* if `π N (x i) = 0` unless `N ⊆ im i`. The
admissible cochains form a subcomplex, and we compute its cohomology by an explicit homotopy
`SimplexCochain.Grading.homotopy`, acting on the `N`-component by

- `x ↦ (i ↦ x (j, i₀, …, iₚ))` for some `j ∉ N` (the cone on `j`), if `N ≠ univ`;
- an explicit recursive homotopy `SimplexCochain.G` of the complex of cochains supported on
  surjective tuples, valid in degrees `≥ card ι`, if `N = univ`.

The homotopy acts on each `N`-component by a fixed integer matrix (`homotopyN_eq_sum`), so it
can be applied coefficientwise to convergent Laurent series as well as to Laurent polynomials.

## Main definitions

- `SimplexCochain.Cochain ι M p`, `SimplexCochain.d`, `SimplexCochain.aug`.
- `SimplexCochain.h j`: the cone homotopy on `j`.
- `SimplexCochain.G l`: the homotopy of the cochains supported on tuples with image `l.toFinset`.
- `SimplexCochain.Grading`, `SimplexCochain.Grading.IsAdmissible`,
  `SimplexCochain.Grading.homotopy`.

## Main results

- `SimplexCochain.d_d`, `SimplexCochain.d_h_add_h_d`, `SimplexCochain.aug_add_h_d`.
- `SimplexCochain.D_G_add_G_D`, `SimplexCochain.suppEq_G`: `G l` is a homotopy on cochains
  supported on tuples with image `T = l.toFinset`, preserving that support in degrees `≥ card T`.
- `SimplexCochain.Grading.d_homotopy_add`: `d ∘ H + H ∘ d = id` on admissible cochains of positive
  degree.
- `SimplexCochain.Grading.exists_eq_d`: an admissible cocycle `x` of degree `q ≥ 1` is the
  coboundary of an admissible cochain (with values in any `π`-stable subgroup containing the
  values of `x`), provided `π univ ∘ x = 0` or `card ι ≤ q`; the first condition is automatic if
  `q + 1 < card ι` (`Grading.proj_univ_eq_zero`).
- `SimplexCochain.Grading.exists_eq_aug`: an admissible `0`-cocycle `x` with `π univ ∘ x = 0` is
  constant with value in the image of `π ∅`.
-/

@[expose] public section

open CategoryTheory Simplicial

namespace SimplexCochain

universe u v w

set_option backward.isDefEq.respectTransparency.types false

variable (ι : Type u) (M : Type v) [AddCommGroup M]

/-- Ordered `p`-cochains of the full simplex on `ι` with values in `M`. -/
abbrev Cochain (p : ℕ) : Type _ := (Fin (p + 1) → ι) → M

variable {ι M}

/-- The restriction of cochains along `θ : Fin (m + 1) → Fin (n + 1)`: `x ↦ (i ↦ x (i ∘ θ))`. -/
def restrict {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) : Cochain ι M m →+ Cochain ι M n :=
  AddMonoidHom.mk' (fun x i ↦ x fun a ↦ i (θ a)) fun _ _ ↦ rfl

@[simp]
lemma restrict_apply {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) (x : Cochain ι M m)
    (i : Fin (n + 1) → ι) : restrict θ x i = x fun a ↦ i (θ a) :=
  rfl

/-- The differential `(d x) i = ∑ₖ (-1) ^ k • x (i ∘ δₖ)`, `δₖ = Fin.succAbove k`. -/
def d (p : ℕ) : Cochain ι M p →+ Cochain ι M (p + 1) :=
  ∑ k : Fin (p + 2), ((-1 : ℤ) ^ (k : ℕ)) • restrict k.succAbove

lemma d_apply (p : ℕ) (x : Cochain ι M p) (i : Fin (p + 2) → ι) :
    d p x i = ∑ k : Fin (p + 2), ((-1 : ℤ) ^ (k : ℕ)) • x fun a ↦ i (k.succAbove a) := by
  rw [d, AddMonoidHom.finsetSum_apply, Finset.sum_apply]
  rfl

/-- The cochains as a cosimplicial abelian group (`ℤ`-module). -/
@[simps]
def cosimplicial : CosimplicialObject (ModuleCat.{max u v} ℤ) where
  obj Δ := ModuleCat.of ℤ (Cochain ι M Δ.len)
  map θ := ModuleCat.ofHom (restrict (M := M) θ.toOrderHom).toIntLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

variable (ι M) in
lemma d_eq_objD (p : ℕ) (x : Cochain ι M p) :
    d p x = (AlgebraicTopology.AlternatingCofaceMapComplex.objD
      (cosimplicial (ι := ι) (M := M)) p).hom x := by
  ext i
  simp only [d_apply, AlgebraicTopology.AlternatingCofaceMapComplex.objD, CosimplicialObject.δ,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.coe_sum, Finset.sum_apply]
  erw [Finset.sum_apply]
  rfl

@[simp]
lemma d_d (p : ℕ) (x : Cochain ι M p) : d (p + 1) (d p x) = 0 := by
  have h := congrArg
    (fun φ : (cosimplicial (ι := ι) (M := M)).obj ⦋p⦌ ⟶
      (cosimplicial (ι := ι) (M := M)).obj ⦋p + 2⦌ ↦ φ.hom x)
    (AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (cosimplicial (ι := ι) (M := M)) p)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at h
  rw [d_eq_objD, d_eq_objD]
  exact h

/-! ### The cone homotopy and the augmentation -/

/-- The cone homotopy on `j`: `(h j x) i = x (j, i₀, …, iₚ)`. -/
def h (j : ι) (p : ℕ) : Cochain ι M (p + 1) →+ Cochain ι M p :=
  AddMonoidHom.mk' (fun x i ↦ x (Fin.cons j i)) fun _ _ ↦ rfl

@[simp]
lemma h_apply (j : ι) (p : ℕ) (x : Cochain ι M (p + 1)) (i : Fin (p + 1) → ι) :
    h j p x i = x (Fin.cons j i) :=
  rfl

/-- The augmentation `M → Cochain ι M 0`, `v ↦ (i ↦ v)`. -/
def aug : M →+ Cochain ι M 0 :=
  AddMonoidHom.mk' (fun v _ ↦ v) fun _ _ ↦ rfl

@[simp]
lemma aug_apply (v : M) (i : Fin 1 → ι) : aug v i = v :=
  rfl

@[simp]
lemma d_aug (v : M) : d 0 (aug (ι := ι) v) = 0 := by
  ext i
  simp [d_apply, Fin.sum_univ_succ]

/-- The cone homotopy is a contracting homotopy in positive degrees. -/
lemma d_h_add_h_d (j : ι) (p : ℕ) (x : Cochain ι M (p + 1)) :
    d p (h j p x) + h j (p + 1) (d (p + 1) x) = x := by
  ext i
  simp only [Pi.add_apply, d_apply, h_apply]
  rw [Fin.sum_univ_succ (n := p + 2)]
  have e0 : (fun a ↦ (Fin.cons j i : Fin (p + 3) → ι) ((0 : Fin (p + 3)).succAbove a)) = i := by
    ext a; simp
  have e1 (k : Fin (p + 2)) : (fun a ↦ (Fin.cons j i : Fin (p + 3) → ι) (k.succ.succAbove a)) =
      (Fin.cons j (fun a ↦ i (k.succAbove a)) : Fin (p + 2) → ι) := by
    ext a
    cases a using Fin.cases <;> simp
  simp only [e0, e1, Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib,
    Fin.val_zero, pow_zero, one_smul]
  abel

/-- The cone homotopy in degree `0`. -/
lemma aug_add_h_d (j : ι) (x : Cochain ι M 0) :
    aug (x fun _ ↦ j) + h j 0 (d 0 x) = x := by
  ext i
  simp only [Pi.add_apply, aug_apply, h_apply, d_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  have e0 : (fun a ↦ (Fin.cons j i : Fin 2 → ι) ((0 : Fin 2).succAbove a)) = i := by
    ext a; simp
  have e1 : (fun a ↦ (Fin.cons j i : Fin 2 → ι) ((0 : Fin 1).succ.succAbove a)) = fun _ ↦ j := by
    ext a; simp [Fin.fin_one_eq_zero a]
  simp only [e0, e1, Fin.val_zero, pow_zero, one_smul, Fin.val_succ, zero_add, pow_one, neg_smul,
    add_zero]
  abel

/-! ### Naturality in the coefficients -/

section Map

variable {M' : Type w} [AddCommGroup M']

/-- Change of coefficients along `φ : M →+ M'`. -/
def map (φ : M →+ M') (p : ℕ) : Cochain ι M p →+ Cochain ι M' p :=
  AddMonoidHom.compLeft φ _

@[simp]
lemma map_apply (φ : M →+ M') (p : ℕ) (x : Cochain ι M p) (i : Fin (p + 1) → ι) :
    map φ p x i = φ (x i) :=
  rfl

@[simp]
lemma d_map (φ : M →+ M') (p : ℕ) (x : Cochain ι M p) :
    d p (map φ p x) = map φ (p + 1) (d p x) := by
  ext i
  simp [d_apply, map_sum, map_zsmul]

@[simp]
lemma h_map (φ : M →+ M') (j : ι) (p : ℕ) (x : Cochain ι M (p + 1)) :
    h j p (map φ (p + 1) x) = map φ p (h j p x) :=
  rfl

end Map

/-! ### Supports -/

section Support

variable [DecidableEq ι]

/-- The image `{i₀, …, iₚ}` of a tuple, as a finset. -/
abbrev im {p : ℕ} (i : Fin (p + 1) → ι) : Finset ι := Finset.univ.image i

lemma im_nonempty {p : ℕ} (i : Fin (p + 1) → ι) : (im i).Nonempty :=
  Finset.univ_nonempty.image i

lemma im_comp_subset {m n : ℕ} (i : Fin (n + 1) → ι) (θ : Fin (m + 1) → Fin (n + 1)) :
    im (fun a ↦ i (θ a)) ⊆ im i := by
  intro t ht
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht ⊢
  obtain ⟨a, rfl⟩ := ht
  exact ⟨_, rfl⟩

lemma im_cons {p : ℕ} (j : ι) (i : Fin (p + 1) → ι) :
    im (Fin.cons j i : Fin (p + 2) → ι) = insert j (im i) := by
  ext t
  simp [Fin.exists_fin_succ, eq_comm]

lemma card_im_le {p : ℕ} (i : Fin (p + 1) → ι) : (im i).card ≤ p + 1 :=
  Finset.card_image_le.trans (by simp)

/-- The restriction to tuples with image in `T`, extended by zero. -/
def res (T : Finset ι) (p : ℕ) : Cochain ι M p →+ Cochain ι M p :=
  AddMonoidHom.mk' (fun x i ↦ if im i ⊆ T then x i else 0) fun x y ↦ by
    ext i; by_cases h : im i ⊆ T <;> simp [h]

@[simp]
lemma res_apply (T : Finset ι) (p : ℕ) (x : Cochain ι M p) (i : Fin (p + 1) → ι) :
    res T p x i = if im i ⊆ T then x i else 0 :=
  rfl

lemma res_res {T T' : Finset ι} (hT : T' ⊆ T) (p : ℕ) (x : Cochain ι M p) :
    res T' p (res T p x) = res T' p x := by
  ext i
  by_cases hi : im i ⊆ T'
  · simp [hi, hi.trans hT]
  · simp [hi]

@[simp]
lemma res_univ [Fintype ι] (p : ℕ) (x : Cochain ι M p) : res Finset.univ p x = x := by
  ext i
  simp

lemma res_d_res (T : Finset ι) (p : ℕ) (x : Cochain ι M p) :
    res T (p + 1) (d p (res T p x)) = res T (p + 1) (d p x) := by
  ext i
  by_cases hi : im i ⊆ T
  · simp only [res_apply, hi, if_true, d_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [if_pos ((im_comp_subset i _).trans hi)]
  · simp [hi]

lemma h_res {T : Finset ι} {j : ι} (hj : j ∈ T) (p : ℕ) (x : Cochain ι M (p + 1)) :
    h j p (res T (p + 1) x) = res T p (h j p x) := by
  ext i
  simp [im_cons, Finset.insert_subset_iff, hj]

/-- A cochain is supported on tuples `i` with `N ⊆ im i ⊆ T`. -/
def SuppBetween (N T : Finset ι) {p : ℕ} (x : Cochain ι M p) : Prop :=
  ∀ i, x i ≠ 0 → N ⊆ im i ∧ im i ⊆ T

/-- A cochain is supported on tuples with image exactly `T`. -/
abbrev SuppEq (T : Finset ι) {p : ℕ} (x : Cochain ι M p) : Prop := SuppBetween T T x

lemma SuppBetween.res_eq {N T : Finset ι} {p : ℕ} {x : Cochain ι M p} (hx : SuppBetween N T x) :
    res T p x = x := by
  ext i
  by_cases hi : im i ⊆ T
  · simp [hi]
  · simp only [res_apply, hi, if_false]
    by_contra h
    exact hi (hx i (Ne.symm h)).2

lemma SuppBetween.res_eq_zero {N T T' : Finset ι} {p : ℕ} {x : Cochain ι M p}
    (hx : SuppBetween N T x) (hN : ¬ N ⊆ T') : res T' p x = 0 := by
  ext i
  by_cases hi : im i ⊆ T'
  · simp only [res_apply, hi, if_true, Pi.zero_apply]
    by_contra h
    exact hN ((hx i h).1.trans hi)
  · simp [hi]

lemma SuppBetween.map_res {N T T' : Finset ι} {p : ℕ} {x : Cochain ι M p}
    (hx : SuppBetween N T x) : SuppBetween N T' (res T' p x) := by
  intro i hi
  simp only [res_apply] at hi
  split_ifs at hi with h
  · exact ⟨(hx i hi).1, h⟩
  · exact absurd rfl hi

lemma SuppBetween.map_D {N T : Finset ι} {p : ℕ} {x : Cochain ι M p} (hx : SuppBetween N T x) :
    SuppBetween N T (res T (p + 1) (d p x)) := by
  intro i hi
  simp only [res_apply] at hi
  split_ifs at hi with hT
  · refine ⟨?_, hT⟩
    rw [d_apply] at hi
    obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
    have hk' : x (fun a ↦ i (k.succAbove a)) ≠ 0 := fun h ↦ hk (by rw [h, smul_zero])
    exact (hx _ hk').1.trans (im_comp_subset i _)
  · exact absurd rfl hi

lemma SuppBetween.mono {N N' T : Finset ι} {p : ℕ} {x : Cochain ι M p} (hx : SuppBetween N T x)
    (hN : N' ⊆ N) : SuppBetween N' T x :=
  fun i hi ↦ ⟨hN.trans (hx i hi).1, (hx i hi).2⟩

lemma SuppBetween.mono_right {N T T' : Finset ι} {p : ℕ} {x : Cochain ι M p}
    (hx : SuppBetween N T x) (hT : T ⊆ T') : SuppBetween N T' x :=
  fun i hi ↦ ⟨(hx i hi).1, (hx i hi).2.trans hT⟩

lemma SuppBetween.zero (N T : Finset ι) (p : ℕ) : SuppBetween N T (0 : Cochain ι M p) :=
  fun _ h ↦ absurd rfl h

lemma SuppBetween.sub {N T : Finset ι} {p : ℕ} {x y : Cochain ι M p} (hx : SuppBetween N T x)
    (hy : SuppBetween N T y) : SuppBetween N T (x - y) := by
  intro i hi
  by_cases h : x i = 0
  · refine hy i fun h' ↦ hi ?_
    simp [h, h']
  · exact hx i h

lemma suppEq_empty {p : ℕ} {x : Cochain ι M p} (hx : SuppEq ∅ x) : x = 0 := by
  ext i
  by_contra h
  exact (im_nonempty i).ne_empty (Finset.subset_empty.mp (hx i h).2)

/-! ### The differential of the subcomplex of cochains supported in `T` -/

/-- The differential of the complex of cochains supported on tuples with image in `T`. -/
def D (T : Finset ι) (p : ℕ) : Cochain ι M p →+ Cochain ι M (p + 1) :=
  (res T (p + 1)).comp (d p)

lemma D_apply (T : Finset ι) (p : ℕ) (x : Cochain ι M p) : D T p x = res T (p + 1) (d p x) :=
  rfl

@[simp]
lemma D_univ [Fintype ι] (p : ℕ) (x : Cochain ι M p) : D Finset.univ p x = d p x := by
  simp [D_apply]

@[simp]
lemma D_D (T : Finset ι) (p : ℕ) (x : Cochain ι M p) : D T (p + 1) (D T p x) = 0 := by
  simp [D_apply, res_d_res]

lemma res_D {T T' : Finset ι} (hT : T' ⊆ T) (p : ℕ) (x : Cochain ι M p) :
    res T' (p + 1) (D T p x) = D T' p (res T' p x) := by
  rw [D_apply, res_res hT, D_apply, res_d_res]

lemma D_h_add_h_D {T : Finset ι} {j : ι} (hj : j ∈ T) (p : ℕ) (x : Cochain ι M (p + 1))
    (hx : res T (p + 1) x = x) : D T p (h j p x) + h j (p + 1) (D T (p + 1) x) = x := by
  rw [D_apply, D_apply, h_res hj, ← map_add, d_h_add_h_d, hx]

/-! ### The homotopy for cochains supported on surjective tuples -/

/-- The correction term `D ∘ g` in positive degrees (and `0` in degree `0`). -/
def corr (T : Finset ι) (g : (p : ℕ) → Cochain ι M (p + 1) →+ Cochain ι M p) :
    (p : ℕ) → Cochain ι M p →+ Cochain ι M p
  | 0 => 0
  | p + 1 => (D T p).comp (g p)

@[simp]
lemma D_corr (T : Finset ι) (g : (p : ℕ) → Cochain ι M (p + 1) →+ Cochain ι M p) (p : ℕ)
    (x : Cochain ι M p) : D T p (corr T g p x) = 0 := by
  cases p with
  | zero => simp [corr]
  | succ p => simp [corr]

/-- The homotopy `G l` of the complex of cochains supported on tuples with image `T = l.toFinset`,
for `l` without duplicates: for `l = j :: l'` and `T' = l'.toFinset`, with `u = h j x`,
`G x = u - D (G' (res_{T'} u)) - G' (res_{T'} (D u))`, `G' = G l'`. -/
def G : List ι → (p : ℕ) → Cochain ι M (p + 1) →+ Cochain ι M p
  | [], _ => 0
  | j :: l, p => h j p - (corr (j :: l).toFinset (G l) p).comp ((res l.toFinset p).comp (h j p)) -
      (G l p).comp ((res l.toFinset (p + 1)).comp ((D (j :: l).toFinset p).comp (h j p)))

@[simp]
lemma G_nil (p : ℕ) (x : Cochain ι M (p + 1)) : G [] p x = 0 :=
  rfl

lemma G_cons (j : ι) (l : List ι) (p : ℕ) (x : Cochain ι M (p + 1)) :
    G (j :: l) p x = h j p x - corr (j :: l).toFinset (G l) p (res l.toFinset p (h j p x)) -
      G l p (res l.toFinset (p + 1) (D (j :: l).toFinset p (h j p x))) :=
  rfl

lemma corr_succ (T : Finset ι) (g : (p : ℕ) → Cochain ι M (p + 1) →+ Cochain ι M p) (p : ℕ)
    (x : Cochain ι M (p + 1)) : corr T g (p + 1) x = D T p (g p x) :=
  rfl

/-- `G l` is a homotopy on the cochains supported on tuples with image `l.toFinset`. -/
theorem D_G_add_G_D (l : List ι) (hl : l.Nodup) (p : ℕ) (x : Cochain ι M (p + 1))
    (hx : SuppEq l.toFinset x) :
    D l.toFinset p (G l p x) + G l (p + 1) (D l.toFinset (p + 1) x) = x := by
  cases l with
  | nil => simp [suppEq_empty hx]
  | cons j l =>
    have hj : j ∉ l := (List.nodup_cons.mp hl).1
    have hjT : j ∈ (j :: l).toFinset := by simp
    have hTT : l.toFinset ⊆ (j :: l).toFinset := by intro t; simp; tauto
    have hx₀ : res l.toFinset (p + 1) x = 0 :=
      hx.res_eq_zero fun h ↦ hj (List.mem_toFinset.mp (h hjT))
    have hxu := D_h_add_h_D hjT p x hx.res_eq
    have h₁ : D (j :: l).toFinset (p + 1)
        (h j (p + 1) (D (j :: l).toFinset (p + 1) x)) = D (j :: l).toFinset (p + 1) x := by
      have := D_h_add_h_D hjT (p + 1) (D (j :: l).toFinset (p + 1) x)
        (by rw [D_apply, res_res le_rfl])
      rwa [D_D, map_zero, add_zero] at this
    have h₂ : res l.toFinset (p + 2) (D (j :: l).toFinset (p + 1) x) = 0 := by
      rw [res_D hTT, hx₀, map_zero]
    have key : G l p (res l.toFinset (p + 1) (D (j :: l).toFinset p (h j p x))) +
        G l p (res l.toFinset (p + 1) (h j (p + 1) (D (j :: l).toFinset (p + 1) x))) = 0 := by
      rw [← map_add, ← map_add, hxu, hx₀, map_zero]
    rw [G_cons, G_cons, corr_succ, map_sub, map_sub, D_corr, sub_zero, h₁, h₂, map_zero,
      sub_zero]
    calc _ = D (j :: l).toFinset p (h j p x) + h j (p + 1) (D (j :: l).toFinset (p + 1) x) -
          D (j :: l).toFinset p
            (G l p (res l.toFinset (p + 1) (D (j :: l).toFinset p (h j p x))) +
              G l p (res l.toFinset (p + 1) (h j (p + 1) (D (j :: l).toFinset (p + 1) x)))) := by
          rw [map_add]; abel
      _ = x := by rw [key, map_zero, sub_zero, hxu]

/-- In degrees `≥ card T - 1`, `G l` preserves the cochains supported on tuples with image
`T = l.toFinset`. -/
theorem suppEq_G (l : List ι) (hl : l.Nodup) (p : ℕ) (hp : l.length ≤ p + 1)
    (x : Cochain ι M (p + 1)) (hx : SuppEq l.toFinset x) : SuppEq l.toFinset (G l p x) := by
  induction l generalizing p x with
  | nil => exact SuppBetween.zero _ _ _
  | cons j l ih =>
    obtain ⟨hj, hl'⟩ := List.nodup_cons.mp hl
    have hT : (j :: l).toFinset = insert j l.toFinset := List.toFinset_cons
    have hTT : l.toFinset ⊆ (j :: l).toFinset := by rw [hT]; exact Finset.subset_insert _ _
    have hu : SuppBetween l.toFinset (j :: l).toFinset (h j p x) := by
      intro i hi
      obtain ⟨h₁, h₂⟩ := hx _ hi
      rw [im_cons] at h₁ h₂
      refine ⟨fun t ht ↦ ?_, (Finset.subset_insert _ _).trans h₂⟩
      rcases Finset.mem_insert.mp (h₁ (hTT ht)) with rfl | h
      · exact absurd (List.mem_toFinset.mp ht) hj
      · exact h
    have hw : SuppEq l.toFinset (res l.toFinset p (h j p x)) := hu.map_res
    have h₃ : SuppEq l.toFinset
        (G l p (res l.toFinset (p + 1) (D (j :: l).toFinset p (h j p x)))) :=
      ih hl' p (by rw [List.length_cons] at hp; omega) _ hu.map_D.map_res
    have h₂ : SuppBetween l.toFinset (j :: l).toFinset
        (corr (j :: l).toFinset (G l) p (res l.toFinset p (h j p x))) := by
      cases p with
      | zero => exact SuppBetween.zero _ _ _
      | succ p =>
        rw [corr_succ]
        exact ((ih hl' p (by rw [List.length_cons] at hp; omega) _ hw).mono_right hTT).map_D
    have hG : SuppBetween l.toFinset (j :: l).toFinset (G (j :: l) p x) := by
      rw [G_cons]
      exact (hu.sub h₂).sub (h₃.mono_right hTT)
    have hG₀ : res l.toFinset p (G (j :: l) p x) = 0 := by
      rw [G_cons, map_sub, map_sub, h₃.res_eq]
      cases p with
      | zero =>
        have hl0 : l = [] := List.eq_nil_of_length_eq_zero (by rw [List.length_cons] at hp; omega)
        subst hl0
        have := suppEq_empty hw
        simp only [List.toFinset_nil] at this ⊢
        simp [this, corr]
      | succ p =>
        rw [corr_succ, res_D hTT, (ih hl' p (by rw [List.length_cons] at hp; omega) _ hw).res_eq,
          res_D hTT]
        rw [sub_sub, D_G_add_G_D l hl' p _ hw, sub_self]
    intro i hi
    obtain ⟨h₁, h₂⟩ := hG i hi
    refine ⟨?_, h₂⟩
    have hji : j ∈ im i := by
      by_contra hji
      refine hi ?_
      have h₄ : im i ⊆ l.toFinset := by
        intro t ht
        have := h₂ ht
        rw [hT, Finset.mem_insert] at this
        rcases this with rfl | h
        · exact absurd ht hji
        · exact h
      simpa [h₄] using congrFun hG₀ i
    rw [hT]
    exact Finset.insert_subset hji h₁

/-! ### Naturality of `res`, `D` and `G` -/

section Map

variable {M' : Type w} [AddCommGroup M']

@[simp]
lemma res_map (φ : M →+ M') (T : Finset ι) (p : ℕ) (x : Cochain ι M p) :
    res T p (map φ p x) = map φ p (res T p x) := by
  ext i
  by_cases hi : im i ⊆ T <;> simp [hi]

@[simp]
lemma D_map (φ : M →+ M') (T : Finset ι) (p : ℕ) (x : Cochain ι M p) :
    D T p (map φ p x) = map φ (p + 1) (D T p x) := by
  simp [D_apply]

lemma G_map (φ : M →+ M') (l : List ι) (p : ℕ) (x : Cochain ι M (p + 1)) :
    G l p (map φ (p + 1) x) = map φ p (G l p x) := by
  induction l generalizing p with
  | nil => simp
  | cons j l ih =>
    rw [G_cons, G_cons]
    cases p with
    | zero => simp [ih, corr]
    | succ p => simp [ih, corr_succ]

end Map

end Support

/-! ### Monomially graded coefficients -/

section Grading

variable [DecidableEq ι] [Fintype ι]

/-- The homotopy on the `N`-component: the cone on some `j ∉ N` if `N ≠ univ`, and `G` for a
list of all elements of `ι` if `N = univ`. -/
noncomputable def homotopyN (N : Finset ι) (p : ℕ) : Cochain ι M (p + 1) →+ Cochain ι M p :=
  if hN : ∃ j, j ∉ N then h hN.choose p else G Finset.univ.toList p

lemma homotopyN_map {M' : Type w} [AddCommGroup M'] (φ : M →+ M') (N : Finset ι) (p : ℕ)
    (x : Cochain ι M (p + 1)) : homotopyN N p (map φ (p + 1) x) = map φ p (homotopyN N p x) := by
  unfold homotopyN
  split_ifs
  · rfl
  · exact G_map φ _ p x

/-- `homotopyN N` is a homotopy on cochains supported on tuples whose image contains `N`. -/
lemma d_homotopyN_add (N : Finset ι) (p : ℕ) (x : Cochain ι M (p + 1))
    (hx : SuppBetween N Finset.univ x) :
    d p (homotopyN N p x) + homotopyN N (p + 1) (d (p + 1) x) = x := by
  unfold homotopyN
  split_ifs with hN
  · exact d_h_add_h_d _ p x
  · push Not at hN
    obtain rfl : N = Finset.univ := Finset.eq_univ_of_forall hN
    have := D_G_add_G_D (M := M) Finset.univ.toList (Finset.nodup_toList _) p x
      (by rwa [Finset.toList_toFinset])
    simpa only [Finset.toList_toFinset, D_univ] using this

/-- `homotopyN N` preserves cochains supported on tuples whose image contains `N`, except
possibly for `N = univ` in degrees `< card ι - 1`. -/
lemma suppBetween_homotopyN (N : Finset ι) (p : ℕ) (x : Cochain ι M (p + 1))
    (hx : SuppBetween N Finset.univ x) (hp : Fintype.card ι ≤ p + 1 ∨ (N = Finset.univ → x = 0)) :
    SuppBetween N Finset.univ (homotopyN N p x) := by
  unfold homotopyN
  split_ifs with hN
  · intro i hi
    refine ⟨fun t ht ↦ ?_, Finset.subset_univ _⟩
    have := (hx _ hi).1 ht
    rw [im_cons, Finset.mem_insert] at this
    rcases this with rfl | h
    · exact absurd ht hN.choose_spec
    · exact h
  · push Not at hN
    obtain rfl : N = Finset.univ := Finset.eq_univ_of_forall hN
    rcases hp with hp | hp
    · have := suppEq_G (M := M) Finset.univ.toList (Finset.nodup_toList _) p
        (by rwa [Finset.length_toList]) x (by rwa [Finset.toList_toFinset])
      rwa [Finset.toList_toFinset] at this
    · rw [hp rfl, map_zero]
      exact SuppBetween.zero _ _ _

/-- `homotopyN N` is given by an integer matrix, independent of the coefficients. -/
lemma homotopyN_eq_sum (N : Finset ι) (p : ℕ) (x : Cochain ι M (p + 1)) (i : Fin (p + 1) → ι) :
    homotopyN N p x i =
      ∑ i' : Fin (p + 2) → ι, homotopyN N p (Pi.single i' (1 : ℤ)) i • x i' := by
  classical
  have hx : x = ∑ i' : Fin (p + 2) → ι,
      map (zmultiplesHom M (x i')) (p + 1) (Pi.single i' (1 : ℤ)) := by
    ext i''
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  simp only [map_sum, homotopyN_map, Finset.sum_apply, map_apply, zmultiplesHom_apply]

variable (ι M) in
/-- A *grading by negative supports* on `M`: orthogonal idempotents `proj N : M →+ M`, indexed by
`N : Finset ι`, summing to the identity. (For Laurent series `∑ₐ cₐ xᵃ`, `proj N` keeps the
monomials with `{j | aⱼ < 0} = N`.) -/
structure Grading where
  /-- The projection onto the `N`-component. -/
  proj : Finset ι → M →+ M
  sum_proj : ∀ m, ∑ N, proj N m = m
  proj_proj : ∀ N N' m, proj N (proj N' m) = if N = N' then proj N m else 0

namespace Grading

variable (π : Grading ι M)

/-- A cochain is admissible if `π N (x i) = 0` unless `N ⊆ im i`. -/
def IsAdmissible {p : ℕ} (x : Cochain ι M p) : Prop :=
  ∀ i N, ¬ N ⊆ im i → π.proj N (x i) = 0

lemma IsAdmissible.suppBetween {p : ℕ} {x : Cochain ι M p} (hx : π.IsAdmissible x)
    (N : Finset ι) : SuppBetween N Finset.univ (map (π.proj N) p x) :=
  fun i hi ↦ ⟨by_contra fun h ↦ hi (hx i N h), Finset.subset_univ _⟩

lemma sum_map_proj {p : ℕ} (x : Cochain ι M p) : ∑ N, map (π.proj N) p x = x := by
  ext i
  simp [Finset.sum_apply, π.sum_proj]

lemma map_proj_map_proj (N N' : Finset ι) {p : ℕ} (x : Cochain ι M p) :
    map (π.proj N) p (map (π.proj N') p x) = if N = N' then map (π.proj N) p x else 0 := by
  ext i
  split_ifs with h <;> simp [π.proj_proj, h]

lemma isAdmissible_d {p : ℕ} {x : Cochain ι M p} (hx : π.IsAdmissible x) :
    π.IsAdmissible (d p x) := by
  intro i N hN
  rw [d_apply, map_sum]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [map_zsmul, hx _ N fun h ↦ hN (h.trans (im_comp_subset i _)), smul_zero]

lemma proj_univ_eq_zero {p : ℕ} {x : Cochain ι M p} (hx : π.IsAdmissible x)
    (hp : p + 1 < Fintype.card ι) (i : Fin (p + 1) → ι) : π.proj Finset.univ (x i) = 0 := by
  refine hx i _ fun h ↦ ?_
  have := Finset.card_le_card h
  rw [Finset.card_univ] at this
  exact absurd ((this.trans (card_im_le i)).trans_lt hp) (lt_irrefl _)

/-- The homotopy `∑_N homotopyN N ∘ π N`. -/
noncomputable def homotopy (p : ℕ) : Cochain ι M (p + 1) →+ Cochain ι M p :=
  ∑ N, (homotopyN N p).comp (map (π.proj N) (p + 1))

lemma homotopy_apply (p : ℕ) (x : Cochain ι M (p + 1)) :
    π.homotopy p x = ∑ N, homotopyN N p (map (π.proj N) (p + 1) x) := by
  simp [homotopy]

lemma proj_homotopy (N : Finset ι) (p : ℕ) (x : Cochain ι M (p + 1)) (i : Fin (p + 1) → ι) :
    π.proj N (π.homotopy p x i) = homotopyN N p (map (π.proj N) (p + 1) x) i := by
  rw [← map_apply (π.proj N) p, homotopy_apply, map_sum]
  simp only [← homotopyN_map, map_proj_map_proj]
  simp [Finset.sum_apply, apply_ite, ite_apply]

/-- `d ∘ H + H ∘ d = id` on admissible cochains of positive degree. -/
theorem d_homotopy_add {p : ℕ} (x : Cochain ι M (p + 1)) (hx : π.IsAdmissible x) :
    d p (π.homotopy p x) + π.homotopy (p + 1) (d (p + 1) x) = x := by
  rw [homotopy_apply, homotopy_apply, map_sum, ← Finset.sum_add_distrib]
  conv_rhs => rw [← π.sum_map_proj x]
  refine Finset.sum_congr rfl fun N _ ↦ ?_
  rw [← d_map, d_homotopyN_add N p _ (hx.suppBetween π N)]

/-- The homotopy preserves admissibility, provided `π univ ∘ x = 0` or `card ι ≤ p + 1`. -/
theorem isAdmissible_homotopy {p : ℕ} {x : Cochain ι M (p + 1)} (hx : π.IsAdmissible x)
    (hp : Fintype.card ι ≤ p + 1 ∨ ∀ i, π.proj Finset.univ (x i) = 0) :
    π.IsAdmissible (π.homotopy p x) := by
  intro i N hN
  rw [proj_homotopy]
  have hs := suppBetween_homotopyN N p _ (hx.suppBetween π N) (by
    refine hp.imp id fun hp hN ↦ ?_
    subst hN
    ext i
    exact hp i)
  by_contra h
  exact hN (hs i h).1

/-- The homotopy preserves values in a `π`-stable subgroup. -/
theorem homotopy_mem (S : AddSubgroup M) (hS : ∀ N, ∀ m ∈ S, π.proj N m ∈ S) {p : ℕ}
    {x : Cochain ι M (p + 1)} (hx : ∀ i, x i ∈ S) (i : Fin (p + 1) → ι) :
    π.homotopy p x i ∈ S := by
  rw [homotopy_apply, Finset.sum_apply]
  refine sum_mem fun N _ ↦ ?_
  have : map (π.proj N) (p + 1) x =
      map S.subtype (p + 1) (fun i ↦ ⟨π.proj N (x i), hS N _ (hx i)⟩) := rfl
  rw [this, homotopyN_map]
  exact SetLike.coe_mem _

/-- **Vanishing in positive degrees**: an admissible cocycle of degree `p + 1` with values in a
`π`-stable subgroup `S` is the coboundary of an admissible cochain with values in `S`, provided
`card ι ≤ p + 1` or `π univ ∘ x = 0` (the latter is automatic if `p + 2 < card ι`, by
`proj_univ_eq_zero`). -/
theorem exists_eq_d (S : AddSubgroup M) (hS : ∀ N, ∀ m ∈ S, π.proj N m ∈ S) {p : ℕ}
    (x : Cochain ι M (p + 1)) (hx : π.IsAdmissible x) (hxS : ∀ i, x i ∈ S)
    (hdx : d (p + 1) x = 0)
    (hp : Fintype.card ι ≤ p + 1 ∨ ∀ i, π.proj Finset.univ (x i) = 0) :
    ∃ y : Cochain ι M p, π.IsAdmissible y ∧ (∀ i, y i ∈ S) ∧ d p y = x := by
  refine ⟨π.homotopy p x, π.isAdmissible_homotopy hx hp, π.homotopy_mem S hS hxS, ?_⟩
  simpa [hdx] using π.d_homotopy_add x hx

lemma isAdmissible_aug {v : M} (hv : π.proj ∅ v = v) : π.IsAdmissible (aug (ι := ι) v) := by
  intro i N hN
  have hN' : N ≠ ∅ := by rintro rfl; exact hN (Finset.empty_subset _)
  rw [aug_apply, ← hv, π.proj_proj, if_neg hN']

/-- **Degree `0`**: an admissible `0`-cocycle `x` with `π univ ∘ x = 0` is constant, with value in
the image of `π ∅` (the "constants"). -/
theorem exists_eq_aug [Nonempty ι] (x : Cochain ι M 0) (hx : π.IsAdmissible x)
    (hdx : d 0 x = 0) (huniv : ∀ i, π.proj Finset.univ (x i) = 0) :
    ∃ v, π.proj ∅ v = v ∧ x = aug v := by
  obtain ⟨j₀⟩ := ‹Nonempty ι›
  refine ⟨π.proj ∅ (x fun _ ↦ j₀), by rw [π.proj_proj, if_pos rfl], ?_⟩
  have key (N : Finset ι) : map (π.proj N) 0 x =
      if N = ∅ then aug (π.proj ∅ (x fun _ ↦ j₀)) else 0 := by
    have hd : d 0 (map (π.proj N) 0 x) = 0 := by rw [d_map, hdx, map_zero]
    split_ifs with hN
    · subst hN
      rw [← aug_add_h_d j₀ (map (π.proj ∅) 0 x), hd, map_zero, add_zero, map_apply]
    · by_cases hj : ∃ j, j ∉ N
      · obtain ⟨j, hj⟩ := hj
        rw [← aug_add_h_d j (map (π.proj N) 0 x), hd, map_zero, add_zero, map_apply]
        rw [hx _ N, map_zero]
        intro h
        obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.mpr hN
        have := h ht
        simp only [im, Finset.mem_image, Finset.mem_univ, true_and] at this
        obtain ⟨_, rfl⟩ := this
        exact hj ht
      · push Not at hj
        obtain rfl : N = Finset.univ := Finset.eq_univ_of_forall hj
        ext i
        exact huniv i
  conv_lhs => rw [← π.sum_map_proj x]
  rw [Finset.sum_congr rfl fun N _ ↦ key N, Finset.sum_ite_eq']
  simp

end Grading

end Grading

end SimplexCochain

end
