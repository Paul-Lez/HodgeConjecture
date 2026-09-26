/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Topology.Sheaves.Cohomology.PushforwardAcyclic

/-!
# Leray's theorem on opens and localisation of Čech complexes

* `TopCat.Sheaf.H_restrictOpen_eq_zero_of_isCechAcyclic` (**Leray**, vanishing form, on an
  open): if `U` covers the open `W`, `F` has no higher cohomology on the finite intersections
  `U_σ`, and `Č•(U, F)` is exact in positive degrees, then `Hⁿ(W, F|_W) = 0` for `n ≥ 1`.
* `TopCat.Presheaf.exactAt_cechComplex_of_localization`: let `U' i ≤ U i` be two finite families
  of opens and `μ : P ⟶ P` an endomorphism of a presheaf of abelian groups which is bijective on
  the sections over the `U'_σ`, such that `P(U_σ) → P(U'_σ)` is "the localisation at `μ`": every
  section over `U'_σ` is, after applying a power of `μ`, the restriction of a section over `U_σ`,
  and sections over `U_σ` restricting to zero are killed by a power of `μ`. Then exactness of
  `Č•(U, P)` in a positive degree implies exactness of `Č•(U', P)` in that degree. This is the
  Čech-level form of `Hᵠ(X_f, F) = Hᵠ(X, F)_f`.
* `TopCat.Sheaf.isPushforwardAcyclic_of_forall_exists`: a sheaf `G` is `f`-acyclic if every
  neighbourhood of every point of `X` contains an open neighbourhood `V'` with
  `Hᵠ(f⁻¹ V', G) = 0` for all `q ≥ 1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

section Leray

variable {ι : Type u} (U : ι → Opens X) {W : Opens X}

/-- **Leray's theorem** (vanishing form) for a cover of an open `W`. Let `U` be a family of opens
with union `W` such that `F` has no higher cohomology on any finite intersection `U_σ`, and such
that the Čech complex `Č•(U, F)` is exact in positive degrees. Then `Hⁿ(W, F|_W) = 0` for all
`n ≥ 1`. -/
theorem H_restrictOpen_eq_zero_of_isCechAcyclic (hU : ⨆ i, U i = W) (F : AbSheaf X)
    (hF : ∀ (n : ℕ) (σ : Fin (n + 1) → ι) (q : ℕ)
      (x : H ((restrictOpen (TopCat.Presheaf.cechOpen U σ)).obj F) (q + 1)), x = 0)
    (hC : TopCat.Presheaf.IsCechAcyclic U F.obj) (q : ℕ)
    (x : H ((restrictOpen W).obj F) (q + 1)) : x = 0 := by
  have hW : ∀ i, U i ≤ W := fun i ↦ hU ▸ le_iSup U i
  induction q generalizing F with
  | zero =>
    exact H_one_restrictOpen_eq_zero_of_surjective W (injSES_shortExact F)
      (surjective_of_cech U (injSES_shortExact F) hW hU.ge
        (fun σ ↦ hF 0 σ 0) (hC 0)) x
  | succ q ih =>
    let S := injSES F
    have hS : S.ShortExact := injSES_shortExact F
    have hsurj : ∀ (n : ℕ) (σ : Fin (n + 1) → ι),
        Function.Surjective (S.g.hom.app (op (TopCat.Presheaf.cechOpen U σ))) :=
      fun n σ ↦ surjective_of_H_one_restrictOpen _ hS (hF n σ 0)
    refine H_succ_succ_restrictOpen_eq_zero W hS (fun z ↦ ih S.X₃ (fun n σ q' z' ↦ ?_) ?_ z) x
    · exact H_succ_restrictOpen_eq_zero_of_H_succ_succ _ hS (hF n σ (q' + 1)) z'
    · exact isCechAcyclic_X₃ hS hC (TopCat.Presheaf.isCechAcyclic_of_injective_sheaf U S.X₂)
        hsurj

end Leray

section PushforwardAcyclic

variable {Y : TopCat.{u}} {f : Y ⟶ X}

/-- A sheaf `G` on `Y` is `f`-acyclic if every open `V ⊆ X` contains, around each of its points,
an open `V'` with `Hᵠ(f⁻¹ V', G) = 0` for all `q ≥ 1`. -/
lemma isPushforwardAcyclic_of_forall_exists (G : AbSheaf Y)
    (h : ∀ (V : Opens X) (x : X), x ∈ V → ∃ V' ≤ V, x ∈ V' ∧ ∀ (q : ℕ)
      (c : H ((restrictOpen ((Opens.map f).obj V')).obj G) (q + 1)), c = 0) :
    IsPushforwardAcyclic f G := by
  rw [isPushforwardAcyclic_iff]
  intro q V c x hx
  obtain ⟨V', hV', hx', h0⟩ := h V x hx
  exact ⟨V', hV', hx', h0 q _⟩

end PushforwardAcyclic

end TopCat.Sheaf

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {ι : Type u} {U U' : ι → Opens X} (hUU' : ∀ i, U' i ≤ U i)
  (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})

include hUU' in
lemma cechOpen_mono {n : ℕ} (σ : Fin (n + 1) → ι) : cechOpen U' σ ≤ cechOpen U σ :=
  iInf_mono fun a ↦ hUU' (σ a)

/-- Restriction of Čech cochains from the family `U` to a smaller family `U'`. -/
def cechRestrict (n : ℕ) : CechCochain U P n →+ CechCochain U' P n where
  toFun c σ := P.map (homOfLE (cechOpen_mono hUU' σ)).op (c σ)
  map_zero' := by ext; simp
  map_add' c c' := by ext; simp

lemma cechRestrict_apply (n : ℕ) (c : CechCochain U P n) (σ : Fin (n + 1) → ι) :
    cechRestrict hUU' P n c σ = P.map (homOfLE (cechOpen_mono hUU' σ)).op (c σ) :=
  rfl

/-- Restriction of cochains commutes with the Čech differential. -/
lemma cechD_cechRestrict (n : ℕ) (c : CechCochain U P n) :
    cechD U' P n (cechRestrict hUU' P n c) = cechRestrict hUU' P (n + 1) (cechD U P n c) := by
  funext τ
  simp only [cechD_apply, cechRestrict_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_homOfLE_map_homOfLE, map_homOfLE_map_homOfLE]

variable {P} (μ : P ⟶ P)

/-- Restriction of cochains commutes with an endomorphism of the presheaf. -/
lemma cechRestrict_cechCochainMap (n : ℕ) (c : CechCochain U P n) :
    cechRestrict hUU' P n (cechCochainMap U μ n c) =
      cechCochainMap U' μ n (cechRestrict hUU' P n c) := by
  funext σ
  simp only [cechRestrict_apply, cechCochainMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, μ.naturality]

lemma cechRestrict_iterate_cechCochainMap (n k : ℕ) (c : CechCochain U P n) :
    cechRestrict hUU' P n ((cechCochainMap U μ n)^[k] c) =
      (cechCochainMap U' μ n)^[k] (cechRestrict hUU' P n c) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih,
      cechRestrict_cechCochainMap]

lemma cechD_iterate_cechCochainMap {V : ι → Opens X} (n k : ℕ) (c : CechCochain V P n) :
    cechD V P n ((cechCochainMap V μ n)^[k] c) =
      (cechCochainMap V μ (n + 1))^[k] (cechD V P n c) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, cechD_cechCochainMap]

lemma iterate_cechCochainMap_apply {V : ι → Opens X} (n k : ℕ) (c : CechCochain V P n)
    (σ : Fin (n + 1) → ι) :
    (cechCochainMap V μ n)^[k] c σ = (μ.app (op (cechOpen V σ)))^[k] (c σ) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

lemma iterate_app_map {A B : Opens X} (h : A ≤ B) (k : ℕ) (x : P.obj (op B)) :
    (μ.app (op A))^[k] (P.map (homOfLE h).op x) = P.map (homOfLE h).op ((μ.app (op B))^[k] x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, μ.naturality]

lemma iterate_app_add {A : Opens X} (k l : ℕ) (x : P.obj (op A)) :
    (μ.app (op A))^[k + l] x = (μ.app (op A))^[k] ((μ.app (op A))^[l] x) :=
  Function.iterate_add_apply _ k l x

lemma iterate_app_zero {A : Opens X} (k : ℕ) : (μ.app (op A))^[k] 0 = 0 :=
  Function.iterate_fixed (map_zero _) k

variable [Finite ι]

include hUU' in
/-- **Čech complexes localise.** Let `U' i ≤ U i` be finite families of opens and `μ : P ⟶ P`
bijective on the sections over every `U'_σ`. Suppose that in degree `n + 1` every section over
`U'_σ` becomes, after applying a power of `μ`, the restriction of a section over `U_σ`, and that
in degree `n + 2` sections over `U_σ` restricting to zero on `U'_σ` are killed by a power of `μ`.
If `Č•(U, P)` is exact in degree `n + 1`, so is `Č•(U', P)`. -/
theorem exactAt_cechComplex_of_localization (n : ℕ)
    (hext : ∀ (σ : Fin (n + 2) → ι) (s : P.obj (op (cechOpen U' σ))), ∃ (k : ℕ)
      (t : P.obj (op (cechOpen U σ))),
        P.map (homOfLE (cechOpen_mono hUU' σ)).op t = (μ.app _)^[k] s)
    (hzero : ∀ (σ : Fin (n + 3) → ι) (t : P.obj (op (cechOpen U σ))),
      P.map (homOfLE (cechOpen_mono hUU' σ)).op t = 0 → ∃ k : ℕ, (μ.app _)^[k] t = 0)
    (hbij : ∀ (m : ℕ) (σ : Fin (m + 1) → ι), Function.Bijective (μ.app (op (cechOpen U' σ))))
    (h : (cechComplex U P).ExactAt (n + 1)) : (cechComplex U' P).ExactAt (n + 1) := by
  classical
  have := Fintype.ofFinite ι
  rw [exactAt_cechComplex_succ_iff] at h ⊢
  intro c hc
  -- lift `μᴷ c` to a cochain `T` on `U`
  choose k t ht using fun σ ↦ hext σ (c σ)
  obtain ⟨K, hK⟩ : ∃ K, ∀ σ, k σ ≤ K := ⟨_, fun σ ↦ Finset.le_sup (Finset.mem_univ σ)⟩
  let T : CechCochain U P (n + 1) := fun σ ↦ (μ.app _)^[K - k σ] (t σ)
  have hT : cechRestrict hUU' P (n + 1) T = (cechCochainMap U' μ (n + 1))^[K] c := by
    funext σ
    rw [iterate_cechCochainMap_apply, cechRestrict_apply, ← iterate_app_map, ht,
      ← iterate_app_add, Nat.sub_add_cancel (hK σ)]
  -- `μᴸ T` is a cocycle
  have hdT : ∀ τ, P.map (homOfLE (cechOpen_mono hUU' τ)).op (cechD U P (n + 1) T τ) = 0 := by
    intro τ
    rw [← cechRestrict_apply hUU', ← cechD_cechRestrict, hT, cechD_iterate_cechCochainMap, hc,
      Function.iterate_fixed (map_zero _) K]
    rfl
  choose l hl using fun τ ↦ hzero τ _ (hdT τ)
  obtain ⟨L, hL⟩ : ∃ L, ∀ τ, l τ ≤ L := ⟨_, fun τ ↦ Finset.le_sup (Finset.mem_univ τ)⟩
  have hdT' : cechD U P (n + 1) ((cechCochainMap U μ (n + 1))^[L] T) = 0 := by
    rw [cechD_iterate_cechCochainMap]
    funext τ
    rw [iterate_cechCochainMap_apply, ← Nat.sub_add_cancel (hL τ), iterate_app_add, hl,
      iterate_app_zero]
    rfl
  obtain ⟨B, hB⟩ := h _ hdT'
  -- restrict `B` to `U'` and divide by `μᴸ⁺ᴷ`
  have hB' : cechD U' P n (cechRestrict hUU' P n B) =
      (cechCochainMap U' μ (n + 1))^[L + K] c := by
    rw [cechD_cechRestrict, hB, cechRestrict_iterate_cechCochainMap, hT,
      ← Function.iterate_add_apply]
  choose b hb using fun σ : Fin (n + 1) → ι ↦
    ((hbij n σ).iterate (L + K)).2 (cechRestrict hUU' P n B σ)
  refine ⟨b, funext fun τ ↦ ((hbij (n + 1) τ).iterate (L + K)).1 ?_⟩
  have hb' : (cechCochainMap U' μ n)^[L + K] b = cechRestrict hUU' P n B :=
    funext fun σ ↦ (iterate_cechCochainMap_apply μ n _ b σ).trans (hb σ)
  rw [← iterate_cechCochainMap_apply, ← iterate_cechCochainMap_apply,
    ← cechD_iterate_cechCochainMap, hb', hB']

end TopCat.Presheaf

end
