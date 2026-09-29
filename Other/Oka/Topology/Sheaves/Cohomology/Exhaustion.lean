/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Topology.Sheaves.Cohomology.LocalVanishing

/-!
# Cohomology of an increasing union

Let `F` be an abelian sheaf on `X`, `U₀ ≤ U₁ ≤ ⋯` opens of `X` and `W = ⋃ₙ Uₙ`. We show that a
class `c ∈ Hᵠ⁺¹(W, F)` which restricts to zero on every `Uₙ` vanishes, provided
`lim¹ₙ Hᵠ(Uₙ, F) = 0` (for `q = 0`: `lim¹ₙ F(Uₙ) = 0`). Here `lim¹ = 0` is used in the concrete form
`TopCat.Sheaf.LimOneVanishes`: for every family `sₙ ∈ Aₙ` there are `aₙ ∈ Aₙ` with
`sₙ = aₙ - aₙ₊₁|_{Uₙ}`. It holds for instance if all transition maps are surjective or zero.

The proof avoids derived limits and works by dimension shifting along `0 → F → I → Q → 0` with
`I` injective. In degree one, `c` comes from `σ ∈ Q(W)`; on each `Uₙ`, `σ` lifts to `aₙ ∈ I(Uₙ)`,
the differences `aₙ₊₁|_{Uₙ} - aₙ` lie in `F(Uₙ)`, and `lim¹ₙ F(Uₙ) = 0` allows to correct the
`aₙ` to a compatible family, which glues to a lift of `σ`. In degree `q + 2`, `c` comes from a
class in `Hᵠ⁺¹(W, Q)` which restricts to zero on every `Uₙ`, and `lim¹ₙ Hᵠ(Uₙ, Q) = 0` follows
from the exact sequences `Hᵠ(Uₙ, I) → Hᵠ(Uₙ, Q) → Hᵠ⁺¹(Uₙ, F) → 0` (the transition maps of
`H⁰(Uₙ, I) = I(Uₙ)` are surjective since `I` is injective).

## Main results

* `TopCat.Sheaf.LimOneVanishes`, `TopCat.Sheaf.LimOneVanishesOn`: vanishing of `lim¹` of an
  inverse sequence of abelian groups, resp. of `P(Uₙ)` for a presheaf `P`, with the criteria
  `LimOneVanishes.of_surjective`, `of_eq_zero`, `of_subsingleton`, `of_surjective_map`, `of_exact`.
* `TopCat.Sheaf.H'_eq_zero_of_monotone` (Mathlib's `H' F q U = Extᵠ(ℤ[U], F)`, restriction maps
  `H'res`), with the degree one version `H'_one_eq_zero_of_monotone` (hypothesis on sections)
  and `H'_eq_zero_of_monotone_of_res_eq_zero` (transition maps `H'ᵠ⁺¹(Uₙ₊₁) → H'ᵠ⁺¹(Uₙ)` zero).
* `TopCat.Sheaf.H_restrictOpen_eq_zero_of_monotone`, `H_one_restrictOpen_eq_zero_of_monotone`,
  `H_restrictOpen_eq_zero_of_monotone_of_res_eq_zero`: the same for `Hᵠ(W, F|_W)` and the
  restriction maps `restrictOpenRes`.
* Vanishing forms `subsingleton_H'_iSup_of_monotone`, `subsingleton_H_restrictOpen_iSup_of_monotone`
  and variants, and the global versions `subsingleton_H_of_monotone`,
  `subsingleton_H_one_of_monotone`, `subsingleton_H_of_monotone_of_subsingleton` for an
  exhaustion `⋃ₙ Uₙ = X`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace TopCat.Sheaf

section LimOne

variable {A B C : ℕ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]
  [∀ n, AddCommGroup (C n)]

/-- Vanishing of `lim¹` of the inverse sequence `⋯ → A (n + 1) → A n → ⋯` with transition maps
`r n`, in concrete form: the map `∏ₙ A n → ∏ₙ A n`, `(aₙ) ↦ (aₙ - r n aₙ₊₁)` is surjective. -/
def LimOneVanishes (r : ∀ n, A (n + 1) →+ A n) : Prop :=
  ∀ s : ∀ n, A n, ∃ a : ∀ n, A n, ∀ n, s n = a n - r n (a (n + 1))

namespace LimOneVanishes

/-- `lim¹` vanishes for an inverse sequence with surjective transition maps. -/
lemma of_surjective {r : ∀ n, A (n + 1) →+ A n} (hr : ∀ n, Function.Surjective (r n)) :
    LimOneVanishes r := by
  intro s
  let a : ∀ n, A n := fun n => Nat.rec (motive := A) 0 (fun n an => (hr n (an - s n)).choose) n
  refine ⟨a, fun n => ?_⟩
  have : r n (a (n + 1)) = a n - s n := (hr n _).choose_spec
  rw [this]
  abel

/-- `lim¹` vanishes for an inverse sequence with zero transition maps. -/
lemma of_eq_zero {r : ∀ n, A (n + 1) →+ A n} (hr : ∀ n, r n = 0) : LimOneVanishes r :=
  fun s => ⟨s, fun n => by simp [hr]⟩

/-- `lim¹` vanishes for a quotient of an inverse sequence with vanishing `lim¹`. -/
lemma of_surjective_map {rA : ∀ n, A (n + 1) →+ A n} {rB : ∀ n, B (n + 1) →+ B n}
    (φ : ∀ n, A n →+ B n) (hφ : ∀ n x, φ n (rA n x) = rB n (φ (n + 1) x))
    (hsurj : ∀ n, Function.Surjective (φ n)) (h : LimOneVanishes rA) : LimOneVanishes rB := by
  intro s
  choose t ht using fun n => hsurj n (s n)
  obtain ⟨a, ha⟩ := h t
  refine ⟨fun n => φ n (a n), fun n => ?_⟩
  rw [← hφ, ← map_sub, ← ha, ht]

/-- If `A → B → C → 0` is an exact sequence of inverse sequences and `lim¹` vanishes for `A` and
`C`, then it vanishes for `B`. -/
lemma of_exact {rA : ∀ n, A (n + 1) →+ A n} {rB : ∀ n, B (n + 1) →+ B n}
    {rC : ∀ n, C (n + 1) →+ C n} (φ : ∀ n, A n →+ B n) (ψ : ∀ n, B n →+ C n)
    (hφ : ∀ n x, φ n (rA n x) = rB n (φ (n + 1) x))
    (hψ : ∀ n x, ψ n (rB n x) = rC n (ψ (n + 1) x))
    (hex : ∀ n, Function.Exact (φ n) (ψ n)) (hsurj : ∀ n, Function.Surjective (ψ n))
    (hA : LimOneVanishes rA) (hC : LimOneVanishes rC) : LimOneVanishes rB := by
  intro s
  obtain ⟨x, hx⟩ := hC (fun n => ψ n (s n))
  choose y hy using fun n => hsurj n (x n)
  have h0 : ∀ n, ψ n (s n - (y n - rB n (y (n + 1)))) = 0 := by
    intro n
    rw [map_sub, map_sub, hy, hψ, hy, hx, sub_self]
  choose z hz using fun n => (hex n _).1 (h0 n)
  obtain ⟨w, hw⟩ := hA z
  refine ⟨fun n => y n + φ n (w n), fun n => ?_⟩
  have e := hz n
  rw [hw n, map_sub, hφ] at e
  simp only [map_add]
  rw [show φ n (w n) = s n - (y n - rB n (y (n + 1))) + rB n (φ (n + 1) (w (n + 1))) by
    rw [← e]; abel]
  abel

/-- `lim¹` vanishes for an inverse sequence of subsingletons. -/
lemma of_subsingleton [∀ n, Subsingleton (A n)] (r : ∀ n, A (n + 1) →+ A n) : LimOneVanishes r :=
  of_surjective fun _ _ => ⟨0, Subsingleton.elim _ _⟩

end LimOneVanishes

end LimOne

variable {X : TopCat.{u}}

/-- `lim¹ₙ P(Uₙ) = 0` for a presheaf `P` of abelian groups and an increasing sequence of opens
`Uₙ`, in the concrete form `LimOneVanishes`. -/
abbrev LimOneVanishesOn (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) {U : ℕ → Opens X}
    (hU : Monotone U) : Prop :=
  LimOneVanishes (A := fun n => P.obj (op (U n))) fun n => (P.map (homOfLE (hU n.le_succ)).op).hom

section FreeYoneda

variable {U V : Opens X}

/-- The zero morphism `ℤ[V] ⟶ B` corresponds to the zero section. -/
lemma freeYonedaHomEquiv_zero (B : AbSheaf X) : freeYonedaHomEquiv V B 0 = 0 := by
  rw [show (0 : freeYoneda V ⟶ B) = 0 ≫ (0 : B ⟶ B) by simp, freeYonedaHomEquiv_comp]
  rfl

end FreeYoneda

section Sections

/-- A short exact sequence of abelian sheaves is left exact on sections. -/
lemma exact_app_of_shortExact {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact) (V : Opens X) :
    Function.Exact (S.f.hom.app (op V)) (S.g.hom.app (op V)) := by
  intro y
  constructor
  · intro hy
    let α := (freeYonedaHomEquiv V S.X₂).symm y
    have hα : α ≫ S.g = 0 := (freeYonedaHomEquiv V S.X₃).injective (by
      rw [freeYonedaHomEquiv_comp, Equiv.apply_symm_apply, hy, freeYonedaHomEquiv_zero])
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₂ _ hS (Ext.mk₀ α)
      (by rw [Ext.mk₀_comp_mk₀, hα, Ext.mk₀_zero])
    obtain ⟨β, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
    rw [Ext.mk₀_comp_mk₀] at hx
    refine ⟨freeYonedaHomEquiv V S.X₁ β, ?_⟩
    rw [← freeYonedaHomEquiv_comp, (Ext.mk₀_bijective _ _).1 hx, Equiv.apply_symm_apply]
  · rintro ⟨x, rfl⟩
    change ((S.f ≫ S.g).hom.app (op V)) x = 0
    rw [S.zero]
    rfl

/-- Sections over the union of an increasing sequence of opens are determined by their
restrictions to the members. -/
lemma eq_of_monotone (G : AbSheaf X) {U : ℕ → Opens X} (s t : G.obj.obj (op (⨆ n, U n)))
    (h : ∀ n, G.obj.map (homOfLE (le_iSup U n)).op s = G.obj.map (homOfLE (le_iSup U n)).op t) :
    s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (F := (G : X.Sheaf AddCommGrpCat.{u})) (fun n => U n)
    (⨆ n, U n) (fun n => homOfLE (le_iSup U n)) le_rfl s t h

variable (G : AbSheaf X) {U : ℕ → Opens X} (hU : Monotone U)
include hU

/-- Sections over the members of an increasing sequence of opens which are compatible under
restriction glue to a section over the union. -/
lemma exists_gluing_of_monotone (a : ∀ n, G.obj.obj (op (U n)))
    (ha : ∀ n, G.obj.map (homOfLE (hU n.le_succ)).op (a (n + 1)) = a n) :
    ∃ s : G.obj.obj (op (⨆ n, U n)), ∀ n, G.obj.map (homOfLE (le_iSup U n)).op s = a n := by
  have hmn : ∀ m n (h : m ≤ n), G.obj.map (homOfLE (hU h)).op (a n) = a m := by
    intro m n h
    induction n, h using Nat.le_induction with
    | base => exact (congr_arg (fun f => G.obj.map f (a m)) (rfl : (homOfLE (hU le_rfl)).op =
        𝟙 _)).trans (by simp)
    | succ n hmn ih =>
      rw [← ih, ← ha n, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := (G : X.Sheaf AddCommGrpCat.{u}))
    (fun n => U n) (⨆ n, U n) (fun n => homOfLE (le_iSup U n)) le_rfl a (by
      intro i j
      rcases le_total i j with h | h
      · rw [← hmn i j h, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl
      · rw [← hmn j i h, ← ConcreteCategory.comp_apply (G.obj.map _), ← Functor.map_comp]
        rfl)
  exact ⟨s, hs⟩

end Sections

section DegreeOne

variable (F : AbSheaf X) {U : ℕ → Opens X} (hU : Monotone U)

/-- **Degree one.** Let `W = ⋃ₙ Uₙ` be an increasing union of opens such that `lim¹ₙ F(Uₙ) = 0`.
A class in `H¹(W, F) = Ext¹(ℤ[W], F)` which restricts to zero on every `Uₙ` vanishes. -/
theorem ext_one_eq_zero_of_monotone
    (hlim : LimOneVanishesOn F.obj hU)
    (c : Ext (freeYoneda (⨆ n, U n)) F 1)
    (hc : ∀ n, (Ext.mk₀ (freeYonedaMap (le_iSup U n))).comp c (zero_add 1) = 0) : c = 0 := by
  obtain ⟨S, hS, hI, rfl⟩ : ∃ S : ShortComplex (AbSheaf X),
      S.ShortExact ∧ Injective S.X₂ ∧ S.X₁ = F :=
    ⟨injSES F, injSES_shortExact F, inferInstance, rfl⟩
  obtain ⟨z, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS c (Ext.eq_zero_of_injective _)
    (zero_add 1)
  obtain ⟨σ, rfl⟩ := (Ext.mk₀_bijective _ _).2 z
  have hlift : ∀ n, ∃ α : freeYoneda (U n) ⟶ S.X₂,
      α ≫ S.g = freeYonedaMap (le_iSup U n) ≫ σ := by
    intro n
    have h := hc n
    rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀] at h
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ _ hS _ (zero_add 1) h
    obtain ⟨α, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
    exact ⟨α, (Ext.mk₀_bijective _ _).1 (by rw [← Ext.mk₀_comp_mk₀]; exact hx)⟩
  choose α hα using hlift
  let a : ∀ n, S.X₂.obj.obj (op (U n)) := fun n => freeYonedaHomEquiv (U n) S.X₂ (α n)
  have ha : ∀ n, S.g.hom.app _ (a n) =
      S.X₃.obj.map (homOfLE (le_iSup U n)).op (freeYonedaHomEquiv _ S.X₃ σ) := by
    intro n
    rw [← freeYonedaHomEquiv_comp, hα, freeYonedaHomEquiv_freeYonedaMap_comp]
  have hd : ∀ n, ∃ e : S.X₁.obj.obj (op (U n)), S.f.hom.app _ e =
      S.X₂.obj.map (homOfLE (hU n.le_succ)).op (a (n + 1)) - a n := by
    intro n
    apply (exact_app_of_shortExact hS (U n) _).1
    rw [map_sub, NatTrans.naturality_apply, ha, ha, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp]
    exact sub_self _
  choose e he using hd
  obtain ⟨b, hb⟩ := hlim e
  dsimp only at hb
  let a' : ∀ n, S.X₂.obj.obj (op (U n)) := fun n => a n + S.f.hom.app _ (b n)
  have ha' : ∀ n, S.X₂.obj.map (homOfLE (hU n.le_succ)).op (a' (n + 1)) = a' n := by
    intro n
    have h := he n
    rw [hb n, map_sub] at h
    simp only [a', map_add]
    rw [← NatTrans.naturality_apply]
    change _ + (S.f.hom.app _) (S.X₁.obj.map _ (b (n + 1))) = _
    rw [show S.X₂.obj.map (homOfLE (hU n.le_succ)).op (a (n + 1)) =
      S.f.hom.app _ (b n) - S.f.hom.app _ (S.X₁.obj.map (homOfLE (hU n.le_succ)).op (b (n + 1))) +
        a n by rw [h]; abel]
    abel
  obtain ⟨s, hs⟩ := exists_gluing_of_monotone S.X₂ hU a' ha'
  have hgs : S.g.hom.app _ s = freeYonedaHomEquiv _ S.X₃ σ := by
    refine eq_of_monotone S.X₃ _ _ fun n => ?_
    rw [← NatTrans.naturality_apply, hs]
    simp only [a', map_add, ha]
    rw [(exact_app_of_shortExact hS (U n) _).2 ⟨b n, rfl⟩, add_zero]
  have hσ : σ = (freeYonedaHomEquiv _ S.X₂).symm s ≫ S.g :=
    (freeYonedaHomEquiv _ S.X₃).injective (by
      rw [freeYonedaHomEquiv_comp, Equiv.apply_symm_apply, hgs])
  rw [hσ, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

end DegreeOne

section HigherDegrees

variable {U V : Opens X}

/-- `ℤ[V] ⟶ ℤ[U]` is a monomorphism. -/
instance mono_freeYonedaMap (h : V ≤ U) : Mono (freeYonedaMap h) := by
  unfold freeYonedaMap
  infer_instance

/-- The identification `H⁰(U, F) = Hom(ℤ[U], F) ≃ F(U)`. -/
noncomputable def extZeroFreeYonedaAddEquiv (F : AbSheaf X) (U : Opens X) :
    Ext (freeYoneda U) F 0 ≃+ F.obj.obj (op U) where
  toEquiv := (Ext.addEquiv₀ (X := freeYoneda U) (Y := F)).toEquiv.trans
    (freeYonedaHomEquiv U F)
  map_add' x y := by
    change freeYonedaHomEquiv U F (Ext.addEquiv₀ (x + y)) =
      freeYonedaHomEquiv U F (Ext.addEquiv₀ x) + freeYonedaHomEquiv U F (Ext.addEquiv₀ y)
    rw [map_add]
    generalize Ext.addEquiv₀ x = s
    generalize Ext.addEquiv₀ y = t
    rw [← Category.id_comp (s + t), ← Category.id_comp s, ← Category.id_comp t,
      freeYonedaHomEquiv_comp, freeYonedaHomEquiv_comp, freeYonedaHomEquiv_comp]
    rfl

/-- `H⁰(U, F) ≃ F(U)` on morphisms `ℤ[U] ⟶ F` is `freeYonedaHomEquiv`. -/
lemma extZeroFreeYonedaAddEquiv_mk₀ (F : AbSheaf X) (U : Opens X) (s : freeYoneda U ⟶ F) :
    extZeroFreeYonedaAddEquiv F U (Ext.mk₀ s) = freeYonedaHomEquiv U F s := by
  change freeYonedaHomEquiv U F (Ext.addEquiv₀ (Ext.mk₀ s)) = _
  rw [← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]

/-- The identification `H⁰(U, F) ≃ F(U)` commutes with restriction. -/
lemma extZeroFreeYonedaAddEquiv_comp (F : AbSheaf X) (h : V ≤ U) (c : Ext (freeYoneda U) F 0) :
    extZeroFreeYonedaAddEquiv F V ((Ext.mk₀ (freeYonedaMap h)).comp c (zero_add 0)) =
      F.obj.map (homOfLE h).op (extZeroFreeYonedaAddEquiv F U c) := by
  obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective _ _).2 c
  rw [Ext.mk₀_comp_mk₀, extZeroFreeYonedaAddEquiv_mk₀, extZeroFreeYonedaAddEquiv_mk₀]
  exact freeYonedaHomEquiv_freeYonedaMap_comp h s

variable {U : ℕ → Opens X} (hU : Monotone U)

/-- **Cohomology of an increasing union.** Let `W = ⋃ₙ Uₙ` be an increasing union of opens and
`q ≥ 0` such that `lim¹ₙ Hᵠ(Uₙ, F) = 0`. A class in `Hᵠ⁺¹(W, F) = Extᵠ⁺¹(ℤ[W], F)` which
restricts to zero on every `Uₙ` vanishes. -/
theorem ext_succ_eq_zero_of_monotone (q : ℕ) (F : AbSheaf X)
    (hlim : LimOneVanishesOn (CategoryTheory.Sheaf.cohomologyPresheaf.{u} F q) hU)
    (c : Ext (freeYoneda (⨆ n, U n)) F (q + 1))
    (hc : ∀ n, (Ext.mk₀ (freeYonedaMap (le_iSup U n))).comp c (zero_add (q + 1)) = 0) :
    c = 0 := by
  induction q generalizing F with
  | zero =>
    refine ext_one_eq_zero_of_monotone F hU ?_ c hc
    have key : ∀ n (x : Ext (freeYoneda (U (n + 1))) F 0),
        extZeroFreeYonedaAddEquiv F (U n) (H'res F 0 (hU n.le_succ) x) =
        F.obj.map (homOfLE (hU n.le_succ)).op (extZeroFreeYonedaAddEquiv F (U (n + 1)) x) :=
      fun n x => by
        exact extZeroFreeYonedaAddEquiv_comp F _ x
    exact LimOneVanishes.of_surjective_map (A := fun n => Ext (freeYoneda (U n)) F 0)
      (B := fun n => F.obj.obj (op (U n)))
      (rA := fun n => ((CategoryTheory.Sheaf.cohomologyPresheaf.{u} F 0).map
        (homOfLE (hU n.le_succ)).op).hom)
      (rB := fun n => (F.obj.map (homOfLE (hU n.le_succ)).op).hom)
      (fun n => (extZeroFreeYonedaAddEquiv F (U n)).toAddMonoidHom) key
      (fun n => (extZeroFreeYonedaAddEquiv F (U n)).surjective) hlim
  | succ q ih =>
    obtain ⟨S, hS, hI, rfl⟩ : ∃ S : ShortComplex (AbSheaf X),
        S.ShortExact ∧ Injective S.X₂ ∧ S.X₁ = F :=
      ⟨injSES F, injSES_shortExact F, inferInstance, rfl⟩
    obtain ⟨z, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS c (Ext.eq_zero_of_injective _) rfl
    have hz : ∀ n, (Ext.mk₀ (freeYonedaMap (le_iSup U n))).comp z (zero_add (q + 1)) = 0 := by
      intro n
      have h := hc n
      rw [← Ext.comp_assoc _ _ _ (zero_add _) rfl (by omega)] at h
      obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ _ hS _ rfl h
      rw [← hx, Ext.eq_zero_of_injective x, Ext.zero_comp]
    suffices hlim' : LimOneVanishesOn (CategoryTheory.Sheaf.cohomologyPresheaf.{u} S.X₃ q) hU by
      rw [ih S.X₃ hlim' z hz, Ext.zero_comp]
    refine LimOneVanishes.of_exact (A := fun n => Ext (freeYoneda (U n)) S.X₂ q)
      (C := fun n => Ext (freeYoneda (U n)) S.X₁ (q + 1))
      (rA := fun n => ((CategoryTheory.Sheaf.cohomologyPresheaf.{u} S.X₂ q).map
        (homOfLE (hU n.le_succ)).op).hom)
      (φ := fun n => (Ext.mk₀ S.g).postcomp (freeYoneda (U n)) (add_zero q))
      (ψ := fun n => hS.extClass.postcomp (freeYoneda (U n)) rfl) ?_ ?_ ?_ ?_ ?_ hlim
    · intro n x
      exact Ext.comp_assoc _ _ _ (zero_add q) (add_zero q) (by omega)
    · intro n x
      exact Ext.comp_assoc _ _ _ (zero_add q) rfl (by omega)
    · intro n
      exact (ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.covariant_sequence_exact₃' _ hS q (q + 1) rfl)
    · intro n y
      exact Ext.covariant_sequence_exact₁ _ hS y (Ext.eq_zero_of_injective _) rfl
    · refine LimOneVanishes.of_surjective fun n x => ?_
      rcases q with _ | q
      · obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
        refine ⟨Ext.mk₀ (Injective.factorThru s (freeYonedaMap (hU n.le_succ))), ?_⟩
        change (Ext.mk₀ (freeYonedaMap (hU n.le_succ))).comp _ (zero_add 0) = _
        rw [Ext.mk₀_comp_mk₀, Injective.comp_factorThru]
      · exact ⟨0, (map_zero _).trans (Ext.eq_zero_of_injective x).symm⟩

end HigherDegrees

section Statements

variable {U : ℕ → Opens X} (hU : Monotone U) (F : AbSheaf X)
include hU

/-- **Cohomology of an increasing union.** Let `W = ⋃ₙ Uₙ` with `Uₙ ≤ Uₙ₊₁` and
`lim¹ₙ H'ᵠ(Uₙ, F) = 0`. Then a class `c ∈ H'ᵠ⁺¹(W, F)` restricting to zero on every `Uₙ` is
zero. -/
theorem H'_eq_zero_of_monotone (q : ℕ)
    (hlim : LimOneVanishesOn (CategoryTheory.Sheaf.cohomologyPresheaf.{u} F q) hU)
    (c : CategoryTheory.Sheaf.H'.{u} F (q + 1) (⨆ n, U n))
    (hc : ∀ n, H'res F (q + 1) (le_iSup U n) c = 0) : c = 0 :=
  ext_succ_eq_zero_of_monotone hU q F hlim c hc

/-- **Cohomology of an increasing union, degree one.** If `lim¹ₙ F(Uₙ) = 0`, a class in
`H'¹(⋃ₙ Uₙ, F)` restricting to zero on every `Uₙ` is zero. -/
theorem H'_one_eq_zero_of_monotone (hlim : LimOneVanishesOn F.obj hU)
    (c : CategoryTheory.Sheaf.H'.{u} F 1 (⨆ n, U n))
    (hc : ∀ n, H'res F 1 (le_iSup U n) c = 0) : c = 0 :=
  ext_one_eq_zero_of_monotone F hU hlim c hc

/-- **Cohomology of an increasing union, higher degrees.** For `q ≥ 2`: if the restriction maps
`H'ᵠ⁻¹(Uₙ₊₁, F) → H'ᵠ⁻¹(Uₙ, F)` vanish, a class in `H'ᵠ(⋃ₙ Uₙ, F)` restricting to zero on every
`Uₙ` is zero. -/
theorem H'_eq_zero_of_monotone_of_res_eq_zero (q : ℕ)
    (hres : ∀ n : ℕ, H'res F (q + 1) (hU n.le_succ) = 0)
    (c : CategoryTheory.Sheaf.H'.{u} F (q + 2) (⨆ n, U n))
    (hc : ∀ n, H'res F (q + 2) (le_iSup U n) c = 0) : c = 0 :=
  H'_eq_zero_of_monotone hU F (q + 1)
    (LimOneVanishes.of_eq_zero fun n => (congrArg AddCommGrpCat.Hom.hom (hres n)).trans rfl) c hc

/-- Vanishing form: if `H'ᵠ⁺¹(Uₙ, F) = 0` for all `n` and `lim¹ₙ H'ᵠ(Uₙ, F) = 0`, then
`H'ᵠ⁺¹(⋃ₙ Uₙ, F) = 0`. -/
theorem subsingleton_H'_iSup_of_monotone (q : ℕ)
    (hq : ∀ n, Subsingleton (CategoryTheory.Sheaf.H'.{u} F (q + 1) (U n)))
    (hlim : LimOneVanishesOn (CategoryTheory.Sheaf.cohomologyPresheaf.{u} F q) hU) :
    Subsingleton (CategoryTheory.Sheaf.H'.{u} F (q + 1) (⨆ n, U n)) :=
  subsingleton_of_forall_eq 0 fun c =>
    H'_eq_zero_of_monotone hU F q hlim c fun _ => Subsingleton.elim _ _

/-- Vanishing form, degree one: if `H'¹(Uₙ, F) = 0` for all `n` and `lim¹ₙ F(Uₙ) = 0`, then
`H'¹(⋃ₙ Uₙ, F) = 0`. -/
theorem subsingleton_H'_one_iSup_of_monotone
    (hq : ∀ n, Subsingleton (CategoryTheory.Sheaf.H'.{u} F 1 (U n)))
    (hlim : LimOneVanishesOn F.obj hU) :
    Subsingleton (CategoryTheory.Sheaf.H'.{u} F 1 (⨆ n, U n)) :=
  subsingleton_of_forall_eq 0 fun c =>
    H'_one_eq_zero_of_monotone hU F hlim c fun _ => Subsingleton.elim _ _

/-- Vanishing form, higher degrees: if `H'ᵠ⁺¹(Uₙ, F) = 0` and `H'ᵠ⁺²(Uₙ, F) = 0` for all `n`,
then `H'ᵠ⁺²(⋃ₙ Uₙ, F) = 0`. -/
theorem subsingleton_H'_iSup_of_monotone_of_subsingleton (q : ℕ)
    (hq : ∀ n, Subsingleton (CategoryTheory.Sheaf.H'.{u} F (q + 1) (U n)))
    (hq' : ∀ n, Subsingleton (CategoryTheory.Sheaf.H'.{u} F (q + 2) (U n))) :
    Subsingleton (CategoryTheory.Sheaf.H'.{u} F (q + 2) (⨆ n, U n)) :=
  subsingleton_H'_iSup_of_monotone hU F (q + 1) hq' (LimOneVanishes.of_subsingleton _)

/-! ### The same statements for `Hᵠ(W, F|_W)` -/

/-- `lim¹ₙ Hᵠ(Uₙ, F|_{Uₙ}) = 0`, for the restriction maps `restrictOpenRes`, in the concrete form
`LimOneVanishes`. -/
abbrev LimOneVanishesH (q : ℕ) : Prop :=
  LimOneVanishes (A := fun n => H ((restrictOpen (U n)).obj F) q)
    fun n => restrictOpenRes F q (hU n.le_succ)

/-- `lim¹ₙ Hᵠ(Uₙ, F|_{Uₙ}) = 0` implies `lim¹ₙ H'ᵠ(Uₙ, F) = 0`. -/
lemma limOneVanishesOn_cohomologyPresheaf_of_limOneVanishesH {q : ℕ}
    (h : LimOneVanishesH hU F q) :
    LimOneVanishesOn (CategoryTheory.Sheaf.cohomologyPresheaf.{u} F q) hU :=
  LimOneVanishes.of_surjective_map (A := fun n => H ((restrictOpen (U n)).obj F) q)
    (B := fun n => CategoryTheory.Sheaf.H'.{u} F q (U n))
    (rB := fun n => (H'res F q (hU n.le_succ)).hom)
    (fun n => (H'AddEquiv (U n) F q).symm.toAddMonoidHom)
    (fun n x => (H'AddEquiv (U n) F q).injective (by
      simp only [AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
        AddEquiv.apply_symm_apply]
      exact (restrictOpenRes_apply _ _).trans rfl))
    (fun n => (H'AddEquiv (U n) F q).symm.surjective) h

/-- **Cohomology of an increasing union.** Let `W = ⋃ₙ Uₙ` with `Uₙ ≤ Uₙ₊₁` and
`lim¹ₙ Hᵠ(Uₙ, F|_{Uₙ}) = 0`. Then a class `c ∈ Hᵠ⁺¹(W, F|_W)` restricting to zero on every
`Uₙ` is zero. -/
theorem H_restrictOpen_eq_zero_of_monotone (q : ℕ) (hlim : LimOneVanishesH hU F q)
    (c : H ((restrictOpen (⨆ n, U n)).obj F) (q + 1))
    (hc : ∀ n, restrictOpenRes F (q + 1) (le_iSup U n) c = 0) : c = 0 := by
  have := H'_eq_zero_of_monotone hU F q
    (limOneVanishesOn_cohomologyPresheaf_of_limOneVanishesH hU F hlim)
    ((H'AddEquiv _ F (q + 1)).symm c) fun n => (H'AddEquiv (U n) F (q + 1)).injective (by
      rw [map_zero, ← restrictOpenRes_H'AddEquiv, AddEquiv.apply_symm_apply, hc])
  simpa using this

/-- **Cohomology of an increasing union, degree one.** If `lim¹ₙ F(Uₙ) = 0`, a class in
`H¹(W, F|_W)`, `W = ⋃ₙ Uₙ`, restricting to zero on every `Uₙ` is zero. -/
theorem H_one_restrictOpen_eq_zero_of_monotone (hlim : LimOneVanishesOn F.obj hU)
    (c : H ((restrictOpen (⨆ n, U n)).obj F) 1)
    (hc : ∀ n, restrictOpenRes F 1 (le_iSup U n) c = 0) : c = 0 := by
  have := H'_one_eq_zero_of_monotone hU F hlim
    ((H'AddEquiv _ F 1).symm c) fun n => (H'AddEquiv (U n) F 1).injective (by
      rw [map_zero, ← restrictOpenRes_H'AddEquiv, AddEquiv.apply_symm_apply, hc])
  simpa using this

/-- **Cohomology of an increasing union, higher degrees.** For `q ≥ 2`: if the restriction maps
`Hᵠ⁻¹(Uₙ₊₁, F|_{Uₙ₊₁}) → Hᵠ⁻¹(Uₙ, F|_{Uₙ})` vanish, a class in `Hᵠ(W, F|_W)`, `W = ⋃ₙ Uₙ`,
restricting to zero on every `Uₙ` is zero. -/
theorem H_restrictOpen_eq_zero_of_monotone_of_res_eq_zero (q : ℕ)
    (hres : ∀ n : ℕ, restrictOpenRes F (q + 1) (hU n.le_succ) = 0)
    (c : H ((restrictOpen (⨆ n, U n)).obj F) (q + 2))
    (hc : ∀ n, restrictOpenRes F (q + 2) (le_iSup U n) c = 0) : c = 0 :=
  H_restrictOpen_eq_zero_of_monotone hU F (q + 1) (LimOneVanishes.of_eq_zero hres) c hc

/-- Vanishing form: if `Hᵠ⁺¹(Uₙ, F|_{Uₙ}) = 0` for all `n` and `lim¹ₙ Hᵠ(Uₙ, F|_{Uₙ}) = 0`, then
`Hᵠ⁺¹(W, F|_W) = 0` for `W = ⋃ₙ Uₙ`. -/
theorem subsingleton_H_restrictOpen_iSup_of_monotone (q : ℕ)
    (hq : ∀ n, Subsingleton (H ((restrictOpen (U n)).obj F) (q + 1)))
    (hlim : LimOneVanishesH hU F q) :
    Subsingleton (H ((restrictOpen (⨆ n, U n)).obj F) (q + 1)) :=
  subsingleton_of_forall_eq 0 fun c =>
    H_restrictOpen_eq_zero_of_monotone hU F q hlim c fun _ => Subsingleton.elim _ _

/-- Vanishing form, degree one: if `H¹(Uₙ, F|_{Uₙ}) = 0` for all `n` and `lim¹ₙ F(Uₙ) = 0`, then
`H¹(W, F|_W) = 0` for `W = ⋃ₙ Uₙ`. -/
theorem subsingleton_H_one_restrictOpen_iSup_of_monotone
    (hq : ∀ n, Subsingleton (H ((restrictOpen (U n)).obj F) 1))
    (hlim : LimOneVanishesOn F.obj hU) :
    Subsingleton (H ((restrictOpen (⨆ n, U n)).obj F) 1) :=
  subsingleton_of_forall_eq 0 fun c =>
    H_one_restrictOpen_eq_zero_of_monotone hU F hlim c fun _ => Subsingleton.elim _ _

/-- Vanishing form, higher degrees: if `Hᵠ⁺¹` and `Hᵠ⁺²` of `F|_{Uₙ}` vanish for all `n`, then
`Hᵠ⁺²(W, F|_W) = 0` for `W = ⋃ₙ Uₙ`. -/
theorem subsingleton_H_restrictOpen_iSup_of_monotone_of_subsingleton (q : ℕ)
    (hq : ∀ n, Subsingleton (H ((restrictOpen (U n)).obj F) (q + 1)))
    (hq' : ∀ n, Subsingleton (H ((restrictOpen (U n)).obj F) (q + 2))) :
    Subsingleton (H ((restrictOpen (⨆ n, U n)).obj F) (q + 2)) :=
  subsingleton_H_restrictOpen_iSup_of_monotone hU F (q + 1) hq'
    (LimOneVanishes.of_subsingleton _)

/-- Global version: if the increasing sequence `Uₙ` exhausts `X`, `Hᵠ⁺¹(Uₙ, F|_{Uₙ}) = 0` for all
`n` and `lim¹ₙ Hᵠ(Uₙ, F|_{Uₙ}) = 0`, then `Hᵠ⁺¹(X, F) = 0`. -/
theorem subsingleton_H_of_monotone (hW : ⨆ n, U n = ⊤) (q : ℕ)
    (hq : ∀ n, Subsingleton (H ((restrictOpen (U n)).obj F) (q + 1)))
    (hlim : LimOneVanishesH hU F q) :
    Subsingleton (H F (q + 1)) := by
  have := subsingleton_H'_iSup_of_monotone hU F q
    (fun n => (H'AddEquiv (U n) F (q + 1)).subsingleton_congr.2 (hq n))
    (limOneVanishesOn_cohomologyPresheaf_of_limOneVanishesH hU F hlim)
  rw [hW] at this
  exact (H'TopAddEquiv F (q + 1)).subsingleton_congr.1 this

/-- Global version in degree one: if the increasing sequence `Uₙ` exhausts `X`,
`H¹(Uₙ, F|_{Uₙ}) = 0` for all `n` and `lim¹ₙ F(Uₙ) = 0`, then `H¹(X, F) = 0`. -/
theorem subsingleton_H_one_of_monotone (hW : ⨆ n, U n = ⊤)
    (hq : ∀ n, Subsingleton (H ((restrictOpen (U n)).obj F) 1))
    (hlim : LimOneVanishesOn F.obj hU) :
    Subsingleton (H F 1) := by
  have := subsingleton_H'_one_iSup_of_monotone hU F
    (fun n => (H'AddEquiv (U n) F 1).subsingleton_congr.2 (hq n)) hlim
  rw [hW] at this
  exact (H'TopAddEquiv F 1).subsingleton_congr.1 this

/-- Global version in higher degrees: if the increasing sequence `Uₙ` exhausts `X` and `Hᵠ⁺¹`,
`Hᵠ⁺²` of `F|_{Uₙ}` vanish for all `n`, then `Hᵠ⁺²(X, F) = 0`. -/
theorem subsingleton_H_of_monotone_of_subsingleton (hW : ⨆ n, U n = ⊤) (q : ℕ)
    (hq : ∀ n, Subsingleton (H ((restrictOpen (U n)).obj F) (q + 1)))
    (hq' : ∀ n, Subsingleton (H ((restrictOpen (U n)).obj F) (q + 2))) :
    Subsingleton (H F (q + 2)) :=
  subsingleton_H_of_monotone hU F hW (q + 1) hq' (LimOneVanishes.of_subsingleton _)

end Statements

end TopCat.Sheaf

end
