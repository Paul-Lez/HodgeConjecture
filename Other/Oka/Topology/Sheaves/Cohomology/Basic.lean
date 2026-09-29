/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Cohomology of abelian sheaves on a topological space

For `X : TopCat.{u}` and `F : X.AbSheaf` (definitionally `X.Sheaf AddCommGrpCat.{u}`) we write
`TopCat.Sheaf.H F n` for the sheaf cohomology `Hⁿ(X, F)`, i.e. Mathlib's
`CategoryTheory.Sheaf.H F n`, the `Ext`-group `Extⁿ(ℤ_X, F)` in the Grothendieck abelian category
of abelian sheaves on `X`.

All statements are phrased in `X.AbSheaf = Sheaf (Opens.grothendieckTopology X) AddCommGrpCat`
(an `abbrev`), so that instance search finds Mathlib's instances for sheaves on a site; objects
and morphisms of `X.Sheaf AddCommGrpCat` can be used directly.

## Main definitions and results

* `TopCat.Sheaf.H F n`: the cohomology group `Hⁿ(X, F) : Type u`.
* `TopCat.Sheaf.H.equiv₀ F : H F 0 ≃+ F.obj.obj (op ⊤)`: degree zero is global sections.
* `TopCat.Sheaf.H.map φ n : H F n →+ H G n`: functoriality.
* `TopCat.Sheaf.H.δ hS n₀ n₁ h : H S.X₃ n₀ →+ H S.X₁ n₁`: the connecting homomorphism of a short
  exact sequence `S` of sheaves, with exactness `TopCat.Sheaf.H.exact₁`, `TopCat.Sheaf.H.exact₂`,
  `TopCat.Sheaf.H.exact₃` and the long exact sequence `TopCat.Sheaf.H.sequence`,
  `TopCat.Sheaf.H.sequence_exact`.
* `TopCat.Sheaf.H.eq_zero_of_injective`: `Hⁿ⁺¹(X, I) = 0` for an injective sheaf `I`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace TopCat

variable {X : TopCat.{u}}

variable (X) in
/-- The category of abelian sheaves on `X`, written as sheaves on the site of opens. It is
definitionally `X.Sheaf AddCommGrpCat.{u}`; functors between such categories are best typed with
`AbSheaf`, so that instance search sees Mathlib's instances for sheaves on a site. -/
abbrev AbSheaf : Type (u + 1) :=
  CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}

namespace Sheaf

variable (X) in
/-- The constant sheaf `ℤ_X` (with values `ULift ℤ`), the source of the `Ext`-groups defining
sheaf cohomology. -/
noncomputable abbrev constZ : AbSheaf X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))

/-- The sheaf cohomology `Hⁿ(X, F)` of an abelian sheaf `F` on a topological space `X`. -/
abbrev H (F : AbSheaf X) (n : ℕ) : Type u :=
  CategoryTheory.Sheaf.H.{u} (J := Opens.grothendieckTopology X) F n

namespace H

variable (F : AbSheaf X)

/-- Degree zero cohomology is the group of global sections. -/
noncomputable def equiv₀ : H F 0 ≃+ F.obj.obj (op ⊤) :=
  CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop

variable {F} {G K : AbSheaf X} (φ : F ⟶ G)

/-- The map `Hⁿ(X, F) → Hⁿ(X, G)` induced by a morphism of sheaves. -/
noncomputable def map (n : ℕ) : H F n →+ H G n :=
  CategoryTheory.Sheaf.H.map φ n

lemma map_apply {n : ℕ} (x : H F n) : map φ n x = x.comp (Ext.mk₀ φ) (add_zero n) := rfl

@[simp]
lemma map_id_apply {n : ℕ} (x : H F n) : map (𝟙 F) n x = x :=
  CategoryTheory.Sheaf.H.map_id_apply x

lemma map_comp_apply {n : ℕ} (ψ : G ⟶ K) (x : H F n) :
    map (φ ≫ ψ) n x = map ψ n (map φ n x) :=
  CategoryTheory.Sheaf.H.map_comp_apply φ ψ x

@[simp]
lemma map_add_apply {n : ℕ} (φ φ' : F ⟶ G) (x : H F n) :
    map (φ + φ') n x = map φ n x + map φ' n x :=
  CategoryTheory.Sheaf.H.map_add_apply φ φ' x

@[simp]
lemma map_zero_apply {n : ℕ} (x : H F n) : map (0 : F ⟶ G) n x = 0 := by
  have h := map_add_apply (0 : F ⟶ G) 0 x
  rw [add_zero] at h
  exact left_eq_add.1 h

/-- The identification of `H⁰` with global sections is natural. -/
lemma equiv₀_map (x : H F 0) :
    equiv₀ G (map φ 0 x) = φ.hom.app (op ⊤) (equiv₀ F x) :=
  (CategoryTheory.Sheaf.H.equiv₀_naturality (hT := isTerminalTop) (f := φ) x).symm

lemma map_equiv₀_symm (s : F.obj.obj (op ⊤)) :
    map φ 0 ((equiv₀ F).symm s) = (equiv₀ G).symm (φ.hom.app (op ⊤) s) :=
  CategoryTheory.Sheaf.H.equiv₀_symm_naturality (hT := isTerminalTop) (f := φ) s

section LongExactSequence

variable {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)

/-- The connecting homomorphism `Hⁿ⁰(X, S.X₃) → Hⁿ¹(X, S.X₁)` (with `n₁ = n₀ + 1`) of a short
exact sequence of abelian sheaves. -/
noncomputable def δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : H S.X₃ n₀ →+ H S.X₁ n₁ :=
  hS.extClass.postcomp _ h

lemma δ_apply {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : H S.X₃ n₀) :
    δ hS n₀ n₁ h x = x.comp hS.extClass h := rfl

include hS in
/-- Exactness of `Hⁿ(S.X₁) → Hⁿ(S.X₂) → Hⁿ(S.X₃)`. -/
lemma exact₂ (n : ℕ) : Function.Exact (map S.f n) (map S.g n) :=
  (ShortComplex.ab_exact_iff_function_exact _).1 (Ext.covariant_sequence_exact₂' (constZ X) hS n)

/-- Exactness of `Hⁿ⁰(S.X₂) → Hⁿ⁰(S.X₃) → Hⁿ¹(S.X₁)`. -/
lemma exact₃ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : Function.Exact (map S.g n₀) (δ hS n₀ n₁ h) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.covariant_sequence_exact₃' (constZ X) hS n₀ n₁ h)

/-- Exactness of `Hⁿ⁰(S.X₃) → Hⁿ¹(S.X₁) → Hⁿ¹(S.X₂)`. -/
lemma exact₁ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : Function.Exact (δ hS n₀ n₁ h) (map S.f n₁) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.covariant_sequence_exact₁' (constZ X) hS n₀ n₁ h)

@[simp]
lemma map_g_map_f {n : ℕ} (x : H S.X₁ n) : map S.g n (map S.f n x) = 0 := by
  rw [← map_comp_apply, S.zero, map_zero_apply]

@[simp]
lemma δ_map_g {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : H S.X₂ n₀) : δ hS n₀ n₁ h (map S.g n₀ x) = 0 :=
  (exact₃ hS n₀ n₁ h).apply_apply_eq_zero x

@[simp]
lemma map_f_δ {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁) (x : H S.X₃ n₀) : map S.f n₁ (δ hS n₀ n₁ h x) = 0 :=
  (exact₁ hS n₀ n₁ h).apply_apply_eq_zero x

include hS in
/-- `H⁰(S.X₁) → H⁰(S.X₂)` is injective. -/
lemma map_f_injective_zero : Function.Injective (map S.f 0) := by
  have := hS.mono_f
  exact Ext.postcomp_mk₀_injective_of_mono (constZ X) S.f

/-- The long exact sequence
`Hⁿ⁰(S.X₁) → Hⁿ⁰(S.X₂) → Hⁿ⁰(S.X₃) → Hⁿ¹(S.X₁) → Hⁿ¹(S.X₂) → Hⁿ¹(S.X₃)`. -/
noncomputable abbrev sequence (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  Ext.covariantSequence (constZ X) hS n₀ n₁ h

lemma sequence_exact (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) : (sequence hS n₀ n₁ h).Exact :=
  Ext.covariantSequence_exact (constZ X) hS n₀ n₁ h

end LongExactSequence

section Injective

/-- Higher cohomology of an injective sheaf vanishes. -/
lemma eq_zero_of_injective (I : AbSheaf X) [hI : Injective I] {n : ℕ}
    (x : H I (n + 1)) : x = 0 :=
  have : Injective (C := CategoryTheory.Sheaf (Opens.grothendieckTopology X) _) I := hI
  Ext.eq_zero_of_injective x

instance (I : AbSheaf X) [Injective I] (n : ℕ) : Subsingleton (H I (n + 1)) :=
  subsingleton_of_forall_eq 0 (eq_zero_of_injective I)

end Injective

/-- Isomorphic sheaves have isomorphic cohomology. -/
noncomputable def addEquivOfIso {F G : AbSheaf X} (e : F ≅ G) (n : ℕ) :
    H F n ≃+ H G n where
  toFun := map e.hom n
  invFun := map e.inv n
  left_inv x := by rw [← map_comp_apply, e.hom_inv_id, map_id_apply]
  right_inv x := by rw [← map_comp_apply, e.inv_hom_id, map_id_apply]
  map_add' := map_add _

end H

end Sheaf

end TopCat

end
