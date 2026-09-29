/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Topology.Sheaves.Cohomology.MayerVietoris

/-!
# The Mayer–Vietoris sequence of two opens and its naturality

Let `F` be an abelian sheaf on `X : TopCat`. We use Mathlib's cohomology of opens
`H'ᵠ(U) = CategoryTheory.Sheaf.H' F q U = Extᵠ(ℤ[U], F)`, which is contravariant in `U` via the
maps `ℤ[V] ⟶ ℤ[U]` for `V ≤ U`, and put the Mayer–Vietoris sequence of `A, B : Opens X`
```
H'ᵠ(A ⊔ B) → H'ᵠ(A) × H'ᵠ(B) → H'ᵠ(A ⊓ B) --δ--> H'ᵠ⁺¹(A ⊔ B)
```
in elementwise form, with maps `x ↦ (x|_A, x|_B)` and `(a, b) ↦ a|_{A⊓B} - b|_{A⊓B}`.

## Main definitions and results

* `TopCat.Sheaf.MayerVietoris.res F q h : H'ᵠ(U) →+ H'ᵠ(V)` for `h : V ≤ U`, with `res_apply`
  (precomposition with `incl h : ℤ[V] ⟶ ℤ[U]`), `res_id`, `res_comp`.
* `TopCat.Sheaf.MayerVietoris.toProd`, `fromProd`, `δ` and the exactness statements
  `exact_toProd_fromProd`, `exact_fromProd_δ`, `exact_δ_toProd` (`Function.Exact`).
* Naturality for `A' ≤ A`, `B' ≤ B`: `toProd_naturality`, `fromProd_naturality` and
  `δ_naturality : δ_{A',B'} (x|_{A'⊓B'}) = (δ_{A,B} x)|_{A'⊔B'}`, deduced from the naturality
  of the connecting class for the morphism of short exact sequences
  `0 → ℤ[A'⊓B'] → ℤ[A'] ⊞ ℤ[B'] → ℤ[A'⊔B'] → 0` to the one for `(A, B)` (`shortComplexMap`).
* Degree zero: `zeroAddEquiv F U : H'⁰(U) ≃+ F(U)`, compatible with restriction
  (`zeroAddEquiv_res`, `res_zeroAddEquiv_symm`), and `δ_zeroAddEquiv_symm_sub`:
  `δ(a|_{A⊓B} - b|_{A⊓B}) = 0` for sections `a ∈ F(A)`, `b ∈ F(B)`, with the converse
  `exists_sub_of_δ_zeroAddEquiv_symm_eq_zero`.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace TopCat.Sheaf.MayerVietoris

variable {X : TopCat.{u}}

section Restriction

variable {U V W : Opens X}

/-- The map `ℤ[V] ⟶ ℤ[U]` of free abelian sheaves induced by an inclusion `V ≤ U`. -/
noncomputable def incl (h : V ≤ U) : freeYoneda V ⟶ freeYoneda U :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (Functor.whiskerRight (yoneda.map (homOfLE h)) AddCommGrpCat.free)

/-- The maps `ℤ[V] ⟶ ℤ[U]` compose. -/
@[reassoc (attr := simp)]
lemma incl_comp (hWV : W ≤ V) (hVU : V ≤ U) : incl hWV ≫ incl hVU = incl (hWV.trans hVU) := by
  simp only [incl, ← Functor.map_comp, ← Functor.whiskerRight_comp]
  rfl

/-- `ℤ[U] ⟶ ℤ[U]` induced by `U ≤ U` is the identity. -/
@[simp]
lemma incl_self : incl (le_refl U) = 𝟙 _ := by
  simp [incl]

variable (F : AbSheaf X) (q : ℕ)

/-- The restriction map `H'ᵠ(U) → H'ᵠ(V)` for `V ≤ U`. -/
noncomputable def res (h : V ≤ U) :
    CategoryTheory.Sheaf.H'.{u} F q U →+ CategoryTheory.Sheaf.H'.{u} F q V :=
  ((F.cohomologyPresheaf q).map (homOfLE h).op).hom

variable {F q}

/-- Restriction is precomposition with `ℤ[V] ⟶ ℤ[U]`. -/
lemma res_apply (h : V ≤ U) (x : CategoryTheory.Sheaf.H'.{u} F q U) :
    res F q h x = (Ext.mk₀ (incl h)).comp (x : Ext (freeYoneda U) F q) (zero_add q) :=
  rfl

/-- Restriction from `U` to `U` is the identity. -/
@[simp]
lemma res_id (x : CategoryTheory.Sheaf.H'.{u} F q U) : res F q (le_refl U) x = x := by
  rw [res_apply, incl_self, Ext.mk₀_id_comp]

/-- Restriction maps compose. -/
@[simp]
lemma res_comp (hVU : V ≤ U) (hWV : W ≤ V) (x : CategoryTheory.Sheaf.H'.{u} F q U) :
    res F q hWV (res F q hVU x) = res F q (hWV.trans hVU) x := by
  rw [res_apply, res_apply, res_apply, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    incl_comp]

end Restriction

section Zero

variable {U V : Opens X}

/-- Under `(ℤ[U] ⟶ B) ≃ B(U)`, precomposition with `ℤ[V] ⟶ ℤ[U]` is restriction of sections. -/
lemma freeYonedaHomEquiv_incl_comp (h : V ≤ U) {B : AbSheaf X} (s : freeYoneda U ⟶ B) :
    freeYonedaHomEquiv V B (incl h ≫ s) =
      B.obj.map (homOfLE h).op (freeYonedaHomEquiv U B s) := by
  simp only [freeYonedaHomEquiv, incl, Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_left]
  erw [Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ _).symm

/-- `(ℤ[U] ⟶ B) ≃ B(U)` is evaluation at the canonical section of `ℤ[U]` over `U`. -/
lemma freeYonedaHomEquiv_eq_app {B : AbSheaf X} (s : freeYoneda U ⟶ B) :
    freeYonedaHomEquiv U B s = s.hom.app (op U) (freeYonedaHomEquiv U _ (𝟙 _)) := by
  rw [← freeYonedaHomEquiv_comp, Category.id_comp]

end Zero

section Zero

/-- Degree zero cohomology of an open is the group of sections: `H'⁰(U) ≃+ F(U)`. -/
noncomputable def zeroAddEquiv (F : AbSheaf X) (U : Opens X) :
    CategoryTheory.Sheaf.H'.{u} F 0 U ≃+ F.obj.obj (op U) :=
  (Ext.addEquiv₀ (X := freeYoneda U) (Y := F)).trans
    { toEquiv := freeYonedaHomEquiv U F
      map_add' := fun x y => by
        simp only [Equiv.toFun_as_coe]
        rw [freeYonedaHomEquiv_eq_app (x + y), freeYonedaHomEquiv_eq_app x,
          freeYonedaHomEquiv_eq_app y, Sheaf.Hom.add_app]
        rfl }

variable {U V : Opens X} {F : AbSheaf X}

lemma zeroAddEquiv_apply (x : CategoryTheory.Sheaf.H'.{u} F 0 U) :
    zeroAddEquiv F U x = freeYonedaHomEquiv U F (Ext.addEquiv₀ x) := rfl

/-- In degree zero, restriction of cohomology classes is restriction of sections. -/
lemma zeroAddEquiv_res (h : V ≤ U) (x : CategoryTheory.Sheaf.H'.{u} F 0 U) :
    zeroAddEquiv F V (res F 0 h x) = F.obj.map (homOfLE h).op (zeroAddEquiv F U x) := by
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective (freeYoneda U) F).2 x
  rw [res_apply, Ext.mk₀_comp_mk₀, zeroAddEquiv_apply, zeroAddEquiv_apply]
  erw [Ext.addEquiv₀.apply_symm_apply, Ext.addEquiv₀.apply_symm_apply]
  exact freeYonedaHomEquiv_incl_comp h f

/-- In degree zero, restriction of sections is restriction of cohomology classes. -/
lemma res_zeroAddEquiv_symm (h : V ≤ U) (s : F.obj.obj (op U)) :
    res F 0 h ((zeroAddEquiv F U).symm s) =
      (zeroAddEquiv F V).symm (F.obj.map (homOfLE h).op s) := by
  apply (zeroAddEquiv F V).injective
  rw [zeroAddEquiv_res, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

end Zero

section Sequence

variable (A B : Opens X) (F : AbSheaf X) (q : ℕ)

/-- The first map of the Mayer–Vietoris sequence, `x ↦ (x|_A, x|_B)`. -/
noncomputable def toProd : CategoryTheory.Sheaf.H'.{u} F q (A ⊔ B) →+
    CategoryTheory.Sheaf.H'.{u} F q A × CategoryTheory.Sheaf.H'.{u} F q B :=
  (res F q le_sup_left).prod (res F q le_sup_right)

/-- The second map of the Mayer–Vietoris sequence, `(a, b) ↦ a|_{A⊓B} - b|_{A⊓B}`. -/
noncomputable def fromProd :
    CategoryTheory.Sheaf.H'.{u} F q A × CategoryTheory.Sheaf.H'.{u} F q B →+
      CategoryTheory.Sheaf.H'.{u} F q (A ⊓ B) :=
  (res F q inf_le_left).coprod (-res F q inf_le_right)

/-- The connecting map `H'ᵠ(A ⊓ B) → H'ᵠ⁺¹(A ⊔ B)` of the Mayer–Vietoris sequence. -/
noncomputable def δ :
    CategoryTheory.Sheaf.H'.{u} F q (A ⊓ B) →+ CategoryTheory.Sheaf.H'.{u} F (q + 1) (A ⊔ B) :=
  ((Opens.mayerVietorisSquare A B).δ F q (q + 1) rfl).hom

variable {A B F q}

@[simp]
lemma toProd_apply (x : CategoryTheory.Sheaf.H'.{u} F q (A ⊔ B)) :
    toProd A B F q x = (res F q le_sup_left x, res F q le_sup_right x) := rfl

@[simp]
lemma fromProd_apply
    (p : CategoryTheory.Sheaf.H'.{u} F q A × CategoryTheory.Sheaf.H'.{u} F q B) :
    fromProd A B F q p = res F q inf_le_left p.1 - res F q inf_le_right p.2 := by
  simp [fromProd, sub_eq_add_neg]

/-- The connecting map is Yoneda product with the class of
`0 → ℤ[A ⊓ B] → ℤ[A] ⊞ ℤ[B] → ℤ[A ⊔ B] → 0`. -/
lemma δ_apply (x : CategoryTheory.Sheaf.H'.{u} F q (A ⊓ B)) :
    δ A B F q x = (Opens.mayerVietorisSquare A B).shortComplex_shortExact.extClass.comp
      (x : Ext (freeYoneda (A ⊓ B)) F q) (add_comm 1 q) := rfl

private lemma toBiprod_eq (x : CategoryTheory.Sheaf.H'.{u} F q (A ⊔ B)) :
    (Opens.mayerVietorisSquare A B).toBiprod F q x =
      (AddCommGrpCat.biprodIsoProd _ _).inv (toProd A B F q x) :=
  (Opens.mayerVietorisSquare A B).toBiprod_apply F x

private lemma fromBiprod_eq
    (p : CategoryTheory.Sheaf.H'.{u} F q A × CategoryTheory.Sheaf.H'.{u} F q B) :
    (Opens.mayerVietorisSquare A B).fromBiprod F q ((AddCommGrpCat.biprodIsoProd _ _).inv p) =
      fromProd A B F q p := by
  rw [fromProd_apply]
  exact (Opens.mayerVietorisSquare A B).fromBiprod_biprodIsoProd_inv_apply F p.1 p.2

variable (A B F q)

private lemma seq_exact (i : ℕ) (hi : i + 2 ≤ 5 := by omega) :
    Function.Exact ((mayerVietorisSequence A B F q (q + 1) rfl).map' i (i + 1)).hom
      ((mayerVietorisSequence A B F q (q + 1) rfl).map' (i + 1) (i + 2)).hom :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    ((mayerVietorisSequence_exact A B F q (q + 1) rfl).exact i)

private lemma exact_equiv {M N N' P : Type*} [Zero P] {f : M → N} {g : N → P} (e : N ≃ N')
    (h : Function.Exact f g) : Function.Exact (e ∘ f) (g ∘ e.symm) := by
  intro y
  refine (h (e.symm y)).trans ⟨fun ⟨x, hx⟩ => ⟨x, ?_⟩, fun ⟨x, hx⟩ => ⟨x, ?_⟩⟩
  · simp [Function.comp_apply, hx]
  · rw [← hx, Function.comp_apply, Equiv.symm_apply_apply]

private lemma exact_comp_equiv {M M' N P : Type*} [Zero P] {f : M → N} {g : N → P} (e : M' ≃ M)
    (h : Function.Exact f g) : Function.Exact (f ∘ e) g := by
  intro y
  rw [h y, EquivLike.range_comp]

private lemma exact_equiv_comp {M N P P' : Type*} [Zero P] [Zero P'] {f : M → N} {g : N → P}
    (e : P ≃ P') (he : e 0 = 0) (h : Function.Exact f g) : Function.Exact f (e ∘ g) := by
  intro y
  rw [← h y, Function.comp_apply, ← he, e.injective.eq_iff]

/-- The additive equivalence `H'ᵠ(A) ⊞ H'ᵠ(B) ≃+ H'ᵠ(A) × H'ᵠ(B)`. -/
private noncomputable abbrev biprodEquiv (A B : Opens X) (F : AbSheaf X) (q : ℕ) :=
  (AddCommGrpCat.biprodIsoProd (CategoryTheory.Sheaf.H'.{u} F q A)
    (CategoryTheory.Sheaf.H'.{u} F q B)).addCommGroupIsoToAddEquiv

private lemma toProd_eq_comp :
    ⇑(toProd A B F q) =
      biprodEquiv A B F q ∘ ((Opens.mayerVietorisSquare A B).toBiprod F q).hom := by
  funext x
  rw [Function.comp_apply, Iso.addCommGroupIsoToAddEquiv_apply, toBiprod_eq]
  exact (Iso.inv_hom_id_apply (AddCommGrpCat.biprodIsoProd _ _) _).symm

private lemma fromProd_eq_comp :
    ⇑(fromProd A B F q) =
      ((Opens.mayerVietorisSquare A B).fromBiprod F q).hom ∘ (biprodEquiv A B F q).symm := by
  funext p
  exact (fromBiprod_eq p).symm

/-- Exactness of `H'ᵠ(A ⊔ B) → H'ᵠ(A) × H'ᵠ(B) → H'ᵠ(A ⊓ B)`. -/
theorem exact_toProd_fromProd : Function.Exact (toProd A B F q) (fromProd A B F q) := by
  rw [toProd_eq_comp, fromProd_eq_comp]
  exact exact_equiv (biprodEquiv A B F q).toEquiv (seq_exact A B F q 0)

/-- Exactness of `H'ᵠ(A) × H'ᵠ(B) → H'ᵠ(A ⊓ B) → H'ᵠ⁺¹(A ⊔ B)`. -/
theorem exact_fromProd_δ : Function.Exact (fromProd A B F q) (δ A B F q) := by
  rw [fromProd_eq_comp]
  exact exact_comp_equiv (biprodEquiv A B F q).symm.toEquiv (seq_exact A B F q 1)

/-- Exactness of `H'ᵠ(A ⊓ B) → H'ᵠ⁺¹(A ⊔ B) → H'ᵠ⁺¹(A) × H'ᵠ⁺¹(B)`. -/
theorem exact_δ_toProd : Function.Exact (δ A B F q) (toProd A B F (q + 1)) := by
  rw [toProd_eq_comp]
  exact exact_equiv_comp (biprodEquiv A B F (q + 1)).toEquiv
    (biprodEquiv A B F (q + 1)).map_zero (seq_exact A B F q 2)

/-- The composition `H'ᵠ(A) × H'ᵠ(B) → H'ᵠ(A ⊓ B) → H'ᵠ⁺¹(A ⊔ B)` vanishes. -/
lemma δ_fromProd
    (p : CategoryTheory.Sheaf.H'.{u} F q A × CategoryTheory.Sheaf.H'.{u} F q B) :
    δ A B F q (fromProd A B F q p) = 0 :=
  (exact_fromProd_δ A B F q).apply_apply_eq_zero p

end Sequence

section Naturality

variable {A B A' B' : Opens X} (hA : A' ≤ A) (hB : B' ≤ B)

/-- The morphism from the short exact sequence `0 → ℤ[A'⊓B'] → ℤ[A'] ⊞ ℤ[B'] → ℤ[A'⊔B'] → 0`
to the one for `(A, B)`, induced by `A' ≤ A` and `B' ≤ B`. -/
noncomputable def shortComplexMap :
    (Opens.mayerVietorisSquare A' B').shortComplex ⟶
      (Opens.mayerVietorisSquare A B).shortComplex where
  τ₁ := incl (inf_le_inf hA hB)
  τ₂ := biprod.map (incl hA) (incl hB)
  τ₃ := incl (sup_le_sup hA hB)
  comm₁₂ := by
    change _ ≫ biprod.lift (incl (inf_le_left : A ⊓ B ≤ A)) (-incl inf_le_right) =
      biprod.lift (incl (inf_le_left : A' ⊓ B' ≤ A')) (-incl inf_le_right) ≫ _
    apply biprod.hom_ext
    · simp only [Category.assoc]
      erw [biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst]
      exact (incl_comp _ _).trans (incl_comp _ _).symm
    · simp only [Category.assoc]
      erw [biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd]
      simp only [Preadditive.neg_comp]
      exact congrArg Neg.neg ((incl_comp _ _).trans (incl_comp _ _).symm)
  comm₂₃ := by
    change _ ≫ biprod.desc (incl (le_sup_left : A ≤ A ⊔ B)) (incl le_sup_right) =
      biprod.desc (incl (le_sup_left : A' ≤ A' ⊔ B')) (incl le_sup_right) ≫ _
    apply biprod.hom_ext'
    · erw [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc]
      exact (incl_comp _ _).trans (incl_comp _ _).symm
    · erw [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc]
      exact (incl_comp _ _).trans (incl_comp _ _).symm

variable (F : AbSheaf X) {q : ℕ}

/-- Naturality of the first Mayer–Vietoris map under restriction. -/
lemma toProd_naturality (x : CategoryTheory.Sheaf.H'.{u} F q (A ⊔ B)) :
    toProd A' B' F q (res F q (sup_le_sup hA hB) x) =
      Prod.map (res F q hA) (res F q hB) (toProd A B F q x) := by
  simp

/-- Naturality of the second Mayer–Vietoris map under restriction. -/
lemma fromProd_naturality
    (p : CategoryTheory.Sheaf.H'.{u} F q A × CategoryTheory.Sheaf.H'.{u} F q B) :
    fromProd A' B' F q (Prod.map (res F q hA) (res F q hB) p) =
      res F q (inf_le_inf hA hB) (fromProd A B F q p) := by
  simp [map_sub]

/-- **Naturality of the Mayer–Vietoris connecting map**: for `A' ≤ A` and `B' ≤ B`,
`δ_{A',B'} (x|_{A'⊓B'}) = (δ_{A,B} x)|_{A'⊔B'}`. -/
theorem δ_naturality (x : CategoryTheory.Sheaf.H'.{u} F q (A ⊓ B)) :
    δ A' B' F q (res F q (inf_le_inf hA hB) x) =
      res F (q + 1) (sup_le_sup hA hB) (δ A B F q x) := by
  have key : ∀ y : Ext (freeYoneda (A ⊓ B)) F q,
      (Opens.mayerVietorisSquare A' B').shortComplex_shortExact.extClass.comp
          ((Ext.mk₀ (incl (inf_le_inf hA hB))).comp y (zero_add q)) (add_comm 1 q) =
        (Ext.mk₀ (incl (sup_le_sup hA hB))).comp
          ((Opens.mayerVietorisSquare A B).shortComplex_shortExact.extClass.comp y
            (add_comm 1 q)) (zero_add (q + 1)) := by
    intro y
    have nat := ShortComplex.ShortExact.extClass_naturality
      (Opens.mayerVietorisSquare A' B').shortComplex_shortExact
      (Opens.mayerVietorisSquare A B).shortComplex_shortExact (shortComplexMap hA hB)
    refine (Ext.comp_assoc_of_second_deg_zero _ _ _ _).symm.trans ?_
    refine (congrArg (fun e => Ext.comp e y (add_comm 1 q)) nat).trans ?_
    exact Ext.comp_assoc _ _ _ _ _ (by omega)
  exact key x

end Naturality

section DegreeZero

variable {A B : Opens X} {F : AbSheaf X}

/-- In degree zero, the connecting map kills differences of restrictions of sections:
`δ(a|_{A⊓B} - b|_{A⊓B}) = 0` for `a ∈ F(A)`, `b ∈ F(B)`. -/
theorem δ_zeroAddEquiv_symm_sub (a : F.obj.obj (op A)) (b : F.obj.obj (op B)) :
    δ A B F 0 ((zeroAddEquiv F (A ⊓ B)).symm
      (F.obj.map (homOfLE inf_le_left).op a - F.obj.map (homOfLE inf_le_right).op b)) = 0 := by
  have h := δ_fromProd A B F 0 ((zeroAddEquiv F A).symm a, (zeroAddEquiv F B).symm b)
  rwa [fromProd_apply, res_zeroAddEquiv_symm, res_zeroAddEquiv_symm, ← map_sub] at h

/-- Conversely, a section over `A ⊓ B` killed by the connecting map is a difference of
restrictions of sections over `A` and `B`. -/
theorem exists_sub_of_δ_zeroAddEquiv_symm_eq_zero (s : F.obj.obj (op (A ⊓ B)))
    (hs : δ A B F 0 ((zeroAddEquiv F (A ⊓ B)).symm s) = 0) :
    ∃ (a : F.obj.obj (op A)) (b : F.obj.obj (op B)),
      F.obj.map (homOfLE inf_le_left).op a - F.obj.map (homOfLE inf_le_right).op b = s := by
  obtain ⟨⟨a, b⟩, hp⟩ := (exact_fromProd_δ A B F 0 _).1 hs
  refine ⟨zeroAddEquiv F A a, zeroAddEquiv F B b, ?_⟩
  apply (zeroAddEquiv F (A ⊓ B)).symm.injective
  rw [map_sub, ← res_zeroAddEquiv_symm, ← res_zeroAddEquiv_symm, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply, ← hp, fromProd_apply]

end DegreeZero

end TopCat.Sheaf.MayerVietoris

end
