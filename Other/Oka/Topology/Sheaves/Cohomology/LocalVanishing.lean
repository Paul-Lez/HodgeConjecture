/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Topology.Sheaves.Cohomology.Leray
public import Other.Oka.Topology.Sheaves.Cohomology.MayerVietoris

/-!
# Cohomology classes vanish locally

For an abelian sheaf `F` on `X`, an open `U` and `q ≥ 1`, every class `c ∈ Hᵠ(U, F)` restricts to
zero on a neighbourhood of each point of `U`.

We work with Mathlib's `CategoryTheory.Sheaf.H' F q U = Extᵠ(ℤ[U], F)`, which is a presheaf in
`U` (`CategoryTheory.Sheaf.cohomologyPresheaf`), so restriction maps are functorial by
construction. The result is transferred to `Hᵠ(U, F|_U)` along `TopCat.Sheaf.H'AddEquiv`.

## Main definitions and results

* `TopCat.Sheaf.H'res F q h : H' F q U ⟶ H' F q V` for `h : V ≤ U`, with `H'res_apply`
  (precomposition with `ℤ[V] ⟶ ℤ[U]`), `H'res_self` and `H'res_res`.
* `TopCat.Sheaf.exists_H'res_eq_zero`: the local vanishing of classes of positive degree, and
  `TopCat.Sheaf.exists_cover_H'res_eq_zero` (a cover of `U` on whose members `c` vanishes).
* `TopCat.Sheaf.restrictOpenRes F q h : Hᵠ(U, F|_U) →+ Hᵠ(V, F|_V)`, the restriction maps
  transported along `H'AddEquiv`, with `restrictOpenRes_self`, `restrictOpenRes_restrictOpenRes`
  and `TopCat.Sheaf.exists_restrictOpenRes_eq_zero`.

The proof is by dimension shifting along `0 → F → I → I/F → 0` with `I` injective: in degree one
a class is the image of a section of `I/F`, which lifts locally to `I`; in higher degrees
`Extᵠ⁺¹(ℤ[U], F)` is the image of `Extᵠ(ℤ[U], I/F)` under the connecting map, which commutes
with restriction.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace Opposite Abelian

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

section FreeYoneda

variable {U V W : Opens X}

/-- The map `ℤ[V] ⟶ ℤ[U]` of free abelian sheaves induced by an inclusion `V ≤ U`. -/
noncomputable def freeYonedaMap (h : V ≤ U) : freeYoneda V ⟶ freeYoneda U :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (Functor.whiskerRight (yoneda.map (homOfLE h)) AddCommGrpCat.free)

/-- Under `ℤ[U] ⟶ B ≃ B(U)`, precomposition with `ℤ[V] ⟶ ℤ[U]` is restriction of sections. -/
lemma freeYonedaHomEquiv_freeYonedaMap_comp (h : V ≤ U) {B : AbSheaf X}
    (s : freeYoneda U ⟶ B) :
    freeYonedaHomEquiv V B (freeYonedaMap h ≫ s) =
      B.obj.map (homOfLE h).op (freeYonedaHomEquiv U B s) := by
  simp only [freeYonedaHomEquiv, freeYonedaMap, Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_left]
  generalize (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).homEquiv _ B
    s = g
  have := (Adjunction.whiskerRight (Opens X)ᵒᵖ AddCommGrpCat.adj).homEquiv_naturality_left
    (yoneda.map (homOfLE h)) g
  exact (congrArg yonedaEquiv this).trans (yonedaEquiv_naturality _ _).symm

end FreeYoneda

section Restriction

variable (F : AbSheaf X) (q : ℕ) {U V W : Opens X}

/-- The restriction map `H' F q U ⟶ H' F q V` for `V ≤ U`. -/
noncomputable abbrev H'res (h : V ≤ U) :
    CategoryTheory.Sheaf.H'.{u} F q U ⟶ CategoryTheory.Sheaf.H'.{u} F q V :=
  (F.cohomologyPresheaf q).map (homOfLE h).op

variable {F q}

/-- Restriction in `H'` is precomposition with `ℤ[V] ⟶ ℤ[U]`. -/
lemma H'res_apply (h : V ≤ U) (c : CategoryTheory.Sheaf.H'.{u} F q U) :
    H'res F q h c =
      (Abelian.Ext.mk₀ (freeYonedaMap h)).comp (c : Ext (freeYoneda U) F q) (zero_add q) :=
  rfl

/-- Restriction from `U` to `U` is the identity. -/
@[simp]
lemma H'res_self (c : CategoryTheory.Sheaf.H'.{u} F q U) : H'res F q (le_refl U) c = c := by
  rw [H'res, show (homOfLE (le_refl U)).op = 𝟙 (op U) from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- Restriction maps compose. -/
@[simp]
lemma H'res_res (hVU : V ≤ U) (hWV : W ≤ V) (c : CategoryTheory.Sheaf.H'.{u} F q U) :
    H'res F q hWV (H'res F q hVU c) = H'res F q (hWV.trans hVU) c := by
  rw [H'res, H'res, H'res, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

end Restriction

section LocalVanishing

variable (F : AbSheaf X)

/-- A degree one class vanishes locally: it is the image of a section of `I/F`, which lifts
locally to the injective sheaf `I`. -/
lemma exists_H'res_eq_zero_one {U : Opens X} (c : CategoryTheory.Sheaf.H'.{u} F 1 U) {x : X}
    (hx : x ∈ U) : ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ H'res F 1 h c = 0 := by
  let S := injSES F
  have hS : S.ShortExact := injSES_shortExact F
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ (freeYoneda U) hS
    (c : Ext (freeYoneda U) F 1) (Ext.eq_zero_of_injective _) (zero_add 1)
  obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective _ _).2 z
  have hloc := (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).1
    ((TopCat.Sheaf.isLocallySurjective_iff_epi (F := (S.X₂ : X.Sheaf AddCommGrpCat.{u}))
      (G := (S.X₃ : X.Sheaf AddCommGrpCat.{u})) S.g).2 hS.epi_g) U
    (freeYonedaHomEquiv U S.X₃ s) x hx
  obtain ⟨V, hVU, ⟨t, ht⟩, hxV⟩ := hloc
  refine ⟨V, hVU, hxV, ?_⟩
  let t' : freeYoneda V ⟶ S.X₂ := (freeYonedaHomEquiv V S.X₂).symm t
  have key : freeYonedaMap hVU ≫ s = t' ≫ S.g := by
    apply (freeYonedaHomEquiv V S.X₃).injective
    rw [freeYonedaHomEquiv_freeYonedaMap_comp, freeYonedaHomEquiv_comp, Equiv.apply_symm_apply,
      ht]
    rfl
  rw [H'res_apply, ← hz]
  change ((Ext.mk₀ (freeYonedaMap hVU)).comp ((Ext.mk₀ s).comp hS.extClass (zero_add 1))
    (zero_add 1) : Ext (freeYoneda V) S.X₁ 1) = 0
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, key, ← Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

/-- **Cohomology classes vanish locally.** For `q ≥ 1`, a class `c ∈ H'ᵠ(U, F)` restricts to zero
on some open neighbourhood `V ≤ U` of any given point `x ∈ U`. -/
theorem exists_H'res_eq_zero (q : ℕ) {U : Opens X}
    (c : CategoryTheory.Sheaf.H'.{u} F (q + 1) U) {x : X} (hx : x ∈ U) :
    ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ H'res F (q + 1) h c = 0 := by
  induction q generalizing F U with
  | zero => exact exists_H'res_eq_zero_one F c hx
  | succ q ih =>
    let S := injSES F
    have hS : S.ShortExact := injSES_shortExact F
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ (freeYoneda U) hS
      (c : Ext (freeYoneda U) F (q + 2)) (Ext.eq_zero_of_injective _) rfl
    obtain ⟨V, hVU, hxV, hV⟩ := ih S.X₃ z hx
    refine ⟨V, hVU, hxV, ?_⟩
    rw [H'res_apply] at hV ⊢
    rw [← hz]
    change ((Ext.mk₀ (freeYonedaMap hVU)).comp (z.comp hS.extClass rfl) (zero_add _) :
      Ext (freeYoneda V) S.X₁ (q + 2)) = 0
    rw [← Ext.comp_assoc _ _ _ (zero_add _) rfl (by omega), hV]
    exact Ext.zero_comp (freeYoneda V) (q + 1) hS.extClass _ _

/-- **Cohomology classes vanish locally**, cover form: for `q ≥ 1` and `c ∈ H'ᵠ(U, F)` there is
an open cover of `U` by opens `V i ≤ U` on each of which `c` restricts to zero. -/
theorem exists_cover_H'res_eq_zero (q : ℕ) {U : Opens X}
    (c : CategoryTheory.Sheaf.H'.{u} F (q + 1) U) :
    ∃ (V : U → Opens X) (h : ∀ i, V i ≤ U), (⨆ i, V i) = U ∧
      ∀ i, H'res F (q + 1) (h i) c = 0 := by
  choose V hVU hxV hV using fun x : U => exists_H'res_eq_zero F q c x.2
  exact ⟨V, hVU, le_antisymm (iSup_le hVU) fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV _⟩, hV⟩

end LocalVanishing

section RestrictOpen

variable (F : AbSheaf X) (q : ℕ) {U V W : Opens X}

/-- The restriction map `Hᵠ(U, F|_U) →+ Hᵠ(V, F|_V)` for `V ≤ U`, transported from `H'res`
along `H'AddEquiv`. -/
noncomputable def restrictOpenRes (h : V ≤ U) :
    H ((restrictOpen U).obj F) q →+ H ((restrictOpen V).obj F) q :=
  ((H'AddEquiv V F q).toAddMonoidHom.comp (H'res F q h).hom).comp
    (H'AddEquiv U F q).symm.toAddMonoidHom

variable {F q}

lemma restrictOpenRes_apply (h : V ≤ U) (c : H ((restrictOpen U).obj F) q) :
    restrictOpenRes F q h c = H'AddEquiv V F q (H'res F q h ((H'AddEquiv U F q).symm c)) :=
  rfl

/-- `restrictOpenRes` corresponds to `H'res` under `H'AddEquiv`. -/
lemma restrictOpenRes_H'AddEquiv (h : V ≤ U) (c : CategoryTheory.Sheaf.H'.{u} F q U) :
    restrictOpenRes F q h (H'AddEquiv U F q c) = H'AddEquiv V F q (H'res F q h c) := by
  rw [restrictOpenRes_apply, AddEquiv.symm_apply_apply]

/-- Restriction from `U` to `U` is the identity. -/
@[simp]
lemma restrictOpenRes_self (c : H ((restrictOpen U).obj F) q) :
    restrictOpenRes F q (le_refl U) c = c := by
  rw [restrictOpenRes_apply, H'res_self, AddEquiv.apply_symm_apply]

/-- Restriction maps compose. -/
@[simp]
lemma restrictOpenRes_restrictOpenRes (hVU : V ≤ U) (hWV : W ≤ V)
    (c : H ((restrictOpen U).obj F) q) :
    restrictOpenRes F q hWV (restrictOpenRes F q hVU c) =
      restrictOpenRes F q (hWV.trans hVU) c := by
  rw [restrictOpenRes_apply, restrictOpenRes_apply, restrictOpenRes_apply,
    AddEquiv.symm_apply_apply, H'res_res]

variable (F q)

/-- **Cohomology classes vanish locally.** For `q ≥ 1`, a class `c ∈ Hᵠ(U, F|_U)` restricts to
zero in `Hᵠ(V, F|_V)` for some open neighbourhood `V ≤ U` of any given point `x ∈ U`. -/
theorem exists_restrictOpenRes_eq_zero (c : H ((restrictOpen U).obj F) (q + 1)) {x : X}
    (hx : x ∈ U) : ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ restrictOpenRes F (q + 1) h c = 0 := by
  obtain ⟨V, h, hxV, hV⟩ := exists_H'res_eq_zero F q ((H'AddEquiv U F (q + 1)).symm c) hx
  exact ⟨V, h, hxV, by rw [restrictOpenRes_apply, hV, map_zero]⟩

end RestrictOpen

end TopCat.Sheaf

end
