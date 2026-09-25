/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.UnitExtensionOpenRestriction

/-!
# Sheaves that are local on an open subset

Let `U` be an open subset of a topological space `Y`, with inclusion `j`, and write
`T := j_* j^*` for the composite `openRestrictionPushforward` with its canonical morphism
`η : F ⟶ T F` (`toOpenRestrictionPushforward`).

This file proves that a direct image `j_* S` is *local on `U`*, in the sense that

`Hom(T F, j_* S) → Hom(F, j_* S)`, `b ↦ η_F ≫ b`

is bijective for every `F` (`isOpenRestrictionLocal_pushforward`). The proof is the adjunction
`j^* ⊣ j_* ` (`openSheafRestrictionAdjunction`) together with the fact that `j^* η_F` is an
isomorphism, which in turn follows from the counit of that adjunction being an isomorphism
(`isIso_openSheafRestrictionCounit_app`): the counit is, on each open `V` of `U`, restriction of
sections along the equality `j^{-1}(j(V)) = V`.

The property is recorded as `TopCat.Sheaf.IsOpenRestrictionLocal`; it is stable under
isomorphisms of the target and holds for zero objects, so it holds for every term of a complex
obtained by pushing forward from `U`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

universe u

variable (Y : TopCat.{u}) (U : Opens Y)

/-- The preimage in `U` of the image of an open subset of `U` is that subset. -/
lemma openRestriction_map_functor_le (V : Opens (TopCat.of U)) :
    (Opens.map U.inclusion').obj (U.isOpenEmbedding.isOpenMap.functor.obj V) ≤ V := by
  rintro x ⟨y, hy, hxy⟩
  exact (Subtype.val_injective hxy) ▸ hy

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the counit of the open-restriction adjunction. -/
def openSheafRestrictionCounitInv :
    𝟭 (Sheaf AddCommGrpCat.{u} (TopCat.of U)) ⟶
      pushforward AddCommGrpCat.{u} U.inclusion' ⋙
        U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u} where
  app F := ⟨{
    app V := F.obj.map (homOfLE (openRestriction_map_functor_le Y U V.unop)).op
    naturality V W f := by
      change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
      rw [← F.obj.map_comp, ← F.obj.map_comp]
      congr 1 }⟩
  naturality F G f := by
    apply CategoryTheory.Sheaf.hom_ext_iff.mpr
    apply NatTrans.ext
    funext V
    exact (f.hom.naturality _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The counit of the open-restriction adjunction is an isomorphism: restricting a sheaf on `U`
to `U` changes nothing. -/
instance isIso_openSheafRestrictionCounit_app (F : Sheaf AddCommGrpCat.{u} (TopCat.of U)) :
    IsIso ((openSheafRestrictionCounit Y U).app F) := by
  refine ⟨(openSheafRestrictionCounitInv Y U).app F, ?_, ?_⟩
  · apply CategoryTheory.Sheaf.hom_ext_iff.mpr
    apply NatTrans.ext
    funext V
    change F.obj.map _ ≫ F.obj.map _ = 𝟙 _
    rw [← F.obj.map_comp]
    convert F.obj.map_id _ using 1
    congr 1
  · apply CategoryTheory.Sheaf.hom_ext_iff.mpr
    apply NatTrans.ext
    funext V
    change F.obj.map _ ≫ F.obj.map _ = 𝟙 _
    rw [← F.obj.map_comp]
    convert F.obj.map_id _ using 1
    congr 1

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The restriction to `U` of the canonical restriction morphism is an isomorphism. -/
instance isIso_sheafPullback_map_toOpenRestrictionPushforward
    (F : Sheaf AddCommGrpCat.{u} Y) :
    IsIso ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).map
      ((toOpenRestrictionPushforward Y U).app F)) := by
  have h := (openSheafRestrictionAdjunction Y U).left_triangle_components F
  letI hc : IsIso ((openSheafRestrictionAdjunction Y U).counit.app
      ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj F)) :=
    isIso_openSheafRestrictionCounit_app Y U _
  letI : IsIso ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).map
      ((toOpenRestrictionPushforward Y U).app F) ≫
      (openSheafRestrictionAdjunction Y U).counit.app
        ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj F)) := by
    rw [show (toOpenRestrictionPushforward Y U).app F =
      (openSheafRestrictionAdjunction Y U).unit.app F from rfl, h]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ ((openSheafRestrictionAdjunction Y U).counit.app _)

/-- A sheaf `T` on `Y` is *local on the open set `U`* when every morphism to `T` from a sheaf `F`
extends uniquely along the canonical restriction morphism `F ⟶ j_* j^* F`. -/
def IsOpenRestrictionLocal (T : Sheaf AddCommGrpCat.{u} Y) : Prop :=
  ∀ F : Sheaf AddCommGrpCat.{u} Y,
    Function.Bijective (fun b : (openRestrictionPushforward Y U).obj F ⟶ T =>
      (toOpenRestrictionPushforward Y U).app F ≫ b)

variable {Y U}

/-- Being local on `U` only depends on the isomorphism class of the target. -/
lemma IsOpenRestrictionLocal.of_iso {T T' : Sheaf AddCommGrpCat.{u} Y}
    (h : IsOpenRestrictionLocal Y U T) (e : T ≅ T') : IsOpenRestrictionLocal Y U T' := by
  intro F
  constructor
  · intro b₁ b₂ hb
    have h₁ : (toOpenRestrictionPushforward Y U).app F ≫ b₁ ≫ e.inv =
        (toOpenRestrictionPushforward Y U).app F ≫ b₂ ≫ e.inv := by
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (fun t => t ≫ e.inv) hb
    have h₂ := (h F).1 h₁
    have h₃ := congrArg (fun t => t ≫ e.hom) h₂
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h₃
  · intro a
    obtain ⟨b, hb⟩ := (h F).2 (a ≫ e.inv)
    replace hb : (toOpenRestrictionPushforward Y U).app F ≫ b = a ≫ e.inv := hb
    refine ⟨b ≫ e.hom, ?_⟩
    show (toOpenRestrictionPushforward Y U).app F ≫ b ≫ e.hom = a
    rw [← Category.assoc, hb, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- A zero sheaf is local on every open set. -/
lemma isOpenRestrictionLocal_of_isZero {T : Sheaf AddCommGrpCat.{u} Y} (hT : IsZero T) :
    IsOpenRestrictionLocal Y U T :=
  fun _ => ⟨fun _ _ _ => hT.eq_of_tgt _ _, fun _ => ⟨0, hT.eq_of_tgt _ _⟩⟩

variable (Y U)

set_option backward.isDefEq.respectTransparency false in
/-- **A direct image from `U` is local on `U`.** This is the adjunction `j^* ⊣ j_*` together with
the fact that `j^*` carries the canonical restriction morphism to an isomorphism. -/
lemma isOpenRestrictionLocal_pushforward (S : Sheaf AddCommGrpCat.{u} (TopCat.of U)) :
    IsOpenRestrictionLocal Y U ((pushforward AddCommGrpCat.{u} U.inclusion').obj S) := by
  intro F
  set L := U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u} with hL
  set adj := openSheafRestrictionAdjunction Y U with hadj
  have hiso : Function.Bijective
      (fun g : L.obj ((openRestrictionPushforward Y U).obj F) ⟶ S =>
        L.map ((toOpenRestrictionPushforward Y U).app F) ≫ g) := by
    constructor
    · intro g₁ g₂ h
      have h' := congrArg
        (fun t => inv (L.map ((toOpenRestrictionPushforward Y U).app F)) ≫ t) h
      simpa only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] using h'
    · intro g
      refine ⟨inv (L.map ((toOpenRestrictionPushforward Y U).app F)) ≫ g, ?_⟩
      show L.map ((toOpenRestrictionPushforward Y U).app F) ≫
        inv (L.map ((toOpenRestrictionPushforward Y U).app F)) ≫ g = g
      rw [IsIso.hom_inv_id_assoc]
  have key : (fun b : (openRestrictionPushforward Y U).obj F ⟶
        (pushforward AddCommGrpCat.{u} U.inclusion').obj S =>
      (toOpenRestrictionPushforward Y U).app F ≫ b) =
      (fun g => (adj.homEquiv F S) g) ∘
        ((fun g => L.map ((toOpenRestrictionPushforward Y U).app F) ≫ g) ∘
          (fun b => (adj.homEquiv ((openRestrictionPushforward Y U).obj F) S).symm b)) := by
    funext b
    show _ = adj.homEquiv F S (L.map ((toOpenRestrictionPushforward Y U).app F) ≫
      (adj.homEquiv _ S).symm b)
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
  rw [key]
  exact (adj.homEquiv F S).bijective.comp
    (hiso.comp (adj.homEquiv ((openRestrictionPushforward Y U).obj F) S).symm.bijective)

end TopCat.Sheaf
