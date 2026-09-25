/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Sites.Whiskering

/-! Forgetful functors between categories of sheaves. -/

@[expose] public section

universe w v v₁ v₂ u u₁ u₂

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {A : Type u₁} [Category.{v₁} A]
variable {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-- A sheaf morphism acts on sections together with their domains. -/
instance Sheaf.homFunLike (F G : Sheaf J A) :
    FunLike (F ⟶ G) (Σ U, ToType (F.obj.obj U)) (Σ U, ToType (G.obj.obj U)) where
  coe f x := ⟨x.1, f.hom.app x.1 x.2⟩
  coe_injective f g h := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    exact eq_of_heq (Sigma.mk.inj_iff.mp (congrFun h ⟨U, x⟩)).2

/-- The underlying type of a sheaf consists of all its sections, tagged by domain. -/
instance Sheaf.concreteCategory : ConcreteCategory (Sheaf J A) (fun F G ↦ F ⟶ G) where
  hom f := f
  ofHom f := f
  id_apply {F} x := by
    change Sigma.mk x.1 (ConcreteCategory.hom (𝟙 (F.obj.obj x.1)) x.2) = x
    simp
  comp_apply {P Q R} f g x := by
    change Sigma.mk (β := fun U ↦ ToType (R.obj.obj U)) x.1
      (ConcreteCategory.hom (f.hom.app x.1 ≫ g.hom.app x.1) x.2) =
      Sigma.mk x.1 (g.hom.app x.1 (f.hom.app x.1 x.2))
    simp only [ConcreteCategory.comp_apply]

private def sheafToTypes (F : A ⥤ Type w) : Sheaf J A ⥤ Type (max u w) where
  obj P := Σ U, F.obj (P.obj.obj U)
  map f := ↾fun x ↦ ⟨x.1, F.map (f.hom.app x.1) x.2⟩
  map_id P := by
    apply ConcreteCategory.hom_ext
    intro x
    change Sigma.mk x.1 (F.map (𝟙 _) x.2) = x
    simp
  map_comp {P Q R} f g := by
    apply ConcreteCategory.hom_ext
    intro x
    change Sigma.mk (β := fun U ↦ F.obj (R.obj.obj U)) x.1
      (F.map (f.hom.app x.1 ≫ g.hom.app x.1) x.2) =
      Sigma.mk x.1 (F.map (g.hom.app x.1) (F.map (f.hom.app x.1) x.2))
    simp only [Functor.map_comp, ConcreteCategory.comp_apply]

variable {B : Type u₂} [Category.{v₂} B]
variable {FB : B → B → Type*} {CB : B → Type w}
  [∀ X Y, FunLike (FB X Y) (CB X) (CB Y)] [ConcreteCategory B FB]
  [HasForget₂ A B] [J.HasSheafCompose (forget₂ A B)]

/-- Forget coefficient structure in a sheaf when the forgetful functor preserves sheaves. -/
@[simps! obj_obj map_hom]
def sheafForget₂ : Sheaf J A ⥤ Sheaf J B :=
  sheafCompose J (forget₂ A B)

/-- Lift a coefficient forgetful functor to sheaves. -/
instance Sheaf.hasForget₂ : HasForget₂ (Sheaf J A) (Sheaf J B) where
  forget₂ := sheafForget₂ J
  forget_comp := by
    change sheafToTypes J (forget₂ A B ⋙ forget B) = sheafToTypes J (forget A)
    rw [HasForget₂.forget_comp]

end CategoryTheory
