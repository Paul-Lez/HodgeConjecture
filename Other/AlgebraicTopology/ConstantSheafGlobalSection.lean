/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.OpenSheafRestriction

/-!
# Morphisms out of the constant integer sheaf

A morphism from the constant integer sheaf of a topological space to a sheaf of additive groups
is the same thing as a global section of that sheaf: the constant presheaf is left adjoint to
global sections, and sheafification does not change morphisms into a sheaf.

Only the direction needed later is built here: a global section `t` of `F` gives a morphism
`constHomOfSection F t` sending the constant `n` to `n` times the restriction of `t`, this
assignment is natural in `F`, and the section `1` of the constant integer sheaf itself gives the
identity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

/-- Evaluating at `1` the morphism from `ℤ` determined by a group element. -/
lemma asHom_one {G : AddCommGrpCat.{0}} (g : G) :
    AddCommGrpCat.asHom g (1 : ℤ) = g := by
  rw [AddCommGrpCat.asHom_hom_apply, one_zsmul]

/-- Postcomposing the morphism determined by a group element. -/
lemma asHom_comp {G H : AddCommGrpCat.{0}} (g : G) (h : G ⟶ H) :
    AddCommGrpCat.asHom g ≫ h = AddCommGrpCat.asHom (h g) := by
  apply AddCommGrpCat.int_hom_ext
  simp

variable (Y : TopCat.{0})

/-- The constant sheaf of integers on a topological space. -/
abbrev integerConstantSheaf : Sheaf AddCommGrpCat.{0} Y :=
  (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj (AddCommGrpCat.of ℤ)

/-- The constant integer presheaf on a topological space. -/
abbrev integerConstantPresheaf : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  (Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of ℤ)

variable {Y}

set_option backward.isDefEq.respectTransparency false in
/-- The morphism of presheaves out of the constant integer presheaf determined by a global
section: on an open set it sends `n` to `n` times the restriction of the section. -/
def constPresheafHomOfSection (F : Sheaf AddCommGrpCat.{0} Y)
    (t : F.obj.obj (op ⊤)) : integerConstantPresheaf Y ⟶ F.obj where
  app V := AddCommGrpCat.asHom (F.obj.map (homOfLE (le_top : V.unop ≤ ⊤)).op t)
  naturality V W f := by
    have hmap : F.obj.map (homOfLE (le_top : V.unop ≤ ⊤)).op ≫ F.obj.map f =
        F.obj.map (homOfLE (le_top : W.unop ≤ ⊤)).op := by
      rw [← F.obj.map_comp]
      congr 1
    simp only [Functor.const_obj_map, asHom_comp]
    rw [← CategoryTheory.comp_apply, hmap]
    exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma constPresheafHomOfSection_app_one (F : Sheaf AddCommGrpCat.{0} Y)
    (t : F.obj.obj (op ⊤)) (V : (Opens Y)ᵒᵖ) :
    (constPresheafHomOfSection F t).app V (1 : ℤ) =
      F.obj.map (homOfLE (le_top : V.unop ≤ ⊤)).op t :=
  asHom_one _

/-- The morphism out of the constant integer sheaf determined by a global section. -/
def constHomOfSection (F : Sheaf AddCommGrpCat.{0} Y) (t : F.obj.obj (op ⊤)) :
    integerConstantSheaf Y ⟶ F :=
  ⟨sheafifyLift (Opens.grothendieckTopology Y) (constPresheafHomOfSection F t) F.property⟩

@[reassoc]
lemma toSheafify_constHomOfSection (F : Sheaf AddCommGrpCat.{0} Y)
    (t : F.obj.obj (op ⊤)) :
    toSheafify (Opens.grothendieckTopology Y) (integerConstantPresheaf Y) ≫
      (constHomOfSection F t).hom = constPresheafHomOfSection F t :=
  toSheafify_sheafifyLift _ _ _

/-- Two morphisms out of the constant integer sheaf agree as soon as the underlying morphisms of
presheaves out of the constant integer presheaf agree. -/
lemma constSheafHom_ext {F : Sheaf AddCommGrpCat.{0} Y}
    (a b : integerConstantSheaf Y ⟶ F)
    (h : toSheafify (Opens.grothendieckTopology Y) (integerConstantPresheaf Y) ≫ a.hom =
      toSheafify (Opens.grothendieckTopology Y) (integerConstantPresheaf Y) ≫ b.hom) :
    a = b := by
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  exact sheafify_hom_ext _ _ _ F.property h

set_option backward.isDefEq.respectTransparency false in
/-- The morphism determined by a global section is natural in the sheaf. -/
lemma constHomOfSection_comp {F G : Sheaf AddCommGrpCat.{0} Y}
    (t : F.obj.obj (op ⊤)) (f : F ⟶ G) :
    constHomOfSection F t ≫ f = constHomOfSection G (f.hom.app (op ⊤) t) := by
  refine constSheafHom_ext _ _ ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc,
    toSheafify_constHomOfSection, toSheafify_constHomOfSection]
  apply NatTrans.ext
  funext V
  simp only [NatTrans.comp_app]
  show AddCommGrpCat.asHom _ ≫ _ = AddCommGrpCat.asHom _
  rw [asHom_comp, ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
    f.hom.naturality (homOfLE (le_top : V.unop ≤ ⊤)).op]

/-- The constant global section `1` of the constant integer sheaf. -/
def integerOne : (integerConstantSheaf Y).obj.obj (op (⊤ : Opens Y)) :=
  (toSheafify (Opens.grothendieckTopology Y) (integerConstantPresheaf Y)).app (op ⊤) (1 : ℤ)

set_option backward.isDefEq.respectTransparency false in
/-- The section `1` of the constant integer sheaf determines the identity. -/
lemma constHomOfSection_integerOne :
    constHomOfSection (integerConstantSheaf Y) (integerOne (Y := Y)) = 𝟙 _ := by
  refine constSheafHom_ext _ _ ?_
  rw [ObjectProperty.FullSubcategory.id_hom]
  refine Eq.trans ?_ (Category.comp_id _).symm
  rw [toSheafify_constHomOfSection]
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.int_hom_ext
  have hnat := (toSheafify (Opens.grothendieckTopology Y)
    (integerConstantPresheaf Y)).naturality (homOfLE (le_top : V.unop ≤ ⊤)).op
  have key : (sheafify (Opens.grothendieckTopology Y) (integerConstantPresheaf Y)).map
        (homOfLE (le_top : V.unop ≤ ⊤)).op (integerOne (Y := Y)) =
      (toSheafify (Opens.grothendieckTopology Y) (integerConstantPresheaf Y)).app V (1 : ℤ) := by
    rw [integerOne, ← CategoryTheory.comp_apply, ← hnat, CategoryTheory.comp_apply]
    rfl
  exact (asHom_one _).trans key

end TopCat.Sheaf
