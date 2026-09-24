/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Mathlib.CategoryTheory.Sites.SheafCohomology.Pair
public import Other.AlgebraicGeometry.Cohomology.GlobalSections
public import Other.AlgebraicTopology.ConstantSheafGlobalSection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable (Y : TopCat.{0})

/-- The constant-integer morphism obtained from the terminal free-abelian generator is the
constant morphism determined by that generator. -/
lemma integerConstantHomAddEquivGlobalSections_freeAbelianTerminal
    (F : Sheaf AddCommGrpCat Y)
    (φ : (CategoryTheory.Sheaf.freeAbelianSheaf
      (Opens.grothendieckTopology Y)).obj (⊤ : Opens Y) ⟶ F) :
    integerConstantHomAddEquivGlobalSections F
        ((constantFunctor Y).map
          ((AddEquiv.ulift (α := ℤ)).symm.toAddCommGrpIso.hom) ≫
          (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso
            (J := Opens.grothendieckTopology Y)
            (T := (⊤ : Opens Y)) isTerminalTop).inv ≫ φ) =
      CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv
        (⊤ : Opens Y) F φ := by
  rw [← Category.assoc,
    integerConstantHomAddEquivGlobalSections_naturality]
  change φ.hom.app (op (⊤ : Opens Y)) _ =
    φ.hom.app (op (⊤ : Opens Y))
      (CategoryTheory.Sheaf.freeAbelianSheafGenerator (⊤ : Opens Y))
  congr 1
  change (((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat
      isTerminalTop).homEquiv (AddCommGrpCat.of ℤ)
      ((CategoryTheory.Sheaf.freeAbelianSheaf
        (Opens.grothendieckTopology Y)).obj (⊤ : Opens Y))
      (((constantFunctor Y).map
        ((AddEquiv.ulift (α := ℤ)).symm.toAddCommGrpIso.hom)) ≫
        (CategoryTheory.Sheaf.freeAbelianSheafTerminalIso
          (J := Opens.grothendieckTopology Y)
          (T := (⊤ : Opens Y)) isTerminalTop).inv)) 1) = _
  rw [Adjunction.homEquiv_naturality_right]
  let e : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of (ULift ℤ) :=
    (AddEquiv.ulift (α := ℤ)).symm.toAddCommGrpIso.hom
  have hi := (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat
      isTerminalTop).homEquiv_naturality_left
    e
    (𝟙 ((constantFunctor Y).obj (AddCommGrpCat.of (ULift ℤ))))
  rw [Category.comp_id] at hi
  rw [hi]
  rw [Adjunction.homEquiv_id]
  change ((CategoryTheory.Sheaf.freeAbelianSheafTerminalIso
      (J := Opens.grothendieckTopology Y) (T := (⊤ : Opens Y)) isTerminalTop).inv.hom.app
      (op (⊤ : Opens Y)))
      (((e ≫ (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat
        isTerminalTop).unit.app (AddCommGrpCat.of (ULift ℤ))).hom) 1) = _
  simp [e, constantSheafAdj, constantPresheafAdj]
  rw [← CategoryTheory.comp_apply]
  let η : (yoneda.obj (⊤ : Opens Y) ⋙ AddCommGrpCat.free) ≅
      (Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ)) :=
    NatIso.ofComponents
      (fun U =>
        letI : Unique (U.unop ⟶ (⊤ : Opens Y)) :=
          ⟨⟨isTerminalTop.from _⟩, fun _ => isTerminalTop.hom_ext _ _⟩
        ((FreeAbelianGroup.uniqueEquiv (U.unop ⟶ (⊤ : Opens Y))).trans
          AddEquiv.ulift.symm).toAddCommGrpIso)
      (by
        intro U V g
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro h
        first
          | rfl
          | simp [FreeAbelianGroup.uniqueEquiv, AddCommGrpCat.free_map_coe,
              FreeAbelianGroup.map_of])
  have hn := toSheafify_naturality
    (J := Opens.grothendieckTopology Y) (η := η.inv)
  change ((toSheafify (Opens.grothendieckTopology Y)
      ((Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ))) ≫
        sheafifyMap (Opens.grothendieckTopology Y) η.inv).app (op (⊤ : Opens Y)))
        (ULift.up 1) = _
  rw [← hn]
  change (toSheafify (Opens.grothendieckTopology Y)
      (yoneda.obj (⊤ : Opens Y) ⋙ AddCommGrpCat.free)).app (op (⊤ : Opens Y))
        ((FreeAbelianGroup.uniqueEquiv ((⊤ : Opens Y) ⟶ ⊤)).symm 1) = _
  congr 1

end TopCat.Sheaf
