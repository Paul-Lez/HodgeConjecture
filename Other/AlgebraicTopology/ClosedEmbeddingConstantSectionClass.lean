/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.DerivedSheafSectionClass
public import Other.AlgebraicTopology.SingularChainSheafOrientation

/-!+# The constant coefficient class on a closed direct image

The map starts with the sheafification of the literal constant section on the inverse
image of the whole ambient space. The whole-support inclusion and the actual derived
unit then give its degree-zero cohomology class. Coherent shifts transport this to the
shifted direct image. No connectedness, generator choice, or comparison between derived
global sections on the two spaces is required.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite

universe u

namespace TopCat.Sheaf

open AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {Z X : TopCat.{u}} (i : Z ⟶ X) (R : Type u) [Field R]

local instance closedConstantSectionSourceDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat.{u} Z) := HasDerivedCategory.standard _

local instance closedConstantSectionTargetDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat.{u} X) := HasDerivedCategory.standard _

local instance closedConstantSectionGroupsDerivedCategory :
    HasDerivedCategory AddCommGrpCat.{u} := HasDerivedCategory.standard _

/-- The literal constant section in the actual direct-image sheaf on the whole ambient space. -/
def constantPushforwardGlobalSection :
    AddCommGrpCat.of R ⟶
      ((pushforward AddCommGrpCat.{u} i).obj
        (singularOrientationConstantSheaf R Z)).obj.obj (op ⊤) :=
  (CategoryTheory.toSheafify (Opens.grothendieckTopology Z)
    ((Functor.const (Opens Z)ᵒᵖ).obj (AddCommGrpCat.of R))).app
      (op ((Opens.map i).obj ⊤))

/-- No nonzero-generator selection occurs: this is the sheafification unit on constants. -/
@[simp]
lemma constantPushforwardGlobalSection_apply (q : R) :
    constantPushforwardGlobalSection i R q =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Z)
        ((Functor.const (Opens Z)ᵒᵖ).obj (AddCommGrpCat.of R))).app
          (op ((Opens.map i).obj ⊤)) q := rfl

/-- Whole-space support introduces no support condition; use its actual inverse inclusion. -/
def constantPushforwardTopSupportSection :
    AddCommGrpCat.of R ⟶
      (closedSupportSections X ⊤).obj
        ((pushforward AddCommGrpCat.{u} i).obj (singularOrientationConstantSheaf R Z)) :=
  constantPushforwardGlobalSection i R ≫
    ((sheafSectionsWithClosedSupportTopIso X).inv.app
      ((pushforward AddCommGrpCat.{u} i).obj
        (singularOrientationConstantSheaf R Z))).hom.app (op ⊤)

/-- Forgetting whole-space support recovers the literal constant section exactly. -/
@[reassoc]
lemma constantPushforwardTopSupportSection_forget :
    constantPushforwardTopSupportSection i R ≫
      ((sheafSectionsWithClosedSupportTopIso X).hom.app
        ((pushforward AddCommGrpCat.{u} i).obj
          (singularOrientationConstantSheaf R Z))).hom.app (op ⊤) =
      constantPushforwardGlobalSection i R := by
  unfold constantPushforwardTopSupportSection
  rw [Category.assoc]
  have h := congrArg (fun f => f.hom.app (op ⊤))
    ((sheafSectionsWithClosedSupportTopIso X).inv_hom_id_app
      ((pushforward AddCommGrpCat.{u} i).obj (singularOrientationConstantSheaf R Z)))
  change _ ≫ _ = _ at h
  rw [h]
  change constantPushforwardGlobalSection i R ≫ 𝟙 _ = _
  exact Category.comp_id _

variable (hi : IsClosedEmbedding i)

/-- At an image point, the actual direct-image stalk comparison takes the constant
global section to the germ of that same literal constant section on the source. -/
@[reassoc]
lemma constantPushforwardGlobalSection_stalk (z : Z) :
    constantPushforwardGlobalSection i R ≫
      Presheaf.germ
        ((pushforward AddCommGrpCat.{u} i).obj
          (singularOrientationConstantSheaf R Z)).obj ⊤ (i z) (by trivial) ≫
        (closedEmbeddingPushforwardStalkIso i hi
          (singularOrientationConstantSheaf R Z) z).hom =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Z)
        ((Functor.const (Opens Z)ᵒᵖ).obj (AddCommGrpCat.of R))).app
          (op ((Opens.map i).obj ⊤)) ≫
        Presheaf.germ (singularOrientationConstantSheaf R Z).obj
          ((Opens.map i).obj ⊤) z (by trivial) := by
  rw [closedEmbeddingPushforwardStalkIso_germ]
  rfl

/-- The literal constant section, sent through the actual derived unit and the exact
single-complex direct-image comparison. -/
def closedEmbeddingConstantSectionClassMap :
    AddCommGrpCat.of R ⟶
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((derivedClosedSupportSections X ⊤).obj
          ((closedEmbeddingDerivedPushforwardPlus i hi).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              (singularOrientationConstantSheaf R Z)))) :=
  constantPushforwardTopSupportSection i R ≫
    (closedSupportSections X ⊤).derivedSectionClassMap
      ((pushforward AddCommGrpCat.{u} i).obj (singularOrientationConstantSheaf R Z)) 0 ≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedClosedSupportSections X ⊤).map
        (closedEmbeddingDerivedPushforwardPlusSingleIso i hi
          (singularOrientationConstantSheaf R Z) 0).inv)

/-- The shifted source cohomology is identified with its degree-zero group through the
constructed coherent shifts of exact direct image, derived sections, and cohomology. -/
def closedEmbeddingConstantShiftedSectionsIso (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (-n)).obj
      ((derivedClosedSupportSections X ⊤).obj
        ((closedEmbeddingDerivedPushforwardPlus i hi).obj
          (((DerivedCategory.Plus.singleFunctor _ 0).obj
            (singularOrientationConstantSheaf R Z))⟦n⟧))) ≅
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedClosedSupportSections X ⊤).obj
        ((closedEmbeddingDerivedPushforwardPlus i hi).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            (singularOrientationConstantSheaf R Z)))) :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (-n)).mapIso
    ((derivedClosedSupportSections X ⊤).mapIso
      (((closedEmbeddingDerivedPushforwardPlus i hi).commShiftIso n).app _) ≪≫
      ((derivedClosedSupportSections X ⊤).commShiftIso n).app _) ≪≫
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 0).shiftIso n (-n) 0
      (by omega)).app _

/-- The canonically shifted constant section class, additive in the original coefficient. -/
def closedEmbeddingConstantShiftedSectionClassMap (n : ℤ) :
    AddCommGrpCat.of R ⟶
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (-n)).obj
        ((derivedClosedSupportSections X ⊤).obj
          ((closedEmbeddingDerivedPushforwardPlus i hi).obj
            (((DerivedCategory.Plus.singleFunctor _ 0).obj
              (singularOrientationConstantSheaf R Z))⟦n⟧))) :=
  closedEmbeddingConstantSectionClassMap i R hi ≫
    (closedEmbeddingConstantShiftedSectionsIso i R hi n).inv

/-- Removing the shifts recovers exactly the derived class of the original constant section. -/
@[reassoc (attr := simp)]
lemma closedEmbeddingConstantShiftedSectionClassMap_unshift (n : ℤ) :
    closedEmbeddingConstantShiftedSectionClassMap i R hi n ≫
      (closedEmbeddingConstantShiftedSectionsIso i R hi n).hom =
        closedEmbeddingConstantSectionClassMap i R hi := by
  simp [closedEmbeddingConstantShiftedSectionClassMap]

end TopCat.Sheaf
