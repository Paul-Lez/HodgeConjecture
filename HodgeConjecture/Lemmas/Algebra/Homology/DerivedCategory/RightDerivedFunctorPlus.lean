/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Additivity of bounded-below right derived functors

This file supplies the additive instances for the bounded-below localization functors and proves
that the bounded-below right derived functor of an additive functor is additive. The proof uses
the equivalence between the bounded-below homotopy category of injective objects and the
bounded-below derived category.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace HomotopyCategory.Plus

variable (C : Type*) [Category* C] [Abelian C]

/-- The quotient functor from bounded-below complexes to the bounded-below homotopy category is
additive. -/
instance quotientAdditive : (quotient C).Additive := by
  let _ : (CochainComplex.Plus.ι C).Additive := { map_add := rfl }
  let _ : (ι C).Additive := { map_add := rfl }
  let _ : (quotient C ⋙ ι C).Additive :=
    Functor.additive_of_iso (quotientCompιIso C).symm
  exact Functor.additive_of_comp_faithful _ (ι C)

end HomotopyCategory.Plus

namespace DerivedCategory.Plus

variable (C : Type*) [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The localization functor from the bounded-below homotopy category is additive. -/
instance QhAdditive : (Qh (C := C)).Additive := by
  let _ : (HomotopyCategory.Plus.ι C).Additive := { map_add := rfl }
  let _ : (ι (C := C)).Additive := { map_add := rfl }
  let _ : (Qh ⋙ ι).Additive :=
    Functor.additive_of_iso (QhCompιIsoιCompQh C).symm
  exact Functor.additive_of_comp_faithful _ ι

/-- The localization functor from bounded-below complexes is additive. -/
instance QAdditive : (Q (C := C)).Additive := by
  dsimp only [Q]
  infer_instance

/-- The bounded-below localization functor agrees with the unbounded localization functor after
both inclusions. -/
def QCompιIsoιCompQ : Q ⋙ ι ≅ CochainComplex.Plus.ι C ⋙ DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.Plus.quotient C) (QhCompιIsoιCompQh C) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (HomotopyCategory.Plus.quotientCompιIso C) DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (CochainComplex.Plus.ι C) (DerivedCategory.quotientCompQhIso C)

/-- A quasi-isomorphism of bounded-below complexes becomes an isomorphism in the bounded-below
derived category. -/
instance {K L : CochainComplex.Plus C} (f : K ⟶ L) [QuasiIso f.hom] : IsIso (Q.map f) := by
  let e := QCompιIsoιCompQ C
  have hi : IsIso (ι.map (Q.map f)) := by
    have : IsIso (ι.map (Q.map f) ≫ e.hom.app L) := by
      change IsIso ((Q ⋙ ι).map f ≫ e.hom.app L)
      rw [e.hom.naturality]
      dsimp
      infer_instance
    exact IsIso.of_isIso_comp_right _ (e.hom.app L)
  exact isIso_of_fully_faithful ι _

end DerivedCategory.Plus

namespace HomotopyCategory.Plus

variable (C : Type*) [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The bounded-below homotopy category of injective objects maps to the bounded-below derived
category. -/
def injectiveToDerived :
    HomotopyCategory.Plus (InjectiveObject C) ⥤ DerivedCategory.Plus C :=
  (InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh

instance : (injectiveToDerived C).Additive := by
  dsimp only [injectiveToDerived]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma injectiveToDerived_map_bijective
    (K L : HomotopyCategory.Plus (InjectiveObject C)) :
    Function.Bijective ((injectiveToDerived C).map : (K ⟶ L) → _) := by
  let incl := (InjectiveObject.ι C).mapHomotopyCategoryPlus
  have hL : CochainComplex.IsKInjective (incl.obj L).obj.as := by
    obtain ⟨n, hn⟩ : CochainComplex.plus C (incl.obj L).obj.as := by
      have h := (incl.obj L).property
      rwa [← HomotopyCategory.plus_quotient_obj_iff]
    exact CochainComplex.isKInjective_of_injective _ n
  exact (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective
    (incl.obj K) (incl.obj L) hL).comp ⟨incl.map_injective, incl.map_surjective⟩

instance : (injectiveToDerived C).Full where
  map_surjective := (injectiveToDerived_map_bijective C _ _).surjective

instance : (injectiveToDerived C).Faithful where
  map_injective {K L} {_f _g} h := (injectiveToDerived_map_bijective C K L).injective h

variable [EnoughInjectives C]

instance : (injectiveToDerived C).EssSurj := by
  dsimp only [injectiveToDerived]
  infer_instance

instance : (injectiveToDerived C).IsEquivalence := { }

instance : (injectiveToDerived C).IsLocalization
    (MorphismProperty.isomorphisms (HomotopyCategory.Plus (InjectiveObject C))) :=
  Functor.IsLocalization.of_isEquivalence _ _ (by rfl)

omit [HasDerivedCategory C] in
/-- Natural transformations into a functor that inverts quasi-isomorphisms are determined by
their values on bounded-below injective complexes. -/
lemma natTrans_ext_on_injectives {H : Type*} [Category* H]
    {F G : HomotopyCategory.Plus C ⥤ H}
    (hG : (HomotopyCategory.Plus.quasiIso C).IsInvertedBy G)
    {α β : F ⟶ G}
    (h : ∀ K : HomotopyCategory.Plus (InjectiveObject C),
      α.app ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj K) =
        β.app ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj K)) : α = β := by
  ext K : 2
  let r := Classical.arbitrary ((HomotopyCategory.Plus.localizerMorphism C).RightResolution K)
  have : IsIso (G.map r.w) := hG r.w r.hw
  rw [← cancel_mono (G.map r.w), ← α.naturality, ← β.naturality, h]

end HomotopyCategory.Plus

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive]

set_option backward.isDefEq.respectTransparency false in
/-- The functor induced by an additive functor on bounded-below homotopy categories is additive. -/
instance mapHomotopyCategoryPlusAdditive : F.mapHomotopyCategoryPlus.Additive where
  map_add {K L} f g := by
    apply (HomotopyCategory.Plus.ι D).map_injective
    exact (F.mapHomotopyCategory (ComplexShape.up ℤ)).map_add

variable [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- Termwise application of `F` to bounded-below injective complexes, followed by passage to the
derived category. -/
def rightDerivedFunctorPlusOnInjectives :
    HomotopyCategory.Plus (InjectiveObject C) ⥤ DerivedCategory.Plus D :=
  (InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙
    F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh

instance : F.rightDerivedFunctorPlusOnInjectives.Additive := by
  dsimp only [rightDerivedFunctorPlusOnInjectives]
  infer_instance

/-- The right-derived unit restricted to injective complexes. -/
def rightDerivedFunctorPlusOnInjectivesUnit :
    F.rightDerivedFunctorPlusOnInjectives ⟶
      HomotopyCategory.Plus.injectiveToDerived C ⋙ F.rightDerivedFunctorPlus :=
  whiskerLeft (InjectiveObject.ι C).mapHomotopyCategoryPlus
      F.rightDerivedFunctorPlusUnit ≫
    (Functor.associator _ _ _).inv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : IsIso F.rightDerivedFunctorPlusOnInjectivesUnit := by
  have h (K : HomotopyCategory.Plus (InjectiveObject C)) :
      IsIso (F.rightDerivedFunctorPlusUnit.app
        ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj K)) :=
    (HomotopyCategory.Plus.localizerMorphism_derives
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).isIso_of_isRightDerivedFunctor
        F.rightDerivedFunctorPlusUnit K
  let _ : ∀ K, IsIso (F.rightDerivedFunctorPlusOnInjectivesUnit.app K) := fun K => by
    simpa only [rightDerivedFunctorPlusOnInjectivesUnit, NatTrans.comp_app,
      whiskerLeft_app, Functor.associator_inv_app, Category.comp_id] using h K
  exact NatIso.isIso_of_isIso_app _

/-- The canonical injective-resolution comparison. -/
def rightDerivedFunctorPlusOnInjectivesIso :
    HomotopyCategory.Plus.injectiveToDerived C ⋙ F.rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlusOnInjectives :=
  (asIso F.rightDerivedFunctorPlusOnInjectivesUnit).symm

/-- A bounded-below right derived functor of an additive functor is additive. -/
instance rightDerivedFunctorPlusAdditive : F.rightDerivedFunctorPlus.Additive := by
  let _ : (HomotopyCategory.Plus.injectiveToDerived C ⋙
      F.rightDerivedFunctorPlus).Additive :=
    Functor.additive_of_iso F.rightDerivedFunctorPlusOnInjectivesIso.symm
  exact Functor.additive_of_full_essSurj_comp
    (HomotopyCategory.Plus.injectiveToDerived C) F.rightDerivedFunctorPlus

instance rightDerivedFunctorPlusInjectiveLifting :
    Localization.Lifting (HomotopyCategory.Plus.injectiveToDerived C)
      (MorphismProperty.isomorphisms (HomotopyCategory.Plus (InjectiveObject C)))
      F.rightDerivedFunctorPlusOnInjectives F.rightDerivedFunctorPlus :=
  ⟨F.rightDerivedFunctorPlusOnInjectivesIso⟩

end CategoryTheory.Functor
