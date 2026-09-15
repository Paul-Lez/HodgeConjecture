/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Shift.Localization

/-!
# Coherent shifts on bounded-below right derived functors

The bounded-below homotopy category of injective objects is equivalent to the bounded-below
derived category. We descend the existing coherent shifts through this equivalence using
Mathlib's localization construction.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace HomotopyCategory.Plus

variable (C : Type*) [Category* C] [Abelian C] [HasDerivedCategory C]

instance : (injectiveToDerived C).CommShift ℤ :=
  inferInstanceAs
    (((InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).CommShift ℤ)

end HomotopyCategory.Plus

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

instance : F.rightDerivedFunctorPlusOnInjectives.CommShift ℤ :=
  inferInstanceAs
    (((InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙
      F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).CommShift ℤ)

/-- Coherent shift compatibility of the actual bounded-below right derived functor. Its zero and
addition coherence laws are inherited by localization from the termwise complex-level shift
compatibility. -/
instance rightDerivedFunctorPlusCommShift : F.rightDerivedFunctorPlus.CommShift ℤ :=
  Functor.commShiftOfLocalization (HomotopyCategory.Plus.injectiveToDerived C)
    (MorphismProperty.isomorphisms (HomotopyCategory.Plus (InjectiveObject C))) ℤ
    F.rightDerivedFunctorPlusOnInjectives F.rightDerivedFunctorPlus

/-- The injective-resolution comparison is compatible with the constructed coherent shifts. -/
instance rightDerivedFunctorPlusOnInjectivesIso_commShift :
    NatTrans.CommShift F.rightDerivedFunctorPlusOnInjectivesIso.hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization
    (HomotopyCategory.Plus.injectiveToDerived C)
    (MorphismProperty.isomorphisms (HomotopyCategory.Plus (InjectiveObject C))) ℤ
    F.rightDerivedFunctorPlusOnInjectives F.rightDerivedFunctorPlus

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Compatibility with the derived unit after restriction to injective complexes. -/
instance rightDerivedFunctorPlusUnit_whiskerLeft_injectives_commShift :
    NatTrans.CommShift (whiskerLeft (InjectiveObject.ι C).mapHomotopyCategoryPlus
      F.rightDerivedFunctorPlusUnit) ℤ := by
  have : NatTrans.CommShift F.rightDerivedFunctorPlusOnInjectivesUnit ℤ :=
    inferInstanceAs (NatTrans.CommShift F.rightDerivedFunctorPlusOnInjectivesIso.inv ℤ)
  have h : F.rightDerivedFunctorPlusOnInjectivesUnit ≫ (Functor.associator _ _ _).hom =
      whiskerLeft (InjectiveObject.ι C).mapHomotopyCategoryPlus
        F.rightDerivedFunctorPlusUnit := by
    simp [rightDerivedFunctorPlusOnInjectivesUnit]
  rw [← h]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The full right-derived unit commutes with the constructed coherent shifts, including on
complexes which are not termwise injective. -/
instance rightDerivedFunctorPlusUnitCommShift :
    NatTrans.CommShift F.rightDerivedFunctorPlusUnit ℤ where
  shift_comm a := by
    apply HomotopyCategory.Plus.natTrans_ext_on_injectives C
    · intro K L f hf
      have : IsIso (DerivedCategory.Plus.Qh.map f) :=
        Localization.inverts DerivedCategory.Plus.Qh
          (HomotopyCategory.Plus.quasiIso C) f hf
      change IsIso ((shiftFunctor (DerivedCategory.Plus D) a).map
        (F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map f)))
      infer_instance
    · intro K
      let incl := (InjectiveObject.ι C).mapHomotopyCategoryPlus
      have h := NatTrans.shift_app_comm
        (whiskerLeft incl F.rightDerivedFunctorPlusUnit) a K
      simp only [Functor.commShiftIso_comp_hom_app, whiskerLeft_app, Category.assoc] at h
      rw [← F.rightDerivedFunctorPlusUnit.naturality_assoc] at h
      apply (cancel_epi ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map
        ((incl.commShiftIso a).hom.app K))).1
      simpa only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
        Functor.commShiftIso_comp_hom_app, Category.assoc] using h

end CategoryTheory.Functor
