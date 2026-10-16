/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Natural transformations on bounded-below right derived functors

A natural transformation of additive functors induces a transformation of their
right derived functors. The construction uses the derived universal property,
and its compatibility with the derived units is proved. This supplies, for
example, the canonical support-enlargement and forget-support maps.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]

variable [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- Compatibility with the derived units on every bounded-below homotopy complex. -/
@[reassoc (attr := simp)]
theorem rightDerivedFunctorPlus_unit (α : F ⟶ G) :
    F.rightDerivedFunctorPlusUnith ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh α.rightDerivedFunctorPlus =
      Functor.whiskerRight α.mapHomotopyCategoryPlus DerivedCategory.Plus.Qh ≫
        G.rightDerivedFunctorPlusUnith :=
  α.rightDerivedFunctorPlus_fach

/-- The pointwise form pins the derived transformation to the coefficient transformation
when computing on an injective resolution. -/
@[reassoc (attr := simp)]
theorem rightDerivedFunctorPlus_unit_app (α : F ⟶ G)
    (K : HomotopyCategory.Plus C) :
    F.rightDerivedFunctorPlusUnith.app K ≫
        α.rightDerivedFunctorPlus.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map (α.mapHomotopyCategoryPlus.app K) ≫
        G.rightDerivedFunctorPlusUnith.app K :=
  α.rightDerivedFunctorPlus_fach_app K

end CategoryTheory.NatTrans

namespace CategoryTheory.NatIso

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- Let `F,G : C → D` be additive functors between abelian categories with derived categories, and
assume `C` has enough injectives. A natural isomorphism `e : F ≅ G` induces this isomorphism `RF
≅ RG` on bounded-below derived categories, by applying `e` degreewise to injective resolutions. -/
def rightDerivedFunctorPlus (e : F ≅ G) :
    F.rightDerivedFunctorPlus ≅ G.rightDerivedFunctorPlus where
  hom := e.hom.rightDerivedFunctorPlus
  inv := e.inv.rightDerivedFunctorPlus
  hom_inv_id := by
    rw [← NatTrans.rightDerivedFunctorPlus_comp, e.hom_inv_id,
      NatTrans.rightDerivedFunctorPlus_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerivedFunctorPlus_comp, e.inv_hom_id,
      NatTrans.rightDerivedFunctorPlus_id]

end CategoryTheory.NatIso
