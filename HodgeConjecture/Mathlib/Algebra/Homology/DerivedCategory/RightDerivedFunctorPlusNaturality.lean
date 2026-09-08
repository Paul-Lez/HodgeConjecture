/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Natural transformations on bounded-below right derived functors

A natural transformation of additive functors induces a transformation of their
actual right derived functors. The construction uses the derived universal property,
and its compatibility with the actual derived units is proved. This supplies, for
example, the canonical support-enlargement and forget-support maps.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]

set_option backward.isDefEq.respectTransparency false in
/-- Apply a natural transformation of additive functors to bounded-below homotopy complexes. -/
def mapHomotopyCategoryPlus (α : F ⟶ G) :
    F.mapHomotopyCategoryPlus ⟶ G.mapHomotopyCategoryPlus where
  app K := ObjectProperty.homMk ((α.mapHomotopyCategory (.up ℤ)).app K.obj)
  naturality K L f := by
    ext
    exact (α.mapHomotopyCategory (.up ℤ)).naturality f.hom

@[simp]
theorem mapHomotopyCategoryPlus_id (F : C ⥤ D) [F.Additive] :
    mapHomotopyCategoryPlus (𝟙 F) = 𝟙 F.mapHomotopyCategoryPlus := by
  ext K
  simp only [mapHomotopyCategoryPlus, mapHomotopyCategory_id, NatTrans.id_app]
  rfl

@[simp]
theorem mapHomotopyCategoryPlus_comp (α : F ⟶ G) (β : G ⟶ H) :
    mapHomotopyCategoryPlus (α ≫ β) =
      mapHomotopyCategoryPlus α ≫ mapHomotopyCategoryPlus β := by
  ext K
  simp only [mapHomotopyCategoryPlus, mapHomotopyCategory_comp, NatTrans.comp_app]
  rfl

variable [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- The transformation of the actual bounded-below right derived functors, obtained
from the universal property, not supplied as an extra comparison datum. -/
def rightDerivedFunctorPlus (α : F ⟶ G) :
    F.rightDerivedFunctorPlus ⟶ G.rightDerivedFunctorPlus :=
  Functor.rightDerivedNatTrans F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlusUnit
      (HomotopyCategory.Plus.quasiIso C)
        (Functor.whiskerRight α.mapHomotopyCategoryPlus DerivedCategory.Plus.Qh)

/-- Compatibility with the actual derived units on every bounded-below homotopy complex. -/
@[reassoc (attr := simp)]
theorem rightDerivedFunctorPlus_unit (α : F ⟶ G) :
    F.rightDerivedFunctorPlusUnit ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh α.rightDerivedFunctorPlus =
      Functor.whiskerRight α.mapHomotopyCategoryPlus DerivedCategory.Plus.Qh ≫
        G.rightDerivedFunctorPlusUnit :=
  Functor.rightDerivedNatTrans_fac _ _ _ _ _ _

/-- The pointwise form pins the derived transformation to the coefficient transformation
when computing on an injective resolution. -/
@[reassoc (attr := simp)]
theorem rightDerivedFunctorPlus_unit_app (α : F ⟶ G)
    (K : HomotopyCategory.Plus C) :
    F.rightDerivedFunctorPlusUnit.app K ≫
        α.rightDerivedFunctorPlus.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map (α.mapHomotopyCategoryPlus.app K) ≫
        G.rightDerivedFunctorPlusUnit.app K :=
  Functor.rightDerivedNatTrans_app _ _ _ _ _ _ _

@[simp]
theorem rightDerivedFunctorPlus_id (F : C ⥤ D) [F.Additive] :
    rightDerivedFunctorPlus (𝟙 F) = 𝟙 F.rightDerivedFunctorPlus := by
  simp [rightDerivedFunctorPlus]

@[simp]
theorem rightDerivedFunctorPlus_comp (α : F ⟶ G) (β : G ⟶ H) :
    rightDerivedFunctorPlus (α ≫ β) =
      rightDerivedFunctorPlus α ≫ rightDerivedFunctorPlus β := by
  simp [rightDerivedFunctorPlus]

end CategoryTheory.NatTrans
