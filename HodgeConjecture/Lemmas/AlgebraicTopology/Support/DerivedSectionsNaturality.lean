/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSectionsShift
public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusShiftNaturality

/-!
# Naturality of derived sections with closed support

Support enlargement comes from the actual kernel inclusion, and is then derived by
the universal property. In particular, forgetting support is the map to whole-space
support; no cohomology-level comparison morphism is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- The support-forgetting inclusion is the actual kernel monomorphism. -/
instance sectionsSupportedOutsideInclusion_mono (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    Mono ((sectionsSupportedOutsideInclusion X U).app F) :=
  inferInstanceAs (Mono (kernel.ι ((toOpenRestrictionPushforward X U).app F)))

/-- The ambient open used when restricting to `U` and pushing forward again. -/
abbrev openRestrictionImage (U W : Opens X) : Opens X :=
  U.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map U.inclusion').obj W)

theorem openRestrictionImage_mono {U V : Opens X} (h : V ≤ U) (W : Opens X) :
    openRestrictionImage X V W ≤ openRestrictionImage X U W := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨⟨y.1, h y.2⟩, hy, rfl⟩

/-- Further restriction from `U` to `V ⊆ U`, on the actual open pushforward functors. -/
def openRestrictionPushforwardMap {U V : Opens X} (h : V ≤ U) :
    openRestrictionPushforward X U ⟶ openRestrictionPushforward X V where
  app F := ⟨{
    app W := F.obj.map (homOfLE (openRestrictionImage_mono X h W.unop)).op
    naturality W W' f := by
      change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
      rw [← F.obj.map_comp, ← F.obj.map_comp]
      congr 1 }⟩
  naturality F G f := by
    apply CategoryTheory.Sheaf.hom_ext_iff.mpr
    ext W : 2
    exact (f.hom.naturality _).symm

/-- Further restriction agrees with direct restriction from the ambient sheaf. -/
@[reassoc (attr := simp)]
theorem toOpenRestrictionPushforward_comp {U V : Opens X} (h : V ≤ U) :
    toOpenRestrictionPushforward X U ≫ openRestrictionPushforwardMap X h =
      toOpenRestrictionPushforward X V := by
  ext F : 2
  apply CategoryTheory.Sheaf.hom_ext_iff.mpr
  ext W : 2
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  rw [← F.obj.map_comp]
  congr 1

/-- The canonical inclusion of sections supported outside `U` into those supported
outside the smaller open `V`. -/
def sectionsSupportedOutsideMap {U V : Opens X} (h : V ≤ U) :
    sectionsSupportedOutside X U ⟶ sectionsSupportedOutside X V where
  app F := liftSectionsSupportedOutside X V
    ((sectionsSupportedOutsideInclusion X U).app F) (by
      rw [← NatTrans.congr_app (toOpenRestrictionPushforward_comp X h) F]
      simp only [NatTrans.comp_app, ← Category.assoc,
        sectionsSupportedOutsideInclusion_restriction, zero_comp])
  naturality F G f := by
    apply (cancel_mono ((sectionsSupportedOutsideInclusion X V).app G)).1
    simp only [Category.assoc, liftSectionsSupportedOutside_inclusion]
    rw [(sectionsSupportedOutsideInclusion X V).naturality f,
      ← Category.assoc, liftSectionsSupportedOutside_inclusion]
    exact (sectionsSupportedOutsideInclusion X U).naturality f

/-- Support enlargement preserves the actual inclusion into the coefficient sheaf. -/
@[reassoc (attr := simp)]
theorem sectionsSupportedOutsideMap_inclusion {U V : Opens X} (h : V ≤ U) :
    sectionsSupportedOutsideMap X h ≫ sectionsSupportedOutsideInclusion X V =
      sectionsSupportedOutsideInclusion X U := by
  ext F
  exact liftSectionsSupportedOutside_inclusion X V _ _

@[simp]
theorem sectionsSupportedOutsideMap_refl (U : Opens X) :
    sectionsSupportedOutsideMap X (le_refl U) = 𝟙 (sectionsSupportedOutside X U) := by
  ext F
  apply (cancel_mono ((sectionsSupportedOutsideInclusion X U).app F)).1
  simp [sectionsSupportedOutsideMap]

@[reassoc (attr := simp)]
theorem sectionsSupportedOutsideMap_comp {U V W : Opens X}
    (h : V ≤ U) (h' : W ≤ V) :
    sectionsSupportedOutsideMap X h ≫ sectionsSupportedOutsideMap X h' =
      sectionsSupportedOutsideMap X (h'.trans h) := by
  ext F
  apply (cancel_mono ((sectionsSupportedOutsideInclusion X W).app F)).1
  simp [sectionsSupportedOutsideMap]

/-- The coefficient-level support-enlargement map for closed subsets. -/
def sheafSectionsWithClosedSupportMap {Z W : Closeds X} (h : Z ≤ W) :
    sheafSectionsWithClosedSupport X Z ⟶ sheafSectionsWithClosedSupport X W :=
  sectionsSupportedOutsideMap X (show W.compl ≤ Z.compl from fun _ hx hz ↦ hx (h hz))

/-- The actual support-enlargement map on global sections. -/
def closedSupportSectionsMap {Z W : Closeds X} (h : Z ≤ W) :
    closedSupportSections X Z ⟶ closedSupportSections X W :=
  Functor.whiskerRight (sheafSectionsWithClosedSupportMap X h)
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
      (evaluation _ AddCommGrpCat).obj (op ⊤))

@[simp]
theorem closedSupportSectionsMap_refl (Z : Closeds X) :
    closedSupportSectionsMap X (le_refl Z) = 𝟙 (closedSupportSections X Z) := by
  simp [closedSupportSectionsMap, sheafSectionsWithClosedSupportMap]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem closedSupportSectionsMap_comp {Z W T : Closeds X} (h : Z ≤ W) (h' : W ≤ T) :
    closedSupportSectionsMap X h ≫ closedSupportSectionsMap X h' =
      closedSupportSectionsMap X (h.trans h') := by
  simp [closedSupportSectionsMap, sheafSectionsWithClosedSupportMap,
    ← Functor.whiskerRight_comp]

local instance derivedSupportNaturalitySheafDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat.{u} X) := HasDerivedCategory.standard _

local instance derivedSupportNaturalityGroupDerivedCategory :
    HasDerivedCategory AddCommGrpCat.{u} := HasDerivedCategory.standard _

/-- Derived support enlargement, constructed from the actual kernel map. -/
def derivedClosedSupportSectionsMap {Z W : Closeds X} (h : Z ≤ W) :
    derivedClosedSupportSections X Z ⟶ derivedClosedSupportSections X W :=
  (closedSupportSectionsMap X h).rightDerivedFunctorPlus

/-- The actual support-enlargement maps commute with the constructed coherent shifts. -/
instance derivedClosedSupportSectionsMap_commShift {Z W : Closeds X} (h : Z ≤ W) :
    NatTrans.CommShift (derivedClosedSupportSectionsMap X h) ℤ :=
  inferInstanceAs (NatTrans.CommShift (closedSupportSectionsMap X h).rightDerivedFunctorPlus ℤ)

@[simp]
theorem derivedClosedSupportSectionsMap_refl (Z : Closeds X) :
    derivedClosedSupportSectionsMap X (le_refl Z) =
      𝟙 (derivedClosedSupportSections X Z) := by
  simp [derivedClosedSupportSectionsMap, derivedClosedSupportSections]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem derivedClosedSupportSectionsMap_comp {Z W T : Closeds X}
    (h : Z ≤ W) (h' : W ≤ T) :
    derivedClosedSupportSectionsMap X h ≫ derivedClosedSupportSectionsMap X h' =
      derivedClosedSupportSectionsMap X (h.trans h') := by
  simp [derivedClosedSupportSectionsMap, ← NatTrans.rightDerivedFunctorPlus_comp]

/-- The actual derived-unit square identifies the support map on injective resolutions. -/
@[reassoc (attr := simp)]
theorem derivedClosedSupportSectionsMap_unit_app {Z W : Closeds X} (h : Z ≤ W)
    (K : HomotopyCategory.Plus (Sheaf AddCommGrpCat.{u} X)) :
    (derivedClosedSupportSectionsUnit X Z).app K ≫
        (derivedClosedSupportSectionsMap X h).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map
          ((closedSupportSectionsMap X h).mapHomotopyCategoryPlus.app K) ≫
        (derivedClosedSupportSectionsUnit X W).app K :=
  (closedSupportSectionsMap X h).rightDerivedFunctorPlus_unit_app K

end TopCat.Sheaf
