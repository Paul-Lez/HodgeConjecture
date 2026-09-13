/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.DerivedSections

/-!
# Concrete sheaf sections with support and their right derived functor

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Support.DerivedSections`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- A morphism of sheaves whose restriction to `U` is zero factors canonically
through the sheaf of sections supported outside `U`. -/
def liftSheafSectionsSupportedOutside (U : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hf : f ≫ (toOpenRestrictionPushforward X U).app G = 0) :
    F ⟶ (sheafSectionsSupportedOutside X U).obj G :=
  kernel.lift _ f hf

@[reassoc (attr := simp)]
lemma liftSheafSectionsSupportedOutside_inclusion (U : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hf : f ≫ (toOpenRestrictionPushforward X U).app G = 0) :
    liftSheafSectionsSupportedOutside X U f hf ≫
      (sheafSectionsSupportedOutsideInclusion X U).app G = f :=
  kernel.lift_ι _ _ _

/-- On every ambient open set, supported sections are exactly the kernel of
restriction to its intersection with `U`. This is the canonical kernel
comparison, not a supplied equivalence. -/
def sheafSectionsSupportedOutsideOnOpenIso (U V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    ((sheafSectionsSupportedOutside X U).obj F).obj.obj (op V) ≅
      kernel (((toOpenRestrictionPushforward X U).app F).hom.app (op V)) :=
  let ev : Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
      (evaluation _ AddCommGrpCat).obj (op V)
  letI : ev.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  letI : PreservesLimitsOfShape WalkingParallelPair ev :=
    comp_preservesLimitsOfShape
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V))
  PreservesKernel.iso ev ((toOpenRestrictionPushforward X U).app F)

/-- The kernel comparison preserves the actual inclusion of supported sections
into all sections. -/
@[reassoc (attr := simp)]
lemma sheafSectionsSupportedOutsideOnOpenIso_hom_ι (U V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (sheafSectionsSupportedOutsideOnOpenIso X U V F).hom ≫
      kernel.ι (((toOpenRestrictionPushforward X U).app F).hom.app (op V)) =
        ((sheafSectionsSupportedOutsideInclusion X U).app F).hom.app (op V) := by
  let ev : Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
      (evaluation _ AddCommGrpCat).obj (op V)
  let _ : ev.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let _ : PreservesLimitsOfShape WalkingParallelPair ev :=
    comp_preservesLimitsOfShape
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V))
  change (PreservesKernel.iso ev ((toOpenRestrictionPushforward X U).app F)).hom ≫
    _ = _
  rw [PreservesKernel.iso_hom]
  exact kernelComparison_comp_ι ((toOpenRestrictionPushforward X U).app F) ev

/-- With no restriction imposed, the support-sheaf inclusion is canonically an
isomorphism with the original coefficient sheaf. -/
def sheafSectionsSupportedOutsideBotIso :
    sheafSectionsSupportedOutside X ⊥ ≅ 𝟭 (Sheaf AddCommGrpCat.{u} X) :=
  NatIso.ofComponents
    (fun F => asIso ((sheafSectionsSupportedOutsideInclusion X ⊥).app F))
    (fun f => (sheafSectionsSupportedOutsideInclusion X ⊥).naturality f)

/-- The sheaf-valued sections-with-support functor for a closed support. -/
def sheafSectionsWithClosedSupport (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X :=
  sheafSectionsSupportedOutside X Z.compl

instance (Z : Closeds X) : (sheafSectionsWithClosedSupport X Z).Additive :=
  inferInstanceAs (sheafSectionsSupportedOutside X Z.compl).Additive

/-- Sections supported on the whole space are all sections, through the actual
support-forgetting inclusion. -/
def sheafSectionsWithClosedSupportTopIso :
    sheafSectionsWithClosedSupport X ⊤ ≅ 𝟭 (Sheaf AddCommGrpCat.{u} X) := by
  have h : (⊤ : Closeds X).compl = ⊥ := by ext; simp
  simpa only [sheafSectionsWithClosedSupport, h] using
    sheafSectionsSupportedOutsideBotIso X

/-- Global sections supported in a closed subset, obtained by evaluating the
concrete support sheaf on the whole ambient space. -/
def closedSupportSections (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  sheafSectionsWithClosedSupport X Z ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
    (evaluation _ AddCommGrpCat).obj (op ⊤)

instance (Z : Closeds X) : (closedSupportSections X Z).Additive where
  map_add {F G} f g :=
    congrArg (fun h : (sheafSectionsWithClosedSupport X Z).obj F ⟶
        (sheafSectionsWithClosedSupport X Z).obj G => h.hom.app (op ⊤))
      ((sheafSectionsWithClosedSupport X Z).map_add (f := f) (g := g))

attribute [local instance] supportSheafHasDerivedCategory

attribute [local instance] supportGroupsHasDerivedCategory

/-- The genuine right derived sheaf sections-with-support functor on bounded-below
complexes. Enough injectives is furnished by the Grothendieck abelian category of
abelian sheaves, not supplied as mathematical data. -/
def derivedSheafSectionsWithClosedSupport (Z : Closeds X) :
    DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X) ⥤
      DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X) :=
  (sheafSectionsWithClosedSupport X Z).rightDerivedFunctorPlus

/-- The canonical comparison from termwise sections with support to their derived
functor. -/
def derivedSheafSectionsWithClosedSupportUnit (Z : Closeds X) :
    (sheafSectionsWithClosedSupport X Z).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ derivedSheafSectionsWithClosedSupport X Z :=
  (sheafSectionsWithClosedSupport X Z).rightDerivedFunctorPlusUnit

/-- This construction satisfies Mathlib's universal property of a right derived
functor; it is not merely a named candidate endofunctor. -/
instance derivedSheafSectionsWithClosedSupport_isRightDerivedFunctor (Z : Closeds X) :
    (derivedSheafSectionsWithClosedSupport X Z).IsRightDerivedFunctor
      (derivedSheafSectionsWithClosedSupportUnit X Z)
      (HomotopyCategory.Plus.quasiIso (Sheaf AddCommGrpCat.{u} X)) := by
  dsimp only [derivedSheafSectionsWithClosedSupport,
    derivedSheafSectionsWithClosedSupportUnit]
  infer_instance

/-- The group-valued derived sections-with-support functor `RΓ_Z` on
bounded-below complexes. This is derived from the actual functor of global
sections vanishing on the complement. -/
def derivedClosedSupportSections (Z : Closeds X) :
    DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u} :=
  (closedSupportSections X Z).rightDerivedFunctorPlus

/-- The canonical unit defining group-valued derived sections with support. -/
def derivedClosedSupportSectionsUnit (Z : Closeds X) :
    (closedSupportSections X Z).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ derivedClosedSupportSections X Z :=
  (closedSupportSections X Z).rightDerivedFunctorPlusUnit

/-- Group-valued supported sections satisfy the universal property of their
right derived functor. -/
instance derivedClosedSupportSections_isRightDerivedFunctor (Z : Closeds X) :
    (derivedClosedSupportSections X Z).IsRightDerivedFunctor
      (derivedClosedSupportSectionsUnit X Z)
      (HomotopyCategory.Plus.quasiIso (Sheaf AddCommGrpCat.{u} X)) := by
  dsimp only [derivedClosedSupportSections, derivedClosedSupportSectionsUnit]
  infer_instance

end TopCat.Sheaf

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- Uniqueness in the universal property of supported sections. -/
lemma liftSheafSectionsSupportedOutside_unique (U : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hf : f ≫ (toOpenRestrictionPushforward X U).app G = 0)
    (g : F ⟶ (sheafSectionsSupportedOutside X U).obj G)
    (hg : g ≫ (sheafSectionsSupportedOutsideInclusion X U).app G = f) :
    g = liftSheafSectionsSupportedOutside X U f hf :=
  (cancel_mono (kernel.ι _)).1 (hg.trans (kernel.lift_ι _ _ _).symm)

attribute [local instance] supportSheafHasDerivedCategory

attribute [local instance] supportGroupsHasDerivedCategory

end TopCat.Sheaf
