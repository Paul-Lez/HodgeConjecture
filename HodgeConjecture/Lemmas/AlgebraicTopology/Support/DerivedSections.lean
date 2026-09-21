/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.DerivedSections
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sets.Closeds

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

@[reassoc (attr := simp)]
lemma sheafSectionsSupportedOutsideInclusion_restriction (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (sheafSectionsSupportedOutsideInclusion X U).app F ≫
      (toOpenRestrictionPushforward X U).app F = 0 :=
  kernel.condition _

end TopCat.Sheaf
end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- Let `U` be open in a topological space `X` and `f : F → G` a morphism of sheaves of abelian
groups whose restriction to `U` is zero. This is the unique factorization of `f` through the
subsheaf of `G` consisting of sections supported in `X \ U`. -/
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

/-- Let `X` be a topological space, `U,V ⊆ X` open, and `F` a sheaf of abelian groups. This
identifies sections on `V` of the subsheaf supported in `X \ U` with `ker(F(V) → F(V ∩ U))`,
where the map is restriction. -/
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

/-- The kernel comparison preserves the inclusion of supported sections
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
  exact kernelComparison_comp_ι ((toOpenRestrictionPushforward X U).app F) ev

/-- Let `X` be a topological space and `Z ⊆ X` closed. This functor sends a sheaf of abelian groups
`F` to the subsheaf `Γ_Z(F)` whose sections on `V` are those elements of `F(V)` that vanish on
`V \ Z`. It is the kernel of restriction to the direct image from `X \ Z`. -/
def sheafSectionsWithClosedSupport (Z : Closeds X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X :=
  sheafSectionsSupportedOutside X Z.compl

instance (Z : Closeds X) : (sheafSectionsWithClosedSupport X Z).Additive :=
  inferInstanceAs (sheafSectionsSupportedOutside X Z.compl).Additive

/-- Let `X` be a topological space and `Z ⊆ X` closed. This functor sends a sheaf of abelian groups
`F` to `Γ_Z(X,F) = ker(F(X) → F(X \ Z))`, the group of global sections whose support is
contained in `Z`. -/
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

/-- Let `X` be a topological space and `Z ⊆ X` closed. This right derived functor on bounded-below
complexes of sheaves of abelian groups replaces a complex by an injective resolution and then
takes, in every degree, the subsheaf of sections vanishing off `Z`. Its values are complexes of
sheaves on `X` in the bounded-below derived category. -/
def derivedSheafSectionsWithClosedSupport (Z : Closeds X) :
    DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X) ⥤
      DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X) :=
  (sheafSectionsWithClosedSupport X Z).rightDerivedFunctorPlus

/-- Let `X` be a topological space and `Z ⊆ X` closed. For a bounded-below complex `K` of sheaves of
abelian groups, the resolution map `K → I` induces a map from the termwise subsheaves of
sections supported in `Z` to the corresponding subsheaves of `I`. This is the resulting natural
comparison with the right derived sheaf functor. -/
def derivedSheafSectionsWithClosedSupportUnit (Z : Closeds X) :
    (sheafSectionsWithClosedSupport X Z).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ derivedSheafSectionsWithClosedSupport X Z :=
  (sheafSectionsWithClosedSupport X Z).rightDerivedFunctorPlusUnit

/-- The construction satisfies Mathlib's universal property of a right derived functor. -/
instance derivedSheafSectionsWithClosedSupport_isRightDerivedFunctor (Z : Closeds X) :
    (derivedSheafSectionsWithClosedSupport X Z).IsRightDerivedFunctor
      (derivedSheafSectionsWithClosedSupportUnit X Z)
      (HomotopyCategory.Plus.quasiIso (Sheaf AddCommGrpCat.{u} X)) := by
  dsimp only [derivedSheafSectionsWithClosedSupport,
    derivedSheafSectionsWithClosedSupportUnit]
  infer_instance

/-- Let `X` be a topological space and `Z ⊆ X` closed. The functor `RΓ_Z(X,-)` from bounded-below
sheaf complexes to the bounded-below derived category of abelian groups is computed by an
injective resolution `I`: in degree `q`, take global sections of `I^q` vanishing on `X \ Z`. Its
degree-`n` cohomology is cohomology with support in `Z`. -/
def derivedClosedSupportSections (Z : Closeds X) :
    DerivedCategory.Plus (Sheaf AddCommGrpCat.{u} X) ⥤
      DerivedCategory.Plus AddCommGrpCat.{u} :=
  (closedSupportSections X Z).rightDerivedFunctorPlus

/-- Let `X` be a topological space and `Z ⊆ X` closed. For a bounded-below complex `K` of sheaves of
abelian groups, this natural map compares the complex of global sections of `K` supported in `Z`
with its right derived value `RΓ_Z(X,K)`. It is induced by mapping `K` to an injective
resolution. -/
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
