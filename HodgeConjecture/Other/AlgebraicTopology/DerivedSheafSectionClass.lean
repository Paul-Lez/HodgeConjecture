/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicTopology.DerivedSheafSupportShift
public import HodgeConjecture.Other.AlgebraicTopology.ClosedEmbeddingDerivedPushforward
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!+# Actual sections as classes in bounded-below derived functors

The comparison below sends a section of an additive functor applied to a coefficient
object through the actual right-derived unit. Its source is the literal section group,
identified with the homology of its single complex by the canonical single-complex map.
In particular, a constant-one section can be used without an independently supplied
global-sections or pushforward comparison.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opposite

universe u v w a

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{w} C]

local instance derivedSectionGroupsHasDerivedCategory : HasDerivedCategory AddCommGrpCat.{a} :=
  HasDerivedCategory.standard _

variable (F : C ⥤ AddCommGrpCat.{a}) [F.Additive] (A : C) (n : ℤ)

/-- The single complex commutes with the literal termwise functor, followed by localization.
All comparisons are the standard single-complex and quotient comparisons. -/
def sectionSinglePlusIso :
    (DerivedCategory.Plus.singleFunctor AddCommGrpCat.{a} n).obj (F.obj A) ≅
      DerivedCategory.Plus.Qh.obj
        (F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor C n).obj A)) :=
  DerivedCategory.Plus.ι.preimageIso
    (DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) n).app A).symm ≪≫
        ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{a}).app _).symm)

/-- The actual right-derived unit on a coefficient sheaf in one degree. -/
def derivedSectionSingleUnit :
    (DerivedCategory.Plus.singleFunctor AddCommGrpCat.{a} n).obj (F.obj A) ⟶
      F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C n).obj A) :=
  (sectionSinglePlusIso F A n).hom ≫
    F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor C n).obj A)

/-- A literal section gives a cohomology class through the actual derived unit. -/
def derivedSectionClassMap :
    F.obj A ⟶ (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{a} n).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C n).obj A)) :=
  ((DerivedCategory.singleFunctorCompHomologyFunctorIso AddCommGrpCat.{a} n).app
    (F.obj A)).inv ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{a} n).map
        (derivedSectionSingleUnit F A n)

/-- The section map uses precisely the standard single-complex class and actual unit. -/
lemma derivedSectionClassMap_eq :
    derivedSectionClassMap F A n =
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso AddCommGrpCat.{a} n).app
        (F.obj A)).inv ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{a} n).map
          ((sectionSinglePlusIso F A n).hom ≫
            F.rightDerivedFunctorPlusUnit.app
              ((HomotopyCategory.Plus.singleFunctor C n).obj A)) := rfl

end CategoryTheory.Functor

namespace TopCat.Sheaf

variable {Z X : TopCat.{u}} (i : Z ⟶ X) (hi : IsClosedEmbedding i)

local instance sectionClosedPushSourceDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat.{u} Z) := HasDerivedCategory.standard _

local instance sectionClosedPushTargetDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat.{u} X) := HasDerivedCategory.standard _

/-- Exact closed direct image commutes with the single coefficient complex in `D⁺`. -/
def closedEmbeddingDerivedPushforwardPlusSingleIso
    (F : Sheaf AddCommGrpCat.{u} Z) (n : ℤ) :
    (closedEmbeddingDerivedPushforwardPlus i hi).obj
      ((DerivedCategory.Plus.singleFunctor _ n).obj F) ≅
        (DerivedCategory.Plus.singleFunctor _ n).obj
          ((pushforward AddCommGrpCat.{u} i).obj F) := by
  have h := closedEmbeddingPushforward_preservesFiniteColimits i hi
  exact DerivedCategory.Plus.ι.preimageIso
    (((pushforward AddCommGrpCat.{u} i).mapDerivedCategorySingleFunctor n).app F)

end TopCat.Sheaf
