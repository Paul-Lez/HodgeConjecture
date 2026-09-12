/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SheafCohomology

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Topology.Sheaves.Abelian

/-!
# Forgetting a support

Sheaf cohomology with support in a closed subset maps to ordinary sheaf cohomology by forgetting
the support, naturally in the sheaf and compatibly with enlarging the support; on the whole space
the two agree.  Passing to the colimit over compact supports, compactly supported cohomology maps
to ordinary cohomology, and on a compact space the two agree.

The statement of the conjecture uses cohomology with support only through the coniveau
filtration, which never forgets a support, so none of this is needed to state it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace

universe u

namespace TopologicalSpace.CompactCloseds

variable (X : Type u) [TopologicalSpace X]

/-- On a compact space, the whole space is a terminal support. -/
def isTerminalUniv [CompactSpace X] : IsTerminal (univ X) :=
  IsTerminal.ofUniqueHom (fun K => homOfLE (show K.1 ≤ ⊤ from le_top))
    (fun _ _ => Subsingleton.elim _ _)

end TopologicalSpace.CompactCloseds

namespace TopCat.Sheaf

open _root_.Opens

variable (X : TopCat.{u})

local instance :
    HasExt.{u} (CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives (CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u})

/-- Restriction of the ambient integer sheaf to a closed support. -/
def integerToSupport (Z : Closeds X) :
    (constantSheaf 𝓖[X] AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ supportIntegerSheaf X Z :=
  constantRestriction (closedInclusion X Z) _

@[reassoc (attr := simp)]
lemma integerToSupport_map {Z W : Closeds X} (h : Z ≤ W) :
    integerToSupport X W ≫ supportIntegerSheafMap X h = integerToSupport X Z :=
  (constantRestriction_comp (TopCat.ofHom ⟨fun z : Z => (⟨z.1, h z.2⟩ : W),
    continuous_subtype_val.subtype_mk _⟩) (closedInclusion X W) _).symm

/-- The integer sheaf supported on the whole space is the ordinary integer sheaf. -/
def supportIntegerSheafTopIso :
    (constantSheaf 𝓖[X] AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ≅ supportIntegerSheaf X ⊤ where
  hom := integerToSupport X ⊤
  inv := (pushforward AddCommGrpCat (closedInclusion X ⊤)).map
    (constantRestriction
      (TopCat.ofHom ⟨fun x : X => (⟨x, Set.mem_univ x⟩ : (⊤ : Closeds X)),
        continuous_id.subtype_mk _⟩) (AddCommGrpCat.of (ULift.{u} ℤ)))
  hom_inv_id :=
   (constantRestriction_comp
      (TopCat.ofHom ⟨fun x : X => (⟨x, Set.mem_univ x⟩ : (⊤ : Closeds X)),
        continuous_id.subtype_mk _⟩) (closedInclusion X ⊤) _).symm.trans
      (constantRestriction_id X _)
  inv_hom_id := by
    have h := (constantRestriction_comp (closedInclusion X ⊤)
      (TopCat.ofHom ⟨fun x : X => (⟨x, Set.mem_univ x⟩ : (⊤ : Closeds X)),
        continuous_id.subtype_mk _⟩) (AddCommGrpCat.of (ULift.{u} ℤ))).symm.trans
      (constantRestriction_id (TopCat.of (⊤ : Closeds X)) _)
    exact congrArg ((pushforward AddCommGrpCat (closedInclusion X ⊤)).map) h

/-- In degree zero, supported cohomology consists of morphisms from the support integer sheaf. -/
def cohomologyWithSupportZeroEquiv (Z : Closeds X)
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) :
    cohomologyWithSupport X Z F 0 ≃+ (supportIntegerSheaf X Z ⟶ F) :=
  Ext.addEquiv₀

/-- Forget a closed support. -/
def forgetClosedSupport (Z : Closeds X)
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    cohomologyWithSupport X Z F n →+ CategoryTheory.Sheaf.H.{u, u} F n :=
  (Ext.mk₀ (integerToSupport X Z)).precomp F (zero_add n)

/-- Forgetting whole-space support identifies supported cohomology with Mathlib's cohomology. -/
def cohomologyWithSupportTopIso
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    AddCommGrpCat.of (cohomologyWithSupport X ⊤ F n) ≅
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{u, u} F n) :=
  ((extFunctor n).mapIso (supportIntegerSheafTopIso X).op).app F

@[simp]
lemma cohomologyWithSupportTopIso_hom
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    (cohomologyWithSupportTopIso X F n).hom =
      AddCommGrpCat.ofHom (forgetClosedSupport X ⊤ F n) := rfl

@[reassoc]
lemma forgetClosedSupport_naturality (Z : Closeds X)
    {F G : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}}
    (f : F ⟶ G) (n : ℕ) :
    ((cohomologyWithSupportFunctor X n).obj Z).map f ≫
        AddCommGrpCat.ofHom (forgetClosedSupport X Z G n) =
      AddCommGrpCat.ofHom (forgetClosedSupport X Z F n) ≫
        (CategoryTheory.Sheaf.functorH 𝓖[X] n).map f :=
  ((extFunctor n).map (integerToSupport X Z).op).naturality f

@[simp]
lemma forgetClosedSupport_enlarge {Z W : Closeds X} (h : Z ≤ W)
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u})
    (n : ℕ) (α : cohomologyWithSupport X Z F n) :
    forgetClosedSupport X W F n
      (((cohomologyWithSupportFunctor X n).map (homOfLE h)).app F α) =
        forgetClosedSupport X Z F n α := by
  change (Ext.mk₀ (integerToSupport X W)).comp
    ((Ext.mk₀ (supportIntegerSheafMap X h)).comp α (zero_add n)) (zero_add n) = _
  rw [Ext.mk₀_comp_mk₀_assoc, integerToSupport_map]
  rfl

/-- Forgetting each compact support gives a cocone to ordinary sheaf cohomology. -/
def forgetCompactSupportCocone
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    Cocone (compactSupportDiagram X F n) where
  pt := ↧(CategoryTheory.Sheaf.H.{u, u} F n)
  ι :=
    { app K := AddCommGrpCat.ofHom (forgetClosedSupport X K.1 F n)
      naturality K L f := by
        ext α
        exact forgetClosedSupport_enlarge X (leOfHom f) F n α }

/-- The canonical map from compactly supported to ordinary sheaf cohomology. -/
def forgetCompactSupport
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    compactlySupportedCohomology X F n ⟶ ↧(CategoryTheory.Sheaf.H.{u, u} F n) :=
  colimit.desc _ (forgetCompactSupportCocone X F n)

@[reassoc (attr := simp)]
lemma toCompactlySupportedCohomology_forget (K : CompactCloseds X)
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    toCompactlySupportedCohomology X K F n ≫ forgetCompactSupport X F n =
      AddCommGrpCat.ofHom (forgetClosedSupport X K.1 F n) :=
  colimit.ι_desc _ K

set_option maxHeartbeats 800000 in
/-- Forgetting compact support is natural in the coefficient sheaf. -/
def forgetCompactSupportNatTrans (n : ℕ) :
    compactlySupportedCohomologyFunctor X n ⟶
      CategoryTheory.Sheaf.functorH 𝓖[X] n where
  app F := forgetCompactSupport X F n
  naturality F G f := by
    apply colimit.hom_ext
    intro K
    change colimit.ι (compactSupportDiagram X F n) K ≫
        (colim.map
            ((CompactCloseds.inclusion X ⋙ cohomologyWithSupportFunctor X n).flip.map f) ≫
          forgetCompactSupport X G n) = _
    erw [colimit.ι_map_assoc]
    change ((cohomologyWithSupportFunctor X n).obj K.1).map f ≫
        (toCompactlySupportedCohomology X K G n ≫ forgetCompactSupport X G n) =
      toCompactlySupportedCohomology X K F n ≫
        (forgetCompactSupport X F n ≫
          (CategoryTheory.Sheaf.functorH 𝓖[X] n).map f)
    erw [toCompactlySupportedCohomology_forget,
      toCompactlySupportedCohomology_forget_assoc]
    exact forgetClosedSupport_naturality X K.1 f n

/-- On a compact space, compactly supported cohomology is ordinary sheaf cohomology. -/
def compactlySupportedCohomologyIso [CompactSpace X]
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    compactlySupportedCohomology X F n ≅ ↧(CategoryTheory.Sheaf.H.{u, u} F n) :=
  (colimit.isColimit (compactSupportDiagram X F n)).coconePointUniqueUpToIso
    (colimitOfDiagramTerminal (CompactCloseds.isTerminalUniv X)
      (compactSupportDiagram X F n)) ≪≫ cohomologyWithSupportTopIso X F n

@[simp]
lemma compactlySupportedCohomologyIso_hom [CompactSpace X]
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    (compactlySupportedCohomologyIso X F n).hom = forgetCompactSupport X F n := by
  apply colimit.hom_ext
  intro K
  dsimp only [compactlySupportedCohomologyIso, Iso.trans_hom]
  erw [← Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
  rw [cohomologyWithSupportTopIso_hom]
  change _ = toCompactlySupportedCohomology X K F n ≫ forgetCompactSupport X F n
  rw [toCompactlySupportedCohomology_forget]
  ext α
  exact forgetClosedSupport_enlarge X (show K.1 ≤ ⊤ from le_top) F n α

end TopCat.Sheaf
