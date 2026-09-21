/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SheafCohomology
public import Other.Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Topology.Sheaves.Abelian

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Cohomology with support in a closed set, via the pushforward of the constant sheaf

An earlier model: `Extⁿ(i_* ℤ_Z, F)` for the inclusion `i : Z → X` of a closed subset, and
compactly supported cohomology as the colimit over compact closed subsets.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace

universe u

/-- Let `X` be a topological space. This is the type of subsets of `X` that are both compact and
closed, ordered by inclusion. Closedness is included separately because `X` need not be
Hausdorff. -/
abbrev TopologicalSpace.CompactCloseds (X : Type u) [TopologicalSpace X] :=
  {K : Closeds X // IsCompact (K : Set X)}

namespace TopologicalSpace.CompactCloseds

variable (X : Type u) [TopologicalSpace X]

instance : Nonempty (CompactCloseds X) := ⟨⟨⊥, isCompact_empty⟩⟩

instance : IsFiltered (CompactCloseds X) where
  cocone_objs K L :=
    ⟨⟨K.1 ⊔ L.1, K.2.union L.2⟩,
      homOfLE (show K.1 ≤ K.1 ⊔ L.1 from le_sup_left),
      homOfLE (show L.1 ≤ K.1 ⊔ L.1 from le_sup_right), trivial⟩
  cocone_maps _ L _ _ := ⟨L, 𝟙 _, Subsingleton.elim _ _⟩

/-- Forget the compactness proof of a compact closed subset. -/
def inclusion : CompactCloseds X ⥤ Closeds X where
  obj K := K.1
  map f := homOfLE (leOfHom f)

/-- The whole space as a compact closed support. -/
def univ [CompactSpace X] : CompactCloseds X := ⟨⊤, isCompact_univ⟩

end TopologicalSpace.CompactCloseds

namespace TopCat.Sheaf

open _root_.Opens

variable (X : TopCat.{u})

/-- The inclusion of a closed subspace. -/
def closedInclusion (Z : Closeds X) : TopCat.of Z ⟶ X :=
  TopCat.subtypeInclusion X (Z : Set X)

/-- The integer sheaf on a closed subspace, pushed forward to the ambient space. -/
def supportIntegerSheaf (Z : Closeds X) :
    CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u} :=
  (pushforward AddCommGrpCat (closedInclusion X Z)).obj 𝓒(↧Z; ULift.{u} ℤ)

/-- Restriction from a larger closed support to a smaller one. -/
def supportIntegerSheafMap {Z W : Closeds X} (h : Z ≤ W) :
    supportIntegerSheaf X W ⟶ supportIntegerSheaf X Z :=
  (pushforward AddCommGrpCat (closedInclusion X W)).map
    (constantRestriction
      (TopCat.ofHom ⟨fun z : Z => (⟨z.1, h z.2⟩ : W),
        continuous_subtype_val.subtype_mk _⟩) (AddCommGrpCat.of (ULift.{u} ℤ)))

@[simp]
lemma supportIntegerSheafMap_refl (Z : Closeds X) :
    supportIntegerSheafMap X (le_refl Z) = 𝟙 _ := by
  change (pushforward AddCommGrpCat (closedInclusion X Z)).map
    (constantRestriction (𝟙 (TopCat.of Z)) _) = _
  rw [constantRestriction_id]
  rfl

lemma supportIntegerSheafMap_trans {Z W V : Closeds X} (hZW : Z ≤ W) (hWV : W ≤ V) :
    supportIntegerSheafMap X (hZW.trans hWV) =
      supportIntegerSheafMap X hWV ≫ supportIntegerSheafMap X hZW := by
  let f : TopCat.of Z ⟶ TopCat.of W :=
    TopCat.ofHom ⟨fun z => ⟨z.1, hZW z.2⟩, continuous_subtype_val.subtype_mk _⟩
  let g : TopCat.of W ⟶ TopCat.of V :=
    TopCat.ofHom ⟨fun w => ⟨w.1, hWV w.2⟩, continuous_subtype_val.subtype_mk _⟩
  change (pushforward AddCommGrpCat (closedInclusion X V)).map
    (constantRestriction (f ≫ g) _) = _
  rw [constantRestriction_comp]
  rfl

/-- The contravariant diagram of integer sheaves on closed supports. -/
def supportIntegerSheafFunctor :
    (Closeds X)ᵒᵖ ⥤
      CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u} where
  obj Z := supportIntegerSheaf X Z.unop
  map f := supportIntegerSheafMap X (leOfHom f.unop)
  map_id Z := supportIntegerSheafMap_refl X Z.unop
  map_comp f g := supportIntegerSheafMap_trans X (leOfHom g.unop) (leOfHom f.unop)

local instance :
    HasExt.{u} (CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) :=
  hasExt_of_enoughInjectives (CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u})

/-- Sheaf cohomology with support in a closed subset, defined using Mathlib's Ext. -/
abbrev cohomologyWithSupport (Z : Closeds X)
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :=
  Ext (supportIntegerSheaf X Z) F n


instance (Z : Closeds X)
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    AddCommGroup (cohomologyWithSupport X Z F n) :=
  inferInstanceAs (AddCommGroup (Ext (supportIntegerSheaf X Z) F n))

instance (Z : Closeds X) (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u})
    [Injective F] (n : ℕ) : Subsingleton (cohomologyWithSupport X Z F (n + 1)) :=
  Ext.subsingleton_of_injective _ _ n

/-- Cohomology with closed support, functorial in both support and coefficients. -/
def cohomologyWithSupportFunctor (n : ℕ) :
    Closeds X ⥤ CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (supportIntegerSheafFunctor X).rightOp ⋙ extFunctor n

/-- The diagram of cohomology groups indexed by compact closed supports. -/
def compactSupportDiagram
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    CompactCloseds X ⥤ AddCommGrpCat.{u} :=
  ((CompactCloseds.inclusion X ⋙ cohomologyWithSupportFunctor X n).flip).obj F

/-- Compactly supported cohomology, functorial in the coefficient sheaf. -/
def compactlySupportedCohomologyFunctor (n : ℕ) :
    CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (CompactCloseds.inclusion X ⋙ cohomologyWithSupportFunctor X n).flip ⋙ colim

/-- Compactly supported sheaf cohomology as a filtered colimit of Ext groups. -/
abbrev compactlySupportedCohomology
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    AddCommGrpCat.{u} :=
  (compactlySupportedCohomologyFunctor X n).obj F

/-- `H_c^n(X; F)` is compactly supported sheaf cohomology of `X` in degree `n` with coefficients
in the sheaf `F`. -/
scoped notation:max "H_c^" n:max "(" X "; " F ")" => compactlySupportedCohomology X F n

/-- A class with specified compact closed support defines a compactly supported class. -/
def toCompactlySupportedCohomology (K : CompactCloseds X)
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    AddCommGrpCat.of (cohomologyWithSupport X K.1 F n) ⟶
      compactlySupportedCohomology X F n :=
  colimit.ι (compactSupportDiagram X F n) K

@[reassoc (attr := simp)]
lemma toCompactlySupportedCohomology_enlarge {K L : CompactCloseds X} (h : K ≤ L)
    (F : CategoryTheory.Sheaf 𝓖[X] AddCommGrpCat.{u}) (n : ℕ) :
    (compactSupportDiagram X F n).map (homOfLE h) ≫
        toCompactlySupportedCohomology X L F n =
      toCompactlySupportedCohomology X K F n :=
  colimit.w _ _

end TopCat.Sheaf

end
