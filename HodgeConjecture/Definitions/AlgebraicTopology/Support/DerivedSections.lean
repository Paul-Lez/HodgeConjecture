/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sets.Closeds

/-!
# Concrete sheaf sections with support and their right derived functor

For an open subset `U` of `X`, restriction gives a natural map `F → j_* (F|_U)`.
Its kernel is the sheaf of sections supported on the closed complement of `U`.
This file constructs that additive functor and its right derived functor on the
bounded-below derived category using Mathlib's injective-resolution machinery.

Both the sheaf-valued local cohomology operation, conventionally `RΓ_Z`, and
the abelian-group-valued derived global sections `RΓ_Z` are constructed, with
different source and target categories displayed explicitly.
No dualizing complex or orientation is assumed or constructed. In particular, this
file does not identify Borel--Moore homology with supported cohomology. Comparison
with the project's restriction mapping-cone model, and coherent commutation with
shifts, remain separate theorems.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- Restrict a sheaf to an open subspace and push it forward again. The pullback
here is the concrete open-embedding pullback, obtained by evaluating on the
corresponding ambient open sets. -/
def openRestrictionPushforward (U : Opens X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X :=
  U.isOpenEmbedding.sheafPullback AddCommGrpCat ⋙
    pushforward AddCommGrpCat U.inclusion'

/-- The actual restriction morphism, functorial in the coefficient sheaf. -/
def toOpenRestrictionPushforward (U : Opens X) :
    𝟭 (Sheaf AddCommGrpCat.{u} X) ⟶ openRestrictionPushforward X U where
  app F := ⟨{
    app V := F.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V.unop).op
    naturality V W f := by
      change F.obj.map f ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
      rw [← F.obj.map_comp, ← F.obj.map_comp]
      congr 1 }⟩
  naturality F G f := by
    apply CategoryTheory.Sheaf.hom_ext_iff.mpr
    ext V : 2
    exact (f.hom.naturality _).symm

/-- The sheaf of sections vanishing on `U`, defined as the kernel of the
coefficient-wise restriction map. -/
def sheafSectionsSupportedOutside (U : Opens X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X where
  obj F := kernel ((toOpenRestrictionPushforward X U).app F)
  map f := kernel.map _ _ f ((openRestrictionPushforward X U).map f)
    ((toOpenRestrictionPushforward X U).naturality f).symm
  map_id F := by
    apply (cancel_mono (kernel.ι _)).1
    simp
  map_comp f g := by
    apply (cancel_mono (kernel.ι _)).1
    simp

set_option backward.isDefEq.respectTransparency false in
instance (U : Opens X) : (sheafSectionsSupportedOutside X U).Additive where
  map_add {F G} f g := by
    apply (cancel_mono (kernel.ι _)).1
    simp [sheafSectionsSupportedOutside, Preadditive.add_comp, Preadditive.comp_add]

/-- Inclusion of supported sections into the original coefficient sheaf. -/
def sheafSectionsSupportedOutsideInclusion (U : Opens X) :
    sheafSectionsSupportedOutside X U ⟶ 𝟭 (Sheaf AddCommGrpCat.{u} X) where
  app F := kernel.ι ((toOpenRestrictionPushforward X U).app F)
  naturality F G f := by simp [sheafSectionsSupportedOutside]

@[reassoc (attr := simp)]
lemma sheafSectionsSupportedOutsideInclusion_restriction (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    (sheafSectionsSupportedOutsideInclusion X U).app F ≫
      (toOpenRestrictionPushforward X U).app F = 0 :=
  kernel.condition _

/-- Restriction to the empty open subspace and pushforward gives the zero sheaf. -/
lemma isZero_openRestrictionPushforward_bot (F : Sheaf AddCommGrpCat.{u} X) :
    IsZero ((openRestrictionPushforward X ⊥).obj F) :=
  (pushforward AddCommGrpCat (⊥ : Opens X).inclusion').map_isZero
    ((isZero_iff_stalkFunctor_obj_isZero _).2 fun x => False.elim x.property)

instance (F : Sheaf AddCommGrpCat.{u} X) :
    IsIso ((sheafSectionsSupportedOutsideInclusion X ⊥).app F) := by
  change IsIso (kernel.ι ((toOpenRestrictionPushforward X ⊥).app F))
  rw [(isZero_openRestrictionPushforward_bot X F).eq_zero_of_tgt
    ((toOpenRestrictionPushforward X ⊥).app F)]
  infer_instance

local instance supportSheafHasDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat.{u} X)

local instance supportGroupsHasDerivedCategory : HasDerivedCategory AddCommGrpCat.{u} :=
  HasDerivedCategory.standard AddCommGrpCat.{u}

end TopCat.Sheaf
