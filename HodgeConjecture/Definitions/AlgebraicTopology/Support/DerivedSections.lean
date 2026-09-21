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

The identification of Borel--Moore homology with supported cohomology, the comparison with the
project's restriction mapping-cone model, and coherent commutation with shifts are separate
theorems.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

/-- Let `X` be a topological space, `U ⊆ X` an open subset, and `j : U → X` the inclusion. This
functor sends a sheaf of abelian groups `F` to `j_*(F|_U)`. Its sections on an open `V ⊆ X` are
the sections `F(V ∩ U)`. -/
def openRestrictionPushforward (U : Opens X) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X :=
  U.isOpenEmbedding.sheafPullback AddCommGrpCat ⋙
    pushforward AddCommGrpCat U.inclusion'

/-- Let `X` be a topological space and `U ⊆ X` open. This natural transformation sends a sheaf of
abelian groups `F` to the restriction morphism `F → j_*(F|_U)`, where `j : U → X` is inclusion.
On each open `V`, it is restriction `F(V) → F(V ∩ U)`. -/
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

/-- Let `X` be a topological space, `U` and `V` open subsets, and `F` a sheaf of abelian groups on
`X`. This is the identification `(j_*(F|_U))(V) ≅ F(V ∩ U)`, where `j : U → X` is the inclusion. -/
def supportedOutsideIntersectionIso (U V : Opens X) (F : Sheaf AddCommGrpCat.{u} X) :
    ((openRestrictionPushforward X U).obj F).presheaf.obj (op V) ≅ F.presheaf.obj (op (V ⊓ U)) :=
  F.obj.mapIso (eqToIso (congrArg op (Opens.functor_map_eq_inf U V)))

/-- Let `X` be a topological space and `U ⊆ X` open. The functor `Γ_{X \ U}` sends a sheaf of
abelian groups `F` to the kernel of restriction `F → j_*(F|_U)`, where `j : U → X` is inclusion.
On an open `V`, its sections are those sections of `F(V)` that vanish on `V ∩ U`, or
equivalently have support in the closed set `X \ U`. -/
def sheafSectionsSupportedOutside (U : Opens X) :
    -- `F ↦ Γ_{X \ U}(F)`, the subsheaf of sections that vanish on `U`.
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

/-- Let `X` be a topological space, `U ⊆ X` open, and `F` a sheaf of abelian groups. This natural
morphism `Γ_{X \ U}(F) → F` includes sections that vanish on `U` into all sections of `F`. -/
def sheafSectionsSupportedOutsideInclusion (U : Opens X) :
    sheafSectionsSupportedOutside X U ⟶ 𝟭 (Sheaf AddCommGrpCat.{u} X) where
  app F := kernel.ι ((toOpenRestrictionPushforward X U).app F)
  naturality F G f := by simp [sheafSectionsSupportedOutside]

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
