/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.DerivedSections
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.InjectiveFlasque
public import HodgeConjecture.Lemmas.Algebra.Homology.DerivedCategory.MappingCoconeShortExact
/-!
# The localization sequence on injective coefficient complexes

For an injective coefficient sheaf, the kernel defining sections supported outside `U` fits
into a short exact sequence with the coefficient sheaf and its restriction-pushforward, with
surjectivity coming from flasqueness of injective sheaves. The sequence stays short exact
after evaluation on an arbitrary open set, giving the complex of supported sections in the
localization calculation. The comparison with the mapping cocone is a quasi-isomorphism
normalized by its projection to the coefficient complex, and the resulting isomorphisms are
built from the `D⁺` right-derived functors and their canonical units on bounded-below
injective models, then displayed in `D` along the full inclusion `D⁺ → D`.

Identifying these fibers with the constant-rational restriction-cone model requires a normalized
comparison between restriction of the ambient injective model and an independently chosen
injective resolution on the complement. That comparison is a separate statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U : Opens X)

/-- Restriction of a flasque coefficient sheaf is surjective on every open set. -/
instance toOpenRestrictionPushforward_app_epi (F : Sheaf AddCommGrpCat.{u} X)
    [F.IsFlasque] (V : Opens X) :
    Epi (((toOpenRestrictionPushforward X U).app F).hom.app (op V)) := by
  change Epi (F.obj.map _)
  infer_instance

instance toOpenRestrictionPushforward_epi (F : Sheaf AddCommGrpCat.{u} X)
    [F.IsFlasque] : Epi ((toOpenRestrictionPushforward X U).app F) := by
  let : ∀ V, Epi (((toOpenRestrictionPushforward X U).app F).hom.app V) :=
    fun V => toOpenRestrictionPushforward_app_epi X U F V.unop
  have : Epi ((toOpenRestrictionPushforward X U).app F).hom :=
    NatTrans.epi_of_epi_app _
  exact (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).epi_of_epi_map this

/-- Let `X` be a topological space and `V ⊆ X` open. This functor sends a sheaf of abelian groups
`F` to its group of sections `F(V)` and evaluates sheaf morphisms on `V`. -/
def supportEvaluation (V : Opens X) : Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
    (evaluation _ AddCommGrpCat).obj (op V)

instance (V : Opens X) : (supportEvaluation X V).Additive where
  map_add := by intros; rfl

set_option backward.isDefEq.respectTransparency false in
instance (V : Opens X) :
    PreservesLimitsOfShape WalkingParallelPair (supportEvaluation X V) :=
  comp_preservesLimitsOfShape
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op V))

instance : (openRestrictionPushforward X U).Additive where
  map_add := by intros; rfl

/-- Let `X` be a topological space, `U ⊆ X` open, and `K` an integer-indexed complex of sheaves of
abelian groups. This is the sequence `Γ_{X \ U}(K) → K → j_*(K|_U)`, formed in every degree,
where `j : U → X` is inclusion. The first map includes sections vanishing on `U`; the second
restricts sections to `U`, so their composite is zero. -/
def supportRestrictionComplexShortComplex
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    -- The sequence `Γ_{X \ U}(K) → K → j_*(K|_U)`.
    ShortComplex (CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :=
  ShortComplex.mk
    (show ((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj K ⟶ K from
      { f n := (sheafSectionsSupportedOutsideInclusion X U).app (K.X n)
        comm' i j h := ((sheafSectionsSupportedOutsideInclusion X U).naturality (K.d i j)).symm })
    (show K ⟶ ((openRestrictionPushforward X U).mapHomologicalComplex ℤᵘᵖ).obj K from
      { f n := (toOpenRestrictionPushforward X U).app (K.X n)
        comm' i j h := ((toOpenRestrictionPushforward X U).naturality (K.d i j)).symm })
    (by ext n; exact sheafSectionsSupportedOutsideInclusion_restriction X U (K.X n))

/-- Let `X` be a topological space, `U` and `V` open subsets, and `K` an integer-indexed complex of
sheaves of abelian groups on `X`. This is the sequence of complexes `Γ_{X \ U}(V, K) → K(V) →
(j_*(K|_U))(V)`, obtained by taking sections on `V`. The first term consists of sections
vanishing on `V ∩ U`, and the last term identifies with `K(V ∩ U)`. -/
def supportRestrictionSectionsComplexShortComplex (V : Opens X)
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    ShortComplex (CochainComplex AddCommGrpCat.{u} ℤ) :=
  (supportRestrictionComplexShortComplex X U K).map
    ((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ)

local instance derivedSupportLocalizationSheafDerivedCategory :
    HasDerivedCategory (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat.{u} X)

local instance derivedSupportLocalizationGroupDerivedCategory : HasDerivedCategory AddCommGrpCat.{u} :=
  HasDerivedCategory.standard AddCommGrpCat.{u}

end TopCat.Sheaf
