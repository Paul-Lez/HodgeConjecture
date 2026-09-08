/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.Algebra.Homology.MapExtend
public import HodgeConjecture.Other.AlgebraicTopology.SingularChainSheafClosedSupport
public import HodgeConjecture.Other.AlgebraicTopology.ClosedEmbeddingDerivedPushforward

/-!
# The actual supported chain map in the derived pushforward interface

The canonical additive-functor/extension comparison puts the existing closed-embedding
chain map in cohomological grading, with source the actual termwise direct image of the
intrinsic cochain sheaf and target the actual termwise closed-support sheaf functor.
Localization then gives the corresponding map out of the constructed derived direct image.

The supported target in this file is explicitly the localization of **termwise** supported
chains. It is not silently identified with the right-derived support functor. This construction
requires no boundedness, smoothness, or intrinsic-to-ambient quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology

universe u

namespace AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {Z X : TopCat.{u}} (i : Z ⟶ X) (R : Type u) [Field R]

/-- The actual closed-support inclusion, now applied to the integer-graded chain model. -/
def singularCochainClosedSupportInclusion (S : Closeds X) :
    ((TopCat.Sheaf.sheafSectionsWithClosedSupport X S).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (singularChainSheafCochainComplex R X) ⟶
      singularChainSheafCochainComplex R X :=
  ((TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X S.compl).mapHomologicalComplex
    (ComplexShape.up ℤ)).app (singularChainSheafCochainComplex R X)

/-- The extension comparison intertwines the actual two support-forgetting inclusions. -/
@[reassoc]
lemma singularCochainClosedSupportInclusion_extend (S : Closeds X) :
    (HomologicalComplex.mapExtendCanonicalIso (TopCat.Sheaf.sheafSectionsWithClosedSupport X S)
      (singularChainSheafComplex R X) ComplexShape.embeddingDownNat).hom ≫
        HomologicalComplex.extendMap (singularChainClosedSupportInclusion R S)
          ComplexShape.embeddingDownNat = singularCochainClosedSupportInclusion R S := by
  have h := HomologicalComplex.mapExtendCanonicalIso_natTrans
    (TopCat.Sheaf.sheafSectionsWithClosedSupport X S) (singularChainSheafComplex R X)
    ComplexShape.embeddingDownNat (TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion X S.compl)
  rw [HomologicalComplex.mapExtendCanonicalIso_id] at h
  erw [Category.comp_id] at h
  exact h.symm

/-- Closed-embedding chain pushforward with the source genuinely `i_* K_Z` in cohomological
grading, rather than a differently presented regraded source. -/
def singularChainSheafCochainPushforward (hi : IsClosedEmbedding i) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (singularChainSheafCochainComplex R Z) ⟶
      singularChainSheafCochainComplex R X :=
  (HomologicalComplex.mapExtendCanonicalIso (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)
    (singularChainSheafComplex R Z) ComplexShape.embeddingDownNat).hom ≫
      singularChainSheafPushforwardRegraded R i hi

/-- The same actual map with its canonically constructed closed support. -/
def singularChainSheafCochainPushforwardWithClosedSupport (hi : IsClosedEmbedding i) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (singularChainSheafCochainComplex R Z) ⟶
    ((TopCat.Sheaf.sheafSectionsWithClosedSupport X (closedEmbeddingSupport i hi)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (singularChainSheafCochainComplex R X) :=
  (HomologicalComplex.mapExtendCanonicalIso (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i)
    (singularChainSheafComplex R Z) ComplexShape.embeddingDownNat).hom ≫
      singularChainSheafPushforwardWithClosedSupportRegraded i R hi ≫
      (HomologicalComplex.mapExtendCanonicalIso
        (TopCat.Sheaf.sheafSectionsWithClosedSupport X (closedEmbeddingSupport i hi))
        (singularChainSheafComplex R X) ComplexShape.embeddingDownNat).inv

/-- Forgetting support recovers exactly the previously constructed cochain pushforward. -/
@[reassoc (attr := simp)]
lemma singularChainSheafCochainPushforwardWithClosedSupport_inclusion (hi : IsClosedEmbedding i) :
    singularChainSheafCochainPushforwardWithClosedSupport i R hi ≫
      singularCochainClosedSupportInclusion R (closedEmbeddingSupport i hi) =
        singularChainSheafCochainPushforward i R hi := by
  rw [singularChainSheafCochainPushforwardWithClosedSupport,
    ← singularCochainClosedSupportInclusion_extend,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    singularChainSheafPushforwardWithClosedSupportRegraded_inclusion]
  rfl

/-- In each degree `-n` the cochain pushforward is the original normalized chain map. -/
lemma singularChainSheafCochainPushforward_f (hi : IsClosedEmbedding i) (n : ℕ) :
    (singularChainSheafCochainPushforward i R hi).f (-((n : ℕ) : ℤ)) =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).map
          (singularChainSheafCochainComplexXIso R Z n).hom ≫
        (singularChainSheafPushforward R i hi).f n ≫
          (singularChainSheafCochainComplexXIso R X n).inv := by
  dsimp only [singularChainSheafCochainPushforward, HomologicalComplex.comp_f,
    singularChainSheafPushforwardRegraded]
  erw [HomologicalComplex.mapExtendCanonicalIso_hom_f _ _ _ (i := n) rfl,
    HomologicalComplex.extendMap_f _ _ (i := n) rfl, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

local instance chainDerivedPushforwardSourceCategory :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{u} Z) := HasDerivedCategory.standard _

local instance chainDerivedPushforwardTargetCategory :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat.{u} X) := HasDerivedCategory.standard _

/-- Localization of the actual cochain pushforward through the constructed exact derived
direct image. This map does not require a smooth or bounded-below source. -/
def singularChainSheafDerivedPushforward (hi : IsClosedEmbedding i) :
    (TopCat.Sheaf.closedEmbeddingDerivedPushforward i hi).obj
      (DerivedCategory.Q.obj (singularChainSheafCochainComplex R Z)) ⟶
        DerivedCategory.Q.obj (singularChainSheafCochainComplex R X) :=
  (TopCat.Sheaf.closedEmbeddingDerivedPushforwardFactors i hi).hom.app
      (singularChainSheafCochainComplex R Z) ≫
    DerivedCategory.Q.map (singularChainSheafCochainPushforward i R hi)

/-- The derived-interface map into the localization of actual termwise supported chains.
The target is not defined to be right-derived sections with support. -/
def singularChainSheafDerivedPushforwardWithClosedSupport (hi : IsClosedEmbedding i) :
    (TopCat.Sheaf.closedEmbeddingDerivedPushforward i hi).obj
      (DerivedCategory.Q.obj (singularChainSheafCochainComplex R Z)) ⟶
    DerivedCategory.Q.obj
      (((TopCat.Sheaf.sheafSectionsWithClosedSupport X (closedEmbeddingSupport i hi)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (singularChainSheafCochainComplex R X)) :=
  (TopCat.Sheaf.closedEmbeddingDerivedPushforwardFactors i hi).hom.app
      (singularChainSheafCochainComplex R Z) ≫
    DerivedCategory.Q.map (singularChainSheafCochainPushforwardWithClosedSupport i R hi)

/-- The derived support factorization preserves the original normalized pushforward. -/
@[reassoc (attr := simp)]
lemma singularChainSheafDerivedPushforwardWithClosedSupport_inclusion (hi : IsClosedEmbedding i) :
    singularChainSheafDerivedPushforwardWithClosedSupport i R hi ≫
      DerivedCategory.Q.map (singularCochainClosedSupportInclusion R (closedEmbeddingSupport i hi)) =
        singularChainSheafDerivedPushforward i R hi := by
  rw [singularChainSheafDerivedPushforwardWithClosedSupport, Category.assoc,
    ← Functor.map_comp, singularChainSheafCochainPushforwardWithClosedSupport_inclusion]
  rfl

end AlgebraicTopology.Singular
