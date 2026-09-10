/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexSheafBorelMoore
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersionComplexPoint
public import Other.AlgebraicTopology.SingularChainSheafDerivedPushforward

/-!
# A normalized derived morphism for a smooth closed complex subvariety

For a closed immersion of smooth complex schemes `i : Z → X`, the constructed source
orientation identifies its actual chain model with `ℚ_Z[2 dim Z]`. Its inverse, followed
by the actual closed-embedding chain pushforward and the constructed ambient orientation,
gives a concrete morphism `i_* ℚ_Z[2 dim Z] → ℚ_X[2 dim X]` in `D⁺`.

The same map factors through the localization of the actual termwise supported ambient
chains. This last target is explicitly not identified here with right-derived sections
with support. Neither an intrinsic-to-ambient quasi-isomorphism nor a freely chosen
orientation is an input. Passing from this morphism to the repository's global cycle-class
groups, and handling singular components, remains separate work.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

noncomputable local instance smoothClosedCycleAnalyticTopology
    (Y : Over (Spec (.of ℂ))) : TopologicalSpace (ComplexPoint Y) :=
  Point.analyticTopology

local instance smoothClosedCycleSheafDerivedCategory
    (Y : Over (Spec (.of ℂ))) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint Y))) :=
  HasDerivedCategory.standard _

variable (Z X : Over (Spec (.of ℂ))) (i : Z ⟶ X)

/-- The actual continuous map of analytifications induced by the scheme morphism. -/
def closedCycleAnalyticMap :
    TopCat.of (ComplexPoint Z) ⟶ TopCat.of (ComplexPoint X) :=
  TopCat.ofHom (Point.continuousMap i)

variable [IsClosedImmersion i.left]

/-- Algebraic closed immersion supplies the required closed topological embedding. -/
theorem closedCycleAnalyticMap_isClosedEmbedding :
    IsClosedEmbedding (closedCycleAnalyticMap Z X i) :=
  isClosedEmbedding_map_of_closedImmersion i

variable (e d : ℕ) [SmoothOfRelativeDimension e Z.hom] [SmoothOfRelativeDimension d X.hom]
  [T2Space (ComplexPoint Z)] [T2Space (ComplexPoint X)]

/-- The actual chain pushforward between the constructed smooth `D⁺` chain objects. -/
def smoothClosedChainPushforwardPlus :
    (TopCat.Sheaf.closedEmbeddingDerivedPushforwardPlus (closedCycleAnalyticMap Z X i)
      (closedCycleAnalyticMap_isClosedEmbedding Z X i)).obj
        (complexChainSheafPlusObject Z e) ⟶ complexChainSheafPlusObject X d :=
  DerivedCategory.Plus.ι.preimage
    (singularChainSheafDerivedPushforward (closedCycleAnalyticMap Z X i) ℚ
      (closedCycleAnalyticMap_isClosedEmbedding Z X i))

/-- The smooth `D⁺` pushforward has exactly the previously constructed singular-chain map
as its underlying derived morphism. -/
@[simp]
lemma smoothClosedChainPushforwardPlus_underlying :
    DerivedCategory.Plus.ι.map (smoothClosedChainPushforwardPlus Z X i e d) =
      singularChainSheafDerivedPushforward (closedCycleAnalyticMap Z X i) ℚ
        (closedCycleAnalyticMap_isClosedEmbedding Z X i) :=
  Functor.map_preimage _ _

/-- Inverse exact source orientation followed by actual closed-embedding pushforward.
No orientation or general Alexander-duality equivalence is supplied as data. -/
def smoothClosedCycleMorphism :
    (TopCat.Sheaf.closedEmbeddingDerivedPushforwardPlus (closedCycleAnalyticMap Z X i)
      (closedCycleAnalyticMap_isClosedEmbedding Z X i)).obj
        ((complexConstantRationalSheafPlusObject Z)⟦2 * (e : ℤ)⟧) ⟶
      complexChainSheafPlusObject X d :=
  (TopCat.Sheaf.closedEmbeddingDerivedPushforwardPlus (closedCycleAnalyticMap Z X i)
    (closedCycleAnalyticMap_isClosedEmbedding Z X i)).map
      (complexChainSheafPlusOrientationIso Z e).inv ≫
    smoothClosedChainPushforwardPlus Z X i e d

/-- Composing back with the fixed source orientation recovers the actual pushforward.
This fixes the normalization of the smooth-cycle morphism. -/
@[reassoc (attr := simp)]
lemma smoothClosedCycleMorphism_source_orientation :
    (TopCat.Sheaf.closedEmbeddingDerivedPushforwardPlus (closedCycleAnalyticMap Z X i)
      (closedCycleAnalyticMap_isClosedEmbedding Z X i)).map
        (complexChainSheafPlusOrientationIso Z e).hom ≫
      smoothClosedCycleMorphism Z X i e d =
        smoothClosedChainPushforwardPlus Z X i e d := by
  rw [smoothClosedCycleMorphism, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The normalized smooth closed-immersion morphism between the shifted rational sheaves.
This is the sheaf-level morphism underlying the smooth cycle class. -/
def smoothClosedOrientedCycleMorphism :
    (TopCat.Sheaf.closedEmbeddingDerivedPushforwardPlus (closedCycleAnalyticMap Z X i)
      (closedCycleAnalyticMap_isClosedEmbedding Z X i)).obj
        ((complexConstantRationalSheafPlusObject Z)⟦2 * (e : ℤ)⟧) ⟶
      (complexConstantRationalSheafPlusObject X)⟦2 * (d : ℤ)⟧ :=
  smoothClosedCycleMorphism Z X i e d ≫ (complexChainSheafPlusOrientationIso X d).hom

/-- The smooth-cycle morphism retains genuine closed support in the localized termwise
supported chain model. This target is not renamed right-derived support. -/
def smoothClosedCycleTermwiseSupportedMorphism :
    DerivedCategory.Plus.ι.obj
      ((TopCat.Sheaf.closedEmbeddingDerivedPushforwardPlus (closedCycleAnalyticMap Z X i)
        (closedCycleAnalyticMap_isClosedEmbedding Z X i)).obj
          ((complexConstantRationalSheafPlusObject Z)⟦2 * (e : ℤ)⟧)) ⟶
    DerivedCategory.Q.obj
      (((TopCat.Sheaf.sheafSectionsWithClosedSupport (TopCat.of (ComplexPoint X))
        (closedEmbeddingSupport (closedCycleAnalyticMap Z X i)
          (closedCycleAnalyticMap_isClosedEmbedding Z X i))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
              (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X)))) :=
  (TopCat.Sheaf.closedEmbeddingDerivedPushforward (closedCycleAnalyticMap Z X i)
    (closedCycleAnalyticMap_isClosedEmbedding Z X i)).map
      (DerivedCategory.Plus.ι.map (complexChainSheafPlusOrientationIso Z e).inv) ≫
    singularChainSheafDerivedPushforwardWithClosedSupport (closedCycleAnalyticMap Z X i) ℚ
      (closedCycleAnalyticMap_isClosedEmbedding Z X i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Forgetting actual termwise support gives precisely the normalized smooth-cycle
morphism, not merely a scalar multiple of it. -/
@[reassoc (attr := simp)]
lemma smoothClosedCycleTermwiseSupportedMorphism_inclusion :
    smoothClosedCycleTermwiseSupportedMorphism Z X i e ≫
      DerivedCategory.Q.map (singularCochainClosedSupportInclusion ℚ
        (closedEmbeddingSupport (closedCycleAnalyticMap Z X i)
          (closedCycleAnalyticMap_isClosedEmbedding Z X i))) =
      DerivedCategory.Plus.ι.map (smoothClosedCycleMorphism Z X i e d) := by
  rw [smoothClosedCycleTermwiseSupportedMorphism, Category.assoc,
    singularChainSheafDerivedPushforwardWithClosedSupport_inclusion,
    smoothClosedCycleMorphism, Functor.map_comp, smoothClosedChainPushforwardPlus_underlying]
  rfl

end AlgebraicGeometry.ComplexPoint
