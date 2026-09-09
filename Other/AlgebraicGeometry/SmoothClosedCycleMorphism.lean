/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ComplexSheafBorelMoore
public import Other.AlgebraicGeometry.ProjectiveAnalytification
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

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable local instance smoothClosedCycleAnalyticTopology
    (Y : Scheme) (sY : Y ⟶ Spec (.of ℂ)) : TopologicalSpace (ComplexPoint Y sY) :=
  Point.analyticTopology

local instance smoothClosedCycleSheafDerivedCategory
    (Y : Scheme) (sY : Y ⟶ Spec (.of ℂ)) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint Y sY))) :=
  HasDerivedCategory.standard _

variable {Z X : Scheme} (sZ : Z ⟶ Spec (.of ℂ)) (sX : X ⟶ Spec (.of ℂ))
  (i : Z ⟶ X) (hi : i ≫ sX = sZ)

/-- The actual continuous map of analytifications induced by the scheme morphism. -/
def closedCycleAnalyticMap :
    TopCat.of (ComplexPoint Z sZ) ⟶ TopCat.of (ComplexPoint X sX) :=
  TopCat.ofHom (Point.continuousMap i hi)

variable [IsClosedImmersion i]

/-- Algebraic closed immersion supplies the required closed topological embedding. -/
theorem closedCycleAnalyticMap_isClosedEmbedding :
    IsClosedEmbedding (closedCycleAnalyticMap sZ sX i hi) :=
  isClosedEmbedding_map_of_closedImmersion hi

variable (e d : ℕ) [SmoothOfRelativeDimension e sZ] [SmoothOfRelativeDimension d sX]
  [T2Space (ComplexPoint Z sZ)] [T2Space (ComplexPoint X sX)]

/-- The actual chain pushforward between the constructed smooth `D⁺` chain objects. -/
def smoothClosedChainPushforwardPlus :
    (TopCat.Sheaf.closedEmbeddingDerivedPushforwardPlus (closedCycleAnalyticMap sZ sX i hi)
      (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi)).obj
        (complexChainSheafPlusObject sZ e) ⟶ complexChainSheafPlusObject sX d :=
  DerivedCategory.Plus.ι.preimage
    (singularChainSheafDerivedPushforward (closedCycleAnalyticMap sZ sX i hi) ℚ
      (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi))

/-- The smooth `D⁺` pushforward has exactly the previously constructed singular-chain map
as its underlying derived morphism. -/
@[simp]
lemma smoothClosedChainPushforwardPlus_underlying :
    DerivedCategory.Plus.ι.map (smoothClosedChainPushforwardPlus sZ sX i hi e d) =
      singularChainSheafDerivedPushforward (closedCycleAnalyticMap sZ sX i hi) ℚ
        (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi) :=
  Functor.map_preimage _ _

/-- Inverse exact source orientation followed by actual closed-embedding pushforward.
No orientation or general Alexander-duality equivalence is supplied as data. -/
def smoothClosedCycleMorphism :
    (TopCat.Sheaf.closedEmbeddingDerivedPushforwardPlus (closedCycleAnalyticMap sZ sX i hi)
      (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi)).obj
        ((complexConstantRationalSheafPlusObject sZ)⟦2 * (e : ℤ)⟧) ⟶
      complexChainSheafPlusObject sX d :=
  (TopCat.Sheaf.closedEmbeddingDerivedPushforwardPlus (closedCycleAnalyticMap sZ sX i hi)
    (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi)).map
      (complexChainSheafPlusOrientationIso sZ e).inv ≫
    smoothClosedChainPushforwardPlus sZ sX i hi e d

/-- Composing back with the fixed source orientation recovers the actual pushforward.
This fixes the normalization of the smooth-cycle morphism. -/
@[reassoc (attr := simp)]
lemma smoothClosedCycleMorphism_source_orientation :
    (TopCat.Sheaf.closedEmbeddingDerivedPushforwardPlus (closedCycleAnalyticMap sZ sX i hi)
      (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi)).map
        (complexChainSheafPlusOrientationIso sZ e).hom ≫
      smoothClosedCycleMorphism sZ sX i hi e d =
        smoothClosedChainPushforwardPlus sZ sX i hi e d := by
  rw [smoothClosedCycleMorphism, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The normalized smooth closed-immersion morphism between the shifted rational sheaves.
This is the sheaf-level morphism underlying the smooth cycle class. -/
def smoothClosedOrientedCycleMorphism :
    (TopCat.Sheaf.closedEmbeddingDerivedPushforwardPlus (closedCycleAnalyticMap sZ sX i hi)
      (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi)).obj
        ((complexConstantRationalSheafPlusObject sZ)⟦2 * (e : ℤ)⟧) ⟶
      (complexConstantRationalSheafPlusObject sX)⟦2 * (d : ℤ)⟧ :=
  smoothClosedCycleMorphism sZ sX i hi e d ≫ (complexChainSheafPlusOrientationIso sX d).hom

/-- The smooth-cycle morphism retains genuine closed support in the localized termwise
supported chain model. This target is not renamed right-derived support. -/
def smoothClosedCycleTermwiseSupportedMorphism :
    DerivedCategory.Plus.ι.obj
      ((TopCat.Sheaf.closedEmbeddingDerivedPushforwardPlus (closedCycleAnalyticMap sZ sX i hi)
        (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi)).obj
          ((complexConstantRationalSheafPlusObject sZ)⟦2 * (e : ℤ)⟧)) ⟶
    DerivedCategory.Q.obj
      (((TopCat.Sheaf.sheafSectionsWithClosedSupport (TopCat.of (ComplexPoint X sX))
        (closedEmbeddingSupport (closedCycleAnalyticMap sZ sX i hi)
          (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
              (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X sX)))) :=
  (TopCat.Sheaf.closedEmbeddingDerivedPushforward (closedCycleAnalyticMap sZ sX i hi)
    (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi)).map
      (DerivedCategory.Plus.ι.map (complexChainSheafPlusOrientationIso sZ e).inv) ≫
    singularChainSheafDerivedPushforwardWithClosedSupport (closedCycleAnalyticMap sZ sX i hi) ℚ
      (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi)

/-- Forgetting actual termwise support gives precisely the normalized smooth-cycle
morphism, not merely a scalar multiple of it. -/
@[reassoc (attr := simp)]
lemma smoothClosedCycleTermwiseSupportedMorphism_inclusion :
    smoothClosedCycleTermwiseSupportedMorphism sZ sX i hi e ≫
      DerivedCategory.Q.map (singularCochainClosedSupportInclusion ℚ
        (closedEmbeddingSupport (closedCycleAnalyticMap sZ sX i hi)
          (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi))) =
      DerivedCategory.Plus.ι.map (smoothClosedCycleMorphism sZ sX i hi e d) := by
  rw [smoothClosedCycleTermwiseSupportedMorphism, Category.assoc,
    singularChainSheafDerivedPushforwardWithClosedSupport_inclusion,
    smoothClosedCycleMorphism, Functor.map_comp, smoothClosedChainPushforwardPlus_underlying]
  rfl

end AlgebraicGeometry.ComplexPoint
