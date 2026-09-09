/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SmoothClosedCycleMorphism
public import Other.AlgebraicTopology.DerivedSheafSupportTruncation

/-!
# The normalized smooth closed-cycle morphism into actual derived support

The actual termwise supported chain map is followed by good truncation of the smooth
ambient chain model and the genuine derived-support unit. Transporting back along
derived support of the proved truncation isomorphism gives a morphism into actual
`RΓ̲_image(K_X)` in `D⁺`. No support-acyclicity or intrinsic-to-ambient quasi-isomorphism
is assumed, and both complex orientations are the existing geometrically normalized ones.

This constructs the sheaf-level morphism underlying a smooth closed-component class.
It does not yet supply the global Chow-group map or a class for singular components.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable local instance smoothSupportedCycleAnalyticTopology
    (Y : Scheme) (sY : Y ⟶ Spec (.of ℂ)) : TopologicalSpace (ComplexPoint Y sY) :=
  Point.analyticTopology

local instance smoothSupportedCycleSheafDerivedCategory
    (Y : Scheme) (sY : Y ⟶ Spec (.of ℂ)) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint Y sY))) :=
  HasDerivedCategory.standard _

variable {X : Scheme} (sX : X ⟶ Spec (.of ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d sX] [T2Space (ComplexPoint X sX)]

/-- The lower bound needed for good truncation is proved from local homology concentration. -/
theorem complexChainSheaf_isGE :
    (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X sX))).IsGE
      (-((2 * d : ℕ) : ℤ)) := by
  apply CochainComplex.isGE_of_homology_concentrated
  intro n hn
  apply complexChainSheafCohomology_concentrated sX d n
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hn

/-- The actual comparison from localized termwise support to the actual `D⁺` derived support
of the smooth ambient chain model. It is a map, not an assumed equivalence. -/
def complexChainTermwiseToDerivedSupport (S : Closeds (ComplexPoint X sX)) :
    DerivedCategory.Q.obj
      (((TopCat.Sheaf.sheafSectionsWithClosedSupport (TopCat.of (ComplexPoint X sX)) S).mapHomologicalComplex
        (.up ℤ)).obj
          (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X sX)))) ⟶
    DerivedCategory.Plus.ι.obj
      ((TopCat.Sheaf.derivedSheafSectionsWithClosedSupport (TopCat.of (ComplexPoint X sX)) S).obj
        (complexChainSheafPlusObject sX d)) := by
  have h := complexChainSheaf_isGE sX d
  exact TopCat.Sheaf.termwiseToDerivedSheafSupport (TopCat.of (ComplexPoint X sX))
    (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X sX)))
    (-((2 * d : ℕ) : ℤ)) S

variable {Z : Scheme} (sZ : Z ⟶ Spec (.of ℂ)) (i : Z ⟶ X) (hi : i ≫ sX = sZ)
  [IsClosedImmersion i] (e : ℕ) [SmoothOfRelativeDimension e sZ]
  [T2Space (ComplexPoint Z sZ)]

/-- The normalized source orientation followed by actual closed-supported chain pushforward
and the proved truncation bridge lands in genuine derived support, entirely in `D⁺`. -/
def smoothClosedDerivedSupportedCycleMorphism :
    (TopCat.Sheaf.closedEmbeddingDerivedPushforwardPlus (closedCycleAnalyticMap sZ sX i hi)
      (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi)).obj
        ((complexConstantRationalSheafPlusObject sZ)⟦2 * (e : ℤ)⟧) ⟶
    (TopCat.Sheaf.derivedSheafSectionsWithClosedSupport (TopCat.of (ComplexPoint X sX))
      (closedEmbeddingSupport (closedCycleAnalyticMap sZ sX i hi)
        (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi))).obj
          (complexChainSheafPlusObject sX d) :=
  DerivedCategory.Plus.ι.preimage
    (smoothClosedCycleTermwiseSupportedMorphism sZ sX i hi e ≫
      complexChainTermwiseToDerivedSupport sX d
        (closedEmbeddingSupport (closedCycleAnalyticMap sZ sX i hi)
          (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi)))

/-- The full-inclusion lift introduces no new morphism data: its underlying map is precisely
the normalized termwise supported map followed by the actual derived-support comparison. -/
@[simp]
lemma smoothClosedDerivedSupportedCycleMorphism_underlying :
    DerivedCategory.Plus.ι.map (smoothClosedDerivedSupportedCycleMorphism sX d sZ i hi e) =
      smoothClosedCycleTermwiseSupportedMorphism sZ sX i hi e ≫
        complexChainTermwiseToDerivedSupport sX d
          (closedEmbeddingSupport (closedCycleAnalyticMap sZ sX i hi)
            (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi)) :=
  Functor.map_preimage _ _

/-- Applying the constructed ambient orientation gives the supported smooth-cycle morphism
with rational constant coefficients. Both orientations are fixed by the exact local classes. -/
def smoothClosedDerivedSupportedOrientedCycleMorphism :
    (TopCat.Sheaf.closedEmbeddingDerivedPushforwardPlus (closedCycleAnalyticMap sZ sX i hi)
      (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi)).obj
        ((complexConstantRationalSheafPlusObject sZ)⟦2 * (e : ℤ)⟧) ⟶
    (TopCat.Sheaf.derivedSheafSectionsWithClosedSupport (TopCat.of (ComplexPoint X sX))
      (closedEmbeddingSupport (closedCycleAnalyticMap sZ sX i hi)
        (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi))).obj
          ((complexConstantRationalSheafPlusObject sX)⟦2 * (d : ℤ)⟧) :=
  smoothClosedDerivedSupportedCycleMorphism sX d sZ i hi e ≫
    (TopCat.Sheaf.derivedSheafSectionsWithClosedSupport (TopCat.of (ComplexPoint X sX))
      (closedEmbeddingSupport (closedCycleAnalyticMap sZ sX i hi)
        (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi))).map
          (complexChainSheafPlusOrientationIso sX d).hom

end AlgebraicGeometry.ComplexPoint
