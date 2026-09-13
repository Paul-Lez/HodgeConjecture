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
`RΓ_image(K_X)` in `D⁺`. No support-acyclicity or intrinsic-to-ambient quasi-isomorphism
is assumed, and both complex orientations are the existing geometrically normalized ones.

This constructs the sheaf-level morphism underlying a smooth closed-component class.
It does not yet supply the global Chow-group map or a class for singular components.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Topology

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

local instance smoothSupportedCycleSheafDerivedCategory
    (Y : Over (Spec (.of ℂ))) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint Y))) :=
  HasDerivedCategory.standard _

variable (X : Over (Spec (.of ℂ))) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom] [T2Space (ComplexPoint X)]

/-- The lower bound needed for good truncation is proved from local homology concentration. -/
theorem complexChainSheaf_isGE :
    (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X))).IsGE
      (-((2 * d : ℕ) : ℤ)) := by
  apply CochainComplex.isGE_of_homology_concentrated
  intro n hn
  apply complexChainSheafCohomology_concentrated X d n
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hn

/-- The actual comparison from localized termwise support to the actual `D⁺` derived support
of the smooth ambient chain model. It is a map, not an assumed equivalence. -/
def complexChainTermwiseToDerivedSupport (S : Closeds (ComplexPoint X)) :
    DerivedCategory.Q.obj
      (((TopCat.Sheaf.sheafSectionsWithClosedSupport (TopCat.of (ComplexPoint X)) S).mapHomologicalComplex
        (.up ℤ)).obj
          (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X)))) ⟶
    DerivedCategory.Plus.ι.obj
      ((TopCat.Sheaf.derivedSheafSectionsWithClosedSupport (TopCat.of (ComplexPoint X)) S).obj
        (complexChainSheafPlusObject X d)) := by
  have h := complexChainSheaf_isGE X d
  exact TopCat.Sheaf.termwiseToDerivedSheafSupport (TopCat.of (ComplexPoint X))
    (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X)))
    (-((2 * d : ℕ) : ℤ)) S

variable (Z : Over (Spec (.of ℂ))) (i : Z ⟶ X)
  [IsClosedImmersion i.left] (e : ℕ) [SmoothOfRelativeDimension e Z.hom]
  [T2Space (ComplexPoint Z)]

/-- The normalized source orientation followed by actual closed-supported chain pushforward
and the proved truncation bridge lands in genuine derived support, entirely in `D⁺`. -/
def smoothClosedDerivedSupportedCycleMorphism :
    (TopCat.Sheaf.closedEmbeddingDerivedPushforwardPlus (closedCycleAnalyticMap Z X i)
      (closedCycleAnalyticMap_isClosedEmbedding Z X i)).obj
        ((complexConstantRationalSheafPlusObject Z)⟦2 * (e : ℤ)⟧) ⟶
    (TopCat.Sheaf.derivedSheafSectionsWithClosedSupport (TopCat.of (ComplexPoint X))
      (closedEmbeddingSupport (closedCycleAnalyticMap Z X i)
        (closedCycleAnalyticMap_isClosedEmbedding Z X i))).obj
          (complexChainSheafPlusObject X d) :=
  DerivedCategory.Plus.ι.preimage
    (smoothClosedCycleTermwiseSupportedMorphism Z X i e ≫
      complexChainTermwiseToDerivedSupport X d
        (closedEmbeddingSupport (closedCycleAnalyticMap Z X i)
          (closedCycleAnalyticMap_isClosedEmbedding Z X i)))

/-- The full-inclusion lift introduces no new morphism data: its underlying map is precisely
the normalized termwise supported map followed by the actual derived-support comparison. -/
@[simp]
lemma smoothClosedDerivedSupportedCycleMorphism_underlying :
    DerivedCategory.Plus.ι.map (smoothClosedDerivedSupportedCycleMorphism X d Z i e) =
      smoothClosedCycleTermwiseSupportedMorphism Z X i e ≫
        complexChainTermwiseToDerivedSupport X d
          (closedEmbeddingSupport (closedCycleAnalyticMap Z X i)
            (closedCycleAnalyticMap_isClosedEmbedding Z X i)) :=
  Functor.map_preimage _ _

end AlgebraicGeometry.ComplexPoint
