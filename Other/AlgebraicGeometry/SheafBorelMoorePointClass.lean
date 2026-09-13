/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.PointSupportedChainSection
public import Other.AlgebraicGeometry.SmoothClosedSupportedCycleMorphism
public import Other.AlgebraicGeometry.ComplexPointCoclassOrientationComparison
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# An actual singleton-supported sheaf Borel–Moore point class

The literal singular zero-simplex, sheafified and pushed through the actual closed-support
factor, is a supported degree-zero cocycle. Good truncation and the actual group-valued
derived unit send it to `H⁰(RΓ_{x}(chainSheaf_X))`. Its coefficient `1` gives the point
class; the constructed complex orientation sends this class to supported degree `2d`.

This constructs an exact-image supported representative. It does not yet identify the
result with the older singular point coclass, nor with the smooth closed-component
construction using the source orientation inverse. Those comparison theorems must show
that the actual trace/cap pairing is normalized; no such theorem is an argument here.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ))) (d : ℕ)

local instance sheafBorelMoorePointClassSheafDerivedCategory :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) :=
  HasDerivedCategory.standard _

local instance sheafBorelMoorePointClassGroupsDerivedCategory : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

variable [SmoothOfRelativeDimension d X.hom] [T2Space (ComplexPoint X)]
  (x : ComplexPoint X)

/-- The point support is the actual closed image of its singleton-subspace inclusion. -/
def sheafBorelMoorePointSupport : Closeds (ComplexPoint X) :=
  closedEmbeddingSupport (pointChainEmbedding (TopCat.of (ComplexPoint X)) x)
    (pointChainEmbedding_isClosedEmbedding (TopCat.of (ComplexPoint X)) x)

/-- Its underlying support is exactly the singleton. -/
@[simp]
lemma sheafBorelMoorePointSupport_coe :
    (sheafBorelMoorePointSupport X x : Set (ComplexPoint X)) = {x} :=
  pointChainEmbedding_support (TopCat.of (ComplexPoint X)) x

/-- The literal point-chain cocycle followed by the group-valued good-truncation bridge
gives an actual morphism into singleton-supported ambient Borel–Moore hypercohomology. -/
def sheafBorelMoorePointMorphism :
    (DerivedCategory.Plus.singleFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℚ) ⟶
      complexAmbientSheafBorelMooreObject X d (sheafBorelMoorePointSupport X x) := by
  have h := complexChainSheaf_isGE X d
  exact DerivedCategory.Plus.ι.preimage
    (DerivedCategory.Q.map
      (pointSupportedChainCocycle ℚ (TopCat.of (ComplexPoint X)) x) ≫
        TopCat.Sheaf.termwiseToDerivedClosedSupport (TopCat.of (ComplexPoint X))
          (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X)))
          (-((2 * d : ℕ) : ℤ)) (sheafBorelMoorePointSupport X x))

/-- The full-inclusion lift does not change the actual point cocycle or the derived-unit map. -/
@[simp]
lemma sheafBorelMoorePointMorphism_underlying :
    DerivedCategory.Plus.ι.map (sheafBorelMoorePointMorphism X d x) =
      DerivedCategory.Q.map
        (pointSupportedChainCocycle ℚ (TopCat.of (ComplexPoint X)) x) ≫
        (by
          have h := complexChainSheaf_isGE X d
          exact TopCat.Sheaf.termwiseToDerivedClosedSupport
            (TopCat.of (ComplexPoint X))
            (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X)))
            (-((2 * d : ℕ) : ℤ)) (sheafBorelMoorePointSupport X x)) := by
  unfold sheafBorelMoorePointMorphism
  exact Functor.map_preimage _ _

end AlgebraicGeometry.ComplexPoint
