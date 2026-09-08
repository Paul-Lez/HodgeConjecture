/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicTopology.PointSupportedChainSection
public import HodgeConjecture.Other.AlgebraicGeometry.SmoothClosedSupportedCycleMorphism
public import HodgeConjecture.Other.AlgebraicGeometry.ComplexPointCoclassOrientationComparison
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

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ)) (d : ℕ)

noncomputable local instance sheafBorelMoorePointClassAnalyticTopology :
    TopologicalSpace (ComplexPoint X structureMap) := Point.analyticTopology

local instance sheafBorelMoorePointClassSheafDerivedCategory :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X structureMap))) :=
  HasDerivedCategory.standard _

local instance sheafBorelMoorePointClassGroupsDerivedCategory : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

variable [SmoothOfRelativeDimension d structureMap] [T2Space (ComplexPoint X structureMap)]
  (x : ComplexPoint X structureMap)

/-- The point support is the actual closed image of its singleton-subspace inclusion. -/
def sheafBorelMoorePointSupport : Closeds (ComplexPoint X structureMap) :=
  closedEmbeddingSupport (pointChainEmbedding (TopCat.of (ComplexPoint X structureMap)) x)
    (pointChainEmbedding_isClosedEmbedding (TopCat.of (ComplexPoint X structureMap)) x)

/-- Its underlying support is exactly the singleton. -/
@[simp]
lemma sheafBorelMoorePointSupport_coe :
    (sheafBorelMoorePointSupport structureMap x : Set (ComplexPoint X structureMap)) = {x} :=
  pointChainEmbedding_support (TopCat.of (ComplexPoint X structureMap)) x

/-- The literal point-chain cocycle followed by the group-valued good-truncation bridge
gives an actual morphism into singleton-supported ambient Borel–Moore hypercohomology. -/
def sheafBorelMoorePointMorphism :
    (DerivedCategory.Plus.singleFunctor AddCommGrpCat 0).obj (AddCommGrpCat.of ℚ) ⟶
      complexAmbientSheafBorelMooreObject structureMap d (sheafBorelMoorePointSupport structureMap x) := by
  have h := complexChainSheaf_isGE structureMap d
  exact DerivedCategory.Plus.ι.preimage
    (DerivedCategory.Q.map
      (pointSupportedChainCocycle ℚ (TopCat.of (ComplexPoint X structureMap)) x) ≫
        TopCat.Sheaf.termwiseToDerivedClosedSupport (TopCat.of (ComplexPoint X structureMap))
          (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X structureMap)))
          (-((2 * d : ℕ) : ℤ)) (sheafBorelMoorePointSupport structureMap x))

/-- The full-inclusion lift does not change the actual point cocycle or the derived-unit map. -/
@[simp]
lemma sheafBorelMoorePointMorphism_underlying :
    DerivedCategory.Plus.ι.map (sheafBorelMoorePointMorphism structureMap d x) =
      DerivedCategory.Q.map
        (pointSupportedChainCocycle ℚ (TopCat.of (ComplexPoint X structureMap)) x) ≫
        (by
          have h := complexChainSheaf_isGE structureMap d
          exact TopCat.Sheaf.termwiseToDerivedClosedSupport
            (TopCat.of (ComplexPoint X structureMap))
            (singularChainSheafCochainComplex ℚ (TopCat.of (ComplexPoint X structureMap)))
            (-((2 * d : ℕ) : ℤ)) (sheafBorelMoorePointSupport structureMap x)) := by
  unfold sheafBorelMoorePointMorphism
  exact Functor.map_preimage _ _

/-- The singleton-supported Borel–Moore point class, additive in its literal chain coefficient. -/
def sheafBorelMoorePointClassMap :
    AddCommGrpCat.of ℚ ⟶
      ComplexAmbientSheafBorelMooreHomology structureMap d
        (sheafBorelMoorePointSupport structureMap x) 0 :=
  ((DerivedCategory.singleFunctorCompHomologyFunctorIso AddCommGrpCat 0).app
    (AddCommGrpCat.of ℚ)).inv ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat 0).map
        (sheafBorelMoorePointMorphism structureMap d x)

/-- The supported point class starts with exactly the coefficient `1`. -/
def sheafBorelMoorePointClass :
    ComplexAmbientSheafBorelMooreHomology structureMap d
      (sheafBorelMoorePointSupport structureMap x) 0 :=
  sheafBorelMoorePointClassMap structureMap d x 1

/-- The constructed orientation transports the actual point class to degree `2d`. -/
def sheafBorelMoorePointSupportedCohomologyClass :
    ComplexDerivedSupportedCohomology structureMap
      (sheafBorelMoorePointSupport structureMap x) (2 * (d : ℤ)) := by
  exact (eqToIso (congrArg
    (ComplexDerivedSupportedCohomology structureMap (sheafBorelMoorePointSupport structureMap x))
      (sub_zero (2 * (d : ℤ))))).hom
        ((complexAmbientSheafBorelMooreHomologyIso structureMap d
          (sheafBorelMoorePointSupport structureMap x) 0).hom
            (sheafBorelMoorePointClass structureMap d x))

end AlgebraicGeometry.ComplexPoint
