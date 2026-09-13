/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.ClosedFiltrationDimension
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.Analytification
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.AffineRelativeDimension
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

/-!
# Ambient closed supports for singular-component localization induction

The singular boundary of an integral cycle component carries its canonical finite reduced
smooth filtration, whose images are closed both algebraically and analytically in the ambient
variety, and whose successive differences are the complex-point images of smooth locally
closed strata. Their local relative dimensions are strictly below `d - p`, so their ambient
normal codimensions are at least `p + 1`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)

/-- The canonical closed remainders inside the integral component's singular boundary. -/
abbrev cycleComponentSingularClosedFiltration (k : ℕ) : Closeds (cycleComponent X.left x) :=
  reducedSmoothClosedFiltration (cycleComponentι X.left x ≫ X.hom)
    (singularLocusClosed (cycleComponentι X.left x ≫ X.hom)) k

/-- Every stage is a closed support in the original algebraic ambient scheme. -/
def cycleComponentSingularAmbientClosedFiltration (k : ℕ) : Closeds X.left :=
  ⟨cycleComponentι X.left x '' (cycleComponentSingularClosedFiltration X x k : Set _),
    (cycleComponentι X.left x).isClosedEmbedding.isClosedMap _
      (cycleComponentSingularClosedFiltration X x k).isClosed⟩

namespace ComplexPoint

/-- The actual analytically closed ambient supports for nested-support localization. -/
def cycleComponentSingularAnalyticClosedFiltration (k : ℕ) : Closeds (ComplexPoint X) :=
  ⟨Point.underlying ⁻¹' (cycleComponentSingularAmbientClosedFiltration X x k : Set X.left),
    (cycleComponentSingularAmbientClosedFiltration X x k).isClosed.preimage
      (continuous_underlying_to_zariski X)⟩

/-- The smooth locus of the component, bundled over `Spec ℂ`. -/
abbrev cycleComponentSmoothLocusOver : Over (Spec (.of ℂ)) :=
  Over.mk (((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
    cycleComponentι X.left x) ≫ X.hom)

instance cycleComponentSmoothLocusOver_locallyOfFiniteType :
    LocallyOfFiniteType (cycleComponentSmoothLocusOver X x).hom := by
  change LocallyOfFiniteType
    (((cycleComponentι X.left x ≫ X.hom).smoothLocus.ι ≫
      cycleComponentι X.left x) ≫ X.hom)
  rw [Category.assoc]
  infer_instance

end ComplexPoint
end AlgebraicGeometry
