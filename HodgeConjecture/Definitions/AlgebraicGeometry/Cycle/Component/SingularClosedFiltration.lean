/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.ClosedFiltration
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.SingularLocusDimension
public import HodgeConjecture.Lemmas.Topology.Dimension.ClosedSubset
public import Mathlib.Topology.NoetherianSpace
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.Analytification
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.AffineRelativeDimension
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Ambient closed supports for localization induction over a closed subvariety

The singular boundary of the integral source of a closed embedding carries its canonical finite
reduced smooth filtration, whose images are closed both algebraically and analytically in the
ambient variety, and whose successive differences are the complex-point images of smooth locally
closed strata. Their local relative dimensions are strictly below `d - p`, so their ambient
normal codimensions are at least `p + 1`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [IsClosedImmersion i.left]

/-- The canonical closed remainders inside the singular boundary of the source. -/
abbrev closedEmbeddingSingularClosedFiltration (k : ℕ) : Closeds Y.left :=
  reducedSmoothClosedFiltration (i.left ≫ X.hom)
    (singularLocusClosed (i.left ≫ X.hom)) k

/-- Every stage is a closed support in the original algebraic ambient scheme. -/
def closedEmbeddingSingularAmbientClosedFiltration (k : ℕ) : Closeds X.left :=
  ⟨i.left '' (closedEmbeddingSingularClosedFiltration i k : Set _),
    i.left.isClosedEmbedding.isClosedMap _
      (closedEmbeddingSingularClosedFiltration i k).isClosed⟩

namespace ComplexPoint

/-- The actual analytically closed ambient supports for nested-support localization. -/
def closedEmbeddingSingularAnalyticClosedFiltration (k : ℕ) : Closeds (ComplexPoint X) :=
  ⟨Point.underlying ⁻¹' (closedEmbeddingSingularAmbientClosedFiltration i k : Set X.left),
    (closedEmbeddingSingularAmbientClosedFiltration i k).isClosed.preimage
      (continuous_underlying_to_zariski X)⟩

/-- The smooth locus of the source, bundled over `Spec ℂ`. -/
abbrev closedEmbeddingSmoothLocusOver : Over (Spec ↧ℂ) :=
  Over.mk ((i.left ≫ X.hom).smoothLocus.ι ≫ Y.hom)

instance closedEmbeddingSmoothLocusOver_locallyOfFiniteType :
    LocallyOfFiniteType (closedEmbeddingSmoothLocusOver i).hom := by
  change LocallyOfFiniteType ((i.left ≫ X.hom).smoothLocus.ι ≫ Y.hom)
  rw [show Y.hom = i.left ≫ X.hom from (Over.w i).symm]
  infer_instance

end ComplexPoint
end AlgebraicGeometry
