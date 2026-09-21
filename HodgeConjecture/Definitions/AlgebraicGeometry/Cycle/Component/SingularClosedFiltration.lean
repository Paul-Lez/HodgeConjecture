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

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the reduced closure of
the scheme point `x`. Start with `S₀ = Z_sing` and obtain `S_{k+1}` by removing the smooth locus
of the reduced scheme on `S_k`. This is the closed subset `S_k` of `Z`, for a natural number
`k`. -/
abbrev cycleComponentSingularClosedFiltration (k : ℕ) : Closeds (cycleComponent X.left x) :=
  reducedSmoothClosedFiltration (cycleComponentι X.left x ≫ X.hom)
    (singularLocusClosed (cycleComponentι X.left x ≫ X.hom)) k

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the reduced closure of
the scheme point `x`. Start with `S₀ = Z_sing` and obtain `S_{k+1}` by removing the smooth locus
of the reduced scheme on `S_k`. This is the image of `S_k` as a closed subset of the ambient
scheme `X`. -/
def cycleComponentSingularAmbientClosedFiltration (k : ℕ) : Closeds X.left :=
  ⟨cycleComponentι X.left x '' (cycleComponentSingularClosedFiltration X x k : Set _),
    (cycleComponentι X.left x).isClosedEmbedding.isClosedMap _
      (cycleComponentSingularClosedFiltration X x k).isClosed⟩

namespace ComplexPoint

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the reduced closure of
the scheme point `x`. Start with `S₀ = Z_sing` and obtain `S_{k+1}` by removing the smooth locus
of the reduced scheme on `S_k`. This is the analytically closed subset `S_k(ℂ) ⊆ X(ℂ)`, formed
by taking complex points whose underlying scheme points lie in `S_k`. -/
def cycleComponentSingularAnalyticClosedFiltration (k : ℕ) : Closeds (ComplexPoint X) :=
  ⟨Point.underlying ⁻¹' (cycleComponentSingularAmbientClosedFiltration X x k : Set X.left),
    (cycleComponentSingularAmbientClosedFiltration X x k).isClosed.preimage
      (continuous_underlying_to_zariski X)⟩

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the reduced closure of
the scheme point `x`. This is the smooth locus `Z_reg` as a scheme over `ℂ`, with structure
morphism induced by its inclusion in `Z` and then in `X`. -/
abbrev cycleComponentSmoothLocusOver : Over (Spec ↧ℂ) :=
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
