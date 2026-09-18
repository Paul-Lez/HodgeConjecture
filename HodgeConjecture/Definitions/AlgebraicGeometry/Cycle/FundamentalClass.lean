/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportConeInjectiveModel
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SupportExtension
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularCohomologySheafComparison
/-!
# Constructed sheaf cycle classes in arbitrary codimension

The exactly normalized normal-chart coclass on the smooth locus of a closed subvariety is
transported to the supported cohomology sheaf. Lowest-degree purity
and the proved unique extension across the singular boundary then give an
supported class on the original ambient variety. Forgetting support
lands in the repository's ordinary rational cohomology.

All comparison maps, purity statements, and extension isomorphisms are
constructed. No fundamental-class, orientation, duality, or vanishing datum
is an argument. The corresponding Borel–Moore fundamental class is obtained
through the previously constructed complex-orientation duality for the
ambient chain sheaf. This does not assert intrinsic compactification
independence or rational-equivalence invariance.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable {X : Over (Spec ↧ℂ)}
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance closedEmbeddingSheafClassAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- `𝓗^n(RΓ_S(ℚ)) ≅ 𝓗^n_S` for a closed `S ⊆ X(ℂ)`: the `n`-th cohomology sheaf of `RΓ_S(ℚ)`, the
`S`-supported part of the injective resolution of `ℚ` on `X(ℂ)`, is the sheaf associated with
`V ↦ H^n(V, V \ S; ℚ)`. The comparison goes through the singular resolution. -/
def complexSupportInjectiveCohomologySheafIsoRelative
    (S : Closeds (ComplexPoint X)) (n : ℕ) :
    -- The `n`-th cohomology sheaf of `RΓ_S(ℚ)`.
    (complexSupportInjectiveComplex X S).homology (n : ℤ) ≅
      𝓗_[S]^n(TopCat.of (ComplexPoint X); ℚ) :=
  letI : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X
  (asIso (HomologicalComplex.homologyMap
    (complexSupportedSingularToAmbientInjective X S.compl) (n : ℤ))).symm ≪≫
      supportedSingularCohomologySheafIsoRelative
        (TopCat.of (ComplexPoint X)) S S.isClosed n

section

variable {Y : Over (Spec ↧ℂ)} (i : Y ⟶ X)
  [IsIntegral Y.left] [IsClosedImmersion i.left]
  {p : ℕ} (hi : Order.coheight (closedEmbeddingGenericPoint i) = p)

/-- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`, the cohomology of `X(ℂ)` with support in `Z(ℂ)`, where `Z` is the
image of `i`. It is computed as `H^{2p}(Γ(X(ℂ), RΓ_{Z(ℂ)}(ℚ)))` in the fixed injective
resolution. -/
abbrev ClosedEmbeddingSupportedCohomology (p : ℕ) : AddCommGrpCat :=
  -- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`, with `Z` the image of `i`.
  (((TopCat.Sheaf.supportEvaluation
    -- `X(ℂ)`.
    (TopCat.of (ComplexPoint X))
    -- Global sections, i.e. sections over all of `X(ℂ)`.
    ⊤).mapHomologicalComplex ℤᵘᵖ).obj
    -- `RΓ_{Z(ℂ)}(ℚ)`.
    (complexSupportInjectiveComplex X
      -- `Z(ℂ)`, as a closed subset of `X(ℂ)`.
      (closedEmbeddingAnalyticClosedSupport i))).homology
    -- Degree `2p`.
    (2 * (p : ℤ))

/-- `Γ(X(ℂ) \ Z_sing(ℂ), 𝓗^{2p}_{Z(ℂ)})`: sections over the complement of the singular locus of
`Z` of the sheaf `𝓗^{2p}_{Z(ℂ)}` associated with `V ↦ H^{2p}(V, V \ Z(ℂ); ℚ)`. -/
abbrev ClosedEmbeddingSmoothCoclassSections (p : ℕ) : AddCommGrpCat :=
  -- Sections of `𝓗^{2p}_{Z(ℂ)}` over `X(ℂ) \ Z_sing(ℂ)`, with support `Z(ℂ)` and degree `2p`.
  (𝓗_[closedEmbeddingSupport i]^(2 * p)(TopCat.of (ComplexPoint X); ℚ)).obj.obj
      -- The open `X(ℂ) \ Z_sing(ℂ)`.
      (op (closedEmbeddingSmoothSupportAmbientOpen i))

/-- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ) ≅ Γ(X(ℂ) \ Z_sing(ℂ), 𝓗^{2p}_{Z(ℂ)})`, as the composite of three
isomorphisms: restriction to `X(ℂ) \ Z_sing(ℂ)`, which is bijective because supported cohomology
of `Z_sing(ℂ)` vanishes in degrees `2p` and `2p + 1`; passage to sections of the lowest nonzero
cohomology sheaf, by purity along `Z(ℂ) \ Z_sing(ℂ)`; and the identification of that sheaf with
`𝓗^{2p}_{Z(ℂ)}`. -/
def closedEmbeddingSupportedClassNormalizationIso :
    ClosedEmbeddingSupportedCohomology i p ≅
      ClosedEmbeddingSmoothCoclassSections i p :=
  have he : ((2 * p : ℕ) : ℤ) = 2 * (p : ℤ) := by omega
  closedEmbeddingSupportExtensionIso i hi ≪≫
    closedEmbeddingSmoothSupportLowestSectionCohomologyIso i hi ≪≫
      (he ▸ (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
        (closedEmbeddingSmoothSupportAmbientOpen i)).mapIso
          (complexSupportInjectiveCohomologySheafIsoRelative
            (closedEmbeddingAnalyticClosedSupport i) (2 * p)))

/-- `Γ(X(ℂ) \ Z_sing(ℂ), 𝓗^{2p}_{Z(ℂ)}) → H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`: a section on the complement of
the singular locus extends uniquely across `Z_sing(ℂ)`. This is the inverse of the normalization
isomorphism; no extension datum is supplied. -/
def closedEmbeddingExtendSmoothCoclass :
    ClosedEmbeddingSmoothCoclassSections i p →+
      ClosedEmbeddingSupportedCohomology i p :=
  (closedEmbeddingSupportedClassNormalizationIso i hi).inv.hom

/-- The class in `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)` that extends the normalized section of `𝓗^{2p}_{Z(ℂ)}`
on `X(ℂ) \ Z_sing(ℂ)` across the singular locus. -/
def closedEmbeddingSupportedInjectiveClass : ClosedEmbeddingSupportedCohomology i p :=
  closedEmbeddingExtendSmoothCoclass i hi
    (closedEmbeddingSmoothSupportCoclassSection i hi)

/-- The same class in `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`, in the mapping-cone presentation of cohomology
with support. The comparison includes the cone sign that support forgetting needs. -/
def closedEmbeddingSheafSupportedClass :
    -- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`, in the support-cone presentation.
    RationalCohomologyWithSupport X
      -- `Z(ℂ)`.
      (closedEmbeddingSupport i)
      -- Degree `2p`.
      (2 * (p : ℤ)) :=
  (rationalSupportAddEquivSupportedInjectiveHomology X (closedEmbeddingSupport i)
    (closedEmbeddingAnalyticClosedSupport i).isClosed (2 * (p : ℤ))).symm
      (closedEmbeddingSupportedInjectiveClass i hi)

/-- **Step 3.** The class `[Z] ∈ H^{2p}(X(ℂ); ℚ)` of the closed subvariety `Z` presented by the
closed embedding `i`: the image of the supported class of step 2 under
`H^{2p}_{Z(ℂ)}(X(ℂ); ℚ) → H^{2p}(X(ℂ); ℚ)`.

This is the composite of the three steps, not a second route into ordinary cohomology; the
agreement with `forgetSupport` is therefore definitional rather than a theorem. -/
def closedEmbeddingSheafClass : H^(2 * (p : ℤ))(X; ℚ) :=
  forgetSupport X (closedEmbeddingSupport i) (2 * (p : ℤ))
    (closedEmbeddingSheafSupportedClass i hi)

/-- The class `[Z] ∈ H^{2p}(X(ℂ); ℚ)` of the integral subvariety `Z` with generic point `x`: the
class of the closed embedding of the reduced closure of `x`. -/
def cycleComponentSheafClass (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) {p : ℕ} (hx : Order.coheight x = p) : H^(2 * (p : ℤ))(X; ℚ) :=
  closedEmbeddingSheafClass (cycleComponentOverι X x)
    (by rwa [closedEmbeddingGenericPoint_cycleComponentOverι])

end

variable (X)

/-- The rational span of the constructed codimension-`p` component classes.

The relative dimension is the canonical `dim X`, whose certificate is proved from smoothness and
integrality. This definition spans explicit normalized component classes. -/
def algebraicCycleClassSpan (p : ℕ) : Submodule ℚ (H^(2 * (p : ℤ))(X; ℚ)) :=
  ⨆ (x : X.left) (hx : Order.coheight x = p),
    Submodule.span ℚ {cycleComponentSheafClass X x hx}

end AlgebraicGeometry.ComplexPoint
