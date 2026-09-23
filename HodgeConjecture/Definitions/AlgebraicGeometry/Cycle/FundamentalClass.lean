/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.WithSupport
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SupportExtension
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularCohomologySheafComparison
/-!
# Sheaf cycle classes in arbitrary codimension

The exactly normalized normal-chart coclass on a component's smooth locus is transported to the
supported cohomology sheaf. Lowest-degree purity and unique extension across the singular
boundary then give a supported class on the original ambient variety, and forgetting its support
lands in ordinary rational cohomology.

The corresponding Borel–Moore fundamental class is obtained through the complex-orientation
duality for the ambient chain sheaf. Compactification independence and rational-equivalence
invariance are separate statements.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance cycleComponentSheafClassAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

section

variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. For a natural number `p`, this is `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`,
computed from global sections of the subsheaves supported in `Z(ℂ)` of the sheafified rational
singular cochains. -/
abbrev CycleComponentSupportedCohomology (p : ℕ) : AddCommGrpCat :=
  -- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`, with `Z` the subvariety with generic point `x`.
  (((TopCat.Sheaf.supportEvaluation
    -- `X(ℂ)`.
    (TopCat.of (ComplexPoint X))
    -- Global sections, i.e. sections over all of `X(ℂ)`.
    ⊤).mapHomologicalComplex ℤᵘᵖ).obj
    -- `RΓ_{Z(ℂ)}(ℚ)`.
    (complexSupportSingularComplex X
      -- `Z(ℂ)`, as a closed subset of `X(ℂ)`.
      (cycleComponentAnalyticClosedSupport X x))).homology
    -- Degree `2p`.
    (2 * (p : ℤ))

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. Write `S = Z(ℂ)`, `U = X(ℂ) \ Z_sing(ℂ)`, and `𝓗^{2p}_S` for the
sheafification of `V ↦ H^{2p}(V, V \ S; ℚ)`. For a natural number `p`, this is the abelian group
`Γ(U, 𝓗^{2p}_S)` of sections of the local relative-cohomology sheaf away from the singular locus
of `Z`. -/
abbrev CycleComponentSmoothCoclassSections (p : ℕ) : AddCommGrpCat :=
  -- Sections of `𝓗^{2p}_{Z(ℂ)}` over `X(ℂ) \ Z_sing(ℂ)`, with support `Z(ℂ)` and degree `2p`.
  (𝓗_[cycleComponentSupport X x]^(2 * p)(TopCat.of (ComplexPoint X); ℚ)).presheaf.obj
      -- The open `X(ℂ) \ Z_sing(ℂ)`.
      (op (cycleComponentSmoothSupportAmbientOpen X x))

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the codimension-`p`
integral subvariety with generic point `x`. Write `S = Z(ℂ)`, `U = X(ℂ) \ Z_sing(ℂ)`, and
`𝓗^{2p}_S` for the sheafification of `V ↦ H^{2p}(V, V \ S; ℚ)`. This is the isomorphism
`H^{2p}_S(X(ℂ); ℚ) ≅ Γ(U, 𝓗^{2p}_S)`. It restricts a supported class to `U` and takes its local
relative classes. Purity on the smooth locus and vanishing of cohomology supported on the
singular locus make the map invertible. -/
def cycleComponentSupportedClassNormalizationIso :
    CycleComponentSupportedCohomology X x p ≅ CycleComponentSmoothCoclassSections X x p :=
  have he : ((2 * p : ℕ) : ℤ) = 2 * (p : ℤ) := by omega
  cycleComponentSupportExtensionIso X x hx ≪≫
    cycleComponentSmoothSupportLowestSectionCohomologyIso X x hx ≪≫
      (he ▸ (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
        (cycleComponentSmoothSupportAmbientOpen X x)).mapIso
          (letI : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X
          supportedSingularCohomologySheafIsoRelative (TopCat.of (ComplexPoint X))
            (cycleComponentAnalyticClosedSupport X x)
            (cycleComponentAnalyticClosedSupport X x).isClosed (2 * p)))

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the codimension-`p`
integral subvariety with generic point `x`. Write `S = Z(ℂ)`, `U = X(ℂ) \ Z_sing(ℂ)`, and
`𝓗^{2p}_S` for the sheafification of `V ↦ H^{2p}(V, V \ S; ℚ)`. This additive map `Γ(U,
𝓗^{2p}_S) → H^{2p}_S(X(ℂ); ℚ)` assigns to a section its unique supported class on all of `X(ℂ)`.
It inverts restriction followed by passage to local relative-cohomology classes. -/
def cycleComponentExtendSmoothCoclass :
    CycleComponentSmoothCoclassSections X x p →+ CycleComponentSupportedCohomology X x p :=
  (cycleComponentSupportedClassNormalizationIso X x hx).inv.hom

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `Z` the codimension-`p` integral
subvariety with generic point `x`. This is the class in `H^{2p}_{Z(ℂ)}(X(ℂ);ℚ)` computed from
sections supported on `Z(ℂ)` of the sheafified rational singular cochains. Its
local classes along the smooth locus of `Z` evaluate to `1` on the complex orientation classes
of the normal spaces. -/
def cycleComponentSupportedSingularClass : CycleComponentSupportedCohomology X x p :=
  cycleComponentExtendSmoothCoclass X x hx
    (cycleComponentSmoothSupportCoclassSection X x hx)

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `Z` the codimension-`p` integral
subvariety with generic point `x`. This is the class in `H^{2p}_{Z(ℂ)}(X(ℂ);ℚ)` whose local classes
along the smooth locus of `Z` evaluate to `1` on the complex orientation classes of the normal
spaces. -/
def cycleComponentSheafSupportedClass :
    -- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`.
    H_[cycleComponentAnalyticClosedSupport X x]^(2 * p)(X; ℚ) :=
  have he : 2 * (p : ℤ) = ((2 * p : ℕ) : ℤ) := by omega
  (rationalSupportAddEquivSupportedSingularHomology X (cycleComponentAnalyticClosedSupport X x)
    (2 * p)).symm (he ▸ cycleComponentSupportedSingularClass X x hx)

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `Z` the codimension-`p` integral
subvariety with generic point `x`. The fundamental cohomology class `[Z] ∈ H^{2p}(X(ℂ);ℚ)` is
obtained by forgetting the support of the class in `H^{2p}_{Z(ℂ)}(X(ℂ);ℚ)` whose local classes
along the smooth locus evaluate to `1` on the complex orientation classes of the normal spaces. -/
def cycleComponentSheafClass : H^(2 * p)(X; ℚ) :=
  forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X x) (2 * p)
    (cycleComponentSheafSupportedClass X x hx)

end

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `p` a natural number. This is the
rational subspace of `H^{2p}(X(ℂ); ℚ)` spanned by the fundamental cohomology classes of all
codimension-`p` integral closed subvarieties of `X`. Their classes are normalized by the complex
orientations of their normal spaces on their smooth loci. -/
def algebraicCycleClassSpan (p : ℕ) : Submodule ℚ (H^(2 * p)(X; ℚ)) :=
  sSup {Submodule.span ℚ {cycleComponentSheafClass X x hx} |
    (x : X.left) (hx : Order.coheight x = p) }

end AlgebraicGeometry.ComplexPoint
