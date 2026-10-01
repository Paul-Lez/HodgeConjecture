/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.WithSupport
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SupportExtension
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
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

section

variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. For a natural number `p`, this is the Ext group
`H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`. -/
abbrev CycleComponentSupportedCohomology (p : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of (H_[cycleComponentAnalyticClosedSupport X x]^(2 * p)(X; ℚ))

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. Write `S = Z(ℂ)`, `U = X(ℂ) \ Z_sing(ℂ)`, and `𝓗^{2p}_S` for the
sheafification of `V ↦ H^{2p}(V, V \ S; ℚ)`. For a natural number `p`, this is the abelian group
`Γ(U, 𝓗^{2p}_S)` of sections of the local relative-cohomology sheaf away from the singular locus
of `Z`. -/
abbrev CycleComponentSmoothCoclassSections (p : ℕ) : AddCommGrpCat :=
  -- Sections of `𝓗^{2p}_{Z(ℂ)}` over `X(ℂ) \ Z_sing(ℂ)`, with support `Z(ℂ)` and degree `2p`.
  (𝓗_[cycleComponentSupport X x]^(2 * p)(TopCat.of (ComplexPoint X); ℚ)).presheaf.obj
    (op (cycleComponentSmoothSupportAmbientOpen X x))

/-- Purity below degree `2p` identifies supported Ext on `X(ℂ) \ Z_sing(ℂ)` with the sections of
`𝓗_[Z]^(2p)` on that open. -/
def cycleComponentSmoothSupportLowestSectionCohomologyEquiv :
    CategoryTheory.Sheaf.relH
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
        (2 * p)
        (homOfLE (cycleComponentSupportComplement_le_smoothAmbientOpen X x)) ≃+
      CycleComponentSmoothCoclassSections X x p :=
  rationalSupportAddEquivSupportedRelativeCohomologySheafSectionOnOpen X
    (cycleComponentAnalyticClosedSupport X x)
    (cycleComponentSmoothSupportAmbientOpen X x)
    (cycleComponentAnalyticClosedSupport X x).compl
    (inf_eq_right.mpr (cycleComponentSupportComplement_le_smoothAmbientOpen X x)) (2 * p)
    (fun j hj => cycleComponentSmoothSupportCohomologySheaf_isZero_of_ne X x hx j
      (Nat.ne_of_lt hj))

/-- Restriction to the smooth ambient open and passage to local relative-cohomology sections
identifies the supported cycle-class group with its normalized coclass sections. -/
def cycleComponentSupportedClassNormalizationIso :
    CycleComponentSupportedCohomology X x p ≃+ CycleComponentSmoothCoclassSections X x p :=
  cycleComponentSupportExtensionIso X x hx |>.trans <|
    cycleComponentSmoothSupportLowestSectionCohomologyEquiv (p := p) X x hx

/-- The supported cycle class is the unique class whose restriction to the smooth ambient open is
the normalized coclass section. -/
def cycleComponentSupportedInjectiveClass : CycleComponentSupportedCohomology X x p :=
  (cycleComponentSupportedClassNormalizationIso X x hx).symm.toAddMonoidHom
    (cycleComponentSmoothSupportCoclassSection X x hx)

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `Z` the codimension-`p` integral
subvariety with generic point `x`. The fundamental cohomology class `[Z] ∈ H^{2p}(X(ℂ);ℚ)` is
obtained by forgetting the support of the class in `H^{2p}_{Z(ℂ)}(X(ℂ);ℚ)` whose local classes
along the smooth locus evaluate to `1` on the complex orientation classes of the normal spaces. -/
def cycleComponentSheafClass : H^(2 * p)(X; ℚ) :=
  forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X x) (2 * p)
    (cycleComponentSupportedInjectiveClass X x hx)

end

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `p` a natural number. This is the
rational subspace of `H^{2p}(X(ℂ); ℚ)` spanned by the fundamental cohomology classes of all
codimension-`p` integral closed subvarieties of `X`. Their classes are normalized by the complex
orientations of their normal spaces on their smooth loci. -/
def algebraicCycleClassSpan (p : ℕ) : Submodule ℚ (H^(2 * p)(X; ℚ)) :=
  sSup {Submodule.span ℚ {cycleComponentSheafClass X x hx} |
    (x : X.left) (hx : Order.coheight x = p) }

end AlgebraicGeometry.ComplexPoint
