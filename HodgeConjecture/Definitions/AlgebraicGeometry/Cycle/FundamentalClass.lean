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

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `S ⊆ X(ℂ)` closed. For a natural
number `n`, this identifies the degree-`n` cohomology sheaf of `Γ_S(I^•)` with the
sheafification of `V ↦ H^n(V, V \ S; ℚ)`. Here `ℚ → I^•` is an injective resolution and `Γ_S`
takes sections vanishing off `S`. -/
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

variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. For a natural number `p`, this is `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`,
computed from global sections of the subsheaves supported in `Z(ℂ)` of a chosen injective
resolution of the constant rational sheaf. -/
abbrev CycleComponentSupportedCohomology (p : ℕ) : AddCommGrpCat :=
  AddCommGrpCat.of (H_[cycleComponentAnalyticClosedSupport X x]^(2 * p)(X; ℚ))

/-- Let `X` be a smooth integral projective scheme over `ℂ`, let `x` be a scheme point, and let `Z`
be its reduced closure in `X`. Write `S = Z(ℂ)`, `U = X(ℂ) \ Z_sing(ℂ)`, and `𝓗^{2p}_S` for the
sheafification of `V ↦ H^{2p}(V, V \ S; ℚ)`. For a natural number `p`, this is the abelian group
`Γ(U, 𝓗^{2p}_S)` of sections of the local relative-cohomology sheaf away from the singular locus
of `Z`. -/
abbrev CycleComponentSmoothCoclassSections (p : ℕ) : AddCommGrpCat :=
  -- Sections of `𝓗^{2p}_{Z(ℂ)}` over `X(ℂ) \ Z_sing(ℂ)`, with support `Z(ℂ)` and degree `2p`.
  (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (cycleComponentSmoothSupportAmbientOpen X x)).obj
    (𝓗_[cycleComponentSupport X x]^(2 * p)(TopCat.of (ComplexPoint X); ℚ))

set_option maxHeartbeats 800000 in
/-- The restricted supported Ext group is the normalized coclass section group. -/
def cycleComponentSmoothSupportLowestSectionCohomologyEquiv :
    CategoryTheory.Sheaf.relH
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
        (2 * p)
        (homOfLE (cycleComponentSupportComplement_le_smoothAmbientOpen X x)) ≃+
      CycleComponentSmoothCoclassSections X x p := by
  let T := TopCat.of (ComplexPoint X)
  let Z := cycleComponentAnalyticClosedSupport X x
  let U := cycleComponentSmoothSupportAmbientOpen X x
  let h := cycleComponentSupportComplement_le_smoothAmbientOpen X x
  let hW : U ⊓ Z.compl = Z.compl := inf_eq_right.mpr h
  let F := (TopCat.Sheaf.constantFunctor T).obj (AddCommGrpCat.of ℚ)
  let n : ℕ := 2 * p
  let bridge := @TopCat.Sheaf.relHAddEquivSupportedSectionsHomology T Z.compl U Z.compl
    hW (analyticHasExt X) F (ambientRationalInjectiveComplex X)
    (ambientRationalInjectiveComplex_isKInjective X)
    (ambientRationalInjectiveSingleAugmentation X)
    (ambientRationalInjectiveSingleAugmentation_quasiIso X) n
  let lowest :
      ((((TopCat.Sheaf.supportEvaluation T U).mapHomologicalComplex ℤᵘᵖ).obj
        (((TopCat.Sheaf.sheafSectionsSupportedOutside T Z.compl).mapHomologicalComplex ℤᵘᵖ).obj
          (ambientRationalInjectiveComplex X))).homology (n : ℤ)) ≅
        (TopCat.Sheaf.supportEvaluation T U).obj
          ((complexSupportInjectiveComplex X Z).homology (n : ℤ)) := by
    change _ ≅
      ((complexSupportInjectiveComplex X Z).homology (n : ℤ)).presheaf.obj (op U)
    exact cycleComponentSmoothSupportLowestSectionCohomologyComplexIso X x hx
  let sheaf := (TopCat.Sheaf.supportEvaluation T U).mapIso
    (complexSupportInjectiveCohomologySheafIsoRelative X Z n)
  change CategoryTheory.Sheaf.relH F n (homOfLE h) ≃+
    (TopCat.Sheaf.supportEvaluation T U).obj (𝓗_[Z]^n(T; ℚ))
  exact bridge.trans (lowest.addCommGroupIsoToAddEquiv.trans sheaf.addCommGroupIsoToAddEquiv)

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the codimension-`p`
integral subvariety with generic point `x`. Write `S = Z(ℂ)`, `U = X(ℂ) \ Z_sing(ℂ)`, and
`𝓗^{2p}_S` for the sheafification of `V ↦ H^{2p}(V, V \ S; ℚ)`. This is the isomorphism
`H^{2p}_S(X(ℂ); ℚ) ≅ Γ(U, 𝓗^{2p}_S)`. It restricts a supported class to `U` and takes its local
relative classes. Purity on the smooth locus and vanishing of cohomology supported on the
singular locus make the map invertible. -/
def cycleComponentSupportedClassNormalizationIso :
    CycleComponentSupportedCohomology X x p ≃+ CycleComponentSmoothCoclassSections X x p :=
  cycleComponentSupportExtensionIso X x hx |>.trans <|
    cycleComponentSmoothSupportLowestSectionCohomologyEquiv X x hx

/-- Let `X` be a smooth integral projective scheme over `ℂ` and let `Z` be the codimension-`p`
integral subvariety with generic point `x`. Write `S = Z(ℂ)`, `U = X(ℂ) \ Z_sing(ℂ)`, and
`𝓗^{2p}_S` for the sheafification of `V ↦ H^{2p}(V, V \ S; ℚ)`. This additive map `Γ(U,
𝓗^{2p}_S) → H^{2p}_S(X(ℂ); ℚ)` assigns to a section its unique supported class on all of `X(ℂ)`.
It inverts restriction followed by passage to local relative-cohomology classes. -/
def cycleComponentExtendSmoothCoclass :
    CycleComponentSmoothCoclassSections X x p →+ CycleComponentSupportedCohomology X x p :=
  (cycleComponentSupportedClassNormalizationIso X x hx).symm.toAddMonoidHom

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `Z` the codimension-`p` integral
subvariety with generic point `x`. This is the class in `H^{2p}_{Z(ℂ)}(X(ℂ);ℚ)` computed from
sections supported on `Z(ℂ)` of an injective resolution of the constant rational sheaf. Its
local classes along the smooth locus of `Z` evaluate to `1` on the complex orientation classes
of the normal spaces. -/
def cycleComponentSupportedInjectiveClass : CycleComponentSupportedCohomology X x p :=
  cycleComponentExtendSmoothCoclass X x hx
    (cycleComponentSmoothSupportCoclassSection X x hx)

/-- Let `X` be a smooth integral projective scheme over `ℂ` and `Z` the codimension-`p` integral
subvariety with generic point `x`. This is the class in `H^{2p}_{Z(ℂ)}(X(ℂ);ℚ)` whose local classes
along the smooth locus of `Z` evaluate to `1` on the complex orientation classes of the normal
spaces. -/
def cycleComponentSheafSupportedClass :
    -- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`.
    H_[cycleComponentAnalyticClosedSupport X x]^(2 * p)(X; ℚ) :=
  cycleComponentSupportedInjectiveClass X x hx

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
