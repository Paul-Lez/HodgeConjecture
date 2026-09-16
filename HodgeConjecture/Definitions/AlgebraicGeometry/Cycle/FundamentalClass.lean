/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportConeForget
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SupportExtension
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularCohomologySheafComparison
/-!
# Constructed sheaf cycle classes in arbitrary codimension

The exactly normalized normal-chart coclass on a component's smooth locus is
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

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance cycleComponentSheafClassAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- `𝓗^n(RΓ_S(ℚ)) ≅ 𝓗^n_S` for a closed `S ⊆ X(ℂ)`: the `n`-th cohomology sheaf of `RΓ_S(ℚ)`, the
`S`-supported part of the injective resolution of `ℚ` on `X(ℂ)`, is the sheaf associated with
`V ↦ H^n(V, V \ S; ℚ)`. The comparison goes through the singular resolution. -/
def complexSupportInjectiveCohomologySheafIsoRelative
    (S : Closeds (ComplexPoint X)) (n : ℕ) :
    -- The `n`-th cohomology sheaf of `RΓ_S(ℚ)`.
    (complexSupportInjectiveComplex X S).homology (n : ℤ) ≅
      -- The sheaf `𝓗^n_S` associated with `V ↦ H^n(V, V \ S; ℚ)`.
      supportRelativeCohomologySheaf
        -- `X(ℂ)`.
        (TopCat.of (ComplexPoint X)) S n :=
  letI : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X
  (asIso (HomologicalComplex.homologyMap
    (complexSupportedSingularToAmbientInjective X S.compl) (n : ℤ))).symm ≪≫
      supportedSingularCohomologySheafIsoRelative
        (TopCat.of (ComplexPoint X)) S S.isClosed n

variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`, the cohomology of `X(ℂ)` with support in `Z(ℂ)`, where `Z` is the
closure of `x`. It is computed as `H^{2p}(Γ(X(ℂ), RΓ_{Z(ℂ)}(ℚ)))` in the fixed injective
resolution. -/
abbrev CycleComponentSupportedCohomology (p : ℕ) : AddCommGrpCat :=
  -- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`, with `Z` the subvariety with generic point `x`.
  (((TopCat.Sheaf.supportEvaluation
    -- `X(ℂ)`.
    (TopCat.of (ComplexPoint X))
    -- Global sections, i.e. sections over all of `X(ℂ)`.
    ⊤).mapHomologicalComplex (.up ℤ)).obj
    -- `RΓ_{Z(ℂ)}(ℚ)`.
    (complexSupportInjectiveComplex X
      -- `Z(ℂ)`, as a closed subset of `X(ℂ)`.
      (cycleComponentAnalyticClosedSupport X x))).homology
    -- Degree `2p`.
    (2 * (p : ℤ))

/-- `Γ(X(ℂ) \ Z_sing(ℂ), 𝓗^{2p}_{Z(ℂ)})`: sections over the complement of the singular locus of
`Z` of the sheaf `𝓗^{2p}_{Z(ℂ)}` associated with `V ↦ H^{2p}(V, V \ Z(ℂ); ℚ)`. -/
abbrev CycleComponentSmoothCoclassSections (p : ℕ) : AddCommGrpCat :=
  -- Sections of `𝓗^{2p}_{Z(ℂ)}` over `X(ℂ) \ Z_sing(ℂ)`.
  (supportRelativeCohomologySheaf
    -- `X(ℂ)`.
    (TopCat.of (ComplexPoint X))
    -- `Z(ℂ)`.
    (cycleComponentSupport X x)
    -- Degree `2p`.
    (2 * p)).obj.obj
      -- The open `X(ℂ) \ Z_sing(ℂ)`.
      (op (cycleComponentSmoothSupportAmbientOpen X x))

/-- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ) ≅ Γ(X(ℂ) \ Z_sing(ℂ), 𝓗^{2p}_{Z(ℂ)})`, as the composite of three
isomorphisms: restriction to `X(ℂ) \ Z_sing(ℂ)`, which is bijective because supported cohomology
of `Z_sing(ℂ)` vanishes in degrees `2p` and `2p + 1`; passage to sections of the lowest nonzero
cohomology sheaf, by purity along `Z(ℂ) \ Z_sing(ℂ)`; and the identification of that sheaf with
`𝓗^{2p}_{Z(ℂ)}`. -/
def cycleComponentSupportedClassNormalizationIso :
    CycleComponentSupportedCohomology X x p ≅
      CycleComponentSmoothCoclassSections X x p :=
  have he : ((2 * p : ℕ) : ℤ) = 2 * (p : ℤ) := by omega
  cycleComponentSupportExtensionIso X x hx ≪≫
    cycleComponentSmoothSupportLowestSectionCohomologyIso X x hx ≪≫
      (he ▸ (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
        (cycleComponentSmoothSupportAmbientOpen X x)).mapIso
          (complexSupportInjectiveCohomologySheafIsoRelative X
            (cycleComponentAnalyticClosedSupport X x) (2 * p)))

/-- `Γ(X(ℂ) \ Z_sing(ℂ), 𝓗^{2p}_{Z(ℂ)}) → H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`: a section on the complement of
the singular locus extends uniquely across `Z_sing(ℂ)`. This is the inverse of the normalization
isomorphism; no extension datum is supplied. -/
def cycleComponentExtendSmoothCoclass :
    CycleComponentSmoothCoclassSections X x p →+
      CycleComponentSupportedCohomology X x p :=
  (cycleComponentSupportedClassNormalizationIso X x hx).inv.hom

/-- The class in `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)` that extends the normalized section of `𝓗^{2p}_{Z(ℂ)}`
on `X(ℂ) \ Z_sing(ℂ)` across the singular locus. -/
def cycleComponentSupportedInjectiveClass : CycleComponentSupportedCohomology X x p :=
  cycleComponentExtendSmoothCoclass X x hx
    (cycleComponentSmoothSupportCoclassSection X x hx)

/-- The same class in `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`, in the mapping-cone presentation of cohomology
with support. The comparison includes the cone sign that support forgetting needs. -/
def cycleComponentSheafSupportedClass :
    -- `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ)`, in the support-cone presentation.
    RationalCohomologyWithSupport X
      -- `Z(ℂ)`.
      (cycleComponentSupport X x)
      -- Degree `2p`.
      (2 * (p : ℤ)) :=
  (rationalSupportAddEquivSupportedInjectiveHomology X (cycleComponentSupport X x)
    (cycleComponentAnalyticClosedSupport X x).isClosed (2 * (p : ℤ))).symm
      (cycleComponentSupportedInjectiveClass X x hx)

/-- **Step 3.** The class `[Z] ∈ H^{2p}(X(ℂ); ℚ)` of the integral subvariety `Z` with generic
point `x`: the image of the supported class of step 2 under `H^{2p}_{Z(ℂ)}(X(ℂ); ℚ) →
H^{2p}(X(ℂ); ℚ)`.

This is the composite of the three steps, not a second route into ordinary cohomology; the
agreement with `forgetSupport` is therefore definitional rather than a theorem. -/
def cycleComponentSheafClass : H^(2 * (p : ℤ))(X; ℚ) :=
  forgetSupport X (cycleComponentSupport X x) (2 * (p : ℤ))
    (cycleComponentSheafSupportedClass X x hx)

end AlgebraicGeometry.ComplexPoint
