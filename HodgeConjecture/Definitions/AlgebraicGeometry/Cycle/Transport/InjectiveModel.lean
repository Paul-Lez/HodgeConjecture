/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportConeForget
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SupportExtension
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SingularCohomologySheafComparison
/-!
# The injective model of supported cohomology, and its comparisons

Three presentations of degree-`2p` cohomology with support in a component meet here.

* the **mapping-cone model** `RationalCohomologyWithSupport X Z n`, which is the one the
  statement uses and the one `forgetSupport` maps out of;
* the **injective model**, the degree-`2p` homology of the globally supported sections of
  a fixed injective resolution, written `CycleComponentSupportedCohomology`;
* the **relative-cohomology sheaf**, whose sections on the smooth-locus ambient open are
  written `CycleComponentSmoothCoclassSections`.

The injective model is a computation device: purity and boundary vanishing are proved in
it, because that is where a resolution can be restricted to an open and truncated. It is
not the model the construction is *stated* in. This file is where it is confined, and
`cycleComponentSupportedClassEquiv` is the bridge that lets
`Cycle/FundamentalClass.lean` state the extension step in the mapping-cone model without
ever naming a resolution.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance cycleComponentSheafClassAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- The supported injective cohomology sheaf is the sheaf of local
relative cohomology, by the constructed singular resolution and its literal
restriction-natural comparison. -/
def complexSupportInjectiveCohomologySheafIsoRelative
    (S : Closeds (ComplexPoint X)) (n : ℕ) :
    (complexSupportInjectiveComplex X S).homology (n : ℤ) ≅
      supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) S n := by
  let : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X
  exact (asIso (HomologicalComplex.homologyMap
    (complexSupportedSingularToAmbientInjective X S.compl) (n : ℤ))).symm ≪≫
      supportedSingularCohomologySheafIsoRelative
        (TopCat.of (ComplexPoint X)) S S.isClosed n

variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- Degree-`2p` cohomology of global sections supported on the component,
computed in the fixed ambient injective resolution. -/
abbrev CycleComponentSupportedCohomology (p : ℕ) : AddCommGrpCat :=
  (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
    (.up ℤ)).obj (complexSupportInjectiveComplex X
      (cycleComponentAnalyticClosedSupport X x))).homology (2 * (p : ℤ))

/-- Sections of the local relative-cohomology sheaf on the smooth-locus ambient open. -/
abbrev CycleComponentSmoothCoclassSections (p : ℕ) : AddCommGrpCat :=
  (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
    (cycleComponentSupport X x) (2 * p)).obj.obj
      (op (cycleComponentSmoothSupportAmbientOpen X x))

/-- Supported cohomology on the full component is identified with sections
of the local relative-cohomology sheaf on its smooth-locus ambient open.
Each of the three arrows is a proved isomorphism. -/
def cycleComponentSupportedClassNormalizationIso :
    CycleComponentSupportedCohomology X x p ≅
      CycleComponentSmoothCoclassSections X x p := by
  refine cycleComponentSupportExtensionIso X x hx ≪≫
    cycleComponentSmoothSupportLowestSectionCohomologyIso X x hx ≪≫ ?_
  let e := (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (cycleComponentSmoothSupportAmbientOpen X x)).mapIso
        (complexSupportInjectiveCohomologySheafIsoRelative X
          (cycleComponentAnalyticClosedSupport X x) (2 * p))
  have he : ((2 * p : ℕ) : ℤ) = 2 * (p : ℤ) := by omega
  dsimp only [TopCat.Sheaf.supportEvaluation, Functor.comp_obj] at e
  rw [he] at e
  exact e

/-- The class in the injective model extending the exact complex-normal coclass. -/
def cycleComponentSupportedInjectiveClass : CycleComponentSupportedCohomology X x p :=
  (cycleComponentSupportedClassNormalizationIso X x hx).inv.hom
    (cycleComponentSmoothSupportCoclassSection X x hx)

/-- The bridge out of the injective model: degree-`2p` cohomology with support in the
component, in the mapping-cone model the statement uses, is identified with sections of the
relative-cohomology sheaf on the smooth-locus ambient open.

Composing the cone/injective comparison with the normalization isomorphism above hides the
resolution: everything downstream of this equivalence is stated in the mapping-cone model. -/
def cycleComponentSupportedClassEquiv :
    RationalCohomologyWithSupport X (cycleComponentSupport X x) (2 * (p : ℤ)) ≃+
      CycleComponentSmoothCoclassSections X x p :=
  (rationalSupportAddEquivSupportedInjectiveHomology X (cycleComponentSupport X x)
      (cycleComponentAnalyticClosedSupport X x).isClosed (2 * (p : ℤ))).trans
    (cycleComponentSupportedClassNormalizationIso X x hx).addCommGroupIsoToAddEquiv

end AlgebraicGeometry.ComplexPoint
