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

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance cycleComponentSheafClassAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- The supported injective cohomology sheaf is the sheaf of local
relative cohomology, by the singular resolution and its
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
Each of the three arrows is an isomorphism. -/
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

/-- Extend a smooth-locus coclass uniquely across the singular boundary. The inverse comes from
purity and boundary vanishing. -/
def cycleComponentExtendSmoothCoclass :
    CycleComponentSmoothCoclassSections X x p →+
      CycleComponentSupportedCohomology X x p :=
  (cycleComponentSupportedClassNormalizationIso X x hx).inv.hom

/-- The globally supported class extending the exact complex-normal
coclass. The inverse is that of the normalization isomorphism. -/
def cycleComponentSupportedInjectiveClass : CycleComponentSupportedCohomology X x p :=
  cycleComponentExtendSmoothCoclass X x hx
    (cycleComponentSmoothSupportCoclassSection X x hx)

/-- The component class in the support-cone presentation. The comparison carries the cone sign
required by support forgetting. -/
def cycleComponentSheafSupportedClass :
    RationalCohomologyWithSupport X (cycleComponentSupport X x) (2 * (p : ℤ)) :=
  (rationalSupportAddEquivSupportedInjectiveHomology X (cycleComponentSupport X x)
    (cycleComponentAnalyticClosedSupport X x).isClosed (2 * (p : ℤ))).symm
      (cycleComponentSupportedInjectiveClass X x hx)

/-- **Step 3.** The unconditional ordinary class of an arbitrary integral component: the
supported class of step 2, with its support forgotten.

Being the composite of the three steps, it agrees with `forgetSupport` definitionally. -/
def cycleComponentSheafClass : H^(2 * (p : ℤ))(X; ℚ) :=
  forgetSupport X (cycleComponentSupport X x) (2 * (p : ℤ))
    (cycleComponentSheafSupportedClass X x hx)

end AlgebraicGeometry.ComplexPoint
