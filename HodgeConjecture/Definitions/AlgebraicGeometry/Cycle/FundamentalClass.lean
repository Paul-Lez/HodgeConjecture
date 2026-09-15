/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportConeForget
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SupportExtension
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularCohomologySheafComparison
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.InjectiveCohomologySheafComparison
/-!
# Constructed sheaf cycle classes in arbitrary codimension

Purity identifies the normalized smooth-locus coclass with lowest-degree supported
cohomology. Boundary vanishing extends it uniquely across the singular locus. A model
comparison gives the supported class, and forgetting support gives the ordinary class.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance cycleComponentSheafClassAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- The supported injective cohomology sheaf is the sheaf of local
relative cohomology, by the constructed singular resolution and its literal
restriction-natural comparison. -/
def complexSupportInjectiveCohomologySheafIsoRelative
    {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (n : ℕ) :
    (complexSupportInjectiveComplex X S).homology (n : ℤ) ≅
      supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) S n :=
  letI : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X
  supportedRationalInjectiveCohomologySheafIsoRelative
    (TopCat.of (ComplexPoint X)) (exists_contractibleOpen_le X) S n

variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- Degree-`2p` cohomology of global sections supported on the component,
computed in the fixed ambient injective resolution. -/
abbrev CycleComponentSupportedCohomology (p : ℕ) : AddCommGrpCat :=
  (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
    (.up ℤ)).obj (complexSupportInjectiveComplex X
      (cycleComponentAnalyticClosedSupport X x))).homology (2 * (p : ℤ))

/-- Supported cohomology on the full component is identified with sections
of the local relative-cohomology sheaf on its smooth-locus ambient open.
Each of the three arrows is a proved isomorphism. -/
def cycleComponentSupportedClassNormalizationIso
    {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) {p : ℕ} (hx : Order.coheight x = p) :
    CycleComponentSupportedCohomology X x p ≅
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * p)).obj.obj
          (op (cycleComponentSmoothSupportAmbientOpen X x)) :=
  have he : ((2 * p : ℕ) : ℤ) = 2 * (p : ℤ) := by omega
  cycleComponentSupportExtensionIso X x hx ≪≫
    cycleComponentSmoothSupportLowestSectionCohomologyIso X x hx ≪≫
      (he ▸ (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
        (cycleComponentSmoothSupportAmbientOpen X x)).mapIso
          (complexSupportInjectiveCohomologySheafIsoRelative
            (cycleComponentAnalyticClosedSupport X x) (2 * p)))

/-- The supported injective-model class with the normalized smooth-locus restriction. -/
def cycleComponentSupportedInjectiveClass
    {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {x : X.left} {p : ℕ} (hx : Order.coheight x = p) :
    CycleComponentSupportedCohomology X x p :=
  (cycleComponentSupportedClassNormalizationIso x hx).inv
    (cycleComponentSmoothSupportCoclassSection X x hx)

/-- The constructed class in the existing support-cone presentation. Its
comparison includes the proved cone sign required by support forgetting. -/
def cycleComponentSheafSupportedClass :
    RationalCohomologyWithSupport X (cycleComponentSupport X x) (2 * (p : ℤ)) :=
  (rationalSupportAddEquivSupportedInjectiveHomology X (cycleComponentSupport X x)
    (cycleComponentAnalyticClosedSupport X x).isClosed (2 * (p : ℤ))).symm
      (cycleComponentSupportedInjectiveClass hx)

/-- The ordinary component class obtained by forgetting support. -/
def cycleComponentSheafClass : H^(2 * (p : ℤ))(X; ℚ) :=
  forgetSupport X (cycleComponentSupport X x) (2 * (p : ℤ))
    (cycleComponentSheafSupportedClass X x hx)

end AlgebraicGeometry.ComplexPoint
