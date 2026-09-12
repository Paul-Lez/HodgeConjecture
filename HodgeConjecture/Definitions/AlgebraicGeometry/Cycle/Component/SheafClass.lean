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
# Constructed sheaf cycle classes in arbitrary codimension

The exactly normalized normal-chart coclass on a component's smooth locus is
transported to the actual supported cohomology sheaf. Lowest-degree purity
and the proved unique extension across the singular boundary then give an
actual supported class on the original ambient variety. Forgetting support
lands in the repository's ordinary rational cohomology.

All comparison maps, purity statements, and extension isomorphisms are
constructed. No fundamental-class, orientation, duality, or vanishing datum
is an argument. The corresponding Borel–Moore fundamental class is obtained
through the previously constructed complex-orientation duality for the actual
ambient chain sheaf. This does not assert intrinsic compactification
independence or rational-equivalence invariance.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance cycleComponentSheafClassAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- The actual supported injective cohomology sheaf is the sheaf of local
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
Each of the three arrows is an actual proved isomorphism. -/
def cycleComponentSupportedClassNormalizationIso :
    CycleComponentSupportedCohomology X x p ≅
      CycleComponentSmoothCoclassSections X x p := by
  refine cycleComponentSupportExtensionIso X x (d := dim X.left) hx ≪≫
    cycleComponentSmoothSupportLowestSectionCohomologyIso X x (d := dim X.left) hx ≪≫ ?_
  let e := (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (cycleComponentSmoothSupportAmbientOpen X x)).mapIso
        (complexSupportInjectiveCohomologySheafIsoRelative X
          (cycleComponentAnalyticClosedSupport X x) (2 * p))
  have he : ((2 * p : ℕ) : ℤ) = 2 * (p : ℤ) := by omega
  dsimp only [TopCat.Sheaf.supportEvaluation, Functor.comp_obj] at e
  rw [he] at e
  exact e

/-- Extend a smooth-locus coclass uniquely across the singular boundary.
The inverse comes from proved purity and boundary vanishing; no extension datum is supplied. -/
def cycleComponentExtendSmoothCoclass :
    CycleComponentSmoothCoclassSections X x p →+
      CycleComponentSupportedCohomology X x p :=
  (cycleComponentSupportedClassNormalizationIso X x hx).inv.hom

/-- The actual globally supported class extending the exact complex-normal
coclass. The inverse is that of the proved normalization isomorphism. -/
def cycleComponentSupportedInjectiveClass : CycleComponentSupportedCohomology X x p :=
  cycleComponentExtendSmoothCoclass X x hx
    (cycleComponentSmoothSupportCoclassSection X x (d := dim X.left) hx)

/-- The constructed class in the existing support-cone presentation. Its
comparison includes the proved cone sign required by actual support forgetting. -/
def cycleComponentSheafSupportedClass :
    RationalCohomologyWithSupport X (cycleComponentSupport X x) (2 * (p : ℤ)) :=
  (rationalSupportAddEquivSupportedInjectiveHomology X (cycleComponentSupport X x)
    (cycleComponentAnalyticClosedSupport X x).isClosed (2 * (p : ℤ))).symm
      (cycleComponentSupportedInjectiveClass X x hx)

/-- The unconditional ordinary class of an arbitrary integral component.
This uses the literal inclusion of supported injective sections. -/
def cycleComponentSheafClass : H^(2 * (p : ℤ))(X; ℚ) :=
  (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * (p : ℤ))).symm
    (HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl ⊤
        (ambientRationalInjectiveComplex X)).f (2 * (p : ℤ))
      (cycleComponentSupportedInjectiveClass X x hx))

include X hx in
omit [IsProjective X.hom] in
/-- The dimension bound needed for the Borel–Moore degree, not an extra input. -/
theorem cycleComponentSheafClass_codimension_le : p ≤ dim X.left := by
  have h := SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := dim X.left) x
  rw [hx] at h
  exact_mod_cast h

end AlgebraicGeometry.ComplexPoint
