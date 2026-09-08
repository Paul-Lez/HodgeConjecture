/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentSupportExtension
public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentSmoothSupportCoclassSection
public import HodgeConjecture.Other.AlgebraicGeometry.ComplexSheafBorelMooreRationalComparison
public import HodgeConjecture.Other.AlgebraicTopology.SupportedSingularCohomologySheafComparison

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

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec (.of ℂ))
  [IsIntegral X] [Smooth s] [IsProjective s]

local instance cycleComponentSheafClassAnalyticTopology :
    TopologicalSpace (ComplexPoint X s) := Point.analyticTopology

/-- The actual supported injective cohomology sheaf is the sheaf of local
relative cohomology, by the constructed singular resolution and its literal
restriction-natural comparison. -/
def complexSupportInjectiveCohomologySheafIsoRelative
    (S : Closeds (ComplexPoint X s)) (n : ℕ) :
    (complexSupportInjectiveComplex s S).homology (n : ℤ) ≅
      supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X s)) S n := by
  let : ∀ V : Opens (ComplexPoint X s), ParacompactSpace V := openParacompactSpace s
  exact (asIso (HomologicalComplex.homologyMap
    (complexSupportedSingularToAmbientInjective s S.compl) (n : ℤ))).symm ≪≫
      supportedSingularCohomologySheafIsoRelative
        (TopCat.of (ComplexPoint X s)) S S.isClosed n

variable (x : X) {d p : ℕ} [SmoothOfRelativeDimension d s]
  (hx : Order.coheight x = p)

/-- Supported cohomology on the full component is identified with sections
of the local relative-cohomology sheaf on its smooth-locus ambient open.
Each of the three arrows is an actual proved isomorphism. -/
def cycleComponentSupportedClassNormalizationIso :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex s
        (cycleComponentAnalyticClosedSupport s x))).homology (2 * (p : ℤ))) ≅
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X s))
        (cycleComponentSupport s x) (2 * p)).obj.obj
          (op (cycleComponentSmoothSupportAmbientOpen s x)) := by
  refine cycleComponentSupportExtensionIso s x (d := d) hx ≪≫
    cycleComponentSmoothSupportLowestSectionCohomologyIso s x (d := d) hx ≪≫ ?_
  let e := (TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s))
      (cycleComponentSmoothSupportAmbientOpen s x)).mapIso
        (complexSupportInjectiveCohomologySheafIsoRelative s
          (cycleComponentAnalyticClosedSupport s x) (2 * p))
  have he : ((2 * p : ℕ) : ℤ) = 2 * (p : ℤ) := by omega
  dsimp only [TopCat.Sheaf.supportEvaluation, Functor.comp_obj] at e
  rw [he] at e
  exact e

/-- The actual globally supported class extending the exact complex-normal
coclass. The inverse is that of the proved normalization isomorphism. -/
def cycleComponentSupportedInjectiveClass :
    (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex s
        (cycleComponentAnalyticClosedSupport s x))).homology (2 * (p : ℤ)) :=
  (cycleComponentSupportedClassNormalizationIso s x (d := d) hx).inv
    (cycleComponentSmoothSupportCoclassSection s x (d := d) hx)

/-- Exact smooth-locus normalization, not equality only up to a scalar. -/
@[simp]
theorem cycleComponentSupportedInjectiveClass_normalization :
    (cycleComponentSupportedClassNormalizationIso s x (d := d) hx).hom
      (cycleComponentSupportedInjectiveClass s x (d := d) hx) =
    cycleComponentSmoothSupportCoclassSection s x (d := d) hx :=
  (cycleComponentSupportedClassNormalizationIso s x (d := d) hx).addCommGroupIsoToAddEquiv.apply_symm_apply _

/-- The normalized global extension is unique, by injectivity of the actual
restriction/purity comparison. This is a theorem, not a supplied existence input. -/
theorem cycleComponentSupportedInjectiveClass_unique
    (a : (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex s
        (cycleComponentAnalyticClosedSupport s x))).homology (2 * (p : ℤ)))
    (ha : (cycleComponentSupportedClassNormalizationIso s x (d := d) hx).hom a =
      cycleComponentSmoothSupportCoclassSection s x (d := d) hx) :
    a = cycleComponentSupportedInjectiveClass s x (d := d) hx := by
  apply (cycleComponentSupportedClassNormalizationIso s x (d := d) hx).addCommGroupIsoToAddEquiv.injective
  exact ha.trans (cycleComponentSupportedInjectiveClass_normalization s x (d := d) hx).symm

/-- The constructed class in the existing support-cone presentation. Its
comparison includes the proved cone sign required by actual support forgetting. -/
def cycleComponentSheafSupportedClass :
    RationalCohomologyWithSupport s (cycleComponentSupport s x) (2 * (p : ℤ)) :=
  (rationalSupportAddEquivSupportedInjectiveHomology s (cycleComponentSupport s x)
    (cycleComponentAnalyticClosedSupport s x).isClosed (2 * (p : ℤ))).symm
      (cycleComponentSupportedInjectiveClass s x (d := d) hx)

/-- The unconditional ordinary class of an arbitrary integral component.
This uses the literal inclusion of supported injective sections. -/
def cycleComponentSheafClass : FieldCohomology ℚ s (2 * (p : ℤ)) :=
  (rationalCohomologyAddEquivAmbientInjectiveHomology s (2 * (p : ℤ))).symm
    (HomologicalComplex.homologyMap
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
        (TopCat.of (ComplexPoint X s)) (cycleComponentAnalyticClosedSupport s x).compl ⊤
        (ambientRationalInjectiveComplex s)).f (2 * (p : ℤ))
      (cycleComponentSupportedInjectiveClass s x (d := d) hx))

/-- The ordinary class agrees with the repository's support-forgetting map,
through the constructed, sign-correct support comparison. -/
theorem cycleComponentSheafClass_eq_forgetSupport :
    cycleComponentSheafClass s x (d := d) hx =
      forgetSupport s (cycleComponentSupport s x) (2 * (p : ℤ))
        (cycleComponentSheafSupportedClass s x (d := d) hx) := by
  apply (rationalCohomologyAddEquivAmbientInjectiveHomology s (2 * (p : ℤ))).injective
  rw [rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport s
    (cycleComponentSupport s x) (cycleComponentAnalyticClosedSupport s x).isClosed]
  simp only [cycleComponentSheafClass, cycleComponentSheafSupportedClass,
    AddEquiv.apply_symm_apply]
  rfl

include s hx in
omit [IsIntegral X] [Smooth s] [IsProjective s] in
/-- The actual dimension bound needed for the Borel–Moore degree, not an extra input. -/
theorem cycleComponentSheafClass_codimension_le : p ≤ d := by
  have h := SmoothOfRelativeDimension.coheight_le_complex (f := s) (d := d) x
  rw [hx] at h
  exact_mod_cast h

/-- The normalized fundamental class in ACTUAL ambient chain-sheaf
Borel–Moore homology, obtained through the constructed orientation shift.
It is not an element of a supplied replacement homology group. -/
def cycleComponentSheafBorelMooreFundamentalClass :
    ComplexAmbientSheafBorelMooreHomology s d (cycleComponentAnalyticClosedSupport s x)
      (2 * ((d - p : ℕ) : ℤ)) :=
  (complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport s d
    (cycleComponentAnalyticClosedSupport s x) p
    (cycleComponentSheafClass_codimension_le s x (d := d) hx)).symm
      (cycleComponentSheafSupportedClass s x (d := d) hx)

/-- The constructed Alexander–Poincaré map sends the fundamental class to
the exact normalized supported class, with no comparison hypothesis. -/
@[simp]
theorem cycleComponentSheafBorelMooreFundamentalClass_duality :
    complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport s d
      (cycleComponentAnalyticClosedSupport s x) p
      (cycleComponentSheafClass_codimension_le s x (d := d) hx)
      (cycleComponentSheafBorelMooreFundamentalClass s x (d := d) hx) =
    cycleComponentSheafSupportedClass s x (d := d) hx :=
  AddEquiv.apply_symm_apply _ _

/-- The ordinary class is also exactly the actual ambient Borel–Moore
cycle-class route. The ordinary-target comparison is proved, not an input. -/
theorem cycleComponentSheafBorelMooreFundamentalClass_toFieldCohomology :
    complexAmbientSheafBorelMooreCycleDegreeToFieldCohomology s d
      (cycleComponentAnalyticClosedSupport s x) p
      (cycleComponentSheafClass_codimension_le s x (d := d) hx)
      (cycleComponentSheafBorelMooreFundamentalClass s x (d := d) hx) =
    cycleComponentSheafClass s x (d := d) hx := by
  change forgetSupport s (cycleComponentSupport s x) (2 * (p : ℤ))
    (complexAmbientSheafBorelMooreCycleDegreeAddEquivRationalSupport s d
      (cycleComponentAnalyticClosedSupport s x) p
      (cycleComponentSheafClass_codimension_le s x (d := d) hx)
      (cycleComponentSheafBorelMooreFundamentalClass s x (d := d) hx)) = _
  rw [cycleComponentSheafBorelMooreFundamentalClass_duality,
    cycleComponentSheafClass_eq_forgetSupport]

end AlgebraicGeometry.ComplexPoint
