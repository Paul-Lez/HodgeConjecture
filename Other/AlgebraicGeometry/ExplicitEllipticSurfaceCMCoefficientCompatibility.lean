/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Other.AlgebraicGeometry.RationalComplexBettiCohomologyCompatibility
import Other.AlgebraicGeometry.ExplicitEllipticSurfaceCMHodgeCriterion

/-!
# Coefficient compatibility for the explicit CM surface class

The general rational-to-complex Betti compatibility theorem is specialized to
the odd CM class on the explicit elliptic surface.
-/

@[expose] noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicTopology

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

local instance surfaceVariety_smoothForCMCoefficientCompatibility :
    Smooth surfaceVariety.hom :=
  SmoothOfRelativeDimension.smooth 2 surfaceVariety.hom

local instance surfaceVariety_openParacompactForCMCoefficientCompatibility
    (U : Opens (ComplexPoint surfaceVariety)) : ParacompactSpace U :=
  ComplexPoint.openParacompactSpace surfaceVariety U

/-- The de Rham--Betti realization of the explicit rational CM class is its
ordinary singular-cohomology complexification. -/
theorem surfaceCMOddCoefficientCompatibility
    (hCM : CurveCMSingularIEigen) :
    SurfaceCMOddCoefficientCompatibility hCM := by
  unfold SurfaceCMOddCoefficientCompatibility surfaceCMOddDeRhamSingularClass
  calc
    deRhamCohomologyEquivComplexSingularCohomology surfaceVariety 2
          (fieldToDeRhamCohomology ℚ surfaceVariety 2
            (surfaceCMOddRationalBettiClass hCM)) =
        AlgebraicTopology.Singular.rationalToComplexCohomologyMap
          (TopCat.of (ComplexPoint surfaceVariety)) 2
          (rationalCohomologyAddEquivSingularCohomology surfaceVariety 2
            (surfaceCMOddRationalBettiClass hCM)) :=
      deRhamCohomologyEquivComplexSingularCohomology_fieldToDeRhamCohomology
        (X := surfaceVariety) 2 (surfaceCMOddRationalBettiClass hCM)
    _ = surfaceCMOddComplexifiedTwoClass hCM := by
      rw [rationalCohomologyAddEquiv_surfaceCMOddRationalBettiClass]
      rfl

end AlgebraicGeometry.ExplicitEllipticCandidate
