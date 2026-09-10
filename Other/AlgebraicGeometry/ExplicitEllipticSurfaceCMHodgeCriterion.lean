/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSurfaceCMOddCandidate

/-!
# A CM-detector criterion for the explicit non-Hodge class

This file places the rational odd external-product class in the public
`FieldCohomology` used by `IsHodgeClass`.  It then records the exact two
comparison statements which finish the CM route: compatibility of coefficient
extension with the Betti comparison, and vanishing of the corrected CM detector
on the first Hodge filtration.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicTopology

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

local instance surfaceVariety_smoothForCMHodgeCriterion :
    Smooth surfaceVariety.hom :=
  SmoothOfRelativeDimension.smooth 2 surfaceVariety.hom

local instance surfaceVariety_openParacompactForCMHodgeCriterion
    (U : Opens (ComplexPoint surfaceVariety)) : ParacompactSpace U :=
  ComplexPoint.openParacompactSpace surfaceVariety U

/-- The rational odd external-product class in the constant-sheaf
cohomology group occurring in `IsHodgeClass`. -/
def surfaceCMOddRationalBettiClass (hCM : CurveCMSingularIEigen) :
    FieldCohomology ℚ surfaceVariety 2 := by
  exact (rationalCohomologyAddEquivSingularCohomology
    surfaceVariety 2).symm (surfaceCMOddRationalTwoClass hCM)

/-- The rational Betti comparison sends the public candidate back to its
defining singular class. -/
theorem rationalCohomologyAddEquiv_surfaceCMOddRationalBettiClass
    (hCM : CurveCMSingularIEigen) :
    rationalCohomologyAddEquivSingularCohomology surfaceVariety 2
        (surfaceCMOddRationalBettiClass hCM) =
      surfaceCMOddRationalTwoClass hCM := by
  exact AddEquiv.apply_symm_apply _ _

theorem surfaceCMOddRationalBettiClass_ne_zero
    (hCM : CurveCMSingularIEigen) :
    surfaceCMOddRationalBettiClass hCM ≠ 0 := by
  exact (rationalCohomologyAddEquivSingularCohomology
    surfaceVariety 2).symm.map_ne_zero_iff.mpr
      (surfaceCMOddRationalTwoClass_ne_zero hCM)

/-- The ordinary complex singular class obtained from the de Rham realization
of the public rational candidate. -/
def surfaceCMOddDeRhamSingularClass (hCM : CurveCMSingularIEigen) :
    Singular.Cohomology ℂ surfaceAnalyticSpace 2 := by
  exact deRhamCohomologyEquivComplexSingularCohomology surfaceVariety 2
    (fieldToDeRhamCohomology ℚ surfaceVariety 2
      (surfaceCMOddRationalBettiClass hCM))

/-- The precise coefficient-comparison square needed by the candidate.  The
left side extends rational constants to de Rham cohomology and then applies
de Rham--Betti; the right side extends coefficients on singular cohomology. -/
abbrev SurfaceCMOddCoefficientCompatibility
    (hCM : CurveCMSingularIEigen) : Prop :=
  surfaceCMOddDeRhamSingularClass hCM =
    surfaceCMOddComplexifiedTwoClass hCM

/-- The precise filtration statement needed by the corrected detector.  It is
stated for every class in `F¹`, so it is independent of the chosen candidate. -/
abbrev SurfaceCMOddDetectorAnnihilatesFirstHodge : Prop :=
  ∀ x : DeRhamHypercohomology surfaceVariety 2,
    x ∈ hodgeFiltration surfaceVariety 1 2 →
      surfaceCMOddDoubleMinusEnd
        (deRhamCohomologyEquivComplexSingularCohomology
          surfaceVariety 2 x) = 0

/-- Once the coefficient square and the filtration-annihilation statement are
available, the public rational candidate is a concrete non-Hodge class. -/
theorem surfaceCMOddRationalBettiClass_not_isHodge
    (hCM : CurveCMSingularIEigen)
    (hcoeff : SurfaceCMOddCoefficientCompatibility hCM)
    (hkill : SurfaceCMOddDetectorAnnihilatesFirstHodge) :
    ¬ IsHodgeClass ℚ surfaceVariety 1
      (surfaceCMOddRationalBettiClass hCM) := by
  intro hhodge
  have hmem :
      fieldToDeRhamCohomology ℚ surfaceVariety 2
          (surfaceCMOddRationalBettiClass hCM) ∈
        hodgeFiltration surfaceVariety 1 2 := hhodge
  have hzero := hkill _ hmem
  change surfaceCMOddDoubleMinusEnd
      (surfaceCMOddDeRhamSingularClass hCM) = 0 at hzero
  rw [hcoeff] at hzero
  exact
    (surfaceCMOddDoubleMinusEnd_surfaceCMOddComplexifiedTwoClass_ne_zero
      hCM) hzero

/-- The same criterion in existential form, matching the non-Hodge witness
required by the Hodge-conjecture counterexample statement. -/
theorem exists_surface_nonHodgeClass_of_CM
    (hCM : CurveCMSingularIEigen)
    (hcoeff : SurfaceCMOddCoefficientCompatibility hCM)
    (hkill : SurfaceCMOddDetectorAnnihilatesFirstHodge) :
    ∃ α : FieldCohomology ℚ surfaceVariety 2,
      ¬ IsHodgeClass ℚ surfaceVariety 1 α :=
  ⟨surfaceCMOddRationalBettiClass hCM,
    surfaceCMOddRationalBettiClass_not_isHodge hCM hcoeff hkill⟩

end AlgebraicGeometry.ExplicitEllipticCandidate
