/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticCMTopology
public import Other.AlgebraicGeometry.ExplicitEllipticGlobalOneForms
public import Other.AlgebraicGeometry.ExplicitEllipticCurveDeRhamClass

/-!
# Complex multiplication on the explicit global elliptic differential

The algebraic CM automorphism preserves both standard affine charts.  Its pullback on
Kähler differentials was computed on those charts in
`ExplicitEllipticCMGlobal`.  Here those two computations are evaluated in the actual
holomorphic one-form sheaf and glued.  This gives a global section characterized by the
honest chartwise pullbacks and proves that it is `i` times the invariant differential.

The final definitions place this transformed section in the existing filtered and full
analytic de Rham hypercohomology groups.  A general change-of-space pullback functor on the
holomorphic de Rham complex is not used here.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Evaluation of a scalar multiple of a regular Kähler differential agrees with the
scalar endomorphism of the sheafified holomorphic one-form sheaf. -/
theorem curveDifferentialToHolomorphicSheaf_smul
    (U : curve.Opens) (c : ℂ) (w : KaehlerDifferential ℂ Γ(curve, U)) :
    curveDifferentialToHolomorphicSheaf U (c • w) =
      (curveHolomorphicOneFormScalarSheafMap c).hom.app
        (.op (curveAnalyticOpen U))
        (curveDifferentialToHolomorphicSheaf U w) := by
  unfold curveDifferentialToHolomorphicSheaf
  rw [curveHolomorphicOneFormScalar_toSheafify]
  congr 1
  exact (curveDifferentialToHolomorphic U).map_smul c w

/-- The global holomorphic differential obtained from the CM-transformed chart
differentials.  Its definition as a scalar multiple makes the global gluing canonical;
the two restriction theorems below identify it with the algebraic pullback formulas. -/
def curveCMGlobalHolomorphicDifferential :
    curveHolomorphicOneFormSheaf.obj.obj (.op ⊤) :=
  curveGlobalHolomorphicDifferential_smul Complex.I

/-- On the affine `Z ≠ 0` chart, the global CM transform is the evaluated algebraic
pullback of the invariant differential. -/
theorem curveCMGlobalHolomorphicDifferential_restrict_z :
    curveHolomorphicOneFormSheaf.obj.map (homOfLE
        (show curveAnalyticOpen (chart 2) ≤ ⊤ from le_top)).op
        curveCMGlobalHolomorphicDifferential =
      curveDifferentialToHolomorphicSheaf (chart 2)
        (curveZCMDifferentialEnd curveZDifferential) := by
  rw [curveZCMDifferentialEnd_curveZDifferential',
    curveDifferentialToHolomorphicSheaf_smul]
  exact curveGlobalHolomorphicDifferential_smul_restrict Complex.I
    (curveAnalyticOpen (chart 2)) |>.trans <|
      congrArg ((curveHolomorphicOneFormScalarSheafMap Complex.I).hom.app
        (.op (curveAnalyticOpen (chart 2))))
        curveGlobalHolomorphicDifferential_restrict_z

/-- On the affine chart containing infinity, the global CM transform is the evaluated
algebraic pullback of the invariant differential. -/
theorem curveCMGlobalHolomorphicDifferential_restrict_y :
    curveHolomorphicOneFormSheaf.obj.map (homOfLE
        (show curveAnalyticOpen (chart 1) ≤ ⊤ from le_top)).op
        curveCMGlobalHolomorphicDifferential =
      curveDifferentialToHolomorphicSheaf (chart 1)
        (curveYCMDifferentialEnd curveYDifferential) := by
  rw [curveYCMDifferentialEnd_curveYDifferential,
    curveDifferentialToHolomorphicSheaf_smul]
  exact curveGlobalHolomorphicDifferential_smul_restrict Complex.I
    (curveAnalyticOpen (chart 1)) |>.trans <|
      congrArg ((curveHolomorphicOneFormScalarSheafMap Complex.I).hom.app
        (.op (curveAnalyticOpen (chart 1))))
        curveGlobalHolomorphicDifferential_restrict_y

/-- The chartwise CM pullback of the invariant differential has eigenvalue `i` as a
global section of the actual holomorphic one-form sheaf. -/
theorem curveCMGlobalHolomorphicDifferential_eq_i_smul :
    curveCMGlobalHolomorphicDifferential =
      curveGlobalHolomorphicDifferential_smul Complex.I := rfl

/-- The transformed global form determines a class in the actual first filtered
hypercohomology group. -/
def curveCMTopFilteredClass :
    FilteredDeRhamHypercohomology curveVariety 1 1 :=
  topHolomorphicFormFilteredEquivOfDimension curveVariety 1 dim_curve_eq_one
    curveCMGlobalHolomorphicDifferential

/-- The corresponding class in full analytic de Rham hypercohomology. -/
def curveCMDeRhamClass : DeRhamHypercohomology curveVariety 1 :=
  filteredToDeRhamCohomology curveVariety 1 1 curveCMTopFilteredClass

end AlgebraicGeometry.ExplicitEllipticCandidate
