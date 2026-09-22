/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectivePlaneHyperplane
public import Other.AlgebraicGeometry.ProjectivePlanePresentation
public import Other.AlgebraicGeometry.SheafCycleClass
public import HodgeConjecture.Lemmas.AlgebraicGeometry.CycleComponentDimension
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothCatenaryDimension
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothPointwiseDimension
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# The coordinate hyperplane as a canonical algebraic-cycle component

This file identifies the reduced closed subscheme `X₀ = 0` in the direct `Proj` model of
`ℙ²_ℂ` with the repository's canonical reduced closure of its explicit homogeneous generic
point.  It then records the corresponding codimension-one cycle and the exact evaluation of
`sheafCycleClassOnCycles` on that cycle.

The generic point, its closure, the identification with the coordinate hyperplane, the
codimension-one calculation, and evaluation by the canonical cycle-class map are unconditional:
the direct `Proj` model is equipped with an explicit projective presentation in
`ProjectivePlanePresentation`.  This file does not identify the canonical cycle-component class
with the separate explicit winding cocycle.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace MvPolynomial AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectivePlane

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous principal ideal `(X₀)`. -/
def coordinateZeroHomogeneousIdeal : HomogeneousIdeal Grading where
  toSubmodule := Ideal.span {coordinateZero}
  is_homogeneous' := Ideal.homogeneous_span Grading {coordinateZero} (by
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst f
    exact ⟨1, (MvPolynomial.mem_homogeneousSubmodule 1 coordinateZero).2
      coordinateZero_homogeneous⟩)

@[simp]
lemma coordinateZeroHomogeneousIdeal_toIdeal :
    coordinateZeroHomogeneousIdeal.toIdeal = Ideal.span {coordinateZero} :=
  rfl

lemma coordinateZeroHomogeneousIdeal_isPrime :
    coordinateZeroHomogeneousIdeal.toIdeal.IsPrime := by
  change (Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin 3) ℂ)}).IsPrime
  exact (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero (0 : Fin 3))).2
    MvPolynomial.X_prime

lemma coordinateOne_mem_irrelevant :
    (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ) ∈ HomogeneousIdeal.irrelevant Grading := by
  rw [HomogeneousIdeal.mem_irrelevant_iff]
  rw [GradedRing.proj_apply]
  exact DirectSum.decompose_of_mem_ne Grading (i := 1) (j := 0)
    ((MvPolynomial.mem_homogeneousSubmodule 1 (MvPolynomial.X 1)).2
      (MvPolynomial.isHomogeneous_X ℂ 1)) (by decide)

lemma coordinateOne_not_mem_coordinateZeroHomogeneousIdeal :
    (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ) ∉ coordinateZeroHomogeneousIdeal := by
  change MvPolynomial.X 1 ∉ (Ideal.span {coordinateZero} :
    Ideal (MvPolynomial (Fin 3) ℂ))
  rw [Ideal.mem_span_singleton]
  simp [coordinateZero]

/-- The relevant homogeneous prime `(X₀)` in the underlying projective spectrum. -/
def hyperplaneGenericPrime : ProjectiveSpectrum Grading where
  asHomogeneousIdeal := coordinateZeroHomogeneousIdeal
  isPrime := coordinateZeroHomogeneousIdeal_isPrime
  not_irrelevant_le := by
    intro h
    exact coordinateOne_not_mem_coordinateZeroHomogeneousIdeal
      (h coordinateOne_mem_irrelevant)

@[simp]
lemma hyperplaneGenericPrime_asHomogeneousIdeal :
    hyperplaneGenericPrime.asHomogeneousIdeal = coordinateZeroHomogeneousIdeal :=
  rfl

/-- The closure of the prime `(X₀)` is exactly the displayed projective zero locus. -/
lemma closure_hyperplaneGenericPrime :
    closure ({hyperplaneGenericPrime} : Set (ProjectiveSpectrum Grading)) =
      ProjectiveSpectrum.zeroLocus Grading {coordinateZero} := by
  rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure Grading]
  simp only [ProjectiveSpectrum.vanishingIdeal_singleton,
    hyperplaneGenericPrime_asHomogeneousIdeal]
  exact ProjectiveSpectrum.zeroLocus_span Grading {coordinateZero}

/-- The explicit generic point of the coordinate hyperplane, represented by `(X₀)`. -/
def hyperplaneGenericPoint : planeOver.left :=
  hyperplaneGenericPrime

@[simp]
lemma hyperplaneGenericPoint_asHomogeneousIdeal :
    hyperplaneGenericPoint.asHomogeneousIdeal = coordinateZeroHomogeneousIdeal :=
  rfl

/-- The closure of `(X₀)` in the direct `Proj` scheme is exactly the displayed projective zero
locus. -/
lemma closure_hyperplaneGenericPoint :
    closure ({hyperplaneGenericPoint} : Set planeOver.left) = hyperplaneLocus :=
  closure_hyperplaneGenericPrime

/-- The closed set used to define the explicit hyperplane is the closure of its displayed
generic point. -/
lemma hyperplaneClosed_eq_closure_genericPoint :
    hyperplaneClosed =
      ⟨closure ({hyperplaneGenericPoint} : Set planeOver.left), isClosed_closure⟩ := by
  apply TopologicalSpace.Closeds.ext
  exact closure_hyperplaneGenericPoint.symm

/-- The explicit reduced hyperplane is definitionally transported to the repository's canonical
reduced cycle component. -/
lemma hyperplane_eq_cycleComponent :
    hyperplane = cycleComponent planeOver.left hyperplaneGenericPoint := by
  unfold hyperplane cycleComponent
  rw [hyperplaneClosed_eq_closure_genericPoint]
  rfl


/-- The explicit reduced hyperplane is integral, because it is the reduced closure of the prime
point `(X₀)`. -/
noncomputable instance hyperplane_integral : IsIntegral hyperplane := by
  rw [hyperplane_eq_cycleComponent]
  infer_instance

noncomputable instance hyperplaneOver_integral : IsIntegral hyperplaneOver.left := by
  change IsIntegral hyperplane
  infer_instance

/-- The canonical cycle-component support of `(X₀)` is exactly the analytic image of the explicit
closed immersion. -/
lemma cycleComponentSupport_hyperplaneGenericPoint
    :
    cycleComponentSupport planeOver hyperplaneGenericPoint =
      Set.range (Point.map hyperplaneOverι) := by
  rw [ComplexPoint.range_map_of_closedImmersion hyperplaneOverι]
  ext z
  change z.underlying ∈ closure ({hyperplaneGenericPoint} : Set planeOver.left) ↔
    z.underlying ∈ Set.range hyperplaneι
  rw [range_hyperplaneι, closure_hyperplaneGenericPoint]
  rfl

/-- The affine chart `D₊(X₁)` used to compute the codimension of `(X₀)`. -/
private def hyperplaneOneChart : plane.Opens :=
  Proj.basicOpen Grading (MvPolynomial.X 1)

private lemma hyperplaneGenericPoint_mem_oneChart :
    hyperplaneGenericPoint ∈ hyperplaneOneChart := by
  exact coordinateOne_not_mem_coordinateZeroHomogeneousIdeal

private def hyperplaneGenericPointOnOneChart : hyperplaneOneChart.toScheme :=
  ⟨hyperplaneGenericPoint, hyperplaneGenericPoint_mem_oneChart⟩

private def hyperplaneOneChartIsoSpec : hyperplaneOneChart.toScheme ≅
    Spec (.of (HomogeneousLocalization.Away Grading (MvPolynomial.X 1))) :=
  Proj.basicOpenIsoSpec Grading (MvPolynomial.X 1)
    (Other.ProjectiveChart.X_mem_one ℂ 1) Nat.one_pos

private def hyperplaneGenericPointOnOneChartSpec :
    Spec (.of (HomogeneousLocalization.Away Grading (MvPolynomial.X 1))) :=
  hyperplaneOneChartIsoSpec.hom hyperplaneGenericPointOnOneChart

private def hyperplaneOneChartPrime :
    Ideal (HomogeneousLocalization.Away Grading (MvPolynomial.X 1)) :=
  hyperplaneGenericPointOnOneChartSpec.asIdeal

private instance : hyperplaneOneChartPrime.IsPrime := by
  change hyperplaneGenericPointOnOneChartSpec.asIdeal.IsPrime
  exact hyperplaneGenericPointOnOneChartSpec.2

private lemma hyperplaneOneChartNormal_mem_prime :
    Other.ProjectiveChart.gen ℂ (1 : Fin 3) 0 ∈ hyperplaneOneChartPrime := by
  change Other.ProjectiveChart.gen ℂ (1 : Fin 3) 0 ∈
    hyperplaneGenericPointOnOneChartSpec.asIdeal
  let z : HomogeneousLocalization.NumDenSameDeg Grading
      (Submonoid.powers (MvPolynomial.X 1)) :=
    ⟨1 • 1,
      ⟨MvPolynomial.X ((1 : Fin 3).succAbove 0),
        Other.ProjectiveChart.X_mem_smul ℂ ((1 : Fin 3).succAbove 0)⟩,
      ⟨MvPolynomial.X 1 ^ 1,
        SetLike.pow_mem_graded 1 (Other.ProjectiveChart.X_mem_one ℂ (1 : Fin 3))⟩,
      ⟨1, rfl⟩⟩
  change HomogeneousLocalization.mk z ∈
    ((ProjectiveSpectrum.Proj.toSpec Grading (MvPolynomial.X 1)).base
      hyperplaneGenericPointOnOneChart).asIdeal
  apply (ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply
    Grading hyperplaneGenericPointOnOneChart z).2
  change coordinateZero ∈ coordinateZeroHomogeneousIdeal
  exact Ideal.subset_span (Set.mem_singleton coordinateZero)

private lemma hyperplaneOneChartPrime_height_eq_coheight :
    hyperplaneOneChartPrime.height = Order.coheight hyperplaneGenericPoint := by
  calc
    hyperplaneOneChartPrime.height =
        Order.coheight hyperplaneGenericPointOnOneChartSpec :=
      idealHeight_eq_coheight _ _
    _ = Order.coheight hyperplaneGenericPointOnOneChart := by
      exact IsOpenEmbedding.coheight_eq (Scheme.homeoOfIso hyperplaneOneChartIsoSpec)
        (Scheme.homeoOfIso hyperplaneOneChartIsoSpec).isOpenEmbedding
    _ = Order.coheight hyperplaneGenericPoint := by
      exact (coheight_eq_of_isOpenImmersion hyperplaneOneChart.ι).symm

private lemma hyperplaneOneChartPrime_minimal_over_normal :
    hyperplaneOneChartPrime ∈ (Ideal.span
      ({Other.ProjectiveChart.gen ℂ (1 : Fin 3) 0} :
        Set (HomogeneousLocalization.Away Grading (MvPolynomial.X 1)))).minimalPrimes := by
  refine ⟨⟨inferInstance, Ideal.span_le.mpr ?_⟩, ?_⟩
  · simpa using hyperplaneOneChartNormal_mem_prime
  · intro q hq hqle
    let qPoint : Spec (.of (HomogeneousLocalization.Away Grading (MvPolynomial.X 1))) :=
      ⟨q, hq.1⟩
    have hspec : hyperplaneGenericPointOnOneChartSpec ≤ qPoint := by
      apply (specOrderIsoPrimeSpectrum
        (.of (HomogeneousLocalization.Away Grading (MvPolynomial.X 1)))).le_iff_le.mp
      exact hqle
    have hchart :
        hyperplaneGenericPointOnOneChart ≤ hyperplaneOneChartIsoSpec.inv qPoint := by
      have h := hyperplaneOneChartIsoSpec.inv.continuous.specialization_monotone hspec
      simpa [hyperplaneGenericPointOnOneChartSpec] using h
    have hambient :
        hyperplaneGenericPoint ≤ hyperplaneOneChart.ι (hyperplaneOneChartIsoSpec.inv qPoint) := by
      exact hyperplaneOneChart.ι.continuous.specialization_monotone hchart
    have hcoord : coordinateZero ∈
        (hyperplaneOneChartIsoSpec.inv qPoint :
          hyperplaneOneChart.toScheme).1.asHomogeneousIdeal := by
      have hnormal : Other.ProjectiveChart.gen ℂ (1 : Fin 3) 0 ∈ q :=
        hq.2 (Ideal.subset_span (Set.mem_singleton _))
      let z : HomogeneousLocalization.NumDenSameDeg Grading
          (Submonoid.powers (MvPolynomial.X 1)) :=
        ⟨1 • 1,
          ⟨MvPolynomial.X ((1 : Fin 3).succAbove 0),
            Other.ProjectiveChart.X_mem_smul ℂ ((1 : Fin 3).succAbove 0)⟩,
          ⟨MvPolynomial.X 1 ^ 1,
            SetLike.pow_mem_graded 1 (Other.ProjectiveChart.X_mem_one ℂ (1 : Fin 3))⟩,
          ⟨1, rfl⟩⟩
      apply (ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply
        Grading (hyperplaneOneChartIsoSpec.inv qPoint) z).1
      change Other.ProjectiveChart.gen ℂ (1 : Fin 3) 0 ∈
        (hyperplaneOneChartIsoSpec.hom (hyperplaneOneChartIsoSpec.inv qPoint)).asIdeal
      have heq : hyperplaneOneChartIsoSpec.hom
          (hyperplaneOneChartIsoSpec.inv qPoint) = qPoint :=
        (Scheme.homeoOfIso hyperplaneOneChartIsoSpec).apply_symm_apply qPoint
      rw [heq]
      exact hnormal
    have hideal :
        (hyperplaneOneChartIsoSpec.inv qPoint :
          hyperplaneOneChart.toScheme).1.asHomogeneousIdeal =
          coordinateZeroHomogeneousIdeal := by
      apply le_antisymm
      · have hs :
            (hyperplaneOneChart.ι (hyperplaneOneChartIsoSpec.inv qPoint) : plane) ⤳
              hyperplaneGenericPoint := Scheme.le_iff_specializes.mp hambient
        exact (ProjectiveSpectrum.le_iff_mem_closure Grading _ _).2
          (specializes_iff_mem_closure.mp hs)
      · change Ideal.span {coordinateZero} ≤ _
        exact Ideal.span_le.mpr (by simpa using hcoord)
    have hy : hyperplaneOneChartIsoSpec.inv qPoint =
        hyperplaneGenericPointOnOneChart := by
      apply Subtype.ext
      apply ProjectiveSpectrum.ext
      exact hideal.trans hyperplaneGenericPoint_asHomogeneousIdeal.symm
    have hpoint : qPoint = hyperplaneGenericPointOnOneChartSpec := by
      calc
        qPoint = hyperplaneOneChartIsoSpec.hom
            (hyperplaneOneChartIsoSpec.inv qPoint) :=
          (Scheme.homeoOfIso hyperplaneOneChartIsoSpec).apply_symm_apply qPoint |>.symm
        _ = hyperplaneOneChartIsoSpec.hom hyperplaneGenericPointOnOneChart := congrArg _ hy
        _ = hyperplaneGenericPointOnOneChartSpec := rfl
    have hqeq : q = hyperplaneOneChartPrime :=
      congrArg PrimeSpectrum.asIdeal hpoint
    exact hqeq.ge

private lemma hyperplaneOneChartNormal_mem_nonZeroDivisors :
    Other.ProjectiveChart.gen ℂ (1 : Fin 3) 0 ∈
      nonZeroDivisors (HomogeneousLocalization.Away Grading (MvPolynomial.X 1)) := by
  rw [mem_nonZeroDivisors_iff]
  constructor
  · intro a ha
    apply (Other.ProjectiveChart.chartRingEquiv ℂ (1 : Fin 3)).symm.injective
    have hmul := congrArg
      (Other.ProjectiveChart.chartRingEquiv ℂ (1 : Fin 3)).symm ha
    rw [map_mul, map_zero] at hmul
    have hgen :
        (Other.ProjectiveChart.chartRingEquiv ℂ (1 : Fin 3)).symm
          (Other.ProjectiveChart.gen ℂ (1 : Fin 3) 0) =
            (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) := by
      apply (Other.ProjectiveChart.chartRingEquiv ℂ (1 : Fin 3)).injective
      simp
    rw [hgen] at hmul
    have hX : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ≠ 0 :=
      MvPolynomial.X_ne_zero 0
    simpa using (mul_eq_zero.mp hmul).resolve_left hX
  · intro a ha
    apply (Other.ProjectiveChart.chartRingEquiv ℂ (1 : Fin 3)).symm.injective
    have hmul := congrArg
      (Other.ProjectiveChart.chartRingEquiv ℂ (1 : Fin 3)).symm ha
    rw [map_mul, map_zero] at hmul
    have hgen :
        (Other.ProjectiveChart.chartRingEquiv ℂ (1 : Fin 3)).symm
          (Other.ProjectiveChart.gen ℂ (1 : Fin 3) 0) =
            (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) := by
      apply (Other.ProjectiveChart.chartRingEquiv ℂ (1 : Fin 3)).injective
      simp
    rw [hgen] at hmul
    have hX : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ≠ 0 :=
      MvPolynomial.X_ne_zero 0
    simpa using (mul_eq_zero.mp hmul).resolve_right hX

private lemma hyperplaneOneChartNormal_not_isUnit :
    ¬ IsUnit (Other.ProjectiveChart.gen ℂ (1 : Fin 3) 0) := by
  intro hunit
  exact (Ideal.notMem_of_isUnit hyperplaneOneChartPrime hunit)
    hyperplaneOneChartNormal_mem_prime

private lemma hyperplaneOneChartPrime_height_eq_one :
    hyperplaneOneChartPrime.height = 1 := by
  letI : IsNoetherianRing
      (HomogeneousLocalization.Away Grading (MvPolynomial.X 1)) :=
    isNoetherianRing_of_ringEquiv (MvPolynomial (Fin 2) ℂ)
      (Other.ProjectiveChart.chartRingEquiv ℂ (1 : Fin 3))
  apply le_antisymm
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _
      hyperplaneOneChartPrime_minimal_over_normal
  · exact (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      hyperplaneOneChartNormal_mem_nonZeroDivisors).trans
        (Ideal.height_mono
          (Ideal.span_le.mpr (by simpa using hyperplaneOneChartNormal_mem_prime)))

/-- The explicit coordinate prime `(X₀)` has codimension one.  This is computed directly on
the affine chart `D₊(X₁)`: its prime is minimal over the non-zero-divisor `X₀/X₁`, so Krull's
principal ideal theorem gives height one.  No smoothness assumption on the hyperplane is used. -/
lemma hyperplaneGenericPoint_coheight :
    Order.coheight hyperplaneGenericPoint = 1 := by
  rw [← hyperplaneOneChartPrime_height_eq_coheight]
  exact hyperplaneOneChartPrime_height_eq_one

/-- The integral codimension-one cycle with coefficient one on the coordinate hyperplane. -/
def coordinateHyperplaneCycle :
    codimensionCycleSubgroup planeOver.left 1 :=
  codimensionCycleSubgroup.single hyperplaneGenericPoint
    hyperplaneGenericPoint_coheight 1

/-- The direct `Proj` plane packaged with its already-proved relative dimension two.  Only the
repository's chosen projective presentation remains a typeclass input here. -/
noncomputable abbrev dimensionedPlane :
    ComplexPoint.DimensionedSmoothProjectiveComplexVariety where
  toSmoothProjectiveComplexVariety :=
    { scheme := planeOver.left
      structureMap := planeOver.hom }
  dimension := 2

@[simp]
lemma dimensionedPlane_over :
    dimensionedPlane.over = planeOver :=
  rfl

noncomputable instance dimensionedPlane_over_integral
    : IsIntegral dimensionedPlane.over.left := by
  rw [dimensionedPlane_over]
  infer_instance

noncomputable instance dimensionedPlane_over_smooth
    : Smooth dimensionedPlane.over.hom := by
  rw [dimensionedPlane_over]
  infer_instance

noncomputable instance dimensionedPlane_over_projective
    : IsProjective dimensionedPlane.over.hom := by
  rw [dimensionedPlane_over]
  infer_instance

noncomputable instance dimensionedPlane_over_smoothOfRelativeDimension
    :
    SmoothOfRelativeDimension 2 dimensionedPlane.over.hom := by
  rw [dimensionedPlane_over]
  infer_instance

/-- Evaluation of the repository's canonical cycle-class map on the explicit coordinate
hyperplane cycle.  This is a direct specialization of `sheafCycleClassOnCycles_single`, with no
additional equality packaged as a hypothesis. -/
@[simp]
theorem sheafCycleClassOnCycles_coordinateHyperplaneCycle
    :
    ComplexPoint.sheafCycleClassOnCycles dimensionedPlane 1 coordinateHyperplaneCycle =
      ComplexPoint.cycleComponentSheafClass dimensionedPlane.over hyperplaneGenericPoint
        (d := 2) hyperplaneGenericPoint_coheight := by
  simpa [coordinateHyperplaneCycle] using
    (ComplexPoint.sheafCycleClassOnCycles_single
      (V := dimensionedPlane) (p := 1) hyperplaneGenericPoint
      hyperplaneGenericPoint_coheight 1)

end AlgebraicGeometry.ProjectivePlane
