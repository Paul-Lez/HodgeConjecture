/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.BettiScalarComparison
public import Other.AlgebraicGeometry.LefschetzOneOneReduction
public import Other.AlgebraicGeometry.ProjectiveAnalytificationHausdorff
public import Other.AlgebraicGeometry.ProjectiveAnalytificationParacompact
public import Other.AlgebraicTopology.IntegralSingularHomologyFinite
public import Other.AlgebraicGeometry.BettiScalarNaturality
public import Other.AlgebraicTopology.SimplicialCochainDenominators

/-!
# Integral denominator clearing from a finite good cover

This file reduces `HasIntegralDenominatorClearing` to the existence of a finite good cover of
the analytic space: such a cover makes integral singular homology finitely generated, the
integral and rational Betti comparisons are compatible with the coefficient map `ℤ → ℚ`, and
on singular cochains a rational class with a finitely generated integral homology group has a
nonzero integer multiple coming from an integral class.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))

/-- The analytic complex-point space admits a finite good cover: finitely many open sets, all of
whose nonempty finite intersections are contractible. -/
def HasFiniteGoodCover : Prop :=
  ∃ (ι : Type) (_ : LinearOrder ι) (U : ι → Set (ComplexPoint X)),
    AlgebraicTopology.Singular.FiniteGoodCover (TopCat.of (ComplexPoint X)) U

/-- A finite good cover makes every integral singular homology group finitely generated. -/
theorem module_finite_singularHomology_of_hasFiniteGoodCover (h : HasFiniteGoodCover X) (n : ℕ) :
    Module.Finite ℤ ((AlgebraicTopology.Singular.SingularChainComplex ℤ
      (TopCat.of (ComplexPoint X))).homology n) := by
  obtain ⟨ι, hι, U, hU⟩ := h
  let := hι
  exact AlgebraicTopology.Singular.singularChainComplex_homology_module_finite_of_finiteGoodCover
    hU n

/-- The second integral singular homology group of the analytic complex-point space is finitely
generated. This is the only input from the topology of `X^an` used for denominator clearing. -/
def HasFiniteSecondHomology : Prop :=
  Module.Finite ℤ ((AlgebraicTopology.Singular.SingularChainComplex ℤ
    (TopCat.of (ComplexPoint X))).homology 2)

theorem hasFiniteSecondHomology_of_hasFiniteGoodCover (h : HasFiniteGoodCover X) :
    HasFiniteSecondHomology X :=
  module_finite_singularHomology_of_hasFiniteGoodCover X h 2

open AlgebraicTopology.Singular in
/-- Change of coefficients on ordinary singular cohomology, evaluated through the forgotten
cochain complexes. -/
lemma ordinarySingularCohomologyCoefficientChange_apply
    {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (Y : TopCat.{0}) (n : ℕ)
    (a : OrdinarySingularCohomology R Y n) :
    ordinarySingularCohomologyCoefficientChange f Y n a =
      (ordinaryForgottenSingularCochainHomologyIso S Y n).hom
        (HomologicalComplex.homologyMap
          (ordinaryForgottenSingularCochainCoefficientChange f Y) n
            ((ordinaryForgottenSingularCochainHomologyIso R Y n).inv a)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Finitely generated second integral homology of the analytic space gives integral denominator
clearing in degree two: every rational class has a nonzero integer multiple in the image of
integral cohomology. -/
theorem hasIntegralDenominatorClearing_of_hasFiniteSecondHomology
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (h : HasFiniteSecondHomology X) : HasIntegralDenominatorClearing X := by
  intro α₀
  let Y := TopCat.of (ComplexPoint X)
  let : ∀ U : Opens (ComplexPoint X), ParacompactSpace U := openParacompactSpace X
  let α : ScalarCohomology X ℚ ((2 : ℕ) : ℤ) := α₀
  let Eℤ := scalarCohomologyAddEquivOrdinarySingularCohomology X ℤ 2
  let Eℚ := scalarCohomologyAddEquivOrdinarySingularCohomology X ℚ 2
  let Fℤ := (AlgebraicTopology.Singular.ordinaryForgottenSingularCochainHomologyIso ℤ Y 2)
    |>.addCommGroupIsoToAddEquiv
  let Fℚ := (AlgebraicTopology.Singular.ordinaryForgottenSingularCochainHomologyIso ℚ Y 2)
    |>.addCommGroupIsoToAddEquiv
  let : Module.Finite ℤ (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ ℤ)).homology 2) := h
  obtain ⟨m, β₀, hm, hβ₀⟩ := SSet.exists_integer_multiple_of_finite_homology
    (TopCat.toSSet.obj Y) 2 (Fℚ.symm (Eℚ α))
  let β' : (AlgebraicTopology.Singular.ordinaryForgottenSingularCochainComplex ℤ Y).homology 2 :=
    β₀
  have hβ' : HomologicalComplex.homologyMap
      (AlgebraicTopology.Singular.ordinaryForgottenSingularCochainCoefficientChange
        (Int.castRingHom ℚ) Y) 2 β' = m • Fℚ.symm (Eℚ α) := hβ₀
  refine ⟨m, Eℤ.symm (Fℤ β'), hm, ?_⟩
  have h1 : integralToRationalCohomology X 2 (Eℤ.symm (Fℤ β')) =
      hypercohomologyMap X (constantCoefficientSheafComplexIntMap X (Int.castRingHom ℚ))
        ((2 : ℕ) : ℤ) (Eℤ.symm (Fℤ β')) := by
    rw [constantCoefficientSheafComplexIntMap_intCast]
    rfl
  rw [h1]
  change hypercohomologyMap X (constantCoefficientSheafComplexIntMap X (Int.castRingHom ℚ))
    ((2 : ℕ) : ℤ) (Eℤ.symm (Fℤ β')) = m • α
  apply Eℚ.injective
  rw [map_zsmul]
  change scalarCohomologyEquivOrdinarySingularCohomology X ℚ 2 _ = _
  rw [scalarCohomologyEquivOrdinarySingularCohomology_coefficientChange]
  change AlgebraicTopology.Singular.ordinarySingularCohomologyCoefficientChange
    (Int.castRingHom ℚ) Y 2 (Eℤ (Eℤ.symm (Fℤ β'))) = m • Eℚ α
  rw [Eℤ.apply_symm_apply, ordinarySingularCohomologyCoefficientChange_apply]
  change Fℚ (HomologicalComplex.homologyMap
    (AlgebraicTopology.Singular.ordinaryForgottenSingularCochainCoefficientChange
      (Int.castRingHom ℚ) Y) 2 (Fℤ.symm (Fℤ β'))) = m • Eℚ α
  rw [Fℤ.symm_apply_apply, hβ', map_zsmul, Fℚ.apply_symm_apply]

/-- A finite good cover of the analytic space gives integral denominator clearing. -/
theorem hasIntegralDenominatorClearing_of_hasFiniteGoodCover
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (h : HasFiniteGoodCover X) : HasIntegralDenominatorClearing X :=
  hasIntegralDenominatorClearing_of_hasFiniteSecondHomology X
    (hasFiniteSecondHomology_of_hasFiniteGoodCover X h)

/-- The rational Lefschetz `(1, 1)` theorem follows from finite generation of the second
integral homology of all analytic spaces together with the divisor representation of
unit-sheaf extensions. -/
theorem _root_.RationalLefschetzOneOne.of_finiteSecondHomology_of_divisor
    (hfin : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasFiniteSecondHomology X)
    (hdivisor : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasDivisorOfUnitExtension X) :
    RationalLefschetzOneOne :=
  RationalLefschetzOneOne.of_obligations
    (fun X _ _ _ ↦ hasIntegralDenominatorClearing_of_hasFiniteSecondHomology X (hfin X)) hdivisor

/-- The rational Lefschetz `(1, 1)` theorem follows from finite good covers of all analytic
spaces together with the divisor representation of unit-sheaf extensions. Integral denominator
clearing is no longer an independent obligation. -/
theorem _root_.RationalLefschetzOneOne.of_finiteGoodCover_of_divisor
    (hcover : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasFiniteGoodCover X)
    (hdivisor : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom],
      HasDivisorOfUnitExtension X) :
    RationalLefschetzOneOne :=
  RationalLefschetzOneOne.of_obligations
    (fun X _ _ _ ↦ hasIntegralDenominatorClearing_of_hasFiniteGoodCover X (hcover X)) hdivisor

end AlgebraicGeometry.ComplexPoint
