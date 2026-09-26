/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# The analytification of projective space is the linear projectivization

`ProjectiveAnalytification.lean` builds a continuous bijection
`projectivizationToComplexPoint` from the linear projectivization of `ℂ^{N+1}` onto the complex
points of scheme-theoretic projective space, but never packages it as a homeomorphism.  Since the
source is compact and the target is Hausdorff, the two are in fact homeomorphic; this file
records that, so that topological questions about `ℙᴺ(ℂ)^an` — in particular the construction of
its standard affine charts, needed for the `H⁰` comparison for twists — can be transported to the
concrete quotient model.
-/

@[expose] public noncomputable section

open CategoryTheory Metric
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ComplexProjectiveSpace

set_option backward.isDefEq.respectTransparency.types false in
/-- Equal projective-spectrum morphisms constructed from nonzero vectors determine the same
linear projective point. -/
lemma projectivization_mk_eq_of_chartIntegralProj_eq {n : ℕ}
    (v w : CoordinateSpace n) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : chartIntegralProj v hv = chartIntegralProj w hw) :
    Projectivization.mk ℂ v hv = Projectivization.mk ℂ w hw := by
  let i := coordinateIndex v hv
  have hi : v i ≠ 0 := coordinateIndex_ne_zero v hv
  have hvopen : IsLocalRing.closedPoint ℂ ∈
      chartIntegralProj v hv ⁻¹ᵁ
        Proj.basicOpen (UniversalGrading n) (MvPolynomial.X i) := by
    rw [chartIntegralProj_eq_chartIntegralProjAt v hv i hi,
      chartIntegralProjAt_preimage_basicOpen (d := 1) v i hi
        (MvPolynomial.X i) zero_lt_one (MvPolynomial.isHomogeneous_X _ _)]
    simp [hi]
    exact trivial
  have hwopen : IsLocalRing.closedPoint ℂ ∈
      chartIntegralProj w hw ⁻¹ᵁ
        Proj.basicOpen (UniversalGrading n) (MvPolynomial.X i) := by
    rw [← h]
    exact hvopen
  have hwi : w i ≠ 0 := by
    intro hwi
    rw [chartIntegralProj_eq_chartIntegralProjAt w hw
        (coordinateIndex w hw) (coordinateIndex_ne_zero w hw),
      chartIntegralProjAt_preimage_basicOpen (d := 1) w
        (coordinateIndex w hw) (coordinateIndex_ne_zero w hw)
        (MvPolynomial.X i) zero_lt_one (MvPolynomial.isHomogeneous_X _ _)] at hwopen
    have hfalse : IsLocalRing.closedPoint ℂ ∈
        (⊥ : (Spec (CommRingCat.of ℂ)).Opens) := by
      simpa [hwi] using hwopen
    exact (TopologicalSpace.Opens.mem_bot.mp hfalse).elim
  have hcharts : chartIntegralProjAt v i hi = chartIntegralProjAt w i hwi := by
    rw [← chartIntegralProj_eq_chartIntegralProjAt v hv i hi,
      ← chartIntegralProj_eq_chartIntegralProjAt w hw i hwi]
    exact h
  have hspec : Spec.map (CommRingCat.ofHom (awayCoordinateEvaluation v i hi)) =
      Spec.map (CommRingCat.ofHom (awayCoordinateEvaluation w i hwi)) := by
    unfold chartIntegralProjAt at hcharts
    exact (cancel_mono
      (Proj.awayι (UniversalGrading n) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X _ _) zero_lt_one)).mp hcharts
  have hcat : CommRingCat.ofHom (awayCoordinateEvaluation v i hi) =
      CommRingCat.ofHom (awayCoordinateEvaluation w i hwi) :=
    Spec.map_injective hspec
  have heval : awayCoordinateEvaluation v i hi = awayCoordinateEvaluation w i hwi :=
    congrArg ConcreteCategory.hom hcat
  apply (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).2
  refine ⟨v i * (w i)⁻¹, ?_⟩
  funext j
  have hj := DFunLike.congr_fun heval (chartCoordinate i j)
  change awayCoordinateEvaluation v i hi
      (HomogeneousLocalization.Away.mk (UniversalGrading n)
        (MvPolynomial.isHomogeneous_X _ i) 1 (MvPolynomial.X j) _) =
    awayCoordinateEvaluation w i hwi
      (HomogeneousLocalization.Away.mk (UniversalGrading n)
        (MvPolynomial.isHomogeneous_X _ i) 1 (MvPolynomial.X j) _) at hj
  rw [awayCoordinateEvaluation_mk
      (hr := MvPolynomial.isHomogeneous_X (ULift ℤ) j),
    awayCoordinateEvaluation_mk
      (hr := MvPolynomial.isHomogeneous_X (ULift ℤ) j)] at hj
  simp only [coordinateEvaluationHom_X] at hj
  change (v i * (w i)⁻¹) * w j = v j
  field_simp [hi, hwi] at hj ⊢
  exact hj.symm

set_option backward.isDefEq.respectTransparency.types false in
lemma injective_projectivizationToComplexPoint {n : ℕ} :
    Function.Injective (projectivizationToComplexPoint (n := n)) := by
  intro p q hpq
  induction p using Projectivization.ind with
  | _ v hv =>
      induction q using Projectivization.ind with
      | _ w hw =>
          apply projectivization_mk_eq_of_chartIntegralProj_eq v w hv hw
          change vectorToComplexPoint v hv = vectorToComplexPoint w hw at hpq
          have hspace := congrArg Over.Hom.left hpq
          change vectorToProjectiveSpace v hv = vectorToProjectiveSpace w hw at hspace
          have hsnd := congrArg (fun f ↦ f ≫ Limits.pullback.snd
            (Limits.terminal.from (Spec ↧ℂ))
            (Limits.terminal.from (Proj (UniversalGrading n)))) hspace
          rw [vectorToProjectiveSpace, vectorToProjectiveSpace,
            Limits.pullback.lift_snd, Limits.pullback.lift_snd] at hsnd
          exact hsnd

/-- Homogeneous coordinates identify the linear projectivization of `ℂ^{N+1}` with the
analytification of scheme-theoretic projective space, as topological spaces. -/
noncomputable def projectivizationHomeomorph (n : ℕ) :
    Projectivization ℂ (CoordinateSpace n) ≃ₜ
      ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (projectivizationToComplexPoint (n := n))
      ⟨injective_projectivizationToComplexPoint, surjective_projectivizationToComplexPoint⟩)
    continuous_projectivizationToComplexPoint

@[simp]
lemma projectivizationHomeomorph_apply (n : ℕ) (p : Projectivization ℂ (CoordinateSpace n)) :
    projectivizationHomeomorph n p = projectivizationToComplexPoint p :=
  rfl

@[simp]
lemma projectivizationHomeomorph_symm_apply (n : ℕ)
    (z : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ)))) :
    projectivizationToComplexPoint ((projectivizationHomeomorph n).symm z) = z :=
  (projectivizationHomeomorph n).apply_symm_apply z

end AlgebraicGeometry.ComplexProjectiveSpace
