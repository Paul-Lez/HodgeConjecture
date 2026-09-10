/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticChartRings
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.Topology.Sets.OpenCover

/-!
# Integral affine charts of the explicit projective cubic

Both affine defining equations are irreducible. Their prime ideals make the actual curve charts
integral, and their nonempty overlap makes the whole reduced projective cubic integral.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial

namespace AlgebraicGeometry.ExplicitEllipticCandidate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Regard `ℂ[u,v]` as `ℂ[u][v]`, matching the Weierstrass affine-coordinate convention. -/
def bivariateEquiv : MvPolynomial (Fin 2) ℂ ≃+* Polynomial (Polynomial ℂ) :=
  ((MvPolynomial.renameEquiv ℂ (Equiv.swap (0 : Fin 2) 1)).toRingEquiv.trans
    (MvPolynomial.finSuccEquiv ℂ 1).toRingEquiv).trans
      (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).toRingEquiv)

@[simp]
theorem bivariateEquiv_X_zero : bivariateEquiv (X 0) = Polynomial.C Polynomial.X := by
  simp only [bivariateEquiv, RingEquiv.trans_apply,
    AlgEquiv.coe_ringEquiv, renameEquiv_apply, rename_X, Equiv.swap_apply_left,
    Polynomial.mapEquiv_apply]
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv ℂ 1 (X (Fin.succ (0 : Fin 1)))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ]
  simp [MvPolynomial.uniqueAlgEquiv]

@[simp]
theorem bivariateEquiv_X_one : bivariateEquiv (X 1) = Polynomial.X := by
  simp [bivariateEquiv, MvPolynomial.finSuccEquiv_X_zero]

@[simp]
theorem chartEquation_z : chartEquation (Equiv.refl (Fin 3)) = X 1 ^ 2 - X 0 ^ 3 + X 0 := by
  simp [chartEquation, dehomogenize_cubic_z]

@[simp]
theorem chartEquation_y : chartEquation (Equiv.swap (1 : Fin 3) 2) =
    X 1 - X 0 ^ 3 + X 0 * X 1 ^ 2 := by
  simp [chartEquation, dehomogenize_cubic_y]

/-- The affine equation in the `Z` chart is exactly the existing Weierstrass polynomial. -/
theorem bivariateEquiv_chartEquation_z :
    bivariateEquiv (chartEquation (Equiv.refl (Fin 3))) = equation.toAffine.polynomial := by
  simp [WeierstrassCurve.Affine.polynomial, equation]
  ring

/-- The `Z` chart's defining polynomial is irreducible. -/
theorem chartEquation_z_irreducible : Irreducible (chartEquation (Equiv.refl (Fin 3))) := by
  apply (MulEquiv.irreducible_iff bivariateEquiv).mp
  rw [bivariateEquiv_chartEquation_z]
  exact WeierstrassCurve.Affine.irreducible_polynomial

/-- The `Z` chart's principal defining ideal is prime. -/
theorem chartEquation_z_prime : (Ideal.span {chartEquation (Equiv.refl (Fin 3))}).IsPrime :=
  (Ideal.span_singleton_prime chartEquation_z_irreducible.ne_zero).2
    chartEquation_z_irreducible.prime

/-- In the other variable order, the `Y` chart equation is the negative of this monic cubic. -/
def yChartMonic : Polynomial (Polynomial ℂ) :=
  Cubic.toPoly ⟨1, 0, -(Polynomial.X ^ 2), -Polynomial.X⟩

/-- The cubic in the `Y` chart satisfies Eisenstein's criterion at the remaining coordinate. -/
theorem yChartMonic_irreducible : Irreducible yChartMonic := by
  let P : Ideal (Polynomial ℂ) := Ideal.span {Polynomial.X}
  have hP : P.IsPrime := (Ideal.span_singleton_prime Polynomial.X_ne_zero).2 Polynomial.prime_X
  have hm : yChartMonic.Monic := Cubic.monic_of_a_eq_one'
  have hn : yChartMonic.natDegree = 3 := Cubic.natDegree_of_a_ne_zero' one_ne_zero
  have he : yChartMonic.IsEisensteinAt P := hm.isEisensteinAt_of_mem_of_notMem hP.ne_top
    (by
      intro n hn'
      rw [hn] at hn'
      interval_cases n <;>
        simp [yChartMonic, P, Ideal.mem_span_singleton])
    (by
      simp only [yChartMonic, Cubic.coeff_eq_d]
      dsimp only [P]
      rw [Ideal.neg_mem_iff, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      intro h
      have hh := Polynomial.X_pow_dvd_iff.mp h 1 (by decide)
      simp at hh)
  exact he.irreducible hP hm.isPrimitive (by omega)

/-- The defining polynomial of the `Y` chart is irreducible as well. -/
theorem chartEquation_y_irreducible :
    Irreducible (chartEquation (Equiv.swap (1 : Fin 3) 2)) := by
  let E := (MvPolynomial.renameEquiv ℂ (Equiv.swap (0 : Fin 2) 1)).toRingEquiv.trans bivariateEquiv
  have hE : E (chartEquation (Equiv.swap (1 : Fin 3) 2)) = -yChartMonic := by
    simp [E, yChartMonic, Cubic.toPoly]
    ring
  apply (MulEquiv.irreducible_iff E).mp
  rw [hE]
  exact Associated.irreducible ⟨-1, mul_neg_one yChartMonic⟩ yChartMonic_irreducible

/-- The principal ideal defining the `Y` chart is prime. -/
theorem chartEquation_y_prime :
    (Ideal.span {chartEquation (Equiv.swap (1 : Fin 3) 2)}).IsPrime :=
  (Ideal.span_singleton_prime chartEquation_y_irreducible.ne_zero).2
    chartEquation_y_irreducible.prime

/-- Prime chart equations give integral actual open subschemes of the projective cubic. -/
theorem curveChart_isIntegral (e : Equiv.Perm (Fin 3))
    (h : (Ideal.span {chartEquation e}).IsPrime) : IsIntegral (curveChart e) := by
  let I : Ideal (MvPolynomial (Fin 2) ℂ) := Ideal.span {chartEquation e}
  have hI : I.IsPrime := h
  have : IsDomain (MvPolynomial (Fin 2) ℂ ⧸ I.radical) := by
    rw [hI.isRadical.radical]
    let := hI
    infer_instance
  have : IsIntegral (Spec (CommRingCat.of (MvPolynomial (Fin 2) ℂ ⧸ I.radical))) :=
    inferInstance
  exact IsIntegral.of_isIso (curveChartIso e).inv

instance chart_two_isIntegral : IsIntegral (chart 2).toScheme := by
  exact curveChart_isIntegral (Equiv.refl (Fin 3)) chartEquation_z_prime

instance chart_one_isIntegral : IsIntegral (chart 1).toScheme := by
  exact curveChart_isIntegral (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime

/-- The two integral charts with nonempty overlap make the actual projective cubic irreducible. -/
instance curve_irreducibleSpace : IrreducibleSpace curve := by
  let U : Fin 2 → curve.Opens := ![chart 1, chart 2]
  have hn : ¬ Disjoint (chart 1) (chart 2) := by
    intro h
    have he : chart 1 ⊓ chart 2 = ⊥ := disjoint_iff.mp h
    have hne := chart_inter_nonempty
    rw [he] at hne
    exact Set.not_nonempty_empty hne
  have hpair : Pairwise (fun i j => ¬ Disjoint (U i) (U j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hn
    · exact fun h => hn h.symm
    · exact (hij rfl).elim
  have hcover : TopologicalSpace.IsOpenCover U := by
    apply top_unique
    rw [← chart_one_sup_chart_two]
    exact sup_le (le_iSup U 0) (le_iSup U 1)
  have hp (i : Fin 2) : PreirreducibleSpace (U i) := by
    fin_cases i
    · exact inferInstanceAs (PreirreducibleSpace (chart 1).toScheme)
    · exact inferInstanceAs (PreirreducibleSpace (chart 2).toScheme)
  have := PreirreducibleSpace.of_isOpenCover hpair hcover hp
  exact ⟨inferInstance⟩

/-- The explicitly constructed projective cubic is an integral scheme. -/
instance curve_isIntegral : IsIntegral curve :=
  isIntegral_of_irreducibleSpace_of_isReduced curve

end AlgebraicGeometry.ExplicitEllipticCandidate
