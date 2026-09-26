/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.TorusIntegral
public import Mathlib.Data.Finsupp.Encodable
public import Other.Oka.LocalOkaRing

/-!
# Analyticity of parametric circle integrals

This file develops the several complex variables analysis that the local Weierstrass division
theorem of `Other/Oka/Weierstrass.lean` rests on: the Cauchy integral formula on a polydisc, and the
analyticity in the parameters of a circle integral whose integrand depends holomorphically on
them.

The route is the classical one. On a polydisc the Cauchy kernel `∏ i, (ζ i - w i)⁻¹` expands as
a multivariate geometric series indexed by multi-indices `d : Fin m →₀ ℕ`; the expansion may be
integrated term by term over the distinguished boundary, so a function represented by its Cauchy
integral is the sum of a convergent power series, hence analytic. Feeding a parametric circle
integral into that statement, after exchanging the torus and the circle integral by Fubini,
gives the two results `Other/Oka/Weierstrass.lean` consumes, `analyticAt_circleIntegral` and
`analyticAt_circleIntegral_snoc`.

## Main definitions

- `finsuppConsEquiv m`: the reindexing `(Fin (m + 1) →₀ ℕ) ≃ ℕ × (Fin m →₀ ℕ)` peeling the
  `0`-th entry off a multi-index.

## Main results

Convergent power series are analytic:

- `MvPowerSeries.hasFPowerSeriesOnBall_of_summableAt_const`: a formal power series summable at
  the constant point `ρ` has its evaluation as the sum of its formal multilinear series on the
  ball of radius `ρ`; `MvPowerSeries.analyticAt_eval_of_summableAt_const` is the pointwise form.
- `analyticAt_of_represents`: a function represented near the origin by a locally convergent
  power series is analytic there; `analyticAt_of_shift` moves analyticity at the origin to
  analyticity at an arbitrary point.

The multivariate geometric series and the Cauchy kernel:

- `summable_norm_multiGeometric` and `hasSum_multiGeometric`: for `‖a i‖ < 1` the family
  `d ↦ ∏ i, a i ^ d i`, indexed by `d : Fin m →₀ ℕ`, is absolutely summable with sum
  `∏ i, (1 - a i)⁻¹`.
- `hasSum_cauchyKernel`: the resulting expansion of `∏ i, (ζ i - w i)⁻¹` in powers of `w`.
- `hasSum_torusIntegral`: a summable family may be integrated term by term over a torus, with
  `torusIntegrable_cauchyTerm` and `summable_integral_norm_cauchyTerm` supplying its hypotheses
  for the terms of the Cauchy expansion.

The Cauchy integral formula on a polydisc:

- `cauchy_torus_formula`: for `f` holomorphic on the closed polydisc of polyradius `R` about `c`
  and `w` in its interior, `f w = (2 * π * I)⁻¹ ^ m • ∯ ζ in T(c, R), (∏ i, (ζ i - w i)⁻¹) • f ζ`.
- `analyticAt_of_cauchyRepr`: a continuous function satisfying that representation on a polydisc
  centred at the origin is analytic at the origin.
- `analyticAt_of_differentiableOn`: consequently a function differentiable on an open set is
  analytic at each of its points.

Parametric circle integrals:

- `torusIntegral_circleIntegral_swap`: a torus integral and a circle integral of a jointly
  continuous function commute.
- `continuousOn_circleIntegral`: a circle integral depending continuously on a parameter is
  continuous in the parameter.
- `analyticAt_circleIntegral`: if `G x ζ` is holomorphic in `x` on a closed polydisc for each `ζ`
  on the circle of radius `ε`, and jointly continuous, then `x ↦ ∮ ζ in C(0, ε), G x ζ` is
  analytic at the origin.
- `analyticAt_circleIntegral_snoc`: the form used downstream, for an integrand
  `F (Fin.snoc w ζ) / G (Fin.snoc w ζ) * E w ζ` where the circle variable `ζ` is substituted
  into the *last* coordinate and `G` does not vanish there.

## Implementation notes

The induction proving the multivariate geometric series is on the number of variables, peeling
off the `0`-th one: `finsuppConsEquiv` and the `Finsupp.cons`/`Finsupp.tail` API are what let a
sum over `Fin (m + 1) →₀ ℕ` be rewritten as an iterated sum over `ℕ` and `Fin m →₀ ℕ`. The
equivalence is used only in those two proofs.

The last section instead singles out the *last* variable, because that is the one Weierstrass
theory distinguishes. Hence the cluster of plumbing lemmas about maps built from `Fin.snoc`:
each is a routine differentiability, norm or continuity statement, stated separately to keep
`analyticAt_circleIntegral_snoc` readable. Note that the `Fin.init` variants
(`differentiable_snocInit`, `norm_snocInit_le`, `continuous_snocInit_circleMap`), and also
`differentiable_snoc_last`, are not used in this file at all; they are here because they belong
with their siblings, and are consumed by `Other/Oka/Weierstrass.lean`.

## References

- [Lars Hörmander, *An introduction to complex analysis in several variables*][hormander1990],
  §2.2
- [Robert C. Gunning and Hugo Rossi, *Analytic functions of several complex
  variables*][gunning-rossi1965], §I.A
-/

@[expose] public section

open Complex
open scoped Topology

namespace MvPowerSeries

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : MvPowerSeries ι ℂ}

/-- If `P` converges absolutely at the constant point `ρ`, then `P.eval` is the sum of its
formal multilinear series on the ball of radius `ρ`. -/
theorem hasFPowerSeriesOnBall_of_summableAt_const {ρ : ℝ} (hρ : 0 < ρ)
    (hsum : P.SummableAt (fun _ ↦ (ρ : ℂ))) :
    HasFPowerSeriesOnBall P.eval (toFPS P) 0 (ENNReal.ofReal ρ) := by
  refine ⟨?_, ENNReal.ofReal_pos.mpr hρ, ?_⟩
  · have hbound : ∀ n : ℕ, ‖toFPS P n‖ * ((Real.toNNReal ρ : NNReal) : ℝ) ^ n ≤
        ∑' d, ‖P.term (fun _ ↦ (ρ : ℂ)) d‖ := by
      intro n
      rw [Real.coe_toNNReal ρ hρ.le]
      have h1 : ‖toFPS P n‖ * ρ ^ n ≤ (∑ d ∈ degFinset ι n, ‖coeff d P‖) * ρ ^ n :=
        mul_le_mul_of_nonneg_right (norm_toFPS_le n) (by positivity)
      have h2 : (∑ d ∈ degFinset ι n, ‖coeff d P‖) * ρ ^ n
          = ∑ d ∈ degFinset ι n, ‖P.term (fun _ ↦ (ρ : ℂ)) d‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun d hd ↦ (norm_term_const hρ.le hd).symm
      have h3 : ∑ d ∈ degFinset ι n, ‖P.term (fun _ ↦ (ρ : ℂ)) d‖ ≤
          ∑' d, ‖P.term (fun _ ↦ (ρ : ℂ)) d‖ :=
        le_hasSum (hasSum_degree_norm hsum) n fun m _ ↦
          Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
      rw [h2] at h1
      exact h1.trans h3
    exact (toFPS P).le_radius_of_bound _ hbound
  · intro y hy
    rw [Metric.eball_ofReal, mem_ball_zero_iff] at hy
    have hle : ∀ i, ‖y i‖ ≤ ‖(fun _ ↦ (ρ : ℂ)) i‖ := fun i ↦ by
      refine (norm_le_pi_norm y i).trans ?_
      simp [Complex.norm_real, Real.norm_of_nonneg hρ.le, hy.le]
    have := hasSum_degree (P := P) (x := y) (hsum.mono hle).hasSum
    simpa only [toFPS_apply_diag, zero_add] using this

omit [DecidableEq ι] in
/-- `P.eval` is analytic at every point of the open ball of radius `ρ`. -/
theorem analyticAt_eval_of_summableAt_const {ρ : ℝ} (hρ : 0 < ρ)
    (hsum : P.SummableAt (fun _ ↦ (ρ : ℂ))) {x : ι → ℂ} (hx : ‖x‖ < ρ) :
    AnalyticAt ℂ P.eval x := by
  classical
  refine (hasFPowerSeriesOnBall_of_summableAt_const hρ hsum).analyticOnNhd x ?_
  rw [Metric.eball_ofReal, mem_ball_zero_iff]
  exact hx

end MvPowerSeries

open MvPowerSeries in
lemma analyticAt_of_represents {m : ℕ} {P : MvPowerSeries (Fin m) ℂ} {g : (Fin m → ℂ) → ℂ}
    (hP : LocallyConvergent P) (hrep : Represents P g) : AnalyticAt ℂ g 0 := by
  refine hP.analyticAt.congr ?_
  filter_upwards [hrep] with x hx
  exact hx.tsum_eq

lemma analyticAt_of_shift {m : ℕ} {f : (Fin m → ℂ) → ℂ} {x₀ : Fin m → ℂ}
    (h : AnalyticAt ℂ (fun y ↦ f (x₀ + y)) 0) : AnalyticAt ℂ f x₀ := by
  have hcomp : AnalyticAt ℂ ((fun y ↦ f (x₀ + y)) ∘ (fun x ↦ x - x₀)) x₀ :=
    AnalyticAt.comp (by simpa using h) (analyticAt_id.sub analyticAt_const)
  have hfe : ((fun y ↦ f (x₀ + y)) ∘ (fun x ↦ x - x₀)) = f := by
    funext x
    simp only [Function.comp_apply]
    congr 1
    abel
  rwa [hfe] at hcomp

/-- Peel off the `0`-th coordinate of a `Fin (m+1)`-indexed `Finsupp`. -/
noncomputable def finsuppConsEquiv (m : ℕ) : (Fin (m + 1) →₀ ℕ) ≃ ℕ × (Fin m →₀ ℕ) where
  toFun t := (t 0, Finsupp.tail t)
  invFun p := Finsupp.cons p.1 p.2
  left_inv t := Finsupp.cons_tail t
  right_inv p := by obtain ⟨y, s⟩ := p; simp

@[simp] lemma finsuppConsEquiv_apply (m : ℕ) (t : Fin (m + 1) →₀ ℕ) :
    finsuppConsEquiv m t = (t 0, Finsupp.tail t) := rfl

@[simp] lemma finsuppConsEquiv_symm_apply (m : ℕ) (p : ℕ × (Fin m →₀ ℕ)) :
    (finsuppConsEquiv m).symm p = Finsupp.cons p.1 p.2 := rfl

/-- The multivariate geometric series converges absolutely: if `‖a i‖ < 1` for every `i`, then
the family `d ↦ ∏ i, a i ^ d i` indexed by multi-indices `d : Fin m →₀ ℕ` is norm-summable. -/
theorem summable_norm_multiGeometric :
    ∀ (m : ℕ) (a : Fin m → ℂ), (∀ i, ‖a i‖ < 1) →
      Summable (fun d : Fin m →₀ ℕ ↦ ‖∏ i, (a i) ^ (d i)‖) := by
  intro m
  induction m with
  | zero =>
      intro a _
      exact (hasSum_single (0 : Fin 0 →₀ ℕ)
        (f := fun d : Fin 0 →₀ ℕ ↦ ‖∏ i, (a i) ^ (d i)‖)
        (fun b' hb' => absurd (Subsingleton.elim b' 0) hb')).summable
  | succ m ih =>
      intro a ha
      have hf : Summable (fun k : ℕ ↦ ‖(a 0) ^ k‖) := by
        simp_rw [norm_pow]
        exact summable_geometric_of_lt_one (norm_nonneg _) (ha 0)
      have hg : Summable (fun t : Fin m →₀ ℕ ↦ ‖∏ i, (a (Fin.succ i)) ^ (t i)‖) :=
        ih (fun i : Fin m => a (Fin.succ i)) (fun i : Fin m => ha (Fin.succ i))
      have hfun :
          (fun d : Fin (m + 1) →₀ ℕ ↦ ‖∏ i, (a i) ^ (d i)‖) ∘ (finsuppConsEquiv m).symm
            = fun x : ℕ × (Fin m →₀ ℕ) ↦ ‖(a 0) ^ x.1 * ∏ i, (a (Fin.succ i)) ^ (x.2 i)‖ := by
        funext x
        simp only [Function.comp_apply, finsuppConsEquiv_symm_apply,
          Fin.prod_univ_succ, Finsupp.cons_zero, Finsupp.cons_succ]
      refine (Equiv.summable_iff (finsuppConsEquiv m).symm).mp ?_
      rw [hfun]
      exact Summable.mul_norm
        (f := fun k : ℕ => (a 0) ^ k)
        (g := fun t : Fin m →₀ ℕ => ∏ i, (a (Fin.succ i)) ^ (t i)) hf hg

/-- The multivariate geometric series: if `‖a i‖ < 1` for every `i`, then the family
`d ↦ ∏ i, a i ^ d i` indexed by multi-indices `d : Fin m →₀ ℕ` sums to `∏ i, (1 - a i)⁻¹`. -/
theorem hasSum_multiGeometric :
    ∀ (m : ℕ) (a : Fin m → ℂ), (∀ i, ‖a i‖ < 1) →
      HasSum (fun d : Fin m →₀ ℕ ↦ ∏ i, (a i) ^ (d i)) (∏ i, (1 - a i)⁻¹) := by
  intro m
  induction m with
  | zero =>
      intro a _
      have e1 : (fun d : Fin 0 →₀ ℕ ↦ ∏ i, (a i) ^ (d i)) = fun _ => (1 : ℂ) := by
        funext d; simp
      have e2 : (∏ i, (1 - a i)⁻¹ : ℂ) = 1 := by simp
      rw [e1, e2]
      exact hasSum_single (0 : Fin 0 →₀ ℕ) (f := fun _ : Fin 0 →₀ ℕ => (1 : ℂ))
        (fun b' hb' => absurd (Subsingleton.elim b' 0) hb')
  | succ m ih =>
      intro a ha
      have hf : HasSum (fun k : ℕ ↦ (a 0) ^ k) (1 - a 0)⁻¹ :=
        hasSum_geometric_of_norm_lt_one (ha 0)
      have hg : HasSum (fun t : Fin m →₀ ℕ ↦ ∏ i, (a (Fin.succ i)) ^ (t i))
          (∏ i, (1 - a (Fin.succ i))⁻¹) :=
        ih (fun i : Fin m => a (Fin.succ i)) (fun i : Fin m => ha (Fin.succ i))
      have hnf : Summable (fun k : ℕ ↦ ‖(a 0) ^ k‖) := by
        simp_rw [norm_pow]
        exact summable_geometric_of_lt_one (norm_nonneg _) (ha 0)
      have hng : Summable (fun t : Fin m →₀ ℕ ↦ ‖∏ i, (a (Fin.succ i)) ^ (t i)‖) :=
        summable_norm_multiGeometric m (fun i : Fin m => a (Fin.succ i))
          (fun i : Fin m => ha (Fin.succ i))
      have hsummable : Summable
          (fun x : ℕ × (Fin m →₀ ℕ) ↦ (a 0) ^ x.1 * ∏ i, (a (Fin.succ i)) ^ (x.2 i)) :=
        summable_mul_of_summable_norm
          (f := fun k : ℕ => (a 0) ^ k)
          (g := fun t : Fin m →₀ ℕ => ∏ i, (a (Fin.succ i)) ^ (t i)) hnf hng
      have hmul := hf.mul hg hsummable
      have hval : (∏ i, (1 - a i)⁻¹ : ℂ)
          = (1 - a 0)⁻¹ * ∏ i : Fin m, (1 - a (Fin.succ i))⁻¹ := Fin.prod_univ_succ _
      have hfun :
          (fun d : Fin (m + 1) →₀ ℕ ↦ ∏ i, (a i) ^ (d i)) ∘ (finsuppConsEquiv m).symm
            = fun x : ℕ × (Fin m →₀ ℕ) ↦ (a 0) ^ x.1 * ∏ i, (a (Fin.succ i)) ^ (x.2 i) := by
        funext x
        simp only [Function.comp_apply, finsuppConsEquiv_symm_apply,
          Fin.prod_univ_succ, Finsupp.cons_zero, Finsupp.cons_succ]
      rw [hval]
      refine (Equiv.hasSum_iff (finsuppConsEquiv m).symm).mp ?_
      rw [hfun]
      exact hmul

/-- Geometric expansion of the Cauchy kernel in the multi-index `d`. -/
theorem hasSum_cauchyKernel {m : ℕ} (ζ w : Fin m → ℂ)
    (hζ : ∀ i, ζ i ≠ 0) (hlt : ∀ i, ‖w i‖ < ‖ζ i‖) :
    HasSum (fun d : Fin m →₀ ℕ ↦ (∏ i, (ζ i ^ (d i + 1))⁻¹) * ∏ i, (w i) ^ (d i))
      (∏ i, (ζ i - w i)⁻¹) := by
  have ha : ∀ i, ‖w i / ζ i‖ < 1 := by
    intro i
    rw [norm_div, div_lt_one (lt_of_le_of_lt (norm_nonneg _) (hlt i))]
    exact hlt i
  have hbase := hasSum_multiGeometric m (fun i => w i / ζ i) ha
  have hmul := hbase.mul_left (∏ i, (ζ i)⁻¹)
  have hval : (∏ i, (ζ i)⁻¹) * ∏ i, (1 - w i / ζ i)⁻¹ = ∏ i, (ζ i - w i)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have h1 : (1 : ℂ) - w i / ζ i = (ζ i - w i) / ζ i := by
      rw [sub_div, div_self (hζ i)]
    rw [h1, inv_div, ← mul_div_assoc, inv_mul_cancel₀ (hζ i), one_div]
  have hfun : (fun d : Fin m →₀ ℕ => (∏ i, (ζ i)⁻¹) * ∏ i, (w i / ζ i) ^ (d i))
      = fun d => (∏ i, (ζ i ^ (d i + 1))⁻¹) * ∏ i, (w i) ^ (d i) := by
    funext d
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [div_pow, div_eq_mul_inv, pow_succ, mul_inv_rev]
    ring
  rw [← hval, ← hfun]
  exact hmul

open MeasureTheory in
/-- Term-by-term integration over a torus. -/
theorem hasSum_torusIntegral {m : ℕ} {c : Fin m → ℂ} {R : Fin m → ℝ}
    {F : (Fin m →₀ ℕ) → (Fin m → ℂ) → ℂ} {S : (Fin m → ℂ) → ℂ}
    (hint : ∀ d, TorusIntegrable (F d) c R)
    (hsum : Summable (fun d ↦ ∫ θ in Set.Icc (0 : Fin m → ℝ) (fun _ ↦ 2 * Real.pi),
        ‖(∏ i, R i * Complex.exp (θ i * Complex.I) * Complex.I : ℂ) • F d (torusMap c R θ)‖))
    (hpt : ∀ θ : Fin m → ℝ,
        HasSum (fun d ↦ F d (torusMap c R θ)) (S (torusMap c R θ))) :
    HasSum (fun d ↦ ∯ ζ in T(c, R), F d ζ) (∯ ζ in T(c, R), S ζ) := by
  have key := hasSum_integral_of_summable_integral_norm
    (μ := (volume : Measure (Fin m → ℝ)).restrict
      (Set.Icc (0 : Fin m → ℝ) (fun _ ↦ 2 * Real.pi)))
    (F := fun d θ ↦ (∏ i, R i * Complex.exp (θ i * Complex.I) * Complex.I : ℂ)
      • F d (torusMap c R θ))
    (fun d ↦ (hint d).function_integrable) hsum
  have hintegrand :
      (fun θ : Fin m → ℝ ↦ ∑' d, (∏ i, R i * Complex.exp (θ i * Complex.I) * Complex.I : ℂ)
        • F d (torusMap c R θ))
        = fun θ ↦ (∏ i, R i * Complex.exp (θ i * Complex.I) * Complex.I : ℂ)
          • S (torusMap c R θ) := by
    funext θ
    exact ((hpt θ).const_smul
      (∏ i, R i * Complex.exp (θ i * Complex.I) * Complex.I : ℂ)).tsum_eq
  rw [hintegrand] at key
  exact key

open MeasureTheory in
/-- Each Cauchy term is torus-integrable on the polydisc of radius `ρ`. -/
theorem torusIntegrable_cauchyTerm {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {g : (Fin m → ℂ) → ℂ}
    (hg : ContinuousOn g (Set.univ.pi fun _ : Fin m ↦ Metric.closedBall (0 : ℂ) ρ))
    (x : Fin m → ℂ) (d : Fin m →₀ ℕ) :
    TorusIntegrable
      (fun ζ ↦ ((∏ i, (ζ i ^ (d i + 1))⁻¹) * ∏ i, (x i) ^ (d i)) * g ζ)
      (0 : Fin m → ℂ) (fun _ ↦ ρ) := by
  unfold TorusIntegrable
  have hnorm : ∀ (θ : Fin m → ℝ) (i), ‖torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ i‖ = ρ := by
    intro θ i
    simp [torusMap, Complex.norm_exp_ofReal_mul_I, abs_of_pos hρ]
  have htm : Continuous (fun θ : Fin m → ℝ ↦ torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ) := by
    unfold torusMap; fun_prop
  have hne : ∀ (θ : Fin m → ℝ) (i), torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ i ≠ 0 := by
    intro θ i hz
    have h := hnorm θ i
    rw [hz, norm_zero] at h
    exact (ne_of_lt hρ) h
  have hker : Continuous
      (fun θ : Fin m → ℝ ↦
        (∏ i, (torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ i ^ (d i + 1))⁻¹) * ∏ i, (x i) ^ (d i)) := by
    apply Continuous.mul _ continuous_const
    apply continuous_finsetProd
    intro i _
    exact (((continuous_apply i).comp htm).pow _).inv₀ (fun θ ↦ pow_ne_zero _ (hne θ i))
  have hmaps : Set.MapsTo (fun θ : Fin m → ℝ ↦ torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ)
      (Set.Icc 0 fun _ ↦ 2 * Real.pi)
      (Set.univ.pi fun _ : Fin m ↦ Metric.closedBall (0 : ℂ) ρ) := by
    intro θ _
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    simp only [Metric.mem_closedBall, Complex.dist_eq, sub_zero, hnorm, le_refl]
  exact ContinuousOn.integrableOn_compact isCompact_Icc
    (hker.continuousOn.mul (hg.comp htm.continuousOn hmaps))

open MeasureTheory in
/-- Geometric summability of the integral-norms of the Cauchy terms. -/
theorem summable_integral_norm_cauchyTerm {m : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {g : (Fin m → ℂ) → ℂ}
    {x : Fin m → ℂ} (hx : ∀ i, ‖x i‖ < ρ) :
    Summable (fun d : Fin m →₀ ℕ ↦
      ∫ θ in Set.Icc (0 : Fin m → ℝ) (fun _ ↦ 2 * Real.pi),
        ‖(∏ i, (ρ : ℂ) * Complex.exp (θ i * Complex.I) * Complex.I) •
          (((∏ i, (torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ i ^ (d i + 1))⁻¹) *
              ∏ i, (x i) ^ (d i)) *
            g (torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ))‖) := by
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  set tm : (Fin m → ℝ) → (Fin m → ℂ) := fun θ ↦ torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ with htm
  have hnorm : ∀ (θ : Fin m → ℝ) (i), ‖tm θ i‖ = ρ := by
    intro θ i
    simp [htm, torusMap, Complex.norm_exp_ofReal_mul_I, abs_of_pos hρ]
  have hpoint : ∀ (d : Fin m →₀ ℕ) (θ : Fin m → ℝ),
      ‖(∏ i, (ρ : ℂ) * Complex.exp (θ i * Complex.I) * Complex.I) •
          (((∏ i, (tm θ i ^ (d i + 1))⁻¹) * ∏ i, (x i) ^ (d i)) * g (tm θ))‖
        = (∏ i, (‖x i‖ / ρ) ^ (d i)) * ‖g (tm θ)‖ := by
    intro d θ
    rw [norm_smul, norm_mul, norm_mul]
    have hJac : ‖∏ i, (ρ : ℂ) * Complex.exp (θ i * Complex.I) * Complex.I‖ = ρ ^ m := by
      rw [norm_prod]
      have h1 : ∀ i ∈ (Finset.univ : Finset (Fin m)),
          ‖(ρ : ℂ) * Complex.exp (θ i * Complex.I) * Complex.I‖ = ρ := by
        intro i _
        rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I,
          Complex.norm_real, Real.norm_of_nonneg hρ.le, mul_one, mul_one]
      rw [Finset.prod_congr rfl h1, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hKer : ‖∏ i, (tm θ i ^ (d i + 1))⁻¹‖ = ∏ i, (ρ ^ (d i + 1))⁻¹ := by
      rw [norm_prod]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [norm_inv, norm_pow, hnorm]
    have hMon : ‖∏ i, (x i) ^ (d i)‖ = ∏ i, ‖x i‖ ^ (d i) := by
      rw [norm_prod]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [norm_pow]
    rw [hJac, hKer, hMon, ← mul_assoc]
    congr 1
    rw [← Finset.prod_mul_distrib,
      show ρ ^ m = ∏ _i : Fin m, ρ from by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [div_pow, pow_succ]
    field_simp
  have hEq : ∀ d : Fin m →₀ ℕ,
      (∫ θ in Set.Icc (0 : Fin m → ℝ) (fun _ ↦ 2 * Real.pi),
        ‖(∏ i, (ρ : ℂ) * Complex.exp (θ i * Complex.I) * Complex.I) •
          (((∏ i, (tm θ i ^ (d i + 1))⁻¹) * ∏ i, (x i) ^ (d i)) * g (tm θ))‖)
        = (∏ i, (‖x i‖ / ρ) ^ (d i)) *
          ∫ θ in Set.Icc (0 : Fin m → ℝ) (fun _ ↦ 2 * Real.pi), ‖g (tm θ)‖ := by
    intro d
    simp_rw [hpoint d]
    rw [integral_const_mul]
  have hxρ : ∀ i, ‖x i / (ρ : ℂ)‖ < 1 := by
    intro i
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le, div_lt_one hρ]
    exact hx i
  have hbase : Summable (fun d : Fin m →₀ ℕ ↦ ∏ i, (‖x i‖ / ρ) ^ (d i)) := by
    refine (summable_norm_multiGeometric m (fun i ↦ x i / (ρ : ℂ)) hxρ).congr (fun d => ?_)
    rw [norm_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  refine (hbase.mul_right
    (∫ θ in Set.Icc (0 : Fin m → ℝ) (fun _ ↦ 2 * Real.pi), ‖g (tm θ)‖)).congr (fun d => ?_)
  exact (hEq d).symm

lemma differentiableOn_cons_slice {m : ℕ} {f : (Fin (m + 1) → ℂ) → ℂ}
    {c : Fin (m + 1) → ℂ} {R : Fin (m + 1) → ℝ}
    (hf : DifferentiableOn ℂ f (Set.univ.pi fun i ↦ Metric.closedBall (c i) (R i)))
    {x : ℂ} (hx : x ∈ Metric.closedBall (c 0) (R 0)) :
    DifferentiableOn ℂ (fun y : Fin m → ℂ ↦ f (Fin.cons x y))
      (Set.univ.pi fun i ↦ Metric.closedBall (c i.succ) (R i.succ)) := by
  have hg : Differentiable ℂ (fun y : Fin m → ℂ ↦ (Fin.cons x y : Fin (m + 1) → ℂ)) := by
    refine differentiable_pi.mpr fun i ↦ ?_
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · simpa using differentiable_apply (𝕜 := ℂ) j
  refine hf.comp hg.differentiableOn ?_
  intro y hy
  simp only [Set.mem_pi, Set.mem_univ, true_implies] at hy ⊢
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa using hx
  · simpa using hy j

theorem cauchy_torus_formula {m : ℕ} (f : (Fin m → ℂ) → ℂ) (c : Fin m → ℂ) (R : Fin m → ℝ)
    (hR : ∀ i, 0 < R i)
    (hf : DifferentiableOn ℂ f (Set.univ.pi fun i ↦ Metric.closedBall (c i) (R i)))
    (w : Fin m → ℂ) (hw : ∀ i, w i ∈ Metric.ball (c i) (R i)) :
    f w = (2 * ↑Real.pi * Complex.I)⁻¹ ^ m •
      ∯ ζ in T(c, R), (∏ i, (ζ i - w i)⁻¹) • f ζ := by
  induction m with
  | zero =>
    rw [torusIntegral_dim0, Subsingleton.elim w c]
    simp
  | succ m ih =>
    -- tail of w
    set w' : Fin m → ℂ := fun i ↦ w i.succ with hw'
    -- (c) the (m+1)-dimensional integrand is torus-integrable
    have hint : TorusIntegrable (fun ζ ↦ (∏ i, (ζ i - w i)⁻¹) • f ζ) c R := by
      unfold TorusIntegrable
      have hnorm : ∀ (θ : Fin (m + 1) → ℝ) (i), ‖torusMap c R θ i - c i‖ = R i := by
        intro θ i
        simp [torusMap, Complex.norm_exp_ofReal_mul_I, abs_of_pos (hR i)]
      have htm : Continuous (fun θ : Fin (m + 1) → ℝ ↦ torusMap c R θ) := by
        unfold torusMap; fun_prop
      have hne : ∀ (θ : Fin (m + 1) → ℝ) (i), torusMap c R θ i - w i ≠ 0 := by
        intro θ i hz
        have heq : torusMap c R θ i = w i := sub_eq_zero.mp hz
        have hlt := Metric.mem_ball.mp (hw i)
        rw [Complex.dist_eq, ← heq, hnorm] at hlt
        exact lt_irrefl _ hlt
      have hker : Continuous (fun θ : Fin (m + 1) → ℝ ↦ ∏ i, (torusMap c R θ i - w i)⁻¹) := by
        apply continuous_finsetProd
        intro i _
        exact (((continuous_apply i).comp htm).sub continuous_const).inv₀ (fun θ ↦ hne θ i)
      have hmaps : Set.MapsTo (fun θ : Fin (m + 1) → ℝ ↦ torusMap c R θ)
          (Set.Icc 0 fun _ ↦ 2 * Real.pi)
          (Set.univ.pi fun i ↦ Metric.closedBall (c i) (R i)) := by
        intro θ _
        simp only [Set.mem_pi, Set.mem_univ, true_implies]
        intro i
        simp only [Metric.mem_closedBall, Complex.dist_eq, hnorm, le_refl]
      exact ContinuousOn.integrableOn_compact isCompact_Icc
        (hker.continuousOn.smul (hf.continuousOn.comp htm.continuousOn hmaps))
    -- (d) the Cauchy kernel factors along the first coordinate
    have hker : ∀ (x : ℂ) (y : Fin m → ℂ),
        (∏ i, ((Fin.cons x y : Fin (m + 1) → ℂ) i - w i)⁻¹)
          = (x - w 0)⁻¹ * ∏ i, (y i - w' i)⁻¹ := by
      intro x y
      rw [Fin.prod_univ_succ]
      simp [Fin.cons_zero, Fin.cons_succ, hw']
    -- (b-inner) inner torus integral evaluated by ih, for x in the closed disk
    have h2pi : (2 * ↑Real.pi * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    have hinner : ∀ x ∈ Metric.closedBall (c 0) (R 0),
        (∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ), (∏ i, (y i - w' i)⁻¹) • f (Fin.cons x y))
          = (2 * ↑Real.pi * Complex.I) ^ m • f (Fin.cons x w') := by
      intro x hx
      have hih := ih (fun y ↦ f (Fin.cons x y)) (c ∘ Fin.succ) (R ∘ Fin.succ)
        (fun i ↦ hR i.succ)
        (differentiableOn_cons_slice hf hx)
        w' (fun i ↦ by simpa [hw'] using hw i.succ)
      rw [hih, smul_smul, ← mul_pow, mul_inv_cancel₀ h2pi, one_pow, one_smul]
    -- (b-outer) the outer slice is continuous on the closed disk, holomorphic on the open disk
    have hcons : Differentiable ℂ (fun x : ℂ ↦ (Fin.cons x w' : Fin (m + 1) → ℂ)) := by
      refine differentiable_pi.mpr fun i ↦ ?_
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp
      · simp
    have hmaps : ∀ x ∈ Metric.closedBall (c 0) (R 0),
        (Fin.cons x w' : Fin (m + 1) → ℂ) ∈ Set.univ.pi fun i ↦ Metric.closedBall (c i) (R i) := by
      intro x hx i _
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa using hx
      · have := hw j.succ
        simp only [hw']
        exact Metric.ball_subset_closedBall this
    have hgcont : ContinuousOn (fun x ↦ f (Fin.cons x w')) (Metric.closedBall (c 0) (R 0)) :=
      hf.continuousOn.comp hcons.continuous.continuousOn hmaps
    have hgdiff : ∀ x ∈ Metric.ball (c 0) (R 0),
        DifferentiableAt ℂ (fun x ↦ f (Fin.cons x w')) x := by
      intro x hx
      have hmem : (Fin.cons x w' : Fin (m + 1) → ℂ)
          ∈ Set.univ.pi fun i ↦ Metric.ball (c i) (R i) := by
        intro i _
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simpa using hx
        · simpa [hw'] using hw j.succ
      have hnhds : Set.univ.pi (fun i ↦ Metric.closedBall (c i) (R i))
          ∈ nhds (Fin.cons x w' : Fin (m + 1) → ℂ) :=
        Filter.mem_of_superset
          ((isOpen_set_pi Set.finite_univ (fun i _ ↦ Metric.isOpen_ball)).mem_nhds hmem)
          (Set.pi_mono fun i _ ↦ Metric.ball_subset_closedBall)
      exact (hf.differentiableAt hnhds).comp x hcons.differentiableAt
    -- (e) assemble: torusIntegral_succ → kernel split → pull constant → hinner
    --     → 1-var Cauchy on the outer slice → Fin.cons_self_tail → power arithmetic
    have hval : (∯ ζ in T(c, R), (∏ i, (ζ i - w i)⁻¹) • f ζ)
        = (2 * ↑Real.pi * Complex.I) ^ (m + 1) • f w := by
      rw [torusIntegral_succ hint]
      have hEq : Set.EqOn
          (fun x : ℂ ↦ ∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ),
              (∏ i, ((Fin.cons x y : Fin (m + 1) → ℂ) i - w i)⁻¹) • f (Fin.cons x y))
          (fun x ↦ (x - w 0)⁻¹ • ((2 * ↑Real.pi * Complex.I) ^ m • f (Fin.cons x w')))
          (Metric.sphere (c 0) (R 0)) := by
        intro x hx
        dsimp only
        simp only [hker, mul_smul]
        rw [torusIntegral_smul, hinner x (Metric.sphere_subset_closedBall hx)]
      rw [circleIntegral.integral_congr (le_of_lt (hR 0)) hEq,
        show (fun x : ℂ ↦ (x - w 0)⁻¹ • ((2 * ↑Real.pi * Complex.I) ^ m • f (Fin.cons x w')))
            = (fun x ↦ (2 * ↑Real.pi * Complex.I) ^ m • ((x - w 0)⁻¹ • f (Fin.cons x w')))
          from funext fun x ↦ smul_comm _ _ _,
        circleIntegral.integral_smul]
      have hcauchy :=
        two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
          (s := (∅ : Set ℂ)) Set.countable_empty (hw 0) hgcont (fun x hx ↦ hgdiff x hx.1)
      have hcw : (Fin.cons (w 0) w' : Fin (m + 1) → ℂ) = w := by
        rw [hw']; exact Fin.cons_self_tail w
      rw [hcw] at hcauchy
      have hJ : (∮ x in C(c 0, R 0), (x - w 0)⁻¹ • f (Fin.cons x w'))
          = (2 * ↑Real.pi * Complex.I) • f w := by
        rw [← hcauchy, smul_smul, mul_inv_cancel₀ h2pi, one_smul]
      rw [hJ, smul_smul, ← pow_succ]
    rw [hval, smul_smul, ← mul_pow, inv_mul_cancel₀ h2pi, one_pow, one_smul]

/-- A continuous function satisfying the Cauchy representation on a polydisc is analytic. -/
theorem analyticAt_of_cauchyRepr {m : ℕ} {g : (Fin m → ℂ) → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hcont : ContinuousOn g (Set.univ.pi fun _ : Fin m ↦ Metric.closedBall (0 : ℂ) ρ))
    (hrepr : ∀ y : Fin m → ℂ, (∀ i, ‖y i‖ < ρ) →
      (2 * ↑Real.pi * Complex.I)⁻¹ ^ m •
        (∯ ζ in T((0 : Fin m → ℂ), fun _ ↦ ρ), (∏ i, (ζ i - y i)⁻¹) * g ζ) = g y) :
    AnalyticAt ℂ g 0 := by
  set P : MvPowerSeries (Fin m) ℂ := fun d ↦
    (2 * ↑Real.pi * Complex.I)⁻¹ ^ m •
      ∯ ζ in T((0 : Fin m → ℂ), fun _ ↦ ρ),
        (∏ i, (ζ i ^ (d i + 1))⁻¹) • g ζ with hP
  have hRep : MvPowerSeries.Represents P g := by
    have hnhds : ∀ᶠ y in 𝓝 (0 : Fin m → ℂ), ∀ i, ‖y i‖ < ρ := by
      rw [Filter.eventually_all]
      intro i
      exact (isOpen_lt (continuous_apply i).norm continuous_const).mem_nhds (by simpa using hρ)
    filter_upwards [hnhds] with y hy
    have hnorm : ∀ (θ : Fin m → ℝ) (i),
        ‖torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ i‖ = ρ := by
      intro θ i
      simp only [torusMap, Pi.zero_apply, zero_add, norm_mul,
        Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hρ.le]
    have hne : ∀ (θ : Fin m → ℝ) (i),
        torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) θ i ≠ 0 := by
      intro θ i hz
      have h := hnorm θ i
      rw [hz, norm_zero] at h
      exact (ne_of_lt hρ) h
    have hpt : ∀ θ : Fin m → ℝ,
        HasSum (fun d : Fin m →₀ ℕ ↦
            ((∏ i, (torusMap (0:Fin m→ℂ) (fun _ ↦ ρ) θ i ^ (d i + 1))⁻¹) *
                ∏ i, (y i) ^ (d i)) * g (torusMap (0:Fin m→ℂ) (fun _ ↦ ρ) θ))
          ((∏ i, (torusMap (0:Fin m→ℂ) (fun _ ↦ ρ) θ i - y i)⁻¹) *
              g (torusMap (0:Fin m→ℂ) (fun _ ↦ ρ) θ)) := by
      intro θ
      exact (hasSum_cauchyKernel (torusMap (0:Fin m→ℂ) (fun _ ↦ ρ) θ) y
        (fun i => hne θ i) (fun i => by rw [hnorm]; exact hy i)).mul_right _
    have hB1 := hasSum_torusIntegral
      (F := fun d ζ => ((∏ i, (ζ i ^ (d i + 1))⁻¹) * ∏ i, (y i) ^ (d i)) * g ζ)
      (S := fun ζ => (∏ i, (ζ i - y i)⁻¹) * g ζ)
      (fun d => torusIntegrable_cauchyTerm hρ hcont y d)
      (summable_integral_norm_cauchyTerm hρ hy) hpt
    rw [← hrepr y hy]
    have hfun_eq : (fun d : Fin m →₀ ℕ ↦ (2 * ↑Real.pi * Complex.I)⁻¹ ^ m •
        (∯ ζ in T((0:Fin m→ℂ), fun _ ↦ ρ),
          ((∏ i, (ζ i ^ (d i + 1))⁻¹) * ∏ i, (y i) ^ (d i)) * g ζ)) = P.term y := by
      funext d
      rw [MvPowerSeries.term, MvPowerSeries.coeff_apply, hP,
        MvPowerSeries.evalMonomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
        show (fun ζ : Fin m → ℂ =>
              ((∏ i, (ζ i ^ (d i + 1))⁻¹) * ∏ i, (y i) ^ (d i)) * g ζ)
            = (fun ζ => (∏ i, (y i) ^ (d i)) * ((∏ i, (ζ i ^ (d i + 1))⁻¹) * g ζ)) from by
          funext ζ; ring,
        torusIntegral_const_mul]
      simp only [smul_eq_mul]
      ring
    rw [← hfun_eq]
    exact hB1.const_smul ((2 * ↑Real.pi * Complex.I)⁻¹ ^ m)
  exact analyticAt_of_represents hRep.locallyConvergent hRep

open MeasureTheory in
/-- Fubini: a torus integral and a circle integral of a jointly continuous function commute. -/
theorem torusIntegral_circleIntegral_swap {m : ℕ} (c : Fin m → ℂ) (R : Fin m → ℝ)
    (ε : ℝ) (H : (Fin m → ℂ) → ℂ → ℂ)
    (hH : Continuous fun p : (Fin m → ℝ) × ℝ ↦
      H (torusMap c R p.1) (circleMap 0 ε p.2)) :
    (∯ ξ in T(c, R), ∮ ζ in C(0, ε), H ξ ζ)
      = ∮ ζ in C(0, ε), ∯ ξ in T(c, R), H ξ ζ := by
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  set A : (Fin m → ℝ) → ℝ → ℂ := fun φ θ ↦
      (∏ i, (R i : ℂ) * Complex.exp (φ i * Complex.I) * Complex.I) *
        (circleMap 0 ε θ * Complex.I * H (torusMap c R φ) (circleMap 0 ε θ)) with hA
  have hcontA : Continuous (Function.uncurry A) := by
    have h1 : Continuous fun p : (Fin m → ℝ) × ℝ ↦
        (∏ i, (R i : ℂ) * Complex.exp (p.1 i * Complex.I) * Complex.I) := by
      apply continuous_finsetProd
      intro i _
      fun_prop
    have h2 : Continuous fun p : (Fin m → ℝ) × ℝ ↦ circleMap 0 ε p.2 * Complex.I := by
      unfold circleMap; fun_prop
    rw [hA]
    change Continuous fun p : (Fin m → ℝ) × ℝ ↦
      (∏ i, (R i : ℂ) * Complex.exp (p.1 i * Complex.I) * Complex.I) *
        (circleMap 0 ε p.2 * Complex.I * H (torusMap c R p.1) (circleMap 0 ε p.2))
    exact h1.mul (h2.mul hH)
  have hint : Integrable (Function.uncurry A)
      ((volume.restrict (Set.Icc (0 : Fin m → ℝ) fun _ ↦ 2 * Real.pi)).prod
        (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    refine IntegrableOn.mono_set ?_
      (Set.prod_mono (subset_refl _) Set.Ioc_subset_Icc_self)
    exact hcontA.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  simp only [torusIntegral, circleIntegral, deriv_circleMap,
    intervalIntegral.integral_of_le h2pi, smul_eq_mul]
  have hL : ∀ φ : Fin m → ℝ,
      (∏ i, (R i : ℂ) * Complex.exp (φ i * Complex.I) * Complex.I) *
          (∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi),
            circleMap 0 ε θ * Complex.I * H (torusMap c R φ) (circleMap 0 ε θ))
        = ∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi), A φ θ := by
    intro φ
    rw [← integral_const_mul]
  have hR : ∀ θ : ℝ,
      circleMap 0 ε θ * Complex.I *
          (∫ φ in Set.Icc (0 : Fin m → ℝ) (fun _ ↦ 2 * Real.pi),
            (∏ i, (R i : ℂ) * Complex.exp (φ i * Complex.I) * Complex.I) *
              H (torusMap c R φ) (circleMap 0 ε θ))
        = ∫ φ in Set.Icc (0 : Fin m → ℝ) (fun _ ↦ 2 * Real.pi), A φ θ := by
    intro θ
    rw [← integral_const_mul]
    congr 1
    funext φ
    rw [hA]
    ring
  simp_rw [hL, hR]
  exact integral_integral_swap hint

open MeasureTheory in
/-- A circle integral depending continuously on a parameter is continuous in the parameter. -/
theorem continuousOn_circleIntegral {m : ℕ} {ε : ℝ} {s : Set (Fin m → ℂ)}
    {G : (Fin m → ℂ) → ℂ → ℂ}
    (hG : Continuous fun p : s × ℝ ↦ G (p.1 : Fin m → ℂ) (circleMap 0 ε p.2)) :
    ContinuousOn (fun x ↦ ∮ ζ in C(0, ε), G x ζ) s := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous fun x : s ↦ ∫ θ in (0:ℝ)..(2 * Real.pi),
      deriv (circleMap 0 ε) θ • G (x : Fin m → ℂ) (circleMap 0 ε θ)
  have hJ : Continuous fun p : (s × ℝ) ↦ deriv (circleMap 0 ε) p.2 := by
    simp only [deriv_circleMap]
    unfold circleMap
    fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (x : s) (θ : ℝ) ↦ deriv (circleMap 0 ε) θ • G (x : Fin m → ℂ) (circleMap 0 ε θ))
    (hJ.smul hG) 0 (2 * Real.pi)

open MeasureTheory in
/-- A circle integral of a family that is holomorphic in the parameter is analytic. -/
theorem analyticAt_circleIntegral {m : ℕ} {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ)
    {G : (Fin m → ℂ) → ℂ → ℂ}
    (hdiff : ∀ ζ : ℂ, ‖ζ‖ = ε → DifferentiableOn ℂ (fun x ↦ G x ζ)
      (Set.univ.pi fun _ : Fin m ↦ Metric.closedBall (0 : ℂ) ρ))
    (hcont : Continuous fun p : (Set.univ.pi fun _ : Fin m ↦ Metric.closedBall (0 : ℂ) ρ) × ℝ ↦
      G (p.1 : Fin m → ℂ) (circleMap 0 ε p.2)) :
    AnalyticAt ℂ (fun x ↦ ∮ ζ in C(0, ε), G x ζ) 0 := by
  have htm : Continuous fun φ : Fin m → ℝ ↦ torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) φ := by
    unfold torusMap; fun_prop
  have hnorm : ∀ (φ : Fin m → ℝ) (i), ‖torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) φ i‖ = ρ := by
    intro φ i
    simp [torusMap, Complex.norm_exp_ofReal_mul_I, abs_of_pos hρ]
  have hmem : ∀ φ : Fin m → ℝ,
      torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) φ ∈
        (Set.univ.pi fun _ : Fin m ↦ Metric.closedBall (0 : ℂ) ρ) := by
    intro φ
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    simp only [Metric.mem_closedBall, Complex.dist_eq, sub_zero, hnorm, le_refl]
  have hGtc : Continuous fun p : (Fin m → ℝ) × ℝ ↦
      G (torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) p.1) (circleMap 0 ε p.2) :=
    hcont.comp (((htm.comp continuous_fst).subtype_mk fun p ↦ hmem p.1).prodMk continuous_snd)
  refine analyticAt_of_cauchyRepr hρ (continuousOn_circleIntegral hcont) ?_
  intro y hy
  have hyne : ∀ (φ : Fin m → ℝ) (i), torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) φ i - y i ≠ 0 := by
    intro φ i h
    have h1 : ‖y i‖ < ρ := hy i
    rw [sub_eq_zero] at h
    rw [← h, hnorm] at h1
    exact lt_irrefl _ h1
  have hHcont : Continuous fun p : (Fin m → ℝ) × ℝ ↦
      (∏ i, (torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) p.1 i - y i)⁻¹) *
        G (torusMap (0 : Fin m → ℂ) (fun _ ↦ ρ) p.1) (circleMap 0 ε p.2) := by
    refine Continuous.mul ?_ hGtc
    apply continuous_finsetProd
    intro i _
    exact (((continuous_apply i).comp (htm.comp continuous_fst)).sub continuous_const).inv₀
      (fun p ↦ hyne p.1 i)
  have hfib : ∀ ζ : ℂ, ‖ζ‖ = ε →
      G y ζ = (2 * ↑Real.pi * Complex.I)⁻¹ ^ m •
        ∯ ξ in T((0 : Fin m → ℂ), fun _ ↦ ρ), (∏ i, (ξ i - y i)⁻¹) • G ξ ζ := by
    intro ζ hζ
    refine cauchy_torus_formula (fun x ↦ G x ζ) 0 (fun _ ↦ ρ) (fun _ ↦ hρ) (hdiff ζ hζ) y
      (fun i ↦ ?_)
    simp only [Metric.mem_ball, Pi.zero_apply, dist_zero_right]
    exact hy i
  have h1 : (∮ ζ in C(0, ε), G y ζ)
      = ∮ ζ in C(0, ε), (2 * ↑Real.pi * Complex.I)⁻¹ ^ m •
          ∯ ξ in T((0 : Fin m → ℂ), fun _ ↦ ρ), (∏ i, (ξ i - y i)⁻¹) • G ξ ζ := by
    refine circleIntegral.integral_congr hε.le ?_
    intro ζ hζ
    exact hfib ζ (mem_sphere_zero_iff_norm.mp hζ)
  rw [h1, circleIntegral.integral_smul]
  congr 1
  simp only [smul_eq_mul]
  rw [← torusIntegral_circleIntegral_swap (0 : Fin m → ℂ) (fun _ ↦ ρ) ε
    (fun ξ ζ ↦ (∏ i, (ξ i - y i)⁻¹) * G ξ ζ) hHcont]
  simp_rw [circleIntegral.integral_const_mul]

/-- The affine map `x ↦ Fin.snoc (Fin.init x) ζ` is differentiable. -/
lemma differentiable_snocInit {m : ℕ} (ζ : ℂ) :
    Differentiable ℂ (fun x : Fin (m + 1) → ℂ ↦ (Fin.snoc (Fin.init x) ζ : Fin (m + 1) → ℂ)) := by
  refine differentiable_pi.mpr fun j ↦ ?_
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp only [Fin.snoc_last]
    exact differentiable_const ζ
  · simp only [Fin.snoc_castSucc, Fin.init_def]
    exact differentiable_apply (𝕜 := ℂ) i.castSucc

/-- A norm bound for `Fin.snoc (Fin.init x) ζ`. -/
lemma norm_snocInit_le {m : ℕ} {x : Fin (m + 1) → ℂ} {ζ : ℂ} {a : ℝ}
    (hx : ∀ i : Fin m, ‖x i.castSucc‖ ≤ a) (hζ : ‖ζ‖ ≤ a) :
    ‖(Fin.snoc (Fin.init x) ζ : Fin (m + 1) → ℂ)‖ ≤ a := by
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg ζ).trans hζ)).mpr fun j ↦ ?_
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simpa only [Fin.snoc_last] using hζ
  · simpa only [Fin.snoc_castSucc, Fin.init_def] using hx i

/-- Joint continuity of `(x, θ) ↦ Fin.snoc (Fin.init x) (circleMap 0 ε θ)`. -/
lemma continuous_snocInit_circleMap {m : ℕ} (ε : ℝ) (s : Set (Fin (m + 1) → ℂ)) :
    Continuous fun p : s × ℝ ↦
      (Fin.snoc (Fin.init (p.1 : Fin (m + 1) → ℂ)) (circleMap 0 ε p.2) :
        Fin (m + 1) → ℂ) := by
  refine continuous_pi fun j ↦ ?_
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp only [Fin.snoc_last]
    unfold circleMap
    fun_prop
  · simp only [Fin.snoc_castSucc, Fin.init_def]
    exact (continuous_apply i.castSucc).comp (continuous_subtype_val.comp continuous_fst)

/-- The affine map `w ↦ Fin.snoc w ζ` is differentiable. -/
lemma differentiable_snoc {m : ℕ} (ζ : ℂ) :
    Differentiable ℂ (fun w : Fin m → ℂ ↦ (Fin.snoc w ζ : Fin (m + 1) → ℂ)) := by
  refine differentiable_pi.mpr fun j ↦ ?_
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp only [Fin.snoc_last]
    exact differentiable_const ζ
  · simp only [Fin.snoc_castSucc]
    exact differentiable_apply (𝕜 := ℂ) i

/-- A norm bound for `Fin.snoc w ζ`. -/
lemma norm_snoc_le {m : ℕ} {w : Fin m → ℂ} {ζ : ℂ} {a : ℝ}
    (hw : ∀ i, ‖w i‖ ≤ a) (hζ : ‖ζ‖ ≤ a) :
    ‖(Fin.snoc w ζ : Fin (m + 1) → ℂ)‖ ≤ a := by
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg ζ).trans hζ)).mpr fun j ↦ ?_
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simpa only [Fin.snoc_last] using hζ
  · simpa only [Fin.snoc_castSucc] using hw i

/-- Joint continuity of `(w, θ) ↦ Fin.snoc w (circleMap 0 ε θ)`. -/
lemma continuous_snoc_circleMap {m : ℕ} (ε : ℝ) (s : Set (Fin m → ℂ)) :
    Continuous fun p : s × ℝ ↦
      (Fin.snoc (p.1 : Fin m → ℂ) (circleMap 0 ε p.2) : Fin (m + 1) → ℂ) := by
  refine continuous_pi fun j ↦ ?_
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp only [Fin.snoc_last]
    unfold circleMap
    fun_prop
  · simp only [Fin.snoc_castSucc]
    exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)

/-- The affine map `s ↦ Fin.snoc w s` (varying the last coordinate) is differentiable. -/
lemma differentiable_snoc_last {m : ℕ} (w : Fin m → ℂ) :
    Differentiable ℂ (fun s : ℂ ↦ (Fin.snoc w s : Fin (m + 1) → ℂ)) := by
  refine differentiable_pi.mpr fun j ↦ ?_
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp only [Fin.snoc_last]
    exact differentiable_id
  · simp only [Fin.snoc_castSucc]
    exact differentiable_const _

open MeasureTheory in
/-- Analyticity of a circle integral of `F/G · E` along the last coordinate. -/
theorem analyticAt_circleIntegral_snoc {m : ℕ} {ε ρ r : ℝ}
    (hε : 0 < ε) (hρ : 0 < ρ) (hρε : ρ < ε) (hεr : ε < r)
    {F G : (Fin (m + 1) → ℂ) → ℂ}
    (hF : ∀ z : Fin (m + 1) → ℂ, ‖z‖ < r → AnalyticAt ℂ F z)
    (hG : ∀ z : Fin (m + 1) → ℂ, ‖z‖ < r → AnalyticAt ℂ G z)
    (hG0 : ∀ w : Fin m → ℂ, (∀ i, ‖w i‖ ≤ ρ) → ∀ ζ : ℂ, ‖ζ‖ = ε →
      G (Fin.snoc w ζ) ≠ 0)
    {E : (Fin m → ℂ) → ℂ → ℂ}
    (hEdiff : ∀ ζ : ℂ, ‖ζ‖ = ε → DifferentiableOn ℂ (fun w ↦ E w ζ)
      (Set.univ.pi fun _ : Fin m ↦ Metric.closedBall (0 : ℂ) ρ))
    (hEcont : Continuous fun p : (Set.univ.pi fun _ : Fin m ↦ Metric.closedBall (0 : ℂ) ρ) × ℝ ↦
      E (p.1 : Fin m → ℂ) (circleMap 0 ε p.2)) :
    AnalyticAt ℂ (fun w : Fin m → ℂ ↦
      ∮ ζ in C(0, ε), F (Fin.snoc w ζ) / G (Fin.snoc w ζ) * E w ζ) 0 := by
  have hcirc : ∀ θ : ℝ, ‖circleMap 0 ε θ‖ = ε := by
    intro θ; simp [norm_circleMap_zero, abs_of_pos hε]
  refine analyticAt_circleIntegral hε hρ ?_ ?_
  · intro ζ hζ w hw
    have hwi : ∀ i, ‖w i‖ ≤ ρ := by
      intro i
      have h := hw i (Set.mem_univ i)
      rwa [Metric.mem_closedBall, dist_zero_right] at h
    have hz : ‖(Fin.snoc w ζ : Fin (m + 1) → ℂ)‖ < r :=
      lt_of_le_of_lt (norm_snoc_le (fun i ↦ le_trans (hwi i) hρε.le) (le_of_eq hζ)) hεr
    have hsn : DifferentiableAt ℂ
        (fun v : Fin m → ℂ ↦ (Fin.snoc v ζ : Fin (m + 1) → ℂ)) w := (differentiable_snoc ζ) w
    have hFd : DifferentiableAt ℂ (fun v : Fin m → ℂ ↦ F (Fin.snoc v ζ)) w := by
      have h := (hF _ hz).differentiableAt.comp w hsn
      simpa [Function.comp_def] using h
    have hGd : DifferentiableAt ℂ (fun v : Fin m → ℂ ↦ G (Fin.snoc v ζ)) w := by
      have h := (hG _ hz).differentiableAt.comp w hsn
      simpa [Function.comp_def] using h
    have hGinv : DifferentiableAt ℂ (fun v : Fin m → ℂ ↦ (G (Fin.snoc v ζ))⁻¹) w :=
      hGd.inv (hG0 w hwi ζ hζ)
    have hquot : DifferentiableAt ℂ
        (fun v : Fin m → ℂ ↦ F (Fin.snoc v ζ) / G (Fin.snoc v ζ)) w := by
      simp_rw [div_eq_mul_inv]
      exact hFd.mul hGinv
    exact hquot.differentiableWithinAt.mul ((hEdiff ζ hζ) w hw)
  · have hΦ := continuous_snoc_circleMap (m := m) ε
      (Set.univ.pi fun _ : Fin m ↦ Metric.closedBall (0 : ℂ) ρ)
    have hznorm : ∀ p : (Set.univ.pi fun _ : Fin m ↦ Metric.closedBall (0 : ℂ) ρ) × ℝ,
        ‖(Fin.snoc (p.1 : Fin m → ℂ) (circleMap 0 ε p.2) : Fin (m + 1) → ℂ)‖ < r := by
      intro p
      refine lt_of_le_of_lt (norm_snoc_le (fun i ↦ ?_) (le_of_eq (hcirc p.2))) hεr
      have h := p.1.2 i (Set.mem_univ _)
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact le_trans h hρε.le
    have hFc : Continuous fun p : (Set.univ.pi fun _ : Fin m ↦
        Metric.closedBall (0 : ℂ) ρ) × ℝ ↦
        F (Fin.snoc (p.1 : Fin m → ℂ) (circleMap 0 ε p.2)) := by
      rw [continuous_iff_continuousAt]
      intro p
      have h : ContinuousAt (F ∘ fun p' : (Set.univ.pi fun _ : Fin m ↦
          Metric.closedBall (0 : ℂ) ρ) × ℝ ↦
            (Fin.snoc (p'.1 : Fin m → ℂ) (circleMap 0 ε p'.2) : Fin (m + 1) → ℂ)) p :=
        ContinuousAt.comp (hF _ (hznorm p)).continuousAt hΦ.continuousAt
      simpa [Function.comp_def] using h
    have hGc : Continuous fun p : (Set.univ.pi fun _ : Fin m ↦
        Metric.closedBall (0 : ℂ) ρ) × ℝ ↦
        G (Fin.snoc (p.1 : Fin m → ℂ) (circleMap 0 ε p.2)) := by
      rw [continuous_iff_continuousAt]
      intro p
      have h : ContinuousAt (G ∘ fun p' : (Set.univ.pi fun _ : Fin m ↦
          Metric.closedBall (0 : ℂ) ρ) × ℝ ↦
            (Fin.snoc (p'.1 : Fin m → ℂ) (circleMap 0 ε p'.2) : Fin (m + 1) → ℂ)) p :=
        ContinuousAt.comp (hG _ (hznorm p)).continuousAt hΦ.continuousAt
      simpa [Function.comp_def] using h
    refine (hFc.div hGc (fun p ↦ ?_)).mul hEcont
    refine hG0 (p.1 : Fin m → ℂ) (fun i ↦ ?_) (circleMap 0 ε p.2) (hcirc p.2)
    have h := p.1.2 i (Set.mem_univ _)
    rwa [Metric.mem_closedBall, dist_zero_right] at h

theorem analyticAt_of_differentiableOn {m : ℕ} {f : (Fin m → ℂ) → ℂ}
    {s : Set (Fin m → ℂ)} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s)
    {x₀ : Fin m → ℂ} (hx₀ : x₀ ∈ s) : AnalyticAt ℂ f x₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs x₀ hx₀
  have hρ : (0 : ℝ) < ε / 2 := by linarith
  have hsub : Metric.closedBall x₀ (ε / 2) ⊆ s :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  refine analyticAt_of_shift ?_
  set g : (Fin m → ℂ) → ℂ := fun y ↦ f (x₀ + y) with hg
  -- (plumbing) g is differentiable on the 0-centred closed polydisc
  have hgdiff : DifferentiableOn ℂ g
      (Set.univ.pi fun _ : Fin m ↦ Metric.closedBall (0 : ℂ) (ε / 2)) := by
    have hT : Differentiable ℂ (fun y : Fin m → ℂ ↦ x₀ + y) := by fun_prop
    refine hf.comp hT.differentiableOn ?_
    intro y hy
    apply hsub
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left,
      pi_norm_le_iff_of_nonneg hρ.le]
    intro i
    have hyi := hy i (Set.mem_univ i)
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hyi
  -- (core) the Cauchy coefficient power series
  set P : MvPowerSeries (Fin m) ℂ := fun d ↦
    (2 * ↑Real.pi * Complex.I)⁻¹ ^ m •
      ∯ ζ in T((0 : Fin m → ℂ), fun _ ↦ ε / 2),
        (∏ i, (ζ i ^ (d i + 1))⁻¹) • g ζ with hP
  -- (core 1) coefficients decay geometrically ⇒ locally convergent
  -- (core) geometric expansion + term-by-term integration ⇒ P represents g
  have hRep : MvPowerSeries.Represents P g := by
    have hnhds : ∀ᶠ y in 𝓝 (0 : Fin m → ℂ), ∀ i, ‖y i‖ < ε / 2 := by
      rw [Filter.eventually_all]
      intro i
      exact (isOpen_lt (continuous_apply i).norm continuous_const).mem_nhds (by simpa using hρ)
    filter_upwards [hnhds] with y hy
    have hnorm : ∀ (θ : Fin m → ℝ) (i),
        ‖torusMap (0 : Fin m → ℂ) (fun _ ↦ ε / 2) θ i‖ = ε / 2 := by
      intro θ i
      simp only [torusMap, Pi.zero_apply, zero_add, norm_mul,
        Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hρ.le]
    have hne : ∀ (θ : Fin m → ℝ) (i),
        torusMap (0 : Fin m → ℂ) (fun _ ↦ ε / 2) θ i ≠ 0 := by
      intro θ i hz
      have h := hnorm θ i
      rw [hz, norm_zero] at h
      exact (ne_of_lt hρ) h
    have hpt : ∀ θ : Fin m → ℝ,
        HasSum (fun d : Fin m →₀ ℕ ↦
            ((∏ i, (torusMap (0:Fin m→ℂ) (fun _ ↦ ε/2) θ i ^ (d i + 1))⁻¹) *
                ∏ i, (y i) ^ (d i)) * g (torusMap (0:Fin m→ℂ) (fun _ ↦ ε/2) θ))
          ((∏ i, (torusMap (0:Fin m→ℂ) (fun _ ↦ ε/2) θ i - y i)⁻¹) *
              g (torusMap (0:Fin m→ℂ) (fun _ ↦ ε/2) θ)) := by
      intro θ
      exact (hasSum_cauchyKernel (torusMap (0:Fin m→ℂ) (fun _ ↦ ε/2) θ) y
        (fun i => hne θ i) (fun i => by rw [hnorm]; exact hy i)).mul_right _
    have hB1 := hasSum_torusIntegral
      (F := fun d ζ => ((∏ i, (ζ i ^ (d i + 1))⁻¹) * ∏ i, (y i) ^ (d i)) * g ζ)
      (S := fun ζ => (∏ i, (ζ i - y i)⁻¹) * g ζ)
      (fun d => torusIntegrable_cauchyTerm hρ hgdiff.continuousOn y d)
      (summable_integral_norm_cauchyTerm hρ hy) hpt
    have hw : ∀ i, y i ∈ Metric.ball (0:ℂ) (ε/2) := by
      intro i; rw [Metric.mem_ball, dist_zero_right]; exact hy i
    have hVE : (2 * ↑Real.pi * Complex.I)⁻¹ ^ m •
        (∯ ζ in T((0:Fin m→ℂ), fun _ ↦ ε/2), (∏ i, (ζ i - y i)⁻¹) * g ζ) = g y := by
      rw [cauchy_torus_formula g (0:Fin m→ℂ) (fun _ ↦ ε/2) (fun _ => hρ) hgdiff y hw]
      simp only [smul_eq_mul]
    rw [← hVE]
    have hfun_eq : (fun d : Fin m →₀ ℕ ↦ (2 * ↑Real.pi * Complex.I)⁻¹ ^ m •
        (∯ ζ in T((0:Fin m→ℂ), fun _ ↦ ε/2),
          ((∏ i, (ζ i ^ (d i + 1))⁻¹) * ∏ i, (y i) ^ (d i)) * g ζ)) = P.term y := by
      funext d
      rw [MvPowerSeries.term, MvPowerSeries.coeff_apply, hP,
        MvPowerSeries.evalMonomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
        show (fun ζ : Fin m → ℂ =>
              ((∏ i, (ζ i ^ (d i + 1))⁻¹) * ∏ i, (y i) ^ (d i)) * g ζ)
            = (fun ζ => (∏ i, (y i) ^ (d i)) * ((∏ i, (ζ i ^ (d i + 1))⁻¹) * g ζ)) from by
          funext ζ; ring,
        torusIntegral_const_mul]
      simp only [smul_eq_mul]
      ring
    rw [← hfun_eq]
    exact hB1.const_smul ((2 * ↑Real.pi * Complex.I)⁻¹ ^ m)
  exact analyticAt_of_represents hRep.locallyConvergent hRep
  -- (core 2) geometric expansion + term-by-term integration ⇒ P represents g

end
