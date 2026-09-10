/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.TraceResidue
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The meromorphic trace `Tr_F α` and the residue-trace compatibility (Miranda §VIII.3, b + c)

This file builds **pillars (b) and (c)** of the trace-to-`ℙ¹` route to the residue theorem
(Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3, "An Algebraic Proof of the Residue
Theorem").  With pillar (a) — the `ℂℙ¹` residue theorem `LaurentForm.…_eq_zero` in
`Jacobians.TraceResidue` — and the cover `F = MeromorphicFunction.toRiemannSphere` (in
`Jacobians.ToSphereGeneral`), they assemble into

> `∑_{p ∈ X} Res_p α = ∑_{q ∈ ℂℙ¹} Res_q (Tr_F α) = 0`.

## Design — the `resAt` (local coordinate) level

A meromorphic `1`-form on `X` is, in any chart, `(coefficient) · dz` with the coefficient
meromorphic; its residue at a point `x` is `resAt (coeff) (chart x)`
(`Jacobians.Dolbeault.resAt`, the `(2πi)⁻¹∮` contour residue).  The deep manifold-bundle trace
already exists for *holomorphic* forms (`Jacobians.TraceForm.traceForm`, the fibre-sum pushforward
with its removable-singularity branch extension); what is genuinely new — and what Lemma 3.2 is
about — is the *residue interaction*, which is a one-variable **coordinate** statement.  So we work
at the `resAt`/coefficient level, where the whole §VIII.3 argument lives, and where it connects
directly to `LaurentForm` for the combine.

The genuine content of Lemma 3.2 is the **residue change-of-variables** under a single
(unramified) sheet `s` of the cover: pushing a `1`-form `g·dw` forward along `w = φ(z)` (with `φ`
a local biholomorphism, `φ'(a) ≠ 0`) gives `g(φ z)·φ'(z)·dz`, whose residue at the source point
equals the residue of `g·dw` at the image point.  The trace over a fibre is the sum over the sheets,
so its residue is the fibre sum of the per-point residues — Lemma 3.2.

## What is proved here (all complete)

* **`resAt_inv_sub_mul`** — Cauchy's integral formula as a residue: `Res_a (h(z)/(z − a)) = h(a)`
  for `h` analytic at `a` (the workhorse simple-pole residue with analytic numerator).
* **`resAt_simplePole_pushforward`** — the **simple-pole residue change-of-variables** (the heart of
  Lemma 3.2, *fully proved*): for `φ` analytic at `a` with `φ'(a) ≠ 0` and `φ a = b`, the
  pushforward `z ↦ c·(φ z − b)⁻¹ · φ'(z)` of the simple pole `c·(w − b)⁻¹` has `resAt = c` at `a`.
  This is exactly the case the `df/f` route to `deg_div` needs (`df/f` has only simple poles).
* **`resAt_logDeriv_eq_order`** — the order link `Res_a(df/f) = ord_a f` (`= n` when
  `meromorphicOrderAt f a = n`), the per-point input of the `deg_div` route.  *Fully proved*: the
  factorization `f = (z−a)^n·g`, `g a ≠ 0`, gives `logDeriv f = n/(z−a) + logDeriv g` with
  `logDeriv g` analytic.
* **`FibreTrace` / `FibreTrace.traceCoeff`** — the coordinate model of the meromorphic trace
  `Tr_F α` over a finite (off-branch) fibre: the finite sum of the per-sheet pushforwards
  `∑ i, coeff i (sheet i w)·(sheet i)'(w)`.
* **Lemma 3.2 (`FibreTrace.resAt_traceCoeff`)** — `Res_b (Tr_F α) = ∑_{sheets} Res_{pre i} (coeff i)`,
  the residue-trace compatibility, from per-sheet change of variables + `resAt_finsum` (additivity).
  Its **simple-pole specialization** `FibreTrace.resAt_traceCoeff_of_simplePole` is *unconditional*
  (no analytic atom), built on the proved `resAt_simplePole_pushforward`.
* **The combine (`finiteResidueSum_trace_eq_zero`, `…_of_fibres`, `…_of_simplePole_fibres`)** —
  packaging `Tr_F α` as a `LaurentForm` and applying pillar (a); the simple-pole form is fully
  hypothesis-free up to the manifold bookkeeping `hL32` (that `L` *is* the trace).

## The one isolated analytic atom

The fully-general (higher-order-pole) residue change-of-variables `resAt (g ∘ φ · φ') a =
resAt g (φ a)` is a contour-substitution / deformation statement that Mathlib lacks at this pin
(no winding-number-invariance of `circleIntegral` along a biholomorphism).  It is isolated as the
named Prop `ResidueChangeOfVariables` and is **not** needed for the `df/f` route (only simple poles
there) — that route uses only the *proved* `resAt_simplePole_pushforward`.  See the report.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces*, §17 (`Res`); §4.22–4.25 (sheets, local normal form).
-/

open Complex Metric Filter Topology
open scoped Real

namespace Jacobians.MeromorphicTrace

open Jacobians.Dolbeault Jacobians.TraceResidue

/-! ### Cauchy's integral formula as a residue

The single workhorse: a simple pole `h(z)/(z − a)` with **analytic numerator** `h` has residue
`h a`.  This is Cauchy's integral formula `(2πi)⁻¹ ∮_{|z−a|=r} h(z)/(z − a) = h(a)` read through
`resAt`.  Everything in this file funnels through it. -/

/-- **Cauchy's integral formula, residue form.**  For `h` analytic at `a`, the residue of the
simple pole `z ↦ (z − a)⁻¹ · h z` at `a` is `h a`. -/
theorem resAt_inv_sub_mul {h : ℂ → ℂ} {a : ℂ} (hh : AnalyticAt ℂ h a) :
    resAt (fun z => (z - a)⁻¹ * h z) a = h a := by
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ z ∈ ball a ρ, DifferentiableAt ℂ h z := by
    have hev := hh.eventually_analyticAt
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hb⟩ := hev
    exact ⟨ε, hε, fun z hz => (hb (mem_ball.mp hz)).differentiableAt⟩
  set r := ρ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrρ : r < ρ := by rw [hr]; exact half_lt_self hρ
  have hpunct : ∀ z ∈ ball a ρ \ {a}, DifferentiableAt ℂ (fun z => (z - a)⁻¹ * h z) z := by
    intro z hz
    have hzne : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hz.2)
    exact (((differentiableAt_id).sub_const a).inv hzne).mul (hball z hz.1)
  rw [resAt_eq_smul_circleIntegral hpunct hr0 hrρ]
  have hcont : ContinuousOn h (closedBall a r) := fun z hz =>
    (hball z (lt_of_le_of_lt (mem_closedBall.mp hz) hrρ)).continuousAt.continuousWithinAt
  have hdiff : ∀ z ∈ ball a r \ (∅ : Set ℂ), DifferentiableAt ℂ h z := fun z hz =>
    hball z (lt_trans (mem_ball.mp hz.1) hrρ)
  have hcauchy := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (R := r) (c := a) (w := a) (f := h) (s := ∅) Set.countable_empty (mem_ball_self hr0) hcont hdiff
  rw [show (fun z => (z - a)⁻¹ * h z) = (fun z => (z - a)⁻¹ • h z) by funext z; rw [smul_eq_mul]]
  exact hcauchy

/-- Variant with the numerator on the left: `Res_a (h(z) · (z − a)⁻¹) = h a`. -/
theorem resAt_mul_inv_sub {h : ℂ → ℂ} {a : ℂ} (hh : AnalyticAt ℂ h a) :
    resAt (fun z => h z * (z - a)⁻¹) a = h a := by
  rw [show (fun z => h z * (z - a)⁻¹) = (fun z => (z - a)⁻¹ * h z) by funext z; ring]
  exact resAt_inv_sub_mul hh

/-! ### Analytic factorization at a simple zero of a biholomorphism

If `φ` is analytic at `a` with `φ'(a) ≠ 0` (a local biholomorphism) and `φ a = b`, then `φ − b`
has a *simple* zero at `a`: `φ z − b = (z − a) · g z` near `a`, with `g` analytic and
`g a = φ'(a) ≠ 0`.  This is the change-of-coordinate fact underlying Lemma 3.2: the cover, read in
charts at an unramified preimage, is exactly such a `φ`. -/

/-- **Simple-zero factorization of a local biholomorphism.**  For `φ` analytic at `a` with
`φ'(a) ≠ 0` and `φ a = b`, there is an analytic `g` (nonzero at `a`, with `g a = φ'(a)`) such that
`φ z − b = (z − a) · g z` for `z` near `a`.  The first-order Taylor expansion with analytic
remainder; `g` is the "analytic slope" of `φ` at `a`. -/
theorem exists_simpleZero_factorization {φ : ℂ → ℂ} {a b : ℂ} (hφ : AnalyticAt ℂ φ a)
    (hφ' : deriv φ a ≠ 0) (hab : φ a = b) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ g a = deriv φ a ∧
      (∀ᶠ z in 𝓝 a, φ z - b = (z - a) * g z) := by
  have hsub : AnalyticAt ℂ (fun z => φ z - b) a := hφ.sub analyticAt_const
  have hne0 : ¬ ∀ᶠ z in 𝓝 a, (fun z => φ z - b) z = 0 := by
    intro hcon
    have hd : deriv φ a = deriv (fun _ : ℂ => b) a := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hcon] with z hz; rw [sub_eq_zero] at hz; exact hz
    rw [deriv_const] at hd; exact hφ' hd
  obtain ⟨e, g, hg, hg0, hfact⟩ := (hsub.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hne0
  have he0 : e ≠ 0 := by
    rintro rfl
    have h := hfact.self_of_nhds
    simp only [pow_zero, one_smul, hab, sub_self] at h
    exact hg0 h.symm
  -- Pin `e = 1` and `g a = φ'(a)` from the first derivative of the factorization.
  have hφeq : φ =ᶠ[𝓝 a] fun z => b + (z - a) ^ e * g z := by
    filter_upwards [hfact] with z hz; simp only [smul_eq_mul] at hz; rw [← hz]; ring
  have hgdiff : DifferentiableAt ℂ g a := hg.differentiableAt
  have hpow_deriv : HasDerivAt (fun z : ℂ => (z - a) ^ e * g z)
      (((e : ℂ) * (a - a) ^ (e - 1)) * g a + (a - a) ^ e * deriv g a) a := by
    have h1 : HasDerivAt (fun z : ℂ => (z - a) ^ e) ((e : ℂ) * (a - a) ^ (e - 1)) a := by
      have hb : HasDerivAt (fun z : ℂ => z - a) 1 a := by simpa using (hasDerivAt_id a).sub_const a
      simpa using hb.pow e
    simpa using h1.mul hgdiff.hasDerivAt
  have hderiv_eq : deriv φ a = ((e : ℂ) * (a - a) ^ (e - 1)) * g a + (a - a) ^ e * deriv g a :=
    ((hpow_deriv.const_add b).congr_of_eventuallyEq hφeq).deriv
  rw [sub_self] at hderiv_eq
  have he1 : e = 1 := by
    by_contra hne
    have h1 : (0 : ℂ) ^ (e - 1) = 0 := zero_pow (by omega)
    have h2 : (0 : ℂ) ^ e = 0 := zero_pow he0
    rw [h1, h2] at hderiv_eq; simp at hderiv_eq; exact hφ' hderiv_eq
  subst he1
  have hga : g a = deriv φ a := by
    simp only [Nat.cast_one, one_mul, Nat.sub_self, pow_zero, mul_one, pow_one, zero_mul,
      add_zero] at hderiv_eq
    exact hderiv_eq.symm
  refine ⟨g, hg, hga, ?_⟩
  filter_upwards [hfact] with z hz; simpa [pow_one] using hz

/-! ### The simple-pole residue change of variables — the heart of Lemma 3.2

For a single (unramified) sheet, pushing the simple pole `c·(w − b)⁻¹` of a `1`-form forward along
the local biholomorphism `w = φ(z)` (`b = φ a`) gives `z ↦ c·(φ z − b)⁻¹·φ'(z)`, whose residue at
the source point `a` is again `c`.  *Fully proved*: by the simple-zero factorization the pushforward
equals `(z − a)⁻¹ · H z` with `H` analytic, `H a = c` (the `φ'` numerator and the slope `g` cancel),
so Cauchy (`resAt_inv_sub_mul`) gives residue `H a = c`.

This is exactly the residue-preservation the `df/f` route to `deg_div` needs: `df/f` has only simple
poles, with residue the integer order, and unramified preimages give such `φ`. -/

/-- **Simple-pole residue change of variables (Lemma 3.2, one unramified sheet).**  For `φ` analytic
at `a` with `φ'(a) ≠ 0` and `φ a = b`, the pushforward `z ↦ c·(φ z − b)⁻¹·φ'(z)` of the simple pole
`c·(w − b)⁻¹` has `resAt = c` at `a` — the residue is preserved across the change of variables. -/
theorem resAt_simplePole_pushforward {φ : ℂ → ℂ} {a b c : ℂ} (hφ : AnalyticAt ℂ φ a)
    (hφ' : deriv φ a ≠ 0) (hab : φ a = b) :
    resAt (fun z => c * (φ z - b)⁻¹ * deriv φ z) a = c := by
  obtain ⟨g, hg, hga, hfact⟩ := exists_simpleZero_factorization hφ hφ' hab
  set H : ℂ → ℂ := fun z => c * deriv φ z / g z with hH
  have hg0 : g a ≠ 0 := hga ▸ hφ'
  have hHana : AnalyticAt ℂ H a := (analyticAt_const.mul hφ.deriv).div hg hg0
  have hHa : H a = c := by simp only [hH]; rw [hga]; field_simp
  rw [resAt_congr (g := fun z => (z - a)⁻¹ * H z) ?_, resAt_inv_sub_mul hHana, hHa]
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hfact,
    mem_nhdsWithin_of_mem_nhds (hg.continuousAt.eventually_ne hg0)] with z hz_ne hzfact hzg
  have hzane : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hz_ne)
  show c * (φ z - b)⁻¹ * deriv φ z = (z - a)⁻¹ * H z
  rw [hzfact, hH]
  field_simp

/-! ### The logarithmic-derivative residue — the `df/f` route to `deg_div`

For the divisor route to the residue theorem, the relevant `1`-form is `α = df/f` (the logarithmic
differential), whose residue at a point is the **order** of `f` there:

> `Res_a (df/f) = ord_a f`.

This is the local argument principle: if `f` has order `n` at `a`, then `f z = (z − a)^n · g z` with
`g a ≠ 0` (`meromorphicOrderAt_eq_int_iff`), so `logDeriv f = n/(z − a) + logDeriv g` near `a`, and
`logDeriv g` is analytic at `a` (`g a ≠ 0`), contributing no residue.  Hence `Res_a (df/f) = n`.
The poles of `df/f` are all *simple* (residue `= n`), which is why the *proved* simple-pole change of
variables (`resAt_simplePole_pushforward`) is all this route needs.  Fully proved. -/

/-- `logDeriv g = deriv g / g` is **analytic at `a`** when `g` is analytic at `a` and `g a ≠ 0`. -/
theorem analyticAt_logDeriv {g : ℂ → ℂ} {a : ℂ} (hg : AnalyticAt ℂ g a) (hg0 : g a ≠ 0) :
    AnalyticAt ℂ (logDeriv g) a := by
  have heq : logDeriv g = fun z => deriv g z / g z := by funext z; rw [logDeriv]; rfl
  rw [heq]; exact hg.deriv.div hg hg0

/-- **The logarithmic-derivative residue (local argument principle).**  For `f` meromorphic at `a`
with order `n` (`meromorphicOrderAt f a = n`), the residue of the logarithmic derivative `df/f` at
`a` is `n`:

> `Res_a (logDeriv f) = n`.

This is exactly `Res_a(df/f) = ord_a f`, the per-point fact the `deg_div` route uses: summed over
`X`, `∑ Res = ∑ ord = #zeros − #poles`, and the residue theorem (the combine above, via `Tr_F`)
forces it to `0`. -/
theorem resAt_logDeriv_eq_order {f : ℂ → ℂ} {a : ℂ} {n : ℤ} (hf : MeromorphicAt f a)
    (hord : meromorphicOrderAt f a = (n : ℤ)) :
    resAt (logDeriv f) a = (n : ℂ) := by
  obtain ⟨g, hg, hg0, hfact⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hord
  -- Propagate the punctured factorization to a full eventual eq at each off-center point.
  have hprop : ∀ᶠ z in 𝓝[≠] a, f =ᶠ[𝓝 z] fun w => (w - a) ^ n • g w := by
    have heq' : ∀ᶠ z in 𝓝[≠] a, f z = (z - a) ^ n • g z := hfact
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at heq'
    obtain ⟨ε, hε, hball⟩ := heq'
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Metric.ball_mem_nhds a hε] with z hz hz_ne
    have hopen : IsOpen (ball a ε \ {a}) := Metric.isOpen_ball.sdiff isClosed_singleton
    have hzmem : z ∈ ball a ε \ {a} := ⟨hz, by simpa using hz_ne⟩
    filter_upwards [hopen.mem_nhds hzmem] with w hw
    exact hball hw.1 (by simpa using hw.2)
  have hgdiff_ev : ∀ᶠ z in 𝓝 a, DifferentiableAt ℂ g z := by
    filter_upwards [hg.eventually_analyticAt] with z hz using hz.differentiableAt
  have hg_ne_ev : ∀ᶠ z in 𝓝 a, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  -- `logDeriv f = n/(z − a) + logDeriv g` on the punctured neighborhood.
  have hlog_eq : logDeriv f =ᶠ[𝓝[≠] a] fun z => (n : ℂ) / (z - a) + logDeriv g z := by
    filter_upwards [hprop, self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hgdiff_ev,
      mem_nhdsWithin_of_mem_nhds hg_ne_ev] with z hzprop hz_ne hzgd hzg0
    have hzne : z ≠ a := by simpa using hz_ne
    have hcongr : logDeriv f z = logDeriv (fun w => (w - a) ^ n • g w) z := by
      simp only [logDeriv, Pi.div_apply, hzprop.deriv_eq, hzprop.eq_of_nhds]
    rw [hcongr]
    simp only [smul_eq_mul]
    have hbase_ne : z - a ≠ 0 := sub_ne_zero.mpr hzne
    have hsub_diff : DifferentiableAt ℂ (fun w : ℂ => w - a) z := differentiableAt_id.sub_const a
    have hpow_ne : (fun w : ℂ => (w - a) ^ n) z ≠ 0 := by simpa using zpow_ne_zero n hbase_ne
    have hpow_diff : DifferentiableAt ℂ (fun w : ℂ => (w - a) ^ n) z :=
      hsub_diff.zpow (Or.inl hbase_ne)
    rw [logDeriv_mul z hpow_ne hzg0 hpow_diff hzgd]
    congr 1
    rw [logDeriv_fun_zpow hsub_diff n]
    have hld : logDeriv (fun w => w - a) z = 1 / (z - a) := by
      have h1 : HasDerivAt (fun w => w - a) 1 z := by simpa using (hasDerivAt_id z).sub_const a
      simp only [logDeriv, Pi.div_apply, h1.deriv]
    rw [hld]; field_simp
  rw [resAt_congr hlog_eq]
  -- `Res_a (n/(z − a) + logDeriv g) = n + 0`.
  have heq : (fun z => (n : ℂ) / (z - a) + logDeriv g z) = (fun z => (n : ℂ) * (z - a)⁻¹) + logDeriv g := by
    funext z; simp only [Pi.add_apply]; rw [div_eq_mul_inv]
  rw [heq]
  have hmono : MeromorphicAt (fun z => (n : ℂ) * (z - a)⁻¹) a :=
    (MeromorphicAt.const (n : ℂ) a).mul ((analyticAt_id.sub analyticAt_const).meromorphicAt.inv)
  rw [resAt_add hmono.holoPunctured (analyticAt_logDeriv hg hg0).meromorphicAt.holoPunctured,
    resAt_const_mul_sub_inv (n : ℂ) a, resAt_eq_zero_of_analyticAt (analyticAt_logDeriv hg hg0),
    add_zero]

/-! ### The general residue change of variables, as a named atom

The fully-general (any-order-pole) residue change of variables `resAt (g ∘ s · s') b = resAt g a`
for `s` a local biholomorphism (`s b = a`, `s'(b) ≠ 0`) and `g` *any* meromorphic function at `a`
is a contour-substitution / homotopy-invariance statement Mathlib lacks at this pin (there is no
winding-number-invariance of `circleIntegral` along a biholomorphism).  We isolate it as a named
`Prop` so the general Lemma 3.2 can be stated and assembled; the **simple-pole** instance below is
*proved* (`resAt_changeOfVariables_of_simplePole`) and is all the `df/f`/`deg_div` route requires.

`s` is the **section** (the local inverse of the cover read in charts): `w ↦ z`.  The pushforward of
the `1`-form `g·dz` is `(g ∘ s)·s'·dw`. -/

/-- **The residue change-of-variables atom.**  For every local biholomorphism `s` at `b`
(`deriv s b ≠ 0`) and every function `g` meromorphic at `s b`, the pushforward `1`-form
`w ↦ g (s w) · s'(w)` has the same residue at `b` as `g·dz` has at `s b`.  *Isolated* as a `Prop`;
not needed for the simple-pole (`df/f`) route. -/
def ResidueChangeOfVariables : Prop :=
  ∀ (s g : ℂ → ℂ) (b : ℂ), AnalyticAt ℂ s b → deriv s b ≠ 0 → MeromorphicAt g (s b) →
    resAt (fun w => g (s w) * deriv s w) b = resAt g (s b)

/-! ### The fibre trace and Lemma 3.2

A **fibre** of the cover over a base point with target-chart coordinate `b` is a finite family of
sheets; sheet `i` has a holomorphic local section `sheet i` (`sheet i b = pre i`, `(sheet i)'(b) ≠
0`) and carries the form coefficient `coeff i` (meromorphic at the preimage coordinate `pre i`).
The **trace coefficient** at the base is the finite sum of the per-sheet pushforwards
`w ↦ ∑ i, coeff i (sheet i w) · (sheet i)'(w)`. -/

/-- A finite fibre of an (unramified) cover over a base point of target-chart coordinate `b`, with
the per-sheet holomorphic sections and meromorphic form coefficients.  The data of Miranda's local
picture for the trace `Tr_F` over `b` (off the branch locus). -/
structure FibreTrace where
  /-- Index of the sheets meeting the fibre. -/
  ι : Type
  /-- Finiteness of the sheet index. -/
  fintype_ι : Fintype ι
  /-- The base-point coordinate in the target chart. -/
  b : ℂ
  /-- The local holomorphic section of sheet `i` (target coord `↦` source coord). -/
  sheet : ι → ℂ → ℂ
  /-- The source-chart coordinate of the `i`-th preimage, `= sheet i b`. -/
  pre : ι → ℂ
  /-- Each section is analytic at the base. -/
  sheet_analytic : ∀ i, AnalyticAt ℂ (sheet i) b
  /-- Each section is a local biholomorphism (nonzero derivative). -/
  sheet_deriv_ne : ∀ i, deriv (sheet i) b ≠ 0
  /-- The section hits the `i`-th preimage at the base. -/
  sheet_base : ∀ i, sheet i b = pre i
  /-- The form coefficient on sheet `i`, meromorphic at the preimage coordinate. -/
  coeff : ι → ℂ → ℂ
  /-- Meromorphy of each sheet's form coefficient. -/
  coeff_mero : ∀ i, MeromorphicAt (coeff i) (pre i)

namespace FibreTrace

attribute [instance] FibreTrace.fintype_ι

variable (T : FibreTrace)

/-- The **trace coefficient** at the base: the finite sum of the per-sheet pushforwards
`coeff i (sheet i w) · (sheet i)'(w)`.  This is `Tr_F α` read in the target chart, over the fibre. -/
noncomputable def traceCoeff : ℂ → ℂ :=
  fun w => ∑ i, T.coeff i (T.sheet i w) * deriv (T.sheet i) w

/-- Each per-sheet summand of the trace coefficient is meromorphic at the base (composition of the
meromorphic form coefficient with the analytic section, times the analytic section derivative). -/
theorem meromorphicAt_summand (i : T.ι) :
    MeromorphicAt (fun w => T.coeff i (T.sheet i w) * deriv (T.sheet i) w) T.b := by
  have hcomp : MeromorphicAt (T.coeff i ∘ T.sheet i) T.b :=
    MeromorphicAt.comp_analyticAt (g := T.sheet i) (f := T.coeff i)
      (by rw [T.sheet_base i]; exact T.coeff_mero i) (T.sheet_analytic i)
  exact hcomp.mul (T.sheet_analytic i).deriv.meromorphicAt

/-- **Lemma 3.2 (residue-trace compatibility).**  Given the residue change-of-variables atom, the
residue of the trace coefficient at the base equals the fibre sum of the residues of the per-sheet
form coefficients at the preimages:

> `Res_b (Tr_F α) = ∑_{sheets i} Res_{pre i} (coeff i)`.

The trace coefficient is a finite sum, so its residue is the sum of the per-summand residues
(`resAt_finsum`); each summand's residue equals the corresponding preimage residue by the change of
variables (`hCoV`). -/
theorem resAt_traceCoeff (hCoV : ResidueChangeOfVariables) :
    resAt T.traceCoeff T.b = ∑ i, resAt (T.coeff i) (T.pre i) := by
  rw [show T.traceCoeff = fun w => ∑ i, T.coeff i (T.sheet i w) * deriv (T.sheet i) w from rfl,
    LaurentForm.resAt_finsum Finset.univ
    (fun i w => T.coeff i (T.sheet i w) * deriv (T.sheet i) w)
    (fun i _ => T.meromorphicAt_summand i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have := hCoV (T.sheet i) (T.coeff i) T.b (T.sheet_analytic i) (T.sheet_deriv_ne i)
    (by rw [T.sheet_base i]; exact T.coeff_mero i)
  rw [T.sheet_base i] at this
  exact this

/-- **Lemma 3.2 for simple-pole coefficients (fully proved, no hypothesis).**  When each sheet's
form coefficient is a *simple* pole `coeff i = c i·(w − pre i)⁻¹` — the case of the logarithmic
differential `df/f` and hence the `deg_div` route — the residue-trace compatibility holds
*unconditionally* (the general change-of-variables atom `ResidueChangeOfVariables` is **not** needed;
the proved `resAt_simplePole_pushforward` supplies each sheet):

> `Res_b (Tr_F α) = ∑_{sheets i} Res_{pre i} (coeff i) = ∑_i c i`. -/
theorem resAt_traceCoeff_of_simplePole (c : T.ι → ℂ)
    (hcoeff : ∀ i, T.coeff i = fun w => c i * (w - T.pre i)⁻¹) :
    resAt T.traceCoeff T.b = ∑ i, resAt (T.coeff i) (T.pre i) := by
  rw [show T.traceCoeff = fun w => ∑ i, T.coeff i (T.sheet i w) * deriv (T.sheet i) w from rfl,
    LaurentForm.resAt_finsum Finset.univ
      (fun i w => T.coeff i (T.sheet i w) * deriv (T.sheet i) w)
      (fun i _ => T.meromorphicAt_summand i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hLHS : resAt (fun w => T.coeff i (T.sheet i w) * deriv (T.sheet i) w) T.b = c i := by
    rw [show (fun w => T.coeff i (T.sheet i w) * deriv (T.sheet i) w)
        = (fun w => c i * (T.sheet i w - T.pre i)⁻¹ * deriv (T.sheet i) w) from by
      funext w; rw [hcoeff i]]
    exact resAt_simplePole_pushforward (T.sheet_analytic i) (T.sheet_deriv_ne i) (T.sheet_base i)
  rw [hLHS, hcoeff i, resAt_const_mul_sub_inv]

end FibreTrace

/-! ### The simple-pole instance of the change of variables (fully proved)

For the `df/f` route to `deg_div`, every form coefficient is `df/f`, which has only **simple poles**,
with residue the integer order.  The simple-pole change of variables `resAt_simplePole_pushforward`
is proved above; here we re-express it in the section (`s = φ⁻¹`) form used by `FibreTrace`, so the
fibre Lemma 3.2 holds *unconditionally* for simple-pole coefficients.

The section form follows from the forward form by reading the inverse: if `s` is the section
(`s b = a`, `s'(b) ≠ 0`) and the coefficient is the simple pole `g w = c·(w − a)⁻¹`, then
`g (s w)·s'(w) = c·(s w − a)⁻¹·s'(w)`, and since `s` is itself a local biholomorphism with
`s b = a`, this is exactly the shape `resAt_simplePole_pushforward` evaluates (with `φ := s`,
`b := a`), giving residue `c = resAt g a` (`resAt_const_mul_sub_inv`). -/

/-- **Simple-pole change of variables, section form (fully proved).**  For a section `s` (local
biholomorphism, `s b = a`) and a simple-pole coefficient `g w = c·(w − a)⁻¹`, the pushforward
`w ↦ g (s w)·s'(w)` has residue `c = resAt g a` at `b`.  This is the unconditional instance of
`ResidueChangeOfVariables` for simple poles — all the `df/f`/`deg_div` route needs. -/
theorem resAt_changeOfVariables_of_simplePole {s : ℂ → ℂ} {a b c : ℂ}
    (hs : AnalyticAt ℂ s b) (hs' : deriv s b ≠ 0) (hsb : s b = a) :
    resAt (fun w => (c * (s w - a)⁻¹) * deriv s w) b = resAt (fun w => c * (w - a)⁻¹) a := by
  rw [resAt_const_mul_sub_inv]
  exact resAt_simplePole_pushforward hs hs' hsb

/-! ### The combine — pillar (a) ∘ Lemma 3.2 = the residue theorem on `X`

The final step of Miranda §VIII.3.  The trace `Tr_F α` is a rational `1`-form on `ℂℙ¹`, so (away
from `∞`) it is in partial-fraction form — a `LaurentForm L` whose coefficient `L.R` is the trace
coefficient.  Pillar (a) gives `L.finiteResidueSum + Res_∞ L.R = 0`.  By Lemma 3.2 each finite
residue `resAt L.R p = Res_p (Tr_F α)` equals the fibre sum `∑_{x ∈ F⁻¹ p} Res_x α`; summing over
the (finitely many) centers regroups `L.finiteResidueSum` as the total residue of `α` over all
finite-fibre points of `X`.  Hence

> `(∑_{finite fibres} ∑_{x ∈ fibre} Res_x α) + Res_∞ (Tr_F α) = 0`,

which is `∑_{x ∈ X} Res_x α = 0` once the `∞`-fibre residues are folded into `Res_∞` (the standard
inversion-symmetric bookkeeping; geometrically the residue theorem on `X`). -/

/-- **The combine (Miranda §VIII.3, conclusion).**  Let `L : LaurentForm` represent `Tr_F α` on
`ℂℙ¹` (so `L.R` is the trace coefficient), and suppose each center `p` of `L` carries a fibre
residue datum `fibreRes p` equal — by Lemma 3.2 — to the local residue `resAt L.R p` (the fibre sum
`∑_{x ∈ F⁻¹ p} Res_x α`).  Then the total fibre-residue sum over the centers, plus the residue at
infinity of the trace, vanishes:

> `(∑_{centers p} fibreRes p) + Res_∞ (Tr_F α) = 0`.

This is the residue theorem on `X`, with the finite residues regrouped by fibre via Lemma 3.2 and
the `∞`-residue carried by `Res_∞ L.R`.  Pure assembly: `finiteResidueSum` is by definition
`∑_{centers} resAt L.R p`, each term replaced by `fibreRes p` via `hfibre`, then pillar (a). -/
theorem finiteResidueSum_trace_eq_zero (L : LaurentForm) (fibreRes : ℂ → ℂ)
    (hfibre : ∀ p ∈ (Finset.univ.image L.a), fibreRes p = resAt L.R p) :
    (∑ p ∈ Finset.univ.image L.a, fibreRes p) + resAtInfty L.R L.ρ = 0 := by
  have hsum : (∑ p ∈ Finset.univ.image L.a, fibreRes p) = L.finiteResidueSum := by
    rw [LaurentForm.finiteResidueSum]
    exact Finset.sum_congr rfl hfibre
  rw [hsum]
  exact L.finiteResidueSum_add_resAtInfty_eq_zero

/-- **The combine, fibre-trace form.**  Specialization of `finiteResidueSum_trace_eq_zero` in which
each center's fibre residue is presented as the `FibreTrace.resAt_traceCoeff` fibre sum, tied to the
`LaurentForm` residue by Lemma 3.2 + the identification of the trace coefficient with `L.R` at each
center.  The hypothesis `hL32` is exactly "Lemma 3.2 holds at every center, and there `L.R` is the
trace coefficient" — both supplied by the manifold assembly of `Tr_F` over the finite cover.

> `(∑_{centers p} (fibre p).resAt_traceCoeff-value) + Res_∞ (Tr_F α) = 0`. -/
theorem finiteResidueSum_trace_eq_zero_of_fibres (L : LaurentForm)
    (fibre : ℂ → FibreTrace) (hCoV : ResidueChangeOfVariables)
    (hL32 : ∀ p ∈ (Finset.univ.image L.a),
      (∑ i, resAt ((fibre p).coeff i) ((fibre p).pre i)) = resAt L.R p) :
    (∑ p ∈ Finset.univ.image L.a, resAt (fibre p).traceCoeff (fibre p).b)
      + resAtInfty L.R L.ρ = 0 := by
  refine finiteResidueSum_trace_eq_zero L (fun p => resAt (fibre p).traceCoeff (fibre p).b) ?_
  intro p hp
  show resAt (fibre p).traceCoeff (fibre p).b = resAt L.R p
  rw [(fibre p).resAt_traceCoeff hCoV]
  exact hL32 p hp

/-- **The combine, simple-pole fibre-trace form (fully proved, no analytic atom).**  The
`df/f`/`deg_div` specialization of `finiteResidueSum_trace_eq_zero_of_fibres`: each fibre's
coefficients are simple poles (`hsp p`), so Lemma 3.2 holds *unconditionally*
(`resAt_traceCoeff_of_simplePole`) — no `ResidueChangeOfVariables` hypothesis.  Given only the
identification `hL32` of each center's fibre-residue sum with `L.R`'s residue (the manifold
bookkeeping that `L` *is* the trace), the total fibre-residue sum plus `Res_∞` vanishes:

> `(∑_{centers p} Res_b (Tr_F α over fibre p)) + Res_∞ (Tr_F α) = 0`. -/
theorem finiteResidueSum_trace_eq_zero_of_simplePole_fibres (L : LaurentForm)
    (fibre : ℂ → FibreTrace) (cs : (p : ℂ) → (fibre p).ι → ℂ)
    (hsp : ∀ p, ∀ i, (fibre p).coeff i = fun w => cs p i * (w - (fibre p).pre i)⁻¹)
    (hL32 : ∀ p ∈ (Finset.univ.image L.a),
      (∑ i, resAt ((fibre p).coeff i) ((fibre p).pre i)) = resAt L.R p) :
    (∑ p ∈ Finset.univ.image L.a, resAt (fibre p).traceCoeff (fibre p).b)
      + resAtInfty L.R L.ρ = 0 := by
  refine finiteResidueSum_trace_eq_zero L (fun p => resAt (fibre p).traceCoeff (fibre p).b) ?_
  intro p hp
  show resAt (fibre p).traceCoeff (fibre p).b = resAt L.R p
  rw [(fibre p).resAt_traceCoeff_of_simplePole (cs p) (hsp p)]
  exact hL32 p hp

end Jacobians.MeromorphicTrace
