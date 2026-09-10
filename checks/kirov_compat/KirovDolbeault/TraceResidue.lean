/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.Residue

/-!
# The residue theorem on `ℂℙ¹` (the trace-to-`ℙ¹` route, Miranda §VIII.3, pillar 2)

This file builds the **second pillar** of the general 1-form residue theorem `∑_a Res_a α = 0`
for a meromorphic 1-form `α` on a compact Riemann surface, via the trace-to-`ℙ¹` route
(Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3, "An Algebraic Proof of the Residue
Theorem"):

> `∑_{p ∈ X} Res_p α = ∑_{q ∈ ℂℙ¹} Res_q (Tr_F α) = 0`,

where `F : X → ℂℙ¹` is a nonconstant holomorphic map (its existence is Riemann–Roch, supplied by
the Serre context), `Tr_F` is the trace (pushforward) of the meromorphic 1-form, and the final
equality is the **residue theorem on `ℂℙ¹`** — proved here, elementarily, from the residue calculus
already built in `Jacobians.Dolbeault.Residue` (`resAt`).

## What is in this file (pillar 2 — the `ℂℙ¹` residue theorem)

The residue theorem on `ℂℙ¹` for a rational 1-form is, in its sharpest elementary form, *partial
fractions*: every rational 1-form `η = R(z) dz` decomposes (away from `∞`) into a finite sum of
Laurent monomials `c·(z − a)^n dz`, and

  `(∑ of the finite residues of η) + Res_∞ η = 0`,

because the only Laurent term with a nonzero residue is the `n = −1` term `c·(z − a)⁻¹`, whose residue
`c` at `a` is exactly cancelled by its residue `−c` at `∞`.  We make this precise via:

* `LaurentForm` — a finite family `(c i)·(z − a i) ^ (n i)` of Laurent monomials, with `R` its
  pointwise sum (the rational coefficient of `dz`), all centres lying inside a fixed disk `ball 0 ρ`.
* `LaurentForm.largeCircleIntegral_eq` — the **multi-pole Cauchy residue theorem** for this explicit
  partial-fraction form: `∮_{|z|=ρ} R = 2πi · ∑_{i : n i = −1} c i` (all centres inside the contour).
  Each `n ≠ −1` monomial integrates to `0` (`circleIntegral.integral_sub_zpow_of_ne`); each `n = −1`
  monomial integrates to `2πi` (`circleIntegral.integral_sub_inv_of_mem_ball`).
* `LaurentForm.resAt_center_eq` — the local residue at a centre `a j`, read by the repo's `resAt`, is
  the sum `∑_{i : a i = a j, n i = −1} c i` of the simple-pole coefficients sitting at that centre.
* `resAtInfty` — the **residue at infinity** of a 1-form coefficient `R`, `Res_∞ := −(2πi)⁻¹ ∮ R`,
  read on a contour enclosing all the (finite) poles.  By construction `Res_∞` is exactly the negative
  of the total finite residue mass, so:
* `LaurentForm.finiteResidueSum_add_resAtInfty_eq_zero` — **the `ℂℙ¹` residue theorem**:
  `(∑_{centres} Res) + Res_∞ R = 0`.

Everything here is complete and depends on no unproved lemma; it reuses only the
one-variable residue calculus of `Residue.lean` and Mathlib's `circleIntegral` toolbox.

## What is deliberately NOT here (the trace combine — Miranda Lemma 3.2)

The remaining two steps of the §VIII.3 route are **not** built here, because the repo's trace
machinery (`Jacobians.TraceForm` / `Jacobians.TracePullback`, the S8 layer) pushes forward only
*holomorphic* 1-forms (`HolomorphicOneForms`), via an off-branch fibre sum plus a removable-
singularity branch extension.  It has **no meromorphic pushforward** and **no residue/order
interaction**.  The missing pieces are therefore:

  1. the **meromorphic trace** `Tr_F (ω₀·f)` of a meromorphic 1-form through the branched cover `F`
     (tracking the pole structure), and
  2. **Miranda Lemma 3.2** — `Res_y (Tr_F α) = ∑_{x ∈ F⁻¹(y)} Res_x α` (the residue of the pushforward
     at `y` is the fibre sum of the residues of `α`).

Both are genuinely new builds (the holomorphic trace gives no foothold for poles), so they are left
to the trace-formalism work; the present file supplies the elementary `ℂℙ¹` end of the argument that
they feed into.  See the report accompanying this commit for the exact remaining goal.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the algebraic proof of the residue
  theorem; the trace `Tr`, Lemma 3.2, and partial fractions on `ℂℙ¹`).
* Forster, *Lectures on Riemann Surfaces*, §17 (`Res`, the residue functional on `H¹(X, Ω)`).
-/

open Complex Metric Filter Topology
open scoped Real

namespace Jacobians.TraceResidue

open Jacobians.Dolbeault

/-! ### A single Laurent monomial: its circle integral and its residue

The atom of partial fractions is `c · (z − a) ^ n` (`n : ℤ`).  Its circle integral over `C(c₀, ρ)`
is `0` unless `n = −1`, in which case (when `a` lies inside the contour) it is `c · 2πi`
(`circleIntegral.integral_sub_zpow_of_ne` / `integral_sub_inv_of_mem_ball`).  Its `resAt` residue at
its own centre `a` is `c` if `n = −1` and `0` otherwise. -/

/-- The circle integral of a single Laurent monomial `c·(z − a)^n` over `C(c₀, ρ)` with the centre
`a` inside the contour: `0` unless `n = −1`, where it is `c · 2πi`. -/
theorem circleIntegral_laurentMonomial {c a c₀ : ℂ} {ρ : ℝ} {n : ℤ} (ha : a ∈ ball c₀ ρ) :
    (∮ z in C(c₀, ρ), c * (z - a) ^ n) = if n = -1 then c * (2 * π * I) else 0 := by
  rw [circleIntegral.integral_const_mul]
  by_cases hn : n = -1
  · subst hn
    rw [if_pos rfl, show ((-1 : ℤ)) = (-1 : ℤ) from rfl]
    rw [show (fun z : ℂ => (z - a) ^ (-1 : ℤ)) = (fun z : ℂ => (z - a)⁻¹) by
      funext z; rw [zpow_neg_one]]
    rw [circleIntegral.integral_sub_inv_of_mem_ball ha]
  · rw [if_neg hn, circleIntegral.integral_sub_zpow_of_ne hn c₀ a ρ, mul_zero]

/-- The `resAt` residue of a single Laurent monomial `c·(z − a)^n` at its own centre `a`: `c` if
`n = −1`, and `0` otherwise (a holomorphic / primitive-having power has no residue). -/
theorem resAt_laurentMonomial (c a : ℂ) (n : ℤ) :
    resAt (fun z => c * (z - a) ^ n) a = if n = -1 then c else 0 := by
  by_cases hn : n = -1
  · subst hn
    rw [if_pos rfl]
    have : (fun z : ℂ => c * (z - a) ^ (-1 : ℤ)) = (fun z : ℂ => c * (z - a)⁻¹) := by
      funext z; rw [zpow_neg_one]
    rw [this, resAt_const_mul_sub_inv]
  · rw [if_neg hn]
    -- `(z - a)^n`, `n ≠ -1`, has a global primitive `(z-a)^(n+1)/(n+1)` off `a` (and is analytic
    -- if `n ≥ 0`); either way every small circle integral vanishes, so the residue is `0`.
    refine resAt_eq_of_eventuallyEq_circleIntegral (K := 0) ?_ |>.trans (by rw [smul_zero])
    filter_upwards [self_mem_nhdsWithin] with r _
    rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_zpow_of_ne hn a a r,
      mul_zero]

/-- **`Res = 0` for an analytic integrand.** If `f : ℂ → ℂ` is `AnalyticAt` `c`, its residue there is
`0` (it is differentiable on a small ball, so every small circle integral vanishes). -/
theorem resAt_eq_zero_of_analyticAt {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticAt ℂ f c) :
    resAt f c = 0 := by
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ z ∈ ball c ρ, DifferentiableAt ℂ f z := by
    have hev := hf.eventually_analyticAt
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hball⟩ := hev
    exact ⟨ε, hε, fun z hz => (hball (mem_ball.mp hz)).differentiableAt⟩
  exact resAt_eq_zero_of_differentiableOn_ball hρ hball

/-- `resAt 0 c = 0` (the zero function is analytic everywhere). -/
theorem resAt_zero (c : ℂ) : resAt (fun _ => (0 : ℂ)) c = 0 :=
  resAt_eq_zero_of_analyticAt analyticAt_const

/-! ### The residue at infinity of a `1`-form coefficient

For a rational coefficient `R : ℂ → ℂ` of `dz`, the **residue at infinity** is
`Res_∞ R := −(2πi)⁻¹ ∮_{|z|=ρ} R` for any contour `C(0, ρ)` enclosing all the finite poles
(the value is independent of such `ρ`; the standard convention, e.g. Miranda §VIII.3).  The minus
sign encodes the inversion `z ↦ 1/w` Jacobian and is exactly what makes the sum of *all* residues
(finite + `∞`) vanish. -/

/-- The **residue at infinity** of the `dz`-coefficient `R`, computed on the contour `C(0, ρ)`:
`Res_∞ R = −(2πi)⁻¹ ∮_{|z|=ρ} R`. -/
noncomputable def resAtInfty (R : ℂ → ℂ) (ρ : ℝ) : ℂ :=
  -(2 * π * I : ℂ)⁻¹ • ∮ z in C((0 : ℂ), ρ), R z

/-! ### A partial-fraction (Laurent) `1`-form on `ℂℙ¹`

A `LaurentForm` packages a rational `1`-form `R dz` as an explicit finite sum of Laurent monomials
`c i · (z − a i) ^ (n i)`, all of whose centres `a i` lie inside a fixed disk `ball 0 ρ` (so a single
contour `C(0, ρ)` encloses every finite pole).  Its coefficient `R` is the pointwise sum. -/

/-- A rational `1`-form on `ℂℙ¹` in partial-fraction (Laurent) form: a finite family of monomials
`c i·(z − a i) ^ (n i)` with all centres inside `ball 0 ρ`.  `R` is the pointwise coefficient sum. -/
structure LaurentForm where
  /-- Index type of the monomials. -/
  ι : Type
  /-- `Fintype` instance for the (finite) index. -/
  fintype_ι : Fintype ι
  /-- `DecidableEq` on the index (to split sums by centre). -/
  decEq_ι : DecidableEq ι
  /-- Coefficient of the `i`-th monomial. -/
  c : ι → ℂ
  /-- Centre of the `i`-th monomial. -/
  a : ι → ℂ
  /-- Integer exponent of the `i`-th monomial. -/
  n : ι → ℤ
  /-- The radius of the enclosing contour. -/
  ρ : ℝ
  /-- Every centre lies strictly inside the contour `C(0, ρ)`. -/
  centers_mem : ∀ i, a i ∈ ball (0 : ℂ) ρ

namespace LaurentForm

attribute [instance] LaurentForm.fintype_ι LaurentForm.decEq_ι

variable (L : LaurentForm)

/-- The `dz`-coefficient of the form: the pointwise sum of the Laurent monomials. -/
noncomputable def R : ℂ → ℂ := fun z => ∑ i, L.c i * (z - L.a i) ^ L.n i

/-- The contour `C(0, ρ)` has nonnegative radius (it contains a centre, so `ρ > 0` whenever the
family is nonempty; in general `dist_nonneg` gives `0 ≤ ρ` from any centre). -/
theorem rho_pos_of_nonempty [Nonempty L.ι] : 0 < L.ρ :=
  pos_of_mem_ball (L.centers_mem (Classical.arbitrary L.ι))

/-- Each monomial `z ↦ c i·(z − a i) ^ (n i)` is circle-integrable on `C(0, ρ)`: its only
singularity `a i` lies strictly inside the contour, off the sphere. -/
theorem circleIntegrable_monomial (i : L.ι) :
    CircleIntegrable (fun z => L.c i * (z - L.a i) ^ L.n i) 0 L.ρ := by
  have hρ0 : 0 ≤ L.ρ := le_of_lt (pos_of_mem_ball (L.centers_mem i))
  by_cases hn : 0 ≤ L.n i
  · -- nonnegative power: continuous, hence integrable.
    lift L.n i to ℕ using hn with m hm
    refine ContinuousOn.circleIntegrable hρ0 ?_
    exact (continuous_const.mul (((continuous_id.sub continuous_const)).pow m)).continuousOn
  · -- negative power `(z - a i)^(n i)`: integrable since `|a i - 0| ≠ |ρ|` (centre inside).
    push Not at hn
    have hmem : L.a i ∈ ball (0 : ℂ) L.ρ := L.centers_mem i
    have hne : (L.a i) ∉ sphere (0 : ℂ) |L.ρ| := by
      rw [mem_sphere_iff_norm, sub_zero]
      have hlt : ‖L.a i‖ < L.ρ := by simpa [dist_eq_norm] using hmem
      have hρ0 : 0 < L.ρ := lt_of_le_of_lt (norm_nonneg _) hlt
      rw [abs_of_pos hρ0]; exact ne_of_lt hlt
    have : CircleIntegrable (fun z => (z - L.a i) ^ L.n i) 0 L.ρ := by
      rw [circleIntegrable_sub_zpow_iff]
      exact Or.inr (Or.inr hne)
    exact this.const_mul (L.c i)

/-- **Multi-pole Cauchy residue theorem (partial-fraction form).** The large-contour integral of the
rational coefficient `R` equals `2πi` times the sum of the simple-pole coefficients (the `c i` with
`n i = −1`), all centres lying inside `C(0, ρ)`:

  `∮_{|z|=ρ} R = 2πi · ∑_{i : n i = −1} c i`.

Termwise: each `n i ≠ −1` monomial integrates to `0`, each `n i = −1` to `c i · 2πi`. -/
theorem largeCircleIntegral_eq :
    (∮ z in C((0 : ℂ), L.ρ), L.R z)
      = (2 * π * I) * ∑ i ∈ Finset.univ.filter (fun i => L.n i = -1), L.c i := by
  classical
  -- Push the contour integral through the finite sum.
  have hsum : (∮ z in C((0 : ℂ), L.ρ), L.R z)
      = ∑ i, ∮ z in C((0 : ℂ), L.ρ), L.c i * (z - L.a i) ^ L.n i := by
    rw [show (fun z => L.R z) = (fun z => ∑ i, L.c i * (z - L.a i) ^ L.n i) from rfl]
    exact circleIntegral.integral_fun_sum (fun i _ => L.circleIntegrable_monomial i)
  rw [hsum]
  -- Evaluate each monomial integral by the centre-inside formula.
  have hterm : ∀ i, (∮ z in C((0 : ℂ), L.ρ), L.c i * (z - L.a i) ^ L.n i)
      = if L.n i = -1 then L.c i * (2 * π * I) else 0 :=
    fun i => circleIntegral_laurentMonomial (L.centers_mem i)
  simp_rw [hterm]
  -- Collapse the `if` sum to the filtered sum over the simple poles.
  rw [Finset.mul_sum, ← Finset.sum_filter]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-! #### The finite residues, read by `resAt`

The finite residue of the form at a centre `a j` is `resAt R (a j)`.  Since the residue is local
(`resAt_congr` / additivity) and each monomial centred elsewhere is holomorphic at `a j`, this equals
the sum of the simple-pole coefficients `c i` whose centre is `a j` and exponent is `−1`. -/

/-- The **finite residue sum**: the sum, over the distinct centres, of the local residues of `R`.
Indexed over the centre images via the index set (each centre counted once through
`Finset.image L.a`). -/
noncomputable def finiteResidueSum : ℂ :=
  ∑ p ∈ Finset.univ.image L.a, resAt L.R p

/-- A Laurent monomial `c·(z − b)^m` is `MeromorphicAt` at any point `p` (so in particular has an
isolated singularity — `HoloPunctured` — there): integer powers of the meromorphic `z ↦ z − b` are
meromorphic, scaled by a constant. -/
theorem meromorphicAt_monomial (c b : ℂ) (m : ℤ) (p : ℂ) :
    MeromorphicAt (fun z => c * (z - b) ^ m) p := by
  have h1 : MeromorphicAt (fun z : ℂ => z - b) p :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  exact (MeromorphicAt.const c p).mul (h1.zpow m)

/-- A Laurent monomial centred at `b ≠ p` is **analytic at `p`** (its only singularity is at `b`):
the `m`-th integer power of `z − b` is analytic where `z − b ≠ 0`. -/
theorem analyticAt_monomial_of_ne (c : ℂ) {b : ℂ} (m : ℤ) {p : ℂ} (hbp : b ≠ p) :
    AnalyticAt ℂ (fun z => c * (z - b) ^ m) p :=
  analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).zpow (z := p) (n := m)
    (by simpa using sub_ne_zero.mpr (Ne.symm hbp)))

/-- `resAt` of a finite sum of functions, each with an isolated singularity at `p`, is the sum of the
residues — finite additivity, by induction from the binary `resAt_add` (with `HoloPunctured.add`
supplied through `MeromorphicAt.holoPunctured`). -/
theorem resAt_finsum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {p : ℂ}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) p) :
    resAt (fun z => ∑ i ∈ s, f i z) p = ∑ i ∈ s, resAt (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [resAt_zero]
  | @insert j s hj ih =>
    have hfj : MeromorphicAt (f j) p := hf j (Finset.mem_insert_self j s)
    have hfs : ∀ i ∈ s, MeromorphicAt (f i) p := fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)
    -- the tail sum is meromorphic at `p` (finite sum of meromorphic functions).
    have hsum_mero : MeromorphicAt (fun z => ∑ i ∈ s, f i z) p :=
      MeromorphicAt.fun_sum (fun i hi => hfs i hi)
    have hsplit : (fun z => ∑ i ∈ insert j s, f i z)
        = (f j) + (fun z => ∑ i ∈ s, f i z) := by
      funext z; rw [Finset.sum_insert hj]; rfl
    rw [hsplit, resAt_add hfj.holoPunctured hsum_mero.holoPunctured, ih hfs,
      Finset.sum_insert hj]

/-- **The local residue of `R` at a centre `p`.** It equals the sum of the simple-pole coefficients
sitting exactly at `p`: `resAt R p = ∑_{i : a i = p, n i = −1} c i`.  (Monomials centred elsewhere are
holomorphic at `p` and contribute no residue; monomials centred at `p` contribute by
`resAt_laurentMonomial`.) -/
theorem resAt_center_eq (p : ℂ) :
    resAt L.R p
      = ∑ i ∈ Finset.univ.filter (fun i => L.a i = p ∧ L.n i = -1), L.c i := by
  classical
  -- `resAt` of the finite sum is the sum of the per-monomial residues.
  rw [show L.R = (fun z => ∑ i, L.c i * (z - L.a i) ^ L.n i) from rfl,
    resAt_finsum Finset.univ (fun i z => L.c i * (z - L.a i) ^ L.n i)
      (fun i _ => meromorphicAt_monomial (L.c i) (L.a i) (L.n i) p)]
  -- Each monomial's residue at `p`: `0` if its centre `a i ≠ p`; else `if n i = -1 then c i else 0`.
  have hterm : ∀ i, resAt (fun z => L.c i * (z - L.a i) ^ L.n i) p
      = if L.a i = p ∧ L.n i = -1 then L.c i else 0 := by
    intro i
    by_cases hai : L.a i = p
    · subst hai
      rw [resAt_laurentMonomial]
      by_cases hni : L.n i = -1 <;> simp [hni]
    · -- off-centre monomial is analytic at `p`, so residue `0`.
      have hana := analyticAt_monomial_of_ne (L.c i) (L.n i) (p := p) hai
      rw [resAt_eq_zero_of_analyticAt hana]
      rw [if_neg (fun h => hai h.1)]
  simp_rw [hterm]
  rw [← Finset.sum_filter]

/-! #### The residue theorem on `ℂℙ¹`

`resAtInfty R = −(2πi)⁻¹ ∮ R = −∑_{i : n i = −1} c i` by `largeCircleIntegral_eq`; the finite residue
sum is `+∑_{i : n i = −1} c i` by `resAt_center_eq` summed over the centres; hence they cancel. -/

/-- `resAtInfty L.R L.ρ = −∑_{i : n i = −1} c i`: the residue at infinity is the negative of the total
simple-pole mass, by the multi-pole Cauchy formula `largeCircleIntegral_eq`. -/
theorem resAtInfty_eq :
    resAtInfty L.R L.ρ = -∑ i ∈ Finset.univ.filter (fun i => L.n i = -1), L.c i := by
  rw [resAtInfty, largeCircleIntegral_eq]
  rw [smul_eq_mul, neg_mul, ← mul_assoc, inv_mul_cancel₀ (by
    simp [Real.pi_ne_zero, Complex.I_ne_zero] : (2 * π * I : ℂ) ≠ 0), one_mul]

/-- **The `ℂℙ¹` residue theorem (Miranda §VIII.3, pillar 2).** For a rational `1`-form `R dz` on
`ℂℙ¹` in partial-fraction form, the sum of all residues — finite plus the residue at infinity —
vanishes:

  `(∑_{centres} Res_p R) + Res_∞ R = 0`.

The only Laurent terms contributing are the simple poles (`n i = −1`); each contributes its
coefficient `c i` to the finite sum (`resAt_center_eq`) and `−c i` to the residue at infinity
(`resAtInfty_eq`), so the total cancels. -/
theorem finiteResidueSum_add_resAtInfty_eq_zero :
    L.finiteResidueSum + resAtInfty L.R L.ρ = 0 := by
  classical
  rw [resAtInfty_eq]
  -- The finite residue sum, expanded over centres then over the index, is the simple-pole mass.
  have hfin : L.finiteResidueSum
      = ∑ i ∈ Finset.univ.filter (fun i => L.n i = -1), L.c i := by
    rw [finiteResidueSum]
    simp_rw [resAt_center_eq L]
    -- ∑_{p ∈ image a} ∑_{i : a i = p ∧ n i = -1} c i  =  ∑_{i : n i = -1} c i
    rw [← Finset.sum_biUnion]
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext i
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_filter]
      constructor
      · intro h
        obtain ⟨p, -, -, hni⟩ := h
        exact hni
      · intro h
        exact ⟨L.a i, ⟨i, rfl⟩, rfl, h⟩
    · -- pairwise-disjoint: distinct centres give disjoint index-fibres.
      intro p _ q _ hpq
      simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i hip hiq
      exact hpq (hip.1 ▸ hiq.1)
  rw [hfin, add_neg_cancel]

end LaurentForm

end Jacobians.TraceResidue
