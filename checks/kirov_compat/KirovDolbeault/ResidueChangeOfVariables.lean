/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.MeromorphicTrace
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# The residue change-of-variables atom (Gate A, input A-i)

This file discharges the named `Prop`
`Jacobians.MeromorphicTrace.ResidueChangeOfVariables` as a genuine theorem
`Jacobians.MeromorphicTrace.residueChangeOfVariables`:

> the residue of a meromorphic function/1-form is **invariant under a holomorphic change of the
> coordinate**.  Concretely, for a local biholomorphism `s` at `b` (`s` analytic at `b`,
> `deriv s b ≠ 0`) and any `g` meromorphic at `s b`, the pushforward 1-form
> `w ↦ g (s w) · s'(w)` has the same residue at `b` as `g · dz` has at `s b`:
>
>   `resAt (fun w => g (s w) * deriv s w) b = resAt g (s b)`.

This is the one isolated one-variable complex-analysis atom that the **general** (any-order pole)
fibre Lemma 3.2 `FibreTrace.resAt_traceCoeff` is gated on, and through it Gate A's 1-form residue
theorem `∑ₐ Resₐ(α) = 0`.  Mathlib
has **no** residue API, so this is built from the repo's `resAt` (the `(2πi)⁻¹∮` contour residue,
`Jacobians.Dolbeault.Residue`) and Mathlib's circle-integral toolbox.

## The proof strategy (no contour reparametrisation needed)

Mathlib lacks winding-number invariance of `circleIntegral` along a biholomorphism, so we do **not**
substitute in the contour.  Instead we peel the Laurent expansion of `g` at `a := s b` one power at
a time and reduce to two monomial facts that are *both directly computable* through `resAt`:

* **simple pole `n = −1`** — the pushforward `c·(s w − a)⁻¹·s'(w)` has residue `c` at `b`, the
  already-proved `Jacobians.MeromorphicTrace.resAt_simplePole_pushforward` (the slope of `s` cancels
  the `s'` numerator, leaving a simple pole with the same coefficient).
* **non-residue power `n ≠ −1`** — the pushforward `c·(s w − a)^n·s'(w)` has residue `0` at `b`,
  because it is the `w`-derivative of `c/(n+1)·(s w − a)^{n+1}` (chain rule), and the contour
  integral of a derivative vanishes (`circleIntegral.integral_eq_zero_of_hasDerivWithinAt`).  This is
  the genuinely new ingredient — the exactness/primitive argument that bypasses contour substitution.

`g` itself, having order `n₀ = meromorphicOrderAt g a`, factors as `(w − a)^{n₀}·h` with `h`
analytic and `h a ≠ 0` (`meromorphicOrderAt_eq_int_iff`); peeling the leading monomial `h a·(w −
a)^{n₀}` lowers the pole order by one (the remainder gains a zero at `a`), so a strong induction on
the pole depth `(−n₀).toNat` reduces every step to the two monomial facts plus `resAt` additivity
(`resAt_add`).  The induction is `resAt_changeOfVariables_aux`; the atom follows.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2 / residue
  change of variables).
* Forster, *Lectures on Riemann Surfaces*, §17 (the residue functional `Res`).
-/

open Complex Metric Filter Topology
open scoped Real

namespace Jacobians.MeromorphicTrace

open Jacobians.Dolbeault Jacobians.TraceResidue

/-! ### The non-residue monomial pushforward has residue zero (the new exactness ingredient)

For `n ≠ −1`, the pushforward `c·(s w − a)^n·s'(w)` of the Laurent monomial `c·(w − a)^n` along a
local biholomorphism `s` (`s b = a`) is the `w`-derivative of `c/(n+1)·(s w − a)^{n+1}`, hence has a
holomorphic primitive on a punctured neighbourhood of `b`; its small circle integrals vanish, so its
residue at `b` is `0`.  (For `n = −1` the primitive would be a logarithm and this fails — that case
is the simple pole, handled separately.) -/

/-- **The non-residue monomial pushforward has residue zero.**  For a local biholomorphism `s` at `b`
(`s` analytic at `b`, `deriv s b ≠ 0`, `s b = a`) and `n : ℤ` with `n ≠ −1`, the pushforward
`w ↦ c·(s w − a)^n·s'(w)` of the Laurent monomial `c·(w − a)^n` has residue `0` at `b`:

> `resAt (fun w => c·(s w − a)^n·s'(w)) b = 0`.

The integrand is `d/dw [c/(n+1)·(s w − a)^{n+1}]` (chain rule), so the small circle integrals all
vanish (`circleIntegral.integral_eq_zero_of_hasDerivWithinAt`). -/
theorem resAt_zpow_pushforward_of_ne {s : ℂ → ℂ} {a b c : ℂ} {n : ℤ}
    (hs : AnalyticAt ℂ s b) (hs' : deriv s b ≠ 0) (hsb : s b = a) (hn : n ≠ -1) :
    resAt (fun w => c * (s w - a) ^ n * deriv s w) b = 0 := by
  -- `s w - a` has a simple zero at `b`, so `s w ≠ a` on a punctured ball; there the integrand is the
  -- `w`-derivative of `c/(n+1)·(s w − a)^{n+1}`, hence has vanishing circle integrals.
  obtain ⟨g, hg, hga, hfact⟩ := exists_simpleZero_factorization hs hs' hsb
  -- choose a radius `ρ > 0` on which: `s` and `deriv s` are analytic, the factorization holds, and
  -- `g ≠ 0` (so `s w − a = (w − b)·g w ≠ 0` for `w ≠ b`).
  have hg0 : g b ≠ 0 := hga ▸ hs'
  have hev : ∀ᶠ z in 𝓝 b,
      AnalyticAt ℂ s z ∧ AnalyticAt ℂ (deriv s) z ∧ (s z - a = (z - b) * g z) ∧ g z ≠ 0 := by
    filter_upwards [hs.eventually_analyticAt, hs.deriv.eventually_analyticAt, hfact,
      hg.continuousAt.eventually_ne hg0] with z hsz hdsz hfz hgz using ⟨hsz, hdsz, hfz, hgz⟩
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ρ, hρ, hball⟩ := hev
  -- the integrand is holomorphic on the punctured ball `ball b ρ \ {b}` (there `s z ≠ a`).
  set F₀ : ℂ → ℂ := fun w => c * (s w - a) ^ n * deriv s w with hF₀
  have hsza : ∀ z ∈ ball b ρ \ {b}, s z - a ≠ 0 := by
    intro z hz
    obtain ⟨_, _, hzf, hzg⟩ := hball (mem_ball.mp hz.1)
    rw [hzf]
    exact mul_ne_zero (sub_ne_zero.mpr (by simpa using hz.2)) hzg
  have hpunct : ∀ z ∈ ball b ρ \ {b}, DifferentiableAt ℂ F₀ z := by
    intro z hz
    obtain ⟨hzs, hzds, _, _⟩ := hball (mem_ball.mp hz.1)
    have hsza' : s z - a ≠ 0 := hsza z hz
    have h1 : DifferentiableAt ℂ (fun w => (s w - a) ^ n) z :=
      (hzs.differentiableAt.sub_const a).zpow (Or.inl hsza')
    have h2 : DifferentiableAt ℂ (deriv s) z := hzds.differentiableAt
    exact ((differentiableAt_const c).mul h1).mul h2
  -- pick a small contour radius and read `resAt` as `(2πi)⁻¹∮`.
  set r := ρ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrρ : r < ρ := by rw [hr]; exact half_lt_self hρ
  rw [hF₀, resAt_eq_smul_circleIntegral hpunct hr0 hrρ]
  -- the contour integral vanishes: the integrand is `d/dw [c/(n+1)·(s w − a)^{n+1}]`.
  suffices hint : (∮ z in C(b, r), F₀ z) = 0 by rw [hF₀] at hint; rw [hint, smul_zero]
  set F : ℂ → ℂ := fun w => c / (n + 1) * (s w - a) ^ (n + 1) with hFdef
  have hn1 : (n : ℂ) + 1 ≠ 0 := by
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℤ) : ℂ) by push_cast; ring]
    exact_mod_cast (by omega : n + 1 ≠ 0)
  refine circleIntegral.integral_eq_zero_of_hasDerivWithinAt (f := F) hr0.le (fun z hz => ?_)
  -- on the sphere of radius `r < ρ`, `z ∈ ball b ρ \ {b}`, so `F` is differentiable with derivative `F₀`.
  have hzmem : z ∈ ball b ρ \ {b} := by
    have hd : dist z b = r := Metric.mem_sphere.mp hz
    refine ⟨mem_ball.mpr (by rw [hd]; exact hrρ), ?_⟩
    simp only [Set.mem_singleton_iff]
    intro he; rw [he, dist_self] at hd; exact absurd hd (ne_of_lt hr0)
  obtain ⟨hzs, _, _, _⟩ := hball (mem_ball.mp hzmem.1)
  have hsza' : s z - a ≠ 0 := hsza z hzmem
  -- chain rule: `HasDerivAt (fun w => (s w − a)^{n+1}) ((n+1)·(s z − a)^n · s'(z)) z`.
  have hsderiv : HasDerivAt s (deriv s z) z := hzs.differentiableAt.hasDerivAt
  have hzpow : HasDerivAt (fun y : ℂ => y ^ (n + 1)) (((n : ℂ) + 1) * (s z - a) ^ (n + 1 - 1)) (s z - a) := by
    have := hasDerivAt_zpow (n + 1) (s z - a) (Or.inl hsza')
    convert this using 2
    push_cast; ring
  have hcomp : HasDerivAt (fun w => (s w - a) ^ (n + 1))
      (((n : ℂ) + 1) * (s z - a) ^ (n + 1 - 1) * deriv s z) z := by
    have hsub : HasDerivAt (fun w => s w - a) (deriv s z) z := hsderiv.sub_const a
    exact hzpow.comp z hsub
  have hF' : HasDerivAt F (F₀ z) z := by
    have h := (hcomp.const_mul (c / (n + 1)))
    refine h.congr_deriv ?_
    show c / ((n : ℂ) + 1) * (((n : ℂ) + 1) * (s z - a) ^ (n + 1 - 1) * deriv s z) = F₀ z
    rw [hF₀]
    field_simp
    rw [show (n + 1 - 1 : ℤ) = n by ring]
    ring
  exact hF'.hasDerivWithinAt

/-! ### The full monomial pushforward residue

Combining the two cases: the pushforward of `c·(w − a)^n` along the biholomorphism `s` has residue
`c` if `n = −1` (simple pole, `resAt_simplePole_pushforward`) and `0` otherwise
(`resAt_zpow_pushforward_of_ne`) — exactly `resAt (c·(w − a)^n) a` (`resAt_laurentMonomial`).  This
is the residue change-of-variables for a single Laurent monomial. -/

/-- **The Laurent-monomial residue change of variables.**  For a local biholomorphism `s` at `b`
(`s b = a`) and any `n : ℤ`, the pushforward `w ↦ c·(s w − a)^n·s'(w)` has the same residue at `b`
as the monomial `c·(w − a)^n` has at `a`:

> `resAt (fun w => c·(s w − a)^n·s'(w)) b = resAt (fun w => c·(w − a)^n) a`. -/
theorem resAt_monomial_pushforward {s : ℂ → ℂ} {a b c : ℂ} (n : ℤ)
    (hs : AnalyticAt ℂ s b) (hs' : deriv s b ≠ 0) (hsb : s b = a) :
    resAt (fun w => c * (s w - a) ^ n * deriv s w) b = resAt (fun w => c * (w - a) ^ n) a := by
  rw [resAt_laurentMonomial]
  by_cases hn : n = -1
  · subst hn
    rw [if_pos rfl]
    have hcv := resAt_simplePole_pushforward (a := b) (b := a) (c := c) hs hs' hsb
    rw [show (fun w => c * (s w - a) ^ (-1 : ℤ) * deriv s w)
        = (fun w => c * (s w - a)⁻¹ * deriv s w) by funext w; rw [zpow_neg_one]]
    exact hcv
  · rw [if_neg hn]
    exact resAt_zpow_pushforward_of_ne hs hs' hsb hn

/-! ### `s` maps a punctured neighbourhood of `b` into a punctured neighbourhood of `a`

A local biholomorphism `s` (`s b = a`, `deriv s b ≠ 0`) is locally injective at `b`, so `s w ≠ a`
for `w ≠ b` near `b`; combined with continuity (`s w → a`) this is `Tendsto s (𝓝[≠] b) (𝓝[≠] a)`.
It lets germ equalities at `a` (off `a`) pull back to germ equalities at `b` (off `b`) along the
pushforward — the bookkeeping that makes the residue depend only on the germ of `g`. -/

/-- **`s` pulls the punctured filter back.**  For a local biholomorphism `s` at `b` (`s b = a`,
`deriv s b ≠ 0`), `s` tends to `a` along `𝓝[≠] b` while staying off `a`:
`Tendsto s (𝓝[≠] b) (𝓝[≠] a)`. -/
theorem tendsto_nhdsNE_of_biholo {s : ℂ → ℂ} {a b : ℂ}
    (hs : AnalyticAt ℂ s b) (hs' : deriv s b ≠ 0) (hsb : s b = a) :
    Filter.Tendsto s (𝓝[≠] b) (𝓝[≠] a) := by
  obtain ⟨g, hg, hga, hfact⟩ := exists_simpleZero_factorization hs hs' hsb
  have hg0 : g b ≠ 0 := hga ▸ hs'
  rw [tendsto_nhdsWithin_iff]
  constructor
  · -- `s → a = s b` along `𝓝[≠] b` (continuity).
    exact (hsb ▸ hs.continuousAt.continuousWithinAt :
      Filter.Tendsto s (𝓝[≠] b) (𝓝 a))
  · -- `s w ≠ a` for `w ≠ b` near `b`, by the simple-zero factorization `s w − a = (w − b)·g w`.
    filter_upwards [mem_nhdsWithin_of_mem_nhds hfact, self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hg.continuousAt.eventually_ne hg0)] with w hwf hw_ne hwg
    have hwb : w ≠ b := by simpa using hw_ne
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro he
    rw [he, sub_self] at hwf
    have hz : (w - b) * g w = 0 := hwf.symm
    rcases mul_eq_zero.mp hz with h | h
    · exact hwb (sub_eq_zero.mp h)
    · exact hwg h

/-- **The pushforward respects germ equality.**  If `g₁` and `g₂` agree on a punctured neighbourhood
of `a := s b`, their pushforwards `g₁∘s·s'` and `g₂∘s·s'` agree on a punctured neighbourhood of `b`,
so have the same residue at `b`. -/
theorem resAt_pushforward_congr {s g₁ g₂ : ℂ → ℂ} {a b : ℂ}
    (hs : AnalyticAt ℂ s b) (hs' : deriv s b ≠ 0) (hsb : s b = a)
    (h : g₁ =ᶠ[𝓝[≠] a] g₂) :
    resAt (fun w => g₁ (s w) * deriv s w) b = resAt (fun w => g₂ (s w) * deriv s w) b := by
  refine resAt_congr ?_
  have hpb : ∀ᶠ w in 𝓝[≠] b, g₁ (s w) = g₂ (s w) :=
    (tendsto_nhdsNE_of_biholo hs hs' hsb).eventually h
  filter_upwards [hpb] with w hw
  rw [hw]

/-- The pushforward `w ↦ g (s w)·s'(w)` of a function `g` meromorphic at `a := s b` is meromorphic
at `b` (composition with the analytic section, times the analytic section derivative). -/
theorem meromorphicAt_pushforward {s g : ℂ → ℂ} {a b : ℂ}
    (hs : AnalyticAt ℂ s b) (hsb : s b = a) (hg : MeromorphicAt g a) :
    MeromorphicAt (fun w => g (s w) * deriv s w) b := by
  have hcomp : MeromorphicAt (g ∘ s) b :=
    MeromorphicAt.comp_analyticAt (by rw [hsb]; exact hg) hs
  exact hcomp.mul hs.deriv.meromorphicAt

/-- **The pushforward is additive on residues.**  For `g₁`, `g₂` meromorphic at `a := s b`, the
pushforward of `g₁ + g₂` splits its residue at `b`:

> `resAt ((g₁+g₂)∘s·s') b = resAt (g₁∘s·s') b + resAt (g₂∘s·s') b`. -/
theorem resAt_pushforward_add {s g₁ g₂ : ℂ → ℂ} {a b : ℂ}
    (hs : AnalyticAt ℂ s b) (hsb : s b = a)
    (hg₁ : MeromorphicAt g₁ a) (hg₂ : MeromorphicAt g₂ a) :
    resAt (fun w => (g₁ (s w) + g₂ (s w)) * deriv s w) b
      = resAt (fun w => g₁ (s w) * deriv s w) b + resAt (fun w => g₂ (s w) * deriv s w) b := by
  have hsplit : (fun w => (g₁ (s w) + g₂ (s w)) * deriv s w)
      = (fun w => g₁ (s w) * deriv s w) + (fun w => g₂ (s w) * deriv s w) := by
    funext w; simp only [Pi.add_apply]; ring
  rw [hsplit]
  exact resAt_add (meromorphicAt_pushforward hs hsb hg₁).holoPunctured
    (meromorphicAt_pushforward hs hsb hg₂).holoPunctured

/-! ### The two trivial cases of the change of variables: zero germ and analytic `g`

When `g` is locally `0` (off `a`), or analytic at `a`, both residues are `0`.  These are the leaves
of the induction below. -/

/-- **Change of variables, zero-germ case.**  If `g` vanishes on a punctured neighbourhood of
`a := s b`, both the pushforward residue at `b` and `resAt g a` are `0`. -/
theorem resAt_changeOfVariables_of_eventuallyEq_zero {s g : ℂ → ℂ} {a b : ℂ}
    (hs : AnalyticAt ℂ s b) (hs' : deriv s b ≠ 0) (hsb : s b = a)
    (h0 : g =ᶠ[𝓝[≠] a] 0) :
    resAt (fun w => g (s w) * deriv s w) b = resAt g (s b) := by
  rw [hsb]
  rw [resAt_pushforward_congr hs hs' hsb h0, resAt_congr (f := g) (g := fun _ => 0) h0]
  simp only [Pi.zero_apply, zero_mul]
  rw [resAt_zero, resAt_zero]

/-- **Change of variables, analytic case.**  If `g` is analytic at `a := s b`, both the pushforward
residue at `b` and `resAt g a` are `0` (the pushforward `g∘s·s'` is analytic at `b`). -/
theorem resAt_changeOfVariables_of_analyticAt {s g : ℂ → ℂ} {a b : ℂ}
    (hs : AnalyticAt ℂ s b) (hsb : s b = a) (hg : AnalyticAt ℂ g a) :
    resAt (fun w => g (s w) * deriv s w) b = resAt g (s b) := by
  rw [hsb, resAt_eq_zero_of_analyticAt hg]
  refine resAt_eq_zero_of_analyticAt ?_
  have hgsb : AnalyticAt ℂ g (s b) := hsb ▸ hg
  have hcomp : AnalyticAt ℂ (g ∘ s) b := hgsb.comp hs
  exact (hcomp.mul hs.deriv : AnalyticAt ℂ (fun w => g (s w) * deriv s w) b)

/-- **Change of variables respects the germ off `a`.**  If `g₁ =ᶠ[𝓝[≠] a] g₂` (`a := s b`) and the
change of variables holds for `g₂`, it holds for `g₁` — both residues only see the germ off the
point (`resAt_pushforward_congr` / `resAt_congr`). -/
theorem resAt_changeOfVariables_congr {s g₁ g₂ : ℂ → ℂ} {a b : ℂ}
    (hs : AnalyticAt ℂ s b) (hs' : deriv s b ≠ 0) (hsb : s b = a)
    (h : g₁ =ᶠ[𝓝[≠] a] g₂)
    (h₂ : resAt (fun w => g₂ (s w) * deriv s w) b = resAt g₂ (s b)) :
    resAt (fun w => g₁ (s w) * deriv s w) b = resAt g₁ (s b) := by
  rw [hsb] at h₂ ⊢
  rw [resAt_pushforward_congr hs hs' hsb h, h₂, resAt_congr h]

/-- A function meromorphic at `x` with `meromorphicOrderAt ≥ 0` agrees, off `x`, with an **analytic**
function (its normal form `toMeromorphicNFAt`).  This is all the residue calculus needs (the residue
only sees the germ off `x`), sidestepping the removable-singularity extension at `x` itself. -/
theorem exists_analyticAt_eventuallyEq_of_meromorphicOrderAt_nonneg {g : ℂ → ℂ} {x : ℂ}
    (hg : MeromorphicAt g x) (hord : 0 ≤ meromorphicOrderAt g x) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h x ∧ g =ᶠ[𝓝[≠] x] h := by
  refine ⟨toMeromorphicNFAt g x, ?_, hg.eq_nhdsNE_toMeromorphicNFAt⟩
  have hnfNF : MeromorphicNFAt (toMeromorphicNFAt g x) x := meromorphicNFAt_toMeromorphicNFAt
  have hord_nf : 0 ≤ meromorphicOrderAt (toMeromorphicNFAt g x) x := by
    rwa [meromorphicOrderAt_congr (hg.eq_nhdsNE_toMeromorphicNFAt)] at hord
  exact hnfNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp hord_nf

/-! ### The peeling induction — the general residue change of variables

We prove the residue change of variables by strong induction on the **pole depth** `k`, where the
hypothesis `(-(k:ℤ)) ≤ meromorphicOrderAt g a` bounds the pole order of `g` at `a := s b` by `k`.

* `k = 0` (`order ≥ 0`): `g` is the zero germ (`order = ⊤`) or analytic (`order ≥ 0` finite) — both
  trivial cases (`resAt_changeOfVariables_of_eventuallyEq_zero` / `_of_analyticAt`).
* `k+1`: if `order ≥ -k`, the inductive hypothesis applies directly.  Otherwise the order is exactly
  `-(k+1)`; factor `g =ᶠ (w−a)^{-(k+1)}·G` (`G` analytic, `G a ≠ 0`) and split off the leading
  monomial `M := G a·(w−a)^{-(k+1)}`.  The remainder `R := g − M` factors as
  `(w−a)^{-(k+1)}·(G − G a)` with `G − G a` vanishing at `a`, so its order is `≥ -(k+1)+1 = -k` and
  the inductive hypothesis applies to it.  Both residues split additively
  (`resAt_add` / `resAt_pushforward_add`) into the monomial contribution
  (`resAt_monomial_pushforward`) plus the remainder contribution (the inductive hypothesis). -/

/-- **The residue change of variables, by induction on the pole depth.**  For a local biholomorphism
`s` at `b` (`s` analytic, `deriv s b ≠ 0`) and `g` meromorphic at `a := s b` with pole order bounded
by `k` (`-(k:ℤ) ≤ meromorphicOrderAt g a`), the pushforward `w ↦ g (s w)·s'(w)` has the same residue
at `b` as `g·dz` has at `a`:

> `resAt (fun w => g (s w)·s'(w)) b = resAt g (s b)`. -/
theorem resAt_changeOfVariables_aux : ∀ (k : ℕ) (s g : ℂ → ℂ) (b : ℂ),
    AnalyticAt ℂ s b → deriv s b ≠ 0 → MeromorphicAt g (s b) →
    (-(k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt g (s b) →
    resAt (fun w => g (s w) * deriv s w) b = resAt g (s b) := by
  intro k
  induction k with
  | zero =>
    intro s g b hs hs' hg hk
    -- `order ≥ 0`: `g` agrees off `s b` with an analytic function `h`; transfer the CoV.
    have hnonneg : 0 ≤ meromorphicOrderAt g (s b) := by simpa using hk
    obtain ⟨h, hh, hgh⟩ := exists_analyticAt_eventuallyEq_of_meromorphicOrderAt_nonneg hg hnonneg
    exact resAt_changeOfVariables_congr hs hs' rfl hgh
      (resAt_changeOfVariables_of_analyticAt hs rfl hh)
  | succ k ih =>
    intro s g b hs hs' hg hk
    set a := s b with ha
    -- dispatch the zero germ first.
    rcases eq_or_ne (meromorphicOrderAt g a) ⊤ with htop | hfin
    · have h0 : g =ᶠ[𝓝[≠] a] 0 := by
        rw [meromorphicOrderAt_eq_top_iff] at htop; exact htop
      exact resAt_changeOfVariables_of_eventuallyEq_zero hs hs' ha.symm h0
    -- finite order `n`.
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
    rw [← hn] at hk hfin
    by_cases hnk : (-(k : ℤ) : WithTop ℤ) ≤ (n : WithTop ℤ)
    · -- order already `≥ -k`: apply the inductive hypothesis directly.
      exact ih s g b hs hs' hg (by rw [← ha, ← hn]; exact hnk)
    · -- order `< -k` but `≥ -(k+1)`, so order `= -(k+1)`.
      have hneq : n = -(k + 1 : ℤ) := by
        have h1 : -(k + 1 : ℤ) ≤ n := by exact_mod_cast hk
        have h2 : ¬ (-(k : ℤ) ≤ n) := fun hc => hnk (by exact_mod_cast hc)
        omega
      -- the leading-monomial factorization `g =ᶠ (w − a)^n • G`.
      have hg_a : MeromorphicAt g a := hg
      have hord_a : meromorphicOrderAt g a = (n : ℤ) := hn.symm
      obtain ⟨G, hG, hGne, hGeq⟩ := (meromorphicOrderAt_eq_int_iff hg_a).mp hord_a
      set c₀ := G a with hc₀
      have hc₀ne : c₀ ≠ 0 := hGne
      set M : ℂ → ℂ := fun w => c₀ * (w - a) ^ n with hM
      set R : ℂ → ℂ := fun w => g w - M w with hR
      have hMmero : MeromorphicAt M a :=
        (MeromorphicAt.const c₀ a).mul ((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow n)
      have hRmero : MeromorphicAt R a := hg_a.sub hMmero
      -- `R =ᶠ (w − a)^n • (G − c₀)` off `a`.
      have hReq : R =ᶠ[𝓝[≠] a] ((fun w => (w - a) ^ n) • (fun w => G w - c₀)) := by
        filter_upwards [hGeq] with z hz
        simp only [hR, hM, hz, Pi.smul_apply', smul_eq_mul]
        ring
      -- `G − c₀` is analytic and vanishes at `a`, so its order is `> 0`, hence `≥ 1`;
      -- thus order `R = n + order(G − c₀) ≥ n + 1 = -k`.
      have hGc₀ : AnalyticAt ℂ (fun w => G w - c₀) a := hG.sub analyticAt_const
      have hGc₀_zero : (fun w => G w - c₀) a = 0 := by simp [hc₀]
      have hord_Gc₀_pos : 0 < meromorphicOrderAt (fun w => G w - c₀) a := by
        rw [← tendsto_zero_iff_meromorphicOrderAt_pos hGc₀.meromorphicAt]
        have htend : Filter.Tendsto (fun w => G w - c₀) (𝓝[≠] a) (𝓝 ((fun w => G w - c₀) a)) :=
          hGc₀.continuousAt.continuousWithinAt.tendsto
        rw [hGc₀_zero] at htend
        exact htend
      have hord_Gc₀ : (1 : WithTop ℤ) ≤ meromorphicOrderAt (fun w => G w - c₀) a := by
        -- `0 < x` for an integer-or-⊤ value forces `1 ≤ x`.
        rcases eq_or_ne (meromorphicOrderAt (fun w => G w - c₀) a) ⊤ with htop | hfin'
        · rw [htop]; exact le_top
        · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hfin'
          rw [← hm] at hord_Gc₀_pos ⊢
          have : (0 : ℤ) < m := by exact_mod_cast hord_Gc₀_pos
          exact_mod_cast (by omega : (1 : ℤ) ≤ m)
      have hpow_mero : MeromorphicAt (fun w => (w - a) ^ n) a :=
        (analyticAt_id.sub analyticAt_const).meromorphicAt.zpow n
      have hord_pow : meromorphicOrderAt (fun w => (w - a) ^ n) a = (n : ℤ) := by
        rw [meromorphicOrderAt_congr (f₁ := fun w => (w - a) ^ n) (f₂ := (· - a) ^ n)
          (Filter.EventuallyEq.refl _ _), meromorphicOrderAt_zpow_id_sub_const]
      have hordR : (-(k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt R a := by
        rw [meromorphicOrderAt_congr hReq,
          meromorphicOrderAt_smul hpow_mero hGc₀.meromorphicAt, hord_pow, hneq]
        -- goal: `-(k:ℤ) ≤ -(k+1) + order(G − c₀)`; case on whether the order is `⊤`.
        rcases eq_or_ne (meromorphicOrderAt (fun w => G w - c₀) a) ⊤ with htop | hfin'
        · rw [htop, WithTop.add_top]; exact le_top
        · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hfin'
          rw [← hm] at hord_Gc₀ ⊢
          have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hord_Gc₀
          rw [show ((-(↑k + 1) : ℤ) : WithTop ℤ) + (m : WithTop ℤ)
              = ((-(↑k + 1) + m : ℤ) : WithTop ℤ) from by rw [WithTop.coe_add]]
          exact_mod_cast (by omega : -(k : ℤ) ≤ -(↑k + 1) + m)
      -- split both residues into the monomial part + remainder.
      have hgMR : ∀ w, g w = M w + R w := fun w => by simp only [hR]; ring
      -- LHS pushforward split.
      have hLHS_split : (fun w => g (s w) * deriv s w)
          = (fun w => (M (s w) + R (s w)) * deriv s w) := by
        funext w; rw [hgMR (s w)]
      rw [show resAt g (s b) = resAt g a from by rw [ha], hLHS_split,
        resAt_pushforward_add hs ha.symm hMmero hRmero]
      -- RHS split.
      have hRHS_split : resAt g a = resAt M a + resAt R a := by
        have hgMR' : g = M + R := by funext w; rw [Pi.add_apply, hgMR w]
        rw [hgMR']
        exact resAt_add hMmero.holoPunctured hRmero.holoPunctured
      rw [hRHS_split]
      -- the monomial residues match (change of variables for a single monomial);
      -- the remainder residues match (inductive hypothesis, order `≥ -k`).
      have hMpush : resAt (fun w => M (s w) * deriv s w) b = resAt M a := by
        rw [show (fun w => M (s w) * deriv s w) = (fun w => c₀ * (s w - a) ^ n * deriv s w) by
          funext w; rw [hM]]
        rw [resAt_monomial_pushforward (c := c₀) n hs hs' ha.symm, hM]
      have hRpush : resAt (fun w => R (s w) * deriv s w) b = resAt R a := by
        have hih := ih s R b hs hs' (ha ▸ hRmero) (by rw [← ha]; exact hordR)
        rw [← ha] at hih; exact hih
      rw [hMpush, hRpush]

/-- **The residue change-of-variables atom (`ResidueChangeOfVariables`), proved.**  For every local
biholomorphism `s` at `b` (`s` analytic, `deriv s b ≠ 0`) and every `g` meromorphic at `s b`, the
pushforward 1-form `w ↦ g (s w)·s'(w)` has the same residue at `b` as `g·dz` at `s b`:

> `resAt (fun w => g (s w) * deriv s w) b = resAt g (s b)`.

This discharges the named `Prop` `ResidueChangeOfVariables` — the isolated one-variable input (Gate
A, A-i) to the general fibre Lemma 3.2 `FibreTrace.resAt_traceCoeff` and the 1-form residue theorem
`∑ₐ Resₐ(α) = 0`.  *Proof:* `g` has some finite pole depth `k = (−order).toNat` (or is the zero
germ), so `resAt_changeOfVariables_aux` applies. -/
theorem residueChangeOfVariables : ResidueChangeOfVariables := by
  intro s g b hs hs' hg
  -- choose a pole-depth bound `k` for `g` at `s b`.
  rcases eq_or_ne (meromorphicOrderAt g (s b)) ⊤ with htop | hfin
  · -- zero germ: depth `0` works.
    exact resAt_changeOfVariables_aux 0 s g b hs hs' hg (by simp [htop])
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
    refine resAt_changeOfVariables_aux (-n).toNat s g b hs hs' hg ?_
    rw [← hn]
    -- `-((-n).toNat) ≤ n` in `WithTop ℤ` (the pole depth `(−n).toNat = max 0 (−n)`).
    have : -((-n).toNat : ℤ) ≤ n := by omega
    exact_mod_cast this

/-! ### The Gate-A feeders, now unconditional

With the atom `residueChangeOfVariables` proved, the general fibre Lemma 3.2 and the general trace
combine no longer need `ResidueChangeOfVariables` as a hypothesis — these are the unconditional
forms of `FibreTrace.resAt_traceCoeff` and `finiteResidueSum_trace_eq_zero_of_fibres` that feed the
1-form residue theorem `∑ₐ Resₐ(α) = 0` (Gate A) without any analytic side condition. -/

/-- **Lemma 3.2 (residue-trace compatibility), unconditional.**  The residue of the trace coefficient
at the base equals the fibre sum of the per-sheet residues — now with **no** hypothesis (the residue
change-of-variables atom is discharged):

> `Res_b (Tr_F α) = ∑_{sheets i} Res_{pre i} (coeff i)`. -/
theorem FibreTrace.resAt_traceCoeff' (T : FibreTrace) :
    resAt T.traceCoeff T.b = ∑ i, resAt (T.coeff i) (T.pre i) :=
  T.resAt_traceCoeff residueChangeOfVariables

/-- **The trace combine, fibre-trace form, unconditional.**  The general (any-order-pole) trace
combine of Miranda §VIII.3, now without the `ResidueChangeOfVariables` hypothesis:

> `(∑_{centers p} Res_b (Tr_F α over fibre p)) + Res_∞ (Tr_F α) = 0`. -/
theorem finiteResidueSum_trace_eq_zero_of_fibres' (L : LaurentForm)
    (fibre : ℂ → FibreTrace)
    (hL32 : ∀ p ∈ (Finset.univ.image L.a),
      (∑ i, resAt ((fibre p).coeff i) ((fibre p).pre i)) = resAt L.R p) :
    (∑ p ∈ Finset.univ.image L.a, resAt (fibre p).traceCoeff (fibre p).b)
      + resAtInfty L.R L.ρ = 0 :=
  finiteResidueSum_trace_eq_zero_of_fibres L fibre residueChangeOfVariables hL32

end Jacobians.MeromorphicTrace
