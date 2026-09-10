/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Dolbeault.FormTraceGlobalConstruct
import KirovDolbeault.Dolbeault.FormTraceMeromorphic
import KirovDolbeault.Dolbeault.FormTracePrincipalPart
import KirovDolbeault.Dolbeault.FormTracePrincipalPartInfty

/-!
# The global trace function `T : ℂ → ℂ` over a fibre family (Gate A, §VIII.3 step 1)

`Jacobians.Dolbeault.FormTraceGlobalAssemble` reduced Gate A (`∑ₐ Resₐ(α) = 0`) to constructing a
`GlobalTrace ω₀ g f poles hac` — a single value-chart `dz`-coefficient function `T : ℂ → ℂ` that
germ-agrees with each *local* fibre trace, together with the holomorphic-remainder data.  This file
builds the **definition of `T`** as Miranda's trace `Tr_F α` read in the value chart, together with
its **meromorphy off the finite exceptional set** — the genuinely-analytic foundational layer the
`GlobalTrace` construction sits on.

## The definition — `T` as a fibre sum of regular-sheet pushforwards

Miranda's trace of the 1-form `α = ω₀·g` along the cover `F = f.toRiemannSphere` is, over a value
`b`, the sum over the fibre `F⁻¹(coe b)` of the pushforward of `α` along the local inverse sheets.  We
package this *intrinsically* as a single function `traceCoeffFun ω₀ g f b`, defined for a chosen
finite family of fibre points `D : FibreRegularData g f b` as the local trace coefficient
`(fibreTrace ω₀ f D).traceCoeff b`.  The genuine global trace `T` is obtained by choosing, at each
regular value, the *full* fibre `F⁻¹(coe b)` (all `deg f` sheets); at a finite pole-value the chosen
fibre is the *pole* sub-fibre (`fibreReg hac`), so `T` carries exactly the principal part of the
trace there (the regular sheets are holomorphic).

The deep §VIII.3 content (the glue across fibres into a single rational function, the kirovGenus-`0`
remainder vanishing) is *not* in this file; here we prove only the local-singularity inputs the
`GlobalTrace` assembly consumes:

* **`analyticAt_traceCoeff`** (reused from `FormTraceGlobalFunction`) — the local trace coefficient is
  analytic at a regular value off the poles of `α`;
* **`meromorphicAt_traceCoeff_fibreTrace`** (reused from `FormTraceMeromorphic`) — it is meromorphic
  at any base value;
* the principal-part / `negTail` extraction (`FormTracePrincipalPart`) — the finite principal parts
  the `LaurentForm L` is assembled from.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2; rationality
  on `ℂℙ¹`).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceGlobal

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTracePrincipalPart Jacobians.Dolbeault.FormTraceInftyRecip

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The local trace coefficient as a function of the base value

For a chosen fibre `D : FibreRegularData g f b`, the trace coefficient `(fibreTrace ω₀ f D).traceCoeff`
is a function `ℂ → ℂ` (the value-chart pushforward of `α` over the fibre).  We record the two
local-singularity facts the global assembly needs at each base value. -/

/-- **The local fibre trace coefficient is analytic at a regular value off the poles of `α`.**  This
re-exports `FormTraceGlobalFunction.analyticAt_traceCoeff` with the base `b` substituted (so the
statement reads at `b`, not `(fibreTrace …).b`).  Over a regular fibre, with `g`'s chart-pullback
analytic at every fibre point, the trace coefficient is holomorphic at `b` — the analytic heart of
"`Tr_F α` is holomorphic off the finite exceptional set". -/
theorem analyticAt_traceCoeff_base (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) {b : ℂ}
    (D : FibreRegularData g f b)
    (hg : ∀ i, AnalyticAt ℂ (fun z => g ((chartAt ℂ (D.xs i)).symm z))
      ((chartAt ℂ (D.xs i)) (D.xs i))) :
    AnalyticAt ℂ (fibreTrace ω₀ f D).traceCoeff b := by
  have h := analyticAt_traceCoeff ω₀ f D hg
  rwa [fibreTrace_b] at h

/-- **Off-centre analyticity from a regular-fibre germ.**  If the global trace `T` agrees, on a full
neighbourhood of a regular value `b`, with the local trace coefficient `(fibreTrace ω₀ f D).traceCoeff`
of a regular fibre `D` over `b` (with `g`'s chart-pullback analytic at each fibre point, so `b` is off
the poles of `α`), then `T` is **analytic at `b`**.  This is the off-exceptional-set half of the
`GlobalTrace` `hT_off` obligation: at every value off the finite exceptional set the geometric trace
agrees with a regular fibre trace, which is analytic by `analyticAt_traceCoeff_base`.  *Proof.*
`AnalyticAt.congr` with `analyticAt_traceCoeff_base`. -/
theorem analyticAt_of_eventuallyEq_regularFibreTrace (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) {T : ℂ → ℂ} {b : ℂ} (D : FibreRegularData g f b)
    (hg : ∀ i, AnalyticAt ℂ (fun z => g ((chartAt ℂ (D.xs i)).symm z))
      ((chartAt ℂ (D.xs i)) (D.xs i)))
    (hT : T =ᶠ[𝓝 b] (fibreTrace ω₀ f D).traceCoeff) :
    AnalyticAt ℂ T b :=
  (analyticAt_traceCoeff_base ω₀ f D hg).congr hT.symm

/-! ### Principal-part extraction for the local trace coefficient

At a finite pole-value `b`, the local trace coefficient `(fibreTrace ω₀ f D).traceCoeff` is
meromorphic (`FormTraceMeromorphic.meromorphicAt_traceCoeff_fibreTrace`), so it has a finite
principal part — a `negTail` (`FormTracePrincipalPart.exists_principalPart_meromorphicAt`) carrying
the pole, with an analytic remainder.  This is the per-centre building block of the `LaurentForm L`
the `GlobalTrace` assembly subtracts. -/

/-- **The local trace coefficient has a finite principal part at its base value.**  At the base value
`b` of the chosen fibre, the local trace coefficient `(fibreTrace ω₀ f D).traceCoeff` is meromorphic
(`meromorphicAt_traceCoeff_fibreTrace`), so there are a degree `N`, principal-part coefficients `b'`,
and an analytic remainder `R` with `(fibreTrace ω₀ f D).traceCoeff =ᶠ[𝓝[≠] b] negTail b b' N + R`.
This is the per-centre `negTail` the `LaurentForm L` is assembled from. -/
theorem exists_principalPart_traceCoeff_fibreTrace (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) {b : ℂ} (D : FibreRegularData g f b) :
    ∃ (N : ℕ) (b' : ℕ → ℂ) (R : ℂ → ℂ), AnalyticAt ℂ R b ∧
      (fibreTrace ω₀ f D).traceCoeff =ᶠ[𝓝[≠] b] fun z => negTail b b' N z + R z :=
  exists_principalPart_meromorphicAt (meromorphicAt_traceCoeff_fibreTrace ω₀ f D)

/-- **The `∞`-fibre trace coefficient has a finite principal part at the reciprocal base `0`.**  The
`∞`-fibre analogue of `exists_principalPart_traceCoeff_fibreTrace`, via
`meromorphicAt_traceCoeff_inftyFibreTrace`.  Used for the reciprocal-chart principal part feeding
`GlobalTrace.hrecip` through `continuousAt_recipRemainder_of_vanishing`. -/
theorem exists_principalPart_traceCoeff_inftyFibreTrace (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (D : InftyFibreData g f) :
    ∃ (N : ℕ) (b' : ℕ → ℂ) (R : ℂ → ℂ), AnalyticAt ℂ R 0 ∧
      (inftyFibreTrace ω₀ f D).traceCoeff =ᶠ[𝓝[≠] 0] fun z => negTail 0 b' N z + R z :=
  exists_principalPart_meromorphicAt (meromorphicAt_traceCoeff_inftyFibreTrace ω₀ f D)

/-! ### Packaging a finite family of principal parts as a `LaurentForm`

The `GlobalTrace.L` field is a `LaurentForm` — an explicit finite family of Laurent monomials
`c·(z − a)^n` with all centres inside a fixed ball `ball 0 ρ`.  The principal-part extraction
(`exists_principalPart_meromorphicAt`) produces, per centre `cs i`, a `negTail cs i (b i) (N i)`
(`∑_{k=1}^{N i} b i k·(z − cs i)^{−k}`).  This section assembles a finite family of such `negTail`s,
one per centre, into a single `LaurentForm` whose coefficient `R` is the pointwise sum and whose
centre-image is exactly `{cs i}`.

Index: `(i : Fin m) × Fin (N i)`; the `(i, k)`-th monomial is the `(k + 1)`-th tail term at centre
`cs i`, exponent `−(k + 1)`, coefficient `b i (k + 1)`. -/

/-- **`LaurentForm` from a finite family of principal parts.**  Given `m` centres `cs : Fin m → ℂ`
all inside `ball 0 ρ` (`hcs`), per-centre degrees `N : Fin m → ℕ` and coefficients
`b : Fin m → ℕ → ℂ`, the `LaurentForm` whose `(i, k)`-th monomial is `b i (k + 1)·(z − cs i)^{−(k+1)}`
(the `negTail` of centre `i`, reindexed).  Its coefficient `R` is `∑ i, negTail (cs i) (b i) (N i)`
(`laurentOfNegTails_R`), and its centre-image is `{cs i}` (modulo the `Fin (N i)` collapse). -/
noncomputable def laurentOfNegTails {m : ℕ} (cs : Fin m → ℂ) (N : Fin m → ℕ) (b : Fin m → ℕ → ℂ)
    (ρ : ℝ) (hcs : ∀ i, cs i ∈ ball (0 : ℂ) ρ) : LaurentForm where
  ι := (i : Fin m) × Fin (N i)
  fintype_ι := inferInstance
  decEq_ι := inferInstance
  c := fun p => b p.1 (p.2.1 + 1)
  a := fun p => cs p.1
  n := fun p => -((p.2.1 : ℤ) + 1)
  ρ := ρ
  centers_mem := fun p => hcs p.1

@[simp] theorem laurentOfNegTails_a {m : ℕ} (cs : Fin m → ℂ) (N : Fin m → ℕ) (b : Fin m → ℕ → ℂ)
    (ρ : ℝ) (hcs : ∀ i, cs i ∈ ball (0 : ℂ) ρ) (p : (i : Fin m) × Fin (N i)) :
    (laurentOfNegTails cs N b ρ hcs).a p = cs p.1 := rfl

/-- **The coefficient of `laurentOfNegTails` is the sum of the `negTail`s.**  `R = ∑ i, negTail (cs i)
(b i) (N i)` — pointwise, the family of principal parts.  *Proof.*  Expand `LaurentForm.R` (a sum
over the sigma index), regroup as `∑ i, ∑ k`, and reindex each inner sum `Fin (N i) → Icc 1 (N i)` by
`k ↦ k + 1` to recover `negTail`. -/
theorem laurentOfNegTails_R {m : ℕ} (cs : Fin m → ℂ) (N : Fin m → ℕ) (b : Fin m → ℕ → ℂ)
    (ρ : ℝ) (hcs : ∀ i, cs i ∈ ball (0 : ℂ) ρ) :
    (laurentOfNegTails cs N b ρ hcs).R = fun z => ∑ i, negTail (cs i) (b i) (N i) z := by
  funext z
  show (∑ p : (i : Fin m) × Fin (N i), b p.1 (p.2.1 + 1) * (z - cs p.1) ^ (-((p.2.1 : ℤ) + 1)))
    = ∑ i, negTail (cs i) (b i) (N i) z
  simp_rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- inner sum over `Fin (N i)`, reindex `k ↦ k + 1` onto `Icc 1 (N i)`.
  show (∑ k : Fin (N i), b i (k.1 + 1) * (z - cs i) ^ (-((k.1 : ℤ) + 1)))
    = ∑ k ∈ Finset.Icc 1 (N i), b i k * (z - cs i) ^ (-(k : ℤ))
  rw [Fin.sum_univ_eq_sum_range (fun k => b i (k + 1) * (z - cs i) ^ (-((k : ℤ) + 1))) (N i)]
  rw [show Finset.Icc 1 (N i) = Finset.Ico 1 (N i + 1) by ext x; simp,
    Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show 1 + k = k + 1 from Nat.add_comm 1 k]
  push_cast
  ring

/-! ### Finite principal-part subtraction into a `LaurentForm`

`exists_finitePrincipalPart` (`FormTracePrincipalPart`) subtracts the finite principal parts of a
coefficient meromorphic at finitely many centres, but returns an *opaque* subtrahend `P` — not the
explicit `LaurentForm` the `GlobalTrace.L` field demands.  Here we re-run the per-centre extraction
(`exists_principalPart_meromorphicAt`) over a finite *indexed* family of centres `cs : Fin m → ℂ`,
collect the `negTail` data, and package it as `laurentOfNegTails`.  The result is a genuine
`LaurentForm L` with explicit centres `cs` such that `T − L.R` is analytic at every centre (the pole
is removed) — the form the `GlobalTrace.hentire` step consumes. -/

/-- **Finite principal-part subtraction into a `LaurentForm`.**  Given `m` centres `cs : Fin m → ℂ`
all inside `ball 0 ρ` and a coefficient `T` that is `MeromorphicAt` at each centre, there is a
`LaurentForm L` with centre-family `cs` (`L.a = cs ∘ ·.1`, `laurentOfNegTails_a`) such that, at each
centre `cs i`, `T − L.R` germ-agrees off `cs i` with an analytic function (the pole at `cs i` is
removed).  *Construction.*  Per centre, `exists_principalPart_meromorphicAt` gives a `negTail` and an
analytic remainder; `laurentOfNegTails` assembles the `negTail`s; `laurentOfNegTails_R` identifies
`L.R = ∑ negTail (cs i)`.  At `cs j`, the `j`-tail removes the pole and the other tails are analytic
at `cs j` (`analyticAt_negTail_of_ne`) — *provided* the centres are distinct, carried as `hcs_inj`. -/
theorem exists_laurentForm_principalPart {T : ℂ → ℂ} {m : ℕ} (cs : Fin m → ℂ) (ρ : ℝ)
    (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ) (hcs_inj : Function.Injective cs)
    (hT : ∀ i, MeromorphicAt T (cs i)) :
    ∃ L : LaurentForm, (Finset.univ.image L.a = Finset.univ.image cs) ∧
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧ (T - L.R) =ᶠ[𝓝[≠] (cs j)] R) := by
  classical
  -- Per-centre principal-part extraction.  Pad each degree to `N i + 1` (coefficient `0` on the
  -- extra index) so every centre carries at least one monomial and appears in `image L.a`.
  choose N b R hR_an hR_eq using fun i => exists_principalPart_meromorphicAt (hT i)
  -- Padded coefficients: `b i` on `[1, N i]`, `0` beyond — `negTail (cs i) bpad (N i + 1)
  -- = negTail (cs i) (b i) (N i)` since the extra term `bpad (N i + 1) = 0`.
  set bpad : Fin m → ℕ → ℂ := fun i k => if k ≤ N i then b i k else 0 with hbpad
  set Npad : Fin m → ℕ := fun i => N i + 1 with hNpad
  have hnegpad : ∀ i z, negTail (cs i) (bpad i) (Npad i) z = negTail (cs i) (b i) (N i) z := by
    intro i z
    simp only [negTail, hNpad, hbpad]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N i + 1)]
    rw [if_neg (by omega), zero_mul, add_zero]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [if_pos (Finset.mem_Icc.mp hk).2]
  refine ⟨laurentOfNegTails cs Npad bpad ρ hcs_ball, ?_, ?_⟩
  · -- centre-image: `image a = image cs`.  Each `a p = cs p.1`; conversely every centre `cs i`
    -- carries the monomial at `⟨i, 0⟩` (since `Npad i = N i + 1 ≥ 1`).
    apply Finset.Subset.antisymm
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨p, rfl⟩ := hx
      exact ⟨p.1, (laurentOfNegTails_a cs Npad bpad ρ hcs_ball p)⟩
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨i, rfl⟩ := hx
      refine ⟨⟨i, ⟨0, Nat.succ_pos (N i)⟩⟩, ?_⟩
      rw [laurentOfNegTails_a cs Npad bpad ρ hcs_ball]
  have hLR : (laurentOfNegTails cs Npad bpad ρ hcs_ball).R
      = fun z => ∑ i, negTail (cs i) (b i) (N i) z := by
    rw [laurentOfNegTails_R cs Npad bpad ρ hcs_ball]
    funext z; exact Finset.sum_congr rfl (fun i _ => hnegpad i z)
  intro j
  -- The other-centre tails, analytic at `cs j` (distinct centres).
  refine ⟨fun z => R j z - ∑ i ∈ Finset.univ.erase j, negTail (cs i) (b i) (N i) z, ?_, ?_⟩
  · -- analytic at `cs j`: `R j` analytic, minus a finite sum of off-centre `negTail`s.
    refine (hR_an j).sub (Finset.analyticAt_fun_sum _ (fun i hi => ?_))
    have hne : cs j ≠ cs i := fun h => (Finset.mem_erase.mp hi).1 (hcs_inj h.symm)
    exact analyticAt_negTail_of_ne (b i) (N i) hne
  · -- germ off `cs j`: `T − L.R = (T − negTail_j) − ∑_{i≠j} negTail_i = R j − ∑_{i≠j} negTail_i`.
    have hsplit : ∀ z, (∑ i, negTail (cs i) (b i) (N i) z)
        = negTail (cs j) (b j) (N j) z + ∑ i ∈ Finset.univ.erase j, negTail (cs i) (b i) (N i) z :=
      fun z => (Finset.add_sum_erase Finset.univ (fun i => negTail (cs i) (b i) (N i) z)
        (Finset.mem_univ j)).symm
    filter_upwards [hR_eq j] with z hz
    simp only [Pi.sub_apply, hLR, hsplit z]
    -- `T z − (negTail_j + ∑_{i≠j}) = (T z − negTail_j) − ∑_{i≠j}`, and `T z − negTail_j = R j z`.
    have hTj : T z - negTail (cs j) (b j) (N j) z = R j z := by
      have := hz; rw [this]; ring
    rw [show T z - (negTail (cs j) (b j) (N j) z
        + ∑ i ∈ Finset.univ.erase j, negTail (cs i) (b i) (N i) z)
        = (T z - negTail (cs j) (b j) (N j) z)
          - ∑ i ∈ Finset.univ.erase j, negTail (cs i) (b i) (N i) z by ring, hTj]

/-! ### The `hentire` field: the remainder `T − L.R` is entire

Combining the principal-part subtraction with the junk-freeness (continuity after pole removal): if
`T` is analytic off the centres, `L.R` is analytic off the centres (its only poles are the centres),
and at each centre `T − L.R` is continuous and germ-analytic (the pole removed by the principal-part
subtraction), then `T − L.R` is **entire** (`AnalyticOnNhd ℂ (T − L.R) univ`).  This is the
`GlobalTrace.hentire` field. -/

/-- **The remainder is entire, from junk-freeness.**  Let `L` be a `LaurentForm` whose centres are
exactly `cs` (so `L.R` is analytic off `{cs i}`), with `T − L.R` germ-analytic at each `cs j` (the
pole removed — the conclusion of `exists_laurentForm_principalPart`).  If `T` is analytic off the
centres (`hT_off`) and `T − L.R` is **continuous at each centre** (`hcont` — the junk-free condition),
then `T − L.R` is entire.  *Proof.*  Off the centres, `T − L.R` is `T` analytic minus `L.R` analytic;
at a centre, `T − L.R` is meromorphic (germ-equal to an analytic function) and continuous, hence
analytic (`MeromorphicAt.analyticAt`). -/
theorem analyticOnNhd_remainder_of_junkFree {T : ℂ → ℂ} {m : ℕ} {cs : Fin m → ℂ} {L : LaurentForm}
    (hLa : Finset.univ.image L.a = Finset.univ.image cs)
    (hLrem : ∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧ (T - L.R) =ᶠ[𝓝[≠] (cs j)] R)
    (hT_off : ∀ z, (∀ i, z ≠ cs i) → AnalyticAt ℂ T z)
    (hcont : ∀ j, ContinuousAt (T - L.R) (cs j)) :
    AnalyticOnNhd ℂ (T - L.R) Set.univ := by
  classical
  -- `L.R` is analytic off the centres: its monomials have centres in `image L.a = image cs`.
  have hLR_off : ∀ z, (∀ i, z ≠ cs i) → AnalyticAt ℂ L.R z := by
    intro z hz
    show AnalyticAt ℂ (fun w => ∑ p, L.c p * (w - L.a p) ^ L.n p) z
    refine Finset.analyticAt_fun_sum _ (fun p _ => ?_)
    refine analyticAt_const.mul ?_
    have hbase : AnalyticAt ℂ (fun w : ℂ => w - L.a p) z := analyticAt_id.sub analyticAt_const
    -- `z ≠ L.a p`: `L.a p ∈ image L.a = image cs`, so `L.a p = cs i` for some `i`, and `z ≠ cs i`.
    have hLap : L.a p ∈ Finset.univ.image cs := by
      rw [← hLa]; exact Finset.mem_image_of_mem L.a (Finset.mem_univ p)
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hLap
    obtain ⟨i, hi⟩ := hLap
    exact hbase.zpow (sub_ne_zero.mpr (hi ▸ hz i))
  intro z _
  by_cases hzc : ∃ i, z = cs i
  · -- at a centre `cs j`: meromorphic (pole removed) + continuous ⟹ analytic.
    obtain ⟨j, rfl⟩ := hzc
    obtain ⟨R, hR_an, hR_eq⟩ := hLrem j
    have hmero : MeromorphicAt (T - L.R) (cs j) := hR_an.meromorphicAt.congr hR_eq.symm
    exact hmero.analyticAt (hcont j)
  · -- off the centres: `T` analytic minus `L.R` analytic.
    push Not at hzc
    exact (hT_off z hzc).sub (hLR_off z hzc)

/-! ### The `hrecip` field: the remainder is holomorphic across `∞`

The reciprocal-chart analogue of `hentire`.  `recipCoeff h 0 = 0` always (the junk `0^{-2}` Jacobian,
`recipCoeff_zero_eval`), so `ContinuousAt (recipCoeff h) 0` is exactly "`recipCoeff h` *tends to* `0`
at `0`".  When the analytic continuation of `recipCoeff h` off `0` is an analytic function `R₀`
**vanishing at `0`** (`R₀ 0 = 0` — the holomorphic remainder has no `dζ`-term at `∞`, the kirovGenus-`0`
content), the continuity to `0` holds.  This is the `GlobalTrace.hrecip` field; it isolates `R₀ 0 = 0`
as the single irreducible `∞` obligation.  (Specialisation of
`continuousAt_recipRemainder_of_vanishing` to a trivial recip-chart principal part `negTail 0 0 0`.) -/

/-- **The remainder is holomorphic across `∞`, from a vanishing analytic continuation.**  If
`recipCoeff h` germ-agrees off `0` with an analytic function `R₀` (`hR_eq`) that vanishes at `0`
(`hR0 : R₀ 0 = 0`), then `recipCoeff h` is **continuous at `0`** (continuity to the junk value `0`).
This is the honest `GlobalTrace.hrecip` shape — `R₀ 0 = 0` is the kirovGenus-`0` "no `dζ`-term at `∞`"
input.  *Proof.*  Along `𝓝[≠] 0` agreement with the continuous `R₀`; at `0` the value is `0 = R₀ 0`. -/
theorem continuousAt_recipCoeff_of_vanishing {h : ℂ → ℂ} {R₀ : ℂ → ℂ}
    (hR_an : AnalyticAt ℂ R₀ 0) (hR0 : R₀ 0 = 0) (hR_eq : recipCoeff h =ᶠ[𝓝[≠] 0] R₀) :
    ContinuousAt (recipCoeff h) 0 := by
  have hval0 : recipCoeff h 0 = R₀ 0 := by rw [recipCoeff_zero_eval, hR0]
  rw [ContinuousAt]
  show Tendsto (recipCoeff h) (𝓝 0) (𝓝 (recipCoeff h 0))
  rw [hval0, ← nhdsNE_sup_pure (0 : ℂ), tendsto_sup]
  refine ⟨?_, ?_⟩
  · -- along `𝓝[≠] 0`: agreement off `0` with the continuous `R₀`.
    exact (hR_an.continuousAt.continuousWithinAt.tendsto).congr' hR_eq.symm
  · -- along `pure 0`: the value at `0` is `R₀ 0`.
    rw [tendsto_pure_left]
    intro s hs
    rw [hval0]
    exact mem_of_mem_nhds hs

/-! ### `hentire` over the centre set `Finset.univ.image L.a`

A variant of `analyticOnNhd_remainder_of_junkFree` phrased directly over the centre *set*
`S = Finset.univ.image L.a` (rather than an indexed family) — the form the `GlobalTrace` constructor
uses, since the `GlobalTrace.hglue_fin`/`hcenters` fields range over `Finset.univ.image L.a`. -/

/-- **The remainder is entire (centre-set form).**  `L.R` is analytic off `S = Finset.univ.image L.a`;
if `T` is analytic off `S` (`hT_off`), `T − L.R` is germ-analytic at every `p ∈ S` (`hrem`, the pole
removed), and `T − L.R` is continuous at every `p ∈ S` (`hcont`, junk-free), then `T − L.R` is entire.
This is the `GlobalTrace.hentire` field, ranging over `Finset.univ.image L.a`. -/
theorem analyticOnNhd_remainder_of_junkFree' {T : ℂ → ℂ} {L : LaurentForm}
    (hT_off : ∀ z ∉ Finset.univ.image L.a, AnalyticAt ℂ T z)
    (hrem : ∀ p ∈ Finset.univ.image L.a, ∃ R : ℂ → ℂ, AnalyticAt ℂ R p ∧ (T - L.R) =ᶠ[𝓝[≠] p] R)
    (hcont : ∀ p ∈ Finset.univ.image L.a, ContinuousAt (T - L.R) p) :
    AnalyticOnNhd ℂ (T - L.R) Set.univ := by
  classical
  -- `L.R` is analytic off `S` (its monomial centres lie in `S = image L.a`).
  have hLR_off : ∀ z ∉ Finset.univ.image L.a, AnalyticAt ℂ L.R z := by
    intro z hz
    show AnalyticAt ℂ (fun w => ∑ p, L.c p * (w - L.a p) ^ L.n p) z
    refine Finset.analyticAt_fun_sum _ (fun p _ => ?_)
    refine analyticAt_const.mul ?_
    have hbase : AnalyticAt ℂ (fun w : ℂ => w - L.a p) z := analyticAt_id.sub analyticAt_const
    have hzap : z ≠ L.a p := by
      intro h; exact hz (h ▸ Finset.mem_image_of_mem L.a (Finset.mem_univ p))
    exact hbase.zpow (sub_ne_zero.mpr hzap)
  intro z _
  by_cases hzS : z ∈ Finset.univ.image L.a
  · obtain ⟨R, hR_an, hR_eq⟩ := hrem z hzS
    have hmero : MeromorphicAt (T - L.R) z := hR_an.meromorphicAt.congr hR_eq.symm
    exact hmero.analyticAt (hcont z hzS)
  · exact (hT_off z hzS).sub (hLR_off z hzS)

end Jacobians.Dolbeault.FormTraceGlobal
