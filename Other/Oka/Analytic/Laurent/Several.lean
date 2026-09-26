/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytic.Laurent.Basic
public import Other.Oka.Analytic.DifferentiableTsum
public import Mathlib.Algebra.MvPolynomial.Basic
public import Other.Oka.Analytic.OkaRingDifferentiable

/-!
# Laurent expansions in several variables

Let `A = ∏ i, annulus (r i) (R i) ⊆ ℂⁿ` be a product of annuli, discs (`r i < 0`) and punctured
planes (`r i = 0`, `R i = ∞`). A function holomorphic on `A` is the sum of its multi-Laurent
series `∑_{k : ℤⁿ} a_k z ^ k`, converging absolutely and locally uniformly on `A`. The
coefficients are iterated circle integrals, computed on a torus `∏ i, {|z i| = ρ i}` inside `A`,
and do not depend on the torus.

## Main definitions

- `Laurent.polyAnnulus r R`: the product `∏ i, annulus (r i) (R i)`.
- `Laurent.torus ρ`: the distinguished boundary `∏ i, sphere 0 (ρ i)`.
- `Laurent.monomial k z = ∏ i, z i ^ k i`, for `k : Fin n → ℤ`.
- `Laurent.mcoeff f ρ k`: the `k`-th multi-Laurent coefficient of `f` on the torus `torus ρ`,
  defined recursively by expanding in the first variable.

## Main results

- `Laurent.norm_mcoeff_le`: the Cauchy estimate `‖a_k‖ ≤ M ∏ i, ρ i ^ (-k i)`.
- `Laurent.mcoeff_eq_of_isRadius`: independence of the torus.
- `Laurent.mcoeff_eq_zero_of_neg`: if the `i`-th factor is a disc, coefficients with
  `k i < 0` vanish.
- `Laurent.exists_summable_bound_mcoeff`: near every point of `A` the terms of the series are
  dominated by a summable sequence (absolute, locally uniform convergence), and
  `Laurent.summable_norm_mcoeff_mul`.
- `Laurent.hasSum_mcoeff`: the multi-Laurent expansion `f w = ∑ k, a_k w ^ k` on `A`.
- `Laurent.mcoeff_eq_of_hasSum`: uniqueness of the coefficients.
- `Laurent.differentiableOn_tsum_monomial`: conversely, a Laurent series converging absolutely
  on `A` whose coefficients vanish in negative degree in the disc factors is holomorphic on `A`.
- `Laurent.differentiableOn_tsum_indicator_mcoeff`: any part `∑_{k ∈ S} a_k z ^ k` of the
  expansion of `f` is holomorphic on `A`, and on the larger product obtained by filling in
  punctured factors in which all exponents in `S` are nonnegative;
  `Laurent.mcoeff_tsum_indicator_mcoeff` computes its coefficients.
- `Laurent.tendstoLocallyUniformlyOn_mcoeff`: locally uniform convergence of the expansion.
- `Laurent.exists_mvPolynomial_eq`: an entire function on `ℂⁿ` with finitely many nonzero
  coefficients is a polynomial.
-/

@[expose] public section

open Complex Metric Filter Set
open scoped Real Topology ENNReal

namespace Laurent

variable {n : ℕ}

/-- The product `∏ i, annulus (r i) (R i) ⊆ ℂⁿ` of annuli about the origin. -/
def polyAnnulus (r : Fin n → ℝ) (R : Fin n → ℝ≥0∞) : Set (Fin n → ℂ) :=
  Set.univ.pi fun i ↦ annulus (r i) (R i)

/-- The torus `∏ i, {‖z i‖ = ρ i}`, the distinguished boundary of a polydisc. -/
def torus (ρ : Fin n → ℝ) : Set (Fin n → ℂ) := Set.univ.pi fun i ↦ sphere (0 : ℂ) (ρ i)

/-- The Laurent monomial `z ^ k = ∏ i, z i ^ k i` for an exponent `k : Fin n → ℤ`. -/
noncomputable def monomial (k : Fin n → ℤ) (z : Fin n → ℂ) : ℂ := ∏ i, z i ^ k i

/-- The `k`-th multi-Laurent coefficient of `f` on the torus of polyradius `ρ`: the Laurent
coefficient of `f` in the first variable is a function of the remaining ones, whose coefficients
are computed recursively. -/
noncomputable def mcoeff : {n : ℕ} → ((Fin n → ℂ) → ℂ) → (Fin n → ℝ) → (Fin n → ℤ) → ℂ
  | 0, f, _, _ => f 0
  | _ + 1, f, ρ, k =>
    mcoeff (fun z ↦ coeff (fun ζ ↦ f (Fin.cons ζ z)) (ρ 0) (k 0)) (Fin.tail ρ) (Fin.tail k)

lemma mcoeff_zero (f : (Fin 0 → ℂ) → ℂ) (ρ : Fin 0 → ℝ) (k : Fin 0 → ℤ) :
    mcoeff f ρ k = f 0 := rfl

lemma mcoeff_succ (f : (Fin (n + 1) → ℂ) → ℂ) (ρ : Fin (n + 1) → ℝ) (k : Fin (n + 1) → ℤ) :
    mcoeff f ρ k =
      mcoeff (fun z ↦ coeff (fun ζ ↦ f (Fin.cons ζ z)) (ρ 0) (k 0)) (Fin.tail ρ) (Fin.tail k) :=
  rfl

lemma mcoeff_cons (f : (Fin (n + 1) → ℂ) → ℂ) (ρ : Fin (n + 1) → ℝ) (j : ℤ) (k : Fin n → ℤ) :
    mcoeff f ρ (Fin.cons j k) =
      mcoeff (fun z ↦ coeff (fun ζ ↦ f (Fin.cons ζ z)) (ρ 0) j) (Fin.tail ρ) k := by
  rw [mcoeff_succ, Fin.cons_zero, Fin.tail_cons]

lemma monomial_cons (j : ℤ) (k : Fin n → ℤ) (ζ : ℂ) (z : Fin n → ℂ) :
    monomial (Fin.cons j k) (Fin.cons ζ z) = ζ ^ j * monomial k z := by
  simp [monomial, Fin.prod_univ_succ]

lemma norm_monomial (k : Fin n → ℤ) (z : Fin n → ℂ) :
    ‖monomial k z‖ = ∏ i, ‖z i‖ ^ k i := by
  simp [monomial, norm_prod, norm_zpow]

lemma mem_polyAnnulus {r : Fin n → ℝ} {R : Fin n → ℝ≥0∞} {z : Fin n → ℂ} :
    z ∈ polyAnnulus r R ↔ ∀ i, z i ∈ annulus (r i) (R i) := by
  simp [polyAnnulus]

lemma isOpen_polyAnnulus (r : Fin n → ℝ) (R : Fin n → ℝ≥0∞) : IsOpen (polyAnnulus r R) :=
  isOpen_set_pi finite_univ fun _ _ ↦ isOpen_annulus

lemma cons_mem_polyAnnulus {r : Fin (n + 1) → ℝ} {R : Fin (n + 1) → ℝ≥0∞} {ζ : ℂ}
    {z : Fin n → ℂ} :
    (Fin.cons ζ z : Fin (n + 1) → ℂ) ∈ polyAnnulus r R ↔
      ζ ∈ annulus (r 0) (R 0) ∧ z ∈ polyAnnulus (Fin.tail r) (Fin.tail R) := by
  simp only [mem_polyAnnulus, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]

lemma mem_torus {ρ : Fin n → ℝ} {z : Fin n → ℂ} : z ∈ torus ρ ↔ ∀ i, ‖z i‖ = ρ i := by
  simp [torus]

lemma cons_mem_torus {ρ : Fin (n + 1) → ℝ} {ζ : ℂ} {z : Fin n → ℂ} :
    (Fin.cons ζ z : Fin (n + 1) → ℂ) ∈ torus ρ ↔ ‖ζ‖ = ρ 0 ∧ z ∈ torus (Fin.tail ρ) := by
  simp only [mem_torus, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]

lemma torus_subset_polyAnnulus {r : Fin n → ℝ} {R : Fin n → ℝ≥0∞} {ρ : Fin n → ℝ}
    (hρ : ∀ i, IsRadius (r i) (R i) (ρ i)) : torus ρ ⊆ polyAnnulus r R := fun z hz ↦
  mem_polyAnnulus.2 fun i ↦ sphere_subset_annulus (hρ i) (by
    rw [mem_sphere_zero_iff_norm]; exact mem_torus.1 hz i)

lemma differentiable_cons_right (ζ : ℂ) :
    Differentiable ℂ fun z : Fin n → ℂ ↦ (Fin.cons ζ z : Fin (n + 1) → ℂ) := by
  refine differentiable_pi.2 fun i ↦ Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simpa using differentiable_apply (𝕜 := ℂ) j

lemma differentiable_cons_left (z : Fin n → ℂ) :
    Differentiable ℂ fun ζ : ℂ ↦ (Fin.cons ζ z : Fin (n + 1) → ℂ) := by
  refine differentiable_pi.2 fun i ↦ Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp

variable {r : Fin n → ℝ} {R : Fin n → ℝ≥0∞} {ρ : Fin n → ℝ}

/-- The multi-Laurent coefficients only depend on the values on the torus. -/
theorem mcoeff_congr {f g : (Fin n → ℂ) → ℂ} (hρ : ∀ i, 0 ≤ ρ i) (h : EqOn f g (torus ρ))
    (k : Fin n → ℤ) : mcoeff f ρ k = mcoeff g ρ k := by
  induction n with
  | zero => exact h (by simp [torus])
  | succ n ih =>
    rw [mcoeff_succ, mcoeff_succ]
    refine ih (fun i ↦ hρ i.succ) (fun z hz ↦ coeff_congr (hρ 0) (fun ζ hζ ↦ h ?_) _) _
    rw [cons_mem_torus]
    exact ⟨by simpa using hζ, hz⟩

/-- The Cauchy estimate for multi-Laurent coefficients. -/
theorem norm_mcoeff_le {f : (Fin n → ℂ) → ℂ} (hρ : ∀ i, 0 < ρ i) {M : ℝ}
    (hM : ∀ z ∈ torus ρ, ‖f z‖ ≤ M) (k : Fin n → ℤ) :
    ‖mcoeff f ρ k‖ ≤ M * ∏ i, ρ i ^ (-k i) := by
  induction n generalizing M with
  | zero => simpa [mcoeff_zero] using hM 0 (by simp [torus])
  | succ n ih =>
    rw [mcoeff_succ, Fin.prod_univ_succ, ← mul_assoc]
    refine ih (fun i ↦ hρ i.succ) (fun z hz ↦ norm_coeff_le (hρ 0) (fun ζ hζ ↦ hM _ ?_) _) _
    rw [cons_mem_torus]
    exact ⟨by simpa using hζ, hz⟩

lemma differentiableOn_slice {r : Fin (n + 1) → ℝ} {R : Fin (n + 1) → ℝ≥0∞}
    {f : (Fin (n + 1) → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (polyAnnulus r R)) {z : Fin n → ℂ}
    (hz : z ∈ polyAnnulus (Fin.tail r) (Fin.tail R)) :
    DifferentiableOn ℂ (fun ζ ↦ f (Fin.cons ζ z)) (annulus (r 0) (R 0)) :=
  hf.comp (differentiable_cons_left z).differentiableOn fun _ hζ ↦
    cons_mem_polyAnnulus.2 ⟨hζ, hz⟩

/-- The Laurent coefficient of `f` in the first variable is holomorphic in the remaining
variables. -/
theorem differentiableOn_coeff_cons {r : Fin (n + 1) → ℝ} {R : Fin (n + 1) → ℝ≥0∞}
    {f : (Fin (n + 1) → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (polyAnnulus r R)) {ρ₀ : ℝ}
    (hρ₀ : IsRadius (r 0) (R 0) ρ₀) (j : ℤ) :
    DifferentiableOn ℂ (fun z ↦ coeff (fun ζ ↦ f (Fin.cons ζ z)) ρ₀ j)
      (polyAnnulus (Fin.tail r) (Fin.tail R)) := by
  intro x₀ hx₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_polyAnnulus _ _) x₀ hx₀
  set δ := ε / 2
  have hδ : 0 < δ := by positivity
  set P : Set (Fin n → ℂ) := Set.univ.pi fun _ ↦ closedBall (0 : ℂ) δ
  have hP : ∀ x ∈ P, x₀ + x ∈ polyAnnulus (Fin.tail r) (Fin.tail R) := by
    intro x hx
    apply hball
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    have : x ∈ closedBall (0 : Fin n → ℂ) δ := by rwa [closedBall_pi _ hδ.le]
    rw [mem_closedBall, dist_zero_right] at this
    linarith [show δ = ε / 2 from rfl]
  have hmem : ∀ x ∈ P, ∀ ζ : ℂ, ‖ζ‖ = ρ₀ →
      (Fin.cons ζ (x₀ + x) : Fin (n + 1) → ℂ) ∈ polyAnnulus r R := fun x hx ζ hζ ↦
    cons_mem_polyAnnulus.2 ⟨sphere_subset_annulus hρ₀ (by simpa using hζ), hP x hx⟩
  have hshift : Differentiable ℂ fun x : Fin n → ℂ ↦ x₀ + x := by fun_prop
  have hcont : Continuous fun p : P × ℝ ↦
      circleMap 0 ρ₀ p.2 ^ (-j - 1) *
        f (Fin.cons (circleMap 0 ρ₀ p.2) (x₀ + (p.1 : Fin n → ℂ))) := by
    refine Continuous.mul ?_ ?_
    · exact ((continuous_circleMap 0 ρ₀).comp continuous_snd).zpow₀ _
        fun p ↦ Or.inl (circleMap_ne_center hρ₀.pos.ne')
    · refine hf.continuousOn.comp_continuous (Continuous.finCons
        ((continuous_circleMap 0 ρ₀).comp continuous_snd)
        (continuous_const.add (continuous_subtype_val.comp continuous_fst))) fun p ↦ ?_
      exact hmem p.1 p.1.2 _ (by simp [abs_of_pos hρ₀.pos])
  have ha := analyticAt_circleIntegral (m := n) hρ₀.pos hδ
    (G := fun x ζ ↦ ζ ^ (-j - 1) * f (Fin.cons ζ (x₀ + x)))
    (fun ζ hζ ↦ (differentiableOn_const _).mul (hf.comp
      ((differentiable_cons_right ζ).comp hshift).differentiableOn fun x hx ↦ hmem x hx ζ hζ))
    hcont
  have ha' : AnalyticAt ℂ (fun x ↦ coeff (fun ζ ↦ f (Fin.cons ζ (x₀ + x))) ρ₀ j) 0 :=
    analyticAt_const.mul ha
  exact (analyticAt_of_shift ha').differentiableAt.differentiableWithinAt

/-- The multi-Laurent coefficients do not depend on the choice of the torus. -/
theorem mcoeff_eq_of_isRadius {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (polyAnnulus r R))
    {ρ ρ' : Fin n → ℝ} (hρ : ∀ i, IsRadius (r i) (R i) (ρ i))
    (hρ' : ∀ i, IsRadius (r i) (R i) (ρ' i)) (k : Fin n → ℤ) : mcoeff f ρ k = mcoeff f ρ' k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [mcoeff_succ, mcoeff_succ f ρ']
    rw [mcoeff_congr (ρ := Fin.tail ρ) (fun i ↦ (hρ i.succ).pos.le)
      (g := fun z ↦ coeff (fun ζ ↦ f (Fin.cons ζ z)) (ρ' 0) (k 0)) fun z hz ↦
        coeff_eq_of_isRadius (differentiableOn_slice hf
          (torus_subset_polyAnnulus (fun i ↦ hρ i.succ) hz)) (hρ 0) (hρ' 0) _]
    exact ih (differentiableOn_coeff_cons hf (hρ' 0) (k 0)) (fun i ↦ hρ i.succ)
      (fun i ↦ hρ' i.succ) _

/-- If the `i`-th factor of the product is a disc, the multi-Laurent coefficients of negative
degree in the `i`-th variable vanish. -/
theorem mcoeff_eq_zero_of_neg {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (polyAnnulus r R))
    (hρ : ∀ i, IsRadius (r i) (R i) (ρ i)) {k : Fin n → ℤ} {i : Fin n} (hr : r i < 0)
    (hk : k i < 0) : mcoeff f ρ k = 0 := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [mcoeff_succ]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · have h0 : ∀ z ∈ torus (Fin.tail ρ), ‖coeff (fun ζ ↦ f (Fin.cons ζ z)) (ρ 0) (k 0)‖ ≤ 0 :=
        fun z hz ↦ by
          rw [coeff_eq_zero_of_neg (differentiableOn_slice hf
            (torus_subset_polyAnnulus (fun i ↦ hρ i.succ) hz)) hr (hρ 0) hk, norm_zero]
      simpa using norm_mcoeff_le (ρ := Fin.tail ρ) (fun i ↦ (hρ i.succ).pos) h0 (Fin.tail k)
    · exact ih (differentiableOn_coeff_cons hf (hρ 0) (k 0)) (fun i ↦ hρ i.succ) (i := i) hr hk

/-- A product of nonnegative summable families on `ℤ` is summable on `ℤⁿ`. -/
lemma summable_prod_fin {β : Fin n → ℤ → ℝ} (h0 : ∀ i k, 0 ≤ β i k)
    (hs : ∀ i, Summable (β i)) : Summable fun k : Fin n → ℤ ↦ ∏ i, β i (k i) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    rw [← (Fin.consEquiv fun _ ↦ ℤ).summable_iff]
    have := (hs 0).mul_of_nonneg (ih (β := fun i ↦ β i.succ) (fun i k ↦ h0 _ _) fun i ↦ hs _)
      (h0 0) fun k ↦ Finset.prod_nonneg fun i _ ↦ h0 _ _
    refine this.congr fun p ↦ ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ]

lemma zpow_neg_mul_zpow_le_of_le {s x t : ℝ} (hs : 0 < s) (hx : 0 ≤ x) (hxt : x ≤ t)
    (m : ℕ) : s ^ (-(m : ℤ)) * x ^ (m : ℤ) ≤ (t / s) ^ m := by
  rw [zpow_neg, zpow_natCast, zpow_natCast, div_pow, inv_mul_eq_div]
  gcongr

lemma zpow_neg_mul_zpow_le_of_ge {s x t : ℝ} (hs : 0 < s) (ht : 0 < t) (htx : t ≤ x)
    (m : ℕ) : s ^ (-(-(m : ℤ))) * x ^ (-(m : ℤ)) ≤ (s / t) ^ m := by
  rw [neg_neg, zpow_neg, zpow_natCast, zpow_natCast, div_pow, ← div_eq_mul_inv]
  gcongr

/-- The Weierstrass bound behind the absolute and locally uniform convergence of the
multi-Laurent series: near every point of the product of annuli, its terms are dominated by a
summable family. -/
theorem exists_summable_bound_mcoeff {f : (Fin n → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (polyAnnulus r R)) (hρ : ∀ i, IsRadius (r i) (R i) (ρ i))
    {w : Fin n → ℂ} (hw : w ∈ polyAnnulus r R) :
    ∃ u : (Fin n → ℤ) → ℝ, Summable u ∧
      ∃ V ∈ 𝓝 w, ∀ k, ∀ z ∈ V, ‖mcoeff f ρ k * monomial k z‖ ≤ u k := by
  rw [mem_polyAnnulus] at hw
  have hi : ∀ i, ∃ a b t₁ t₂ : ℝ, IsRadius (r i) (R i) a ∧ IsRadius (r i) (R i) b ∧ a ≤ b ∧
      ‖w i‖ < t₂ ∧ t₂ < b ∧ 0 < t₁ ∧ (w i = 0 ∨ (a < t₁ ∧ t₁ < ‖w i‖)) := by
    intro i
    obtain ⟨b, hb, hwb⟩ := exists_isRadius_gt (hw i)
    rcases eq_or_ne (w i) 0 with h0 | h0
    · exact ⟨b, b, 1, (‖w i‖ + b) / 2, hb, hb, le_rfl, by linarith, by linarith, one_pos,
        Or.inl h0⟩
    · obtain ⟨a, ha, haw⟩ := exists_isRadius_lt (hw i) h0
      exact ⟨a, b, (a + ‖w i‖) / 2, (‖w i‖ + b) / 2, ha, hb, by linarith, by linarith,
        by linarith, by linarith [ha.pos], Or.inr ⟨by linarith, by linarith⟩⟩
  choose a b t₁ t₂ ha hb hab hwt₂ ht₂b ht₁ hwt₁ using hi
  set K : Set (Fin n → ℂ) := Set.univ.pi fun i ↦ closedBall (0 : ℂ) (b i) \ ball 0 (a i)
  have hKc : IsCompact K := isCompact_univ_pi fun i ↦ (isCompact_closedBall _ _).diff isOpen_ball
  have hKA : K ⊆ polyAnnulus r R := fun z hz ↦ mem_polyAnnulus.2 fun i ↦ by
    obtain ⟨h1, h2⟩ := hz i (Set.mem_univ i)
    rw [mem_closedBall_zero_iff] at h1
    rw [mem_ball_zero_iff, not_lt] at h2
    exact mem_annulus_of_le (ha i) (hb i) h2 h1
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hf.continuousOn.mono hKA)
  have hbK : (fun i ↦ (b i : ℂ)) ∈ K := fun i _ ↦ by
    refine ⟨by simp [Complex.norm_real, abs_of_pos (hb i).pos], ?_⟩
    simp [Complex.norm_real, abs_of_pos (hb i).pos, hab i]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ hbK)
  set q₂ : Fin n → ℝ := fun i ↦ t₂ i / b i
  set q₁ : Fin n → ℝ := fun i ↦ if w i = 0 then 0 else a i / t₁ i
  have hq₂ : ∀ i, 0 ≤ q₂ i ∧ q₂ i < 1 := fun i ↦
    ⟨div_nonneg (by linarith [norm_nonneg (w i), hwt₂ i]) (hb i).pos.le,
      (div_lt_one (hb i).pos).2 (ht₂b i)⟩
  have hq₁ : ∀ i, 0 ≤ q₁ i ∧ q₁ i < 1 := fun i ↦ by
    simp only [q₁]
    split_ifs with h
    · exact ⟨le_rfl, one_pos⟩
    · obtain ⟨h1, -⟩ := (hwt₁ i).resolve_left h
      exact ⟨div_nonneg (ha i).pos.le (ht₁ i).le, (div_lt_one (ht₁ i)).2 h1⟩
  set β : Fin n → ℤ → ℝ := fun i k ↦ q₂ i ^ k.natAbs + q₁ i ^ k.natAbs
  have hβ0 : ∀ i k, 0 ≤ β i k := fun i k ↦
    add_nonneg (pow_nonneg (hq₂ i).1 _) (pow_nonneg (hq₁ i).1 _)
  have hβs : ∀ i, Summable (β i) := fun i ↦
    (summable_pow_natAbs (hq₂ i).1 (hq₂ i).2).add (summable_pow_natAbs (hq₁ i).1 (hq₁ i).2)
  refine ⟨fun k ↦ M * ∏ i, β i (k i), (summable_prod_fin hβ0 hβs).mul_left M,
    {z | ∀ i, ‖z i‖ < t₂ i ∧ (w i = 0 ∨ t₁ i < ‖z i‖)}, ?_, fun k z hz ↦ ?_⟩
  · refine Filter.eventually_all.2 fun i ↦ ?_
    have h2 : ∀ᶠ z in 𝓝 w, ‖z i‖ < t₂ i :=
      (isOpen_lt ((continuous_apply i).norm) continuous_const).mem_nhds (hwt₂ i)
    rcases hwt₁ i with h0 | ⟨-, h1⟩
    · filter_upwards [h2] with z hz using ⟨hz, Or.inl h0⟩
    · have h1' : ∀ᶠ z in 𝓝 w, t₁ i < ‖z i‖ :=
        (isOpen_lt continuous_const ((continuous_apply i).norm)).mem_nhds h1
      filter_upwards [h2, h1'] with z hz hz' using ⟨hz, Or.inr hz'⟩
  have hu0 : 0 ≤ M * ∏ i, β i (k i) := mul_nonneg hM0 (Finset.prod_nonneg fun i _ ↦ hβ0 _ _)
  by_cases hbad : ∃ i, w i = 0 ∧ k i < 0
  · obtain ⟨i, hwi, hki⟩ := hbad
    have hr : r i < 0 := by simpa [hwi] using (hw i).1
    rw [mcoeff_eq_zero_of_neg hf hρ hr hki, zero_mul, norm_zero]
    exact hu0
  simp only [not_exists, not_and, not_lt] at hbad
  set σ : Fin n → ℝ := fun i ↦ if 0 ≤ k i then b i else a i
  have hσ : ∀ i, IsRadius (r i) (R i) (σ i) := fun i ↦ by
    simp only [σ]; split_ifs; exacts [hb i, ha i]
  have hσK : torus σ ⊆ K := fun z hz i _ ↦ by
    have := mem_torus.1 hz i
    simp only [σ] at this
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff, this]; split_ifs; exacts [le_rfl, hab i]
    · rw [mem_ball_zero_iff, not_lt, this]; split_ifs; exacts [hab i, le_rfl]
  have hcoeff := norm_mcoeff_le (fun i ↦ (hσ i).pos) (fun z hz ↦ hM z (hσK hz)) k
  rw [mcoeff_eq_of_isRadius hf hρ hσ, norm_mul, norm_monomial]
  calc ‖mcoeff f σ k‖ * ∏ i, ‖z i‖ ^ k i
      ≤ (M * ∏ i, σ i ^ (-k i)) * ∏ i, ‖z i‖ ^ k i :=
        mul_le_mul_of_nonneg_right hcoeff (Finset.prod_nonneg fun i _ ↦ zpow_nonneg
          (norm_nonneg _) _)
    _ = M * ∏ i, (σ i ^ (-k i) * ‖z i‖ ^ k i) := by rw [Finset.prod_mul_distrib, mul_assoc]
    _ ≤ M * ∏ i, β i (k i) := by
      refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ ↦ ?_) fun i _ ↦ ?_) hM0
      · exact mul_nonneg (zpow_nonneg (hσ i).pos.le _) (zpow_nonneg (norm_nonneg _) _)
      · obtain ⟨hz2, hz1⟩ := hz i
        rcases le_or_gt 0 (k i) with hk | hk
        · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hk
          simp only [σ, if_pos hk, β, hm, Int.natAbs_natCast]
          exact (zpow_neg_mul_zpow_le_of_le (hb i).pos (norm_nonneg _) hz2.le m).trans
            (le_add_of_nonneg_right (pow_nonneg (hq₁ i).1 _))
        · obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat hk.le
          have hwi : w i ≠ 0 := fun h ↦ (not_lt.2 (hbad i h)) hk
          replace hz1 := hz1.resolve_left hwi
          simp only [σ, if_neg (not_le.2 hk), β, hm, Int.natAbs_neg, Int.natAbs_natCast, q₁,
            if_neg hwi]
          exact (zpow_neg_mul_zpow_le_of_ge (ha i).pos (ht₁ i) hz1.le m).trans
            (le_add_of_nonneg_left (pow_nonneg (hq₂ i).1 _))

/-- The multi-Laurent series converges absolutely on the product of annuli. -/
theorem summable_norm_mcoeff_mul {f : (Fin n → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (polyAnnulus r R)) (hρ : ∀ i, IsRadius (r i) (R i) (ρ i))
    {w : Fin n → ℂ} (hw : w ∈ polyAnnulus r R) :
    Summable fun k ↦ ‖mcoeff f ρ k * monomial k w‖ := by
  obtain ⟨u, hu, V, hV, hle⟩ := exists_summable_bound_mcoeff hf hρ hw
  exact hu.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun k ↦ hle k w (mem_of_mem_nhds hV)

lemma mcoeff_mul_monomial_cons (f : (Fin (n + 1) → ℂ) → ℂ) (ρ : Fin (n + 1) → ℝ) (j : ℤ)
    (k : Fin n → ℤ) (w : Fin (n + 1) → ℂ) :
    mcoeff f ρ (Fin.cons j k) * monomial (Fin.cons j k) w =
      mcoeff (fun z ↦ coeff (fun ζ ↦ f (Fin.cons ζ z)) (ρ 0) j) (Fin.tail ρ) k *
        monomial k (Fin.tail w) * w 0 ^ j := by
  rw [mcoeff_cons]
  conv_lhs => rw [← Fin.cons_self_tail w]
  rw [monomial_cons]
  ring

lemma norm_mul_monomial_of_mem_torus (b : ℂ) (k : Fin n → ℤ) {z : Fin n → ℂ}
    (hz : z ∈ torus ρ) : ‖b * monomial k z‖ = ‖b‖ * ∏ i, ρ i ^ k i := by
  rw [norm_mul, norm_monomial]
  congr 1
  exact Finset.prod_congr rfl fun i _ ↦ by rw [mem_torus.1 hz i]

/-- **Multi-Laurent expansion**: a function holomorphic on a product of annuli is the sum of its
multi-Laurent series there. -/
theorem hasSum_mcoeff {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (polyAnnulus r R))
    (hρ : ∀ i, IsRadius (r i) (R i) (ρ i)) {w : Fin n → ℂ} (hw : w ∈ polyAnnulus r R) :
    HasSum (fun k ↦ mcoeff f ρ k * monomial k w) (f w) := by
  induction n with
  | zero =>
    obtain rfl : w = 0 := Subsingleton.elim _ _
    simp [mcoeff_zero, monomial]
  | succ n ih =>
    have hw' := cons_mem_polyAnnulus.1
      (show (Fin.cons (w 0) (Fin.tail w) : Fin (n + 1) → ℂ) ∈ _ by rwa [Fin.cons_self_tail])
    have h1 : HasSum (fun j : ℤ ↦
        coeff (fun ζ ↦ f (Fin.cons ζ (Fin.tail w))) (ρ 0) j * w 0 ^ j) (f w) := by
      have := hasSum_coeff (differentiableOn_slice hf hw'.2) (hρ 0) hw'.1
      simpa only [Fin.cons_self_tail] using this
    have h2 : ∀ j, HasSum (fun k ↦
        mcoeff (fun z ↦ coeff (fun ζ ↦ f (Fin.cons ζ z)) (ρ 0) j) (Fin.tail ρ) k *
          monomial k (Fin.tail w) * w 0 ^ j)
        (coeff (fun ζ ↦ f (Fin.cons ζ (Fin.tail w))) (ρ 0) j * w 0 ^ j) := fun j ↦
      (ih (differentiableOn_coeff_cons hf (hρ 0) j) (ρ := Fin.tail ρ) (fun i ↦ hρ i.succ)
        hw'.2).mul_right _
    have e : ((fun k ↦ mcoeff f ρ k * monomial k w) ∘ Fin.consEquiv fun _ ↦ ℤ) =
        fun p : ℤ × (Fin n → ℤ) ↦
          mcoeff (fun z ↦ coeff (fun ζ ↦ f (Fin.cons ζ z)) (ρ 0) p.1) (Fin.tail ρ) p.2 *
            monomial p.2 (Fin.tail w) * w 0 ^ p.1 :=
      funext fun p ↦ mcoeff_mul_monomial_cons f ρ p.1 p.2 w
    have hs : Summable fun k ↦ mcoeff f ρ k * monomial k w :=
      (summable_norm_mcoeff_mul hf hρ hw).of_norm
    rw [← (Fin.consEquiv fun _ ↦ ℤ).summable_iff, e] at hs
    rw [h1.unique (hs.hasSum.prod_fiberwise h2), ← (Fin.consEquiv fun _ ↦ ℤ).hasSum_iff, e]
    exact hs.hasSum

/-- **Uniqueness of multi-Laurent coefficients**: if `f` is the sum of an absolutely convergent
Laurent series on the torus of polyradius `ρ`, its coefficients are the multi-Laurent
coefficients of `f`. -/
theorem mcoeff_eq_of_hasSum {f : (Fin n → ℂ) → ℂ} (hρ : ∀ i, 0 < ρ i)
    {b : (Fin n → ℤ) → ℂ} (hb : Summable fun k ↦ ‖b k‖ * ∏ i, ρ i ^ k i)
    (hf : ∀ z ∈ torus ρ, HasSum (fun k ↦ b k * monomial k z) (f z)) (k : Fin n → ℤ) :
    mcoeff f ρ k = b k := by
  induction n with
  | zero =>
    have h2 := hasSum_single (f := fun k : Fin 0 → ℤ ↦ b k * monomial k 0) k
      fun k' hk' ↦ absurd (Subsingleton.elim k' k) hk'
    rw [mcoeff_zero, (hf 0 (by simp [torus])).unique h2]
    simp [monomial]
  | succ n ih =>
    rw [← Fin.cons_self_tail k, mcoeff_cons]
    set e := Fin.consEquiv fun _ : Fin (n + 1) ↦ ℤ
    have hbp : Summable fun p : ℤ × (Fin n → ℤ) ↦
        ‖b (Fin.cons p.1 p.2)‖ * (ρ 0 ^ p.1 * ∏ i, Fin.tail ρ i ^ p.2 i) := by
      rw [← e.summable_iff] at hb
      refine hb.congr fun p ↦ ?_
      simp [e, Fin.consEquiv, Fin.prod_univ_succ, Fin.tail]
    have hbp0 : 0 ≤ fun p : ℤ × (Fin n → ℤ) ↦
        ‖b (Fin.cons p.1 p.2)‖ * (ρ 0 ^ p.1 * ∏ i, Fin.tail ρ i ^ p.2 i) := fun p ↦
      mul_nonneg (norm_nonneg _) (mul_nonneg (zpow_nonneg (hρ 0).le _)
        (Finset.prod_nonneg fun i _ ↦ zpow_nonneg (hρ i.succ).le _))
    have hinner : ∀ j, Summable fun k' : Fin n → ℤ ↦
        ‖b (Fin.cons j k')‖ * ∏ i, Fin.tail ρ i ^ k' i := fun j ↦ by
      have := (hbp.prod_factor j).mul_left (ρ 0 ^ j)⁻¹
      refine this.congr fun k' ↦ ?_
      have : ρ 0 ^ j ≠ 0 := (zpow_pos (hρ 0) _).ne'
      field_simp
    have hinner' : ∀ j, ∀ z' ∈ torus (Fin.tail ρ),
        Summable fun k' : Fin n → ℤ ↦ b (Fin.cons j k') * monomial k' z' := fun j z' hz' ↦
      Summable.of_norm ((hinner j).congr fun k' ↦
        (norm_mul_monomial_of_mem_torus _ _ hz').symm)
    have hc : ∀ j, ∀ z' ∈ torus (Fin.tail ρ), coeff (fun ζ ↦ f (Fin.cons ζ z')) (ρ 0) j =
        ∑' k', b (Fin.cons j k') * monomial k' z' := by
      intro j z' hz'
      refine coeff_eq_of_hasSum (hρ 0) (b := fun j ↦ ∑' k', b (Fin.cons j k') * monomial k' z')
        ?_ (fun ζ hζ ↦ ?_) j
      · refine ((summable_prod_of_nonneg hbp0).1 hbp).2.of_nonneg_of_le
          (fun j ↦ mul_nonneg (norm_nonneg _) (zpow_nonneg (hρ 0).le _)) fun j ↦ ?_
        calc ‖∑' k', b (Fin.cons j k') * monomial k' z'‖ * ρ 0 ^ j
            ≤ (∑' k', ‖b (Fin.cons j k') * monomial k' z'‖) * ρ 0 ^ j :=
              mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm
                ((hinner j).congr fun k' ↦ (norm_mul_monomial_of_mem_torus _ _ hz').symm))
                (zpow_nonneg (hρ 0).le _)
          _ = ∑' k', ‖b (Fin.cons j k')‖ * (ρ 0 ^ j * ∏ i, Fin.tail ρ i ^ k' i) := by
              rw [← tsum_mul_right]
              refine tsum_congr fun k' ↦ ?_
              rw [norm_mul_monomial_of_mem_torus _ _ hz']
              ring
      · have hz : (Fin.cons ζ z' : Fin (n + 1) → ℂ) ∈ torus ρ :=
          cons_mem_torus.2 ⟨by simpa using hζ, hz'⟩
        have h1 := hf _ hz
        rw [← e.hasSum_iff] at h1
        refine h1.prod_fiberwise fun j ↦ ?_
        have e2 : (fun k' : Fin n → ℤ ↦
            ((fun k ↦ b k * monomial k (Fin.cons ζ z')) ∘ e) (j, k')) =
            fun k' ↦ b (Fin.cons j k') * monomial k' z' * ζ ^ j := by
          funext k'
          simp only [Function.comp_apply, e, Fin.consEquiv, Equiv.coe_fn_mk, monomial_cons]
          ring
        rw [e2]
        exact ((hinner' j z' hz').hasSum).mul_right _
    refine ih (ρ := Fin.tail ρ) (fun i ↦ hρ i.succ) (b := fun k' ↦ b (Fin.cons (k 0) k'))
      (hinner (k 0)) (fun z' hz' ↦ ?_) (Fin.tail k)
    rw [hc (k 0) z' hz']
    exact (hinner' (k 0) z' hz').hasSum

/-- The multi-Laurent series converges locally uniformly on the product of annuli. -/
theorem tendstoLocallyUniformlyOn_mcoeff {f : (Fin n → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (polyAnnulus r R)) (hρ : ∀ i, IsRadius (r i) (R i) (ρ i)) :
    TendstoLocallyUniformlyOn
      (fun (s : Finset (Fin n → ℤ)) (z : Fin n → ℂ) ↦ ∑ k ∈ s, mcoeff f ρ k * monomial k z) f
      atTop (polyAnnulus r R) := by
  intro U hU w hw
  obtain ⟨u, hu, V, hV, hle⟩ := exists_summable_bound_mcoeff hf hρ hw
  refine ⟨polyAnnulus r R ∩ V, inter_mem_nhdsWithin _ hV, ?_⟩
  have h := ((tendstoUniformlyOn_tsum hu fun k z hz ↦ hle k z hz).mono
    inter_subset_right).congr_right fun z hz ↦ (hasSum_mcoeff hf hρ hz.1).tsum_eq
  exact h U hU

lemma zpow_le_zpow_of_neg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {k : ℤ} (hk : k < 0) :
    b ^ k ≤ a ^ k := by
  obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hk.le
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  exact inv_anti₀ (pow_pos ha m) (pow_le_pow_left₀ ha.le hab m)

/-- **Holomorphy of Laurent series**: a Laurent series which converges absolutely at every point
of a product of annuli, and whose coefficients of negative degree in the disc factors vanish,
has a holomorphic sum there. -/
theorem differentiableOn_tsum_monomial {b : (Fin n → ℤ) → ℂ}
    (hb0 : ∀ k i, r i < 0 → k i < 0 → b k = 0)
    (hsum : ∀ w ∈ polyAnnulus r R, Summable fun k ↦ ‖b k‖ * ∏ i, ‖w i‖ ^ k i) :
    DifferentiableOn ℂ (fun z ↦ ∑' k, b k * monomial k z) (polyAnnulus r R) := by
  refine differentiableOn_tsum_of_locally_summable (isOpen_polyAnnulus r R) (fun k ↦ ?_)
    fun w hw ↦ ?_
  · by_cases hk : b k = 0
    · simp only [hk, zero_mul]
      exact differentiableOn_const 0
    refine (differentiableOn_const _).mul fun z hz ↦ ?_
    change DifferentiableWithinAt ℂ (fun z : Fin n → ℂ ↦ ∏ i, z i ^ k i) _ z
    classical
    refine (HasFDerivAt.finsetProd (u := Finset.univ)
      (g := fun (i : Fin n) (z : Fin n → ℂ) ↦ z i ^ k i)
      fun i _ ↦ (DifferentiableAt.hasFDerivAt ?_)).differentiableAt.differentiableWithinAt
    refine (differentiableAt_apply (𝕜 := ℂ) i z).zpow ?_
    rcases le_or_gt 0 (k i) with h | h
    · exact Or.inr h
    · have hr : 0 ≤ r i := not_lt.1 fun hr ↦ hk (hb0 k i hr h)
      exact Or.inl (norm_pos_iff.1 (hr.trans_lt ((mem_polyAnnulus.1 hz) i).1))
  · rw [mem_polyAnnulus] at hw
    have hi : ∀ i, ∃ T₁ T₂ : ℝ, IsRadius (r i) (R i) T₁ ∧ IsRadius (r i) (R i) T₂ ∧
        ‖w i‖ < T₂ ∧ (r i < 0 ∨ T₁ < ‖w i‖) := by
      intro i
      obtain ⟨T₂, h₂, hw₂⟩ := exists_isRadius_gt (hw i)
      rcases lt_or_ge (r i) 0 with hr | hr
      · exact ⟨T₂, T₂, h₂, h₂, hw₂, Or.inl hr⟩
      · have hw0 : w i ≠ 0 := norm_pos_iff.1 (hr.trans_lt (hw i).1)
        obtain ⟨T₁, h₁, hw₁⟩ := exists_isRadius_lt (hw i) hw0
        exact ⟨T₁, T₂, h₁, h₂, hw₂, Or.inr hw₁⟩
    choose T₁ T₂ h₁ h₂ hw₂ hw₁ using hi
    set τ : (Fin n → Bool) → Fin n → ℝ := fun s i ↦ if s i then T₂ i else T₁ i
    have hτ : ∀ s i, IsRadius (r i) (R i) (τ s i) := fun s i ↦ by
      simp only [τ]; split_ifs; exacts [h₂ i, h₁ i]
    have hτmem : ∀ s, (fun i ↦ (τ s i : ℂ)) ∈ polyAnnulus r R := fun s ↦
      mem_polyAnnulus.2 fun i ↦ sphere_subset_annulus (hτ s i)
        (by simp [Complex.norm_real, abs_of_pos (hτ s i).pos])
    refine ⟨fun k ↦ ∑ s, ‖b k‖ * ∏ i, τ s i ^ k i, summable_sum fun s _ ↦ ?_,
      {z | ∀ i, ‖z i‖ < T₂ i ∧ (r i < 0 ∨ T₁ i < ‖z i‖)}, ?_, fun k z hz ↦ ?_⟩
    · refine (hsum _ (hτmem s)).congr fun k ↦ ?_
      simp [Complex.norm_real, abs_of_pos (hτ s _).pos]
    · refine Filter.eventually_all.2 fun i ↦ ?_
      have h2 : ∀ᶠ z in 𝓝 w, ‖z i‖ < T₂ i :=
        (isOpen_lt ((continuous_apply i).norm) continuous_const).mem_nhds (hw₂ i)
      rcases hw₁ i with h0 | h1
      · filter_upwards [h2] with z hz using ⟨hz, Or.inl h0⟩
      · have h1' : ∀ᶠ z in 𝓝 w, T₁ i < ‖z i‖ :=
          (isOpen_lt continuous_const ((continuous_apply i).norm)).mem_nhds h1
        filter_upwards [h2, h1'] with z hz hz' using ⟨hz, Or.inr hz'⟩
    · by_cases hk : b k = 0
      · simp [hk]
      set s₀ : Fin n → Bool := fun i ↦ decide (0 ≤ k i)
      rw [norm_mul, norm_monomial]
      refine le_trans ?_ (Finset.single_le_sum (f := fun s ↦ ‖b k‖ * ∏ i, τ s i ^ k i)
        (fun s _ ↦ mul_nonneg (norm_nonneg _)
          (Finset.prod_nonneg fun i _ ↦ zpow_nonneg (hτ s i).pos.le _)) (Finset.mem_univ s₀))
      refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod
        (fun i _ ↦ zpow_nonneg (norm_nonneg _) _) fun i _ ↦ ?_) (norm_nonneg _)
      obtain ⟨hz2, hz1⟩ := hz i
      rcases le_or_gt 0 (k i) with hki | hki
      · simp only [τ, s₀, decide_eq_true hki, if_true]
        exact zpow_le_zpow_left₀ hki (norm_nonneg _) hz2.le
      · have hr : ¬ r i < 0 := fun hr ↦ hk (hb0 k i hr hki)
        simp only [τ, s₀, decide_eq_false (not_le.2 hki)]
        exact zpow_le_zpow_of_neg (h₁ i).pos (hz1.resolve_left hr).le hki

/-- Any part `∑_{k ∈ S} a_k z ^ k` of the multi-Laurent expansion of a function `f` holomorphic
on `polyAnnulus r R` is holomorphic on `polyAnnulus r' R` for any inner radii `r'` (e.g. filling
in some factors to discs, `r' i < 0`), provided all exponents in `S` are nonnegative in the
factors where `r'` differs from `r`. For `r' = r` this holds for every `S`. -/
theorem differentiableOn_tsum_indicator_mcoeff {f : (Fin n → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (polyAnnulus r R)) (hρ : ∀ i, IsRadius (r i) (R i) (ρ i))
    (S : Set (Fin n → ℤ)) {r' : Fin n → ℝ}
    (hS : ∀ k ∈ S, ∀ i, r' i ≠ r i → 0 ≤ k i) :
    DifferentiableOn ℂ (fun z ↦ ∑' k, S.indicator (mcoeff f ρ) k * monomial k z)
      (polyAnnulus r' R) := by
  refine differentiableOn_tsum_monomial (fun k i hr hk ↦ ?_) fun w hw ↦ ?_
  · by_cases hkS : k ∈ S
    · rw [Set.indicator_of_mem hkS]
      by_cases hne : r' i = r i
      · exact mcoeff_eq_zero_of_neg hf hρ (hne ▸ hr) hk
      · exact absurd (hS k hkS i hne) (not_le.2 hk)
    · exact Set.indicator_of_notMem hkS _
  · rw [mem_polyAnnulus] at hw
    have hi : ∀ i, ∃ w' : ℂ, w' ∈ annulus (r i) (R i) ∧ (r' i ≠ r i → ‖w i‖ ≤ ‖w'‖) ∧
        (r' i = r i → w' = w i) := by
      intro i
      by_cases h : r' i = r i
      · exact ⟨w i, h ▸ hw i, fun h' ↦ absurd h h', fun _ ↦ rfl⟩
      · obtain ⟨t, ht, hwt⟩ := exists_isRadius_gt_of_enorm_lt (hρ i) (hw i).2
        refine ⟨t, sphere_subset_annulus ht (by simp [Complex.norm_real, abs_of_pos ht.pos]),
          fun _ ↦ ?_, fun h' ↦ absurd h' h⟩
        simpa [Complex.norm_real, abs_of_pos ht.pos] using hwt.le
    choose w' hw'A hw'le hw'eq using hi
    have hs := summable_norm_mcoeff_mul hf hρ (w := w') (mem_polyAnnulus.2 hw'A)
    refine hs.of_nonneg_of_le (fun k ↦ mul_nonneg (norm_nonneg _)
      (Finset.prod_nonneg fun i _ ↦ zpow_nonneg (norm_nonneg _) _)) fun k ↦ ?_
    by_cases hkS : k ∈ S
    · rw [Set.indicator_of_mem hkS, norm_mul, norm_monomial]
      refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod
        (fun i _ ↦ zpow_nonneg (norm_nonneg _) _) fun i _ ↦ ?_) (norm_nonneg _)
      by_cases h : r' i = r i
      · rw [hw'eq i h]
      · exact zpow_le_zpow_left₀ (hS k hkS i h) (norm_nonneg _) (hw'le i h)
    · rw [Set.indicator_of_notMem hkS, norm_zero, zero_mul]
      exact norm_nonneg _

/-- The multi-Laurent coefficients of a part `∑_{k ∈ S} a_k z ^ k` of the expansion of `f` are
those of `f` in `S` and vanish outside `S`. -/
theorem mcoeff_tsum_indicator_mcoeff {f : (Fin n → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (polyAnnulus r R)) (hρ : ∀ i, IsRadius (r i) (R i) (ρ i))
    (S : Set (Fin n → ℤ)) (k : Fin n → ℤ) :
    mcoeff (fun z ↦ ∑' k, S.indicator (mcoeff f ρ) k * monomial k z) ρ k =
      S.indicator (mcoeff f ρ) k := by
  have hρz : (fun i ↦ (ρ i : ℂ)) ∈ torus ρ :=
    mem_torus.2 fun i ↦ by simp [Complex.norm_real, abs_of_pos (hρ i).pos]
  have hs := summable_norm_mcoeff_mul hf hρ (torus_subset_polyAnnulus hρ hρz)
  have hb : Summable fun k ↦ ‖S.indicator (mcoeff f ρ) k‖ * ∏ i, ρ i ^ k i := by
    refine hs.of_nonneg_of_le (fun k ↦ mul_nonneg (norm_nonneg _)
      (Finset.prod_nonneg fun i _ ↦ zpow_nonneg (hρ i).pos.le _)) fun k ↦ ?_
    rw [norm_mul_monomial_of_mem_torus _ _ hρz]
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ ↦
      zpow_nonneg (hρ i).pos.le _)
    by_cases hkS : k ∈ S
    · rw [Set.indicator_of_mem hkS]
    · rw [Set.indicator_of_notMem hkS, norm_zero]
      exact norm_nonneg _
  refine mcoeff_eq_of_hasSum (fun i ↦ (hρ i).pos) hb (fun z hz ↦ ?_) k
  exact (Summable.of_norm (hb.congr fun k ↦
    (norm_mul_monomial_of_mem_torus _ _ hz).symm)).hasSum

/-- A function holomorphic on `ℂⁿ` whose multi-Laurent coefficients vanish outside a finite set
of exponents is a polynomial. -/
theorem exists_mvPolynomial_eq {f : (Fin n → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (hρ : ∀ i, 0 < ρ i) (s : Finset (Fin n → ℤ)) (hs : ∀ k ∉ s, mcoeff f ρ k = 0) :
    ∃ p : MvPolynomial (Fin n) ℂ, ∀ z, f z = MvPolynomial.eval z p := by
  have hρA : ∀ i, IsRadius ((fun _ ↦ (-1 : ℝ)) i) ((fun _ ↦ (⊤ : ℝ≥0∞)) i) (ρ i) :=
    fun i ↦ ⟨hρ i, by linarith [hρ i], ENNReal.ofReal_lt_top⟩
  have hmem : ∀ z : Fin n → ℂ, z ∈ polyAnnulus (fun _ ↦ -1) fun _ ↦ ⊤ := fun z ↦
    mem_polyAnnulus.2 fun i ↦ ⟨by linarith [norm_nonneg (z i)], enorm_lt_top⟩
  have hfA : DifferentiableOn ℂ f (polyAnnulus (fun _ ↦ -1) fun _ ↦ ⊤) := hf.differentiableOn
  refine ⟨∑ k ∈ s, MvPolynomial.C (mcoeff f ρ k) * ∏ i, MvPolynomial.X i ^ (k i).toNat,
    fun z ↦ ?_⟩
  have h := hasSum_mcoeff hfA hρA (hmem z)
  rw [h.unique (hasSum_sum_of_ne_finset_zero fun k hk ↦ by rw [hs k hk, zero_mul])]
  simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, map_pow, MvPolynomial.eval_X]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : mcoeff f ρ k = 0
  · simp [hk]
  · congr 1
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    have hki : 0 ≤ k i :=
      not_lt.1 fun h ↦ hk (mcoeff_eq_zero_of_neg hfA hρA (i := i) (by norm_num) h)
    rw [← zpow_natCast, Int.toNat_of_nonneg hki]

end Laurent

end
