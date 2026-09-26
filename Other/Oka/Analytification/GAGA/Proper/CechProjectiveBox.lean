/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.CechProjectiveAn
public import Other.Oka.Analytification.GAGA.CousinCoordinate

/-!
# The analytic Čech complex of `𝒪(d)` on `ℙⁿ × U`

This is the version with holomorphic parameters of `Other/Oka/Analytification/GAGA/CechProjectiveAn.lean`.
Let `U ⊆ ℂᵐ` be open. We work in homogeneous coordinates `z ∈ ℂⁿ⁺¹` and parameters `y ∈ U`. For
`I : Finset (Fin (n + 1))` the space `holP d U I` of functions holomorphic on `V I × U`,
homogeneous of degree `d : ℤ` in `z` and vanishing outside `V I × U` is the space of sections
of `𝒪(d)` over `U_I × U ⊆ ℙⁿ × U`.

A section is determined by its Laurent coefficients in `z`, which are now functions of `y`
(`toPCoeff`). The parts of the expansion with a fixed negative support `N` are holomorphic on
the bigger domain `V N × U` (`differentiableOn_tsum_proj_toCoeff`): locally in `y` this follows
from the joint Laurent expansion in `(z, y)` (`exists_local_expansion`). Hence the coefficient
families of all sections lie in one subgroup `pcoeffSpace d U`, stable under the projections
onto fixed negative supports, and the monomially graded complex of
`Other/Oka/AlgebraicTopology/SimplexCochain.lean` computes the cohomology, exactly as for `U = pt`.

## Main definitions

- `CechProjectiveBox.holP d U I`, `CechProjectiveBox.holPRes`: sections of `𝒪(d)` over
  `U_I × U`, and restriction.
- `CechProjectiveBox.PCochain`, `CechProjectiveBox.holPD`: the Čech complex of the standard cover
  of `ℙⁿ`, times `U`.
- `CechProjectiveBox.holPAug e`: the augmentation from families, indexed by the exponents of the
  monomials of degree `e`, of holomorphic functions on `U`.

## Main results

- `CechProjectiveBox.differentiableOn_toCoeff_slice`: the Laurent coefficients in `z` of a
  function holomorphic on `V I × U` are holomorphic in `y`.
- `CechProjectiveBox.holPD_holPD`: `d ∘ d = 0`.
- `CechProjectiveBox.holPD_exact`: exactness in degree `q = p + 1` if `q > n`, `q < n`, or
  `d > -n - 1`.
- `CechProjectiveBox.holPAug_injective`, `CechProjectiveBox.holPAug_exact`: for `d = e ≥ 0`,
  `H⁰` is the free `𝒪(U)`-module on the monomials of degree `e`: the `0`-cocycles are exactly the
  functions `∑_{|k| = e} c_k(y) zᵏ` with `c_k` holomorphic on `U`.
- `CechProjectiveBox.holPD_zero_injective`: `H⁰ = 0` for `d < 0` (if `n ≥ 1`).
-/

@[expose] public section

open Complex Set Laurent SimplexCochain CechProjectiveAn Metric Filter
open scoped ENNReal Topology

namespace CechProjectiveBox

/-! ### Laurent expansions in `(z, u)` -/

section Append

variable {a b : ℕ}

lemma monomial_append (k : Fin a → ℤ) (l : Fin b → ℤ) (z : Fin a → ℂ) (u : Fin b → ℂ) :
    monomial (Fin.append k l) (Fin.append z u) = monomial k z * monomial l u := by
  simp [monomial, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

lemma append_mem_polyAnnulus {r : Fin a → ℝ} {r' : Fin b → ℝ} {R : Fin a → ℝ≥0∞}
    {R' : Fin b → ℝ≥0∞} {z : Fin a → ℂ} {u : Fin b → ℂ} :
    Fin.append z u ∈ polyAnnulus (Fin.append r r') (Fin.append R R') ↔
      z ∈ polyAnnulus r R ∧ u ∈ polyAnnulus r' R' := by
  simp only [mem_polyAnnulus, Fin.forall_fin_add, Fin.append_left, Fin.append_right]

lemma mem_polyAnnulus_disc {δ : ℝ} (hδ : 0 < δ) {u : Fin b → ℂ} :
    u ∈ polyAnnulus (fun _ ↦ -1) (fun _ ↦ ENNReal.ofReal δ) ↔ u ∈ ball 0 δ := by
  rw [mem_ball_zero_iff, pi_norm_lt_iff hδ, mem_polyAnnulus]
  refine forall_congr' fun j ↦ ?_
  rw [mem_annulus, enorm_lt_iff_ofReal_lt, ENNReal.ofReal_lt_ofReal_iff hδ]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨by linarith [norm_nonneg (u j)], h⟩⟩

lemma differentiable_append :
    Differentiable ℂ fun p : (Fin a → ℂ) × (Fin b → ℂ) ↦ Fin.append p.1 p.2 := by
  refine differentiable_pi.2 fun i ↦ ?_
  induction i using Fin.addCases with
  | left i =>
    simp only [Fin.append_left]
    fun_prop
  | right j =>
    simp only [Fin.append_right]
    fun_prop

end Append

variable {n m : ℕ}

/-- **Local joint Laurent expansion.** Let `f` be holomorphic on `V I × B`, `B ⊆ ℂᵐ` open, and
`y₀ ∈ B`. Near `y₀`, `f (z, y₀ + u) = ∑_{k, l} C (k, l) zᵏ uˡ` (absolutely) for `z ∈ V I`, the
coefficients vanishing unless `l ≥ 0`, and every part `∑_{negSupp k = N} C (k, l) zᵏ uˡ` with
`N ⊆ I` is holomorphic on `V N × ball 0 δ`. -/
theorem exists_local_expansion {B : Set (Fin m → ℂ)} (hB : IsOpen B) {I : Finset (Fin (n + 1))}
    {f : (Fin (n + 1) → ℂ) × (Fin m → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (V I ×ˢ B))
    {y₀ : Fin m → ℂ} (hy₀ : y₀ ∈ B) :
    ∃ δ > 0, ∃ C : (Fin (n + 1) → ℤ) × (Fin m → ℤ) → ℂ,
      (∀ u ∈ ball (0 : Fin m → ℂ) δ, y₀ + u ∈ B) ∧
      (∀ q : (Fin (n + 1) → ℤ) × (Fin m → ℤ), ∀ j, q.2 j < 0 → C q = 0) ∧
      (∀ z ∈ V I, ∀ u ∈ ball (0 : Fin m → ℂ) δ,
        Summable (fun q ↦ ‖C q * (monomial q.1 z * monomial q.2 u)‖) ∧
        HasSum (fun q ↦ C q * (monomial q.1 z * monomial q.2 u)) (f (z, y₀ + u))) ∧
      (∀ N ⊆ I, DifferentiableOn ℂ (fun p : (Fin (n + 1) → ℂ) × (Fin m → ℂ) ↦
        ∑' q : (Fin (n + 1) → ℤ) × (Fin m → ℤ),
          (if negSupp q.1 = N then C q else 0) * (monomial q.1 p.1 * monomial q.2 p.2))
        (V N ×ˢ ball (0 : Fin m → ℂ) δ)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hB y₀ hy₀
  have hsub : ∀ u ∈ ball (0 : Fin m → ℂ) ε, y₀ + u ∈ B := fun u hu ↦ hball (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    simpa using hu)
  set r₁ : Fin (n + 1 + m) → ℝ := Fin.append (radii I) fun _ ↦ -1
  set R₁ : Fin (n + 1 + m) → ℝ≥0∞ := Fin.append (fun _ ↦ ⊤) fun _ ↦ ENNReal.ofReal ε
  set ρ₁ : Fin (n + 1 + m) → ℝ := Fin.append (fun _ ↦ 1) fun _ ↦ ε / 2
  have hρ : ∀ i, IsRadius (r₁ i) (R₁ i) (ρ₁ i) := by
    intro i
    induction i using Fin.addCases with
    | left i =>
      simp only [r₁, R₁, ρ₁, Fin.append_left]
      exact isRadius_one I i
    | right j =>
      simp only [r₁, R₁, ρ₁, Fin.append_right]
      exact ⟨by positivity, by linarith, (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)⟩
  set φ : (Fin (n + 1 + m) → ℂ) → (Fin (n + 1) → ℂ) × (Fin m → ℂ) := fun x ↦
    (fun i ↦ x (Fin.castAdd m i), y₀ + fun j ↦ x (Fin.natAdd (n + 1) j))
  have hφ : Differentiable ℂ φ := by
    refine Differentiable.prodMk (differentiable_pi.2 fun i ↦ differentiable_apply _)
      ((differentiable_const _).add (differentiable_pi.2 fun j ↦ differentiable_apply _))
  have hφa : ∀ z u, φ (Fin.append z u) = (z, y₀ + u) := fun z u ↦ by
    simp [φ, Fin.append_left, Fin.append_right]
  have hmem : ∀ z u, Fin.append z u ∈ polyAnnulus r₁ R₁ ↔ z ∈ V I ∧ u ∈ ball 0 ε := fun z u ↦ by
    rw [append_mem_polyAnnulus, mem_polyAnnulus_disc hε, V_eq_polyAnnulus]
  have hA : MapsTo φ (polyAnnulus r₁ R₁) (V I ×ˢ B) := by
    intro x hx
    rw [← Fin.append_castAdd_natAdd (f := x)] at hx ⊢
    rw [hφa]
    obtain ⟨h1, h2⟩ := (hmem _ _).1 hx
    exact ⟨h1, hsub _ h2⟩
  have hg : DifferentiableOn ℂ (f ∘ φ) (polyAnnulus r₁ R₁) := hf.comp hφ.differentiableOn hA
  set c := mcoeff (f ∘ φ) ρ₁
  set e := Fin.appendEquiv (α := ℤ) (n + 1) m
  have he : ∀ q, e q = Fin.append q.1 q.2 := fun q ↦ rfl
  refine ⟨ε, hε, fun q ↦ c (e q), hsub, fun q j hq ↦ ?_, fun z hz u hu ↦ ?_, fun N hN ↦ ?_⟩
  · exact mcoeff_eq_zero_of_neg hg hρ (i := Fin.natAdd (n + 1) j)
      (by simp [r₁, Fin.append_right]) (by simpa [he, Fin.append_right] using hq)
  · have hx := (hmem z u).2 ⟨hz, hu⟩
    refine ⟨?_, ?_⟩
    · refine ((summable_norm_mcoeff_mul hg hρ hx).comp_injective e.injective).congr fun q ↦ ?_
      simp only [Function.comp_apply, he, monomial_append]
      rfl
    · convert e.hasSum_iff.2 (hasSum_mcoeff hg hρ hx) using 1
      · ext q
        simp only [Function.comp_apply, he, monomial_append]
        rfl
      · rw [Function.comp_apply, hφa]
  · set S : Set (Fin (n + 1 + m) → ℤ) := {κ | negSupp (fun i ↦ κ (Fin.castAdd m i)) = N}
    set r₂ : Fin (n + 1 + m) → ℝ := Fin.append (radii N) fun _ ↦ -1
    have hS : ∀ κ ∈ S, ∀ i, r₂ i ≠ r₁ i → 0 ≤ κ i := by
      intro κ hκ i hi
      induction i using Fin.addCases with
      | left i =>
        simp only [r₂, r₁, Fin.append_left, radii] at hi
        have hiN : i ∉ N := fun h ↦ hi (by simp [h, hN h])
        by_contra hneg
        exact hiN (hκ ▸ mem_negSupp.2 (not_le.1 hneg))
      | right j => simp [r₂, r₁, Fin.append_right] at hi
    have hG := differentiableOn_tsum_indicator_mcoeff hg hρ S hS
    refine (hG.comp differentiable_append.differentiableOn fun p hp ↦ ?_).congr fun p _ ↦ ?_
    · rw [append_mem_polyAnnulus, mem_polyAnnulus_disc hε, ← V_eq_polyAnnulus]
      exact hp
    · simp only [Function.comp_apply]
      rw [← e.tsum_eq]
      refine tsum_congr fun q ↦ ?_
      rw [he, monomial_append, Set.indicator_apply]
      simp only [S, mem_setOf_eq, Fin.append_left]
      rfl

section Expansion

variable {I : Finset (Fin (n + 1))} {C : (Fin (n + 1) → ℤ) × (Fin m → ℤ) → ℂ} {u : Fin m → ℂ}
  {h : (Fin (n + 1) → ℂ) → ℂ}

lemma summable_norm_fiber
    (hC : ∀ z ∈ V I, Summable (fun q ↦ ‖C q * (monomial q.1 z * monomial q.2 u)‖) ∧
      HasSum (fun q ↦ C q * (monomial q.1 z * monomial q.2 u)) (h z))
    (k : Fin (n + 1) → ℤ) : Summable fun l ↦ ‖C (k, l) * monomial l u‖ := by
  simpa [monomial_one] using (hC _ (const_mem_V I one_ne_zero)).1.prod_factor k

/-- The Laurent coefficients in `z` of `h z = ∑_{k, l} C (k, l) zᵏ uˡ` are `∑_l C (k, l) uˡ`. -/
lemma toCoeff_eq_tsum
    (hC : ∀ z ∈ V I, Summable (fun q ↦ ‖C q * (monomial q.1 z * monomial q.2 u)‖) ∧
      HasSum (fun q ↦ C q * (monomial q.1 z * monomial q.2 u)) (h z)) :
    toCoeff h = fun k ↦ ∑' l, C (k, l) * monomial l u := by
  refine toCoeff_eq_of_hasSum ?_ fun z hz ↦ ?_
  · have h1 := (hC _ (const_mem_V I one_ne_zero)).1
    refine h1.prod.of_nonneg_of_le (fun k ↦ mul_nonneg (norm_nonneg _)
      (Finset.prod_nonneg fun _ _ ↦ zpow_nonneg (norm_nonneg _) _)) fun k ↦ ?_
    simp only [norm_one, one_zpow, Finset.prod_const_one, mul_one, monomial_one, one_mul]
    exact norm_tsum_le_tsum_norm (summable_norm_fiber hC k)
  · refine (hC z (torus_subset_V I hz)).2.prod_fiberwise fun k ↦ ?_
    have := (Summable.of_norm (summable_norm_fiber hC k)).hasSum.mul_right (monomial k z)
    have e : (fun l ↦ C (k, l) * (monomial (k, l).1 z * monomial (k, l).2 u)) =
        fun l ↦ C (k, l) * monomial l u * monomial k z := funext fun l ↦ by dsimp only; ring
    rw [e]
    exact this

/-- The part with negative support `N` of the Laurent expansion in `z` of
`h z = ∑_{k, l} C (k, l) zᵏ uˡ`, evaluated at `w ∈ V N`. -/
lemma tsum_proj_toCoeff_eq
    (hC : ∀ z ∈ V I, Summable (fun q ↦ ‖C q * (monomial q.1 z * monomial q.2 u)‖) ∧
      HasSum (fun q ↦ C q * (monomial q.1 z * monomial q.2 u)) (h z))
    {N : Finset (Fin (n + 1))} {w : Fin (n + 1) → ℂ} (hw : w ∈ V N) :
    ∑' k, proj N (toCoeff h) k * monomial k w =
      ∑' q : (Fin (n + 1) → ℤ) × (Fin m → ℤ),
        (if negSupp q.1 = N then C q else 0) * (monomial q.1 w * monomial q.2 u) := by
  classical
  rw [toCoeff_eq_tsum hC]
  let w' : Fin (n + 1) → ℂ := fun j ↦ if j ∈ I ∧ j ∉ N then ((‖w j‖ + 1 : ℝ) : ℂ) else w j
  have hw' : w' ∈ V I := fun j hj ↦ by
    by_cases hjN : j ∈ N
    · simp [w', hjN, hw j hjN]
    · simp only [w', hj, hjN, not_false_eq_true, and_self, if_true, ne_eq,
        Complex.ofReal_eq_zero]
      positivity
  have hmono : ∀ k, negSupp k = N → ‖monomial k w‖ ≤ ‖monomial k w'‖ := by
    intro k hk
    rw [norm_monomial, norm_monomial]
    refine Finset.prod_le_prod (fun i _ ↦ zpow_nonneg (norm_nonneg _) _) fun i _ ↦ ?_
    by_cases hi : i ∈ I ∧ i ∉ N
    · have : 0 ≤ k i := not_lt.1 fun h ↦ hi.2 (hk ▸ mem_negSupp.2 h)
      simp only [w', hi, not_false_eq_true, and_self, if_true, Complex.norm_real,
        Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      exact zpow_le_zpow_left₀ this (norm_nonneg _) (by linarith)
    · simp only [w', hi, if_false, le_refl]
  have hs : Summable fun q : (Fin (n + 1) → ℤ) × (Fin m → ℤ) ↦
      ‖(if negSupp q.1 = N then C q else 0) * (monomial q.1 w * monomial q.2 u)‖ := by
    refine (hC w' hw').1.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun q ↦ ?_
    split_ifs with hq
    · rw [norm_mul, norm_mul, norm_mul, norm_mul]
      gcongr
      exact hmono q.1 hq
    · simp only [zero_mul, norm_zero]
      positivity
  refine HasSum.tsum_eq ((Summable.of_norm hs).hasSum.prod_fiberwise fun k ↦ ?_)
  simp only [proj_apply]
  split_ifs with hk
  · have := (Summable.of_norm (summable_norm_fiber hC k)).hasSum.mul_right (monomial k w)
    have e : (fun l ↦ C (k, l) * (monomial k w * monomial l u)) =
        fun l ↦ C (k, l) * monomial l u * monomial k w := funext fun l ↦ by ring
    rw [e]
    exact this
  · simp only [zero_mul]
    exact hasSum_zero

end Expansion

variable {I : Finset (Fin (n + 1))} {B : Set (Fin m → ℂ)}
  {f : (Fin (n + 1) → ℂ) × (Fin m → ℂ) → ℂ}

/-- **Parts of Laurent expansions with parameters.** Let `f` be holomorphic on `V I × B`. For
`N ⊆ I`, the part with negative support `N` of the Laurent expansion of `f` in `z` is holomorphic
on `V N × B`. -/
theorem differentiableOn_tsum_proj_toCoeff (hB : IsOpen B) (hf : DifferentiableOn ℂ f (V I ×ˢ B))
    {N : Finset (Fin (n + 1))} (hN : N ⊆ I) :
    DifferentiableOn ℂ (fun p ↦ ∑' k, proj N (toCoeff fun z ↦ f (z, p.2)) k * monomial k p.1)
      (V N ×ˢ B) := by
  rintro ⟨w₀, y₀⟩ ⟨hw₀, hy₀⟩
  obtain ⟨δ, hδ, C, -, -, hC, hG⟩ := exists_local_expansion hB hf hy₀
  set D := V N ×ˢ ball y₀ δ
  have hD : IsOpen D := (isOpen_V N).prod isOpen_ball
  have hpD : (w₀, y₀) ∈ D := ⟨hw₀, mem_ball_self hδ⟩
  set τ : (Fin (n + 1) → ℂ) × (Fin m → ℂ) → (Fin (n + 1) → ℂ) × (Fin m → ℂ) :=
    fun p ↦ (p.1, p.2 - y₀)
  have hτ : MapsTo τ D (V N ×ˢ ball 0 δ) := fun p hp ↦
    ⟨hp.1, by simpa [mem_ball, dist_eq_norm] using hp.2⟩
  have hGD := (hG N hN).comp (by fun_prop : Differentiable ℂ τ).differentiableOn hτ
  refine ((hGD.differentiableAt (hD.mem_nhds hpD)).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hD.mem_nhds hpD] with p hp
  have hu : p.2 - y₀ ∈ ball (0 : Fin m → ℂ) δ := (hτ hp).2
  have hC' : ∀ z ∈ V I, Summable (fun q ↦ ‖C q * (monomial q.1 z * monomial q.2 (p.2 - y₀))‖) ∧
      HasSum (fun q ↦ C q * (monomial q.1 z * monomial q.2 (p.2 - y₀))) (f (z, p.2)) := by
    intro z hz
    simpa only [add_sub_cancel] using hC z hz _ hu
  exact tsum_proj_toCoeff_eq hC' hp.1

/-- **Laurent coefficients with parameters are holomorphic**: for `f` holomorphic on `V I × B`,
the Laurent coefficients of `z ↦ f (z, y)` are holomorphic functions of `y ∈ B`. -/
theorem differentiableOn_toCoeff_slice (hB : IsOpen B) (hf : DifferentiableOn ℂ f (V I ×ˢ B))
    (k : Fin (n + 1) → ℤ) : DifferentiableOn ℂ (fun y ↦ toCoeff (fun z ↦ f (z, y)) k) B := by
  intro y₀ hy₀
  obtain ⟨δ, hδ, C, -, hC0, hC, -⟩ := exists_local_expansion hB hf hy₀
  set g : (Fin m → ℂ) → ℂ := fun u ↦ ∑' l, C (k, l) * monomial l u
  have hpa : polyAnnulus (fun _ ↦ (-1 : ℝ)) (fun _ ↦ ENNReal.ofReal δ) = ball (0 : Fin m → ℂ) δ :=
    Set.ext fun _ ↦ mem_polyAnnulus_disc hδ
  have hg : DifferentiableOn ℂ g (ball 0 δ) := by
    rw [← hpa]
    refine differentiableOn_tsum_monomial (fun l j _ hl ↦ hC0 (k, l) j hl) fun u hu ↦ ?_
    rw [hpa] at hu
    refine (summable_norm_fiber (fun z hz ↦ hC z hz u hu) k).congr fun l ↦ ?_
    rw [norm_mul, norm_monomial]
  have hD : ball y₀ δ ∈ 𝓝 y₀ := ball_mem_nhds y₀ hδ
  have hτ : MapsTo (fun y ↦ y - y₀) (ball y₀ δ) (ball 0 δ) := fun y hy ↦ by
    simpa [mem_ball, dist_eq_norm] using hy
  have hgD := hg.comp (by fun_prop : Differentiable ℂ fun y : Fin m → ℂ ↦ y - y₀).differentiableOn
    hτ
  refine ((hgD.differentiableAt hD).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [hD] with y hy
  have hC' : ∀ z ∈ V I, Summable (fun q ↦ ‖C q * (monomial q.1 z * monomial q.2 (y - y₀))‖) ∧
      HasSum (fun q ↦ C q * (monomial q.1 z * monomial q.2 (y - y₀))) (f (z, y)) := by
    intro z hz
    simpa only [add_sub_cancel] using hC z hz _ (hτ hy)
  exact congrFun (toCoeff_eq_tsum hC') k

/-! ### Sections of `𝒪(d)` over `U_I × U` -/

open TopologicalSpace

/-- The space of functions holomorphic on `V I × U`, homogeneous of degree `d` in `z` there, and
vanishing outside `V I × U`: the sections of `𝒪(d)` over `U_I × U ⊆ ℙⁿ × U`. -/
def holP (d : ℤ) (U : Opens (Fin m → ℂ)) (I : Finset (Fin (n + 1))) :
    Submodule ℂ ((Fin (n + 1) → ℂ) × (Fin m → ℂ) → ℂ) where
  carrier := {f | DifferentiableOn ℂ f (V I ×ˢ (U : Set (Fin m → ℂ))) ∧
    (∀ z ∈ V I, ∀ y ∈ U, ∀ c : ℂ, c ≠ 0 → f (c • z, y) = c ^ d * f (z, y)) ∧
    ∀ p ∉ V I ×ˢ (U : Set (Fin m → ℂ)), f p = 0}
  add_mem' {f g} hf hg := ⟨hf.1.add hg.1, fun z hz y hy c hc ↦ by
    simp [hf.2.1 z hz y hy c hc, hg.2.1 z hz y hy c hc, mul_add], fun p hp ↦ by
    simp [hf.2.2 p hp, hg.2.2 p hp]⟩
  zero_mem' := ⟨differentiableOn_const 0, by simp, by simp⟩
  smul_mem' a f hf := ⟨hf.1.const_smul a, fun z hz y hy c hc ↦ by
    simp only [Pi.smul_apply, smul_eq_mul, hf.2.1 z hz y hy c hc]; ring, fun p hp ↦ by
    simp [hf.2.2 p hp]⟩

variable {d : ℤ} {U : Opens (Fin m → ℂ)} {J : Finset (Fin (n + 1))}

/-- Restriction `holP d U J → holP d U I` along `V I × U ⊆ V J × U`, for `J ⊆ I`. -/
noncomputable def holPRes (d : ℤ) (U : Opens (Fin m → ℂ)) (h : J ⊆ I) :
    holP d U J →ₗ[ℂ] holP d U I where
  toFun f := ⟨(V I ×ˢ (U : Set (Fin m → ℂ))).indicator f,
    ((f.2.1.mono (prod_mono (V_anti h) subset_rfl)).congr fun p hp ↦ indicator_of_mem hp _),
    fun z hz y hy c hc ↦ by
      rw [indicator_of_mem (mk_mem_prod (smul_mem_V hc hz) hy),
        indicator_of_mem (mk_mem_prod hz hy),
        f.2.2.1 z (V_anti h hz) y hy c hc], fun p hp ↦ indicator_of_notMem hp _⟩
  map_add' f g := by
    ext p
    by_cases hp : p ∈ V I ×ˢ (U : Set (Fin m → ℂ)) <;> simp [hp]
  map_smul' a f := by
    ext p
    by_cases hp : p ∈ V I ×ˢ (U : Set (Fin m → ℂ)) <;> simp [hp]

lemma coe_holPRes (h : J ⊆ I) (f : holP d U J) :
    (holPRes d U h f : (Fin (n + 1) → ℂ) × (Fin m → ℂ) → ℂ) =
      (V I ×ˢ (U : Set (Fin m → ℂ))).indicator f :=
  rfl

lemma slice_mem (hf : f ∈ holP d U I) {y : Fin m → ℂ} (hy : y ∈ U) :
    (fun z ↦ f (z, y)) ∈ hol d I :=
  ⟨hf.1.comp (by fun_prop : Differentiable ℂ fun z : Fin (n + 1) → ℂ ↦ (z, y)).differentiableOn
    fun _ hz ↦ ⟨hz, hy⟩, fun z hz c hc ↦ hf.2.1 z hz y hy c hc,
    fun _ hz ↦ hf.2.2 _ fun h ↦ hz h.1⟩

lemma slice_eq_zero (hf : f ∈ holP d U I) {y : Fin m → ℂ} (hy : y ∉ U) :
    (fun z ↦ f (z, y)) = 0 :=
  funext fun _ ↦ hf.2.2 _ fun h ↦ hy h.2

/-! ### Coefficient families with parameters -/

variable (n m) in
/-- Families of Laurent coefficients `k ↦ aₖ` depending on a parameter `y ∈ ℂᵐ`. -/
abbrev PCoeff : Type := (Fin (n + 1) → ℤ) → (Fin m → ℂ) → ℂ

/-- The coefficient family at the parameter `y`. -/
def aty (a : PCoeff n m) (y : Fin m → ℂ) : Coeff n := fun k ↦ a k y

@[simp] lemma aty_zero (y : Fin m → ℂ) : aty (0 : PCoeff n m) y = 0 := rfl

lemma aty_add (a b : PCoeff n m) (y : Fin m → ℂ) : aty (a + b) y = aty a y + aty b y := rfl

lemma aty_smul (c : ℂ) (a : PCoeff n m) (y : Fin m → ℂ) : aty (c • a) y = c • aty a y := rfl

/-- The projection onto the monomials with negative support `N`. -/
def pproj (N : Finset (Fin (n + 1))) : PCoeff n m →ₗ[ℂ] PCoeff n m where
  toFun a k y := if negSupp k = N then a k y else 0
  map_add' a b := by ext k y; by_cases h : negSupp k = N <;> simp [h]
  map_smul' c a := by ext k y; by_cases h : negSupp k = N <;> simp [h]

lemma pproj_apply (N : Finset (Fin (n + 1))) (a : PCoeff n m) (k : Fin (n + 1) → ℤ)
    (y : Fin m → ℂ) : pproj N a k y = if negSupp k = N then a k y else 0 :=
  rfl

lemma aty_pproj (N : Finset (Fin (n + 1))) (a : PCoeff n m) (y : Fin m → ℂ) :
    aty (pproj N a) y = proj N (aty a y) := by
  ext k
  simp only [aty, pproj_apply, proj_apply]

variable (n m) in
/-- The grading of coefficient families by negative supports. -/
def pgrading : Grading (Fin (n + 1)) (PCoeff n m) where
  proj N := (pproj N).toAddMonoidHom
  sum_proj a := by
    ext k y
    simp [Finset.sum_apply, pproj_apply]
  proj_proj N N' a := by
    ext k y
    simp only [LinearMap.toAddMonoidHom_coe, pproj_apply]
    by_cases h : N = N'
    · subst h; by_cases h1 : negSupp k = N <;> simp [h1, pproj_apply]
    · rw [if_neg h]
      by_cases h1 : negSupp k = N
      · subst h1; simp [h]
      · simp [h1]

@[simp]
lemma pgrading_proj (N : Finset (Fin (n + 1))) (a : PCoeff n m) :
    (pgrading n m).proj N a = pproj N a :=
  rfl

variable (n) in
/-- The subspace of coefficient families of degree `d`, vanishing for `y ∉ U`, all of whose
parts with fixed negative support `N` converge absolutely on `V N × U` to a holomorphic function
there. It contains the coefficients of all sections. -/
def pcoeffSpace (d : ℤ) (U : Opens (Fin m → ℂ)) : Submodule ℂ (PCoeff n m) where
  carrier := {a | (∀ k y, a k y ≠ 0 → ∑ i, k i = d) ∧ (∀ k, ∀ y ∉ U, a k y = 0) ∧
    ∀ N, (∀ w ∈ V N, ∀ y ∈ U, SummableAt (proj N (aty a y)) w) ∧
      DifferentiableOn ℂ (fun p ↦ ∑' k, proj N (aty a p.2) k * monomial k p.1)
        (V N ×ˢ (U : Set (Fin m → ℂ)))}
  add_mem' {a b} ha hb := by
    refine ⟨fun k y hk ↦ ?_, fun k y hy ↦ by simp [ha.2.1 k y hy, hb.2.1 k y hy], fun N ↦
      ⟨fun w hw y hy ↦ ?_, ((ha.2.2 N).2.add (hb.2.2 N).2).congr fun p hp ↦ ?_⟩⟩
    · by_cases h : a k y = 0
      · exact hb.1 k y (by simpa [h] using hk)
      · exact ha.1 k y h
    · rw [aty_add, map_add]
      exact ((ha.2.2 N).1 w hw y hy).add ((hb.2.2 N).1 w hw y hy)
    · have hsa := Summable.of_norm ((summableAt_iff _ _).1 ((ha.2.2 N).1 p.1 hp.1 p.2 hp.2))
      have hsb := Summable.of_norm ((summableAt_iff _ _).1 ((hb.2.2 N).1 p.1 hp.1 p.2 hp.2))
      simp only [aty_add, map_add, Pi.add_apply, add_mul]
      exact hsa.tsum_add hsb
  zero_mem' := ⟨fun k y hk ↦ absurd rfl hk, fun _ _ _ ↦ rfl, fun N ↦ ⟨fun w _ _ _ ↦ by
    simpa using summableAt_zero w, by
    simp only [aty_zero, map_zero, Pi.zero_apply, zero_mul, tsum_zero]
    exact differentiableOn_const 0⟩⟩
  smul_mem' c a ha := by
    refine ⟨fun k y hk ↦ ha.1 k y fun h ↦ hk (by simp [h]), fun k y hy ↦ by simp [ha.2.1 k y hy],
      fun N ↦ ⟨fun w hw y hy ↦ ?_, ((ha.2.2 N).2.const_smul c).congr fun p _ ↦ ?_⟩⟩
    · rw [aty_smul, map_smul]
      exact ((ha.2.2 N).1 w hw y hy).smul c
    · simp only [aty_smul, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left]

lemma pproj_mem_pcoeffSpace (N : Finset (Fin (n + 1))) {a : PCoeff n m}
    (ha : a ∈ pcoeffSpace n d U) : pproj N a ∈ pcoeffSpace n d U := by
  have key : ∀ N' y, proj N' (aty (pproj N a) y) = if N' = N then proj N' (aty a y) else 0 :=
    fun N' y ↦ by
      rw [aty_pproj]
      simpa using (grading n).proj_proj N' N (aty a y)
  refine ⟨fun k y hk ↦ ha.1 k y fun h ↦ hk (by simp [pproj_apply, h]),
    fun k y hy ↦ by simp [pproj_apply, ha.2.1 k y hy], fun N' ↦ ?_⟩
  simp only [key]
  split_ifs with h
  · exact ha.2.2 N'
  · refine ⟨fun w _ _ _ ↦ summableAt_zero w, ?_⟩
    simp only [Pi.zero_apply, zero_mul, tsum_zero]
    exact differentiableOn_const 0

/-- The coefficient families of sections over `V I × U`: those in `pcoeffSpace n d U` whose
negative supports lie in `I`. -/
def pcoef (d : ℤ) (U : Opens (Fin m → ℂ)) (I : Finset (Fin (n + 1))) :
    Submodule ℂ (PCoeff n m) where
  carrier := {a | a ∈ pcoeffSpace n d U ∧ ∀ k y, a k y ≠ 0 → negSupp k ⊆ I}
  add_mem' {a b} ha hb := ⟨add_mem ha.1 hb.1, fun k y hk ↦ by
    by_cases h : a k y = 0
    · exact hb.2 k y (by simpa [h] using hk)
    · exact ha.2 k y h⟩
  zero_mem' := ⟨zero_mem _, fun k y hk ↦ absurd rfl hk⟩
  smul_mem' c a ha := ⟨Submodule.smul_mem _ c ha.1, fun k y hk ↦
    ha.2 k y fun h ↦ hk (by simp [h])⟩

lemma aty_mem_coef {a : PCoeff n m} (ha : a ∈ pcoef d U I) {y : Fin m → ℂ} (hy : y ∈ U) :
    aty a y ∈ coef d I :=
  ⟨⟨fun k hk ↦ ha.1.1 k y hk, fun N w hw ↦ (ha.1.2.2 N).1 w hw y hy⟩, fun k hk ↦ ha.2 k y hk⟩

/-! ### Laurent coefficients of sections -/

/-- The Laurent coefficients in `z` of `f`, as functions of the parameter. -/
noncomputable def toPCoeff (f : (Fin (n + 1) → ℂ) × (Fin m → ℂ) → ℂ) : PCoeff n m :=
  fun k y ↦ toCoeff (fun z ↦ f (z, y)) k

lemma aty_toPCoeff (f : (Fin (n + 1) → ℂ) × (Fin m → ℂ) → ℂ) (y : Fin m → ℂ) :
    aty (toPCoeff f) y = toCoeff fun z ↦ f (z, y) :=
  rfl

/-- The sum `∑ₖ aₖ(y) zᵏ` on `V I × U`, extended by zero. -/
noncomputable def ofPCoeff (U : Opens (Fin m → ℂ)) (I : Finset (Fin (n + 1))) (a : PCoeff n m) :
    (Fin (n + 1) → ℂ) × (Fin m → ℂ) → ℂ :=
  (V I ×ˢ (U : Set (Fin m → ℂ))).indicator fun p ↦ ∑' k, a k p.2 * monomial k p.1

lemma ofPCoeff_apply (a : PCoeff n m) {y : Fin m → ℂ} (hy : y ∈ U) (z : Fin (n + 1) → ℂ) :
    ofPCoeff U I a (z, y) = ofCoeff I (aty a y) z := by
  by_cases hz : z ∈ V I
  · rw [ofPCoeff, indicator_of_mem (mk_mem_prod hz hy), ofCoeff, indicator_of_mem hz]
    rfl
  · rw [ofPCoeff, indicator_of_notMem (fun h ↦ hz h.1), ofCoeff, indicator_of_notMem hz]

lemma ofPCoeff_of_notMem (a : PCoeff n m) {y : Fin m → ℂ} (hy : y ∉ U) (z : Fin (n + 1) → ℂ) :
    ofPCoeff U I a (z, y) = 0 :=
  indicator_of_notMem (fun h ↦ hy h.2) _

lemma toCoeff_zero : toCoeff (0 : (Fin (n + 1) → ℂ) → ℂ) = 0 :=
  toCoeff_eq_of_hasSum (summableAt_zero _) fun _ _ ↦ by
    simp only [Pi.zero_apply, zero_mul]
    exact hasSum_zero

lemma aty_toPCoeff_of_notMem (hf : f ∈ holP d U I) {y : Fin m → ℂ} (hy : y ∉ U) :
    aty (toPCoeff f) y = 0 := by
  rw [aty_toPCoeff, slice_eq_zero hf hy, toCoeff_zero]

lemma mem_of_toPCoeff_ne_zero (hf : f ∈ holP d U I) {k : Fin (n + 1) → ℤ} {y : Fin m → ℂ}
    (hk : toPCoeff f k y ≠ 0) : y ∈ U :=
  by_contra fun hy ↦ hk (congrFun (aty_toPCoeff_of_notMem hf hy) k)

lemma toPCoeff_mem (hf : f ∈ holP d U I) : toPCoeff f ∈ pcoef d U I := by
  have hneg : ∀ k y, toPCoeff f k y ≠ 0 → negSupp k ⊆ I := fun k y hk ↦
    negSupp_subset_of_toCoeff_ne_zero (slice_mem hf (mem_of_toPCoeff_ne_zero hf hk)) hk
  refine ⟨⟨fun k y hk ↦ sum_eq_of_toCoeff_ne_zero
    (slice_mem hf (mem_of_toPCoeff_ne_zero hf hk)) hk,
    fun k y hy ↦ congrFun (aty_toPCoeff_of_notMem hf hy) k, fun N ↦
    ⟨fun w hw y hy ↦ (toCoeff_mem (slice_mem hf hy)).1.2 N w hw, ?_⟩⟩, hneg⟩
  by_cases hN : N ⊆ I
  · exact differentiableOn_tsum_proj_toCoeff U.isOpen hf.1 hN
  · have : ∀ y, proj N (aty (toPCoeff f) y) = 0 := fun y ↦
      proj_eq_zero_of_negSupp (fun k hk ↦ hneg k y hk) hN
    simp only [this, Pi.zero_apply, zero_mul, tsum_zero]
    exact differentiableOn_const 0

lemma ofPCoeff_mem {a : PCoeff n m} (ha : a ∈ pcoef d U I) : ofPCoeff U I a ∈ holP d U I := by
  have hzero : ∀ N, ¬ N ⊆ I → ∀ y, proj N (aty a y) = 0 := fun N hN y ↦
    proj_eq_zero_of_negSupp (fun k hk ↦ ha.2 k y hk) hN
  refine ⟨?_, fun z hz y hy c hc ↦ ?_, fun p hp ↦ indicator_of_notMem hp _⟩
  · have hd : DifferentiableOn ℂ (fun p ↦ ∑ N, ∑' k, proj N (aty a p.2) k * monomial k p.1)
        (V I ×ˢ (U : Set (Fin m → ℂ))) := by
      refine DifferentiableOn.fun_sum fun N _ ↦ ?_
      by_cases hN : N ⊆ I
      · exact (ha.1.2.2 N).2.mono (prod_mono (V_anti hN) subset_rfl)
      · simp only [hzero N hN, Pi.zero_apply, zero_mul, tsum_zero]
        exact differentiableOn_const 0
    refine hd.congr fun p hp ↦ ?_
    have hs : ∀ N, Summable fun k ↦ proj N (aty a p.2) k * monomial k p.1 := fun N ↦ by
      by_cases hN : N ⊆ I
      · exact Summable.of_norm ((summableAt_iff _ _).1
          ((ha.1.2.2 N).1 p.1 (V_anti hN hp.1) p.2 hp.2))
      · simp only [hzero N hN, Pi.zero_apply, zero_mul]
        exact summable_zero
    rw [ofPCoeff, indicator_of_mem hp, ← (hasSum_sum fun N _ ↦ (hs N).hasSum).tsum_eq]
    refine tsum_congr fun k ↦ ?_
    rw [← Finset.sum_mul]
    congr 1
    have := congrFun ((grading n).sum_proj (aty a p.2)) k
    simp only [grading_proj, Finset.sum_apply] at this
    exact this.symm
  · rw [ofPCoeff_apply a hy, ofPCoeff_apply a hy]
    exact (ofCoeff_mem (aty_mem_coef ha hy)).2.1 z hz c hc

lemma toPCoeff_ofPCoeff {a : PCoeff n m} (ha : a ∈ pcoef d U I) :
    toPCoeff (ofPCoeff U I a) = a := by
  funext k y
  change toCoeff (fun z ↦ ofPCoeff U I a (z, y)) k = a k y
  by_cases hy : y ∈ U
  · have : (fun z ↦ ofPCoeff U I a (z, y)) = ofCoeff I (aty a y) :=
      funext fun z ↦ ofPCoeff_apply a hy z
    rw [this, toCoeff_ofCoeff (aty_mem_coef ha hy)]
    rfl
  · have : (fun z ↦ ofPCoeff U I a (z, y)) = 0 := funext fun z ↦ ofPCoeff_of_notMem a hy z
    rw [this, toCoeff_zero, ha.1.2.1 k y hy]
    rfl

lemma ofPCoeff_toPCoeff (hf : f ∈ holP d U I) : ofPCoeff U I (toPCoeff f) = f := by
  funext ⟨z, y⟩
  by_cases hy : y ∈ U
  · rw [ofPCoeff_apply _ hy, aty_toPCoeff, ofCoeff_toCoeff (slice_mem hf hy)]
  · rw [ofPCoeff_of_notMem _ hy, hf.2.2 _ fun h ↦ hy h.2]

lemma toPCoeff_add {g : (Fin (n + 1) → ℂ) × (Fin m → ℂ) → ℂ} (hf : f ∈ holP d U I)
    (hg : g ∈ holP d U I) : toPCoeff (f + g) = toPCoeff f + toPCoeff g := by
  funext k y
  by_cases hy : y ∈ U
  · exact congrFun (toCoeff_add (slice_mem hf hy) (slice_mem hg hy)) k
  · have h1 := congrFun (aty_toPCoeff_of_notMem hf hy) k
    have h2 := congrFun (aty_toPCoeff_of_notMem hg hy) k
    have h3 := congrFun (aty_toPCoeff_of_notMem (add_mem hf hg) hy) k
    simp only [aty, Pi.zero_apply] at h1 h2 h3
    simp [h1, h2, h3]

lemma toPCoeff_smul (hf : f ∈ holP d U I) (c : ℂ) : toPCoeff (c • f) = c • toPCoeff f := by
  funext k y
  by_cases hy : y ∈ U
  · exact congrFun (toCoeff_smul (slice_mem hf hy) c) k
  · have h1 := congrFun (aty_toPCoeff_of_notMem hf hy) k
    have h3 := congrFun (aty_toPCoeff_of_notMem (Submodule.smul_mem _ c hf) hy) k
    simp only [aty, Pi.zero_apply] at h1 h3
    simp [h1, h3]

/-- Sections of `𝒪(d)` over `V I × U` are identified with their Laurent coefficients. -/
noncomputable def holPEquiv (d : ℤ) (U : Opens (Fin m → ℂ)) (I : Finset (Fin (n + 1))) :
    holP d U I ≃ₗ[ℂ] pcoef d U I where
  toFun f := ⟨toPCoeff f, toPCoeff_mem f.2⟩
  map_add' f g := Subtype.ext (toPCoeff_add f.2 g.2)
  map_smul' c f := Subtype.ext (toPCoeff_smul f.2 c)
  invFun a := ⟨ofPCoeff U I a, ofPCoeff_mem a.2⟩
  left_inv f := Subtype.ext (ofPCoeff_toPCoeff f.2)
  right_inv a := Subtype.ext (toPCoeff_ofPCoeff a.2)

@[simp]
lemma coe_holPEquiv (f : holP d U I) : (holPEquiv d U I f : PCoeff n m) = toPCoeff f :=
  rfl

@[simp]
lemma coe_holPEquiv_symm (a : pcoef d U I) :
    ((holPEquiv d U I).symm a : (Fin (n + 1) → ℂ) × (Fin m → ℂ) → ℂ) = ofPCoeff U I a :=
  rfl

lemma toPCoeff_holPRes (h : J ⊆ I) (F : holP d U J) :
    toPCoeff (holPRes d U h F : (Fin (n + 1) → ℂ) × (Fin m → ℂ) → ℂ) = toPCoeff F := by
  set G : (Fin (n + 1) → ℂ) × (Fin m → ℂ) → ℂ := F.1
  funext k y
  by_cases hy : y ∈ U
  · change toCoeff (fun z ↦ (V I ×ˢ (U : Set (Fin m → ℂ))).indicator G (z, y)) k =
      toCoeff (fun z ↦ G (z, y)) k
    have : (fun z ↦ (V I ×ˢ (U : Set (Fin m → ℂ))).indicator G (z, y)) =
        (V I).indicator fun z ↦ G (z, y) := funext fun z ↦ by
      by_cases hz : z ∈ V I
      · rw [indicator_of_mem (mk_mem_prod hz hy), indicator_of_mem hz]
      · rw [indicator_of_notMem (fun h ↦ hz h.1), indicator_of_notMem hz]
    rw [this, toCoeff_indicator]
  · exact (congrFun (aty_toPCoeff_of_notMem (holPRes d U h F).2 hy) k).trans
      (congrFun (aty_toPCoeff_of_notMem F.2 hy) k).symm

/-! ### The Čech complex -/

variable (n) in
/-- The ordered Čech cochains `C^p = ∏_{i : Fin (p + 1) → Fin (n + 1)} Γ(U_{im i} × U, 𝒪(d))`
for the standard cover of `ℙⁿ`, times `U`. -/
abbrev PCochain (d : ℤ) (U : Opens (Fin m → ℂ)) (p : ℕ) : Type :=
  ∀ i : Fin (p + 1) → Fin (n + 1), holP d U (im i)

variable (d U) in
/-- The Čech differential `(d x) i = ∑ₖ (-1) ^ k • (x (i ∘ δₖ))|_{V (im i) × U}`. -/
noncomputable def holPD (p : ℕ) : PCochain n d U p →ₗ[ℂ] PCochain n d U (p + 1) where
  toFun x i := ∑ k : Fin (p + 2), ((-1 : ℤ) ^ (k : ℕ)) •
    holPRes d U (im_comp_subset i k.succAbove) (x fun a ↦ i (k.succAbove a))
  map_add' x y := by
    funext i
    simp [Finset.sum_add_distrib, smul_add]
  map_smul' c x := by
    funext i
    simp [Finset.smul_sum, smul_comm c]

/-- The Laurent coefficients of a Čech cochain, as a cochain with values in `PCoeff n m`. -/
noncomputable def toPCochain {p : ℕ} (x : PCochain n d U p) :
    Cochain (Fin (n + 1)) (PCoeff n m) p :=
  fun i ↦ toPCoeff (x i)

lemma toPCochain_mem {p : ℕ} (x : PCochain n d U p) (i : Fin (p + 1) → Fin (n + 1)) :
    toPCochain x i ∈ pcoef d U (im i) :=
  toPCoeff_mem (x i).2

lemma isAdmissible_iff_p {p : ℕ} (x : Cochain (Fin (n + 1)) (PCoeff n m) p) :
    (pgrading n m).IsAdmissible x ↔ ∀ i k y, x i k y ≠ 0 → negSupp k ⊆ im i := by
  refine ⟨fun h i k y hk ↦ by_contra fun hN ↦ hk ?_, fun h i N hN ↦ ?_⟩
  · have := congrFun (congrFun (h i _ hN) k) y
    simpa [pproj_apply] using this
  · ext k y
    simp only [pgrading_proj, pproj_apply, Pi.zero_apply]
    split_ifs with hk
    · by_contra hx
      exact hN (hk ▸ h i k y hx)
    · rfl

lemma isAdmissible_toPCochain {p : ℕ} (x : PCochain n d U p) :
    (pgrading n m).IsAdmissible (toPCochain x) :=
  (isAdmissible_iff_p _).2 fun i k y hk ↦ (toPCochain_mem x i).2 k y hk

lemma toPCochain_injective {p : ℕ} :
    Function.Injective (toPCochain (d := d) (U := U) (n := n) (p := p)) :=
  fun _ _ h ↦ funext fun i ↦ (holPEquiv d U (im i)).injective (Subtype.ext (congrFun h i))

@[simp]
lemma toPCochain_zero {p : ℕ} : toPCochain (0 : PCochain n d U p) = 0 := by
  funext i
  change toPCoeff ((0 : holP d U (im i)) : (Fin (n + 1) → ℂ) × (Fin m → ℂ) → ℂ) = 0
  rw [← coe_holPEquiv, map_zero]
  rfl

lemma exists_toPCochain_eq {p : ℕ} (y : Cochain (Fin (n + 1)) (PCoeff n m) p)
    (hy : ∀ i, y i ∈ pcoef d U (im i)) : ∃ x : PCochain n d U p, toPCochain x = y :=
  ⟨fun i ↦ (holPEquiv d U (im i)).symm ⟨y i, hy i⟩, funext fun i ↦ by
    change toPCoeff ((holPEquiv d U (im i)).symm ⟨y i, hy i⟩ :
      (Fin (n + 1) → ℂ) × (Fin m → ℂ) → ℂ) = y i
    rw [← coe_holPEquiv, LinearEquiv.apply_symm_apply]⟩

lemma toPCochain_holPD {p : ℕ} (x : PCochain n d U p) :
    toPCochain (holPD d U p x) = SimplexCochain.d p (toPCochain x) := by
  funext i
  rw [SimplexCochain.d_apply]
  change toPCoeff ((∑ k : Fin (p + 2), ((-1 : ℤ) ^ (k : ℕ)) •
    holPRes d U (im_comp_subset i k.succAbove) (x fun a ↦ i (k.succAbove a)) :
      holP d U (im i)) : (Fin (n + 1) → ℂ) × (Fin m → ℂ) → ℂ) = _
  rw [← coe_holPEquiv, map_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_zsmul, Submodule.coe_smul_of_tower, coe_holPEquiv, toPCoeff_holPRes]
  rfl

@[simp]
lemma holPD_holPD {p : ℕ} (x : PCochain n d U p) : holPD d U (p + 1) (holPD d U p x) = 0 :=
  toPCochain_injective (by rw [toPCochain_holPD, toPCochain_holPD, d_d, toPCochain_zero])

lemma pproj_univ_eq_zero_of_lt {a : PCoeff n m} (ha : a ∈ pcoeffSpace n d U)
    (hd : -((n : ℤ) + 1) < d) : pproj Finset.univ a = 0 := by
  ext k y
  simp only [pproj_apply, Pi.zero_apply]
  split_ifs with hk
  · by_contra hak
    have hs := ha.1 k y hak
    have : ∑ i, k i ≤ ∑ _i : Fin (n + 1), (-1 : ℤ) := Finset.sum_le_sum fun i _ ↦ by
      have := mem_negSupp.1 (hk ▸ Finset.mem_univ i)
      omega
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    omega
  · rfl

/-- **Exactness of the Čech complex of `𝒪(d)` on `ℙⁿ × U`** in degree `q = p + 1`, if `q > n`,
or `0 < q < n`, or `d > -n - 1`. -/
theorem holPD_exact (d : ℤ) (U : Opens (Fin m → ℂ)) (p : ℕ)
    (hp : n ≤ p ∨ p + 1 < n ∨ -((n : ℤ) + 1) < d) :
    Function.Exact (holPD d U (n := n) p) (holPD d U (p + 1)) := by
  intro x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have hdx : SimplexCochain.d (p + 1) (toPCochain x) = 0 := by
      rw [← toPCochain_holPD, hx, toPCochain_zero]
    have hadm := isAdmissible_toPCochain x
    obtain ⟨y, hy, hyS, hdy⟩ := (pgrading n m).exists_eq_d (pcoeffSpace n d U).toAddSubgroup
      (fun N _ hm ↦ pproj_mem_pcoeffSpace N hm) (toPCochain x) hadm
      (fun i ↦ (toPCochain_mem x i).1) hdx (by
        rcases hp with hp | hp | hp
        · left; simpa using hp
        · right; exact (pgrading n m).proj_univ_eq_zero hadm (by simpa using hp)
        · right; intro i; exact pproj_univ_eq_zero_of_lt (toPCochain_mem x i).1 hp)
    obtain ⟨w, hw⟩ := exists_toPCochain_eq y fun i ↦ ⟨hyS i, (isAdmissible_iff_p y).1 hy i⟩
    exact ⟨w, toPCochain_injective (by rw [toPCochain_holPD, hw, hdy])⟩
  · rintro ⟨w, rfl⟩
    exact holPD_holPD w

/-! ### Degree zero -/

lemma nonneg_of_pproj_empty {v : PCoeff n m} (hv : pproj ∅ v = v) {k : Fin (n + 1) → ℤ}
    {y : Fin m → ℂ} (hk : v k y ≠ 0) (i : Fin (n + 1)) : 0 ≤ k i := by
  have h := congrFun (congrFun hv k) y
  rw [pproj_apply] at h
  split_ifs at h with h0
  · exact not_lt.1 fun hi ↦ by simpa [h0] using mem_negSupp.2 hi
  · exact absurd h.symm hk

/-- The `0`-cocycles of the Čech complex are the coefficient families of constant cochains
supported on nonnegative exponents. -/
lemma exists_toPCochain_eq_aug (x : PCochain n d U 0) (hx : holPD d U 0 x = 0)
    (hn : 0 < n ∨ -((n : ℤ) + 1) < d) :
    ∃ v ∈ pcoeffSpace n d U, (∀ k y, v k y ≠ 0 → ∀ i, 0 ≤ k i) ∧
      toPCochain x = SimplexCochain.aug v := by
  have hdx : SimplexCochain.d 0 (toPCochain x) = 0 := by
    rw [← toPCochain_holPD, hx, toPCochain_zero]
  have hadm := isAdmissible_toPCochain x
  obtain ⟨v, hv, hxv⟩ := (pgrading n m).exists_eq_aug (toPCochain x) hadm hdx (by
    rcases hn with hn | hn
    · exact (pgrading n m).proj_univ_eq_zero hadm (by simpa using hn)
    · intro i; exact pproj_univ_eq_zero_of_lt (toPCochain_mem x i).1 hn)
  have hvx : v = toPCochain x fun _ ↦ 0 := by rw [hxv]; rfl
  exact ⟨v, hvx ▸ (toPCochain_mem x _).1, fun k y hk ↦ nonneg_of_pproj_empty hv hk, hxv⟩

/-- **`H⁰` of `𝒪(d)` on `ℙⁿ × U`, `d < 0`**: there are no nonzero `0`-cocycles (for `n ≥ 1`). -/
theorem holPD_zero_injective (hd : d < 0) (hn : 0 < n ∨ -((n : ℤ) + 1) < d) :
    Function.Injective (holPD d U (n := n) 0) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨v, hvS, hv0, hxv⟩ := exists_toPCochain_eq_aug x hx hn
  have hv : v = 0 := by
    funext k y
    by_contra hk
    have h1 := hvS.1 k y hk
    have h2 : 0 ≤ ∑ i, k i := Finset.sum_nonneg fun i _ ↦ hv0 k y hk i
    omega
  exact toPCochain_injective (by rw [hxv, hv, map_zero, toPCochain_zero])

/-! ### Degree zero: polynomials with holomorphic coefficients -/

lemma toGlobalFun_of_notMem (c : OkaRing U) {y : Fin m → ℂ} (hy : y ∉ U) :
    c.toGlobalFun _ y = 0 :=
  Function.extend_apply' _ _ _ fun ⟨a, ha⟩ ↦ hy (ha ▸ a.2)

lemma toGlobalFun_add (c c' : OkaRing U) :
    (c + c').toGlobalFun _ = c.toGlobalFun _ + c'.toGlobalFun _ := by
  funext y
  by_cases hy : y ∈ U
  · simp only [Pi.add_apply, OkaRing.toGlobalFun_apply _ hy]
    rfl
  · simp [toGlobalFun_of_notMem _ hy]

lemma toGlobalFun_smul (a : ℂ) (c : OkaRing U) : (a • c).toGlobalFun _ = a • c.toGlobalFun _ := by
  funext y
  by_cases hy : y ∈ U
  · simp only [Pi.smul_apply, OkaRing.toGlobalFun_apply _ hy]
    rfl
  · simp [toGlobalFun_of_notMem _ hy]

variable (n) in
/-- The exponents of the monomials of degree `e` in `n + 1` variables. -/
abbrev MonoExp (e : ℕ) : Type := ↥(Finset.Nat.antidiagonalTuple (n + 1) e)

/-- An exponent in `ℕⁿ⁺¹`, as an element of `ℤⁿ⁺¹`. -/
def castExp (s : Fin (n + 1) → ℕ) : Fin (n + 1) → ℤ := fun i ↦ s i

lemma castExp_injective : Function.Injective (castExp (n := n)) := fun s t h ↦
  funext fun i ↦ by simpa [castExp] using congrFun h i

lemma monomial_castExp (s : Fin (n + 1) → ℕ) (z : Fin (n + 1) → ℂ) :
    monomial (castExp s) z = ∏ i, z i ^ s i := by
  simp [monomial, castExp]

variable (n U) in
/-- The coefficient family of `∑_s c_s(y) zˢ`, the sum over the monomials of degree `e`. -/
noncomputable def polyPCoeff (e : ℕ) : (MonoExp n e → OkaRing U) →ₗ[ℂ] PCoeff n m where
  toFun c k y := ∑ s : MonoExp n e, if k = castExp s.1 then (c s).toGlobalFun _ y else 0
  map_add' c c' := by
    ext k y
    simp only [Pi.add_apply, toGlobalFun_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    split_ifs <;> simp
  map_smul' a c := by
    ext k y
    simp only [Pi.smul_apply, toGlobalFun_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    split_ifs <;> simp

variable {e : ℕ}

lemma polyPCoeff_apply (c : MonoExp n e → OkaRing U) (k : Fin (n + 1) → ℤ) (y : Fin m → ℂ) :
    polyPCoeff n U e c k y =
      ∑ s : MonoExp n e, if k = castExp s.1 then (c s).toGlobalFun _ y else 0 :=
  rfl

lemma polyPCoeff_castExp (c : MonoExp n e → OkaRing U) (s : MonoExp n e) (y : Fin m → ℂ) :
    polyPCoeff n U e c (castExp s.1) y = (c s).toGlobalFun _ y := by
  change ∑ t : MonoExp n e, _ = _
  rw [Finset.sum_eq_single s (fun t _ hts ↦ if_neg fun h ↦ hts
    (Subtype.ext (castExp_injective h).symm)) (by simp), if_pos rfl]

lemma polyPCoeff_eq_zero (c : MonoExp n e → OkaRing U) {k : Fin (n + 1) → ℤ}
    (hk : ∀ s : MonoExp n e, k ≠ castExp s.1) (y : Fin m → ℂ) : polyPCoeff n U e c k y = 0 :=
  (polyPCoeff_apply c k y).trans (Finset.sum_eq_zero fun s _ ↦ if_neg (hk s))

lemma differentiable_monomial_castExp (s : Fin (n + 1) → ℕ) :
    Differentiable ℂ (monomial (castExp s)) := by
  have : monomial (castExp s) = fun z ↦ ∏ i, z i ^ s i := funext (monomial_castExp s)
  rw [this]
  fun_prop

lemma polyPCoeff_mem (c : MonoExp n e → OkaRing U) (I : Finset (Fin (n + 1))) :
    polyPCoeff n U e c ∈ pcoef (e : ℤ) U I := by
  set a := polyPCoeff n U e c
  have hsupp : ∀ k y, a k y ≠ 0 → ∃ s : MonoExp n e, k = castExp s.1 := fun k y hk ↦ by
    by_contra h
    push Not at h
    exact hk (polyPCoeff_eq_zero c h y)
  have hnn : ∀ k y, a k y ≠ 0 → ∀ i, 0 ≤ k i := fun k y hk i ↦ by
    obtain ⟨s, rfl⟩ := hsupp k y hk
    simp [castExp]
  set T : Finset (Fin (n + 1) → ℤ) := Finset.univ.image fun s : MonoExp n e ↦ castExp s.1
  have hT : ∀ k ∉ T, ∀ y, a k y = 0 := fun k hk y ↦
    polyPCoeff_eq_zero c (fun s hs ↦ hk (Finset.mem_image.2 ⟨s, Finset.mem_univ _, hs.symm⟩)) y
  have hTp : ∀ N y, ∀ k ∉ T, proj N (aty a y) k = 0 := fun N y k hk ↦ by
    simp only [proj_apply, aty, hT k hk y, ite_self]
  refine ⟨⟨fun k y hk ↦ ?_, fun k y hy ↦ ?_, fun N ↦ ⟨fun w _ y _ ↦
    summableAt_of_finite T (hTp N y) w, ?_⟩⟩, fun k y hk j hj ↦ ?_⟩
  · obtain ⟨s, rfl⟩ := hsupp k y hk
    have := Finset.Nat.mem_antidiagonalTuple.1 s.2
    simp only [castExp]
    exact_mod_cast this
  · rw [show a k y = _ from polyPCoeff_apply c k y]
    exact Finset.sum_eq_zero fun s _ ↦ by
      split_ifs
      · exact toGlobalFun_of_notMem _ hy
      · rfl
  · have hd : DifferentiableOn ℂ (fun p ↦ ∑ k ∈ T, proj N (aty a p.2) k * monomial k p.1)
        (V N ×ˢ (U : Set (Fin m → ℂ))) := by
      refine DifferentiableOn.fun_sum fun k hk ↦ ?_
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hk
      simp only [proj_apply, aty]
      split_ifs
      · simp only [polyPCoeff_castExp, a]
        exact ((c t).differentiableOn_toGlobalFun.comp differentiableOn_snd
          fun p hp ↦ hp.2).mul ((differentiable_monomial_castExp t.1).comp
            differentiable_fst).differentiableOn
      · simp only [zero_mul]
        exact differentiableOn_const 0
    exact hd.congr fun p _ ↦ tsum_eq_sum fun k hk ↦ by rw [hTp N p.2 k hk, zero_mul]
  · exact absurd (mem_negSupp.1 hj) (not_lt.2 (hnn k y hk j))

variable (n U) in
/-- The augmentation `c ↦ (i ↦ (∑_s c_s(y) zˢ)|_{V (im i) × U})` from families, indexed by the
monomials of degree `e`, of holomorphic functions on `U`. -/
noncomputable def holPAug (e : ℕ) : (MonoExp n e → OkaRing U) →ₗ[ℂ] PCochain n (e : ℤ) U 0 :=
  LinearMap.pi fun i ↦ (holPEquiv (e : ℤ) U (im i)).symm.toLinearMap ∘ₗ
    (polyPCoeff n U e).codRestrict (pcoef (e : ℤ) U (im i)) fun c ↦ polyPCoeff_mem c _

lemma holPAug_apply (c : MonoExp n e → OkaRing U) (i : Fin 1 → Fin (n + 1))
    {z : Fin (n + 1) → ℂ} (hz : z ∈ V (im i)) {y : Fin m → ℂ} (hy : y ∈ U) :
    (holPAug n U e c i : (Fin (n + 1) → ℂ) × (Fin m → ℂ) → ℂ) (z, y) =
      ∑ s : MonoExp n e, (c s).toGlobalFun _ y * ∏ j, z j ^ s.1 j := by
  change ofPCoeff U (im i) (polyPCoeff n U e c) (z, y) = _
  rw [ofPCoeff, indicator_of_mem (mk_mem_prod hz hy)]
  refine HasSum.tsum_eq ?_
  simp_rw [← monomial_castExp]
  change HasSum (fun k ↦ (∑ s : MonoExp n e,
    if k = castExp s.1 then (c s).toGlobalFun _ y else 0) * monomial k z) _
  simp_rw [Finset.sum_mul]
  refine hasSum_sum fun s _ ↦ ?_
  convert hasSum_ite_eq (castExp s.1) ((c s).toGlobalFun _ y * monomial (castExp s.1) z)
    using 1
  ext k
  split_ifs with h
  · rw [h]
  · rw [zero_mul]

lemma toPCochain_holPAug (c : MonoExp n e → OkaRing U) :
    toPCochain (holPAug n U e c) = SimplexCochain.aug (polyPCoeff n U e c) := by
  funext i
  change toPCoeff (ofPCoeff U (im i) (polyPCoeff n U e c)) = _
  rw [toPCoeff_ofPCoeff (polyPCoeff_mem c _)]
  rfl

@[simp]
lemma holPD_holPAug (c : MonoExp n e → OkaRing U) : holPD (e : ℤ) U 0 (holPAug n U e c) = 0 :=
  toPCochain_injective (by rw [toPCochain_holPD, toPCochain_holPAug, d_aug, toPCochain_zero])

theorem holPAug_injective (e : ℕ) : Function.Injective (holPAug n U e) := by
  intro c c' h
  have h' := congrFun (congrArg toPCochain h) fun _ ↦ 0
  rw [toPCochain_holPAug, toPCochain_holPAug, aug_apply, aug_apply] at h'
  funext s
  refine OkaRing.ext (funext fun y ↦ ?_)
  have := congrFun (congrFun h' (castExp s.1)) y.1
  rw [polyPCoeff_castExp, polyPCoeff_castExp, OkaRing.toGlobalFun_apply _ y.2,
    OkaRing.toGlobalFun_apply _ y.2] at this
  exact this

/-- **`H⁰` of `𝒪(e)` on `ℙⁿ × U`, `e ≥ 0`**: the `0`-cocycles are exactly the (restrictions of)
the functions `∑_{|s| = e} c_s(y) zˢ` with `c_s` holomorphic on `U`. -/
theorem holPAug_exact (e : ℕ) : Function.Exact (holPAug n U e) (holPD (e : ℤ) U 0) := by
  intro x
  refine ⟨fun hx ↦ ?_, by rintro ⟨c, rfl⟩; exact holPD_holPAug c⟩
  obtain ⟨v, hvS, hv0, hxv⟩ := exists_toPCochain_eq_aug x hx (Or.inr (by omega))
  have hvx : v = toPCoeff (x fun _ ↦ 0 : (Fin (n + 1) → ℂ) × (Fin m → ℂ) → ℂ) := by
    have := congrFun hxv fun _ ↦ 0
    rw [aug_apply] at this
    exact this.symm
  have hdiff : ∀ k, DifferentiableOn ℂ (v k) U := fun k ↦ by
    rw [hvx]
    exact differentiableOn_toCoeff_slice U.isOpen (x _).2.1 k
  let c : MonoExp n e → OkaRing U := fun s ↦ OkaRing.ofDifferentiableOn (v (castExp s.1)) (hdiff _)
  have hcv : polyPCoeff n U e c = v := by
    funext k y
    by_cases hk : ∃ s : MonoExp n e, k = castExp s.1
    · obtain ⟨s, rfl⟩ := hk
      rw [polyPCoeff_castExp]
      by_cases hy : y ∈ U
      · rw [OkaRing.toGlobalFun_apply _ hy, OkaRing.ofDifferentiableOn_toFun]
      · rw [toGlobalFun_of_notMem _ hy, hvS.2.1 _ y hy]
    · push Not at hk
      rw [polyPCoeff_eq_zero c hk]
      by_contra hne
      have h0 := hv0 k y (Ne.symm hne)
      have hs := hvS.1 k y (Ne.symm hne)
      have hsum : ∑ i, ((k i).toNat : ℤ) = ∑ i, k i :=
        Finset.sum_congr rfl fun i _ ↦ Int.toNat_of_nonneg (h0 i)
      have hmem : (fun i ↦ (k i).toNat) ∈ Finset.Nat.antidiagonalTuple (n + 1) e := by
        rw [Finset.Nat.mem_antidiagonalTuple]
        have : ((∑ i, (k i).toNat : ℕ) : ℤ) = e := by push_cast; rw [hsum, hs]
        exact_mod_cast this
      exact hk ⟨_, hmem⟩ (funext fun i ↦ (Int.toNat_of_nonneg (h0 i)).symm)
  exact ⟨c, toPCochain_injective (by rw [toPCochain_holPAug, hxv, hcv])⟩

end CechProjectiveBox

end
