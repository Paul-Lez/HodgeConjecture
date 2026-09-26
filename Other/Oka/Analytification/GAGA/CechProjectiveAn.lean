/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytic.Laurent.Several
public import Other.Oka.AlgebraicTopology.SimplexCochain
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The analytic Čech complex of `𝒪(d)` on `ℙⁿ`

We work in homogeneous coordinates `z ∈ ℂⁿ⁺¹`. For `I : Finset (Fin (n + 1))` let
`V I = {z | z j ≠ 0 for j ∈ I}`; it is the product of annuli `Laurent.polyAnnulus` with factors
`ℂ^×` for `j ∈ I` and `ℂ` otherwise. The space `hol d I` of functions holomorphic on `V I` and
homogeneous of degree `d : ℤ` is the space of sections of `𝒪(d)` over the standard open
`U_I = ⋂_{j ∈ I} {z_j ≠ 0}` of `ℙⁿ`. (We normalise sections to vanish outside `V I`, so that
restriction along `V I ⊆ V J` is `(V I).indicator`.)

The ordered Čech complex of `𝒪(d)` for the standard cover has terms
`HolCochain d n p = ∏_{i : Fin (p + 1) → Fin (n + 1)} hol d (im i)` and differential `holD d p`,
`(holD x) i = ∑ₖ (-1) ^ k • (x (i ∘ δₖ))|_{V (im i)}`.

## Method

A function in `hol d I` is the sum of its multi-Laurent series `∑ₖ aₖ zᵏ` (coefficients computed
on the unit torus, which lies in every `V I`). By homogeneity `aₖ = 0` unless `∑ kᵢ = d`, and
`aₖ = 0` unless the negative support `negSupp k = {j | kⱼ < 0}` is contained in `I`
(`Laurent.mcoeff_eq_zero_of_neg`). Conversely such coefficient families which converge
absolutely on `V I` give elements of `hol d I` (`holEquiv`). The parts of the expansion with a
fixed negative support `N` converge on the bigger domain `V N`, so the coefficient families of
all sections lie in one subgroup `coeffSpace d`, stable under the projections onto fixed
negative supports. The Čech complex is thereby identified with the complex of admissible
cochains with values in `coeffSpace d` of the monomially graded complex of
`Other/Oka/AlgebraicTopology/SimplexCochain.lean`, whose cohomology is computed there by an explicit
homotopy.

## Main definitions

- `CechProjectiveAn.V`, `CechProjectiveAn.hol`, `CechProjectiveAn.holRes`.
- `CechProjectiveAn.HolCochain`, `CechProjectiveAn.holD`: the Čech complex.
- `CechProjectiveAn.holAug`: the augmentation from homogeneous polynomials of degree `e`.
- `CechProjectiveAn.holEquiv`: sections over `V I` ≃ their Laurent coefficients.

## Main results

- `CechProjectiveAn.holD_holD`: `d ∘ d = 0`.
- `CechProjectiveAn.holD_exact`: exactness in degree `q = p + 1` if `q > n`, `q < n`, or
  `d > -n - 1`.
- `CechProjectiveAn.holAug_injective`, `CechProjectiveAn.holAug_exact`: for `d = e ≥ 0`,
  `H⁰` is the space of homogeneous polynomials of degree `e`.
- `CechProjectiveAn.holD_zero_injective`: `H⁰ = 0` for `d < 0` (if `n ≥ 1`).
- `CechProjectiveAn.holD_exact_zero`, `CechProjectiveAn.holD_zero_eq_zero_iff`: for `d = 0` the
  complex is exact in positive degrees and `H⁰ = ℂ` (constants).
-/

@[expose] public section

open Complex Set Laurent SimplexCochain
open scoped ENNReal

namespace CechProjectiveAn

variable {n : ℕ}

/-! ### The opens `V I` -/

/-- `V I = {z ∈ ℂⁿ⁺¹ | z j ≠ 0 for all j ∈ I}`, the cone over the standard open `U_I`. -/
def V (I : Finset (Fin (n + 1))) : Set (Fin (n + 1) → ℂ) := {z | ∀ j ∈ I, z j ≠ 0}

/-- The inner radii presenting `V I` as a product of annuli: `0` on `I`, `-1` off `I`. -/
def radii (I : Finset (Fin (n + 1))) : Fin (n + 1) → ℝ := fun j ↦ if j ∈ I then 0 else -1

lemma V_eq_polyAnnulus (I : Finset (Fin (n + 1))) :
    V I = polyAnnulus (radii I) (fun _ ↦ ⊤) := by
  ext z
  simp only [V, mem_setOf_eq, mem_polyAnnulus, annulus, radii, enorm_lt_top, and_true]
  refine ⟨fun h j ↦ ?_, fun h j hj ↦ ?_⟩
  · split_ifs with hj
    · exact norm_pos_iff.2 (h j hj)
    · linarith [norm_nonneg (z j)]
  · have := h j
    rw [if_pos hj] at this
    exact norm_pos_iff.1 this

lemma isRadius_one (I : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    IsRadius (radii I j) ((fun _ ↦ (⊤ : ℝ≥0∞)) j) ((fun _ ↦ (1 : ℝ)) j) := by
  refine ⟨one_pos, ?_, ENNReal.ofReal_lt_top⟩
  simp only [radii]
  split_ifs <;> norm_num

lemma isOpen_V (I : Finset (Fin (n + 1))) : IsOpen (V I) := by
  rw [V_eq_polyAnnulus]; exact isOpen_polyAnnulus _ _

lemma V_anti {I J : Finset (Fin (n + 1))} (h : J ⊆ I) : V I ⊆ V J :=
  fun _ hz j hj ↦ hz j (h hj)

lemma torus_subset_V (I : Finset (Fin (n + 1))) : torus (fun _ ↦ (1 : ℝ)) ⊆ V I := by
  rw [V_eq_polyAnnulus]; exact torus_subset_polyAnnulus (isRadius_one I)

lemma smul_mem_V {I : Finset (Fin (n + 1))} {c : ℂ} (hc : c ≠ 0) {z : Fin (n + 1) → ℂ}
    (hz : z ∈ V I) : c • z ∈ V I :=
  fun j hj ↦ by simpa using And.intro hc (hz j hj)

lemma const_mem_V (I : Finset (Fin (n + 1))) {c : ℂ} (hc : c ≠ 0) :
    (fun _ ↦ c) ∈ V I :=
  fun _ _ ↦ hc

lemma prod_zpow_eq {G₀ : Type*} [CommGroupWithZero G₀] {c : G₀} (hc : c ≠ 0) (k : Fin (n + 1) → ℤ) :
    ∏ i, c ^ k i = c ^ ∑ i, k i := by
  have (s : Finset (Fin (n + 1))) : ∏ i ∈ s, c ^ k i = c ^ ∑ i ∈ s, k i := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hc, ih]
  exact this _

lemma monomial_smul {c : ℂ} (hc : c ≠ 0) (k : Fin (n + 1) → ℤ) (z : Fin (n + 1) → ℂ) :
    monomial k (c • z) = c ^ (∑ i, k i) * monomial k z := by
  simp only [monomial, Pi.smul_apply, smul_eq_mul, mul_zpow, Finset.prod_mul_distrib,
    prod_zpow_eq hc]

lemma monomial_one (k : Fin (n + 1) → ℤ) : monomial k (fun _ ↦ (1 : ℂ)) = 1 := by
  simp [monomial]

lemma monomial_const {c : ℂ} (hc : c ≠ 0) (k : Fin (n + 1) → ℤ) :
    monomial k (fun _ ↦ c) = c ^ (∑ i, k i) := by
  simp [monomial, prod_zpow_eq hc]

/-! ### Sections of `𝒪(d)` -/

/-- The space `𝒜_I^d` of functions holomorphic on `V I`, homogeneous of degree `d` there, and
vanishing outside `V I`: the sections of `𝒪(d)` over the standard open `U_I` of `ℙⁿ`. -/
def hol (d : ℤ) (I : Finset (Fin (n + 1))) : Submodule ℂ ((Fin (n + 1) → ℂ) → ℂ) where
  carrier := {f | DifferentiableOn ℂ f (V I) ∧
    (∀ z ∈ V I, ∀ c : ℂ, c ≠ 0 → f (c • z) = c ^ d * f z) ∧ ∀ z ∉ V I, f z = 0}
  add_mem' {f g} hf hg := ⟨hf.1.add hg.1, fun z hz c hc ↦ by
    simp [hf.2.1 z hz c hc, hg.2.1 z hz c hc, mul_add], fun z hz ↦ by
    simp [hf.2.2 z hz, hg.2.2 z hz]⟩
  zero_mem' := ⟨differentiableOn_const 0, by simp, by simp⟩
  smul_mem' a f hf := ⟨hf.1.const_smul a, fun z hz c hc ↦ by
    simp only [Pi.smul_apply, smul_eq_mul, hf.2.1 z hz c hc]; ring, fun z hz ↦ by
    simp [hf.2.2 z hz]⟩

/-- Restriction `hol d J → hol d I` along `V I ⊆ V J`, for `J ⊆ I`. -/
noncomputable def holRes (d : ℤ) {I J : Finset (Fin (n + 1))} (h : J ⊆ I) :
    hol d J →ₗ[ℂ] hol d I where
  toFun f := ⟨(V I).indicator f, ((f.2.1.mono (V_anti h)).congr fun z hz ↦
      indicator_of_mem hz _), fun z hz c hc ↦ by
      rw [indicator_of_mem (smul_mem_V hc hz), indicator_of_mem hz,
        f.2.2.1 z (V_anti h hz) c hc], fun z hz ↦ indicator_of_notMem hz _⟩
  map_add' f g := by ext z; by_cases hz : z ∈ V I <;> simp [hz]
  map_smul' a f := by ext z; by_cases hz : z ∈ V I <;> simp [hz]

lemma coe_holRes (d : ℤ) {I J : Finset (Fin (n + 1))} (h : J ⊆ I) (f : hol d J) :
    (holRes d h f : (Fin (n + 1) → ℂ) → ℂ) = (V I).indicator f :=
  rfl

/-! ### Coefficient families -/

variable (n) in
/-- Families of Laurent coefficients `k ↦ aₖ`, `k ∈ ℤⁿ⁺¹`. -/
abbrev Coeff : Type := (Fin (n + 1) → ℤ) → ℂ

/-- The negative support `{j | kⱼ < 0}` of an exponent. -/
def negSupp (k : Fin (n + 1) → ℤ) : Finset (Fin (n + 1)) := Finset.univ.filter fun j ↦ k j < 0

lemma mem_negSupp {k : Fin (n + 1) → ℤ} {j : Fin (n + 1)} : j ∈ negSupp k ↔ k j < 0 := by
  simp [negSupp]

/-- The projection onto the monomials with negative support `N`. -/
def proj (N : Finset (Fin (n + 1))) : Coeff n →ₗ[ℂ] Coeff n where
  toFun a k := if negSupp k = N then a k else 0
  map_add' a b := by ext k; split_ifs <;> simp [*]
  map_smul' c a := by ext k; split_ifs <;> simp [*]

lemma proj_apply (N : Finset (Fin (n + 1))) (a : Coeff n) (k : Fin (n + 1) → ℤ) :
    proj N a k = if negSupp k = N then a k else 0 :=
  rfl

variable (n) in
/-- The grading of coefficient families by negative supports. -/
def grading : Grading (Fin (n + 1)) (Coeff n) where
  proj N := (proj N).toAddMonoidHom
  sum_proj a := by
    ext k
    simp [Finset.sum_apply, proj_apply]
  proj_proj N N' a := by
    ext k
    simp only [LinearMap.toAddMonoidHom_coe, proj_apply]
    by_cases h : N = N'
    · subst h; by_cases h1 : negSupp k = N <;> simp [h1, proj_apply]
    · rw [if_neg h]
      by_cases h1 : negSupp k = N
      · subst h1; simp [h]
      · simp [h1]

@[simp]
lemma grading_proj (N : Finset (Fin (n + 1))) (a : Coeff n) :
    (grading n).proj N a = proj N a :=
  rfl

/-- Absolute convergence of `∑ₖ aₖ wᵏ`. -/
def SummableAt (a : Coeff n) (w : Fin (n + 1) → ℂ) : Prop :=
  Summable fun k ↦ ‖a k‖ * ∏ i, ‖w i‖ ^ k i

lemma summableAt_iff (a : Coeff n) (w : Fin (n + 1) → ℂ) :
    SummableAt a w ↔ Summable fun k ↦ ‖a k * monomial k w‖ := by
  simp [SummableAt, norm_monomial]

lemma SummableAt.of_le {a b : Coeff n} {w w' : Fin (n + 1) → ℂ} (h : SummableAt b w')
    (hab : ∀ k, a k ≠ 0 → ‖a k‖ ≤ ‖b k‖ ∧ ∀ i, ‖w i‖ ^ k i ≤ ‖w' i‖ ^ k i) :
    SummableAt a w := by
  refine h.of_nonneg_of_le (fun k ↦ mul_nonneg (norm_nonneg _)
    (Finset.prod_nonneg fun i _ ↦ zpow_nonneg (norm_nonneg _) _)) fun k ↦ ?_
  by_cases hk : a k = 0
  · simp only [hk, norm_zero, zero_mul]
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ ↦ zpow_nonneg (norm_nonneg _) _)
  · exact mul_le_mul (hab k hk).1 (Finset.prod_le_prod
      (fun i _ ↦ zpow_nonneg (norm_nonneg _) _) fun i _ ↦ (hab k hk).2 i)
      (Finset.prod_nonneg fun i _ ↦ zpow_nonneg (norm_nonneg _) _) (norm_nonneg _)

lemma summableAt_zero (w : Fin (n + 1) → ℂ) : SummableAt 0 w := by
  simp [SummableAt, summable_zero]

lemma SummableAt.add {a b : Coeff n} {w : Fin (n + 1) → ℂ} (ha : SummableAt a w)
    (hb : SummableAt b w) : SummableAt (a + b) w := by
  refine (Summable.add ha hb).of_nonneg_of_le (fun k ↦ mul_nonneg (norm_nonneg _)
    (Finset.prod_nonneg fun i _ ↦ zpow_nonneg (norm_nonneg _) _)) fun k ↦ ?_
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _)
    (Finset.prod_nonneg fun i _ ↦ zpow_nonneg (norm_nonneg _) _)

lemma SummableAt.smul {a : Coeff n} {w : Fin (n + 1) → ℂ} (ha : SummableAt a w) (c : ℂ) :
    SummableAt (c • a) w := by
  refine (ha.mul_left ‖c‖).congr fun k ↦ ?_
  simp [mul_assoc]

lemma summableAt_of_proj {a : Coeff n} {w : Fin (n + 1) → ℂ}
    (h : ∀ N, SummableAt (proj N a) w) : SummableAt a w := by
  refine (summable_sum fun N (_ : N ∈ Finset.univ) ↦ h N).congr fun k ↦ ?_
  simp [proj_apply, apply_ite, ite_mul]

lemma summableAt_of_finite {a : Coeff n} (s : Finset (Fin (n + 1) → ℤ))
    (hs : ∀ k ∉ s, a k = 0) (w : Fin (n + 1) → ℂ) : SummableAt a w :=
  summable_of_ne_finset_zero (s := s) fun k hk ↦ by simp [hs k hk]

variable (n) in
/-- The subgroup of coefficient families of degree `d` all of whose parts with fixed negative
support `N` converge absolutely on `V N`. It contains the coefficients of all sections. -/
def coeffSpace (d : ℤ) : Submodule ℂ (Coeff n) where
  carrier := {a | (∀ k, a k ≠ 0 → ∑ i, k i = d) ∧ ∀ N, ∀ w ∈ V N, SummableAt (proj N a) w}
  add_mem' {a b} ha hb := ⟨fun k hk ↦ by
    by_cases h : a k = 0
    · exact hb.1 k (by simpa [h] using hk)
    · exact ha.1 k h, fun N w hw ↦ by rw [map_add]; exact (ha.2 N w hw).add (hb.2 N w hw)⟩
  zero_mem' := ⟨fun k hk ↦ absurd rfl hk, fun N w _ ↦ by simpa using summableAt_zero w⟩
  smul_mem' c a ha := ⟨fun k hk ↦ ha.1 k fun h ↦ hk (by simp [h]), fun N w hw ↦ by
    rw [map_smul]; exact (ha.2 N w hw).smul c⟩

lemma proj_mem_coeffSpace {d : ℤ} (N : Finset (Fin (n + 1))) {a : Coeff n}
    (ha : a ∈ coeffSpace n d) : proj N a ∈ coeffSpace n d := by
  refine ⟨fun k hk ↦ ha.1 k fun h ↦ hk (by simp [proj_apply, h]), fun N' w hw ↦ ?_⟩
  have := (grading n).proj_proj N' N a
  simp only [grading_proj] at this
  rw [this]
  split_ifs with h
  · subst h; exact ha.2 N' w hw
  · exact summableAt_zero w

/-- The coefficient families of sections over `V I`: those in `coeffSpace n d` whose negative
supports lie in `I`. -/
def coef (d : ℤ) (I : Finset (Fin (n + 1))) : Submodule ℂ (Coeff n) where
  carrier := {a | a ∈ coeffSpace n d ∧ ∀ k, a k ≠ 0 → negSupp k ⊆ I}
  add_mem' {a b} ha hb := ⟨add_mem ha.1 hb.1, fun k hk ↦ by
    by_cases h : a k = 0
    · exact hb.2 k (by simpa [h] using hk)
    · exact ha.2 k h⟩
  zero_mem' := ⟨zero_mem _, fun k hk ↦ absurd rfl hk⟩
  smul_mem' c a ha := ⟨Submodule.smul_mem _ c ha.1, fun k hk ↦ ha.2 k fun h ↦ hk (by simp [h])⟩

lemma proj_eq_zero_of_negSupp {I N : Finset (Fin (n + 1))} {a : Coeff n}
    (ha : ∀ k, a k ≠ 0 → negSupp k ⊆ I) (hN : ¬ N ⊆ I) : proj N a = 0 := by
  ext k
  simp only [proj_apply, Pi.zero_apply]
  split_ifs with h
  · by_contra hk
    exact hN (h ▸ ha k hk)
  · rfl

lemma summableAt_of_mem_coef {d : ℤ} {I : Finset (Fin (n + 1))} {a : Coeff n}
    (ha : a ∈ coef d I) {w : Fin (n + 1) → ℂ} (hw : w ∈ V I) : SummableAt a w := by
  refine summableAt_of_proj fun N ↦ ?_
  by_cases hN : N ⊆ I
  · exact ha.1.2 N w (V_anti hN hw)
  · rw [proj_eq_zero_of_negSupp ha.2 hN]; exact summableAt_zero w

lemma isAdmissible_iff {p : ℕ} (x : Cochain (Fin (n + 1)) (Coeff n) p) :
    (grading n).IsAdmissible x ↔ ∀ i k, x i k ≠ 0 → negSupp k ⊆ im i := by
  refine ⟨fun h i k hk ↦ by_contra fun hN ↦ hk ?_, fun h i N hN ↦ ?_⟩
  · have := congrFun (h i _ hN) k
    simpa [proj_apply] using this
  · ext k
    simp only [grading_proj, proj_apply, Pi.zero_apply]
    split_ifs with hk
    · by_contra hx
      exact hN (hk ▸ h i k hx)
    · rfl

/-! ### Laurent coefficients of sections -/

/-- The multi-Laurent coefficients of `f` computed on the unit torus. -/
noncomputable def toCoeff (f : (Fin (n + 1) → ℂ) → ℂ) : Coeff n := mcoeff f fun _ ↦ 1

/-- The sum `∑ₖ aₖ zᵏ` on `V I`, extended by zero. -/
noncomputable def ofCoeff (I : Finset (Fin (n + 1))) (a : Coeff n) :
    (Fin (n + 1) → ℂ) → ℂ :=
  (V I).indicator fun z ↦ ∑' k, a k * monomial k z

variable {d : ℤ} {I : Finset (Fin (n + 1))} {f g : (Fin (n + 1) → ℂ) → ℂ}

lemma differentiableOn_polyAnnulus (hf : f ∈ hol d I) :
    DifferentiableOn ℂ f (polyAnnulus (radii I) fun _ ↦ ⊤) :=
  V_eq_polyAnnulus I ▸ hf.1

lemma hasSum_toCoeff (hf : f ∈ hol d I) {z : Fin (n + 1) → ℂ} (hz : z ∈ V I) :
    HasSum (fun k ↦ toCoeff f k * monomial k z) (f z) :=
  hasSum_mcoeff (differentiableOn_polyAnnulus hf) (isRadius_one I) (V_eq_polyAnnulus I ▸ hz)

lemma summableAt_toCoeff (hf : f ∈ hol d I) {z : Fin (n + 1) → ℂ} (hz : z ∈ V I) :
    SummableAt (toCoeff f) z :=
  (summableAt_iff _ _).2 (summable_norm_mcoeff_mul (differentiableOn_polyAnnulus hf)
    (isRadius_one I) (V_eq_polyAnnulus I ▸ hz))

/-- Uniqueness of Laurent coefficients on the unit torus. -/
lemma toCoeff_eq_of_hasSum {b : Coeff n} (hb : SummableAt b fun _ ↦ 1)
    (h : ∀ z ∈ torus (fun _ ↦ (1 : ℝ)), HasSum (fun k ↦ b k * monomial k z) (f z)) :
    toCoeff f = b :=
  funext (mcoeff_eq_of_hasSum (fun _ ↦ one_pos) (by simpa [SummableAt] using hb) h)

lemma toCoeff_indicator (J : Finset (Fin (n + 1))) (f : (Fin (n + 1) → ℂ) → ℂ) :
    toCoeff ((V J).indicator f) = toCoeff f :=
  funext fun k ↦ mcoeff_congr (fun _ ↦ zero_le_one)
    (fun _ hz ↦ indicator_of_mem (torus_subset_V J hz) f) k

/-- The Laurent coefficients of a homogeneous function of degree `d` are supported on exponents
of total degree `d`. -/
lemma sum_eq_of_toCoeff_ne_zero (hf : f ∈ hol d I) {k : Fin (n + 1) → ℤ}
    (hk : toCoeff f k ≠ 0) : ∑ i, k i = d := by
  set a := toCoeff f
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hb : SummableAt a fun _ ↦ 2 := summableAt_toCoeff hf (const_mem_V I h2)
  have e1 : toCoeff (fun z ↦ f ((2 : ℂ) • z)) = fun k ↦ a k * 2 ^ (∑ i, k i) := by
    refine toCoeff_eq_of_hasSum ?_ fun z hz ↦ ?_
    · rw [summableAt_iff] at hb ⊢
      simpa [monomial_one, monomial_const h2] using hb
    · convert hasSum_toCoeff hf (smul_mem_V h2 (torus_subset_V I hz)) using 1
      ext k
      rw [monomial_smul h2]
      ring
  have e2 : toCoeff (fun z ↦ f ((2 : ℂ) • z)) = (2 : ℂ) ^ d • a := by
    refine toCoeff_eq_of_hasSum
      ((summableAt_toCoeff hf (const_mem_V I one_ne_zero)).smul _) fun z hz ↦ ?_
    have hz' := torus_subset_V I hz
    rw [hf.2.1 z hz' 2 h2]
    simpa [mul_assoc] using (hasSum_toCoeff hf hz').mul_left ((2 : ℂ) ^ d)
  have h := congrFun (e1.symm.trans e2) k
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [mul_comm] at h
  have h' := congrArg norm (mul_right_cancel₀ hk h)
  simp only [norm_zpow, Complex.norm_ofNat] at h'
  exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) h'

/-- The Laurent coefficients of a function holomorphic on `V I` have negative supports in
`I`. -/
lemma negSupp_subset_of_toCoeff_ne_zero (hf : f ∈ hol d I) {k : Fin (n + 1) → ℤ}
    (hk : toCoeff f k ≠ 0) : negSupp k ⊆ I := by
  intro j hj
  by_contra hjI
  exact hk (mcoeff_eq_zero_of_neg (differentiableOn_polyAnnulus hf) (isRadius_one I) (i := j)
    (by simp [radii, hjI]) (mem_negSupp.1 hj))

lemma toCoeff_mem (hf : f ∈ hol d I) : toCoeff f ∈ coef d I := by
  classical
  have hneg := fun k (hk : toCoeff f k ≠ 0) ↦ negSupp_subset_of_toCoeff_ne_zero hf hk
  refine ⟨⟨fun k hk ↦ sum_eq_of_toCoeff_ne_zero hf hk, fun N w hw ↦ ?_⟩, hneg⟩
  by_cases hN : N ⊆ I
  · let w' : Fin (n + 1) → ℂ := fun j ↦ if j ∈ I ∧ j ∉ N then ((‖w j‖ + 1 : ℝ) : ℂ) else w j
    have hw' : w' ∈ V I := fun j hj ↦ by
      by_cases hjN : j ∈ N
      · simp [w', hjN, hw j hjN]
      · simp only [w', hj, hjN, not_false_eq_true, and_self, if_true, ne_eq,
          Complex.ofReal_eq_zero]
        positivity
    refine (summableAt_toCoeff hf hw').of_le fun k hk ↦ ?_
    by_cases hkN : negSupp k = N
    swap
    · simp [proj_apply, hkN] at hk
    simp only [proj_apply, if_pos hkN]
    refine ⟨le_rfl, fun i ↦ ?_⟩
    by_cases hi : i ∈ I ∧ i ∉ N
    · have : 0 ≤ k i := not_lt.1 fun h ↦ hi.2 (hkN ▸ mem_negSupp.2 h)
      simp only [w', hi, not_false_eq_true, and_self, if_true, Complex.norm_real,
        Real.norm_eq_abs]
      rw [abs_of_pos (by positivity)]
      exact zpow_le_zpow_left₀ this (norm_nonneg _) (by linarith)
    · simp only [w', hi, if_false, le_refl]
  · rw [proj_eq_zero_of_negSupp hneg hN]
    exact summableAt_zero w

lemma hasSum_ofCoeff {a : Coeff n} (ha : a ∈ coef d I) {z : Fin (n + 1) → ℂ} (hz : z ∈ V I) :
    HasSum (fun k ↦ a k * monomial k z) (ofCoeff I a z) := by
  rw [ofCoeff, indicator_of_mem hz]
  exact (Summable.of_norm ((summableAt_iff _ _).1 (summableAt_of_mem_coef ha hz))).hasSum

lemma ofCoeff_mem {a : Coeff n} (ha : a ∈ coef d I) : ofCoeff I a ∈ hol d I := by
  refine ⟨?_, fun z hz c hc ↦ ?_, fun z hz ↦ indicator_of_notMem hz _⟩
  · have hb0 : ∀ k i, radii I i < 0 → k i < 0 → a k = 0 := fun k i hr hk ↦ by
      by_contra hak
      have := ha.2 k hak (mem_negSupp.2 hk)
      simp [radii, this] at hr
    have := differentiableOn_tsum_monomial hb0
      (fun w hw ↦ summableAt_of_mem_coef ha ((V_eq_polyAnnulus I).symm ▸ hw))
    rw [← V_eq_polyAnnulus] at this
    exact this.congr fun z hz ↦ indicator_of_mem hz _
  · rw [← (hasSum_ofCoeff ha (smul_mem_V hc hz)).tsum_eq, ← (hasSum_ofCoeff ha hz).tsum_eq,
      ← tsum_mul_left]
    congr 1
    ext k
    rw [monomial_smul hc]
    by_cases hk : a k = 0
    · simp [hk]
    · rw [ha.1.1 k hk]; ring

lemma toCoeff_ofCoeff {a : Coeff n} (ha : a ∈ coef d I) : toCoeff (ofCoeff I a) = a :=
  toCoeff_eq_of_hasSum (summableAt_of_mem_coef ha (const_mem_V I one_ne_zero))
    fun _ hz ↦ hasSum_ofCoeff ha (torus_subset_V I hz)

lemma ofCoeff_toCoeff (hf : f ∈ hol d I) : ofCoeff I (toCoeff f) = f := by
  ext z
  by_cases hz : z ∈ V I
  · exact (hasSum_ofCoeff (toCoeff_mem hf) hz).unique (hasSum_toCoeff hf hz)
  · rw [ofCoeff, indicator_of_notMem hz, hf.2.2 z hz]

lemma toCoeff_add (hf : f ∈ hol d I) (hg : g ∈ hol d I) :
    toCoeff (f + g) = toCoeff f + toCoeff g :=
  toCoeff_eq_of_hasSum ((summableAt_toCoeff hf (const_mem_V I one_ne_zero)).add
    (summableAt_toCoeff hg (const_mem_V I one_ne_zero))) fun z hz ↦ by
    have hz' := torus_subset_V I hz
    simpa [add_mul] using (hasSum_toCoeff hf hz').add (hasSum_toCoeff hg hz')

lemma toCoeff_smul (hf : f ∈ hol d I) (c : ℂ) : toCoeff (c • f) = c • toCoeff f :=
  toCoeff_eq_of_hasSum ((summableAt_toCoeff hf (const_mem_V I one_ne_zero)).smul c)
    fun z hz ↦ by
    simpa [mul_assoc] using (hasSum_toCoeff hf (torus_subset_V I hz)).mul_left c

variable (d I) in
/-- Sections of `𝒪(d)` over `V I` are identified with their Laurent coefficients. -/
noncomputable def holEquiv : hol d I ≃ₗ[ℂ] coef d I where
  toFun f := ⟨toCoeff f, toCoeff_mem f.2⟩
  map_add' f g := Subtype.ext (toCoeff_add f.2 g.2)
  map_smul' c f := Subtype.ext (toCoeff_smul f.2 c)
  invFun a := ⟨ofCoeff I a, ofCoeff_mem a.2⟩
  left_inv f := Subtype.ext (ofCoeff_toCoeff f.2)
  right_inv a := Subtype.ext (toCoeff_ofCoeff a.2)

@[simp]
lemma coe_holEquiv (f : hol d I) : (holEquiv d I f : Coeff n) = toCoeff f :=
  rfl

@[simp]
lemma coe_holEquiv_symm (a : coef d I) :
    ((holEquiv d I).symm a : (Fin (n + 1) → ℂ) → ℂ) = ofCoeff I a :=
  rfl

/-! ### The Čech complex -/

/-- The ordered Čech cochains `C^p = ∏_{i : Fin (p + 1) → Fin (n + 1)} 𝒜^d_{im i}` of `𝒪(d)`
for the standard cover of `ℙⁿ`. -/
abbrev HolCochain (d : ℤ) (n p : ℕ) : Type := ∀ i : Fin (p + 1) → Fin (n + 1), hol d (im i)

variable (d) in
/-- The Čech differential `(d x) i = ∑ₖ (-1) ^ k • (x (i ∘ δₖ))|_{V (im i)}`. -/
noncomputable def holD (p : ℕ) : HolCochain d n p →ₗ[ℂ] HolCochain d n (p + 1) where
  toFun x i := ∑ k : Fin (p + 2), ((-1 : ℤ) ^ (k : ℕ)) •
    holRes d (im_comp_subset i k.succAbove) (x fun a ↦ i (k.succAbove a))
  map_add' x y := by
    funext i
    simp [Finset.sum_add_distrib, smul_add]
  map_smul' c x := by
    funext i
    simp [Finset.smul_sum, smul_comm c]

/-- The Laurent coefficients of a Čech cochain, as a cochain with values in `Coeff n`. -/
noncomputable def toCochain {p : ℕ} (x : HolCochain d n p) : Cochain (Fin (n + 1)) (Coeff n) p :=
  fun i ↦ toCoeff (x i)

lemma toCochain_mem {p : ℕ} (x : HolCochain d n p) (i : Fin (p + 1) → Fin (n + 1)) :
    toCochain x i ∈ coef d (im i) :=
  toCoeff_mem (x i).2

lemma isAdmissible_toCochain {p : ℕ} (x : HolCochain d n p) :
    (grading n).IsAdmissible (toCochain x) :=
  (isAdmissible_iff _).2 fun i k hk ↦ (toCochain_mem x i).2 k hk

lemma toCochain_injective {p : ℕ} : Function.Injective (toCochain (d := d) (n := n) (p := p)) :=
  fun _ _ h ↦ funext fun i ↦ (holEquiv d (im i)).injective (Subtype.ext (congrFun h i))

@[simp]
lemma toCochain_zero {p : ℕ} : toCochain (0 : HolCochain d n p) = 0 := by
  funext i
  change toCoeff ((0 : hol d (im i)) : (Fin (n + 1) → ℂ) → ℂ) = 0
  rw [← coe_holEquiv, map_zero]
  rfl

lemma exists_toCochain_eq {p : ℕ} (y : Cochain (Fin (n + 1)) (Coeff n) p)
    (hy : ∀ i, y i ∈ coef d (im i)) : ∃ x : HolCochain d n p, toCochain x = y :=
  ⟨fun i ↦ (holEquiv d (im i)).symm ⟨y i, hy i⟩, funext fun i ↦ by
    change toCoeff ((holEquiv d (im i)).symm ⟨y i, hy i⟩ : (Fin (n + 1) → ℂ) → ℂ) = y i
    rw [← coe_holEquiv, LinearEquiv.apply_symm_apply]⟩

lemma toCochain_holD {p : ℕ} (x : HolCochain d n p) :
    toCochain (holD d p x) = SimplexCochain.d p (toCochain x) := by
  funext i
  rw [SimplexCochain.d_apply]
  change toCoeff ((∑ k : Fin (p + 2), ((-1 : ℤ) ^ (k : ℕ)) •
    holRes d (im_comp_subset i k.succAbove) (x fun a ↦ i (k.succAbove a)) : hol d (im i)) :
      (Fin (n + 1) → ℂ) → ℂ) = _
  rw [← coe_holEquiv, map_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_zsmul, Submodule.coe_smul_of_tower, coe_holEquiv, coe_holRes, toCoeff_indicator]
  rfl

@[simp]
lemma holD_holD {p : ℕ} (x : HolCochain d n p) : holD d (p + 1) (holD d p x) = 0 :=
  toCochain_injective (by rw [toCochain_holD, toCochain_holD, d_d, toCochain_zero])

lemma proj_univ_eq_zero_of_lt {a : Coeff n} (ha : a ∈ coeffSpace n d)
    (hd : -((n : ℤ) + 1) < d) : proj Finset.univ a = 0 := by
  ext k
  simp only [proj_apply, Pi.zero_apply]
  split_ifs with hk
  · by_contra hak
    have hs := ha.1 k hak
    have : ∑ i, k i ≤ ∑ _i : Fin (n + 1), (-1 : ℤ) := Finset.sum_le_sum fun i _ ↦ by
      have := mem_negSupp.1 (hk ▸ Finset.mem_univ i)
      omega
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    push_cast at this
    omega
  · rfl

/-- **Exactness of the analytic Čech complex of `𝒪(d)` on `ℙⁿ`** in degree `q = p + 1`, if
`q > n`, or `0 < q < n`, or `d > -n - 1`. -/
theorem holD_exact (d : ℤ) (p : ℕ) (hp : n ≤ p ∨ p + 1 < n ∨ -((n : ℤ) + 1) < d) :
    Function.Exact (holD d (n := n) p) (holD d (p + 1)) := by
  intro x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have hdx : SimplexCochain.d (p + 1) (toCochain x) = 0 := by
      rw [← toCochain_holD, hx, toCochain_zero]
    have hadm := isAdmissible_toCochain x
    obtain ⟨y, hy, hyS, hdy⟩ := (grading n).exists_eq_d (coeffSpace n d).toAddSubgroup
      (fun N _ hm ↦ proj_mem_coeffSpace N hm) (toCochain x) hadm
      (fun i ↦ (toCochain_mem x i).1) hdx (by
        rcases hp with hp | hp | hp
        · left; simpa using hp
        · right; exact (grading n).proj_univ_eq_zero hadm (by simpa using hp)
        · right; intro i; exact proj_univ_eq_zero_of_lt (toCochain_mem x i).1 hp)
    obtain ⟨w, hw⟩ := exists_toCochain_eq y fun i ↦ ⟨hyS i, (isAdmissible_iff y).1 hy i⟩
    exact ⟨w, toCochain_injective (by rw [toCochain_holD, hw, hdy])⟩
  · rintro ⟨w, rfl⟩
    exact holD_holD w

/-! ### Degree zero: homogeneous polynomials -/

/-- The exponent of a monomial, as an element of `ℤⁿ⁺¹`. -/
def expToInt (s : Fin (n + 1) →₀ ℕ) : Fin (n + 1) → ℤ := fun i ↦ s i

lemma expToInt_injective : Function.Injective (expToInt (n := n)) := fun s t h ↦ by
  ext i
  simpa [expToInt] using congrFun h i

lemma sum_expToInt (s : Fin (n + 1) →₀ ℕ) : ∑ i, expToInt s i = (s.degree : ℤ) := by
  simp [expToInt, Finsupp.degree_eq_sum]

variable (n) in
/-- The coefficient family of a polynomial. -/
noncomputable def polyCoeff : MvPolynomial (Fin (n + 1)) ℂ →ₗ[ℂ] Coeff n where
  toFun P k := if ∀ i, 0 ≤ k i then
    P.coeff (Finsupp.equivFunOnFinite.symm fun i ↦ (k i).toNat) else 0
  map_add' P Q := by ext k; by_cases h : ∀ i, 0 ≤ k i <;> simp [h]
  map_smul' c P := by ext k; by_cases h : ∀ i, 0 ≤ k i <;> simp [h]

lemma polyCoeff_apply (P : MvPolynomial (Fin (n + 1)) ℂ) (k : Fin (n + 1) → ℤ) :
    polyCoeff n P k = if ∀ i, 0 ≤ k i then
      P.coeff (Finsupp.equivFunOnFinite.symm fun i ↦ (k i).toNat) else 0 :=
  rfl

lemma expToInt_toNat {k : Fin (n + 1) → ℤ} (hk : ∀ i, 0 ≤ k i) :
    expToInt (Finsupp.equivFunOnFinite.symm fun i ↦ (k i).toNat) = k := by
  ext i
  simp [expToInt, hk i]

lemma polyCoeff_expToInt (P : MvPolynomial (Fin (n + 1)) ℂ) (s : Fin (n + 1) →₀ ℕ) :
    polyCoeff n P (expToInt s) = P.coeff s := by
  rw [polyCoeff_apply, if_pos fun i ↦ by simp [expToInt]]
  congr
  ext i
  simp [expToInt]

lemma exists_expToInt_of_polyCoeff_ne_zero {P : MvPolynomial (Fin (n + 1)) ℂ}
    {k : Fin (n + 1) → ℤ} (hk : polyCoeff n P k ≠ 0) :
    ∃ s, P.coeff s ≠ 0 ∧ expToInt s = k := by
  rw [polyCoeff_apply] at hk
  split_ifs at hk with h0
  · exact ⟨_, hk, expToInt_toNat h0⟩
  · exact absurd rfl hk

lemma polyCoeff_eq_zero_of_notMem (P : MvPolynomial (Fin (n + 1)) ℂ) {k : Fin (n + 1) → ℤ}
    (hk : k ∉ P.support.image expToInt) : polyCoeff n P k = 0 := by
  by_contra h
  obtain ⟨s, hs, rfl⟩ := exists_expToInt_of_polyCoeff_ne_zero h
  exact hk (Finset.mem_image_of_mem _ (MvPolynomial.mem_support_iff.2 hs))

lemma hasSum_polyCoeff (P : MvPolynomial (Fin (n + 1)) ℂ) (z : Fin (n + 1) → ℂ) :
    HasSum (fun k ↦ polyCoeff n P k * monomial k z) (MvPolynomial.eval z P) := by
  have h : MvPolynomial.eval z P =
      ∑ k ∈ P.support.image expToInt, polyCoeff n P k * monomial k z := by
    rw [MvPolynomial.eval_eq', Finset.sum_image expToInt_injective.injOn]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [polyCoeff_expToInt]
    simp [monomial, expToInt]
  rw [h]
  exact hasSum_sum_of_ne_finset_zero fun k hk ↦ by rw [polyCoeff_eq_zero_of_notMem P hk, zero_mul]

lemma polyCoeff_mem {e : ℕ} {P : MvPolynomial (Fin (n + 1)) ℂ}
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ e) (I : Finset (Fin (n + 1))) :
    polyCoeff n P ∈ coef (e : ℤ) I := by
  rw [MvPolynomial.mem_homogeneousSubmodule] at hP
  refine ⟨⟨fun k hk ↦ ?_, fun N w _ ↦ summableAt_of_finite (P.support.image expToInt)
    (fun k hk ↦ ?_) w⟩, fun k hk ↦ ?_⟩
  · obtain ⟨s, hs, rfl⟩ := exists_expToInt_of_polyCoeff_ne_zero hk
    have : s.degree = e := by rw [Finsupp.degree_eq_weight_one]; exact hP hs
    rw [sum_expToInt, this]
  · simp [proj_apply, polyCoeff_eq_zero_of_notMem P hk]
  · obtain ⟨s, -, rfl⟩ := exists_expToInt_of_polyCoeff_ne_zero hk
    intro j hj
    have := mem_negSupp.1 hj
    simp only [expToInt] at this
    omega

variable (n) in
/-- The augmentation `P ↦ (i ↦ P|_{V (im i)})` from homogeneous polynomials of degree `e`. -/
noncomputable def holAug (e : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ e →ₗ[ℂ] HolCochain (e : ℤ) n 0 :=
  LinearMap.pi fun i ↦ (holEquiv (e : ℤ) (im i)).symm.toLinearMap ∘ₗ
    ((polyCoeff n).comp (Submodule.subtype _)).codRestrict (coef (e : ℤ) (im i))
      fun P ↦ polyCoeff_mem P.2 _

lemma holAug_apply {e : ℕ} (P : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ e)
    (i : Fin 1 → Fin (n + 1)) {z : Fin (n + 1) → ℂ} (hz : z ∈ V (im i)) :
    (holAug n e P i : (Fin (n + 1) → ℂ) → ℂ) z =
      MvPolynomial.eval z (P : MvPolynomial (Fin (n + 1)) ℂ) :=
  (hasSum_ofCoeff (polyCoeff_mem P.2 _) hz).unique (hasSum_polyCoeff _ z)

lemma toCochain_holAug {e : ℕ} (P : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ e) :
    toCochain (holAug n e P) = SimplexCochain.aug (polyCoeff n P) := by
  funext i
  change toCoeff (ofCoeff (im i) (polyCoeff n P)) = _
  rw [toCoeff_ofCoeff (polyCoeff_mem P.2 _)]
  rfl

@[simp]
lemma holD_holAug {e : ℕ} (P : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ e) :
    holD (e : ℤ) 0 (holAug n e P) = 0 :=
  toCochain_injective (by rw [toCochain_holD, toCochain_holAug, d_aug, toCochain_zero])

theorem holAug_injective (e : ℕ) : Function.Injective (holAug n e) := by
  intro P Q h
  have h' := congrFun (congrArg toCochain h) fun _ ↦ 0
  rw [toCochain_holAug, toCochain_holAug] at h'
  refine Subtype.ext (MvPolynomial.ext _ _ fun s ↦ ?_)
  rw [← polyCoeff_expToInt, ← polyCoeff_expToInt]
  exact congrFun h' _

lemma nonneg_of_proj_empty {v : Coeff n} (hv : proj ∅ v = v) {k : Fin (n + 1) → ℤ}
    (hk : v k ≠ 0) (i : Fin (n + 1)) : 0 ≤ k i := by
  have h := congrFun hv k
  rw [proj_apply] at h
  split_ifs at h with h0
  · exact not_lt.1 fun hi ↦ by simpa [h0] using mem_negSupp.2 hi
  · exact absurd h.symm hk

/-- The `0`-cocycles of the Čech complex are the coefficient families of constant cochains
supported on nonnegative exponents. -/
lemma exists_toCochain_eq_aug (x : HolCochain d n 0) (hx : holD d 0 x = 0)
    (hn : 0 < n ∨ -((n : ℤ) + 1) < d) :
    ∃ v ∈ coeffSpace n d, (∀ k, v k ≠ 0 → ∀ i, 0 ≤ k i) ∧ toCochain x = SimplexCochain.aug v := by
  have hdx : SimplexCochain.d 0 (toCochain x) = 0 := by rw [← toCochain_holD, hx, toCochain_zero]
  have hadm := isAdmissible_toCochain x
  obtain ⟨v, hv, hxv⟩ := (grading n).exists_eq_aug (toCochain x) hadm hdx (by
    rcases hn with hn | hn
    · exact (grading n).proj_univ_eq_zero hadm (by simpa using hn)
    · intro i; exact proj_univ_eq_zero_of_lt (toCochain_mem x i).1 hn)
  have hvx : v = toCochain x fun _ ↦ 0 := by rw [hxv]; rfl
  exact ⟨v, hvx ▸ (toCochain_mem x _).1, fun k hk ↦ nonneg_of_proj_empty hv hk, hxv⟩

/-- **`H⁰` of `𝒪(e)`, `e ≥ 0`**: the `0`-cocycles are exactly the (restrictions of) homogeneous
polynomials of degree `e`. -/
theorem holAug_exact (e : ℕ) : Function.Exact (holAug n e) (holD (e : ℤ) 0) := by
  intro x
  refine ⟨fun hx ↦ ?_, by rintro ⟨P, rfl⟩; exact holD_holAug P⟩
  obtain ⟨v, hvS, hv0, hxv⟩ := exists_toCochain_eq_aug x hx (Or.inr (by omega))
  have hfin : (Function.support fun s : Fin (n + 1) →₀ ℕ ↦ v (expToInt s)).Finite :=
    (Finsupp.finite_of_degree_le e).subset fun s hs ↦ by
      have := hvS.1 _ hs
      rw [sum_expToInt] at this
      simp only [mem_setOf_eq]
      omega
  let P : MvPolynomial (Fin (n + 1)) ℂ := AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite _ hfin)
  have hP (s : Fin (n + 1) →₀ ℕ) : P.coeff s = v (expToInt s) := rfl
  have hPv : polyCoeff n P = v := by
    funext k
    rw [polyCoeff_apply]
    split_ifs with h0
    · rw [hP, expToInt_toNat h0]
    · by_contra hk
      exact h0 (hv0 k (Ne.symm hk))
  have hPh : P ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ e := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    intro s hs
    rw [hP] at hs
    have := hvS.1 _ hs
    rw [sum_expToInt] at this
    have h : s.degree = e := by exact_mod_cast this
    rw [Finsupp.degree_eq_weight_one] at h
    exact h
  exact ⟨⟨P, hPh⟩, toCochain_injective (by rw [toCochain_holAug, hxv]; exact congrArg _ hPv)⟩

/-- **`H⁰` of `𝒪(d)`, `d < 0`**: there are no nonzero `0`-cocycles (for `n ≥ 1`). -/
theorem holD_zero_injective {d : ℤ} (hd : d < 0) (hn : 0 < n ∨ -((n : ℤ) + 1) < d) :
    Function.Injective (holD d (n := n) 0) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨v, hvS, hv0, hxv⟩ := exists_toCochain_eq_aug x hx hn
  have hv : v = 0 := by
    funext k
    by_contra hk
    have h1 := hvS.1 k hk
    have h2 : 0 ≤ ∑ i, k i := Finset.sum_nonneg fun i _ ↦ hv0 k hk i
    omega
  exact toCochain_injective (by rw [hxv, hv, map_zero, toCochain_zero])

/-! ### The case `d = 0` -/

/-- For `d = 0` the Čech complex of holomorphic functions of degree `0` on the standard cover
of `ℙⁿ` is exact in all positive degrees. -/
theorem holD_exact_zero (p : ℕ) : Function.Exact (holD 0 (n := n) p) (holD 0 (p + 1)) :=
  holD_exact 0 p (Or.inr (Or.inr (by omega)))

/-- For `d = 0` the `0`-cocycles are the constants: `H⁰ = ℂ`. -/
theorem holD_zero_eq_zero_iff (x : HolCochain 0 n 0) :
    holD 0 0 x = 0 ↔ ∃ c : ℂ, ∀ i, ∀ z ∈ V (im i), (x i : (Fin (n + 1) → ℂ) → ℂ) z = c := by
  constructor
  · intro hx
    obtain ⟨P, rfl⟩ := (holAug_exact (n := n) 0 x).1 hx
    have hP := (MvPolynomial.mem_homogeneousSubmodule _ _).1 P.2
    refine ⟨(P : MvPolynomial (Fin (n + 1)) ℂ).coeff 0, fun i z hz ↦ ?_⟩
    rw [holAug_apply P i hz]
    by_cases h0 : (P : MvPolynomial (Fin (n + 1)) ℂ) = 0
    · simp [h0]
    · rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 (hP.totalDegree h0), MvPolynomial.eval_C,
        MvPolynomial.coeff_C, if_pos rfl]
  · rintro ⟨c, hc⟩
    let P : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ 0 :=
      ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C _ c⟩
    have hx : x = holAug n 0 P := by
      funext i
      refine Subtype.ext (funext fun z ↦ ?_)
      by_cases hz : z ∈ V (im i)
      · rw [holAug_apply P i hz, hc i z hz, MvPolynomial.eval_C]
      · rw [(x i).2.2.2 z hz, (holAug n 0 P i).2.2.2 z hz]
    rw [hx]
    exact holD_holAug P

end CechProjectiveAn

end
