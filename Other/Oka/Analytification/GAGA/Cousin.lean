/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.CauchyRectangle
public import Other.Oka.Analytification.GAGA.ParametricIntervalIntegral

/-!
# Cousin splitting on rectangles

This file provides the basic analytic input for Theorem B for the structure sheaf on product
domains: Cauchy integrals over the sides of a rectangle, with holomorphic dependence on
parameters, and the Cousin splitting lemma. The module docstring also records the plan for the
rest of Theorem B (part P8 of the GAGA blueprint).

## Main definitions

- `Complex.cauchyBottom f a b`, `Complex.cauchyRight f a b`, `Complex.cauchyTop f a b`,
  `Complex.cauchyLeft f a b`: for `f : ℂ × E → ℂ`, the functions `(z, w) ↦ (2πi)⁻¹ ∫ f (ζ, w) /
  (ζ - z) dζ` over the four sides of the positively oriented boundary of the rectangle with lower
  left corner `a` and upper right corner `b`.

## Main results

- `Complex.differentiableOn_cauchyEdge`: `(z, w) ↦ ∫ (γ t - z)⁻¹ f (γ t, w) dt` is holomorphic
  (jointly) off the path `γ`, for `w` in an open subset of a finite-dimensional space `E`.
- `Complex.differentiableOn_cauchyBottom` (and `Right`, `Top`, `Left`): each side integral is
  holomorphic off its side.
- `Complex.sum_cauchySides_of_mem`, `Complex.sum_cauchySides_of_notMem`: **Cauchy
  decomposition**: the four side integrals sum to `f` on the open rectangle and to `0` off the
  closed rectangle.
- `Complex.exists_cousin_split_re`, `Complex.exists_cousin_split_im`: **Cousin splitting** with
  holomorphic parameters: `f = f₁ - f₂` on the open rectangle with `f₁` holomorphic on a half-plane
  `{Re z < b.re}` (resp. `{Im z < b.im}`) and `f₂` on the opposite half-strip. One-variable
  versions: `Complex.exists_cousin_split_re_of_differentiableOn`, `..._im_...`.
- `Complex.RectSide`, `Complex.RectSide.cauchy`, `Complex.RectSide.set`: the four sides as an
  enumeration; `Complex.RectSide.differentiableOn_sum_cauchy`,
  `Complex.RectSide.sum_add_sum_compl_of_mem`, `Complex.RectSide.sum_add_sum_compl_of_notMem`:
  **Cousin splitting by grouping sides**: for any set `S` of sides, `f` is the sum of the side
  integrals over `S` (holomorphic off the sides in `S`) and over the other sides, on the open
  rectangle, and this sum vanishes off the closed rectangle.

Grouping the sides gives all splittings used below, e.g. for two rectangles `T`, `L` meeting in a
corner rectangle `C = T ∩ L` (shrunk to a closed rectangle): the integrals over the sides of `C`
not meeting `T` are holomorphic on (the shrunk) `T`, the others on `L`, and their sum vanishes
off `C`, which lets several corners be treated at once. The version for `OkaRing` (sections of
the structure sheaf of `ℂ^ι`, one coordinate singled out) is `OkaRing.exists_cousin_split` in
`Oka.Analytification.GAGA.CousinCoordinate`.

## Plan for Theorem B (Mayer–Vietoris route)

We follow Grauert–Remmert's route by Cousin integrals and exhaustion. The Dolbeault route would
need, beyond the same exhaustion argument, smooth forms, area integrals with singular kernel
(Cauchy–Pompeiu, i.e. Green's formula) and fine resolutions; the Cousin route needs only line
integrals over segments.

**Domains.** A holed rectangle (`Complex.HoledRect`) is `(x₀, x₁) × (y₀, y₁) \ [-r, r]²` (no hole
if `r < 0`); `𝒮` denotes the products `HoledRect.prod s ⊆ ℂ^ι` of such, and
`D = puncturedSet P = (ℂ^×)^P × ℂ^{ι \ P}` (the finite intersections of the standard charts of
`ℙⁿ_an`, in chart coordinates). **Goal:** `H^q(D, 𝒪) = 0` for `q ≥ 1`. The same argument, with
exhaustions by boxes and `Complex.exists_approx_entire_of_rect` in `Complex.exists_approx_pi`,
gives it for bounded boxes (products of rectangles).

Caveat: Čech vanishing for *finite* covers alone does not give acyclicity of non-compact sets (a
cover of an open box needs infinitely many members near the boundary), so an exhaustion argument
is unavoidable. The split below puts it at the sheaf level.

**Sheaf-level lemmas to be supplied by P1/P2** (for an abelian sheaf `F` on a space `X`):
- (S1) *local vanishing*: every class in `H^q(U, F)`, `q ≥ 1`, restricts to zero on the members
  of some open cover of `U`;
- (S2) *Mayer–Vietoris* for `U = A ∪ B`, natural with respect to restriction to `A' ∪ B'` with
  `A' ⊆ A`, `B' ⊆ B`; in degree `0 → 1` the connecting map kills `(a + b)|_{A ∩ B}` for
  `a ∈ F(A)`, `b ∈ F(B)`;
- (S3) *exhaustion (Milnor)*: if `U = ⋃ U_n` increasing, `c ∈ H^q(U, F)` restricts to zero on
  every `U_n`, and `lim¹_n H^{q-1}(U_n, F) = 0`, then `c = 0`. Here `lim¹ = 0` for a tower
  `(M_n)` means: for all `g_n ∈ M_n` there are `f_n ∈ M_n` with `g_n = f_n - f_{n+1}|`; it holds
  if all transition maps are zero.

**Proof skeleton**, by induction on `q ≥ 1`. For `c ∈ H^q(W, 𝒪)` let `𝒵_c` be the family of
`W' ⊆ W` such that `c|_{W''} = 0` for all open `W''` with compact closure in `W'`.
1. *(Z_q)* For `S ∈ 𝒮` (or `S = D`) and `c ∈ H^q(S, 𝒪)`, `c|_{W'} = 0` whenever `W'` has compact
   closure in `S`. Indeed `closure W'` lies in some `prod s₀` with compact closure in `S`
   (`HoledRect.exists_subset_prod_shrink`, `HoledRect.exists_prod_of_isCompact`), and
   `prod s₀ ∈ 𝒵_c` by the merging theorem `HoledRect.mem_of_merge`, whose hypotheses are:
   `∅ ∈ 𝒵_c`, closure under subsets, the local hypothesis (by (S1)), and closure under the cuts
   `MergeRe`, `MergeIm`. The last is the *merge lemma*: for a cut `prod s = A ∪ B`
   (`HoledRect.prod_cutRe_union`) with `A, B ∈ 𝒵_c`, and `W''` with compact closure `K` in
   `A ∪ B`, take the shrinkings `A'' ⋐ A' ⋐ A`, `B'' ⋐ B' ⋐ B` of `Complex.CousinShrinkable`
   (`Complex.cousinShrinkable_cutRe`, `Complex.cousinShrinkable_cutIm`). By (S2) for
   `A' ∪ B'`, `c|_{A' ∪ B'} = ∂ d` with `d ∈ H^{q-1}(A' ∩ B')`; restricting to `A'' ∪ B'' ⊇ K`
   gives `c|_{A'' ∪ B''} = ∂ (d|_{A'' ∩ B''})`, and `d|_{A'' ∩ B''} = 0` in `H^{q-1}` modulo the
   image of `𝒪(A'') ⊕ 𝒪(B'')`: for `q = 1` by the splitting in `CousinShrinkable`, for `q ≥ 2` by
   `(Z_{q-1})` for `A' ∩ B' ∈ 𝒮`, since `A'' ∩ B''` has compact closure in `A' ∩ B'`.
2. *(B_q)* `H^q(D, 𝒪) = 0`: by (S3) along the exhaustion `U n = prod (Complex.exhaustion P n)`
   of `D` (`Complex.iUnion_exhaustion`, `Complex.monotone_exhaustion`), whose members have
   compact closure in the next (`Complex.closure_exhaustion_subset`): `c|_{U n} = 0` by `(Z_q)`;
   for `q ≥ 2` the transition maps `H^{q-1}(U (n+1)) → H^{q-1}(U n)` vanish by `(Z_{q-1})`, and
   for `q = 1`, `lim¹_n 𝒪(U n) = 0` is `Complex.exists_mittagLeffler_exhaustion`.

**Analytic input (this part, P8), all proved:**
- (C) Cousin splitting after shrinking for the cuts: `Complex.cousinShrinkable_cutRe`,
  `Complex.cousinShrinkable_cutIm` (`Oka.Analytification.GAGA.CousinShrink`), from the Cauchy
  decomposition of this file (grouping sides of rectangles, `Complex.exists_split_of_rects`).
  The cut is chosen so that its strip avoids the edges `±r` of the hole; then the overlap is one
  rectangle or two rectangles (above and below the hole), and all pieces are again holed
  rectangles. The combinatorics of merging is `Complex.HoledRect.mem_of_merge`
  (`Oka.Analytification.GAGA.GridMerge`).
- (W) Weierstrass' theorem in several variables:
  `differentiableOn_of_tendstoLocallyUniformlyOn` (`Oka.Analytification.GAGA.MittagLeffler`).
- (R) Runge approximation with holomorphic parameters: on rectangles by entire functions
  (`Complex.exists_approx_entire_of_rect`), on frames `[rectangle] \ (-ρ, ρ)²` by functions
  holomorphic on `ℂ^×` (`Complex.exists_approx_punctured_of_frame`, via the Cauchy formula on
  frames `Complex.frame_cauchy`), and on products one coordinate at a time
  (`Complex.exists_approx_pi`).
- (ML) `lim¹_n 𝒪(U n) = 0` for the exhaustion of `D`: `Complex.exists_mittagLeffler_exhaustion`
  (from the abstract `exists_mittagLeffler` and `Complex.exists_approx_exhaustion`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

open Set MeasureTheory
open scoped Interval Real Topology

namespace Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Cauchy integrals along a path are holomorphic off the path**, jointly with holomorphic
parameters: if `f` is holomorphic on `V × P` and the path `γ` runs in `V`, then
`(z, w) ↦ ∫ t in t₀..t₁, (γ t - z)⁻¹ * f (γ t, w)` is holomorphic on `(ℂ \ γ[t₀, t₁]) × P`. -/
theorem differentiableOn_cauchyEdge {V : Set ℂ} {P : Set E} (hP : IsOpen P)
    {f : ℂ × E → ℂ} (hf : DifferentiableOn ℂ f (V ×ˢ P)) {γ : ℝ → ℂ} (hγ : Continuous γ)
    {t₀ t₁ : ℝ} (hγV : ∀ t ∈ [[t₀, t₁]], γ t ∈ V) :
    DifferentiableOn ℂ (fun p : ℂ × E ↦ ∫ t in t₀..t₁, (γ t - p.1)⁻¹ * f (γ t, p.2))
      ((γ '' [[t₀, t₁]])ᶜ ×ˢ P) := by
  have hW : IsOpen (γ '' [[t₀, t₁]])ᶜ := (isCompact_uIcc.image hγ).isClosed.isOpen_compl
  have hne : ∀ p ∈ (γ '' [[t₀, t₁]])ᶜ ×ˢ P, ∀ t ∈ [[t₀, t₁]], γ t - p.1 ≠ 0 :=
    fun p hp t ht h ↦ hp.1 ⟨t, ht, sub_eq_zero.mp h⟩
  have hfc : ContinuousOn f (V ×ˢ P) := hf.continuousOn
  refine differentiableOn_intervalIntegral (hW.prod hP) (fun t ht ↦ ?_) ?_
  · refine ((differentiableOn_const _).sub differentiableOn_fst).inv (fun p hp ↦ hne p hp t ht)
      |>.mul ?_
    exact hf.comp ((differentiableOn_const _).prodMk differentiableOn_snd)
      fun p hp ↦ ⟨hγV t ht, hp.2⟩
  · refine ContinuousOn.mul ?_ ?_
    · refine ContinuousOn.inv₀ (by fun_prop) fun q hq ↦ hne q.1 hq.1 q.2 hq.2
    · exact hfc.comp (by fun_prop) fun q hq ↦ ⟨hγV q.2 hq.2, hq.1.2⟩

section Sides

variable (f : ℂ × E → ℂ) (a b : ℂ)

/-- The Cauchy integral of `f (·, w)` along the bottom edge of the rectangle with lower left
corner `a` and upper right corner `b`, divided by `2πi`. -/
noncomputable def cauchyBottom (p : ℂ × E) : ℂ :=
  (2 * π * I)⁻¹ * ∫ x : ℝ in a.re..b.re, ((x : ℂ) + a.im * I - p.1)⁻¹ * f ((x : ℂ) + a.im * I, p.2)

/-- The Cauchy integral of `f (·, w)` along the (leftwards oriented) top edge of the rectangle
with corners `a` and `b`, divided by `2πi`. -/
noncomputable def cauchyTop (p : ℂ × E) : ℂ :=
  -((2 * π * I)⁻¹ *
    ∫ x : ℝ in a.re..b.re, ((x : ℂ) + b.im * I - p.1)⁻¹ * f ((x : ℂ) + b.im * I, p.2))

/-- The Cauchy integral of `f (·, w)` along the (upwards oriented) right edge of the rectangle
with corners `a` and `b`, divided by `2πi`. -/
noncomputable def cauchyRight (p : ℂ × E) : ℂ :=
  (2 * π * I)⁻¹ * (I *
    ∫ y : ℝ in a.im..b.im, ((b.re : ℂ) + y * I - p.1)⁻¹ * f ((b.re : ℂ) + y * I, p.2))

/-- The Cauchy integral of `f (·, w)` along the (downwards oriented) left edge of the rectangle
with corners `a` and `b`, divided by `2πi`. -/
noncomputable def cauchyLeft (p : ℂ × E) : ℂ :=
  -((2 * π * I)⁻¹ * (I *
    ∫ y : ℝ in a.im..b.im, ((a.re : ℂ) + y * I - p.1)⁻¹ * f ((a.re : ℂ) + y * I, p.2)))

variable {f a b}

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
/-- The four side integrals in terms of `rectBoundaryIntegral`. -/
lemma sum_cauchySides_eq (z : ℂ) (w : E) :
    cauchyBottom f a b (z, w) + cauchyRight f a b (z, w) + cauchyTop f a b (z, w) +
      cauchyLeft f a b (z, w) =
      (2 * π * I)⁻¹ * rectBoundaryIntegral (fun ζ ↦ (ζ - z)⁻¹ • f (ζ, w)) a b := by
  simp only [cauchyBottom, cauchyRight, cauchyTop, cauchyLeft, rectBoundaryIntegral,
    smul_eq_mul]
  ring

variable {V : Set ℂ} (hab : Icc a.re b.re ×ℂ Icc a.im b.im ⊆ V)
  {P : Set E} (hP : IsOpen P) (hf : DifferentiableOn ℂ f (V ×ˢ P))
include hab hP hf

/-- The bottom Cauchy integral is holomorphic off the bottom edge. -/
theorem differentiableOn_cauchyBottom (hre : a.re ≤ b.re) (him : a.im ≤ b.im) :
    DifferentiableOn ℂ (cauchyBottom f a b)
      (((fun x : ℝ ↦ (x : ℂ) + a.im * I) '' [[a.re, b.re]])ᶜ ×ˢ P) :=
  (differentiableOn_cauchyEdge hP hf (by fun_prop) fun x hx ↦ hab
    (mapsTo_horizontal_rectBoundary hre him (Or.inl rfl) hx).1).const_mul _

/-- The top Cauchy integral is holomorphic off the top edge. -/
theorem differentiableOn_cauchyTop (hre : a.re ≤ b.re) (him : a.im ≤ b.im) :
    DifferentiableOn ℂ (cauchyTop f a b)
      (((fun x : ℝ ↦ (x : ℂ) + b.im * I) '' [[a.re, b.re]])ᶜ ×ˢ P) :=
  ((differentiableOn_cauchyEdge hP hf (by fun_prop) fun x hx ↦ hab
    (mapsTo_horizontal_rectBoundary hre him (Or.inr rfl) hx).1).const_mul _).neg

/-- The right Cauchy integral is holomorphic off the right edge. -/
theorem differentiableOn_cauchyRight (hre : a.re ≤ b.re) (him : a.im ≤ b.im) :
    DifferentiableOn ℂ (cauchyRight f a b)
      (((fun y : ℝ ↦ (b.re : ℂ) + y * I) '' [[a.im, b.im]])ᶜ ×ˢ P) :=
  ((differentiableOn_cauchyEdge hP hf (by fun_prop) fun y hy ↦ hab
    (mapsTo_vertical_rectBoundary hre him (Or.inr rfl) hy).1).const_mul _).const_mul _

/-- The left Cauchy integral is holomorphic off the left edge. -/
theorem differentiableOn_cauchyLeft (hre : a.re ≤ b.re) (him : a.im ≤ b.im) :
    DifferentiableOn ℂ (cauchyLeft f a b)
      (((fun y : ℝ ↦ (a.re : ℂ) + y * I) '' [[a.im, b.im]])ᶜ ×ˢ P) :=
  (((differentiableOn_cauchyEdge hP hf (by fun_prop) fun y hy ↦ hab
    (mapsTo_vertical_rectBoundary hre him (Or.inl rfl) hy).1).const_mul _).const_mul _).neg

omit [FiniteDimensional ℂ E] hP in
/-- **Cauchy decomposition, inside.** On the open rectangle, `f` is the sum of its four side
Cauchy integrals. -/
theorem sum_cauchySides_of_mem {z : ℂ} (hz : z ∈ Ioo a.re b.re ×ℂ Ioo a.im b.im) {w : E}
    (hw : w ∈ P) :
    cauchyBottom f a b (z, w) + cauchyRight f a b (z, w) + cauchyTop f a b (z, w) +
      cauchyLeft f a b (z, w) = f (z, w) := by
  have hsub : Ioo a.re b.re ×ℂ Ioo a.im b.im ⊆ Icc a.re b.re ×ℂ Icc a.im b.im :=
    fun w hw ↦ ⟨Ioo_subset_Icc_self hw.1, Ioo_subset_Icc_self hw.2⟩
  have hg : DifferentiableOn ℂ (fun ζ ↦ f (ζ, w)) V :=
    hf.comp (differentiableOn_id.prodMk (differentiableOn_const _)) fun ζ hζ ↦ ⟨hζ, hw⟩
  rw [sum_cauchySides_eq, rectBoundaryIntegral_sub_inv_smul
    ((hg.mono hab).continuousOn) ((hg.mono (hsub.trans hab))) hz, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_mul]

omit [FiniteDimensional ℂ E] hP in
/-- **Cauchy decomposition, outside.** Off the closed rectangle, the four side Cauchy integrals
of `f` sum to zero. -/
theorem sum_cauchySides_of_notMem (hre : a.re ≤ b.re) (him : a.im ≤ b.im) {z : ℂ}
    (hz : z ∉ Icc a.re b.re ×ℂ Icc a.im b.im) {w : E} (hw : w ∈ P) :
    cauchyBottom f a b (z, w) + cauchyRight f a b (z, w) + cauchyTop f a b (z, w) +
      cauchyLeft f a b (z, w) = 0 := by
  have hg : DifferentiableOn ℂ (fun ζ ↦ (ζ - z)⁻¹ * f (ζ, w))
      (Icc a.re b.re ×ℂ Icc a.im b.im) := by
    refine DifferentiableOn.mul ?_ ?_
    · exact (differentiableOn_id.sub (differentiableOn_const _)).inv
        fun ζ hζ h ↦ hz (sub_eq_zero.mp h ▸ hζ)
    · exact hf.comp (differentiableOn_id.prodMk (differentiableOn_const _))
        fun ζ hζ ↦ ⟨hab hζ, hw⟩
  have h0 := integral_boundary_rect_eq_zero_of_differentiableOn _ a b
    (by rwa [uIcc_of_le hre, uIcc_of_le him])
  rw [sum_cauchySides_eq]
  change (2 * π * I)⁻¹ * rectBoundaryIntegral _ a b = 0
  rw [show rectBoundaryIntegral (fun ζ ↦ (ζ - z)⁻¹ • f (ζ, w)) a b = 0 from h0, mul_zero]

end Sides

/-- The four sides of a rectangle. -/
inductive RectSide
  | bottom | right | top | left
  deriving DecidableEq, Fintype

namespace RectSide

variable (f : ℂ × E → ℂ) (a b : ℂ)

/-- The Cauchy integral of `f` over a side of the rectangle with corners `a` and `b` (as part of
its positively oriented boundary), divided by `2πi`. -/
noncomputable def cauchy : RectSide → ℂ × E → ℂ
  | bottom => cauchyBottom f a b
  | right => cauchyRight f a b
  | top => cauchyTop f a b
  | left => cauchyLeft f a b

/-- A side of the rectangle with corners `a` and `b`, as a subset of `ℂ`. -/
def set : RectSide → Set ℂ
  | bottom => (fun x : ℝ ↦ (x : ℂ) + a.im * I) '' [[a.re, b.re]]
  | right => (fun y : ℝ ↦ (b.re : ℂ) + y * I) '' [[a.im, b.im]]
  | top => (fun x : ℝ ↦ (x : ℂ) + b.im * I) '' [[a.re, b.re]]
  | left => (fun y : ℝ ↦ (a.re : ℂ) + y * I) '' [[a.im, b.im]]

variable {a b}

lemma set_bottom_subset : set a b bottom ⊆ [[a.re, b.re]] ×ℂ {a.im} := by
  rintro _ ⟨x, hx, rfl⟩; simpa [mem_reProdIm] using hx

lemma set_top_subset : set a b top ⊆ [[a.re, b.re]] ×ℂ {b.im} := by
  rintro _ ⟨x, hx, rfl⟩; simpa [mem_reProdIm] using hx

lemma set_right_subset : set a b right ⊆ {b.re} ×ℂ [[a.im, b.im]] := by
  rintro _ ⟨y, hy, rfl⟩; simpa [mem_reProdIm] using hy

lemma set_left_subset : set a b left ⊆ {a.re} ×ℂ [[a.im, b.im]] := by
  rintro _ ⟨y, hy, rfl⟩; simpa [mem_reProdIm] using hy

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
lemma sum_univ_cauchy (p : ℂ × E) :
    ∑ s, cauchy f a b s p =
      cauchyBottom f a b p + cauchyRight f a b p + cauchyTop f a b p + cauchyLeft f a b p := by
  rw [show (Finset.univ : Finset RectSide) = {bottom, right, top, left} from rfl]
  simp [cauchy, add_assoc]

variable {f} {V : Set ℂ} (hab : Icc a.re b.re ×ℂ Icc a.im b.im ⊆ V)
  {P : Set E} (hP : IsOpen P) (hf : DifferentiableOn ℂ f (V ×ˢ P))
include hab hP hf

/-- Each side integral is holomorphic off its side. -/
theorem differentiableOn_cauchy (hre : a.re ≤ b.re) (him : a.im ≤ b.im) (s : RectSide) :
    DifferentiableOn ℂ (cauchy f a b s) ((set a b s)ᶜ ×ˢ P) := by
  cases s
  · exact differentiableOn_cauchyBottom hab hP hf hre him
  · exact differentiableOn_cauchyRight hab hP hf hre him
  · exact differentiableOn_cauchyTop hab hP hf hre him
  · exact differentiableOn_cauchyLeft hab hP hf hre him

/-- A sum of side integrals is holomorphic off the union of the sides involved. -/
theorem differentiableOn_sum_cauchy (hre : a.re ≤ b.re) (him : a.im ≤ b.im)
    (S : Finset RectSide) :
    DifferentiableOn ℂ (fun p ↦ ∑ s ∈ S, cauchy f a b s p) ((⋃ s ∈ S, set a b s)ᶜ ×ˢ P) := by
  refine DifferentiableOn.fun_sum fun s hs ↦ ?_
  refine (differentiableOn_cauchy hab hP hf hre him s).mono (prod_mono ?_ subset_rfl)
  exact compl_subset_compl.mpr (subset_biUnion_of_mem (u := fun s ↦ set a b s) hs)

omit [FiniteDimensional ℂ E] hP in
/-- **Cousin splitting by grouping sides, inside.** On the open rectangle, `f` is the sum of the
side integrals over `S` and over its complement. -/
theorem sum_add_sum_compl_of_mem (S : Finset RectSide) {z : ℂ}
    (hz : z ∈ Ioo a.re b.re ×ℂ Ioo a.im b.im) {w : E} (hw : w ∈ P) :
    (∑ s ∈ S, cauchy f a b s (z, w)) + ∑ s ∈ Sᶜ, cauchy f a b s (z, w) = f (z, w) := by
  rw [Finset.sum_add_sum_compl, sum_univ_cauchy, sum_cauchySides_of_mem hab hf hz hw]

omit [FiniteDimensional ℂ E] hP in
/-- **Cousin splitting by grouping sides, outside.** Off the closed rectangle, the side
integrals over `S` and over its complement cancel. -/
theorem sum_add_sum_compl_of_notMem (hre : a.re ≤ b.re) (him : a.im ≤ b.im)
    (S : Finset RectSide) {z : ℂ} (hz : z ∉ Icc a.re b.re ×ℂ Icc a.im b.im) {w : E}
    (hw : w ∈ P) :
    (∑ s ∈ S, cauchy f a b s (z, w)) + ∑ s ∈ Sᶜ, cauchy f a b s (z, w) = 0 := by
  rw [Finset.sum_add_sum_compl, sum_univ_cauchy, sum_cauchySides_of_notMem hab hf hre him hz hw]

end RectSide

section Cousin

variable {V : Set ℂ} {a b : ℂ} {P : Set E} {f : ℂ × E → ℂ}

/-- **Cousin splitting along a vertical line, with holomorphic parameters.** Let `f` be
holomorphic on `V × P`, where `V` contains the closed rectangle `[a.re, b.re] × [a.im, b.im]`.
Then on the open rectangle `f = f₁ - f₂`, where `f₁` is holomorphic on the left half-plane
`{Re z < b.re}` and `f₂` on the right half-strip `{Re z > a.re, a.im < Im z < b.im}`
(both times `P`). -/
theorem exists_cousin_split_re (hre : a.re < b.re) (him : a.im < b.im)
    (hab : Icc a.re b.re ×ℂ Icc a.im b.im ⊆ V) (hP : IsOpen P)
    (hf : DifferentiableOn ℂ f (V ×ˢ P)) :
    ∃ f₁ f₂ : ℂ × E → ℂ, DifferentiableOn ℂ f₁ ({z : ℂ | z.re < b.re} ×ˢ P) ∧
      DifferentiableOn ℂ f₂ ((Ioi a.re ×ℂ Ioo a.im b.im) ×ˢ P) ∧
      ∀ z ∈ Ioo a.re b.re ×ℂ Ioo a.im b.im, ∀ w ∈ P, f (z, w) = f₁ (z, w) - f₂ (z, w) := by
  refine ⟨cauchyRight f a b,
    fun p ↦ -(cauchyBottom f a b p + cauchyTop f a b p + cauchyLeft f a b p), ?_, ?_, ?_⟩
  · refine (differentiableOn_cauchyRight hab hP hf hre.le him.le).mono
      (prod_mono (fun z hz ↦ ?_) subset_rfl)
    rintro ⟨y, -, rfl⟩
    simp at hz
  · refine (((differentiableOn_cauchyBottom hab hP hf hre.le him.le).mono
      (prod_mono (fun z hz ↦ ?_) subset_rfl)).add
      ((differentiableOn_cauchyTop hab hP hf hre.le him.le).mono
      (prod_mono (fun z hz ↦ ?_) subset_rfl))).add
      ((differentiableOn_cauchyLeft hab hP hf hre.le him.le).mono
      (prod_mono (fun z hz ↦ ?_) subset_rfl)) |>.neg
    all_goals
      rintro ⟨t, -, rfl⟩
      simp [mem_reProdIm] at hz
  · intro z hz w hw
    rw [← sum_cauchySides_of_mem hab hf hz hw]
    ring

/-- **Cousin splitting along a horizontal line, with holomorphic parameters.** Let `f` be
holomorphic on `V × P`, where `V` contains the closed rectangle `[a.re, b.re] × [a.im, b.im]`.
Then on the open rectangle `f = f₁ - f₂`, where `f₁` is holomorphic on the lower half-plane
`{Im z < b.im}` and `f₂` on the upper half-strip `{a.re < Re z < b.re, Im z > a.im}`
(both times `P`). -/
theorem exists_cousin_split_im (hre : a.re < b.re) (him : a.im < b.im)
    (hab : Icc a.re b.re ×ℂ Icc a.im b.im ⊆ V) (hP : IsOpen P)
    (hf : DifferentiableOn ℂ f (V ×ˢ P)) :
    ∃ f₁ f₂ : ℂ × E → ℂ, DifferentiableOn ℂ f₁ ({z : ℂ | z.im < b.im} ×ˢ P) ∧
      DifferentiableOn ℂ f₂ ((Ioo a.re b.re ×ℂ Ioi a.im) ×ˢ P) ∧
      ∀ z ∈ Ioo a.re b.re ×ℂ Ioo a.im b.im, ∀ w ∈ P, f (z, w) = f₁ (z, w) - f₂ (z, w) := by
  refine ⟨cauchyTop f a b,
    fun p ↦ -(cauchyBottom f a b p + cauchyRight f a b p + cauchyLeft f a b p), ?_, ?_, ?_⟩
  · refine (differentiableOn_cauchyTop hab hP hf hre.le him.le).mono
      (prod_mono (fun z hz ↦ ?_) subset_rfl)
    rintro ⟨y, -, rfl⟩
    simp at hz
  · refine (((differentiableOn_cauchyBottom hab hP hf hre.le him.le).mono
      (prod_mono (fun z hz ↦ ?_) subset_rfl)).add
      ((differentiableOn_cauchyRight hab hP hf hre.le him.le).mono
      (prod_mono (fun z hz ↦ ?_) subset_rfl))).add
      ((differentiableOn_cauchyLeft hab hP hf hre.le him.le).mono
      (prod_mono (fun z hz ↦ ?_) subset_rfl)) |>.neg
    all_goals
      rintro ⟨t, -, rfl⟩
      simp [mem_reProdIm] at hz
  · intro z hz w hw
    rw [← sum_cauchySides_of_mem hab hf hz hw]
    ring

/-- **Cousin splitting along a vertical line**, one-variable version. -/
theorem exists_cousin_split_re_of_differentiableOn {g : ℂ → ℂ} (hre : a.re < b.re)
    (him : a.im < b.im) (hab : Icc a.re b.re ×ℂ Icc a.im b.im ⊆ V)
    (hg : DifferentiableOn ℂ g V) :
    ∃ g₁ g₂ : ℂ → ℂ, DifferentiableOn ℂ g₁ {z : ℂ | z.re < b.re} ∧
      DifferentiableOn ℂ g₂ (Ioi a.re ×ℂ Ioo a.im b.im) ∧
      ∀ z ∈ Ioo a.re b.re ×ℂ Ioo a.im b.im, g z = g₁ z - g₂ z := by
  obtain ⟨f₁, f₂, h₁, h₂, h⟩ := exists_cousin_split_re (E := ℂ) (P := univ)
    (f := fun p ↦ g p.1) hre him hab isOpen_univ
    (hg.comp differentiableOn_fst fun p hp ↦ hp.1)
  have hi : ∀ s : Set ℂ, MapsTo (fun z : ℂ ↦ (z, (0 : ℂ))) s (s ×ˢ univ) :=
    fun _ _ hz ↦ ⟨hz, mem_univ _⟩
  exact ⟨fun z ↦ f₁ (z, 0), fun z ↦ f₂ (z, 0),
    h₁.comp (differentiableOn_id.prodMk (differentiableOn_const _)) (hi _),
    h₂.comp (differentiableOn_id.prodMk (differentiableOn_const _)) (hi _),
    fun z hz ↦ h z hz 0 (mem_univ _)⟩

/-- **Cousin splitting along a horizontal line**, one-variable version. -/
theorem exists_cousin_split_im_of_differentiableOn {g : ℂ → ℂ} (hre : a.re < b.re)
    (him : a.im < b.im) (hab : Icc a.re b.re ×ℂ Icc a.im b.im ⊆ V)
    (hg : DifferentiableOn ℂ g V) :
    ∃ g₁ g₂ : ℂ → ℂ, DifferentiableOn ℂ g₁ {z : ℂ | z.im < b.im} ∧
      DifferentiableOn ℂ g₂ (Ioo a.re b.re ×ℂ Ioi a.im) ∧
      ∀ z ∈ Ioo a.re b.re ×ℂ Ioo a.im b.im, g z = g₁ z - g₂ z := by
  obtain ⟨f₁, f₂, h₁, h₂, h⟩ := exists_cousin_split_im (E := ℂ) (P := univ)
    (f := fun p ↦ g p.1) hre him hab isOpen_univ
    (hg.comp differentiableOn_fst fun p hp ↦ hp.1)
  have hi : ∀ s : Set ℂ, MapsTo (fun z : ℂ ↦ (z, (0 : ℂ))) s (s ×ˢ univ) :=
    fun _ _ hz ↦ ⟨hz, mem_univ _⟩
  exact ⟨fun z ↦ f₁ (z, 0), fun z ↦ f₂ (z, 0),
    h₁.comp (differentiableOn_id.prodMk (differentiableOn_const _)) (hi _),
    h₂.comp (differentiableOn_id.prodMk (differentiableOn_const _)) (hi _),
    fun z hz ↦ h z hz 0 (mem_univ _)⟩

end Cousin

end Complex

end
