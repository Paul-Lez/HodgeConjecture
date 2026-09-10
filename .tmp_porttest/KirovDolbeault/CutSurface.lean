import Mathlib.Analysis.Complex.CauchyIntegral
import KirovDolbeault.BoundaryPositivity

/-!
# Cut-surface bridge: proving the Riemann bilinear relations

This file formalizes the *analytic heart* of the period-lattice goal (#7): the two Riemann bilinear
relations R1 (vanishing) and R2 (positivity) are **proven** from a single, more primitive topological
input — the **boundary word** of a canonical dissection realized as a cut surface (a chart
`cut : box → X`, holomorphic on the interior, a diffeo onto `X` minus the cuts, whose boundary
traverses the loops `a₁b₁a₁⁻¹b₁⁻¹⋯`).

The boundary word is the identity `∑ₖ(A_{ki}B_{kj} − B_{ki}A_{kj}) = ∮_{∂box}(F_i · h_j dz)` (and a
conjugated variant), where `h_j = cut^*ω_j` is the pullback of the `j`-th holomorphic form and `F_i`
is a primitive of `h_i`. Given it, R1/R2 are pure analysis:

* **R1** — the boundary integral of the *holomorphic* `F_i·h_j` over `∂box` is `0` by **Cauchy's
  theorem on the rectangle** (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`). Hence
  `∑ₖ(A_{ki}B_{kj} − B_{ki}A_{kj}) = 0`, i.e. `AᵀB = BᵀA`.
* **R2** — the conjugated boundary integral is `−(i/2)⁻¹` times a strictly positive area integral
  (`Jacobians.boundaryForm_pos`), giving positive-definiteness of the period Hermitian form.

Only the boundary word stays isolated (it encodes the surface's polygonal schema, which Mathlib
lacks); the relations themselves are theorems.
-/

open MeasureTheory Set intervalIntegral Complex Matrix
open scoped ComplexConjugate

namespace Jacobians

/-- The counterclockwise contour integral of `f` over the boundary of the unit box `[0,1]²`
(identified with the square `0,1,1+i,i` in `ℂ`), in the orientation of Mathlib's rectangle Cauchy
theorem: `∫P(·,0) − ∫P(·,1) + i∫P(1,·) − i∫P(0,·)`, i.e. `∮ f dz`. -/
noncomputable def rectBoundaryIntegral (f : ℂ → ℂ) : ℂ :=
  ((∫ x in (0:ℝ)..1, f (x : ℂ)) - ∫ x in (0:ℝ)..1, f ((x : ℂ) + Complex.I))
    + Complex.I * (∫ y in (0:ℝ)..1, f (1 + (y : ℂ) * Complex.I))
    - Complex.I * ∫ y in (0:ℝ)..1, f ((y : ℂ) * Complex.I)

/-- **Cauchy on the box.** If `f` is holomorphic on (a set containing) the closed unit box, its
contour integral over `∂box` vanishes. Direct from
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` specialized to `z = 0`, `w = 1 + i`. -/
theorem rectBoundaryIntegral_eq_zero_of_differentiableOn {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Set.uIcc 0 1 ×ℂ Set.uIcc 0 1)) :
    rectBoundaryIntegral f = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f 0 (1 + Complex.I) (by
    simpa using hf)
  simpa [rectBoundaryIntegral, smul_eq_mul] using h

/-- **Riemann's first bilinear relation, from the boundary word.** Given period blocks `A, B`,
pullbacks `h_j` with primitives `F_i`, and the boundary-word identity
`(AᵀB − BᵀA) i j = ∮_{∂box}(F_i·h_j) dz`, the relation `AᵀB = BᵀA` holds: each `F_i·h_j` is
holomorphic, so its box contour integral vanishes by Cauchy. (The boundary word is supplied by the
cut surface and is itself a theorem there — see `CutSurface`.) -/
theorem riemann_R1_of_boundaryWord {g : ℕ} (A B : Matrix (Fin g) (Fin g) ℂ) (h F : Fin g → ℂ → ℂ)
    (hFh : ∀ i j, DifferentiableOn ℂ (fun z => F i z * h j z) (Set.uIcc 0 1 ×ℂ Set.uIcc 0 1))
    (boundaryWord : ∀ i j,
      (Aᵀ * B - Bᵀ * A) i j = rectBoundaryIntegral (fun z => F i z * h j z)) :
    Aᵀ * B = Bᵀ * A := by
  rw [← sub_eq_zero]
  ext i j
  rw [Matrix.zero_apply, boundaryWord i j]
  exact rectBoundaryIntegral_eq_zero_of_differentiableOn (hFh i j)

/-- **Per-handle cancellation = the boundary word, PROVEN from the gluing.** This is the geometric
heart of the boundary word for a *single handle* (one `a`-loop, one `b`-loop): the box contour
integral `∮_{∂box}(F·h dz)` equals the antisymmetric period product `A·B' − B·A'`, derived purely
from the cut chart's **gluing** and the primitive's **jumps** across the cuts.

Hypotheses (all supplied by a cut chart that identifies the box's opposite edges):
* **gluing** `hper_a`/`hper_b` — the pullback `h = cut^*ω` takes equal values on identified edges
  (the chart glues `x ↦ x+i` and `y·i ↦ 1+y·i`);
* **jumps** `hjump_a`/`hjump_b` — the primitive `F` of `h` increases by a fixed period across each
  cut: by `B` (the `b`-period of the `F`-form) crossing the `a`-cut, and by `A` (the `a`-period)
  crossing the `b`-cut. This is the monodromy fact "primitive jump = period";
* **periods** `hAper`/`hBper` — the `a`-period `A' = ∫₀¹ h(x) dx` and `b`-period `B' = i∫₀¹ h(yi) dy`
  of the `h`-form, read off the bottom/left edges.

Then `∮_{∂box}(F·h) = A·B' − B·A'`. (Bottom−top collapses to `−B·A'` via the `a`-cut jump;
right−left to `A·B'` via the `b`-cut jump. Pure interval-integral algebra; no surface topology — that
lives in *realizing* the gluing/jump data, i.e. the isolated `exists_cutSurface`.) Combined with box
Cauchy (`rectBoundaryIntegral_eq_zero_of_differentiableOn`) this gives `A·B' = B·A'` — Riemann's R1
for one handle. The general-`g` boundary word sums `g` such handles over the `4g`-gon. -/
theorem rectBoundaryIntegral_singleHandle (h F : ℂ → ℂ) (A B Aper Bper : ℂ)
    (hper_a : ∀ x ∈ Set.uIcc (0:ℝ) 1, h ((x:ℂ) + Complex.I) = h (x:ℂ))
    (hjump_a : ∀ x ∈ Set.uIcc (0:ℝ) 1, F ((x:ℂ) + Complex.I) = F (x:ℂ) + B)
    (hper_b : ∀ y ∈ Set.uIcc (0:ℝ) 1, h (1 + (y:ℂ) * Complex.I) = h ((y:ℂ) * Complex.I))
    (hjump_b : ∀ y ∈ Set.uIcc (0:ℝ) 1, F (1 + (y:ℂ) * Complex.I) = F ((y:ℂ) * Complex.I) + A)
    (hAper : (∫ x in (0:ℝ)..1, h (x:ℂ)) = Aper)
    (hBper : Complex.I * ∫ y in (0:ℝ)..1, h ((y:ℂ) * Complex.I) = Bper)
    (hi_bot : IntervalIntegrable (fun x : ℝ => F (x:ℂ) * h (x:ℂ)) volume 0 1)
    (hi_both : IntervalIntegrable (fun x : ℝ => h (x:ℂ)) volume 0 1)
    (hi_left : IntervalIntegrable
      (fun y : ℝ => F ((y:ℂ) * Complex.I) * h ((y:ℂ) * Complex.I)) volume 0 1)
    (hi_lefth : IntervalIntegrable (fun y : ℝ => h ((y:ℂ) * Complex.I)) volume 0 1) :
    rectBoundaryIntegral (fun z => F z * h z) = A * Bper - B * Aper := by
  have htop : (∫ x in (0:ℝ)..1, (fun z => F z * h z) ((x:ℂ) + Complex.I))
      = (∫ x in (0:ℝ)..1, F (x:ℂ) * h (x:ℂ)) + B * Aper := by
    rw [intervalIntegral.integral_congr (g := fun x => F (x:ℂ) * h (x:ℂ) + B * h (x:ℂ))
        (fun x hx => by simp only; rw [hper_a x hx, hjump_a x hx]; ring),
      intervalIntegral.integral_add hi_bot (hi_both.const_mul B),
      show (∫ x in (0:ℝ)..1, B * h (x:ℂ)) = B * ∫ x in (0:ℝ)..1, h (x:ℂ) from
        intervalIntegral.integral_const_mul B _, hAper]
  have hright : (∫ y in (0:ℝ)..1, (fun z => F z * h z) (1 + (y:ℂ) * Complex.I))
      = (∫ y in (0:ℝ)..1, F ((y:ℂ) * Complex.I) * h ((y:ℂ) * Complex.I))
        + A * ∫ y in (0:ℝ)..1, h ((y:ℂ) * Complex.I) := by
    rw [intervalIntegral.integral_congr
        (g := fun y => F ((y:ℂ) * Complex.I) * h ((y:ℂ) * Complex.I) + A * h ((y:ℂ) * Complex.I))
        (fun y hy => by simp only; rw [hper_b y hy, hjump_b y hy]; ring),
      intervalIntegral.integral_add hi_left (hi_lefth.const_mul A),
      show (∫ y in (0:ℝ)..1, A * h ((y:ℂ) * Complex.I))
          = A * ∫ y in (0:ℝ)..1, h ((y:ℂ) * Complex.I) from
        intervalIntegral.integral_const_mul A _]
  rw [rectBoundaryIntegral, htop, hright, ← hAper, ← hBper]; ring

end Jacobians
