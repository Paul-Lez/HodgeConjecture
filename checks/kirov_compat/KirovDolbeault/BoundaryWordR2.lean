/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.BoundaryPositivity
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef

/-!
# Riemann's second bilinear relation, from the boundary word

This is the box-layer analytic core for **R2** (positive-definiteness of the period Hermitian form),
the companion of `Jacobians.riemann_R1_of_boundaryWord` (the box-layer R1).

Given period blocks `A B : Matrix (Fin g) (Fin g) ℂ`, pullback coefficients `h_j` (`= cut^*ω_j`)
holomorphic on a convex open `U ⊇ [0,1]²` with primitives `F_i` (`F_i' = h_i`), the **boundary word**
identity (the genuinely topological input, supplied by the cut surface)

  `(Aᵀ·B̄ − Bᵀ·Ā)_{ij} = − boundaryForm (h_j) (F_i)`   (`boundaryForm (h) (F) = ∮_{∂box} F̄·h dz`)

together with non-degeneracy of the pullbacks forces the Hermitian form `H = i·(Aᵀ·B̄ − Bᵀ·Ā)` to be
**positive definite**. The proof is pure box-level analysis:

* `boundaryForm` is bilinear (`boundaryForm_combo`), so the quadratic form `vᴴ(Aᵀ·B̄ − Bᵀ·Ā)v`
  collapses to `−boundaryForm (h_v) (F_v)` for the combinations `h_v = ∑ⱼ vⱼ hⱼ`, `F_v = ∑ᵢ vᵢ Fᵢ`;
* `Jacobians.boundaryForm_pos` makes `−(i/2)·boundaryForm (h_v) (F_v)` a strictly positive real
  (Green's theorem: it equals `∬_box ‖h_v‖² > 0`), since `h_v ≠ 0` somewhere in the open box;
* hence `vᴴ H v = i·(−boundaryForm (h_v) (F_v)) = 2·(∬‖h_v‖²) > 0`.

The sign is validated at `g = 1`: the standard torus `ℂ/(ℤ+ℤτ)` gives `vᴴ H v = 2·Im τ > 0`.

No surface topology enters here — only matrix algebra, interval integrals, and the proven Green
positivity bridge. This is a "hard Lean, no missing math" leaf.
-/

open MeasureTheory Set intervalIntegral Complex Matrix
open scoped ComplexConjugate ComplexOrder

namespace Jacobians

variable {g : ℕ}

/-- A single boundary-edge contribution `∫₀¹ F̄(γ t)·h(γ t) dt`, the building block of
`boundaryForm`. -/
noncomputable def edgeBF (γ : ℝ → ℂ) (h F : ℂ → ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1, (starRingEnd ℂ) (F (γ t)) * h (γ t)

/-- **`boundaryForm` as a signed sum of four edge contributions.** Unfolds the definition; the four
edges of `∂box` are the images of `t ↦ wCLM (t,0)`, `wCLM (1,·)`, `wCLM (·,1)`, `wCLM (0,·)`. -/
lemma boundaryForm_eq_edges (h F : ℂ → ℂ) :
    boundaryForm h F
      = (edgeBF (fun t => wCLM (t, 0)) h F + Complex.I * edgeBF (fun t => wCLM (1, t)) h F)
        - edgeBF (fun t => wCLM (t, 1)) h F - Complex.I * edgeBF (fun t => wCLM (0, t)) h F := by
  rfl

/-- **Edge-level bilinearity.** Expanding the combinations `h_v = ∑ⱼ vⱼ·hⱼ`, `F_v = ∑ᵢ vᵢ·Fᵢ` inside
one boundary edge: `edgeBF γ (h_v) (F_v) = ∑ᵢ ∑ⱼ conj(vᵢ)·vⱼ · edgeBF γ (hⱼ) (Fᵢ)` (interval-integral
linearity). -/
lemma edgeBF_combo (γ : ℝ → ℂ) (v : Fin g → ℂ) (h F : Fin g → ℂ → ℂ)
    (hint : ∀ i j, IntervalIntegrable
      (fun t => (starRingEnd ℂ) (F i (γ t)) * h j (γ t)) volume 0 1) :
    edgeBF γ (fun z => ∑ j, v j * h j z) (fun z => ∑ i, v i * F i z)
      = ∑ i, ∑ j, (starRingEnd ℂ) (v i) * v j * edgeBF γ (h j) (F i) := by
  unfold edgeBF
  rw [intervalIntegral.integral_congr (g := fun t =>
      ∑ i, ∑ j, ((starRingEnd ℂ) (v i) * v j) * ((starRingEnd ℂ) (F i (γ t)) * h j (γ t)))
      (fun t _ => ?_)]
  · -- ∫ of the double sum = double sum of (const · ∫)
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [intervalIntegral.integral_finsetSum]
      · exact Finset.sum_congr rfl (fun j _ => intervalIntegral.integral_const_mul _ _)
      · exact fun j _ => (hint i j).const_mul _
    · intro i _
      rw [show (fun t => ∑ j, ((starRingEnd ℂ) (v i) * v j) *
              ((starRingEnd ℂ) (F i (γ t)) * h j (γ t)))
            = ∑ j : Fin g, (fun t => ((starRingEnd ℂ) (v i) * v j) *
              ((starRingEnd ℂ) (F i (γ t)) * h j (γ t)))
          from funext (fun t => by rw [Finset.sum_apply])]
      exact IntervalIntegrable.sum _ (fun j _ => (hint i j).const_mul _)
  · -- pointwise integrand expansion
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [map_mul]; ring

/-- Finite-sum linearity used to reassemble the four boundary edges. -/
private lemma sum_lincomb4 (c a b d e : Fin g → Fin g → ℂ) :
    (∑ i, ∑ j, c i j * a i j) + Complex.I * (∑ i, ∑ j, c i j * b i j)
      - (∑ i, ∑ j, c i j * d i j) - Complex.I * (∑ i, ∑ j, c i j * e i j)
      = ∑ i, ∑ j, c i j * (a i j + Complex.I * b i j - d i j - Complex.I * e i j) := by
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- **Bilinearity of `boundaryForm`** over the combinations `h_v = ∑ⱼ vⱼ·hⱼ`, `F_v = ∑ᵢ vᵢ·Fᵢ`:
`boundaryForm (h_v) (F_v) = ∑ᵢ ∑ⱼ conj(vᵢ)·vⱼ · boundaryForm (hⱼ) (Fᵢ)`. (`boundaryForm` is ℂ-linear
in its first argument and conjugate-linear in its second, via interval-integral linearity.) -/
lemma boundaryForm_combo (v : Fin g → ℂ) (h F : Fin g → ℂ → ℂ)
    (hcont : ∀ i, ContinuousOn (h i) (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)))
    (hcontF : ∀ i, ContinuousOn (F i) (wCLM '' (Icc 0 1 ×ˢ Icc 0 1))) :
    boundaryForm (fun z => ∑ j, v j * h j z) (fun z => ∑ i, v i * F i z)
      = ∑ i, ∑ j, (starRingEnd ℂ) (v i) * v j * boundaryForm (h j) (F i) := by
  -- integrability of `F̄_i·h_j` along any box edge `t ↦ wCLM (p t)` with `p` valued in the box
  have edge_int : ∀ (p : ℝ → ℝ × ℝ), Continuous p →
      (∀ t ∈ Icc (0:ℝ) 1, p t ∈ Icc 0 1 ×ˢ Icc 0 1) → ∀ i j,
        IntervalIntegrable (fun t => (starRingEnd ℂ) (F i (wCLM (p t))) * h j (wCLM (p t)))
          volume 0 1 := by
    intro p hp hmem i j
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have hγc : ContinuousOn (fun t => wCLM (p t)) (Icc 0 1) := (wCLM.continuous.comp hp).continuousOn
    have hγm : MapsTo (fun t => wCLM (p t)) (Icc 0 1) (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)) :=
      fun t ht => ⟨p t, hmem t ht, rfl⟩
    exact (Complex.continuous_conj.comp_continuousOn ((hcontF i).comp hγc hγm)).mul
      ((hcont j).comp hγc hγm)
  rw [boundaryForm_eq_edges,
    edgeBF_combo _ v h F (edge_int (fun t => (t, 0)) (by fun_prop) (fun t ht => ⟨ht, by simp⟩)),
    edgeBF_combo _ v h F (edge_int (fun t => (1, t)) (by fun_prop) (fun t ht => ⟨by simp, ht⟩)),
    edgeBF_combo _ v h F (edge_int (fun t => (t, 1)) (by fun_prop) (fun t ht => ⟨ht, by simp⟩)),
    edgeBF_combo _ v h F (edge_int (fun t => (0, t)) (by fun_prop) (fun t ht => ⟨by simp, ht⟩))]
  simp only [boundaryForm_eq_edges]
  exact sum_lincomb4 _ _ _ _ _

/-- **Riemann's second bilinear relation (positive-definiteness), from the boundary word.**
Given period blocks `A, B`, holomorphic pullbacks `h_j` on a convex open `U ⊇ [0,1]²` with primitives
`F_i`, the per-entry boundary word `(Aᵀ·B̄ − Bᵀ·Ā)_{ij} = −boundaryForm (h_j) (F_i)`, and
non-degeneracy of the pullbacks, the period Hermitian form `i·(Aᵀ·B̄ − Bᵀ·Ā)` is positive definite.

(Hermitian-ness is automatic from the structure of the form; positivity is the Green-positivity
`∬_box ‖h_v‖² > 0`. Sign validated at `g = 1` → `2·Im τ > 0`.) -/
theorem riemann_R2_posDef_of_boundaryWord
    (A B : Matrix (Fin g) (Fin g) ℂ) (h F : Fin g → ℂ → ℂ) (U : Set ℂ)
    (hbox : wCLM '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ U)
    (hh : ∀ i, ∀ z ∈ U, HasDerivAt (h i) (deriv (h i) z) z)
    (hF : ∀ i, ∀ z ∈ U, HasDerivAt (F i) (h i z) z)
    (boundaryWord : ∀ i j,
      (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ)) i j
        = - boundaryForm (h j) (F i))
    (nondeg : ∀ v : Fin g → ℂ, v ≠ 0 →
      ∃ p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1, (∑ j, v j * h j (wCLM p)) ≠ 0) :
    (Complex.I • (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ))).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · -- Hermitian: `(I • (AᵀB̄ − BᵀĀ))ᴴ = I • (AᵀB̄ − BᵀĀ)`, since `(AᵀB̄ − BᵀĀ)ᴴ = −(AᵀB̄ − BᵀĀ)`.
    show (Complex.I • (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ)))ᴴ
      = Complex.I • (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ))
    rw [Matrix.conjTranspose_smul,
      show (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ))ᴴ
          = -(Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ)) from ?_]
    · rw [RCLike.star_def, Complex.conj_I, smul_neg, neg_smul, neg_neg]
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, star_sub, star_sum, star_mul',
        RCLike.star_def, Complex.conj_conj]
      rw [neg_sub]; congr 1 <;> exact Finset.sum_congr rfl (fun x _ => by ring)
  · -- positivity: `vᴴ (I • (AᵀB̄ − BᵀĀ)) v = −i·boundaryForm (h_v) (F_v) = 2·∬‖h_v‖² > 0`.
    intro v hv
    have hcont : ∀ i, ContinuousOn (h i) (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)) :=
      fun i z hz => ((hh i z (hbox hz)).continuousAt).continuousWithinAt
    have hcontF : ∀ i, ContinuousOn (F i) (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)) :=
      fun i z hz => ((hF i z (hbox hz)).continuousAt).continuousWithinAt
    -- (a) the quadratic form expanded over entries
    have hexp : star v ⬝ᵥ ((Complex.I •
          (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ))) *ᵥ v)
        = ∑ i, ∑ j, (starRingEnd ℂ) (v i) *
            (Complex.I • (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ))) i j * v j := by
      rw [dotProduct]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by simp [Pi.star_apply, mul_assoc])
    -- (b) collapse to the boundary form via the per-entry boundary word + bilinearity
    have key : star v ⬝ᵥ ((Complex.I •
          (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ))) *ᵥ v)
        = -Complex.I * boundaryForm (fun z => ∑ j, v j * h j z) (fun z => ∑ i, v i * F i z) := by
      rw [hexp, boundaryForm_combo v h F hcont hcontF, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Matrix.smul_apply, smul_eq_mul, boundaryWord i j]; ring
    -- (c) the Green-positivity bridge: `−(i/2)·boundaryForm (h_v) (F_v) = c > 0`
    obtain ⟨p₀, hp₀, hp₀ne⟩ := nondeg v hv
    have hhv : ∀ z ∈ U, HasDerivAt (fun z => ∑ j, v j * h j z) (deriv (fun z => ∑ j, v j * h j z) z) z := by
      intro z hz
      have hd : HasDerivAt (fun z => ∑ j, v j * h j z) (∑ j, v j * deriv (h j) z) z :=
        HasDerivAt.fun_sum (fun j _ => (hh j z hz).const_mul (v j))
      rwa [hd.deriv]
    have hFv : ∀ z ∈ U, HasDerivAt (fun z => ∑ i, v i * F i z) ((fun z => ∑ j, v j * h j z) z) z :=
      fun z hz => HasDerivAt.fun_sum (fun i _ => (hF i z hz).const_mul (v i))
    obtain ⟨c, hc, hceq⟩ := boundaryForm_pos hbox hhv hFv p₀ hp₀ hp₀ne
    rw [key, show -Complex.I * boundaryForm (fun z => ∑ j, v j * h j z) (fun z => ∑ i, v i * F i z)
          = 2 * (-(Complex.I / 2) *
              boundaryForm (fun z => ∑ j, v j * h j z) (fun z => ∑ i, v i * F i z)) from by ring,
      hceq, show (2 : ℂ) * (c : ℂ) = ((2 * c : ℝ) : ℂ) from by push_cast; ring]
    exact_mod_cast (by positivity : (0:ℝ) < 2 * c)

end Jacobians
