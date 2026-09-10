import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.Complex.Order

open Matrix
open scoped ComplexConjugate ComplexOrder

namespace Jacobians

variable {g : ℕ}

/-- **Riemann period independence.** Let `A B : Matrix (Fin g) (Fin g) ℂ` be the `a`-period and
`b`-period blocks (row = loop, column = holomorphic form). If
* (R1, vanishing) `Aᵀ * B = Bᵀ * A`, and
* (R2, positivity) the Hermitian matrix `H = I • (Aᵀ * conj B - Bᵀ * conj A)` is positive
  definite (this is the geometric Riemann form; at `g = 1` with `A = 1, B = τ` it is `2·Im τ`),
then the `2g` period vectors (the rows of `fromRows A B`, indexed by `Fin g ⊕ Fin g`) are
ℝ-linearly independent in `Fin g → ℂ`. -/
theorem linearIndependent_periodRows_of_posDef
    (A B : Matrix (Fin g) (Fin g) ℂ)
    (H : Matrix (Fin g) (Fin g) ℂ)
    (hH : H = Complex.I • (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ)))
    (hR1 : Aᵀ * B = Bᵀ * A)
    (hR2 : H.PosDef) :
    LinearIndependent ℝ (fun k : Fin g ⊕ Fin g => (Matrix.fromRows A B k : Fin g → ℂ)) := by
  classical
  -- Entrywise conjugates of `A` and `B`.
  set cA : Matrix (Fin g) (Fin g) ℂ := A.map (starRingEnd ℂ) with hcA
  set cB : Matrix (Fin g) (Fin g) ℂ := B.map (starRingEnd ℂ) with hcB
  -- The doubled period matrix: first g columns are `M = fromRows A B`, last g columns are `conj M`.
  set N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ := Matrix.fromBlocks A cA B cB with hN
  -- The symplectic form.
  set J : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ := Matrix.fromBlocks 0 1 (-1) 0 with hJ
  -- The two antidiagonal blocks of `Nᵀ * J * N`.
  set K : Matrix (Fin g) (Fin g) ℂ := Aᵀ * cB - Bᵀ * cA with hK
  set L : Matrix (Fin g) (Fin g) ℂ := cAᵀ * B - cBᵀ * A with hL
  -- Transpose of N.
  have hNt : Nᵀ = Matrix.fromBlocks Aᵀ Bᵀ cAᵀ cBᵀ := by
    rw [hN, Matrix.fromBlocks_transpose]
  -- Nᵀ * J.
  have hNtJ : Nᵀ * J = Matrix.fromBlocks (-Bᵀ) Aᵀ (-cBᵀ) cAᵀ := by
    rw [hNt, hJ, Matrix.fromBlocks_multiply]
    simp
  -- Nᵀ * J * N is block-antidiagonal: `fromBlocks 0 K L 0`.
  have hNJN : Nᵀ * J * N = Matrix.fromBlocks 0 K L 0 := by
    rw [hNtJ, hN, Matrix.fromBlocks_multiply]
    congr 1
    · -- top-left: -Bᵀ*A + Aᵀ*B = 0 by R1.
      rw [hR1]; simp only [neg_mul]; abel
    · -- top-right = K.
      rw [hK]; simp only [neg_mul, sub_eq_add_neg]; abel
    · -- bottom-left = L.
      rw [hL]; simp only [neg_mul, sub_eq_add_neg]; abel
    · -- bottom-right: -cBᵀ*cA + cAᵀ*cB = conj(Aᵀ*B - Bᵀ*A) = 0.
      have e1 : cAᵀ * cB = (Aᵀ * B).map (starRingEnd ℂ) := by
        rw [hcA, hcB, ← Matrix.transpose_map, ← Matrix.map_mul]
      have e2 : cBᵀ * cA = (Bᵀ * A).map (starRingEnd ℂ) := by
        rw [hcA, hcB, ← Matrix.transpose_map, ← Matrix.map_mul]
      simp only [neg_mul]
      rw [e1, e2, hR1]
      abel
  -- Step 4: K and L have nonzero determinant.
  -- K = -I • H  (since H = I • K).
  have hKIH : K = (-Complex.I) • H := by
    rw [hH, smul_smul]
    rw [show -Complex.I * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I, neg_neg]]
    rw [one_smul]
  have hHdet : H.det ≠ 0 := ne_of_gt hR2.det_pos
  have hKdet : K.det ≠ 0 := by
    rw [hKIH, Matrix.det_smul, Fintype.card_fin]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)) hHdet
  -- L = -Kᵀ.
  have hLt : Lᵀ = -K := by
    rw [hL, hK, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose]
    abel
  have hLeq : L = -Kᵀ := by
    rw [← Matrix.transpose_transpose L, hLt, Matrix.transpose_neg]
  have hLdet : L.det ≠ 0 := by
    rw [hLeq, Matrix.det_neg, Matrix.det_transpose, Fintype.card_fin]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hKdet
  -- Step 5: det N ≠ 0.
  -- The swap block matrix P = fromBlocks 0 1 1 0 is its own inverse, hence a unit.
  set P : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ := Matrix.fromBlocks 0 1 1 0 with hP
  have hPP : P * P = 1 := by
    rw [hP, Matrix.fromBlocks_multiply]
    simp [← Matrix.fromBlocks_one]
  have hPdetsq : P.det * P.det = 1 := by
    rw [← Matrix.det_mul, hPP, Matrix.det_one]
  have hPdet : P.det ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hPdetsq
    exact one_ne_zero hPdetsq.symm
  -- The antidiagonal product factors through P and a block-diagonal matrix.
  have hfac : Matrix.fromBlocks (0 : Matrix (Fin g) (Fin g) ℂ) K L 0
      = P * Matrix.fromBlocks L 0 0 K := by
    rw [hP, Matrix.fromBlocks_multiply]
    simp
  have hNJNdet : (Nᵀ * J * N).det ≠ 0 := by
    rw [hNJN, hfac, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
    exact mul_ne_zero hPdet (mul_ne_zero hLdet hKdet)
  -- Expand (Nᵀ*J*N).det = N.det * J.det * N.det; nonzero ⟹ N.det ≠ 0.
  have hNdet : N.det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hNJNdet
    intro hz
    apply hNJNdet
    rw [hz]; ring
  -- Step 6: independence from `N.det ≠ 0`.
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- The complex vector of real coefficients.
  set z : Fin g ⊕ Fin g → ℂ := fun k => (c k : ℂ) with hz
  -- Column-sum vanishing, extracted from `hc` evaluated pointwise.
  have hcol : ∀ j, (∑ k, z k * Matrix.fromRows A B k j) = 0 := by
    intro j
    have hcj := congrFun hc j
    rw [Finset.sum_apply] at hcj
    simp only [Pi.smul_apply, Pi.zero_apply] at hcj
    rw [← hcj]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact (Complex.real_smul).symm
  -- Row `inl j` of `Nᵀ` at column `k` is the `(k, j)` entry of the period matrix `M`.
  have hrow_inl : ∀ (j : Fin g) (k : Fin g ⊕ Fin g),
      Nᵀ (Sum.inl j) k = Matrix.fromRows A B k j := by
    intro j k
    rw [hNt]
    cases k <;>
      simp [Matrix.fromBlocks, Matrix.transpose_apply, Matrix.fromRows]
  -- Row `inr j` of `Nᵀ` at column `k` is the conjugate of that entry.
  have hrow_inr : ∀ (j : Fin g) (k : Fin g ⊕ Fin g),
      Nᵀ (Sum.inr j) k = starRingEnd ℂ (Matrix.fromRows A B k j) := by
    intro j k
    rw [hNt]
    cases k <;>
      simp [Matrix.fromBlocks, Matrix.transpose_apply, Matrix.fromRows, hcA, hcB, Matrix.map_apply]
  -- `z` is fixed by conjugation (its entries are real).
  have hzconj : ∀ k, starRingEnd ℂ (z k) = z k := by
    intro k; rw [hz]; exact Complex.conj_ofReal _
  -- `Nᵀ.mulVec z = 0`.
  have hmv : Nᵀ.mulVec z = 0 := by
    funext i
    rw [Pi.zero_apply, Matrix.mulVec, dotProduct]
    cases i with
    | inl j =>
      -- ∑ k, M k j * z k = ∑ k, z k * M k j = 0.
      simp_rw [hrow_inl]
      rw [← hcol j]
      exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    | inr j =>
      -- ∑ k, conj(M k j) * z k = conj (∑ k, M k j * z k) = conj 0 = 0.
      have hinner : (∑ k, Matrix.fromRows A B k j * z k) = 0 := by
        rw [← hcol j]
        exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
      simp_rw [hrow_inr]
      have hterm : ∀ k, starRingEnd ℂ (Matrix.fromRows A B k j) * z k
          = starRingEnd ℂ (Matrix.fromRows A B k j * z k) := by
        intro k; rw [map_mul, hzconj]
      simp_rw [hterm, ← map_sum, hinner, map_zero]
  -- det Nᵀ ≠ 0 ⟹ z = 0.
  have hNtdet : Nᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact hNdet
  have hzz : z = 0 := Matrix.eq_zero_of_mulVec_eq_zero hNtdet hmv
  intro k
  have : (c k : ℂ) = 0 := congrFun hzz k
  exact_mod_cast this

end Jacobians
