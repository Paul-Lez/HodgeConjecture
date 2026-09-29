/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Maximal minors and the support of a finitely presented module

Let `F` be a free module over a commutative ring `R` with basis `e_i` (`i ∈ I`), and let
`v_j = ∑ᵢ A i j • e_i` (`j ∈ J`) be finitely many elements of `F`. Write `A_σ` for the square
matrix whose `k`-th column is the `σ k`-th column of `A`, for `σ : I → J`. Then:

- every maximal minor `det A_σ` kills `F ⧸ span v` (`Matrix.det_submatrix_smul_mem_span`);
- if `R` is local and the `v_j` span `F`, some maximal minor is a unit
  (`Matrix.exists_isUnit_det_submatrix_of_mul_eq_one`).

Together these say that the zero locus of the maximal minors of a presentation matrix is the
support of the presented module, which is how the support of a coherent sheaf is described by
finitely many sections.

## Main results

- `Matrix.det_mul_eq_sum_det_submatrix`: `det (A * C) = ∑_σ (∏_k C (σ k) k) * det A_σ`.
- `Matrix.det_submatrix_smul_mem_span`.
- `Matrix.exists_isUnit_det_submatrix_of_mul_eq_one`.
- `Module.det_submatrix_mem_annihilator` and `Module.exists_isUnit_det_submatrix`: the two
  statements for a module presented by a surjection from a free module.
-/

@[expose] public section

open Finset

namespace Matrix

variable {R : Type*} [CommRing R] {I J : Type*} [Fintype I] [DecidableEq I]

/-- **Expansion of a determinant along maximal minors**, a form of the Cauchy–Binet formula:
`det (A * C) = ∑_{σ : I → J} (∏_k C (σ k) k) * det A_σ`, where `A_σ` has `k`-th column the
`σ k`-th column of `A`. -/
theorem det_mul_eq_sum_det_submatrix [Fintype J] (A : Matrix I J R) (C : Matrix J I R) :
    (A * C).det = ∑ σ : I → J, (∏ k, C (σ k) k) * (A.submatrix id σ).det := by
  classical
  rw [← det_transpose, transpose_mul]
  have hrow : (Cᵀ * Aᵀ : Matrix I I R) = fun k ↦ ∑ j, C j k • Aᵀ j := by
    ext k i
    simp [mul_apply, Finset.sum_apply, mul_comm]
  calc (Cᵀ * Aᵀ).det = detRowAlternating (fun k ↦ ∑ j, C j k • Aᵀ j) := by rw [hrow]; rfl
    _ = ∑ σ : I → J, detRowAlternating (fun k ↦ C (σ k) k • Aᵀ (σ k)) :=
        (detRowAlternating (n := I) (R := R)).toMultilinearMap.map_sum
          (fun k j ↦ C j k • Aᵀ j)
    _ = ∑ σ : I → J, (∏ k, C (σ k) k) * (A.submatrix id σ).det := by
        refine Finset.sum_congr rfl fun σ _ ↦ ?_
        rw [AlternatingMap.map_smul_univ, smul_eq_mul, ← det_transpose (A.submatrix id σ)]
        rfl

/-- If `A * C = 1` over a local ring, some maximal minor of `A` is a unit. -/
theorem exists_isUnit_det_submatrix_of_mul_eq_one [Fintype J] [IsLocalRing R]
    {A : Matrix I J R} {C : Matrix J I R} (h : A * C = 1) :
    ∃ σ : I → J, IsUnit (A.submatrix id σ).det := by
  by_contra hne
  push Not at hne
  have hsum : (A * C).det ∈ IsLocalRing.maximalIdeal R := by
    rw [det_mul_eq_sum_det_submatrix]
    exact sum_mem fun σ _ ↦ Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hne σ))
  rw [h, det_one] at hsum
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 hsum)

/-- **A maximal minor kills the cokernel**: `det A_σ • e_k` lies in the span of the elements
`v_j = ∑ᵢ A i j • e_i`. -/
theorem det_submatrix_smul_mem_span {F : Type*} [AddCommGroup F] [Module R F] (e : I → F)
    (A : Matrix I J R) (σ : I → J) (k : I) :
    (A.submatrix id σ).det • e k ∈
      Submodule.span R (Set.range fun j ↦ ∑ i, A i j • e i) := by
  set B := A.submatrix id σ
  have h1 : ∑ i', B.adjugate i' k • ∑ i, A i (σ i') • e i = ∑ i, (B * B.adjugate) i k • e i := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i' _ ↦ ?_
    simp [B, mul_comm]
  have h2 : ∑ i, (B * B.adjugate) i k • e i = B.det • e k := by
    rw [mul_adjugate]
    simp [Matrix.one_apply, ite_smul]
  rw [← h2, ← h1]
  exact Submodule.sum_mem _ fun i' _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ i', rfl⟩)

end Matrix

namespace Module

variable {R : Type*} [CommRing R] {I J : Type*} [Fintype I] [DecidableEq I]
  {F Q : Type*} [AddCommGroup F] [Module R F] [AddCommGroup Q] [Module R Q]

/-- **Maximal minors of a presentation matrix annihilate the presented module.** Here `Q` is
presented as the quotient of `F` (with basis `e`) by the span of the `v_j`, and the matrix has
entries the coordinates of the `v_j`. -/
theorem det_submatrix_mem_annihilator (e : Basis I R F) (v : J → F) (p : F →ₗ[R] Q)
    (hp : Function.Surjective p) (hker : Submodule.span R (Set.range v) ≤ LinearMap.ker p)
    (σ : I → J) :
    ((Matrix.of fun i j ↦ e.repr (v j) i).submatrix id σ).det ∈ Module.annihilator R Q := by
  rw [Module.mem_annihilator]
  intro q
  obtain ⟨f, rfl⟩ := hp q
  have hv : (fun j ↦ ∑ i, (Matrix.of fun i j ↦ e.repr (v j) i) i j • e i) = v :=
    funext fun j ↦ e.sum_repr (v j)
  have hmem : ((Matrix.of fun i j ↦ e.repr (v j) i).submatrix id σ).det • f ∈
      Submodule.span R (Set.range v) := by
    rw [← e.sum_repr f, Finset.smul_sum]
    refine Submodule.sum_mem _ fun k _ ↦ ?_
    rw [smul_comm]
    refine Submodule.smul_mem _ _ ?_
    have := Matrix.det_submatrix_smul_mem_span e (Matrix.of fun i j ↦ e.repr (v j) i) σ k
    rwa [hv] at this
  rw [← map_smul]
  exact hker hmem

/-- **If the presented module vanishes, some maximal minor of a presentation matrix is a
unit**, over a local ring. -/
theorem exists_isUnit_det_submatrix [IsLocalRing R] [Finite J] (e : Basis I R F) (v : J → F)
    (p : F →ₗ[R] Q) (hker : LinearMap.ker p ≤ Submodule.span R (Set.range v))
    [Subsingleton Q] :
    ∃ σ : I → J, IsUnit ((Matrix.of fun i j ↦ e.repr (v j) i).submatrix id σ).det := by
  haveI := Fintype.ofFinite J
  have hk : ∀ k, ∃ c : J → R, ∑ j, c j • v j = e k := fun k ↦
    (Submodule.mem_span_range_iff_exists_fun R).mp (hker (Subsingleton.elim _ _))
  choose c hc using hk
  refine Matrix.exists_isUnit_det_submatrix_of_mul_eq_one (C := Matrix.of fun j k ↦ c k j) ?_
  ext i k
  have := congrArg (fun x ↦ e.repr x i) (hc k)
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, Basis.repr_self, Finsupp.single_apply] at this
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply]
  rw [show (if i = k then (1 : R) else 0) = if k = i then 1 else 0 from if_congr eq_comm rfl rfl,
    ← this]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _

end Module

end
