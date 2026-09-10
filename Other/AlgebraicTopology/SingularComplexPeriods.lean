/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Other.AlgebraicTopology.SingularCohomologyCoefficientNonvanishing
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Complex periods on rational singular homology

A complex singular cohomology class restricts along rational-to-complex homology base change to
a complex-valued rational period functional.  The restriction is injective because rational
homology spans complex homology after coefficient extension.  This gives a convenient real
structure without choosing a conjugation map on a homology quotient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits
open AlgebraicTopology
open scoped Simplicial TensorProduct

namespace AlgebraicTopology.Singular

section PeriodLinearAlgebra

variable (M : Type) [AddCommGroup M] [Module ℚ M]

/-- Pull a complex-valued rational period functional back along a rational-linear map. -/
def periodPrecomp (T : M →ₗ[ℚ] M) :
    Module.End ℂ (ComplexPeriodSpace M) where
  toFun phi := phi.comp T
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem periodPrecomp_apply (T : M →ₗ[ℚ] M)
    (phi : ComplexPeriodSpace M) (z : M) :
    periodPrecomp M T phi z = phi (T z) :=
  rfl

theorem conjugatePeriod_smul (c : ℂ) (phi : ComplexPeriodSpace M) :
    conjugatePeriod M (c • phi) =
      (starRingEnd ℂ c) • conjugatePeriod M phi := by
  ext z
  simp [map_mul]

theorem periodPrecomp_conjugatePeriod (T : M →ₗ[ℚ] M)
    (phi : ComplexPeriodSpace M) :
    periodPrecomp M T (conjugatePeriod M phi) =
      conjugatePeriod M (periodPrecomp M T phi) := by
  ext z
  rfl

/-- A nonzero period eigenvector and its conjugate are independent when their eigenvalues are
distinct. -/
theorem period_conjugate_linearIndependent_of_eigen
    (T : M →ₗ[ℚ] M) (lambda : ℂ) (phi : ComplexPeriodSpace M)
    (hphi : periodPrecomp M T phi = lambda • phi)
    (hlambda : lambda ≠ starRingEnd ℂ lambda) (hne : phi ≠ 0) :
    LinearIndependent ℂ ![phi, conjugatePeriod M phi] := by
  apply (periodPrecomp M T).eigenvectors_linearIndependent'
    ![lambda, starRingEnd ℂ lambda]
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hlambda hij).elim
    · exact (hlambda hij.symm).elim
    · rfl
  · intro i
    fin_cases i
    · exact ⟨Module.End.mem_eigenspace_iff.mpr hphi, hne⟩
    · have heigen :
          periodPrecomp M T (conjugatePeriod M phi) =
            (starRingEnd ℂ lambda) • conjugatePeriod M phi := by
        rw [periodPrecomp_conjugatePeriod, hphi, conjugatePeriod_smul]
      have hconj : conjugatePeriod M phi ≠ 0 := by
        intro hzero
        apply hne
        have h := congrArg (conjugatePeriod M) hzero
        simpa using h
      change (periodPrecomp M T).HasEigenvector (starRingEnd ℂ lambda)
        (conjugatePeriod M phi)
      exact ⟨Module.End.mem_eigenspace_iff.mpr heigen, hconj⟩

/-- Two independent complex-valued rational functionals are detected by two rational vectors
with a nonzero evaluation determinant. -/
theorem exists_pairing_det_ne_zero_of_linearIndependent
    (phi psi : ComplexPeriodSpace M)
    (h : LinearIndependent ℂ ![phi, psi]) :
    ∃ x y : M, phi x * psi y - phi y * psi x ≠ 0 := by
  have hphi : phi ≠ 0 := h.ne_zero 0
  obtain ⟨x, hx⟩ : ∃ x : M, phi x ≠ 0 := by
    simpa [LinearMap.ext_iff] using hphi
  let c : ℂ := psi x / phi x
  have hdiff : psi - c • phi ≠ 0 := by
    intro hzero
    have hrel : (-c) • phi + (1 : ℂ) • psi = 0 := by
      rw [sub_eq_zero.mp hzero]
      simp
    have hc := h.eq_zero_of_pair hrel
    exact one_ne_zero hc.2
  obtain ⟨y, hy⟩ : ∃ y : M, (psi - c • phi) y ≠ 0 := by
    simpa [LinearMap.ext_iff] using hdiff
  refine ⟨x, y, ?_⟩
  have hc : psi x = c * phi x := by
    dsimp [c]
    field_simp
  have hfactor :
      phi x * psi y - phi y * psi x =
        phi x * ((psi - c • phi) y) := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply]
    rw [hc]
    ring
  rw [hfactor]
  exact mul_ne_zero hx hy

/-- A nonzero two-by-two evaluation determinant makes the two detecting rational vectors
linearly independent. -/
theorem linearIndependent_pair_of_pairing_det_ne_zero
    (phi psi : ComplexPeriodSpace M) (x y : M)
    (hdet : phi x * psi y - phi y * psi x ≠ 0) :
    LinearIndependent ℚ ![x, y] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hy
    have hy' : y = 0 := by simpa using hy
    subst y
    simp at hdet
  · intro a hax
    have hax' : a • y = x := by simpa using hax
    have hphi := congrArg phi hax'
    have hpsi := congrArg psi hax'
    simp only [map_smul, Algebra.smul_def] at hphi hpsi
    apply hdet
    rw [← hphi, ← hpsi]
    ring

/-- Coordinate functionals on an independent rational pair extend to the whole vector space. -/
theorem exists_rational_dual_pair (x y : M)
    (hxy : LinearIndependent ℚ ![x, y]) :
    ∃ beta gamma : M →ₗ[ℚ] ℚ,
      beta x = 1 ∧ beta y = 0 ∧ gamma x = 0 ∧ gamma y = 1 := by
  let v : Fin 2 → M := ![x, y]
  let P : Submodule ℚ M := Submodule.span ℚ (Set.range v)
  let b : Module.Basis (Fin 2) ℚ P := Module.Basis.span hxy
  obtain ⟨beta, hbeta⟩ := (b.coord 0).exists_extend
  obtain ⟨gamma, hgamma⟩ := (b.coord 1).exists_extend
  refine ⟨beta, gamma, ?_, ?_, ?_, ?_⟩
  · have h : beta ((b 0 : P) : M) = 1 := by
      calc
        beta ((b 0 : P) : M) = b.coord 0 (b 0) := LinearMap.congr_fun hbeta (b 0)
        _ = 1 := by simp
    simpa [b, v, P] using h
  · have h : beta ((b 1 : P) : M) = 0 := by
      calc
        beta ((b 1 : P) : M) = b.coord 0 (b 1) := LinearMap.congr_fun hbeta (b 1)
        _ = 0 := by simp
    simpa [b, v, P] using h
  · have h : gamma ((b 0 : P) : M) = 0 := by
      calc
        gamma ((b 0 : P) : M) = b.coord 1 (b 0) := LinearMap.congr_fun hgamma (b 0)
        _ = 0 := by simp
    simpa [b, v, P] using h
  · have h : gamma ((b 1 : P) : M) = 1 := by
      calc
        gamma ((b 1 : P) : M) = b.coord 1 (b 1) := LinearMap.congr_fun hgamma (b 1)
        _ = 1 := by simp
    simpa [b, v, P] using h

/-- The complex period functionals obtained from a rational coordinate pair remain independent
over `ℂ`. -/
theorem rationalPeriod_pair_linearIndependent_of_dual_values
    (x y : M) (beta gamma : M →ₗ[ℚ] ℚ)
    (hbx : beta x = 1) (_hby : beta y = 0)
    (hgx : gamma x = 0) (hgy : gamma y = 1) :
    LinearIndependent ℂ
      ![rationalPeriod M beta, rationalPeriod M gamma] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hzero
    have h := LinearMap.congr_fun hzero y
    change algebraMap ℚ ℂ (gamma y) = 0 at h
    rw [hgy] at h
    norm_num at h
  · intro c heq
    have h := congrArg (fun f : ComplexPeriodSpace M => f x) heq
    change c * algebraMap ℚ ℂ (gamma x) = algebraMap ℚ ℂ (beta x) at h
    rw [hbx, hgx] at h
    norm_num at h

/-- Any independent pair of complex periods forces an independent pair coming from rational
dual classes. -/
theorem exists_rationalPeriod_pair_linearIndependent
    (phi psi : ComplexPeriodSpace M)
    (h : LinearIndependent ℂ ![phi, psi]) :
    ∃ beta gamma : M →ₗ[ℚ] ℚ,
      LinearIndependent ℂ
        ![rationalPeriod M beta, rationalPeriod M gamma] := by
  obtain ⟨x, y, hdet⟩ := exists_pairing_det_ne_zero_of_linearIndependent M phi psi h
  have hxy := linearIndependent_pair_of_pairing_det_ne_zero M phi psi x y hdet
  obtain ⟨beta, gamma, hbx, hby, hgx, hgy⟩ :=
    exists_rational_dual_pair M x y hxy
  exact ⟨beta, gamma,
    rationalPeriod_pair_linearIndependent_of_dual_values M x y beta gamma
      hbx hby hgx hgy⟩

end PeriodLinearAlgebra

local instance (X : TopCat) (n : ℕ) : Module ℚ ((CChains X).homology n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (X : TopCat) (n : ℕ) : IsScalarTower ℚ ℂ ((CChains X).homology n) :=
  IsScalarTower.of_compHom ℚ ℂ _

/-- Restrict a complex singular cohomology class to complex-valued periods on rational
homology. -/
def complexCohomologyPeriod (X : TopCat) (n : ℕ) :
    Cohomology ℂ X n →ₗ[ℂ] ComplexPeriodSpace (Homology ℚ X n) where
  toFun alpha :=
    { toFun := fun z => alpha (qToCHomology X n z)
      map_add' := by intro x y; simp
      map_smul' := by intro q z; simp [Algebra.smul_def] }
  map_add' alpha beta := by
    ext z
    simp
  map_smul' c alpha := by
    ext z
    simp

@[simp]
theorem complexCohomologyPeriod_apply (X : TopCat) (n : ℕ)
    (alpha : Cohomology ℂ X n) (z : Homology ℚ X n) :
    complexCohomologyPeriod X n alpha z = alpha (qToCHomology X n z) :=
  rfl

/-- Complex cohomology classes are determined by their values on complexifications of rational
homology classes.  No finite-dimensionality hypothesis is needed. -/
theorem complexCohomologyPeriod_injective (X : TopCat) (n : ℕ) :
    Function.Injective (complexCohomologyPeriod X n) := by
  intro alpha beta h
  ext w
  apply (qToCHomology_isBaseChange X n).inductionOn w (fun w => alpha w = beta w)
  · simp
  · intro z
    exact LinearMap.congr_fun h z
  · intro c z hz
    simp [hz]
  · intro x y hx hy
    simp [hx, hy]

/-- The periods of a rational cohomology class after coefficient extension are exactly its
rational values embedded in `ℂ`. -/
theorem complexCohomologyPeriod_rationalToComplex (X : TopCat) (n : ℕ)
    (beta : Cohomology ℚ X n) :
    complexCohomologyPeriod X n (rationalToComplexCohomologyMap X n beta) =
      rationalPeriod (Homology ℚ X n) beta := by
  apply LinearMap.ext
  intro z
  exact (qToCHomology_isBaseChange X n).toDual_comp_apply beta z

/-- Two independent complex period functionals force two rational cohomology classes whose
complexifications remain independent.  This avoids any finite-dimensionality assumption on
singular homology. -/
theorem exists_rationalCohomology_pair_complexification_linearIndependent_of_periods
    (X : TopCat) (n : ℕ)
    (phi psi : ComplexPeriodSpace (Homology ℚ X n))
    (h : LinearIndependent ℂ ![phi, psi]) :
    ∃ beta gamma : Cohomology ℚ X n,
      LinearIndependent ℂ
        ![rationalToComplexCohomologyMap X n beta,
          rationalToComplexCohomologyMap X n gamma] := by
  obtain ⟨beta, gamma, hrat⟩ :=
    exists_rationalPeriod_pair_linearIndependent (Homology ℚ X n) phi psi h
  refine ⟨beta, gamma, ?_⟩
  apply LinearIndependent.of_comp (complexCohomologyPeriod X n)
  convert hrat using 1
  funext i
  fin_cases i
  · change complexCohomologyPeriod X n
      (rationalToComplexCohomologyMap X n beta) = rationalPeriod _ beta
    exact complexCohomologyPeriod_rationalToComplex X n beta
  · change complexCohomologyPeriod X n
      (rationalToComplexCohomologyMap X n gamma) = rationalPeriod _ gamma
    exact complexCohomologyPeriod_rationalToComplex X n gamma

/-- A nonzero complex class has a nonzero rational period functional. -/
theorem complexCohomologyPeriod_ne_zero (X : TopCat) (n : ℕ)
    {alpha : Cohomology ℂ X n} (halpha : alpha ≠ 0) :
    complexCohomologyPeriod X n alpha ≠ 0 := by
  have h := (complexCohomologyPeriod_injective X n).ne halpha
  simpa using h

end AlgebraicTopology.Singular
