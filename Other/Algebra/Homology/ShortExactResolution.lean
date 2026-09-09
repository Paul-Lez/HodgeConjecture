/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# A two-term resolution from a short exact sequence

For a short exact sequence `0 → A → B → C → 0`, the complex `B → C` in degrees zero and
one is quasi-isomorphic to `A` in degree zero. The construction retains the displayed maps,
so maps from the resolution can be compared on their two components.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits ZeroObject

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C)

/-- The two-term complex `X₂ → X₃` in degrees zero and one. -/
def rightResolution : CochainComplex C ℕ :=
  CochainComplex.of (fun | 0 => S.X₂ | 1 => S.X₃ | _ + 2 => 0)
    (fun | 0 => S.g | _ + 1 => 0) (by intro n; cases n <;> simp)

@[simp]
theorem rightResolution_d_zero_one : S.rightResolution.d 0 1 = S.g := by
  simp [rightResolution, CochainComplex.of.d]

@[simp]
theorem rightResolution_d_succ (n : ℕ) : S.rightResolution.d (n + 1) (n + 2) = 0 := by
  simp [rightResolution, CochainComplex.of.d]

/-- The augmentation given by the displayed kernel map. -/
def rightResolutionι : (CochainComplex.single₀ C).obj S.X₁ ⟶ S.rightResolution :=
  (CochainComplex.fromSingle₀Equiv S.rightResolution S.X₁).symm
    ⟨S.f, by rw [rightResolution_d_zero_one]; exact S.zero⟩

/-- Exactness and injectivity identify the degree-zero homology of the resolution. -/
theorem rightResolutionι_quasiIsoAt_zero (hS : S.ShortExact) :
    QuasiIsoAt S.rightResolutionι 0 := by
  rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
  · constructor
    · change (ShortComplex.mk
        (((CochainComplex.fromSingle₀Equiv S.rightResolution S.X₁).symm
          ⟨S.f, _⟩).f 0) (S.rightResolution.d 0 1) _).Exact
      simp only [CochainComplex.fromSingle₀Equiv_symm_apply_f_zero, rightResolution_d_zero_one]
      convert hS.exact using 1
      rfl
    · simpa [rightResolutionι, CochainComplex.fromSingle₀Equiv] using hS.mono_f
  all_goals rfl

/-- Surjectivity kills the degree-one homology, and all higher terms vanish. -/
theorem rightResolution_exactAt_succ (hS : S.ShortExact) (n : ℕ) :
    S.rightResolution.ExactAt (n + 1) := by
  cases n with
  | zero =>
      rw [HomologicalComplex.exactAt_iff' S.rightResolution 0 1 2
        (CochainComplex.prev_nat_succ 0) (CochainComplex.next ℕ 1)]
      change (ShortComplex.mk (S.rightResolution.d 0 1) (S.rightResolution.d 1 2) _).Exact
      simp only [rightResolution_d_zero_one, rightResolution_d_succ]
      exact (ShortComplex.exact_iff_epi _ rfl).2 hS.epi_g
  | succ n =>
      apply ShortComplex.exact_of_isZero_X₂
      exact isZero_zero C

/-- The displayed augmentation is a quasi-isomorphism when the sequence is short exact. -/
theorem rightResolutionι_quasiIso (hS : S.ShortExact) : _root_.QuasiIso S.rightResolutionι where
  quasiIsoAt n := by
    cases n with
    | zero => exact S.rightResolutionι_quasiIsoAt_zero hS
    | succ n =>
        rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj S.X₁ n)]
        exact S.rightResolution_exactAt_succ hS n

/-- A map out of the two-term resolution is specified by a compatible map in each degree. -/
def fromRightResolution {K : CochainComplex C ℕ}
    (f₀ : S.X₂ ⟶ K.X 0) (f₁ : S.X₃ ⟶ K.X 1)
    (h₀ : f₀ ≫ K.d 0 1 = S.g ≫ f₁) (h₁ : f₁ ≫ K.d 1 2 = 0) :
    S.rightResolution ⟶ K :=
  CochainComplex.ofHom (fun | 0 => f₀ | 1 => f₁ | _ + 2 => 0) (by
    intro n
    cases n with
    | zero =>
        change f₀ ≫ K.d 0 1 = S.rightResolution.d 0 1 ≫ f₁
        rw [rightResolution_d_zero_one]
        exact h₀
    | succ n =>
        cases n with
        | zero =>
            change f₁ ≫ K.d 1 2 = S.rightResolution.d 1 2 ≫ 0
            rw [rightResolution_d_succ, zero_comp]
            exact h₁
        | succ n => simp)

@[simp]
theorem fromRightResolution_f_zero {K : CochainComplex C ℕ}
    (f₀ : S.X₂ ⟶ K.X 0) (f₁ : S.X₃ ⟶ K.X 1)
    (h₀ : f₀ ≫ K.d 0 1 = S.g ≫ f₁) (h₁ : f₁ ≫ K.d 1 2 = 0) :
    (S.fromRightResolution f₀ f₁ h₀ h₁).f 0 = f₀ := rfl

@[simp]
theorem fromRightResolution_f_one {K : CochainComplex C ℕ}
    (f₀ : S.X₂ ⟶ K.X 0) (f₁ : S.X₃ ⟶ K.X 1)
    (h₀ : f₀ ≫ K.d 0 1 = S.g ≫ f₁) (h₁ : f₁ ≫ K.d 1 2 = 0) :
    (S.fromRightResolution f₀ f₁ h₀ h₁).f 1 = f₁ := rfl

end CategoryTheory.ShortComplex
