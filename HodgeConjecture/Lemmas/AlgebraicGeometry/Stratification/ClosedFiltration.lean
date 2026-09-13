/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Stratification.ClosedFiltration

/-!
# The canonical smooth decomposition as a closed filtration

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Stratification.ClosedFiltration`.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

@[simp] theorem reducedSmoothClosedFiltration_zero (S : Closeds X) :
    reducedSmoothClosedFiltration f S 0 = S := rfl

@[simp] theorem reducedSmoothClosedFiltration_succ (S : Closeds X) (k : ℕ) :
    reducedSmoothClosedFiltration f S (k + 1) =
      reducedClosedSingularRemainder f (reducedSmoothClosedFiltration f S k) := rfl

theorem reducedSmoothClosedFiltration_succ_start (S : Closeds X) (k : ℕ) :
    reducedSmoothClosedFiltration f S (k + 1) =
      reducedSmoothClosedFiltration f (reducedClosedSingularRemainder f S) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [reducedSmoothClosedFiltration_succ, ih, reducedSmoothClosedFiltration_succ]

@[simp] theorem reducedClosedSingularRemainder_bot :
    reducedClosedSingularRemainder f ⊥ = ⊥ :=
  le_bot_iff.mp (reducedClosedSingularRemainder_le f ⊥)

@[simp] theorem reducedSmoothClosedFiltration_bot (k : ℕ) :
    reducedSmoothClosedFiltration f ⊥ k = ⊥ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [reducedSmoothClosedFiltration_succ, ih, reducedClosedSingularRemainder_bot]

theorem reducedSmoothClosedFiltration_succ_le (S : Closeds X) (k : ℕ) :
    reducedSmoothClosedFiltration f S (k + 1) ≤ reducedSmoothClosedFiltration f S k :=
  reducedClosedSingularRemainder_le f _

theorem reducedSmoothClosedFiltration_antitone (S : Closeds X) :
    Antitone (reducedSmoothClosedFiltration f S) :=
  antitone_nat_of_succ_le (reducedSmoothClosedFiltration_succ_le f S)

theorem reducedSmoothClosedFiltration_le (S : Closeds X) (k : ℕ) :
    reducedSmoothClosedFiltration f S k ≤ S :=
  reducedSmoothClosedFiltration_antitone f S (Nat.zero_le k)

/-- Each successive layer is the range of the smooth locally closed immersion. -/
theorem reducedSmoothClosedFiltration_layer (S : Closeds X) (k : ℕ) :
    Set.range (reducedClosedSmoothPieceι f (reducedSmoothClosedFiltration f S k)) =
      (reducedSmoothClosedFiltration f S k : Set X) \
        (reducedSmoothClosedFiltration f S (k + 1) : Set X) :=
  reducedClosedSmoothPiece_range f _

variable [PerfectField K] [NoetherianSpace X]

/-- The terminal index is the finite list length, not supplied termination data. -/
theorem reducedSmoothClosedFiltration_length (S : Closeds X) :
    reducedSmoothClosedFiltration f S (reducedSmoothStratification f S).length = ⊥ := by
  induction S using (wellFounded_lt (α := Closeds X)).induction with
  | h S ih =>
    by_cases hS : S = ⊥
    · subst S
      exact reducedSmoothClosedFiltration_bot f _
    · have hlen : (reducedSmoothStratification f S).length =
          (reducedSmoothStratification f (reducedClosedSingularRemainder f S)).length + 1 := by
        rw [reducedSmoothStratification, dif_neg hS, List.length_cons]
      rw [hlen, reducedSmoothClosedFiltration_succ_start]
      exact ih _ (reducedClosedSingularRemainder_lt f S hS)

end AlgebraicGeometry
