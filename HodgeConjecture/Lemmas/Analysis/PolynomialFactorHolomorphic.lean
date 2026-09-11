/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Analysis.PolynomialFactorGrowth
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Algebra.Polynomial.Splits

/-!
# Factors selected on the simple-root cover

This file studies a monic polynomial whose coefficients are polynomials in one complex
parameter.  Over the locus where every root is simple, a subset of the root cover canonically
selects a monic factor in each fiber.
-/

@[expose] public section

open scoped Polynomial
open Set

namespace Polynomial

noncomputable section

/-- Specialization of a one-parameter polynomial family. -/
def familySpecialization (p : Polynomial (Polynomial ℂ)) (z : ℂ) : Polynomial ℂ :=
  p.map (Polynomial.evalRingHom z)

/-- The parameter locus on which all roots of a polynomial family are simple. -/
def SimpleRootBase (p : Polynomial (Polynomial ℂ)) :=
  {z : ℂ // ∀ w : ℂ, (familySpecialization p z).eval w = 0 →
    (familySpecialization p z).derivative.eval w ≠ 0}

/-- The simple-root cover of a one-parameter polynomial family. -/
def SimpleRootCover (p : Polynomial (Polynomial ℂ)) :=
  {zw : SimpleRootBase p × ℂ // (familySpecialization p zw.1.1).eval zw.2 = 0}

/-- Projection of the simple-root cover to its parameter. -/
def SimpleRootCover.proj {p : Polynomial (Polynomial ℂ)} : SimpleRootCover p → SimpleRootBase p :=
  fun zw ↦ zw.1.1

/-- The multiset of roots in a fiber which belong to a specified subset of the root cover. -/
def selectedRoots {p : Polynomial (Polynomial ℂ)}
    (S : Set (SimpleRootCover p)) (z : SimpleRootBase p) : Multiset ℂ := by
  classical
  exact (familySpecialization p z.1).roots.filter fun w ↦
    ∃ h : (familySpecialization p z.1).eval w = 0,
      (⟨(z, w), h⟩ : SimpleRootCover p) ∈ S

/-- The monic fiber factor selected by a subset of the simple-root cover. -/
def selectedFactor {p : Polynomial (Polynomial ℂ)} (_hp : p.Monic)
    (S : Set (SimpleRootCover p)) (z : SimpleRootBase p) : Polynomial ℂ :=
  ((selectedRoots S z).map fun w ↦ X - C w).prod

theorem selectedFactor_monic {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    (S : Set (SimpleRootCover p)) (z : SimpleRootBase p) :
    (selectedFactor hp S z).Monic := by
  exact monic_multisetProd_X_sub_C (selectedRoots S z)

theorem selectedFactor_dvd {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    (S : Set (SimpleRootCover p)) (z : SimpleRootBase p) :
    selectedFactor hp S z ∣ familySpecialization p z.1 := by
  classical
  rw [selectedFactor, selectedRoots]
  exact (Multiset.prod_dvd_prod_of_le
    (Multiset.map_le_map (Multiset.filter_le _ _))).trans
      (familySpecialization p z.1).prod_multiset_X_sub_C_dvd

theorem natDegree_selectedFactor {p : Polynomial (Polynomial ℂ)} (hp : p.Monic)
    (S : Set (SimpleRootCover p)) (z : SimpleRootBase p) :
    (selectedFactor hp S z).natDegree =
      (selectedRoots S z).card := by
  simp [selectedFactor]

end

end Polynomial
