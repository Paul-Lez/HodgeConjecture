/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache License 2.0 as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.TwoOpenCechCochain

/-!
# The transition part of a three-open Čech--cochain total complex

For an ordered three-open cover, the first Chern cocycle has no components on the individual
opens: it consists of degree-one cochains on the three pairwise overlaps, together with a
degree-zero branch-jump cochain on the triple overlap.  This file packages precisely that
literal part of the Čech--singular total complex.

The convention is

`res₀₁(a₀₁) - res₀₂(a₀₂) + res₁₂(a₁₂) = - d b`.

It is implemented as the existing two-open cone after grouping the `01` and `12` summands.
Consequently it is a raw cochain construction: no local or global cohomology class, and no
choice of representative, is used here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology.Singular

variable {K₀₁ K₀₂ K₁₂ K₀₁₂ : CochainComplex (ModuleCat ℚ) ℤ}

/-- The alternating Čech restriction from the three pairwise intersections to the triple
intersection, with the standard `01 - 02 + 12` signs. -/
def threeOpenCechTransitionDifference
    (r₀₁ : K₀₁ ⟶ K₀₁₂) (r₀₂ : K₀₂ ⟶ K₀₁₂) (r₁₂ : K₁₂ ⟶ K₀₁₂) :
    (K₀₁ ⊞ K₁₂) ⊞ K₀₂ ⟶ K₀₁₂ :=
  biprod.desc (biprod.desc r₀₁ r₁₂) (-r₀₂)

/-- The Čech--singular transition total for three opens.  Its degree `n - 1` term contains
degree-`n` cochains on `01`, `02`, and `12`, plus a degree-`n-1` cochain on `012`. -/
def threeOpenCechTransitionTotal
    (r₀₁ : K₀₁ ⟶ K₀₁₂) (r₀₂ : K₀₂ ⟶ K₀₁₂) (r₁₂ : K₁₂ ⟶ K₀₁₂) :
    CochainComplex (ModuleCat ℚ) ℤ :=
  twoOpenCechTotal (biprod.desc r₀₁ r₁₂) r₀₂

/-- The literal transition cochain with its three pair-overlap cochains and its specified
triple-overlap branch-jump primitive. -/
def threeOpenCechTransitionCochain
    (r₀₁ : K₀₁ ⟶ K₀₁₂) (r₀₂ : K₀₂ ⟶ K₀₁₂) (r₁₂ : K₁₂ ⟶ K₀₁₂) (n : ℤ)
    (a₀₁ : K₀₁.X n) (a₀₂ : K₀₂.X n) (a₁₂ : K₁₂.X n) (b : K₀₁₂.X (n - 1)) :
    (threeOpenCechTransitionTotal r₀₁ r₀₂ r₁₂).X (n - 1) :=
  twoOpenCechCochain (biprod.desc r₀₁ r₁₂) r₀₂ n
    (((biprod.inl : K₀₁ ⟶ K₀₁ ⊞ K₁₂).f n).hom a₀₁ +
      ((biprod.inr : K₁₂ ⟶ K₀₁ ⊞ K₁₂).f n).hom a₁₂)
    a₀₂ b

/-- Explicit pair/triple-overlap data satisfying the Čech transition equation is a closed
cochain in the three-open transition total. -/
theorem threeOpenCechTransitionCochain_closed
    (r₀₁ : K₀₁ ⟶ K₀₁₂) (r₀₂ : K₀₂ ⟶ K₀₁₂) (r₁₂ : K₁₂ ⟶ K₀₁₂) (n : ℤ)
    (a₀₁ : K₀₁.X n) (a₀₂ : K₀₂.X n) (a₁₂ : K₁₂.X n) (b : K₀₁₂.X (n - 1))
    (ha₀₁ : K₀₁.d n (n + 1) a₀₁ = 0) (ha₀₂ : K₀₂.d n (n + 1) a₀₂ = 0)
    (ha₁₂ : K₁₂.d n (n + 1) a₁₂ = 0)
    (hcompat : r₀₁.f n a₀₁ - r₀₂.f n a₀₂ + r₁₂.f n a₁₂ =
      -K₀₁₂.d (n - 1) n b) :
    (threeOpenCechTransitionTotal r₀₁ r₀₂ r₁₂).d (n - 1) n
      (threeOpenCechTransitionCochain r₀₁ r₀₂ r₁₂ n a₀₁ a₀₂ a₁₂ b) = 0 := by
  let K₀ : CochainComplex (ModuleCat ℚ) ℤ := K₀₁ ⊞ K₁₂
  let a₀ : K₀.X n :=
    ((biprod.inl : K₀₁ ⟶ K₀).f n).hom a₀₁ +
      ((biprod.inr : K₁₂ ⟶ K₀).f n).hom a₁₂
  have ha₀ : K₀.d n (n + 1) a₀ = 0 := by
    change ((K₀₁ ⊞ K₁₂).d n (n + 1))
      (((biprod.inl : K₀₁ ⟶ K₀₁ ⊞ K₁₂).f n).hom a₀₁ +
        ((biprod.inr : K₁₂ ⟶ K₀₁ ⊞ K₁₂).f n).hom a₁₂) = 0
    rw [map_add]
    have h₀ := ConcreteCategory.congr_hom
      ((biprod.inl : K₀₁ ⟶ K₀₁ ⊞ K₁₂).comm n (n + 1)) a₀₁
    have h₁ := ConcreteCategory.congr_hom
      ((biprod.inr : K₁₂ ⟶ K₀₁ ⊞ K₁₂).comm n (n + 1)) a₁₂
    simp only [ConcreteCategory.comp_apply] at h₀ h₁
    rw [h₀, h₁, ha₀₁, ha₁₂, map_zero, map_zero, add_zero]
  have hδ : (biprod.desc r₀₁ r₁₂).f n a₀ =
      r₀₁.f n a₀₁ + r₁₂.f n a₁₂ := by
    change (biprod.desc r₀₁ r₁₂).f n
        (((biprod.inl : K₀₁ ⟶ K₀₁ ⊞ K₁₂).f n).hom a₀₁ +
          ((biprod.inr : K₁₂ ⟶ K₀₁ ⊞ K₁₂).f n).hom a₁₂) = _
    rw [map_add]
    have h₀ := ConcreteCategory.congr_hom
      (congrArg (fun f => f.f n) (biprod.inl_desc r₀₁ r₁₂)) a₀₁
    have h₁ := ConcreteCategory.congr_hom
      (congrArg (fun f => f.f n) (biprod.inr_desc r₀₁ r₁₂)) a₁₂
    simpa only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] using
      congrArg₂ (· + ·) h₀ h₁
  apply twoOpenCechCochain_closed (biprod.desc r₀₁ r₁₂) r₀₂ n a₀ a₀₂ b ha₀ ha₀₂
  rw [hδ]
  calc
    r₀₁.f n a₀₁ + r₁₂.f n a₁₂ - r₀₂.f n a₀₂ =
        r₀₁.f n a₀₁ - r₀₂.f n a₀₂ + r₁₂.f n a₁₂ := by abel
    _ = -K₀₁₂.d (n - 1) n b := hcompat

end AlgebraicTopology.Singular
