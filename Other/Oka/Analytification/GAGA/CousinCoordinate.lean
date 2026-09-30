/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.Cousin
public import Other.Oka.StructureSheaf
public import Other.Oka.Analytic.OkaRingDifferentiable

/-!
# Cousin splitting for holomorphic functions on opens of `ℂ^ι`

We transport the Cauchy decomposition of `Oka.Analytification.GAGA.Cousin` to the rings
`OkaRing U` of holomorphic functions on opens `U ⊆ ℂ^ι` (the sections of the structure sheaf
`okaSheaf ι`), singling out one coordinate `i : ι`; the remaining coordinates are parameters.

## Main definitions

- `Complex.splitAt i : (ι → ℂ) ≃L[ℂ] ℂ × ({j // j ≠ i} → ℂ)`: splitting off the `i`-th
  coordinate.
- `OkaRing.ofDifferentiableOn`: the element of `OkaRing U` given by a function holomorphic on `U`.

## Main results

- `OkaRing.exists_cousin_split`: **Cousin splitting in the `i`-th coordinate.** Let `f` be
  holomorphic on an open `W` containing the cylinder `{x | x i ∈ C, x_{≠ i} ∈ P}` over a closed
  rectangle `C`, and let `S` be a set of sides of `C`. Then there are `f₁`, `f₂` holomorphic
  off the cylinders over the sides in `S`, resp. not in `S`, with `f = f₁ + f₂` over the open
  rectangle and `f₁ + f₂ = 0` off the closed rectangle.
-/

@[expose] public section

open Set TopologicalSpace

universe u

variable {ι : Type u} [Fintype ι]

namespace Complex

variable [DecidableEq ι]

/-- The splitting `ℂ^ι ≃ ℂ × ℂ^{ι ∖ {i}}` off the `i`-th coordinate. -/
noncomputable def splitAt (i : ι) : (ι → ℂ) ≃L[ℂ] ℂ × ({j // j ≠ i} → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { Equiv.funSplitAt i ℂ with
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

@[simp]
lemma splitAt_apply (i : ι) (x : ι → ℂ) : splitAt i x = (x i, fun j : {j // j ≠ i} ↦ x j) :=
  rfl

end Complex

open Complex

namespace OkaRing

/-- The element of `OkaRing U` given by a function holomorphic on `U`. -/
noncomputable def ofDifferentiableOn {U : Opens (ι → ℂ)} (g : (ι → ℂ) → ℂ)
    (hg : DifferentiableOn ℂ g U) : OkaRing U :=
  OkaRing.mk (fun y : U ↦ g y) (okaAnalytic_restrict fun _ hx ↦
    analyticAt_of_differentiableOn_of_finiteDimensional U.isOpen hg hx)

@[simp]
lemma ofDifferentiableOn_toFun {U : Opens (ι → ℂ)} (g : (ι → ℂ) → ℂ)
    (hg : DifferentiableOn ℂ g U) (y : U) : (ofDifferentiableOn g hg).toFun _ y = g y :=
  rfl

variable [DecidableEq ι]

/-- The side integral, in the `i`-th coordinate, of `f` over a side of the rectangle with
corners `a` and `b`, as a function on `ℂ^ι`. -/
noncomputable def cauchySide (i : ι) (a b : ℂ) {W : Opens (ι → ℂ)} (f : OkaRing W)
    (s : RectSide) : (ι → ℂ) → ℂ :=
  fun x ↦ RectSide.cauchy (fun p ↦ f.toGlobalFun _ ((splitAt i).symm p)) a b s (splitAt i x)

variable (i : ι) {a b : ℂ} {V : Set ℂ} {P : Set ({j // j ≠ i} → ℂ)} {W : Opens (ι → ℂ)}

private lemma differentiableOn_comp_symm (hW : splitAt i ⁻¹' (V ×ˢ P) ⊆ W) (f : OkaRing W) :
    DifferentiableOn ℂ (fun p ↦ f.toGlobalFun _ ((splitAt i).symm p)) (V ×ˢ P) :=
  f.differentiableOn_toGlobalFun.comp (splitAt i).symm.differentiableOn
    fun p hp ↦ hW (by simpa using hp)

/-- A sum of side integrals in the `i`-th coordinate is holomorphic off the cylinders over the
sides involved. -/
theorem differentiableOn_sum_cauchySide (hre : a.re ≤ b.re) (him : a.im ≤ b.im)
    (hab : Icc a.re b.re ×ℂ Icc a.im b.im ⊆ V) (hP : IsOpen P)
    (hW : splitAt i ⁻¹' (V ×ˢ P) ⊆ W) (f : OkaRing W) (S : Finset RectSide) :
    DifferentiableOn ℂ (fun x ↦ ∑ s ∈ S, cauchySide i a b f s x)
      (splitAt i ⁻¹' ((⋃ s ∈ S, RectSide.set a b s)ᶜ ×ˢ P)) :=
  (RectSide.differentiableOn_sum_cauchy hab hP (differentiableOn_comp_symm i hW f) hre him
    S).comp (splitAt i).differentiableOn fun _ hx ↦ hx

/-- **Cousin splitting in the `i`-th coordinate.** Let `f` be holomorphic on an open `W`
containing the cylinder over `V × P`, where `V` contains the closed rectangle `C` with corners
`a`, `b` and `P` is open. For a set `S` of sides of `C` there are `f₁` holomorphic on any open
`U₁` off the cylinders over the sides in `S`, and `f₂` holomorphic on any open `U₂` off the
cylinders over the other sides, such that `f = f₁ + f₂` on every open inside the cylinder over the
open rectangle, and `f₁ + f₂ = 0` on every open inside the cylinder over the complement of the
closed rectangle. -/
theorem exists_cousin_split (hre : a.re < b.re) (him : a.im < b.im)
    (hab : Icc a.re b.re ×ℂ Icc a.im b.im ⊆ V) (hP : IsOpen P)
    (hW : splitAt i ⁻¹' (V ×ˢ P) ⊆ W) (f : OkaRing W) (S : Finset RectSide)
    (U₁ U₂ : Opens (ι → ℂ))
    (hU₁ : (U₁ : Set (ι → ℂ)) ⊆ splitAt i ⁻¹' ((⋃ s ∈ S, RectSide.set a b s)ᶜ ×ˢ P))
    (hU₂ : (U₂ : Set (ι → ℂ)) ⊆ splitAt i ⁻¹' ((⋃ s ∈ Sᶜ, RectSide.set a b s)ᶜ ×ˢ P)) :
    ∃ (f₁ : OkaRing U₁) (f₂ : OkaRing U₂),
      (∀ (U : Opens (ι → ℂ)) (h₀ : U ≤ W) (h₁ : U ≤ U₁) (h₂ : U ≤ U₂),
        (U : Set (ι → ℂ)) ⊆ splitAt i ⁻¹' ((Ioo a.re b.re ×ℂ Ioo a.im b.im) ×ˢ P) →
          OkaRing.restrict h₀ f = OkaRing.restrict h₁ f₁ + OkaRing.restrict h₂ f₂) ∧
      (∀ (U : Opens (ι → ℂ)) (h₁ : U ≤ U₁) (h₂ : U ≤ U₂),
        (U : Set (ι → ℂ)) ⊆ splitAt i ⁻¹' ((Icc a.re b.re ×ℂ Icc a.im b.im)ᶜ ×ˢ P) →
          OkaRing.restrict h₁ f₁ + OkaRing.restrict h₂ f₂ = 0) := by
  have hF := differentiableOn_comp_symm i hW f
  refine ⟨ofDifferentiableOn _ ((differentiableOn_sum_cauchySide i hre.le him.le hab hP hW f
    S).mono hU₁), ofDifferentiableOn _ ((differentiableOn_sum_cauchySide i hre.le him.le hab hP
    hW f Sᶜ).mono hU₂), fun U h₀ h₁ h₂ hU ↦ ?_, fun U h₁ h₂ hU ↦ ?_⟩
  · ext y
    have hy := hU y.2
    have h := RectSide.sum_add_sum_compl_of_mem hab hF S hy.1 hy.2
    simp only [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply] at h
    change f.toFun _ _ = (∑ s ∈ S, cauchySide i a b f s y) + ∑ s ∈ Sᶜ, cauchySide i a b f s y
    rw [← f.toGlobalFun_apply (h₀ y.2)]
    exact h.symm
  · ext y
    have hy := hU y.2
    exact RectSide.sum_add_sum_compl_of_notMem hab hF hre.le him.le S hy.1 hy.2

end OkaRing

end
