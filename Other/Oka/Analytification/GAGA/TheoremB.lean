/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.CompactlyZero
public import Other.Oka.Analytification.GAGA.CousinCoordinate
public import Other.Oka.Analytification.GAGA.ProjectiveSpaceAnAcyclic

/-!
# Theorem B for the structure sheaf on `(ℂ^×)^P × ℂ^{ι \ P}`, and on the charts of `ℙⁿ_an`

Let `𝒪` be the structure sheaf of `ℂ^ι` (`complexSpace ι`), regarded as an abelian sheaf
(`AlgebraicGeometry.LocallyRingedSpace.structureSheafAb`); its sections over `U` are the elements
of `OkaRing U`. It satisfies the analytic hypotheses of `Oka.Analytification.GAGA.CompactlyZero`:
Cousin splittings of holomorphic functions are splittings of sections (a tautology), and
`lim¹ 𝒪 = 0` along the standard exhaustion of `D = (ℂ^×)^P × ℂ^{ι \ P}`
(`Complex.exists_mittagLeffler_exhaustion`). Hence `Hᵠ(D, 𝒪) = 0` for `q ≥ 1`.

Transported along the charts of `ℙⁿ_an` (`Oka.Analytification.GAGA.ProjectiveSpaceAnAcyclic`),
this gives the acyclicity of `𝒪_{ℙⁿ_an}` on all finite intersections of the standard charts,
i.e. on `π⁻¹(U_I)` for `I` nonempty, and `Hᵠ(ℙⁿ_an, 𝒪) = 0` for `q > n`.

## Main results

- `Complex.TheoremB.cousinSplitting_structureSheafAb`,
  `Complex.TheoremB.mittagLefflerExhaustion_structureSheafAb`: the analytic hypotheses for `𝒪`.
- `Complex.TheoremB.H'_structureSheafAb_eq_zero`,
  `Complex.TheoremB.subsingleton_H_restrictOpen_structureSheafAb`: **Theorem B** on
  `(ℂ^×)^P × ℂ^{ι \ P}`, for Mathlib's cohomology of opens and for the cohomology of the
  restricted sheaf.
- `ComplexAnalytic.projectiveSpaceAn.subsingleton_H_restrictOpen_opensUI`: `Hᵠ(π⁻¹(U_I), 𝒪) = 0`
  for `q ≥ 1` and `I` nonempty; `subsingleton_H_restrictOpen_iInf_chartOpens` (the same for the
  intersection of the chart images), and
  `ComplexAnalytic.projectiveSpaceAn.subsingleton_H_structureSheafAb_of_lt`:
  `Hᵠ(ℙⁿ_an, 𝒪) = 0` for `q > n`.
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace Opposite Set AlgebraicGeometry

namespace Complex.TheoremB

open HoledRect

variable {ι : Type u} [Fintype ι]

/-- The structure sheaf of `ℂ^ι` as an abelian sheaf on `TopCat.of (ι → ℂ)`. -/
noncomputable abbrev complexSpaceStructureSheafAb (ι : Type u) [Fintype ι] :
    TopCat.AbSheaf (TopCat.of (ι → ℂ)) :=
  (complexSpace ι).structureSheafAb

/-- Sections of the structure sheaf split along Cousin splittings of holomorphic functions. -/
theorem cousinSplitting_structureSheafAb : CousinSplitting (complexSpaceStructureSheafAb ι) := by
  intro V A B h hsplit s
  obtain ⟨fA, fB, hfA, hfB, hf⟩ :=
    hsplit _ (OkaRing.differentiableOn_toGlobalFun (U := V) (s : OkaRing V))
  refine ⟨(OkaRing.ofDifferentiableOn fA hfA : OkaRing A),
    (OkaRing.ofDifferentiableOn (-fB) hfB.neg : OkaRing B), ?_⟩
  change OkaRing.restrict h (s : OkaRing V) =
    OkaRing.restrict inf_le_left (OkaRing.ofDifferentiableOn fA hfA) -
      OkaRing.restrict inf_le_right (OkaRing.ofDifferentiableOn (-fB) hfB.neg)
  refine OkaRing.ext (funext fun x ↦ ?_)
  have hx := hf x.1 x.2
  rw [OkaRing.toGlobalFun_apply _ (h x.2)] at hx
  change (s : OkaRing V).toFun _ ⟨x.1, h x.2⟩ = fA x.1 - -fB x.1
  rw [hx, sub_neg_eq_add]

/-- `lim¹ 𝒪 = 0` along the standard exhaustion of `(ℂ^×)^P × ℂ^{ι \ P}`. -/
theorem mittagLefflerExhaustion_structureSheafAb [DecidableEq ι] :
    MittagLefflerExhaustion (complexSpaceStructureSheafAb ι) := by
  intro P U hU hUP s
  have hs : ∀ n, DifferentiableOn ℂ ((s n : OkaRing (U n)).toGlobalFun _)
      (prod (exhaustion P n)) := fun n ↦ by
    rw [← hUP n]
    exact OkaRing.differentiableOn_toGlobalFun _
  obtain ⟨f, hf, hfs⟩ := exists_mittagLeffler_exhaustion P _ hs
  have hf' : ∀ n, DifferentiableOn ℂ (f n) (U n) := fun n ↦ by
    rw [hUP n]
    exact hf n
  refine ⟨fun n ↦ (OkaRing.ofDifferentiableOn (f n) (hf' n) : OkaRing (U n)), fun n ↦ ?_⟩
  change (s n : OkaRing (U n)) = OkaRing.ofDifferentiableOn (f n) (hf' n) -
    OkaRing.restrict (hU n.le_succ) (OkaRing.ofDifferentiableOn (f (n + 1)) (hf' (n + 1)))
  refine OkaRing.ext (funext fun x ↦ ?_)
  have hx := hfs n x.1 (by rw [← hUP n]; exact x.2)
  rw [OkaRing.toGlobalFun_apply _ x.2] at hx
  exact hx

/-- **Theorem B on `(ℂ^×)^P × ℂ^{ι \ P}`**, for Mathlib's cohomology of opens: every class of
positive degree of the structure sheaf on `D = (ℂ^×)^P × ℂ^{ι \ P}` vanishes. -/
theorem H'_structureSheafAb_eq_zero (P : Set ι) {D : Opens (TopCat.of (ι → ℂ))}
    (hD : (D : Set (ι → ℂ)) = puncturedSet P) {q : ℕ}
    (c : CategoryTheory.Sheaf.H'.{u} (complexSpaceStructureSheafAb ι) (q + 1) D) : c = 0 := by
  classical
  refine eq_zero_of_eq_puncturedSet cousinSplitting_structureSheafAb
    mittagLefflerExhaustion_structureSheafAb (Set.toFinite P).toFinset ?_ c
  rw [hD, Set.Finite.coe_toFinset]

/-- **Theorem B on `(ℂ^×)^P × ℂ^{ι \ P}`**: `Hᵠ(D, 𝒪|_D) = 0` for `q ≥ 1`. -/
theorem subsingleton_H_restrictOpen_structureSheafAb (P : Set ι)
    {D : Opens (TopCat.of (ι → ℂ))} (hD : (D : Set (ι → ℂ)) = puncturedSet P) {q : ℕ}
    (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H
      ((TopCat.Sheaf.restrictOpen D).obj (complexSpaceStructureSheafAb ι)) q) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_lt hq
  rw [zero_add]
  have : Subsingleton (CategoryTheory.Sheaf.H'.{u} (complexSpaceStructureSheafAb ι) (q + 1) D) :=
    subsingleton_of_forall_eq 0 (H'_structureSheafAb_eq_zero P hD)
  exact (TopCat.Sheaf.H'AddEquiv D _ (q + 1)).symm.toEquiv.subsingleton

end Complex.TheoremB

namespace ComplexAnalytic.projectiveSpaceAn

variable {n : ℕ}

/-- **Theorem B on the chart intersections of `ℙⁿ_an`**: `Hᵠ(π⁻¹(U_I), 𝒪_{ℙⁿ_an}) = 0` for
`q ≥ 1` and `I` nonempty. -/
theorem subsingleton_H_restrictOpen_opensUI {I : Finset (Fin (n + 1))} (hI : I.Nonempty) (q : ℕ)
    (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (opensUI.{u} I)).obj
      (projectiveSpaceAn.{u} n).toLocallyRingedSpace.structureSheafAb) q) :=
  subsingleton_H_opensUI (fun P _ hq ↦
    Complex.TheoremB.subsingleton_H_restrictOpen_structureSheafAb P (D := puncturedOpens P) rfl
      hq) hI q hq

/-- **Theorem B on the intersections of the chart images of `ℙⁿ_an`**:
`Hᵠ(⋂_{i ∈ I} U i, 𝒪_{ℙⁿ_an}) = 0` for `q ≥ 1` and `I` nonempty. -/
theorem subsingleton_H_restrictOpen_iInf_chartOpens (I : Finset (Fin (n + 1))) (hI : I.Nonempty)
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (⨅ i ∈ I, chartOpens.{u} i)).obj
      (projectiveSpaceAn.{u} n).toLocallyRingedSpace.structureSheafAb) q) :=
  subsingleton_H_iInf_chartOpens (fun P _ hq ↦
    Complex.TheoremB.subsingleton_H_restrictOpen_structureSheafAb P (D := puncturedOpens P) rfl
      hq) I hI q hq

/-- `Hᵠ(ℙⁿ_an, 𝒪) = 0` for `q > n`. -/
theorem subsingleton_H_structureSheafAb_of_lt (q : ℕ) (hq : n < q) :
    Subsingleton (TopCat.Sheaf.H
      (projectiveSpaceAn.{u} n).toLocallyRingedSpace.structureSheafAb q) :=
  subsingleton_H_structureSheafAb (fun P _ hq ↦
    Complex.TheoremB.subsingleton_H_restrictOpen_structureSheafAb P (D := puncturedOpens P) rfl
      hq) q hq

end ComplexAnalytic.projectiveSpaceAn

end
