import KirovDolbeault.LineIntegral
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Covering.Basic
import KirovDolbeault.Discharge.Manifold.CriticalValuesFiniteGeneral
import KirovDolbeault.Discharge.Manifold.RegularValueExistsRegUnconditional
import KirovDolbeault.ManifoldIFT
import KirovDolbeault.SmoothPath
import KirovDolbeault.SmoothPathCore
import KirovDolbeault.CutSurfaceRelations
import KirovDolbeault.ZLatticeQuotient
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Period lattice of a compact Riemann surface

Real (non-placeholder) period lattice of `HolomorphicOneForms X`.
Defined as the ℤ-span of the image of smooth closed loops under the
period pairing.

## Structure

* `periodBasisForm X i` — the i-th basis element of
  `HolomorphicOneForms X` (via `ambientIso X`), used for the period
  pairing. Aligning with `ambientIso` makes the matrix identities
  for `ambientPhi` / `ambientPsi` clean.
* `periodVec γ` — period vector of a path `γ`.
* `closedLoopPeriods X` — image of the period pairing over smooth
  closed loops.
* `truePeriodLattice X` — the ℤ-span.
* `periodVec_pushforward` — the change-of-variables identity
  `periodVec Y (f ∘ γ) = ambientPhi f hf (periodVec X γ)`, from
  which `ambientPhi` preservation of the period lattice follows.
* `DiscreteTopology`/`IsZLattice ℝ` of `truePeriodLattice X` — both instances below are now
  *derived* (not assumed) from `exists_periodLattice_realBasis`: the lattice is the ℤ-span of an
  ℝ-basis, hence discrete (`ZSpan.instDiscreteTopology`) and a full-rank ℤ-lattice
  (`instIsZLatticeRealSpan`). `exists_periodLattice_realBasis` itself is proven (`Dissection.lean`)
  modulo the single isolated input `exists_canonicalDissection` (surface topology + the two Riemann
  bilinear relations); its analytic core `periodVec_linearIndependent` is axiom-clean. So every
  `Jacobian`-as-torus consequence now rests on that one isolated input, not on these instances
  directly.

## References

Forster §§20–21; Miranda Ch. V §§1–3.
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Bundle Topology
open Filter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

-- The foundational smoothPath-independent declarations (`basepoint`,
-- path-connectedness instances, `continuousPath`, `periodBasisForm`,
-- `periodVec`, `IsClosedSmoothLoop`, `closedLoopPeriods`, `IsSmoothPath`
-- + `toClosedSmoothLoop`/`reverse`/`isSmoothPath_const`, and
-- `IsClosedSmoothLoop.reverse`) have moved UPSTREAM to
-- `Jacobians/SmoothPathCore.lean`, so the chart-ball-hop machinery there
-- can be constructed without depending on this file. They remain in the
-- `Jacobians` namespace and are available here via `import
-- Jacobians.SmoothPathCore`.

-- The smoothPath definition and its properties have moved below
-- `periodVec_mem_truePeriodLattice_of_closed`, where they can all
-- be derived from a single consolidated existence theorem
-- (`exists_smoothPath_family`). The previous chart-cover-piecewise
-- scaffolding (`Jacobians.smoothPathRaw`) remains in
-- `Jacobians/SmoothPath.lean` for future explicit-construction work
-- to discharge the consolidated existence.

/-- **True period lattice**: ℤ-span of period vectors of closed
loops. -/
noncomputable def truePeriodLattice (X : Type*) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    Submodule ℤ (Fin (kirovGenus X) → ℂ) :=
  Submodule.span ℤ (closedLoopPeriods X)

/-- Any closed-smooth-loop period vector is in the period lattice. -/
theorem periodVec_mem_truePeriodLattice_of_closed (γ : ℝ → X)
    (hγ : IsClosedSmoothLoop γ) :
    periodVec γ ∈ truePeriodLattice X :=
  Submodule.subset_span ⟨γ, hγ, rfl⟩


/-- **Constant-path period vector is zero.** Classical fact: the
tangent of a constant curve is zero, so every integrand is zero. -/
theorem periodVec_const (P : X) : periodVec (fun _ : ℝ => P) = 0 := by
  funext i
  exact lineIntegral_const _ P

/-- **Period vector reverses sign under path reversal.** Classical
fact: `∫_{reverse γ} ω = -∫_γ ω`. Applied componentwise to the basis
forms. The α-independent differentiability hypothesis is inherited
from `lineIntegral_reverse`. -/
theorem periodVec_reverse (γ : ℝ → X)
    (hdiff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ (1 - t))).toFun ∘ γ) (1 - t)) :
    periodVec (reverse γ) = -periodVec γ := by
  funext i
  exact lineIntegral_reverse (periodBasisForm X i) γ hdiff

open MeasureTheory in
/-- **Period vector is additive under path concatenation.** Classical
fact: `∫_{γ ∗ γ'} ω = ∫_γ ω + ∫_{γ'} ω`. Applied componentwise to
basis forms. Hypotheses (integrability per basis form + pointwise
a.e. identities from the `pathSpeed` chain rule on each half) are
per-i quantified versions of `lineIntegral_concat`'s hypotheses. -/
theorem periodVec_concat (γ γ' : ℝ → X)
    (hint_γ : ∀ i : Fin (kirovGenus X), IntervalIntegrable
      (fun u => (periodBasisForm X i).toFun (γ u) (pathSpeed γ u)) volume 0 1)
    (hint_γ' : ∀ i : Fin (kirovGenus X), IntervalIntegrable
      (fun u => (periodBasisForm X i).toFun (γ' u) (pathSpeed γ' u)) volume 0 1)
    (hint_concat_left : ∀ i : Fin (kirovGenus X), IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun ((concat γ γ') t)
        (pathSpeed (concat γ γ') t)) volume 0 (1/2))
    (hint_concat_right : ∀ i : Fin (kirovGenus X), IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun ((concat γ γ') t)
        (pathSpeed (concat γ γ') t)) volume (1/2) 1)
    (h_ae_left : ∀ i : Fin (kirovGenus X), ∀ᵐ t ∂(volume.restrict (Set.uIoc (0 : ℝ) (1/2))),
      (periodBasisForm X i).toFun ((concat γ γ') t) (pathSpeed (concat γ γ') t) =
        (2 : ℂ) * (periodBasisForm X i).toFun (γ (2 * t)) (pathSpeed γ (2 * t)))
    (h_ae_right : ∀ i : Fin (kirovGenus X), ∀ᵐ t ∂(volume.restrict (Set.uIoc ((1 : ℝ)/2) 1)),
      (periodBasisForm X i).toFun ((concat γ γ') t) (pathSpeed (concat γ γ') t) =
        (2 : ℂ) * (periodBasisForm X i).toFun (γ' (2 * t - 1)) (pathSpeed γ' (2 * t - 1))) :
    periodVec (concat γ γ') = periodVec γ + periodVec γ' := by
  funext i
  exact lineIntegral_concat (periodBasisForm X i) γ γ'
    (hint_γ i) (hint_γ' i)
    (hint_concat_left i) (hint_concat_right i)
    (h_ae_left i) (h_ae_right i)

/-- **Closed-loop period is zero in the Jacobian.** Classical fact:
integrating any form along a closed smooth loop gives an element of
the period lattice, which is the zero class in the Jacobian quotient. -/
theorem mk_periodVec_closed_loop_zero (γ : ℝ → X) (hγ : IsClosedSmoothLoop γ) :
    (QuotientAddGroup.mk (periodVec γ) :
      (Fin (kirovGenus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr
    (periodVec_mem_truePeriodLattice_of_closed γ hγ)

/-- **Constant-path Jacobian class is zero.** Corollary of
`periodVec_const`: the quotient class of the zero vector is zero. -/
theorem mk_periodVec_const_zero (P : X) :
    (QuotientAddGroup.mk (periodVec (fun _ : ℝ => P)) :
      (Fin (kirovGenus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) = 0 := by
  rw [periodVec_const]
  exact QuotientAddGroup.mk_zero _

/-- **Abel-Jacobi additivity under concatenation.** Classical fact:
concatenating a path `P → Q` with a path `Q → R` corresponds to
adding their Jacobian-valued classes. Takes the same per-basis-form
hypotheses as `periodVec_concat`. -/
theorem mk_periodVec_concat_eq_add
    (γ γ' : ℝ → X) (hperiod : periodVec (concat γ γ') = periodVec γ + periodVec γ') :
    (QuotientAddGroup.mk (periodVec (concat γ γ')) :
      (Fin (kirovGenus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) =
      QuotientAddGroup.mk (periodVec γ) + QuotientAddGroup.mk (periodVec γ') := by
  rw [hperiod]
  rfl

/-! ### Abel–Jacobi well-definedness (classical, Abel 1826)

Two paths with the same endpoints yield period vectors that differ
by a period-lattice element. The classical proof uses `γ₁` followed
by `reverse γ₂` to form a closed loop; its period vector is
`periodVec γ₁ - periodVec γ₂`, manifestly in the lattice.

The smoothness content is packed into the `hconcat` hypothesis:
`periodVec (concat γ₁ (reverse γ₂)) = periodVec γ₁ - periodVec γ₂`.
This single equation encodes the output of Phase 1 reversal and
concatenation identities (which individually carry differentiability /
integrability hypotheses). Downstream callers who have smooth γ can
derive `hconcat` from Phase 1 lemmas; callers working abstractly can
just pass it in. -/

/-- **Abel–Jacobi well-definedness (lattice form).** If two smooth
paths share endpoints, their period vectors differ by a lattice
element. The concatenation `γ₁ ∗ reverse γ₂` must itself be a closed
smooth loop (passed in as `hsmooth`). -/
theorem periodVec_sub_mem_truePeriodLattice
    (γ₁ γ₂ : ℝ → X) (_h0 : γ₁ 0 = γ₂ 0)
    (hsmooth : IsClosedSmoothLoop (concat γ₁ (reverse γ₂)))
    (hconcat : periodVec (concat γ₁ (reverse γ₂)) =
      periodVec γ₁ - periodVec γ₂) :
    periodVec γ₁ - periodVec γ₂ ∈ truePeriodLattice X := by
  rw [← hconcat]
  exact periodVec_mem_truePeriodLattice_of_closed _ hsmooth

/-- **Abel–Jacobi well-definedness (quotient form).** Two smooth
paths sharing both endpoints map to the same element of
`(Fin (kirovGenus X) → ℂ) ⧸ truePeriodLattice X`. -/
theorem mk_periodVec_eq_of_endpoints
    (γ₁ γ₂ : ℝ → X) (h0 : γ₁ 0 = γ₂ 0)
    (hsmooth : IsClosedSmoothLoop (concat γ₁ (reverse γ₂)))
    (hconcat : periodVec (concat γ₁ (reverse γ₂)) =
      periodVec γ₁ - periodVec γ₂) :
    (QuotientAddGroup.mk (periodVec γ₁) :
      (Fin (kirovGenus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) =
      QuotientAddGroup.mk (periodVec γ₂) := by
  rw [QuotientAddGroup.eq]
  have h := periodVec_sub_mem_truePeriodLattice γ₁ γ₂ h0 hsmooth hconcat
  have : -periodVec γ₁ + periodVec γ₂ = -(periodVec γ₁ - periodVec γ₂) := by ring
  rw [this]
  exact (truePeriodLattice X).neg_mem h

/-- **Period vector is additive under concatenation of two smooth paths.**
Packages the 6 hypotheses of `periodVec_concat` for smooth paths sharing an
endpoint (no zero-velocity needed — additivity holds for any smooth paths). -/
theorem periodVec_concat_of_smooth {P Q R : X} {g₁ g₂ : ℝ → X}
    (h₁ : IsSmoothPath P Q g₁) (h₂ : IsSmoothPath Q R g₂) :
    periodVec (Jacobians.concat g₁ g₂) = periodVec g₁ + periodVec g₂ := by
  have h_ae_neq : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), t ≠ (1/2 : ℝ) := by
    rw [MeasureTheory.ae_iff]; simp
  refine periodVec_concat g₁ g₂ (fun i => h₁.integrable i) (fun i => h₂.integrable i) ?_ ?_ ?_ ?_
  · intro i
    have h_Ψ₁_shift : IntervalIntegrable
        (fun t => (periodBasisForm X i).toFun (g₁ (2 * t)) (pathSpeed g₁ (2 * t)))
        MeasureTheory.volume 0 (1/2) := by
      have h_mul := (h₁.integrable i).comp_mul_left (c := 2)
      convert h_mul using 2; norm_num
    refine (h_Ψ₁_shift.const_mul (2:ℂ)).congr_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [h_ae_neq] with t h_neq ht
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at ht
    have h_lt : t < 1/2 := lt_of_le_of_ne ht.2 h_neq
    have h_2t_uIcc : 2 * t ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨by linarith [ht.1], by linarith⟩
    have h_ca : Jacobians.concat g₁ g₂ t = g₁ (2 * t) :=
      Jacobians.concat_apply_left _ _ (le_of_lt h_lt)
    have h_ps : pathSpeed (Jacobians.concat g₁ g₂) t = 2 * pathSpeed g₁ (2 * t) :=
      Jacobians.pathSpeed_concat_left _ _ t h_lt (h₁.diff (2 * t) h_2t_uIcc)
    show (2:ℂ) * (periodBasisForm X i).toFun (g₁ (2*t)) (pathSpeed g₁ (2*t)) =
      (periodBasisForm X i).toFun (Jacobians.concat g₁ g₂ t) (pathSpeed (Jacobians.concat g₁ g₂) t)
    rw [h_ca, h_ps]
    have h_lin := ((periodBasisForm X i).toFun (g₁ (2*t))).map_smul (2:ℂ) (pathSpeed g₁ (2*t))
    simp only [smul_eq_mul] at h_lin
    exact h_lin.symm
  · intro i
    have h_Ψ₂_shift : IntervalIntegrable
        (fun t => (periodBasisForm X i).toFun (g₂ (2 * t)) (pathSpeed g₂ (2 * t)))
        MeasureTheory.volume 0 (1/2) := by
      have h_mul := (h₂.integrable i).comp_mul_left (c := 2)
      convert h_mul using 2; norm_num
    have h_Ψ₂_shift_2 : IntervalIntegrable
        (fun t => (periodBasisForm X i).toFun (g₂ (2 * t - 1)) (pathSpeed g₂ (2 * t - 1)))
        MeasureTheory.volume (1/2) 1 := by
      have h_sub := h_Ψ₂_shift.comp_sub_right (1/2)
      rw [show (0:ℝ) + 1/2 = 1/2 from by norm_num, show (1/2:ℝ) + 1/2 = 1 from by norm_num] at h_sub
      have h_fn_eq : (fun t : ℝ => (periodBasisForm X i).toFun (g₂ (2 * (t - 1/2)))
            (pathSpeed g₂ (2 * (t - 1/2)))) =
          (fun t : ℝ => (periodBasisForm X i).toFun (g₂ (2 * t - 1)) (pathSpeed g₂ (2 * t - 1))) := by
        funext t; rw [show (2:ℝ) * (t - 1/2) = 2 * t - 1 from by ring]
      rw [h_fn_eq] at h_sub; exact h_sub
    refine (h_Ψ₂_shift_2.const_mul (2:ℂ)).congr_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [h_ae_neq] with t _h_neq ht
    rw [Set.uIoc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at ht
    have h_gt : 1/2 < t := ht.1
    have h_2tm1_uIcc : 2 * t - 1 ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨by linarith, by linarith [ht.2]⟩
    have h_ca : Jacobians.concat g₁ g₂ t = g₂ (2 * t - 1) :=
      Jacobians.concat_apply_right _ _ (not_le.mpr h_gt)
    have h_ps : pathSpeed (Jacobians.concat g₁ g₂) t = 2 * pathSpeed g₂ (2 * t - 1) :=
      Jacobians.pathSpeed_concat_right _ _ t h_gt (h₂.diff (2 * t - 1) h_2tm1_uIcc)
    show (2:ℂ) * (periodBasisForm X i).toFun (g₂ (2*t-1)) (pathSpeed g₂ (2*t-1)) =
      (periodBasisForm X i).toFun (Jacobians.concat g₁ g₂ t) (pathSpeed (Jacobians.concat g₁ g₂) t)
    rw [h_ca, h_ps]
    have h_lin := ((periodBasisForm X i).toFun (g₂ (2*t-1))).map_smul (2:ℂ) (pathSpeed g₂ (2*t-1))
    simp only [smul_eq_mul] at h_lin
    exact h_lin.symm
  · intro i
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [h_ae_neq] with t h_neq ht
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at ht
    have h_lt : t < 1/2 := lt_of_le_of_ne ht.2 h_neq
    have h_2t_uIcc : 2 * t ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨by linarith [ht.1], by linarith⟩
    have h_ca : Jacobians.concat g₁ g₂ t = g₁ (2 * t) :=
      Jacobians.concat_apply_left _ _ (le_of_lt h_lt)
    have h_ps : pathSpeed (Jacobians.concat g₁ g₂) t = 2 * pathSpeed g₁ (2 * t) :=
      Jacobians.pathSpeed_concat_left _ _ t h_lt (h₁.diff (2 * t) h_2t_uIcc)
    show (periodBasisForm X i).toFun (Jacobians.concat g₁ g₂ t) (pathSpeed (Jacobians.concat g₁ g₂) t) =
      (2:ℂ) * (periodBasisForm X i).toFun (g₁ (2*t)) (pathSpeed g₁ (2*t))
    rw [h_ca, h_ps]
    have h_lin := ((periodBasisForm X i).toFun (g₁ (2*t))).map_smul (2:ℂ) (pathSpeed g₁ (2*t))
    simp only [smul_eq_mul] at h_lin
    exact h_lin
  · intro i
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [h_ae_neq] with t _h_neq ht
    rw [Set.uIoc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at ht
    have h_gt : 1/2 < t := ht.1
    have h_2tm1_uIcc : 2 * t - 1 ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨by linarith, by linarith [ht.2]⟩
    have h_ca : Jacobians.concat g₁ g₂ t = g₂ (2 * t - 1) :=
      Jacobians.concat_apply_right _ _ (not_le.mpr h_gt)
    have h_ps : pathSpeed (Jacobians.concat g₁ g₂) t = 2 * pathSpeed g₂ (2 * t - 1) :=
      Jacobians.pathSpeed_concat_right _ _ t h_gt (h₂.diff (2 * t - 1) h_2tm1_uIcc)
    show (periodBasisForm X i).toFun (Jacobians.concat g₁ g₂ t) (pathSpeed (Jacobians.concat g₁ g₂) t) =
      (2:ℂ) * (periodBasisForm X i).toFun (g₂ (2*t-1)) (pathSpeed g₂ (2*t-1))
    rw [h_ca, h_ps]
    have h_lin := ((periodBasisForm X i).toFun (g₂ (2*t-1))).map_smul (2:ℂ) (pathSpeed g₂ (2*t-1))
    simp only [smul_eq_mul] at h_lin
    exact h_lin

/-- Membership helper: `t ∈ [0,1] → 1 - t ∈ [0,1]`. -/
private lemma one_sub_mem_uIcc {t : ℝ} (ht : t ∈ Set.uIcc (0:ℝ) 1) :
    (1:ℝ) - t ∈ Set.uIcc (0:ℝ) 1 := by
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht ⊢
  exact ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩

/-! ## Consolidated existence of a smooth-path family

The classical theorem (Forster §§1–2, 21): on a compact connected Riemann
surface there is a family of smooth paths between every pair of points with
(1) `IsSmoothPath P Q (sp P Q)` and (2) the basepoint-change cocycle
`[sp(P₀,A)] = [sp(P,A)] + [sp(P₀,P)]` mod the period lattice.

As of 2026-05-29 this is **no longer a single monolithic unproved obligation**: it is
reduced (`exists_smoothPath_family`, proven below) to the focused kernel
`exists_zeroVel_smoothPath` (existence of a smooth path with zero endpoint
velocity), using `IsSmoothPath.concat`, `periodVec_concat_of_smooth`, and
`mk_periodVec_eq_of_endpoints`. The cocycle holds because the Jacobian class
depends only on endpoints and is additive under concatenation.

The provably-false third conjunct (unquotiented smoothness of
`Q ↦ periodVec (sp P Q)`) was removed 2026-05-28; see the project memory
`project_smoothpath_math_error`. -/
/-- A valid chart-ball hop `Q₀ → Q`: `Q` is in `Q₀`'s chart source and the
affine segment between their chart images stays in the chart target. Exactly
the hypotheses `ChartBallPathSmooth` needs. -/
def HopValid (Q₀ Q : X) : Prop :=
  Q ∈ (chartAt (H := ℂ) Q₀).source ∧
  ∀ s ∈ Set.Icc (0 : ℝ) 1,
    ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
      (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target

/-- A valid hop yields a smooth path with zero velocity at both endpoints
(`ChartBallPathSmooth` is smoothstep-reparametrized). -/
theorem zeroVelHop {Q₀ Q : X} (h : HopValid Q₀ Q) :
    IsSmoothPath Q₀ Q (ChartBallPathSmooth Q₀ Q) ∧
    pathSpeed (ChartBallPathSmooth Q₀ Q) 0 = 0 ∧
    pathSpeed (ChartBallPathSmooth Q₀ Q) 1 = 0 := by
  obtain ⟨hsrc, haff⟩ := h
  refine ⟨OfCurveSkeleton.isSmoothPath_ChartBallPathSmooth Q₀ Q hsrc haff, ?_, ?_⟩
  · show pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q ∘ smoothStep01) 0 = 0
    rw [OfCurveSkeleton.pathSpeed_smoothStep01_comp_eq (Jacobians.ChartBallPath Q₀ Q₀ Q) 0
        (Jacobians.ChartBallPath_chart_at_self_differentiableAt Q₀ Q₀ Q (smoothStep01 0)
          (haff (smoothStep01 0) (Jacobians.smoothStep01_mem_unit 0))),
      smoothStep01_deriv_zero, Complex.ofReal_zero, zero_mul]
  · show pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q ∘ smoothStep01) 1 = 0
    rw [OfCurveSkeleton.pathSpeed_smoothStep01_comp_eq (Jacobians.ChartBallPath Q₀ Q₀ Q) 1
        (Jacobians.ChartBallPath_chart_at_self_differentiableAt Q₀ Q₀ Q (smoothStep01 1)
          (haff (smoothStep01 1) (Jacobians.smoothStep01_mem_unit 1))),
      smoothStep01_deriv_one, Complex.ofReal_zero, zero_mul]

/-- Generic neighborhood cover of a path: given an open-neighborhood assignment
`W y ∋ y`, a continuous `γ` is covered segment-by-segment, each segment landing
in some `W (x k)`. (Generalizes `exists_chartCover` from chart sources to `W`.) -/
theorem exists_nbhd_cover (γ : ℝ → X) (hγ : Continuous γ)
    (W : X → Set X) (hW_open : ∀ y, IsOpen (W y)) (hW_mem : ∀ y, y ∈ W y) :
    ∃ (n : ℕ) (_hn : 0 < n) (x : Fin n → X),
      ∀ (k : Fin n) (s : ℝ),
        (k : ℝ) / n ≤ s → s ≤ ((k : ℝ) + 1) / n → γ s ∈ W (x k) := by
  set scc : Set ℝ := Set.Icc (0 : ℝ) 1 with hs_def
  set U : scc → Set ℝ := fun t => γ ⁻¹' W (γ t.1) with hU_def
  have hU_open : ∀ t : scc, IsOpen (U t) := fun t => (hW_open (γ t.1)).preimage hγ
  have hU_cover : scc ⊆ ⋃ t : scc, U t := by
    intro t ht
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hW_mem (γ t)⟩
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    lebesgue_number_lemma_of_metric isCompact_Icc hU_open hU_cover
  obtain ⟨n, hn_gt⟩ : ∃ n : ℕ, 1 / δ < (n : ℝ) := exists_nat_gt _
  have hn_pos : 0 < n := by
    have h1 : (0 : ℝ) < 1 / δ := by positivity
    exact_mod_cast lt_trans h1 hn_gt
  have key : ∀ k : Fin n, ∃ x : X, ∀ y : ℝ,
      (k : ℝ) / n ≤ y → y ≤ ((k : ℝ) + 1) / n → γ y ∈ W x := by
    intro k
    set m : ℝ := ((k : ℝ) + 1/2) / n with hm_def
    have hm_mem : m ∈ scc := by
      refine ⟨?_, ?_⟩
      · apply div_nonneg
        · have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
          linarith
        · exact Nat.cast_nonneg _
      · rw [hm_def, div_le_one (by exact_mod_cast hn_pos)]
        have hk : (k : ℝ) + 1 ≤ n := by
          have : (k.val + 1 : ℕ) ≤ n := k.isLt
          exact_mod_cast this
        linarith
    obtain ⟨t₀, ht₀⟩ := hδ m hm_mem
    refine ⟨γ t₀.1, fun y hy_low hy_high => ?_⟩
    apply ht₀
    show y ∈ Metric.ball m δ
    rw [Metric.mem_ball, Real.dist_eq]
    have hn : (1 : ℝ) / n < δ := by
      have hn_R : (0 : ℝ) < n := by exact_mod_cast hn_pos
      rw [div_lt_iff₀ hn_R]
      have h := mul_lt_mul_of_pos_left hn_gt hδ_pos
      have h_simp : δ * (1 / δ) = 1 := by field_simp
      linarith
    have h_dist : |y - m| ≤ 1 / (2 * n) := by
      rw [abs_sub_le_iff]
      refine ⟨?_, ?_⟩
      · have : y - m ≤ ((k : ℝ) + 1) / n - ((k : ℝ) + 1/2) / n := by linarith
        have heq : ((k : ℝ) + 1) / n - ((k : ℝ) + 1/2) / n = 1 / (2 * n) := by
          field_simp; ring
        linarith
      · have : m - y ≤ ((k : ℝ) + 1/2) / n - (k : ℝ) / n := by linarith
        have heq : ((k : ℝ) + 1/2) / n - (k : ℝ) / n = 1 / (2 * n) := by
          field_simp; ring
        linarith
    have h1 : (1 : ℝ) / (2 * n) ≤ 1 / n := by
      apply div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hn_pos)
      have hnn : (0 : ℝ) < n := by exact_mod_cast hn_pos
      nlinarith
    linarith
  classical
  exact ⟨n, hn_pos, fun k => (key k).choose,
    fun k y h1 h2 => (key k).choose_spec y h1 h2⟩

/-- Common-anchor segment: if a point `w` validly hops to both `u` and `v`,
then there is a zero-endpoint-velocity smooth path `u → v` (go `u → w` via the
reversed hop, then `w → v` via the forward hop). -/
theorem exists_zeroVelPath_of_common_anchor {w u v : X}
    (hu : HopValid w u) (hv : HopValid w v) :
    ∃ γ, IsSmoothPath u v γ ∧ pathSpeed γ 0 = 0 ∧ pathSpeed γ 1 = 0 := by
  obtain ⟨hu_sm, hu_v0, hu_v1⟩ := zeroVelHop hu
  obtain ⟨hv_sm, hv_v0, hv_v1⟩ := zeroVelHop hv
  have h0uIcc : (0:ℝ) ∈ Set.uIcc (0:ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨le_refl _, zero_le_one⟩
  have h1uIcc : (1:ℝ) ∈ Set.uIcc (0:ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨zero_le_one, le_refl _⟩
  -- reversed hop u → w, zero velocity at both ends
  have hrev_sm : IsSmoothPath u w (Jacobians.reverse (ChartBallPathSmooth w u)) := hu_sm.reverse
  have hrev_v0 : pathSpeed (Jacobians.reverse (ChartBallPathSmooth w u)) 0 = 0 := by
    rw [Jacobians.pathSpeed_reverse _ 0
        (by rw [show (1:ℝ)-0 = 1 from by norm_num]; exact hu_sm.diff 1 h1uIcc),
      show (1:ℝ)-0 = 1 from by norm_num, hu_v1, neg_zero]
  have hrev_v1 : pathSpeed (Jacobians.reverse (ChartBallPathSmooth w u)) 1 = 0 := by
    rw [Jacobians.pathSpeed_reverse _ 1
        (by rw [show (1:ℝ)-1 = 0 from by norm_num]; exact hu_sm.diff 0 h0uIcc),
      show (1:ℝ)-1 = 0 from by norm_num, hu_v0, neg_zero]
  refine ⟨Jacobians.concat (Jacobians.reverse (ChartBallPathSmooth w u)) (ChartBallPathSmooth w v),
    hrev_sm.concat hv_sm hrev_v1 hv_v0, ?_, ?_⟩
  · have hd : DifferentiableAt ℝ
        ((chartAt (H := ℂ) (Jacobians.reverse (ChartBallPathSmooth w u) (2 * 0))).toFun ∘
          Jacobians.reverse (ChartBallPathSmooth w u)) (2 * 0) := by
      rw [show (2:ℝ)*0 = 0 from by norm_num]; exact hrev_sm.diff 0 h0uIcc
    rw [Jacobians.pathSpeed_concat_left _ _ 0 (by norm_num) hd,
      show (2:ℝ)*0 = 0 from by norm_num, hrev_v0, mul_zero]
  · have hd : DifferentiableAt ℝ
        ((chartAt (H := ℂ) (ChartBallPathSmooth w v (2 * 1 - 1))).toFun ∘
          ChartBallPathSmooth w v) (2 * 1 - 1) := by
      rw [show (2:ℝ)*1-1 = 1 from by norm_num]; exact hv_sm.diff 1 h1uIcc
    rw [Jacobians.pathSpeed_concat_right _ (ChartBallPathSmooth w v) 1 (by norm_num) hd,
      show (2:ℝ)*1-1 = 1 from by norm_num, hv_v1, mul_zero]

/-- The `HopValid`-validity neighborhood of `y` (open, contains `y`). -/
def hopNbhd (y : X) : Set X := interior {Q | HopValid y Q}

theorem isOpen_hopNbhd (y : X) : IsOpen (hopNbhd y) := isOpen_interior

theorem self_mem_hopNbhd (y : X) : y ∈ hopNbhd y := by
  rw [hopNbhd, mem_interior_iff_mem_nhds]
  exact (OfCurveSkeleton.Q_in_chart_source_eventually y).and
    (OfCurveSkeleton.affine_in_target_eventually y)

theorem hopValid_of_mem_hopNbhd {y Q : X} (h : Q ∈ hopNbhd y) : HopValid y Q :=
  interior_subset (s := {Q' : X | HopValid y Q'}) h

/-- **Chart-ball cover (S1-B)**: a chain of zero-velocity smooth-path hops from
`P` to `Q`. Lebesgue-number cover of `continuousPath P Q`; each segment's
endpoints are reached from a common Lebesgue anchor via `exists_zeroVelPath_of_common_anchor`. -/
theorem exists_smoothChain (P Q : X) :
    ∃ (n : ℕ) (a : ℕ → X), a 0 = P ∧ a n = Q ∧
      ∀ k, k < n → ∃ γ, IsSmoothPath (a k) (a (k+1)) γ ∧
        pathSpeed γ 0 = 0 ∧ pathSpeed γ 1 = 0 := by
  set c : ℝ → X := fun t => (continuousPath P Q).extend t with hc_def
  have hc_cont : Continuous c := (continuousPath P Q).continuous_extend
  have hc0 : c 0 = P := Path.extend_zero _
  have hc1 : c 1 = Q := Path.extend_one _
  obtain ⟨n, hn_pos, x, hx⟩ :=
    exists_nbhd_cover c hc_cont hopNbhd isOpen_hopNbhd self_mem_hopNbhd
  refine ⟨n, fun j => c ((j : ℝ) / n), ?_, ?_, ?_⟩
  · show c (((0 : ℕ) : ℝ) / (n : ℝ)) = P
    rw [Nat.cast_zero, zero_div]; exact hc0
  · show c (((n : ℕ) : ℝ) / (n : ℝ)) = Q
    rw [div_self (by exact_mod_cast hn_pos.ne' : (n : ℝ) ≠ 0)]; exact hc1
  · intro k hk
    have hkn : (k : ℝ) / n ≤ (k : ℝ) / n := le_refl _
    have hk1n : (k : ℝ) / n ≤ ((k : ℝ) + 1) / n := by
      gcongr
      linarith
    have hkk1 : ((k : ℝ) + 1) / n ≤ ((k : ℝ) + 1) / n := le_refl _
    -- both endpoints land in hopNbhd (x ⟨k,hk⟩)
    have hu : HopValid (x ⟨k, hk⟩) (c ((k : ℝ) / n)) :=
      hopValid_of_mem_hopNbhd (hx ⟨k, hk⟩ ((k : ℝ) / n) hkn hk1n)
    have hv : HopValid (x ⟨k, hk⟩) (c (((k : ℝ) + 1) / n)) :=
      hopValid_of_mem_hopNbhd (hx ⟨k, hk⟩ (((k : ℝ) + 1) / n) hk1n hkk1)
    obtain ⟨γ, hγsm, hγv0, hγv1⟩ := exists_zeroVelPath_of_common_anchor hu hv
    refine ⟨γ, ?_, hγv0, hγv1⟩
    have hcast : ((k : ℝ) + 1) / n = ((k + 1 : ℕ) : ℝ) / n := by push_cast; ring
    rw [hcast] at hγsm
    exact hγsm

/-- **Generalized n-piece glue**: a chain of zero-velocity smooth-path hops
glues to a single zero-velocity smooth path, by induction on the chain length. -/
theorem exists_zeroVel_smoothPath_aux (a : ℕ → X) :
    ∀ n, (∀ k, k < n → ∃ γ, IsSmoothPath (a k) (a (k+1)) γ ∧
          pathSpeed γ 0 = 0 ∧ pathSpeed γ 1 = 0) →
      ∃ γ, IsSmoothPath (a 0) (a n) γ ∧ pathSpeed γ 0 = 0 ∧ pathSpeed γ 1 = 0 := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨fun _ => a 0, isSmoothPath_const (a 0),
      by rw [pathSpeed_const], by rw [pathSpeed_const]⟩
  | succ m ih =>
    intro hstep
    obtain ⟨γ, hγsm, hγv0, hγv1⟩ := ih (fun k hk => hstep k (by omega))
    obtain ⟨g, hgsm, hgv0, hgv1⟩ := hstep m (by omega)
    have h0uIcc : (0:ℝ) ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨le_refl _, zero_le_one⟩
    have h1uIcc : (1:ℝ) ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨zero_le_one, le_refl _⟩
    refine ⟨Jacobians.concat γ g, hγsm.concat hgsm hγv1 hgv0, ?_, ?_⟩
    · have hd : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ (2 * 0))).toFun ∘ γ) (2 * 0) := by
        rw [show (2:ℝ)*0 = 0 from by norm_num]; exact hγsm.diff 0 h0uIcc
      rw [Jacobians.pathSpeed_concat_left γ g 0 (by norm_num) hd,
        show (2:ℝ)*0 = 0 from by norm_num, hγv0, mul_zero]
    · have hd : DifferentiableAt ℝ ((chartAt (H := ℂ) (g (2 * 1 - 1))).toFun ∘ g) (2 * 1 - 1) := by
        rw [show (2:ℝ)*1-1 = 1 from by norm_num]; exact hgsm.diff 1 h1uIcc
      rw [Jacobians.pathSpeed_concat_right γ g 1 (by norm_num) hd,
        show (2:ℝ)*1-1 = 1 from by norm_num, hgv1, mul_zero]

/-- **S1 kernel, fully proven**: a zero-endpoint-velocity smooth path exists
between any two points (chart-ball cover glued by the n-piece induction). -/
theorem exists_zeroVel_smoothPath (P Q : X) :
    ∃ γ, IsSmoothPath P Q γ ∧ pathSpeed γ 0 = 0 ∧ pathSpeed γ 1 = 0 := by
  obtain ⟨n, a, ha0, han, hstep⟩ := exists_smoothChain P Q
  obtain ⟨γ, hsm, hv0, hv1⟩ := exists_zeroVel_smoothPath_aux a n hstep
  exact ⟨γ, ha0 ▸ han ▸ hsm, hv0, hv1⟩

theorem exists_smoothPath_family
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    ∃ sp : X → X → ℝ → X,
      (∀ P Q, IsSmoothPath P Q (sp P Q)) ∧
      (∀ P P₀ A,
        (QuotientAddGroup.mk (periodVec (sp P₀ A)) :
          (Fin (kirovGenus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) =
        QuotientAddGroup.mk (periodVec (sp P A)) +
        QuotientAddGroup.mk (periodVec (sp P₀ P))) := by
  choose sp hS hv0 hv1 using fun P Q => exists_zeroVel_smoothPath (X := X) P Q
  refine ⟨sp, hS, fun P P₀ A => ?_⟩
  have hadd : periodVec (Jacobians.concat (sp P₀ P) (sp P A)) =
      periodVec (sp P₀ P) + periodVec (sp P A) :=
    periodVec_concat_of_smooth (hS P₀ P) (hS P A)
  have hcc : IsSmoothPath P₀ A (Jacobians.concat (sp P₀ P) (sp P A)) :=
    (hS P₀ P).concat (hS P A) (hv1 P₀ P) (hv0 P A)
  have h1uIcc : (1:ℝ) ∈ Set.uIcc (0:ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨zero_le_one, le_refl _⟩
  have hcc_v1 : pathSpeed (Jacobians.concat (sp P₀ P) (sp P A)) 1 = 0 := by
    rw [Jacobians.pathSpeed_concat_right (sp P₀ P) (sp P A) 1 (by norm_num)
        (by rw [show (2:ℝ)*1-1 = 1 from by norm_num]; exact (hS P A).diff 1 h1uIcc),
      show (2:ℝ)*1-1 = 1 from by norm_num, hv1 P A, mul_zero]
  have hrev : IsSmoothPath A P₀ (Jacobians.reverse (Jacobians.concat (sp P₀ P) (sp P A))) :=
    hcc.reverse
  have hrev_v0 : pathSpeed (Jacobians.reverse (Jacobians.concat (sp P₀ P) (sp P A))) 0 = 0 := by
    rw [Jacobians.pathSpeed_reverse _ 0
        (by rw [show (1:ℝ)-0 = 1 from by norm_num]; exact hcc.diff 1 h1uIcc),
      show (1:ℝ)-0 = 1 from by norm_num, hcc_v1, neg_zero]
  have hloop : IsClosedSmoothLoop
      (Jacobians.concat (sp P₀ A) (Jacobians.reverse (Jacobians.concat (sp P₀ P) (sp P A)))) :=
    ((hS P₀ A).concat hrev (hv1 P₀ A) hrev_v0).toClosedSmoothLoop
  have hrevpv : periodVec (Jacobians.reverse (Jacobians.concat (sp P₀ P) (sp P A))) =
      -periodVec (Jacobians.concat (sp P₀ P) (sp P A)) :=
    Jacobians.periodVec_reverse _ (fun t ht => hcc.diff (1 - t) (one_sub_mem_uIcc ht))
  have hep : (QuotientAddGroup.mk (periodVec (sp P₀ A)) :
        (Fin (kirovGenus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) =
      QuotientAddGroup.mk (periodVec (Jacobians.concat (sp P₀ P) (sp P A))) := by
    refine mk_periodVec_eq_of_endpoints (sp P₀ A) (Jacobians.concat (sp P₀ P) (sp P A))
      ?_ hloop ?_
    · rw [(hS P₀ A).start, Jacobians.concat_apply_left _ _ (by norm_num : (0:ℝ) ≤ 1/2),
          show (2:ℝ)*0 = 0 from by norm_num, (hS P₀ P).start]
    · rw [periodVec_concat_of_smooth (hS P₀ A) hrev, hrevpv]; ring
  rw [hep, mk_periodVec_concat_eq_add (sp P₀ P) (sp P A) hadd, add_comm]

/-- The smooth path between `P` and `Q`, extracted via `Classical.choice`
from `exists_smoothPath_family`. -/
noncomputable def smoothPath (P Q : X) : ℝ → X :=
  (exists_smoothPath_family X).choose P Q

/-- The chosen smooth path satisfies `IsSmoothPath`. -/
theorem isSmoothPath_smoothPath (P Q : X) : IsSmoothPath P Q (smoothPath P Q) :=
  (exists_smoothPath_family X).choose_spec.1 P Q

/-- Boundary value: `smoothPath P Q 0 = P`. -/
@[simp] lemma smoothPath_zero (P Q : X) : smoothPath P Q 0 = P :=
  (isSmoothPath_smoothPath P Q).start

/-- Boundary value: `smoothPath P Q 1 = Q`. -/
@[simp] lemma smoothPath_one (P Q : X) : smoothPath P Q 1 = Q :=
  (isSmoothPath_smoothPath P Q).finish

/-- The `periodVec` of the smooth path from `P` to `P` is in the period
lattice (it's a closed smooth loop). -/
theorem periodVec_smoothPath_self_mem_lattice (P : X) :
    periodVec (smoothPath P P) ∈ truePeriodLattice X :=
  periodVec_mem_truePeriodLattice_of_closed _
    (isSmoothPath_smoothPath P P).toClosedSmoothLoop

/-- **Basepoint change for `smoothPath` modulo the period lattice**
(classical, Forster §21). Extracted from the second conjunct of
`exists_smoothPath_family`. -/
theorem smoothPath_basepoint_change (P P₀ A : X) :
    (QuotientAddGroup.mk (periodVec (smoothPath P₀ A)) :
      (Fin (kirovGenus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) =
    QuotientAddGroup.mk (periodVec (smoothPath P A)) +
    QuotientAddGroup.mk (periodVec (smoothPath P₀ P)) :=
  (exists_smoothPath_family X).choose_spec.2 P P₀ A

/-! ### Phase 4 support: change of variables under smooth maps

For `f : X → Y` smooth and `γ : ℝ → X` a path, the period vector of
the image loop `f ∘ γ` in `Y` is the `ambientPhi`-image of the period
vector of `γ` in `X`. This is the formal expression of "image of a
loop has period given by the pullback matrix" — the analytic content
that forces `ambientPhi` to preserve the lattice. -/

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **Pullback of a `Y`-basis form via `f`, expressed in the `X`
basis coordinates.** Classical linear-algebra identity tying
`pullbackForm` to `ambientPsi`. Pure manipulation of the
`ambientIso`-based definitions; no analytic content. -/
theorem pullbackForm_periodBasisForm_eq (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (j : Fin (kirovGenus Y)) :
    pullbackForm f hf (periodBasisForm Y j) =
      ambientIso X (ambientPsi (gX := kirovGenus X) (gY := kirovGenus Y) f hf
        (Pi.basisFun ℂ (Fin (kirovGenus Y)) j)) := by
  unfold ambientPsi
  set_option linter.unusedSimpArgs false in
  simp only [dif_pos rfl]
  show pullbackForm f hf (periodBasisForm Y j) =
    ambientIso X (((ambientIso X).symm.toLinearMap.comp
      ((pullbackForm f hf).comp (ambientIso Y).toLinearMap) : _ →ₗ[_] _)
        (Pi.basisFun ℂ (Fin (kirovGenus Y)) j))
  simp [periodBasisForm, LinearMap.comp_apply]

/-- **Smooth loops compose with smooth maps.** If `γ : ℝ → X` is a
closed smooth loop and `f : X → Y` is smooth, then `f ∘ γ` is a
closed smooth loop in `Y`. Sub-lemmas:
1. Closedness: from `γ 0 = γ 1`.
2. Continuity: from continuity of `f` and `γ`.
3. Chart-pullback differentiability of `chart_Y ∘ (f ∘ γ)` at `t`:
   via the chart chain rule `f_loc ∘ (chart_X ∘ γ)` (proved inside
   `pathSpeed_comp_eq_mfderiv`).
4. Integrability of each Y-basis form along `f ∘ γ`: via
   `lineIntegral_pullback`, the integrand equals
   `(pullbackForm f hf (periodBasisForm Y j)).toFun (γ t) (pathSpeed γ t)`
   (at least a.e.), which is a ℂ-linear combination of X-basis
   integrands — each integrable by hypothesis.

**Remaining content**: the sub-lemmas 3 and 4 require replaying the
chart chain rule + linear-algebra arguments from elsewhere in the
file. Bounded but ~100 lines. -/
theorem IsClosedSmoothLoop.comp (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    {γ : ℝ → X} (hγ : IsClosedSmoothLoop γ) :
    IsClosedSmoothLoop (f ∘ γ) where
  closed := by simp [Function.comp_apply, hγ.closed]
  cont := hf.continuous.comp hγ.cont
  diff := by
    intro t ht
    -- Near t, (chartAt ℂ (f (γ t))).toFun ∘ (f ∘ γ) = f_loc ∘ (chart_X ∘ γ).
    set φ_X := chartAt (H := ℂ) (γ t)
    set φ_Y := chartAt (H := ℂ) (f (γ t))
    set f_loc : ℂ → ℂ := fun z => φ_Y (f (φ_X.symm z))
    set g_X : ℝ → ℂ := φ_X.toFun ∘ γ
    have hγ_source : ∀ᶠ s in 𝓝 t, γ s ∈ φ_X.source :=
      hγ.cont.continuousAt.eventually
        (φ_X.open_source.mem_nhds (mem_chart_source ℂ (γ t)))
    have h_eq : (φ_Y.toFun ∘ (f ∘ γ)) =ᶠ[𝓝 t] f_loc ∘ g_X := by
      filter_upwards [hγ_source] with s hs
      simp only [Function.comp_apply]
      congr 2
      exact (φ_X.left_inv hs).symm
    have hf_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (γ t) :=
      hf.mdifferentiableAt (by decide : ω ≠ 0)
    have hf_loc_diff_ℂ : DifferentiableAt ℂ f_loc (g_X t) := by
      have h1 := hf_mdiff.differentiableWithinAt_writtenInExtChartAt
      rw [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at h1
      convert h1 using 2
    -- Bypass the ℝ/ℂ diamond: construct ℝ-HasFDerivAt manually.
    have hf_loc_hasFD_ℂ : HasFDerivAt f_loc (fderiv ℂ f_loc (g_X t)) (g_X t) :=
      hf_loc_diff_ℂ.hasFDerivAt
    have hf_loc_hasFD_ℝ : HasFDerivAt f_loc
        ((fderiv ℂ f_loc (g_X t)).restrictScalars ℝ) (g_X t) := by
      rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hf_loc_hasFD_ℂ ⊢
      simp only [ContinuousLinearMap.coe_restrictScalars']
      exact hf_loc_hasFD_ℂ
    have hf_loc_diff_ℝ : DifferentiableAt ℝ f_loc (g_X t) :=
      hf_loc_hasFD_ℝ.differentiableAt
    have h_comp_diff : DifferentiableAt ℝ (f_loc ∘ g_X) t :=
      hf_loc_diff_ℝ.comp t (hγ.diff t ht)
    exact (h_eq.differentiableAt_iff).mpr h_comp_diff
  velCont :=
    velCont_comp f hf γ hγ.cont
      (fun s hs => hγ.diff s (Set.Icc_subset_uIcc hs)) hγ.velCont

/-- Change-of-variables at the vector level: evaluating each Y-basis
form against `f ∘ γ` equals evaluating its pullback against `γ`.
Requires path regularity hypotheses (inherited from `lineIntegral_pullback`). -/
theorem periodVec_comp_eq_lineIntegral_pullback
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (γ : ℝ → X) (j : Fin (kirovGenus Y))
    (hγ_cont : Continuous γ)
    (hγ_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t) :
    periodVec (f ∘ γ) j =
      lineIntegral (pullbackForm f hf (periodBasisForm Y j)) γ := by
  unfold periodVec
  exact lineIntegral_pullback f hf (periodBasisForm Y j) γ hγ_cont hγ_diff

/-- **Key identity**: the period vector of the image loop equals
`ambientPhi` applied to the period vector of the source loop.

With `periodBasisForm Y j = ambientIso Y e_j^Y`, the pullback
`pullbackForm f hf (periodBasisForm Y j)` expanded in the `X`-basis
has coefficients `(ambientPsi f hf e_j^Y) i = M_ij`. Then:

  `(ambientPhi f hf v)_j = ∑_i M_ij v_i`

matches:

  `periodVec Y (f∘γ) j = ∫_γ pullbackForm f hf (basis_j^Y)
                       = ∑_i M_ij (periodVec X γ)_i`.

Uses `lineIntegral_pullback` + linearity of `lineIntegral` via basis
expansion. Requires path regularity (the hypotheses of
`IsClosedSmoothLoop`). -/
theorem periodVec_pushforward
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (γ : ℝ → X)
    (hγ_cont : Continuous γ)
    (hγ_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t)
    (hint_X : ∀ i : Fin (kirovGenus X), IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t))
        MeasureTheory.volume 0 1) :
    periodVec (f ∘ γ) =
      ambientPhi (gX := kirovGenus X) (gY := kirovGenus Y) f hf (periodVec γ) := by
  funext j
  show lineIntegral (periodBasisForm Y j) (f ∘ γ) =
    ambientPhi (gX := kirovGenus X) (gY := kirovGenus Y) f hf (periodVec γ) j
  rw [lineIntegral_pullback f hf _ γ hγ_cont hγ_diff]
  rw [pullbackForm_periodBasisForm_eq]
  -- Goal: lineIntegral (ambientIso X (ambientPsi f hf e_j^Y)) γ = (ambientPhi f hf (periodVec γ)) j
  set v := ambientPsi (gX := kirovGenus X) (gY := kirovGenus Y) f hf
    (Pi.basisFun ℂ (Fin (kirovGenus Y)) j) with hv_def
  -- Step 1: ambientIso X v = ∑ i, v i • periodBasisForm X i
  have h_iso_sum : ambientIso X v = ∑ i, v i • periodBasisForm X i := by
    have h_v_decomp : v = ∑ i, v i • Pi.basisFun ℂ (Fin (kirovGenus X)) i := by
      have := pi_eq_sum_univ' v
      convert this using 2
      simp [Pi.basisFun_apply]
    conv_lhs => rw [h_v_decomp, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
    rfl
  rw [h_iso_sum]
  -- Step 2: lineIntegral distributes over the Finset sum (needs integrability).
  have h_sum_lineIntegral : lineIntegral (∑ i, v i • periodBasisForm X i) γ =
      ∑ i, v i * lineIntegral (periodBasisForm X i) γ := by
    unfold lineIntegral
    have h_pw : ∀ t : ℝ,
        (∑ i, v i • periodBasisForm X i).toFun (γ t) (pathSpeed γ t) =
          ∑ i, v i * (periodBasisForm X i).toFun (γ t) (pathSpeed γ t) := by
      intro t
      -- Unfold toFun on a finset sum of smul'd sections.
      induction (Finset.univ : Finset (Fin (kirovGenus X))) using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        show (0 : HolomorphicOneForms X).toFun (γ t) (pathSpeed γ t) = 0
        rfl
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        show ((v a • periodBasisForm X a) + ∑ i ∈ s, v i • periodBasisForm X i).toFun (γ t)
            (pathSpeed γ t) = _
        rw [show ((v a • periodBasisForm X a) + ∑ i ∈ s, v i • periodBasisForm X i).toFun (γ t) =
            (v a • periodBasisForm X a).toFun (γ t) +
              (∑ i ∈ s, v i • periodBasisForm X i).toFun (γ t) from rfl,
          ContinuousLinearMap.add_apply, ih]
        show v a * (periodBasisForm X a).toFun (γ t) (pathSpeed γ t) +
            ∑ i ∈ s, v i * (periodBasisForm X i).toFun (γ t) (pathSpeed γ t) =
          v a * (periodBasisForm X a).toFun (γ t) (pathSpeed γ t) +
            ∑ i ∈ s, v i * (periodBasisForm X i).toFun (γ t) (pathSpeed γ t)
        rfl
    simp_rw [h_pw]
    rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
      (f := fun i t => v i * (periodBasisForm X i).toFun (γ t) (pathSpeed γ t))
      (fun i _ => (hint_X i).const_mul (v i))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact intervalIntegral.integral_const_mul _ _
  rw [h_sum_lineIntegral]
  -- Step 3: (ambientPhi f hf (periodVec γ)) j = ∑ i, v i * (periodVec γ) i (matrix transpose).
  show ∑ i, v i * lineIntegral (periodBasisForm X i) γ =
    (ambientPhi f hf (periodVec γ)) j
  have h_ambientPhi : (ambientPhi f hf (periodVec γ)) j = ∑ i, v i * (periodVec γ) i := by
    show (Matrix.transpose (LinearMap.toMatrix
      (Pi.basisFun ℂ (Fin (kirovGenus Y))) (Pi.basisFun ℂ (Fin (kirovGenus X)))
      (ambientPsi f hf).toLinearMap)).mulVecLin (periodVec γ) j =
      ∑ i, v i * (periodVec γ) i
    rw [Matrix.mulVecLin_apply]
    show ∑ i, (Matrix.transpose (LinearMap.toMatrix _ _ _)) j i * (periodVec γ) i =
      ∑ i, v i * (periodVec γ) i
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    show (LinearMap.toMatrix (Pi.basisFun ℂ (Fin (kirovGenus Y)))
      (Pi.basisFun ℂ (Fin (kirovGenus X))) (ambientPsi f hf).toLinearMap) i j = v i
    rw [LinearMap.toMatrix_apply]
    show ((Pi.basisFun ℂ (Fin (kirovGenus X))).repr
      (ambientPsi f hf (Pi.basisFun ℂ (Fin (kirovGenus Y)) j))) i = v i
    rw [Pi.basisFun_repr]
  rw [h_ambientPhi]
  -- Goal: ∑ i, v i * lineIntegral (periodBasisForm X i) γ = ∑ i, v i * (periodVec γ) i
  rfl

/-- **Existence of a period ℝ-basis** — the *single* classical input behind the
Jacobian-as-complex-torus structure (the Riemann bilinear relations, Forster §§20–21).
It states the period lattice is generated, as a `ℤ`-module, by a **real basis** of
`ℂ^(kirovGenus X) ≅ ℝ^(2·kirovGenus X)`: the `2g` periods of a symplectic homology basis are
`ℝ`-linearly independent and `ℤ`-generate the lattice.

From this, **both** the discreteness and the full-rank-`ℤ`-lattice instances below are
*mechanical* — they are Mathlib's `ZSpan.instDiscreteTopology` / `instIsZLatticeRealSpan`
for the `ℤ`-span of a real basis, transported across the lattice equality. So this is the
only remaining classical content; everything downstream is unconditional given it.

**Now PROVEN modulo the two-pillar scaffold** (`Jacobians/Dissection.lean`): the *assembly*
`realBasis_of_canonicalDissection` is unconditional; the remaining inputs are
`exists_canonicalDissection` (the isolated surface-topology pillar — `H₁(X;ℤ) ≅ ℤ^{2g}` + the
canonical dissection + period homology-invariance) and `periodVec_linearIndependent` (the analytic
pillar — the Riemann bilinear relations, to be built via cut-surface + Green's theorem). -/
theorem exists_periodLattice_realBasis :
    ∃ b : Module.Basis (Fin (2 * kirovGenus X)) ℝ (Fin (kirovGenus X) → ℂ),
      truePeriodLattice X = Submodule.span ℤ (Set.range ⇑b) := by
  obtain ⟨D⟩ := exists_canonicalDissection X
  obtain ⟨b, hb⟩ := realBasis_of_canonicalDissection D
  exact ⟨b, by rw [truePeriodLattice]; exact hb⟩

/-- **Discrete topology on the period lattice.** Mechanical from
`exists_periodLattice_realBasis`: a `ℤ`-span of a real basis is discrete
(`ZSpan.instDiscreteTopology`). -/
instance : DiscreteTopology (truePeriodLattice X) := by
  obtain ⟨b, hb⟩ := exists_periodLattice_realBasis (X := X)
  rw [hb]; infer_instance

/-- **Period lattice is a `ℤ`-lattice of full real rank** `2 * kirovGenus X` in
`ℂ^(kirovGenus X) = ℝ^(2g)`. Mechanical from `exists_periodLattice_realBasis`: a `ℤ`-span
of a real basis is a full-rank `ℤ`-lattice (`instIsZLatticeRealSpan`). -/
instance : IsZLattice ℝ (truePeriodLattice X) := by
  obtain ⟨b, hb⟩ := exists_periodLattice_realBasis (X := X)
  exact { span_top := by rw [hb]; exact (instIsZLatticeRealSpan b).span_top }

/-! ### Phase 4a: `ambientPhi` preserves the period lattice

From `periodVec_pushforward`: for a closed loop `γ` in `X`, `f ∘ γ`
is a closed loop in `Y`, so `periodVec (f ∘ γ)` lies in the period
lattice of `Y`. This equals `ambientPhi f hf (periodVec γ)`, so
`ambientPhi` sends `closedLoopPeriods X` into `truePeriodLattice Y`.
By ℤ-linearity, it sends the whole ℤ-span into `truePeriodLattice Y`.

Stated here in the `AddSubgroup.comap` form matching `Jacobians.lean`. -/

theorem ambientPhi_preserves_truePeriodLattice
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (truePeriodLattice X).toAddSubgroup ≤
      (truePeriodLattice Y).toAddSubgroup.comap
        (ambientPhi (gX := kirovGenus X) (gY := kirovGenus Y) f hf).toAddMonoidHom := by
  show ∀ v ∈ truePeriodLattice X,
    ambientPhi (gX := kirovGenus X) (gY := kirovGenus Y) f hf v ∈ truePeriodLattice Y
  intro v hv
  refine Submodule.span_induction
    (p := fun v _ => ambientPhi (gX := kirovGenus X) (gY := kirovGenus Y) f hf v ∈
      truePeriodLattice Y) ?_ ?_ ?_ ?_ hv
  · -- member case: γ ∈ closedLoopPeriods carries IsClosedSmoothLoop.
    rintro _ ⟨γ, hγ, rfl⟩
    rw [← periodVec_pushforward f hf γ hγ.cont hγ.diff hγ.integrable]
    -- f ∘ γ is IsClosedSmoothLoop via `IsClosedSmoothLoop.comp`.
    exact periodVec_mem_truePeriodLattice_of_closed (f ∘ γ) (hγ.comp f hf)
  · -- zero case
    simp
  · -- add case
    intro x y _ _ hx hy
    simp only [map_add]
    exact Submodule.add_mem _ hx hy
  · -- smul case (ℤ-scalar)
    intro r x _ hx
    simp only [map_zsmul]
    exact Submodule.smul_mem _ r hx

/-! ### Phase 4b: `ambientPsi` preserves the period lattice

This is the **trace / pullback-of-cycle direction**. Split by whether
`f` is constant:

**Constant case (real)**: if `f x = y₀` for all `x`, then
`mfderiv f x = 0` (by `mfderiv_const`), so `pullbackForm f hf = 0`
(pointwise composition with zero), so `ambientPsi f hf = 0`. Hence
the image is `0 ∈ truePeriodLattice X` for free.

**Non-constant case (content-gated)**: `f` is a branched cover of
some degree `d ≥ 1`; the preimage `f⁻¹(δ)` is a ℤ-cycle in `X` and
the trace identity places `ambientPsi (periodVec δ)` in the period
lattice (Forster §10.11). Real infrastructure required: branched-cover
lift existence + trace adjunction (~200–500 lines not yet in place). -/

/-- **pullbackForm of a constant map is zero.** If `f` is constant,
then `mfderiv f x = 0` everywhere, making the pointwise composition
`α(f x) ∘ mfderiv f x = 0`. -/
theorem pullbackForm_eq_zero_of_const
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hconst : ∃ y₀ : Y, ∀ x, f x = y₀) :
    pullbackForm f hf = 0 := by
  obtain ⟨y₀, hy₀⟩ := hconst
  ext α
  apply ContMDiffSection.ext
  intro x
  show (α.toFun (f x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x) = 0
  have : mfderiv 𝓘(ℂ) 𝓘(ℂ) f x = 0 := by
    have hfconst : f = fun _ => y₀ := funext hy₀
    rw [hfconst]
    exact mfderiv_const
  rw [this, ContinuousLinearMap.comp_zero]

/-- **ambientPsi of a constant map is zero.** Follows from
`pullbackForm_eq_zero_of_const`: `ambientPsi = iso⁻¹ ∘ pullbackForm ∘ iso`,
and composition with zero is zero. -/
theorem ambientPsi_eq_zero_of_const
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hconst : ∃ y₀ : Y, ∀ x, f x = y₀) :
    ambientPsi (gX := kirovGenus X) (gY := kirovGenus Y) f hf = 0 := by
  unfold ambientPsi
  simp only [dite_true]
  rw [pullbackForm_eq_zero_of_const f hf hconst]
  ext v i
  simp

/-! #### Branched-cover infrastructure (incremental)

For non-constant holomorphic `f : X → Y` between compact connected
Riemann surfaces:

* `criticalSet f` := `{x | mfderiv f x = 0}` — the ramification locus.
* `branchLocus f` := `f '' criticalSet f` — image of critical points.

Classical facts (partially in place, partially axiomatized):
* `criticalSet` is closed (preimage of `{0}` under the continuous
  `mfderiv` section).
* For non-constant `f`, `criticalSet f ≠ Set.univ` (open mapping
  theorem applied locally in charts).
* `criticalSet` is discrete in `X` (isolated zeros of a non-zero
  analytic function in local coords).
* Being closed + discrete in compact `X`, `criticalSet` is FINITE.
* On `X ∖ criticalSet`, `f` is a local diffeomorphism (inverse
  function theorem).
* On `Y ∖ branchLocus`, `f` restricts to a finite covering.
* Closed loops in `Y ∖ branchLocus` admit lifts to closed loops in
  `X ∖ criticalSet` (covering-space path lifting).
* Loops meeting `branchLocus` can be homotoped off it (removing
  finitely many points from a connected manifold preserves π₁ access).

Each step below is stated as a theorem; real proofs fill in in
subsequent commits. -/

/-- **Critical set of a holomorphic map** between complex 1-manifolds.

Defined as `Jacobians.Discharge.Manifold.criticalSetGeneral f` — the set of
points at which `f` is not locally injective. Classically equivalent to
`{x | mfderiv f x = 0}` for analytic maps between complex 1-manifolds
(the planar bridge ZZ99 / Forster §I.7); the local-injectivity definition is
the one supported by the imported discharge infrastructure, which gives us
closedness, ne-univ, and finiteness directly. -/
def criticalSet (f : X → Y) : Set X :=
  Jacobians.Discharge.Manifold.criticalSetGeneral f

/-- **Branch locus**: the image of the critical set. -/
def branchLocus (f : X → Y) : Set Y :=
  f '' criticalSet f

/-- **Critical set is closed.** The not-locally-injective set is closed via
the discharge's `isClosed_criticalSetGeneral` (CriticalSetClosed). -/
theorem isClosed_criticalSet (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    IsClosed (criticalSet f) :=
  Jacobians.Discharge.Manifold.isClosed_criticalSetGeneral f

/-- **Critical set of a non-constant map is not everything.** Discharge
proves `(criticalSet f).Finite`; `X` is infinite (a compact connected
complex 1-manifold has an open chart into ℂ which contains an open ball,
hence infinitely many points); so `criticalSet f ≠ univ`. -/
theorem criticalSet_ne_univ_of_nonconstant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    criticalSet f ≠ Set.univ := by
  intro h_eq
  have h_fin : (criticalSet f).Finite :=
    Jacobians.Discharge.Manifold.criticalSet_finite_general f hf hnonconst
  rw [h_eq] at h_fin
  haveI : Infinite X :=
    Jacobians.Discharge.ContMDiff.Degree.y_infinite_of_chartedSpace_complex
  exact Set.infinite_univ.not_finite h_fin

/-- **Critical set is finite** (Forster §4 / isolated-zeros). For
non-constant holomorphic `f`, `criticalSet f` is finite. Direct forward
to discharge's `criticalSet_finite_general`. -/
theorem finite_criticalSet_of_nonconstant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    (criticalSet f).Finite :=
  Jacobians.Discharge.Manifold.criticalSet_finite_general f hf hnonconst

/-- **Branch locus is finite.** Image of a finite set is finite. -/
theorem finite_branchLocus_of_nonconstant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    (branchLocus f).Finite :=
  (finite_criticalSet_of_nonconstant f hf hnonconst).image f

/-! ## §1 Local structure of non-constant holomorphic maps

Non-constant holomorphic maps between Riemann surfaces are open and discrete
(Forster §4.2); off the branch locus they are local homeomorphisms (§4.4), and
since a compact source makes them proper, they restrict to finite-sheeted
coverings off the branch locus (§4.22–4.23). The open-mapping half is proven
below (`isOpenMap_of_nonconstant`). -/

/-- Chart pullback of `f` at `x`. -/
noncomputable def chartPullback (f : X → Y) (x : X) : ℂ → ℂ :=
  (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm

theorem analyticAt_chartPullback (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (x : X) :
    AnalyticAt ℂ (chartPullback f x) ((chartAt ℂ x) x) :=
  Jacobians.Discharge.ContMDiff.Degree.contMDiffAt_omega_analyticAt_chart_pullback (hf x)

/-- **Local open mapping at `x`** (provided the chart pullback is not locally
constant there): `f` sends neighborhoods of `x` to neighborhoods of `f x`. This
is the heart of the open mapping theorem, transferred through the charts. -/
theorem nhds_le_map_of_chartPullback_not_eventuallyConst
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (x : X)
    (hnc : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x), chartPullback f x z = chartPullback f x ((chartAt ℂ x) x)) :
    𝓝 (f x) ≤ Filter.map f (𝓝 x) := by
  set φ := chartAt ℂ x with hφ
  set ψ := chartAt ℂ (f x) with hψ
  set g := chartPullback f x with hg
  have hxφ : x ∈ φ.source := mem_chart_source ℂ x
  have hfxψ : f x ∈ ψ.source := mem_chart_source ℂ (f x)
  -- g is open at φ x: from analyticity + not-locally-constant, `nhds_le_map_nhds`.
  have hgA : AnalyticAt ℂ g (φ x) := analyticAt_chartPullback f hf x
  have hg_open : 𝓝 (g (φ x)) ≤ Filter.map g (𝓝 (φ x)) :=
    hgA.eventually_constant_or_nhds_le_map_nhds.resolve_left hnc
  -- g (φ x) = ψ (f x).
  have hgφx : g (φ x) = ψ (f x) := by
    simp only [hg, chartPullback, Function.comp_apply]
    rw [φ.left_inv hxφ]
  -- 𝓝 x = map φ.symm (𝓝 (φ x)).
  have hnx : Filter.map φ.symm (𝓝 (φ x)) = 𝓝 x := φ.symm_map_nhds_eq hxφ
  -- 𝓝 (f x) = map ψ.symm (𝓝 (ψ (f x))).
  have hnfx : Filter.map ψ.symm (𝓝 (ψ (f x))) = 𝓝 (f x) := ψ.symm_map_nhds_eq hfxψ
  -- f ∘ φ.symm =ᶠ[𝓝 (φ x)] ψ.symm ∘ g  near φ x.
  have hev : (f ∘ φ.symm) =ᶠ[𝓝 (φ x)] (ψ.symm ∘ g) := by
    have hφxtarget : φ x ∈ φ.target := φ.map_source hxφ
    have hcont : ContinuousAt (fun z => f (φ.symm z)) (φ x) :=
      hf.continuous.continuousAt.comp
        (φ.continuousOn_symm.continuousAt (φ.open_target.mem_nhds hφxtarget))
    have hval : f (φ.symm (φ x)) = f x := by rw [φ.left_inv hxφ]
    have hsrc_nhds : ψ.source ∈ 𝓝 (f (φ.symm (φ x))) := by
      rw [hval]; exact ψ.open_source.mem_nhds hfxψ
    have hpre : ∀ᶠ z in 𝓝 (φ x), f (φ.symm z) ∈ ψ.source :=
      hcont.preimage_mem_nhds hsrc_nhds
    filter_upwards [hpre] with z hz
    show f (φ.symm z) = ψ.symm (g z)
    simp only [hg, chartPullback, Function.comp_apply]
    rw [ψ.left_inv hz]
  -- assemble: 𝓝 (f x) ≤ map f (𝓝 x)
  calc 𝓝 (f x) = Filter.map ψ.symm (𝓝 (ψ (f x))) := hnfx.symm
    _ ≤ Filter.map ψ.symm (Filter.map g (𝓝 (φ x))) := by
          rw [← hgφx]; exact Filter.map_mono hg_open
    _ = Filter.map (ψ.symm ∘ g) (𝓝 (φ x)) := by rw [Filter.map_map]
    _ = Filter.map (f ∘ φ.symm) (𝓝 (φ x)) := by rw [Filter.map_congr hev.symm]
    _ = Filter.map f (Filter.map φ.symm (𝓝 (φ x))) := by rw [Filter.map_map]
    _ = Filter.map f (𝓝 x) := by rw [hnx]

section GlobalizedIdentity
open Set

/-- `f` is locally constant at `x`: eventually equal to `f x`. -/
def locConst (f : X → Y) (x : X) : Prop := ∀ᶠ x' in 𝓝 x, f x' = f x

-- Lemma A: chart-pullback eventually const at chart image ↔ f locally const at x.
theorem chartPullback_eventuallyConst_iff_locConst
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (x : X) :
    (∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
      chartPullback f x z = chartPullback f x ((chartAt ℂ x) x))
    ↔ locConst f x := by
  set φ := chartAt ℂ x with hφ
  set ψ := chartAt ℂ (f x) with hψ
  have hxφ : x ∈ φ.source := mem_chart_source ℂ x
  have hfxψ : f x ∈ ψ.source := mem_chart_source ℂ (f x)
  -- 𝓝 x = map φ.symm (𝓝 (φ x)), and 𝓝 (φ x) = map φ (𝓝 x)
  have hmap : Filter.map φ.symm (𝓝 (φ x)) = 𝓝 x := φ.symm_map_nhds_eq hxφ
  have hmap' : Filter.map φ (𝓝 x) = 𝓝 (φ x) := φ.map_nhds_eq hxφ
  -- f continuous near x stays in ψ.source
  have hcontf : ContinuousAt f x := hf.continuous.continuousAt
  have hf_src : ∀ᶠ x' in 𝓝 x, f x' ∈ ψ.source :=
    hcontf.preimage_mem_nhds (ψ.open_source.mem_nhds hfxψ)
  -- φ.symm (φ x) = x
  have hsymm : φ.symm (φ x) = x := φ.left_inv hxφ
  -- chartPullback f x (φ x') = ψ (f x') when x' ∈ φ.source
  have hpb_eq : ∀ x', x' ∈ φ.source →
      chartPullback f x (φ x') = ψ (f x') := by
    intro x' hx'
    simp only [chartPullback, Function.comp_apply, ← hφ, ← hψ]
    rw [φ.left_inv hx']
  have hpbx : chartPullback f x (φ x) = ψ (f x) := hpb_eq x hxφ
  -- x' ∈ φ.source for x' near x
  have hx_src : ∀ᶠ x' in 𝓝 x, x' ∈ φ.source :=
    φ.open_source.mem_nhds hxφ
  constructor
  · -- pullback const ⇒ locConst
    intro hev
    rw [← hmap', Filter.eventually_map] at hev
    -- hev : ∀ᶠ x' in 𝓝 x, chartPullback f x (φ x') = chartPullback f x (φ x)
    filter_upwards [hev, hf_src, hx_src] with x' hpb hx'src hx'φ
    -- ψ (f x') = ψ (f x) ⇒ f x' = f x
    rw [hpb_eq x' hx'φ, hpbx] at hpb
    exact ψ.injOn hx'src hfxψ hpb
  · -- locConst ⇒ pullback const
    intro hlc
    rw [← hmap', Filter.eventually_map]
    filter_upwards [hlc, hx_src] with x' hfx' hx'φ
    rw [hpb_eq x' hx'φ, hpbx, hfx']

/-- **Bridge with a fixed target chart.** For `x` in the source chart of `x₀`
whose image `f x` lies in the *fixed* target chart of `x₀`, local constancy of
`f` at `x` is equivalent to the (single, `x₀`-based) chart pullback being
eventually constant at `φ₀ x`. -/
theorem locConst_iff_pullback_const_fixedChart
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (x₀ x : X)
    (hxφ : x ∈ (chartAt ℂ x₀).source)
    (hfxψ : f x ∈ (chartAt ℂ (f x₀)).source) :
    locConst f x ↔
      ∀ᶠ z in 𝓝 ((chartAt ℂ x₀) x), chartPullback f x₀ z = chartPullback f x₀ ((chartAt ℂ x₀) x) := by
  set φ := chartAt ℂ x₀ with hφ
  set ψ := chartAt ℂ (f x₀) with hψ
  -- 𝓝 (φ x) = map φ (𝓝 x)
  have hmap' : Filter.map φ (𝓝 x) = 𝓝 (φ x) := φ.map_nhds_eq hxφ
  -- f continuous near x stays in ψ.source
  have hcontf : ContinuousAt f x := hf.continuous.continuousAt
  have hf_src : ∀ᶠ x' in 𝓝 x, f x' ∈ ψ.source :=
    hcontf.preimage_mem_nhds (ψ.open_source.mem_nhds hfxψ)
  -- chartPullback f x₀ (φ x') = ψ (f x') when x' ∈ φ.source
  have hpb_eq : ∀ x', x' ∈ φ.source →
      chartPullback f x₀ (φ x') = ψ (f x') := by
    intro x' hx'
    simp only [chartPullback, Function.comp_apply, ← hφ, ← hψ]
    rw [φ.left_inv hx']
  have hpbx : chartPullback f x₀ (φ x) = ψ (f x) := hpb_eq x hxφ
  have hx_src : ∀ᶠ x' in 𝓝 x, x' ∈ φ.source := φ.open_source.mem_nhds hxφ
  constructor
  · -- locConst ⇒ pullback const
    intro hlc
    rw [← hmap', Filter.eventually_map]
    filter_upwards [hlc, hx_src] with x' hfx' hx'φ
    rw [hpb_eq x' hx'φ, hpbx, hfx']
  · -- pullback const ⇒ locConst
    intro hev
    rw [← hmap', Filter.eventually_map] at hev
    filter_upwards [hev, hf_src, hx_src] with x' hpb hx'src hx'φ
    rw [hpb_eq x' hx'φ, hpbx] at hpb
    exact ψ.injOn hx'src hfxψ hpb

/-- The set of points where `f` is locally constant is **open**. -/
theorem isOpen_locConst (f : X → Y) : IsOpen {x | locConst f x} := by
  rw [isOpen_iff_eventually]
  intro x₀ hx₀
  -- hx₀ : locConst f x₀, i.e. ∀ᶠ x' in 𝓝 x₀, f x' = f x₀
  simp only [mem_setOf_eq, locConst] at hx₀
  rw [eventually_iff_exists_mem] at hx₀
  obtain ⟨W, hW, hWeq⟩ := hx₀
  -- W ∈ 𝓝 x₀ with f = f x₀ on W
  rw [eventually_iff_exists_mem]
  refine ⟨interior W, interior_mem_nhds.mpr hW, ?_⟩
  intro x hxW
  -- f locally const at x: on interior W (a nbhd of x), f = f x₀ = f x
  have hfx : f x = f x₀ := hWeq x (interior_subset hxW)
  have : ∀ᶠ x' in 𝓝 x, f x' = f x := by
    filter_upwards [isOpen_interior.mem_nhds hxW] with x' hx'
    rw [hWeq x' (interior_subset hx'), hfx]
  exact this

/-- The set of points where `f` is locally constant is **closed**
(equivalently, its complement is open), via the identity theorem. -/
theorem isClosed_locConst (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    IsClosed {x | locConst f x} := by
  rw [← isOpen_compl_iff, isOpen_iff_eventually]
  intro x₀ hx₀
  simp only [mem_compl_iff, mem_setOf_eq] at hx₀ ⊢
  set φ := chartAt ℂ x₀ with hφ
  set ψ := chartAt ℂ (f x₀) with hψ
  set G := chartPullback f x₀ with hG
  set z₀ := φ x₀ with hz₀
  have hxφ₀ : x₀ ∈ φ.source := mem_chart_source ℂ x₀
  have hfxψ₀ : f x₀ ∈ ψ.source := mem_chart_source ℂ (f x₀)
  -- G not eventually const at z₀, via Lemma A
  have hGnc : ¬ ∀ᶠ z in 𝓝 z₀, G z = G z₀ :=
    fun h => hx₀ ((chartPullback_eventuallyConst_iff_locConst f hf x₀).mp h)
  -- G analytic on a ball around z₀
  have hGA : AnalyticAt ℂ G z₀ := analyticAt_chartPullback f hf x₀
  obtain ⟨r, hr, hball⟩ := hGA.exists_ball_analyticOnNhd
  have hballpc : IsPreconnected (Metric.ball z₀ r) := (convex_ball z₀ r).isPreconnected
  -- For every z₁ in the ball, G not eventually const at z₁.
  have hnc_ball : ∀ z₁ ∈ Metric.ball z₀ r, ¬ ∀ᶠ z in 𝓝 z₁, G z = G z₁ := by
    intro z₁ hz₁ hev
    -- G = G z₁ on the ball
    have heqOn : EqOn G (fun _ => G z₁) (Metric.ball z₀ r) :=
      Jacobians.Discharge.ContMDiff.Degree.eqOn_const_of_preconnected_of_eventuallyEq
        hball hballpc hz₁ hev
    -- so G eventually const at z₀
    apply hGnc
    have hz₀ball : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
    filter_upwards [Metric.ball_mem_nhds z₀ hr] with z hz
    rw [heqOn hz, heqOn hz₀ball]
  -- Now: the open set around x₀ where the bridge applies.
  -- V := φ.source ∩ φ ⁻¹' (ball) ∩ f ⁻¹' ψ.source
  have hVopen : IsOpen (φ.source ∩ φ ⁻¹' (Metric.ball z₀ r)) :=
    φ.continuousOn.isOpen_inter_preimage φ.open_source Metric.isOpen_ball
  have hfopen : IsOpen (f ⁻¹' ψ.source) :=
    ψ.open_source.preimage hf.continuous
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨(φ.source ∩ φ ⁻¹' (Metric.ball z₀ r)) ∩ (f ⁻¹' ψ.source), ?_, ?_⟩
  · refine (hVopen.inter hfopen).mem_nhds ⟨⟨hxφ₀, ?_⟩, hfxψ₀⟩
    show φ x₀ ∈ Metric.ball z₀ r
    rw [← hz₀]; exact Metric.mem_ball_self hr
  · rintro x ⟨⟨hxsrc, hxball⟩, hxfsrc⟩
    -- ¬ locConst f x via bridge + hnc_ball
    rw [locConst_iff_pullback_const_fixedChart f hf x₀ x hxsrc hxfsrc]
    -- goal: ¬ ∀ᶠ z in 𝓝 (φ x), G z = G (φ x)
    exact hnc_ball (φ x) hxball

/-- **Globalized identity theorem.** The chart pullback of a non-constant
holomorphic map is not locally constant at any chart image. -/
theorem chartPullback_not_eventuallyConst
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (x : X) :
    ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
      chartPullback f x z = chartPullback f x ((chartAt ℂ x) x) := by
  rw [chartPullback_eventuallyConst_iff_locConst f hf x]
  -- Suppose f is locally constant at x. Show f is globally constant.
  intro hlc
  apply hnonconst
  -- S = {x | locConst f x} is clopen and nonempty, hence all of X.
  have hclopen : IsClopen {x : X | locConst f x} :=
    ⟨isClosed_locConst f hf, isOpen_locConst f⟩
  have hne : {x : X | locConst f x}.Nonempty := ⟨x, hlc⟩
  have huniv : {x : X | locConst f x} = Set.univ :=
    (isClopen_iff.mp hclopen).resolve_left
      (Set.nonempty_iff_ne_empty.mp hne)
  -- So f is locally constant everywhere ⇒ IsLocallyConstant ⇒ constant.
  have hLC : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y
    have hy : y ∈ {x : X | locConst f x} := by rw [huniv]; trivial
    exact hy
  obtain ⟨y₀, hy₀⟩ := hLC.exists_eq_const
  exact ⟨y₀, fun x' => congrFun hy₀ x'⟩

end GlobalizedIdentity


/-- **[PROVEN modulo `chartPullback_not_eventuallyConst`]** A non-constant
holomorphic map between Riemann surfaces is an open map. Assembled from the
proven open-mapping transfer `nhds_le_map_of_chartPullback_not_eventuallyConst`
and the (refined) non-constancy lemma. -/
theorem isOpenMap_of_nonconstant (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    IsOpenMap f := by
  rw [isOpenMap_iff_nhds_le]
  intro x
  exact nhds_le_map_of_chartPullback_not_eventuallyConst f hf x
    (chartPullback_not_eventuallyConst f hf hnonconst x)

/-- **[PROVEN]** A non-constant holomorphic map between compact connected
Riemann surfaces is surjective: its range is open (open mapping), closed
(continuous image of compact in a T2 space), and nonempty, hence clopen, hence
all of the connected target `Y`. -/
theorem surjective_of_nonconstant (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    Function.Surjective f := by
  have hopen : IsOpen (Set.range f) := (isOpenMap_of_nonconstant f hf hnonconst).isOpen_range
  have hclosed : IsClosed (Set.range f) := (isCompact_range hf.continuous).isClosed
  have hclopen : IsClopen (Set.range f) := ⟨hclosed, hopen⟩
  rcases isClopen_iff.mp hclopen with h | h
  · exact absurd h (Set.range_nonempty f).ne_empty
  · exact Set.range_eq_univ.mp h

/-- **[PROVEN]** A holomorphic map from a compact Riemann surface is proper
(Forster §4.20): a continuous map from a compact space to a T2 space is proper.
This is what makes the branched-cover theory (§4.22–4.25) available: a proper
local homeomorphism is a covering map. -/
theorem isProperMap_of_contMDiff (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    IsProperMap f :=
  hf.continuous.isProperMap

/-- **[PROVEN modulo `isOpenMap_of_nonconstant`]** Local homeomorphism off the
critical set (Forster §4.4): where `f` is locally injective (`x ∉ criticalSet f`,
i.e. by definition `∃ U ∈ 𝓝 x, InjOn f U`), it restricts to an open injection on
a neighborhood — open via the open-mapping theorem, injective by hypothesis.
Together with `isProperMap_of_contMDiff` this is the input to the covering
structure off the branch locus. -/
theorem isLocalHomeoOffCritical (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) {x : X} (hx : x ∉ criticalSet f) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Set.InjOn f U ∧ IsOpen (f '' U) := by
  have hex : ∃ U ∈ nhds x, Set.InjOn f U := not_not.mp hx
  obtain ⟨U₀, hU₀nhds, hinj₀⟩ := hex
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hU₀nhds
  exact ⟨U, hUopen, hxU, hinj₀.mono hUsub,
    isOpenMap_of_nonconstant f hf hnonconst U hUopen⟩

/-- **Chart-bridge package at a single point.** For non-constant analytic
`f : X → Y` and any `x : X`, assembles the `ChartBridgePackage f x` consumed by
the ZZ99 bridge `criticalSet_iff_chart_pullback_deriv_zero`. The chart pullback
`F := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm` is analytic at `z₀ := chartAt ℂ x x`
(ZZ24), has finite local order `k ≥ 1` of `F - F z₀` (finiteness = `F` not
eventually constant, via the clopenness/chart-overlap discharge applied to the
non-constant `f`; positivity because `(F - F z₀)(z₀) = 0`), and the manifold ↔
chart-pullback non-injectivity transfer holds through the chart homeomorphism.
This is the single-point specialization of `criticalChartPullbackData_general`'s
per-point work. -/
noncomputable def chartBridgePackage_of_nonconstant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (x : X) :
    Jacobians.Discharge.Manifold.ChartBridgePackage f x := by
  classical
  -- Canonical charts at `x` and `f x`, and the chart pullback `F`.
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc_def
  set d : OpenPartialHomeomorph Y ℂ := chartAt ℂ (f x) with hd_def
  set F : ℂ → ℂ := d ∘ f ∘ c.symm with hF_def
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  have hfxd : f x ∈ d.source := mem_chart_source ℂ (f x)
  -- `F` is `AnalyticAt ℂ` at `c x` (ZZ24).
  have hFA : AnalyticAt ℂ F (c x) :=
    Jacobians.Discharge.ContMDiff.Degree.contMDiff_omega_analyticAt_chart_pullback hf x
  -- `F (c x) = d (f x)` via chart left-inverse.
  have hFcx : F (c x) = d (f x) := by
    have h_inv : c.symm (c x) = x := c.left_inv hxc
    show (d ∘ f ∘ c.symm) (c x) = d (f x)
    simp [Function.comp, h_inv]
  -- Non-eventual-constancy of `F` at `c x` (clopenness/chart-overlap discharge).
  have hClop :
      Jacobians.Discharge.ContMDiff.Degree.ClopennessOfLocallyConstHypothesis X Y :=
    Jacobians.Discharge.ContMDiff.Degree.clopennessOfLocallyConst_holds
  have hChartNEC :
      Jacobians.Discharge.ContMDiff.Degree.ChartPullbackNotEventuallyConstHypothesis X Y :=
    Jacobians.Discharge.ContMDiff.Degree.chartPullbackNotEventuallyConst_of_clopennessOfLocallyConst
      hClop
  have hFne_raw :
      ¬ ∀ᶠ z in 𝓝 (c x),
        ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z = (chartAt ℂ (f x)) (f x) :=
    hChartNEC f hf hnonconst (f x) x rfl
  have hFne : ¬ ∀ᶠ z in 𝓝 (c x), F z = F (c x) := by
    intro hev
    apply hFne_raw
    exact hev.mono (fun z hz => by
      show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z = (chartAt ℂ (f x)) (f x)
      have hz' : F z = F (c x) := hz
      rw [show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z = F z from rfl, hz', hFcx])
  -- Order of `(F - F (c x))` at `c x` is finite and ≥ 1.
  have hFA_sub : AnalyticAt ℂ (fun z => F z - F (c x)) (c x) := hFA.sub analyticAt_const
  have h_ord_ne_top : analyticOrderAt (fun z => F z - F (c x)) (c x) ≠ ⊤ := by
    intro h_top
    apply hFne
    have h := analyticOrderAt_eq_top.mp h_top
    exact h.mono (fun z hz => sub_eq_zero.mp hz)
  have hF_self : (fun z => F z - F (c x)) (c x) = 0 := by simp
  have h_ord_ne_zero : analyticOrderAt (fun z => F z - F (c x)) (c x) ≠ 0 := by
    intro h_zero
    exact (hFA_sub.analyticOrderAt_eq_zero.mp h_zero) hF_self
  set ord : ℕ∞ := analyticOrderAt (fun z => F z - F (c x)) (c x) with hord_def
  -- Extract the finite order as `k : ℕ` (the goal here is `Type`-valued, so we
  -- compute `k := ord.toNat` rather than destructuring the existential).
  set k : ℕ := ord.toNat with hk_def
  have hk_eq : ord = (k : ℕ∞) := (ENat.coe_toNat h_ord_ne_top).symm
  have hk_ge_one : 1 ≤ k :=
    Nat.one_le_iff_ne_zero.mpr (fun h0 => h_ord_ne_zero (by rw [hk_eq, h0, Nat.cast_zero]))
  -- Manifold ↔ chart-pullback non-injectivity transfer.
  have h_inj_iff : (∃ U ∈ 𝓝 x, Set.InjOn f U) ↔ (∃ U' ∈ 𝓝 (c x), Set.InjOn F U') := by
    constructor
    · rintro ⟨U, hU_nhds, hU_inj⟩
      set U₁ : Set X := U ∩ c.source ∩ f ⁻¹' d.source with hU₁_def
      have hf_cont : Continuous f := hf.continuous
      have hU₁_nhds : U₁ ∈ 𝓝 x :=
        Filter.inter_mem (Filter.inter_mem hU_nhds (c.open_source.mem_nhds hxc))
          (hf_cont.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds hfxd))
      have hU₁_subc : U₁ ⊆ c.source := fun _ hy => hy.1.2
      obtain ⟨U₁o, hU₁o_open, hU₁o_sub, hx_U₁o⟩ :
          ∃ Uo, IsOpen Uo ∧ Uo ⊆ U₁ ∧ x ∈ Uo := by
        obtain ⟨W, hW_sub, hW_open, hxW⟩ := mem_nhds_iff.mp hU₁_nhds
        exact ⟨W, hW_open, hW_sub, hxW⟩
      have hU₁o_subc : U₁o ⊆ c.source := hU₁o_sub.trans hU₁_subc
      set U' : Set ℂ := c '' U₁o with hU'_def
      have hU'_open : IsOpen U' := c.isOpen_image_of_subset_source hU₁o_open hU₁o_subc
      have hcx_U' : c x ∈ U' := ⟨x, hx_U₁o, rfl⟩
      refine ⟨U', hU'_open.mem_nhds hcx_U', ?_⟩
      rintro z₁ ⟨y₁, hy₁_U, hy₁_eq⟩ z₂ ⟨y₂, hy₂_U, hy₂_eq⟩ hF_eq
      have hy₁_subc : y₁ ∈ c.source := hU₁o_subc hy₁_U
      have hy₂_subc : y₂ ∈ c.source := hU₁o_subc hy₂_U
      have hy₁_U₁ : y₁ ∈ U₁ := hU₁o_sub hy₁_U
      have hy₂_U₁ : y₂ ∈ U₁ := hU₁o_sub hy₂_U
      have h_inv_y₁ : c.symm (c y₁) = y₁ := c.left_inv hy₁_subc
      have h_inv_y₂ : c.symm (c y₂) = y₂ := c.left_inv hy₂_subc
      have hF_at_y₁ : F (c y₁) = d (f y₁) := by
        show (d ∘ f ∘ c.symm) (c y₁) = d (f y₁); simp [Function.comp, h_inv_y₁]
      have hF_at_y₂ : F (c y₂) = d (f y₂) := by
        show (d ∘ f ∘ c.symm) (c y₂) = d (f y₂); simp [Function.comp, h_inv_y₂]
      rw [← hy₁_eq, ← hy₂_eq] at hF_eq
      rw [hF_at_y₁, hF_at_y₂] at hF_eq
      have hf_eq : f y₁ = f y₂ := d.injOn hy₁_U₁.2 hy₂_U₁.2 hF_eq
      have hy_eq : y₁ = y₂ := hU_inj hy₁_U₁.1.1 hy₂_U₁.1.1 hf_eq
      rw [← hy₁_eq, ← hy₂_eq, hy_eq]
    · rintro ⟨U', hU'_nhds, hU'_inj⟩
      obtain ⟨U'o, hU'o_open, hU'o_sub, hcx_U'o⟩ :
          ∃ U'o, IsOpen U'o ∧ U'o ⊆ U' ∧ c x ∈ U'o := by
        obtain ⟨W, hW_sub, hW_open, hxW⟩ := mem_nhds_iff.mp hU'_nhds
        exact ⟨W, hW_open, hW_sub, hxW⟩
      set U : Set X := c.source ∩ c ⁻¹' U'o with hU_def
      have hU_open : IsOpen U :=
        c.continuousOn_toFun.isOpen_inter_preimage c.open_source hU'o_open
      have hx_U : x ∈ U := ⟨hxc, hcx_U'o⟩
      refine ⟨U, hU_open.mem_nhds hx_U, ?_⟩
      intro y₁ hy₁ y₂ hy₂ hf_eq
      obtain ⟨hy₁_subc, hy₁_pre⟩ := hy₁
      obtain ⟨hy₂_subc, hy₂_pre⟩ := hy₂
      have hcy₁_U' : c y₁ ∈ U' := hU'o_sub hy₁_pre
      have hcy₂_U' : c y₂ ∈ U' := hU'o_sub hy₂_pre
      have h_inv_y₁ : c.symm (c y₁) = y₁ := c.left_inv hy₁_subc
      have h_inv_y₂ : c.symm (c y₂) = y₂ := c.left_inv hy₂_subc
      have hF_at_y₁ : F (c y₁) = d (f y₁) := by
        show (d ∘ f ∘ c.symm) (c y₁) = d (f y₁); simp [Function.comp, h_inv_y₁]
      have hF_at_y₂ : F (c y₂) = d (f y₂) := by
        show (d ∘ f ∘ c.symm) (c y₂) = d (f y₂); simp [Function.comp, h_inv_y₂]
      have hF_eq : F (c y₁) = F (c y₂) := by rw [hF_at_y₁, hF_at_y₂, hf_eq]
      have hcy_eq : c y₁ = c y₂ := hU'_inj hcy₁_U' hcy₂_U' hF_eq
      exact c.injOn hy₁_subc hy₂_subc hcy_eq
  -- Package it up. `inj_iff` is the negation of `h_inj_iff`.
  exact
    { F := F
      z₀ := c x
      hF_an := hFA
      k := k
      hk_ge_one := hk_ge_one
      hord := hk_eq
      inj_iff := by
        constructor
        · intro h hex; exact h (h_inj_iff.mpr hex)
        · intro h hex; exact h (h_inj_iff.mp hex) }

/-- **[PROVEN]** Local holomorphic section at a non-critical point. For non-constant
holomorphic `f` and `x ∉ criticalSet f`, `f` admits a `C^ω` local section `g` near
`f x` with `g (f x) = x` and `f ∘ g = id` on an open neighborhood. Composes the
manifold IFT (`exists_holo_localInverse`) with the ZZ99 critical-set ↔ chart-deriv
bridge. The input for the branched-cover trace's fiber sum. -/
theorem exists_holo_localInverse_of_notMem_criticalSet
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) {x : X} (hxcrit : x ∉ criticalSet f) :
    ∃ (g : Y → X) (V : Set Y), IsOpen V ∧ f x ∈ V ∧ g (f x) = x ∧
      (∀ y ∈ V, f (g y) = y) ∧ ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g V := by
  -- Step 1: build the chart-bridge package and apply ZZ99 to get `deriv F z₀ ≠ 0`.
  set P : Jacobians.Discharge.Manifold.ChartBridgePackage f x :=
    chartBridgePackage_of_nonconstant f hf hnonconst x with hP_def
  -- `x ∉ criticalSet f` unfolds to `¬ ¬ (∃ U ∈ 𝓝 x, InjOn f U)`.
  have hnotcrit : ¬ (¬ ∃ U ∈ 𝓝 x, Set.InjOn f U) := hxcrit
  have hbridge : (¬ ∃ U ∈ 𝓝 x, Set.InjOn f U) ↔ deriv P.F P.z₀ = 0 :=
    Jacobians.Discharge.Manifold.criticalSet_iff_chart_pullback_deriv_zero P
  have hderiv0 : deriv P.F P.z₀ ≠ 0 := fun h => hnotcrit (hbridge.mpr h)
  -- `P.F` and `P.z₀` are definitionally the IFT's expected chart pullback / base point.
  have hderiv : deriv ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 :=
    hderiv0
  -- Step 2: apply the manifold IFT.
  exact exists_holo_localInverse f hf x hderiv

/-- **[PROVEN]** Proper preimage-neighborhood lemma (Forster 4.21b): for a proper
`f`, an open `V` containing the fibre `f⁻¹{x}` has an open neighborhood `U ∋ x`
with `f⁻¹U ⊆ V`. (From `f` being a closed map.) Used to shrink the disjoint
local-homeo sheets over a fibre to a common base neighborhood — the key step in
the covering structure off the branch locus (Forster 4.22). -/
theorem properNbhd {f : X → Y} (hf : IsProperMap f) (x : Y) {V : Set X}
    (hV : IsOpen V) (hsub : f ⁻¹' {x} ⊆ V) :
    ∃ U : Set Y, IsOpen U ∧ x ∈ U ∧ f ⁻¹' U ⊆ V := by
  have hcompl : IsClosed (f '' Vᶜ) := hf.isClosedMap _ hV.isClosed_compl
  refine ⟨(f '' Vᶜ)ᶜ, hcompl.isOpen_compl, ?_, ?_⟩
  · rintro ⟨z, hzV, hzx⟩
    exact hzV (hsub hzx)
  · intro z hz
    by_contra hzV
    exact hz ⟨z, hzV, rfl⟩

/-- **[PROVEN modulo `isOpenMap_of_nonconstant`]** Covering off the branch locus
(Forster 4.22): a non-constant holomorphic map restricts to a covering map on
the complement of its (finite) branch locus. Proven via Mathlib's
`IsCoveringMapOn.of_openPartialHomeomorph` (the proper-local-homeo ⇒ covering
theorem — Mathlib already has it, so no hand-built `f⁻¹U ≃ₜ U × fibre`): off the
branch locus every fibre point is off `criticalSet`, so `isLocalHomeoOffCritical`
gives an open injective neighborhood, packaged as an `OpenPartialHomeomorph`
whose `toFun` is `f`. -/
theorem isCoveringMapOn_compl_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    IsCoveringMapOn f (Set.univ \ branchLocus f) := by
  have hopen : IsOpenMap f := isOpenMap_of_nonconstant f hf hnonconst
  refine IsCoveringMapOn.of_openPartialHomeomorph hf.continuous ?_
  intro e he
  have hfe : f e ∉ branchLocus f := he.2
  have hecrit : e ∉ criticalSet f := fun hmem => hfe ⟨e, hmem, rfl⟩
  obtain ⟨U, hUopen, heU, hinj, _himg⟩ := isLocalHomeoOffCritical f hf hnonconst hecrit
  let pe : PartialEquiv X Y := Set.InjOn.toPartialEquiv f U hinj
  have hpe_coe : ⇑pe = f := rfl
  have hpe_source : pe.source = U := rfl
  refine ⟨OpenPartialHomeomorph.ofContinuousOpen pe ?_ ?_ ?_, ?_, ?_⟩
  · rw [hpe_coe, hpe_source]; exact hf.continuous.continuousOn
  · rw [hpe_coe]; exact hopen
  · rw [hpe_source]; exact hUopen
  · show e ∈ (OpenPartialHomeomorph.ofContinuousOpen pe _ _ _).source
    rw [OpenPartialHomeomorph.ofContinuousOpen]
    show e ∈ pe.source
    rw [hpe_source]; exact heU
  · rw [OpenPartialHomeomorph.coe_ofContinuousOpen]; exact hpe_coe

/-- **[PROVEN]** Subtype corestriction of the off-branch covering. Bridges
`isCoveringMapOn_compl_branchLocus` (an `IsCoveringMapOn` on the *set*
`univ ∖ branchLocus f`) to a genuine `IsCoveringMap` of the corestricted map
`↥(f ⁻¹' (univ ∖ branchLocus f)) → ↥(univ ∖ branchLocus f)`, via Mathlib's
`IsCoveringMapOn.isCoveringMap_restrictPreimage`.

This is the form `Mathlib.Topology.Homotopy.Lifting` consumes: it unlocks
`IsCoveringMap.liftPath` (path lifting, Forster §4.14) and
`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` (monodromy / homotopy
invariance of lift endpoints) — the toolkit for assembling the lifted loops in
`exists_preimageCycle_of_off_branchLocus` (relocated to
`Jacobians/TracePullback.lean`, where the genuine `ambientPullbackJac` lives). -/
theorem isCoveringMap_restrictPreimage_compl_branchLocus
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    IsCoveringMap ((Set.univ \ branchLocus f).restrictPreimage f) :=
  (isCoveringMapOn_compl_branchLocus f hf hnonconst).isCoveringMap_restrictPreimage

/-! ## §2 Homotopy invariance and genericity

The supporting classical fact (stated only in prose to avoid an unsound
placeholder lemma): **`periodVec` is homotopy-invariant** — homotopic closed
smooth loops have equal period vectors, because the period forms are closed
holomorphic 1-forms and `∫_γ ω` depends only on the homotopy class by Stokes on
the homotopy cylinder (Forster §10.5; Mathlib lacks manifold Stokes). Stating
it as a Lean lemma requires the right smooth-homotopy hypothesis (a genuine
homotopy of loops), which is folded directly into `exists_loop_off_branchLocus`
(relocated to `Jacobians/TracePullback.lean`) rather than asserted separately. -/

/-! ## §3 Off-branch fibre finiteness

The remaining §3 ingredient that lives here (the preimage-cycle lift itself was
relocated to `Jacobians/TracePullback.lean`, downstream of the genuine
`ambientPullbackJac`). -/

/-- **[PROVEN]** Fibres off the branch locus are **finite**. For `y ∉ branchLocus f`
every preimage `x` is a non-critical point, where `f` is locally injective
(`isLocalHomeoOffCritical`), so `x` is isolated in the fibre ⟹ the fibre is
`IsDiscrete`; it is also closed in compact `X` ⟹ compact, hence finite. This is
the sheet count of the cover over `y` (classically `= deg f`) — the foundation of
the §3 preimage-cycle lift. Note: unlike the discharge's
`fibres_finite_of_connectivity_hypothesis` (gated on the global identity theorem),
this is unconditional off the branch locus, since `isLocalHomeoOffCritical` is
already proven there. -/
theorem fiber_finite_off_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) {y : Y} (hy : y ∉ branchLocus f) :
    (f ⁻¹' {y}).Finite := by
  apply Jacobians.Discharge.ContMDiff.Degree.fiber_finite_of_isDiscrete hf.continuous y
  rw [isDiscrete_iff_forall_exists_isOpen]
  intro x hx
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
  have hxcrit : x ∉ criticalSet f := fun hmem => hy ⟨x, hmem, hx⟩
  obtain ⟨U, hUopen, hxU, hinj, _⟩ := isLocalHomeoOffCritical f hf hnonconst hxcrit
  refine ⟨U, hUopen, Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hxU, ?_⟩, ?_⟩⟩
  · rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hx
  · rintro x' ⟨hx'U, hx'fib⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx'fib
    exact hinj hx'U hxU (hx'fib.trans hx.symm)

end Jacobians
