/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.TraceForm
import KirovDolbeault.LoopOffBranch
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# The Jacobian pullback in ambient coordinates, driven by the geometric trace

This file sits **downstream of the genuine geometric trace** `traceForm`
(`Jacobians/TraceForm.lean`) and turns it into the data the Jacobian `pullback`
consumes:

* `ambientTrace` — `traceFormTotal` read in the `ambientIso` basis coordinates
  (matrix `T`, direction `gX → gY`);
* `ambientPullbackJac` — the transpose `Tᵀ` (direction `gY → gX`), the genuine
  Jacobian pullback in ambient coordinates. By the projection formula it realises
  `periodVec δ ↦ periodVec(preimage cycle)`.

It also hosts the **§3 lift chain** (relocated here from `PeriodLattice.lean`,
whose covering / fibre-finiteness infrastructure is still imported through
`TraceForm`): the `PreimageCycle` structure whose `pullback_eq` field references
`ambientPullbackJac`, and the lemmas that conclude `ambientPullbackJac` preserves
the period lattice.

## Architecture note

Previously `ambientPullbackJac` was driven by an **opaque stub**
`pushforwardForm := if const then 0 else (a placeholder)` in `HolomorphicForms.lean`. That
stub is gone: the single source of truth is now the geometric trace `traceForm`,
and `traceFormTotal` is only its constant-map bookkeeping wrapper (`0` on constant
maps). So the Jacobian pullback is now genuinely the transpose of the geometric
trace of forms.

## References

Forster §§4, 10 (the trace / branched cover); Griffiths–Harris Ch. 2 §2.7
(the trace map for forms, and `f₊ ∘ f* = deg • id`).
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Bundle Topology
open Filter Set

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-! ## Trace-coordinates layer

`ambientTrace` is the geometric trace `traceFormTotal` expressed in the chosen
basis coordinates (via `ambientIso`); `ambientPullbackJac` is its matrix transpose.
The construction is the exact dual of `ambientPsi`/`ambientPhi` for `pullbackForm`
(see `HolomorphicForms.lean`), but built from the genuine trace rather than the old
opaque stub. -/

/-- Coordinate form of the trace `f₊`, parallel to `ambientPsi` for `pullbackForm`:
`ambientTrace = (ambientIso Y)⁻¹ ∘ traceFormTotal f hf ∘ (ambientIso X)` (matrix
`T`, direction `gX → gY`; zero on the unused off-kirovGenus branch). Built from the
genuine geometric trace `traceFormTotal` (which is `traceForm` off the constant
locus and `0` on constant maps). -/
noncomputable def ambientTrace {gX gY : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin gX → ℂ) →L[ℂ] (Fin gY → ℂ) := by
  classical
  by_cases hX : gX = kirovGenus X
  · by_cases hY : gY = kirovGenus Y
    · subst hX; subst hY
      refine LinearMap.toContinuousLinearMap
        ((ambientIso Y).symm.toLinearMap.comp
          ((traceFormTotal f hf).comp (ambientIso X).toLinearMap))
    · exact 0
  · exact 0

/-- The genuine Jacobian **pullback** in ambient coordinates: `Tᵀ`, the transpose
of `ambientTrace` (via the standard Pi basis). Direction `gY → gX`. By the
projection formula this realises `periodVec δ ↦ periodVec(preimage cycle)`; it
replaces the misformalized `ambientPsi`-as-pullback. As with `ambientPhi`, the
transpose makes contravariant `ambientPullbackJac_comp` automatic from covariant
`ambientTrace_comp`. -/
noncomputable def ambientPullbackJac {gX gY : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin gY → ℂ) →L[ℂ] (Fin gX → ℂ) :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toMatrix (Pi.basisFun ℂ (Fin gX)) (Pi.basisFun ℂ (Fin gY))
        (ambientTrace f hf).toLinearMap).transpose.mulVecLin

/-- `ambientTrace id = id`. Proven via `traceFormTotal_id`. -/
theorem ambientTrace_id (x : Fin (kirovGenus X) → ℂ) :
    ambientTrace (X := X) (Y := X) (gX := kirovGenus X) (gY := kirovGenus X) id contMDiff_id x = x := by
  unfold ambientTrace
  set_option linter.unusedSimpArgs false in
  simp only [dif_pos rfl]
  show (((ambientIso X).symm.toLinearMap.comp
      ((traceFormTotal (id : X → X) contMDiff_id).comp (ambientIso X).toLinearMap)) : _ →ₗ[_] _) x = x
  rw [show (traceFormTotal (id : X → X) contMDiff_id) = LinearMap.id from traceFormTotal_id]
  simp

/-- Covariant composition: `ambientTrace (g ∘ f) = ambientTrace g ∘ ambientTrace f`.
Proven via `traceFormTotal_comp`. -/
theorem ambientTrace_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f))
    (x : Fin (kirovGenus X) → ℂ) :
    ambientTrace (gX := kirovGenus X) (gY := kirovGenus Z) (g ∘ f) hgf x =
      ambientTrace (gX := kirovGenus Y) (gY := kirovGenus Z) g hg
        (ambientTrace (gX := kirovGenus X) (gY := kirovGenus Y) f hf x) := by
  unfold ambientTrace
  set_option linter.unusedSimpArgs false in
  simp only [dif_pos rfl]
  show (((ambientIso Z).symm.toLinearMap.comp
      ((traceFormTotal (g ∘ f) hgf).comp (ambientIso X).toLinearMap))) x = _
  rw [traceFormTotal_comp f hf g hg hgf]
  simp [LinearMap.comp_apply]

/-- `ambientPullbackJac id = id` — transpose of the identity matrix is the
identity, via `ambientTrace_id`. -/
theorem ambientPullbackJac_id (y : Fin (kirovGenus X) → ℂ) :
    ambientPullbackJac (X := X) (Y := X) (gX := kirovGenus X) (gY := kirovGenus X) id contMDiff_id y = y := by
  have htr : ambientTrace (X := X) (Y := X) (gX := kirovGenus X) (gY := kirovGenus X) id contMDiff_id
      = ContinuousLinearMap.id ℂ (Fin (kirovGenus X) → ℂ) :=
    ContinuousLinearMap.ext (fun x => ambientTrace_id x)
  unfold ambientPullbackJac
  rw [show (ambientTrace (X := X) (Y := X) (gX := kirovGenus X) (gY := kirovGenus X) id contMDiff_id).toLinearMap
      = LinearMap.id (R := ℂ) (M := Fin (kirovGenus X) → ℂ) from by rw [htr]; rfl]
  simp [Matrix.transpose_one, Matrix.mulVecLin_one]

/-- Contravariant composition: `ambientPullbackJac (g ∘ f) = ambientPullbackJac f ∘ ambientPullbackJac g`.
Follows from covariant `ambientTrace_comp` via matrix transpose reversing order. -/
theorem ambientPullbackJac_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f))
    (z : Fin (kirovGenus Z) → ℂ) :
    ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Z) (g ∘ f) hgf z =
      ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf
        (ambientPullbackJac (gX := kirovGenus Y) (gY := kirovGenus Z) g hg z) := by
  have htr : ambientTrace (gX := kirovGenus X) (gY := kirovGenus Z) (g ∘ f) hgf =
      (ambientTrace (gX := kirovGenus Y) (gY := kirovGenus Z) g hg).comp
        (ambientTrace (gX := kirovGenus X) (gY := kirovGenus Y) f hf) :=
    ContinuousLinearMap.ext (fun x => ambientTrace_comp f hf g hg hgf x)
  unfold ambientPullbackJac
  rw [show (ambientTrace (gX := kirovGenus X) (gY := kirovGenus Z) (g ∘ f) hgf).toLinearMap =
      (ambientTrace (gX := kirovGenus Y) (gY := kirovGenus Z) g hg).toLinearMap ∘ₗ
      (ambientTrace (gX := kirovGenus X) (gY := kirovGenus Y) f hf).toLinearMap from by rw [htr]; rfl]
  rw [LinearMap.toMatrix_comp (Pi.basisFun ℂ (Fin (kirovGenus X))) (Pi.basisFun ℂ (Fin (kirovGenus Y)))
    (Pi.basisFun ℂ (Fin (kirovGenus Z)))]
  rw [Matrix.transpose_mul, Matrix.mulVecLin_mul]
  rfl

/-- **ambientTrace of a constant map is zero**, from `traceFormTotal_eq_zero_of_const`
(mirrors `ambientPsi_eq_zero_of_const`). -/
theorem ambientTrace_eq_zero_of_const (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hconst : ∃ y₀ : Y, ∀ x, f x = y₀) :
    ambientTrace (gX := kirovGenus X) (gY := kirovGenus Y) f hf = 0 := by
  unfold ambientTrace
  simp only [dite_true]
  rw [traceFormTotal_eq_zero_of_const f hf hconst]
  ext v i
  simp

/-- **ambientPullbackJac of a constant map is zero** (`Tᵀ = 0` when `T = 0`).
The constant-case input to `ambientPullbackJac_preserves_truePeriodLattice`. -/
theorem ambientPullbackJac_eq_zero_of_const (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hconst : ∃ y₀ : Y, ∀ x, f x = y₀) :
    ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf = 0 := by
  unfold ambientPullbackJac
  rw [show (ambientTrace (gX := kirovGenus X) (gY := kirovGenus Y) f hf).toLinearMap
      = (0 : (Fin (kirovGenus X) → ℂ) →ₗ[ℂ] (Fin (kirovGenus Y) → ℂ)) from by
    rw [ambientTrace_eq_zero_of_const f hf hconst]; rfl]
  ext v i
  simp

/-- **Algebraic bridge (projection formula, period level).** The `i`-th component of
the genuine Jacobian pullback `ambientPullbackJac f hf (periodVec δ)` is the line
integral of the trace of the `i`-th basis form along `δ`:
`(Tᵀ · periodVec δ)ᵢ = ∫_δ traceFormTotal f hf (ωᵢ^X)`.

Pure linear algebra + linearity of `lineIntegral`, dual to `periodVec_pushforward`
(`PeriodLattice.lean`). With `w := (ambientIso Y).symm (traceFormTotal f hf ωᵢ^X)`:
the matrix entry `Tᵀ i j = (ambientTrace f hf eᵢ^X) j = w j` (`ambientTrace` is the
`ambientIso`-conjugate of `traceFormTotal`), so the LHS is `∑ⱼ wⱼ (periodVec δ)ⱼ`;
and `traceFormTotal f hf ωᵢ^X = ambientIso Y w = ∑ⱼ wⱼ • ωⱼ^Y`, so the RHS line
integral is `∑ⱼ wⱼ ∫_δ ωⱼ^Y = ∑ⱼ wⱼ (periodVec δ)ⱼ` by linearity. The integrability
hypothesis is the per-basis-form regularity of a closed smooth loop. -/
theorem ambientPullbackJac_periodVec_apply_eq_lineIntegral_traceFormTotal
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (δ : ℝ → Y) (i : Fin (kirovGenus X))
    (hint_Y : ∀ j : Fin (kirovGenus Y), IntervalIntegrable
      (fun t => (periodBasisForm Y j).toFun (δ t) (pathSpeed δ t)) MeasureTheory.volume 0 1) :
    ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf (periodVec δ) i =
      lineIntegral (traceFormTotal f hf (periodBasisForm X i)) δ := by
  classical
  set w := (ambientIso Y).symm (traceFormTotal f hf (periodBasisForm X i)) with hw_def
  -- The matrix-transpose action `(Tᵀ · periodVec δ)ᵢ = ∑ⱼ wⱼ (periodVec δ)ⱼ`.
  have hLHS : ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf (periodVec δ) i
      = ∑ j, w j * (periodVec δ) j := by
    show (Matrix.transpose (LinearMap.toMatrix (Pi.basisFun ℂ (Fin (kirovGenus X)))
        (Pi.basisFun ℂ (Fin (kirovGenus Y))) (ambientTrace f hf).toLinearMap)).mulVecLin
        (periodVec δ) i = ∑ j, w j * (periodVec δ) j
    rw [Matrix.mulVecLin_apply]
    show ∑ j, (Matrix.transpose (LinearMap.toMatrix _ _ _)) i j * (periodVec δ) j
        = ∑ j, w j * (periodVec δ) j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    show (LinearMap.toMatrix (Pi.basisFun ℂ (Fin (kirovGenus X)))
      (Pi.basisFun ℂ (Fin (kirovGenus Y))) (ambientTrace f hf).toLinearMap) j i = w j
    rw [LinearMap.toMatrix_apply]
    show ((Pi.basisFun ℂ (Fin (kirovGenus Y))).repr
      (ambientTrace f hf (Pi.basisFun ℂ (Fin (kirovGenus X)) i))) j = w j
    rw [Pi.basisFun_repr]
    -- `ambientTrace f hf eᵢ^X = w` (ambientIso-conjugate of traceFormTotal).
    have hat : ambientTrace (gX := kirovGenus X) (gY := kirovGenus Y) f hf
        (Pi.basisFun ℂ (Fin (kirovGenus X)) i) = w := by
      rw [hw_def]
      unfold ambientTrace
      set_option linter.unusedSimpArgs false in simp only [dif_pos rfl]
      rfl
    rw [hat]
  -- The line integral of the trace form `= ∑ⱼ wⱼ (periodVec δ)ⱼ`.
  have hRHS : lineIntegral (traceFormTotal f hf (periodBasisForm X i)) δ
      = ∑ j, w j * (periodVec δ) j := by
    have h_iso : traceFormTotal f hf (periodBasisForm X i) = ambientIso Y w := by
      rw [hw_def]; exact ((ambientIso Y).apply_symm_apply _).symm
    rw [h_iso]
    have h_iso_sum : ambientIso Y w = ∑ j, w j • periodBasisForm Y j := by
      have h_w_decomp : w = ∑ j, w j • Pi.basisFun ℂ (Fin (kirovGenus Y)) j := by
        have := pi_eq_sum_univ' w
        convert this using 2
        simp [Pi.basisFun_apply]
      conv_lhs => rw [h_w_decomp, map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul]; rfl
    rw [h_iso_sum]
    -- `lineIntegral (∑ⱼ wⱼ • ωⱼ^Y) δ = ∑ⱼ wⱼ ∫_δ ωⱼ^Y = ∑ⱼ wⱼ (periodVec δ)ⱼ`.
    have h_sum_lineIntegral : lineIntegral (∑ j, w j • periodBasisForm Y j) δ =
        ∑ j, w j * lineIntegral (periodBasisForm Y j) δ := by
      unfold lineIntegral
      have h_pw : ∀ t : ℝ,
          (∑ j, w j • periodBasisForm Y j).toFun (δ t) (pathSpeed δ t) =
            ∑ j, w j * (periodBasisForm Y j).toFun (δ t) (pathSpeed δ t) := by
        intro t
        induction (Finset.univ : Finset (Fin (kirovGenus Y))) using Finset.induction_on with
        | empty =>
          rw [Finset.sum_empty, Finset.sum_empty]
          show (0 : HolomorphicOneForms Y).toFun (δ t) (pathSpeed δ t) = 0
          rfl
        | @insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          show ((w a • periodBasisForm Y a) + ∑ j ∈ s, w j • periodBasisForm Y j).toFun (δ t)
              (pathSpeed δ t) = _
          rw [show ((w a • periodBasisForm Y a) + ∑ j ∈ s, w j • periodBasisForm Y j).toFun (δ t) =
              (w a • periodBasisForm Y a).toFun (δ t) +
                (∑ j ∈ s, w j • periodBasisForm Y j).toFun (δ t) from rfl,
            ContinuousLinearMap.add_apply, ih]
          rfl
      simp_rw [h_pw]
      rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
        (f := fun j t => w j * (periodBasisForm Y j).toFun (δ t) (pathSpeed δ t))
        (fun j _ => (hint_Y j).const_mul (w j))]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact intervalIntegral.integral_const_mul _ _
    rw [h_sum_lineIntegral]
    rfl
  rw [hLHS, hRHS]

/-! ## §3 The preimage cycle and lattice preservation

Relocated here from `PeriodLattice.lean` (whose covering / fibre-finiteness
infrastructure is still imported via `TraceForm`): these are the parts of the §3
lift chain that reference the **genuine** `ambientPullbackJac` defined above. The
`PreimageCycle.pullback_eq` field is the projection-formula identity
`Tᵀ·periodVec δ = ∑ coeffs·periodVec loopsᵢ`. -/

/-- A **preimage cycle** witnessing the trace identity: a finite
ℤ-combination of closed smooth loops in `X` whose period-vector sum
realizes the genuine Jacobian pullback `ambientPullbackJac f hf (periodVec δ)`.

Classically: for non-constant holomorphic `f : X → Y` between compact
Riemann surfaces, `f` is a branched cover of some degree `d ≥ 1`,
and the set-theoretic preimage `f⁻¹(δ)` of a loop `δ` (avoiding
branch points) is `d` disjoint closed loops in `X` whose signed sum
realizes `Tᵀ (periodVec δ)` (Forster §10.11).

Defining `PreimageCycle` as a bundle of (loops + coefficients +
pullback/pushforward equations) lets us isolate the classical content: the theorem
`ambientPullbackJac_periodVec_mem_truePeriodLattice_of_preimageCycle` is
real and purely algebraic; only *producing* a `PreimageCycle` for
each non-constant `f, δ` is content-gated. -/
structure PreimageCycle (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (δ : ℝ → Y) where
  /-- Number of lifts. -/
  n : ℕ
  /-- The lifted closed loops in X. -/
  loops : Fin n → ℝ → X
  /-- Each lift is a closed smooth loop. -/
  loops_smooth : ∀ i, IsClosedSmoothLoop (loops i)
  /-- Integer coefficients (signed lifts / branching multiplicities). -/
  coeffs : Fin n → ℤ
  /-- Sheet count of the cover (classically `= deg f`). -/
  sheets : ℕ
  /-- **Pullback identity** (projection formula): the genuine Jacobian pullback
  `ambientPullbackJac` (= `Tᵀ`) on `periodVec δ` equals the ℤ-combination of the
  lifts' period vectors `periodVec(Γ) = Tᵀ·periodVec δ`. -/
  pullback_eq : ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf (periodVec δ) =
    ∑ i, coeffs i • periodVec (loops i)
  /-- **Pushforward identity** (`f∘Γ = sheets·δ` on periods): the lifts project to
  `δ` with multiplicities summing to `sheets`. Feeds the S8 connection keystone. -/
  pushforward_eq : ∑ i, coeffs i • periodVec (f ∘ loops i) =
    (sheets : ℤ) • periodVec δ

/-- **Pullback identity — algebraic reduction.** Given a `PreimageCycle`
witness for `(f, δ)`, the pulled-back period vector
`ambientPullbackJac (periodVec δ)` lies in `truePeriodLattice X`: each
`periodVec` of a closed smooth loop is in the lattice, and the
lattice is closed under ℤ-linear combinations. -/
theorem ambientPullbackJac_periodVec_mem_truePeriodLattice_of_preimageCycle
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (δ : ℝ → Y) (c : PreimageCycle f hf δ) :
    ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf (periodVec δ) ∈
      truePeriodLattice X := by
  rw [c.pullback_eq]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ (c.coeffs i)
      (periodVec_mem_truePeriodLattice_of_closed _ (c.loops_smooth i))

/-! ### Off-branch detour — per-piece geometric kernel

The chart-coordinate image of the branch locus inside one chart is finite (the branch locus is
finite), so the proven planar two-segment dodge (`OfCurveSkeleton.exists_relay_dodge_finite`) gives a
relay point dodging it; pulling the two segments back through the chart and gluing the two flat-ended
general-anchor chart paths (`OfCurveSkeleton.ChartBallPathSmooth3`) produces a flat-ended off-branch
smooth path between the two (off-branch) piece endpoints, whose chart image stays in the chosen
sub-ball. This is the per-piece replacement arc used to build `δ'`. -/

/-- The chart-coordinate image of the branch locus inside the chart at `w` is finite. -/
lemma finite_chartImage_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ y, f y = y₀) (w : Y) :
    ((chartAt (H := ℂ) w) '' (branchLocus f ∩ (chartAt (H := ℂ) w).source)).Finite :=
  ((finite_branchLocus_of_nonconstant f hf hnonconst).inter_of_left _).image _

/-- Off-branch transfer: a chart-target point off the chart-image of the branch locus pulls back to
a point off the branch locus. -/
lemma chartSymm_notMem_branchLocus {f : X → Y} {w : Y} {v : ℂ}
    (hv_target : v ∈ (chartAt (H := ℂ) w).target)
    (hvB : v ∉ (chartAt (H := ℂ) w) '' (branchLocus f ∩ (chartAt (H := ℂ) w).source)) :
    (chartAt (H := ℂ) w).symm v ∉ branchLocus f := by
  intro hmem
  apply hvB
  refine ⟨(chartAt (H := ℂ) w).symm v, ⟨hmem, (chartAt (H := ℂ) w).map_target hv_target⟩, ?_⟩
  exact (chartAt (H := ℂ) w).right_inv hv_target

/-- **Per-piece off-branch detour (geometric kernel).** Given a chart anchor `w`, a sub-ball
`Metric.ball c r ⊆ (chartAt w).target`, and two points `P, Q` off `branchLocus f` whose chart
images lie in the sub-ball, there is a flat-ended smooth path `γ : P → Q` that
* avoids `branchLocus f` on all of `[0,1]`,
* stays in `(chartAt w).source`,
* has chart-`w` image inside `Metric.ball c r` on `[0,1]`,
* has matching chart endpoints `chart (γ 0) = chart P`, `chart (γ 1) = chart Q`,
* has vanishing endpoint velocities.

The relay is `OfCurveSkeleton.exists_relay_dodge_finite` (planar dodge of the finite
chart-image of the branch locus); the arc is the concatenation of two
`OfCurveSkeleton.ChartBallPathSmooth3` hops `P → relay`, `relay → Q`. -/
lemma exists_offBranch_detour_piece (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ y, f y = y₀)
    (w P Q : Y) (c : ℂ) (r : ℝ)
    (hball : Metric.ball c r ⊆ (chartAt (H := ℂ) w).target)
    (hP_src : P ∈ (chartAt (H := ℂ) w).source) (hQ_src : Q ∈ (chartAt (H := ℂ) w).source)
    (hP_ball : (chartAt (H := ℂ) w) P ∈ Metric.ball c r)
    (hQ_ball : (chartAt (H := ℂ) w) Q ∈ Metric.ball c r)
    (hP_off : P ∉ branchLocus f) (hQ_off : Q ∉ branchLocus f) :
    ∃ γ : ℝ → Y, IsSmoothPath P Q γ ∧
      (∀ t : ℝ, γ t ∉ branchLocus f) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, (chartAt (H := ℂ) w) (γ t) ∈ Metric.ball c r) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ (chartAt (H := ℂ) w).source) ∧
      pathSpeed γ 0 = 0 ∧ pathSpeed γ 1 = 0 := by
  classical
  set e := chartAt (H := ℂ) w with he
  set B : Set ℂ := e '' (branchLocus f ∩ e.source) with hB
  have hBfin : B.Finite := finite_chartImage_branchLocus f hf hnonconst w
  -- chart images of P, Q are off B.
  have hPB : e P ∉ B := by
    intro hmem; exact hP_off (by
      obtain ⟨y, ⟨hy_br, hy_src⟩, hy_eq⟩ := hmem
      have : y = P := e.injOn hy_src hP_src hy_eq
      rwa [this] at hy_br)
  have hQB : e Q ∉ B := by
    intro hmem; exact hQ_off (by
      obtain ⟨y, ⟨hy_br, hy_src⟩, hy_eq⟩ := hmem
      have : y = Q := e.injOn hy_src hQ_src hy_eq
      rwa [this] at hy_br)
  -- planar dodge: relay m ∈ ball, segments in ball off B.
  obtain ⟨m, hm_ball, hseg1_ball, hseg2_ball, hseg1_off, hseg2_off⟩ :=
    OfCurveSkeleton.exists_relay_dodge_finite B hBfin c r (e P) (e Q) hP_ball hQ_ball hPB hQB
  set mPt : Y := e.symm m with hmPt
  have hm_target : m ∈ e.target := hball hm_ball
  have hmPt_src : mPt ∈ e.source := e.map_target hm_target
  have he_mPt : e mPt = m := e.right_inv hm_target
  -- `m` itself is off `B` (it is the shared endpoint of both off-`B` segments).
  have hmB : m ∉ B := by
    have hm_in : m ∈ segment ℝ (e P) m := right_mem_segment ℝ (e P) m
    exact fun hmem => (Set.disjoint_left.mp hseg1_off hm_in) hmem
  have hmPt_off : mPt ∉ branchLocus f := chartSymm_notMem_branchLocus hm_target hmB
  -- Segment-membership of the affine combination (real-smul ↔ complex-mult form).
  have hsmem : ∀ (a b : ℂ) (σ : ℝ), σ ∈ Set.Icc (0:ℝ) 1 →
      (1 - (σ : ℂ)) * a + (σ : ℂ) * b ∈ segment ℝ a b := by
    intro a b σ hσ
    refine ⟨1 - σ, σ, by linarith [hσ.2], hσ.1, by ring, ?_⟩
    rw [Complex.real_smul, Complex.real_smul]; push_cast; ring
  -- Chart-ball hypotheses for the two A3 hops (segment ⊆ ball ⊆ target).
  have hball1 : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * e P + (s : ℂ) * e mPt) ∈ e.target := by
    intro s hs
    refine hball (hseg1_ball ?_)
    rw [he_mPt]; exact hsmem (e P) m s hs
  have hball2 : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * e mPt + (s : ℂ) * e Q) ∈ e.target := by
    intro s hs
    refine hball (hseg2_ball ?_)
    rw [he_mPt]; exact hsmem m (e Q) s hs
  set γ₁ : ℝ → Y := OfCurveSkeleton.ChartBallPathSmooth3 w P mPt with hγ₁
  set γ₂ : ℝ → Y := OfCurveSkeleton.ChartBallPathSmooth3 w mPt Q with hγ₂
  have hsp1 : IsSmoothPath P mPt γ₁ :=
    OfCurveSkeleton.isSmoothPath_ChartBallPathSmooth3 w P mPt hP_src hmPt_src hball1
  have hsp2 : IsSmoothPath mPt Q γ₂ :=
    OfCurveSkeleton.isSmoothPath_ChartBallPathSmooth3 w mPt Q hmPt_src hQ_src hball2
  have hv1_0 : pathSpeed γ₁ 0 = 0 :=
    OfCurveSkeleton.pathSpeed_ChartBallPathSmooth3_zero w P mPt hball1
  have hv1_1 : pathSpeed γ₁ 1 = 0 :=
    OfCurveSkeleton.pathSpeed_ChartBallPathSmooth3_one w P mPt hball1
  have hv2_0 : pathSpeed γ₂ 0 = 0 :=
    OfCurveSkeleton.pathSpeed_ChartBallPathSmooth3_zero w mPt Q hball2
  have hv2_1 : pathSpeed γ₂ 1 = 0 :=
    OfCurveSkeleton.pathSpeed_ChartBallPathSmooth3_one w mPt Q hball2
  set γ : ℝ → Y := Jacobians.concat γ₁ γ₂ with hγ
  -- Per-hop chart-image-in-ball (all of ℝ, since smoothStep01 clamps into [0,1]).
  have hγ₁_ball : ∀ t : ℝ, e (γ₁ t) ∈ Metric.ball c r := by
    intro t
    have hσ := Jacobians.smoothStep01_mem_unit t
    rw [hγ₁, OfCurveSkeleton.chart_ChartBallPathSmooth3_eq w P mPt t (hball1 _ hσ), he_mPt]
    exact hseg1_ball (hsmem (e P) m _ hσ)
  have hγ₂_ball : ∀ t : ℝ, e (γ₂ t) ∈ Metric.ball c r := by
    intro t
    have hσ := Jacobians.smoothStep01_mem_unit t
    rw [hγ₂, OfCurveSkeleton.chart_ChartBallPathSmooth3_eq w mPt Q t (hball2 _ hσ), he_mPt]
    exact hseg2_ball (hsmem m (e Q) _ hσ)
  -- Per-hop in chart source (all of ℝ).
  have hγ₁_src : ∀ t : ℝ, γ₁ t ∈ e.source := fun t =>
    OfCurveSkeleton.ChartBallPathSmooth3_mem_source w P mPt t hball1
  have hγ₂_src : ∀ t : ℝ, γ₂ t ∈ e.source := fun t =>
    OfCurveSkeleton.ChartBallPathSmooth3_mem_source w mPt Q t hball2
  -- Per-hop off-branch (all of ℝ): chart image is a segment point off B.
  have hγ₁_off : ∀ t : ℝ, γ₁ t ∉ branchLocus f := by
    intro t
    have hσ := Jacobians.smoothStep01_mem_unit t
    have hchart : e (γ₁ t) ∈ segment ℝ (e P) m := by
      rw [hγ₁, OfCurveSkeleton.chart_ChartBallPathSmooth3_eq w P mPt t (hball1 _ hσ), he_mPt]
      exact hsmem (e P) m _ hσ
    have hnotB : e (γ₁ t) ∉ B := fun hmem => (Set.disjoint_left.mp hseg1_off hchart) hmem
    have := chartSymm_notMem_branchLocus (f := f) (w := w) (e.map_source (hγ₁_src t)) hnotB
    rwa [e.left_inv (hγ₁_src t)] at this
  have hγ₂_off : ∀ t : ℝ, γ₂ t ∉ branchLocus f := by
    intro t
    have hσ := Jacobians.smoothStep01_mem_unit t
    have hchart : e (γ₂ t) ∈ segment ℝ m (e Q) := by
      rw [hγ₂, OfCurveSkeleton.chart_ChartBallPathSmooth3_eq w mPt Q t (hball2 _ hσ), he_mPt]
      exact hsmem m (e Q) _ hσ
    have hnotB : e (γ₂ t) ∉ B := fun hmem => (Set.disjoint_left.mp hseg2_off hchart) hmem
    have := chartSymm_notMem_branchLocus (f := f) (w := w) (e.map_source (hγ₂_src t)) hnotB
    rwa [e.left_inv (hγ₂_src t)] at this
  refine ⟨γ, hsp1.concat hsp2 hv1_1 hv2_0, ?_, ?_, ?_, ?_, ?_⟩
  · -- off-branch for all t, splitting at the concat junction.
    intro t
    by_cases ht : t ≤ 1/2
    · rw [hγ, Jacobians.concat_apply_left _ _ ht]; exact hγ₁_off _
    · rw [hγ, Jacobians.concat_apply_right _ _ ht]; exact hγ₂_off _
  · -- chart-image-in-ball on [0,1].
    intro t _
    by_cases ht : t ≤ 1/2
    · rw [hγ, Jacobians.concat_apply_left _ _ ht]; exact hγ₁_ball _
    · rw [hγ, Jacobians.concat_apply_right _ _ ht]; exact hγ₂_ball _
  · -- in chart source on [0,1].
    intro t _
    by_cases ht : t ≤ 1/2
    · rw [hγ, Jacobians.concat_apply_left _ _ ht]; exact hγ₁_src _
    · rw [hγ, Jacobians.concat_apply_right _ _ ht]; exact hγ₂_src _
  · -- pathSpeed γ 0 = 0.
    have h0uIcc : (0:ℝ) ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨le_refl _, zero_le_one⟩
    have hd : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ₁ (2 * 0))).toFun ∘ γ₁) (2 * 0) := by
      rw [show (2:ℝ)*0 = 0 from by norm_num]; exact hsp1.diff 0 h0uIcc
    rw [hγ, Jacobians.pathSpeed_concat_left γ₁ γ₂ 0 (by norm_num) hd,
      show (2:ℝ)*0 = 0 from by norm_num, hv1_0, mul_zero]
  · -- pathSpeed γ 1 = 0.
    have h1uIcc : (1:ℝ) ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨zero_le_one, le_refl _⟩
    have hd : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ₂ (2 * 1 - 1))).toFun ∘ γ₂) (2 * 1 - 1) := by
      rw [show (2:ℝ)*1-1 = 1 from by norm_num]; exact hsp2.diff 1 h1uIcc
    rw [hγ, Jacobians.pathSpeed_concat_right γ₁ γ₂ 1 (by norm_num) hd,
      show (2:ℝ)*1-1 = 1 from by norm_num, hv2_1, mul_zero]

/-- A nonempty open subset of `Y` (a complex `1`-manifold) is infinite: locally homeomorphic to a
nonempty open subset of `ℂ`, which is infinite. (Local copy of `Jacobians.infinite_of_isOpen_nonempty`
from `DegreeOneSphere.lean`, which is downstream of this file and so cannot be imported here.) -/
private theorem infinite_of_isOpen_nonempty_local {W : Set Y} (hW : IsOpen W) (hne : W.Nonempty) :
    W.Infinite := by
  obtain ⟨y₀, hy₀⟩ := hne
  set c : OpenPartialHomeomorph Y ℂ := chartAt ℂ y₀ with hc
  set U : Set Y := c.source ∩ W with hU
  have hUopen : IsOpen U := c.open_source.inter hW
  have hy₀U : y₀ ∈ U := ⟨mem_chart_source ℂ y₀, hy₀⟩
  have hcU_open : IsOpen (c '' U) := c.isOpen_image_of_subset_source hUopen Set.inter_subset_left
  have hcy₀ : c y₀ ∈ c '' U := ⟨y₀, hy₀U, rfl⟩
  haveI : Filter.NeBot (𝓝[≠] (c y₀)) := Module.punctured_nhds_neBot ℂ ℂ (c y₀)
  have hcU_inf : (c '' U).Infinite := infinite_of_mem_nhds (c y₀) (hcU_open.mem_nhds hcy₀)
  have hsub : c '' U ⊆ c.target := by rintro _ ⟨x, hx, rfl⟩; exact c.map_source hx.1
  have himg : (c.symm '' (c '' U)).Infinite := hcU_inf.image (c.symm.injOn.mono hsub)
  refine himg.mono ?_
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  rw [c.left_inv hx.1]; exact hx.2

/-- Removing a finite set from a nonempty open subset of `Y` leaves a point. (Local copy of
`Jacobians.exists_mem_open_notMem_finite`.) -/
private theorem exists_mem_open_notMem_finite_local {W C : Set Y}
    (hW : IsOpen W) (hne : W.Nonempty) (hC : C.Finite) : ∃ y ∈ W, y ∉ C := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  exact (infinite_of_isOpen_nonempty_local hW hne) (hC.subset (fun y hy => h y hy))

/-- **[OVERLAP CONNECTOR — the off-branch breakpoint perturbation].** Let `P` be a point lying in
the sources of two chart anchors `w₁, w₂` (the anchors of two adjacent cover pieces sharing the
breakpoint `P = δ(k/n)`), with chart-image inside each anchor's sub-ball `ball (c_j) (r_j) ⊆
target(w_j)`. Then there is a point `p` **off** `branchLocus f`, together with a flat-ended smooth
**connecting path** `c : P → p`, whose chart-image stays inside *both* sub-balls (and whose body
stays in both chart sources) on all of `[0,1]`.

This is the perturbation that the false `exists_offBranch_subBallChartCover` was trying (and failing)
to do at the level of `δ` itself: `δ(k/n)` may sit on the branch locus, but we dodge to a nearby
off-branch `p` and record the short connecting path `c`. Because `c` lies in the *overlap* of the two
sub-balls, the line integral of any period form along `c` is the **same** primitive-difference whether
computed in ball `1` or ball `2` — which is exactly the intrinsic correction term that makes the
telescope in `exists_loop_off_branchLocus` close.

Construction: a small ball `D` around `chart₂ P` inside `ball (c₂) (r₂)` whose `chart₂.symm`-image is
in `source w₁` with `chart₁`-image in `ball (c₁) (r₁)` (continuity of the transition `chart₁ ∘
chart₂.symm` at `chart₂ P`, where `chart₁ P ∈ ball (c₁) (r₁)` is open). Any `p` with `chart₂ p ∈ D`
then lies in both balls; pick `p ∈ chart₂.symm '' D` off the finite `branchLocus` (open-minus-finite).
The connector is the chart-`2` straight segment `ChartBallPathSmooth3 w₂ P p`, confined to the convex
`D` (so to ball `2`), hence to ball `1` via the transition. -/
lemma exists_offBranch_overlap_connector (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ y, f y = y₀)
    (w₁ w₂ P : Y) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ)
    (_hball₁ : Metric.ball c₁ r₁ ⊆ (chartAt (H := ℂ) w₁).target)
    (hball₂ : Metric.ball c₂ r₂ ⊆ (chartAt (H := ℂ) w₂).target)
    (hP₁_src : P ∈ (chartAt (H := ℂ) w₁).source) (hP₂_src : P ∈ (chartAt (H := ℂ) w₂).source)
    (hP₁_ball : (chartAt (H := ℂ) w₁) P ∈ Metric.ball c₁ r₁)
    (hP₂_ball : (chartAt (H := ℂ) w₂) P ∈ Metric.ball c₂ r₂) :
    ∃ (p : Y) (c : ℝ → Y),
      p ∉ branchLocus f ∧ IsSmoothPath P p c ∧
      pathSpeed c 0 = 0 ∧ pathSpeed c 1 = 0 ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, c t ∈ (chartAt (H := ℂ) w₁).source) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, c t ∈ (chartAt (H := ℂ) w₂).source) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, (chartAt (H := ℂ) w₁) (c t) ∈ Metric.ball c₁ r₁) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, (chartAt (H := ℂ) w₂) (c t) ∈ Metric.ball c₂ r₂) := by
  classical
  set e₁ := chartAt (H := ℂ) w₁ with he₁
  set e₂ := chartAt (H := ℂ) w₂ with he₂
  -- The transition `g := e₁ ∘ e₂.symm` is continuous at `e₂ P` and sends it into `ball c₁ r₁`.
  -- `e₂.symm` is continuous at `e₂ P` (which is in `e₂.target`).
  have hP₂_tgt : e₂ P ∈ e₂.target := e₂.map_source hP₂_src
  have he₂symm_at : ContinuousAt e₂.symm (e₂ P) := e₂.continuousAt_symm hP₂_tgt
  have he₂symm_P : e₂.symm (e₂ P) = P := e₂.left_inv hP₂_src
  -- `e₁` is continuous at `P` (within nothing special — use continuousAt on its source).
  have he₁_at : ContinuousAt e₁ P := e₁.continuousAt hP₁_src
  -- Build the small ball `D = ball (e₂ P) ρ` with the three confinement properties.
  -- (a) `e₂.symm` maps a nbhd of `e₂ P` into `e₁.source`.
  have hpre₁_src : e₂.symm ⁻¹' e₁.source ∈ nhds (e₂ P) := by
    have : e₁.source ∈ nhds (e₂.symm (e₂ P)) := by rw [he₂symm_P]; exact e₁.open_source.mem_nhds hP₁_src
    exact he₂symm_at this
  -- (b) `g = e₁ ∘ e₂.symm` maps a nbhd of `e₂ P` into `ball c₁ r₁`.
  have hg_at : ContinuousAt (fun v => e₁ (e₂.symm v)) (e₂ P) := by
    have hcomp : ContinuousAt e₁ (e₂.symm (e₂ P)) := by rw [he₂symm_P]; exact he₁_at
    exact hcomp.comp he₂symm_at
  have hpre₁_ball : e₂.symm ⁻¹' (e₁ ⁻¹' Metric.ball c₁ r₁) ∈ nhds (e₂ P) := by
    have hball₁_nhds : Metric.ball c₁ r₁ ∈ nhds (e₁ (e₂.symm (e₂ P))) := by
      rw [he₂symm_P]; exact Metric.isOpen_ball.mem_nhds hP₁_ball
    have := hg_at hball₁_nhds
    exact this
  -- (c) `e₂ P` is in the open `ball c₂ r₂`.
  have hball₂_nhds : Metric.ball c₂ r₂ ∈ nhds (e₂ P) := Metric.isOpen_ball.mem_nhds hP₂_ball
  -- Intersect the three neighborhoods; extract a ball `D = ball (e₂ P) ρ` inside all of them.
  have hInter : (e₂.symm ⁻¹' e₁.source) ∩ (e₂.symm ⁻¹' (e₁ ⁻¹' Metric.ball c₁ r₁)) ∩
      Metric.ball c₂ r₂ ∈ nhds (e₂ P) :=
    Filter.inter_mem (Filter.inter_mem hpre₁_src hpre₁_ball) hball₂_nhds
  obtain ⟨ρ, hρpos, hρ_sub⟩ := Metric.mem_nhds_iff.mp hInter
  set D : Set ℂ := Metric.ball (e₂ P) ρ with hD
  -- Properties of D, decoded from hρ_sub.
  have hD_src₁ : ∀ v ∈ D, e₂.symm v ∈ e₁.source := fun v hv => (hρ_sub hv).1.1
  have hD_ball₁ : ∀ v ∈ D, e₁ (e₂.symm v) ∈ Metric.ball c₁ r₁ := fun v hv => (hρ_sub hv).1.2
  have hD_ball₂ : ∀ v ∈ D, v ∈ Metric.ball c₂ r₂ := fun v hv => (hρ_sub hv).2
  have hD_tgt₂ : ∀ v ∈ D, v ∈ e₂.target := fun v hv => hball₂ (hD_ball₂ v hv)
  have hD_src₂ : ∀ v ∈ D, e₂.symm v ∈ e₂.source := fun v hv => e₂.map_target (hD_tgt₂ v hv)
  have hP_in_D : e₂ P ∈ D := Metric.mem_ball_self hρpos
  -- The open set `W := e₂.symm '' D` in Y, containing P, off which we dodge the finite branch locus.
  have hD_open : IsOpen D := Metric.isOpen_ball
  have hD_sub_tgt : D ⊆ e₂.target := fun v hv => hD_tgt₂ v hv
  have hW_open : IsOpen (e₂.symm '' D) :=
    e₂.symm.isOpen_image_of_subset_source hD_open (by rw [e₂.symm_source]; exact hD_sub_tgt)
  have hW_ne : (e₂.symm '' D).Nonempty := ⟨P, e₂ P, hP_in_D, he₂symm_P⟩
  obtain ⟨p, hp_W, hp_off⟩ :=
    exists_mem_open_notMem_finite_local hW_open hW_ne
      (finite_branchLocus_of_nonconstant f hf hnonconst)
  obtain ⟨vp, hvp_D, hvp_eq⟩ := hp_W
  -- `e₂ p = vp ∈ D`.
  have hp_src₂ : p ∈ e₂.source := by rw [← hvp_eq]; exact hD_src₂ vp hvp_D
  have he₂p : e₂ p = vp := by rw [← hvp_eq]; exact e₂.right_inv (hD_tgt₂ vp hvp_D)
  have hp_D : e₂ p ∈ D := by rw [he₂p]; exact hvp_D
  -- The connector: chart-2 straight segment P → p.
  set c : ℝ → Y := OfCurveSkeleton.ChartBallPathSmooth3 w₂ P p with hc
  -- chart-2 segment confinement: chart₂(c t) is a segment point of [chart₂ P, chart₂ p] ⊆ D.
  have hseg_D : ∀ σ : ℝ, σ ∈ Set.Icc (0:ℝ) 1 →
      (1 - (σ : ℂ)) * e₂ P + (σ : ℂ) * e₂ p ∈ D := by
    intro σ hσ
    have hmem : (1 - (σ : ℂ)) * e₂ P + (σ : ℂ) * e₂ p ∈ segment ℝ (e₂ P) (e₂ p) := by
      refine ⟨1 - σ, σ, by linarith [hσ.2], hσ.1, by ring, ?_⟩
      rw [Complex.real_smul, Complex.real_smul]; push_cast; ring
    exact (convex_ball (e₂ P) ρ).segment_subset hP_in_D hp_D hmem
  -- chart-ball hypothesis for the ChartBallPathSmooth3 machinery (segment ⊆ D ⊆ target₂).
  have hcb : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * e₂ P + (s : ℂ) * e₂ p) ∈ e₂.target :=
    fun s hs => hD_tgt₂ _ (hseg_D s hs)
  -- chart₂(c t) ∈ D, source₂, smoothness, flatness.
  have hc_chart₂ : ∀ t : ℝ, e₂ (c t) ∈ D := by
    intro t
    have hσ := Jacobians.smoothStep01_mem_unit t
    rw [hc, OfCurveSkeleton.chart_ChartBallPathSmooth3_eq w₂ P p t (hcb _ hσ)]
    exact hseg_D _ hσ
  have hc_src₂ : ∀ t : ℝ, c t ∈ e₂.source := fun t =>
    OfCurveSkeleton.ChartBallPathSmooth3_mem_source w₂ P p t hcb
  have hsp : IsSmoothPath P p c :=
    OfCurveSkeleton.isSmoothPath_ChartBallPathSmooth3 w₂ P p hP₂_src hp_src₂ hcb
  have hv0 : pathSpeed c 0 = 0 := OfCurveSkeleton.pathSpeed_ChartBallPathSmooth3_zero w₂ P p hcb
  have hv1 : pathSpeed c 1 = 0 := OfCurveSkeleton.pathSpeed_ChartBallPathSmooth3_one w₂ P p hcb
  -- chart₂(c t) ∈ ball c₂ r₂ via D.
  have hc_ball₂ : ∀ t ∈ Set.Icc (0:ℝ) 1, e₂ (c t) ∈ Metric.ball c₂ r₂ :=
    fun t _ => hD_ball₂ _ (hc_chart₂ t)
  -- Transfer to chart-1: c t ∈ source₁ and chart₁(c t) ∈ ball c₁ r₁, using e₂.symm (e₂ (c t)) = c t.
  have he₂symm_ct : ∀ t : ℝ, e₂.symm (e₂ (c t)) = c t := fun t => e₂.left_inv (hc_src₂ t)
  have hc_src₁ : ∀ t ∈ Set.Icc (0:ℝ) 1, c t ∈ e₁.source := by
    intro t _
    have := hD_src₁ _ (hc_chart₂ t)
    rwa [he₂symm_ct t] at this
  have hc_ball₁ : ∀ t ∈ Set.Icc (0:ℝ) 1, e₁ (c t) ∈ Metric.ball c₁ r₁ := by
    intro t _
    have := hD_ball₁ _ (hc_chart₂ t)
    rwa [he₂symm_ct t] at this
  exact ⟨p, c, hp_off, hsp, hv0, hv1, hc_src₁, fun t _ => hc_src₂ t, hc_ball₁, hc_ball₂⟩

/-- **[BATCH of off-branch overlap connectors, one per breakpoint].** From the proven sub-ball cover
of `δ` (uniform `n`-partition, per-piece anchor `x k`, sub-ball `ball (c k) (r k) ⊆ target(x k)`,
confining `δ`'s chart-image on piece `k`), produce, for every breakpoint `k : Fin n` (sitting at
parameter `k/n`), an off-branch point `p k` and a flat-ended smooth connector `cc k : δ(k/n) → p k`
whose body and chart-image are confined to *both* adjacent sub-balls: the "this" ball `k` (left end of
piece `k`) and the "previous" ball `k-1` (right end of piece `k-1`, with the wrap `0-1 = n-1` handled
via `δ 1 = δ 0`).

The endpoint `p k` thus lies in `source(x k) ∩ source(x (k-1))` with chart-images in both balls — so
adjacent detours can be built between the `p`'s — and the connector lies in the overlap, so the line
integral of any period form along `cc k` is the same primitive-difference in either ball (the
intrinsic correction term `corr` of the telescope). Single application of
`exists_offBranch_overlap_connector` per breakpoint. -/
lemma exists_overlap_connectors (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ y, f y = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ)
    (n : ℕ) [NeZero n] (hn : 0 < n) (x : Fin n → Y) (c : Fin n → ℂ) (r : Fin n → ℝ)
    (hconf : ∀ (k : Fin n) (s : ℝ), (k : ℝ) / n ≤ s → s ≤ ((k : ℝ) + 1) / n →
      Metric.ball (c k) (r k) ⊆ (chartAt (H := ℂ) (x k)).target ∧
      δ s ∈ (chartAt (H := ℂ) (x k)).source ∧
      (chartAt (H := ℂ) (x k)) (δ s) ∈ Metric.ball (c k) (r k)) :
    ∃ (p : Fin n → Y) (cc : Fin n → ℝ → Y),
      ∀ k : Fin n,
        p k ∉ branchLocus f ∧
        IsSmoothPath (δ ((k : ℝ) / n)) (p k) (cc k) ∧
        pathSpeed (cc k) 0 = 0 ∧ pathSpeed (cc k) 1 = 0 ∧
        (∀ t ∈ Set.Icc (0:ℝ) 1, cc k t ∈ (chartAt (H := ℂ) (x (k - 1))).source) ∧
        (∀ t ∈ Set.Icc (0:ℝ) 1, cc k t ∈ (chartAt (H := ℂ) (x k)).source) ∧
        (∀ t ∈ Set.Icc (0:ℝ) 1, (chartAt (H := ℂ) (x (k - 1))) (cc k t) ∈ Metric.ball (c (k - 1)) (r (k - 1))) ∧
        (∀ t ∈ Set.Icc (0:ℝ) 1, (chartAt (H := ℂ) (x k)) (cc k t) ∈ Metric.ball (c k) (r k)) := by
  classical
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  -- per-breakpoint data via the overlap connector, choosing prev = k-1 (modular).
  have hdata : ∀ k : Fin n, ∃ (p : Y) (cv : ℝ → Y),
      p ∉ branchLocus f ∧ IsSmoothPath (δ ((k : ℝ) / n)) p cv ∧
      pathSpeed cv 0 = 0 ∧ pathSpeed cv 1 = 0 ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, cv t ∈ (chartAt (H := ℂ) (x (k - 1))).source) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, cv t ∈ (chartAt (H := ℂ) (x k)).source) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, (chartAt (H := ℂ) (x (k - 1))) (cv t) ∈ Metric.ball (c (k - 1)) (r (k - 1))) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, (chartAt (H := ℂ) (x k)) (cv t) ∈ Metric.ball (c k) (r k)) := by
    intro k
    -- this-ball confinement of the breakpoint (left end of piece k).
    have hkself := hconf k ((k:ℝ)/n) (le_refl _)
      (by rw [div_le_div_iff_of_pos_right hnpos]; linarith)
    obtain ⟨hsub₂, hP_src₂, hP_ball₂⟩ := hkself
    -- prev-ball confinement of the breakpoint (right end of piece k-1), modular wrap at k=0.
    have hprev : δ ((k:ℝ)/n) ∈ (chartAt (H := ℂ) (x (k - 1))).source ∧
        (chartAt (H := ℂ) (x (k - 1))) (δ ((k:ℝ)/n)) ∈ Metric.ball (c (k - 1)) (r (k - 1)) ∧
        Metric.ball (c (k - 1)) (r (k - 1)) ⊆ (chartAt (H := ℂ) (x (k - 1))).target := by
      rcases Nat.eq_zero_or_pos k.val with hk0 | hkpos
      · -- k = 0: prev = n-1 ; breakpoint is δ 0 = δ 1, right end of piece (n-1) at parameter 1.
        have hkval0 : (k:ℝ)/n = 0 := by rw [show (k:ℝ) = 0 from by exact_mod_cast hk0]; simp
        -- (k-1).val = n-1, hence ((k-1):ℝ) = n-1.
        have hprevval : (k - 1 : Fin n).val = n - 1 := by
          have hone : ((1 : Fin n):ℕ) = 1 % n := Fin.val_one' n
          rcases (by omega : 2 ≤ n ∨ n = 1) with h2 | h2
          · have h1 : (1:ℕ) % n = 1 := Nat.mod_eq_of_lt h2
            have hval : (k - 1 : Fin n).val = (n - 1 + 0) % n := by
              rw [Fin.sub_def, hone, h1, hk0]
            rw [hval, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
          · subst h2; simp [Fin.val_eq_zero]
        have hprevR : (((k - 1 : Fin n)):ℝ) = (n:ℝ) - 1 := by
          rw [hprevval, Nat.cast_sub hn]; push_cast; ring
        have hlast := hconf (k - 1) 1
          (by rw [hprevR, div_le_one hnpos]; linarith)
          (by rw [hprevR, show (n:ℝ) - 1 + 1 = (n:ℝ) from by ring,
                div_self (ne_of_gt hnpos)])
        obtain ⟨hsubL, hsrcL, hballL⟩ := hlast
        rw [hkval0, hδ.closed]
        exact ⟨hsrcL, hballL, hsubL⟩
      · -- k > 0: prev = k-1 with (k-1).val = k.val - 1, breakpoint is right end of piece (k-1).
        have hne : k ≠ 0 := fun h => by rw [h] at hkpos; simp at hkpos
        have hkm1 : (((k - 1 : Fin n)):ℝ) = (k:ℝ) - 1 := by
          rw [Fin.val_sub_one_of_ne_zero hne, Nat.cast_sub hkpos]; push_cast; ring
        have hlo : (((k - 1 : Fin n)):ℝ)/n ≤ (k:ℝ)/n := by
          rw [hkm1, div_le_div_iff_of_pos_right hnpos]; linarith
        have hhi : (k:ℝ)/n ≤ ((((k - 1 : Fin n)):ℝ) + 1)/n := by
          rw [hkm1, show (k:ℝ) - 1 + 1 = (k:ℝ) from by ring]
        have hprevc := hconf (k - 1) ((k:ℝ)/n) hlo hhi
        obtain ⟨hsubP, hsrcP, hballP⟩ := hprevc
        exact ⟨hsrcP, hballP, hsubP⟩
    obtain ⟨hP_src₁, hP_ball₁, hsub₁⟩ := hprev
    obtain ⟨p, cv, hp_off, hsp, hv0, hv1, hsrc1, hsrc2, hb1, hb2⟩ :=
      exists_offBranch_overlap_connector f hf hnonconst (x (k - 1)) (x k) (δ ((k:ℝ)/n))
        (c (k - 1)) (c k) (r (k - 1)) (r k) hsub₁ hsub₂ hP_src₁ hP_src₂ hP_ball₁ hP_ball₂
    exact ⟨p, cv, hp_off, hsp, hv0, hv1, hsrc1, hsrc2, hb1, hb2⟩
  choose p cv hspec using hdata
  exact ⟨p, cv, hspec⟩

/-- **[off-branch surgery, period-preserving — the discharge of #6].** A closed smooth loop `δ` in
`Y` can be deformed off the finite `branchLocus f` *without changing its period vector*.

This is proven **directly** (no intermediate off-branch-breakpoint cover — that statement is false,
since a `C¹` loop may linger on a branch value, so a uniform breakpoint `δ(k/n)` can be forced onto
the locus). Instead we *perturb the breakpoints*:

1. **Cover.** `OfCurveSkeleton.exists_subBallChartCover` gives a uniform `n`-partition with, per piece
   `k`, a chart anchor `x k` and a sub-ball `ball (c k) (r k) ⊆ target(x k)` confining `δ`'s
   chart-image on `[k/n,(k+1)/n]`. (No off-branch claim.)
2. **Perturb.** `exists_overlap_connectors` dodges each breakpoint `δ(k/n)` to a nearby off-branch
   `p k`, with a flat-ended connector `cc k : δ(k/n) → p k` confined to *both* adjacent sub-balls.
3. **Detour + glue.** `exists_offBranch_detour_piece` builds, per piece, an off-branch detour
   `p k → p(k+1)` confined to ball `k`; `OfCurveSkeleton.uniformGlue` glues them into a closed smooth
   loop `δ'` avoiding `branchLocus f` (wrap `p n = p 0` from `δ 1 = δ 0`).
4. **Period equality.** On piece `k`, working with the *single* ball-`k` holomorphic primitive `F` of
   `chartFormCoeff (x k) i` (`intervalIntegral_form_pathSpeed_eq_primitive_diff_of_primitive`):
   `∫δ'|ₖ − ∫δ|ₖ = corr(k+1) − corr(k)`, where `corr(j) := ∫₀¹ ωᵢ(cc j)` is the **intrinsic** line
   integral of the connector (the same value in either adjacent ball, since `cc j` lies in the
   overlap). The corrections telescope to `corr(n) − corr(0) = 0` (`cc n = cc 0`), giving
   `periodVec δ' = periodVec δ` via `periodVec_eq_of_partition_integral_telescope`.

NO global manifold Stokes / de Rham / homotopy is involved — only the 1-dimensional chart-disk FTC,
ball-confined path-independence, and a telescoping sum. Consumers
(`exists_preimageCycle_of_nonconstant`, `…sheets_eq_fibreCard_…`) require the period vector LITERALLY
equal (threaded through `PreimageCycle.congr_periodVec`), which this provides. -/
theorem exists_loop_off_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) :
    ∃ δ', IsClosedSmoothLoop δ' ∧ periodVec δ' = periodVec δ ∧
      (∀ t : ℝ, δ' t ∉ branchLocus f) := by
  classical
  -- 1. Sub-ball cover of δ.
  obtain ⟨n, hn, x, c, r, hr, hconf⟩ :=
    OfCurveSkeleton.exists_subBallChartCover δ hδ.cont
  haveI : NeZero n := ⟨hn.ne'⟩
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  -- 2. Off-branch overlap connectors, one per breakpoint.
  obtain ⟨p, cc, hcc⟩ :=
    exists_overlap_connectors f hf hnonconst δ hδ n hn x c r hconf
  -- The Fin index of the right breakpoint of piece k (k<n): (k+1) mod n.
  set nextFin : ℕ → Fin n := fun k => ⟨(k+1) % n, Nat.mod_lt _ hn⟩ with hnextFin
  -- Key index identity: (nextFin k) - 1 = ⟨k, hk⟩  (so cc(nextFin k)'s prev ball is ball k).
  have hnextPrev : ∀ (k : ℕ) (hk : k < n), (nextFin k) - 1 = (⟨k, hk⟩ : Fin n) := by
    intro k hk
    apply Fin.ext
    show (nextFin k - 1).val = k
    have hone : ((1 : Fin n):ℕ) = 1 % n := Fin.val_one' n
    rcases (by omega : k + 1 < n ∨ k + 1 = n) with hlt | heq
    · have hnf : (nextFin k).val = k + 1 := Nat.mod_eq_of_lt hlt
      have hne : (nextFin k) ≠ 0 := by
        intro h; have : (nextFin k).val = (0 : Fin n).val := by rw [h]
        rw [hnf, Fin.val_zero] at this; omega
      rw [Fin.val_sub_one_of_ne_zero hne, hnf]; omega
    · -- k+1 = n, so nextFin k = 0, and (0 - 1).val = n-1 = k.
      have hnf0 : (nextFin k).val = 0 := by show (k+1) % n = 0; rw [heq, Nat.mod_self]
      have hz : nextFin k = 0 := Fin.ext (by rw [hnf0, Fin.val_zero])
      rw [hz]
      rcases (by omega : 2 ≤ n ∨ n = 1) with h2 | h2
      · have h1 : (1:ℕ) % n = 1 := Nat.mod_eq_of_lt h2
        have hval : ((0 : Fin n) - 1).val = (n - 1 + 0) % n := by rw [Fin.sub_def, hone, h1]; rfl
        rw [hval, Nat.add_zero, Nat.mod_eq_of_lt (show n - 1 < n by omega)]; omega
      · have hk0 : k = 0 := by omega
        have : ((0 : Fin n) - 1).val = 0 := by subst h2; rfl
        rw [this, hk0]
  -- endpoint values of the connectors.
  have hcc_start : ∀ k : Fin n, cc k 0 = δ ((k:ℝ)/n) := fun k => (hcc k).2.1.start
  have hcc_finish : ∀ k : Fin n, cc k 1 = p k := fun k => (hcc k).2.1.finish
  -- "this"-ball confinement of the right endpoint p k (left end of piece k).
  have hp_self_src : ∀ k : Fin n, p k ∈ (chartAt (H := ℂ) (x k)).source := by
    intro k; have := (hcc k).2.2.2.2.2.1 1 ⟨zero_le_one, le_refl _⟩
    rwa [hcc_finish k] at this
  have hp_self_ball : ∀ k : Fin n, (chartAt (H := ℂ) (x k)) (p k) ∈ Metric.ball (c k) (r k) := by
    intro k; have := (hcc k).2.2.2.2.2.2.2 1 ⟨zero_le_one, le_refl _⟩
    rwa [hcc_finish k] at this
  -- 3. Per-piece off-branch detour data between p ⟨k,hk⟩ and p (nextFin k), confined to ball k.
  have hpieceData : ∀ (k : ℕ) (hk : k < n), ∃ γ : ℝ → Y,
      IsSmoothPath (p ⟨k, hk⟩) (p (nextFin k)) γ ∧
      (∀ t : ℝ, γ t ∉ branchLocus f) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, (chartAt (H := ℂ) (x ⟨k, hk⟩)) (γ t) ∈ Metric.ball (c ⟨k, hk⟩) (r ⟨k, hk⟩)) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ (chartAt (H := ℂ) (x ⟨k, hk⟩)).source) ∧
      pathSpeed γ 0 = 0 ∧ pathSpeed γ 1 = 0 := by
    intro k hk
    set K : Fin n := ⟨k, hk⟩ with hK
    have hball_sub : Metric.ball (c K) (r K) ⊆ (chartAt (H := ℂ) (x K)).target :=
      (hconf K ((k:ℝ)/n) (le_refl _) (by rw [div_le_div_iff_of_pos_right hnpos]; linarith)).1
    have hP_src : p K ∈ (chartAt (H := ℂ) (x K)).source := hp_self_src K
    have hP_ball : (chartAt (H := ℂ) (x K)) (p K) ∈ Metric.ball (c K) (r K) := hp_self_ball K
    have hidxeq : (nextFin k) - 1 = K := hnextPrev k hk
    have hQ_src : p (nextFin k) ∈ (chartAt (H := ℂ) (x K)).source := by
      have h := (hcc (nextFin k)).2.2.2.2.1 1 ⟨zero_le_one, le_refl _⟩
      rw [hcc_finish (nextFin k), hidxeq] at h; exact h
    have hQ_ball : (chartAt (H := ℂ) (x K)) (p (nextFin k)) ∈ Metric.ball (c K) (r K) := by
      have h := (hcc (nextFin k)).2.2.2.2.2.2.1 1 ⟨zero_le_one, le_refl _⟩
      rw [hcc_finish (nextFin k), hidxeq] at h; exact h
    have hP_off : p K ∉ branchLocus f := (hcc K).1
    have hQ_off : p (nextFin k) ∉ branchLocus f := (hcc (nextFin k)).1
    obtain ⟨γ, hsp, hγoff, hγball, hγsrc, hv0, hv1⟩ :=
      exists_offBranch_detour_piece f hf hnonconst (x K) (p K) (p (nextFin k))
        (c K) (r K) hball_sub hP_src hQ_src hP_ball hQ_ball hP_off hQ_off
    exact ⟨γ, hsp, hγoff, hγball, hγsrc, hv0, hv1⟩
  -- assemble the glue function (junk = constant p ⟨0⟩ for k ≥ n, so chaining wraps correctly).
  set g : ℕ → ℝ → Y := fun k => if h : k < n then (hpieceData k h).choose
    else (fun _ => p ⟨0, hn⟩) with hg
  have hg_start : ∀ k (hk : k < n), g k 0 = p ⟨k, hk⟩ := by
    intro k hk; simp only [hg, dif_pos hk]; exact (hpieceData k hk).choose_spec.1.start
  have hg_finish : ∀ k (hk : k < n), g k 1 = p (nextFin k) := by
    intro k hk; simp only [hg, dif_pos hk]; exact (hpieceData k hk).choose_spec.1.finish
  -- chaining g j 1 = g (j+1) 0 : p (nextFin j) = p ⟨j+1,_⟩, and the wrap at j = n-1 gives p ⟨0⟩.
  have hnextFin_eq_succ : ∀ (j : ℕ) (hj1 : j + 1 < n), nextFin j = (⟨j+1, hj1⟩ : Fin n) := by
    intro j hj1; apply Fin.ext; show (j+1) % n = j+1; exact Nat.mod_eq_of_lt hj1
  have hchain : ∀ j, g j 1 = g (j+1) 0 := by
    intro j
    by_cases hj : j < n
    · rw [hg_finish j hj]
      by_cases hj1 : j + 1 < n
      · rw [hg_start (j+1) hj1, hnextFin_eq_succ j hj1]
      · -- j = n-1 : nextFin j = ⟨0,_⟩ ; g (j+1) 0 = p ⟨0⟩ (junk).
        have hjn : j + 1 = n := by omega
        have hnf0 : (nextFin j).val = 0 := by show (j+1) % n = 0; rw [hjn, Nat.mod_self]
        rw [show nextFin j = (⟨0, hn⟩ : Fin n) from Fin.ext hnf0]
        simp only [hg, dif_neg (show ¬ j + 1 < n from by omega)]
    · simp only [hg, dif_neg hj, dif_neg (show ¬ j + 1 < n from by omega)]
  -- piece smoothness/flatness hypotheses (k < n).
  have hpiece : ∀ k, k < n → IsSmoothPath (g k 0) (g k 1) (g k) := by
    intro k hk
    rw [hg_start k hk, hg_finish k hk]; simp only [hg, dif_pos hk]
    exact (hpieceData k hk).choose_spec.1
  have hv0 : ∀ k, k < n → pathSpeed (g k) 0 = 0 := by
    intro k hk; simp only [hg, dif_pos hk]; exact (hpieceData k hk).choose_spec.2.2.2.2.1
  have hv1 : ∀ k, k < n → pathSpeed (g k) 1 = 0 := by
    intro k hk; simp only [hg, dif_pos hk]; exact (hpieceData k hk).choose_spec.2.2.2.2.2
  -- the glued loop.
  set δ' : ℝ → Y := OfCurveSkeleton.uniformGlue g n with hδ'def
  have hsp_glue : IsSmoothPath (g 0 0) (g (n-1) 1) δ' :=
    OfCurveSkeleton.isSmoothPath_uniformGlue g hchain n hn hpiece hv0 hv1
  -- δ' is a closed loop: g 0 0 = p ⟨0⟩ and g (n-1) 1 = p (nextFin (n-1)) = p ⟨0⟩.
  have hg00 : g 0 0 = p ⟨0, hn⟩ := hg_start 0 hn
  have hgn1 : g (n-1) 1 = p ⟨0, hn⟩ := by
    rw [hg_finish (n-1) (by omega)]; congr 1
    apply Fin.ext
    show ((n-1)+1) % n = (0 : Fin n).val
    rw [Nat.sub_add_cancel hn, Nat.mod_self, Fin.val_zero]
  have heq_ends : g 0 0 = g (n-1) 1 := by rw [hg00, hgn1]
  have hloop : IsClosedSmoothLoop δ' :=
    { closed := by rw [hsp_glue.start, hsp_glue.finish, heq_ends]
      cont := hsp_glue.cont
      diff := hsp_glue.diff
      velCont := hsp_glue.velCont }
  -- off-branch: every point of δ' lies on some detour piece (uIdx < n), which avoids branchLocus.
  have hidx_lt : ∀ t : ℝ, OfCurveSkeleton.uIdx n t < n := by
    intro t; unfold OfCurveSkeleton.uIdx; omega
  have hoff_glue : ∀ t : ℝ, δ' t ∉ branchLocus f := by
    intro t
    show OfCurveSkeleton.uniformGlue g n t ∉ branchLocus f
    unfold OfCurveSkeleton.uniformGlue
    have hlt := hidx_lt t
    simp only [hg, dif_pos hlt]
    exact (hpieceData (OfCurveSkeleton.uIdx n t) hlt).choose_spec.2.1 _
  refine ⟨δ', hloop, ?_, hoff_glue⟩
  -- 4. PERIOD EQUALITY via the per-piece correction telescope.
  -- the uniform partition and the intrinsic correction term.
  set sfun : ℕ → ℝ := fun k => (k:ℝ)/n with hsfun
  set corr : Fin (kirovGenus Y) → ℕ → ℂ := fun i k =>
    if h : k < n then lineIntegral (periodBasisForm Y i) (cc ⟨k, h⟩)
    else lineIntegral (periodBasisForm Y i) (cc ⟨0, hn⟩) with hcorr
  have hs0 : sfun 0 = 0 := by simp [hsfun]
  have hsn : sfun n = 1 := by simp only [hsfun]; exact div_self (ne_of_gt hnpos)
  have hs_sub : ∀ k, k < n → Set.uIcc (sfun k) (sfun (k+1)) ⊆ Set.Icc (0:ℝ) 1 := by
    intro k hk
    have hle : sfun k ≤ sfun (k+1) := by
      simp only [hsfun]; rw [div_le_div_iff_of_pos_right hnpos]; push_cast; linarith
    rw [Set.uIcc_of_le hle]
    intro u hu
    simp only [hsfun, Set.mem_Icc] at hu ⊢
    refine ⟨le_trans ?_ hu.1, le_trans hu.2 ?_⟩
    · positivity
    · rw [div_le_one hnpos]; push_cast; exact_mod_cast hk
  -- correction is periodic: corr i n = corr i 0.
  have hcorr_per : ∀ i, corr i n = corr i 0 := by
    intro i; simp only [hcorr, dif_neg (lt_irrefl n), dif_pos hn]
  -- the per-piece correction identity.
  have hpiece_corr : ∀ (i : Fin (kirovGenus Y)) (k : ℕ), k < n →
      (∫ t in (sfun k)..(sfun (k+1)), (periodBasisForm Y i).toFun (δ' t) (pathSpeed δ' t)) =
      (∫ t in (sfun k)..(sfun (k+1)), (periodBasisForm Y i).toFun (δ t) (pathSpeed δ t))
        + corr i (k+1) - corr i k := by
    intro i k hk
    set K : Fin n := ⟨k, hk⟩ with hK
    have hk1cast : sfun (k+1) = ((k:ℝ)+1)/n := by simp only [hsfun]; push_cast; ring
    have hk0cast : sfun k = (k:ℝ)/n := by simp only [hsfun]
    rw [hk0cast, hk1cast]
    have hab_le : (k:ℝ)/n ≤ ((k:ℝ)+1)/n := by rw [div_le_div_iff_of_pos_right hnpos]; linarith
    have huIcc_eq : Set.uIcc ((k:ℝ)/n) (((k:ℝ)+1)/n) = Set.Icc ((k:ℝ)/n) (((k:ℝ)+1)/n) :=
      Set.uIcc_of_le hab_le
    have hsubIcc : Set.uIcc ((k:ℝ)/n) (((k:ℝ)+1)/n) ⊆ Set.uIcc (0:ℝ) 1 := by
      rw [huIcc_eq, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; intro u hu
      simp only [Set.mem_Icc] at hu ⊢
      refine ⟨le_trans (by positivity) hu.1, le_trans hu.2 ?_⟩
      rw [div_le_one hnpos]; exact_mod_cast hk
    -- ball-K data and the single primitive F on ball K.
    have hsub : Metric.ball (c K) (r K) ⊆ (chartAt (H := ℂ) (x K)).target :=
      (hconf K ((k:ℝ)/n) (le_refl _) hab_le).1
    obtain ⟨F, hF⟩ :=
      ((OfCurveSkeleton.chartFormCoeff_differentiableOn (x K) i).mono hsub).isExactOn_ball
    -- piece detour data.
    set γc : ℝ → Y := (hpieceData k hk).choose with hγc
    obtain ⟨hγc_sp, hγc_off, hγc_ball, hγc_src, hγc_v0, hγc_v1⟩ := (hpieceData k hk).choose_spec
    -- δ' = γc (n·-k) on the closed piece.
    have hδ'_eq : ∀ t, (k:ℝ)/n ≤ t → t ≤ ((k:ℝ)+1)/n → δ' t = γc ((n:ℝ)*t - k) := by
      intro t ht0 ht1
      show OfCurveSkeleton.uniformGlue g n t = γc ((n:ℝ)*t - k)
      rw [OfCurveSkeleton.uniformGlue_apply_of_mem g hchain n hn k hk t ht0 ht1]
      simp only [hg, dif_pos hk, hγc]
    have harg_mem : ∀ t, (k:ℝ)/n ≤ t → t ≤ ((k:ℝ)+1)/n → (n:ℝ)*t - k ∈ Set.Icc (0:ℝ) 1 := by
      intro t ht0 ht1
      refine ⟨?_, ?_⟩
      · rw [div_le_iff₀ hnpos] at ht0; linarith
      · rw [le_div_iff₀ hnpos] at ht1; linarith
    -- helper to apply the given-primitive prim-diff on the piece for a path φ.
    -- ∫δ' = F(chart(δ' b)) − F(chart(δ' a)).
    have hInt_δ' :
        (∫ t in ((k:ℝ)/n)..(((k:ℝ)+1)/n), (periodBasisForm Y i).toFun (δ' t) (pathSpeed δ' t)) =
        F ((chartAt (H := ℂ) (x K)) (δ' (((k:ℝ)+1)/n)))
          - F ((chartAt (H := ℂ) (x K)) (δ' ((k:ℝ)/n))) := by
      apply OfCurveSkeleton.intervalIntegral_form_pathSpeed_eq_primitive_diff_of_primitive
        (x K) δ' i (c K) (r K) ((k:ℝ)/n) (((k:ℝ)+1)/n) F hF
      · intro t ht; rw [huIcc_eq, Set.mem_Icc] at ht
        rw [hδ'_eq t ht.1 ht.2]; exact hγc_ball _ (harg_mem t ht.1 ht.2)
      · intro t ht; rw [huIcc_eq, Set.mem_Icc] at ht
        rw [hδ'_eq t ht.1 ht.2]; exact hγc_src _ (harg_mem t ht.1 ht.2)
      · exact hloop.cont
      · intro t ht; rw [huIcc_eq, Set.mem_Icc] at ht
        refine OfCurveSkeleton.differentiableAt_chart_anchor_of_self (x K) δ' t hloop.cont ?_
          (hloop.diff t (hsubIcc (by rw [huIcc_eq, Set.mem_Icc]; exact ht)))
        rw [hδ'_eq t ht.1 ht.2]; exact hγc_src _ (harg_mem t ht.1 ht.2)
      · exact (hloop.integrable i).mono_set hsubIcc
    -- ∫δ = F(chart(δ b)) − F(chart(δ a)).
    have hInt_δ :
        (∫ t in ((k:ℝ)/n)..(((k:ℝ)+1)/n), (periodBasisForm Y i).toFun (δ t) (pathSpeed δ t)) =
        F ((chartAt (H := ℂ) (x K)) (δ (((k:ℝ)+1)/n)))
          - F ((chartAt (H := ℂ) (x K)) (δ ((k:ℝ)/n))) := by
      apply OfCurveSkeleton.intervalIntegral_form_pathSpeed_eq_primitive_diff_of_primitive
        (x K) δ i (c K) (r K) ((k:ℝ)/n) (((k:ℝ)+1)/n) F hF
      · intro t ht; rw [huIcc_eq, Set.mem_Icc] at ht; exact (hconf K t ht.1 ht.2).2.2
      · intro t ht; rw [huIcc_eq, Set.mem_Icc] at ht; exact (hconf K t ht.1 ht.2).2.1
      · exact hδ.cont
      · intro t ht; rw [huIcc_eq, Set.mem_Icc] at ht
        refine OfCurveSkeleton.differentiableAt_chart_anchor_of_self (x K) δ t hδ.cont ?_
          (hδ.diff t (hsubIcc (by rw [huIcc_eq, Set.mem_Icc]; exact ht)))
        exact (hconf K t ht.1 ht.2).2.1
      · exact (hδ.integrable i).mono_set hsubIcc
    -- corr i k = F(chart(p K)) − F(chart(δ(k/n))), via cc K confined to ball K (this-ball).
    have hcorr_k : corr i k = F ((chartAt (H := ℂ) (x K)) (p K))
        - F ((chartAt (H := ℂ) (x K)) (δ ((k:ℝ)/n))) := by
      simp only [hcorr, dif_pos hk]
      show lineIntegral (periodBasisForm Y i) (cc K) = _
      unfold lineIntegral
      rw [OfCurveSkeleton.intervalIntegral_form_pathSpeed_eq_primitive_diff_of_primitive
        (x K) (cc K) i (c K) (r K) 0 1 F hF
        (fun t ht => (hcc K).2.2.2.2.2.2.2 t (by rwa [Set.uIcc_of_le zero_le_one] at ht))
        (fun t ht => (hcc K).2.2.2.2.2.1 t (by rwa [Set.uIcc_of_le zero_le_one] at ht))
        (hcc K).2.1.cont
        (fun t ht => OfCurveSkeleton.differentiableAt_chart_anchor_of_self (x K) (cc K) t
          (hcc K).2.1.cont ((hcc K).2.2.2.2.2.1 t (by rwa [Set.uIcc_of_le zero_le_one] at ht))
          ((hcc K).2.1.diff t ht))
        ((hcc K).2.1.integrable i)]
      rw [hcc_finish K, hcc_start K]
    -- corr i (k+1) = F(chart(p(nextFin k))) − F(chart(δ((k+1)/n))), via cc(nextFin k) in ball K
    -- (prev-ball, since (nextFin k)-1 = K).
    have hidxeq : (nextFin k) - 1 = K := hnextPrev k hk
    -- cc (nextFin k) starts at δ((k+1)/n).  In the WRAP case (k+1=n) the breakpoint nextFin k = 0
    -- sits at parameter 0, and δ 0 = δ 1 = δ((k+1)/n) via closedness; else (nextFin k:ℝ)/n = (k+1)/n.
    have hcc_next_start : cc (nextFin k) 0 = δ (((k:ℝ)+1)/n) := by
      rw [hcc_start (nextFin k)]
      rcases (by omega : k + 1 < n ∨ k + 1 = n) with hlt | heq
      · congr 1; rw [hnextFin_eq_succ k hlt]; push_cast; ring
      · have hnf0 : (nextFin k).val = 0 := by show (k+1) % n = 0; rw [heq, Nat.mod_self]
        have hzero : ((((nextFin k):ℝ))/n) = 0 := by
          rw [show ((nextFin k : Fin n):ℝ) = ((nextFin k).val : ℝ) from rfl, hnf0]; simp
        rw [hzero, hδ.closed]
        congr 1
        rw [show ((k:ℝ)+1) = (n:ℝ) from by rw [← heq]; push_cast; ring,
          div_self (ne_of_gt hnpos)]
    have hcorr_k1 : corr i (k+1) = F ((chartAt (H := ℂ) (x K)) (p (nextFin k)))
        - F ((chartAt (H := ℂ) (x K)) (δ (((k:ℝ)+1)/n))) := by
      -- corr i (k+1) = lineIntegral over cc (nextFin k) (whether k+1<n or =n).
      have hval : corr i (k+1) = lineIntegral (periodBasisForm Y i) (cc (nextFin k)) := by
        rcases (by omega : k + 1 < n ∨ k + 1 = n) with hlt | heq
        · simp only [hcorr, dif_pos hlt]
          rw [hnextFin_eq_succ k hlt]
        · have hnf0 : (nextFin k).val = 0 := by show (k+1) % n = 0; rw [heq, Nat.mod_self]
          simp only [hcorr, dif_neg (show ¬ k + 1 < n from by omega)]
          rw [show nextFin k = (⟨0, hn⟩ : Fin n) from Fin.ext hnf0]
      rw [hval]
      show lineIntegral (periodBasisForm Y i) (cc (nextFin k)) = _
      unfold lineIntegral
      -- cc (nextFin k) confined to ball K via prev-ball (ball ((nextFin k)-1) = ball K).
      have hball_prev : ∀ t ∈ Set.uIcc (0:ℝ) 1,
          (chartAt (H := ℂ) (x K)) (cc (nextFin k) t) ∈ Metric.ball (c K) (r K) := by
        intro t ht
        have h := (hcc (nextFin k)).2.2.2.2.2.2.1 t (by rwa [Set.uIcc_of_le zero_le_one] at ht)
        rw [hidxeq] at h; exact h
      have hsrc_prev : ∀ t ∈ Set.uIcc (0:ℝ) 1, cc (nextFin k) t ∈ (chartAt (H := ℂ) (x K)).source := by
        intro t ht
        have h := (hcc (nextFin k)).2.2.2.2.1 t (by rwa [Set.uIcc_of_le zero_le_one] at ht)
        rw [hidxeq] at h; exact h
      rw [OfCurveSkeleton.intervalIntegral_form_pathSpeed_eq_primitive_diff_of_primitive
        (x K) (cc (nextFin k)) i (c K) (r K) 0 1 F hF hball_prev hsrc_prev
        (hcc (nextFin k)).2.1.cont
        (fun t ht => OfCurveSkeleton.differentiableAt_chart_anchor_of_self (x K) (cc (nextFin k)) t
          (hcc (nextFin k)).2.1.cont (hsrc_prev t ht) ((hcc (nextFin k)).2.1.diff t ht))
        ((hcc (nextFin k)).2.1.integrable i)]
      rw [hcc_finish (nextFin k), hcc_next_start]
    -- δ' endpoints: δ'(k/n) = p K, δ'((k+1)/n) = p(nextFin k).
    have hδ'_a : δ' ((k:ℝ)/n) = p K := by
      rw [hδ'_eq ((k:ℝ)/n) (le_refl _) hab_le,
        show (n:ℝ)*((k:ℝ)/n) - k = 0 from by rw [mul_div_cancel₀ _ (ne_of_gt hnpos)]; ring]
      exact hγc_sp.start
    have hδ'_b : δ' (((k:ℝ)+1)/n) = p (nextFin k) := by
      rw [hδ'_eq (((k:ℝ)+1)/n) hab_le (le_refl _),
        show (n:ℝ)*(((k:ℝ)+1)/n) - k = 1 from by rw [mul_div_cancel₀ _ (ne_of_gt hnpos)]; ring]
      exact hγc_sp.finish
    -- assemble: ∫δ' − ∫δ = corr(k+1) − corr(k).
    rw [hInt_δ', hInt_δ, hcorr_k, hcorr_k1, hδ'_a, hδ'_b]
    ring
  exact periodVec_eq_of_partition_integral_telescope δ δ' hδ hloop sfun n hs0 hsn hs_sub
    corr hcorr_per hpiece_corr

/-- **Continuous path-lift off the branch locus.** A path `δ` in `Y` that avoids the
branch locus lifts, through the proven covering
`(univ \ branchLocus f).restrictPreimage f`, to a continuous path `Γ` in `X` with
`f (Γ t) = δ t` on `[0,1]` and prescribed start `Γ 0 = e` (any fibre point over
`δ 0`). The lift is Mathlib's `IsCoveringMap.liftPath`, repackaged from the unit
interval to `ℝ → X` via `Set.projIcc`. Foundation for the smooth-loop assembly
(§3 sub-piece A).

The lift is `Set.projIcc`-clamped, so it is **constant outside `[0,1]`** (`= e` on
`(-∞,0]`, `= Γ 1` on `[1,∞)`); these two facts are exposed in the conclusion — they
give the two-sided endpoint control the seam-flattening construction needs. -/
theorem exists_continuous_lift_off_branchLocus
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ_cont : Continuous δ) (havoid : ∀ t : ℝ, δ t ∉ branchLocus f)
    {e : X} (he : f e = δ 0) :
    ∃ Γ : ℝ → X, Continuous Γ ∧ (∀ t ∈ Set.Icc (0:ℝ) 1, f (Γ t) = δ t) ∧ Γ 0 = e ∧
      (∀ t : ℝ, t ≤ 0 → Γ t = e) ∧ (∀ t : ℝ, 1 ≤ t → Γ t = Γ 1) := by
  classical
  have cov : IsCoveringMap ((Set.univ \ branchLocus f).restrictPreimage f) :=
    isCoveringMap_restrictPreimage_compl_branchLocus f hf hnonconst
  -- `δ` lands in `s := univ \ branchLocus f` everywhere (it avoids the branch locus).
  have hδs : ∀ t : ℝ, δ t ∈ Set.univ \ branchLocus f := fun t => ⟨Set.mem_univ _, havoid t⟩
  -- Corestrict `δ` to the unit interval, as a continuous map into the subtype.
  let δ' : C(unitInterval, ↥(Set.univ \ branchLocus f)) :=
    ⟨fun t => ⟨δ t, hδs t⟩, (hδ_cont.comp continuous_subtype_val).subtype_mk _⟩
  -- The start point, lifted into the fibre subtype.
  have hes : e ∈ f ⁻¹' (Set.univ \ branchLocus f) := by
    show f e ∈ Set.univ \ branchLocus f; rw [he]; exact hδs 0
  let e' : ↥(f ⁻¹' (Set.univ \ branchLocus f)) := ⟨e, hes⟩
  have hγ0 : δ' 0 = (Set.univ \ branchLocus f).restrictPreimage f e' := by
    apply Subtype.ext
    show δ ((0 : unitInterval) : ℝ) = f e
    rw [Set.Icc.coe_zero, he]
  have hlifts := IsCoveringMap.liftPath_lifts cov δ' e' hγ0
  have hzero := IsCoveringMap.liftPath_zero cov δ' e' hγ0
  refine ⟨fun t => ((IsCoveringMap.liftPath cov δ' e' hγ0)
      (Set.projIcc 0 1 zero_le_one t) : X), ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp
      ((map_continuous (IsCoveringMap.liftPath cov δ' e' hγ0)).comp continuous_projIcc)
  · intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hδ'c : ∀ x : unitInterval, (↑(δ' x) : Y) = δ ↑x := fun _ => rfl
    have h := congrArg Subtype.val (congr_fun hlifts (Set.projIcc 0 1 zero_le_one t))
    simpa [Function.comp_apply, Set.restrictPreimage_coe, hδ'c, Set.coe_projIcc,
      min_eq_right ht1, max_eq_right ht0] using h
  · have h0 : Set.projIcc (0:ℝ) 1 zero_le_one 0 = 0 := by
      apply Subtype.ext; simp
    show ((IsCoveringMap.liftPath cov δ' e' hγ0)
      (Set.projIcc 0 1 zero_le_one 0) : X) = e
    rw [h0, hzero]
  · -- Clamp on `(-∞, 0]`: `projIcc` sends `t ≤ 0` to the left endpoint `0`, so `Γ t = e`.
    intro t ht
    show ((IsCoveringMap.liftPath cov δ' e' hγ0)
      (Set.projIcc 0 1 zero_le_one t) : X) = e
    have h0' : Set.projIcc (0:ℝ) 1 zero_le_one t = 0 := by
      rw [Set.projIcc_of_le_left _ ht]; rfl
    rw [h0', hzero]
  · -- Clamp on `[1, ∞)`: `projIcc` sends `1 ≤ t` to the right endpoint `1`, as it does `1`.
    intro t ht
    show ((IsCoveringMap.liftPath cov δ' e' hγ0)
        (Set.projIcc 0 1 zero_le_one t) : X) =
      ((IsCoveringMap.liftPath cov δ' e' hγ0)
        (Set.projIcc 0 1 zero_le_one 1) : X)
    have h1 : Set.projIcc (0:ℝ) 1 zero_le_one t = Set.projIcc (0:ℝ) 1 zero_le_one 1 := by
      rw [Set.projIcc_of_right_le _ ht, Set.projIcc_of_right_le _ le_rfl]
    rw [h1]

/-! ### Seam-flattening reparametrization (§3 step C)

A path-lift produced by `exists_continuous_lift_off_branchLocus` is `Set.projIcc`-
clamped (constant outside `[0,1]`), so it is *not* differentiable at the endpoints
`0,1`, and `differentiableAt_chart_lift_of_notMem_criticalSet` (B) only delivers
differentiability on the open `(0,1)`. To concatenate lifts into closed loops we
need lifts that are genuine smooth paths with *zero endpoint velocity*. The fix is
to reparametrize the base loop by `flatEndReparam`, which is **constant near each
endpoint** (a genuine plateau, not merely zero-derivative). Then the lift of the
reparametrized loop is *constant* near `0,1` (continuity + local injectivity of `f`),
hence trivially smooth with zero velocity there, while the interior is handled by B —
sidestepping any one-sided gluing. -/

/-- A smooth reparametrization of the unit interval, **constant near the endpoints**:
`flatEndReparam t = Real.smoothTransition (2 t - 1/2)`. It is `≡ 0` on `(-∞, 1/4]`,
`≡ 1` on `[3/4, ∞)`, smooth, monotone, maps `[0,1]` into `[0,1]`, and fixes the
endpoints (`0 ↦ 0`, `1 ↦ 1`). The end plateaus are what make a lift of
`δ ∘ flatEndReparam` constant near the seam. -/
noncomputable def flatEndReparam (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1 / 2)

@[simp] theorem flatEndReparam_zero : flatEndReparam 0 = 0 := by
  unfold flatEndReparam; rw [Real.smoothTransition.zero_of_nonpos (by norm_num)]

@[simp] theorem flatEndReparam_one : flatEndReparam 1 = 1 := by
  unfold flatEndReparam; rw [Real.smoothTransition.one_of_one_le (by norm_num)]

/-- `flatEndReparam` is `≡ 0` on the left plateau `(-∞, 1/4]`. -/
theorem flatEndReparam_eqZero_of_le {t : ℝ} (ht : t ≤ 1 / 4) : flatEndReparam t = 0 := by
  unfold flatEndReparam; exact Real.smoothTransition.zero_of_nonpos (by linarith)

/-- `flatEndReparam` is `≡ 1` on the right plateau `[3/4, ∞)`. -/
theorem flatEndReparam_eqOne_of_ge {t : ℝ} (ht : 3 / 4 ≤ t) : flatEndReparam t = 1 := by
  unfold flatEndReparam; exact Real.smoothTransition.one_of_one_le (by linarith)

theorem flatEndReparam_mem_unit (t : ℝ) : flatEndReparam t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem contDiff_flatEndReparam {n : ℕ∞} : ContDiff ℝ n flatEndReparam :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem differentiable_flatEndReparam : Differentiable ℝ flatEndReparam :=
  (contDiff_flatEndReparam (n := 1)).differentiable (by norm_num)

theorem flatEndReparam_hasDerivAt (t : ℝ) :
    HasDerivAt flatEndReparam (deriv flatEndReparam t) t :=
  (differentiable_flatEndReparam t).hasDerivAt

theorem flatEndReparam_monotone : Monotone flatEndReparam := by
  intro a b hab; unfold flatEndReparam; exact Real.smoothTransition.monotone (by linarith)

theorem flatEndReparam_image_Icc : flatEndReparam '' Set.Icc (0:ℝ) 1 = Set.Icc 0 1 := by
  apply Set.eq_of_subset_of_subset
  · rintro u ⟨t, -, rfl⟩; exact flatEndReparam_mem_unit t
  · have h := intermediate_value_Icc (zero_le_one (α := ℝ))
      differentiable_flatEndReparam.continuous.continuousOn
    rwa [flatEndReparam_zero, flatEndReparam_one] at h

/-- Reparametrized pathSpeed (chain rule): `pathSpeed (γ ∘ flatEndReparam) t =
flatEndReparam'(t) · pathSpeed γ (flatEndReparam t)`. Mirrors
`pathSpeed_smoothStep01_comp_eq`. -/
theorem pathSpeed_flatEndReparam_comp_eq (γ : ℝ → X) (t : ℝ)
    (hγ_diff : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (γ (flatEndReparam t))).toFun ∘ γ) (flatEndReparam t)) :
    pathSpeed (γ ∘ flatEndReparam) t =
      ((deriv flatEndReparam t : ℝ) : ℂ) * pathSpeed γ (flatEndReparam t) := by
  unfold pathSpeed
  have h_assoc : (chartAt (H := ℂ) ((γ ∘ flatEndReparam) t)).toFun ∘ (γ ∘ flatEndReparam) =
      ((chartAt (H := ℂ) (γ (flatEndReparam t))).toFun ∘ γ) ∘ flatEndReparam := by
    funext s; rfl
  rw [h_assoc]
  have hσ : HasDerivAt flatEndReparam (deriv flatEndReparam t) t := flatEndReparam_hasDerivAt t
  have hφ : HasDerivAt ((chartAt (H := ℂ) (γ (flatEndReparam t))).toFun ∘ γ)
      (pathSpeed γ (flatEndReparam t)) (flatEndReparam t) := hγ_diff.hasDerivAt
  have h_comp : HasDerivAt
      (((chartAt (H := ℂ) (γ (flatEndReparam t))).toFun ∘ γ) ∘ flatEndReparam)
      (deriv flatEndReparam t • pathSpeed γ (flatEndReparam t)) t := hφ.scomp t hσ
  have h_deriv := h_comp.deriv
  have h_lhs_eq : (fderiv ℝ
      (((chartAt (H := ℂ) (γ (flatEndReparam t))).toFun ∘ γ) ∘ flatEndReparam) t) 1 =
      deriv flatEndReparam t • pathSpeed γ (flatEndReparam t) := by rw [← h_deriv]; rfl
  rw [h_lhs_eq]; exact Complex.real_smul

/-- **Reparametrization-invariance of the line integral** (the textbook monotone
change of variables). Reparametrizing a (regular, integrable) path by the monotone
`flatEndReparam` leaves the line integral unchanged. Uses Mathlib's measure-theoretic
monotone CoV `integral_image_eq_integral_deriv_smul_of_monotoneOn` (valid for merely
*integrable* integrands — no `C¹` needed), exactly the value-level companion of the
`smoothStep01` integrability argument in `isSmoothPath_smoothPathSmooth`. The key to
transporting the preimage-cycle construction from `δ∘flatEndReparam` back to `δ`. -/
theorem lineIntegral_comp_flatEndReparam (α : HolomorphicOneForms X) (γ : ℝ → X)
    (hγ_diff : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t) :
    lineIntegral α (γ ∘ flatEndReparam) = lineIntegral α γ := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  -- The monotone change-of-variables (value version) for the integrand of `γ`.
  have hcov := MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
    (s := Set.Icc (0:ℝ) 1) measurableSet_Icc (f := flatEndReparam) (f' := deriv flatEndReparam)
    (fun x _ => (flatEndReparam_hasDerivAt x).hasDerivWithinAt) (flatEndReparam_monotone.monotoneOn _)
    (fun u => α.toFun (γ u) (pathSpeed γ u))
  rw [flatEndReparam_image_Icc] at hcov
  -- `lineIntegral α γ` as a set integral over `Icc 0 1`.
  have hRHS : lineIntegral α γ = ∫ x in Set.Icc (0:ℝ) 1, α.toFun (γ x) (pathSpeed γ x) := by
    unfold lineIntegral
    rw [intervalIntegral.integral_of_le h01, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- `lineIntegral α (γ∘r)` as the reparametrized set integral over `Icc 0 1`.
  have hLHS : lineIntegral α (γ ∘ flatEndReparam) =
      ∫ x in Set.Icc (0:ℝ) 1,
        deriv flatEndReparam x • α.toFun (γ (flatEndReparam x)) (pathSpeed γ (flatEndReparam x)) := by
    unfold lineIntegral
    rw [intervalIntegral.integral_of_le h01, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
    have hrt : flatEndReparam t ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le h01]; exact flatEndReparam_mem_unit t
    have hps := pathSpeed_flatEndReparam_comp_eq γ t (hγ_diff (flatEndReparam t) hrt)
    show α.toFun (γ (flatEndReparam t)) (pathSpeed (γ ∘ flatEndReparam) t) =
      deriv flatEndReparam t • α.toFun (γ (flatEndReparam t)) (pathSpeed γ (flatEndReparam t))
    rw [hps]
    have h_lin : (α.toFun (γ (flatEndReparam t)))
          (((deriv flatEndReparam t : ℝ) : ℂ) * pathSpeed γ (flatEndReparam t)) =
        ((deriv flatEndReparam t : ℝ) : ℂ) *
          (α.toFun (γ (flatEndReparam t))) (pathSpeed γ (flatEndReparam t)) := by
      have h_ml := (α.toFun (γ (flatEndReparam t))).map_smul
        ((deriv flatEndReparam t : ℝ) : ℂ) (pathSpeed γ (flatEndReparam t))
      simp only [smul_eq_mul] at h_ml
      exact h_ml
    rw [h_lin, Complex.real_smul]
  rw [hLHS, hRHS]; exact hcov.symm

/-- **Period vector is `flatEndReparam`-invariant.** A closed smooth loop and its
seam-flattened reparametrization `γ ∘ flatEndReparam` have the same period vector
(componentwise `lineIntegral_comp_flatEndReparam`). This is what lets the
preimage-cycle construction, carried out for `δ ∘ flatEndReparam`, transport back to
`δ` (via `PreimageCycle.congr_periodVec`). -/
theorem periodVec_comp_flatEndReparam (γ : ℝ → X) (hγ : IsClosedSmoothLoop γ) :
    periodVec (γ ∘ flatEndReparam) = periodVec γ := by
  funext i
  exact lineIntegral_comp_flatEndReparam (periodBasisForm X i) γ hγ.diff

/-- **Line integral depends only on the path's values on `[0,1]`.** Two paths
agreeing on `[0,1]` have equal line integrals: the integrand (value + `pathSpeed`,
a germ at `t`) agrees on the open interior `(0,1)` — where `[0,1]` is a neighborhood —
hence a.e. on `(0,1]`. The endpoints, where the germ leaks outside `[0,1]`, are a
null set. Gives the single-lift pushforward `lineIntegral α (f∘Γ) = lineIntegral α δr`
since a lift satisfies `f∘Γ = δr` on `[0,1]`. -/
theorem lineIntegral_congr_of_eqOn (α : HolomorphicOneForms X) {g₁ g₂ : ℝ → X}
    (h : Set.EqOn g₁ g₂ (Set.Icc (0:ℝ) 1)) :
    lineIntegral α g₁ = lineIntegral α g₂ := by
  unfold lineIntegral
  refine intervalIntegral.integral_congr_ae ?_
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (1 : ℝ))
  intro t ht
  simp only [Set.mem_setOf_eq, Classical.not_imp] at ht
  obtain ⟨ht_mem, ht_ne⟩ := ht
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht_mem
  by_contra ht1
  refine ht_ne ?_
  have ht_Ioo : t ∈ Set.Ioo (0:ℝ) 1 :=
    ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 (by simpa using ht1)⟩
  have heq_nbhd : g₁ =ᶠ[𝓝 t] g₂ := by
    filter_upwards [Ioo_mem_nhds ht_Ioo.1 ht_Ioo.2] with s hs
    exact h ⟨hs.1.le, hs.2.le⟩
  have hval : g₁ t = g₂ t := h ⟨ht_Ioo.1.le, ht_Ioo.2.le⟩
  show α.toFun (g₁ t) (pathSpeed g₁ t) = α.toFun (g₂ t) (pathSpeed g₂ t)
  rw [hval]
  congr 1
  show fderiv ℝ ((chartAt (H := ℂ) (g₁ t)).toFun ∘ g₁) t 1 =
    fderiv ℝ ((chartAt (H := ℂ) (g₂ t)).toFun ∘ g₂) t 1
  rw [hval, (heq_nbhd.fun_comp (chartAt (H := ℂ) (g₂ t)).toFun).fderiv_eq]

/-- **Period vector depends only on the loop's values on `[0,1]`.** Componentwise
`lineIntegral_congr_of_eqOn`. -/
theorem periodVec_congr_of_eqOn {g₁ g₂ : ℝ → X}
    (h : Set.EqOn g₁ g₂ (Set.Icc (0:ℝ) 1)) : periodVec g₁ = periodVec g₂ := by
  funext i; exact lineIntegral_congr_of_eqOn (periodBasisForm X i) h

/-- **Integrability is preserved by the `flatEndReparam` reparametrization.** If the
form-integrand of `γ` is interval-integrable, so is that of `γ ∘ flatEndReparam`. Same
monotone-CoV *integrability* lemma the codebase uses for `smoothStep01`
(`integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn`); the integrand of the
reparametrized path equals `flatEndReparam' • (integrand ∘ flatEndReparam)` a.e. (chain
rule `pathSpeed_flatEndReparam_comp_eq`). Feeds the lift-integrability upgrade. -/
theorem intervalIntegrable_comp_flatEndReparam (α : HolomorphicOneForms X) (γ : ℝ → X)
    (hγ_diff : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t)
    (hγ_int : IntervalIntegrable (fun t => α.toFun (γ t) (pathSpeed γ t))
      MeasureTheory.volume 0 1) :
    IntervalIntegrable
      (fun t => α.toFun ((γ ∘ flatEndReparam) t) (pathSpeed (γ ∘ flatEndReparam) t))
      MeasureTheory.volume 0 1 := by
  set h : ℝ → ℂ := fun u => α.toFun (γ u) (pathSpeed γ u) with hh_def
  have h_int_Icc : MeasureTheory.IntegrableOn h (Set.Icc (0:ℝ) 1) MeasureTheory.volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp hγ_int
  have h_subst_iff := MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
    (s := Set.Icc (0:ℝ) 1) measurableSet_Icc (f := flatEndReparam) (f' := deriv flatEndReparam)
    (fun x _ => (flatEndReparam_hasDerivAt x).hasDerivWithinAt) (flatEndReparam_monotone.monotoneOn _) h
  rw [flatEndReparam_image_Icc] at h_subst_iff
  have h_subst_Ioc : MeasureTheory.IntegrableOn
      (fun x => deriv flatEndReparam x • h (flatEndReparam x)) (Set.Ioc (0:ℝ) 1) MeasureTheory.volume :=
    (h_subst_iff.mp h_int_Icc).mono_set Set.Ioc_subset_Icc_self
  have h_sub_intInt : IntervalIntegrable
      (fun x => deriv flatEndReparam x • h (flatEndReparam x)) MeasureTheory.volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr h_subst_Ioc
  apply h_sub_intInt.congr
  intro t _ht
  have hrt : flatEndReparam t ∈ Set.uIcc (0:ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact flatEndReparam_mem_unit t
  have h_speed := pathSpeed_flatEndReparam_comp_eq γ t (hγ_diff (flatEndReparam t) hrt)
  show deriv flatEndReparam t • h (flatEndReparam t) =
    α.toFun (γ (flatEndReparam t)) (pathSpeed (γ ∘ flatEndReparam) t)
  rw [h_speed]
  have h_lin : α.toFun (γ (flatEndReparam t))
        (((deriv flatEndReparam t : ℝ) : ℂ) * pathSpeed γ (flatEndReparam t)) =
      ((deriv flatEndReparam t : ℝ) : ℂ) *
        α.toFun (γ (flatEndReparam t)) (pathSpeed γ (flatEndReparam t)) := by
    have h_ml := (α.toFun (γ (flatEndReparam t))).map_smul
      ((deriv flatEndReparam t : ℝ) : ℂ) (pathSpeed γ (flatEndReparam t))
    simp only [smul_eq_mul] at h_ml
    exact h_ml
  rw [h_lin]
  show (deriv flatEndReparam t : ℝ) • h (flatEndReparam t) =
    ((deriv flatEndReparam t : ℝ) : ℂ) * h (flatEndReparam t)
  exact Complex.real_smul


/-- **§3 sub-piece B — smoothness of the lift.** A continuous lift `Γ` of `δ`
through a non-critical point inherits `δ`'s chart-pullback differentiability.
Given `Γ` continuous at `t₀`, `f ∘ Γ = δ` near `t₀`, `Γ t₀` off the critical set,
and `δ` chart-pullback-differentiable at `t₀`, the lift `Γ` is chart-pullback
differentiable at `t₀`.

Proof: take the two-sided local inverse `g` at `Γ t₀`
(`exists_twoSided_localInverse`). Near `t₀`, `Γ = g ∘ δ` directly from `g∘f=id`
near `Γ t₀` + continuity of `Γ` + `f∘Γ=δ` (no lift-uniqueness needed). In charts,
`(chart_Γt₀)∘Γ =ᶠ G∘d` where `G = (chart_Γt₀)∘g∘(chart_δt₀).symm` is the chart
representation of the holomorphic `g` and `d = (chart_δt₀)∘δ`. `G` is `ℂ`-, hence
`ℝ`-differentiable (via `writtenInExtChartAt` + `restrictScalars`), so the chain
rule and `congr_of_eventuallyEq` conclude. Mirrors `IsClosedSmoothLoop.comp` /
`pathSpeed_comp_eq_mfderiv`. Foundation for assembling the lift into a smooth loop. -/
theorem differentiableAt_chart_lift_of_notMem_criticalSet
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (Γ : ℝ → X) {t₀ : ℝ}
    (hΓ_cont : ContinuousAt Γ t₀)
    (hfΓδ : ∀ᶠ t in 𝓝 t₀, f (Γ t) = δ t)
    (hΓcrit : Γ t₀ ∉ criticalSet f)
    (hδ_diff : DifferentiableAt ℝ ((chartAt (H := ℂ) (δ t₀)).toFun ∘ δ) t₀) :
    DifferentiableAt ℝ ((chartAt (H := ℂ) (Γ t₀)).toFun ∘ Γ) t₀ := by
  classical
  obtain ⟨g, V, hVopen, hfΓt₀V, hgfΓ, hsec, hg_smooth, hgf_id⟩ :=
    exists_twoSided_localInverse f hf hnonconst hΓcrit
  have hfΓt₀ : f (Γ t₀) = δ t₀ := hfΓδ.self_of_nhds
  have hδt₀V : δ t₀ ∈ V := hfΓt₀ ▸ hfΓt₀V
  have hgδt₀ : g (δ t₀) = Γ t₀ := hfΓt₀ ▸ hgfΓ
  -- Near `t₀`, the lift coincides with `g ∘ δ`.
  have hΓ_eq : Γ =ᶠ[𝓝 t₀] g ∘ δ := by
    have hgf_along : ∀ᶠ t in 𝓝 t₀, (g ∘ f) (Γ t) = id (Γ t) := hΓ_cont.tendsto.eventually hgf_id
    filter_upwards [hgf_along, hfΓδ] with t h1 h2
    show Γ t = g (δ t)
    rw [← h2]
    exact h1.symm
  -- `δ` is continuous at `t₀` (it equals `f ∘ Γ` near `t₀`).
  have hδ_contAt : ContinuousAt δ t₀ :=
    (hf.continuous.continuousAt.comp hΓ_cont).congr hfΓδ
  have hδ_source : ∀ᶠ t in 𝓝 t₀, δ t ∈ (chartAt (H := ℂ) (δ t₀)).source :=
    hδ_contAt.eventually_mem
      ((chartAt (H := ℂ) (δ t₀)).open_source.mem_nhds (mem_chart_source ℂ (δ t₀)))
  -- `g` is `MDifferentiableAt` at `δ t₀ ∈ V`.
  have hg_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (δ t₀) :=
    (hg_smooth.contMDiffAt (hVopen.mem_nhds hδt₀V)).mdifferentiableAt (by decide : ω ≠ 0)
  -- Chart representation `G` of `g` and chart pullback `d` of `δ`.
  set d : ℝ → ℂ := (chartAt (H := ℂ) (δ t₀)).toFun ∘ δ with hd_def
  set G : ℂ → ℂ :=
    fun z => (chartAt (H := ℂ) (Γ t₀)).toFun (g ((chartAt (H := ℂ) (δ t₀)).symm z)) with hG_def
  -- `G` is `ℝ`-differentiable at `d t₀` (holomorphic `g` in charts).
  have hG_diff_ℝ : DifferentiableAt ℝ G (d t₀) := by
    have hG_diff_ℂ : DifferentiableAt ℂ G (d t₀) := by
      have h1 := hg_mdiff.differentiableWithinAt_writtenInExtChartAt
      rw [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at h1
      rw [hG_def, show (chartAt (H := ℂ) (Γ t₀)) = (chartAt (H := ℂ) (g (δ t₀))) from by rw [hgδt₀]]
      convert h1 using 2
    have hFD_ℂ := hG_diff_ℂ.hasFDerivAt
    have hFD_ℝ : HasFDerivAt G ((fderiv ℂ G (d t₀)).restrictScalars ℝ) (d t₀) := by
      rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hFD_ℂ ⊢
      simp only [ContinuousLinearMap.coe_restrictScalars']
      exact hFD_ℂ
    exact hFD_ℝ.differentiableAt
  -- Assemble: `chart_Γt₀ ∘ Γ =ᶠ G ∘ d`, then chain rule.
  have hcomp_eq : ((chartAt (H := ℂ) (Γ t₀)).toFun ∘ (g ∘ δ)) =ᶠ[𝓝 t₀] (G ∘ d) := by
    filter_upwards [hδ_source] with t ht
    show (chartAt (H := ℂ) (Γ t₀)) (g (δ t)) =
      (chartAt (H := ℂ) (Γ t₀)) (g ((chartAt (H := ℂ) (δ t₀)).symm ((chartAt (H := ℂ) (δ t₀)) (δ t))))
    rw [(chartAt (H := ℂ) (δ t₀)).left_inv ht]
  have hΓchart_eq : ((chartAt (H := ℂ) (Γ t₀)).toFun ∘ Γ) =ᶠ[𝓝 t₀] (G ∘ d) :=
    (hΓ_eq.fun_comp (chartAt (H := ℂ) (Γ t₀)).toFun).trans hcomp_eq
  rw [hΓchart_eq.differentiableAt_iff]
  exact hG_diff_ℝ.comp t₀ hδ_diff

/-- **Velocity-section continuity of the seam-flattening reparametrization.** For a closed
smooth loop `δ` in `Y`, the velocity tangent-section of `δ ∘ flatEndReparam` is
`ContinuousOn (Icc 0 1)` — i.e. `δ ∘ flatEndReparam` (the base loop the §3 lifts cover)
satisfies the `velCont` regularity. Via `velCont_reparam` with `σ = flatEndReparam`
(monotone, `C²`, mapping `[0,1]` into `[0,1]`), the chain-rule input being
`pathSpeed_flatEndReparam_comp_eq`. Feeds the interior case of each lift's `velCont`. -/
private theorem velCont_flatEndReparam (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) :
    ContinuousOn (fun s : ℝ => Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := Y))
        ((δ ∘ flatEndReparam) s) (pathSpeed (δ ∘ flatEndReparam) s))
      (Set.Icc 0 1) := by
  refine velCont_reparam δ flatEndReparam (deriv flatEndReparam) (D := Set.Icc 0 1)
    (fun s _ => flatEndReparam_mem_unit s) differentiable_flatEndReparam.continuous.continuousOn
    ((Complex.continuous_ofReal.comp
      ((contDiff_flatEndReparam (n := 2)).continuous_deriv (by norm_num))).continuousOn)
    (fun s _ => ?_) hδ.velCont
  have hrt : flatEndReparam s ∈ Set.uIcc (0:ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact flatEndReparam_mem_unit s
  rw [pathSpeed_flatEndReparam_comp_eq δ s (hδ.diff (flatEndReparam s) hrt), smul_eq_mul]

/-- **Velocity-section germ invariance.** If two paths agree near `t₀`, their velocity
tangent-sections agree near `t₀`: the section value at `s`, `⟨γ s, pathSpeed γ s⟩`, depends
on `γ` only through its germ at `s` (base point `γ s`, chart-pullback derivative `pathSpeed γ s`).
Lets a lift's `velCont` be read off a locally-coinciding model path — `const` near the
seam-flat ends, `g ∘ δr` (a local two-sided inverse `g`) in the interior. -/
private theorem velsection_eventuallyEq_of_eventuallyEq {γ h : ℝ → X} {t₀ : ℝ}
    (hγh : γ =ᶠ[𝓝 t₀] h) :
    (fun s : ℝ => Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s) (pathSpeed γ s))
      =ᶠ[𝓝 t₀]
    (fun s : ℝ => Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (h s) (pathSpeed h s)) := by
  filter_upwards [hγh, hγh.eventuallyEq_nhds] with s hs hs_nhds
  have hps : pathSpeed γ s = pathSpeed h s := by
    show fderiv ℝ ((chartAt (H := ℂ) (γ s)).toFun ∘ γ) s 1
       = fderiv ℝ ((chartAt (H := ℂ) (h s)).toFun ∘ h) s 1
    rw [hs, (hs_nhds.fun_comp (chartAt (H := ℂ) (h s)).toFun).fderiv_eq]
  rw [hps, hs]

/-- **Pointwise local velocity-section continuity under post-composition** — the
`ContinuousWithinAt` companion of `velCont_compOn`. At a single `t₀ ∈ [0,1]`, if the base
velocity section of `γ` is `ContinuousWithinAt` and `γ` lands in the open `C^ω`-domain `V`
of `g` near `t₀`, then the velocity section of `g ∘ γ` is `ContinuousWithinAt`. This is what
patches the §3 lift's `velCont` chart-by-chart: each interior point lies in some local
two-sided inverse's domain, where the lift coincides with `g ∘ δr`. -/
private theorem velContWithinAt_compOn (g : Y → X) {V : Set Y}
    (hg : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g V) (hVo : IsOpen V) (γ : ℝ → Y) (hγc : Continuous γ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc (0:ℝ) 1)
    (hγV : ∀ᶠ s in 𝓝[Set.Icc (0:ℝ) 1] t₀, γ s ∈ V)
    (hγdiff : ∀ᶠ s in 𝓝[Set.Icc (0:ℝ) 1] t₀,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ s)).toFun ∘ γ) s)
    (hγ : ContinuousWithinAt (fun s : ℝ => (Bundle.TotalSpace.mk' ℂ
      (E := TangentSpace 𝓘(ℂ) (M := Y)) (γ s) (pathSpeed γ s))) (Set.Icc 0 1) t₀) :
    ContinuousWithinAt (fun s : ℝ => (Bundle.TotalSpace.mk' ℂ
      (E := TangentSpace 𝓘(ℂ) (M := X)) (g (γ s)) (pathSpeed (g ∘ γ) s))) (Set.Icc 0 1) t₀ := by
  have hγt₀V : γ t₀ ∈ V := hγV.self_of_nhdsWithin ht₀
  set S : ℝ → Bundle.TotalSpace ℂ (TangentSpace 𝓘(ℂ) (M := Y)) :=
    fun s => Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := Y)) (γ s) (pathSpeed γ s) with hS
  have htmw : ContinuousOn (tangentMapWithin 𝓘(ℂ) 𝓘(ℂ) g V) (Bundle.TotalSpace.proj ⁻¹' V) :=
    hg.continuousOn_tangentMapWithin (by decide : (1 : WithTop ℕ∞) ≤ ω) hVo.uniqueMDiffOn
  have htmw_at : ContinuousWithinAt (tangentMapWithin 𝓘(ℂ) 𝓘(ℂ) g V)
      (Bundle.TotalSpace.proj ⁻¹' V) (S t₀) := htmw (S t₀) hγt₀V
  have hS_tendsto : Filter.Tendsto S (𝓝[Set.Icc 0 1] t₀)
      (𝓝[Bundle.TotalSpace.proj ⁻¹' V] (S t₀)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hγ, by filter_upwards [hγV] with s hs using hs⟩
  have hcomp : ContinuousWithinAt (tangentMapWithin 𝓘(ℂ) 𝓘(ℂ) g V ∘ S) (Set.Icc 0 1) t₀ :=
    htmw_at.tendsto.comp hS_tendsto
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hγV, hγdiff] with s hsV hsdiff
    have hgmdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (γ s) :=
      (hg.contMDiffAt (hVo.mem_nhds hsV)).mdifferentiableAt (by decide : ω ≠ 0)
    show Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (g (γ s)) (pathSpeed (g ∘ γ) s)
        = tangentMapWithin 𝓘(ℂ) 𝓘(ℂ) g V (S s)
    rw [tangentMapWithin_eq_tangentMap (hVo.uniqueMDiffWithinAt hsV) hgmdiff]
    simp only [tangentMap, Bundle.TotalSpace.mk']
    congr 1
    exact pathSpeed_comp_eq_mfderiv_of_mdiff g γ s hgmdiff hγc.continuousAt hsdiff
  · have hgmdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (γ t₀) :=
      (hg.contMDiffAt (hVo.mem_nhds hγt₀V)).mdifferentiableAt (by decide : ω ≠ 0)
    show Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (g (γ t₀)) (pathSpeed (g ∘ γ) t₀)
        = tangentMapWithin 𝓘(ℂ) 𝓘(ℂ) g V (S t₀)
    rw [tangentMapWithin_eq_tangentMap (hVo.uniqueMDiffWithinAt hγt₀V) hgmdiff]
    simp only [tangentMap, Bundle.TotalSpace.mk']
    congr 1
    exact pathSpeed_comp_eq_mfderiv_of_mdiff g γ t₀ hgmdiff hγc.continuousAt
      (hγdiff.self_of_nhdsWithin ht₀)

/-- **§3 sub-piece C — the seam-flattened smooth lift.** Lifting the *reparametrized*
loop `δ ∘ flatEndReparam` (constant near `0,1`) off the branch locus from a fibre
point `e` yields a genuine smooth path with **zero endpoint velocity**:

* `Γ` is constant `= e` near `0` and constant `= Γ 1` near `1` (continuity + local
  injectivity of `f`, using the lift's `projIcc` clamp), so it is chart-differentiable
  with zero velocity at both endpoints;
* on the interior `(0,1)`, `Γ` is chart-differentiable by sub-piece B;
* its **velocity tangent-section is `ContinuousOn [0,1]`** (`velCont`): off the endpoints via
  `velContWithinAt_compOn` (each interior point lies in a local two-sided inverse `g`'s domain,
  where `Γ =ᶠ g ∘ δr`), and at the seam-flat ends via `velsection_eventuallyEq_of_eventuallyEq`
  against the constant path — so `Γ` is a full `IsSmoothPath`, not merely chart-differentiable;
* its endpoint `Γ 1` lies in the same fibre (`f (Γ 1) = δ 0`), the monodromy target.

This is the per-segment building block of the orbit construction: concatenating these
over a monodromy orbit (zero junction velocities ⇒ `IsSmoothPath.concat`) closes the
lift into a smooth loop. The base loop is `δ ∘ flatEndReparam`, a reparametrization of
`δ` (its period vector is unchanged — recorded separately). -/
theorem exists_smoothLift_flatEnd_off_branchLocus
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) (havoid : ∀ t : ℝ, δ t ∉ branchLocus f)
    {e : X} (he : f e = δ 0) :
    ∃ Γ : ℝ → X,
      Continuous Γ ∧ Γ 0 = e ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, f (Γ t) = δ (flatEndReparam t)) ∧
      (∀ t ∈ Set.uIcc (0:ℝ) 1, DifferentiableAt ℝ ((chartAt (H := ℂ) (Γ t)).toFun ∘ Γ) t) ∧
      ContinuousOn (fun s : ℝ => Bundle.TotalSpace.mk' ℂ
          (E := TangentSpace 𝓘(ℂ) (M := X)) (Γ s) (pathSpeed Γ s)) (Set.Icc 0 1) ∧
      pathSpeed Γ 0 = 0 ∧ pathSpeed Γ 1 = 0 ∧
      f (Γ 1) = δ 0 := by
  classical
  -- The reparametrized base loop `δr = δ ∘ flatEndReparam`, constant near the endpoints.
  set δr : ℝ → Y := δ ∘ flatEndReparam with hδr_def
  have hδr_cont : Continuous δr := hδ.cont.comp differentiable_flatEndReparam.continuous
  have hδr_avoid : ∀ t : ℝ, δr t ∉ branchLocus f := fun t => havoid (flatEndReparam t)
  have hδr0 : δr 0 = δ 0 := by show δ (flatEndReparam 0) = δ 0; rw [flatEndReparam_zero]
  have he' : f e = δr 0 := by rw [hδr0]; exact he
  -- Lift `δr` from `e` (sub-piece A), exposing the endpoint clamps.
  obtain ⟨Γ, hΓ_cont, hΓ_lift, hΓ0, hΓ_clampL, hΓ_clampR⟩ :=
    exists_continuous_lift_off_branchLocus f hf hnonconst δr hδr_cont hδr_avoid he'
  -- `f (Γ 1) = δ 0`.
  have hfΓ1 : f (Γ 1) = δ 0 := by
    rw [hΓ_lift 1 ⟨zero_le_one, le_rfl⟩]; show δ (flatEndReparam 1) = δ 0
    rw [flatEndReparam_one]; exact hδ.closed.symm
  -- `δr` is chart-pullback-differentiable on `[0,1]` (chain rule `δ ∘ flatEndReparam`).
  have hδr_diff : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (δr t)).toFun ∘ δr) t := by
    intro t _
    have hrt : flatEndReparam t ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact flatEndReparam_mem_unit t
    have hδr_comp : ((chartAt (H := ℂ) (δr t)).toFun ∘ δr) =
        ((chartAt (H := ℂ) (δ (flatEndReparam t))).toFun ∘ δ) ∘ flatEndReparam := by
      funext s; rfl
    rw [hδr_comp]
    exact (hδ.diff (flatEndReparam t) hrt).comp t (differentiable_flatEndReparam t)
  -- `Γ` is constant `= e` near `0`.
  have hΓ_const0 : Γ =ᶠ[𝓝 (0:ℝ)] (fun _ => e) := by
    have he_crit : e ∉ criticalSet f := fun hmem => (havoid 0) ⟨e, hmem, he⟩
    obtain ⟨U, hUopen, heU, hinj, -⟩ := isLocalHomeoOffCritical f hf hnonconst he_crit
    have hΓU : ∀ᶠ t in 𝓝 (0:ℝ), Γ t ∈ U :=
      hΓ_cont.continuousAt.eventually_mem (by rw [hΓ0]; exact hUopen.mem_nhds heU)
    have hfΓ0 : ∀ᶠ t in 𝓝 (0:ℝ), f (Γ t) = δ 0 := by
      filter_upwards [Iic_mem_nhds (show (0:ℝ) < 1/4 by norm_num)] with t ht
      simp only [Set.mem_Iic] at ht
      rcases le_or_gt t 0 with htle | htpos
      · rw [hΓ_clampL t htle, he]
      · rw [hΓ_lift t ⟨htpos.le, by linarith⟩]
        show δ (flatEndReparam t) = δ 0; rw [flatEndReparam_eqZero_of_le ht]
    filter_upwards [hΓU, hfΓ0] with t htU htf
    exact hinj htU heU (htf.trans he.symm)
  -- `Γ` is constant `= Γ 1` near `1`.
  have hΓ_const1 : Γ =ᶠ[𝓝 (1:ℝ)] (fun _ => Γ 1) := by
    have hΓ1_crit : Γ 1 ∉ criticalSet f := fun hmem => (havoid 0) ⟨Γ 1, hmem, hfΓ1⟩
    obtain ⟨U, hUopen, hΓ1U, hinj, -⟩ := isLocalHomeoOffCritical f hf hnonconst hΓ1_crit
    have hΓU : ∀ᶠ t in 𝓝 (1:ℝ), Γ t ∈ U :=
      hΓ_cont.continuousAt.eventually_mem (hUopen.mem_nhds hΓ1U)
    have hfΓ1' : ∀ᶠ t in 𝓝 (1:ℝ), f (Γ t) = δ 0 := by
      filter_upwards [Ici_mem_nhds (show (3/4:ℝ) < 1 by norm_num)] with t ht
      simp only [Set.mem_Ici] at ht
      rcases le_or_gt 1 t with htge | htlt
      · rw [hΓ_clampR t htge, hfΓ1]
      · rw [hΓ_lift t ⟨by linarith, htlt.le⟩]
        show δ (flatEndReparam t) = δ 0; rw [flatEndReparam_eqOne_of_ge ht]; exact hδ.closed.symm
    filter_upwards [hΓU, hfΓ1'] with t htU htf
    exact hinj htU hΓ1U (htf.trans hfΓ1.symm)
  -- Chart-pullback differentiability on `[0,1]`.
  have hΓ_diff : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (Γ t)).toFun ∘ Γ) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    obtain ⟨ht0, ht1⟩ := ht
    rcases eq_or_lt_of_le ht0 with rfl | h0pos
    · have hc : ((chartAt (H := ℂ) (Γ 0)).toFun ∘ Γ) =ᶠ[𝓝 (0:ℝ)]
          (fun _ => (chartAt (H := ℂ) (Γ 0)).toFun e) := hΓ_const0.fun_comp _
      rw [hc.differentiableAt_iff]; exact differentiableAt_const _
    · rcases eq_or_lt_of_le ht1 with rfl | h1lt
      · have hc : ((chartAt (H := ℂ) (Γ 1)).toFun ∘ Γ) =ᶠ[𝓝 (1:ℝ)]
            (fun _ => (chartAt (H := ℂ) (Γ 1)).toFun (Γ 1)) := hΓ_const1.fun_comp _
        rw [hc.differentiableAt_iff]; exact differentiableAt_const _
      · refine differentiableAt_chart_lift_of_notMem_criticalSet f hf hnonconst δr Γ
          hΓ_cont.continuousAt ?_ ?_ ?_
        · filter_upwards [Ioo_mem_nhds h0pos h1lt] with s hs
          exact hΓ_lift s ⟨hs.1.le, hs.2.le⟩
        · exact fun hmem => (hδr_avoid t) ⟨Γ t, hmem, hΓ_lift t ⟨h0pos.le, h1lt.le⟩⟩
        · exact hδr_diff t (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨h0pos.le, h1lt.le⟩)
  -- Zero endpoint velocities (chart pullback is eventually constant).
  have hps0 : pathSpeed Γ 0 = 0 := by
    have hc : ((chartAt (H := ℂ) (Γ 0)).toFun ∘ Γ) =ᶠ[𝓝 (0:ℝ)]
        (fun _ => (chartAt (H := ℂ) (Γ 0)).toFun e) := hΓ_const0.fun_comp _
    show fderiv ℝ ((chartAt (H := ℂ) (Γ 0)).toFun ∘ Γ) 0 1 = 0
    rw [hc.fderiv_eq]; simp
  have hps1 : pathSpeed Γ 1 = 0 := by
    have hc : ((chartAt (H := ℂ) (Γ 1)).toFun ∘ Γ) =ᶠ[𝓝 (1:ℝ)]
        (fun _ => (chartAt (H := ℂ) (Γ 1)).toFun (Γ 1)) := hΓ_const1.fun_comp _
    show fderiv ℝ ((chartAt (H := ℂ) (Γ 1)).toFun ∘ Γ) 1 1 = 0
    rw [hc.fderiv_eq]; simp
  -- **Velocity-section continuity** (`velCont`). At each `t₀ ∈ [0,1]`, the section is read
  -- off a locally-coinciding model path (`velsection_eventuallyEq_of_eventuallyEq`): near the
  -- seam-flat endpoints `Γ` is constant (`isSmoothPath_const`), and at every interior point
  -- `Γ =ᶠ g ∘ δr` for a local two-sided inverse `g`, handled by `velContWithinAt_compOn`.
  have hvelCont : ContinuousOn (fun s : ℝ => Bundle.TotalSpace.mk' ℂ
      (E := TangentSpace 𝓘(ℂ) (M := X)) (Γ s) (pathSpeed Γ s)) (Set.Icc 0 1) := by
    intro t₀ ht₀
    obtain ⟨ht0, ht1⟩ := ht₀
    rcases eq_or_lt_of_le ht0 with rfl | h0pos
    · -- `t₀ = 0`: plateau, `Γ =ᶠ[𝓝 0] (fun _ => e)`.
      exact ((isSmoothPath_const e).velCont 0 (Set.left_mem_Icc.mpr zero_le_one)).congr_of_eventuallyEq
        ((velsection_eventuallyEq_of_eventuallyEq hΓ_const0).filter_mono nhdsWithin_le_nhds)
        (velsection_eventuallyEq_of_eventuallyEq hΓ_const0).self_of_nhds
    · rcases eq_or_lt_of_le ht1 with rfl | h1lt
      · -- `t₀ = 1`: plateau, `Γ =ᶠ[𝓝 1] (fun _ => Γ 1)`.
        exact ((isSmoothPath_const (Γ 1)).velCont 1 (Set.right_mem_Icc.mpr zero_le_one)).congr_of_eventuallyEq
          ((velsection_eventuallyEq_of_eventuallyEq hΓ_const1).filter_mono nhdsWithin_le_nhds)
          (velsection_eventuallyEq_of_eventuallyEq hΓ_const1).self_of_nhds
      · -- interior `0 < t₀ < 1`: local two-sided inverse `g`, `Γ =ᶠ g ∘ δr`, `velContWithinAt_compOn`.
        have ht01 : t₀ ∈ Set.Icc (0:ℝ) 1 := ⟨h0pos.le, h1lt.le⟩
        have hΓcrit : Γ t₀ ∉ criticalSet f :=
          fun hmem => (hδr_avoid t₀) ⟨Γ t₀, hmem, hΓ_lift t₀ ht01⟩
        obtain ⟨g, V, hVopen, hfΓtV, hgfΓ, hsec, hg_smooth, hgf_id⟩ :=
          exists_twoSided_localInverse f hf hnonconst hΓcrit
        have hδrtV : δr t₀ ∈ V := hΓ_lift t₀ ht01 ▸ hfΓtV
        have hγV : ∀ᶠ s in 𝓝[Set.Icc (0:ℝ) 1] t₀, δr s ∈ V :=
          (hδr_cont.continuousAt.eventually_mem (hVopen.mem_nhds hδrtV)).filter_mono nhdsWithin_le_nhds
        have hγdiff : ∀ᶠ s in 𝓝[Set.Icc (0:ℝ) 1] t₀,
            DifferentiableAt ℝ ((chartAt (H := ℂ) (δr s)).toFun ∘ δr) s :=
          Filter.eventually_of_mem self_mem_nhdsWithin fun s hs =>
            hδr_diff s (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hs)
        have hγ : ContinuousWithinAt (fun s : ℝ => Bundle.TotalSpace.mk' ℂ
            (E := TangentSpace 𝓘(ℂ) (M := Y)) (δr s) (pathSpeed δr s)) (Set.Icc 0 1) t₀ :=
          velCont_flatEndReparam δ hδ t₀ ht01
        -- Near `t₀`, the lift coincides with `g ∘ δr`.
        have hΓ_eq : Γ =ᶠ[𝓝 t₀] g ∘ δr := by
          have hfΓδr : ∀ᶠ s in 𝓝 t₀, f (Γ s) = δr s := by
            filter_upwards [Ioo_mem_nhds h0pos h1lt] with s hs
            exact hΓ_lift s ⟨hs.1.le, hs.2.le⟩
          have hgf_along : ∀ᶠ s in 𝓝 t₀, (g ∘ f) (Γ s) = id (Γ s) :=
            hΓ_cont.continuousAt.tendsto.eventually hgf_id
          filter_upwards [hgf_along, hfΓδr] with s h1 h2
          show Γ s = g (δr s)
          rw [← h2]; exact h1.symm
        exact (velContWithinAt_compOn g hg_smooth hVopen δr hδr_cont ht01 hγV hγdiff
            hγ).congr_of_eventuallyEq
          ((velsection_eventuallyEq_of_eventuallyEq hΓ_eq).filter_mono nhdsWithin_le_nhds)
          (velsection_eventuallyEq_of_eventuallyEq hΓ_eq).self_of_nhds
  exact ⟨Γ, hΓ_cont, hΓ0, hΓ_lift, hΓ_diff, hvelCont, hps0, hps1, hfΓ1⟩

/-! ## §3 monodromy decomposition of the preimage-cycle lift

`exists_preimageLoopFamily` (the geometric heart) is assembled from three leaf
statements, bottomed-out below. The new analytic-free route replaces the old
segment-partition/sheet-reassembly projection plan with a single **pointwise
fibre-sum identity** (leaf D), made possible by carrying a *global* lift family
along `δr := δ ∘ flatEndReparam`:

* `MonodromyLiftFamily f δ` — the interface: a finite family of seam-flattened
  smooth lifts `Γ i` of `δr`, whose time-`t` values `i ↦ Γ i t` sweep the fibre
  `f⁻¹(δr t)` *bijectively* for every `t ∈ [0,1]`. The bijection at `t = 1` is the
  monodromy permutation; the bijection at general `t` is what reindexes the trace
  fibre-sum in the projection formula.
* `exists_monodromyLiftFamily` (leaf A+B) — construct it off the branch locus
  (one seam-flattened lift per fibre point, with `velCont`; injectivity by lift
  uniqueness, surjectivity by fibre-cardinality constancy).
* `lineIntegral_traceFormTotal_eq_sum_periodVec` (leaf D) — the projection formula
  `∫_δ trace(ωⱼ) = ∑ᵢ periodVec(Γᵢ)ⱼ`, via the pointwise identity
  `trace(ωⱼ)(δr t)(δr' t) = ∑ᵢ ωⱼ(Γᵢ t)(Γᵢ' t)` (fibre-sum reindexed by the
  bijection; each summand `= ωⱼ(Γᵢ t)((mfderiv f)⁻¹ δr' t)` with the inverse hitting
  `Γᵢ' t` since `f ∘ Γᵢ = δr`).
* `exists_orbitLoops_of_monodromyLiftFamily` (leaf E) — group the lifts into closed
  smooth loops along the `σ`-orbits (iterated `concat`, junction velocities `0`),
  accounting both period identities.
-/

/-- **Interface for the §3 monodromy construction.** A finite family of
seam-flattened smooth lifts `Γ i` of `δr = δ ∘ flatEndReparam`, whose time-`t`
evaluations `i ↦ Γ i t` sweep the fibre `f⁻¹(δr t)` injectively and surjectively
for every `t ∈ [0,1]`. Carrying the whole family at once (rather than local sheets)
is what turns the projection formula into a pointwise fibre-sum identity, and the
`t = 1` bijection is the monodromy permutation driving the orbit loops. -/
structure MonodromyLiftFamily (f : X → Y) (δ : ℝ → Y) where
  /-- Number of lifts `= #fibre = #sheets`. -/
  n : ℕ
  /-- The lifts, `Γ i : ℝ → X`. -/
  Γ : Fin n → ℝ → X
  /-- Each lift is a smooth path (from `Γ i 0` to `Γ i 1`), carrying `velCont`. -/
  smooth : ∀ i, IsSmoothPath (Γ i 0) (Γ i 1) (Γ i)
  /-- Seam-flattened: zero start velocity (for orbit `concat` junctions). -/
  velZero_zero : ∀ i, pathSpeed (Γ i) 0 = 0
  /-- Seam-flattened: zero end velocity. -/
  velZero_one : ∀ i, pathSpeed (Γ i) 1 = 0
  /-- `Γ i` lifts `δr`: `f ∘ Γ i = δ ∘ flatEndReparam` on `[0,1]`. -/
  lifts : ∀ i, Set.EqOn (f ∘ Γ i) (δ ∘ flatEndReparam) (Set.Icc 0 1)
  /-- For each `t ∈ [0,1]`, the lifts are pairwise distinct at time `t`. -/
  fibre_inj : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective fun i => Γ i t
  /-- For each `t ∈ [0,1]`, the lifts sweep out the *entire* fibre over `δr t`. -/
  fibre_surj : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : X,
    f x = δ (flatEndReparam t) → ∃ i, Γ i t = x

/-- **The lift count is the regular-fibre cardinality.** At `t = 0` the map
`i ↦ Γ i 0` is a bijection from `Fin M.n` onto the fibre `f⁻¹{δ(flatEndReparam 0)}`
(injective by `fibre_inj`, onto by `fibre_surj`), so `M.n` equals that fibre's
`ncard`. This is what pins the cycle's sheet count to a *regular* fibre. -/
lemma MonodromyLiftFamily.n_eq_fibre_ncard {f : X → Y} {δ : ℝ → Y}
    (M : MonodromyLiftFamily f δ) :
    M.n = (f ⁻¹' {δ (flatEndReparam 0)}).ncard := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := Set.left_mem_Icc.mpr zero_le_one
  have hinj : Function.Injective (fun i => M.Γ i 0) := M.fibre_inj 0 h0
  have hrange : Set.range (fun i => M.Γ i 0) = f ⁻¹' {δ (flatEndReparam 0)} := by
    apply Set.Subset.antisymm
    · rintro z ⟨i, rfl⟩
      show f (M.Γ i 0) = δ (flatEndReparam 0)
      exact M.lifts i h0
    · intro x hx
      exact M.fibre_surj 0 h0 x hx
  rw [← hrange, ← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]


/-- **Lift uniqueness on `[0,1]`.** Two continuous lifts `Γ₁, Γ₂` of the same base path `β`
(off the branch locus) that agree at one time `t₀ ∈ [0,1]` agree on all of `[0,1]`. The
agreement set is clopen in the connected `[0,1]`: closed as the equalizer of continuous maps
into the `T₂` space `X`, and open because at any agreement point `Γ₁ s = Γ₂ s` the value is
off-critical, where `f` is locally injective (`isLocalHomeoOffCritical`) — and both lifts
project to `β`, so local injectivity forces them to coincide nearby. Drives `fibre_inj`. -/
private theorem lift_eqOn_Icc_of_eq {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) {β : ℝ → Y}
    (hβ : ∀ t ∈ Set.Icc (0:ℝ) 1, β t ∉ branchLocus f)
    {Γ₁ Γ₂ : ℝ → X} (hc₁ : Continuous Γ₁) (hc₂ : Continuous Γ₂)
    (hl₁ : ∀ t ∈ Set.Icc (0:ℝ) 1, f (Γ₁ t) = β t)
    (hl₂ : ∀ t ∈ Set.Icc (0:ℝ) 1, f (Γ₂ t) = β t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc (0:ℝ) 1) (heq : Γ₁ t₀ = Γ₂ t₀) :
    Set.EqOn Γ₁ Γ₂ (Set.Icc (0:ℝ) 1) := by
  classical
  haveI : PreconnectedSpace ↥(Set.Icc (0:ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  set S : Set ↥(Set.Icc (0:ℝ) 1) := {p | Γ₁ ↑p = Γ₂ ↑p} with hS_def
  have hclosed : IsClosed S :=
    isClosed_eq (hc₁.comp continuous_subtype_val) (hc₂.comp continuous_subtype_val)
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hpeq : Γ₁ ↑p = Γ₂ ↑p := hp
    have hx₀crit : Γ₁ ↑p ∉ criticalSet f :=
      fun hmem => hβ ↑p p.2 ⟨Γ₁ ↑p, hmem, hl₁ ↑p p.2⟩
    obtain ⟨U, hUopen, hx₀U, hinj, -⟩ := isLocalHomeoOffCritical f hf hnonconst hx₀crit
    have h1U := (hc₁.comp continuous_subtype_val).continuousAt.eventually_mem (hUopen.mem_nhds hx₀U)
    have h2U := (hc₂.comp continuous_subtype_val).continuousAt.eventually_mem
      (hUopen.mem_nhds (hpeq ▸ hx₀U))
    filter_upwards [h1U, h2U] with q hq1 hq2
    exact hinj hq1 hq2 ((hl₁ ↑q q.2).trans (hl₂ ↑q q.2).symm)
  have hSuniv : S = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨t₀, ht₀⟩, heq⟩
  intro t ht
  have : (⟨t, ht⟩ : ↥(Set.Icc (0:ℝ) 1)) ∈ S := by rw [hSuniv]; exact Set.mem_univ _
  exact this

/-- **Leaf A + B — construct the monodromy lift family.** Off the branch locus, the
seam-flattened lifts of `δ` (one per fibre point, `exists_smoothLift_flatEnd_off_branchLocus`
upgraded with `velCont`) assemble into a `MonodromyLiftFamily`: injectivity is lift
uniqueness, surjectivity is constancy of the off-branch fibre cardinality along the
connected `[0,1]` (via the local sheet system). -/
theorem exists_monodromyLiftFamily (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) (havoid : ∀ t : ℝ, δ t ∉ branchLocus f) :
    Nonempty (MonodromyLiftFamily f δ) := by
  classical
  -- The fibre over `δ 0` is finite (off-branch); enumerate it as `Fin n`.
  have hfin : (f ⁻¹' {δ 0}).Finite := fiber_finite_off_branchLocus f hf hnonconst (havoid 0)
  have _ffib : Fintype ↥(f ⁻¹' {δ 0}) := hfin.fintype
  set n : ℕ := Fintype.card ↥(f ⁻¹' {δ 0}) with hn_def
  set enum : Fin n ≃ ↥(f ⁻¹' {δ 0}) := (Fintype.equivFin _).symm with henum_def
  set pt : Fin n → X := fun i => ((enum i : ↥(f ⁻¹' {δ 0})) : X) with hpt_def
  have hpt_fib : ∀ i, f (pt i) = δ 0 := fun i => (enum i).2
  -- One seam-flattened smooth lift per fibre point.
  have hlift : ∀ i : Fin n, ∃ Γ : ℝ → X,
      Continuous Γ ∧ Γ 0 = pt i ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, f (Γ t) = δ (flatEndReparam t)) ∧
      (∀ t ∈ Set.uIcc (0:ℝ) 1, DifferentiableAt ℝ ((chartAt (H := ℂ) (Γ t)).toFun ∘ Γ) t) ∧
      ContinuousOn (fun s : ℝ => Bundle.TotalSpace.mk' ℂ
          (E := TangentSpace 𝓘(ℂ) (M := X)) (Γ s) (pathSpeed Γ s)) (Set.Icc 0 1) ∧
      pathSpeed Γ 0 = 0 ∧ pathSpeed Γ 1 = 0 ∧ f (Γ 1) = δ 0 :=
    fun i => exists_smoothLift_flatEnd_off_branchLocus f hf hnonconst δ hδ havoid (hpt_fib i)
  choose Γ hcont hΓ0 hlifts hdiff hvc hps0 hps1 _hfΓ1 using hlift
  -- `δr` is off-branch everywhere (the lifts cover it on `[0,1]`).
  have hδr_avoid : ∀ t : ℝ, δ (flatEndReparam t) ∉ branchLocus f := fun t => havoid (flatEndReparam t)
  -- **Fibre injectivity** (lift uniqueness): two lifts agreeing at some time `t ∈ [0,1]` agree at
  -- `0`, so their distinct basepoints `pt i` force `i = k`.
  have hfib_inj : ∀ t ∈ Set.Icc (0:ℝ) 1, Function.Injective fun i => Γ i t := by
    intro t ht i k hik
    have hEq : Set.EqOn (Γ i) (Γ k) (Set.Icc (0:ℝ) 1) :=
      lift_eqOn_Icc_of_eq hf hnonconst (fun s _ => hδr_avoid s) (hcont i) (hcont k)
        (hlifts i) (hlifts k) ht hik
    have hpteq : pt i = pt k := by
      rw [← hΓ0 i, ← hΓ0 k]; exact hEq (Set.left_mem_Icc.mpr zero_le_one)
    exact enum.injective (Subtype.ext hpteq)
  -- `ncard` of the range of an injective `Fin m → X` is `m`.
  have hrange_ncard : ∀ {m : ℕ} (g : Fin m → X), Function.Injective g →
      (Set.range g).ncard = m := fun g hg => by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hg, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  -- **Fibre cardinality is constant `= n`** along `[0,1]`: `t ↦ #(f⁻¹{δr t})` is locally constant
  -- (over each `LocalSheetSystem` base the fibre is the range of the injective sheet map, so its
  -- card is the sheet count), hence constant on the connected `[0,1]`; its value at `0` is `n`.
  have hcard : ∀ t ∈ Set.Icc (0:ℝ) 1, (f ⁻¹' {δ (flatEndReparam t)}).ncard = n := by
    set fc : ℝ → ℕ := fun t => (f ⁻¹' {δ (flatEndReparam t)}).ncard with hfc_def
    have hδr_cont : Continuous fun t => δ (flatEndReparam t) :=
      hδ.cont.comp differentiable_flatEndReparam.continuous
    have hfc_cont : ContinuousOn fc (Set.Icc (0:ℝ) 1) := by
      intro t₀ _
      obtain ⟨S⟩ := exists_localSheetSystem f hf hnonconst (hδr_avoid t₀)
      have hcard_sheets : ∀ y ∈ S.V, (f ⁻¹' {y}).ncard = S.n := fun y hy => by
        rw [S.fibre_eq y hy]; exact hrange_ncard _ (S.sheet_inj y hy)
      have hmem : ∀ᶠ t in 𝓝[Set.Icc (0:ℝ) 1] t₀, δ (flatEndReparam t) ∈ S.V :=
        (hδr_cont.continuousAt.eventually_mem (S.isOpen_V.mem_nhds S.mem_V)).filter_mono
          nhdsWithin_le_nhds
      have hloc : ∀ᶠ t in 𝓝[Set.Icc (0:ℝ) 1] t₀, fc t = fc t₀ := by
        filter_upwards [hmem] with t htV
        show (f ⁻¹' {δ (flatEndReparam t)}).ncard = (f ⁻¹' {δ (flatEndReparam t₀)}).ncard
        rw [hcard_sheets _ htV, hcard_sheets _ S.mem_V]
      exact (tendsto_pure.mpr hloc).mono_right (pure_le_nhds _)
    intro t ht
    have hconst := IsPreconnected.constant isPreconnected_Icc hfc_cont ht
      (Set.left_mem_Icc.mpr zero_le_one)
    show fc t = n
    rw [hconst]
    show (f ⁻¹' {δ (flatEndReparam 0)}).ncard = n
    rw [flatEndReparam_zero, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  refine ⟨{
    n := n
    Γ := Γ
    smooth := fun i => ⟨rfl, rfl, hcont i, hdiff i, hvc i⟩
    velZero_zero := hps0
    velZero_one := hps1
    lifts := fun i t ht => hlifts i t ht
    fibre_inj := hfib_inj
    fibre_surj := ?_ }⟩
  -- `fibre_surj`: `i ↦ Γ i t` injects `Fin n` into the `n`-element fibre over `δr t`, so it is onto.
  intro t ht x hx
  have hfibfin : (f ⁻¹' {δ (flatEndReparam t)}).Finite :=
    fiber_finite_off_branchLocus f hf hnonconst (hδr_avoid t)
  have hsub : Set.range (fun i => Γ i t) ⊆ f ⁻¹' {δ (flatEndReparam t)} := by
    rintro z ⟨i, rfl⟩; exact hlifts i t ht
  have heq : Set.range (fun i => Γ i t) = f ⁻¹' {δ (flatEndReparam t)} :=
    Set.eq_of_subset_of_ncard_le hsub
      (le_of_eq (by rw [hcard t ht, hrange_ncard _ (hfib_inj t ht)])) hfibfin
  have hxrange : x ∈ Set.range (fun i => Γ i t) := by rw [heq]; exact hx
  obtain ⟨i, hi⟩ := hxrange
  exact ⟨i, hi⟩

/-- **Per-sheet velocity identity (interior).** At an interior `t ∈ (0,1)`, the trace
summand of `α` at the lift point `M.Γ i t`, evaluated at the reparametrized base
velocity `pathSpeed (δ ∘ flatEndReparam) t`, equals the form `α` at `M.Γ i t` evaluated
at the lift's own velocity `pathSpeed (M.Γ i) t`. The local two-sided inverse `g` at
the (non-critical) point `M.Γ i t` realizes `traceSummand = sheetPullback`, and the
germ identity `M.Γ i =ᶠ g ∘ δr` (same `g∘f=id`-near-the-point factorization as
`differentiableAt_chart_lift_of_notMem_criticalSet`) turns `mfderiv g (δr t)` applied
to the base velocity into `pathSpeed (M.Γ i) t`. -/
private theorem traceSummand_lift_velocity_interior (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) (havoid : ∀ t : ℝ, δ t ∉ branchLocus f)
    (M : MonodromyLiftFamily f δ) (α : HolomorphicOneForms X) (i : Fin M.n) {t : ℝ}
    (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    traceSummand f α (M.Γ i t) (pathSpeed (δ ∘ flatEndReparam) t)
      = α.toFun (M.Γ i t) (pathSpeed (M.Γ i) t) := by
  classical
  set δr : ℝ → Y := δ ∘ flatEndReparam with hδr_def
  -- Membership of `t` in `[0,1]`, base velocity facts.
  have ht01 : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  -- The lift covers `δr` at `t`: `f (Γ i t) = δr t`.
  have hfΓt : f (M.Γ i t) = δr t := M.lifts i ht01
  -- `Γ i t` is off the critical set (else `δr t ∈ branchLocus`, contradicting `havoid`).
  have hΓcrit : M.Γ i t ∉ criticalSet f := by
    intro hmem
    exact (havoid (flatEndReparam t)) ⟨M.Γ i t, hmem, hfΓt⟩
  -- A `C^ω` two-sided local inverse `g` at `Γ i t`.
  obtain ⟨g, V, hVopen, hfΓtV, hgfΓ, hsec, hg_smooth, hgf_id⟩ :=
    exists_twoSided_localInverse f hf hnonconst hΓcrit
  have hδrtV : δr t ∈ V := hfΓt ▸ hfΓtV
  have hgδrt : g (δr t) = M.Γ i t := hfΓt ▸ hgfΓ
  -- `f` and `g` are `MDifferentiableAt` at the relevant points.
  have hf_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (M.Γ i t) := hf.mdifferentiableAt (by decide)
  have hg_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (f (M.Γ i t)) := by
    rw [hfΓt]
    exact (hg_smooth.contMDiffAt (hVopen.mem_nhds hδrtV)).mdifferentiableAt (by decide : ω ≠ 0)
  -- `f ∘ g = id` near `f (Γ i t)` (open `V`).
  have hfs : (f ∘ g) =ᶠ[𝓝 (f (M.Γ i t))] id := by
    rw [hfΓt]
    filter_upwards [hVopen.mem_nhds hδrtV] with y hy
    show f (g y) = y; exact hsec y hy
  -- `g ∘ f = id` near `Γ i t`.
  have hsf : (g ∘ f) =ᶠ[𝓝 (M.Γ i t)] id := hgf_id
  have hgfx : g (f (M.Γ i t)) = M.Γ i t := by rw [hfΓt]; exact hgδrt
  -- The key value identity: `traceSummand f α (Γ i t) = sheetPullback α g (f (Γ i t))`.
  have hval := traceSummand_eq_sheetPullback (f := f) (g := g) (x₀ := M.Γ i t)
    α hgfx hf_mdiff hg_mdiff hfs hsf
  -- `δr` is chart-pullback differentiable at the interior `t` (chain rule on `δ ∘ flatEndReparam`).
  have hδr_diff : DifferentiableAt ℝ ((chartAt (H := ℂ) (δr t)).toFun ∘ δr) t := by
    have hrt : flatEndReparam t ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact flatEndReparam_mem_unit t
    have hδr_comp : ((chartAt (H := ℂ) (δr t)).toFun ∘ δr) =
        ((chartAt (H := ℂ) (δ (flatEndReparam t))).toFun ∘ δ) ∘ flatEndReparam := by
      funext s; rfl
    rw [hδr_comp]
    exact (hδ.diff (flatEndReparam t) hrt).comp t (differentiable_flatEndReparam t)
  -- `δr` is continuous at `t`.
  have hδr_contAt : ContinuousAt δr t :=
    (hδ.cont.comp differentiable_flatEndReparam.continuous).continuousAt
  -- Near `t`, the lift coincides with `g ∘ δr` (same factorization as the lift-smoothness lemma).
  have hΓ_eq : M.Γ i =ᶠ[𝓝 t] g ∘ δr := by
    have hfΓδr : ∀ᶠ s in 𝓝 t, f (M.Γ i s) = δr s := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact M.lifts i ⟨hs.1.le, hs.2.le⟩
    have hΓ_contAt : ContinuousAt (M.Γ i) t := (M.smooth i).cont.continuousAt
    have hgf_along : ∀ᶠ s in 𝓝 t, (g ∘ f) (M.Γ i s) = id (M.Γ i s) :=
      hΓ_contAt.tendsto.eventually hgf_id
    filter_upwards [hgf_along, hfΓδr] with s h1 h2
    show M.Γ i s = g (δr s)
    rw [← h2]; exact h1.symm
  -- `pathSpeed (g ∘ δr) t = mfderiv g (δr t) (pathSpeed δr t)` (chain rule via local section).
  have hps_comp : pathSpeed (g ∘ δr) t = mfderiv 𝓘(ℂ) 𝓘(ℂ) g (δr t) (pathSpeed δr t) := by
    have hg_mdiff' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (δr t) := by
      have := hg_mdiff; rwa [hfΓt] at this
    exact pathSpeed_comp_eq_mfderiv_of_mdiff g δr t hg_mdiff' hδr_contAt hδr_diff
  -- `pathSpeed (Γ i) t = pathSpeed (g ∘ δr) t` (germ invariance of pathSpeed).
  have hps_eq : pathSpeed (M.Γ i) t = pathSpeed (g ∘ δr) t := by
    show fderiv ℝ ((chartAt (H := ℂ) (M.Γ i t)).toFun ∘ M.Γ i) t 1 =
      fderiv ℝ ((chartAt (H := ℂ) ((g ∘ δr) t)).toFun ∘ (g ∘ δr)) t 1
    have hval_t : M.Γ i t = (g ∘ δr) t := hΓ_eq.self_of_nhds
    rw [hval_t, (hΓ_eq.fun_comp (chartAt (H := ℂ) ((g ∘ δr) t)).toFun).fderiv_eq]
  -- Assemble.
  rw [hps_eq, hps_comp, hval]
  show (α.toFun (g (f (M.Γ i t)))).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g (f (M.Γ i t)))
      (pathSpeed δr t) = α.toFun (M.Γ i t) (mfderiv 𝓘(ℂ) 𝓘(ℂ) g (δr t) (pathSpeed δr t))
  rw [hfΓt, hgδrt, ContinuousLinearMap.comp_apply]

/-- **Off-branch trace value at the lift fibre-sum (interior).** At an interior
`t ∈ (0,1)`, the trace form value `(traceForm f hf hnonconst α) (δr t)` (a fibre-sum of
trace summands) evaluated at the base velocity reindexes, via the time-`t` bijection
`i ↦ M.Γ i t` of `Fin M.n` onto the (finite, off-branch) fibre `f⁻¹{δr t}`, to the sum
over the lift family of the per-sheet velocity terms. -/
private theorem traceForm_apply_eq_sum_lift_interior (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (_hδ : IsClosedSmoothLoop δ) (havoid : ∀ t : ℝ, δ t ∉ branchLocus f)
    (M : MonodromyLiftFamily f δ) (α : HolomorphicOneForms X) {t : ℝ}
    (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    (traceForm f hf hnonconst α).toFun (δ (flatEndReparam t))
        (pathSpeed (δ ∘ flatEndReparam) t)
      = ∑ i, traceSummand f α (M.Γ i t) (pathSpeed (δ ∘ flatEndReparam) t) := by
  classical
  set δr : ℝ → Y := δ ∘ flatEndReparam with hδr_def
  set v : ℂ := pathSpeed δr t with hv_def
  have ht01 : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  show ((traceForm f hf hnonconst α).toFun (δr t)) v
    = ∑ i, traceSummand f α (M.Γ i t) v
  -- Off-branch: the trace form value is the fibre-sum `traceFun`.
  have hδr_avoid : δr t ∉ branchLocus f := havoid (flatEndReparam t)
  rw [traceForm_toFun_of_notMem_branchLocus f hf hnonconst α hδr_avoid]
  -- The fibre over `δr t` is finite.
  have hfin : (f ⁻¹' {δr t}).Finite := fiber_finite_off_branchLocus f hf hnonconst hδr_avoid
  -- Unfold the fibre sum; reindex the fibre Finset by the time-`t` bijection `i ↦ M.Γ i t`
  -- at the covector (CLM) level, then evaluate at `v`.
  rw [traceFun, finsum_mem_eq_finite_toFinset_sum _ hfin]
  simp only [traceSummandAt]
  have hreindex : ∑ x ∈ hfin.toFinset, traceSummand f α x
      = ∑ i, traceSummand f α (M.Γ i t) := by
    refine (Finset.sum_bij (fun (i : Fin M.n) (_ : i ∈ Finset.univ) => M.Γ i t)
      ?_ ?_ ?_ ?_).symm
    · -- maps into the fibre Finset
      intro i _
      rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]
      exact M.lifts i ht01
    · -- injective on `univ` (fibre injectivity at `t`)
      intro a₁ _ a₂ _ heq
      exact M.fibre_inj t ht01 heq
    · -- surjective onto the fibre Finset (fibre surjectivity at `t`)
      intro x hx
      rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hx
      obtain ⟨i, hi⟩ := M.fibre_surj t ht01 x hx
      exact ⟨i, Finset.mem_univ i, hi⟩
    · -- termwise equality
      intro i _; rfl
  rw [hreindex]
  exact ContinuousLinearMap.sum_apply Finset.univ (fun i => traceSummand f α (M.Γ i t)) v

/-- **Leaf D — projection formula (pointwise fibre-sum).** The line integral of the
trace form along `δ` equals the sum, over the lift family, of the lift periods:
`∫_δ traceFormTotal(ωⱼ) = ∑ᵢ periodVec(Γ i) j`. Reparametrize to `δr`, then integrate
the pointwise identity `traceFun f ωⱼ (δr t)(δr' t) = ∑ᵢ ωⱼ(Γ i t)(Γ i' t)` (the trace
fibre-sum reindexed by the time-`t` bijection `i ↦ Γ i t`, each summand the pullback
covector with `(mfderiv f)⁻¹ (δr' t) = pathSpeed (Γ i) t`). -/
theorem lineIntegral_traceFormTotal_eq_sum_periodVec (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) (havoid : ∀ t : ℝ, δ t ∉ branchLocus f)
    (M : MonodromyLiftFamily f δ) (j : Fin (kirovGenus X)) :
    lineIntegral (traceFormTotal f hf (periodBasisForm X j)) δ
      = ∑ i, periodVec (M.Γ i) j := by
  classical
  set ωj : HolomorphicOneForms X := periodBasisForm X j with hωj_def
  set δr : ℝ → Y := δ ∘ flatEndReparam with hδr_def
  -- Step 1: total trace = genuine trace (off-constant).
  rw [traceFormTotal_of_nonconstant f hf hnonconst]
  -- Step 2: reparametrize the LHS line integral by `flatEndReparam`.
  rw [← lineIntegral_comp_flatEndReparam (traceForm f hf hnonconst ωj) δ hδ.diff]
  -- Step 3: pull the RHS sum inside the integral.
  have hRHS : ∑ i, periodVec (M.Γ i) j
      = ∫ t in (0:ℝ)..1, ∑ i, ωj.toFun (M.Γ i t) (pathSpeed (M.Γ i) t) := by
    rw [intervalIntegral.integral_finsetSum (fun i _ => (M.smooth i).integrable j)]
    rfl
  rw [hRHS]
  -- Unfold the LHS to an interval integral over the reparametrized integrand.
  show (∫ t in (0:ℝ)..1, (traceForm f hf hnonconst ωj).toFun ((δ ∘ flatEndReparam) t)
        (pathSpeed (δ ∘ flatEndReparam) t))
    = ∫ t in (0:ℝ)..1, ∑ i, ωj.toFun (M.Γ i t) (pathSpeed (M.Γ i) t)
  -- Step 4: the integrands agree a.e. on `(0,1]` (pointwise on the interior `(0,1)`;
  -- the endpoint `{1}` is null).
  refine intervalIntegral.integral_congr_ae ?_
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (1 : ℝ))
  intro t ht
  simp only [Set.mem_setOf_eq, Classical.not_imp] at ht
  obtain ⟨ht_mem, ht_ne⟩ := ht
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht_mem
  by_contra ht1
  refine ht_ne ?_
  -- `t ∈ (0,1)`.
  have ht_Ioo : t ∈ Set.Ioo (0:ℝ) 1 :=
    ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 (by simpa using ht1)⟩
  -- Pointwise identity on the interior.
  show (traceForm f hf hnonconst ωj).toFun (δ (flatEndReparam t))
        (pathSpeed (δ ∘ flatEndReparam) t)
    = ∑ i, ωj.toFun (M.Γ i t) (pathSpeed (M.Γ i) t)
  rw [traceForm_apply_eq_sum_lift_interior f hf hnonconst δ hδ havoid M ωj ht_Ioo]
  exact Finset.sum_congr rfl fun i _ =>
    traceSummand_lift_velocity_interior f hf hnonconst δ hδ havoid M ωj i ht_Ioo

/-! ### Leaf E helpers: monodromy permutation, orbit chains, push-forward by `f` -/

/-- **Push a smooth path forward by a global `C^ω` map.** `f ∘ γ` is a smooth path
from `f P` to `f Q`: continuity by composition; chart-pullback differentiability via the
chart-local representation `f_loc = chartY ∘ f ∘ chartX.symm` (holomorphic ⟹ ℝ-diff by
`restrictScalars`, as in `differentiableAt_chart_lift_of_notMem_criticalSet`); `velCont` by
`velCont_comp`. The orbit loops push to multiples of `δ`, so `f ∘ (orbit loop)` must be a
smooth path for the period accounting. -/
theorem IsSmoothPath.comp (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    {P Q : X} {γ : ℝ → X} (hγ : IsSmoothPath P Q γ) :
    IsSmoothPath (f P) (f Q) (f ∘ γ) where
  start := by simp [Function.comp_apply, hγ.start]
  finish := by simp [Function.comp_apply, hγ.finish]
  cont := hf.continuous.comp hγ.cont
  diff := by
    intro t ht
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
    have hf_loc_hasFD_ℝ : HasFDerivAt f_loc
        ((fderiv ℂ f_loc (g_X t)).restrictScalars ℝ) (g_X t) := by
      have hf_loc_hasFD_ℂ : HasFDerivAt f_loc (fderiv ℂ f_loc (g_X t)) (g_X t) :=
        hf_loc_diff_ℂ.hasFDerivAt
      rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hf_loc_hasFD_ℂ ⊢
      simp only [ContinuousLinearMap.coe_restrictScalars']
      exact hf_loc_hasFD_ℂ
    have h_comp_diff : DifferentiableAt ℝ (f_loc ∘ g_X) t :=
      hf_loc_hasFD_ℝ.differentiableAt.comp t (hγ.diff t ht)
    exact (h_eq.differentiableAt_iff).mpr h_comp_diff
  velCont :=
    velCont_comp f hf γ hγ.cont
      (fun s hs => hγ.diff s (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hs))
      hγ.velCont

/-- **Each lift pushes to `δ`'s period.** Since `f ∘ Γ i = δ ∘ flatEndReparam` on `[0,1]`
and the period is `flatEndReparam`-invariant. -/
private theorem periodVec_comp_lift (f : X → Y) (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ)
    (M : MonodromyLiftFamily f δ) (i : Fin M.n) :
    periodVec (f ∘ M.Γ i) = periodVec δ := by
  rw [periodVec_congr_of_eqOn (M.lifts i)]
  exact periodVec_comp_flatEndReparam δ hδ

/-- **Orbit chain.** `concatPow σ k i` concatenates the lifts `Γ i, Γ (σ i), …, Γ (σ^k i)`
— a path from `Γ i 0` to `Γ (σ^k i) 1 = Γ (σ^{k+1} i) 0`. The orbit loop is `concatPow`
to the orbit length minus one (then start `= finish`). -/
private noncomputable def concatPow (f : X → Y) (δ : ℝ → Y) (M : MonodromyLiftFamily f δ)
    (σ : Equiv.Perm (Fin M.n)) : ℕ → Fin M.n → (ℝ → X)
  | 0, i => M.Γ i
  | (k+1), i => Jacobians.concat (M.Γ i) (concatPow f δ M σ k (σ i))

/-- `concatPow σ k i` is a smooth path `Γ i 0 → Γ (σ^k i) 1` with zero endpoint velocities
(so consecutive chains and the final closure glue with `IsSmoothPath.concat`). -/
private theorem concatPow_isSmoothPath (f : X → Y) (δ : ℝ → Y) (M : MonodromyLiftFamily f δ)
    (σ : Equiv.Perm (Fin M.n)) (hσ : ∀ i, M.Γ (σ i) 0 = M.Γ i 1) :
    ∀ (k : ℕ) (i : Fin M.n),
      IsSmoothPath (M.Γ i 0) (M.Γ ((σ^k) i) 1) (concatPow f δ M σ k i)
      ∧ pathSpeed (concatPow f δ M σ k i) 0 = 0
      ∧ pathSpeed (concatPow f δ M σ k i) 1 = 0 := by
  intro k
  induction k with
  | zero =>
    intro i
    refine ⟨?_, ?_, ?_⟩
    · simpa [concatPow, pow_zero] using M.smooth i
    · simpa [concatPow] using M.velZero_zero i
    · simpa [concatPow, pow_zero] using M.velZero_one i
  | succ k ih =>
    intro i
    obtain ⟨ih_sp, ih_v0, _ih_v1⟩ := ih (σ i)
    have h1 : IsSmoothPath (M.Γ i 0) (M.Γ i 1) (M.Γ i) := M.smooth i
    have hjoin : M.Γ i 1 = M.Γ (σ i) 0 := (hσ i).symm
    have ih_sp' : IsSmoothPath (M.Γ i 1) (M.Γ ((σ^k) (σ i)) 1) (concatPow f δ M σ k (σ i)) := by
      rw [hjoin]; exact ih_sp
    have hconcat : IsSmoothPath (M.Γ i 0) (M.Γ ((σ^k) (σ i)) 1)
        (Jacobians.concat (M.Γ i) (concatPow f δ M σ k (σ i))) :=
      h1.concat ih_sp' (M.velZero_one i) ih_v0
    have hpow : (σ^(k+1)) i = (σ^k) (σ i) := by rw [pow_succ]; rfl
    have hmem0 : (0:ℝ) ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨le_refl 0, zero_le_one⟩
    have hmem1 : (1:ℝ) ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨zero_le_one, le_refl 1⟩
    refine ⟨?_, ?_, ?_⟩
    · show IsSmoothPath (M.Γ i 0) (M.Γ ((σ^(k+1)) i) 1) _
      rw [hpow]; exact hconcat
    · show pathSpeed (Jacobians.concat (M.Γ i) (concatPow f δ M σ k (σ i))) 0 = 0
      rw [Jacobians.pathSpeed_concat_left _ _ 0 (by norm_num)
          (by rw [show (2:ℝ) * 0 = 0 from by norm_num]; exact (M.smooth i).diff 0 hmem0),
        show (2:ℝ) * 0 = 0 from by norm_num, M.velZero_zero i, mul_zero]
    · show pathSpeed (Jacobians.concat (M.Γ i) (concatPow f δ M σ k (σ i))) 1 = 0
      rw [Jacobians.pathSpeed_concat_right _ _ 1 (by norm_num)
          (by rw [show (2:ℝ) * 1 - 1 = 1 from by norm_num]; exact ih_sp'.diff 1 hmem1),
        show (2:ℝ) * 1 - 1 = 1 from by norm_num, _ih_v1, mul_zero]

/-- `periodVec` of the orbit chain is the sum of the lift periods over `Γ i, …, Γ (σ^k i)`. -/
private theorem concatPow_periodVec (f : X → Y) (δ : ℝ → Y) (M : MonodromyLiftFamily f δ)
    (σ : Equiv.Perm (Fin M.n)) (hσ : ∀ i, M.Γ (σ i) 0 = M.Γ i 1) :
    ∀ (k : ℕ) (i : Fin M.n),
      periodVec (concatPow f δ M σ k i) = ∑ j ∈ Finset.range (k+1), periodVec (M.Γ ((σ^j) i)) := by
  intro k
  induction k with
  | zero => intro i; simp [concatPow, pow_zero]
  | succ k ih =>
    intro i
    show periodVec (Jacobians.concat (M.Γ i) (concatPow f δ M σ k (σ i))) = _
    have hsp2 : IsSmoothPath (M.Γ i 1) (M.Γ ((σ^k) (σ i)) 1) (concatPow f δ M σ k (σ i)) := by
      have := (concatPow_isSmoothPath f δ M σ hσ k (σ i)).1; rw [hσ i] at this; exact this
    rw [periodVec_concat_of_smooth (M.smooth i) hsp2, ih (σ i),
        Finset.sum_range_succ' (fun j => periodVec (M.Γ ((σ ^ j) i))) (k+1)]
    exact add_comm _ _

/-- `f ∘ (orbit chain)` pushes to `(k+1) • periodVec δ` (it traverses `δ` `k+1` times). -/
private theorem comp_concatPow_periodVec (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) (M : MonodromyLiftFamily f δ)
    (σ : Equiv.Perm (Fin M.n)) (hσ : ∀ i, M.Γ (σ i) 0 = M.Γ i 1) :
    ∀ (k : ℕ) (i : Fin M.n),
      periodVec (f ∘ concatPow f δ M σ k i) = (k+1) • periodVec δ := by
  intro k
  induction k with
  | zero => intro i; show periodVec (f ∘ M.Γ i) = (0+1) • periodVec δ;
            rw [periodVec_comp_lift f δ hδ M i]; simp
  | succ k ih =>
    intro i
    have hpush : f ∘ concatPow f δ M σ (k+1) i
        = Jacobians.concat (f ∘ M.Γ i) (f ∘ concatPow f δ M σ k (σ i)) := by
      show f ∘ Jacobians.concat (M.Γ i) (concatPow f δ M σ k (σ i)) = _
      funext t; simp only [Function.comp_apply, Jacobians.concat]; split <;> rfl
    rw [hpush]
    have hsp1 : IsSmoothPath (f (M.Γ i 0)) (f (M.Γ i 1)) (f ∘ M.Γ i) := (M.smooth i).comp f hf
    have hsp2' : IsSmoothPath (f (M.Γ i 1)) (f (M.Γ ((σ^k) (σ i)) 1)) (f ∘ concatPow f δ M σ k (σ i)) := by
      have h2 : IsSmoothPath (M.Γ i 1) (M.Γ ((σ^k) (σ i)) 1) (concatPow f δ M σ k (σ i)) := by
        have := (concatPow_isSmoothPath f δ M σ hσ k (σ i)).1; rw [hσ i] at this; exact this
      have := h2.comp f hf; exact this
    rw [periodVec_concat_of_smooth hsp1 hsp2', periodVec_comp_lift f δ hδ M i, ih (σ i),
      show (k+1+1) • periodVec δ = periodVec δ + (k+1) • periodVec δ by
        rw [add_comm, add_smul, one_smul]]

/-- **The monodromy permutation.** `σ i` is the unique index with `Γ (σ i) 0 = Γ i 1`
(both endpoints lie in the fibre over `δ 0`): existence by `fibre_surj` at `t = 1`,
injectivity by `fibre_inj` at `t = 1`, bijective since `Fin M.n` is finite. -/
private theorem exists_monodromyPerm (f : X → Y) (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ)
    (M : MonodromyLiftFamily f δ) :
    ∃ σ : Equiv.Perm (Fin M.n), ∀ i, M.Γ (σ i) 0 = M.Γ i 1 := by
  classical
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl 0, by norm_num⟩
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by norm_num, le_refl 1⟩
  have key : ∀ i, ∃ j, M.Γ j 0 = M.Γ i 1 := by
    intro i
    have hfi1 : f (M.Γ i 1) = δ (flatEndReparam 1) := M.lifts i h1
    have heq : δ (flatEndReparam 1) = δ (flatEndReparam 0) := by
      rw [flatEndReparam_one, flatEndReparam_zero, hδ.closed]
    rw [heq] at hfi1
    exact M.fibre_surj 0 h0 (M.Γ i 1) hfi1
  choose g hg using key
  have hg_inj : Function.Injective g := by
    intro i j hij
    have : M.Γ i 1 = M.Γ j 1 := by rw [← hg i, ← hg j, hij]
    exact M.fibre_inj 1 h1 this
  have hg_bij : Function.Bijective g := (Finite.injective_iff_bijective).mp hg_inj
  exact ⟨Equiv.ofBijective g hg_bij, fun i => by simp only [Equiv.ofBijective_apply]; exact hg i⟩

/-- After `orderOf (σ.cycleOf e)` steps, `σ` returns `e` to itself (orbit closes). -/
private theorem perm_pow_orderOf_cycleOf_apply_self {N : ℕ} (σ : Equiv.Perm (Fin N)) (e : Fin N) :
    (σ ^ orderOf (σ.cycleOf e)) e = e := by
  classical
  have h1 : ((σ.cycleOf e) ^ orderOf (σ.cycleOf e)) e = (σ ^ orderOf (σ.cycleOf e)) e :=
    Equiv.Perm.cycleOf_pow_apply_self σ e (orderOf (σ.cycleOf e))
  rw [← h1, pow_orderOf_eq_one]; rfl

/-- `j ↦ σ^j e` is injective on `range (orderOf (σ.cycleOf e))` (the orbit has exactly
that many distinct elements). -/
private theorem perm_pow_apply_injOn {N : ℕ} (σ : Equiv.Perm (Fin N)) (e : Fin N) :
    Set.InjOn (fun j => (σ ^ j) e) (Finset.range (orderOf (σ.cycleOf e))) := by
  classical
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  simp only at hab
  rw [← Equiv.Perm.cycleOf_pow_apply_self σ e a, ← Equiv.Perm.cycleOf_pow_apply_self σ e b] at hab
  set c := σ.cycleOf e with hc
  rcases eq_or_ne c 1 with hc1 | hc1
  · rw [hc1] at ha hb; simp at ha hb; omega
  · have hσe : σ e ≠ e := by rwa [Ne, ← Equiv.Perm.cycleOf_eq_one_iff (f := σ)]
    have hcyc : c.IsCycle := σ.isCycle_cycleOf hσe
    have he_mem : e ∈ c.support := by
      rw [hc, Equiv.Perm.mem_support_cycleOf_iff]
      exact ⟨Equiv.Perm.SameCycle.rfl, Equiv.Perm.mem_support.mpr hσe⟩
    have hcOn : c.IsCycleOn (c.support : Set (Fin N)) := by
      have h := hcyc.isCycleOn
      have hset : ({x | c x ≠ x} : Set (Fin N)) = (c.support : Set (Fin N)) := by
        ext x; simp [Equiv.Perm.mem_support]
      rwa [hset] at h
    have hord : orderOf c = c.support.card := hcyc.orderOf
    rw [Equiv.Perm.IsCycleOn.pow_apply_eq_pow_apply hcOn he_mem] at hab
    rw [hord] at ha hb
    exact (Nat.ModEq.eq_of_lt_of_lt hab ha hb)

/-- **Orbit-coefficient partition (pure permutation combinatorics).** For a permutation
`σ` of `Fin N`, there are integer coefficients — the indicator of one representative
(orbit-minimum) per `σ`-orbit — such that for ANY orbit-summed family
`loopval i = ∑_{k < orderOf (cycleOf i)} F (σ^k i)`, the weighted sum
`∑ coeffs i • loopval i` collapses to `∑ i, F i`. This is the orbit-partition accounting
shared by both period identities of the orbit loops (`F = periodVec ∘ Γ` for the pullback
identity; `F` constant for the pushforward count). -/
private theorem exists_orbitCoeff {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    ∃ coeffs : Fin N → ℤ, ∀ {A : Type*} [AddCommGroup A] (F loopval : Fin N → A),
      (∀ i, loopval i = ∑ k ∈ Finset.range (orderOf (σ.cycleOf i)), F ((σ ^ k) i)) →
      ∑ i, coeffs i • loopval i = ∑ i, F i := by
  classical
  set orb : Fin N → Finset (Fin N) := fun i => Finset.univ.filter (σ.SameCycle i) with horb
  have horb_self : ∀ i, i ∈ orb i := fun i => by
    simp only [horb, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Equiv.Perm.SameCycle.refl σ i
  set rep : Fin N → Fin N := fun i => (orb i).min' ⟨i, horb_self i⟩ with hrep
  have hℓpos : ∀ i, 0 < orderOf (σ.cycleOf i) := fun i => orderOf_pos _
  -- the orbit is the image of `k ↦ σ^k i` over `[0, orderOf (cycleOf i))`
  have hKimg : ∀ i, (Finset.range (orderOf (σ.cycleOf i))).image (fun k => (σ ^ k) i) = orb i := by
    intro i
    apply Finset.Subset.antisymm
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨k, _, rfl⟩ := hx
      simp only [horb, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Equiv.Perm.SameCycle.refl σ i).pow_right
    · intro x hx
      simp only [horb, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨m, hm⟩ := hx.exists_nat_pow_eq
      simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨m % orderOf (σ.cycleOf i), Nat.mod_lt _ (hℓpos i),
        by rw [Equiv.Perm.pow_mod_orderOf_cycleOf_apply]; exact hm⟩
  have hinj : ∀ i, Set.InjOn (fun k => (σ ^ k) i) ↑(Finset.range (orderOf (σ.cycleOf i))) :=
    fun i => perm_pow_apply_injOn σ i
  have hrep_sc : ∀ i, σ.SameCycle i (rep i) := by
    intro i
    have hm : rep i ∈ orb i := (orb i).min'_mem _
    simpa only [horb, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  have horb_eq : ∀ i j, σ.SameCycle i j → orb i = orb j := by
    intro i j h
    simp only [horb]
    exact Finset.filter_congr (fun x _ => ⟨fun hix => h.symm.trans hix, fun hjx => h.trans hjx⟩)
  have hrep_eq_iff : ∀ i j, rep i = rep j ↔ σ.SameCycle i j := by
    intro i j
    refine ⟨fun h => ?_, fun h => by simp only [hrep, horb_eq i j h]⟩
    have h1 := hrep_sc i
    have h2 := hrep_sc j
    rw [← h] at h2
    exact h1.trans h2.symm
  have hrep_idem : ∀ i, rep (rep i) = rep i := fun i => (hrep_eq_iff (rep i) i).mpr (hrep_sc i).symm
  have hfiber : ∀ i, rep i = i → Finset.univ.filter (fun x => rep x = i) = orb i := by
    intro i hi
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, horb]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hx : rep x = rep i := by rw [h, hi]
      exact ((hrep_eq_iff x i).mp hx).symm
    · have hx : rep x = rep i := (hrep_eq_iff x i).mpr h.symm
      rw [hx, hi]
  refine ⟨fun i => if rep i = i then (1 : ℤ) else 0, ?_⟩
  intro A _ F loopval hloop
  have hper : ∀ i, (if rep i = i then (1 : ℤ) else 0) • loopval i
      = ∑ x ∈ Finset.univ.filter (fun x => rep x = i), F x := by
    intro i
    by_cases hi : rep i = i
    · simp only [hi, if_true, one_zsmul]
      rw [hloop i, hfiber i hi, ← hKimg i]
      exact (Finset.sum_image (fun a ha b hb hab =>
        hinj i (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab)).symm
    · simp only [hi, if_false, zero_zsmul]
      have hempty : Finset.univ.filter (fun x => rep x = i) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun x _ hx => hi (by rw [← hx]; exact hrep_idem x))
      rw [hempty, Finset.sum_empty]
  rw [Finset.sum_congr rfl (fun i _ => hper i)]
  exact Finset.sum_fiberwise Finset.univ rep F

/-- **Leaf E — orbit loops.** Group the lift family into closed smooth loops along
the orbits of the monodromy permutation `σ i := the index with Γ (σ i) 0 = Γ i 1`
(bijective by `fibre_inj`/`fibre_surj` at `t = 1`): each orbit gives the iterated
`concat` of its lifts (a closed loop — junction velocities `0` — smooth by
`velCont_concat`). With all `coeffs = 1` and `sheets = M.n`, period accounting gives
the two identities: `∑ orbit-periods = ∑ᵢ periodVec(Γ i)` (orbit partition +
`periodVec_concat_of_smooth`), and `∑ periodVec(f ∘ loop) = M.n • periodVec δ`
(each `f ∘ Γ i = δr` so each orbit pushes to `(orbit length) • periodVec δ`). -/
theorem exists_orbitLoops_of_monodromyLiftFamily (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ)
    (M : MonodromyLiftFamily f δ) :
    ∃ (m : ℕ) (loops : Fin m → ℝ → X) (coeffs : Fin m → ℤ),
      (∀ i, IsClosedSmoothLoop (loops i)) ∧
      (∑ i, coeffs i • periodVec (loops i) = ∑ i, periodVec (M.Γ i)) ∧
      (∑ i, coeffs i • periodVec (f ∘ loops i) = (M.n : ℤ) • periodVec δ) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_monodromyPerm f δ hδ M
  obtain ⟨coeffs, hcoeff⟩ := exists_orbitCoeff σ
  refine ⟨M.n, fun i => concatPow f δ M σ (orderOf (σ.cycleOf i) - 1) i, coeffs, ?_, ?_, ?_⟩
  · -- each orbit loop is a closed smooth loop (start = finish, since `σ^(orderOf) i = i`)
    intro i
    obtain ⟨hsp, _, _⟩ := concatPow_isSmoothPath f δ M σ hσ (orderOf (σ.cycleOf i) - 1) i
    have hσℓ : σ ((σ ^ (orderOf (σ.cycleOf i) - 1)) i) = i := by
      have h1 : σ ((σ ^ (orderOf (σ.cycleOf i) - 1)) i) = (σ ^ orderOf (σ.cycleOf i)) i := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel (orderOf_pos _)]
      rw [h1]; exact perm_pow_orderOf_cycleOf_apply_self σ i
    have hclose : M.Γ ((σ ^ (orderOf (σ.cycleOf i) - 1)) i) 1 = M.Γ i 0 := by
      rw [(hσ ((σ ^ (orderOf (σ.cycleOf i) - 1)) i)).symm, hσℓ]
    rw [hclose] at hsp
    exact hsp.toClosedSmoothLoop
  · -- pullback identity: orbit-period accounting with `F = periodVec ∘ Γ`
    have hloop2 : ∀ i, periodVec (concatPow f δ M σ (orderOf (σ.cycleOf i) - 1) i)
        = ∑ k ∈ Finset.range (orderOf (σ.cycleOf i)), periodVec (M.Γ ((σ ^ k) i)) := fun i => by
      rw [concatPow_periodVec f δ M σ hσ (orderOf (σ.cycleOf i) - 1) i,
        Nat.sub_add_cancel (orderOf_pos _)]
    exact hcoeff (fun x => periodVec (M.Γ x)) _ hloop2
  · -- pushforward identity: orbit-period accounting with `F` constant `= periodVec δ`
    have hloop3 : ∀ i, periodVec (f ∘ concatPow f δ M σ (orderOf (σ.cycleOf i) - 1) i)
        = ∑ _k ∈ Finset.range (orderOf (σ.cycleOf i)), periodVec δ := fun i => by
      rw [comp_concatPow_periodVec f hf δ hδ M σ hσ (orderOf (σ.cycleOf i) - 1) i,
        Finset.sum_const, Finset.card_range, Nat.sub_add_cancel (orderOf_pos _)]
    rw [hcoeff (fun _ => periodVec δ) _ hloop3, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, ← natCast_zsmul]

/-- **[open] — geometric heart of the preimage-cycle lift.** The monodromy/orbit
construction, stated **purely in elementary line-integral / period-vector terms**
(no ambient-coordinate `ambientPullbackJac`): off the branch locus, `δ` lifts to a
finite ℤ-family of closed smooth loops realizing
* the **projection identity** `∫_δ traceFormTotal(ωⱼ^X) = ∑ᵢ coeffsᵢ • periodVec(loopsᵢ)ⱼ`
  (the per-component pullback, before coordinatization), and
* the **pushforward identity** `∑ᵢ coeffsᵢ • periodVec(f∘loopsᵢ) = sheets • periodVec δ`.

The reduction `exists_preimageCycle_of_off_branchLocus` below turns this into a
`PreimageCycle` via the **proven** coordinate bridge
`ambientPullbackJac_periodVec_apply_eq_lineIntegral_traceFormTotal` — so this lemma
isolates exactly the remaining *geometry*.

What it still needs (all infrastructure is identified):
* the seam-flattened smooth lifts `exists_smoothLift_flatEnd_off_branchLocus` (DONE),
  one per fibre point (`fiber_finite_off_branchLocus` ⇒ `Fintype`), assembled into a
  monodromy permutation via lift uniqueness (`IsCoveringMap.eq_liftPath_iff`) and
  concatenated over its orbits (`IsSmoothPath.concat`, junction velocities zero);
* the partition/sheet-reassembly projection formula (`exists_nbhd_cover` +
  `exists_localSheetSystem_traceForm_eq_sum` + `lineIntegral_pullback_section`);
* the two analytic facts that were the last walls are now **both CLEARED**: the
  line-integral reparametrization-invariance `periodVec (δ∘flatEndReparam) =
  periodVec δ` is PROVEN (`periodVec_comp_flatEndReparam`, monotone change-of-variables
  for *integrable* integrands), and the lifts' integrability now follows from the
  **C¹ loop-predicate refactor** (`IsClosedSmoothLoop` carries `velCont`; a local-section
  lift `g∘δr` gets its `velCont` from `velCont_compOn`, whence `integrable`). So what
  remains here is *purely* the monodromy/orbit/projection geometry — no missing analysis. -/
theorem exists_preimageLoopFamily (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) (havoid : ∀ t : ℝ, δ t ∉ branchLocus f) :
    ∃ (m : ℕ) (loops : Fin m → ℝ → X) (coeffs : Fin m → ℤ) (sheets : ℕ),
      (∀ i, IsClosedSmoothLoop (loops i)) ∧
      (fun j => lineIntegral (traceFormTotal f hf (periodBasisForm X j)) δ) =
        ∑ i, coeffs i • periodVec (loops i) ∧
      ∑ i, coeffs i • periodVec (f ∘ loops i) = (sheets : ℤ) • periodVec δ := by
  -- Construct the global lift family along `δr = δ ∘ flatEndReparam` (leaf A+B).
  obtain ⟨M⟩ := exists_monodromyLiftFamily f hf hnonconst δ hδ havoid
  -- Group the lifts into closed smooth loops along the monodromy orbits (leaf E).
  obtain ⟨m, loops, coeffs, hclosed, hper, hpush⟩ :=
    exists_orbitLoops_of_monodromyLiftFamily f hf δ hδ M
  refine ⟨m, loops, coeffs, M.n, hclosed, ?_, hpush⟩
  -- Projection identity: the trace integral is the sum of lift periods (leaf D),
  -- which the orbit grouping rewrites as the loop periods.
  have hproj : (fun j => lineIntegral (traceFormTotal f hf (periodBasisForm X j)) δ)
      = ∑ i, periodVec (M.Γ i) := by
    funext j
    rw [lineIntegral_traceFormTotal_eq_sum_periodVec f hf hnonconst δ hδ havoid M j,
      Finset.sum_apply]
  rw [hproj]; exact hper.symm

/-- **A closed smooth loop off the branch locus lifts to a preimage cycle.** The
coordinate-layer reduction is now **proven**: it takes the elementary geometric
loop family `exists_preimageLoopFamily` and packages it as a `PreimageCycle`, the
only nontrivial step being the projection identity's conversion from the line-integral
form `∫_δ trace(ωⱼ)` to the ambient pullback `(ambientPullbackJac f hf (periodVec δ))ⱼ`
via the proven bridge `ambientPullbackJac_periodVec_apply_eq_lineIntegral_traceFormTotal`
(integrability supplied by `hδ.integrable`). The remaining content is entirely inside
`exists_preimageLoopFamily` (the monodromy/projection geometry). -/
theorem exists_preimageCycle_of_off_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) (havoid : ∀ t : ℝ, δ t ∉ branchLocus f) :
    Nonempty (PreimageCycle f hf δ) := by
  obtain ⟨m, loops, coeffs, sheets, hclosed, hproj, hpush⟩ :=
    exists_preimageLoopFamily f hf hnonconst δ hδ havoid
  refine ⟨⟨m, loops, hclosed, coeffs, sheets, ?_, hpush⟩⟩
  -- Convert the projection identity to the ambient pullback via the proven bridge.
  have hb : ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf (periodVec δ) =
      (fun j => lineIntegral (traceFormTotal f hf (periodBasisForm X j)) δ) := by
    funext j
    exact ambientPullbackJac_periodVec_apply_eq_lineIntegral_traceFormTotal f hf δ j hδ.integrable
  rw [hb, hproj]

/-- **[PROVEN]** A `PreimageCycle` depends on `δ` only through `periodVec δ`
(the only places `δ` enters the data are the pullback/pushforward identities,
whose `δ`-dependence is exactly through `periodVec δ`). Transporting along a
period-vector equality reuses the same loops/coeffs. -/
def PreimageCycle.congr_periodVec {f : X → Y} {hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f}
    {δ δ' : ℝ → Y} (h : periodVec δ = periodVec δ') (c : PreimageCycle f hf δ') :
    PreimageCycle f hf δ where
  n := c.n
  loops := c.loops
  loops_smooth := c.loops_smooth
  coeffs := c.coeffs
  sheets := c.sheets
  pullback_eq := by rw [h]; exact c.pullback_eq
  pushforward_eq := by rw [h]; exact c.pushforward_eq

/-- **[PROVEN]** `exists_preimageCycle_of_nonconstant`, assembled: homotope `δ`
off the branch locus, lift it to a preimage cycle, and transport back
along the period-vector equality (`congr_periodVec`). -/
theorem exists_preimageCycle_of_nonconstant (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) :
    Nonempty (PreimageCycle f hf δ) := by
  obtain ⟨δ', hδ', hpv, havoid⟩ := exists_loop_off_branchLocus f hf hnonconst δ hδ
  obtain ⟨c⟩ := exists_preimageCycle_of_off_branchLocus f hf hnonconst δ' hδ' havoid
  exact ⟨PreimageCycle.congr_periodVec hpv.symm c⟩

/-- A value off the branch locus is off the (defeq) general critical-value set
`criticalValuesGeneral`. (`branchLocus f = f '' criticalSet f =
f '' criticalSetGeneral f = criticalValuesGeneral f` by definition.) -/
theorem notMem_criticalValuesGeneral_of_notMem_branchLocus {f : X → Y} {y : Y}
    (h : y ∉ branchLocus f) :
    y ∉ Jacobians.Discharge.Manifold.criticalValuesGeneral f := by
  unfold branchLocus criticalSet at h
  unfold Jacobians.Discharge.Manifold.criticalValuesGeneral
  exact h

/-- **Strengthened off-branch cycle.** Beyond the `PreimageCycle`, returns a
*regular value* `y₀` (off the branch locus) whose fibre has cardinality equal
to the cycle's `sheets`. This exposes `sheets = #(regular fibre)`, the bridge
identifying `sheets` with the analytic degree `degreeFiber`. Built exactly like
`exists_preimageCycle_of_off_branchLocus`, but keeping the monodromy family `M`
in scope so its `n = #fibre` (`M.n_eq_fibre_ncard`) can be read off. -/
theorem exists_preimageCycle_sheets_eq_fibreCard_of_off_branchLocus
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) (havoid : ∀ t : ℝ, δ t ∉ branchLocus f) :
    ∃ (c : PreimageCycle f hf δ) (y₀ : Y),
      y₀ ∉ branchLocus f ∧ c.sheets = (f ⁻¹' {y₀}).ncard := by
  obtain ⟨M⟩ := exists_monodromyLiftFamily f hf hnonconst δ hδ havoid
  obtain ⟨m, loops, coeffs, hclosed, hper, hpush⟩ :=
    exists_orbitLoops_of_monodromyLiftFamily f hf δ hδ M
  have hb : ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf (periodVec δ) =
      (fun j => lineIntegral (traceFormTotal f hf (periodBasisForm X j)) δ) := by
    funext j
    exact ambientPullbackJac_periodVec_apply_eq_lineIntegral_traceFormTotal f hf δ j hδ.integrable
  have hproj : (fun j => lineIntegral (traceFormTotal f hf (periodBasisForm X j)) δ)
      = ∑ i, periodVec (M.Γ i) := by
    funext j
    rw [lineIntegral_traceFormTotal_eq_sum_periodVec f hf hnonconst δ hδ havoid M j,
      Finset.sum_apply]
  refine ⟨⟨m, loops, hclosed, coeffs, M.n, ?_, hpush⟩, δ (flatEndReparam 0),
    havoid _, M.n_eq_fibre_ncard⟩
  rw [hb, hproj]; exact hper.symm

/-- **Strengthened cycle for any non-constant `f`.** Combines
`exists_preimageCycle_sheets_eq_fibreCard_of_off_branchLocus` with the
off-branch homotopy; `congr_periodVec` carries `sheets` (and hence the
fibre-cardinality identity) across. -/
theorem exists_preimageCycle_sheets_eq_fibreCard_of_nonconstant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) :
    ∃ (c : PreimageCycle f hf δ) (y₀ : Y),
      y₀ ∉ branchLocus f ∧ c.sheets = (f ⁻¹' {y₀}).ncard := by
  obtain ⟨δ', hδ', hpv, havoid⟩ := exists_loop_off_branchLocus f hf hnonconst δ hδ
  obtain ⟨c, y₀, hy₀, hsheets⟩ :=
    exists_preimageCycle_sheets_eq_fibreCard_of_off_branchLocus f hf hnonconst δ' hδ' havoid
  exact ⟨PreimageCycle.congr_periodVec hpv.symm c, y₀, hy₀, hsheets⟩

/-- **Pullback identity — member case.** For a closed smooth loop `δ`
in `Y`, the genuine pullback `ambientPullbackJac (periodVec δ)` lies
in `truePeriodLattice X`. Case-splits on constancy of `f`:

* If `f` is constant, `ambientPullbackJac f hf = 0`
  (`ambientPullbackJac_eq_zero_of_const`), so the image is `0`.
* If `f` is non-constant, extract a preimage cycle witness via
  `exists_preimageCycle_of_nonconstant`, then apply the algebraic reduction
  `ambientPullbackJac_periodVec_mem_truePeriodLattice_of_preimageCycle`. -/
theorem ambientPullbackJac_periodVec_mem_truePeriodLattice
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) :
    ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf (periodVec δ) ∈
      truePeriodLattice X := by
  by_cases hconst : ∃ y₀ : Y, ∀ x, f x = y₀
  · -- Constant case: ambientPullbackJac = 0.
    rw [ambientPullbackJac_eq_zero_of_const f hf hconst]
    simp
  · -- Non-constant case: extract a preimage cycle and apply the algebraic
    -- reduction.
    obtain ⟨c⟩ := exists_preimageCycle_of_nonconstant f hf hconst δ hδ
    exact ambientPullbackJac_periodVec_mem_truePeriodLattice_of_preimageCycle f hf δ c

/-- `ambientPullbackJac` (the genuine Jacobian pullback `Tᵀ`) preserves the period
lattice. Reduces to `ambientPullbackJac_periodVec_mem_truePeriodLattice` on
closed-loop generators, extended to the ℤ-span by `Submodule.span_induction` and
ℤ-linearity. Discharges `Jacobian.ambientPullbackJac_preserves_lattice`. -/
theorem ambientPullbackJac_preserves_truePeriodLattice
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (truePeriodLattice Y).toAddSubgroup ≤
      (truePeriodLattice X).toAddSubgroup.comap
        (ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf).toAddMonoidHom := by
  show ∀ v ∈ truePeriodLattice Y,
    ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf v ∈ truePeriodLattice X
  intro v hv
  refine Submodule.span_induction
    (p := fun v _ => ambientPullbackJac (gX := kirovGenus X) (gY := kirovGenus Y) f hf v ∈
      truePeriodLattice X) ?_ ?_ ?_ ?_ hv
  · -- Generator case: v = periodVec δ for a closed smooth loop δ in Y.
    rintro _ ⟨δ, hδ, rfl⟩
    exact ambientPullbackJac_periodVec_mem_truePeriodLattice f hf δ hδ
  · -- Zero case.
    simp
  · -- Additive case.
    intro x y _ _ hx hy
    simp only [map_add]
    exact Submodule.add_mem _ hx hy
  · -- ℤ-scalar case.
    intro r x _ hx
    simp only [map_zsmul]
    exact Submodule.smul_mem _ r hx

end Jacobians
