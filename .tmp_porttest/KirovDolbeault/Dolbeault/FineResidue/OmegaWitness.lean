/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FineResidue.Integral
import KirovDolbeault.Dolbeault.FormCoeff
import KirovDolbeault.SmoothPathCore

/-!
# R4 — the `ω₀`-coefficient witness for `IsOneZeroCoeff`

The `dz`-slot input of the R3 glue law (`Glue.lean`) is a holomorphic `(1,0)` chart-coefficient
family `IsOneZeroCoeff 𝔇 g` — in the residue application, the chart coefficients of the S1
canonical holomorphic 1-form `ω₀` with `K = div ω₀`.  Until now its only known inhabitant was
`0`.  This file supplies the real witness:

* `omegaCoeff 𝔇 α j := coeffAt α (𝔇.center j)` — the canonical-chart coefficient of a global
  holomorphic 1-form `α : HolomorphicOneForms X` in the chart of the `j`-th cover disk (the
  proven `Montel.localRep`/`FormCoeff.coeffAt` layer);
* `localRep_transitionMap` — the transformation law of the local representatives across two
  cover charts: `localRep α c_j = φ′_{jk} · localRep α c_k` at every point of `U j ⊓ U k`,
  derived from the proven frame identity `trivAt_symmL_one_eq_fderiv_C` (the chart-`c`
  tangent frame *is* the `fderiv` of the chart transition) plus the planar chain rule for
  `fderiv` through the transition `φ_{jk}`;
* `isOneZeroCoeff_omegaCoeff` — **the R4 witness**: `omegaCoeff 𝔇 α` satisfies the germ-eventual
  `φ′` overlap law `OneZeroLawAt` at every overlap point, for every cover and every `α`;
* `exists_omegaCoeff_ne_zero` — at genus ≥ 1 the witness is non-trivial: there is an `α` whose
  coefficient family does not vanish identically (`Montel` nontriviality of
  `HolomorphicOneForms` + `exists_localRep_self_ne_zero` + the nonvanishing chart-transition
  factor).

## Where the cover-refinement constraint does and does not bite

The witness here is **unconditional**: it holds for *every* chart-disk cover `𝔇`, with no
refinement hypothesis — `ω₀` is globally holomorphic, so its chart coefficients satisfy the
`(1,0)` law on every overlap of every cover.  The K-point cover-refinement constraint recorded
in `Glue.lean` and `docs/planning/R_LANE_PROGRESS.log` bites **only on the scalar overlap data
`w`** (the `Z¹(𝒪_K)`-cocycle representatives fed to `HolomorphicOnOverlaps`): at `K = div ω₀ ≠ 0`
(genus ≥ 2) those scalars have poles at the `K`-points, so the cover must be refined until each
of the finitely many `K`-points lies in a single cover set.  That constraint surfaces when R6
evaluates the functional on genuine `Z¹(𝒪_K)` data, not here.

## Genus 0

At `kirovGenus X = 0` there is **no nonzero** global holomorphic 1-form, so only the `0` family
inhabits `IsOneZeroCoeff` and the Forster fine-sheaf construction does not produce a residue
functional — this is genuine, not a gap (Gemini DT flag on PR #156).  The g = 0 routing decision
is recorded in `docs/planning/R4_G0_NOTE.md`: genus 0 goes through the snapshot's
`SerreResidueDirectGenus0*` route (S9 of the S3 scoping), and lane R is conditioned on
`0 < kirovGenus X`.  Do **not** fake a g = 0 witness or generalize `ω₀` to meromorphic forms.

Sign/normalization: the functional integrating against these coefficients is normalized by the
R0 constant `resNormalization = −π⁻¹` (`SignTest.lean`; cite, do not re-derive).
-/

open Complex Filter
open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable (𝔇 : ChartDiskCover X)

/-! ### The transformation law of local representatives across cover charts -/

/-- **Local representatives transform by the transition derivative**: at a point `y` of the
overlap `U j ⊓ U k`,

  `localRep α c_j y = φ′_{jk}(chart_j y) · localRep α c_k y`.

Proof: by the proven frame identity (`trivAt_symmL_one_eq_fderiv_C`) the chart-`c` unit tangent
at `y` is `fderiv ℂ (chart_y ∘ chart_c⁻¹)` applied to `1`; near `chart_j y` the transition
`chart_y ∘ chart_j⁻¹` factors as `(chart_y ∘ chart_k⁻¹) ∘ φ_{jk}`, so the `fderiv` chain rule
turns the chart-`j` frame into `φ′_{jk} •` the chart-`k` frame, and the ℂ-linearity of `α` at
`y` carries the factor out. -/
theorem localRep_transitionMap (α : HolomorphicOneForms X) {j k : 𝔇.toFiniteCover.ι} {y : X}
    (hyj : y ∈ (𝔇.U j : Set X)) (hyk : y ∈ (𝔇.U k : Set X)) :
    Jacobians.Montel.localRep α (𝔇.center j) y
      = deriv (transitionMap 𝔇 j k) (chartMap 𝔇 j y)
          * Jacobians.Montel.localRep α (𝔇.center k) y := by
  have hsrcj : y ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hyj
  have hsrck : y ∈ (chartAt ℂ (𝔇.center k)).source := mem_chartSource_of_mem_U 𝔇 hyk
  -- the two frame tangents, as chart-transition `fderiv`s (proven frame identity)
  have h1 : (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) (𝔇.center j)).symmL ℂ y 1
      = fderiv ℂ ((chartAt ℂ y) ∘ (chartAt ℂ (𝔇.center j)).symm) (chartMap 𝔇 j y) 1 :=
    Jacobians.OfCurveSkeleton.trivAt_symmL_one_eq_fderiv_C (𝔇.center j) y hsrcj
  have h2 : (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) (𝔇.center k)).symmL ℂ y 1
      = fderiv ℂ ((chartAt ℂ y) ∘ (chartAt ℂ (𝔇.center k)).symm) (chartMap 𝔇 k y) 1 :=
    Jacobians.OfCurveSkeleton.trivAt_symmL_one_eq_fderiv_C (𝔇.center k) y hsrck
  -- analytic inputs for the chain rule
  have hφd : DifferentiableAt ℂ (transitionMap 𝔇 j k) (chartMap 𝔇 j y) :=
    (transitionMap_analyticAt 𝔇 hyj hyk).differentiableAt
  have hfd : DifferentiableAt ℂ
      ((chartAt ℂ y) ∘ (chartAt ℂ (𝔇.center k)).symm) (chartMap 𝔇 k y) :=
    (transition_analyticAt_of_mem hsrck (mem_chart_source ℂ y)).differentiableAt
  -- the chart-`j` transition factors through `φ_{jk}` near `chart_j y`
  have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j y) = y :=
    (chartAt ℂ (𝔇.center j)).left_inv hsrcj
  have heq : ((chartAt ℂ y) ∘ (chartAt ℂ (𝔇.center j)).symm)
      =ᶠ[𝓝 (chartMap 𝔇 j y)]
        (((chartAt ℂ y) ∘ (chartAt ℂ (𝔇.center k)).symm) ∘ transitionMap 𝔇 j k) := by
    have hcont : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j y) :=
      (chartAt ℂ (𝔇.center j)).symm.continuousAt
        (by rw [(chartAt ℂ (𝔇.center j)).symm_source]
            exact (chartAt ℂ (𝔇.center j)).map_source hsrcj)
    have hsrc_nhds : (chartAt ℂ (𝔇.center k)).source
        ∈ 𝓝 ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j y)) := by
      rw [hli]
      exact (chartAt ℂ (𝔇.center k)).open_source.mem_nhds hsrck
    filter_upwards [hcont.preimage_mem_nhds hsrc_nhds] with w hw
    show (chartAt ℂ y) ((chartAt ℂ (𝔇.center j)).symm w)
        = (chartAt ℂ y) ((chartAt ℂ (𝔇.center k)).symm
            ((chartAt ℂ (𝔇.center k)) ((chartAt ℂ (𝔇.center j)).symm w)))
    rw [(chartAt ℂ (𝔇.center k)).left_inv hw]
  -- chain rule for the `fderiv`s
  have hfd' : DifferentiableAt ℂ ((chartAt ℂ y) ∘ (chartAt ℂ (𝔇.center k)).symm)
      (transitionMap 𝔇 j k (chartMap 𝔇 j y)) := by
    rw [transitionMap_chartMap 𝔇 hyj]
    exact hfd
  have hder : fderiv ℂ ((chartAt ℂ y) ∘ (chartAt ℂ (𝔇.center j)).symm) (chartMap 𝔇 j y)
      = (fderiv ℂ ((chartAt ℂ y) ∘ (chartAt ℂ (𝔇.center k)).symm) (chartMap 𝔇 k y)).comp
          (fderiv ℂ (transitionMap 𝔇 j k) (chartMap 𝔇 j y)) := by
    rw [heq.fderiv_eq, fderiv_comp (chartMap 𝔇 j y) hfd' hφd, transitionMap_chartMap 𝔇 hyj]
  -- evaluate the chain rule at the unit tangent
  have hval : fderiv ℂ ((chartAt ℂ y) ∘ (chartAt ℂ (𝔇.center j)).symm) (chartMap 𝔇 j y) 1
      = deriv (transitionMap 𝔇 j k) (chartMap 𝔇 j y)
          • fderiv ℂ ((chartAt ℂ y) ∘ (chartAt ℂ (𝔇.center k)).symm) (chartMap 𝔇 k y) 1 := by
    rw [hder]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [fderiv_apply_one_eq_deriv]
    have hsm : deriv (transitionMap 𝔇 j k) (chartMap 𝔇 j y)
        = deriv (transitionMap 𝔇 j k) (chartMap 𝔇 j y) • (1 : ℂ) := by
      rw [smul_eq_mul, mul_one]
    conv_lhs => rw [hsm]
    exact map_smul _ _ _
  -- transport through the ℂ-linear evaluation of `α` at `y`
  unfold Jacobians.Montel.localRep
  rw [h1, h2, hval]
  have happ : (α.toFun y)
      ((deriv (transitionMap 𝔇 j k) (chartMap 𝔇 j y)
        • fderiv ℂ ((chartAt ℂ y) ∘ (chartAt ℂ (𝔇.center k)).symm) (chartMap 𝔇 k y) 1 : ℂ))
      = deriv (transitionMap 𝔇 j k) (chartMap 𝔇 j y)
          • (α.toFun y) (fderiv ℂ ((chartAt ℂ y) ∘ (chartAt ℂ (𝔇.center k)).symm)
              (chartMap 𝔇 k y) 1) :=
    map_smul (α.toFun y) _ _
  rw [happ, smul_eq_mul]

/-! ### The `ω₀`-coefficient family -/

/-- The **chart-coefficient family of a global holomorphic 1-form** on a chart-disk cover: in
the `j`-th cover chart, the canonical-chart coefficient `coeffAt α (𝔇.center j)` (the proven
`Montel.localRep` layer of `FormCoeff.lean`).  In the residue application, `α = ω₀` is the S1
canonical form with `K = div ω₀`, and this family is the `dz`-slot of the R3 `glueCoeff`. -/
noncomputable def omegaCoeff (α : HolomorphicOneForms X) : 𝔇.toFiniteCover.ι → ℂ → ℂ :=
  fun j => coeffAt α (𝔇.center j)

omit [Nonempty X] in
@[simp] theorem omegaCoeff_apply (α : HolomorphicOneForms X) (j : 𝔇.toFiniteCover.ι) (z : ℂ) :
    omegaCoeff 𝔇 α j z = coeffAt α (𝔇.center j) z := rfl

/-- **R4 witness: the chart coefficients of a global holomorphic 1-form form a holomorphic
`(1,0)` chart-coefficient family** — `IsOneZeroCoeff 𝔇 (omegaCoeff 𝔇 α)` for every chart-disk
cover `𝔇` and every `α : HolomorphicOneForms X` (no cover-refinement hypothesis; see the module
docstring).  Analyticity is `coeffAt_analyticAt`; the germ-eventual `φ′` overlap law
`OneZeroLawAt` is `localRep_transitionMap` read back through the charts. -/
theorem isOneZeroCoeff_omegaCoeff (α : HolomorphicOneForms X) :
    IsOneZeroCoeff 𝔇 (omegaCoeff 𝔇 α) := by
  refine ⟨fun j x hx => coeffAt_analyticAt α (𝔇.center j)
    ((chartAt ℂ (𝔇.center j)).map_source (mem_chartSource_of_mem_U 𝔇 hx)),
    fun j k x hx => ?_⟩
  unfold OneZeroLawAt
  have hxsrc : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hx.1
  have hzt : chartMap 𝔇 j x ∈ (chartAt ℂ (𝔇.center j)).target :=
    (chartAt ℂ (𝔇.center j)).map_source hxsrc
  have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
    (chartAt ℂ (𝔇.center j)).left_inv hxsrc
  have hcont : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) :=
    (chartAt ℂ (𝔇.center j)).symm.continuousAt
      (by rw [(chartAt ℂ (𝔇.center j)).symm_source]; exact hzt)
  have hov : ((𝔇.U j ⊓ 𝔇.U k : Opens X) : Set X)
      ∈ 𝓝 ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x)) := by
    rw [hli]
    exact (𝔇.U j ⊓ 𝔇.U k : Opens X).isOpen.mem_nhds hx
  filter_upwards [hcont.preimage_mem_nhds hov,
    (chartAt ℂ (𝔇.center j)).open_target.mem_nhds hzt] with w hw hwt
  have hyj : (chartAt ℂ (𝔇.center j)).symm w ∈ (𝔇.U j : Set X) := hw.1
  have hyk : (chartAt ℂ (𝔇.center j)).symm w ∈ (𝔇.U k : Set X) := hw.2
  have hwy : chartMap 𝔇 j ((chartAt ℂ (𝔇.center j)).symm w) = w :=
    (chartAt ℂ (𝔇.center j)).right_inv hwt
  have hφw : transitionMap 𝔇 j k w
      = chartMap 𝔇 k ((chartAt ℂ (𝔇.center j)).symm w) := by
    conv_lhs => rw [← hwy]
    exact transitionMap_chartMap 𝔇 hyj
  -- reduce both chart coefficients to `localRep` at the surface point `(chart j).symm w`
  show coeffAt α (𝔇.center j) w
      = coeffAt α (𝔇.center k) (transitionMap 𝔇 j k w) * deriv (transitionMap 𝔇 j k) w
  have hL : coeffAt α (𝔇.center j) w
      = Jacobians.Montel.localRep α (𝔇.center j) ((chartAt ℂ (𝔇.center j)).symm w) := rfl
  have hli2 : (chartAt ℂ (𝔇.center k)).symm
        (chartMap 𝔇 k ((chartAt ℂ (𝔇.center j)).symm w))
      = (chartAt ℂ (𝔇.center j)).symm w :=
    (chartAt ℂ (𝔇.center k)).left_inv (mem_chartSource_of_mem_U 𝔇 hyk)
  have hR : coeffAt α (𝔇.center k) (transitionMap 𝔇 j k w)
      = Jacobians.Montel.localRep α (𝔇.center k) ((chartAt ℂ (𝔇.center j)).symm w) := by
    rw [hφw]
    show Jacobians.Montel.localRep α (𝔇.center k)
        ((chartAt ℂ (𝔇.center k)).symm (chartMap 𝔇 k ((chartAt ℂ (𝔇.center j)).symm w))) = _
    rw [hli2]
  have h := localRep_transitionMap 𝔇 α hyj hyk
  rw [hwy] at h
  rw [hL, hR, h, mul_comm]

/-! ### Non-triviality at genus ≥ 1 -/

/-- **The witness is non-trivial at genus ≥ 1**: for `0 < kirovGenus X` there is a global
holomorphic 1-form whose chart-coefficient family does not vanish — at a point where the
Montel local representative in the point's own canonical chart is nonzero
(`exists_localRep_self_ne_zero`), the cover-chart coefficient is also nonzero because the two
representatives differ by the nonvanishing chart-transition factor
(`Montel.localRep_chart_transition` + `chartTransitionFactor_ne_zero`).

At `kirovGenus X = 0` no such `α` exists (only `0` inhabits `IsOneZeroCoeff` nontrivially) —
see the module docstring and `docs/planning/R4_G0_NOTE.md` for the genus-0 routing. -/
theorem exists_omegaCoeff_ne_zero (hg : 0 < kirovGenus X) :
    ∃ α : HolomorphicOneForms X, ∃ j : 𝔇.toFiniteCover.ι, ∃ z : ℂ,
      omegaCoeff 𝔇 α j z ≠ 0 := by
  have hfr : 0 < Module.finrank ℂ (HolomorphicOneForms X) := hg
  have hnt : Nontrivial (HolomorphicOneForms X) := Module.nontrivial_of_finrank_pos hfr
  obtain ⟨α, hα⟩ := exists_ne (0 : HolomorphicOneForms X)
  obtain ⟨a, ha⟩ := exists_localRep_self_ne_zero α hα
  have hmem : a ∈ ⨆ i, 𝔇.toFiniteCover.U i := by
    rw [𝔇.toFiniteCover.covers]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hmem
  refine ⟨α, j, chartMap 𝔇 j a, ?_⟩
  have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j a) = a :=
    (chartAt ℂ (𝔇.center j)).left_inv (mem_chartSource_of_mem_U 𝔇 hj)
  have hval : omegaCoeff 𝔇 α j (chartMap 𝔇 j a)
      = Jacobians.Montel.localRep α (𝔇.center j) a := by
    show Jacobians.Montel.localRep α (𝔇.center j)
        ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j a)) = _
    rw [hli]
  rw [hval]
  intro hzero
  have hbase_a : a ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) a).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source ℂ a
  have hbase_j : a ∈ (trivializationAt ℂ
      (TangentSpace 𝓘(ℂ, ℂ) (M := X)) (𝔇.center j)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chartSource_of_mem_U 𝔇 hj
  have htr := Jacobians.Montel.localRep_chart_transition α (𝔇.center j) a a hbase_a hbase_j
  rw [hzero, mul_zero] at htr
  exact ha htr

end Jacobians.Dolbeault.FineResidue
