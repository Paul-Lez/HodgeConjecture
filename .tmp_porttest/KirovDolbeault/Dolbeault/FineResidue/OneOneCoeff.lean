/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.ChartDiskCover
import KirovDolbeault.Dolbeault.CechModelManifold

/-!
# R1 — the chart-coefficient `(1,1)`-representation layer

The fine-sheaf residue functional (S3 scoping §2.2, lane R) never builds an `A²` bundle of
`(1,1)`-forms on `X`: on a curve, a `(1,1)`-form is per chart one smooth planar coefficient
function, with the overlap law given by the **area Jacobian** `|φ′|²` of the holomorphic chart
transition `φ` — exactly the factor produced by Lebesgue change of variables, which is how the
chart-local area integrals of R4 are patched.  This file defines that representation:

* `chartMap 𝔇 j` / `transitionMap 𝔇 j k` — the chart coordinate of cover index `j` and the
  planar transition `φ_{jk} = (chart k) ∘ (chart j)⁻¹`, with the analytic facts
  (`transitionMap_analyticAt`, `transitionMap_deriv_ne_zero`, from the proven
  `transition_analyticAt_of_mem` / `transition_deriv_ne_zero` atoms);
* `OneOneLawAt` — the overlap law `t_j = (t_k ∘ φ_{jk})·|φ′_{jk}|²`, stated **up to germ**
  (`∀ᶠ` in `𝓝 (chartMap 𝔇 j x)` at each overlap point `x`): R1's coefficient extraction picks
  germ representatives by `Classical.choice`, so all downstream identities (risk register item 2
  of the scoping) must be germ-eventual, never raw function equalities;
* `IsOneOneCoeff` / `oneOneCoeff : Submodule ℂ (ι → ℂ → ℂ)` — coefficient families smooth at the
  chart image of their own cover set and pairwise compatible; a `Submodule`, so the ℂ-module
  structure that R4's integral functional is linear over is free;
* `isOneOneCoeff_congr` — germ-robustness: membership only depends on the germs of the
  coefficients at the chart images, so germ-representative choice noise cannot leak in.

R3 will *produce* members of `oneOneCoeff` (from `∂̄` of `(1,0)` split coefficients, via the
Wirtinger chain rule), and R4 will *consume* them (the PoU-localized area integral and the
chart-relocation lemma, whose Jacobian is literally the `|φ′|²` of `OneOneLawAt`).

The sign/normalization convention for integrating these coefficients is **already pinned** by R0
(`KirovDolbeault.Dolbeault.FineResidue.SignTest`): Lebesgue area on `ℂ`, normalizer
`resNormalization = −π⁻¹`.
-/

open Complex Filter
open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable (𝔇 : ChartDiskCover X)

/-! ### Chart coordinates and planar transitions of a chart-disk cover -/

/-- The planar chart coordinate of cover index `j`: `x ↦ (chartAt ℂ (center j)) x`.  Agrees with
the `extChartAt 𝓘(ℝ, ℂ)` coordinate that `ChartDiskCover` is stated with
(`chartMap_eq_extChartAt`). -/
noncomputable def chartMap (j : 𝔇.toFiniteCover.ι) : X → ℂ :=
  fun x => chartAt ℂ (𝔇.center j) x

/-- `chartMap` is the `extChartAt 𝓘(ℝ, ℂ)` coordinate (the model embedding is the identity). -/
theorem chartMap_eq_extChartAt (j : 𝔇.toFiniteCover.ι) (x : X) :
    chartMap 𝔇 j x = extChartAt 𝓘(ℝ, ℂ) (𝔇.center j) x := rfl

/-- A point of `U j` lies in the source of the `j`-th chart. -/
theorem mem_chartSource_of_mem_U {j : 𝔇.toFiniteCover.ι} {x : X} (hx : x ∈ (𝔇.U j : Set X)) :
    x ∈ (chartAt ℂ (𝔇.center j)).source := by
  have h := 𝔇.subset_chart_source j hx
  rwa [extChartAt_source] at h

/-- The planar transition `φ_{jk} = (chart k) ∘ (chart j)⁻¹` from chart-`j` to chart-`k`
coordinates. -/
noncomputable def transitionMap (j k : 𝔇.toFiniteCover.ι) : ℂ → ℂ :=
  (chartAt ℂ (𝔇.center k)) ∘ (chartAt ℂ (𝔇.center j)).symm

/-- On the chart image of the overlap, the transition relocates chart-`j` to chart-`k`
coordinates: `φ_{jk} (chartMap j x) = chartMap k x`. -/
theorem transitionMap_chartMap {j k : 𝔇.toFiniteCover.ι} {x : X}
    (hj : x ∈ (𝔇.U j : Set X)) :
    transitionMap 𝔇 j k (chartMap 𝔇 j x) = chartMap 𝔇 k x := by
  simp only [transitionMap, chartMap, Function.comp_apply,
    (chartAt ℂ (𝔇.center j)).left_inv (mem_chartSource_of_mem_U 𝔇 hj)]

/-- The transition `φ_{jk}` is **holomorphic** at the chart-`j` coordinate of every overlap
point (the proven `transition_analyticAt_of_mem` atom, specialized to the cover charts). -/
theorem transitionMap_analyticAt {j k : 𝔇.toFiniteCover.ι} {x : X}
    (hj : x ∈ (𝔇.U j : Set X)) (hk : x ∈ (𝔇.U k : Set X)) :
    AnalyticAt ℂ (transitionMap 𝔇 j k) (chartMap 𝔇 j x) :=
  transition_analyticAt_of_mem (mem_chartSource_of_mem_U 𝔇 hj) (mem_chartSource_of_mem_U 𝔇 hk)

/-- The transition derivative `φ′_{jk}` is **nonvanishing** at the chart-`j` coordinate of every
overlap point — so the `|φ′_{jk}|²` factor of the `(1,1)` law is strictly positive there. -/
theorem transitionMap_deriv_ne_zero {j k : 𝔇.toFiniteCover.ι} {x : X}
    (hj : x ∈ (𝔇.U j : Set X)) (hk : x ∈ (𝔇.U k : Set X)) :
    deriv (transitionMap 𝔇 j k) (chartMap 𝔇 j x) ≠ 0 :=
  transition_deriv_ne_zero (mem_chartSource_of_mem_U 𝔇 hj) (mem_chartSource_of_mem_U 𝔇 hk)

/-! ### The `(1,1)` overlap law and the coefficient submodule -/

/-- The **`(1,1)` chart-coefficient overlap law at an overlap point `x`, up to germ**:

  `t_j(z) = t_k(φ_{jk} z) · |φ′_{jk}(z)|²`  for `z` near `chartMap 𝔇 j x`,

with `|·|²` the area Jacobian `Complex.normSq` of the holomorphic transition — exactly the factor
of the planar Lebesgue change of variables (R4) and of reading a `(1,1)`-form coefficient across
charts.  Stated `∀ᶠ` (germ-eventual), per the scoping's germ-noise rule: coefficient families are
built from `Classical.choice` germ representatives, so only their germs are meaningful. -/
def OneOneLawAt (t : 𝔇.toFiniteCover.ι → ℂ → ℂ) (j k : 𝔇.toFiniteCover.ι) (x : X) : Prop :=
  ∀ᶠ z in 𝓝 (chartMap 𝔇 j x),
    t j z = t k (transitionMap 𝔇 j k z) * (normSq (deriv (transitionMap 𝔇 j k) z) : ℂ)

/-- A **`(1,1)` chart-coefficient family** for the chart-disk cover `𝔇`: one planar function per
cover index, smooth (`C^∞` over `ℝ`) at the chart image of its own cover set, satisfying the
germ-eventual `|φ′|²` overlap law at every overlap point.  This is the curve-level stand-in for
"smooth `(1,1)`-form on `X` presented in the cover charts" (S3 scoping §2.2). -/
def IsOneOneCoeff (t : 𝔇.toFiniteCover.ι → ℂ → ℂ) : Prop :=
  (∀ j, ∀ x ∈ (𝔇.U j : Set X), ContDiffAt ℝ (⊤ : ℕ∞) (t j) (chartMap 𝔇 j x)) ∧
    ∀ j k, ∀ x ∈ (𝔇.U j ⊓ 𝔇.U k : Opens X), OneOneLawAt 𝔇 t j k x

/-- The `(1,1)` chart-coefficient families form a **ℂ-submodule** of `ι → ℂ → ℂ`: both the
smoothness and the (coefficient-linear) overlap law are stable under `0`, `+`, and `c •`.  This
gives R4's integral functional its ℂ-linear domain for free. -/
def oneOneCoeff : Submodule ℂ (𝔇.toFiniteCover.ι → ℂ → ℂ) where
  carrier := {t | IsOneOneCoeff 𝔇 t}
  zero_mem' := by
    refine ⟨fun j x _ => contDiffAt_const, fun j k x _ => Eventually.of_forall fun z => ?_⟩
    simp
  add_mem' := by
    rintro s t ⟨hs1, hs2⟩ ⟨ht1, ht2⟩
    refine ⟨fun j x hx => (hs1 j x hx).add (ht1 j x hx), fun j k x hx => ?_⟩
    filter_upwards [hs2 j k x hx, ht2 j k x hx] with z h1 h2
    simp only [Pi.add_apply, h1, h2]
    ring
  smul_mem' := by
    rintro c t ⟨ht1, ht2⟩
    refine ⟨fun j x hx => (ht1 j x hx).const_smul c, fun j k x hx => ?_⟩
    filter_upwards [ht2 j k x hx] with z h1
    simp only [Pi.smul_apply, smul_eq_mul, h1]
    ring

@[simp] theorem mem_oneOneCoeff {t : 𝔇.toFiniteCover.ι → ℂ → ℂ} :
    t ∈ oneOneCoeff 𝔇 ↔ IsOneOneCoeff 𝔇 t := Iff.rfl

/-! ### Germ-robustness -/

/-- **Germ-robustness of the `(1,1)` layer** (risk register item 2 of the scoping): membership in
`oneOneCoeff` depends only on the germs of the coefficients at the chart images of their cover
sets.  Replacing each `t j` by any function agreeing with it near `chartMap 𝔇 j x` for every
`x ∈ U j` — e.g. a different `Classical.choice` germ representative — lands in the submodule
again.  The overlap law transports because the transition is continuous and matches the chart
coordinates on overlaps (`transitionMap_chartMap`). -/
theorem isOneOneCoeff_congr {t t' : 𝔇.toFiniteCover.ι → ℂ → ℂ} (ht : IsOneOneCoeff 𝔇 t)
    (heq : ∀ j, ∀ x ∈ (𝔇.U j : Set X), t' j =ᶠ[𝓝 (chartMap 𝔇 j x)] t j) :
    IsOneOneCoeff 𝔇 t' := by
  refine ⟨fun j x hx => (ht.1 j x hx).congr_of_eventuallyEq (heq j x hx),
    fun j k x hx => ?_⟩
  have hj : x ∈ (𝔇.U j : Set X) := hx.1
  have hk : x ∈ (𝔇.U k : Set X) := hx.2
  -- The transition tends to `chartMap 𝔇 k x`, so the `k`-germ equality pulls back through it.
  have htend : Tendsto (transitionMap 𝔇 j k) (𝓝 (chartMap 𝔇 j x)) (𝓝 (chartMap 𝔇 k x)) := by
    have hc := (transitionMap_analyticAt 𝔇 hj hk).continuousAt
    rwa [ContinuousAt, transitionMap_chartMap 𝔇 hj] at hc
  have hpull : (fun z => t' k (transitionMap 𝔇 j k z))
      =ᶠ[𝓝 (chartMap 𝔇 j x)] fun z => t k (transitionMap 𝔇 j k z) :=
    (heq k x hk).comp_tendsto htend
  filter_upwards [ht.2 j k x hx, heq j x hj, hpull] with z h1 h2 h3
  rw [h2, h1, ← h3]

end Jacobians.Dolbeault.FineResidue
