/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.ProjectiveLine
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# `S²` is simply connected — reachable scaffolding for `#1b`

The backward headline `#1b` (`genus_zero_of_nonempty_homeo_sphere`,
`Jacobians/DegreeOneSphere.lean`) and its transport helper
`Jacobians.simplyConnectedSpace_of_homeo_sphere` (`Jacobians/GenusSphereBackward.lean`)
carry **`SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)`** as an
explicit hypothesis, because Mathlib provides only a `proof_wanted` for the Poincaré
conjecture and nothing about `π₁(Sⁿ)`.  This file assembles, with no gaps, every piece of
that instance *except* the single irreducible analytic/topological core — the abstract
**two-open van Kampen** statement, which Mathlib lacks entirely.

## The model: the Riemann sphere `OnePoint ℂ`

The repo's `S²` is reached through `RiemannSphere.homeoSphere : OnePoint ℂ ≃ₜ S²`
(`Jacobians/ProjectiveLine.lean`), so we prove simple-connectivity for the **more tractable**
model `OnePoint ℂ = ℂ ∪ {∞}` and transport along that homeomorphism (simple-connectivity is a
homeomorphism invariant, `Homeomorph.toHomotopyEquiv` + `simplyConnectedSpace_iff`).

`OnePoint ℂ` is covered by two opens, each **contractible** (hence simply connected):

* `U := {∞}ᶜ = range (↑) ≃ₜ ℂ` — the affine chart;
* `V := {0}ᶜ` — the `∞`-chart, `≃ₜ ℂ` via the inversion `invMap` (`z ↦ z⁻¹`, swapping `0 ↔ ∞`),
  so `V = invMap '' U`.

Their overlap `U ∩ V` is the finite nonzero locus `≃ₜ ℂ ∖ {0}`, which is **path-connected**
(`isPathConnected_compl_singleton_of_one_lt_rank`, `rank ℝ ℂ = 2 > 1`).  The whole space is
path-connected (`OnePoint`'s `ConnectedSpace` + `LocPathConnectedSpace`).

## What is proved here, and the one wall

* **Transport** to the exact target type — `simplyConnectedSpace_sphere_of_onePoint`.
* **`U` simply connected** — `isSimplyConnected_compl_infty`.
* **`V` simply connected** — `isSimplyConnected_compl_zero`.
* **`U ∪ V = univ`** and **`U ∩ V` path-connected** — `union_charts_eq_univ`,
  `isPathConnected_inter_charts`.
* **`OnePoint ℂ` path-connected** — free instance.

The **single wall** is the abstract engine

```
TwoOpenVanKampen :
  ∀ {Z} [TopologicalSpace Z] [PathConnectedSpace Z] {U V : Set Z},
    IsOpen U → IsOpen V → U ∪ V = univ →
    IsSimplyConnected U → IsSimplyConnected V → IsPathConnected (U ∩ V) →
    SimplyConnectedSpace Z
```

i.e. Seifert–van Kampen specialised to a two-element simply-connected open cover with
path-connected intersection.  **Mathlib has no Seifert–van Kampen for `π₁`** (the `VanKampen`
files are category-theoretic colimit/extensive-category notions; the only sphere-homotopy facts
are the `proof_wanted`s in `Mathlib/Geometry/Manifold/PoincareConjecture.lean`).  Its proof is a
genuine homotopy-theory development (Lebesgue-subdivide a loop into arcs each inside one chart,
route the joins through `U ∩ V`, and fill inductively): realistically several hundred to ~1–1.5k
LoC.  We therefore take it as an explicit hypothesis in the capstones
`simplyConnectedSpace_onePoint_of_vanKampen` and `simplyConnectedSpace_sphere_of_vanKampen`,
which compose it with all the (proven) side-conditions and the transport — leaving exactly that
one input to discharge, the same pattern the repo already uses downstream.

## References

* Forster, *Lectures on Riemann Surfaces*, §1 (`ℂℙ¹` as two charts).
* tom Dieck, *Algebraic Topology*, §2.7–2.8 (Seifert–van Kampen; the two-open corollary).
-/

noncomputable section

open scoped Topology
open Set OnePoint

namespace Jacobians.RiemannSphere

/-! ### The abstract two-open van Kampen statement (the wall)

This is the one input Mathlib does not provide.  Stated as a `Prop`-valued abbreviation so the
capstones can take it as a single hypothesis. -/

/-- **Two-open van Kampen.** A space that is path-connected and is the union of two open simply
connected subsets with path-connected intersection is simply connected.  This is the only piece
of the `SimplyConnectedSpace (OnePoint ℂ)` proof that Mathlib does not supply (no Seifert–van
Kampen for `π₁`); every *use* of it below has all side-conditions discharged. -/
def TwoOpenVanKampen : Prop :=
  ∀ {Z : Type} [TopologicalSpace Z] [PathConnectedSpace Z] {U V : Set Z},
    IsOpen U → IsOpen V → U ∪ V = Set.univ →
    IsSimplyConnected U → IsSimplyConnected V → IsPathConnected (U ∩ V) →
    SimplyConnectedSpace Z

/-! ### The two contractible charts of `OnePoint ℂ` -/

/-- The affine chart `U = {∞}ᶜ` is **simply connected**: it is `range (↑) ≃ₜ ℂ`, and `ℂ` is a
real topological vector space, hence contractible, hence simply connected. -/
theorem isSimplyConnected_compl_infty :
    IsSimplyConnected ({∞}ᶜ : Set (OnePoint ℂ)) := by
  -- `ℂ` is contractible ⇒ simply connected; transport `univ ≃ₜ ℂ` then embed by `coe`.
  haveI : SimplyConnectedSpace ℂ := SimplyConnectedSpace.ofContractible ℂ
  have huniv : IsSimplyConnected (Set.univ : Set ℂ) := by
    rw [IsSimplyConnected]
    exact (Homeomorph.Set.univ ℂ).toHomotopyEquiv.simplyConnectedSpace
  -- `{∞}ᶜ = range coe = coe '' univ`.
  have himg : IsSimplyConnected ((↑) '' (Set.univ : Set ℂ) : Set (OnePoint ℂ)) :=
    (OnePoint.isOpenEmbedding_coe.isEmbedding.isSimplyConnected_image).2 huniv
  rwa [Set.image_univ, ← OnePoint.compl_infty] at himg

/-- The `∞`-chart `V = {0}ᶜ` is **simply connected**: it is the image of the affine chart `{∞}ᶜ`
under the inversion self-homeomorphism `inversionHomeomorph` (which swaps `0 ↔ ∞`), so
`V = inversionHomeomorph '' {∞}ᶜ`, and simple-connectivity is a homeomorphism invariant. -/
theorem isSimplyConnected_compl_zero :
    IsSimplyConnected ({((0 : ℂ) : OnePoint ℂ)}ᶜ : Set (OnePoint ℂ)) := by
  -- `inversionHomeomorph '' {∞}ᶜ = {0}ᶜ`.
  have himg : inversionHomeomorph '' ({∞}ᶜ : Set (OnePoint ℂ))
      = ({((0 : ℂ) : OnePoint ℂ)}ᶜ : Set (OnePoint ℂ)) := by
    ext p
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff,
      inversionHomeomorph_apply]
    constructor
    · rintro ⟨q, hq, rfl⟩
      intro hcontra
      -- `invMap q = (0:ℂ)` forces `q = ∞`.
      apply hq
      have := congrArg invMap hcontra
      rwa [involutive_invMap, invMap_coe_zero] at this
    · intro hp
      refine ⟨invMap p, ?_, by rw [involutive_invMap]⟩
      intro hcontra
      -- `invMap p = ∞` forces `p = (0:ℂ)`.
      apply hp
      have := congrArg invMap hcontra
      rwa [involutive_invMap, invMap_infty] at this
  rw [← himg]
  exact (inversionHomeomorph.isSimplyConnected_image).2 isSimplyConnected_compl_infty

/-! ### The cover and its intersection -/

/-- The two charts cover the sphere: `{∞}ᶜ ∪ {0}ᶜ = univ` (no point is both `∞` and `0`). -/
theorem union_charts_eq_univ :
    ({∞}ᶜ : Set (OnePoint ℂ)) ∪ ({((0 : ℂ) : OnePoint ℂ)}ᶜ) = Set.univ := by
  rw [← Set.compl_inter, Set.compl_univ_iff, Set.eq_empty_iff_forall_notMem]
  rintro p ⟨h1, h2⟩
  simp only [Set.mem_singleton_iff] at h1 h2
  exact OnePoint.infty_ne_coe 0 (h1.symm.trans h2)

/-- The overlap of the two charts is path-connected: `{∞}ᶜ ∩ {0}ᶜ` is the image under `coe` of
`ℂ ∖ {0}`, which is path-connected because `rank ℝ ℂ = 2 > 1`. -/
theorem isPathConnected_inter_charts :
    IsPathConnected (({∞}ᶜ : Set (OnePoint ℂ)) ∩ ({((0 : ℂ) : OnePoint ℂ)}ᶜ)) := by
  -- `ℂ ∖ {0}` is path-connected.
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have hcompl : IsPathConnected (({(0 : ℂ)}ᶜ) : Set ℂ) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  -- Its image under the open embedding `coe` is path-connected, and equals the overlap.
  have himg : IsPathConnected ((↑) '' (({(0 : ℂ)}ᶜ) : Set ℂ) : Set (OnePoint ℂ)) :=
    hcompl.image OnePoint.continuous_coe
  have hset : ((↑) '' (({(0 : ℂ)}ᶜ) : Set ℂ) : Set (OnePoint ℂ))
      = ({∞}ᶜ : Set (OnePoint ℂ)) ∩ ({((0 : ℂ) : OnePoint ℂ)}ᶜ) := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
      exact ⟨OnePoint.coe_ne_infty z, fun h => hz (OnePoint.coe_injective h)⟩
    · rintro ⟨h1, h2⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h1 h2
      -- `p ≠ ∞`, so `p = coe z` for some `z`; and `p ≠ 0` gives `z ≠ 0`.
      induction p using OnePoint.rec with
      | infty => exact absurd rfl h1
      | coe z =>
        refine ⟨z, ?_, rfl⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hz; exact h2 (by rw [hz])
  rwa [hset] at himg

/-! ### The capstones (resting on the one missing engine) -/

/-- **`OnePoint ℂ` is simply connected** — modulo the abstract two-open van Kampen engine.
Every side-condition (path-connectivity, the two simply-connected charts, the cover equation, the
path-connected overlap) is discharged above; only `vanKampen` itself — Seifert–van
Kampen for a two-element open cover, absent from Mathlib — is taken as input. -/
theorem simplyConnectedSpace_onePoint_of_vanKampen (vanKampen : TwoOpenVanKampen) :
    SimplyConnectedSpace (OnePoint ℂ) :=
  vanKampen isOpen_compl_singleton isOpen_compl_singleton union_charts_eq_univ
    isSimplyConnected_compl_infty isSimplyConnected_compl_zero isPathConnected_inter_charts

/-- **The Euclidean `2`-sphere `S² ⊆ ℝ³` is simply connected** — modulo the same engine.
Transports `simplyConnectedSpace_onePoint_of_vanKampen` along `homeoSphere : OnePoint ℂ ≃ₜ S²`
(simple-connectivity is a homeomorphism invariant). This is *exactly* the hypothesis that
`Jacobians.simplyConnectedSpace_of_homeo_sphere` and `genus_zero_of_nonempty_homeo_sphere`
consume; supplying `TwoOpenVanKampen` discharges `#1b`'s backward simple-connectivity input. -/
theorem simplyConnectedSpace_sphere_of_vanKampen (vanKampen : TwoOpenVanKampen) :
    SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  haveI := simplyConnectedSpace_onePoint_of_vanKampen vanKampen
  exact homeoSphere.toHomotopyEquiv.symm.simplyConnectedSpace

end Jacobians.RiemannSphere
