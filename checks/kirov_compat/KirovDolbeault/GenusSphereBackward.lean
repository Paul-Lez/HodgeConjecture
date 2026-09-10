/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.Genus
import KirovDolbeault.HolomorphicForms
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Backward headline `#1b`: a surface `≃ₜ S²` has kirovGenus `0` — reachable scaffolding

Target (`Jacobians/DegreeOneSphere.lean`):
```
theorem genus_zero_of_nonempty_homeo_sphere
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) : kirovGenus X = 0
```
with `kirovGenus X = Module.finrank ℂ (HolomorphicOneForms X)`.

## Intended PDE-free route (prove the contrapositive)

`kirovGenus X ≥ 1 ⟹ X` is NOT simply connected ⟹ `X ̸≃ₜ S²`:

1. `kirovGenus X ≥ 1 ⟹ ∃ ω : HolomorphicOneForms X, ω ≠ 0`.  *(linear algebra — DONE here)*
2. A holomorphic `1`-form is **closed** (`dω = 0`).
3. **Not exact**: `ω = df` globally ⟹ `f` holomorphic on compact `X` ⟹ `f` constant
   (max-modulus / Liouville) ⟹ `ω = 0`, contradiction.
4. **closed + not exact ⟹ ∃ loop `γ` with `∮_γ ω ≠ 0`** ⟹ `γ` not null-homotopic ⟹
   `X` not simply connected.
5. `S²` is **simply connected** and `≃ₜ` preserves simple connectivity, so
   `X ≃ₜ S² ⟹ X` simply connected — contradicting step 4.

## Status of the route in Mathlib + this repo (see module-level report)

* **Step 1**: fully provable.  Provided below as `exists_ne_zero_holomorphicOneForm_of_genus_pos`
  and its contrapositive `genus_eq_zero_of_forall_holomorphicOneForm_eq_zero`.
* **Step 5 — homeomorphism transport**: the *transport half* is in Mathlib
  (`Homeomorph.toHomotopyEquiv` + `ContinuousMap.HomotopyEquiv.simplyConnectedSpace_iff`).
  Provided below as `simplyConnectedSpace_of_homeo` and the sphere-specialised
  `simplyConnectedSpace_of_homeo_sphere`.
* **Step 5 — `S²` simply connected**: **NOT in Mathlib** (a `proof_wanted` in
  `Mathlib/Geometry/Manifold/PoincareConjecture.lean`).  This is a genuine gap.
* **Step 4 — closed-not-exact ⟹ nonzero period**: **absent** from both Mathlib (no manifold
  de Rham / no homotopy-invariance of curve integrals over manifold loops; the convex-set
  Poincaré lemma in `Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean` does not lift)
  and this repo (`Jacobians/LineIntegral.lean` explicitly removed even a *local* version for
  lack of a `Convex`/`SimplyConnected` hypothesis).  This is the de Rham / Hodge wall.

The two missing nodes (steps 4 and 5b) are each substantial independent developments, so `#1b`
is **not** closable on this route today.  Everything that *is* reachable is below.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace Jacobians

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Step 1 — positivity of the kirovGenus produces a nonzero holomorphic form -/

/-- **Step 1.** If `kirovGenus X ≥ 1` then there is a nonzero global holomorphic `1`-form.
Pure linear algebra: a positive `finrank` over the field `ℂ` forces the module to be
nontrivial, hence to contain an element distinct from `0`. -/
theorem exists_ne_zero_holomorphicOneForm_of_genus_pos (h : 1 ≤ kirovGenus X) :
    ∃ η : HolomorphicOneForms X, η ≠ 0 := by
  have hpos : 0 < Module.finrank ℂ (HolomorphicOneForms X) := h
  have : Nontrivial (HolomorphicOneForms X) := Module.nontrivial_of_finrank_pos hpos
  exact exists_ne 0

/-- **Step 1, contrapositive form** — the exact logical shape the endgame consumes.
If *every* global holomorphic `1`-form vanishes, the kirovGenus is `0`.  (This is the conclusion
the route delivers: route steps 2–5 show, under `X ≃ₜ S²`, that no nonzero form can exist.) -/
theorem genus_eq_zero_of_forall_holomorphicOneForm_eq_zero
    (h : ∀ η : HolomorphicOneForms X, η = 0) : kirovGenus X = 0 := by
  by_contra hne
  obtain ⟨η, hη⟩ := exists_ne_zero_holomorphicOneForm_of_genus_pos
    (Nat.one_le_iff_ne_zero.mpr hne)
  exact hη (h η)

/-! ### Step 5 — homeomorphism transport of simple connectivity (the provable half) -/

/-- **Step 5 (transport).** A homeomorphism transports simple connectivity:
if `Y` is simply connected and `X ≃ₜ Y`, then `X` is simply connected.
Via `Homeomorph.toHomotopyEquiv` and `ContinuousMap.HomotopyEquiv.simplyConnectedSpace`. -/
theorem simplyConnectedSpace_of_homeo {Y : Type*} [TopologicalSpace Y]
    [SimplyConnectedSpace Y] (e : X ≃ₜ Y) : SimplyConnectedSpace X :=
  e.toHomotopyEquiv.simplyConnectedSpace

/-- **Step 5 (transport), `iff` form.** Simple connectivity is a homeomorphism invariant. -/
theorem simplyConnectedSpace_iff_of_homeo {Y : Type*} [TopologicalSpace Y] (e : X ≃ₜ Y) :
    SimplyConnectedSpace X ↔ SimplyConnectedSpace Y :=
  e.toHomotopyEquiv.simplyConnectedSpace_iff

/-- **Step 5, specialised to the `2`-sphere.** *If* `S² ⊆ ℝ³` is simply connected
(an input still missing from Mathlib — a `proof_wanted` in
`Mathlib/Geometry/Manifold/PoincareConjecture.lean`), then any `X ≃ₜ S²` is simply connected.
Phrased with `SimplyConnectedSpace (sphere …)` as an explicit hypothesis so the statement is
**complete** and ready to be discharged the moment that instance lands. -/
theorem simplyConnectedSpace_of_homeo_sphere
    (hS : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (e : X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    SimplyConnectedSpace X :=
  (simplyConnectedSpace_iff_of_homeo e).mpr hS

end Jacobians
