/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import KirovDolbeault.Discharge.Manifold.FibreCardWellDefinedAtRegular
import KirovDolbeault.Discharge.Manifold.PreconnectedFromFiniteComplement
import KirovDolbeault.Discharge.Manifold.RegularSubsetPreconnected

/-! # Hurwitz constant-card, staged on `h_path` (ZZ160, ZZ172-corrected)

Compose ZZ155 (`fibre_card_well_defined_at_regular_holds_of_lc_ncard_and_topo`)
with ZZ159 (`h_topo_of_h_path`) so that the *only* topological residual
exposed at the headline is the manifold-lift content `(M1)`:

```
∀ C : Set Y, C.Finite → (Cᶜ).Nonempty → IsPathConnected (Cᶜ : Set Y).
```

When `(M1)` lands unconditionally (target of ZZ165), this theorem
becomes one rewrite away from the strict-closure of the constant-card
statement.

## What this file does and does not deliver

This file *stages* the topological side. ZZ155 still needs the analytic
content this file does not — and cannot, at the present pin — discharge:

* **Per-`f` regular-subset packaging.** The consumer supplies, for every
  non-constant analytic `f`, a finite set `C ⊆ Y` such that
  - every `RegularValueWitnessReg f` has its `value` in `Cᶜ`, and
  - the fibre-cardinality `(f ⁻¹' {y}).ncard` is locally constant on `Cᶜ`.

  Specialising `C := f.criticalValues` is what ZZ100 produces under a
  `CriticalSetWitness` for `f : MeromorphicNonzero X` (Riemann-sphere
  target). For an arbitrary `f : X → Y` between general complex
  1-manifolds, no unconditional packaging is available at this pin.

The wrapper below therefore exposes the analytic packaging as a single
`h_pkg` parameter, with `h_path` factored out via ZZ159 so the
*topological* residual is the single named manifold-lift content `(M1)`.

Compared with the pre-ZZ172 version, the universally-false `h_C_fin`
hypothesis (which asserted that *every* set in `Y` is finite) is removed.
The `C` finiteness is instead supplied by the per-`f` packaging.

No gaps, no `axiom`. -/

@[expose] public section

open Set
open scoped Manifold ContDiff

namespace Jacobians.Discharge

namespace ContMDiff

namespace Degree

universe u v

/-- **Hurwitz constant-card, staged on `h_path` (ZZ172-corrected).**

Given:

* `h_path` — manifold-lift `(M1)`: the complement of any finite set in
  `Y` is path-connected (when nonempty). This is the *single* named
  topological residual; ZZ159 turns it into the `IsPreconnected`
  hypothesis that ZZ134 consumes.
* `h_pkg` — per-`f` packaging: existence of a finite `C ⊆ Y` with
  - regular witnesses' values in `Cᶜ`,
  - locally-constant fibre-ncard on `Cᶜ`.

Conclude the unfolded form of `fibre_card_well_defined_at_regular_statement`.

When ZZ165 lands `h_path` unconditionally as a theorem of complex
1-manifolds, this wrapper closes to a one-input statement parameterised
only on the per-`f` analytic packaging. -/
theorem fibre_card_well_defined_at_regular_holds_of_h_path
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (h_path : ∀ C : Set Y, C.Finite → (Cᶜ : Set Y).Nonempty →
      IsPathConnected (Cᶜ : Set Y))
    (h_pkg : ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
      ∃ (C : Set Y), C.Finite ∧
        (∀ w : RegularValueWitnessReg f, w.toWitness.value ∈ (Cᶜ : Set Y)) ∧
        IsLocallyConstant
          (fun y : (Cᶜ : Set Y) => (f ⁻¹' {y.val}).ncard)) :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f → ¬ Jacobians.Discharge.IsConstantMap f →
      ∀ (w₁ w₂ : RegularValueWitnessReg f), w₁.card = w₂.card := by
  -- Build h_topo from h_path via ZZ159.
  have h_topo : ∀ C : Set Y, C.Finite → IsPreconnected (Cᶜ : Set Y) :=
    Jacobians.Discharge.Manifold.h_topo_of_h_path h_path
  -- Apply ZZ155 (corrected): supply the bundled (R, h_supp, h_lc, h_conn).
  apply fibre_card_well_defined_at_regular_holds_of_lc_ncard_and_topo
  intro f hf hnc
  obtain ⟨C, hC_fin, h_supp, h_lc⟩ := h_pkg f hf hnc
  refine ⟨(Cᶜ : Set Y), h_supp, h_lc, ?_⟩
  -- IsPreconnected (univ : Set Cᶜ) from h_topo via subtype lift.
  exact Jacobians.Discharge.Manifold.regularSubset_isPreconnected_of_finite_complement_hypothesis
    h_topo C hC_fin

end Degree

end ContMDiff

end Jacobians.Discharge
