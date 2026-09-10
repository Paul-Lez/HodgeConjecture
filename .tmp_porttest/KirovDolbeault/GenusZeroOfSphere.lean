/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.GenusSphereBackward
import KirovDolbeault.VanKampen
import Mathlib.Geometry.Manifold.Complex

/-!
# Backward headline `#1b`: a surface `≃ₜ S²` has kirovGenus `0` — assembled route

Target (`Jacobians/DegreeOneSphere.lean`):
```
theorem genus_zero_of_nonempty_homeo_sphere
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) : kirovGenus X = 0
```
with `kirovGenus X = Module.finrank ℂ (HolomorphicOneForms X)`.

## What this file does

`kirovGenus X` is the **analytic** invariant `finrank ℂ (HolomorphicOneForms X)`, whereas the
hypothesis `X ≃ₜ S²` is **purely topological** (a homeomorphism does not preserve the complex
structure). The bridge is the classical contrapositive route from `Jacobians.GenusSphereBackward`:

> `kirovGenus X ≥ 1 ⟹ ∃ ω ≠ 0` closed holomorphic 1-form `⟹` `ω` has a nonzero period `⟹` `X` is
> not simply connected `⟹` `X ̸≃ₜ S²` (since `S²` is simply connected).

Since the original scaffolding was written, **two of its three walls have fallen**:

* **`S²` is simply connected** — now *unconditional* in the repo
  (`Jacobians.VanKampen` proves `twoOpenVanKampen_holds`, giving the global instance
  `SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)`). So
  `h : X ≃ₜ S²` yields `SimplyConnectedSpace X` completely (transport, `simplyConnectedSpace_of_homeo`).
* **Liouville / max-modulus** ("a holomorphic primitive on compact connected `X` is constant")
  — now in Mathlib (`MDifferentiable.exists_eq_const_of_compactSpace`, `Mathlib.Geometry.Manifold.Complex`).

The route is therefore reduced to a **single** genuine analytic input, isolated here as the honest
hypothesis `HasHolomorphicPrimitives X`:

> on a simply connected surface, every holomorphic `1`-form `η` has a *global* holomorphic
> primitive `F : X → ℂ` (`dF = η`).

This is the holomorphic Poincaré lemma / monodromy theorem — true for any simply connected Riemann
surface (path-independence of `∫ η` from simple connectivity, Forster §10.5). Mathlib has the
**plane** version (`Complex.DifferentiableOn.isExactOn_ball`, on balls) and covering-map path-lifting
monodromy, but **not** the manifold de Rham line-integral homotopy invariance needed to globalise the
primitive on an abstract `X`; that is the remaining de Rham wall.

Given `HasHolomorphicPrimitives X`, this file discharges **everything else completely**:
the primitive `F` is constant (Mathlib, compactness), so `mfderiv F = 0`, so `η = 0`; hence
`kirovGenus X = 0`. The capstone `genus_zero_of_nonempty_homeo_sphere_of_hasPrimitives` takes the de Rham
input *and the homeomorphism* and proves the exact target statement, axiom-clean. This mirrors the
repo's established "isolate the one missing classical input as an explicit hypothesis" pattern
(`simplyConnectedSpace_sphere_of_vanKampen`, `AbelStatement`).

## References

* Forster, *Lectures on Riemann Surfaces*, §10.5 (period homotopy invariance), §10 (holomorphic
  forms), §1 (`ℂℙ¹`/`S²` charts).
* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. IV §1.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace Jacobians

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The one remaining analytic input: holomorphic primitives on a simply connected surface -/

/-- **The de Rham wall, isolated.** On a simply connected complex `1`-manifold, every global
holomorphic `1`-form `η` admits a *global* holomorphic primitive `F : X → ℂ` (i.e. `dF = η`,
expressed value-wise on tangent vectors to avoid the cotangent/trivial-bundle type diamond).

This is the holomorphic Poincaré lemma / monodromy theorem: simple connectivity makes `∫ η`
path-independent, so `F(x) := ∫_{x₀}^{x} η` is well defined and holomorphic with `dF = η`
(Forster §10.5). Mathlib provides this only on balls in `ℂ`
(`Complex.DifferentiableOn.isExactOn_ball`); the manifold globalisation (homotopy invariance of the
line integral over loops in `X`) is absent from both Mathlib and this repo — the remaining de Rham
gap. Isolated as an explicit hypothesis, not a gap, so the rest of the route is complete. -/
def HasHolomorphicPrimitives (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Prop :=
  SimplyConnectedSpace X →
    ∀ η : HolomorphicOneForms X, ∃ F : X → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧
      ∀ (x : X) (v : TangentSpace 𝓘(ℂ) x), η.toFun x v = mfderiv 𝓘(ℂ) 𝓘(ℂ) F x v

/-! ### Liouville step (Mathlib): a holomorphic primitive on compact connected `X` is constant -/

/-- A holomorphic form with a *global* holomorphic primitive on a compact connected surface is `0`.
The primitive `F` is constant (`MDifferentiable.exists_eq_const_of_compactSpace`, the manifold
maximum-modulus / Liouville theorem), so `mfderiv F = 0`, so `η` vanishes on every tangent vector,
so `η = 0`. -/
theorem holomorphicOneForm_eq_zero_of_hasPrimitive
    (η : HolomorphicOneForms X) (F : X → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hprim : ∀ (x : X) (v : TangentSpace 𝓘(ℂ) x), η.toFun x v = mfderiv 𝓘(ℂ) 𝓘(ℂ) F x v) :
    η = 0 := by
  -- `F` is constant (compact connected complex manifold ⇒ holomorphic = constant).
  obtain ⟨c, hc⟩ := hF.exists_eq_const_of_compactSpace
  -- Hence `mfderiv F x = 0` everywhere, so `η.toFun x v = 0` for all `x`, `v`.
  apply ContMDiffSection.ext
  intro x
  -- Reduce to the underlying continuous linear map at `x`.
  apply ContinuousLinearMap.ext
  intro v
  have hmf : mfderiv 𝓘(ℂ) 𝓘(ℂ) F x = 0 := by
    rw [hc]; exact mfderiv_const
  have := hprim x v
  rw [hmf] at this
  -- `this : η.toFun x v = (0 : _) v`; both sides are `(0 : HolomorphicOneForms X).toFun x v = 0`.
  simpa using this

/-! ### The route capstones -/

/-- **`#1b`, abstract form.** Given the de Rham input `HasHolomorphicPrimitives X` and that `X` is
simply connected, `kirovGenus X = 0`. Every holomorphic `1`-form has a primitive (input), hence vanishes
(`holomorphicOneForm_eq_zero_of_hasPrimitive`), so the kirovGenus — `finrank ℂ` of the space of such
forms — is `0`. -/
theorem genus_eq_zero_of_hasPrimitives_of_simplyConnected
    (hPrim : HasHolomorphicPrimitives X) (hSC : SimplyConnectedSpace X) :
    kirovGenus X = 0 := by
  apply genus_eq_zero_of_forall_holomorphicOneForm_eq_zero
  intro η
  obtain ⟨F, hF, hprim⟩ := hPrim hSC η
  exact holomorphicOneForm_eq_zero_of_hasPrimitive η F hF hprim

/-- **`#1b`, the exact target — assembled.** A surface homeomorphic to `S²` has `kirovGenus 0`, given the
single remaining de Rham input `HasHolomorphicPrimitives X`.

The simple-connectivity input is supplied *unconditionally* by the repo: `X ≃ₜ S²` transports
`SimplyConnectedSpace` from the now-proven `SimplyConnectedSpace S²`
(`Jacobians.VanKampen`, `twoOpenVanKampen_holds`). Composing with
`genus_eq_zero_of_hasPrimitives_of_simplyConnected` discharges the goal.

This has the exact signature of `genus_zero_of_nonempty_homeo_sphere`
(`Jacobians/DegreeOneSphere.lean`) *plus* the explicit de Rham hypothesis — supplying
`HasHolomorphicPrimitives X` closes that headline obligation. -/
theorem genus_zero_of_nonempty_homeo_sphere_of_hasPrimitives
    (hPrim : HasHolomorphicPrimitives X)
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    kirovGenus X = 0 := by
  obtain ⟨e⟩ := h
  -- `S²` is simply connected (repo, unconditional), so `X` is too (transport).
  have hSC : SimplyConnectedSpace X := simplyConnectedSpace_of_homeo e
  exact genus_eq_zero_of_hasPrimitives_of_simplyConnected hPrim hSC

end Jacobians
