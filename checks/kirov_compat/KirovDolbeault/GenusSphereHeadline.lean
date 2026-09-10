/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import KirovDolbeault.DegreeOneSphere
import KirovDolbeault.RiemannRoch

/-!
# The kirovGenus-0 ⟺ sphere headline (the Riemann–Roch-gated endgame)

The **forward** direction `kirovGenus X = 0 ⟹ X ≃ₜ S²` consumes Riemann–Roch
(`exists_singleSimplePole_of_genus_zero_of_rr`), so it — and the challenge theorem
`genus_eq_zero_iff_homeo` — live here, **downstream** of `Jacobians.RiemannRoch`.

The RR-*free* `toSphere` / degree-route machinery and the degree-one endgame
(`nonempty_homeo_sphere_of_singleSimplePole`) stay in `Jacobians.DegreeOneSphere`, which is now
RR-free and therefore sits **upstream** of `RiemannRoch`. This lets `DegDivResidue` reuse `toSphere`
to prove the residue-theorem degree route (`exists_properMapDegree`), which `RiemannRoch.deg_div`
consumes — closing the upstream/downstream cycle that would otherwise block the degree route.
-/

open scoped Manifold ContDiff in
/-- **Riemann–Roch consequence `l(P) = 2`.** Genus `0` yields a meromorphic function with a single
simple pole (Forster §16: `l(P) = deg P + 1 − g + l(K−P) = 1 + 1 − 0 + 0 = 2`). The single-simple-pole
extraction from `l(P) = 2` is fully proven in `Jacobians.RiemannRoch`; the only remaining inputs are
the classical `exists_riemannRoch_divisor` (Dolbeault/Serre) and `MeromorphicFunction.deg_div`
(argument principle), isolated there. -/
theorem exists_singleSimplePole_of_genus_zero {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (h : kirovGenus X = 0) :
    ∃ (P : X) (f : Jacobians.MeromorphicFunction X), f.HasSingleSimplePole P :=
  Jacobians.exists_singleSimplePole_of_genus_zero_of_rr h

open scoped Manifold ContDiff in
/-- A compact Riemann surface has kirovGenus `0` iff it is homeomorphic to the `2`-sphere — the challenge
theorem (the "anti-hack" constraint preventing `∀ X, kirovGenus X = 0`).

The **forward** direction is the genuine content: kirovGenus `0` ⟹ a single-simple-pole meromorphic
function (`exists_singleSimplePole_of_genus_zero`, Riemann–Roch) ⟹ a degree-1 map `X → ℂℙ¹` ⟹
`X ≃ₜ S²` (`Jacobians.nonempty_homeo_sphere_of_singleSimplePole`, the degree-one endgame). The
**backward** direction is `Ω(ℂℙ¹) = 0` (`genus_zero_of_nonempty_homeo_sphere`). -/
theorem genus_eq_zero_iff_homeo {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    kirovGenus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  ⟨fun h => by
    obtain ⟨P, f, hP⟩ := exists_singleSimplePole_of_genus_zero h
    exact Jacobians.nonempty_homeo_sphere_of_singleSimplePole f hP,
   genus_zero_of_nonempty_homeo_sphere⟩
