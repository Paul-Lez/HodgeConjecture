/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticSegre
public import Other.AlgebraicGeometry.ProjectiveAnalytification
public import Other.AlgebraicGeometry.HolomorphicExponential
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Geometry.Manifold.Complex

/-!
# Global holomorphic functions on components of the explicit elliptic curve

A holomorphic function on a compact complex manifold is locally constant.  This
file records the form of that fact needed by the explicit Cech obstruction: two
points in the same connected component have the same value, without assuming
that the whole analytification is connected.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint

/-- A global holomorphic function on the explicit projective elliptic curve is
constant on every connected component of the top-open subtype. -/
theorem curveGlobalHolomorphicFunction_eq_of_mem_connectedComponent
    (q : OpenHolomorphicFunctions curveVariety 1 (.op ⊤))
    (x y : {z : ComplexPoint curveVariety // z ∈
      (⊤ : Opens (TopCat.of (ComplexPoint curveVariety)))})
    (hy : y ∈ connectedComponent x) :
    q.1 y = q.1 x := by
  letI : IsManifold (modelWithCornersSelf ℂ (Fin 1 → ℂ)) ω
      (ComplexPoint curveVariety) := isManifold_omega curveVariety 1
  letI : CompactSpace
      {z : ComplexPoint curveVariety // z ∈
        (⊤ : Opens (TopCat.of (ComplexPoint curveVariety)))} :=
    isCompact_iff_compactSpace.mp isCompact_univ
  have hlocal : IsLocallyConstant q.1 :=
    ((holomorphicFunctionSheaf_section_analytic curveVariety 1 q).mdifferentiable
      (by simp)).isLocallyConstant
  exact hlocal.apply_eq_of_isPreconnected
    isPreconnected_connectedComponent hy mem_connectedComponent

end AlgebraicGeometry.ExplicitEllipticCandidate
