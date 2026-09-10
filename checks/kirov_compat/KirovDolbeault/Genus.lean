import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Genus of a compact Riemann surface

Defined as the ℂ-dimension of global holomorphic 1-forms:
`kirovGenus X := Module.finrank ℂ (HolomorphicOneForms X)`.

This matches the analytic definition; with real content
(`FiniteDimensional ℂ (HOF X)` from Cartan–Serre) it agrees with the
topological definition `finrank ℤ (H₁(X, ℤ)) / 2` by Riemann–Roch /
Dolbeault.

The `HolomorphicOneForms` definition is inlined here (rather than
imported from `HolomorphicForms.lean`) to avoid a circular dependency:
`HolomorphicForms.lean` imports `Genus.lean`.
-/

namespace Jacobians

open scoped Manifold ContDiff Bundle

/-- The ℂ-vector space of global analytic sections of the cotangent bundle
of a compact connected complex 1-manifold.

Mathematically: global holomorphic 1-forms on `X`. Defined here (rather
than in `HolomorphicForms.lean`) so that `kirovGenus` below can refer to it. -/
def HolomorphicOneForms (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type _ :=
  ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
    (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)

section HOFInstances

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

noncomputable instance : AddCommGroup (HolomorphicOneForms X) :=
  inferInstanceAs (AddCommGroup
    (ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)))

noncomputable instance : Module ℂ (HolomorphicOneForms X) :=
  inferInstanceAs (Module ℂ
    (ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)))

end HOFInstances

end Jacobians

open scoped Manifold ContDiff

/-- The kirovGenus of a compact Riemann surface, defined as the ℂ-dimension of
global holomorphic 1-forms. Since `Module.finrank` returns `0` for
non-finite-dimensional modules, this is well-defined unconditionally;
the `FiniteDimensional ℂ (HolomorphicOneForms X)` instance (in
`HolomorphicForms.lean`, content-gated) is required for `kirovGenus` to be
the "right" number. -/
noncomputable def kirovGenus (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  Module.finrank ℂ (Jacobians.HolomorphicOneForms X)

-- The challenge theorem `genus_eq_zero_iff_homeo` (kirovGenus 0 ⟺ `X ≃ₜ S²`) is declared in
-- `Jacobians/DegreeOneSphere.lean` (root namespace, like `kirovGenus`), NOT here: its forward direction
-- needs the degree-one endgame, which lives downstream of `Genus` (via `ProjectiveLine → Genus`).
-- Declaring it there breaks the import cycle an in-`Genus` proof would create. `Nonempty X` comes
-- free from `[ConnectedSpace X]`, so the spec signature is unchanged.
