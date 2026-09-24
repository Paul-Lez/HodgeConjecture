/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingLift
public import Other.AlgebraicGeometry.ChernWindingUnitClass
public import Other.Geometry.Manifold.HolomorphicLogarithm

/-!
# Holomorphic logarithms on a simply connected chart

The `exists_log` field of `AlgebraicGeometry.ComplexPoint.ChernWindingChart` asks that every
invertible holomorphic function on the chart be `exp(2πi f)`.  The repository only had the
germ-local `ContMDiffAt.exists_local_log`.  This file proves the statement on any **simply
connected, locally path connected** analytic open — in particular on a ball of a holomorphic
chart:

`AlgebraicGeometry.ComplexPoint.exists_holomorphicExponential_of_simplyConnected`.

The proof has two steps.

* *Topology.*  The underlying continuous function of the unit is nowhere zero, so
  `ChernWinding.exists_expLift` (the covering-space lifting criterion for `Complex.exp`) produces
  a **continuous** logarithm `L` on the whole open.
* *Holomorphy.*  Near any point, `ContMDiffAt.exists_local_log` produces a holomorphic logarithm
  `G`; then `exp (L - G) = 1` near that point, so by
  `ContinuousAt.exists_local_exp_period` the continuous function `L - G` is locally the constant
  `n · 2πi`.  Hence `L` agrees near the point with `G + n · 2πi`, which is holomorphic, so `L`
  itself is.

The last section records that these two topological hypotheses hold for an analytic open
homeomorphic to a nonempty convex subset of a real normed space — e.g. to a ball in a holomorphic
chart (`ChernWinding.simplyConnectedSpace_of_homeomorphConvex`,
`ChernWinding.locallyPathConnectedSpace_of_homeomorphConvex`).
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace ChernWinding

/-! ### Transporting the two hypotheses along a homeomorphism with a convex set -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
  {Z : Type*} [TopologicalSpace Z]

theorem simplyConnectedSpace_of_homeomorphConvex (hs : Convex ℝ s) (hne : s.Nonempty)
    (φ : Z ≃ₜ s) : SimplyConnectedSpace Z :=
  letI : ContractibleSpace s := hs.contractibleSpace hne
  φ.toHomotopyEquiv.simplyConnectedSpace

theorem locallyPathConnectedSpace_of_homeomorphConvex (hs : Convex ℝ s)
    (φ : Z ≃ₜ s) : LocallyPathConnectedSpace Z :=
  letI : LocallyPathConnectedSpace s := Convex.locallyPathConnectedSpace hs
  φ.isOpenEmbedding.locallyPathConnectedSpace

end ChernWinding

namespace AlgebraicGeometry.ComplexPoint

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance chernWindingHolomorphicLogTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- **A holomorphic unit on a simply connected analytic open is an exponential.**  This is the
`exists_log` field of `ChernWindingChart`, for any simply connected, locally path connected
chart. -/
theorem exists_holomorphicExponential_of_simplyConnected
    (V : Opens (TopCat.of (ComplexPoint X)))
    [SimplyConnectedSpace (V : Set (ComplexPoint X))]
    [LocallyPathConnectedSpace (V : Set (ComplexPoint X))]
    (u : (holomorphicUnitSheaf X d).obj.obj (op V)) :
    ∃ f : (holomorphicAdditiveSheaf X d).obj.obj (op V),
      (holomorphicExponential X d).hom.app (op V) f = u := by
  classical
  -- the nowhere vanishing continuous function underlying the unit
  set F : C^ω⟮𝓘(ℂ, Fin d → ℂ), ↥V; 𝓘(ℂ, ℂ), ℂ⟯ := (unitOf u).val with hF
  have hFne : ∀ y : ↥V, F y ≠ 0 := by
    intro y hy
    have h : (F * (unitOf u).inv) y =
        (1 : C^ω⟮𝓘(ℂ, Fin d → ℂ), ↥V; 𝓘(ℂ, ℂ), ℂ⟯) y := by rw [hF, (unitOf u).val_inv]
    rw [show ((F * (unitOf u).inv) y) = F y * (unitOf u).inv y from rfl, hy, zero_mul] at h
    exact zero_ne_one h
  have hcont : Continuous (fun y : ↥V => F y) := F.2.continuous
  obtain ⟨y₀⟩ : Nonempty (V : Set (ComplexPoint X)) := PathConnectedSpace.nonempty
  obtain ⟨L, hL⟩ := ChernWinding.exists_expLift (⟨fun y => F y, hcont⟩ : C(↥V, ℂ)) hFne y₀
  -- the continuous logarithm is holomorphic
  have hsm : ∀ y : ↥V, ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ) ω (fun z : ↥V => L z) y := by
    intro y
    obtain ⟨G, hGsm, hGe⟩ := ContMDiffAt.exists_local_log (I := 𝓘(ℂ, Fin d → ℂ))
      (f := fun z : ↥V => F z) (x := y) F.2.contMDiffAt (hFne y)
    have hexp1 : ∀ᶠ z in nhds y, Complex.exp (L z - G z) = 1 := by
      filter_upwards [hGe] with z hz
      rw [Complex.exp_sub, hL z, hz]
      exact div_self (hFne z)
    obtain ⟨n, hn⟩ := ContinuousAt.exists_local_exp_period
      (f := fun z : ↥V => L z - G z) (L.continuous.continuousAt.sub hGsm.continuousAt) hexp1
    refine ContMDiffAt.congr_of_eventuallyEq
      (f := fun z : ↥V => G z + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
      (hGsm.add contMDiffAt_const) ?_
    filter_upwards [hn] with z hz
    rw [← hz]
    ring
  refine ⟨(⟨fun y : ↥V => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * L y,
    fun y => contMDiffAt_const.mul (hsm y)⟩ :
      C^ω⟮𝓘(ℂ, Fin d → ℂ), ↥V; 𝓘(ℂ, ℂ), ℂ⟯), ?_⟩
  refine unitOf_injective fun y => ?_
  show Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
    ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ * L y)) = F y
  rw [← mul_assoc, mul_inv_cancel₀ ChernWinding.twoPiI_ne_zero, one_mul]
  exact hL y

end AlgebraicGeometry.ComplexPoint
