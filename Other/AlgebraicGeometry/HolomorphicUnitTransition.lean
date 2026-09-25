/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicUnitExtension

/-!
# Holomorphic transition functions of a unit-sheaf extension

The additive transition sections of a unit-sheaf extension are invertible holomorphic
functions. Their additive cocycle law becomes the multiplicative gluing law.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint.HolomorphicUnitExtension

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance holomorphicUnitTransitionTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

variable (E : HolomorphicUnitExtension X d)

/-- The nowhere-zero holomorphic transition function on a common open subset. -/
def transitionUnit (x y : ComplexPoint X) (V : Opens (TopCat.of (ComplexPoint X)))
    (hx : V ≤ E.localLifts.opens x) (hy : V ≤ E.localLifts.opens y) :
    (C^ω⟮𝓘(ℂ, Fin d → ℂ), V; ℂ⟯)ˣ :=
  Additive.toMul (E.localLifts.transition E.shortExact x y V hx hy)

/-- The self-transition is the constant unit `1`. -/
@[simp]
theorem transitionUnit_self (x : ComplexPoint X)
    (V : Opens (TopCat.of (ComplexPoint X))) (hx : V ≤ E.localLifts.opens x) :
    E.transitionUnit x x V hx hx = 1 :=
  congrArg Additive.toMul (E.localLifts.transition_self E.shortExact x V hx)

/-- The transition functions satisfy the multiplicative cocycle identity. -/
theorem transitionUnit_mul (x y z : ComplexPoint X)
    (V : Opens (TopCat.of (ComplexPoint X)))
    (hx : V ≤ E.localLifts.opens x) (hy : V ≤ E.localLifts.opens y)
    (hz : V ≤ E.localLifts.opens z) :
    E.transitionUnit x y V hx hy * E.transitionUnit y z V hy hz =
      E.transitionUnit x z V hx hz :=
  congrArg Additive.toMul (E.localLifts.transition_add E.shortExact x y z V hx hy hz)

/-- Restricting a transition function gives the transition function on the smaller overlap. -/
theorem transitionUnit_restrict_apply (x y : ComplexPoint X)
    {U V : Opens (TopCat.of (ComplexPoint X))}
    (hx : U ≤ E.localLifts.opens x) (hy : U ≤ E.localLifts.opens y) (hVU : V ≤ U)
    (z : V) :
    (E.transitionUnit x y V (hVU.trans hx) (hVU.trans hy)).val z =
      (E.transitionUnit x y U hx hy).val ⟨z, hVU z.property⟩ := by
  have h := E.localLifts.transition_restrict E.shortExact x y hx hy hVU
  exact (congrArg (fun c : E.shortComplex.X₁.obj.obj (op V) =>
    (show Additive (C^ω⟮𝓘(ℂ, Fin d → ℂ), V; ℂ⟯)ˣ from c).toMul.val z) h).symm

/-- A transition function does not vanish at any point of its domain. -/
theorem transitionUnit_ne_zero (x y : ComplexPoint X)
    (V : Opens (TopCat.of (ComplexPoint X)))
    (hx : V ≤ E.localLifts.opens x) (hy : V ≤ E.localLifts.opens y) (z : V) :
    (E.transitionUnit x y V hx hy).val z ≠ 0 :=
  ((E.transitionUnit x y V hx hy).isUnit.map
    (ContMDiffMap.evalRingHom (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) z)).ne_zero

end AlgebraicGeometry.ComplexPoint.HolomorphicUnitExtension
