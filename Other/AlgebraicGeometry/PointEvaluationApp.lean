/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexAffineSpace

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Evaluation of a regular function at a complex point, through `app`

`ComplexPoint.evaluate_top_eq_appTop` computes the value of a *global* regular function at a
complex point as `(ΓSpecIso ℂ).hom (z.left.appTop s)`.  This file records the same statement for a
regular function on an arbitrary open `U` whose preimage under the point is all of `Spec ℂ` —
equivalently, whose domain contains the point.  This is the elementary bridge between
`Point.evaluate` and the `Scheme.Hom.app` calculus, and it makes evaluations computable by
factoring the point through an affine chart.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.ComplexPoint

variable {X : Over (Spec ↧ℂ)}

/-- **Evaluation through `appLE`.**  If the preimage of `U` under a complex point is all of
`Spec ℂ`, the value of a regular function on `U` at that point is its image under
`z.left.appLE U ⊤`, read in `ℂ` through `ΓSpecIso`. -/
theorem evaluate_eq_appLE_top (U : X.left.Opens) (s : Γ(X.left, U)) (z : ComplexPoint X)
    (h : (⊤ : (Spec ↧ℂ).Opens) ≤ z.left ⁻¹ᵁ U) :
    Point.evaluate U s z = (Scheme.ΓSpecIso ↧ℂ).hom (z.left.appLE U ⊤ h s) := by
  have hz : z = Point.map z (𝟙 (Over.mk (𝟙 (Spec ↧ℂ)))) := by
    change z = 𝟙 (Over.mk (𝟙 (Spec ↧ℂ))) ≫ z
    rw [Category.id_comp]
  calc Point.evaluate U s z
      = Point.evaluate U s (Point.map z (𝟙 (Over.mk (𝟙 (Spec ↧ℂ))))) := by rw [← hz]
    _ = Point.evaluate (z.left ⁻¹ᵁ U) (z.left.app U s)
          (𝟙 (Over.mk (𝟙 (Spec ↧ℂ)))) := Point.evaluate_map z U s _
    _ = Point.evaluate (⊤ : (Spec ↧ℂ).Opens)
          ((Spec ↧ℂ).presheaf.map (homOfLE h).op (z.left.app U s))
          (𝟙 (Over.mk (𝟙 (Spec ↧ℂ)))) :=
        Point.evaluate_res h _ _ trivial
    _ = (Scheme.ΓSpecIso ↧ℂ).hom
          ((Over.Hom.left (𝟙 (Over.mk (𝟙 (Spec ↧ℂ))))).appTop
            ((Spec ↧ℂ).presheaf.map (homOfLE h).op (z.left.app U s))) :=
        evaluate_top_eq_appTop _ _
    _ = (Scheme.ΓSpecIso ↧ℂ).hom (z.left.appLE U ⊤ h s) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Evaluation of an inverse-image regular function.**  The value of `g^* u` at a complex point
`z` is the value of `u` read through the composite scheme morphism `z.left ≫ g`. -/
theorem evaluate_app_eq_appLE_top {Y : Scheme} (g : X.left ⟶ Y) (W : Y.Opens) (u : Γ(Y, W))
    (z : ComplexPoint X) (h : (⊤ : (Spec ↧ℂ).Opens) ≤ (z.left ≫ g) ⁻¹ᵁ W) :
    Point.evaluate (g ⁻¹ᵁ W) (g.app W u) z =
      (Scheme.ΓSpecIso ↧ℂ).hom ((z.left ≫ g).appLE W ⊤ h u) := by
  have h' : (⊤ : (Spec ↧ℂ).Opens) ≤ z.left ⁻¹ᵁ (g ⁻¹ᵁ W) := h
  rw [evaluate_eq_appLE_top (g ⁻¹ᵁ W) (g.app W u) z h', Scheme.Hom.comp_appLE]
  rfl

end AlgebraicGeometry.ComplexPoint
