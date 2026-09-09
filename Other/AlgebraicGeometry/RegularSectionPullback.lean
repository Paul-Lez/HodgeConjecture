/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RegularHolomorphicForms

/-!
# Complex-algebraic pullback of regular sections

A morphism over the complex base pulls back regular sections as an algebra
homomorphism for the scalar structures used by analytification.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] regularSectionAlgebra

variable {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y)

/-- Pullback of regular functions, retaining the actual complex structure maps. -/
def regularSectionPullback (U : Y.left.Opens) (V : X.left.Opens)
    (h : V ≤ f.left ⁻¹ᵁ U) : Γ(Y.left, U) →ₐ[ℂ] Γ(X.left, V) where
  toRingHom := (f.left.appLE U V h).hom
  commutes' c := by
    change (((Scheme.ΓSpecIso ↧ℂ).inv ≫ Y.hom.appTop ≫
      Y.left.presheaf.map (homOfLE le_top).op) ≫ f.left.appLE U V h) c =
      ((Scheme.ΓSpecIso ↧ℂ).inv ≫ X.hom.appTop ≫
        X.left.presheaf.map (homOfLE le_top).op) c
    have hf : f.left.appLE ⊤ V (by simp) =
        f.left.appTop ≫ X.left.presheaf.map (homOfLE le_top).op := by
      simp [Scheme.Hom.appTop, Scheme.Hom.appLE]
    simp only [Category.assoc, Scheme.Hom.map_appLE]
    rw [hf, ← Category.assoc Y.hom.appTop, ← Scheme.Hom.comp_appTop, Over.w]

/-- Pullback commutes with restriction on the source scheme. -/
theorem regularSectionPullback_restrict (U : Y.left.Opens) {V W : X.left.Opens}
    (h : V ≤ f.left ⁻¹ᵁ U) (hWV : W ≤ V) :
    (regularSectionRestriction X hWV).comp (regularSectionPullback f U V h) =
      regularSectionPullback f U W (hWV.trans h) := by
  ext s
  change (f.left.appLE U V h ≫ X.left.presheaf.map (homOfLE hWV).op) s = _
  rw [Scheme.Hom.appLE_map]
  rfl

/-- Pulling back a restricted section agrees with pulling back the original section. -/
theorem regularSectionPullback_restrict_domain {U V : Y.left.Opens} (hVU : V ≤ U)
    (W : X.left.Opens) (h : W ≤ f.left ⁻¹ᵁ V) :
    (regularSectionPullback f V W h).comp (regularSectionRestriction Y hVU) =
      regularSectionPullback f U W
        (h.trans ((Opens.map f.left.base).map (homOfLE hVU)).le) := by
  ext s
  change (Y.left.presheaf.map (homOfLE hVU).op ≫ f.left.appLE V W h) s = _
  rw [Scheme.Hom.map_appLE]
  rfl

end AlgebraicGeometry.ComplexPoint
