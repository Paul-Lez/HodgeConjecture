/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.Modules.QuasicoherentSections
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.RelativeSerreMorphism

/-!
# Multiplication by a power of a coordinate along a morphism to projective space

For a cocycle `d` on an open cover `U` of a scheme `X` and a global section `h = (hᵢ)` of the
line bundle `L_d` (`hᵢ = dᵢⱼ hⱼ`), multiplication by `h` is a morphism `F ⟶ F ⊗ L_d`
(`AlgebraicGeometry.Scheme.Modules.mulSection`). If `h_l = 1`, it is bijective on sections over
every open contained in `U_l` (`AlgebraicGeometry.Scheme.Modules.mulSection_app_bijective`).

For a morphism `j : Y' ⟶ ℙₒ(n; K)` and `m : ℕ`, the pullbacks along `j` of the sections
`(Xₗ / Xᵢ)ᵐ` form such a global section of the pullback of `O(m)`, giving multiplication by
`Xₗᵐ`, `G ⟶ G(m) = G ⊗ j^* O(m)` (`AlgebraicGeometry.ProjectiveSpace.mulXPowAlong`). It is
bijective on sections over opens contained in `j⁻¹ D₊(Xₗ)`
(`AlgebraicGeometry.ProjectiveSpace.mulXPowAlong_app_bijective`).
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- An isomorphism of sheaves of modules is bijective on sections. -/
lemma bijective_app_of_iso {M N : X.Modules} (e : M ≅ N) (V : X.Opens) :
    Function.Bijective (e.hom.app V) := by
  refine Function.bijective_iff_has_inverse.2 ⟨e.inv.app V, fun s ↦ ?_, fun s ↦ ?_⟩
  · rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.hom_inv_id, Hom.id_app]
    rfl
  · rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.inv_hom_id, Hom.id_app]
    rfl

variable {ι : Type} {U : ι → X.Opens} (F : X.Modules) (c d : Cocycle U) (h : ∀ i, Γ(X, U i))
  (hh : ∀ i j, (h i |ₒ (U i ⊓ U j)) = d.g i j * (h j |ₒ (U i ⊓ U j)))

/-- If `h_l = 1`, multiplication by `h` is bijective on sections over opens contained in
`U_l`. -/
lemma twistMulSection_app_bijective {l : ι} (hl : h l = 1) {V : X.Opens} (hV : V ≤ U l) :
    Function.Bijective ((twistMulSection F c d h hh).app V) := by
  have key : ∀ s, twistSectionsEquiv (c * d) l hV ((twistMulSection F c d h hh).app V s) =
      twistSectionsEquiv c l hV s := fun s ↦ by
    rw [twistSectionsEquiv_apply, twistSectionsEquiv_apply, twistComp_twistMulSection_app, hl,
      ores_one, one_smul]
  have e : ⇑((twistMulSection F c d h hh).app V) =
      (twistSectionsEquiv (c * d) l hV).symm ∘ twistSectionsEquiv c l hV := by
    funext s
    apply (twistSectionsEquiv (c * d) l hV).injective
    rw [Function.comp_apply, LinearEquiv.apply_symm_apply, key]
  rw [e]
  exact (LinearEquiv.bijective _).comp (LinearEquiv.bijective _)

/-- **Multiplication by a global section** `h = (hᵢ)` of `L_d`, `F ⟶ F ⊗ L_d`,
`t ↦ (hᵢ t)ᵢ`. -/
noncomputable def mulSection : F ⟶ twist F d :=
  toTwistOne F ≫ twistMulSection F 1 d h hh ≫ ((twistFunctorCongr (one_mul d)).app F).hom

/-- If the `Uᵢ` cover `X` and `h_l = 1`, multiplication by `h` is bijective on sections over
opens contained in `U_l`. -/
lemma mulSection_app_bijective (hU : ⨆ i, U i = ⊤) {l : ι} (hl : h l = 1) {V : X.Opens}
    (hV : V ≤ U l) : Function.Bijective ((mulSection F d h hh).app V) := by
  have e : ⇑((mulSection F d h hh).app V) = ⇑(((twistFunctorCongr (one_mul d)).app F).hom.app V) ∘
      ⇑((twistMulSection F 1 d h hh).app V) ∘ ⇑((toTwistOne F).app V) := rfl
  rw [e]
  exact (bijective_app_of_iso _ V).comp
    ((twistMulSection_app_bijective F 1 d h hh hl hV).comp (toTwistOne_bijective hU V))

variable {Y : Scheme.{u}} (φ : Y ⟶ X)

include hh in
/-- The pullback along `φ` of a global section of `L_d` is a global section of `L_{φ^♯ d}`. -/
lemma comap_mulSection_compat (i j : ι) :
    (φ.app (U i) (h i) |ₒ (φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j)) =
      (d.comap φ).g i j * (φ.app (U j) (h j) |ₒ (φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j)) := by
  have e₁ : φ.app (U i ⊓ U j) (h i |ₒ (U i ⊓ U j)) =
      (φ.app (U i) (h i) |ₒ (φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j)) := app_ores φ inf_le_left (h i)
  have e₂ : φ.app (U i ⊓ U j) (h j |ₒ (U i ⊓ U j)) =
      (φ.app (U j) (h j) |ₒ (φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j)) := app_ores φ inf_le_right (h j)
  have e₃ : φ.app (U i ⊓ U j) (d.g i j) = (d.comap φ).g i j := by
    rw [Cocycle.comap_g, Scheme.Hom.app_eq_appLE]
    rfl
  rw [← e₁, ← e₂, ← e₃, hh i j, map_mul]
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules

variable {n : ℕ} {K : Type u} [CommRing K] {Y' : Scheme.{u}} (j : Y' ⟶ ℙₒ(n; K))

/-- The preimages of the standard charts cover `Y'`. -/
lemma iSup_preimage_U : ⨆ i, j ⁻¹ᵁ U n K i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, iSup_U, Scheme.Hom.preimage_top]

/-- `(Xₗ / Xᵢ)ᵐ` on `Uᵢ = D₊(Xᵢ)`: a global section of `O(m)`. -/
lemma xDiv_pow_compat (m : ℕ) (l i i' : Fin (n + 1)) :
    ((xDiv i l ^ m) |ₒ (U n K i ⊓ U n K i')) =
      (cocycle n K ^ (m : ℤ)).g i i' * ((xDiv i' l ^ m) |ₒ (U n K i ⊓ U n K i')) := by
  rw [ores_pow, ores_pow, zpow_natCast, Cocycle.pow_g, ← mul_pow, ← xDiv_compat]

/-- **Multiplication by `Xₗᵐ` along `j`**, `G ⟶ G(m) = G ⊗ j^* O(m)`: on `j⁻¹ D₊(Xᵢ)` it is
multiplication by the pullback of `(Xₗ / Xᵢ)ᵐ`. -/
noncomputable def mulXPowAlong (G : Y'.Modules) (m : ℕ) (l : Fin (n + 1)) :
    G ⟶ twistAlong j G m :=
  mulSection G ((cocycle n K ^ (m : ℤ)).comap j) (fun i ↦ j.app (U n K i) (xDiv i l ^ m))
    (comap_mulSection_compat (cocycle n K ^ (m : ℤ)) (fun i ↦ xDiv i l ^ m)
      (xDiv_pow_compat m l) j)

/-- Multiplication by `Xₗᵐ` along `j` is bijective on sections over opens contained in
`j⁻¹ D₊(Xₗ)`. -/
lemma mulXPowAlong_app_bijective (G : Y'.Modules) (m : ℕ) (l : Fin (n + 1)) {V : Y'.Opens}
    (hV : V ≤ j ⁻¹ᵁ U n K l) : Function.Bijective ((mulXPowAlong j G m l).app V) :=
  mulSection_app_bijective G _ _ _ (iSup_preimage_U j)
    (by simp only [xDiv_self, one_pow, map_one]) hV

end AlgebraicGeometry.ProjectiveSpace

end
