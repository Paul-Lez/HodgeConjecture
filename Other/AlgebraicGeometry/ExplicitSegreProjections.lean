/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitSegreMorphism

/-!
# Recovering the projective factors from Segre coordinates

On a matrix-coordinate chart, its distinguished row and column recover the two projective
factors. These are actual morphism identities, used to prove that the Segre morphism is monic.
-/

@[expose] public noncomputable section

open MvPolynomial HomogeneousLocalization CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveRatioSections

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (R : Type u) [CommRing R] {σ : Type u} [DecidableEq σ] [Fintype σ]
  {Y : Scheme.{u}} (f : Y ⟶ Proj (homogeneousSubmodule σ R))

attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The coefficient map induced by an actual projective chart morphism. -/
def pullCoefficient (U : Y.Opens) (i : σ)
    (hi : U ≤ f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) (X i)) : R →+* Γ(Y, U) :=
  (f.appLE _ U hi).hom.comp
    ((Proj.awayToSection (homogeneousSubmodule σ R) (X i)).hom.comp
      (ProjectiveSpaceChart.coefficient R i))

/-- An actual morphism to projective space is recovered from its regular coordinate ratios. -/
theorem fromSections_pullRatio (U : Y.Opens) (i : σ)
    (hi : U ≤ f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) (X i)) :
    ProjectiveCoordinates.fromSections U (pullCoefficient R f U i hi)
      (pullRatio R f U i hi) i (by simp) = U.ι ≫ f := by
  have h : ProjectiveCoordinates.evaluate (pullCoefficient R f U i hi)
      (pullRatio R f U i hi) (X i) (by simp) =
      ((Proj.awayToSection (homogeneousSubmodule σ R) (X i)) ≫ f.appLE _ U hi).hom := by
    apply ProjectiveSpaceChart.ringHom_ext
    · intro r
      rw [ProjectiveCoordinates.evaluate_coefficient _ _ i (by simp) r]
      rfl
    · intro a
      rw [ProjectiveCoordinates.evaluate_ratio _ _ i a (by simp) 1 (by simp), mul_one]
      rfl
  rw [ProjectiveCoordinates.fromSections, ProjectiveCoordinates.toProjective, h,
    show CommRingCat.ofHom
      ((Proj.awayToSection (homogeneousSubmodule σ R) (X i)) ≫ f.appLE _ U hi).hom =
        Proj.awayToSection (homogeneousSubmodule σ R) (X i) ≫ f.appLE _ U hi from rfl,
    Spec.map_comp]
  simp only [Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
  change f.resLE _ U hi ≫ (Proj.basicOpenToSpec (homogeneousSubmodule σ R) (X i) ≫
    Proj.awayι (homogeneousSubmodule σ R) (X i) (isHomogeneous_X R i) zero_lt_one) = _
  rw [← Proj.basicOpenIsoSpec_hom (homogeneousSubmodule σ R) (X i)
    (isHomogeneous_X R i) zero_lt_one, Proj.awayι, Iso.hom_inv_id_assoc,
    Scheme.Hom.resLE_comp_ι]

end AlgebraicGeometry.ProjectiveRatioSections

namespace AlgebraicGeometry.SegreMorphism

universe u
variable (R : Type u) [CommRing R] {σ τ : Type u}
  [DecidableEq σ] [DecidableEq τ] [Fintype σ] [Fintype τ]

attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The first factor recovered from the distinguished column of a matrix-coordinate chart. -/
def firstProjection (p : σ × τ) :
    (Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X p)).toScheme ⟶
      Proj (homogeneousSubmodule σ R) :=
  (Proj.basicOpenIsoSpec (homogeneousSubmodule (σ × τ) R) (X p)
    (isHomogeneous_X R p) zero_lt_one).hom ≫
    ProjectiveCoordinates.toProjective (ProjectiveSpaceChart.coefficient R p)
      (fun a ↦ ProjectiveSpaceChart.ratio R p (a, p.2)) p.1 (by simp)

/-- The second factor recovered from the distinguished row of a matrix-coordinate chart. -/
def secondProjection (p : σ × τ) :
    (Proj.basicOpen (homogeneousSubmodule (σ × τ) R) (X p)).toScheme ⟶
      Proj (homogeneousSubmodule τ R) :=
  (Proj.basicOpenIsoSpec (homogeneousSubmodule (σ × τ) R) (X p)
    (isHomogeneous_X R p) zero_lt_one).hom ≫
    ProjectiveCoordinates.toProjective (ProjectiveSpaceChart.coefficient R p)
      (fun b ↦ ProjectiveSpaceChart.ratio R p (p.1, b)) p.2 (by simp)

variable {Y : Scheme.{u}} (c : R →+* Γ(Y, ⊤))
  (f : Y ⟶ Proj (homogeneousSubmodule σ R))
  (g : Y ⟶ Proj (homogeneousSubmodule τ R))

omit [DecidableEq τ] [Fintype τ] in
/-- The selected matrix column of the local Segre morphism recovers the first projective map. -/
@[reassoc] theorem localToChart_firstProjection (p : σ × τ)
    (hc : scalar R c f g p = ProjectiveRatioSections.pullCoefficient R f
      (chart R f g p) p.1 inf_le_left) :
    localToChart R c f g p ≫ firstProjection R p = (chart R f g p).ι ≫ f := by
  let E := ProjectiveCoordinates.evaluate (scalar R c f g p) (coordinate R f g p)
    (X p) (by simp)
  have hec : E.comp (ProjectiveSpaceChart.coefficient R p) = scalar R c f g p := by
    apply RingHom.ext
    intro r
    exact ProjectiveCoordinates.evaluate_coefficient _ _ p (by simp) r
  have hev : E ∘ (fun a ↦ ProjectiveSpaceChart.ratio R p (a, p.2)) =
      ProjectiveRatioSections.pullRatio R f (chart R f g p) p.1 inf_le_left := by
    funext a
    change E (ProjectiveSpaceChart.ratio R p (a, p.2)) = _
    rw [ProjectiveCoordinates.evaluate_ratio _ _ p (a, p.2) (by simp) 1 (by simp), mul_one]
    simp [coordinate]
  simp only [localToChart, firstProjection, Category.assoc, Iso.inv_hom_id_assoc]
  rw [ProjectiveCoordinates.SpecMap_toProjective]
  change (chart R f g p).toSpecΓ ≫ ProjectiveCoordinates.toProjective
    (E.comp (ProjectiveSpaceChart.coefficient R p))
    (E ∘ (fun a ↦ ProjectiveSpaceChart.ratio R p (a, p.2))) p.1 _ = _
  have hmap : ProjectiveCoordinates.toProjective
      (E.comp (ProjectiveSpaceChart.coefficient R p))
      (E ∘ (fun a ↦ ProjectiveSpaceChart.ratio R p (a, p.2))) p.1 (by rw [hev]; simp) =
      ProjectiveCoordinates.toProjective
        (ProjectiveRatioSections.pullCoefficient R f (chart R f g p) p.1 inf_le_left)
        (ProjectiveRatioSections.pullRatio R f (chart R f g p) p.1 inf_le_left) p.1
        (by simp) := by
    congr! 1
    exact hec.trans hc
  rw [hmap]
  exact ProjectiveRatioSections.fromSections_pullRatio R f _ p.1 inf_le_left

omit [DecidableEq σ] [Fintype σ] in
/-- The selected matrix row of the local Segre morphism recovers the second projective map. -/
@[reassoc] theorem localToChart_secondProjection (p : σ × τ)
    (hc : scalar R c f g p = ProjectiveRatioSections.pullCoefficient R g
      (chart R f g p) p.2 inf_le_right) :
    localToChart R c f g p ≫ secondProjection R p = (chart R f g p).ι ≫ g := by
  let E := ProjectiveCoordinates.evaluate (scalar R c f g p) (coordinate R f g p)
    (X p) (by simp)
  have hec : E.comp (ProjectiveSpaceChart.coefficient R p) = scalar R c f g p := by
    apply RingHom.ext
    intro r
    exact ProjectiveCoordinates.evaluate_coefficient _ _ p (by simp) r
  have hev : E ∘ (fun b ↦ ProjectiveSpaceChart.ratio R p (p.1, b)) =
      ProjectiveRatioSections.pullRatio R g (chart R f g p) p.2 inf_le_right := by
    funext b
    change E (ProjectiveSpaceChart.ratio R p (p.1, b)) = _
    rw [ProjectiveCoordinates.evaluate_ratio _ _ p (p.1, b) (by simp) 1 (by simp), mul_one]
    simp [coordinate]
  simp only [localToChart, secondProjection, Category.assoc, Iso.inv_hom_id_assoc]
  rw [ProjectiveCoordinates.SpecMap_toProjective]
  change (chart R f g p).toSpecΓ ≫ ProjectiveCoordinates.toProjective
    (E.comp (ProjectiveSpaceChart.coefficient R p))
    (E ∘ (fun b ↦ ProjectiveSpaceChart.ratio R p (p.1, b))) p.2 _ = _
  have hmap : ProjectiveCoordinates.toProjective
      (E.comp (ProjectiveSpaceChart.coefficient R p))
      (E ∘ (fun b ↦ ProjectiveSpaceChart.ratio R p (p.1, b))) p.2 (by rw [hev]; simp) =
      ProjectiveCoordinates.toProjective
        (ProjectiveRatioSections.pullCoefficient R g (chart R f g p) p.2 inf_le_right)
        (ProjectiveRatioSections.pullRatio R g (chart R f g p) p.2 inf_le_right) p.2
        (by simp) := by
    congr! 1
    exact hec.trans hc
  rw [hmap]
  exact ProjectiveRatioSections.fromSections_pullRatio R g _ p.2 inf_le_right

end AlgebraicGeometry.SegreMorphism
