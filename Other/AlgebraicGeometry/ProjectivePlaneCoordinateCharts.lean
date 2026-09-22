/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Other.AlgebraicGeometry.ProjectivePlaneHyperplane
public import Other.AlgebraicGeometry.ProjectiveChartIso
public import Other.AlgebraicTopology.WindingRelativeUnitBoundary
public import Other.AlgebraicTopology.TwoOpenCechCochain
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexAffineSpace
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexOpen

/-!
# The two affine coordinates used by the coordinate hyperplane of `ℙ²`

This file ties the concrete chart calculation to the actual scheme
`Proj (ℂ[X₀,X₁,X₂])`.  On `D₊(Xᵢ)`, the element
`X_{i.succAbove j}/Xᵢ` of the homogeneous localization gives a literal regular
function, hence a continuous complex-valued function on analytic points.

For the coordinate hyperplane `X₀ = 0`, the charts `D₊(X₁)` and `D₊(X₂)` both
use the `j = 0` ratio as their normal coordinate.
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial AlgebraicGeometry AlgebraicTopology.Singular
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectivePlane.CoordinateCharts

open AlgebraicGeometry.ComplexPoint

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Evaluation of a section on an open subscheme agrees with evaluation of the corresponding
section on the ambient open. -/
lemma evaluate_topIso_inv {X : Over (Spec ↧ℂ)} (U : X.left.Opens) (s : Γ(X.left, U))
    (z : ComplexPoint (openScheme X U)) :
    Point.evaluate ⊤ (U.topIso.inv s) z =
      Point.evaluate U s (Point.map (openInclusion X U) z) := by
  calc
    Point.evaluate ⊤ (U.topIso.inv s) z =
        Point.evaluate (U.ι ''ᵁ (⊤ : U.toScheme.Opens))
          ((U.ι.appIso ⊤).inv (U.topIso.inv s))
          (Point.map (openInclusion X U) z) :=
      (evaluate_openEquiv X U (U.topIso.inv s) z).symm
    _ = Point.evaluate U s (Point.map (openInclusion X U) z) := by
      rw [evaluate_eq (Y := X) U.ι_image_top]
      congr 2
      change (X.left.presheaf.map (eqToHom U.ι_image_top.symm).op).hom
          ((U.ι.appIso ⊤).inv (U.topIso.inv s)) = s
      have hmap : X.left.presheaf.map (eqToHom U.ι_image_top.symm).op = U.topIso.hom := rfl
      rw [hmap]
      simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
      exact ConcreteCategory.congr_hom U.topIso.inv_hom_id s

/-- The standard affine open `D₊(Xᵢ)` of the concrete projective plane. -/
def chartOpen (i : Fin 3) : plane.Opens :=
  Proj.basicOpen Grading (MvPolynomial.X i)

/-- The zeroth standard chart is the actual principal-open complement of the displayed
scheme-theoretic zero locus `{X₀ = 0}`. -/
lemma chartOpen_zero_eq_hyperplaneComplementOpen :
    chartOpen 0 = hyperplaneComplementOpen := rfl

/-- The `j`-th ratio coordinate on the affine scheme `D₊(Xᵢ)`. -/
def chartCoordinate (i : Fin 3) (j : Fin 2) :
    Γ((chartOpen i).toScheme, ⊤) :=
  (chartOpen i).topIso.inv
    ((Proj.basicOpenIsoAway Grading (MvPolynomial.X i)
      (Other.ProjectiveChart.X_mem_one ℂ i) Nat.one_pos).hom
      (Other.ProjectiveChart.gen ℂ i j))

/-- The direct `Proj` model, regarded over `Spec ℂ`; this transparent abbreviation keeps the
chart-level evaluation lemmas definitionally aligned with `plane`. -/
abbrev analyticPlane : Over (Spec ↧ℂ) :=
  Over.mk structureMap

/-- The analytic open subscheme associated to `D₊(Xᵢ)`. -/
abbrev analyticChart (i : Fin 3) : Over (Spec ↧ℂ) :=
  openScheme analyticPlane (chartOpen i)

/-- Evaluation of the literal ratio coordinate on analytic points of its chart. -/
def chartCoordinateValue (i : Fin 3) (j : Fin 2) :
    ComplexPoint (analyticChart i) → ℂ :=
  Point.evaluate ⊤ (chartCoordinate i j)

/-- Each ratio coordinate is continuous in the analytic topology. -/
lemma continuous_chartCoordinateValue (i : Fin 3) (j : Fin 2) :
    Continuous (chartCoordinateValue i j) :=
  continuous_evaluate_top (X := analyticChart i) (chartCoordinate i j)

/-- The normal coordinate `X₀/X₁` on the chart `D₊(X₁)`. -/
abbrev firstNormalCoordinate :
    ComplexPoint (analyticChart 1) → ℂ :=
  chartCoordinateValue 1 0

/-- The normal coordinate `X₀/X₂` on the chart `D₊(X₂)`. -/
abbrev secondNormalCoordinate :
    ComplexPoint (analyticChart 2) → ℂ :=
  chartCoordinateValue 2 0

lemma continuous_firstNormalCoordinate : Continuous firstNormalCoordinate :=
  continuous_chartCoordinateValue 1 0

lemma continuous_secondNormalCoordinate : Continuous secondNormalCoordinate :=
  continuous_chartCoordinateValue 2 0

/-- The intersection `D₊(X₁) ∩ D₊(X₂)`, written as the principal open
`D₊(X₁ X₂)`. -/
def overlapOpen : plane.Opens :=
  Proj.basicOpen Grading (MvPolynomial.X 1 * MvPolynomial.X 2)

lemma overlapOpen_le_firstChart : overlapOpen ≤ chartOpen 1 := by
  exact Proj.basicOpen_mono Grading (MvPolynomial.X 1) (MvPolynomial.X 1 * MvPolynomial.X 2)
    ⟨MvPolynomial.X 2, rfl⟩

lemma overlapOpen_le_secondChart : overlapOpen ≤ chartOpen 2 := by
  exact Proj.basicOpen_mono Grading (MvPolynomial.X 2) (MvPolynomial.X 1 * MvPolynomial.X 2)
    ⟨MvPolynomial.X 1, mul_comm _ _⟩

/-- The analytic overlap, as the actual open subscheme of the projective plane. -/
abbrev analyticOverlap : Over (Spec ↧ℂ) :=
  openScheme analyticPlane overlapOpen

lemma coordinateOne_homogeneous :
    (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ) ∈ Grading 1 :=
  Other.ProjectiveChart.X_mem_one ℂ 1

lemma coordinateTwo_homogeneous :
    (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ) ∈ Grading 1 :=
  Other.ProjectiveChart.X_mem_one ℂ 2

lemma overlapEquation_homogeneous :
    (MvPolynomial.X 1 * MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ) ∈ Grading 2 := by
  simpa using SetLike.mul_mem_graded coordinateOne_homogeneous coordinateTwo_homogeneous

lemma coordinateOneSquare_homogeneous :
    (MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 3) ℂ) ∈ Grading 2 := by
  simpa [pow_two] using SetLike.mul_mem_graded coordinateOne_homogeneous
    coordinateOne_homogeneous

lemma coordinateTwoSquare_homogeneous :
    (MvPolynomial.X 2 ^ 2 : MvPolynomial (Fin 3) ℂ) ∈ Grading 2 := by
  simpa [pow_two] using SetLike.mul_mem_graded coordinateTwo_homogeneous
    coordinateTwo_homogeneous

/-- The regular unit `X₁/X₂` on `D₊(X₁X₂)`, written directly as
`X₁² / (X₁ X₂)` in the homogeneous localization. -/
def overlapUnitElement :
    HomogeneousLocalization.Away Grading (MvPolynomial.X 1 * MvPolynomial.X 2) :=
  HomogeneousLocalization.Away.mk Grading overlapEquation_homogeneous 1
    (MvPolynomial.X 1 ^ 2) coordinateOneSquare_homogeneous

/-- The inverse regular unit `X₂/X₁` on the same overlap. -/
def overlapUnitInverseElement :
    HomogeneousLocalization.Away Grading (MvPolynomial.X 1 * MvPolynomial.X 2) :=
  HomogeneousLocalization.Away.mk Grading overlapEquation_homogeneous 1
    (MvPolynomial.X 2 ^ 2) coordinateTwoSquare_homogeneous

/-- The two displayed homogeneous fractions multiply to one. -/
lemma overlapUnitElement_mul_inverse :
    overlapUnitElement * overlapUnitInverseElement = 1 := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X 1 * MvPolynomial.X 2))
  dsimp [overlapUnitElement, overlapUnitInverseElement]
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  use 1
  simp
  ring

/-- The restriction of `X₀ / X₁` to `D₊(X₁ X₂)`, computed directly in the
homogeneous localization. -/
def overlapFirstNormalElement :
    HomogeneousLocalization.Away Grading (MvPolynomial.X 1 * MvPolynomial.X 2) :=
  HomogeneousLocalization.awayMap Grading coordinateTwo_homogeneous rfl
    (Other.ProjectiveChart.gen ℂ 1 0)

/-- The restriction of `X₀ / X₂` to the same overlap. -/
def overlapSecondNormalElement :
    HomogeneousLocalization.Away Grading (MvPolynomial.X 1 * MvPolynomial.X 2) :=
  HomogeneousLocalization.awayMap Grading coordinateOne_homogeneous (by rw [mul_comm])
    (Other.ProjectiveChart.gen ℂ 2 0)

/-- The literal homogeneous-localization calculation
`X₀/X₂ = (X₀/X₁) * (X₁/X₂)`. -/
lemma overlapSecondNormalElement_eq_first_mul_unit :
    overlapSecondNormalElement = overlapFirstNormalElement * overlapUnitElement := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X 1 * MvPolynomial.X 2))
  dsimp [overlapFirstNormalElement, overlapSecondNormalElement, overlapUnitElement,
    Other.ProjectiveChart.gen]
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp
  ring

/-- Send an element of the overlap homogeneous localization to its corresponding regular
section on the displayed principal open. -/
def overlapGlobalSection
    (x : HomogeneousLocalization.Away Grading (MvPolynomial.X 1 * MvPolynomial.X 2)) :
    Γ(plane, overlapOpen) := by
  change Γ(Proj Grading, Proj.basicOpen Grading (MvPolynomial.X 1 * MvPolynomial.X 2))
  exact (Proj.basicOpenIsoAway Grading (MvPolynomial.X 1 * MvPolynomial.X 2)
    overlapEquation_homogeneous (by norm_num)).hom x

lemma overlapGlobalSection_mul
    (x y : HomogeneousLocalization.Away Grading (MvPolynomial.X 1 * MvPolynomial.X 2)) :
    overlapGlobalSection (x * y) = overlapGlobalSection x * overlapGlobalSection y := by
  change (Proj.basicOpenIsoAway Grading (MvPolynomial.X 1 * MvPolynomial.X 2)
      overlapEquation_homogeneous (by norm_num)).hom (x * y) = _
  exact map_mul _ _ _

/-- The first normal coordinate as a section on the actual overlap scheme. -/
def overlapFirstNormalGlobalSection : Γ(plane, overlapOpen) :=
  overlapGlobalSection overlapFirstNormalElement

/-- The second normal coordinate as a section on the actual overlap scheme. -/
def overlapSecondNormalGlobalSection : Γ(plane, overlapOpen) :=
  overlapGlobalSection overlapSecondNormalElement

/-- The section `X₀/X₁` on the first standard principal open. -/
def firstNormalGlobalSection : Γ(plane, chartOpen 1) :=
  (Proj.basicOpenIsoAway Grading (MvPolynomial.X 1)
    coordinateOne_homogeneous (by norm_num)).hom (Other.ProjectiveChart.gen ℂ 1 0)

/-- The section `X₀/X₂` on the second standard principal open. -/
def secondNormalGlobalSection : Γ(plane, chartOpen 2) :=
  (Proj.basicOpenIsoAway Grading (MvPolynomial.X 2)
    coordinateTwo_homogeneous (by norm_num)).hom (Other.ProjectiveChart.gen ℂ 2 0)

/-- The direct `Proj` section `X₀/X₁`, now regarded as a global function on the first affine
chart scheme. -/
def firstNormalSection : Γ((chartOpen 1).toScheme, ⊤) :=
  (chartOpen 1).topIso.inv firstNormalGlobalSection

/-- On `D₊(X₁)`, the nonvanishing locus of the literal function `X₀ / X₁` is
exactly the pullback of the principal-open complement `D₊(X₀)` of the displayed
scheme-theoretic hyperplane.

This is an equality of scheme opens, proved through the standard `Proj` affine-chart
isomorphism; it is not an assumed identification of zero loci. -/
lemma firstNormalSection_basicOpen_eq_preimage_hyperplaneComplementOpen :
    (chartOpen 1).toScheme.basicOpen firstNormalSection =
      (chartOpen 1).ι ⁻¹ᵁ hyperplaneComplementOpen := by
  let e := Proj.basicOpenIsoSpec Grading (MvPolynomial.X 1)
    coordinateOne_homogeneous (by norm_num)
  let a : HomogeneousLocalization.Away Grading (MvPolynomial.X 1) :=
    Other.ProjectiveChart.gen ℂ 1 0
  have hsection :
      (e.hom.app ⊤) ((Scheme.ΓSpecIso _).inv a) = firstNormalSection := by
    dsimp only [e, a]
    rw [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec_app_top]
    change ((Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection Grading (MvPolynomial.X 1) ≫
      (chartOpen 1).topIso.inv).hom
        ((Scheme.ΓSpecIso _).inv (Other.ProjectiveChart.gen ℂ 1 0)) = _
    simp only [← ConcreteCategory.comp_apply, Iso.inv_hom_id_assoc]
    rfl
  have hgen :
      HomogeneousLocalization.Away.isLocalizationElem coordinateOne_homogeneous
        coordinateZero_homogeneous = a := by
    dsimp only [a]
    rw [HomogeneousLocalization.ext_iff_val]
    simp [coordinateZero, HomogeneousLocalization.Away.isLocalizationElem,
      Other.ProjectiveChart.gen]
  have hnormal :
      e.hom ⁻¹ᵁ (Spec (CommRingCat.of (HomogeneousLocalization.Away Grading
        (MvPolynomial.X 1)))).basicOpen ((Scheme.ΓSpecIso _).inv a) =
        (chartOpen 1).toScheme.basicOpen firstNormalSection := by
    rw [Scheme.preimage_basicOpen, hsection]
    rfl
  rw [← hnormal, basicOpen_eq_of_affine, ← hgen,
    ← Proj.awayι_preimage_basicOpen (𝒜 := Grading) coordinateOne_homogeneous (by norm_num)
      coordinateZero_homogeneous (by norm_num)]
  change e.hom ⁻¹ᵁ (Proj.awayι Grading (MvPolynomial.X 1)
    coordinateOne_homogeneous (by norm_num) ⁻¹ᵁ Proj.basicOpen Grading coordinateZero) = _
  rw [← Scheme.Hom.comp_preimage]
  change (e.hom ≫ Proj.awayι Grading (MvPolynomial.X 1)
    coordinateOne_homogeneous (by norm_num)) ⁻¹ᵁ hyperplaneComplementOpen = _
  simp only [chartOpen, e, Proj.awayι, Iso.hom_inv_id_assoc]
  rfl

/-- The literal regular function `X₀ / X₂` on the second standard affine chart. -/
def secondNormalSection : Γ((chartOpen 2).toScheme, ⊤) :=
  (chartOpen 2).topIso.inv secondNormalGlobalSection

/-- The chart-coordinate presentation and the direct-section presentation of `X₀ / X₂`
have the same value at every analytic point. -/
lemma secondNormalCoordinate_eq_evaluate_secondNormalSection
    (z : ComplexPoint (analyticChart 2)) :
    secondNormalCoordinate z = Point.evaluate ⊤ secondNormalSection z := by
  rfl

/-- On `D₊(X₂)`, the nonvanishing locus of `X₀ / X₂` is exactly the pullback of
`D₊(X₀)`, the complement of the displayed scheme-theoretic hyperplane. -/
lemma secondNormalSection_basicOpen_eq_preimage_hyperplaneComplementOpen :
    (chartOpen 2).toScheme.basicOpen secondNormalSection =
      (chartOpen 2).ι ⁻¹ᵁ hyperplaneComplementOpen := by
  let e := Proj.basicOpenIsoSpec Grading (MvPolynomial.X 2)
    coordinateTwo_homogeneous (by norm_num)
  let a : HomogeneousLocalization.Away Grading (MvPolynomial.X 2) :=
    Other.ProjectiveChart.gen ℂ 2 0
  have hsection :
      (e.hom.app ⊤) ((Scheme.ΓSpecIso _).inv a) = secondNormalSection := by
    dsimp only [e, a]
    rw [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec_app_top]
    change ((Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection Grading (MvPolynomial.X 2) ≫
      (chartOpen 2).topIso.inv).hom
        ((Scheme.ΓSpecIso _).inv (Other.ProjectiveChart.gen ℂ 2 0)) = _
    simp only [← ConcreteCategory.comp_apply, Iso.inv_hom_id_assoc]
    rfl
  have hgen :
      HomogeneousLocalization.Away.isLocalizationElem coordinateTwo_homogeneous
        coordinateZero_homogeneous = a := by
    dsimp only [a]
    rw [HomogeneousLocalization.ext_iff_val]
    simp [coordinateZero, HomogeneousLocalization.Away.isLocalizationElem,
      Other.ProjectiveChart.gen]
  have hnormal :
      e.hom ⁻¹ᵁ (Spec (CommRingCat.of (HomogeneousLocalization.Away Grading
        (MvPolynomial.X 2)))).basicOpen ((Scheme.ΓSpecIso _).inv a) =
        (chartOpen 2).toScheme.basicOpen secondNormalSection := by
    rw [Scheme.preimage_basicOpen, hsection]
    rfl
  rw [← hnormal, basicOpen_eq_of_affine, ← hgen,
    ← Proj.awayι_preimage_basicOpen (𝒜 := Grading) coordinateTwo_homogeneous (by norm_num)
      coordinateZero_homogeneous (by norm_num)]
  change e.hom ⁻¹ᵁ (Proj.awayι Grading (MvPolynomial.X 2)
    coordinateTwo_homogeneous (by norm_num) ⁻¹ᵁ Proj.basicOpen Grading coordinateZero) = _
  rw [← Scheme.Hom.comp_preimage]
  change (e.hom ≫ Proj.awayι Grading (MvPolynomial.X 2)
    coordinateTwo_homogeneous (by norm_num)) ⁻¹ᵁ hyperplaneComplementOpen = _
  simp only [chartOpen, e, Proj.awayι, Iso.hom_inv_id_assoc]
  rfl

/-- The analytic function defined by the direct regular section `X₀/X₁` on `D₊(X₁)`. -/
def firstNormalValue : ComplexPoint (analyticChart 1) → ℂ :=
  Point.evaluate ⊤ firstNormalSection

lemma continuous_firstNormalValue : Continuous firstNormalValue :=
  continuous_evaluate_top (X := analyticChart 1) firstNormalSection

/-- At the level of regular-section morphisms, restriction from `D₊(X₁)` to
`D₊(X₁X₂)` is precisely the homogeneous-localization map which inverts `X₂`.

This is the actual scheme-theoretic restriction map; keeping it as a morphism equality avoids
unfolding the concrete section value prematurely. -/
lemma overlapFirstNormal_restriction_hom :
    CommRingCat.ofHom
        (HomogeneousLocalization.awayMap Grading coordinateTwo_homogeneous rfl) ≫
      Proj.awayToSection Grading (MvPolynomial.X 1 * MvPolynomial.X 2) =
        Proj.awayToSection Grading (MvPolynomial.X 1) ≫
          plane.presheaf.map (homOfLE overlapOpen_le_firstChart).op := by
  exact Proj.awayMap_awayToSection Grading coordinateTwo_homogeneous rfl

/-- Likewise, restriction from `D₊(X₂)` to `D₊(X₁X₂)` is the localization map which inverts
`X₁`. -/
lemma overlapSecondNormal_restriction_hom :
    CommRingCat.ofHom
        (HomogeneousLocalization.awayMap Grading coordinateOne_homogeneous (by rw [mul_comm])) ≫
      Proj.awayToSection Grading (MvPolynomial.X 1 * MvPolynomial.X 2) =
        Proj.awayToSection Grading (MvPolynomial.X 2) ≫
          plane.presheaf.map (homOfLE overlapOpen_le_secondChart).op := by
  exact Proj.awayMap_awayToSection Grading coordinateOne_homogeneous (by rw [mul_comm])

/-- Evaluating the first restriction morphism at `X₀/X₁` recovers the concrete overlap
section.  This is the elementwise chart-restriction statement used by the analytic cochains. -/
lemma overlapFirstNormalGlobalSection_eq_restrict :
    overlapFirstNormalGlobalSection =
      plane.presheaf.map (homOfLE overlapOpen_le_firstChart).op firstNormalGlobalSection := by
  change
    (CommRingCat.ofHom
        (HomogeneousLocalization.awayMap Grading coordinateTwo_homogeneous rfl) ≫
      Proj.awayToSection Grading (MvPolynomial.X 1 * MvPolynomial.X 2)).hom
        (Other.ProjectiveChart.gen ℂ 1 0) =
      (Proj.awayToSection Grading (MvPolynomial.X 1) ≫
        plane.presheaf.map (homOfLE overlapOpen_le_firstChart).op).hom
          (Other.ProjectiveChart.gen ℂ 1 0)
  rw [overlapFirstNormal_restriction_hom]
  rfl

/-- Evaluating the second restriction morphism at `X₀/X₂` recovers the concrete overlap
section. -/
lemma overlapSecondNormalGlobalSection_eq_restrict :
    overlapSecondNormalGlobalSection =
      plane.presheaf.map (homOfLE overlapOpen_le_secondChart).op secondNormalGlobalSection := by
  change
    (CommRingCat.ofHom
        (HomogeneousLocalization.awayMap Grading coordinateOne_homogeneous (by rw [mul_comm])) ≫
      Proj.awayToSection Grading (MvPolynomial.X 1 * MvPolynomial.X 2)).hom
        (Other.ProjectiveChart.gen ℂ 2 0) =
      (Proj.awayToSection Grading (MvPolynomial.X 2) ≫
        plane.presheaf.map (homOfLE overlapOpen_le_secondChart).op).hom
          (Other.ProjectiveChart.gen ℂ 2 0)
  rw [overlapSecondNormal_restriction_hom]
  rfl

lemma overlapSecondNormalGlobalSection_eq_first_mul_unit :
    overlapSecondNormalGlobalSection = overlapFirstNormalGlobalSection *
      overlapGlobalSection overlapUnitElement := by
  rw [overlapSecondNormalGlobalSection, overlapFirstNormalGlobalSection,
    overlapSecondNormalElement_eq_first_mul_unit, overlapGlobalSection_mul]

/-- `X₁/X₂` as a section on the displayed principal open of the projective plane. -/
def overlapUnitGlobalSection : Γ(plane, overlapOpen) := by
  change Γ(Proj Grading, Proj.basicOpen Grading (MvPolynomial.X 1 * MvPolynomial.X 2))
  exact (Proj.basicOpenIsoAway Grading (MvPolynomial.X 1 * MvPolynomial.X 2)
    overlapEquation_homogeneous (by norm_num)).hom overlapUnitElement

/-- `X₂/X₁` as the displayed inverse section on the same principal open. -/
def overlapUnitInverseGlobalSection : Γ(plane, overlapOpen) := by
  change Γ(Proj Grading, Proj.basicOpen Grading (MvPolynomial.X 1 * MvPolynomial.X 2))
  exact (Proj.basicOpenIsoAway Grading (MvPolynomial.X 1 * MvPolynomial.X 2)
    overlapEquation_homogeneous (by norm_num)).hom overlapUnitInverseElement

lemma overlapUnitGlobalSection_mul_inverse :
    overlapUnitGlobalSection * overlapUnitInverseGlobalSection = 1 := by
  change (Proj.basicOpenIsoAway Grading (MvPolynomial.X 1 * MvPolynomial.X 2)
      overlapEquation_homogeneous (by norm_num)).hom overlapUnitElement *
    (Proj.basicOpenIsoAway Grading (MvPolynomial.X 1 * MvPolynomial.X 2)
      overlapEquation_homogeneous (by norm_num)).hom overlapUnitInverseElement = 1
  rw [← map_mul, overlapUnitElement_mul_inverse, map_one]

/-- `X₁/X₂` as a literal global regular function on the overlap affine scheme. -/
def overlapUnitSection : Γ(overlapOpen.toScheme, ⊤) :=
  overlapOpen.topIso.inv overlapUnitGlobalSection

/-- `X₂/X₁` as the displayed inverse regular function on the overlap. -/
def overlapUnitInverseSection : Γ(overlapOpen.toScheme, ⊤) :=
  overlapOpen.topIso.inv overlapUnitInverseGlobalSection

/-- `X₀/X₁` as a regular function on the overlap affine scheme. -/
def overlapFirstNormalSection : Γ(overlapOpen.toScheme, ⊤) :=
  overlapOpen.topIso.inv overlapFirstNormalGlobalSection

/-- `X₀/X₂` as a regular function on the overlap affine scheme. -/
def overlapSecondNormalSection : Γ(overlapOpen.toScheme, ⊤) :=
  overlapOpen.topIso.inv overlapSecondNormalGlobalSection

lemma overlapUnitSection_mul_inverse :
    overlapUnitSection * overlapUnitInverseSection = 1 := by
  apply overlapOpen.topIso.commRingCatIsoToRingEquiv.injective
  change overlapOpen.topIso.hom (overlapUnitSection * overlapUnitInverseSection) =
    overlapOpen.topIso.hom 1
  rw [map_mul, map_one]
  change overlapOpen.topIso.hom (overlapOpen.topIso.inv overlapUnitGlobalSection) *
      overlapOpen.topIso.hom (overlapOpen.topIso.inv overlapUnitInverseGlobalSection) = 1
  have h₁ := ConcreteCategory.congr_hom overlapOpen.topIso.inv_hom_id
    overlapUnitGlobalSection
  have h₂ := ConcreteCategory.congr_hom overlapOpen.topIso.inv_hom_id
    overlapUnitInverseGlobalSection
  change overlapOpen.topIso.hom (overlapOpen.topIso.inv overlapUnitGlobalSection) =
    overlapUnitGlobalSection at h₁
  change overlapOpen.topIso.hom (overlapOpen.topIso.inv overlapUnitInverseGlobalSection) =
    overlapUnitInverseGlobalSection at h₂
  rw [h₁, h₂]
  exact overlapUnitGlobalSection_mul_inverse

lemma overlapSecondNormalSection_eq_first_mul_unit :
    overlapSecondNormalSection = overlapFirstNormalSection * overlapUnitSection := by
  apply overlapOpen.topIso.commRingCatIsoToRingEquiv.injective
  change overlapOpen.topIso.hom overlapSecondNormalSection =
    overlapOpen.topIso.hom (overlapFirstNormalSection * overlapUnitSection)
  rw [map_mul]
  change overlapOpen.topIso.hom (overlapOpen.topIso.inv overlapSecondNormalGlobalSection) =
    overlapOpen.topIso.hom (overlapOpen.topIso.inv overlapFirstNormalGlobalSection) *
      overlapOpen.topIso.hom (overlapOpen.topIso.inv overlapUnitGlobalSection)
  have h₀ := ConcreteCategory.congr_hom overlapOpen.topIso.inv_hom_id
    overlapSecondNormalGlobalSection
  have h₁ := ConcreteCategory.congr_hom overlapOpen.topIso.inv_hom_id
    overlapFirstNormalGlobalSection
  have hU := ConcreteCategory.congr_hom overlapOpen.topIso.inv_hom_id overlapUnitGlobalSection
  change overlapOpen.topIso.hom (overlapOpen.topIso.inv overlapSecondNormalGlobalSection) =
    overlapSecondNormalGlobalSection at h₀
  change overlapOpen.topIso.hom (overlapOpen.topIso.inv overlapFirstNormalGlobalSection) =
    overlapFirstNormalGlobalSection at h₁
  change overlapOpen.topIso.hom (overlapOpen.topIso.inv overlapUnitGlobalSection) =
    overlapUnitGlobalSection at hU
  rw [h₀, h₁, hU]
  exact overlapSecondNormalGlobalSection_eq_first_mul_unit

/-- Evaluation of the globally invertible overlap transition function. -/
def overlapUnitValue : ComplexPoint analyticOverlap → ℂ :=
  Point.evaluate ⊤ overlapUnitSection

/-- The two normal-coordinate functions on the actual analytic overlap. -/
def overlapFirstNormalValue : ComplexPoint analyticOverlap → ℂ :=
  Point.evaluate ⊤ overlapFirstNormalSection

def overlapSecondNormalValue : ComplexPoint analyticOverlap → ℂ :=
  Point.evaluate ⊤ overlapSecondNormalSection

lemma continuous_overlapUnitValue : Continuous overlapUnitValue :=
  continuous_evaluate_top (X := analyticOverlap) overlapUnitSection

lemma continuous_overlapFirstNormalValue : Continuous overlapFirstNormalValue :=
  continuous_evaluate_top (X := analyticOverlap) overlapFirstNormalSection

lemma continuous_overlapSecondNormalValue : Continuous overlapSecondNormalValue :=
  continuous_evaluate_top (X := analyticOverlap) overlapSecondNormalSection

lemma overlapUnitValue_ne_zero (z : ComplexPoint analyticOverlap) : overlapUnitValue z ≠ 0 := by
  intro hz
  have h := congrArg (fun s ↦ (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom s)
    overlapUnitSection_mul_inverse
  have hmul := map_mul (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom
    overlapUnitSection overlapUnitInverseSection
  have hvalue :
      (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom overlapUnitSection *
        (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom overlapUnitInverseSection = 1 :=
    hmul.symm.trans (h.trans (map_one (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom))
  have heval : (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom overlapUnitSection =
      Point.evaluate ⊤ overlapUnitSection z :=
    Point.evaluationHom_apply ⊤ ⟨z, trivial⟩ overlapUnitSection
  have hevalInv : (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom overlapUnitInverseSection =
      Point.evaluate ⊤ overlapUnitInverseSection z :=
    Point.evaluationHom_apply ⊤ ⟨z, trivial⟩ overlapUnitInverseSection
  have hvalue' : overlapUnitValue z * Point.evaluate ⊤ overlapUnitInverseSection z = 1 := by
    simpa only [overlapUnitValue, heval, hevalInv] using hvalue
  rw [hz, zero_mul] at hvalue'
  exact zero_ne_one hvalue'

lemma overlapNormalValue_transition (z : ComplexPoint analyticOverlap) :
    overlapSecondNormalValue z = overlapFirstNormalValue z * overlapUnitValue z := by
  have h := congrArg (fun s ↦ (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom s)
    overlapSecondNormalSection_eq_first_mul_unit
  have hmul := map_mul (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom
    overlapFirstNormalSection overlapUnitSection
  have hleft : (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom overlapSecondNormalSection =
      Point.evaluate ⊤ overlapSecondNormalSection z :=
    Point.evaluationHom_apply ⊤ ⟨z, trivial⟩ overlapSecondNormalSection
  have hfirst : (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom overlapFirstNormalSection =
      Point.evaluate ⊤ overlapFirstNormalSection z :=
    Point.evaluationHom_apply ⊤ ⟨z, trivial⟩ overlapFirstNormalSection
  have hunit : (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom overlapUnitSection =
      Point.evaluate ⊤ overlapUnitSection z :=
    Point.evaluationHom_apply ⊤ ⟨z, trivial⟩ overlapUnitSection
  calc
    overlapSecondNormalValue z =
        (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom overlapSecondNormalSection :=
      hleft.symm
    _ = (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom overlapFirstNormalSection *
        (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom overlapUnitSection := h.trans hmul
    _ = overlapFirstNormalValue z * overlapUnitValue z := by
      rw [hfirst, hunit]
      rfl

/-- The complement of the coordinate hyperplane inside the actual analytic overlap. -/
def overlapNormalComplement : Set (ComplexPoint analyticOverlap) :=
  {z | overlapFirstNormalValue z ≠ 0}

/-- The genuine topological pair `(D₊(X₁X₂), D₊(X₁X₂) \ {X₀ = 0})`. -/
abbrev overlapHyperplanePair : TopPair :=
  TopPair.ofSubset (X := TopCat.of (ComplexPoint analyticOverlap)) overlapNormalComplement

/-- The first normal coordinate on the complement of the hyperplane in the overlap. -/
def overlapFirstNormalOnComplement : C(overlapHyperplanePair.snd, ℂ) :=
  ⟨fun z => overlapFirstNormalValue z.1,
    continuous_overlapFirstNormalValue.comp continuous_subtype_val⟩

lemma overlapFirstNormalOnComplement_ne_zero :
    ∀ z, overlapFirstNormalOnComplement z ≠ 0 := by
  intro z
  change overlapFirstNormalValue z.1 ≠ 0
  exact z.property

/-- The second normal coordinate on the same punctured overlap. -/
def overlapSecondNormalOnComplement : C(overlapHyperplanePair.snd, ℂ) :=
  ⟨fun z => overlapSecondNormalValue z.1,
    continuous_overlapSecondNormalValue.comp continuous_subtype_val⟩

lemma overlapSecondNormalOnComplement_ne_zero :
    ∀ z, overlapSecondNormalOnComplement z ≠ 0 := by
  intro z
  change overlapSecondNormalValue z.1 ≠ 0
  rw [overlapNormalValue_transition]
  exact mul_ne_zero z.property (overlapUnitValue_ne_zero z.1)

/-- The globally invertible transition function, as a continuous function on the overlap. -/
def overlapUnitOnAmbient : C(overlapHyperplanePair.fst, ℂ) :=
  ⟨overlapUnitValue, continuous_overlapUnitValue⟩

lemma overlapUnitOnAmbient_ne_zero : ∀ z, overlapUnitOnAmbient z ≠ 0 :=
  overlapUnitValue_ne_zero

lemma overlapNormalOnComplement_transition (z : overlapHyperplanePair.snd) :
    overlapSecondNormalOnComplement z = overlapFirstNormalOnComplement z *
      (overlapUnitOnAmbient.comp (ChernWinding.topMap overlapHyperplanePair.map)) z := by
  change overlapSecondNormalValue z.1 =
    overlapFirstNormalValue z.1 * overlapUnitValue z.1
  exact overlapNormalValue_transition z.1

/-- The literal relative winding cochain of `X₀/X₁` on the actual overlap pair. -/
def overlapFirstWindingCochain :
    (CochainComplex.mappingCone
      (AlgebraicTopology.Singular.relativeCochainRestrictionInt ℚ
        overlapHyperplanePair)).X (ComplexShape.embeddingUpNat.f 1) :=
  ChernWinding.rawRelativeWindingCochain (X := overlapHyperplanePair)
    overlapFirstNormalOnComplement overlapFirstNormalOnComplement_ne_zero

/-- The literal relative winding cochain of `X₀/X₂` on the actual overlap pair. -/
def overlapSecondWindingCochain :
    (CochainComplex.mappingCone
      (AlgebraicTopology.Singular.relativeCochainRestrictionInt ℚ
        overlapHyperplanePair)).X (ComplexShape.embeddingUpNat.f 1) :=
  ChernWinding.rawRelativeWindingCochain (X := overlapHyperplanePair)
    overlapSecondNormalOnComplement overlapSecondNormalOnComplement_ne_zero

/-- The displayed degree-one primitive that records the `X₁/X₂` transition. -/
def overlapWindingTransitionPrimitive :
    (CochainComplex.mappingCone
      (AlgebraicTopology.Singular.relativeCochainRestrictionInt ℚ
        overlapHyperplanePair)).X (ComplexShape.embeddingUpNat.f 0) :=
  ChernWinding.rawRelativeWindingCoordinateTransitionPrimitive
    (X := overlapHyperplanePair)
    overlapFirstNormalOnComplement overlapUnitOnAmbient overlapSecondNormalOnComplement
    overlapFirstNormalOnComplement_ne_zero overlapUnitOnAmbient_ne_zero
    overlapSecondNormalOnComplement_ne_zero overlapNormalOnComplement_transition

/-- The actual overlap cochains differ by the displayed cone differential.

This is the coordinate transition calculation needed for the Čech cocycle; every term is a
specific singular cochain on a specific analytic open of the actual projective plane. -/
lemma overlapWindingCochain_transition :
    overlapSecondWindingCochain = overlapFirstWindingCochain +
      (CochainComplex.mappingCone
        (AlgebraicTopology.Singular.relativeCochainRestrictionInt ℚ overlapHyperplanePair)).d
        (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1)
        overlapWindingTransitionPrimitive :=
  ChernWinding.rawRelativeWindingCochain_coordinateTransition
    (X := overlapHyperplanePair)
    overlapFirstNormalOnComplement overlapUnitOnAmbient overlapSecondNormalOnComplement
    overlapFirstNormalOnComplement_ne_zero overlapUnitOnAmbient_ne_zero
    overlapSecondNormalOnComplement_ne_zero overlapNormalOnComplement_transition

/-- The actual open-immersion morphism from `D₊(X₁X₂)` to `D₊(X₁)` over `Spec ℂ`. -/
def overlapToFirstChartOver : analyticOverlap ⟶ analyticChart 1 :=
  Over.homMk (plane.homOfLE overlapOpen_le_firstChart) (by
    dsimp [analyticOverlap, analyticChart, analyticPlane, openScheme]
    rw [← Category.assoc, Scheme.homOfLE_ι])

/-- The actual open-immersion morphism from `D₊(X₁X₂)` to `D₊(X₂)` over `Spec ℂ`. -/
def overlapToSecondChartOver : analyticOverlap ⟶ analyticChart 2 :=
  Over.homMk (plane.homOfLE overlapOpen_le_secondChart) (by
    dsimp [analyticOverlap, analyticChart, analyticPlane, openScheme]
    rw [← Category.assoc, Scheme.homOfLE_ι])

/-- Composing the first overlap-to-chart inclusion with the chart inclusion gives the original
inclusion of the overlap into the projective plane. -/
lemma overlapToFirstChartOver_comp_openInclusion :
    overlapToFirstChartOver ≫ openInclusion analyticPlane (chartOpen 1) =
      openInclusion analyticPlane overlapOpen := by
  apply Over.OverMorphism.ext
  dsimp [overlapToFirstChartOver, analyticOverlap, analyticChart, openScheme,
    analyticPlane, openInclusion]
  exact Scheme.homOfLE_ι plane overlapOpen_le_firstChart

/-- The analogous factorization through the second chart. -/
lemma overlapToSecondChartOver_comp_openInclusion :
    overlapToSecondChartOver ≫ openInclusion analyticPlane (chartOpen 2) =
      openInclusion analyticPlane overlapOpen := by
  apply Over.OverMorphism.ext
  dsimp [overlapToSecondChartOver, analyticOverlap, analyticChart, openScheme,
    analyticPlane, openInclusion]
  exact Scheme.homOfLE_ι plane overlapOpen_le_secondChart

/-- The analytic map from the overlap into the first standard chart.  This is the map induced
by the actual scheme morphism `overlapToFirstChartOver`, not merely a set-theoretic inclusion. -/
def overlapToFirstChart :
    ComplexPoint analyticOverlap → ComplexPoint (analyticChart 1) :=
  Point.map overlapToFirstChartOver

/-- The analytic map from the overlap into the second standard chart. -/
def overlapToSecondChart :
    ComplexPoint analyticOverlap → ComplexPoint (analyticChart 2) :=
  Point.map overlapToSecondChartOver

lemma continuous_overlapToFirstChart : Continuous overlapToFirstChart :=
  Point.continuous_map overlapToFirstChartOver

lemma continuous_overlapToSecondChart : Continuous overlapToSecondChart :=
  Point.continuous_map overlapToSecondChartOver

/-- On the actual overlap, the local function obtained by restricting `X₀/X₁` is the pullback
of the literal regular function on `D₊(X₁)`. -/
lemma overlapFirstNormalValue_eq_firstNormalValue (z : ComplexPoint analyticOverlap) :
    overlapFirstNormalValue z = firstNormalValue (overlapToFirstChart z) := by
  change Point.evaluate ⊤ (overlapOpen.topIso.inv overlapFirstNormalGlobalSection) z =
    Point.evaluate ⊤ ((chartOpen 1).topIso.inv firstNormalGlobalSection)
      (Point.map overlapToFirstChartOver z)
  dsimp only [analyticOverlap, analyticChart, analyticPlane, openScheme] at z ⊢
  rw [evaluate_topIso_inv (X := Over.mk structureMap) overlapOpen
    overlapFirstNormalGlobalSection z,
    evaluate_topIso_inv (X := Over.mk structureMap) (chartOpen 1)
      firstNormalGlobalSection (Point.map overlapToFirstChartOver z)]
  rw [← Point.map_comp_apply, overlapToFirstChartOver_comp_openInclusion,
    overlapFirstNormalGlobalSection_eq_restrict]
  exact (Point.evaluate_res overlapOpen_le_firstChart firstNormalGlobalSection
    (Point.map (openInclusion analyticPlane overlapOpen) z)
    (openEquiv analyticPlane overlapOpen z).2).symm

/-- The parallel statement for `X₀/X₂` and the second standard chart. -/
lemma overlapSecondNormalValue_eq_secondNormalValue (z : ComplexPoint analyticOverlap) :
    overlapSecondNormalValue z = secondNormalCoordinate (overlapToSecondChart z) := by
  change Point.evaluate ⊤ (overlapOpen.topIso.inv overlapSecondNormalGlobalSection) z =
    Point.evaluate ⊤ ((chartOpen 2).topIso.inv secondNormalGlobalSection)
      (Point.map overlapToSecondChartOver z)
  dsimp only [analyticOverlap, analyticChart, analyticPlane, openScheme] at z ⊢
  rw [evaluate_topIso_inv (X := Over.mk structureMap) overlapOpen
    overlapSecondNormalGlobalSection z,
    evaluate_topIso_inv (X := Over.mk structureMap) (chartOpen 2)
      secondNormalGlobalSection (Point.map overlapToSecondChartOver z)]
  rw [← Point.map_comp_apply, overlapToSecondChartOver_comp_openInclusion,
    overlapSecondNormalGlobalSection_eq_restrict]
  exact (Point.evaluate_res overlapOpen_le_secondChart secondNormalGlobalSection
    (Point.map (openInclusion analyticPlane overlapOpen) z)
    (openEquiv analyticPlane overlapOpen z).2).symm

/-- The complement of the coordinate hyperplane inside the first standard chart. -/
def firstNormalComplement : Set (ComplexPoint (analyticChart 1)) :=
  {z | firstNormalValue z ≠ 0}

/-- The punctured first affine chart is literally the preimage of the complement of the
scheme-theoretic zero locus `{X₀ = 0}`. -/
lemma mem_firstNormalComplement_iff (z : ComplexPoint (analyticChart 1)) :
    z ∈ firstNormalComplement ↔
      Point.map (openInclusion analyticPlane (chartOpen 1)) z ∈
        Point.overOpen hyperplaneComplementOpen := by
  change Point.evaluate ⊤ firstNormalSection z ≠ 0 ↔ _
  have hz : z ∈ Point.overOpen (⊤ : (analyticChart 1).left.Opens) := by
    change z.underlying ∈ (⊤ : (analyticChart 1).left.Opens)
    trivial
  rw [← Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero firstNormalSection z hz]
  change z ∈ Point.overOpen ((chartOpen 1).toScheme.basicOpen firstNormalSection) ↔ _
  rw [firstNormalSection_basicOpen_eq_preimage_hyperplaneComplementOpen]
  exact (Point.mem_overOpen_map_iff
    (openInclusion analyticPlane (chartOpen 1)) z hyperplaneComplementOpen).symm

/-- Equivalently, the punctured first chart is the complement of the actual analytic image
of the closed immersion defining the hyperplane. -/
lemma mem_firstNormalComplement_iff_not_mem_hyperplane (z : ComplexPoint (analyticChart 1)) :
    z ∈ firstNormalComplement ↔
      Point.map (openInclusion analyticPlane (chartOpen 1)) z ∉
        Set.range (Point.map hyperplaneOverι) := by
  rw [mem_firstNormalComplement_iff,
    show Point.overOpen (X := analyticPlane) hyperplaneComplementOpen =
      (Set.range (Point.map hyperplaneOverι))ᶜ from
        hyperplaneComplementOpen_eq_compl_range_complexPoint]
  rfl

/-- Set-level form of `mem_firstNormalComplement_iff_not_mem_hyperplane`, suitable for
transporting the relative cochain complex from the chart to the actual hyperplane support. -/
lemma firstNormalComplement_eq_preimage_hyperplaneSupportComplement :
    firstNormalComplement =
      (Point.map (openInclusion analyticPlane (chartOpen 1))) ⁻¹'
        (Set.range (Point.map hyperplaneOverι))ᶜ := by
  ext z
  exact mem_firstNormalComplement_iff_not_mem_hyperplane z

/-- The normal-coordinate topological pair on `D₊(X₁)`.

Its second component is the pullback of the complement of the scheme-theoretic hyperplane
`{X₀ = 0}`, by `mem_firstNormalComplement_iff`. -/
abbrev firstChartHyperplanePair : TopPair :=
  TopPair.ofSubset (X := TopCat.of (ComplexPoint (analyticChart 1))) firstNormalComplement

/-- The normal coordinate restricted to the complement of its zero locus. -/
def firstNormalOnComplement : C(firstChartHyperplanePair.snd, ℂ) :=
  ⟨fun z => firstNormalValue z.1,
    continuous_firstNormalValue.comp continuous_subtype_val⟩

lemma firstNormalOnComplement_ne_zero : ∀ z, firstNormalOnComplement z ≠ 0 := by
  intro z
  change firstNormalValue z.1 ≠ 0
  exact z.property

/-- A literal degree-two relative singular cochain for `X₀ = 0` on `D₊(X₁)`.

Unfolding this definition gives the mapping-cone element `(0, windingIndex(X₀ / X₁))`.
It is therefore an actual cochain, rather than a class selected from an existence theorem. -/
def firstChartHyperplaneCochain :
    (CochainComplex.mappingCone
      (AlgebraicTopology.Singular.relativeCochainRestrictionInt ℚ
        firstChartHyperplanePair)).X (ComplexShape.embeddingUpNat.f 1) :=
  ChernWinding.rawRelativeWindingCochain (X := firstChartHyperplanePair)
    firstNormalOnComplement firstNormalOnComplement_ne_zero

/-- The displayed first-chart hyperplane cochain is closed. -/
lemma firstChartHyperplaneCochain_closed :
    (CochainComplex.mappingCone
      (AlgebraicTopology.Singular.relativeCochainRestrictionInt ℚ
        firstChartHyperplanePair)).d
      (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2)
      firstChartHyperplaneCochain = 0 :=
  ChernWinding.rawRelativeWindingCochain_closed
    (X := firstChartHyperplanePair)
    firstNormalOnComplement firstNormalOnComplement_ne_zero

/-- The relative singular cohomology class of the explicit first-chart cochain.  This is formed
from the displayed mapping-cone cocycle `(0, windingIndex(X₀/X₁))`, before any passage to a
cycle class or a Chern-class theorem. -/
def firstChartHyperplaneRelativeSingularClass :
    AlgebraicTopology.Singular.RelativeCohomology ℚ firstChartHyperplanePair 2 :=
  ChernWinding.windingRelativeCochainClass (X := firstChartHyperplanePair)
    firstNormalOnComplement firstNormalOnComplement_ne_zero

/-- Restriction from the first affine chart to the actual overlap, regarded as a morphism of the
pairs obtained by deleting the explicit zero loci of `X₀/X₁`. -/
def overlapToFirstChartPair : overlapHyperplanePair ⟶ firstChartHyperplanePair := by
  refine TopPair.ofHom (TopCat.ofHom ⟨overlapToFirstChart, continuous_overlapToFirstChart⟩) ?_ ?_
  · have hmem : ∀ z : overlapHyperplanePair.snd,
        firstNormalValue (overlapToFirstChart z.1) ≠ 0 := by
      intro z hz
      apply z.2
      rw [overlapFirstNormalValue_eq_firstNormalValue]
      exact hz
    have hmem' : ∀ z : overlapHyperplanePair.snd,
        overlapToFirstChart z.1 ∈ firstNormalComplement := hmem
    exact TopCat.ofHom ⟨fun z ↦ ⟨overlapToFirstChart z.1, hmem' z⟩,
      (continuous_overlapToFirstChart.comp continuous_subtype_val).subtype_mk hmem'⟩
  · ext z
    rfl

/-- Pulling `X₀/X₁` back along the map of punctured pairs is literally the normal function on
the overlap. -/
lemma firstNormalOnComplement_pullback_to_overlap :
    firstNormalOnComplement.comp
      (ChernWinding.topMap (TopPair.Hom.snd overlapToFirstChartPair)) =
        overlapFirstNormalOnComplement := by
  ext z
  change firstNormalValue (overlapToFirstChart z.1) = overlapFirstNormalValue z.1
  exact (overlapFirstNormalValue_eq_firstNormalValue z.1).symm

/-- The literal cochain on the overlap is exactly the raw relative-cochain pullback of the
literal first-chart cochain.  Thus this is not only equality of cohomology classes. -/
lemma overlapFirstWindingCochain_eq_pullback_firstChartHyperplaneCochain :
    overlapFirstWindingCochain =
      ChernWinding.rawRelativeWindingCochainPullback overlapToFirstChartPair
        firstNormalOnComplement firstNormalOnComplement_ne_zero := by
  have raw_congr (g h : C(overlapHyperplanePair.snd, ℂ))
      (hg : ∀ z, g z ≠ 0) (hh : ∀ z, h z ≠ 0) (e : g = h) :
      ChernWinding.rawRelativeWindingCochain (X := overlapHyperplanePair) g hg =
        ChernWinding.rawRelativeWindingCochain (X := overlapHyperplanePair) h hh := by
    cases e
    rfl
  change ChernWinding.rawRelativeWindingCochain (X := overlapHyperplanePair)
      overlapFirstNormalOnComplement overlapFirstNormalOnComplement_ne_zero = _
  calc
    _ = ChernWinding.rawRelativeWindingCochain (X := overlapHyperplanePair)
        (firstNormalOnComplement.comp
          (ChernWinding.topMap (TopPair.Hom.snd overlapToFirstChartPair)))
        (fun z => firstNormalOnComplement_ne_zero (TopPair.Hom.snd overlapToFirstChartPair z)) :=
      raw_congr _ _ _ _ firstNormalOnComplement_pullback_to_overlap.symm
    _ = _ :=
      (ChernWinding.rawRelativeWindingCochainPullback_eq_rawRelativeWindingCochain
        overlapToFirstChartPair firstNormalOnComplement firstNormalOnComplement_ne_zero).symm

/-- The complement of the displayed normal-coordinate zero set inside the second standard
chart. -/
def secondNormalComplement : Set (ComplexPoint (analyticChart 2)) :=
  {z | secondNormalCoordinate z ≠ 0}

/-- The punctured second affine chart is literally the preimage of the complement of the
scheme-theoretic zero locus `{X₀ = 0}`. -/
lemma mem_secondNormalComplement_iff (z : ComplexPoint (analyticChart 2)) :
    z ∈ secondNormalComplement ↔
      Point.map (openInclusion analyticPlane (chartOpen 2)) z ∈
        Point.overOpen hyperplaneComplementOpen := by
  change secondNormalCoordinate z ≠ 0 ↔ _
  rw [secondNormalCoordinate_eq_evaluate_secondNormalSection]
  have hz : z ∈ Point.overOpen (⊤ : (analyticChart 2).left.Opens) := by
    change z.underlying ∈ (⊤ : (analyticChart 2).left.Opens)
    trivial
  rw [← Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero secondNormalSection z hz]
  change z ∈ Point.overOpen ((chartOpen 2).toScheme.basicOpen secondNormalSection) ↔ _
  rw [secondNormalSection_basicOpen_eq_preimage_hyperplaneComplementOpen]
  exact (Point.mem_overOpen_map_iff
    (openInclusion analyticPlane (chartOpen 2)) z hyperplaneComplementOpen).symm

/-- Equivalently, the punctured second chart is the complement of the actual analytic image
of the closed immersion defining the hyperplane. -/
lemma mem_secondNormalComplement_iff_not_mem_hyperplane (z : ComplexPoint (analyticChart 2)) :
    z ∈ secondNormalComplement ↔
      Point.map (openInclusion analyticPlane (chartOpen 2)) z ∉
        Set.range (Point.map hyperplaneOverι) := by
  rw [mem_secondNormalComplement_iff,
    show Point.overOpen (X := analyticPlane) hyperplaneComplementOpen =
      (Set.range (Point.map hyperplaneOverι))ᶜ from
        hyperplaneComplementOpen_eq_compl_range_complexPoint]
  rfl

/-- Set-level form of `mem_secondNormalComplement_iff_not_mem_hyperplane`, suitable for
transporting the relative cochain complex from the chart to the actual hyperplane support. -/
lemma secondNormalComplement_eq_preimage_hyperplaneSupportComplement :
    secondNormalComplement =
      (Point.map (openInclusion analyticPlane (chartOpen 2))) ⁻¹'
        (Set.range (Point.map hyperplaneOverι))ᶜ := by
  ext z
  exact mem_secondNormalComplement_iff_not_mem_hyperplane z

/-- The normal-coordinate pair on `D₊(X₂)`, whose punctured part is the pullback of the
complement of the scheme-theoretic hyperplane. -/
abbrev secondChartHyperplanePair : TopPair :=
  TopPair.ofSubset (X := TopCat.of (ComplexPoint (analyticChart 2))) secondNormalComplement

/-- The second normal coordinate, restricted to its punctured chart. -/
def secondNormalOnComplement : C(secondChartHyperplanePair.snd, ℂ) :=
  ⟨fun z => secondNormalCoordinate z.1,
    continuous_secondNormalCoordinate.comp continuous_subtype_val⟩

lemma secondNormalOnComplement_ne_zero : ∀ z, secondNormalOnComplement z ≠ 0 := by
  intro z
  change secondNormalCoordinate z.1 ≠ 0
  exact z.property

/-- The literal degree-two relative cochain on the second `Proj` chart. -/
def secondChartHyperplaneCochain :
    (CochainComplex.mappingCone
      (AlgebraicTopology.Singular.relativeCochainRestrictionInt ℚ
        secondChartHyperplanePair)).X (ComplexShape.embeddingUpNat.f 1) :=
  ChernWinding.rawRelativeWindingCochain (X := secondChartHyperplanePair)
    secondNormalOnComplement secondNormalOnComplement_ne_zero

lemma secondChartHyperplaneCochain_closed :
    (CochainComplex.mappingCone
      (AlgebraicTopology.Singular.relativeCochainRestrictionInt ℚ
        secondChartHyperplanePair)).d
      (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2)
      secondChartHyperplaneCochain = 0 :=
  ChernWinding.rawRelativeWindingCochain_closed
    (X := secondChartHyperplanePair)
    secondNormalOnComplement secondNormalOnComplement_ne_zero

/-- The relative singular cohomology class of the explicit second-chart cochain.  As on the
first chart, this is formed directly from the displayed mapping-cone cocycle
`(0, windingIndex(X₀/X₂))`. -/
def secondChartHyperplaneRelativeSingularClass :
    AlgebraicTopology.Singular.RelativeCohomology ℚ secondChartHyperplanePair 2 :=
  ChernWinding.windingRelativeCochainClass (X := secondChartHyperplanePair)
    secondNormalOnComplement secondNormalOnComplement_ne_zero

/-- Restriction from the overlap to the second affine chart, as a map of punctured pairs. -/
def overlapToSecondChartPair : overlapHyperplanePair ⟶ secondChartHyperplanePair := by
  refine TopPair.ofHom (TopCat.ofHom ⟨overlapToSecondChart, continuous_overlapToSecondChart⟩) ?_ ?_
  · have hmem : ∀ z : overlapHyperplanePair.snd,
        secondNormalCoordinate (overlapToSecondChart z.1) ≠ 0 := by
      intro z
      rw [← overlapSecondNormalValue_eq_secondNormalValue]
      exact overlapSecondNormalOnComplement_ne_zero z
    have hmem' : ∀ z : overlapHyperplanePair.snd,
        overlapToSecondChart z.1 ∈ secondNormalComplement := hmem
    exact TopCat.ofHom ⟨fun z ↦ ⟨overlapToSecondChart z.1, hmem' z⟩,
      (continuous_overlapToSecondChart.comp continuous_subtype_val).subtype_mk hmem'⟩
  · ext z
    rfl

/-- The second chart normal function pulls back to the actual overlap normal function. -/
lemma secondNormalOnComplement_pullback_to_overlap :
    secondNormalOnComplement.comp
      (ChernWinding.topMap (TopPair.Hom.snd overlapToSecondChartPair)) =
        overlapSecondNormalOnComplement := by
  ext z
  change secondNormalCoordinate (overlapToSecondChart z.1) = overlapSecondNormalValue z.1
  exact (overlapSecondNormalValue_eq_secondNormalValue z.1).symm

/-- The overlap's second winding cochain is the literal pullback of the second chart cochain. -/
lemma overlapSecondWindingCochain_eq_pullback_secondChartHyperplaneCochain :
    overlapSecondWindingCochain =
      ChernWinding.rawRelativeWindingCochainPullback overlapToSecondChartPair
        secondNormalOnComplement secondNormalOnComplement_ne_zero := by
  have raw_congr (g h : C(overlapHyperplanePair.snd, ℂ))
      (hg : ∀ z, g z ≠ 0) (hh : ∀ z, h z ≠ 0) (e : g = h) :
      ChernWinding.rawRelativeWindingCochain (X := overlapHyperplanePair) g hg =
        ChernWinding.rawRelativeWindingCochain (X := overlapHyperplanePair) h hh := by
    cases e
    rfl
  change ChernWinding.rawRelativeWindingCochain (X := overlapHyperplanePair)
      overlapSecondNormalOnComplement overlapSecondNormalOnComplement_ne_zero = _
  calc
    _ = ChernWinding.rawRelativeWindingCochain (X := overlapHyperplanePair)
        (secondNormalOnComplement.comp
          (ChernWinding.topMap (TopPair.Hom.snd overlapToSecondChartPair)))
        (fun z => secondNormalOnComplement_ne_zero (TopPair.Hom.snd overlapToSecondChartPair z)) :=
      raw_congr _ _ _ _ secondNormalOnComplement_pullback_to_overlap.symm
    _ = _ :=
      (ChernWinding.rawRelativeWindingCochainPullback_eq_rawRelativeWindingCochain
        overlapToSecondChartPair secondNormalOnComplement secondNormalOnComplement_ne_zero).symm

/-- Restriction of the literal first-chart relative cochain to the actual overlap pair. -/
def firstChartCochainRestriction :
    CochainComplex.mappingCone
      (AlgebraicTopology.Singular.relativeCochainRestrictionInt ℚ firstChartHyperplanePair) ⟶
    CochainComplex.mappingCone
      (AlgebraicTopology.Singular.relativeCochainRestrictionInt ℚ overlapHyperplanePair) :=
  AlgebraicTopology.Singular.relativeCochainConeMap ℚ overlapToFirstChartPair

/-- Restriction of the literal second-chart relative cochain to the actual overlap pair. -/
def secondChartCochainRestriction :
    CochainComplex.mappingCone
      (AlgebraicTopology.Singular.relativeCochainRestrictionInt ℚ secondChartHyperplanePair) ⟶
    CochainComplex.mappingCone
      (AlgebraicTopology.Singular.relativeCochainRestrictionInt ℚ overlapHyperplanePair) :=
  AlgebraicTopology.Singular.relativeCochainConeMap ℚ overlapToSecondChartPair

lemma firstChartCochainRestriction_winding :
    firstChartCochainRestriction.f (ComplexShape.embeddingUpNat.f 1)
      firstChartHyperplaneCochain = overlapFirstWindingCochain := by
  change ChernWinding.rawRelativeWindingCochainPullback overlapToFirstChartPair
    firstNormalOnComplement firstNormalOnComplement_ne_zero = _
  exact overlapFirstWindingCochain_eq_pullback_firstChartHyperplaneCochain.symm

lemma secondChartCochainRestriction_winding :
    secondChartCochainRestriction.f (ComplexShape.embeddingUpNat.f 1)
      secondChartHyperplaneCochain = overlapSecondWindingCochain := by
  change ChernWinding.rawRelativeWindingCochainPullback overlapToSecondChartPair
    secondNormalOnComplement secondNormalOnComplement_ne_zero = _
  exact overlapSecondWindingCochain_eq_pullback_secondChartHyperplaneCochain.symm

/-- The literal two-open Čech--singular cochain for the hyperplane on the two actual standard
`Proj` charts meeting it.  Its three components are the two displayed winding cochains and the
explicit branch-jump/unit primitive on `D₊(X₁X₂)`. -/
def coordinateHyperplaneCechCochain :
    (AlgebraicTopology.Singular.twoOpenCechTotal
      firstChartCochainRestriction secondChartCochainRestriction).X 0 :=
  AlgebraicTopology.Singular.twoOpenCechCochain
    firstChartCochainRestriction secondChartCochainRestriction 1
    firstChartHyperplaneCochain secondChartHyperplaneCochain overlapWindingTransitionPrimitive

lemma coordinateHyperplaneCechCochain_compatibility :
    firstChartCochainRestriction.f (ComplexShape.embeddingUpNat.f 1)
      firstChartHyperplaneCochain -
      secondChartCochainRestriction.f (ComplexShape.embeddingUpNat.f 1)
        secondChartHyperplaneCochain =
      -(CochainComplex.mappingCone
        (AlgebraicTopology.Singular.relativeCochainRestrictionInt ℚ overlapHyperplanePair)).d
          (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1)
          overlapWindingTransitionPrimitive := by
  rw [firstChartCochainRestriction_winding, secondChartCochainRestriction_winding,
    overlapWindingCochain_transition]
  abel

/-- The actual `Proj` Čech--singular cochain is closed before taking cohomology. -/
lemma coordinateHyperplaneCechCochain_closed :
    (AlgebraicTopology.Singular.twoOpenCechTotal
      firstChartCochainRestriction secondChartCochainRestriction).d 0 1
      coordinateHyperplaneCechCochain = 0 :=
  AlgebraicTopology.Singular.twoOpenCechCochain_closed
    firstChartCochainRestriction secondChartCochainRestriction 1
    firstChartHyperplaneCochain secondChartHyperplaneCochain overlapWindingTransitionPrimitive
    firstChartHyperplaneCochain_closed secondChartHyperplaneCochain_closed
    coordinateHyperplaneCechCochain_compatibility

/-- The displayed coordinate-hyperplane cochain, packaged as a cycle of the actual
Čech--singular total complex.  This is just the closed cochain above factored through the
kernel of its differential; no representative is selected by choice. -/
def coordinateHyperplaneCechCocycle :
    ModuleCat.of ℚ ℚ ⟶
      (AlgebraicTopology.Singular.twoOpenCechTotal
        firstChartCochainRestriction secondChartCochainRestriction).cycles 0 :=
  (AlgebraicTopology.Singular.twoOpenCechTotal
    firstChartCochainRestriction secondChartCochainRestriction).liftCycles
    (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ coordinateHyperplaneCechCochain)) 1
    (by norm_num) (by
      ext
      change (AlgebraicTopology.Singular.twoOpenCechTotal
        firstChartCochainRestriction secondChartCochainRestriction).d 0 1
          (LinearMap.toSpanSingleton ℚ _ coordinateHyperplaneCechCochain 1) = 0
      rw [LinearMap.toSpanSingleton_apply]
      simpa using coordinateHyperplaneCechCochain_closed)

/-- Forgetting that `coordinateHyperplaneCechCocycle` lands in cycles recovers precisely the
three-component cochain written above.  Thus the passage to cohomology has not hidden a
choice of a cocycle representative. -/
lemma coordinateHyperplaneCechCocycle_iCycles :
    coordinateHyperplaneCechCocycle ≫
      (AlgebraicTopology.Singular.twoOpenCechTotal
        firstChartCochainRestriction secondChartCochainRestriction).iCycles 0 =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ coordinateHyperplaneCechCochain) := by
  exact HomologicalComplex.liftCycles_i _ _ _ _ _

/-- The cohomology class represented by the literal coordinate-hyperplane Čech--singular
cocycle.  In particular its construction retains the explicit two winding cochains and their
explicit overlap primitive. -/
def coordinateHyperplaneCechClass :
    (AlgebraicTopology.Singular.twoOpenCechTotal
      firstChartCochainRestriction secondChartCochainRestriction).homology 0 :=
  (coordinateHyperplaneCechCocycle ≫
    (AlgebraicTopology.Singular.twoOpenCechTotal
      firstChartCochainRestriction secondChartCochainRestriction).homologyπ 0).hom 1

end AlgebraicGeometry.ProjectivePlane.CoordinateCharts
