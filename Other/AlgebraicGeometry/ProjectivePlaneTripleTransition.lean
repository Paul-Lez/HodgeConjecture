/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache License 2.0 as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectivePlaneCoordinateCharts
public import Other.AlgebraicTopology.CechWindingTransition
public import Other.AlgebraicTopology.FiniteGoodCoverHomology
public import Other.AlgebraicTopology.RationalOpenCoverOrderedCechBicomplex

/-!
# The three coordinate transition functions on the triple overlap of `ℙ²`

This is a literal homogeneous-localization calculation of a Čech transition cocycle associated
to the coordinate ratios. On `D₊(X₀X₁X₂)` it constructs the three units

`X₁/X₀`, `X₂/X₀`, and `X₂/X₁`

and proves their product identity as an equality of actual regular functions, then as an
equality of continuous complex-valued functions on analytic points. The separate comparison with
the supported class of the zero locus `X₀ = 0` is not supplied by this file.
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial AlgebraicGeometry AlgebraicTopology.Singular
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectivePlane.CoordinateCharts

open AlgebraicGeometry.ComplexPoint

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual triple standard overlap `D₊(X₀X₁X₂)` in the direct `Proj` model. -/
def tripleOpen : plane.Opens :=
  Proj.basicOpen Grading (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)

/-- Its open subscheme, still over `Spec ℂ`. -/
abbrev analyticTriple : Over (Spec ↧ℂ) :=
  openScheme analyticPlane tripleOpen

lemma coordinateZero_homogeneous :
    (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℂ) ∈ Grading 1 :=
  Other.ProjectiveChart.X_mem_one ℂ 0

lemma tripleEquation_homogeneous :
    (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 :
      MvPolynomial (Fin 3) ℂ) ∈ Grading 3 := by
  simpa [mul_assoc] using SetLike.mul_mem_graded
    (SetLike.mul_mem_graded coordinateZero_homogeneous coordinateOne_homogeneous)
    coordinateTwo_homogeneous

lemma triple01Numerator_homogeneous :
    (MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ) ∈ Grading 3 := by
  simpa [pow_two] using SetLike.mul_mem_graded
    (SetLike.mul_mem_graded coordinateOne_homogeneous coordinateOne_homogeneous)
    coordinateTwo_homogeneous

lemma triple02Numerator_homogeneous :
    (MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2 : MvPolynomial (Fin 3) ℂ) ∈ Grading 3 := by
  simpa [pow_two] using SetLike.mul_mem_graded
    coordinateOne_homogeneous
    (SetLike.mul_mem_graded coordinateTwo_homogeneous coordinateTwo_homogeneous)

lemma triple12Numerator_homogeneous :
    (MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2 : MvPolynomial (Fin 3) ℂ) ∈ Grading 3 := by
  simpa [pow_two] using SetLike.mul_mem_graded
    coordinateZero_homogeneous
    (SetLike.mul_mem_graded coordinateTwo_homogeneous coordinateTwo_homogeneous)

lemma triple01InverseNumerator_homogeneous :
    (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ) ∈ Grading 3 := by
  simpa [pow_two] using SetLike.mul_mem_graded
    (SetLike.mul_mem_graded coordinateZero_homogeneous coordinateZero_homogeneous)
    coordinateTwo_homogeneous

lemma triple02InverseNumerator_homogeneous :
    (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ) ∈ Grading 3 := by
  simpa [pow_two] using SetLike.mul_mem_graded
    (SetLike.mul_mem_graded coordinateZero_homogeneous coordinateZero_homogeneous)
    coordinateOne_homogeneous

lemma triple12InverseNumerator_homogeneous :
    (MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 3) ℂ) ∈ Grading 3 := by
  simpa [pow_two] using SetLike.mul_mem_graded
    coordinateZero_homogeneous
    (SetLike.mul_mem_graded coordinateOne_homogeneous coordinateOne_homogeneous)

/-- `X₁/X₀`, represented over the triple denominator by `X₁²X₂/(X₀X₁X₂)`. -/
def triple01Element :
    HomogeneousLocalization.Away Grading
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) :=
  HomogeneousLocalization.Away.mk Grading tripleEquation_homogeneous 1
    (MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2) triple01Numerator_homogeneous

/-- `X₂/X₀`, represented over the triple denominator. -/
def triple02Element :
    HomogeneousLocalization.Away Grading
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) :=
  HomogeneousLocalization.Away.mk Grading tripleEquation_homogeneous 1
    (MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2) triple02Numerator_homogeneous

/-- `X₂/X₁`, represented over the triple denominator. -/
def triple12Element :
    HomogeneousLocalization.Away Grading
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) :=
  HomogeneousLocalization.Away.mk Grading tripleEquation_homogeneous 1
    (MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2) triple12Numerator_homogeneous

/-- The displayed inverse of `X₁/X₀`. -/
def triple01InverseElement :
    HomogeneousLocalization.Away Grading
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) :=
  HomogeneousLocalization.Away.mk Grading tripleEquation_homogeneous 1
    (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2) triple01InverseNumerator_homogeneous

/-- The displayed inverse of `X₂/X₀`. -/
def triple02InverseElement :
    HomogeneousLocalization.Away Grading
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) :=
  HomogeneousLocalization.Away.mk Grading tripleEquation_homogeneous 1
    (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1) triple02InverseNumerator_homogeneous

/-- The displayed inverse of `X₂/X₁`. -/
def triple12InverseElement :
    HomogeneousLocalization.Away Grading
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) :=
  HomogeneousLocalization.Away.mk Grading tripleEquation_homogeneous 1
    (MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2) triple12InverseNumerator_homogeneous

lemma triple01Element_mul_inverse : triple01Element * triple01InverseElement = 1 := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2))
  dsimp [triple01Element, triple01InverseElement]
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  use 1
  simp
  ring

lemma triple02Element_mul_inverse : triple02Element * triple02InverseElement = 1 := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2))
  dsimp [triple02Element, triple02InverseElement]
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  use 1
  simp
  ring

lemma triple12Element_mul_inverse : triple12Element * triple12InverseElement = 1 := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2))
  dsimp [triple12Element, triple12InverseElement]
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  use 1
  simp
  ring

/-- The literal homogeneous-localization transition identity
`X₂/X₀ = (X₁/X₀) * (X₂/X₁)`. -/
lemma triple02Element_eq_triple01_mul_triple12 :
    triple02Element = triple01Element * triple12Element := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2))
  dsimp [triple01Element, triple02Element, triple12Element]
  rw [HomogeneousLocalization.val_mul]
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp
  ring

/-- Interpret an element of the triple homogeneous localization as a regular section on the
actual `Proj` open. -/
def tripleGlobalSection
    (x : HomogeneousLocalization.Away Grading
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)) :
    Γ(plane, tripleOpen) := by
  change Γ(Proj Grading,
    Proj.basicOpen Grading (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2))
  exact (Proj.basicOpenIsoAway Grading (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)
    tripleEquation_homogeneous (by norm_num)).hom x

lemma tripleGlobalSection_mul
    (x y : HomogeneousLocalization.Away Grading
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)) :
    tripleGlobalSection (x * y) = tripleGlobalSection x * tripleGlobalSection y := by
  change (Proj.basicOpenIsoAway Grading (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)
      tripleEquation_homogeneous (by norm_num)).hom (x * y) = _
  exact map_mul _ _ _

/-- The corresponding regular function on the affine triple-overlap scheme. -/
def tripleSection
    (x : HomogeneousLocalization.Away Grading
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)) :
    Γ(tripleOpen.toScheme, ⊤) :=
  tripleOpen.topIso.inv (tripleGlobalSection x)

lemma tripleSection_mul
    (x y : HomogeneousLocalization.Away Grading
      (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)) :
    tripleSection (x * y) = tripleSection x * tripleSection y := by
  apply tripleOpen.topIso.commRingCatIsoToRingEquiv.injective
  change tripleOpen.topIso.hom (tripleOpen.topIso.inv (tripleGlobalSection (x * y))) =
    tripleOpen.topIso.hom
      (tripleOpen.topIso.inv (tripleGlobalSection x) *
        tripleOpen.topIso.inv (tripleGlobalSection y))
  rw [map_mul]
  have hxy := ConcreteCategory.congr_hom tripleOpen.topIso.inv_hom_id
    (tripleGlobalSection (x * y))
  have hx := ConcreteCategory.congr_hom tripleOpen.topIso.inv_hom_id (tripleGlobalSection x)
  have hy := ConcreteCategory.congr_hom tripleOpen.topIso.inv_hom_id (tripleGlobalSection y)
  change tripleOpen.topIso.hom (tripleOpen.topIso.inv (tripleGlobalSection (x * y))) =
    tripleGlobalSection (x * y) at hxy
  change tripleOpen.topIso.hom (tripleOpen.topIso.inv (tripleGlobalSection x)) =
    tripleGlobalSection x at hx
  change tripleOpen.topIso.hom (tripleOpen.topIso.inv (tripleGlobalSection y)) =
    tripleGlobalSection y at hy
  rw [hxy, hx, hy]
  exact tripleGlobalSection_mul x y

lemma tripleSection02_eq_section01_mul_section12 :
    tripleSection triple02Element =
      tripleSection triple01Element * tripleSection triple12Element := by
  rw [← tripleSection_mul, triple02Element_eq_triple01_mul_triple12]

lemma tripleSection_one : tripleSection (1 : HomogeneousLocalization.Away Grading
    (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)) = 1 := by
  apply tripleOpen.topIso.commRingCatIsoToRingEquiv.injective
  change tripleOpen.topIso.hom (tripleOpen.topIso.inv (tripleGlobalSection 1)) =
    tripleOpen.topIso.hom 1
  rw [map_one]
  have h := ConcreteCategory.congr_hom tripleOpen.topIso.inv_hom_id (tripleGlobalSection 1)
  change tripleOpen.topIso.hom (tripleOpen.topIso.inv (tripleGlobalSection 1)) =
    tripleGlobalSection 1 at h
  rw [h]
  change (Proj.basicOpenIsoAway Grading (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)
    tripleEquation_homogeneous (by norm_num)).hom 1 = 1
  exact map_one _

lemma tripleSection01_mul_inverse :
    tripleSection triple01Element * tripleSection triple01InverseElement = 1 := by
  rw [← tripleSection_mul, triple01Element_mul_inverse]
  exact tripleSection_one

lemma tripleSection02_mul_inverse :
    tripleSection triple02Element * tripleSection triple02InverseElement = 1 := by
  rw [← tripleSection_mul, triple02Element_mul_inverse]
  exact tripleSection_one

lemma tripleSection12_mul_inverse :
    tripleSection triple12Element * tripleSection triple12InverseElement = 1 := by
  rw [← tripleSection_mul, triple12Element_mul_inverse]
  exact tripleSection_one

/-- A regular function whose product with another is one has no zero on analytic points. -/
lemma evaluate_ne_zero_of_mul_eq_one {U : plane.Opens} (s t : Γ(U.toScheme, ⊤))
    (h : s * t = 1) (z : ComplexPoint (openScheme analyticPlane U)) :
    Point.evaluate ⊤ s z ≠ 0 := by
  intro hz
  have heval := congrArg (fun u ↦ (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom u) h
  have hmul := map_mul (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom s t
  have hs : (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom s = Point.evaluate ⊤ s z :=
    Point.evaluationHom_apply ⊤ ⟨z, trivial⟩ s
  have ht : (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom t = Point.evaluate ⊤ t z :=
    Point.evaluationHom_apply ⊤ ⟨z, trivial⟩ t
  have hprod : Point.evaluate ⊤ s z * Point.evaluate ⊤ t z = 1 := by
    rw [← hs, ← ht]
    exact hmul.symm.trans (heval.trans (map_one _))
  rw [hz, zero_mul] at hprod
  exact zero_ne_one hprod

/-- The three transition functions as literal continuous functions on analytic triple overlap. -/
def triple01Value : ComplexPoint analyticTriple → ℂ :=
  Point.evaluate ⊤ (tripleSection triple01Element)

def triple02Value : ComplexPoint analyticTriple → ℂ :=
  Point.evaluate ⊤ (tripleSection triple02Element)

def triple12Value : ComplexPoint analyticTriple → ℂ :=
  Point.evaluate ⊤ (tripleSection triple12Element)

lemma continuous_triple01Value : Continuous triple01Value :=
  continuous_evaluate_top (X := analyticTriple) (tripleSection triple01Element)

lemma continuous_triple02Value : Continuous triple02Value :=
  continuous_evaluate_top (X := analyticTriple) (tripleSection triple02Element)

lemma continuous_triple12Value : Continuous triple12Value :=
  continuous_evaluate_top (X := analyticTriple) (tripleSection triple12Element)

lemma triple01Value_ne_zero (z : ComplexPoint analyticTriple) : triple01Value z ≠ 0 :=
  evaluate_ne_zero_of_mul_eq_one (tripleSection triple01Element)
    (tripleSection triple01InverseElement) tripleSection01_mul_inverse z

lemma triple02Value_ne_zero (z : ComplexPoint analyticTriple) : triple02Value z ≠ 0 :=
  evaluate_ne_zero_of_mul_eq_one (tripleSection triple02Element)
    (tripleSection triple02InverseElement) tripleSection02_mul_inverse z

lemma triple12Value_ne_zero (z : ComplexPoint analyticTriple) : triple12Value z ≠ 0 :=
  evaluate_ne_zero_of_mul_eq_one (tripleSection triple12Element)
    (tripleSection triple12InverseElement) tripleSection12_mul_inverse z

lemma tripleValue_transition (z : ComplexPoint analyticTriple) :
    triple02Value z = triple01Value z * triple12Value z := by
  have heval := congrArg (fun u ↦ (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom u)
    tripleSection02_eq_section01_mul_section12
  have hmul := map_mul (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom
    (tripleSection triple01Element) (tripleSection triple12Element)
  have h01 : (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom (tripleSection triple01Element) =
      triple01Value z :=
    Point.evaluationHom_apply ⊤ ⟨z, trivial⟩ (tripleSection triple01Element)
  have h02 : (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom (tripleSection triple02Element) =
      triple02Value z :=
    Point.evaluationHom_apply ⊤ ⟨z, trivial⟩ (tripleSection triple02Element)
  have h12 : (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom (tripleSection triple12Element) =
      triple12Value z :=
    Point.evaluationHom_apply ⊤ ⟨z, trivial⟩ (tripleSection triple12Element)
  calc
    triple02Value z = (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom
        (tripleSection triple01Element * tripleSection triple12Element) := h02.symm.trans heval
    _ = (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom (tripleSection triple01Element) *
        (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom (tripleSection triple12Element) := hmul
    _ = triple01Value z * triple12Value z := by rw [h01, h12]

/-- The analytic triple overlap as a `TopCat`, for the singular-cochain construction. -/
abbrev analyticTripleTop : TopCat := TopCat.of (ComplexPoint analyticTriple)

/-- The three standard affine analytic opens of the direct projective-plane model. -/
def projectiveCover (i : Fin 3) : Set (ComplexPoint analyticPlane) :=
  Point.overOpen (chartOpen i)

lemma isOpen_projectiveCover (i : Fin 3) : IsOpen (projectiveCover i) :=
  Point.isOpen_overOpen (X := analyticPlane) (chartOpen i)

/-- The three standard affine opens cover the analytic points of the direct `Proj` projective
plane. -/
lemma iUnion_projectiveCover : ⋃ i : Fin 3, projectiveCover i = Set.univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  have hz : z.underlying ∈ ⨆ i : Fin 3, Proj.basicOpen Grading (MvPolynomial.X i) := by
    rw [Other.ProjectiveChart.iSup_basicOpen_X_eq_top ℂ 2]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  exact ⟨i, hi⟩

/-- The normalized singular Čech chains of the three actual standard projective opens compute
the singular chains of the direct `Proj` analytification.  This is the global comparison that
will carry the literal transition cocycle to ordinary singular cohomology after dualization. -/
theorem projectiveCover_normalizedCechToSingular_quasiIso :
    QuasiIso
      (AlgebraicTopology.Singular.openCoverNormalizedCechTotalToSingular
        (TopCat.of (ComplexPoint analyticPlane)) projectiveCover) :=
  AlgebraicTopology.Singular.openCoverNormalizedCechTotalToSingular_quasiIso
    (TopCat.of (ComplexPoint analyticPlane)) projectiveCover
    isOpen_projectiveCover iUnion_projectiveCover

/-- The same normalized three-chart comparison with rational coefficients.  Its linear dual is
the cochain complex into which the displayed coordinate winding cocycle will be placed. -/
theorem projectiveCover_rationalNormalizedCechToSingular_quasiIso :
    QuasiIso
      (AlgebraicTopology.Singular.rationalOpenCoverNormalizedCechTotalToSingular
        (TopCat.of (ComplexPoint analyticPlane)) projectiveCover) :=
  AlgebraicTopology.Singular.rationalOpenCoverNormalizedCechTotalToSingular_quasiIso
    (TopCat.of (ComplexPoint analyticPlane)) projectiveCover
    isOpen_projectiveCover iUnion_projectiveCover

/-- The genuine `01` intersection `D₊(X₀X₁)`. -/
def pair01Open : plane.Opens :=
  Proj.basicOpen Grading (MvPolynomial.X 0 * MvPolynomial.X 1)

/-- The genuine `02` intersection `D₊(X₀X₂)`. -/
def pair02Open : plane.Opens :=
  Proj.basicOpen Grading (MvPolynomial.X 0 * MvPolynomial.X 2)

abbrev analyticPair01 : Over (Spec ↧ℂ) :=
  openScheme analyticPlane pair01Open

abbrev analyticPair02 : Over (Spec ↧ℂ) :=
  openScheme analyticPlane pair02Open

lemma pair01Equation_homogeneous :
    (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ) ∈ Grading 2 := by
  simpa using SetLike.mul_mem_graded coordinateZero_homogeneous coordinateOne_homogeneous

lemma pair02Equation_homogeneous :
    (MvPolynomial.X 0 * MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ) ∈ Grading 2 := by
  simpa using SetLike.mul_mem_graded coordinateZero_homogeneous coordinateTwo_homogeneous

lemma coordinateZeroSquare_homogeneous :
    (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 3) ℂ) ∈ Grading 2 := by
  simpa [pow_two] using SetLike.mul_mem_graded coordinateZero_homogeneous
    coordinateZero_homogeneous

/-- `X₁/X₀` on the actual pair intersection `D₊(X₀X₁)`. -/
def pair01Element :
    HomogeneousLocalization.Away Grading (MvPolynomial.X 0 * MvPolynomial.X 1) :=
  HomogeneousLocalization.Away.mk Grading pair01Equation_homogeneous 1
    (MvPolynomial.X 1 ^ 2) coordinateOneSquare_homogeneous

/-- Its displayed inverse `X₀/X₁`. -/
def pair01InverseElement :
    HomogeneousLocalization.Away Grading (MvPolynomial.X 0 * MvPolynomial.X 1) :=
  HomogeneousLocalization.Away.mk Grading pair01Equation_homogeneous 1
    (MvPolynomial.X 0 ^ 2) coordinateZeroSquare_homogeneous

/-- `X₂/X₀` on the actual pair intersection `D₊(X₀X₂)`. -/
def pair02Element :
    HomogeneousLocalization.Away Grading (MvPolynomial.X 0 * MvPolynomial.X 2) :=
  HomogeneousLocalization.Away.mk Grading pair02Equation_homogeneous 1
    (MvPolynomial.X 2 ^ 2) coordinateTwoSquare_homogeneous

/-- Its displayed inverse `X₀/X₂`. -/
def pair02InverseElement :
    HomogeneousLocalization.Away Grading (MvPolynomial.X 0 * MvPolynomial.X 2) :=
  HomogeneousLocalization.Away.mk Grading pair02Equation_homogeneous 1
    (MvPolynomial.X 0 ^ 2) coordinateZeroSquare_homogeneous

lemma pair01Element_mul_inverse : pair01Element * pair01InverseElement = 1 := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1))
  dsimp [pair01Element, pair01InverseElement]
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  use 1
  simp
  ring

lemma pair02Element_mul_inverse : pair02Element * pair02InverseElement = 1 := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 2))
  dsimp [pair02Element, pair02InverseElement]
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  use 1
  simp
  ring

def pair01GlobalSection
    (x : HomogeneousLocalization.Away Grading (MvPolynomial.X 0 * MvPolynomial.X 1)) :
    Γ(plane, pair01Open) := by
  change Γ(Proj Grading, Proj.basicOpen Grading (MvPolynomial.X 0 * MvPolynomial.X 1))
  exact (Proj.basicOpenIsoAway Grading (MvPolynomial.X 0 * MvPolynomial.X 1)
    pair01Equation_homogeneous (by norm_num)).hom x

def pair02GlobalSection
    (x : HomogeneousLocalization.Away Grading (MvPolynomial.X 0 * MvPolynomial.X 2)) :
    Γ(plane, pair02Open) := by
  change Γ(Proj Grading, Proj.basicOpen Grading (MvPolynomial.X 0 * MvPolynomial.X 2))
  exact (Proj.basicOpenIsoAway Grading (MvPolynomial.X 0 * MvPolynomial.X 2)
    pair02Equation_homogeneous (by norm_num)).hom x

def pair01Section
    (x : HomogeneousLocalization.Away Grading (MvPolynomial.X 0 * MvPolynomial.X 1)) :
    Γ(pair01Open.toScheme, ⊤) :=
  pair01Open.topIso.inv (pair01GlobalSection x)

def pair02Section
    (x : HomogeneousLocalization.Away Grading (MvPolynomial.X 0 * MvPolynomial.X 2)) :
    Γ(pair02Open.toScheme, ⊤) :=
  pair02Open.topIso.inv (pair02GlobalSection x)

lemma pair01Section_mul
    (x y : HomogeneousLocalization.Away Grading (MvPolynomial.X 0 * MvPolynomial.X 1)) :
    pair01Section (x * y) = pair01Section x * pair01Section y := by
  apply pair01Open.topIso.commRingCatIsoToRingEquiv.injective
  change pair01Open.topIso.hom (pair01Open.topIso.inv (pair01GlobalSection (x * y))) =
    pair01Open.topIso.hom
      (pair01Open.topIso.inv (pair01GlobalSection x) * pair01Open.topIso.inv (pair01GlobalSection y))
  rw [map_mul]
  have hxy := ConcreteCategory.congr_hom pair01Open.topIso.inv_hom_id
    (pair01GlobalSection (x * y))
  have hx := ConcreteCategory.congr_hom pair01Open.topIso.inv_hom_id (pair01GlobalSection x)
  have hy := ConcreteCategory.congr_hom pair01Open.topIso.inv_hom_id (pair01GlobalSection y)
  change pair01Open.topIso.hom (pair01Open.topIso.inv (pair01GlobalSection (x * y))) =
    pair01GlobalSection (x * y) at hxy
  change pair01Open.topIso.hom (pair01Open.topIso.inv (pair01GlobalSection x)) =
    pair01GlobalSection x at hx
  change pair01Open.topIso.hom (pair01Open.topIso.inv (pair01GlobalSection y)) =
    pair01GlobalSection y at hy
  rw [hxy, hx, hy]
  change (Proj.basicOpenIsoAway Grading (MvPolynomial.X 0 * MvPolynomial.X 1)
    pair01Equation_homogeneous (by norm_num)).hom (x * y) = _
  exact map_mul _ _ _

lemma pair02Section_mul
    (x y : HomogeneousLocalization.Away Grading (MvPolynomial.X 0 * MvPolynomial.X 2)) :
    pair02Section (x * y) = pair02Section x * pair02Section y := by
  apply pair02Open.topIso.commRingCatIsoToRingEquiv.injective
  change pair02Open.topIso.hom (pair02Open.topIso.inv (pair02GlobalSection (x * y))) =
    pair02Open.topIso.hom
      (pair02Open.topIso.inv (pair02GlobalSection x) * pair02Open.topIso.inv (pair02GlobalSection y))
  rw [map_mul]
  have hxy := ConcreteCategory.congr_hom pair02Open.topIso.inv_hom_id
    (pair02GlobalSection (x * y))
  have hx := ConcreteCategory.congr_hom pair02Open.topIso.inv_hom_id (pair02GlobalSection x)
  have hy := ConcreteCategory.congr_hom pair02Open.topIso.inv_hom_id (pair02GlobalSection y)
  change pair02Open.topIso.hom (pair02Open.topIso.inv (pair02GlobalSection (x * y))) =
    pair02GlobalSection (x * y) at hxy
  change pair02Open.topIso.hom (pair02Open.topIso.inv (pair02GlobalSection x)) =
    pair02GlobalSection x at hx
  change pair02Open.topIso.hom (pair02Open.topIso.inv (pair02GlobalSection y)) =
    pair02GlobalSection y at hy
  rw [hxy, hx, hy]
  change (Proj.basicOpenIsoAway Grading (MvPolynomial.X 0 * MvPolynomial.X 2)
    pair02Equation_homogeneous (by norm_num)).hom (x * y) = _
  exact map_mul _ _ _

lemma pair01Section_one : pair01Section
    (1 : HomogeneousLocalization.Away Grading (MvPolynomial.X 0 * MvPolynomial.X 1)) = 1 := by
  apply pair01Open.topIso.commRingCatIsoToRingEquiv.injective
  change pair01Open.topIso.hom (pair01Open.topIso.inv (pair01GlobalSection 1)) =
    pair01Open.topIso.hom 1
  rw [map_one]
  have h := ConcreteCategory.congr_hom pair01Open.topIso.inv_hom_id (pair01GlobalSection 1)
  change pair01Open.topIso.hom (pair01Open.topIso.inv (pair01GlobalSection 1)) =
    pair01GlobalSection 1 at h
  rw [h]
  change (Proj.basicOpenIsoAway Grading (MvPolynomial.X 0 * MvPolynomial.X 1)
    pair01Equation_homogeneous (by norm_num)).hom 1 = 1
  exact map_one _

lemma pair02Section_one : pair02Section
    (1 : HomogeneousLocalization.Away Grading (MvPolynomial.X 0 * MvPolynomial.X 2)) = 1 := by
  apply pair02Open.topIso.commRingCatIsoToRingEquiv.injective
  change pair02Open.topIso.hom (pair02Open.topIso.inv (pair02GlobalSection 1)) =
    pair02Open.topIso.hom 1
  rw [map_one]
  have h := ConcreteCategory.congr_hom pair02Open.topIso.inv_hom_id (pair02GlobalSection 1)
  change pair02Open.topIso.hom (pair02Open.topIso.inv (pair02GlobalSection 1)) =
    pair02GlobalSection 1 at h
  rw [h]
  change (Proj.basicOpenIsoAway Grading (MvPolynomial.X 0 * MvPolynomial.X 2)
    pair02Equation_homogeneous (by norm_num)).hom 1 = 1
  exact map_one _

lemma pair01Section_mul_inverse :
    pair01Section pair01Element * pair01Section pair01InverseElement = 1 := by
  rw [← pair01Section_mul, pair01Element_mul_inverse]
  exact pair01Section_one

lemma pair02Section_mul_inverse :
    pair02Section pair02Element * pair02Section pair02InverseElement = 1 := by
  rw [← pair02Section_mul, pair02Element_mul_inverse]
  exact pair02Section_one

def pair01Value : ComplexPoint analyticPair01 → ℂ :=
  Point.evaluate ⊤ (pair01Section pair01Element)

def pair02Value : ComplexPoint analyticPair02 → ℂ :=
  Point.evaluate ⊤ (pair02Section pair02Element)

lemma continuous_pair01Value : Continuous pair01Value :=
  continuous_evaluate_top (X := analyticPair01) (pair01Section pair01Element)

lemma continuous_pair02Value : Continuous pair02Value :=
  continuous_evaluate_top (X := analyticPair02) (pair02Section pair02Element)

lemma pair01Value_ne_zero (z : ComplexPoint analyticPair01) : pair01Value z ≠ 0 :=
  evaluate_ne_zero_of_mul_eq_one (pair01Section pair01Element)
    (pair01Section pair01InverseElement) pair01Section_mul_inverse z

lemma pair02Value_ne_zero (z : ComplexPoint analyticPair02) : pair02Value z ≠ 0 :=
  evaluate_ne_zero_of_mul_eq_one (pair02Section pair02Element)
    (pair02Section pair02InverseElement) pair02Section_mul_inverse z

/-- The corresponding concrete continuous functions on the two genuine pair intersections. -/
def pair01Transition : C(TopCat.of (ComplexPoint analyticPair01), ℂ) :=
  ⟨pair01Value, continuous_pair01Value⟩

def pair02Transition : C(TopCat.of (ComplexPoint analyticPair02), ℂ) :=
  ⟨pair02Value, continuous_pair02Value⟩

lemma pair01Transition_ne_zero : ∀ z, pair01Transition z ≠ 0 := pair01Value_ne_zero

lemma pair02Transition_ne_zero : ∀ z, pair02Transition z ≠ 0 := pair02Value_ne_zero

/-- `X₂/X₁` on the genuine `12` pair intersection (the inverse of the unit already used for
the transition between the two affine normal coordinates). -/
def pair12Value : ComplexPoint analyticOverlap → ℂ :=
  Point.evaluate ⊤ overlapUnitInverseSection

lemma continuous_pair12Value : Continuous pair12Value :=
  continuous_evaluate_top (X := analyticOverlap) overlapUnitInverseSection

lemma pair12Value_ne_zero (z : ComplexPoint analyticOverlap) : pair12Value z ≠ 0 := by
  apply evaluate_ne_zero_of_mul_eq_one overlapUnitInverseSection overlapUnitSection _ z
  rw [mul_comm, overlapUnitSection_mul_inverse]

def pair12Transition : C(TopCat.of (ComplexPoint analyticOverlap), ℂ) :=
  ⟨pair12Value, continuous_pair12Value⟩

lemma pair12Transition_ne_zero : ∀ z, pair12Transition z ≠ 0 := pair12Value_ne_zero

/-- The triple intersection is contained in the genuine `01` intersection. -/
lemma tripleOpen_le_pair01 : tripleOpen ≤ pair01Open := by
  exact Proj.basicOpen_mono Grading (MvPolynomial.X 0 * MvPolynomial.X 1)
    (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) ⟨MvPolynomial.X 2, rfl⟩

/-- The triple intersection is contained in the genuine `02` intersection. -/
lemma tripleOpen_le_pair02 : tripleOpen ≤ pair02Open := by
  exact Proj.basicOpen_mono Grading (MvPolynomial.X 0 * MvPolynomial.X 2)
    (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)
    ⟨MvPolynomial.X 1, by ring⟩

/-- The triple intersection is contained in the existing `12` intersection. -/
lemma tripleOpen_le_overlap : tripleOpen ≤ overlapOpen := by
  exact Proj.basicOpen_mono Grading (MvPolynomial.X 1 * MvPolynomial.X 2)
    (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)
    ⟨MvPolynomial.X 0, by ring⟩

/-- The map from the triple intersection to the actual `01` pair intersection. -/
def tripleToPair01Over : analyticTriple ⟶ analyticPair01 :=
  Over.homMk (plane.homOfLE tripleOpen_le_pair01) (by
    dsimp [analyticTriple, analyticPair01, analyticPlane, openScheme]
    rw [← Category.assoc, Scheme.homOfLE_ι])

/-- The map from the triple intersection to the actual `02` pair intersection. -/
def tripleToPair02Over : analyticTriple ⟶ analyticPair02 :=
  Over.homMk (plane.homOfLE tripleOpen_le_pair02) (by
    dsimp [analyticTriple, analyticPair02, analyticPlane, openScheme]
    rw [← Category.assoc, Scheme.homOfLE_ι])

/-- The map from the triple intersection to the actual `12` pair intersection. -/
def tripleToOverlapOver : analyticTriple ⟶ analyticOverlap :=
  Over.homMk (plane.homOfLE tripleOpen_le_overlap) (by
    dsimp [analyticTriple, analyticOverlap, analyticPlane, openScheme]
    rw [← Category.assoc, Scheme.homOfLE_ι])

def tripleToPair01 : ComplexPoint analyticTriple → ComplexPoint analyticPair01 :=
  Point.map tripleToPair01Over

def tripleToPair02 : ComplexPoint analyticTriple → ComplexPoint analyticPair02 :=
  Point.map tripleToPair02Over

def tripleToOverlap : ComplexPoint analyticTriple → ComplexPoint analyticOverlap :=
  Point.map tripleToOverlapOver

lemma continuous_tripleToPair01 : Continuous tripleToPair01 :=
  Point.continuous_map tripleToPair01Over

lemma continuous_tripleToPair02 : Continuous tripleToPair02 :=
  Point.continuous_map tripleToPair02Over

lemma continuous_tripleToOverlap : Continuous tripleToOverlap :=
  Point.continuous_map tripleToOverlapOver

/-- The literal image of the `01` fraction after inverting `X₂`. -/
def pair01RestrictionElement : HomogeneousLocalization.Away Grading
    (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) :=
  HomogeneousLocalization.awayMap
    (f := MvPolynomial.X 0 * MvPolynomial.X 1)
    (x := MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)
    Grading coordinateTwo_homogeneous rfl pair01Element

/-- Localizing the `01` fraction further at `X₂` gives the displayed triple fraction. -/
lemma triple01Element_eq_pair01Restriction :
    triple01Element = pair01RestrictionElement := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2))
  dsimp [triple01Element, pair01RestrictionElement, pair01Element]
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  use 1
  simp

/-- The literal image of the `02` fraction after inverting `X₁`. -/
def pair02RestrictionElement : HomogeneousLocalization.Away Grading
    (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) :=
  HomogeneousLocalization.awayMap
    (f := MvPolynomial.X 0 * MvPolynomial.X 2)
    (x := MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)
    Grading coordinateOne_homogeneous (by ac_rfl) pair02Element

/-- Localizing the `02` fraction further at `X₁` gives the displayed triple fraction. -/
lemma triple02Element_eq_pair02Restriction :
    triple02Element = pair02RestrictionElement := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2))
  dsimp [triple02Element, pair02RestrictionElement, pair02Element]
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  use 1
  simp
  ring

/-- The literal image of the `12` fraction after inverting `X₀`. -/
def overlapRestrictionElement : HomogeneousLocalization.Away Grading
    (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) :=
  HomogeneousLocalization.awayMap
    (f := MvPolynomial.X 1 * MvPolynomial.X 2)
    (x := MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)
    Grading coordinateZero_homogeneous (by ac_rfl) overlapUnitInverseElement

/-- Localizing the `12` fraction further at `X₀` gives the displayed triple fraction. -/
lemma triple12Element_eq_overlapRestriction :
    triple12Element = overlapRestrictionElement := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2))
  dsimp [triple12Element, overlapRestrictionElement, overlapUnitInverseElement]
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  use 1
  simp
  ring

/-- Restriction from the `01` pair intersection to the triple intersection is the displayed
homogeneous-localization map. -/
lemma triple01_restriction_hom :
    CommRingCat.ofHom
        (HomogeneousLocalization.awayMap
          (f := MvPolynomial.X 0 * MvPolynomial.X 1)
          (x := MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)
          Grading coordinateTwo_homogeneous rfl) ≫
      Proj.awayToSection Grading (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) =
        Proj.awayToSection Grading (MvPolynomial.X 0 * MvPolynomial.X 1) ≫
          plane.presheaf.map (homOfLE tripleOpen_le_pair01).op := by
  exact Proj.awayMap_awayToSection Grading coordinateTwo_homogeneous rfl

/-- Restriction from the `02` pair intersection to the triple intersection is the displayed
homogeneous-localization map. -/
lemma triple02_restriction_hom :
    CommRingCat.ofHom
        (HomogeneousLocalization.awayMap
          (f := MvPolynomial.X 0 * MvPolynomial.X 2)
          (x := MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)
          Grading coordinateOne_homogeneous (by ac_rfl)) ≫
      Proj.awayToSection Grading (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) =
        Proj.awayToSection Grading (MvPolynomial.X 0 * MvPolynomial.X 2) ≫
          plane.presheaf.map (homOfLE tripleOpen_le_pair02).op := by
  exact Proj.awayMap_awayToSection Grading coordinateOne_homogeneous (by ac_rfl)

/-- Restriction from the `12` pair intersection to the triple intersection is the displayed
homogeneous-localization map. -/
lemma triple12_restriction_hom :
    CommRingCat.ofHom
        (HomogeneousLocalization.awayMap
          (f := MvPolynomial.X 1 * MvPolynomial.X 2)
          (x := MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)
          Grading coordinateZero_homogeneous (by ac_rfl)) ≫
      Proj.awayToSection Grading (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2) =
        Proj.awayToSection Grading (MvPolynomial.X 1 * MvPolynomial.X 2) ≫
          plane.presheaf.map (homOfLE tripleOpen_le_overlap).op := by
  exact Proj.awayMap_awayToSection Grading coordinateZero_homogeneous (by ac_rfl)

lemma triple01GlobalSection_eq_restrictPair01 :
    tripleGlobalSection triple01Element =
      plane.presheaf.map (homOfLE tripleOpen_le_pair01).op
        (pair01GlobalSection pair01Element) := by
  rw [triple01Element_eq_pair01Restriction]
  change
    (CommRingCat.ofHom
        (HomogeneousLocalization.awayMap
          (f := MvPolynomial.X 0 * MvPolynomial.X 1)
          (x := MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)
          Grading coordinateTwo_homogeneous rfl) ≫
      Proj.awayToSection Grading (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)).hom
        pair01Element =
      (Proj.awayToSection Grading (MvPolynomial.X 0 * MvPolynomial.X 1) ≫
        plane.presheaf.map (homOfLE tripleOpen_le_pair01).op).hom pair01Element
  rw [triple01_restriction_hom]
  rfl

lemma triple02GlobalSection_eq_restrictPair02 :
    tripleGlobalSection triple02Element =
      plane.presheaf.map (homOfLE tripleOpen_le_pair02).op
        (pair02GlobalSection pair02Element) := by
  rw [triple02Element_eq_pair02Restriction]
  change
    (CommRingCat.ofHom
        (HomogeneousLocalization.awayMap
          (f := MvPolynomial.X 0 * MvPolynomial.X 2)
          (x := MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)
          Grading coordinateOne_homogeneous (by ac_rfl)) ≫
      Proj.awayToSection Grading (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)).hom
        pair02Element =
      (Proj.awayToSection Grading (MvPolynomial.X 0 * MvPolynomial.X 2) ≫
        plane.presheaf.map (homOfLE tripleOpen_le_pair02).op).hom pair02Element
  rw [triple02_restriction_hom]
  rfl

lemma triple12GlobalSection_eq_restrictOverlap :
    tripleGlobalSection triple12Element =
      plane.presheaf.map (homOfLE tripleOpen_le_overlap).op overlapUnitInverseGlobalSection := by
  rw [triple12Element_eq_overlapRestriction]
  change
    (CommRingCat.ofHom
        (HomogeneousLocalization.awayMap
          (f := MvPolynomial.X 1 * MvPolynomial.X 2)
          (x := MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)
          Grading coordinateZero_homogeneous (by ac_rfl)) ≫
      Proj.awayToSection Grading (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)).hom
        overlapUnitInverseElement =
      (Proj.awayToSection Grading (MvPolynomial.X 1 * MvPolynomial.X 2) ≫
        plane.presheaf.map (homOfLE tripleOpen_le_overlap).op).hom overlapUnitInverseElement
  rw [triple12_restriction_hom]
  rfl

lemma tripleToPair01Over_comp_openInclusion :
    tripleToPair01Over ≫ openInclusion analyticPlane pair01Open =
      openInclusion analyticPlane tripleOpen := by
  apply Over.OverMorphism.ext
  dsimp [tripleToPair01Over, analyticTriple, analyticPair01, analyticPlane, openScheme,
    openInclusion]
  exact Scheme.homOfLE_ι plane tripleOpen_le_pair01

lemma tripleToPair02Over_comp_openInclusion :
    tripleToPair02Over ≫ openInclusion analyticPlane pair02Open =
      openInclusion analyticPlane tripleOpen := by
  apply Over.OverMorphism.ext
  dsimp [tripleToPair02Over, analyticTriple, analyticPair02, analyticPlane, openScheme,
    openInclusion]
  exact Scheme.homOfLE_ι plane tripleOpen_le_pair02

lemma tripleToOverlapOver_comp_openInclusion :
    tripleToOverlapOver ≫ openInclusion analyticPlane overlapOpen =
      openInclusion analyticPlane tripleOpen := by
  apply Over.OverMorphism.ext
  dsimp [tripleToOverlapOver, analyticTriple, analyticOverlap, analyticPlane, openScheme,
    openInclusion]
  exact Scheme.homOfLE_ι plane tripleOpen_le_overlap

/-- On the triple intersection, the `01` pair function is the displayed fraction `X₁/X₀`. -/
lemma triple01Value_eq_pair01Value (z : ComplexPoint analyticTriple) :
    triple01Value z = pair01Value (tripleToPair01 z) := by
  change Point.evaluate ⊤ (tripleOpen.topIso.inv (tripleGlobalSection triple01Element)) z =
    Point.evaluate ⊤ (pair01Open.topIso.inv (pair01GlobalSection pair01Element))
      (Point.map tripleToPair01Over z)
  dsimp only [analyticTriple, analyticPair01, analyticPlane, openScheme] at z ⊢
  rw [evaluate_topIso_inv (X := Over.mk structureMap) tripleOpen
    (tripleGlobalSection triple01Element) z,
    evaluate_topIso_inv (X := Over.mk structureMap) pair01Open
      (pair01GlobalSection pair01Element) (Point.map tripleToPair01Over z)]
  rw [← Point.map_comp_apply, tripleToPair01Over_comp_openInclusion,
    triple01GlobalSection_eq_restrictPair01]
  exact (Point.evaluate_res tripleOpen_le_pair01 (pair01GlobalSection pair01Element)
    (Point.map (openInclusion analyticPlane tripleOpen) z)
    (openEquiv analyticPlane tripleOpen z).2).symm

/-- On the triple intersection, the `02` pair function is the displayed fraction `X₂/X₀`. -/
lemma triple02Value_eq_pair02Value (z : ComplexPoint analyticTriple) :
    triple02Value z = pair02Value (tripleToPair02 z) := by
  change Point.evaluate ⊤ (tripleOpen.topIso.inv (tripleGlobalSection triple02Element)) z =
    Point.evaluate ⊤ (pair02Open.topIso.inv (pair02GlobalSection pair02Element))
      (Point.map tripleToPair02Over z)
  dsimp only [analyticTriple, analyticPair02, analyticPlane, openScheme] at z ⊢
  rw [evaluate_topIso_inv (X := Over.mk structureMap) tripleOpen
    (tripleGlobalSection triple02Element) z,
    evaluate_topIso_inv (X := Over.mk structureMap) pair02Open
      (pair02GlobalSection pair02Element) (Point.map tripleToPair02Over z)]
  rw [← Point.map_comp_apply, tripleToPair02Over_comp_openInclusion,
    triple02GlobalSection_eq_restrictPair02]
  exact (Point.evaluate_res tripleOpen_le_pair02 (pair02GlobalSection pair02Element)
    (Point.map (openInclusion analyticPlane tripleOpen) z)
    (openEquiv analyticPlane tripleOpen z).2).symm

/-- On the triple intersection, the `12` pair function is the displayed fraction `X₂/X₁`. -/
lemma triple12Value_eq_pair12Value (z : ComplexPoint analyticTriple) :
    triple12Value z = pair12Value (tripleToOverlap z) := by
  change Point.evaluate ⊤ (tripleOpen.topIso.inv (tripleGlobalSection triple12Element)) z =
    Point.evaluate ⊤ (overlapOpen.topIso.inv overlapUnitInverseGlobalSection)
      (Point.map tripleToOverlapOver z)
  dsimp only [analyticTriple, analyticOverlap, analyticPlane, openScheme] at z ⊢
  rw [evaluate_topIso_inv (X := Over.mk structureMap) tripleOpen
    (tripleGlobalSection triple12Element) z,
    evaluate_topIso_inv (X := Over.mk structureMap) overlapOpen
      overlapUnitInverseGlobalSection (Point.map tripleToOverlapOver z)]
  rw [← Point.map_comp_apply, tripleToOverlapOver_comp_openInclusion,
    triple12GlobalSection_eq_restrictOverlap]
  exact (Point.evaluate_res tripleOpen_le_overlap overlapUnitInverseGlobalSection
    (Point.map (openInclusion analyticPlane tripleOpen) z)
    (openEquiv analyticPlane tripleOpen z).2).symm

/-- The literal continuous transition function `X₁/X₀` on the triple overlap. -/
def triple01Transition : C(analyticTripleTop, ℂ) :=
  ⟨triple01Value, continuous_triple01Value⟩

/-- The literal continuous transition function `X₂/X₀` on the triple overlap. -/
def triple02Transition : C(analyticTripleTop, ℂ) :=
  ⟨triple02Value, continuous_triple02Value⟩

/-- The literal continuous transition function `X₂/X₁` on the triple overlap. -/
def triple12Transition : C(analyticTripleTop, ℂ) :=
  ⟨triple12Value, continuous_triple12Value⟩

lemma triple01Transition_ne_zero : ∀ z, triple01Transition z ≠ 0 :=
  triple01Value_ne_zero

lemma triple02Transition_ne_zero : ∀ z, triple02Transition z ≠ 0 :=
  triple02Value_ne_zero

lemma triple12Transition_ne_zero : ∀ z, triple12Transition z ≠ 0 :=
  triple12Value_ne_zero

lemma tripleTransition_product : ∀ z,
    triple02Transition z = triple01Transition z * triple12Transition z :=
  tripleValue_transition

lemma triple01Transition_comp_id :
    triple01Transition.comp (ChernWinding.topMap (𝟙 analyticTripleTop)) = triple01Transition := by
  ext z
  rfl

lemma triple02Transition_comp_id :
    triple02Transition.comp (ChernWinding.topMap (𝟙 analyticTripleTop)) = triple02Transition := by
  ext z
  rfl

lemma triple12Transition_comp_id :
    triple12Transition.comp (ChernWinding.topMap (𝟙 analyticTripleTop)) = triple12Transition := by
  ext z
  rfl

/-- The three maps from the triple intersection to the genuine pair intersections, viewed as
continuous maps for singular cochains. -/
def tripleToPair01Top : analyticTripleTop ⟶ TopCat.of (ComplexPoint analyticPair01) :=
  TopCat.ofHom ⟨tripleToPair01, continuous_tripleToPair01⟩

def tripleToPair02Top : analyticTripleTop ⟶ TopCat.of (ComplexPoint analyticPair02) :=
  TopCat.ofHom ⟨tripleToPair02, continuous_tripleToPair02⟩

def tripleToOverlapTop : analyticTripleTop ⟶ TopCat.of (ComplexPoint analyticOverlap) :=
  TopCat.ofHom ⟨tripleToOverlap, continuous_tripleToOverlap⟩

lemma pair01Transition_restricts :
    pair01Transition.comp (ChernWinding.topMap tripleToPair01Top) = triple01Transition := by
  ext z
  change pair01Value (tripleToPair01 z) = triple01Value z
  exact (triple01Value_eq_pair01Value z).symm

lemma pair02Transition_restricts :
    pair02Transition.comp (ChernWinding.topMap tripleToPair02Top) = triple02Transition := by
  ext z
  change pair02Value (tripleToPair02 z) = triple02Value z
  exact (triple02Value_eq_pair02Value z).symm

lemma pair12Transition_restricts :
    pair12Transition.comp (ChernWinding.topMap tripleToOverlapTop) = triple12Transition := by
  ext z
  change pair12Value (tripleToOverlap z) = triple12Value z
  exact (triple12Value_eq_pair12Value z).symm

/-- The displayed degree-two cocycle, now with its three degree-one components on the three
genuine pair intersections of the standard cover of `ℙ²`. -/
def coordinateProjectiveCechCochain :
    (AlgebraicTopology.Singular.threeOpenCechTransitionTotal
      (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair01Top)
      (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair02Top)
      (AlgebraicTopology.Singular.CechWinding.pullback tripleToOverlapTop)).X 0 :=
  AlgebraicTopology.Singular.CechWinding.threeOpenWindingTransitionCochain
    tripleToPair01Top tripleToPair02Top tripleToOverlapTop
    pair01Transition pair02Transition pair12Transition
    pair01Transition_ne_zero pair02Transition_ne_zero pair12Transition_ne_zero
    triple01Transition triple12Transition triple02Transition
    triple01Transition_ne_zero triple12Transition_ne_zero triple02Transition_ne_zero
    tripleTransition_product

/-- The actual three-chart coordinate cochain is closed before any passage to cohomology. -/
lemma coordinateProjectiveCechCochain_closed :
    (AlgebraicTopology.Singular.threeOpenCechTransitionTotal
      (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair01Top)
      (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair02Top)
      (AlgebraicTopology.Singular.CechWinding.pullback tripleToOverlapTop)).d 0 1
      coordinateProjectiveCechCochain = 0 :=
  AlgebraicTopology.Singular.CechWinding.threeOpenWindingTransitionCochain_closed
    tripleToPair01Top tripleToPair02Top tripleToOverlapTop
    pair01Transition pair02Transition pair12Transition
    pair01Transition_ne_zero pair02Transition_ne_zero pair12Transition_ne_zero
    triple01Transition triple12Transition triple02Transition
    triple01Transition_ne_zero triple12Transition_ne_zero triple02Transition_ne_zero
    tripleTransition_product pair01Transition_restricts pair02Transition_restricts
    pair12Transition_restricts

/-- The actual coordinate cochain factored through the cycle object of the three-chart
Čech--singular transition complex. -/
def coordinateProjectiveCechCocycle :
    ModuleCat.of ℚ ℚ ⟶
      (AlgebraicTopology.Singular.threeOpenCechTransitionTotal
        (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair01Top)
        (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair02Top)
        (AlgebraicTopology.Singular.CechWinding.pullback tripleToOverlapTop)).cycles 0 :=
  (AlgebraicTopology.Singular.threeOpenCechTransitionTotal
    (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair01Top)
    (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair02Top)
    (AlgebraicTopology.Singular.CechWinding.pullback tripleToOverlapTop)).liftCycles
      (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ coordinateProjectiveCechCochain)) 1
      (by norm_num) (by
        ext
        change (AlgebraicTopology.Singular.threeOpenCechTransitionTotal
          (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair01Top)
          (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair02Top)
          (AlgebraicTopology.Singular.CechWinding.pullback tripleToOverlapTop)).d 0 1
            (LinearMap.toSpanSingleton ℚ _ coordinateProjectiveCechCochain 1) = 0
        rw [LinearMap.toSpanSingleton_apply]
        simpa using coordinateProjectiveCechCochain_closed)

/-- Forgetting the cycle factorization recovers the displayed raw cochain exactly. -/
lemma coordinateProjectiveCechCocycle_iCycles :
    coordinateProjectiveCechCocycle ≫
      (AlgebraicTopology.Singular.threeOpenCechTransitionTotal
        (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair01Top)
        (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair02Top)
        (AlgebraicTopology.Singular.CechWinding.pullback tripleToOverlapTop)).iCycles 0 =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ coordinateProjectiveCechCochain) := by
  apply (AlgebraicTopology.Singular.threeOpenCechTransitionTotal
    (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair01Top)
    (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair02Top)
    (AlgebraicTopology.Singular.CechWinding.pullback tripleToOverlapTop)).liftCycles_i

/-- The cohomology class of the literal three-chart coordinate cocycle. -/
def coordinateProjectiveCechClass :
    (AlgebraicTopology.Singular.threeOpenCechTransitionTotal
      (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair01Top)
      (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair02Top)
      (AlgebraicTopology.Singular.CechWinding.pullback tripleToOverlapTop)).homology 0 :=
  (coordinateProjectiveCechCocycle ≫
    (AlgebraicTopology.Singular.threeOpenCechTransitionTotal
      (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair01Top)
      (AlgebraicTopology.Singular.CechWinding.pullback tripleToPair02Top)
      (AlgebraicTopology.Singular.CechWinding.pullback tripleToOverlapTop)).homologyπ 0).hom 1

/-- A fully displayed degree-two Čech--singular transition cochain coming from the three
coordinate ratios of the direct `Proj` projective plane.  The three pair-overlap slots are
represented on their common triple overlap; the final slot is the explicit principal-log
branch-jump cochain. -/
def coordinateTripleCechCochain :
    (AlgebraicTopology.Singular.threeOpenCechTransitionTotal
      (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))
      (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))
      (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))).X 0 :=
  AlgebraicTopology.Singular.CechWinding.threeOpenWindingTransitionCochain
    (𝟙 analyticTripleTop) (𝟙 analyticTripleTop) (𝟙 analyticTripleTop)
    triple01Transition triple02Transition triple12Transition
    triple01Transition_ne_zero triple02Transition_ne_zero triple12Transition_ne_zero
    triple01Transition triple12Transition triple02Transition
    triple01Transition_ne_zero triple12Transition_ne_zero triple02Transition_ne_zero
    tripleTransition_product

/-- The direct coordinate Čech--singular transition cochain is closed before passing to any
cohomology group. -/
lemma coordinateTripleCechCochain_closed :
    (AlgebraicTopology.Singular.threeOpenCechTransitionTotal
      (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))
      (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))
      (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))).d 0 1
      coordinateTripleCechCochain = 0 :=
  AlgebraicTopology.Singular.CechWinding.threeOpenWindingTransitionCochain_closed
    (𝟙 analyticTripleTop) (𝟙 analyticTripleTop) (𝟙 analyticTripleTop)
    triple01Transition triple02Transition triple12Transition
    triple01Transition_ne_zero triple02Transition_ne_zero triple12Transition_ne_zero
    triple01Transition triple12Transition triple02Transition
    triple01Transition_ne_zero triple12Transition_ne_zero triple02Transition_ne_zero
    tripleTransition_product triple01Transition_comp_id triple02Transition_comp_id
    triple12Transition_comp_id

/-- The explicit coordinate transition cochain factored through the cycle object of its
Čech--singular total complex. -/
def coordinateTripleCechCocycle :
    ModuleCat.of ℚ ℚ ⟶
      (AlgebraicTopology.Singular.threeOpenCechTransitionTotal
        (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))
        (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))
        (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))).cycles 0 :=
  (AlgebraicTopology.Singular.threeOpenCechTransitionTotal
    (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))
    (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))
    (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))).liftCycles
      (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ coordinateTripleCechCochain)) 1
      (by norm_num) (by
        ext
        change (AlgebraicTopology.Singular.threeOpenCechTransitionTotal
          (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))
          (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))
          (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))).d 0 1
            (LinearMap.toSpanSingleton ℚ _ coordinateTripleCechCochain 1) = 0
        rw [LinearMap.toSpanSingleton_apply]
        simpa using coordinateTripleCechCochain_closed)

/-- The degree-two coordinate-transition class in the literal Čech--singular total model.
The mapping-cone index is `0`: the three displayed pair cochains are degree one and live in
Čech degree one. -/
def coordinateTripleCechClass :
    (AlgebraicTopology.Singular.threeOpenCechTransitionTotal
      (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))
      (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))
      (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))).homology 0 :=
  (coordinateTripleCechCocycle ≫
    (AlgebraicTopology.Singular.threeOpenCechTransitionTotal
      (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))
      (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))
      (AlgebraicTopology.Singular.CechWinding.pullback (𝟙 analyticTripleTop))).homologyπ 0).hom 1
