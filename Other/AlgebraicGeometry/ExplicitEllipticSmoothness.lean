/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticIntegrality
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Smoothness of the explicit projective cubic

Explicit Bézout identities show that the coordinate partial derivatives cover both curve charts.
Localizing their presentations at those derivatives gives standard smooth algebras of relative
dimension one. The chart isomorphisms respect the original map to `Spec ℂ`, so they establish
smoothness of the actual projective cubic and of its self-product.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial

namespace AlgebraicGeometry.ExplicitEllipticCandidate

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Inverting the Jacobian of a finite presubmersive presentation produces a standard
smooth algebra of the presentation's relative dimension. -/
theorem standardSmooth_localizationJacobian {R S ι σ : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Finite ι] [Finite σ] (P : Algebra.PreSubmersivePresentation R S ι σ) :
    Algebra.IsStandardSmoothOfRelativeDimension P.dimension R (Localization.Away P.jacobian) := by
  let Q := Algebra.PreSubmersivePresentation.localizationAway (Localization.Away P.jacobian)
    P.jacobian
  let E : Algebra.SubmersivePresentation R (Localization.Away P.jacobian) (Unit ⊕ ι) (Unit ⊕ σ) :=
    { Q.comp P with
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian]
        dsimp only [Q]
        rw [Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
        exact (IsLocalization.Away.algebraMap_isUnit P.jacobian).mul
          (IsLocalization.Away.algebraMap_isUnit P.jacobian) }
  apply E.isStandardSmoothOfRelativeDimension
  change (Q.comp P).dimension = _
  rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  simp [Algebra.Presentation.dimension]

/-- The usual affine hypersurface coordinate ring. -/
abbrev HypersurfaceRing {R : Type*} [CommRing R] (f : MvPolynomial (Fin 2) R) :=
  MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range (fun _ : Unit => f))

/-- A one-equation presentation with a specified coordinate derivative. -/
def hypersurfacePresentation {R : Type*} [CommRing R] (f : MvPolynomial (Fin 2) R)
    (i : Fin 2) : Algebra.PreSubmersivePresentation R (HypersurfaceRing f) (Fin 2) Unit :=
  Algebra.PreSubmersivePresentation.naive (fun _ => i) (Function.injective_of_subsingleton _)

theorem hypersurfacePresentation_jacobian {R : Type*} [CommRing R]
    (f : MvPolynomial (Fin 2) R) (i : Fin 2) :
    (hypersurfacePresentation f i).jacobian =
      Ideal.Quotient.mk _ (pderiv i f) := by
  simp [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    hypersurfacePresentation]

/-- The Jacobian criterion for a two-variable affine hypersurface, retaining relative dimension. -/
theorem hypersurface_locally_standardSmooth {R : Type} [CommRing R]
    (f : MvPolynomial (Fin 2) R)
    (h : Ideal.span (Set.range (fun i => (hypersurfacePresentation f i).jacobian)) = ⊤) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (HypersurfaceRing f)) := by
  refine ⟨_, h, ?_⟩
  rintro _ ⟨i, rfl⟩
  rw [← IsScalarTower.algebraMap_eq,
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  convert standardSmooth_localizationJacobian (hypersurfacePresentation f i) using 1
  simp [Algebra.Presentation.dimension]

/-- A polynomial Bézout identity makes the coordinate Jacobians generate the unit ideal. -/
theorem hypersurface_jacobians_span_top {R : Type*} [CommRing R]
    (f a b c : MvPolynomial (Fin 2) R)
    (h : a * f + b * pderiv 0 f + c * pderiv 1 f = 1) :
    Ideal.span (Set.range (fun i => (hypersurfacePresentation f i).jacobian)) = ⊤ := by
  let I := Ideal.span (Set.range (fun i => (hypersurfacePresentation f i).jacobian))
  have hj (i : Fin 2) : Ideal.Quotient.mk _ (pderiv i f) ∈ I := by
    rw [← hypersurfacePresentation_jacobian]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hf : Ideal.Quotient.mk (Ideal.span (Set.range (fun _ : Unit => f))) f = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(), rfl⟩)
  have hh := congrArg (Ideal.Quotient.mk (Ideal.span (Set.range (fun _ : Unit => f)))) h
  simp only [map_add, map_mul, map_one, hf, mul_zero, zero_add] at hh
  apply (Ideal.eq_top_iff_one _).2
  rw [← hh]
  exact I.add_mem (I.mul_mem_left _ (hj 0)) (I.mul_mem_left _ (hj 1))

/-- The first affine chart satisfies the smoothness criterion. -/
theorem chartEquation_z_jacobians_span_top :
    Ideal.span (Set.range (fun i =>
      (hypersurfacePresentation (chartEquation (Equiv.refl (Fin 3))) i).jacobian)) = ⊤ := by
  apply hypersurface_jacobians_span_top _ (C (1 / 4) * (18 * X 0))
    (C (1 / 4) * (4 - 6 * X 0 ^ 2)) (C (1 / 4) * (-9 * X 0 * X 1))
  simp
  calc
    _ = C (1 / 4 : ℂ) * 4 := by ring_nf
    _ = 1 := by rw [← map_ofNat C 4, ← map_mul]; norm_num

/-- The second affine chart satisfies the smoothness criterion, including the point at infinity. -/
theorem chartEquation_y_jacobians_span_top :
    Ideal.span (Set.range (fun i =>
      (hypersurfacePresentation (chartEquation (Equiv.swap (1 : Fin 3) 2)) i).jacobian)) = ⊤ := by
  apply hypersurface_jacobians_span_top _ (2 * X 1 ^ 3) (-X 1 ^ 2)
    (X 0 ^ 2 * X 1 ^ 2 - X 1 ^ 4 - 2 * X 0 * X 1 + 1)
  simp
  ring_nf

/-- The ambient chart isomorphism respects the given complex base. -/
theorem ambientChartIsoAffineSpace_hom_toBase (e : Equiv.Perm (Fin 3)) :
    (ambientChartIsoAffineSpace e).hom ≫ (AffineSpace (Fin 2) base ↘ base) =
      (ambientChart e).ι ≫ ProjectiveSpace.toBase (Fin 3) base := by
  change (ambientChartIsoAffineSpace e).hom ≫ pullback.fst _ _ = _
  simp [ambientChartIsoAffineSpace, ProjectiveSpace.toBase]
  change (pullbackRestrictIsoRestrict planeToIntegerPlane
    (Proj.basicOpen (ProjectivePlaneChart.grading (ULift ℤ)) (X (e 2)))).inv ≫
      pullback.fst planeToIntegerPlane _ ≫ _ = _
  rw [pullbackRestrictIsoRestrict_inv_fst_assoc]
  rfl

/-- The polynomial coefficient inclusion is the actual chart's structure map to `Spec ℂ`. -/
theorem ambientChartIsoSpec_hom_toBase (e : Equiv.Perm (Fin 3)) :
    (ambientChartIsoSpec e).hom ≫ Spec.map (CommRingCat.ofHom (C : ℂ →+* MvPolynomial (Fin 2) ℂ)) =
      (ambientChart e).ι ≫ ProjectiveSpace.toBase (Fin 3) base := by
  have hs := congrArg (fun g => (AffineSpace.SpecIso (Fin 2) (CommRingCat.of ℂ)).hom ≫ g)
    (AffineSpace.SpecIso_inv_over (n := Fin 2) (CommRingCat.of ℂ))
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] at hs
  rw [ambientChartIsoSpec, Iso.trans_hom, Category.assoc]
  exact (congrArg (fun g => (ambientChartIsoAffineSpace e).hom ≫ g) hs.symm).trans
    (ambientChartIsoAffineSpace_hom_toBase e)

/-- The closed chart embedding respects the original structure morphism of the curve. -/
theorem curveChartToSpec_toBase (e : Equiv.Perm (Fin 3)) :
    curveChartToSpec e ≫ Spec.map (CommRingCat.ofHom (C : ℂ →+* MvPolynomial (Fin 2) ℂ)) =
      (curveToPlane ⁻¹ᵁ ambientChart e).ι ≫ curveToBase := by
  rw [curveChartToSpec, Category.assoc, ambientChartIsoSpec_hom_toBase]
  simp [curveToBase]

/-- For a prime equation, the actual curve chart is the polynomial quotient without taking a radical,
compatibly with its embedding in the affine plane. -/
theorem exists_curveChartIsoHypersurface (e : Equiv.Perm (Fin 3))
    (hp : (Ideal.span {chartEquation e}).IsPrime) :
    ∃ E : curveChart e ≅ Spec (CommRingCat.of (HypersurfaceRing (chartEquation e))),
      curveChartToSpec e = E.hom ≫ Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span (Set.range (fun _ : Unit => chartEquation e))))) := by
  have hI : Ideal.span (Set.range (fun _ : Unit => chartEquation e)) =
      (Ideal.span {chartEquation e}).radical := by
    rw [Set.range_const, hp.isRadical.radical]
  dsimp only [HypersurfaceRing]
  rw [hI]
  exact exists_reducedClosedImmersionIso (curveChartToSpec e) (Ideal.span {chartEquation e}) (by
    rw [PrimeSpectrum.zeroLocus_span]
    exact range_curveChartToSpec e)

/-- A prime hypersurface equation with a Jacobian cover gives an actual smooth curve chart
of relative dimension one over its original complex base. -/
theorem curveChart_smoothOfRelativeDimension (e : Equiv.Perm (Fin 3))
    (hp : (Ideal.span {chartEquation e}).IsPrime)
    (hj : Ideal.span (Set.range (fun i =>
      (hypersurfacePresentation (chartEquation e) i).jacobian)) = ⊤) :
    SmoothOfRelativeDimension 1 ((curveToPlane ⁻¹ᵁ ambientChart e).ι ≫ curveToBase) := by
  obtain ⟨E, hE⟩ := exists_curveChartIsoHypersurface e hp
  have hs : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (HypersurfaceRing (chartEquation e))))) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).2
      (hypersurface_locally_standardSmooth (chartEquation e) hj)
  have hf : (curveToPlane ⁻¹ᵁ ambientChart e).ι ≫ curveToBase =
      E.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (HypersurfaceRing (chartEquation e)))) := by
    rw [← curveChartToSpec_toBase, hE, Category.assoc, ← Spec.map_comp]
    rfl
  rw [hf]
  exact IsZariskiLocalAtSource.comp hs E.hom

/-- The constructed projective cubic is smooth of relative dimension one over `ℂ`. -/
instance curve_smoothOfRelativeDimension : SmoothOfRelativeDimension 1 curveToBase := by
  let U : Fin 2 → curve.Opens := ![chart 1, chart 2]
  have hU : iSup U = ⊤ := by
    apply top_unique
    rw [← chart_one_sup_chart_two]
    exact sup_le (le_iSup U 0) (le_iSup U 1)
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1) U hU
  intro i
  fin_cases i
  · exact curveChart_smoothOfRelativeDimension (Equiv.swap (1 : Fin 3) 2)
      chartEquation_y_prime chartEquation_y_jacobians_span_top
  · exact curveChart_smoothOfRelativeDimension (Equiv.refl (Fin 3))
      chartEquation_z_prime chartEquation_z_jacobians_span_top

instance curve_smooth : Smooth curveToBase := SmoothOfRelativeDimension.smooth 1 curveToBase

/-- The constructed self-product is smooth of relative dimension two. -/
instance surface_smoothOfRelativeDimension : SmoothOfRelativeDimension 2 surfaceToBase := by
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 (pullback.fst curveToBase curveToBase) :=
    MorphismProperty.pullback_fst curveToBase curveToBase inferInstance
  exact inferInstanceAs (SmoothOfRelativeDimension (1 + 1)
    (pullback.fst curveToBase curveToBase ≫ curveToBase))

instance surface_smooth : Smooth surfaceToBase :=
  SmoothOfRelativeDimension.smooth 2 surfaceToBase

end AlgebraicGeometry.ExplicitEllipticCandidate
