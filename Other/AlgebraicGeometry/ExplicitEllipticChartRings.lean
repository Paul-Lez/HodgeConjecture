/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticCharts
public import Other.AlgebraicGeometry.ExplicitProjectivePlaneChart
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Polynomial coordinate rings for the explicit cubic's charts

The standard charts of the actual complex projective plane used to construct the cubic
are identified with affine two-space and hence with the spectrum of `ℂ[u,v]`. The actual curve
charts are spectra of the quotients by the radicals of their dehomogenized equations; the
isomorphisms respect the closed embeddings in the affine planes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial

namespace AlgebraicGeometry.ExplicitEllipticCandidate

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ambient projective-plane chart where the permuted third coordinate is nonzero. -/
def ambientChart (e : Equiv.Perm (Fin 3)) : plane.Opens :=
  planeToIntegerPlane ⁻¹ᵁ
    Proj.basicOpen (ProjectivePlaneChart.grading (ULift ℤ)) (X (e 2))

/-- The actual ambient chart is affine two-space over the given complex base. -/
def ambientChartIsoAffineSpace (e : Equiv.Perm (Fin 3)) :
    (ambientChart e).toScheme ≅ AffineSpace (Fin 2) base := by
  let U := Proj.basicOpen (ProjectivePlaneChart.grading (ULift ℤ)) (X (e 2))
  let E := ProjectivePlaneChart.basicOpenIso (ULift ℤ) e
  exact (pullbackRestrictIsoRestrict planeToIntegerPlane U).symm ≪≫
    pullbackLeftPullbackSndIso (terminal.from base) (terminal.from integerPlane) U.ι ≪≫
    asIso (pullback.map (terminal.from base) (U.ι ≫ terminal.from integerPlane)
      (terminal.from base) (terminal.from (Spec (CommRingCat.of (MvPolynomial (Fin 2) (ULift ℤ)))))
      (𝟙 base) E.hom (𝟙 _) (by simp) (Subsingleton.elim _ _))

/-- The actual ambient chart is the spectrum of a polynomial ring in two complex variables. -/
def ambientChartIsoSpec (e : Equiv.Perm (Fin 3)) :
    (ambientChart e).toScheme ≅ Spec (CommRingCat.of (MvPolynomial (Fin 2) ℂ)) :=
  ambientChartIsoAffineSpace e ≪≫ AffineSpace.SpecIso (Fin 2) (CommRingCat.of ℂ)

/-- The polynomial coordinates agree with the integral affine-space projection. -/
theorem affineSpace_SpecIso_inv_toSpecMvPoly :
    (AffineSpace.SpecIso (Fin 2) (CommRingCat.of ℂ)).inv ≫
      AffineSpace.toSpecMvPoly (Fin 2) base =
        Spec.map (CommRingCat.ofHom (MvPolynomial.map integerToComplex)) := by
  apply (AffineSpace.toSpecMvPolyIntEquiv (Fin 2)).injective
  funext i
  rw [AffineSpace.toSpecMvPolyIntEquiv_comp]
  change (AffineSpace.SpecIso (Fin 2) (CommRingCat.of ℂ)).inv.appTop
    (AffineSpace.coord base i) = _
  dsimp only [base]
  rw [AffineSpace.SpecIso_inv_appTop_coord]
  change _ = ((Scheme.ΓSpecIso _).inv ≫
    (Spec.map (CommRingCat.ofHom (MvPolynomial.map integerToComplex))).appTop) (X i)
  rw [← Scheme.ΓSpecIso_inv_naturality]
  change _ = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) ℂ))).inv
    (MvPolynomial.map integerToComplex (X i))
  rw [MvPolynomial.map_X]

theorem ambientChartIsoAffineSpace_hom_toSpecMvPoly (e : Equiv.Perm (Fin 3)) :
    (ambientChartIsoAffineSpace e).hom ≫ AffineSpace.toSpecMvPoly (Fin 2) base =
      planeToIntegerPlane ∣_ Proj.basicOpen (ProjectivePlaneChart.grading (ULift ℤ)) (X (e 2)) ≫
        (ProjectivePlaneChart.basicOpenIso (ULift ℤ) e).hom := by
  simp [ambientChartIsoAffineSpace, AffineSpace.toSpecMvPoly, morphismRestrict]
  rfl

/-- The actual complex chart map respects the integral projective model. -/
theorem ambientChartIsoSpec_inv_toIntegerPlane (e : Equiv.Perm (Fin 3)) :
    (ambientChartIsoSpec e).inv ≫ (ambientChart e).ι ≫ planeToIntegerPlane =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map integerToComplex)) ≫
        ProjectivePlaneChart.chartMap (ULift ℤ) e := by
  apply (cancel_epi (ambientChartIsoSpec e).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [ambientChartIsoSpec, Iso.trans_hom, Category.assoc]
  rw [← affineSpace_SpecIso_inv_toSpecMvPoly]
  dsimp only [base]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change (ambientChart e).ι ≫ planeToIntegerPlane =
    (ambientChartIsoAffineSpace e).hom ≫ AffineSpace.toSpecMvPoly (Fin 2) base ≫ _
  rw [← Category.assoc, ambientChartIsoAffineSpace_hom_toSpecMvPoly]
  simp [ProjectivePlaneChart.chartMap]
  rfl

/-- The defining polynomial of the cubic in the chosen complex affine coordinates. -/
def chartEquation (e : Equiv.Perm (Fin 3)) : MvPolynomial (Fin 2) ℂ :=
  (ProjectivePlaneChart.dehomogenize (ULift.{0} ℤ) e cubic).map integerToComplex

/-- Nonvanishing of the original homogeneous cubic is nonvanishing of its chart equation. -/
theorem ambientChartIsoSpec_preimage_basicOpen_cubic (e : Equiv.Perm (Fin 3)) :
    ((ambientChartIsoSpec e).inv ≫ (ambientChart e).ι ≫ planeToIntegerPlane) ⁻¹ᵁ
        Proj.basicOpen (ProjectivePlaneChart.grading (ULift ℤ)) cubic =
      PrimeSpectrum.basicOpen (chartEquation e) := by
  rw [ambientChartIsoSpec_inv_toIntegerPlane, Scheme.Hom.comp_preimage,
    ProjectivePlaneChart.chartMap_preimage_basicOpen _ _ 3 cubic cubic_homogeneous (by decide),
    SpecMap_preimage_basicOpen]
  rfl

/-- The closed subset used to construct the curve is precisely the chart equation's zero locus. -/
theorem ambientChartIsoSpec_preimage_cubicLocus (e : Equiv.Perm (Fin 3)) :
    ((ambientChartIsoSpec e).inv ≫ (ambientChart e).ι) ⁻¹' (cubicLocus : Set plane) =
      PrimeSpectrum.zeroLocus {chartEquation e} := by
  ext x
  have h := congrArg (fun U => x ∈ U)
    (ambientChartIsoSpec_preimage_basicOpen_cubic e)
  change ({cubic} : Set (MvPolynomial (Fin 3) (ULift.{0} ℤ))) ⊆
    (((ambientChartIsoSpec e).inv ≫ (ambientChart e).ι ≫
      planeToIntegerPlane) x).asHomogeneousIdeal ↔
    ({chartEquation e} : Set (MvPolynomial (Fin 2) ℂ)) ⊆ x.asIdeal
  rw [Set.singleton_subset_iff, Set.singleton_subset_iff]
  exact not_iff_not.mp h.to_iff

/-- The actual open subscheme of the curve inside an ambient affine chart. -/
def curveChart (e : Equiv.Perm (Fin 3)) : Scheme :=
  (curveToPlane ⁻¹ᵁ ambientChart e).toScheme

instance (e : Equiv.Perm (Fin 3)) : IsReduced (curveChart e) :=
  inferInstanceAs (IsReduced (curveToPlane ⁻¹ᵁ ambientChart e).toScheme)

/-- The closed embedding of a curve chart into its affine polynomial-coordinate plane. -/
def curveChartToSpec (e : Equiv.Perm (Fin 3)) :
    curveChart e ⟶ Spec (CommRingCat.of (MvPolynomial (Fin 2) ℂ)) :=
  curveToPlane ∣_ ambientChart e ≫ (ambientChartIsoSpec e).hom

instance (e : Equiv.Perm (Fin 3)) : IsClosedImmersion (curveChartToSpec e) := by
  dsimp only [curveChartToSpec]
  infer_instance

/-- The chart embedding has exactly the zero locus of the displayed affine equation as image. -/
theorem range_curveChartToSpec (e : Equiv.Perm (Fin 3)) :
    Set.range (curveChartToSpec e) = PrimeSpectrum.zeroLocus {chartEquation e} := by
  have hr : Set.range (curveToPlane ∣_ ambientChart e) =
      (ambientChart e).ι ⁻¹' (cubicLocus : Set plane) := by
    unfold morphismRestrict
    change Set.range (⇑(pullback.snd curveToPlane (ambientChart e).ι) ∘
      (pullbackRestrictIsoRestrict curveToPlane (ambientChart e)).inv) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr
      (show Function.Surjective (pullbackRestrictIsoRestrict curveToPlane (ambientChart e)).inv
        from (pullbackRestrictIsoRestrict curveToPlane (ambientChart e)).inv.homeomorph.surjective),
      Set.image_univ, Scheme.Pullback.range_snd]
    congr 1
    exact cubicIdeal.range_subschemeι.trans
      (Scheme.IdealSheafData.coe_support_vanishingIdeal cubicLocus)
  rw [← ambientChartIsoSpec_preimage_cubicLocus]
  change Set.range ((ambientChartIsoSpec e).hom ∘ (curveToPlane ∣_ ambientChart e)) = _
  rw [Set.range_comp, hr]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    refine ⟨(ambientChartIsoSpec e).inv x, hx, ?_⟩
    simp

/-- A reduced closed subscheme of an affine scheme is determined by its underlying closed set. -/
theorem exists_reducedClosedImmersionIso {R : CommRingCat.{u}} {X : Scheme.{u}} [IsReduced X]
    (f : X ⟶ Spec R) [IsClosedImmersion f] (I : Ideal R)
    (hf : Set.range f = PrimeSpectrum.zeroLocus I) :
    ∃ E : X ≅ Spec (CommRingCat.of (R ⧸ I.radical)),
      f = E.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I.radical)) := by
  obtain ⟨J, E, hE⟩ := (IsClosedImmersion.Spec_iff (f := f)).mp inferInstance
  have : IsReduced (Spec (CommRingCat.of (R ⧸ J))) := isReduced_of_isOpenImmersion E.inv
  have hJ : J.IsRadical := Ideal.isRadical_iff_quotient_reduced J |>.2
    ((affine_isReduced_iff (CommRingCat.of (R ⧸ J))).1 inferInstance)
  have hrange : Set.range f = PrimeSpectrum.zeroLocus (J : Set R) := by
    rw [hE]
    change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J) ∘ E.hom) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr
      (show Function.Surjective E.hom from E.hom.homeomorph.surjective), Set.image_univ,
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker]
  have hJI : J = I.radical := by
    rw [← hJ.radical]
    exact PrimeSpectrum.zeroLocus_eq_iff.mp (hrange.symm.trans hf)
  subst J
  exact ⟨E, hE⟩

/-- The coordinate-ring quotient describing the actual cubic chart, with its reduced structure. -/
def curveChartIso (e : Equiv.Perm (Fin 3)) : curveChart e ≅
    Spec (CommRingCat.of (MvPolynomial (Fin 2) ℂ ⧸
      (Ideal.span {chartEquation e}).radical)) :=
  (exists_reducedClosedImmersionIso (curveChartToSpec e) (Ideal.span {chartEquation e}) (by
    rw [PrimeSpectrum.zeroLocus_span]
    exact range_curveChartToSpec e)).choose

/-- The chart-coordinate isomorphism intertwines the actual closed embedding and quotient map. -/
theorem curveChartIso_hom_quotientMap (e : Equiv.Perm (Fin 3)) :
    (curveChartIso e).hom ≫ Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {chartEquation e}).radical)) = curveChartToSpec e :=
  (exists_reducedClosedImmersionIso (curveChartToSpec e) (Ideal.span {chartEquation e}) (by
    rw [PrimeSpectrum.zeroLocus_span]
    exact range_curveChartToSpec e)).choose_spec.symm

/-- In the `Z` chart the cubic equation is `v² - u³ + u`. -/
theorem dehomogenize_cubic_z :
    ProjectivePlaneChart.dehomogenize (ULift ℤ) (Equiv.refl (Fin 3)) cubic =
      X 1 ^ 2 - X 0 ^ 3 + X 0 := by
  simp [cubic, ProjectivePlaneChart.dehomogenize, ProjectivePlaneChart.coordinateValues]

/-- In the `Y` chart the cubic equation is `v - u³ + uv²`. -/
theorem dehomogenize_cubic_y :
    ProjectivePlaneChart.dehomogenize (ULift ℤ) (Equiv.swap (1 : Fin 3) 2) cubic =
      X 1 - X 0 ^ 3 + X 0 * X 1 ^ 2 := by
  simp [cubic, ProjectivePlaneChart.dehomogenize, ProjectivePlaneChart.coordinateValues, Equiv.swap_apply_def]

end AlgebraicGeometry.ExplicitEllipticCandidate
