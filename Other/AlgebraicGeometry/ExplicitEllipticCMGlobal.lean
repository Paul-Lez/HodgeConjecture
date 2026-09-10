/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticCMAutomorphism
public import Other.AlgebraicGeometry.ExplicitEllipticDifferentialOverlap
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Global complex multiplication on the explicit elliptic cubic

This file continues the two affine calculations for the projective automorphism
`[X : Y : Z] ↦ [-X : iY : Z]`.  In particular, it proves on the chart containing
infinity that the invariant differential has eigenvalue `i`, matching the previously
proved calculation on the affine `Z ≠ 0` chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MvPolynomial

namespace AlgebraicGeometry

/-- Conjugate a ring automorphism of the section ring of an affine open by the
canonical affine-spectrum equivalence. -/
def affineOpenSelfIsoOfRingEquiv {X : Scheme} {U : X.Opens}
    (hU : IsAffineOpen U) (e : Γ(X, U) ≃+* Γ(X, U)) :
    U.toScheme ≅ U.toScheme :=
  hU.isoSpec ≪≫ Scheme.Spec.mapIso e.toCommRingCatIso.op ≪≫ hU.isoSpec.symm

/-- The pullback on global functions of `affineOpenSelfIsoOfRingEquiv` is exactly
the ring automorphism used to define it, transported through `U.topIso`. -/
theorem affineOpenSelfIsoOfRingEquiv_appTop {X : Scheme} {U : X.Opens}
    (hU : IsAffineOpen U) (e : Γ(X, U) ≃+* Γ(X, U)) :
    (affineOpenSelfIsoOfRingEquiv hU e).hom.appTop =
      U.topIso.hom ≫ CommRingCat.ofHom e.toRingHom ≫ U.topIso.inv := by
  simp only [affineOpenSelfIsoOfRingEquiv, Iso.trans_hom, Scheme.Hom.comp_appTop]
  rw [show hU.isoSpec.symm.hom.appTop =
      U.topIso.hom ≫ (Scheme.ΓSpecIso Γ(X, U)).inv from
        hU.isoSpec_inv_appTop]
  rw [show hU.isoSpec.hom.appTop =
      (Scheme.ΓSpecIso Γ(X, U)).hom ≫ U.topIso.inv from
        hU.isoSpec_hom_appTop]
  have hc :
      (Scheme.ΓSpecIso Γ(X, U)).inv ≫
          ((Scheme.Spec.mapIso e.toCommRingCatIso.op).hom.appTop ≫
            (Scheme.ΓSpecIso Γ(X, U)).hom) =
        CommRingCat.ofHom e.toRingHom := by
    rw [show
        (Scheme.Spec.mapIso e.toCommRingCatIso.op).hom.appTop =
          (Spec.map (CommRingCat.ofHom e.toRingHom)).appTop from rfl]
    rw [Scheme.ΓSpecIso_naturality]
    exact (Scheme.ΓSpecIso Γ(X, U)).inv_hom_id_assoc _
  have hc' := congrArg
    (fun k => U.topIso.hom ≫ k ≫ U.topIso.inv) hc
  convert hc' using 1 <;> simp only [Category.assoc]

@[simp] theorem affineOpenSelfIsoOfRingEquiv_appTop_apply {X : Scheme}
    {U : X.Opens} (hU : IsAffineOpen U) (e : Γ(X, U) ≃+* Γ(X, U))
    (r : Γ(X, U)) :
    (affineOpenSelfIsoOfRingEquiv hU e).hom.appTop (U.topIso.inv r) =
      U.topIso.inv (e r) := by
  rw [affineOpenSelfIsoOfRingEquiv_appTop]
  change U.topIso.inv (e (U.topIso.hom (U.topIso.inv r))) = U.topIso.inv (e r)
  rw [U.topIso.inv_hom_id_apply]

/-- A ring automorphism that sends a section to a unit multiple of itself preserves
the associated basic open of the affine chart. -/
theorem affineOpenSelfIsoOfRingEquiv_preimage_basicOpen
    {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
    (e : Γ(X, U) ≃+* Γ(X, U)) (r c : Γ(X, U))
    (hc : IsUnit c) (he : e r = c * r) :
    (affineOpenSelfIsoOfRingEquiv hU e).hom ⁻¹ᵁ
        U.toScheme.basicOpen (U.topIso.inv r) =
      U.toScheme.basicOpen (U.topIso.inv r) := by
  rw [Scheme.preimage_basicOpen_top,
    affineOpenSelfIsoOfRingEquiv_appTop_apply, he, map_mul,
    Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit]
  · simp
  · exact hc.map U.topIso.inv.hom

/-- The global-section map of the canonical inclusion between two open subschemes
is ordinary restriction, conjugated by the two `topIso`s. -/
theorem homOfLE_appTop_eq_restriction {X : Scheme} {U V : X.Opens}
    (h : V ≤ U) :
    (X.homOfLE h).appTop = U.topIso.hom ≫
      X.presheaf.map (homOfLE h).op ≫ V.topIso.inv := by
  change (X.homOfLE h).app ⊤ = _
  have hx := Scheme.Hom.resLE_app_top
    (f := 𝟙 X) (U := U) (V := V) h
  rw [Scheme.Hom.resLE_id] at hx
  rw [hx]
  congr 1

/-- If an endomorphism of a smaller open is the restriction of an affine ring
automorphism, then its pullback intertwines ordinary section restriction with that
ring automorphism. -/
theorem affineOpenSelfIso_restriction_intertwines
    {X : Scheme} {U V : X.Opens} (h : V ≤ U) (hU : IsAffineOpen U)
    (e : Γ(X, U) ≃+* Γ(X, U)) (g : V.toScheme ⟶ V.toScheme)
    (hg : g ≫ X.homOfLE h =
      X.homOfLE h ≫ (affineOpenSelfIsoOfRingEquiv hU e).hom)
    (r : Γ(X, U)) :
    V.topIso.hom
        (g.appTop (V.topIso.inv
          (X.presheaf.map (homOfLE h).op r))) =
      X.presheaf.map (homOfLE h).op (e r) := by
  have hm := congrArg Scheme.Hom.appTop hg
  simp only [Scheme.Hom.comp_appTop] at hm
  rw [homOfLE_appTop_eq_restriction,
    affineOpenSelfIsoOfRingEquiv_appTop] at hm
  have hm' := congrArg
    (fun k => U.topIso.inv ≫ k ≫ V.topIso.hom) hm
  have hm'' :
      X.presheaf.map (homOfLE h).op ≫ V.topIso.inv ≫
          g.appTop ≫ V.topIso.hom =
        CommRingCat.ofHom e.toRingHom ≫
          X.presheaf.map (homOfLE h).op := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using hm'
  exact congrArg (fun k => k r) (congrArg ConcreteCategory.hom hm'')

end AlgebraicGeometry

namespace AlgebraicGeometry.ExplicitEllipticCandidate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A distinct copy of the Y-chart ring, used to construct the pullback on Kähler
differentials for the nonidentity CM endomorphism. -/
structure CurveYRingCopy where
  down : Γ(curve, curveYOpen)

def curveYRingCopyEquiv : CurveYRingCopy ≃ Γ(curve, curveYOpen) where
  toFun := CurveYRingCopy.down
  invFun := CurveYRingCopy.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : CommRing CurveYRingCopy := curveYRingCopyEquiv.commRing

def curveYRingCopyRingEquiv : CurveYRingCopy ≃+* Γ(curve, curveYOpen) where
  __ := curveYRingCopyEquiv
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

instance : Algebra ℂ CurveYRingCopy :=
  (curveYRingCopyRingEquiv.symm.toRingHom.comp
    (algebraMap ℂ Γ(curve, curveYOpen))).toAlgebra

def curveYRingCopyAlgEquiv : CurveYRingCopy ≃ₐ[ℂ] Γ(curve, curveYOpen) where
  __ := curveYRingCopyRingEquiv
  commutes' _ := rfl

/-- The Y-chart CM map factored through a definitionally distinct ring. -/
def curveYCMToCopy : Γ(curve, curveYOpen) →ₐ[ℂ] CurveYRingCopy :=
  curveYRingCopyAlgEquiv.symm.toAlgHom.comp curveYCMEnd

def curveYCMFromCopy : CurveYRingCopy →ₐ[ℂ] Γ(curve, curveYOpen) :=
  curveYRingCopyAlgEquiv.toAlgHom

def curveYCMDifferentialToCopy :
    KaehlerDifferential ℂ Γ(curve, curveYOpen) →ₗ[ℂ]
      KaehlerDifferential ℂ CurveYRingCopy := by
  letI : Algebra Γ(curve, curveYOpen) CurveYRingCopy :=
    curveYCMToCopy.toRingHom.toAlgebra
  letI : IsScalarTower ℂ Γ(curve, curveYOpen) CurveYRingCopy :=
    IsScalarTower.of_algebraMap_eq' curveYCMToCopy.comp_algebraMap.symm
  exact (KaehlerDifferential.map ℂ ℂ Γ(curve, curveYOpen)
    CurveYRingCopy).restrictScalars ℂ

def curveYCMDifferentialFromCopy :
    KaehlerDifferential ℂ CurveYRingCopy →ₗ[ℂ]
      KaehlerDifferential ℂ Γ(curve, curveYOpen) := by
  letI : Algebra CurveYRingCopy Γ(curve, curveYOpen) :=
    curveYCMFromCopy.toRingHom.toAlgebra
  letI : IsScalarTower ℂ CurveYRingCopy Γ(curve, curveYOpen) :=
    IsScalarTower.of_algebraMap_eq' curveYCMFromCopy.comp_algebraMap.symm
  exact (KaehlerDifferential.map ℂ ℂ CurveYRingCopy
    Γ(curve, curveYOpen)).restrictScalars ℂ

/-- Pullback on Kähler differentials along the CM endomorphism of the Y chart. -/
def curveYCMDifferentialEnd :
    KaehlerDifferential ℂ Γ(curve, curveYOpen) →ₗ[ℂ]
      KaehlerDifferential ℂ Γ(curve, curveYOpen) :=
  curveYCMDifferentialFromCopy.comp curveYCMDifferentialToCopy

@[simp] theorem curveYCMDifferentialEnd_D (r : Γ(curve, curveYOpen)) :
    curveYCMDifferentialEnd (KaehlerDifferential.D ℂ _ r) =
      KaehlerDifferential.D ℂ _ (curveYCMEnd r) := by
  simp only [curveYCMDifferentialEnd, LinearMap.comp_apply,
    curveYCMDifferentialFromCopy, curveYCMDifferentialToCopy,
    LinearMap.restrictScalars_apply, KaehlerDifferential.map_D]
  rfl

theorem curveYCMDifferentialEnd_smul
    (r : Γ(curve, curveYOpen))
    (w : KaehlerDifferential ℂ Γ(curve, curveYOpen)) :
    curveYCMDifferentialEnd (r • w) =
      curveYCMEnd r • curveYCMDifferentialEnd w := by
  rw [curveYCMDifferentialEnd, LinearMap.comp_apply]
  change curveYCMDifferentialFromCopy
      (curveYCMDifferentialToCopy (r • w)) = _
  have h₁ : curveYCMDifferentialToCopy (r • w) =
      curveYCMToCopy r • curveYCMDifferentialToCopy w := by
    letI : Algebra Γ(curve, curveYOpen) CurveYRingCopy :=
      curveYCMToCopy.toRingHom.toAlgebra
    letI : IsScalarTower ℂ Γ(curve, curveYOpen) CurveYRingCopy :=
      IsScalarTower.of_algebraMap_eq' curveYCMToCopy.comp_algebraMap.symm
    exact (KaehlerDifferential.map ℂ ℂ Γ(curve, curveYOpen)
      CurveYRingCopy).map_smul r w
  rw [h₁]
  have h₂ : curveYCMDifferentialFromCopy
      (curveYCMToCopy r • curveYCMDifferentialToCopy w) =
      curveYCMFromCopy (curveYCMToCopy r) •
        curveYCMDifferentialFromCopy (curveYCMDifferentialToCopy w) := by
    letI : Algebra CurveYRingCopy Γ(curve, curveYOpen) :=
      curveYCMFromCopy.toRingHom.toAlgebra
    letI : IsScalarTower ℂ CurveYRingCopy Γ(curve, curveYOpen) :=
      IsScalarTower.of_algebraMap_eq' curveYCMFromCopy.comp_algebraMap.symm
    exact (KaehlerDifferential.map ℂ ℂ CurveYRingCopy
      Γ(curve, curveYOpen)).map_smul _ _
  rw [h₂]
  rfl

theorem yCMPolynomialEnd_yDifferentialB :
    yCMPolynomialEnd yDifferentialB = -yDifferentialB := by
  simp only [yDifferentialB, map_neg, map_pow, yCMPolynomialEnd_X_one]
  have hI : (C Complex.I : YPoly) * C Complex.I = -1 := by
    rw [← map_mul]
    simp [Complex.I_sq]
  calc
    -(-(C Complex.I * X (1 : Fin 2))) ^ 2 =
        -((C Complex.I * C Complex.I) * X (1 : Fin 2) ^ 2) := by ring
    _ = -(-X 1 ^ 2) := by rw [hI]; ring

theorem yCMPolynomialEnd_yDifferentialC :
    yCMPolynomialEnd yDifferentialC = yDifferentialC := by
  simp only [yDifferentialC, map_add, map_sub, map_mul, map_pow, map_ofNat,
    map_one, yCMPolynomialEnd_X_zero, yCMPolynomialEnd_X_one]
  have hI2 : (C Complex.I : YPoly) ^ 2 = -1 := by
    rw [← map_pow]
    simp [Complex.I_sq]
  have hI4 : (C Complex.I : YPoly) ^ 4 = 1 := by
    calc
      (C Complex.I : YPoly) ^ 4 = ((C Complex.I : YPoly) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hI2]; norm_num
  ring_nf
  rw [hI2, hI4]
  ring

/-- The CM automorphism acts by `i` on the invariant differential on the chart
containing the point at infinity. -/
theorem curveYCMDifferentialEnd_curveYDifferential :
    curveYCMDifferentialEnd curveYDifferential =
      Complex.I • curveYDifferential := by
  unfold curveYDifferential hypersurfaceDifferential
  rw [map_neg, map_sub, curveYCMDifferentialEnd_smul,
    curveYCMDifferentialEnd_smul,
    curveYCMDifferentialEnd_D, curveYCMDifferentialEnd_D]
  rw [curveYCMEnd_coordinate, curveYCMEnd_coordinate,
    curveYCMEnd_coordinate, curveYCMEnd_coordinate]
  rw [yCMPolynomialEnd_yDifferentialC,
    yCMPolynomialEnd_yDifferentialB,
    yCMPolynomialEnd_X_zero, yCMPolynomialEnd_X_one]
  simp only [map_neg, map_mul]
  rw [show hypersurfaceCoordinateMap
      (chartEquation (Equiv.swap (1 : Fin 3) 2))
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
        chartEquation_y_prime) (C Complex.I) = algebraMap ℂ _ Complex.I by
    exact (hypersurfaceCoordinateMap
      (chartEquation (Equiv.swap (1 : Fin 3) 2))
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
        chartEquation_y_prime)).commutes Complex.I]
  rw [Derivation.leibniz, Derivation.leibniz]
  simp only [Derivation.map_algebraMap, zero_smul, zero_add]
  module

/-- The earlier Z-chart differential used for the CM calculation is definitionally the
same differential used to construct the global holomorphic form. -/
theorem curveZDifferentialCM_eq_curveZDifferential :
    curveZDifferentialCM = curveZDifferential := rfl

/-- Thus the invariant differential has eigenvalue `i` on both members of the standard
two-chart cover. -/
theorem curveZCMDifferentialEnd_curveZDifferential' :
    curveZCMDifferentialEnd curveZDifferential =
      Complex.I • curveZDifferential := by
  simpa [curveZDifferentialCM_eq_curveZDifferential] using
    curveZCMDifferentialEnd_curveZDifferential

theorem curveZOpen_isAffine : IsAffineOpen curveZOpen := chart_isAffineOpen 2

theorem curveYOpen_isAffine : IsAffineOpen curveYOpen := chart_isAffineOpen 1

/-- The Z-chart scheme automorphism, in a form whose action on global sections is
available through `affineOpenSelfIsoOfRingEquiv_appTop`. -/
def curveZCMChartIso : curveZOpen.toScheme ≅ curveZOpen.toScheme :=
  affineOpenSelfIsoOfRingEquiv curveZOpen_isAffine curveZCMAlgEquiv.toRingEquiv

/-- The Y-chart scheme automorphism, in a form whose action on global sections is
available through `affineOpenSelfIsoOfRingEquiv_appTop`. -/
def curveYCMChartIso : curveYOpen.toScheme ≅ curveYOpen.toScheme :=
  affineOpenSelfIsoOfRingEquiv curveYOpen_isAffine curveYCMAlgEquiv.toRingEquiv

theorem curveZCMChartIso_appTop : curveZCMChartIso.hom.appTop =
    curveZOpen.topIso.hom ≫
      CommRingCat.ofHom curveZCMAlgEquiv.toRingEquiv.toRingHom ≫
      curveZOpen.topIso.inv :=
  affineOpenSelfIsoOfRingEquiv_appTop _ _

theorem curveYCMChartIso_appTop : curveYCMChartIso.hom.appTop =
    curveYOpen.topIso.hom ≫
      CommRingCat.ofHom curveYCMAlgEquiv.toRingEquiv.toRingHom ≫
      curveYOpen.topIso.inv :=
  affineOpenSelfIsoOfRingEquiv_appTop _ _

/-! ## Preservation of the chart overlap -/

/-- On the Z chart, the overlap with the chart at infinity is the nonvanishing
locus of the affine coordinate `y = Y/Z`. -/
def curveZOverlapCoordinate : Γ(curve, curveZOpen) :=
  ProjectiveRatioSections.pullRatio (ULift ℤ) curveToIntegerPlane
    curveZOpen 2 le_rfl 1

/-- On the Y chart, the same overlap is the nonvanishing locus of `v = Z/Y`. -/
def curveYOverlapCoordinate : Γ(curve, curveYOpen) :=
  ProjectiveRatioSections.pullRatio (ULift ℤ) curveToIntegerPlane
    curveYOpen 1 le_rfl 2

theorem curveZOverlapCoordinate_eq_coordinate :
    curveZOverlapCoordinate =
      hypersurfaceCoordinateMap
        (chartEquation (Equiv.refl (Fin 3)))
        (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3))
          chartEquation_z_prime) (X 1) := by
  have h := curveSectionRestriction_coordinate
    (Equiv.refl (Fin 3)) chartEquation_z_prime
      (V := curveZOpen) le_rfl 1
  simpa [curveZOverlapCoordinate, curveSectionRestriction] using h.symm

theorem curveYOverlapCoordinate_eq_coordinate :
    curveYOverlapCoordinate =
      hypersurfaceCoordinateMap
        (chartEquation (Equiv.swap (1 : Fin 3) 2))
        (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2)
          chartEquation_y_prime) (X 1) := by
  have h := curveSectionRestriction_coordinate
    (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime
      (V := curveYOpen) le_rfl 1
  simpa [curveYOverlapCoordinate, curveSectionRestriction] using h.symm

theorem curveZOverlapCoordinate_cm :
    curveZCMEnd curveZOverlapCoordinate =
      Complex.I • curveZOverlapCoordinate := by
  rw [curveZOverlapCoordinate_eq_coordinate]
  exact curveZCMEnd_coordinate_one

theorem curveYOverlapCoordinate_cm :
    curveYCMEnd curveYOverlapCoordinate =
      -(Complex.I • curveYOverlapCoordinate) := by
  rw [curveYOverlapCoordinate_eq_coordinate]
  exact curveYCMEnd_coordinate_one

theorem curveZOverlapCoordinate_basicOpen :
    curve.basicOpen curveZOverlapCoordinate = curveZOpen ⊓ curveYOpen :=
  ProjectiveRatioSections.basicOpen_pullRatio (ULift ℤ)
    curveToIntegerPlane curveZOpen 2 1 le_rfl

theorem curveYOverlapCoordinate_basicOpen :
    curve.basicOpen curveYOverlapCoordinate = curveYOpen ⊓ curveZOpen :=
  ProjectiveRatioSections.basicOpen_pullRatio (ULift ℤ)
    curveToIntegerPlane curveYOpen 1 2 le_rfl

/-- The Z-chart CM automorphism preserves its open intersection with the Y chart. -/
theorem curveZCMChartIso_preimage_overlap :
    curveZCMChartIso.hom ⁻¹ᵁ
        curveZOpen.toScheme.basicOpen
          (curveZOpen.topIso.inv curveZOverlapCoordinate) =
      curveZOpen.toScheme.basicOpen
        (curveZOpen.topIso.inv curveZOverlapCoordinate) := by
  apply affineOpenSelfIsoOfRingEquiv_preimage_basicOpen
    curveZOpen_isAffine curveZCMAlgEquiv.toRingEquiv curveZOverlapCoordinate
    (algebraMap ℂ Γ(curve, curveZOpen) Complex.I)
  · exact (isUnit_iff_ne_zero.mpr Complex.I_ne_zero).map
      (algebraMap ℂ Γ(curve, curveZOpen))
  · change curveZCMEnd curveZOverlapCoordinate = _
    rw [curveZOverlapCoordinate_cm]
    simp [Algebra.smul_def]

/-- The Y-chart CM automorphism preserves its open intersection with the Z chart. -/
theorem curveYCMChartIso_preimage_overlap :
    curveYCMChartIso.hom ⁻¹ᵁ
        curveYOpen.toScheme.basicOpen
          (curveYOpen.topIso.inv curveYOverlapCoordinate) =
      curveYOpen.toScheme.basicOpen
        (curveYOpen.topIso.inv curveYOverlapCoordinate) := by
  apply affineOpenSelfIsoOfRingEquiv_preimage_basicOpen
    curveYOpen_isAffine curveYCMAlgEquiv.toRingEquiv curveYOverlapCoordinate
    (-(algebraMap ℂ Γ(curve, curveYOpen) Complex.I))
  · exact ((isUnit_iff_ne_zero.mpr Complex.I_ne_zero).map
      (algebraMap ℂ Γ(curve, curveYOpen))).neg
  · change curveYCMEnd curveYOverlapCoordinate = _
    rw [curveYOverlapCoordinate_cm]
    simp [Algebra.smul_def]

/-- The overlap, regarded as a basic open inside the Z chart. -/
def curveZCMLocalOverlap : curveZOpen.toScheme.Opens :=
  curveZOpen.toScheme.basicOpen
    (curveZOpen.topIso.inv curveZOverlapCoordinate)

/-- The overlap, regarded as a basic open inside the Y chart. -/
def curveYCMLocalOverlap : curveYOpen.toScheme.Opens :=
  curveYOpen.toScheme.basicOpen
    (curveYOpen.topIso.inv curveYOverlapCoordinate)

/-- A fixed global model for the overlap of the two standard affine charts. -/
def curveCMOverlap : curve.Opens := curve.basicOpen curveZOverlapCoordinate

theorem curveZCMLocalOverlap_image :
    curveZOpen.ι ''ᵁ curveZCMLocalOverlap = curveCMOverlap := by
  simpa [curveZCMLocalOverlap, curveCMOverlap] using
    curveZOpen.ι_image_basicOpen_topIso_inv curveZOverlapCoordinate

theorem curveYCMLocalOverlap_image :
    curveYOpen.ι ''ᵁ curveYCMLocalOverlap = curveCMOverlap := by
  calc
    curveYOpen.ι ''ᵁ curveYCMLocalOverlap =
        curve.basicOpen curveYOverlapCoordinate := by
      simpa [curveYCMLocalOverlap] using
        curveYOpen.ι_image_basicOpen_topIso_inv curveYOverlapCoordinate
    _ = curveYOpen ⊓ curveZOpen := curveYOverlapCoordinate_basicOpen
    _ = curveZOpen ⊓ curveYOpen := inf_comm _ _
    _ = curve.basicOpen curveZOverlapCoordinate :=
      curveZOverlapCoordinate_basicOpen.symm
    _ = curveCMOverlap := rfl

/-- The Z-chart model of the overlap is canonically isomorphic to the fixed global
overlap. -/
def curveZCMLocalOverlapIso :
    curveZCMLocalOverlap.toScheme ≅ curveCMOverlap.toScheme :=
  curveZOpen.ι.isoImage curveZCMLocalOverlap ≪≫
    curve.isoOfEq curveZCMLocalOverlap_image

/-- The Y-chart model of the overlap is canonically isomorphic to the fixed global
overlap. -/
def curveYCMLocalOverlapIso :
    curveYCMLocalOverlap.toScheme ≅ curveCMOverlap.toScheme :=
  curveYOpen.ι.isoImage curveYCMLocalOverlap ≪≫
    curve.isoOfEq curveYCMLocalOverlap_image

@[reassoc (attr := simp)] theorem curveZCMLocalOverlapIso_hom_ι :
    curveZCMLocalOverlapIso.hom ≫ curveCMOverlap.ι =
      curveZCMLocalOverlap.ι ≫ curveZOpen.ι := by
  simp [curveZCMLocalOverlapIso]

@[reassoc (attr := simp)] theorem curveYCMLocalOverlapIso_hom_ι :
    curveYCMLocalOverlapIso.hom ≫ curveCMOverlap.ι =
      curveYCMLocalOverlap.ι ≫ curveYOpen.ι := by
  simp [curveYCMLocalOverlapIso]

/-- Restriction of the Z-chart CM automorphism to the preserved overlap. -/
def curveZCMLocalOverlapEnd :
    curveZCMLocalOverlap.toScheme ⟶ curveZCMLocalOverlap.toScheme :=
  curveZCMChartIso.hom.resLE curveZCMLocalOverlap curveZCMLocalOverlap (by
    have hpre : curveZCMChartIso.hom ⁻¹ᵁ curveZCMLocalOverlap =
        curveZCMLocalOverlap := by
      simpa only [curveZCMLocalOverlap] using
        curveZCMChartIso_preimage_overlap
    rw [hpre])

/-- Restriction of the Y-chart CM automorphism to the preserved overlap. -/
def curveYCMLocalOverlapEnd :
    curveYCMLocalOverlap.toScheme ⟶ curveYCMLocalOverlap.toScheme :=
  curveYCMChartIso.hom.resLE curveYCMLocalOverlap curveYCMLocalOverlap (by
    have hpre : curveYCMChartIso.hom ⁻¹ᵁ curveYCMLocalOverlap =
        curveYCMLocalOverlap := by
      simpa only [curveYCMLocalOverlap] using
        curveYCMChartIso_preimage_overlap
    rw [hpre])

@[reassoc (attr := simp)] theorem curveZCMLocalOverlapEnd_ι :
    curveZCMLocalOverlapEnd ≫ curveZCMLocalOverlap.ι =
      curveZCMLocalOverlap.ι ≫ curveZCMChartIso.hom :=
  Scheme.Hom.resLE_comp_ι _ _

@[reassoc (attr := simp)] theorem curveYCMLocalOverlapEnd_ι :
    curveYCMLocalOverlapEnd ≫ curveYCMLocalOverlap.ι =
      curveYCMLocalOverlap.ι ≫ curveYCMChartIso.hom :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The overlap endomorphism obtained from the Z chart, transported to the fixed
global model of the overlap. -/
def curveZCMOverlapEnd : curveCMOverlap.toScheme ⟶ curveCMOverlap.toScheme :=
  curveZCMLocalOverlapIso.inv ≫ curveZCMLocalOverlapEnd ≫
    curveZCMLocalOverlapIso.hom

/-- The overlap endomorphism obtained from the Y chart, transported to the fixed
global model of the overlap. -/
def curveYCMOverlapEnd : curveCMOverlap.toScheme ⟶ curveCMOverlap.toScheme :=
  curveYCMLocalOverlapIso.inv ≫ curveYCMLocalOverlapEnd ≫
    curveYCMLocalOverlapIso.hom

/-- The fixed overlap is affine, since it is a basic open inside the affine Z chart. -/
theorem curveCMOverlap_isAffine : IsAffineOpen curveCMOverlap := by
  exact curveZOpen_isAffine.basicOpen curveZOverlapCoordinate

theorem curveCMOverlap_le_z : curveCMOverlap ≤ curveZOpen :=
  Scheme.basicOpen_le curve curveZOverlapCoordinate

theorem curveCMOverlap_le_y : curveCMOverlap ≤ curveYOpen := by
  rw [curveCMOverlap, curveZOverlapCoordinate_basicOpen]
  exact inf_le_right

/-- The fixed global overlap included into its Z-chart model. -/
def curveCMOverlapToZ : curveCMOverlap.toScheme ⟶ curveZOpen.toScheme :=
  curveZCMLocalOverlapIso.inv ≫ curveZCMLocalOverlap.ι

/-- The fixed global overlap included into its Y-chart model. -/
def curveCMOverlapToY : curveCMOverlap.toScheme ⟶ curveYOpen.toScheme :=
  curveYCMLocalOverlapIso.inv ≫ curveYCMLocalOverlap.ι

@[reassoc (attr := simp)] theorem curveCMOverlapToZ_ι :
    curveCMOverlapToZ ≫ curveZOpen.ι = curveCMOverlap.ι := by
  rw [curveCMOverlapToZ, Category.assoc]
  calc
    curveZCMLocalOverlapIso.inv ≫
        (curveZCMLocalOverlap.ι ≫ curveZOpen.ι) =
      curveZCMLocalOverlapIso.inv ≫
        (curveZCMLocalOverlapIso.hom ≫ curveCMOverlap.ι) := by
          rw [curveZCMLocalOverlapIso_hom_ι]
    _ = curveCMOverlap.ι := by
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

@[reassoc (attr := simp)] theorem curveCMOverlapToY_ι :
    curveCMOverlapToY ≫ curveYOpen.ι = curveCMOverlap.ι := by
  rw [curveCMOverlapToY, Category.assoc]
  calc
    curveYCMLocalOverlapIso.inv ≫
        (curveYCMLocalOverlap.ι ≫ curveYOpen.ι) =
      curveYCMLocalOverlapIso.inv ≫
        (curveYCMLocalOverlapIso.hom ≫ curveCMOverlap.ι) := by
          rw [curveYCMLocalOverlapIso_hom_ι]
    _ = curveCMOverlap.ι := by
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem curveCMOverlapToZ_eq_homOfLE :
    curveCMOverlapToZ = curve.homOfLE curveCMOverlap_le_z := by
  apply (cancel_mono curveZOpen.ι).mp
  rw [curveCMOverlapToZ_ι, Scheme.homOfLE_ι]

theorem curveCMOverlapToY_eq_homOfLE :
    curveCMOverlapToY = curve.homOfLE curveCMOverlap_le_y := by
  apply (cancel_mono curveYOpen.ι).mp
  rw [curveCMOverlapToY_ι, Scheme.homOfLE_ι]

theorem curveCMOverlapToZ_appTop : curveCMOverlapToZ.appTop =
    curveZOpen.topIso.hom ≫
      CommRingCat.ofHom (curveSectionRestriction curveCMOverlap_le_z).toRingHom ≫
      curveCMOverlap.topIso.inv := by
  rw [curveCMOverlapToZ_eq_homOfLE, homOfLE_appTop_eq_restriction]
  rfl

theorem curveCMOverlapToY_appTop : curveCMOverlapToY.appTop =
    curveYOpen.topIso.hom ≫
      CommRingCat.ofHom (curveSectionRestriction curveCMOverlap_le_y).toRingHom ≫
      curveCMOverlap.topIso.inv := by
  rw [curveCMOverlapToY_eq_homOfLE, homOfLE_appTop_eq_restriction]
  rfl

/-- The overlap endomorphism transported from the Z chart intertwines the global
overlap inclusion with the Z-chart automorphism. -/
@[reassoc] theorem curveZCMOverlapEnd_toZ :
    curveZCMOverlapEnd ≫ curveCMOverlapToZ =
      curveCMOverlapToZ ≫ curveZCMChartIso.hom := by
  simp [curveZCMOverlapEnd, curveCMOverlapToZ, Category.assoc]

/-- The overlap endomorphism transported from the Y chart intertwines the global
overlap inclusion with the Y-chart automorphism. -/
@[reassoc] theorem curveYCMOverlapEnd_toY :
    curveYCMOverlapEnd ≫ curveCMOverlapToY =
      curveCMOverlapToY ≫ curveYCMChartIso.hom := by
  simp [curveYCMOverlapEnd, curveCMOverlapToY, Category.assoc]

/-- On sections obtained from the Z chart, the transported overlap endomorphism
acts by the Z-chart CM ring automorphism. -/
theorem curveZCMOverlapEnd_restriction (r : Γ(curve, curveZOpen)) :
    curveCMOverlap.topIso.hom
        (curveZCMOverlapEnd.appTop
          (curveCMOverlap.topIso.inv
            (curveSectionRestriction curveCMOverlap_le_z r))) =
      curveSectionRestriction curveCMOverlap_le_z (curveZCMEnd r) := by
  apply affineOpenSelfIso_restriction_intertwines
    curveCMOverlap_le_z curveZOpen_isAffine curveZCMAlgEquiv.toRingEquiv
    curveZCMOverlapEnd
  simpa only [curveCMOverlapToZ_eq_homOfLE, curveZCMChartIso] using
    curveZCMOverlapEnd_toZ

/-- On sections obtained from the Y chart, the transported overlap endomorphism
acts by the Y-chart CM ring automorphism. -/
theorem curveYCMOverlapEnd_restriction (r : Γ(curve, curveYOpen)) :
    curveCMOverlap.topIso.hom
        (curveYCMOverlapEnd.appTop
          (curveCMOverlap.topIso.inv
            (curveSectionRestriction curveCMOverlap_le_y r))) =
      curveSectionRestriction curveCMOverlap_le_y (curveYCMEnd r) := by
  apply affineOpenSelfIso_restriction_intertwines
    curveCMOverlap_le_y curveYOpen_isAffine curveYCMAlgEquiv.toRingEquiv
    curveYCMOverlapEnd
  simpa only [curveCMOverlapToY_eq_homOfLE, curveYCMChartIso] using
    curveYCMOverlapEnd_toY

/-! ## Equality of the two overlap maps -/

/-- Pullback on the section ring of the common overlap, computed from the Z chart. -/
def curveZCMOverlapRingEnd : Γ(curve, curveCMOverlap) →+* Γ(curve, curveCMOverlap) :=
  (curveCMOverlap.topIso.inv ≫ curveZCMOverlapEnd.appTop ≫
    curveCMOverlap.topIso.hom).hom

/-- Pullback on the section ring of the common overlap, computed from the Y chart. -/
def curveYCMOverlapRingEnd : Γ(curve, curveCMOverlap) →+* Γ(curve, curveCMOverlap) :=
  (curveCMOverlap.topIso.inv ≫ curveYCMOverlapEnd.appTop ≫
    curveCMOverlap.topIso.hom).hom

@[simp] theorem curveZCMOverlapRingEnd_restriction (r : Γ(curve, curveZOpen)) :
    curveZCMOverlapRingEnd (curveSectionRestriction curveCMOverlap_le_z r) =
      curveSectionRestriction curveCMOverlap_le_z (curveZCMEnd r) := by
  exact curveZCMOverlapEnd_restriction r

@[simp] theorem curveYCMOverlapRingEnd_restriction (r : Γ(curve, curveYOpen)) :
    curveYCMOverlapRingEnd (curveSectionRestriction curveCMOverlap_le_y r) =
      curveSectionRestriction curveCMOverlap_le_y (curveYCMEnd r) := by
  exact curveYCMOverlapEnd_restriction r

@[simp] theorem curveYCMOverlapRingEnd_algebraMap (c : ℂ) :
    curveYCMOverlapRingEnd (algebraMap ℂ Γ(curve, curveCMOverlap) c) =
      algebraMap ℂ Γ(curve, curveCMOverlap) c := by
  rw [← (curveSectionRestriction curveCMOverlap_le_y).commutes c,
    curveYCMOverlapRingEnd_restriction, (curveYCMEnd).commutes,
    (curveSectionRestriction curveCMOverlap_le_y).commutes]

/-- The restriction of the Z-chart coordinate `X/Z` to the overlap. -/
def curveCMOverlapZX : Γ(curve, curveCMOverlap) :=
  curveSectionRestriction curveCMOverlap_le_z
    (hypersurfaceCoordinateMap
      (chartEquation (Equiv.refl (Fin 3)))
      (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime) (X 0))

/-- The restriction of the Z-chart coordinate `Y/Z` to the overlap. -/
def curveCMOverlapZY : Γ(curve, curveCMOverlap) :=
  curveSectionRestriction curveCMOverlap_le_z
    (hypersurfaceCoordinateMap
      (chartEquation (Equiv.refl (Fin 3)))
      (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime) (X 1))

/-- The restriction of the Y-chart coordinate `X/Y` to the overlap. -/
def curveCMOverlapYU : Γ(curve, curveCMOverlap) :=
  curveSectionRestriction curveCMOverlap_le_y
    (hypersurfaceCoordinateMap
      (chartEquation (Equiv.swap (1 : Fin 3) 2))
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime) (X 0))

/-- The restriction of the Y-chart coordinate `Z/Y` to the overlap. -/
def curveCMOverlapYV : Γ(curve, curveCMOverlap) :=
  curveSectionRestriction curveCMOverlap_le_y
    (hypersurfaceCoordinateMap
      (chartEquation (Equiv.swap (1 : Fin 3) 2))
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime) (X 1))

theorem curveCMOverlap_x_mul_v :
    curveCMOverlapZX * curveCMOverlapYV = curveCMOverlapYU := by
  dsimp only [curveCMOverlapZX, curveCMOverlapYV, curveCMOverlapYU]
  simp only [curveSectionRestriction_coordinate]
  exact (ProjectiveRatioSections.pullRatio_transition (ULift ℤ) curveToIntegerPlane
    curveCMOverlap 1 2 0 curveCMOverlap_le_y curveCMOverlap_le_z).symm

theorem curveCMOverlap_y_mul_v :
    curveCMOverlapZY * curveCMOverlapYV = 1 := by
  dsimp only [curveCMOverlapZY, curveCMOverlapYV]
  simp only [curveSectionRestriction_coordinate]
  have ht := ProjectiveRatioSections.pullRatio_transition (ULift ℤ) curveToIntegerPlane
    curveCMOverlap 1 2 1 curveCMOverlap_le_y curveCMOverlap_le_z
  simp only [ProjectiveRatioSections.pullRatio_self] at ht
  exact ht.symm

@[simp] theorem curveYCMOverlapRingEnd_YU :
    curveYCMOverlapRingEnd curveCMOverlapYU = Complex.I • curveCMOverlapYU := by
  rw [curveCMOverlapYU, curveYCMOverlapRingEnd_restriction,
    curveYCMEnd_coordinate_zero, map_smul]

@[simp] theorem curveYCMOverlapRingEnd_YV :
    curveYCMOverlapRingEnd curveCMOverlapYV = -(Complex.I • curveCMOverlapYV) := by
  rw [curveCMOverlapYV, curveYCMOverlapRingEnd_restriction,
    curveYCMEnd_coordinate_one, map_neg, map_smul]

/-- The Y-chart overlap map gives the expected CM action on `X/Z`. -/
theorem curveYCMOverlapRingEnd_ZX :
    curveYCMOverlapRingEnd curveCMOverlapZX = -curveCMOverlapZX := by
  have hm := congrArg curveYCMOverlapRingEnd curveCMOverlap_x_mul_v
  simp only [map_mul] at hm
  rw [curveYCMOverlapRingEnd_YU] at hm
  have hy := congrArg curveYCMOverlapRingEnd curveCMOverlap_y_mul_v
  simp only [map_mul, map_one] at hy
  have he : (-curveCMOverlapZX) * curveYCMOverlapRingEnd curveCMOverlapYV =
      Complex.I • curveCMOverlapYU := by
    rw [curveYCMOverlapRingEnd_YV, ← curveCMOverlap_x_mul_v]
    simp [Algebra.smul_def]
    ring
  calc
    curveYCMOverlapRingEnd curveCMOverlapZX =
        curveYCMOverlapRingEnd curveCMOverlapZX * 1 := (mul_one _).symm
    _ = curveYCMOverlapRingEnd curveCMOverlapZX *
        (curveYCMOverlapRingEnd curveCMOverlapZY *
          curveYCMOverlapRingEnd curveCMOverlapYV) := by rw [hy]
    _ = curveYCMOverlapRingEnd curveCMOverlapZY *
        (curveYCMOverlapRingEnd curveCMOverlapZX *
          curveYCMOverlapRingEnd curveCMOverlapYV) := by ring
    _ = curveYCMOverlapRingEnd curveCMOverlapZY *
        (Complex.I • curveCMOverlapYU) := by rw [hm]
    _ = curveYCMOverlapRingEnd curveCMOverlapZY *
        ((-curveCMOverlapZX) * curveYCMOverlapRingEnd curveCMOverlapYV) := by rw [he]
    _ = (-curveCMOverlapZX) *
        (curveYCMOverlapRingEnd curveCMOverlapZY *
          curveYCMOverlapRingEnd curveCMOverlapYV) := by ring
    _ = -curveCMOverlapZX := by rw [hy, mul_one]

/-- The Y-chart overlap map gives the expected CM action on `Y/Z`. -/
theorem curveYCMOverlapRingEnd_ZY :
    curveYCMOverlapRingEnd curveCMOverlapZY = Complex.I • curveCMOverlapZY := by
  have hm := congrArg curveYCMOverlapRingEnd curveCMOverlap_y_mul_v
  simp only [map_mul, map_one] at hm
  have he : (Complex.I • curveCMOverlapZY) *
      curveYCMOverlapRingEnd curveCMOverlapYV = 1 := by
    rw [curveYCMOverlapRingEnd_YV]
    simp only [Algebra.smul_def]
    have hI : algebraMap ℂ Γ(curve, curveCMOverlap) Complex.I *
        algebraMap ℂ Γ(curve, curveCMOverlap) Complex.I = -1 := by
      rw [← map_mul]
      simp [Complex.I_sq]
    calc
      (algebraMap ℂ Γ(curve, curveCMOverlap) Complex.I * curveCMOverlapZY) *
          -(algebraMap ℂ Γ(curve, curveCMOverlap) Complex.I * curveCMOverlapYV) =
        -(algebraMap ℂ Γ(curve, curveCMOverlap) Complex.I *
          algebraMap ℂ Γ(curve, curveCMOverlap) Complex.I) *
            (curveCMOverlapZY * curveCMOverlapYV) := by ring
      _ = curveCMOverlapZY * curveCMOverlapYV := by rw [hI]; ring
      _ = 1 := curveCMOverlap_y_mul_v
  calc
    curveYCMOverlapRingEnd curveCMOverlapZY =
        curveYCMOverlapRingEnd curveCMOverlapZY * 1 := (mul_one _).symm
    _ = curveYCMOverlapRingEnd curveCMOverlapZY *
        (curveYCMOverlapRingEnd curveCMOverlapZY *
          curveYCMOverlapRingEnd curveCMOverlapYV) := by rw [hm]
    _ = curveYCMOverlapRingEnd curveCMOverlapZY * 1 := by rw [hm]
    _ = curveYCMOverlapRingEnd curveCMOverlapZY *
        ((Complex.I • curveCMOverlapZY) *
          curveYCMOverlapRingEnd curveCMOverlapYV) := by rw [he]
    _ = (Complex.I • curveCMOverlapZY) *
        (curveYCMOverlapRingEnd curveCMOverlapZY *
          curveYCMOverlapRingEnd curveCMOverlapYV) := by ring
    _ = Complex.I • curveCMOverlapZY := by rw [hm, mul_one]

theorem curveCMOverlapRingEnds_comp_restriction :
    curveZCMOverlapRingEnd.comp
        (curveSectionRestriction curveCMOverlap_le_z).toRingHom =
      curveYCMOverlapRingEnd.comp
        (curveSectionRestriction curveCMOverlap_le_z).toRingHom := by
  ext r
  change curveCMOverlap.topIso.hom
      (curveZCMOverlapEnd.appTop
        (curveCMOverlap.topIso.inv
          (curveSectionRestriction curveCMOverlap_le_z r))) =
    curveCMOverlap.topIso.hom
      (curveYCMOverlapEnd.appTop
        (curveCMOverlap.topIso.inv
          (curveSectionRestriction curveCMOverlap_le_z r)))
  rw [curveZCMOverlapEnd_restriction]
  obtain ⟨p, hp⟩ := hypersurfaceCoordinateMap_surjective
    (chartEquation (Equiv.refl (Fin 3)))
    (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime) r
  rw [← hp]
  let coord := hypersurfaceCoordinateMap
    (chartEquation (Equiv.refl (Fin 3)))
    (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime)
  let f : ZPoly →+* Γ(curve, curveCMOverlap) :=
    (curveSectionRestriction curveCMOverlap_le_z).toRingHom.comp
      ((curveZCMEnd).toRingHom.comp coord.toRingHom)
  let g : ZPoly →+* Γ(curve, curveCMOverlap) :=
    curveYCMOverlapRingEnd.comp
      ((curveSectionRestriction curveCMOverlap_le_z).toRingHom.comp coord.toRingHom)
  have hfg : f = g := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change curveSectionRestriction curveCMOverlap_le_z
          (curveZCMEnd (coord (C c))) =
        curveYCMOverlapRingEnd
          (curveSectionRestriction curveCMOverlap_le_z (coord (C c)))
      rw [show coord (C c) = algebraMap ℂ Γ(curve, curveZOpen) c from coord.commutes c,
        (curveZCMEnd).commutes, (curveSectionRestriction curveCMOverlap_le_z).commutes,
        curveYCMOverlapRingEnd_algebraMap]
    · intro j
      fin_cases j
      · change curveSectionRestriction curveCMOverlap_le_z
            (curveZCMEnd (coord (X 0))) =
          curveYCMOverlapRingEnd
            (curveSectionRestriction curveCMOverlap_le_z (coord (X 0)))
        rw [curveZCMEnd_coordinate_zero, map_neg]
        exact curveYCMOverlapRingEnd_ZX.symm
      · change curveSectionRestriction curveCMOverlap_le_z
            (curveZCMEnd (coord (X 1))) =
          curveYCMOverlapRingEnd
            (curveSectionRestriction curveCMOverlap_le_z (coord (X 1)))
        rw [curveZCMEnd_coordinate_one, map_smul]
        exact curveYCMOverlapRingEnd_ZY.symm
  exact RingHom.congr_fun hfg p

/-- The two affine formulas define the same ring endomorphism on the overlap. -/
theorem curveZCMOverlapRingEnd_eq_curveYCMOverlapRingEnd :
    curveZCMOverlapRingEnd = curveYCMOverlapRingEnd := by
  letI : Algebra Γ(curve, curveZOpen) Γ(curve, curveCMOverlap) :=
    (curveSectionRestriction curveCMOverlap_le_z).toRingHom.toAlgebra
  letI : IsLocalization.Away curveZOverlapCoordinate Γ(curve, curveCMOverlap) := by
    change IsLocalization.Away curveZOverlapCoordinate
      Γ(curve, curve.basicOpen curveZOverlapCoordinate)
    exact curveZOpen_isAffine.isLocalization_basicOpen curveZOverlapCoordinate
  apply IsLocalization.ringHom_ext (.powers curveZOverlapCoordinate)
  change curveZCMOverlapRingEnd.comp
      (curveSectionRestriction curveCMOverlap_le_z).toRingHom =
    curveYCMOverlapRingEnd.comp
      (curveSectionRestriction curveCMOverlap_le_z).toRingHom
  exact curveCMOverlapRingEnds_comp_restriction

/-- The CM scheme morphisms constructed on the two affine charts agree on their
common overlap. -/
theorem curveZCMOverlapEnd_eq_curveYCMOverlapEnd :
    curveZCMOverlapEnd = curveYCMOverlapEnd := by
  letI : IsAffine curveCMOverlap.toScheme := curveCMOverlap_isAffine
  apply ext_of_isAffine
  have h : curveCMOverlap.topIso.inv ≫ curveZCMOverlapEnd.appTop ≫
        curveCMOverlap.topIso.hom =
      curveCMOverlap.topIso.inv ≫ curveYCMOverlapEnd.appTop ≫
        curveCMOverlap.topIso.hom :=
    CommRingCat.hom_ext curveZCMOverlapRingEnd_eq_curveYCMOverlapRingEnd
  apply (cancel_epi curveCMOverlap.topIso.inv).mp
  apply (cancel_mono curveCMOverlap.topIso.hom).mp
  simpa only [Category.assoc] using h

/-! ## The global CM endomorphism -/

/-- The two local CM formulas agree after inclusion in the projective curve. -/
theorem curveCMChartMaps_overlap :
    curve.homOfLE (inf_le_left : curveZOpen ⊓ curveYOpen ≤ curveZOpen) ≫
        curveZCMChartIso.hom ≫ curveZOpen.ι =
      curve.homOfLE (inf_le_right : curveZOpen ⊓ curveYOpen ≤ curveYOpen) ≫
        curveYCMChartIso.hom ≫ curveYOpen.ι := by
  let e : curveCMOverlap.toScheme ≅ (curveZOpen ⊓ curveYOpen).toScheme :=
    curve.isoOfEq curveZOverlapCoordinate_basicOpen
  have hz : e.hom ≫
      curve.homOfLE (inf_le_left : curveZOpen ⊓ curveYOpen ≤ curveZOpen) =
        curveCMOverlapToZ := by
    apply (cancel_mono curveZOpen.ι).mp
    simp [e, curveCMOverlapToZ_ι]
  have hy : e.hom ≫
      curve.homOfLE (inf_le_right : curveZOpen ⊓ curveYOpen ≤ curveYOpen) =
        curveCMOverlapToY := by
    apply (cancel_mono curveYOpen.ι).mp
    simp [e, curveCMOverlapToY_ι]
  apply (cancel_epi e.hom).mp
  simp only [← Category.assoc]
  rw [hz, hy]
  rw [← curveZCMOverlapEnd_toZ, ← curveYCMOverlapEnd_toY]
  simp only [Category.assoc, curveZCMOverlapEnd_eq_curveYCMOverlapEnd,
    curveCMOverlapToZ_ι, curveCMOverlapToY_ι]

/-- The two standard affine charts, ordered Z then Y. -/
abbrev curveCMCover : curve.OpenCover := curve.openCoverOfIsOpenCover
    (fun i : Fin 2 => ![curveZOpen, curveYOpen] i) (by
      apply top_unique
      rw [← chart_one_sup_chart_two]
      exact sup_le
        (le_iSup (fun i : Fin 2 => ![curveZOpen, curveYOpen] i) 1)
        (le_iSup (fun i : Fin 2 => ![curveZOpen, curveYOpen] i) 0))

/-- The two affine CM formulas, followed by their inclusions into the curve. -/
def curveCMLocalMap : ∀ i : Fin 2, (curveCMCover.X i) ⟶ curve :=
  Fin.cases (curveZCMChartIso.hom ≫ curveZOpen.ι)
    (Fin.cases (curveYCMChartIso.hom ≫ curveYOpen.ι) (fun i => i.elim0))

theorem curveCMLocalMap_compatible (i j : Fin 2) :
    pullback.fst (curveCMCover.f i) (curveCMCover.f j) ≫ curveCMLocalMap i =
      pullback.snd (curveCMCover.f i) (curveCMCover.f j) ≫ curveCMLocalMap j := by
  fin_cases i <;> fin_cases j
  · congr 1
    exact (cancel_mono (curveCMCover.f _)).mp pullback.condition
  · change pullback.fst curveZOpen.ι curveYOpen.ι ≫
        (curveZCMChartIso.hom ≫ curveZOpen.ι) =
      pullback.snd curveZOpen.ι curveYOpen.ι ≫
        (curveYCMChartIso.hom ≫ curveYOpen.ι)
    rw [← cancel_epi (isPullback_opens_inf curveZOpen curveYOpen).isoPullback.hom]
    simpa only [IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_snd_assoc] using curveCMChartMaps_overlap
  · change pullback.fst curveYOpen.ι curveZOpen.ι ≫
        (curveYCMChartIso.hom ≫ curveYOpen.ι) =
      pullback.snd curveYOpen.ι curveZOpen.ι ≫
        (curveZCMChartIso.hom ≫ curveZOpen.ι)
    rw [← cancel_epi (isPullback_opens_inf curveYOpen curveZOpen).isoPullback.hom]
    simp only [IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_snd_assoc]
    let e : (curveZOpen ⊓ curveYOpen).toScheme ≅
        (curveYOpen ⊓ curveZOpen).toScheme := curve.isoOfEq (inf_comm _ _)
    apply (cancel_epi e.hom).mp
    have hy : e.hom ≫
        curve.homOfLE (inf_le_left : curveYOpen ⊓ curveZOpen ≤ curveYOpen) =
          curve.homOfLE (inf_le_right : curveZOpen ⊓ curveYOpen ≤ curveYOpen) := by
      apply (cancel_mono curveYOpen.ι).mp
      simp [e]
    have hz : e.hom ≫
        curve.homOfLE (inf_le_right : curveYOpen ⊓ curveZOpen ≤ curveZOpen) =
          curve.homOfLE (inf_le_left : curveZOpen ⊓ curveYOpen ≤ curveZOpen) := by
      apply (cancel_mono curveZOpen.ι).mp
      simp [e]
    simp only [← Category.assoc]
    rw [hy, hz]
    exact curveCMChartMaps_overlap.symm
  · congr 1
    exact (cancel_mono (curveCMCover.f _)).mp pullback.condition

/-- The global algebraic self-map `[X:Y:Z] ↦ [-X:iY:Z]` of the explicit cubic. -/
def curveCMEnd : curve ⟶ curve :=
  curveCMCover.glueMorphisms curveCMLocalMap curveCMLocalMap_compatible

/-- On the Z chart, the global CM map is the explicit affine CM automorphism. -/
@[reassoc] theorem curveZOpen_ι_curveCMEnd :
    curveZOpen.ι ≫ curveCMEnd = curveZCMChartIso.hom ≫ curveZOpen.ι := by
  have h := curveCMCover.ι_glueMorphisms
    curveCMLocalMap curveCMLocalMap_compatible (0 : Fin 2)
  change curveZOpen.ι ≫ curveCMEnd =
    curveZCMChartIso.hom ≫ curveZOpen.ι at h
  exact h

/-- On the Y chart, the global CM map is the explicit affine CM automorphism. -/
@[reassoc] theorem curveYOpen_ι_curveCMEnd :
    curveYOpen.ι ≫ curveCMEnd = curveYCMChartIso.hom ≫ curveYOpen.ι := by
  have h := curveCMCover.ι_glueMorphisms
    curveCMLocalMap curveCMLocalMap_compatible (1 : Fin 2)
  change curveYOpen.ι ≫ curveCMEnd =
    curveYCMChartIso.hom ≫ curveYOpen.ι at h
  exact h

theorem curveZCMRingHom_four :
    CommRingCat.ofHom curveZCMAlgEquiv.toRingEquiv.toRingHom ≫
        CommRingCat.ofHom curveZCMAlgEquiv.toRingEquiv.toRingHom ≫
        CommRingCat.ofHom curveZCMAlgEquiv.toRingEquiv.toRingHom ≫
        CommRingCat.ofHom curveZCMAlgEquiv.toRingEquiv.toRingHom =
      𝟙 (CommRingCat.of Γ(curve, curveZOpen)) := by
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom curveZCMEnd_four

theorem curveYCMRingHom_four :
    CommRingCat.ofHom curveYCMAlgEquiv.toRingEquiv.toRingHom ≫
        CommRingCat.ofHom curveYCMAlgEquiv.toRingEquiv.toRingHom ≫
        CommRingCat.ofHom curveYCMAlgEquiv.toRingEquiv.toRingHom ≫
        CommRingCat.ofHom curveYCMAlgEquiv.toRingEquiv.toRingHom =
      𝟙 (CommRingCat.of Γ(curve, curveYOpen)) := by
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom curveYCMEnd_four

theorem curveZCMChartIso_hom_four :
    curveZCMChartIso.hom ≫ curveZCMChartIso.hom ≫
        curveZCMChartIso.hom ≫ curveZCMChartIso.hom =
      𝟙 curveZOpen.toScheme := by
  letI : IsAffine curveZOpen.toScheme := curveZOpen_isAffine
  apply ext_of_isAffine
  simp only [Scheme.Hom.comp_appTop]
  rw [curveZCMChartIso_appTop]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  calc
    _ = curveZOpen.topIso.hom ≫
        (CommRingCat.ofHom curveZCMAlgEquiv.toRingEquiv.toRingHom ≫
          CommRingCat.ofHom curveZCMAlgEquiv.toRingEquiv.toRingHom ≫
          CommRingCat.ofHom curveZCMAlgEquiv.toRingEquiv.toRingHom ≫
          CommRingCat.ofHom curveZCMAlgEquiv.toRingEquiv.toRingHom) ≫
        curveZOpen.topIso.inv := by simp only [Category.assoc]
    _ = _ := by
      rw [curveZCMRingHom_four]
      simp only [Category.comp_id, Category.id_comp, Scheme.Hom.id_appTop]
      exact curveZOpen.topIso.hom_inv_id

theorem curveYCMChartIso_hom_four :
    curveYCMChartIso.hom ≫ curveYCMChartIso.hom ≫
        curveYCMChartIso.hom ≫ curveYCMChartIso.hom =
      𝟙 curveYOpen.toScheme := by
  letI : IsAffine curveYOpen.toScheme := curveYOpen_isAffine
  apply ext_of_isAffine
  simp only [Scheme.Hom.comp_appTop]
  rw [curveYCMChartIso_appTop]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  calc
    _ = curveYOpen.topIso.hom ≫
        (CommRingCat.ofHom curveYCMAlgEquiv.toRingEquiv.toRingHom ≫
          CommRingCat.ofHom curveYCMAlgEquiv.toRingEquiv.toRingHom ≫
          CommRingCat.ofHom curveYCMAlgEquiv.toRingEquiv.toRingHom ≫
          CommRingCat.ofHom curveYCMAlgEquiv.toRingEquiv.toRingHom) ≫
        curveYOpen.topIso.inv := by simp only [Category.assoc]
    _ = _ := by
      rw [curveYCMRingHom_four]
      simp only [Category.comp_id, Category.id_comp, Scheme.Hom.id_appTop]
      exact curveYOpen.topIso.hom_inv_id

/-- The global CM endomorphism has order dividing four. -/
theorem curveCMEnd_four :
    curveCMEnd ≫ curveCMEnd ≫ curveCMEnd ≫ curveCMEnd = 𝟙 curve := by
  apply Scheme.hom_ext_of_forall
  intro x
  have hx : x ∈ curveYOpen ⊔ curveZOpen := by
    change x ∈ chart 1 ⊔ chart 2
    rw [chart_one_sup_chart_two]
    trivial
  rcases hx with hx | hx
  · refine ⟨curveYOpen, hx, ?_⟩
    simp only [Category.assoc, curveYOpen_ι_curveCMEnd_assoc]
    rw [curveYOpen_ι_curveCMEnd]
    calc
      curveYCMChartIso.hom ≫ curveYCMChartIso.hom ≫
          curveYCMChartIso.hom ≫ curveYCMChartIso.hom ≫ curveYOpen.ι =
        (curveYCMChartIso.hom ≫ curveYCMChartIso.hom ≫
          curveYCMChartIso.hom ≫ curveYCMChartIso.hom) ≫ curveYOpen.ι := by
            simp only [Category.assoc]
      _ = curveYOpen.ι := by rw [curveYCMChartIso_hom_four, Category.id_comp]
      _ = curveYOpen.ι ≫ 𝟙 curve := (Category.comp_id _).symm
  · refine ⟨curveZOpen, hx, ?_⟩
    simp only [Category.assoc, curveZOpen_ι_curveCMEnd_assoc]
    rw [curveZOpen_ι_curveCMEnd]
    calc
      curveZCMChartIso.hom ≫ curveZCMChartIso.hom ≫
          curveZCMChartIso.hom ≫ curveZCMChartIso.hom ≫ curveZOpen.ι =
        (curveZCMChartIso.hom ≫ curveZCMChartIso.hom ≫
          curveZCMChartIso.hom ≫ curveZCMChartIso.hom) ≫ curveZOpen.ι := by
            simp only [Category.assoc]
      _ = curveZOpen.ι := by rw [curveZCMChartIso_hom_four, Category.id_comp]
      _ = curveZOpen.ι ≫ 𝟙 curve := (Category.comp_id _).symm

end AlgebraicGeometry.ExplicitEllipticCandidate
