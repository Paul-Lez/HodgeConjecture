import Other.AlgebraicGeometry.ExplicitEllipticCMGlobal

open CategoryTheory MvPolynomial
open AlgebraicGeometry
open AlgebraicGeometry.ExplicitEllipticCandidate

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

#check AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen
#check IsLocalization.ringHom_ext
#check CommRingCat.hom_ext
#check AlgebraicGeometry.ext_of_isAffine
#check ProjectiveRatioSections.pullRatio_transition
#check ProjectiveRatioSections.pullRatio_self
#check Scheme.openCoverOfIsOpenCover
#check Scheme.isoOfEq
#check Scheme.Cover.hom_ext
#check Scheme.basicOpen
#check Scheme.Hom.resLE

example : IsLocalization.Away curveZOverlapCoordinate
    Γ(curve, curve.basicOpen curveZOverlapCoordinate) := by
  exact curveZOpen_isAffine.isLocalization_basicOpen curveZOverlapCoordinate

def zEndOnOverlapRing :
    Γ(curve, curveCMOverlap) →+* Γ(curve, curveCMOverlap) :=
  (curveCMOverlap.topIso.inv ≫ curveZCMOverlapEnd.appTop ≫
    curveCMOverlap.topIso.hom).hom

def yEndOnOverlapRing :
    Γ(curve, curveCMOverlap) →+* Γ(curve, curveCMOverlap) :=
  (curveCMOverlap.topIso.inv ≫ curveYCMOverlapEnd.appTop ≫
    curveCMOverlap.topIso.hom).hom

@[simp] theorem zEndOnOverlapRing_restriction (r : Γ(curve, curveZOpen)) :
    zEndOnOverlapRing (curveSectionRestriction curveCMOverlap_le_z r) =
      curveSectionRestriction curveCMOverlap_le_z (curveZCMEnd r) := by
  exact curveZCMOverlapEnd_restriction r

@[simp] theorem yEndOnOverlapRing_restriction (r : Γ(curve, curveYOpen)) :
    yEndOnOverlapRing (curveSectionRestriction curveCMOverlap_le_y r) =
      curveSectionRestriction curveCMOverlap_le_y (curveYCMEnd r) := by
  exact curveYCMOverlapEnd_restriction r

@[simp] theorem yEndOnOverlapRing_algebraMap (c : ℂ) :
    yEndOnOverlapRing
        (algebraMap ℂ Γ(curve, curveCMOverlap) c) =
      algebraMap ℂ Γ(curve, curveCMOverlap) c := by
  rw [← (curveSectionRestriction curveCMOverlap_le_y).commutes c,
    yEndOnOverlapRing_restriction, (curveYCMEnd).commutes,
    (curveSectionRestriction curveCMOverlap_le_y).commutes]

def overlapZX : Γ(curve, curveCMOverlap) :=
  curveSectionRestriction curveCMOverlap_le_z
    (hypersurfaceCoordinateMap
      (chartEquation (Equiv.refl (Fin 3)))
      (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime) (X 0))

def overlapZY : Γ(curve, curveCMOverlap) :=
  curveSectionRestriction curveCMOverlap_le_z
    (hypersurfaceCoordinateMap
      (chartEquation (Equiv.refl (Fin 3)))
      (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime) (X 1))

def overlapYU : Γ(curve, curveCMOverlap) :=
  curveSectionRestriction curveCMOverlap_le_y
    (hypersurfaceCoordinateMap
      (chartEquation (Equiv.swap (1 : Fin 3) 2))
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime) (X 0))

def overlapYV : Γ(curve, curveCMOverlap) :=
  curveSectionRestriction curveCMOverlap_le_y
    (hypersurfaceCoordinateMap
      (chartEquation (Equiv.swap (1 : Fin 3) 2))
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime) (X 1))

theorem overlap_x_mul_v : overlapZX * overlapYV = overlapYU := by
  dsimp only [overlapZX, overlapYV, overlapYU]
  simp only [curveSectionRestriction_coordinate]
  exact (ProjectiveRatioSections.pullRatio_transition (ULift ℤ) curveToIntegerPlane
    curveCMOverlap 1 2 0 curveCMOverlap_le_y curveCMOverlap_le_z).symm

theorem overlap_y_mul_v : overlapZY * overlapYV = 1 := by
  dsimp only [overlapZY, overlapYV]
  simp only [curveSectionRestriction_coordinate]
  have ht := ProjectiveRatioSections.pullRatio_transition (ULift ℤ) curveToIntegerPlane
    curveCMOverlap 1 2 1 curveCMOverlap_le_y curveCMOverlap_le_z
  simp only [ProjectiveRatioSections.pullRatio_self] at ht
  exact ht.symm

@[simp] theorem yEnd_overlapYU :
    yEndOnOverlapRing overlapYU = Complex.I • overlapYU := by
  rw [overlapYU, yEndOnOverlapRing_restriction, curveYCMEnd_coordinate_zero,
    map_smul]

@[simp] theorem yEnd_overlapYV :
    yEndOnOverlapRing overlapYV = -(Complex.I • overlapYV) := by
  rw [overlapYV, yEndOnOverlapRing_restriction, curveYCMEnd_coordinate_one,
    map_neg, map_smul]

theorem yEnd_overlapZX : yEndOnOverlapRing overlapZX = -overlapZX := by
  have hm := congrArg yEndOnOverlapRing overlap_x_mul_v
  simp only [map_mul] at hm
  rw [yEnd_overlapYU] at hm
  have hy := congrArg yEndOnOverlapRing overlap_y_mul_v
  simp only [map_mul, map_one] at hy
  have he : (-overlapZX) * yEndOnOverlapRing overlapYV =
      Complex.I • overlapYU := by
    rw [yEnd_overlapYV, ← overlap_x_mul_v]
    simp [Algebra.smul_def]
    ring
  calc
    yEndOnOverlapRing overlapZX =
        yEndOnOverlapRing overlapZX * 1 := (mul_one _).symm
    _ = yEndOnOverlapRing overlapZX *
        (yEndOnOverlapRing overlapZY * yEndOnOverlapRing overlapYV) := by rw [hy]
    _ = yEndOnOverlapRing overlapZY *
        (yEndOnOverlapRing overlapZX * yEndOnOverlapRing overlapYV) := by ring
    _ = yEndOnOverlapRing overlapZY * (Complex.I • overlapYU) := by rw [hm]
    _ = yEndOnOverlapRing overlapZY * ((-overlapZX) *
        yEndOnOverlapRing overlapYV) := by rw [he]
    _ = (-overlapZX) *
        (yEndOnOverlapRing overlapZY * yEndOnOverlapRing overlapYV) := by ring
    _ = -overlapZX := by rw [hy, mul_one]

theorem yEnd_overlapZY : yEndOnOverlapRing overlapZY = Complex.I • overlapZY := by
  have hm := congrArg yEndOnOverlapRing overlap_y_mul_v
  simp only [map_mul, map_one] at hm
  have he : (Complex.I • overlapZY) * yEndOnOverlapRing overlapYV = 1 := by
    rw [yEnd_overlapYV]
    simp only [Algebra.smul_def]
    have hI : algebraMap ℂ Γ(curve, curveCMOverlap) Complex.I *
        algebraMap ℂ Γ(curve, curveCMOverlap) Complex.I = -1 := by
      rw [← map_mul]
      simp [Complex.I_sq]
    calc
      (algebraMap ℂ Γ(curve, curveCMOverlap) Complex.I * overlapZY) *
          -(algebraMap ℂ Γ(curve, curveCMOverlap) Complex.I * overlapYV) =
        -(algebraMap ℂ Γ(curve, curveCMOverlap) Complex.I *
          algebraMap ℂ Γ(curve, curveCMOverlap) Complex.I) *
            (overlapZY * overlapYV) := by ring
      _ = overlapZY * overlapYV := by rw [hI]; ring
      _ = 1 := overlap_y_mul_v
  calc
    yEndOnOverlapRing overlapZY =
        yEndOnOverlapRing overlapZY * 1 := (mul_one _).symm
    _ = yEndOnOverlapRing overlapZY *
        (yEndOnOverlapRing overlapZY * yEndOnOverlapRing overlapYV) := by rw [hm]
    _ = yEndOnOverlapRing overlapZY * 1 := by rw [hm]
    _ = yEndOnOverlapRing overlapZY *
        ((Complex.I • overlapZY) * yEndOnOverlapRing overlapYV) := by rw [he]
    _ = (Complex.I • overlapZY) *
        (yEndOnOverlapRing overlapZY * yEndOnOverlapRing overlapYV) := by ring
    _ = Complex.I • overlapZY := by rw [hm, mul_one]

theorem overlapRingEnds_comp_restriction : zEndOnOverlapRing.comp
      (curveSectionRestriction curveCMOverlap_le_z).toRingHom =
    yEndOnOverlapRing.comp
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
    yEndOnOverlapRing.comp
      ((curveSectionRestriction curveCMOverlap_le_z).toRingHom.comp coord.toRingHom)
  have hfg : f = g := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change curveSectionRestriction curveCMOverlap_le_z
          (curveZCMEnd (coord (C c))) =
        yEndOnOverlapRing
          (curveSectionRestriction curveCMOverlap_le_z (coord (C c)))
      rw [show coord (C c) = algebraMap ℂ Γ(curve, curveZOpen) c from coord.commutes c,
        (curveZCMEnd).commutes, (curveSectionRestriction curveCMOverlap_le_z).commutes,
        yEndOnOverlapRing_algebraMap]
    · intro j
      fin_cases j
      · change curveSectionRestriction curveCMOverlap_le_z
            (curveZCMEnd (coord (X 0))) =
          yEndOnOverlapRing
            (curveSectionRestriction curveCMOverlap_le_z (coord (X 0)))
        rw [curveZCMEnd_coordinate_zero, map_neg]
        exact yEnd_overlapZX.symm
      · change curveSectionRestriction curveCMOverlap_le_z
            (curveZCMEnd (coord (X 1))) =
          yEndOnOverlapRing
            (curveSectionRestriction curveCMOverlap_le_z (coord (X 1)))
        rw [curveZCMEnd_coordinate_one, map_smul]
        exact yEnd_overlapZY.symm
  exact RingHom.congr_fun hfg p

example : zEndOnOverlapRing = yEndOnOverlapRing := by
  letI : Algebra Γ(curve, curveZOpen) Γ(curve, curveCMOverlap) :=
    (curveSectionRestriction curveCMOverlap_le_z).toRingHom.toAlgebra
  letI : IsLocalization.Away curveZOverlapCoordinate Γ(curve, curveCMOverlap) := by
    change IsLocalization.Away curveZOverlapCoordinate
      Γ(curve, curve.basicOpen curveZOverlapCoordinate)
    exact curveZOpen_isAffine.isLocalization_basicOpen curveZOverlapCoordinate
  apply IsLocalization.ringHom_ext (.powers curveZOverlapCoordinate)
  change zEndOnOverlapRing.comp
      (curveSectionRestriction curveCMOverlap_le_z).toRingHom =
    yEndOnOverlapRing.comp
      (curveSectionRestriction curveCMOverlap_le_z).toRingHom
  exact overlapRingEnds_comp_restriction
