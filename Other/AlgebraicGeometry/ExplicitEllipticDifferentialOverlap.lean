/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticDifferentials
public import Other.AlgebraicGeometry.ExplicitProjectiveRatioSections
public import Mathlib.Tactic.LinearCombination

/-!
# Agreement of the elliptic curve's regular differentials

The coordinate changes are identities in the actual section ring of the overlap.
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry.ExplicitEllipticCandidate

attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The invariant differential is unchanged by `u = x/y`, `v = 1/y`.
This calculation applies to any derivation into any module, including Kähler differentials. -/
theorem ellipticDifferential_transition {S M : Type*} [CommRing S] [Algebra ℂ S]
    [AddCommGroup M] [Module S M] [Module ℂ M] [IsScalarTower ℂ S M]
    (D : Derivation ℂ S M) (x y u v : S) (wz wy : M)
    (hx : x * v = u) (hyv : y * v = 1) (hf : v - u ^ 3 + u * v ^ 2 = 0)
    (hz : (2 * y) • wz = D x)
    (hu : (1 + 2 * u * v) • wy = -D u)
    (hv : (v ^ 2 - 3 * u ^ 2) • wy = D v) : wz = wy := by
  have hxy : x = u * y := by
    calc
      x = x * (y * v) := by rw [hyv, mul_one]
      _ = (x * v) * y := by ring
      _ = u * y := by rw [hx]
  have hcoef : y * (-(1 + 2 * u * v)) - x * y * (v ^ 2 - 3 * u ^ 2) = 2 * y := by
    rw [hxy]
    linear_combination -3 * y ^ 2 * hf + (2 * u * y * v + 3 * y) * hyv
  have hdu : D u = -(1 + 2 * u * v) • wy := by
    rw [neg_smul, hu, neg_neg]
  have hdxv := congrArg D hx
  rw [Derivation.leibniz] at hdxv
  have hdx : D x = y • D u - (x * y) • D v := by
    calc
      D x = (y * v) • D x := by rw [hyv, one_smul]
      _ = y • (v • D x + x • D v) - (x * y) • D v := by module
      _ = y • D u - (x * y) • D v := by rw [add_comm, hdxv]
  have he : (2 * y) • wz = (2 * y) • wy := by
    rw [hz, hdx, hdu, ← hv, smul_smul, smul_smul, ← sub_smul, hcoef]
  have htwo : (algebraMap ℂ S (1 / 2)) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℂ S) 2, ← map_mul]
    norm_num
  have hi : ((algebraMap ℂ S (1 / 2)) * v) * (2 * y) = 1 := by
    calc
      _ = ((algebraMap ℂ S (1 / 2)) * 2) * (y * v) := by ring
      _ = 1 := by rw [htwo, hyv, one_mul]
  have hc := congrArg (fun w => ((algebraMap ℂ S (1 / 2)) * v) • w) he
  simpa only [smul_smul, hi, one_smul] using hc

/-- Restriction of regular functions respects the specified complex scalar maps. -/
def curveSectionRestriction {U V : curve.Opens} (h : V ≤ U) : Γ(curve, U) →ₐ[ℂ] Γ(curve, V) where
  toRingHom := (curve.presheaf.map (homOfLE h).op).hom
  commutes' r := by
    change (((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ curveToBase.appTop ≫
      curve.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) ≫
      curve.presheaf.map (homOfLE h).op) r =
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ curveToBase.appTop ≫
        curve.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op) r
    simp only [Category.assoc, ← Functor.map_comp]
    rfl

/-- Restriction on Kähler differentials, using the actual structure-sheaf ring homomorphism. -/
def curveDifferentialRestriction {U V : curve.Opens} (h : V ≤ U) :
    KaehlerDifferential ℂ Γ(curve, U) →ₗ[ℂ] KaehlerDifferential ℂ Γ(curve, V) :=
  letI := (curveSectionRestriction h).toRingHom.toAlgebra
  letI : IsScalarTower ℂ Γ(curve, U) Γ(curve, V) :=
    IsScalarTower.of_algebraMap_eq' (curveSectionRestriction h).comp_algebraMap.symm
  (KaehlerDifferential.map ℂ ℂ Γ(curve, U) Γ(curve, V)).restrictScalars ℂ

@[simp] theorem curveDifferentialRestriction_D {U V : curve.Opens} (h : V ≤ U)
    (r : Γ(curve, U)) :
    curveDifferentialRestriction h (KaehlerDifferential.D ℂ Γ(curve, U) r) =
      KaehlerDifferential.D ℂ Γ(curve, V) (curveSectionRestriction h r) := by
  simp only [curveDifferentialRestriction, LinearMap.restrictScalars_apply,
    KaehlerDifferential.map_D]
  rfl

@[simp] theorem curveDifferentialRestriction_smul {U V : curve.Opens} (h : V ≤ U)
    (r : Γ(curve, U)) (w : KaehlerDifferential ℂ Γ(curve, U)) :
    curveDifferentialRestriction h (r • w) =
      curveSectionRestriction h r • curveDifferentialRestriction h w := by
  let := (curveSectionRestriction h).toRingHom.toAlgebra
  let : IsScalarTower ℂ Γ(curve, U) Γ(curve, V) :=
    IsScalarTower.of_algebraMap_eq' (curveSectionRestriction h).comp_algebraMap.symm
  exact (KaehlerDifferential.map ℂ ℂ Γ(curve, U) Γ(curve, V)).map_smul r w

/-- The quotient coordinates are pulled back along the actual affine chart embedding. -/
theorem hypersurfaceCoordinateMap_eq_chartToSpec (e : Equiv.Perm (Fin 3))
    (hp : (Ideal.span {chartEquation e}).IsPrime) (p : MvPolynomial (Fin 2) ℂ) :
    hypersurfaceCoordinateMap (chartEquation e) (curveChartGlobalAlgEquiv e hp) p =
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) ℂ))).inv ≫
        (curveChartToSpec e).appTop ≫
        (curveToPlane ⁻¹ᵁ ambientChart e).topIso.hom) p := by
  have he := (exists_curveChartIsoHypersurface e hp).choose_spec
  change curveChartToSpec e = (curveChartHypersurfaceIso e hp).hom ≫ _ at he
  rw [he, Scheme.Hom.comp_appTop, Category.assoc, ← Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

/-- The affine coordinates of the curve respect the original integral projective chart. -/
theorem curveChartToSpec_toIntegerChart (e : Equiv.Perm (Fin 3)) :
    curveChartToSpec e ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.map integerToComplex)) =
      curveToIntegerPlane ∣_ Proj.basicOpen (ProjectivePlaneChart.grading (ULift ℤ)) (X (e 2)) ≫
        (ProjectivePlaneChart.basicOpenIso (ULift ℤ) e).hom := by
  apply (cancel_mono (ProjectivePlaneChart.basicOpenIso (ULift ℤ) e).inv).mp
  apply (cancel_mono (Proj.basicOpen (ProjectivePlaneChart.grading (ULift ℤ)) (X (e 2))).ι).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc, morphismRestrict_ι]
  rw [← ProjectivePlaneChart.chartMap, ← ambientChartIsoSpec_inv_toIntegerPlane]
  simp [curveChartToSpec, curveToIntegerPlane]
  rfl

/-- Polynomial coordinates on a projective-plane chart are its regular coordinate ratios. -/
theorem projectivePlaneChart_coordinate (e : Equiv.Perm (Fin 3)) (j : Fin 2) :
    ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) (ULift ℤ)))).inv ≫
      (ProjectivePlaneChart.basicOpenIso (ULift ℤ) e).hom.appTop ≫
      (Proj.basicOpen (ProjectivePlaneChart.grading (ULift ℤ)) (X (e 2))).topIso.hom)
        (X j) = ProjectiveRatioSections.ratio (ULift ℤ) (e 2) (e j.castSucc) := by
  change ((Scheme.ΓSpecIso _).inv ≫
    (Spec.map (CommRingCat.ofHom (ProjectivePlaneChart.fromPolynomial (ULift ℤ) e))).appTop ≫
    (Proj.basicOpenToSpec (ProjectivePlaneChart.grading (ULift ℤ)) (X (e 2))).appTop ≫
    (Proj.basicOpen (ProjectivePlaneChart.grading (ULift ℤ)) (X (e 2))).topIso.hom) (X j) = _
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  change (CommRingCat.ofHom (ProjectivePlaneChart.fromPolynomial (ULift ℤ) e) ≫
    (Scheme.ΓSpecIso _).inv ≫
    (Proj.basicOpenToSpec (ProjectivePlaneChart.grading (ULift ℤ)) (X (e 2))).app ⊤ ≫
    (Proj.basicOpen (ProjectivePlaneChart.grading (ULift ℤ)) (X (e 2))).topIso.hom) (X j) = _
  rw [Proj.basicOpenToSpec_app_top]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  change Proj.awayToSection _ _ (ProjectivePlaneChart.fromPolynomial (ULift ℤ) e (X j)) = _
  rw [ProjectivePlaneChart.fromPolynomial_X]
  rfl

/-- The two quotient coordinates are the actual ratios pulled back from projective space. -/
theorem hypersurfaceCoordinateMap_X_eq_pullRatio (e : Equiv.Perm (Fin 3))
    (hp : (Ideal.span {chartEquation e}).IsPrime) (j : Fin 2) :
    hypersurfaceCoordinateMap (chartEquation e) (curveChartGlobalAlgEquiv e hp) (X j) =
      ProjectiveRatioSections.pullRatio (ULift ℤ) curveToIntegerPlane
        (curveToPlane ⁻¹ᵁ ambientChart e) (e 2) le_rfl (e j.castSucc) := by
  rw [hypersurfaceCoordinateMap_eq_chartToSpec]
  have h := congrArg Scheme.Hom.appTop (curveChartToSpec_toIntegerChart e)
  have hn := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (MvPolynomial.map integerToComplex :
      MvPolynomial (Fin 2) (ULift ℤ) →+* MvPolynomial (Fin 2) ℂ))
  have hc := congrArg (fun g =>
    ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 2) (ULift ℤ)))).inv ≫ g ≫
      (curveToPlane ⁻¹ᵁ ambientChart e).topIso.hom) (X j)) h
  simp only [Scheme.Hom.comp_appTop, ← Category.assoc, ← hn] at hc
  change ((Scheme.ΓSpecIso _).inv ≫ (curveChartToSpec e).appTop ≫
    (curveToPlane ⁻¹ᵁ ambientChart e).topIso.hom)
      (MvPolynomial.map integerToComplex (X j)) = _ at hc
  rw [MvPolynomial.map_X] at hc
  rw [hc]
  have hr :
      (curveToIntegerPlane ∣_ Proj.basicOpen
        (ProjectivePlaneChart.grading (ULift ℤ)) (X (e 2))).appTop ≫
        (curveToPlane ⁻¹ᵁ ambientChart e).topIso.hom =
      (Proj.basicOpen (ProjectivePlaneChart.grading (ULift ℤ)) (X (e 2))).topIso.hom ≫
        curveToIntegerPlane.appLE _ (curveToPlane ⁻¹ᵁ ambientChart e) le_rfl := by
    simp [Scheme.Hom.appTop, morphismRestrict_app', Scheme.Opens.topIso,
      Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  change ((Scheme.ΓSpecIso _).inv ≫
    (ProjectivePlaneChart.basicOpenIso (ULift ℤ) e).hom.appTop ≫
    (curveToIntegerPlane ∣_ _).appTop ≫
    (curveToPlane ⁻¹ᵁ ambientChart e).topIso.hom) (X j) = _
  rw [hr]
  exact congrArg (curveToIntegerPlane.appLE
    (Proj.basicOpen (ProjectivePlaneChart.grading (ULift ℤ)) (X (e 2)))
    (curveToPlane ⁻¹ᵁ ambientChart e) le_rfl) (projectivePlaneChart_coordinate e j)

/-- Coordinate restriction is literal restriction of the pulled-back projective ratios. -/
theorem curveSectionRestriction_coordinate (e : Equiv.Perm (Fin 3))
    (hp : (Ideal.span {chartEquation e}).IsPrime) {V : curve.Opens}
    (h : V ≤ curveToPlane ⁻¹ᵁ ambientChart e) (j : Fin 2) :
    curveSectionRestriction h
      (hypersurfaceCoordinateMap (chartEquation e) (curveChartGlobalAlgEquiv e hp) (X j)) =
      ProjectiveRatioSections.pullRatio (ULift ℤ) curveToIntegerPlane V
        (e 2) h (e j.castSucc) := by
  rw [hypersurfaceCoordinateMap_X_eq_pullRatio]
  exact ProjectiveRatioSections.restrict_pullRatio (ULift ℤ) curveToIntegerPlane h
    (e 2) le_rfl (e j.castSucc)

/-- The two regular Kähler forms agree after restriction to every common open. -/
theorem curveDifferential_overlap_on (V : curve.Opens)
    (hZ : V ≤ chart 2) (hY : V ≤ chart 1) :
    curveDifferentialRestriction hZ curveZDifferential =
      curveDifferentialRestriction hY curveYDifferential := by
  let rz := curveSectionRestriction
    (show V ≤ curveToPlane ⁻¹ᵁ ambientChart (Equiv.refl (Fin 3)) from hZ)
  let ry := curveSectionRestriction
    (show V ≤ curveToPlane ⁻¹ᵁ ambientChart (Equiv.swap (1 : Fin 3) 2) from hY)
  let z := rz.comp (hypersurfaceCoordinateMap _
    (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime))
  let y := ry.comp (hypersurfaceCoordinateMap _
    (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime))
  apply ellipticDifferential_transition (KaehlerDifferential.D ℂ Γ(curve, V))
    (z (X 0)) (z (X 1)) (y (X 0)) (y (X 1))
  · dsimp only [z, y, AlgHom.comp_apply, rz, ry]
    simp only [curveSectionRestriction_coordinate]
    exact (ProjectiveRatioSections.pullRatio_transition (ULift ℤ) curveToIntegerPlane V
      1 2 0 hY hZ).symm
  · dsimp only [z, y, AlgHom.comp_apply, rz, ry]
    simp only [curveSectionRestriction_coordinate]
    have ht := ProjectiveRatioSections.pullRatio_transition (ULift ℤ) curveToIntegerPlane V
      1 2 1 hY hZ
    simp only [ProjectiveRatioSections.pullRatio_self] at ht
    exact ht.symm
  · have he := congrArg ry (hypersurfaceCoordinateMap_equation
      (chartEquation (Equiv.swap (1 : Fin 3) 2))
      (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime))
    simp only [chartEquation_y, map_add, map_sub, map_pow, map_mul, map_zero] at he
    exact he
  · have hp : pderiv 1 (chartEquation (Equiv.refl (Fin 3))) = 2 * X 1 := by simp
    have hb := hypersurfaceDifferential_smul_y _ _ _ _
        (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime)
        zDifferential_bezout
    rw [hp, map_mul, map_ofNat] at hb
    have he := congrArg (curveDifferentialRestriction
      (show V ≤ curveToPlane ⁻¹ᵁ ambientChart (Equiv.refl (Fin 3)) from hZ)) hb
    simp only [curveDifferentialRestriction_smul, curveDifferentialRestriction_D,
      map_mul, map_ofNat] at he
    exact he
  · have hp : pderiv 1 (chartEquation (Equiv.swap (1 : Fin 3) 2)) =
        1 + 2 * X 0 * X 1 := by simp; ring
    have hb := hypersurfaceDifferential_smul_y _ _ _ _
        (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime)
        yDifferential_bezout
    rw [hp, map_add, map_one, map_mul, map_mul, map_ofNat] at hb
    have he := congrArg (curveDifferentialRestriction
      (show V ≤ curveToPlane ⁻¹ᵁ ambientChart (Equiv.swap (1 : Fin 3) 2) from hY)) hb
    simp only [curveDifferentialRestriction_smul, curveDifferentialRestriction_D,
      map_add, map_one, map_mul, map_ofNat] at he
    have hn := congrArg Neg.neg he
    rw [← smul_neg] at hn
    simp only [curveYDifferential, map_neg]
    exact hn
  · have hp : pderiv 0 (chartEquation (Equiv.swap (1 : Fin 3) 2)) =
        X 1 ^ 2 - 3 * X 0 ^ 2 := by simp; ring
    have hb := hypersurfaceDifferential_smul_x _ _ _ _
        (curveChartGlobalAlgEquiv (Equiv.swap (1 : Fin 3) 2) chartEquation_y_prime)
        yDifferential_bezout
    rw [hp, map_sub, map_pow, map_mul, map_pow, map_ofNat] at hb
    have he := congrArg (curveDifferentialRestriction
      (show V ≤ curveToPlane ⁻¹ᵁ ambientChart (Equiv.swap (1 : Fin 3) 2) from hY)) hb
    simp only [curveDifferentialRestriction_smul, curveDifferentialRestriction_D,
      map_sub, map_pow, map_mul, map_ofNat, map_neg] at he
    have hn := congrArg Neg.neg he
    rw [← smul_neg, neg_neg] at hn
    simp only [curveYDifferential, map_neg]
    exact hn

/-- The previously constructed local regular forms agree on their actual chart overlap. -/
theorem curveDifferential_overlap :
    curveDifferentialRestriction (show chart 2 ⊓ chart 1 ≤ chart 2 from inf_le_left)
        curveZDifferential =
      curveDifferentialRestriction (show chart 2 ⊓ chart 1 ≤ chart 1 from inf_le_right)
        curveYDifferential :=
  curveDifferential_overlap_on _ inf_le_left inf_le_right

end AlgebraicGeometry.ExplicitEllipticCandidate
