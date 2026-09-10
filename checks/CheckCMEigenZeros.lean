import Other.AlgebraicGeometry.ExplicitEllipticCMOverlapFunctions
import Other.AlgebraicGeometry.ExplicitEllipticCurveConnectivity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace MvPolynomial

open AlgebraicGeometry

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint Point

#check Point.isoMapHomeomorph
#check Point.isoMapHomeomorph_apply
#check ComplexPoint.affineSpecHomeomorph
#check ComplexPoint.affineSpecEquiv
#check ComplexPoint.affineSpecEquiv_apply
#check Point.evaluate_map
#check Scheme.Opens.topIso
#check curveChartHypersurfaceIso
#check curveChartHypersurfaceIso_over
#check curveZCMChartIso_appTop
#check curveZOpenVarietyCMEnd
#check curveZOpenInclusion_curveVarietyCMEnd
#check hypersurfaceCoordinateMap_surjective
#check curveZCMEnd_coordinate
#check curveZCMEnd_coordinate_zero
#check curveZCMEnd_coordinate_one
#check ComplexPoint.openEquiv
#check ComplexPoint.map_asOpenPoint
#check ComplexPoint.evaluate_top_eq_appTop
#check Scheme.toSpecΓ_appTop
#check Scheme.Hom.comp_appTop
#check Scheme.Γ.map
#check MvPolynomial.ringHom_ext
#check MvPolynomial.ringHom_ext'
#check AlgHom.toRingHom
#check CommRingCat.comp_apply

lemma test_affine_point_ext
    (X : Over (Spec (CommRingCat.of ℂ))) [IsAffine X.left]
    (z w : ComplexPoint X)
    (h : ∀ r : Γ(X.left, ⊤), Point.evaluate ⊤ r z = Point.evaluate ⊤ r w) :
    z = w := by
  have happ : (Over.Hom.left z).appTop = (Over.Hom.left w).appTop := by
    simp only [ComplexPoint.evaluate_top_eq_appTop] at h
    apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).mp
    ext r
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
    exact h r
  apply Over.OverMorphism.ext
  apply (cancel_mono X.left.toSpecΓ).mp
  apply ext_to_Spec
  ext r
  simp only [Scheme.Γ_map_op, Scheme.Hom.comp_appTop]
  rw [Scheme.toSpecΓ_appTop]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact ConcreteCategory.congr_hom happ r

noncomputable abbrev testCurveZCoordinateMap : ZPoly →ₐ[ℂ] Γ(curve, curveZOpen) :=
  hypersurfaceCoordinateMap
    (chartEquation (Equiv.refl (Fin 3)))
    (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime)

lemma test_curveZCMEnd_sq_evaluate_of_y_eq_zero
    (z : ComplexPoint curveVariety) (hz : z ∈ Point.overOpen curveZOpen)
    (hy : Point.evaluate curveZOpen curveZOverlapCoordinate z = 0)
    (s : Γ(curve, curveZOpen)) :
    Point.evaluate curveZOpen (curveZCMEnd (curveZCMEnd s)) z =
      Point.evaluate curveZOpen s z := by
  let ev := Point.evaluationHom (X := curveVariety) curveZOpen ⟨z, hz⟩
  have hy' : ev (testCurveZCoordinateMap (X 1)) = 0 := by
    rw [Point.evaluationHom_apply]
    simpa only [curveZOverlapCoordinate_eq_coordinate] using hy
  let evPoly : ZPoly →+* ℂ :=
    { toFun := fun p ↦ ev (testCurveZCoordinateMap p)
      map_one' := by simp
      map_mul' := by intro p q; simp
      map_zero' := by simp
      map_add' := by intro p q; simp }
  have hyPoly : evPoly (X 1) = 0 := by
    change ev (testCurveZCoordinateMap (X 1)) = 0
    exact hy'
  have hRing :
      evPoly.comp ((zCMPolynomialEnd.comp zCMPolynomialEnd).toRingHom) =
        evPoly := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [evPoly]
    · intro j
      fin_cases j
      · simp [evPoly, zCMPolynomialEnd_X_zero]
      · change evPoly (zCMPolynomialEnd (zCMPolynomialEnd (X 1))) =
          evPoly (X 1)
        rw [zCMPolynomialEnd_X_one, zCMPolynomialEnd_C_mul_X_one]
        simp [Complex.I_mul_I, hyPoly]
  obtain ⟨p, rfl⟩ := hypersurfaceCoordinateMap_surjective
    (chartEquation (Equiv.refl (Fin 3)))
    (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime) s
  rw [← Point.evaluationHom_apply (X := curveVariety) curveZOpen ⟨z, hz⟩,
    ← Point.evaluationHom_apply (X := curveVariety) curveZOpen ⟨z, hz⟩]
  rw [curveZCMEnd_coordinate, curveZCMEnd_coordinate]
  exact RingHom.congr_fun hRing p

lemma test_curveZOpenVarietyCMEnd_inclusion_apply
    (z : ComplexPoint (openScheme curveVariety curveZOpen)) :
    Point.map (openInclusion curveVariety curveZOpen)
        (Point.map curveZOpenVarietyCMEnd z) =
      Point.map curveVarietyCMEnd
        (Point.map (openInclusion curveVariety curveZOpen) z) := by
  rw [← Point.map_comp_apply, ← Point.map_comp_apply,
    curveZOpenInclusion_curveVarietyCMEnd]

lemma test_evaluate_curveZCMEnd
    (s : Γ(curve, curveZOpen))
    (z : ComplexPoint curveVariety) (hz : z ∈ Point.overOpen curveZOpen) :
    Point.evaluate curveZOpen (curveZCMEnd s) z =
      Point.evaluate curveZOpen s (Point.map curveVarietyCMEnd z) := by
  let w := asOpenPoint curveVariety curveZOpen z hz
  have hw : Point.map (openInclusion curveVariety curveZOpen) w = z := by
    exact Over.OverMorphism.ext
      (liftToOpen_fac curveVariety curveZOpen z hz)
  rw [← hw]
  rw [← test_curveZOpenVarietyCMEnd_inclusion_apply]
  let t : Γ(curveZOpen.toScheme, ⊤) := curveZOpen.topIso.inv s
  let t' : Γ(curveZOpen.toScheme, ⊤) :=
    curveZCMChartIso.hom.appTop t
  have hleft := evaluate_openEquiv curveVariety curveZOpen t' w
  have hright := evaluate_openEquiv curveVariety curveZOpen t
    (Point.map curveZOpenVarietyCMEnd w)
  have hmap := Point.evaluate_map curveZOpenVarietyCMEnd ⊤ t w
  have hchain := hleft.trans (hmap.symm.trans hright.symm)
  simp_rw [evaluate_eq (Y := curveVariety) curveZOpen.ι_image_top] at hchain
  have htransport :
      (curveZOpen.ι.appIso ⊤).inv ≫
          curveVariety.left.presheaf.map
            (eqToHom curveZOpen.ι_image_top.symm).op =
        curveZOpen.topIso.hom := by
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv,
      Scheme.Opens.topIso]
    change curveVariety.left.presheaf.map
        (eqToHom curveZOpen.ι_image_top.symm).op =
      curveVariety.left.presheaf.map
        (eqToHom curveZOpen.ι_image_top.symm).op
    rfl
  change Point.evaluate curveZOpen
      (((curveZOpen.ι.appIso ⊤).inv ≫
        curveVariety.left.presheaf.map
          (eqToHom curveZOpen.ι_image_top.symm).op) t')
        (Point.map (openInclusion curveVariety curveZOpen) w) =
    Point.evaluate curveZOpen
      (((curveZOpen.ι.appIso ⊤).inv ≫
        curveVariety.left.presheaf.map
          (eqToHom curveZOpen.ι_image_top.symm).op) t)
        (Point.map (openInclusion curveVariety curveZOpen)
          (Point.map curveZOpenVarietyCMEnd w)) at hchain
  rw [htransport] at hchain
  dsimp only [t] at hchain
  have hcancel : curveZOpen.topIso.hom
      (curveZOpen.topIso.inv s) = s :=
    curveZOpen.topIso.inv_hom_id_apply s
  have hcancelEval := congrArg
    (fun q : Γ(curve, curveZOpen) ↦
      Point.evaluate curveZOpen q
        (Point.map (openInclusion curveVariety curveZOpen)
          (Point.map curveZOpenVarietyCMEnd w))) hcancel
  have hout := hchain.trans hcancelEval
  change Point.evaluate curveZOpen
      (curveZOpen.topIso.hom
        (curveZCMChartIso.hom.appTop (curveZOpen.topIso.inv s)))
        (Point.map (openInclusion curveVariety curveZOpen) w) =
    Point.evaluate curveZOpen s
      (Point.map (openInclusion curveVariety curveZOpen)
        (Point.map curveZOpenVarietyCMEnd w)) at hout
  rw [curveZCMChartIso_appTop] at hout
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply,
    Iso.hom_inv_id_apply] at hout
  convert hout using 1
  apply congrArg
    (fun q : Γ(curve, curveZOpen) ↦
      Point.evaluate curveZOpen q
        (Point.map (openInclusion curveVariety curveZOpen) w))
  change curveZCMAlgEquiv.toAlgHom s =
    curveZCMAlgEquiv.toRingEquiv.toRingHom s
  rfl

lemma test_evaluate_openEquiv_top
    (X : Over (Spec (CommRingCat.of ℂ))) (U : X.left.Opens)
    (t : Γ(U.toScheme, ⊤)) (z : ComplexPoint (openScheme X U)) :
    Point.evaluate U (U.topIso.hom t)
        (Point.map (openInclusion X U) z) =
      Point.evaluate ⊤ t z := by
  have h := evaluate_openEquiv X U t z
  simp_rw [evaluate_eq (Y := X) U.ι_image_top] at h
  have htransport :
      (U.ι.appIso ⊤).inv ≫
          X.left.presheaf.map (eqToHom U.ι_image_top.symm).op =
        U.topIso.hom := by
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv,
      Scheme.Opens.topIso]
    change X.left.presheaf.map (eqToHom U.ι_image_top.symm).op =
      X.left.presheaf.map (eqToHom U.ι_image_top.symm).op
    rfl
  change Point.evaluate U
      (((U.ι.appIso ⊤).inv ≫
        X.left.presheaf.map (eqToHom U.ι_image_top.symm).op) t)
      (Point.map (openInclusion X U) z) = Point.evaluate ⊤ t z at h
  rw [htransport] at h
  exact h

lemma test_complexPoint_eq_of_mem_affineOpen_of_evaluate_eq
    (X : Over (Spec (CommRingCat.of ℂ))) (U : X.left.Opens)
    (hU : IsAffineOpen U) (z w : ComplexPoint X)
    (hz : z ∈ Point.overOpen U) (hw : w ∈ Point.overOpen U)
    (h : ∀ s : Γ(X.left, U),
      Point.evaluate U s z = Point.evaluate U s w) : z = w := by
  let zU := asOpenPoint X U z hz
  let wU := asOpenPoint X U w hw
  have hzU : Point.map (openInclusion X U) zU = z :=
    ComplexPoint.map_asOpenPoint U z hz
  have hwU : Point.map (openInclusion X U) wU = w :=
    ComplexPoint.map_asOpenPoint U w hw
  letI : IsAffine (openScheme X U).left := by
    change IsAffine U.toScheme
    exact hU
  have hzwU : zU = wU := by
    apply test_affine_point_ext (openScheme X U) zU wU
    intro t
    rw [← test_evaluate_openEquiv_top X U t zU,
      ← test_evaluate_openEquiv_top X U t wU, hzU, hwU]
    exact h (U.topIso.hom t)
  calc
    z = Point.map (openInclusion X U) zU := hzU.symm
    _ = Point.map (openInclusion X U) wU := by rw [hzwU]
    _ = w := hwU

lemma test_curveVarietyCMEnd_sq_of_overlapCoordinate_eq_zero
    (z : ComplexPoint curveVariety) (hz : z ∈ Point.overOpen curveZOpen)
    (hy : Point.evaluate curveZOpen curveZOverlapCoordinate z = 0) :
    Point.map curveVarietyCMEnd (Point.map curveVarietyCMEnd z) = z := by
  let z₁ := Point.map curveVarietyCMEnd z
  have hz₁ : z₁ ∈ Point.overOpen curveZOpen :=
    curveVarietyCMEnd_mem_curveZOpen z hz
  have hz₂ : Point.map curveVarietyCMEnd z₁ ∈ Point.overOpen curveZOpen :=
    curveVarietyCMEnd_mem_curveZOpen z₁ hz₁
  apply test_complexPoint_eq_of_mem_affineOpen_of_evaluate_eq
    curveVariety curveZOpen curveZOpen_isAffine
    (Point.map curveVarietyCMEnd z₁) z hz₂ hz
  intro s
  calc
    Point.evaluate curveZOpen s (Point.map curveVarietyCMEnd z₁) =
        Point.evaluate curveZOpen (curveZCMEnd s) z₁ :=
      (test_evaluate_curveZCMEnd s z₁ hz₁).symm
    _ = Point.evaluate curveZOpen (curveZCMEnd (curveZCMEnd s)) z :=
      (test_evaluate_curveZCMEnd (curveZCMEnd s) z hz).symm
    _ = Point.evaluate curveZOpen s z :=
      test_curveZCMEnd_sq_evaluate_of_y_eq_zero z hz hy s

lemma test_curveZAnalyticCMMap_sq_of_overlapCoordinate_eq_zero
    (z : regularAnalyticOpen curveVariety curveZOpen)
    (hy : Point.evaluate curveZOpen curveZOverlapCoordinate z.1 = 0) :
    curveZAnalyticCMMap (curveZAnalyticCMMap z) = z := by
  apply Subtype.ext
  exact test_curveVarietyCMEnd_sq_of_overlapCoordinate_eq_zero z.1 z.2 hy

lemma test_curveZHolomorphicCMMinusEigen_zero_of_overlapCoordinate_eq_zero
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen)))
    (hf : curveZHolomorphicCMEnd f = -Complex.I • f)
    (z : regularAnalyticOpen curveVariety curveZOpen)
    (hy : Point.evaluate curveZOpen curveZOverlapCoordinate z.1 = 0) :
    f.1 z = 0 := by
  have h₁ := congrArg (fun g : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen)) ↦ g.1 z) hf
  have h₂ := congrArg (fun g : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen)) ↦
        g.1 (curveZAnalyticCMMap z)) hf
  change f.1 (curveZAnalyticCMMap z) = -Complex.I * f.1 z at h₁
  change f.1 (curveZAnalyticCMMap (curveZAnalyticCMMap z)) =
    -Complex.I * f.1 (curveZAnalyticCMMap z) at h₂
  rw [test_curveZAnalyticCMMap_sq_of_overlapCoordinate_eq_zero z hy, h₁] at h₂
  have hneg : f.1 z = -f.1 z := by
    calc
      f.1 z = -Complex.I * (-Complex.I * f.1 z) := h₂
      _ = -f.1 z := by rw [← mul_assoc]; simp [Complex.I_sq]
  have htwo : (2 : ℂ) * f.1 z = 0 := by
    linear_combination hneg
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

end AlgebraicGeometry.ExplicitEllipticCandidate
