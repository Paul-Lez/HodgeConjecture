/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitEllipticCMOverlapFunctions

/-!
# Zeros of CM eigenfunctions on the explicit elliptic curve

The square of complex multiplication fixes each zero of the affine overlap
coordinate `y`. Consequently a holomorphic function with CM eigenvalue `-i`
vanishes at every such point. This is the fixed-point input used by the
two-chart Cech obstruction argument.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open CategoryTheory TopologicalSpace MvPolynomial

open AlgebraicGeometry

namespace AlgebraicGeometry.ExplicitEllipticCandidate

open ComplexPoint Point

/-- Complex points of an affine complex scheme are determined by evaluation
of all global regular functions. -/
lemma complexPoint_ext_of_affine_evaluate_eq
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
  simp only [Iso.inv_hom_id_assoc]
  exact ConcreteCategory.congr_hom happ r

/-- The polynomial presentation map for the affine `Z` chart. -/
noncomputable abbrev curveZPolynomialCoordinateMap : ZPoly →ₐ[ℂ] Γ(curve, curveZOpen) :=
  hypersurfaceCoordinateMap
    (chartEquation (Equiv.refl (Fin 3)))
    (curveChartGlobalAlgEquiv (Equiv.refl (Fin 3)) chartEquation_z_prime)

/-- At a zero of `y`, evaluating a regular function after two CM pullbacks
gives its original value. -/
lemma curveZCMEnd_sq_evaluate_of_overlapCoordinate_eq_zero
    (z : ComplexPoint curveVariety) (hz : z ∈ Point.overOpen curveZOpen)
    (hy : Point.evaluate curveZOpen curveZOverlapCoordinate z = 0)
    (s : Γ(curve, curveZOpen)) :
    Point.evaluate curveZOpen (curveZCMEnd (curveZCMEnd s)) z =
      Point.evaluate curveZOpen s z := by
  let ev := Point.evaluationHom (X := curveVariety) curveZOpen ⟨z, hz⟩
  have hy' : ev (curveZPolynomialCoordinateMap (X 1)) = 0 := by
    rw [Point.evaluationHom_apply]
    simpa only [curveZOverlapCoordinate_eq_coordinate] using hy
  let evPoly : ZPoly →+* ℂ :=
    { toFun := fun p ↦ ev (curveZPolynomialCoordinateMap p)
      map_one' := by simp
      map_mul' := by intro p q; simp
      map_zero' := by simp
      map_add' := by intro p q; simp }
  have hyPoly : evPoly (X 1) = 0 := by
    change ev (curveZPolynomialCoordinateMap (X 1)) = 0
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

/-- The local `Z`-chart CM map agrees with the global CM map after inclusion. -/
lemma curveZOpenVarietyCMEnd_inclusion_apply
    (z : ComplexPoint (openScheme curveVariety curveZOpen)) :
    Point.map (openInclusion curveVariety curveZOpen)
        (Point.map curveZOpenVarietyCMEnd z) =
      Point.map curveVarietyCMEnd
        (Point.map (openInclusion curveVariety curveZOpen) z) := by
  rw [← Point.map_comp_apply, ← Point.map_comp_apply,
    curveZOpenInclusion_curveVarietyCMEnd]

/-- Algebraic CM pullback on the `Z` chart evaluates by precomposition with
the analytic CM point map. -/
lemma evaluate_curveZCMEnd
    (s : Γ(curve, curveZOpen))
    (z : ComplexPoint curveVariety) (hz : z ∈ Point.overOpen curveZOpen) :
    Point.evaluate curveZOpen (curveZCMEnd s) z =
      Point.evaluate curveZOpen s (Point.map curveVarietyCMEnd z) := by
  let w := asOpenPoint curveVariety curveZOpen z hz
  have hw : Point.map (openInclusion curveVariety curveZOpen) w = z := by
    exact Over.OverMorphism.ext
      (liftToOpen_fac curveVariety curveZOpen z hz)
  rw [← hw]
  rw [← curveZOpenVarietyCMEnd_inclusion_apply]
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
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] at hout
  convert hout using 1
  apply congrArg
    (fun q : Γ(curve, curveZOpen) ↦
      Point.evaluate curveZOpen q
        (Point.map (openInclusion curveVariety curveZOpen) w))
  change curveZCMAlgEquiv.toAlgHom s =
    curveZCMAlgEquiv.toRingEquiv.toRingHom s
  rfl

/-- Evaluation of a top-open section of an open subscheme agrees with
evaluation of its ambient-open transport. -/
lemma evaluate_openEquiv_top_section
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

/-- Two points in an affine open are equal when every regular function on the
open has equal values at them. -/
lemma complexPoint_eq_of_mem_affineOpen_of_evaluate_eq
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
    apply complexPoint_ext_of_affine_evaluate_eq (openScheme X U) zU wU
    intro t
    rw [← evaluate_openEquiv_top_section X U t zU,
      ← evaluate_openEquiv_top_section X U t wU, hzU, hwU]
    exact h (U.topIso.hom t)
  calc
    z = Point.map (openInclusion X U) zU := hzU.symm
    _ = Point.map (openInclusion X U) wU := by rw [hzwU]
    _ = w := hwU

/-- The square of complex multiplication fixes every point in the `Z` chart
where the overlap coordinate `y` vanishes. -/
lemma curveVarietyCMEnd_sq_of_overlapCoordinate_eq_zero
    (z : ComplexPoint curveVariety) (hz : z ∈ Point.overOpen curveZOpen)
    (hy : Point.evaluate curveZOpen curveZOverlapCoordinate z = 0) :
    Point.map curveVarietyCMEnd (Point.map curveVarietyCMEnd z) = z := by
  let z₁ := Point.map curveVarietyCMEnd z
  have hz₁ : z₁ ∈ Point.overOpen curveZOpen :=
    curveVarietyCMEnd_mem_curveZOpen z hz
  have hz₂ : Point.map curveVarietyCMEnd z₁ ∈ Point.overOpen curveZOpen :=
    curveVarietyCMEnd_mem_curveZOpen z₁ hz₁
  apply complexPoint_eq_of_mem_affineOpen_of_evaluate_eq
    curveVariety curveZOpen curveZOpen_isAffine
    (Point.map curveVarietyCMEnd z₁) z hz₂ hz
  intro s
  calc
    Point.evaluate curveZOpen s (Point.map curveVarietyCMEnd z₁) =
        Point.evaluate curveZOpen (curveZCMEnd s) z₁ :=
      (evaluate_curveZCMEnd s z₁ hz₁).symm
    _ = Point.evaluate curveZOpen (curveZCMEnd (curveZCMEnd s)) z :=
      (evaluate_curveZCMEnd (curveZCMEnd s) z hz).symm
    _ = Point.evaluate curveZOpen s z :=
      curveZCMEnd_sq_evaluate_of_overlapCoordinate_eq_zero z hz hy s

/-- The restricted analytic CM map squares to the identity at a zero of `y`. -/
lemma curveZAnalyticCMMap_sq_of_overlapCoordinate_eq_zero
    (z : regularAnalyticOpen curveVariety curveZOpen)
    (hy : Point.evaluate curveZOpen curveZOverlapCoordinate z.1 = 0) :
    curveZAnalyticCMMap (curveZAnalyticCMMap z) = z := by
  apply Subtype.ext
  exact curveVarietyCMEnd_sq_of_overlapCoordinate_eq_zero z.1 z.2 hy

/-- A `-i` CM eigenfunction on the `Z` chart vanishes at every zero of `y`. -/
lemma curveZHolomorphicCMMinusEigen_zero_of_overlapCoordinate_eq_zero
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
  rw [curveZAnalyticCMMap_sq_of_overlapCoordinate_eq_zero z hy, h₁] at h₂
  have hneg : f.1 z = -f.1 z := by
    calc
      f.1 z = -Complex.I * (-Complex.I * f.1 z) := h₂
      _ = -f.1 z := by rw [← mul_assoc]; simp
  have htwo : (2 : ℂ) * f.1 z = 0 := by
    linear_combination hneg
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Ambient-point form of
`curveZHolomorphicCMMinusEigen_zero_of_overlapCoordinate_eq_zero`. -/
lemma curveZHolomorphicCMMinusEigen_evaluate_zero_of_overlapCoordinate_eq_zero
    (f : OpenHolomorphicFunctions curveVariety 1
      (.op (regularAnalyticOpen curveVariety curveZOpen)))
    (hf : curveZHolomorphicCMEnd f = -Complex.I • f)
    (z : ComplexPoint curveVariety) (hz : z ∈ Point.overOpen curveZOpen)
    (hy : Point.evaluate curveZOpen curveZOverlapCoordinate z = 0) :
    f.1 (⟨z, by
      change z ∈ Point.overOpen curveZOpen
      exact hz⟩ : regularAnalyticOpen curveVariety curveZOpen) = 0 := by
  let z' : regularAnalyticOpen curveVariety curveZOpen :=
    ⟨z, by
      change z ∈ Point.overOpen curveZOpen
      exact hz⟩
  exact curveZHolomorphicCMMinusEigen_zero_of_overlapCoordinate_eq_zero
    f hf z' hy

end AlgebraicGeometry.ExplicitEllipticCandidate
