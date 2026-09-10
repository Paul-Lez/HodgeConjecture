import Other.AlgebraicGeometry.ExplicitEllipticCMGlobal
import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothComplexCoordinates

noncomputable section

open CategoryTheory AlgebraicGeometry

#check AlgebraicGeometry.ext_of_isAffine
#check Scheme.Hom.appTop
#check Scheme.Hom.comp_appTop
#check Scheme.Hom.ext
#check AlgebraicGeometry.ExplicitEllipticCandidate.curveChartToSpec_toBase
#check AlgebraicGeometry.ExplicitEllipticCandidate.curveZCMChartIso_appTop
#check AlgebraicGeometry.ExplicitEllipticCandidate.curveZCMAlgEquiv
#check AlgebraicGeometry.ExplicitEllipticCandidate.curveZOpen
#check AlgebraicGeometry.ExplicitEllipticCandidate.curveZOpen_isAffine
#check (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
#check (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv

namespace AlgebraicGeometry.ExplicitEllipticCandidate

theorem test_curveZCMChartIso_toBase :
    curveZCMChartIso.hom ≫ curveZOpen.ι ≫ curveToBase =
      curveZOpen.ι ≫ curveToBase := by
  letI : IsAffine curveZOpen.toScheme := curveZOpen_isAffine
  letI : IsAffine base := by
    dsimp [base]
    infer_instance
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  rw [curveZCMChartIso_appTop]
  have ht : curveZOpen.ι.appTop ≫ curveZOpen.topIso.hom =
      curve.presheaf.map (homOfLE (show curveZOpen ≤ ⊤ from le_top)).op :=
    Scheme.Opens.ι_appTop_topIso_hom curveZOpen
  apply CommRingCat.hom_ext
  ext s
  let c : ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom s
  have hs : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c = s := by
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom_inv_id_apply s
  rw [← hs]
  change curveZOpen.topIso.inv
      (curveZCMAlgEquiv
        (curveZOpen.topIso.hom
          (curveZOpen.ι.appTop
            (curveToBase.appTop
              ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))))) =
    curveZOpen.ι.appTop
      (curveToBase.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))
  have hcscalar : curveZOpen.topIso.hom
        (curveZOpen.ι.appTop
          (curveToBase.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))) =
      curveScalar curveZOpen c := by
    change (curveZOpen.ι.appTop ≫ curveZOpen.topIso.hom)
        (curveToBase.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) = _
    rw [ht]
    rfl
  rw [hcscalar]
  have he : curveZCMAlgEquiv (curveScalar curveZOpen c) =
      curveScalar curveZOpen c := by
    change curveZCMAlgEquiv (algebraMap ℂ Γ(curve, curveZOpen) c) =
      algebraMap ℂ Γ(curve, curveZOpen) c
    exact curveZCMAlgEquiv.commutes c
  rw [he]
  rw [← hcscalar]
  exact curveZOpen.topIso.hom_inv_id_apply _

theorem test_curveYCMChartIso_toBase :
    curveYCMChartIso.hom ≫ curveYOpen.ι ≫ curveToBase =
      curveYOpen.ι ≫ curveToBase := by
  letI : IsAffine curveYOpen.toScheme := curveYOpen_isAffine
  letI : IsAffine base := by
    dsimp [base]
    infer_instance
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  rw [curveYCMChartIso_appTop]
  have ht : curveYOpen.ι.appTop ≫ curveYOpen.topIso.hom =
      curve.presheaf.map (homOfLE (show curveYOpen ≤ ⊤ from le_top)).op :=
    Scheme.Opens.ι_appTop_topIso_hom curveYOpen
  apply CommRingCat.hom_ext
  ext s
  let c : ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom s
  have hs : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c = s := by
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom_inv_id_apply s
  rw [← hs]
  change curveYOpen.topIso.inv
      (curveYCMAlgEquiv
        (curveYOpen.topIso.hom
          (curveYOpen.ι.appTop
            (curveToBase.appTop
              ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))))) =
    curveYOpen.ι.appTop
      (curveToBase.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))
  have hcscalar : curveYOpen.topIso.hom
        (curveYOpen.ι.appTop
          (curveToBase.appTop
            ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))) =
      curveScalar curveYOpen c := by
    change (curveYOpen.ι.appTop ≫ curveYOpen.topIso.hom)
        (curveToBase.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) = _
    rw [ht]
    rfl
  rw [hcscalar]
  have he : curveYCMAlgEquiv (curveScalar curveYOpen c) =
      curveScalar curveYOpen c := by
    change curveYCMAlgEquiv (algebraMap ℂ Γ(curve, curveYOpen) c) =
      algebraMap ℂ Γ(curve, curveYOpen) c
    exact curveYCMAlgEquiv.commutes c
  rw [he]
  rw [← hcscalar]
  exact curveYOpen.topIso.hom_inv_id_apply _

#check Scheme.Cover.hom_ext

theorem test_curveCMEnd_toBase : curveCMEnd ≫ curveToBase = curveToBase := by
  apply curveCMCover.hom_ext
  change ∀ i : Fin 2, _
  intro i
  fin_cases i
  · change curveZOpen.ι ≫ curveCMEnd ≫ curveToBase =
      curveZOpen.ι ≫ curveToBase
    simpa only [Category.assoc, curveZOpen_ι_curveCMEnd_assoc] using
      test_curveZCMChartIso_toBase
  · change curveYOpen.ι ≫ curveCMEnd ≫ curveToBase =
      curveYOpen.ι ≫ curveToBase
    simpa only [Category.assoc, curveYOpen_ι_curveCMEnd_assoc] using
      test_curveYCMChartIso_toBase

end AlgebraicGeometry.ExplicitEllipticCandidate
