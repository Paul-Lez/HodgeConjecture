import Other.AlgebraicGeometry.ExplicitEllipticCMGlobal

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.ExplicitEllipticCandidate

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem testZRingFour :
    CommRingCat.ofHom curveZCMAlgEquiv.toRingEquiv.toRingHom ≫
        CommRingCat.ofHom curveZCMAlgEquiv.toRingEquiv.toRingHom ≫
        CommRingCat.ofHom curveZCMAlgEquiv.toRingEquiv.toRingHom ≫
        CommRingCat.ofHom curveZCMAlgEquiv.toRingEquiv.toRingHom =
      𝟙 (CommRingCat.of Γ(curve, curveZOpen)) := by
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom curveZCMEnd_four

theorem testYRingFour :
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
      rw [testZRingFour]
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
      rw [testYRingFour]
      simp only [Category.comp_id, Category.id_comp, Scheme.Hom.id_appTop]
      exact curveYOpen.topIso.hom_inv_id

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

end

end AlgebraicGeometry.ExplicitEllipticCandidate
