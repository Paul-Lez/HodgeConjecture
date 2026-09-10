import Other.AlgebraicGeometry.ExplicitEllipticCMGlobal

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.ExplicitEllipticCandidate

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

def curveCMEnd : curve ⟶ curve :=
  curveCMCover.glueMorphisms curveCMLocalMap curveCMLocalMap_compatible

@[reassoc] theorem curveZOpen_ι_curveCMEnd :
    curveZOpen.ι ≫ curveCMEnd = curveZCMChartIso.hom ≫ curveZOpen.ι := by
  have h := curveCMCover.ι_glueMorphisms
    curveCMLocalMap curveCMLocalMap_compatible (0 : Fin 2)
  change curveZOpen.ι ≫ curveCMEnd =
    curveZCMChartIso.hom ≫ curveZOpen.ι at h
  exact h

@[reassoc] theorem curveYOpen_ι_curveCMEnd :
    curveYOpen.ι ≫ curveCMEnd = curveYCMChartIso.hom ≫ curveYOpen.ι := by
  have h := curveCMCover.ι_glueMorphisms
    curveCMLocalMap curveCMLocalMap_compatible (1 : Fin 2)
  change curveYOpen.ι ≫ curveCMEnd =
    curveYCMChartIso.hom ≫ curveYOpen.ι at h
  exact h

theorem curveZCMChartIso_hom_four :
    curveZCMChartIso.hom ≫ curveZCMChartIso.hom ≫
        curveZCMChartIso.hom ≫ curveZCMChartIso.hom =
      𝟙 curveZOpen.toScheme := by
  letI : IsAffine curveZOpen.toScheme := curveZOpen_isAffine
  apply ext_of_isAffine
  simp only [Scheme.Hom.comp_appTop]
  rw [curveZCMChartIso_appTop]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  have h : CommRingCat.ofHom
        (curveZCMEnd.comp (curveZCMEnd.comp (curveZCMEnd.comp curveZCMEnd))).toRingHom =
      𝟙 (CommRingCat.of Γ(curve, curveZOpen)) := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom curveZCMEnd_four
  rw [h]
  simp

theorem curveYCMChartIso_hom_four :
    curveYCMChartIso.hom ≫ curveYCMChartIso.hom ≫
        curveYCMChartIso.hom ≫ curveYCMChartIso.hom =
      𝟙 curveYOpen.toScheme := by
  letI : IsAffine curveYOpen.toScheme := curveYOpen_isAffine
  apply ext_of_isAffine
  simp only [Scheme.Hom.comp_appTop]
  rw [curveYCMChartIso_appTop]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  have h : CommRingCat.ofHom
        (curveYCMEnd.comp (curveYCMEnd.comp (curveYCMEnd.comp curveYCMEnd))).toRingHom =
      𝟙 (CommRingCat.of Γ(curve, curveYOpen)) := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom curveYCMEnd_four
  rw [h]
  simp

theorem curveCMEnd_four :
    curveCMEnd ≫ curveCMEnd ≫ curveCMEnd ≫ curveCMEnd = 𝟙 curve := by
  apply curveCMCover.hom_ext
  intro i
  fin_cases i
  · simp only [Category.assoc, curveZOpen_ι_curveCMEnd_assoc]
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
      curveZCMChartIso_hom_four, Category.id_comp, Category.comp_id]
  · simp only [Category.assoc, curveYOpen_ι_curveCMEnd_assoc]
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
      curveYCMChartIso_hom_four, Category.id_comp, Category.comp_id]

end

end AlgebraicGeometry.ExplicitEllipticCandidate
