/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectivePlaneHyperplane
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Comparing the direct and relative models of the complex projective plane

This file constructs the canonical morphism from the direct
`Proj ℂ[X₀,X₁,X₂]` model to the pullback-model projective plane used by
`ProjectiveSpace`.  Proving that this morphism is an isomorphism will give the direct model its
explicit projective presentation.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MvPolynomial AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectivePlane

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] ULift.algebra'
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The universal integral grading used in the pullback-model projective plane. -/
abbrev IntegralGrading : ℕ →
    Submodule (ULift ℤ) (MvPolynomial (Fin 3) (ULift ℤ)) :=
  homogeneousSubmodule (Fin 3) (ULift ℤ)

/-- Extension of coefficients from the universal integral polynomial ring to `ℂ`. -/
def integralToComplex :
    MvPolynomial (Fin 3) (ULift ℤ) →+* MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.map ((algebraMap ℤ ℂ).comp ULift.ringEquiv.toRingHom)

/-- The coefficient map underlying extension of scalars. -/
def integralCoefficientMap : ULift ℤ →+* ℂ :=
  (algebraMap ℤ ℂ).comp ULift.ringEquiv.toRingHom

/-- Extension of coefficients preserves the standard grading. -/
def integralToComplexGraded : IntegralGrading →+*ᵍ Grading where
  __ := integralToComplex
  map_mem hp := hp.map _

@[simp]
lemma integralToComplex_X (i : Fin 3) :
    integralToComplex (MvPolynomial.X i) = MvPolynomial.X i := by
  simp [integralToComplex]

@[simp]
lemma integralToComplexGraded_X (i : Fin 3) :
    integralToComplexGraded
        (MvPolynomial.X i : MvPolynomial (Fin 3) (ULift ℤ)) =
      (MvPolynomial.X i : MvPolynomial (Fin 3) ℂ) :=
  integralToComplex_X i

/-- The coefficient-extension map satisfies the irrelevant-ideal hypothesis required by
`Proj.map`.  Surjectivity on coefficients is not needed: the image ideal contains every
degree-one variable, hence the entire irrelevant ideal. -/
lemma irrelevant_le_map_integralToComplex :
    (HomogeneousIdeal.irrelevant Grading) ≤
      (HomogeneousIdeal.irrelevant IntegralGrading).map integralToComplexGraded := by
  rw [← toIdeal_le_toIdeal_iff,
    HomogeneousIdeal.toIdeal_map]
  refine (Other.ProjectiveChart.irrelevant_le_span_X ℂ 2).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [← integralToComplex_X i]
  exact Ideal.mem_map_of_mem integralToComplex
    (HomogeneousIdeal.mem_irrelevant_of_mem IntegralGrading zero_lt_one
      (MvPolynomial.isHomogeneous_X (ULift ℤ) i))

/-- The morphism from the direct complex `Proj` to the universal integral `Proj`, induced by
extension of coefficients. -/
def planeToIntegralProj : plane ⟶ Proj IntegralGrading :=
  Proj.map integralToComplexGraded irrelevant_le_map_integralToComplex

/-- On a standard affine chart, the comparison is the map of degree-zero homogeneous
localizations induced by extension of coefficients. -/
def coordinateAwayMap (i : Fin 3) :
    HomogeneousLocalization.Away IntegralGrading (MvPolynomial.X i) →+*
      HomogeneousLocalization.Away Grading (MvPolynomial.X i) := by
  exact (integralToComplexGraded_X i) ▸
    HomogeneousLocalization.Away.map integralToComplexGraded
      (MvPolynomial.X i : MvPolynomial (Fin 3) (ULift ℤ))

/-- The coefficient-extension map on the `i`-th standard affine chart, expressed through
the explicit polynomial coordinates on both homogeneous localizations.  This definition avoids
the dependent cast in `coordinateAwayMap` and is the convenient map for proving the base-change
universal property of the chart. -/
def coordinateChartBaseChangeMap (i : Fin 3) :
    HomogeneousLocalization.Away IntegralGrading (MvPolynomial.X i) →+*
      HomogeneousLocalization.Away Grading (MvPolynomial.X i) :=
  (Other.ProjectiveChart.chartRingEquiv ℂ i).toRingHom.comp
    ((MvPolynomial.map integralCoefficientMap).comp
      (Other.ProjectiveChart.chartRingEquiv (ULift ℤ) i).symm.toRingHom)

/-- On every standard projective chart, extension from the universal integral model to the
complex model is a pushout of coordinate rings.  Equivalently, after applying `Spec`, this is
the affine pullback square needed for the chartwise proof that `planeToProjectiveSpace` is an
isomorphism.  All four maps are explicit and no projectivity or isomorphism assumption occurs
in this statement. -/
lemma coordinateChartBaseChange_isPushout (i : Fin 3) :
    IsPushout
      (CommRingCat.ofHom integralCoefficientMap)
      (CommRingCat.ofHom (Other.ProjectiveChart.cR (ULift ℤ) i))
      (CommRingCat.ofHom (Other.ProjectiveChart.cR ℂ i))
      (CommRingCat.ofHom (coordinateChartBaseChangeMap i)) := by
  letI : Algebra.IsPushout (ULift ℤ) ℂ (MvPolynomial (Fin 2) (ULift ℤ))
      (MvPolynomial (Fin 2) ℂ) := MvPolynomial.instIsPushout
  let h := CommRingCat.isPushout_of_isPushout (ULift ℤ) ℂ
    (MvPolynomial (Fin 2) (ULift ℤ)) (MvPolynomial (Fin 2) ℂ)
  refine h.of_iso (Iso.refl _) (Iso.refl _)
    (Other.ProjectiveChart.chartRingEquiv (ULift ℤ) i).toCommRingCatIso
    (Other.ProjectiveChart.chartRingEquiv ℂ i).toCommRingCatIso ?_ ?_ ?_ ?_
  · rfl
  · exact congrArg CommRingCat.ofHom
      (Other.ProjectiveChart.chartRingEquiv_comp_C (ULift ℤ) i)
  · exact congrArg CommRingCat.ofHom
      (Other.ProjectiveChart.chartRingEquiv_comp_C ℂ i)
  · apply CommRingCat.hom_ext
    apply DFunLike.ext _ _
    intro x
    change (Other.ProjectiveChart.chartRingEquiv ℂ i)
        (MvPolynomial.map integralCoefficientMap x) =
      (Other.ProjectiveChart.chartRingEquiv ℂ i)
        (MvPolynomial.map integralCoefficientMap
          ((Other.ProjectiveChart.chartRingEquiv (ULift ℤ) i).symm
            ((Other.ProjectiveChart.chartRingEquiv (ULift ℤ) i) x)))
    rw [RingEquiv.symm_apply_apply]

/-- Contravariant geometric form of `coordinateChartBaseChange_isPushout`: the spectra of the
four explicit affine coordinate rings form a pullback square. -/
lemma coordinateChartBaseChange_isPullback (i : Fin 3) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Other.ProjectiveChart.cR ℂ i)))
      (Spec.map (CommRingCat.ofHom (coordinateChartBaseChangeMap i)))
      (Spec.map (CommRingCat.ofHom integralCoefficientMap))
      (Spec.map (CommRingCat.ofHom (Other.ProjectiveChart.cR (ULift ℤ) i))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (coordinateChartBaseChange_isPushout i)

private lemma coordinateAwayMap_mk_aux (i : Fin 3)
    (g : MvPolynomial (Fin 3) ℂ)
    (h : integralToComplexGraded
      (MvPolynomial.X i : MvPolynomial (Fin 3) (ULift ℤ)) = g)
    (hg : g ∈ Grading 1) (n : ℕ) (a : MvPolynomial (Fin 3) (ULift ℤ))
    (ha : a ∈ IntegralGrading (n • 1))
    (hga : integralToComplex a ∈ Grading (n • 1)) :
    (h ▸ HomogeneousLocalization.Away.map integralToComplexGraded
      (MvPolynomial.X i : MvPolynomial (Fin 3) (ULift ℤ)))
        (HomogeneousLocalization.Away.mk IntegralGrading
          (Other.ProjectiveChart.X_mem_one (ULift ℤ) i) n a ha) =
      HomogeneousLocalization.Away.mk Grading hg n (integralToComplex a) hga := by
  subst g
  rw [HomogeneousLocalization.Away.map_mk]
  rfl

lemma coordinateChartBaseChangeMap_eq_coordinateAwayMap (i : Fin 3) :
    coordinateChartBaseChangeMap i = coordinateAwayMap i := by
  apply RingHom.ext
  intro x
  obtain ⟨n, a, ha, hx⟩ := HomogeneousLocalization.Away.mk_surjective IntegralGrading
    (Other.ProjectiveChart.X_mem_one (ULift ℤ) i) x
  rw [← hx]
  have hdeh_comm :
      (MvPolynomial.map integralCoefficientMap).comp
          (Other.ProjectiveChart.deh (ULift ℤ) i) =
        (Other.ProjectiveChart.deh ℂ i).comp integralToComplex := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [Other.ProjectiveChart.deh, integralToComplex, integralCoefficientMap]
    · intro j
      refine Fin.succAboveCases i ?_ ?_ j
      · simp [Other.ProjectiveChart.deh, integralToComplex, integralCoefficientMap]
      · intro k
        simp only [RingHom.comp_apply, Other.ProjectiveChart.deh_X_succAbove,
          MvPolynomial.map_X]
        rw [integralToComplex_X, Other.ProjectiveChart.deh_X_succAbove]
  have hchartZ := Other.ProjectiveChart.chartHom_deh_eq (ULift ℤ) i ha
  have hdehZ :
      (Other.ProjectiveChart.chartRingEquiv (ULift ℤ) i).symm
          (HomogeneousLocalization.Away.mk IntegralGrading
            (Other.ProjectiveChart.X_mem_one (ULift ℤ) i) n a ha) =
        Other.ProjectiveChart.deh (ULift ℤ) i a := by
    rw [← hchartZ]
    change (Other.ProjectiveChart.chartRingEquiv (ULift ℤ) i).symm
      ((Other.ProjectiveChart.chartRingEquiv (ULift ℤ) i)
        (Other.ProjectiveChart.deh (ULift ℤ) i a)) = _
    exact (Other.ProjectiveChart.chartRingEquiv (ULift ℤ) i).symm_apply_apply _
  simp only [coordinateChartBaseChangeMap, RingHom.coe_comp, Function.comp_apply]
  change (Other.ProjectiveChart.chartRingEquiv ℂ i)
      (MvPolynomial.map integralCoefficientMap
        ((Other.ProjectiveChart.chartRingEquiv (ULift ℤ) i).symm
          (HomogeneousLocalization.Away.mk IntegralGrading
            (Other.ProjectiveChart.X_mem_one (ULift ℤ) i) n a ha))) = _
  rw [hdehZ]
  rw [show MvPolynomial.map integralCoefficientMap
      (Other.ProjectiveChart.deh (ULift ℤ) i a) =
      Other.ProjectiveChart.deh ℂ i (integralToComplex a) from
    DFunLike.congr_fun hdeh_comm a]
  have hdegC : integralToComplex a ∈ Grading (n • 1) :=
    integralToComplexGraded.map_mem ha
  have hchartC := Other.ProjectiveChart.chartHom_deh_eq ℂ i hdegC
  simp only [Other.ProjectiveChart.chartRingEquiv_apply]
  rw [hchartC]
  change HomogeneousLocalization.Away.mk Grading
    (Other.ProjectiveChart.X_mem_one ℂ i) n (integralToComplex a) hdegC = _
  unfold coordinateAwayMap
  exact (coordinateAwayMap_mk_aux i (MvPolynomial.X i) (integralToComplexGraded_X i)
    (Other.ProjectiveChart.X_mem_one ℂ i) n a ha hdegC).symm

@[reassoc]
lemma awayι_map_integralToComplex (i : Fin 3) :
    Proj.awayι Grading
        (integralToComplex (MvPolynomial.X i : MvPolynomial (Fin 3) (ULift ℤ)))
        (integralToComplexGraded.map_mem
          (MvPolynomial.isHomogeneous_X (ULift ℤ) i)) zero_lt_one ≫
        planeToIntegralProj =
      Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.Away.map integralToComplexGraded
          (MvPolynomial.X i : MvPolynomial (Fin 3) (ULift ℤ)))) ≫
        Proj.awayι IntegralGrading (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X (ULift ℤ) i) zero_lt_one :=
  Proj.awayι_comp_map integralToComplexGraded irrelevant_le_map_integralToComplex
    zero_lt_one (MvPolynomial.X i : MvPolynomial (Fin 3) (ULift ℤ))
    (MvPolynomial.isHomogeneous_X (ULift ℤ) i)

/-- The canonical comparison from the direct `Proj ℂ[X₀,X₁,X₂]` model to the
pullback-model projective plane over `Spec ℂ`. -/
def planeToProjectiveSpace :
    plane ⟶ ProjectiveSpace (Fin 3) (Spec ↧ℂ) :=
  pullback.lift structureMap planeToIntegralProj (Subsingleton.elim _ _)

/-- The standard `i`-th affine chart in the pullback model of complex projective space. -/
def projectiveSpaceCoordinateChart (i : Fin 3) :
    Spec (CommRingCat.of
        (HomogeneousLocalization.Away Grading (MvPolynomial.X i))) ⟶
      ProjectiveSpace (Fin 3) (Spec ↧ℂ) :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (Other.ProjectiveChart.cR ℂ i)))
    (Spec.map (CommRingCat.ofHom (coordinateChartBaseChangeMap i)) ≫
      Proj.awayι IntegralGrading (MvPolynomial.X i)
        (Other.ProjectiveChart.X_mem_one (ULift ℤ) i) zero_lt_one)
    (Subsingleton.elim _ _)

/-- The affine coordinate-ring pullback remains a pullback after replacing
`Spec (ULift ℤ)` by the terminal scheme. -/
lemma coordinateChartBaseChange_isPullback_terminal (i : Fin 3) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Other.ProjectiveChart.cR ℂ i)))
      (Spec.map (CommRingCat.ofHom (coordinateChartBaseChangeMap i)))
      (terminal.from (Spec ↧ℂ))
      (terminal.from (Spec (CommRingCat.of
        (HomogeneousLocalization.Away IntegralGrading (MvPolynomial.X i))))) := by
  let e : Spec ↧(ULift ℤ) ≅ ⊤_ Scheme :=
    specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal
  refine (coordinateChartBaseChange_isPullback i).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

/-- Each explicit affine chart of the pullback-model projective space is the pullback of the
corresponding standard affine chart in the universal integral `Proj`. -/
lemma projectiveSpaceCoordinateChart_isPullback (i : Fin 3) :
    IsPullback
      (projectiveSpaceCoordinateChart i)
      (Spec.map (CommRingCat.ofHom (coordinateChartBaseChangeMap i)))
      (pullback.snd (terminal.from (Spec ↧ℂ))
        (terminal.from (Proj IntegralGrading)))
      (Proj.awayι IntegralGrading (MvPolynomial.X i)
        (Other.ProjectiveChart.X_mem_one (ULift ℤ) i) zero_lt_one) := by
  let hglobal : IsPullback
      (pullback.fst (terminal.from (Spec ↧ℂ)) (terminal.from (Proj IntegralGrading)))
      (pullback.snd (terminal.from (Spec ↧ℂ)) (terminal.from (Proj IntegralGrading)))
      (terminal.from (Spec ↧ℂ)) (terminal.from (Proj IntegralGrading)) :=
    IsPullback.of_hasPullback _ _
  have hkfst : projectiveSpaceCoordinateChart i ≫
      pullback.fst (terminal.from (Spec ↧ℂ)) (terminal.from (Proj IntegralGrading)) =
      Spec.map (CommRingCat.ofHom (Other.ProjectiveChart.cR ℂ i)) := by
    exact pullback.lift_fst _ _ _
  have houter : IsPullback
      (projectiveSpaceCoordinateChart i ≫
        pullback.fst (terminal.from (Spec ↧ℂ)) (terminal.from (Proj IntegralGrading)))
      (Spec.map (CommRingCat.ofHom (coordinateChartBaseChangeMap i)))
      (terminal.from (Spec ↧ℂ))
      (Proj.awayι IntegralGrading (MvPolynomial.X i)
          (Other.ProjectiveChart.X_mem_one (ULift ℤ) i) zero_lt_one ≫
        terminal.from (Proj IntegralGrading)) := by
    rw [hkfst]
    rw [Subsingleton.elim
      (Proj.awayι IntegralGrading (MvPolynomial.X i)
          (Other.ProjectiveChart.X_mem_one (ULift ℤ) i) zero_lt_one ≫
        terminal.from (Proj IntegralGrading))
      (terminal.from (Spec (CommRingCat.of
        (HomogeneousLocalization.Away IntegralGrading (MvPolynomial.X i)))))]
    exact coordinateChartBaseChange_isPullback_terminal i
  exact houter.of_right (pullback.lift_snd _ _ _) hglobal

noncomputable instance projectiveSpaceCoordinateChart_isOpenImmersion (i : Fin 3) :
    IsOpenImmersion (projectiveSpaceCoordinateChart i) :=
  MorphismProperty.of_isPullback (projectiveSpaceCoordinateChart_isPullback i).flip inferInstance

@[reassoc]
lemma planeToProjectiveSpace_toBase :
    planeToProjectiveSpace ≫ ProjectiveSpace.toBase (Fin 3) (Spec ↧ℂ) = structureMap :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma planeToProjectiveSpace_toIntegralProj :
    planeToProjectiveSpace ≫
        pullback.snd (terminal.from (Spec ↧ℂ)) (terminal.from (Proj IntegralGrading)) =
      planeToIntegralProj :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma projectiveSpaceCoordinateChart_toBase (i : Fin 3) :
    projectiveSpaceCoordinateChart i ≫
        pullback.fst (terminal.from (Spec ↧ℂ)) (terminal.from (Proj IntegralGrading)) =
      Spec.map (CommRingCat.ofHom (Other.ProjectiveChart.cR ℂ i)) :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma projectiveSpaceCoordinateChart_toIntegralProj (i : Fin 3) :
    projectiveSpaceCoordinateChart i ≫
        pullback.snd (terminal.from (Spec ↧ℂ)) (terminal.from (Proj IntegralGrading)) =
      Spec.map (CommRingCat.ofHom (coordinateChartBaseChangeMap i)) ≫
        Proj.awayι IntegralGrading (MvPolynomial.X i)
          (Other.ProjectiveChart.X_mem_one (ULift ℤ) i) zero_lt_one :=
  pullback.lift_snd _ _ _

/-- The range of an explicit affine chart of pullback-model projective space is the inverse
image of the corresponding standard open in the universal integral `Proj`. -/
lemma projectiveSpaceCoordinateChart_opensRange (i : Fin 3) :
    (projectiveSpaceCoordinateChart i).opensRange =
      (pullback.snd (terminal.from (Spec ↧ℂ))
        (terminal.from (Proj IntegralGrading))) ⁻¹ᵁ
        Proj.basicOpen IntegralGrading (MvPolynomial.X i) := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (projectiveSpaceCoordinateChart_isPullback i).flip
    (⊤ : (Spec (CommRingCat.of
      (HomogeneousLocalization.Away IntegralGrading (MvPolynomial.X i)))).Opens)
  simp only [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange,
    Proj.opensRange_awayι] at h
  apply TopologicalSpace.Opens.ext
  exact congrArg TopologicalSpace.Opens.carrier h

/-- The three explicit standard affine charts cover the pullback-model projective plane. -/
lemma iSup_projectiveSpaceCoordinateChart_opensRange :
    ⨆ i : Fin 3, (projectiveSpaceCoordinateChart i).opensRange = ⊤ := by
  simp_rw [projectiveSpaceCoordinateChart_opensRange]
  exact (pullback.snd (terminal.from (Spec ↧ℂ))
    (terminal.from (Proj IntegralGrading))).iSup_preimage_eq_top
      (Other.ProjectiveChart.iSup_basicOpen_X_eq_top (ULift ℤ) 2)

/-- The open cover of pullback-model projective space by its three explicit standard affine
charts. -/
def projectiveSpaceCoordinateOpenCover :
    Scheme.OpenCover (ProjectiveSpace (Fin 3) (Spec ↧ℂ)) :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (Fin 3)
    (fun i => Spec (CommRingCat.of
      (HomogeneousLocalization.Away Grading (MvPolynomial.X i))))
    projectiveSpaceCoordinateChart (by
      intro x
      have hx : x ∈ (⊤ : (ProjectiveSpace (Fin 3) (Spec ↧ℂ)).Opens) := trivial
      rw [← iSup_projectiveSpaceCoordinateChart_opensRange] at hx
      have hx' : x ∈
          (↑(⨆ i, (projectiveSpaceCoordinateChart i).opensRange) :
            Set (ProjectiveSpace (Fin 3) (Spec ↧ℂ))) := hx
      rw [TopologicalSpace.Opens.coe_iSup] at hx'
      simpa only [Scheme.Hom.coe_opensRange, Set.mem_iUnion, Set.mem_range] using hx')

@[reassoc]
private lemma awayι_planeToIntegralProj_aux (i : Fin 3)
    (g : MvPolynomial (Fin 3) ℂ)
    (h : integralToComplexGraded
      (MvPolynomial.X i : MvPolynomial (Fin 3) (ULift ℤ)) = g)
    (hg : g ∈ Grading 1) :
    Proj.awayι Grading g hg zero_lt_one ≫ planeToIntegralProj =
      Spec.map (CommRingCat.ofHom
        (h ▸ HomogeneousLocalization.Away.map integralToComplexGraded
          (MvPolynomial.X i : MvPolynomial (Fin 3) (ULift ℤ)))) ≫
        Proj.awayι IntegralGrading (MvPolynomial.X i)
          (Other.ProjectiveChart.X_mem_one (ULift ℤ) i) zero_lt_one := by
  subst g
  exact Proj.awayι_comp_map integralToComplexGraded irrelevant_le_map_integralToComplex
    zero_lt_one (MvPolynomial.X i : MvPolynomial (Fin 3) (ULift ℤ))
    (Other.ProjectiveChart.X_mem_one (ULift ℤ) i)

/-- The comparison to the integral `Proj` on a standard affine chart. -/
@[reassoc]
lemma awayι_planeToIntegralProj (i : Fin 3) :
    Proj.awayι Grading (MvPolynomial.X i)
        (Other.ProjectiveChart.X_mem_one ℂ i) zero_lt_one ≫
        planeToIntegralProj =
      Spec.map (CommRingCat.ofHom (coordinateAwayMap i)) ≫
        Proj.awayι IntegralGrading (MvPolynomial.X i)
          (Other.ProjectiveChart.X_mem_one (ULift ℤ) i) zero_lt_one := by
  exact awayι_planeToIntegralProj_aux i (MvPolynomial.X i)
    (integralToComplexGraded_X i) (Other.ProjectiveChart.X_mem_one ℂ i)

/-- The direct projective plane's structure map on a standard affine chart is the spectrum of
the explicit constant-polynomial map. -/
@[reassoc]
lemma awayι_structureMap (i : Fin 3) :
    Proj.awayι Grading (MvPolynomial.X i)
        (Other.ProjectiveChart.X_mem_one ℂ i) zero_lt_one ≫ structureMap =
      Spec.map (CommRingCat.ofHom (Other.ProjectiveChart.cR ℂ i)) := by
  change Proj.awayι Grading (MvPolynomial.X i)
      (Other.ProjectiveChart.X_mem_one ℂ i) zero_lt_one ≫
      (Proj.toSpecZero Grading ≫ Scheme.Spec.map degreeZeroIso.symm.hom.op) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero]
  rw [Scheme.Spec_map]
  rw [← Spec.map_comp]
  rw [Spec.map_inj]
  ext r
  simp [degreeZeroIso, Other.ProjectiveChart.cR, Other.ProjectiveChart.cZero,
    ProjectiveSpace.degreeZeroEquiv, HomogeneousLocalization.fromZeroRingHom]
  rfl

/-- The `i`-th standard affine chart of the direct `Proj` model of the projective plane. -/
def planeCoordinateChart (i : Fin 3) :
    Spec (CommRingCat.of
      (HomogeneousLocalization.Away Grading (MvPolynomial.X i))) ⟶ plane :=
  Proj.awayι Grading (MvPolynomial.X i)
    (Other.ProjectiveChart.X_mem_one ℂ i) zero_lt_one

instance planeCoordinateChart_isOpenImmersion (i : Fin 3) :
    IsOpenImmersion (planeCoordinateChart i) := by
  unfold planeCoordinateChart plane
  infer_instance

@[reassoc]
lemma planeCoordinateChart_structureMap (i : Fin 3) :
    planeCoordinateChart i ≫ structureMap =
      Spec.map (CommRingCat.ofHom (Other.ProjectiveChart.cR ℂ i)) :=
  awayι_structureMap i

@[reassoc]
lemma planeCoordinateChart_toIntegralProj (i : Fin 3) :
    planeCoordinateChart i ≫ planeToIntegralProj =
      Spec.map (CommRingCat.ofHom (coordinateAwayMap i)) ≫
        Proj.awayι IntegralGrading (MvPolynomial.X i)
          (Other.ProjectiveChart.X_mem_one (ULift ℤ) i) zero_lt_one :=
  awayι_planeToIntegralProj i

/-- The comparison from the direct model to the pullback model identifies their explicit
standard affine charts. -/
@[reassoc]
lemma planeCoordinateChart_comp_planeToProjectiveSpace (i : Fin 3) :
    planeCoordinateChart i ≫ planeToProjectiveSpace =
      projectiveSpaceCoordinateChart i := by
  unfold planeToProjectiveSpace projectiveSpaceCoordinateChart ProjectiveSpace
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst,
      planeCoordinateChart_structureMap]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd,
      planeCoordinateChart_toIntegralProj,
      coordinateChartBaseChangeMap_eq_coordinateAwayMap]

/-- Pulling a target standard chart back along the comparison gives the corresponding standard
open of the direct model. -/
lemma planeToProjectiveSpace_preimage_coordinateChart_opensRange (i : Fin 3) :
    planeToProjectiveSpace ⁻¹ᵁ (projectiveSpaceCoordinateChart i).opensRange =
      (planeCoordinateChart i).opensRange := by
  rw [projectiveSpaceCoordinateChart_opensRange]
  unfold planeToProjectiveSpace ProjectiveSpace
  rw [← Scheme.Hom.comp_preimage]
  rw [pullback.lift_snd]
  unfold planeToIntegralProj
  unfold plane
  rw [Proj.map_preimage_basicOpen]
  rw [integralToComplexGraded_X]
  unfold planeCoordinateChart
  rw [Proj.opensRange_awayι]

/-- On each standard target chart, `planeToProjectiveSpace` is the identity after identifying
the two charts with the same explicit affine spectrum. -/
lemma planeCoordinateChart_isPullback (i : Fin 3) :
    IsPullback (𝟙 _)
      (planeCoordinateChart i) (projectiveSpaceCoordinateChart i)
      planeToProjectiveSpace := by
  apply IsOpenImmersion.isPullback
  · simpa using planeCoordinateChart_comp_planeToProjectiveSpace i
  · exact planeToProjectiveSpace_preimage_coordinateChart_opensRange i

/-- Each pullback of the comparison to a standard target chart is an isomorphism. -/
instance pullbackSnd_planeToProjectiveSpace_coordinateChart_isIso (i : Fin 3) :
    IsIso (pullback.snd planeToProjectiveSpace
      (projectiveSpaceCoordinateChart i)) := by
  let H := (planeCoordinateChart_isPullback i).flip
  have hsnd : pullback.snd planeToProjectiveSpace
      (projectiveSpaceCoordinateChart i) = H.isoPullback.inv := by
    simpa using H.isoPullback_inv_snd.symm
  rw [hsnd]
  infer_instance

/-- The direct `Proj ℂ[X₀,X₁,X₂]` model is canonically isomorphic to the
pullback-model projective plane over `Spec ℂ`. -/
instance planeToProjectiveSpace_isIso : IsIso planeToProjectiveSpace := by
  have h : MorphismProperty.isomorphisms Scheme planeToProjectiveSpace :=
    MorphismProperty.of_zeroHypercover_target projectiveSpaceCoordinateOpenCover (by
      intro i
      change IsIso (pullback.snd planeToProjectiveSpace
        (projectiveSpaceCoordinateChart i))
      exact pullbackSnd_planeToProjectiveSpace_coordinateChart_isIso i)
  exact h

/-- The canonical comparison supplies an explicit projective presentation of the direct
`Proj` model. -/
def planePresentationOfIsIso [IsIso planeToProjectiveSpace] :
    ProjectiveSpace.Presentation structureMap where
  ambientDimension := 2
  immersion := planeToProjectiveSpace
  isClosedImmersion := inferInstance
  immersion_toBase := planeToProjectiveSpace_toBase

/-- The explicit projective presentation, with the chartwise isomorphism proof discharged by
`planeToProjectiveSpace_isIso`.  In particular, this declaration has no hypothesis. -/
def planePresentation : ProjectiveSpace.Presentation structureMap :=
  planePresentationOfIsIso

/-- The explicit direct-`Proj` complex projective plane is projective over `Spec ℂ`. -/
instance planeOver_isProjective : IsProjective planeOver.hom :=
  ⟨⟨planePresentation⟩⟩

end AlgebraicGeometry.ProjectivePlane
