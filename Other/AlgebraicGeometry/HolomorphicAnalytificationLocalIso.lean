/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicAnalytificationCharts
public import Other.Oka.AnalyticSpace.LocalAtSource
public import Other.Oka.Analytification.SchemeAffine
public import Other.Oka.Analytification.UniversalProperty
public import Other.Oka.Analytification.RET.EtaleLocalIso

/-! The project-specific comparison with Oka's analytification is locally an isomorphism. -/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.ComplexPoint


variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- The algebraic chart neighborhood, viewed over Oka's lifted complex base. -/
def localNeighborhoodSchemeLFTℂ (z : ComplexPoint X) :
    ComplexAnalytic.SchemeLFTℂ.{0} :=
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  ⟨Over.mk (((localEtaleCoordinates X d z).neighborhood.ι ≫ X.hom) ≫
      (specComplexULiftIso).hom),
    show LocallyOfFiniteType
      (((localEtaleCoordinates X d z).neighborhood.ι ≫ X.hom) ≫
        (specComplexULiftIso).hom) from inferInstance⟩

/-- The chart neighborhood inclusion as a morphism of Oka's finite-type schemes. -/
def localNeighborhoodInclusionSchemeLFTℂ (z : ComplexPoint X) :
    localNeighborhoodSchemeLFTℂ X d z ⟶ toSchemeLFTℂ X d :=
  ObjectProperty.homMk <| Over.homMk
    (localEtaleCoordinates X d z).neighborhood.ι <| by
      simp only [localNeighborhoodSchemeLFTℂ, toSchemeLFTℂ]
      exact (Category.assoc _ _ _).symm

/-- The local comparison morphism to the algebraic chart neighborhood, over `Spec ℂ`. -/
def localHolomorphicAnalytificationπ (z : ComplexPoint X) :
    ComplexAnalytic.AnalyticSpace.toOverSpec.obj
        (localChartAnalyticSpace (X := X) (d := d) z) ⟶
      ComplexAnalytic.schemeToOverSpec.obj (localNeighborhoodSchemeLFTℂ X d z).obj :=
  Over.homMk (localAnalytificationToNeighborhood X d z) <| by
    have hglobal := Over.w
      (ComplexAnalytic.AnalyticSpace.toOverSpec.map
        ((holomorphicAnalyticSpace X d).ofRestrict (localChartSource X d z)) ≫
        holomorphicAnalytificationπ X d)
    change localAnalytificationToNeighborhood X d z ≫
        ((((localEtaleCoordinates X d z).neighborhood.ι ≫ X.hom) ≫
          (specComplexULiftIso).hom).toLRSHom) = _
    rw [show ((((localEtaleCoordinates X d z).neighborhood.ι ≫ X.hom) ≫
        (specComplexULiftIso).hom).toLRSHom) =
      (localEtaleCoordinates X d z).neighborhood.ι.toLRSHom ≫
        (X.hom ≫ (specComplexULiftIso).hom).toLRSHom from rfl]
    rw [← Category.assoc, localAnalytificationToNeighborhood_comp]
    exact hglobal

/-- The local comparison with the canonical analytification of the chart neighborhood. -/
def localComparisonToCanonical (z : ComplexPoint X) :
    localChartAnalyticSpace (X := X) (d := d) z ⟶
      ComplexAnalytic.analytification.obj (localNeighborhoodSchemeLFTℂ X d z) :=
  (ComplexAnalytic.isAnalytification_analytificationπ
    (localNeighborhoodSchemeLFTℂ X d z)).lift
      (localHolomorphicAnalytificationπ X d z)

@[reassoc (attr := simp)]
lemma localComparisonToCanonical_fac (z : ComplexPoint X) :
    ComplexAnalytic.AnalyticSpace.toOverSpec.map (localComparisonToCanonical X d z) ≫
        ComplexAnalytic.analytificationπ (localNeighborhoodSchemeLFTℂ X d z) =
      localHolomorphicAnalytificationπ X d z :=
  (ComplexAnalytic.isAnalytification_analytificationπ
    (localNeighborhoodSchemeLFTℂ X d z)).lift_fac _

/-- The lifted complex-algebra structure on the raw polynomial ring used by the chart square. -/
def coordinateAffineAlgebraMap :
    ULift.{0} ℂ →+* MvPolynomial (ULift.{0} (Fin d)) ℂ :=
  ComplexAnalytic.uliftAlgMap MvPolynomial.C

lemma coordinateAffineAlgebraMap_finiteType :
    (coordinateAffineAlgebraMap d).FiniteType := by
  refine RingHom.FiniteType.comp ?_
    (RingHom.FiniteType.of_surjective _ ULift.ringEquiv.surjective)
  rw [← MvPolynomial.algebraMap_eq, RingHom.finiteType_algebraMap]
  infer_instance

/-- The raw affine coordinate scheme, with the same spectrum as the chart square. -/
def coordinateAffineSchemeLFTℂ : ComplexAnalytic.SchemeLFTℂ.{0} :=
  ComplexAnalytic.SchemeLFTℂ.spec
    (CommRingCat.ofHom (coordinateAffineAlgebraMap d))
    (coordinateAffineAlgebraMap_finiteType d)

lemma okaGlobalOfMvPolynomial_comp_coordinateAffineAlgebraMap :
    (okaGlobalOfMvPolynomial (ULift.{0} (Fin d))).hom.comp
        (coordinateAffineAlgebraMap d) =
      ComplexAnalytic.uliftAlgMap
        (ComplexAnalytic.AnalyticSpace.complexAffineSpace.{0} d).algebraMap := by
  ext c
  change OkaRing.ofMvPolynomial _ (MvPolynomial.C c.down) =
    algebraMap ℂ (OkaRing ⊤) c.down
  exact (OkaRing.ofMvPolynomial _).commutes c.down

/-- The classical map from complex affine space to the raw affine coordinate scheme. -/
def coordinateAffineAnalytificationπ :
    ComplexAnalytic.AnalyticSpace.toOverSpec.obj
        (ComplexAnalytic.AnalyticSpace.complexAffineSpace.{0} d) ⟶
      ComplexAnalytic.schemeToOverSpec.obj (coordinateAffineSchemeLFTℂ d).obj :=
  Over.homMk (complexSpaceToSpec (ULift.{0} (Fin d))) <| by
    change (_root_.complexAffineSpace.{0} d).toSpecOfAlgMap
        (okaGlobalOfMvPolynomial (ULift.{0} (Fin d))).hom ≫
          Spec.locallyRingedSpaceMap
            (CommRingCat.ofHom (coordinateAffineAlgebraMap d)) =
      (_root_.complexAffineSpace.{0} d).toSpecOfAlgMap
        (ComplexAnalytic.uliftAlgMap
          (ComplexAnalytic.AnalyticSpace.complexAffineSpace.{0} d).algebraMap)
    rw [ComplexAnalytic.toSpecOfAlgMap_comp_locallyRingedSpaceMap]
    exact congrArg ((_root_.complexAffineSpace.{0} d).toSpecOfAlgMap)
      (okaGlobalOfMvPolynomial_comp_coordinateAffineAlgebraMap d)

def localAlgebraicAlgebraMap {x : X.left} (D : LocalEtaleCoordinates X d x) :
    ℂ →+* LocallyRingedSpace.Γ.obj (op D.neighborhood.toScheme.toLocallyRingedSpace) :=
  ((ΓSpec.locallyRingedSpaceAdjunction.homEquiv
    D.neighborhood.toScheme.toLocallyRingedSpace (op ↧ℂ)).symm
      (D.neighborhood.ι ≫ X.hom).toLRSHom).unop.hom

lemma localAlgebraicAlgebraMap_eq_appTop
    {x : X.left} (D : LocalEtaleCoordinates X d x) :
    localAlgebraicAlgebraMap X d D =
      (D.neighborhood.ι ≫ X.hom).appTop.hom.comp
        (Scheme.ΓSpecIso ↧ℂ).inv.hom := by
  simp only [localAlgebraicAlgebraMap, Functor.rightOp_obj,
    LocallyRingedSpace.Γ_obj]
  rfl

lemma localAlgebraicStructure_eq_toSpecOfAlgebraMap
    {x : X.left} (D : LocalEtaleCoordinates X d x) :
    (((D.neighborhood.ι ≫ X.hom) ≫ (specComplexULiftIso).hom).toLRSHom) =
      D.neighborhood.toScheme.toLocallyRingedSpace.toSpecOfAlgMap
        (ComplexAnalytic.uliftAlgMap (localAlgebraicAlgebraMap X d D)) := by
  have hD : D.neighborhood.toScheme.toLocallyRingedSpace.toSpecOfAlgMap
      (localAlgebraicAlgebraMap X d D) =
        (D.neighborhood.ι ≫ X.hom).toLRSHom := by
    rw [LocallyRingedSpace.toSpecOfAlgMap_eq_homEquiv]
    exact (ΓSpec.locallyRingedSpaceAdjunction.homEquiv
      D.neighborhood.toScheme.toLocallyRingedSpace (op ↧ℂ)).apply_symm_apply
        (D.neighborhood.ι ≫ X.hom).toLRSHom
  change (D.neighborhood.ι ≫ X.hom).toLRSHom ≫
      Spec.locallyRingedSpaceMap
        (CommRingCat.ofHom ULift.ringEquiv.toRingHom) = _
  rw [← hD]
  change (D.neighborhood.toScheme.toLocallyRingedSpace.toΓSpec ≫
      Spec.locallyRingedSpaceMap
        (CommRingCat.ofHom (localAlgebraicAlgebraMap X d D))) ≫
        Spec.locallyRingedSpaceMap
          (CommRingCat.ofHom ULift.ringEquiv.toRingHom) =
    D.neighborhood.toScheme.toLocallyRingedSpace.toΓSpec ≫
      Spec.locallyRingedSpaceMap
        (CommRingCat.ofHom
          ((localAlgebraicAlgebraMap X d D).comp ULift.ringEquiv.toRingHom))
  calc
    _ = D.neighborhood.toScheme.toLocallyRingedSpace.toΓSpec ≫
        (Spec.locallyRingedSpaceMap
            (CommRingCat.ofHom (localAlgebraicAlgebraMap X d D)) ≫
          Spec.locallyRingedSpaceMap
            (CommRingCat.ofHom ULift.ringEquiv.toRingHom)) := by
      rw [Category.assoc]
    _ = D.neighborhood.toScheme.toLocallyRingedSpace.toΓSpec ≫
        Spec.locallyRingedSpaceMap
          (CommRingCat.ofHom ULift.ringEquiv.toRingHom ≫
            CommRingCat.ofHom (localAlgebraicAlgebraMap X d D)) := by
      rw [Spec.locallyRingedSpaceMap_comp]
    _ = _ := by
      apply congrArg (fun q ↦
        D.neighborhood.toScheme.toLocallyRingedSpace.toΓSpec ≫
          Spec.locallyRingedSpaceMap q)
      exact (CommRingCat.ofHom_comp ULift.ringEquiv.toRingHom
        (localAlgebraicAlgebraMap X d D)).symm

lemma coordinateRingHomULift_comp_coordinateAffineAlgebraMap
    {x : X.left} (D : LocalEtaleCoordinates X d x) :
    (coordinateRingHomULift D).comp (coordinateAffineAlgebraMap d) =
      ComplexAnalytic.uliftAlgMap (localAlgebraicAlgebraMap X d D) := by
  ext c
  simp only [RingHom.coe_comp, Function.comp_apply, coordinateRingHomULift,
    coordinateAffineAlgebraMap, ComplexAnalytic.uliftAlgMap,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  change D.coordinateRingHomOnOpen
      (MvPolynomial.rename ULift.down (MvPolynomial.C (ULift.ringEquiv c))) =
    localAlgebraicAlgebraMap X d D (ULift.ringEquiv c)
  rw [MvPolynomial.rename_C]
  rw [localAlgebraicAlgebraMap_eq_appTop]
  exact DFunLike.congr_fun
    (congrArg CommRingCat.Hom.hom D.C_comp_coordinateRingHomOnOpen) (ULift.ringEquiv c)

/-- The étale coordinate map, bundled between schemes over lifted `Spec ℂ`. -/
def localCoordinateSchemeHom (z : ComplexPoint X) :
    localNeighborhoodSchemeLFTℂ X d z ⟶ coordinateAffineSchemeLFTℂ d :=
  ObjectProperty.homMk <| Over.homMk
    (toCoordinateSpecULift (localEtaleCoordinates X d z)) <| by
      let D := localEtaleCoordinates X d z
      apply Scheme.forgetToLocallyRingedSpace.map_injective
      change (D.neighborhood.toScheme.toSpecΓ.toLRSHom ≫
          Spec.locallyRingedSpaceMap
            (CommRingCat.ofHom (coordinateRingHomULift D))) ≫
            Spec.locallyRingedSpaceMap
              (CommRingCat.ofHom (coordinateAffineAlgebraMap d)) =
        (((D.neighborhood.ι ≫ X.hom) ≫ (specComplexULiftIso).hom).toLRSHom)
      rw [localAlgebraicStructure_eq_toSpecOfAlgebraMap X d D]
      change (D.neighborhood.toScheme.toLocallyRingedSpace.toSpecOfAlgMap
          (coordinateRingHomULift D)) ≫
            Spec.locallyRingedSpaceMap
              (CommRingCat.ofHom (coordinateAffineAlgebraMap d)) = _
      rw [ComplexAnalytic.toSpecOfAlgMap_comp_locallyRingedSpaceMap]
      exact congrArg D.neighborhood.toScheme.toLocallyRingedSpace.toSpecOfAlgMap
        (coordinateRingHomULift_comp_coordinateAffineAlgebraMap X d D)


variable (d : ℕ)

/-- The empty analytic zero locus is all of complex affine space. -/
def rawAnalytificationEmptyIso :
    ComplexAnalytic.AnalyticSpace.analytification.{0}
        (Fin.elim0 : Fin 0 → MvPolynomial (ULift.{0} (Fin d)) ℂ) ≅
      ComplexAnalytic.AnalyticSpace.complexAffineSpace.{0} d where
  hom := ComplexAnalytic.analytificationInclHom _
  inv := ComplexAnalytic.liftHom _ _ ComplexAnalytic.coord
    (fun j ↦ j.elim0)
  hom_inv_id := ComplexAnalytic.hom_ext_analytification _ _ _ fun i ↦ by
    rw [Category.id_comp, Category.assoc,
      ComplexAnalytic.AnalyticSpace.coordPullback_comp,
      ComplexAnalytic.coordPullback_liftHom_comp]
    rfl
  inv_hom_id := ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace _ _ fun j ↦ by
    change ComplexAnalytic.AnalyticSpace.coordPullback _ j =
      ComplexAnalytic.AnalyticSpace.coordPullback (𝟙 _) j
    rw [ComplexAnalytic.coordPullback_liftHom_comp]
    simp only [ComplexAnalytic.AnalyticSpace.coordPullback_apply]
    rfl

/-- Quotienting the raw polynomial ring by the ideal generated by the empty tuple changes
nothing. -/
def rawEmptyPresentationRingEquiv :
    MvPolynomial (ULift.{0} (Fin d)) ℂ ≃+*
      ComplexAnalytic.PresentedAlgebra.{0} d 0 Fin.elim0 :=
  (RingEquiv.quotientBot _).symm.trans
    (Ideal.quotEquivOfEq (by simp [ComplexAnalytic.presentationIdeal]))

@[simp]
lemma rawEmptyPresentationRingEquiv_apply
    (p : MvPolynomial (ULift.{0} (Fin d)) ℂ) :
    rawEmptyPresentationRingEquiv d p =
      Ideal.Quotient.mk _ p := by
  simp [rawEmptyPresentationRingEquiv]

/-- The spectrum of the empty presentation is the raw affine coordinate scheme over `Spec ℂ`. -/
def rawSpecPresentationOverIso :
    ComplexAnalytic.specOver
        (CommRingCat.ofHom (ComplexAnalytic.uliftAlgMap.{0}
          (ComplexAnalytic.presentedAlgebraMap
            (Fin.elim0 : Fin 0 → MvPolynomial (ULift.{0} (Fin d)) ℂ)))) ≅
      ComplexAnalytic.schemeToOverSpec.obj (coordinateAffineSchemeLFTℂ d).obj :=
  Over.isoMk (Spec.toLocallyRingedSpace.mapIso
    (rawEmptyPresentationRingEquiv d).toCommRingCatIso.op) (by
      change Spec.locallyRingedSpaceMap _ ≫ Spec.locallyRingedSpaceMap _ =
        Spec.locallyRingedSpaceMap _
      rw [← Spec.locallyRingedSpaceMap_comp]
      congr 1)

/-- The raw affine comparison, constructed through the empty presentation. -/
def coordinateAffineAnalytificationπViaPresentation :
    ComplexAnalytic.AnalyticSpace.toOverSpec.obj
        (ComplexAnalytic.AnalyticSpace.complexAffineSpace.{0} d) ⟶
      ComplexAnalytic.schemeToOverSpec.obj (coordinateAffineSchemeLFTℂ d).obj :=
  ComplexAnalytic.AnalyticSpace.toOverSpec.map (rawAnalytificationEmptyIso d).inv ≫
    ComplexAnalytic.analytificationToSpecOver
      (Fin.elim0 : Fin 0 → MvPolynomial (ULift.{0} (Fin d)) ℂ) ≫
    (rawSpecPresentationOverIso d).hom

theorem isAnalytification_coordinateAffineAnalytificationπViaPresentation :
    ComplexAnalytic.IsAnalytification
      (coordinateAffineAnalytificationπViaPresentation d) := by
  have h := ((ComplexAnalytic.isAnalytification_analytificationToSpec
    (Fin.elim0 : Fin 0 → MvPolynomial (ULift.{0} (Fin d)) ℂ)).of_iso
      (rawSpecPresentationOverIso d)).of_iso_source
        (rawAnalytificationEmptyIso d).symm
  simpa [coordinateAffineAnalytificationπViaPresentation] using h

@[simp]
lemma coordinateAffineAnalytificationπ_left :
    (coordinateAffineAnalytificationπ d).left =
      complexSpaceToSpec (ULift.{0} (Fin d)) := rfl

@[simp]
lemma coordinateAffineAnalytificationπViaPresentation_left :
    (coordinateAffineAnalytificationπViaPresentation d).left =
      (rawAnalytificationEmptyIso d).inv.toLRSHom ≫
        ComplexAnalytic.analytificationToSpec
          (Fin.elim0 : Fin 0 → MvPolynomial (ULift.{0} (Fin d)) ℂ) ≫
        Spec.locallyRingedSpaceMap
          (rawEmptyPresentationRingEquiv d).toCommRingCatIso.hom := rfl

theorem coordinateAffineAnalytificationπ_eq_viaPresentation :
    coordinateAffineAnalytificationπ d =
      coordinateAffineAnalytificationπViaPresentation d := by
  apply Over.OverMorphism.ext
  rw [coordinateAffineAnalytificationπ_left,
    coordinateAffineAnalytificationπViaPresentation_left]
  have hspec : Spec.locallyRingedSpaceMap
      (rawEmptyPresentationRingEquiv d).toCommRingCatIso.hom =
    Spec.locallyRingedSpaceMap
      (CommRingCat.ofHom (Ideal.Quotient.mk
        (ComplexAnalytic.presentationIdeal
          (Fin.elim0 : Fin 0 → MvPolynomial (ULift.{0} (Fin d)) ℂ)))) := by
    congr 1
  rw [hspec, ComplexAnalytic.analytificationToSpec_comp_specMk]
  rw [← Category.assoc]
  have hinv : (rawAnalytificationEmptyIso d).inv.toLRSHom ≫
      (rawAnalytificationEmptyIso d).hom.toLRSHom = 𝟙 _ :=
    congrArg ComplexAnalytic.AnalyticSpace.Hom.toLRSHom
      (rawAnalytificationEmptyIso d).inv_hom_id
  change complexSpaceToSpec (ULift.{0} (Fin d)) =
    ((rawAnalytificationEmptyIso d).inv.toLRSHom ≫
      (rawAnalytificationEmptyIso d).hom.toLRSHom) ≫
        complexSpaceToSpec (ULift.{0} (Fin d))
  rw [hinv, Category.id_comp]

theorem isAnalytification_coordinateAffineAnalytificationπ :
    ComplexAnalytic.IsAnalytification (coordinateAffineAnalytificationπ d) := by
  rw [coordinateAffineAnalytificationπ_eq_viaPresentation]
  exact isAnalytification_coordinateAffineAnalytificationπViaPresentation d


variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

lemma coordinateRingHomULift_etale
    {x : X.left} (D : LocalEtaleCoordinates X d x) :
    (coordinateRingHomULift D).Etale := by
  exact RingHom.Etale.respectsIso.2 D.coordinateRingHomOnOpen
    (MvPolynomial.renameEquiv ℂ Equiv.ulift).toRingEquiv
    D.coordinateRingHomOnOpen_etale

theorem localCoordinateSchemeHom_etale (z : ComplexPoint X) :
    Etale (localCoordinateSchemeHom X d z).hom.left := by
  let D := localEtaleCoordinates X d z
  letI : IsAffine D.neighborhood.toScheme := D.isAffine
  letI : IsIso D.neighborhood.toScheme.toSpecΓ := IsAffine.affine
  letI : Etale D.neighborhood.toScheme.toSpecΓ :=
    MorphismProperty.of_isIso @Etale _
  have hspec : Etale
      (Spec.map (CommRingCat.ofHom (coordinateRingHomULift D))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2
      (coordinateRingHomULift_etale X d D)
  letI : Etale (Spec.map (CommRingCat.ofHom (coordinateRingHomULift D))) := hspec
  change Etale (D.neighborhood.toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (coordinateRingHomULift D)))
  exact MorphismProperty.comp_mem @Etale _ _
    (MorphismProperty.of_isIso @Etale _) hspec

/-- Identify complex affine space with the canonical analytification of the raw coordinate
scheme. -/
def coordinateAffineCanonicalIso :
    ComplexAnalytic.AnalyticSpace.complexAffineSpace.{0} d ≅
      ComplexAnalytic.analytification.obj (coordinateAffineSchemeLFTℂ d) :=
  (isAnalytification_coordinateAffineAnalytificationπ d).isoOfIsAnalytification
    (ComplexAnalytic.isAnalytification_analytificationπ
      (coordinateAffineSchemeLFTℂ d))

@[reassoc (attr := simp)]
lemma coordinateAffineCanonicalIso_hom_comp :
    ComplexAnalytic.AnalyticSpace.toOverSpec.map
        (coordinateAffineCanonicalIso d).hom ≫
      ComplexAnalytic.analytificationπ (coordinateAffineSchemeLFTℂ d) =
        coordinateAffineAnalytificationπ d :=
  ComplexAnalytic.IsAnalytification.isoOfIsAnalytification_hom_comp _ _

def localChartAnalyticIso (z : ComplexPoint X) :
    localChartAnalyticSpace (X := X) (d := d) z ≅
      localChartTargetAnalyticSpace (X := X) (d := d) z where
  hom := ⟨(localChartLocallyRingedSpaceIso X d z).hom,
    localChartLocallyRingedSpaceIso_isCLinear X d z⟩
  inv := ⟨(localChartLocallyRingedSpaceIso X d z).inv,
    localChartLocallyRingedSpaceIso_inv_isCLinear (X := X) (d := d) z⟩
  hom_inv_id :=
    ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace.map_injective
      (localChartLocallyRingedSpaceIso X d z).hom_inv_id
  inv_hom_id :=
    ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace.map_injective
      (localChartLocallyRingedSpaceIso X d z).inv_hom_id

def localChartToComplexAffineSpaceHom (z : ComplexPoint X) :
    localChartAnalyticSpace (X := X) (d := d) z ⟶
      ComplexAnalytic.AnalyticSpace.complexAffineSpace.{0} d :=
  (localChartAnalyticIso X d z).hom ≫
    (ComplexAnalytic.AnalyticSpace.complexAffineSpace.{0} d).ofRestrict
      (localChartTargetULift X d z)

@[simp]
lemma localChartToComplexAffineSpaceHom_toLRSHom (z : ComplexPoint X) :
    (localChartToComplexAffineSpaceHom X d z).toLRSHom =
      localChartToComplexAffineSpace X d z := rfl

theorem localComparisonToCanonical_comp_coordinateMap (z : ComplexPoint X) :
    localComparisonToCanonical X d z ≫
        ComplexAnalytic.analytification.map (localCoordinateSchemeHom X d z) =
      localChartToComplexAffineSpaceHom X d z ≫
        (coordinateAffineCanonicalIso d).hom := by
  apply (ComplexAnalytic.isAnalytification_analytificationπ
    (coordinateAffineSchemeLFTℂ d)).hom_ext
  rw [Functor.map_comp, Functor.map_comp, Category.assoc,
    ComplexAnalytic.analytificationπ_naturality]
  rw [← Category.assoc, localComparisonToCanonical_fac]
  rw [Category.assoc, coordinateAffineCanonicalIso_hom_comp]
  apply Over.OverMorphism.ext
  change localAnalytificationToNeighborhood X d z ≫
      (toCoordinateSpecULift (localEtaleCoordinates X d z)).toLRSHom =
    localChartToComplexAffineSpace X d z ≫
      complexSpaceToSpec (ULift.{0} (Fin d))
  exact (localChart_comparison_square_raw (X := X) (d := d) z).symm

theorem localComparisonToCanonical_isLocalIso (z : ComplexPoint X) :
    ComplexAnalytic.AnalyticSpace.IsLocalIso
      (localComparisonToCanonical X d z) := by
  letI : Etale (localCoordinateSchemeHom X d z).hom.left :=
    localCoordinateSchemeHom_etale X d z
  letI : ComplexAnalytic.AnalyticSpace.IsLocalIso
      (ComplexAnalytic.analytification.map (localCoordinateSchemeHom X d z)) :=
    ComplexAnalytic.isLocalIso_analytification_map_of_etale _
  letI : ComplexAnalytic.AnalyticSpace.IsLocalIso
      (coordinateAffineCanonicalIso d).hom :=
    ComplexAnalytic.AnalyticSpace.isLocalIso_of_isIso _
  letI : ComplexAnalytic.AnalyticSpace.IsLocalIso
      (localChartAnalyticIso X d z).hom :=
    ComplexAnalytic.AnalyticSpace.isLocalIso_of_isIso _
  letI : ComplexAnalytic.AnalyticSpace.IsLocalIso
      ((ComplexAnalytic.AnalyticSpace.complexAffineSpace.{0} d).ofRestrict
        (localChartTargetULift X d z)) := inferInstance
  letI : ComplexAnalytic.AnalyticSpace.IsLocalIso
      (localChartToComplexAffineSpaceHom X d z) := by
    change ComplexAnalytic.AnalyticSpace.IsLocalIso
      ((localChartAnalyticIso X d z).hom ≫
        (ComplexAnalytic.AnalyticSpace.complexAffineSpace.{0} d).ofRestrict
          (localChartTargetULift X d z))
    infer_instance
  letI : ComplexAnalytic.AnalyticSpace.IsLocalIso
      (localChartToComplexAffineSpaceHom X d z ≫
        (coordinateAffineCanonicalIso d).hom) := inferInstance
  letI : ComplexAnalytic.AnalyticSpace.IsLocalIso
      (localComparisonToCanonical X d z ≫
        ComplexAnalytic.analytification.map
          (localCoordinateSchemeHom X d z)) := by
    rw [localComparisonToCanonical_comp_coordinateMap]
    infer_instance
  exact ComplexAnalytic.AnalyticSpace.isLocalIso_of_comp
    (localComparisonToCanonical X d z)
    (ComplexAnalytic.analytification.map (localCoordinateSchemeHom X d z))

theorem localComparisonToCanonical_comp_neighborhoodInclusion
    (z : ComplexPoint X) :
    (holomorphicAnalyticSpace X d).ofRestrict (localChartSource X d z) ≫
        comparisonToCanonical X d =
      localComparisonToCanonical X d z ≫
        ComplexAnalytic.analytification.map
          (localNeighborhoodInclusionSchemeLFTℂ X d z) := by
  apply (ComplexAnalytic.isAnalytification_analytificationπ
    (toSchemeLFTℂ X d)).hom_ext
  rw [Functor.map_comp, Functor.map_comp, Category.assoc,
    comparisonToCanonical_fac]
  rw [Category.assoc, ComplexAnalytic.analytificationπ_naturality]
  rw [← Category.assoc, localComparisonToCanonical_fac]
  apply Over.OverMorphism.ext
  change localToAlgebraic X d z =
    localAnalytificationToNeighborhood X d z ≫
      (localEtaleCoordinates X d z).neighborhood.ι.toLRSHom
  exact (localAnalytificationToNeighborhood_comp X d z).symm

theorem localNeighborhoodInclusionSchemeLFTℂ_etale (z : ComplexPoint X) :
    Etale (localNeighborhoodInclusionSchemeLFTℂ X d z).hom.left := by
  change Etale (localEtaleCoordinates X d z).neighborhood.ι
  infer_instance

theorem comparisonToCanonical_ofRestrict_isLocalIso (z : ComplexPoint X) :
    ComplexAnalytic.AnalyticSpace.IsLocalIso
      ((holomorphicAnalyticSpace X d).ofRestrict (localChartSource X d z) ≫
        comparisonToCanonical X d) := by
  letI : Etale (localNeighborhoodInclusionSchemeLFTℂ X d z).hom.left :=
    localNeighborhoodInclusionSchemeLFTℂ_etale X d z
  letI : ComplexAnalytic.AnalyticSpace.IsLocalIso
      (ComplexAnalytic.analytification.map
        (localNeighborhoodInclusionSchemeLFTℂ X d z)) :=
    ComplexAnalytic.isLocalIso_analytification_map_of_etale _
  letI : ComplexAnalytic.AnalyticSpace.IsLocalIso
      (localComparisonToCanonical X d z) :=
    localComparisonToCanonical_isLocalIso X d z
  rw [localComparisonToCanonical_comp_neighborhoodInclusion]
  infer_instance

theorem localChartSource_isOpenCover :
    TopologicalSpace.IsOpenCover
      (fun z : ComplexPoint X ↦ localChartSource X d z) := by
  apply TopologicalSpace.IsOpenCover.mk
  rw [eq_top_iff]
  intro z _
  exact Opens.mem_iSup.mpr ⟨z, mem_localChart_source X d z⟩

/-- The project-specific comparison is a local isomorphism, by descent from its coordinate
charts. -/
theorem comparisonToCanonical_isLocalIso :
    ComplexAnalytic.AnalyticSpace.IsLocalIso
      (comparisonToCanonical X d) := by
  exact ComplexAnalytic.AnalyticSpace.isLocalIso_of_isOpenCover_source
    (comparisonToCanonical X d)
    (fun z : ComplexPoint X ↦ localChartSource X d z)
    (localChartSource_isOpenCover X d)
    (comparisonToCanonical_ofRestrict_isLocalIso X d)

instance instIsLocalIsoComparisonToCanonical :
    ComplexAnalytic.AnalyticSpace.IsLocalIso
      (comparisonToCanonical X d) :=
  comparisonToCanonical_isLocalIso X d

end AlgebraicGeometry.ComplexPoint
