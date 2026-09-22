/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitProjectivePlaneHyperplaneClass
public import Other.AlgebraicGeometry.ProjectivePlaneHyperplaneCycle
public import HodgeConjecture.Lemmas.AlgebraicGeometry.CycleComponentSheafClass
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothClosedSupportCoclassSection
public import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothClosedSupportCoclassAmbientIso
public import Other.AlgebraicGeometry.CycleComponentCoclassNonzeroTransfer
public import Other.AlgebraicGeometry.CycleComponentPointClassNormalization
public import Other.AlgebraicTopology.OpenRestrictedLowestCohomologyNormalization

/-!
# Reduction of the explicit/canonical hyperplane comparison to normalization

This file does not assert that the two supported classes agree.  It transports the explicit
smooth-closed class to the canonical component support and uses the existing uniqueness theorem
to isolate the exact remaining normalization equality.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace AlgebraicGeometry
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ProjectivePlane

open AlgebraicGeometry.ComplexPoint


attribute [local instance] MvPolynomial.gradedAlgebra


/-- The canonical component structure morphism is the displayed smooth hyperplane structure
morphism, up to the equality `hyperplane_eq_cycleComponent`.  This transports the supplied
relative-dimension-one geometry to the canonical component rather than silently assuming that
its smooth locus is all of the hyperplane. -/
lemma hyperplaneCycleComponent_smoothOfRelativeDimension
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    SmoothOfRelativeDimension 1
      (cycleComponentι planeOver.left hyperplaneGenericPoint ≫ planeOver.hom) := by
  let C : Closeds planeOver.left :=
    ⟨closure ({hyperplaneGenericPoint} : Set planeOver.left), isClosed_closure⟩
  have hC : hyperplaneClosed = C := hyperplaneClosed_eq_closure_genericPoint
  let e : hyperplane ≅ cycleComponent planeOver.left hyperplaneGenericPoint :=
    eqToIso hyperplane_eq_cycleComponent
  have eqToIso_subschemeι (C D : Closeds planeOver.left) (h : C = D) :
      (eqToIso (congrArg (fun Z : Closeds planeOver.left ↦
        (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) h)).hom ≫
          (Scheme.IdealSheafData.vanishingIdeal D).subschemeι =
        (Scheme.IdealSheafData.vanishingIdeal C).subschemeι := by
    subst D
    simp
  have he : e.hom ≫ cycleComponentι planeOver.left hyperplaneGenericPoint = hyperplaneι :=
    eqToIso_subschemeι hyperplaneClosed C hC
  letI : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension 1) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).respectsIso
  apply (MorphismProperty.cancel_left_of_respectsIso
    (P := @SmoothOfRelativeDimension 1) e.hom _).mp
  rw [← Category.assoc, he]
  change SmoothOfRelativeDimension 1 hyperplaneOver.hom
  infer_instance

/-- The smooth locus used by the canonical cycle-component construction is the whole displayed
hyperplane. -/
lemma hyperplaneCycleComponent_smoothLocus_eq_top
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    (cycleComponentι planeOver.left hyperplaneGenericPoint ≫
      planeOver.hom).smoothLocus = ⊤ := by
  letI : SmoothOfRelativeDimension 1
      (cycleComponentι planeOver.left hyperplaneGenericPoint ≫ planeOver.hom) :=
    hyperplaneCycleComponent_smoothOfRelativeDimension
  letI : Smooth
      (cycleComponentι planeOver.left hyperplaneGenericPoint ≫ planeOver.hom) :=
    SmoothOfRelativeDimension.smooth 1 _
  exact Scheme.Hom.smoothLocus_eq_top _

/-- The canonical smooth-locus source has the expected relative dimension one. -/
noncomputable instance hyperplaneCycleComponentSmoothLocusOver_smoothOfRelativeDimension
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    SmoothOfRelativeDimension 1
      (cycleComponentSmoothLocusOver planeOver hyperplaneGenericPoint).hom := by
  simpa using cycleComponentSmoothClosedLiftStructureMap_smoothOfRelativeDimension
    planeOver hyperplaneGenericPoint (d := 2) hyperplaneGenericPoint_coheight

/-- Because the component is smooth, its smooth-locus immersion into the plane is
itself a closed immersion. -/
noncomputable instance hyperplaneCycleComponentSmoothLocusOverι_isClosedImmersion
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    IsClosedImmersion
      (cycleComponentSmoothLocusOverι planeOver hyperplaneGenericPoint).left := by
  haveI : IsIso
      (cycleComponentι planeOver.left hyperplaneGenericPoint ≫
        planeOver.hom).smoothLocus.ι := by
    rw [hyperplaneCycleComponent_smoothLocus_eq_top]
    exact (cycleComponent planeOver.left hyperplaneGenericPoint).topIso.isIso_hom
  change IsClosedImmersion
    ((cycleComponentι planeOver.left hyperplaneGenericPoint ≫
      planeOver.hom).smoothLocus.ι ≫
        cycleComponentι planeOver.left hyperplaneGenericPoint)
  infer_instance

/-- Consequently the algebraic singular boundary of the canonical component is empty. -/
lemma hyperplaneCycleComponent_singularLocusClosed_eq_bot
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    singularLocusClosed
      (cycleComponentι planeOver.left hyperplaneGenericPoint ≫ planeOver.hom) = ⊥ := by
  letI : SmoothOfRelativeDimension 1
      (cycleComponentι planeOver.left hyperplaneGenericPoint ≫ planeOver.hom) :=
    hyperplaneCycleComponent_smoothOfRelativeDimension
  unfold singularLocusClosed
  rw [hyperplaneCycleComponent_smoothLocus_eq_top]
  ext y
  simp

/-- The first canonical singular-filtration remainder is empty for the smooth hyperplane. -/
lemma hyperplaneCycleComponent_singularClosedFiltration_zero_eq_bot
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    cycleComponentSingularClosedFiltration planeOver hyperplaneGenericPoint 0 = ⊥ := by
  rw [cycleComponentSingularClosedFiltration, reducedSmoothClosedFiltration_zero,
    hyperplaneCycleComponent_singularLocusClosed_eq_bot]

/-- The corresponding ambient algebraic support is empty. -/
lemma hyperplaneCycleComponent_singularAmbientClosedFiltration_zero_eq_bot
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    cycleComponentSingularAmbientClosedFiltration planeOver hyperplaneGenericPoint 0 = ⊥ := by
  apply SetLike.coe_injective
  change cycleComponentι planeOver.left hyperplaneGenericPoint ''
      (cycleComponentSingularClosedFiltration planeOver hyperplaneGenericPoint 0 : Set _) = ∅
  rw [hyperplaneCycleComponent_singularClosedFiltration_zero_eq_bot]
  exact Set.image_empty _

/-- The auxiliary algebraic ambient open used for the component's smooth closed lift is the
whole projective plane. -/
lemma hyperplaneCycleComponent_smoothLocusAmbientOpen_eq_top
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    cycleComponentSmoothLocusAmbientOpen planeOver hyperplaneGenericPoint = ⊤ := by
  change (cycleComponentSingularAmbientClosedFiltration
    planeOver hyperplaneGenericPoint 0).compl = ⊤
  rw [hyperplaneCycleComponent_singularAmbientClosedFiltration_zero_eq_bot]
  apply SetLike.coe_injective
  ext y
  simp

/-- The analytified singular boundary is empty as well. -/
lemma hyperplaneCycleComponent_singularAnalyticClosedFiltration_zero_eq_bot
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    cycleComponentSingularAnalyticClosedFiltration planeOver hyperplaneGenericPoint 0 = ⊥ := by
  apply SetLike.coe_injective
  change Point.underlying ⁻¹'
      (cycleComponentSingularAmbientClosedFiltration planeOver hyperplaneGenericPoint 0 :
        Set planeOver.left) = ∅
  rw [hyperplaneCycleComponent_singularAmbientClosedFiltration_zero_eq_bot]
  exact Set.preimage_empty

/-- The canonical smooth-locus presentation and the displayed coordinate
hyperplane have exactly the same analytic image in the plane. -/
lemma cycleComponentSmoothLocus_range_eq_hyperplane_range
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    Set.range (Point.map
      (cycleComponentSmoothLocusOverι planeOver hyperplaneGenericPoint)) =
      Set.range (Point.map hyperplaneOverι) := by
  rw [cycleComponentSmoothLocus_complexPoints_range_eq_support_sdiff_boundary,
    hyperplaneCycleComponent_singularAnalyticClosedFiltration_zero_eq_bot]
  simpa using cycleComponentSupport_hyperplaneGenericPoint

/-- The globally normalized section for the displayed hyperplane agrees with
the globally normalized section of the canonical smooth-locus presentation.
This is the same-ambient comparison; the remaining canonical normalization
bridge is compatibility with transport through the auxiliary ambient open. -/
lemma hyperplaneSmoothClosedSupportCoclassSection_eq_cycleComponentSmoothLocus
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    smoothClosedSupportCoclassSection
        planeOver hyperplaneOver hyperplaneOverι 1 2 =
      supportRelativeCohomologySectionTransport
        (TopCat.of (ComplexPoint planeOver))
        (Set.range (Point.map hyperplaneOverι)) 2
        cycleComponentSmoothLocus_range_eq_hyperplane_range ⊤
        (smoothClosedSupportCoclassSection planeOver
          (cycleComponentSmoothLocusOver planeOver hyperplaneGenericPoint)
          (cycleComponentSmoothLocusOverι planeOver hyperplaneGenericPoint) 1 2) := by
  exact smoothClosedSupportCoclassSection_eq_cross planeOver hyperplaneOver
    hyperplaneOverι 1 2 (cycleComponentSmoothLocusOver planeOver hyperplaneGenericPoint)
    (cycleComponentSmoothLocusOverι planeOver hyperplaneGenericPoint)
    cycleComponentSmoothLocus_range_eq_hyperplane_range

/-- Thus the open on which the canonical component normalization lives is the whole analytic
projective plane. -/
lemma hyperplaneCycleComponent_smoothSupportAmbientOpen_eq_top
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    cycleComponentSmoothSupportAmbientOpen planeOver hyperplaneGenericPoint = ⊤ := by
  change (cycleComponentSingularAnalyticClosedFiltration
    planeOver hyperplaneGenericPoint 0).compl = ⊤
  rw [hyperplaneCycleComponent_singularAnalyticClosedFiltration_zero_eq_bot]
  apply SetLike.coe_injective
  ext y
  simp

lemma cycleComponentSmoothLocus_range_eq_cycleComponentSupport
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    Set.range (Point.map
      (cycleComponentSmoothLocusOverι planeOver hyperplaneGenericPoint)) =
      cycleComponentSupport planeOver hyperplaneGenericPoint :=
  cycleComponentSmoothLocus_range_eq_hyperplane_range.trans
    cycleComponentSupport_hyperplaneGenericPoint.symm

set_option maxHeartbeats 1600000 in
/-- In the smooth hyperplane case, transport from the auxiliary algebraic ambient open preserves
the normalized normal-chart section exactly.  This is the ambient-open naturality step that is
not supplied by the fixed-chart winding computation. -/
lemma hyperplaneCycleComponentSmoothSupportCoclassSection_eq_direct
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    cycleComponentSmoothSupportCoclassSection planeOver hyperplaneGenericPoint
        (d := 2) hyperplaneGenericPoint_coheight =
      supportRelativeCohomologySectionSupportOpenTransport
        (TopCat.of (ComplexPoint planeOver))
        (cycleComponentSupport planeOver hyperplaneGenericPoint) 2
        cycleComponentSmoothLocus_range_eq_cycleComponentSupport
        hyperplaneCycleComponent_smoothSupportAmbientOpen_eq_top.symm
        (smoothClosedSupportCoclassSection planeOver
          (cycleComponentSmoothLocusOver planeOver hyperplaneGenericPoint)
          (cycleComponentSmoothLocusOverι planeOver hyperplaneGenericPoint) 1 2) := by
  let A := cycleComponentSmoothLocusAmbientOpenOver planeOver hyperplaneGenericPoint
  let Y := cycleComponentSmoothLocusOver planeOver hyperplaneGenericPoint
  let f : A ⟶ planeOver := openInclusion planeOver
    (cycleComponentSmoothLocusAmbientOpen planeOver hyperplaneGenericPoint)
  let i : Y ⟶ A := cycleComponentSmoothLocusClosedLiftOver
    planeOver hyperplaneGenericPoint
  let hf : IsOpenEmbedding (Point.map f) :=
    cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding
      planeOver hyperplaneGenericPoint
  letI : SmoothOfRelativeDimension 2 A.hom :=
    cycleComponentSmoothLocusAmbientOpen_smoothOfRelativeDimension
      planeOver hyperplaneGenericPoint
  letI : SmoothOfRelativeDimension 1 Y.hom :=
    hyperplaneCycleComponentSmoothLocusOver_smoothOfRelativeDimension
  letI : IsClosedImmersion i.left :=
    cycleComponentSmoothLocusClosedLiftOver_isClosedImmersion
      planeOver hyperplaneGenericPoint
  have hcomp : i ≫ f =
      cycleComponentSmoothLocusOverι planeOver hyperplaneGenericPoint := by
    apply CostructuredArrow.hom_ext
    exact cycleComponentSmoothLocusClosedLift_ι planeOver hyperplaneGenericPoint
  letI : IsClosedImmersion (i ≫ f).left := by
    rw [hcomp]
    exact hyperplaneCycleComponentSmoothLocusOverι_isClosedImmersion
  letI : IsIso
      (cycleComponentSmoothLocusAmbientOpen planeOver hyperplaneGenericPoint).ι := by
    rw [hyperplaneCycleComponent_smoothLocusAmbientOpen_eq_top]
    exact planeOver.left.topIso.isIso_hom
  letI : IsIso f.left := by
    change IsIso
      (cycleComponentSmoothLocusAmbientOpen planeOver hyperplaneGenericPoint).ι
    infer_instance
  letI : IsIso f := by
    letI : IsIso ((Over.forget (Spec (.of ℂ))).map f) := by
      change IsIso f.left
      infer_instance
    exact isIso_of_reflects_iso f (Over.forget _)
  letI : Nonempty (ComplexPoint Y) :=
    cycleComponentSmoothLocusOver_nonempty planeOver hyperplaneGenericPoint
  letI : Nonempty (ComplexPoint A) :=
    ⟨Point.map i (Classical.choice (inferInstance : Nonempty (ComplexPoint Y)))⟩
  have hsupport : cycleComponentSupport planeOver hyperplaneGenericPoint =
      Set.range (Point.map (i ≫ f)) := by
    rw [hcomp, cycleComponentSmoothLocus_range_eq_hyperplane_range]
    exact cycleComponentSupport_hyperplaneGenericPoint
  have hB : Point.map f ⁻¹' Set.range (Point.map (i ≫ f)) =
      Set.range (Point.map i) := by
    rw [← hsupport]
    exact cycleComponentSmoothClosedLiftAmbientMap_support
      planeOver hyperplaneGenericPoint
  have hTop : (ambientAlgebraicMapOpenFunctor A planeOver f hf).obj ⊤ = ⊤ := by
    exact (cycleComponentSmoothClosedLiftAmbientMap_imageOpen
      planeOver hyperplaneGenericPoint).trans
        hyperplaneCycleComponent_smoothSupportAmbientOpen_eq_top
  have h := smoothClosedSupportCoclassSection_ambientIso
    A planeOver Y f i 1 2 hf hB hTop
  have hrange : Set.range (Point.map
      (cycleComponentSmoothLocusOverι planeOver hyperplaneGenericPoint)) =
      Set.range (Point.map (i ≫ f)) := by rw [hcomp]
  have hc := smoothClosedSupportCoclassSection_eq_cross planeOver Y (i ≫ f) 1 2 Y
    (cycleComponentSmoothLocusOverι planeOver hyperplaneGenericPoint) hrange
  have h' := h.trans hc
  have haux : cycleComponentSmoothClosedLiftCoclassSection
      planeOver hyperplaneGenericPoint (d := 2) hyperplaneGenericPoint_coheight =
      smoothClosedSupportCoclassSection A Y i 1 2 := by
    rfl
  change supportRelativeCohomologySectionOnOpen
      (cycleComponentSmoothClosedLiftAmbientMap planeOver hyperplaneGenericPoint)
      (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding
        planeOver hyperplaneGenericPoint)
      (cycleComponentSupport planeOver hyperplaneGenericPoint)
      (Set.range (Point.map i))
      (cycleComponentSmoothClosedLiftAmbientMap_support
        planeOver hyperplaneGenericPoint) 2
      (cycleComponentSmoothSupportAmbientOpen planeOver hyperplaneGenericPoint)
      (cycleComponentSmoothClosedLiftAmbientMap_imageOpen
        planeOver hyperplaneGenericPoint)
      (cycleComponentSmoothClosedLiftCoclassSection planeOver hyperplaneGenericPoint
        (d := 2) hyperplaneGenericPoint_coheight) = _
  rw [haux]
  have htransport := supportRelativeCohomologySectionOnOpen_transport
    (cycleComponentSmoothClosedLiftAmbientMap planeOver hyperplaneGenericPoint)
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding
      planeOver hyperplaneGenericPoint)
    (cycleComponentSupport planeOver hyperplaneGenericPoint)
    (Set.range (Point.map i))
    (cycleComponentSmoothClosedLiftAmbientMap_support
      planeOver hyperplaneGenericPoint)
    hsupport.symm hB
    hyperplaneCycleComponent_smoothSupportAmbientOpen_eq_top.symm
    hTop
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen
      planeOver hyperplaneGenericPoint)
    2
    (smoothClosedSupportCoclassSection A Y i 1 2)
  have h'trans := congrArg
    (supportRelativeCohomologySectionSupportOpenTransport
      (TopCat.of (ComplexPoint planeOver))
      (cycleComponentSupport planeOver hyperplaneGenericPoint) 2
      hsupport.symm hyperplaneCycleComponent_smoothSupportAmbientOpen_eq_top.symm) h'
  have h'trans' :
      supportRelativeCohomologySectionSupportOpenTransport
          (TopCat.of (ComplexPoint planeOver))
          (cycleComponentSupport planeOver hyperplaneGenericPoint) 2
          hsupport.symm hyperplaneCycleComponent_smoothSupportAmbientOpen_eq_top.symm
          (supportRelativeCohomologySectionOnOpen
            (cycleComponentSmoothClosedLiftAmbientMap planeOver hyperplaneGenericPoint)
            (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding
              planeOver hyperplaneGenericPoint)
            (Set.range (Point.map (i ≫ f))) (Set.range (Point.map i)) hB
            2 ⊤ hTop (smoothClosedSupportCoclassSection A Y i 1 2)) =
        supportRelativeCohomologySectionSupportOpenTransport
          (TopCat.of (ComplexPoint planeOver))
          (cycleComponentSupport planeOver hyperplaneGenericPoint) 2
          hsupport.symm hyperplaneCycleComponent_smoothSupportAmbientOpen_eq_top.symm
          (supportRelativeCohomologySectionTransport
            (TopCat.of (ComplexPoint planeOver)) (Set.range (Point.map (i ≫ f)))
            2 hrange ⊤
            (smoothClosedSupportCoclassSection planeOver Y
              (cycleComponentSmoothLocusOverι planeOver hyperplaneGenericPoint) 1 2)) := by
    simpa only [f, hf, cycleComponentSmoothClosedLiftAmbientMap, Nat.reduceMul] using h'trans
  rw [htransport]
  rw [h'trans']
  rw [supportRelativeCohomologySectionSupportOpenTransport_comp_support]

/-- For the smooth hyperplane the canonical support-extension restriction is the identity,
after transporting sections along the proved equality of its smooth-support open with `⊤`.
The equality transport is displayed explicitly because the source and target section complexes
are not definitionally the same object. -/
lemma hyperplaneCycleComponent_supportSectionRestriction_comp_topTransport
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    cycleComponentSupportSectionRestriction planeOver hyperplaneGenericPoint ≫
      (TopCat.Sheaf.sectionComplexEqIso
        (TopCat.of (ComplexPoint planeOver))
        (complexSupportInjectiveComplex planeOver
          (cycleComponentAnalyticClosedSupport planeOver hyperplaneGenericPoint))
        hyperplaneCycleComponent_smoothSupportAmbientOpen_eq_top).hom = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  let F := (complexSupportInjectiveComplex planeOver
    (cycleComponentAnalyticClosedSupport planeOver hyperplaneGenericPoint)).X n
  change F.obj.map _ ≫ F.obj.map _ = 𝟙 _
  rw [← F.obj.map_comp, ← F.obj.map_id]
  congr 1

/-- The preceding literal identity survives passage to homology in the hyperplane's cycle
degree.  Thus the support-extension part of the canonical normalization contributes no class or
sign in this smooth example. -/
lemma hyperplaneCycleComponent_supportSectionRestriction_homology_comp_topTransport
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    HomologicalComplex.homologyMap
        (cycleComponentSupportSectionRestriction planeOver hyperplaneGenericPoint) 2 ≫
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.sectionComplexEqIso
          (TopCat.of (ComplexPoint planeOver))
          (complexSupportInjectiveComplex planeOver
            (cycleComponentAnalyticClosedSupport planeOver hyperplaneGenericPoint))
          hyperplaneCycleComponent_smoothSupportAmbientOpen_eq_top).hom 2 = 𝟙 _ := by
  rw [← HomologicalComplex.homologyMap_comp,
    hyperplaneCycleComponent_supportSectionRestriction_comp_topTransport,
    HomologicalComplex.homologyMap_id]

/-- The closed analytic support attached to the canonical component `(X₀)` is the same closed
subset as the image support of the displayed hyperplane immersion. -/
lemma cycleComponentAnalyticClosedSupport_hyperplaneGenericPoint
    [IsProjective planeOver.hom] :
    cycleComponentAnalyticClosedSupport planeOver hyperplaneGenericPoint =
      smoothClosedAnalyticSupport planeOver hyperplaneOver hyperplaneOverι := by
  apply Closeds.ext
  exact cycleComponentSupport_hyperplaneGenericPoint

/-- The explicit smooth-closed supported-injective class, transported only along the proved
equality of its closed support with the canonical component support. -/
noncomputable def hyperplaneSmoothClosedSupportInjectiveClassInCycleComponent
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    CycleComponentSupportedCohomology planeOver hyperplaneGenericPoint 1 := by
  change ((((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint planeOver)) ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (complexSupportInjectiveComplex planeOver
          (cycleComponentAnalyticClosedSupport planeOver hyperplaneGenericPoint)))).homology
            (2 * (1 : ℤ))
  rw [cycleComponentAnalyticClosedSupport_hyperplaneGenericPoint]
  simpa using
    (smoothClosedSupportInjectiveClass planeOver hyperplaneOver hyperplaneOverι 1 2)

/-- Equality of the explicit supported-injective hyperplane class with the canonical
cycle-component class is equivalent to one concrete normalization equation.  The reverse
implication is exactly `cycleComponentSupportedInjectiveClass_unique`; no equality is supplied
as a hypothesis to either construction. -/
theorem hyperplaneSmoothClosedSupportInjectiveClass_eq_cycleComponent_iff_normalization
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    hyperplaneSmoothClosedSupportInjectiveClassInCycleComponent =
        cycleComponentSupportedInjectiveClass planeOver hyperplaneGenericPoint
          (d := 2) hyperplaneGenericPoint_coheight ↔
      (cycleComponentSupportedClassNormalizationIso planeOver hyperplaneGenericPoint
          (d := 2) hyperplaneGenericPoint_coheight).hom
          hyperplaneSmoothClosedSupportInjectiveClassInCycleComponent =
      cycleComponentSmoothSupportCoclassSection planeOver hyperplaneGenericPoint
          (d := 2) hyperplaneGenericPoint_coheight := by
  constructor
  · intro h
    rw [h]
    exact cycleComponentSupportedInjectiveClass_normalization
      planeOver hyperplaneGenericPoint hyperplaneGenericPoint_coheight
  · intro h
    exact cycleComponentSupportedInjectiveClass_unique
      planeOver hyperplaneGenericPoint hyperplaneGenericPoint_coheight _ h

set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The normalization equation for the displayed coordinate hyperplane is proved from the
actual support-sheaf comparison and the ambient-open transport theorem.  No local winding
normalization is assumed here: the only input is the displayed smooth relative-dimension
instance. -/
theorem hyperplaneSmoothClosedSupportInjectiveClass_normalization
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    (cycleComponentSupportedClassNormalizationIso planeOver hyperplaneGenericPoint
        (d := 2) (p := 1) (by simpa using hyperplaneGenericPoint_coheight)).hom
        hyperplaneSmoothClosedSupportInjectiveClassInCycleComponent =
      cycleComponentSmoothSupportCoclassSection planeOver hyperplaneGenericPoint
        (d := 2) (by simpa using hyperplaneGenericPoint_coheight) := by
  rw [cycleComponentSupportedClassNormalizationIso_hom]
  rw [cycleComponentSmoothSupportLowestSectionCohomologyIso]
  rw [TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso_hom]
  simp only [ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply]
  have hsection :=
    complexSupportInjectiveCohomologySheafIsoRelative_restriction_section
      planeOver (cycleComponentAnalyticClosedSupport planeOver hyperplaneGenericPoint) 2
      (homOfLE (show cycleComponentSmoothSupportAmbientOpen planeOver hyperplaneGenericPoint ≤
        ⊤ from le_top))
  dsimp [cycleComponentSupportSectionRestriction] at hsection ⊢
  rw [← ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply]
  rw [hsection]
  simp only [ConcreteCategory.comp_apply]
  have hnorm := smoothClosedSupportInjectiveClass_normalization
    planeOver hyperplaneOver hyperplaneOverι 1 2
  dsimp [hyperplaneSmoothClosedSupportInjectiveClassInCycleComponent] at hnorm ⊢
  have hS : cycleComponentAnalyticClosedSupport planeOver hyperplaneGenericPoint =
      smoothClosedAnalyticSupport planeOver hyperplaneOver hyperplaneOverι :=
    cycleComponentAnalyticClosedSupport_hyperplaneGenericPoint
  have hR : Set.range (Point.map hyperplaneOverι) =
      cycleComponentSupport planeOver hyperplaneGenericPoint :=
    cycleComponentSupport_hyperplaneGenericPoint.symm
  have happly := complexSupportInjectiveCohomologySheafIsoRelative_section_apply
    planeOver (smoothClosedAnalyticSupport planeOver hyperplaneOver hyperplaneOverι) 2 ⊤
    (smoothClosedSupportInjectiveClass planeOver hyperplaneOver hyperplaneOverι 1 2)
  have hbase := happly.symm.trans hnorm
  have hhelper : ∀ (S : Closeds (ComplexPoint planeOver))
      (hS' : S = smoothClosedAnalyticSupport planeOver hyperplaneOver hyperplaneOverι)
      (hSet : (S : Set (ComplexPoint planeOver)) =
        cycleComponentSupport planeOver hyperplaneGenericPoint)
      (z : ((((TopCat.Sheaf.supportEvaluation
        (TopCat.of (ComplexPoint planeOver)) ⊤).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (complexSupportInjectiveComplex planeOver S))).homology 2)
      (hz : z = (by
        change ((((TopCat.Sheaf.supportEvaluation
          (TopCat.of (ComplexPoint planeOver)) ⊤).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (complexSupportInjectiveComplex planeOver S))).homology 2
        rw [hS']
        simpa using (smoothClosedSupportInjectiveClass
          planeOver hyperplaneOver hyperplaneOverι 1 2))),
      supportRelativeCohomologySectionTransport
          (TopCat.of (ComplexPoint planeOver))
          (cycleComponentSupport planeOver hyperplaneGenericPoint) 2 hSet ⊤
          ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint planeOver))
            (S : Set (ComplexPoint planeOver)) 2).app (Opposite.op ⊤)
            ((complexSupportInjectiveSectionCohomologyEquiv planeOver S ⊤ 2) z)) =
        supportRelativeCohomologySectionTransport
          (TopCat.of (ComplexPoint planeOver))
          (cycleComponentSupport planeOver hyperplaneGenericPoint) 2 hR ⊤
          (smoothClosedSupportCoclassSection planeOver hyperplaneOver hyperplaneOverι 1 2) := by
    intro S hS' hSet z hz
    subst S
    have hz' : z = smoothClosedSupportInjectiveClass
        planeOver hyperplaneOver hyperplaneOverι 1 2 := by
      simpa using hz
    rw [hz']
    have hb := congrArg
      (fun s ↦ supportRelativeCohomologySectionTransport
        (TopCat.of (ComplexPoint planeOver))
        (cycleComponentSupport planeOver hyperplaneGenericPoint) 2 hSet ⊤ s) hbase
    have hp : hSet = hR := Subsingleton.elim _ _
    simpa only [hp] using hb
  have hclass : hyperplaneSmoothClosedSupportInjectiveClassInCycleComponent = (by
      change ((((TopCat.Sheaf.supportEvaluation
        (TopCat.of (ComplexPoint planeOver)) ⊤).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (complexSupportInjectiveComplex planeOver
          (cycleComponentAnalyticClosedSupport planeOver hyperplaneGenericPoint)))).homology 2
      rw [hS]
      simpa using (smoothClosedSupportInjectiveClass
        planeOver hyperplaneOver hyperplaneOverι 1 2)) := by
    rfl
  have hinner :
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint planeOver))
          (cycleComponentAnalyticClosedSupport planeOver hyperplaneGenericPoint) 2).app
        (Opposite.op ⊤)
        ((complexSupportInjectiveSectionCohomologyEquiv planeOver
          (cycleComponentAnalyticClosedSupport planeOver hyperplaneGenericPoint) ⊤ 2)
          hyperplaneSmoothClosedSupportInjectiveClassInCycleComponent) =
        supportRelativeCohomologySectionTransport
          (TopCat.of (ComplexPoint planeOver))
          (cycleComponentSupport planeOver hyperplaneGenericPoint) 2 hR ⊤
          (smoothClosedSupportCoclassSection planeOver hyperplaneOver hyperplaneOverι 1 2) := by
    simpa only [supportRelativeCohomologySectionTransport] using
      (hhelper (cycleComponentAnalyticClosedSupport planeOver hyperplaneGenericPoint) hS rfl
        hyperplaneSmoothClosedSupportInjectiveClassInCycleComponent hclass)
  calc
    _ = (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint planeOver))
        (cycleComponentSupport planeOver hyperplaneGenericPoint) 2).obj.map
        (homOfLE (show cycleComponentSmoothSupportAmbientOpen planeOver hyperplaneGenericPoint ≤
          ⊤ from le_top)).op
        (supportRelativeCohomologySectionTransport
          (TopCat.of (ComplexPoint planeOver))
          (cycleComponentSupport planeOver hyperplaneGenericPoint) 2 hR ⊤
          (smoothClosedSupportCoclassSection planeOver hyperplaneOver hyperplaneOverι 1 2)) := by
      exact congrArg (fun s ↦
        (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint planeOver))
          (cycleComponentSupport planeOver hyperplaneGenericPoint) 2).obj.map
          (homOfLE (show cycleComponentSmoothSupportAmbientOpen planeOver hyperplaneGenericPoint ≤
            ⊤ from le_top)).op s) hinner
    _ = _ := by
      have hrestrict : ∀ (U : Opens (ComplexPoint planeOver))
          (hU : U = ⊤),
          (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint planeOver))
              (cycleComponentSupport planeOver hyperplaneGenericPoint) 2).obj.map
              (homOfLE (show U ≤ ⊤ from le_top)).op
              (supportRelativeCohomologySectionTransport
                (TopCat.of (ComplexPoint planeOver))
                (cycleComponentSupport planeOver hyperplaneGenericPoint) 2 hR ⊤
                (smoothClosedSupportCoclassSection planeOver hyperplaneOver hyperplaneOverι 1 2)) =
            supportRelativeCohomologySectionSupportOpenTransport
              (TopCat.of (ComplexPoint planeOver))
              (cycleComponentSupport planeOver hyperplaneGenericPoint) 2 hR hU.symm
              (smoothClosedSupportCoclassSection planeOver hyperplaneOver hyperplaneOverι 1 2) := by
        intro U hU
        cases hU
        rw [show (homOfLE (show (⊤ : Opens (ComplexPoint planeOver)) ≤ ⊤ from le_top)).op =
          𝟙 _ by subsingleton]
        simp
        rfl
      rw [hrestrict _ hyperplaneCycleComponent_smoothSupportAmbientOpen_eq_top]
      have hcross := hyperplaneSmoothClosedSupportCoclassSection_eq_cycleComponentSmoothLocus
      rw [hcross]
      rw [supportRelativeCohomologySectionSupportOpenTransport_comp_support]
      exact (hyperplaneCycleComponentSmoothSupportCoclassSection_eq_direct).symm

/-- The explicit normalized supported-injective class is therefore the canonical class of the
coordinate-hyperplane cycle component. -/
theorem hyperplaneSmoothClosedSupportInjectiveClass_eq_cycleComponent
    [IsProjective planeOver.hom]
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    hyperplaneSmoothClosedSupportInjectiveClassInCycleComponent =
        cycleComponentSupportedInjectiveClass planeOver hyperplaneGenericPoint
          (d := 2) hyperplaneGenericPoint_coheight := by
  apply (hyperplaneSmoothClosedSupportInjectiveClass_eq_cycleComponent_iff_normalization).mpr
  simpa only [Nat.reduceMul] using
    hyperplaneSmoothClosedSupportInjectiveClass_normalization

end AlgebraicGeometry.ProjectivePlane
