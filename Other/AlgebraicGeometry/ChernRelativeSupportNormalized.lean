/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation
public import Other.AlgebraicGeometry.ChernRelativeSupportSingular
public import Other.AlgebraicTopology.SupportedSingularSupportMap
public import Other.AlgebraicGeometry.Cohomology.SupportSheafNormalization
public import Other.AlgebraicGeometry.ChernWindingSupportedBoundary
public import Other.AlgebraicGeometry.RationalSupportBoundaryRelative

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open HomologicalComplex
open AlgebraicTopology.Singular
open AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
local instance supportNormalizedTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology
attribute [local instance] isNoetherian_of_isProjective
variable {X}

lemma supportedSingularInjectiveSection_supportMap
    {S T : Closeds (ComplexPoint X)} (hST : S ≤ T)
    (W : Opens (TopCat.of (ComplexPoint X))) (n : ℤ)
    (a : ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex
      ℤᵘᵖ).obj (supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X)) S.compl))).homology n) :
    (HomologicalComplex.homologyMap
        (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex
          ℤᵘᵖ).map (supportedInjectiveComplexMap X hST)) n)
        ((complexSupportedSingularInjectiveHomologyIso X S.compl W n).hom a) =
      (complexSupportedSingularInjectiveHomologyIso X T.compl W n).hom
      ((HomologicalComplex.homologyMap
        (TopCat.Sheaf.supportRestrictionSectionsSupportMap
          (show T.compl ≤ S.compl from fun _ hs ht => hs (hST ht))
          (rationalSingularCochainComplex (TopCat.of (ComplexPoint X))) W).τ₁ n) a) := by
  let Y := TopCat.of (ComplexPoint X)
  let eS := complexSupportedSingularInjectiveHomologyIso X S.compl W n
  let eT := complexSupportedSingularInjectiveHomologyIso X T.compl W n
  let F := (TopCat.Sheaf.supportEvaluation Y W).mapHomologicalComplex ℤᵘᵖ
  have hcompF :
      F.map (supportedSingularComplexMap X hST) ≫
          F.map (complexSupportedSingularToAmbientInjective X T.compl) =
        F.map (complexSupportedSingularToAmbientInjective X S.compl) ≫
          F.map (supportedInjectiveComplexMap X hST) := by
    have hmapS := F.map_comp (complexSupportedSingularToAmbientInjective X S.compl)
      (supportedInjectiveComplexMap X hST)
    have hc := congrArg F.map (supportedSingularComplexMap_comp X hST)
    rw [F.map_comp (supportedSingularComplexMap X hST)
      (complexSupportedSingularToAmbientInjective X T.compl)] at hc
    exact hc.trans hmapS
  have hcompH :
      HomologicalComplex.homologyMap (F.map (supportedSingularComplexMap X hST)) n ≫
          HomologicalComplex.homologyMap
            (F.map (complexSupportedSingularToAmbientInjective X T.compl)) n =
        HomologicalComplex.homologyMap
            (F.map (complexSupportedSingularToAmbientInjective X S.compl)) n ≫
          HomologicalComplex.homologyMap (F.map (supportedInjectiveComplexMap X hST)) n := by
    have hmapH := HomologicalComplex.homologyMap_comp
      (F.map (complexSupportedSingularToAmbientInjective X S.compl))
      (F.map (supportedInjectiveComplexMap X hST)) n
    have hmapL := HomologicalComplex.homologyMap_comp
      (F.map (supportedSingularComplexMap X hST))
      (F.map (complexSupportedSingularToAmbientInjective X T.compl)) n
    have hc := congrArg (fun f => HomologicalComplex.homologyMap f n) hcompF
    exact hmapL.symm.trans (hc.trans hmapH)
  have hc := ConcreteCategory.congr_hom hcompH a
  change
    (ConcreteCategory.hom
      (HomologicalComplex.homologyMap
        (((TopCat.Sheaf.supportEvaluation Y W).mapHomologicalComplex ℤᵘᵖ).map
          (supportedInjectiveComplexMap X hST)) n))
      ((ConcreteCategory.hom
        (complexSupportedSingularInjectiveHomologyIso X S.compl W n).hom) a) =
    (ConcreteCategory.hom
      (complexSupportedSingularInjectiveHomologyIso X T.compl W n).hom)
      ((ConcreteCategory.hom
        (HomologicalComplex.homologyMap
          (((TopCat.Sheaf.supportEvaluation Y W).mapHomologicalComplex ℤᵘᵖ).map
            (supportedSingularComplexMap X hST)) n)) a)
  exact hc.symm

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
local instance supportBoundaryNormalizedTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology
attribute [local instance] isNoetherian_of_isProjective
local instance supportBoundaryNormalizedParacompact : ∀ V : Opens (ComplexPoint X), ParacompactSpace V :=
  openParacompactSpace X
variable {X}

set_option maxHeartbeats 1000000 in
lemma normalizedSupportSection_supportMap_of_boundary
    {S T : Closeds (ComplexPoint X)} (hST : S ≤ T)
    (W : Opens (TopCat.of (ComplexPoint X)))
    (aS : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
      (TopCat.of (ComplexPoint X)) S.compl W
      (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).X₁.homology (2 : ℤ))
    (aT : (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
      (TopCat.of (ComplexPoint X)) T.compl W
      (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).X₁.homology (2 : ℤ))
    (hmap : (ConcreteCategory.hom
      (HomologicalComplex.homologyMap
        (TopCat.Sheaf.supportRestrictionSectionsSupportMap
          (show T.compl ≤ S.compl from fun _ hs ht => hs (hST ht))
          (rationalSingularCochainComplex (TopCat.of (ComplexPoint X))) W).τ₁ (2 : ℤ))) aS = aT)
    (wS : RelativeCohomology ℚ
      (ChernWinding.supportPair (W : Set (ComplexPoint X)) (S : Set (ComplexPoint X))) 2)
    (wT : RelativeCohomology ℚ
      (ChernWinding.supportPair (W : Set (ComplexPoint X)) (T : Set (ComplexPoint X))) 2)
    (hwindS : supportedRationalSingularSectionCohomologyEquivSupportComplement
      (TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X)) S.isClosed W 2 aS = wS)
    (hwindT : supportedRationalSingularSectionCohomologyEquivSupportComplement
      (TopCat.of (ComplexPoint X)) (T : Set (ComplexPoint X)) T.isClosed W 2 aT = wT) :
    (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hST) (2 : ℤ)).hom.app
        (op W)
        ((complexSupportInjectiveCohomologySheafIsoRelative X S 2).inv.hom.app (op W)
          ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X)) 2).app
            (op W) wS)) =
      (complexSupportInjectiveCohomologySheafIsoRelative X T 2).inv.hom.app (op W)
        ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) (T : Set (ComplexPoint X)) 2).app
          (op W) wT) := by
  let Y := TopCat.of (ComplexPoint X)
  let eS := complexSupportedSingularInjectiveHomologyIso X S.compl W (2 : ℤ)
  let eT := complexSupportedSingularInjectiveHomologyIso X T.compl W (2 : ℤ)
  let NS := complexSupportInjectiveCohomologySheafIsoRelative X S 2
  let NT := complexSupportInjectiveCohomologySheafIsoRelative X T 2
  let sS := TopCat.Sheaf.sectionCohomologyToSheafSection Y
    (complexSupportInjectiveComplex X S) (2 : ℤ) W (eS.hom aS)
  let sT := TopCat.Sheaf.sectionCohomologyToSheafSection Y
    (complexSupportInjectiveComplex X T) (2 : ℤ) W (eT.hom aT)
  have hNS : NS.hom.hom.app (op W) sS =
      (supportRelativeCohomologyToSheaf Y (S : Set (ComplexPoint X)) 2).app (op W) wS := by
    change (complexSupportInjectiveCohomologySheafIsoRelative X S 2).hom.hom.app (op W)
        (TopCat.Sheaf.sectionCohomologyToSheafSection Y
          (complexSupportInjectiveComplex X S) (2 : ℤ) W (eS.hom aS)) = _
    exact (complexSupportInjectiveCohomologySheafIsoRelative_section_apply X S 2 W
      (eS.hom aS)).trans <|
      (congrArg (fun z => (supportRelativeCohomologyToSheaf Y
        (S : Set (ComplexPoint X)) 2).app (op W) z)
        (complexSupportInjectiveSectionCohomologyEquiv_supported_singular X S W 2 aS)).trans
      (congrArg (fun z => (supportRelativeCohomologyToSheaf Y
        (S : Set (ComplexPoint X)) 2).app (op W) z) hwindS)
  have hNT : NT.hom.hom.app (op W) sT =
      (supportRelativeCohomologyToSheaf Y (T : Set (ComplexPoint X)) 2).app (op W) wT := by
    change (complexSupportInjectiveCohomologySheafIsoRelative X T 2).hom.hom.app (op W)
        (TopCat.Sheaf.sectionCohomologyToSheafSection Y
          (complexSupportInjectiveComplex X T) (2 : ℤ) W (eT.hom aT)) = _
    exact (complexSupportInjectiveCohomologySheafIsoRelative_section_apply X T 2 W
      (eT.hom aT)).trans <|
      (congrArg (fun z => (supportRelativeCohomologyToSheaf Y
        (T : Set (ComplexPoint X)) 2).app (op W) z)
        (complexSupportInjectiveSectionCohomologyEquiv_supported_singular X T W 2 aT)).trans
      (congrArg (fun z => (supportRelativeCohomologyToSheaf Y
        (T : Set (ComplexPoint X)) 2).app (op W) z) hwindT)
  have hsectionS : NS.inv.hom.app (op W)
      ((supportRelativeCohomologyToSheaf Y (S : Set (ComplexPoint X)) 2).app (op W) wS) = sS := by
    calc
      _ = NS.inv.hom.app (op W) (NS.hom.hom.app (op W) sS) := congrArg _ hNS.symm
      _ = sS := by
        have hi := congrArg (fun f => f.hom.app (op W)) NS.hom_inv_id
        exact ConcreteCategory.congr_hom hi sS
  have hsectionT : NT.inv.hom.app (op W)
      ((supportRelativeCohomologyToSheaf Y (T : Set (ComplexPoint X)) 2).app (op W) wT) = sT := by
    calc
      _ = NT.inv.hom.app (op W) (NT.hom.hom.app (op W) sT) := congrArg _ hNT.symm
      _ = sT := by
        have hi := congrArg (fun f => f.hom.app (op W)) NT.hom_inv_id
        exact ConcreteCategory.congr_hom hi sT
  rw [hsectionS]
  have hnat := TopCat.Sheaf.sectionCohomologyToSheafSection_naturality Y
    (supportedInjectiveComplexMap X hST) (2 : ℤ) W
  have he := supportedSingularInjectiveSection_supportMap (X := X) hST W 2 aS
  have hlocal :
      (ConcreteCategory.hom
        (HomologicalComplex.homologyMap
          (((TopCat.Sheaf.supportEvaluation Y W).mapHomologicalComplex ℤᵘᵖ).map
            (supportedInjectiveComplexMap X hST)) (2 : ℤ))) (eS.hom aS) = eT.hom aT := by
    rw [he, hmap]
  have hnat' :
      (ConcreteCategory.hom
        (TopCat.Sheaf.sectionCohomologyToSheafSection Y
          (complexSupportInjectiveComplex X T) (2 : ℤ) W))
        ((ConcreteCategory.hom
          (HomologicalComplex.homologyMap
            (((TopCat.Sheaf.supportEvaluation Y W).mapHomologicalComplex ℤᵘᵖ).map
              (supportedInjectiveComplexMap X hST)) (2 : ℤ))) (eS.hom aS)) =
      (ConcreteCategory.hom
        ((HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hST) (2 : ℤ)).hom.app
          (op W)))
        ((ConcreteCategory.hom
          (TopCat.Sheaf.sectionCohomologyToSheafSection Y
            (complexSupportInjectiveComplex X S) (2 : ℤ) W)) (eS.hom aS)) :=
    ConcreteCategory.congr_hom hnat (eS.hom aS)
  rw [hlocal] at hnat'
  change sT =
      (ConcreteCategory.hom
        ((HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hST) (2 : ℤ)).hom.app
          (op W))) sS at hnat'
  rw [hsectionT]
  exact hnat'.symm

set_option maxHeartbeats 1000000 in
/-- The fixed winding normalization commutes with enlargement of closed supports. -/
lemma normalizedWinding_supportMap_of_raw
    {S T : Closeds (ComplexPoint X)} (hST : S ≤ T)
    (W : Opens (TopCat.of (ComplexPoint X)))
    (gS : C(ChernWinding.puncturedSpace (W : Set (ComplexPoint X)) (S : Set (ComplexPoint X)), ℂ))
    (hgS : ∀ y, gS y ≠ 0)
    (hS : ChernWinding.HasRationalWindingPeriod
      (W : Set (ComplexPoint X)) (S : Set (ComplexPoint X)) gS hgS)
    (gT : C(ChernWinding.puncturedSpace (W : Set (ComplexPoint X)) (T : Set (ComplexPoint X)), ℂ))
    (hgT : ∀ y, gT y ≠ 0)
    (hT : ChernWinding.HasRationalWindingPeriod
      (W : Set (ComplexPoint X)) (T : Set (ComplexPoint X)) gT hgT)
    (hcomp : gS.comp (ChernWinding.topMap (TopPair.Hom.snd
      (neighborhoodSupportSupportInclusionPairMap X hST W))) = gT) :
    (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hST) (2 : ℤ)).hom.app
        (op W)
        ((complexSupportInjectiveCohomologySheafIsoRelative X S 2).inv.hom.app (op W)
          ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
            (S : Set (ComplexPoint X)) 2).app
            (op W) (ChernWinding.windingRelativeClass (W : Set (ComplexPoint X))
              (S : Set (ComplexPoint X)) hS))) =
      (complexSupportInjectiveCohomologySheafIsoRelative X T 2).inv.hom.app (op W)
        ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
          (T : Set (ComplexPoint X)) 2).app
          (op W) (ChernWinding.windingRelativeClass (W : Set (ComplexPoint X))
            (T : Set (ComplexPoint X)) hT)) := by
  let US : Opens (TopCat.of (ComplexPoint X)) := ⟨(S : Set (ComplexPoint X))ᶜ,
    S.isClosed.isOpen_compl⟩
  let UT : Opens (TopCat.of (ComplexPoint X)) := ⟨(T : Set (ComplexPoint X))ᶜ,
    T.isClosed.isOpen_compl⟩
  let qS := openIntersectionPairIsoSupportComplement
    (TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X)) S.isClosed W
  let qT := openIntersectionPairIsoSupportComplement
    (TopCat.of (ComplexPoint X)) (T : Set (ComplexPoint X)) T.isClosed W
  let zS := ChernWinding.openRawRationalWindingClass (TopCat.of (ComplexPoint X))
    (W ⊓ US) (gS.comp (ChernWinding.topMap qS.hom.left))
      (fun y => hgS (qS.hom.left y))
  let zT := ChernWinding.openRawRationalWindingClass (TopCat.of (ComplexPoint X))
    (W ⊓ UT) (gT.comp (ChernWinding.topMap qT.hom.left))
      (fun y => hgT (qT.hom.left y))
  let aS := (supportedSingularKernelHomologyIsoCone (TopCat.of (ComplexPoint X))
      US W 2).inv
    (HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
          (TopCat.of (ComplexPoint X)) US W
          (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).g) 1
      (HomologicalComplex.homologyMap
        (openRawToSupportedSingularOutside (TopCat.of (ComplexPoint X)) US W) 1 zS))
  let aT := (supportedSingularKernelHomologyIsoCone (TopCat.of (ComplexPoint X))
      UT W 2).inv
    (HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr
        (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
          (TopCat.of (ComplexPoint X)) UT W
          (rationalSingularCochainComplex (TopCat.of (ComplexPoint X)))).g) 1
      (HomologicalComplex.homologyMap
        (openRawToSupportedSingularOutside (TopCat.of (ComplexPoint X)) UT W) 1 zT))
  have hwindS : supportedRationalSingularSectionCohomologyEquivSupportComplement
      (TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X)) S.isClosed W 2 aS =
      ChernWinding.windingRelativeClass (W : Set (ComplexPoint X)) (S : Set (ComplexPoint X)) hS := by
    simpa only [aS, US, zS, qS] using
      (ChernWinding.supportedSingularSectionCohomologyEquivSupportComplement_winding_boundary
        (TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X)) S.isClosed W gS hgS hS)
  have hwindT : supportedRationalSingularSectionCohomologyEquivSupportComplement
      (TopCat.of (ComplexPoint X)) (T : Set (ComplexPoint X)) T.isClosed W 2 aT =
      ChernWinding.windingRelativeClass (W : Set (ComplexPoint X)) (T : Set (ComplexPoint X)) hT := by
    simpa only [aT, UT, zT, qT] using
      (ChernWinding.supportedSingularSectionCohomologyEquivSupportComplement_winding_boundary
        (TopCat.of (ComplexPoint X)) (T : Set (ComplexPoint X)) T.isClosed W gT hgT hT)
  have hraw : HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap
        (openRawSingularRestriction ℚ (TopCat.of (ComplexPoint X))
          (homOfLE (inf_le_inf_left W (show T.compl ≤ S.compl from
            fun _ hs ht => hs (hST ht))))) ComplexShape.embeddingUpNat) 1 zS = zT := by
    dsimp only [zS, zT]
    let qS := openIntersectionPairIsoSupportComplement
      (TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X)) S.isClosed W
    let qT := openIntersectionPairIsoSupportComplement
      (TopCat.of (ComplexPoint X)) (T : Set (ComplexPoint X)) T.isClosed W
    let i := homOfLE (inf_le_inf_left W (show T.compl ≤ S.compl from
      fun _ hs ht => hs (hST ht)))
    let fS := gS.comp (ChernWinding.topMap qS.hom.left)
    let fT := gT.comp (ChernWinding.topMap qT.hom.left)
    let hfS : ∀ y, fS y ≠ 0 := fun y => hgS (qS.hom.left y)
    have hfun : fS.comp (ChernWinding.topMap
        ((Opens.toTopCat (TopCat.of (ComplexPoint X))).map i)) = fT := by
      ext y
      change gS (qS.hom.left ((Opens.toTopCat (TopCat.of (ComplexPoint X))).map i y)) =
        gT (qT.hom.left y)
      rw [← hcomp]
      rfl
    refine (ChernWinding.openRawRationalWindingClass_restriction
      (TopCat.of (ComplexPoint X)) i fS hfS).trans ?_
    congr 1
  have hmap := supportedSingularKernelBoundary_supportMap_of_raw
    (TopCat.of (ComplexPoint X))
    (U := US) (V := UT)
    (show UT ≤ US from fun _ hs ht => hs (hST ht)) W zS zT hraw
  exact normalizedSupportSection_supportMap_of_boundary (X := X) hST W aS aT hmap
    _ _ hwindS hwindT

end AlgebraicGeometry.ComplexPoint
