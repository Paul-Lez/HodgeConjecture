/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicGeometry.ChernRelativeChartFormulaAssembly
public import Other.AlgebraicGeometry.ChernRelativeClosedSupportSection
public import Other.AlgebraicGeometry.ChernRelativeClosedSupportUnit
public import Other.AlgebraicGeometry.ChernRelativeSupportGenericUnit
public import Other.AlgebraicGeometry.Cohomology.OriginalChernRawWindingSection
public import Other.AlgebraicGeometry.Cohomology.SupportSheafConeRestrictionNaturality
public import Other.AlgebraicGeometry.Cohomology.OriginalChernAmbientRawSection
public import Other.AlgebraicGeometry.Cohomology.OriginalChernRawWindingNormalizationOnOpen
public import Other.AlgebraicGeometry.CartierOriginalChernFrame
public import Other.AlgebraicGeometry.ChernOriginalRawAmbientTransport

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open AlgebraicTopology.Singular
open AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance finalAssemblyTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology
attribute [local instance] isNoetherian_of_isProjective

variable {X}

set_option maxHeartbeats 1000000 in
/-- Every representing Cartier datum has cycle class equal to the rational first Chern class. -/
theorem hasDivisorClassOfCartierData : HasDivisorClassOfCartierData X := by
  apply hasDivisorClassOfCartierData_of_localModel X
    (hasComponentSupportDecomposition_unconditional X)
  apply hasChernLocalModel_of_original_local_section
  intro c E L hL e hc g hg hrep ℓ hℓ hcompat cmp x hxS hx q G hG
  let ch := G.toChart
  have hxdiv : c.divisor x ≠ 0 :=
    (mem_cycleComponents_iff X c.divisor x).mp hxS
  let ℓU := E.frameLift q ch.carrier hG
    (ch.regularFrame g E e)
    (ch.holomorphicGenerates_regularFrame g E e hg)
  have hframe := ChernWindingChart.compatible_frame_restriction
    (g := g) (E := E) (e := e) (hg := hg) ch ℓ hcompat q hG hxdiv
  have hℓU : E.projection.hom.app (op ch.carrier) ℓU =
      (𝓒(↧(ComplexPoint X); ℤ)).obj.map
        (homOfLE (le_top : ch.carrier ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection := by
    simpa only [ℓU, integerOneRestrict] using hframe.1
  let Ω : Opens (TopCat.of (ComplexPoint X)) :=
    (analyticClosedSupport X (badLocus c)).compl
  let hEq : ch.carrier ⊓ Ω = ch.punctured :=
    ch.inf_goodComplement_eq_punctured hxdiv
  let w : (holomorphicUnitSheaf X (dim X.left)).obj.obj
      (op (ch.carrier ⊓ Ω)) :=
    (holomorphicUnitSheaf X (dim X.left)).obj.map (homOfLE hEq.le).op
      ch.cartierUnit
  have hw : E.inclusion.hom.app (op (ch.carrier ⊓ Ω)) w =
      E.middle.obj.map (homOfLE inf_le_right).op ℓ -
        E.middle.obj.map (homOfLE inf_le_left).op ℓU := by
    simpa only [w, Ω, hEq] using hframe.2
  have hclosed := restrict_original_relativeChernClass_closed_support_section
    (X := X) (S := analyticClosedSupport X (badLocus c)) E ℓ hℓ cmp
    ch.carrier ℓU hℓU w hw
  dsimp only at hclosed
  let V := (Opens.isOpenEmbedding (X := TopCat.of (ComplexPoint X)) ch.carrier).functor.obj
    (⊤ : Opens ((Opens.toTopCat (TopCat.of (ComplexPoint X))).obj ch.carrier))
  let S₀ : Closeds (ComplexPoint X) :=
    ⟨((analyticClosedSupport X (badLocus c)).compl : Set (ComplexPoint X))ᶜ,
      (analyticClosedSupport X (badLocus c)).compl.isOpen.isClosed_compl⟩
  let hS : S₀ = analyticClosedSupport X (badLocus c) := by
    apply Closeds.ext
    change (((analyticClosedSupport X (badLocus c)).compl : Set (ComplexPoint X))ᶜ) = _
    exact compl_compl _
  change supportedInjectiveLocalSection V 2
      (relativeChernSupportedClassOnClosed
        (analyticClosedSupport X (badLocus c)) E ℓ hℓ cmp) = _ at hclosed
  let Y := TopCat.of (ComplexPoint X)
  let Z : Set (ComplexPoint X) :=
    ((analyticClosedSupport X (badLocus c)).compl : Set (ComplexPoint X))ᶜ
  let hZ : IsClosed Z := (analyticClosedSupport X (badLocus c)).compl.isOpen.isClosed_compl
  let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
  let K₀' := (TopCat.Sheaf.supportRestrictionComplexShortComplex Y
      ⟨Zᶜ, hZ.isOpen_compl⟩ (ambientRationalInjectiveComplex X)).X₁
  let m := supportSheafToAmbientInjectiveCone X Z hZ
  let : IsIso ((HomologicalComplex.homologyMap m 1).hom.app (op V)) := by
    have : IsIso (HomologicalComplex.homologyMap m 1) :=
      (quasiIsoAt_iff_isIso_homologyMap m 1).mp inferInstance
    infer_instance
  let F := (Opens.isOpenEmbedding (X := TopCat.of (ComplexPoint X)) ch.carrier).sheafPullback
    AddCommGrpCat
  let gU := originalLocalBoundaryMap X (dim X.left)
    (analyticClosedSupport X (badLocus c)).compl ch.carrier w
  let a₀ := (TopCat.Sheaf.globalSectionsComplexInt Y
      (TopCat.Sheaf.integerConstantSingleComplex Y)).homologyπ 0
      (TopCat.Sheaf.integerCocycleGlobalSection Y
        (TopCat.Sheaf.integerConstantSingleComplex Y) 0
        (CochainComplex.HomComplex.Cocycle.ofHom
          (𝟙 (TopCat.Sheaf.integerConstantSingleComplex Y))))
  let bV :=
    ((((TopCat.Sheaf.integerConstantSingleComplex Y).sc 0).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap gU 0 ≫
          (((C⟦(1 : ℤ)⟧).sc 0).mapHomologyIso F).hom).hom.app
      (op (⊤ : Opens (TopCat.of ch.carrier)))
      (((TopCat.Sheaf.integerConstantSingleComplex Y).homology 0).obj.map
        (homOfLE (le_top : V ≤ ⊤)).op
        (TopCat.Sheaf.sectionCohomologyToSheafSection Y
          (TopCat.Sheaf.integerConstantSingleComplex Y) 0 ⊤ a₀))
  let tV := (TopCat.Sheaf.sectionCohomologySheafShiftMap Y C
    1 0 1 (by omega)).hom.app (op V) bV
  let yV := -(TopCat.Sheaf.sectionCohomologySheafShiftMap Y K₀'
    1 1 2 (by omega)).hom.app (op V)
      (inv ((HomologicalComplex.homologyMap m 1).hom.app (op V)) tV)
  change supportedInjectiveLocalSection V 2
      (relativeChernSupportedClassOnClosed
        (analyticClosedSupport X (badLocus c)) E ℓ hℓ cmp) =
    (HomologicalComplex.homologyMap
      (supportedInjectiveComplexMap X hS.le) 2).hom.app (op V) yV at hclosed
  have hUV : ch.carrier ≤ V := by
    dsimp only [V]
    change ch.carrier ≤
      (Opens.isOpenEmbedding (X := TopCat.of (ComplexPoint X)) ch.carrier).functor.obj ⊤
    rw [Opens.isOpenEmbedding_obj_top]
  let K := complexSupportInjectiveComplex X (analyticClosedSupport X (badLocus c))
  let K₀ := complexSupportInjectiveComplex X S₀
  let rK := (HomologicalComplex.homology K 2).obj.map (homOfLE hUV).op
  let rK₀ := (HomologicalComplex.homology K₀ 2).obj.map (homOfLE hUV).op
  have hsec := ConcreteCategory.congr_hom
    (TopCat.Sheaf.sectionCohomologyToSheafSection_restriction
      (TopCat.of (ComplexPoint X)) K 2 (homOfLE hUV))
      (HomologicalComplex.homologyMap
        (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) (.up ℤ) K
          (homOfLE (le_top : V ≤ ⊤))) 2
        (relativeChernSupportedClassOnClosed
          (analyticClosedSupport X (badLocus c)) E ℓ hℓ cmp))
  have hrestr := congrArg (ConcreteCategory.hom rK) hclosed
  have hcomp :
      HomologicalComplex.homologyMap
          (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) (.up ℤ) K
            (homOfLE (le_top : V ≤ ⊤))) 2 ≫
        HomologicalComplex.homologyMap
          (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) (.up ℤ) K
            (homOfLE hUV)) 2 =
      HomologicalComplex.homologyMap
          (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) (.up ℤ) K
            (homOfLE (le_top : ch.carrier ≤ ⊤))) 2 := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun f => HomologicalComplex.homologyMap f (2 : ℤ))
      (TopCat.Sheaf.sectionComplexRestriction_comp' (TopCat.of (ComplexPoint X))
        (.up ℤ) K (homOfLE (le_top : V ≤ ⊤)) (homOfLE hUV)
        (homOfLE (le_top : ch.carrier ≤ ⊤))).symm
  have hnat :=
    ((HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hS.le) 2).hom).naturality
      (homOfLE hUV).op
  have hnat' (y : (K₀.homology 2).presheaf.obj (op V)) :
      (ConcreteCategory.hom rK)
          ((ConcreteCategory.hom
            ((HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hS.le) 2).hom.app
              (op V))) y) =
        (ConcreteCategory.hom
          ((HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hS.le) 2).hom.app
            (op ch.carrier)))
          ((ConcreteCategory.hom rK₀) y) := by
    have hh := ConcreteCategory.congr_hom hnat y
    exact hh.symm
  have hleft :
      (ConcreteCategory.hom rK)
          (supportedInjectiveLocalSection V 2
            (relativeChernSupportedClassOnClosed
              (analyticClosedSupport X (badLocus c)) E ℓ hℓ cmp)) =
        supportedInjectiveLocalSection ch.carrier 2
            (relativeChernSupportedClassOnClosed
              (analyticClosedSupport X (badLocus c)) E ℓ hℓ cmp) := by
    dsimp only [supportedInjectiveLocalSection]
    have hs := hsec.symm
    simp only [ConcreteCategory.comp_apply] at hs ⊢
    rw [← hcomp]
    exact hs
  have hunit := G.normalizedCartierUnit_supportMap hxdiv
  dsimp only at hunit
  rw [hunit]
  have hdouble := normalizedWindingUnit_supportMap_doubleComplement
    (X := X) (d := dim X.left)
      (analyticClosedSupport X (badLocus c)) ch.carrier w
  dsimp only at hdouble
  rw [← hdouble]
  have hclosedU := hleft.symm.trans hrestr
  rw [hclosedU]
  have houter := hnat' yV
  have hshift := supportSheafSection_shift_restrict_naturality
    (X := X) (Z := Z) (hZ := hZ) (U := ch.carrier) (V := V)
    (j := homOfLE hUV) tV
  dsimp only at hshift
  refine houter.trans ?_
  have hmshift := congrArg
    (fun a => (ConcreteCategory.hom
      ((HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hS.le) 2).hom.app
        (op ch.carrier))) a) hshift
  change (ConcreteCategory.hom
      ((HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hS.le) 2).hom.app
        (op ch.carrier))) ((ConcreteCategory.hom rK₀) yV) = _ at hmshift
  rw [hmshift]
  let zraw := ChernWinding.openRawRationalWindingClass Y (ch.carrier ⊓ Ω)
    (holomorphicUnitFunction X (dim X.left) (ch.carrier ⊓ Ω) (-w))
    (holomorphicUnitFunction_ne_zero X (dim X.left) (ch.carrier ⊓ Ω) (-w))
  let rC := (C.homology 1).obj.map (homOfLE hUV).op
  have hrawV := originalLocalBoundaryMap_ambient_section_eq_raw_winding
    (X := X) (d := dim X.left) (Ω := Ω) (U := ch.carrier) w
  dsimp only at hrawV
  let Γ := (TopCat.Sheaf.supportEvaluation Y ch.carrier).mapHomologicalComplex (.up ℤ)
  let rDirect :=
    openRawToSupportedSingularOutside Y Ω ch.carrier ≫
      Γ.map (naturalSingularOutsideResolutionComparisonOnOpen X Ω) ≫
      Γ.map (CochainComplex.mappingCone.inr
        (ambientRationalInjectiveRestriction X Z hZ))
  let aΩ := HomologicalComplex.homologyMap
    (Γ.map (naturalSingularOutsideResolutionComparisonOnOpen X Ω)) 1
    (HomologicalComplex.homologyMap
      (openRawToSupportedSingularOutside Y Ω ch.carrier) 1 zraw)
  have hcompRaw :
      (HomologicalComplex.homologyMap rDirect 1).hom zraw =
        ((HomologicalComplex.homologyMap
          (Γ.map (CochainComplex.mappingCone.inr
            (ambientRationalInjectiveRestriction X Z hZ))) 1).hom aΩ) := by
    dsimp only [rDirect, aΩ]
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
    rfl
  have hdirect := originalLocalRawToAmbientCone_direct_section_eq_restricted_original
    X Ω ch.carrier zraw
  dsimp only at hdirect
  have htop :
      (TopCat.Sheaf.openRestrictionTopSectionsIso Y ch.carrier).hom.app
          (C.homology 1) = (C.homology 1).obj.map (homOfLE hUV).op := by
    rfl
  have hdirect' :
      TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 ch.carrier
          ((HomologicalComplex.homologyMap rDirect 1).hom zraw) =
        (ConcreteCategory.hom rC)
          (TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 V
            ((HomologicalComplex.homologyMap
              (originalLocalRawToAmbientCone X Ω ch.carrier) 1).hom zraw)) := by
    have hdirect' := hdirect
    simp only [ConcreteCategory.comp_apply] at hdirect'
    rw [htop] at hdirect'
    exact hdirect'
  have hrawBridge :
      (ConcreteCategory.hom rC) tV =
        TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 ch.carrier
          ((HomologicalComplex.homologyMap
            (Γ.map (CochainComplex.mappingCone.inr
              (ambientRationalInjectiveRestriction X Z hZ))) 1).hom aΩ) := by
    exact (congrArg (ConcreteCategory.hom rC) hrawV).trans
      (hdirect'.symm.trans
        (congrArg (fun x => TopCat.Sheaf.sectionCohomologyToSheafSection Y C 1 ch.carrier x)
          hcompRaw))
  have hnorm := originalRawAmbientSection_shift_inv_eq_winding_on_open
    (X := X) (d := dim X.left) (Ω := Ω) (V := ch.carrier) w
  dsimp only at hnorm
  rw [← hrawBridge] at hnorm
  exact congrArg (fun a => (ConcreteCategory.hom
    ((HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hS.le) 2).hom.app
      (op ch.carrier))) a) hnorm

end AlgebraicGeometry.ComplexPoint
