import Other.AlgebraicGeometry.ProjectivePlaneRelativeCechCompatibility
import Other.AlgebraicTopology.RelativeCechConeRawCochain
import Other.AlgebraicTopology.RelativeCochainConeForgetComparison
import Other.AlgebraicTopology.UniversalMemberCechContraction
import Other.AlgebraicGeometry.ProjectivePlaneHyperplane
import Other.AlgebraicGeometry.ExplicitProjectivePlaneHyperplaneClass
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology
open scoped AlgebraicGeometry
@[expose] noncomputable section
namespace AlgebraicGeometry.ProjectivePlane.CoordinateCharts
open AlgebraicTopology.RelativeCechConeComparison
open AlgebraicTopology.Singular
open AlgebraicGeometry.ComplexPoint
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "analyticPlaneTop" => (TopCat.of (ComplexPoint analyticPlane))
set_option maxHeartbeats 600000

/-! The concrete prepend map for the first pulled-back cover.  This is the geometric map used by
the eventual extra-degeneracy contraction; its construction is fully explicit, including the
support-enlarging intersection isomorphism. -/

noncomputable def firstChartUniversalMemberPrependMap (n : ℕ) :
    (rationalOpenCoverIntersectionChainModels firstChartHyperplanePair.fst
        firstChartPulledbackProjectiveCover).cechObject TupleClass.all n ⟶
      (rationalOpenCoverIntersectionChainModels firstChartHyperplanePair.fst
        firstChartPulledbackProjectiveCover).cechObject TupleClass.all (n + 1) :=
  universalMemberPrependMap firstChartHyperplanePair.fst
    firstChartPulledbackProjectiveCover 1 n
    firstChartPulledbackProjectiveCover_one_eq_univ

/-! The singleton sections also give a comparison in the reverse direction, from the
pulled-back relative Čech cone to the literal relative singular-cochain cone.  Unlike an
abstract inverse obtained from `asIso`, this map is concrete enough to evaluate the global
coordinate cocycle on the distinguished chart member. -/

noncomputable def firstChartRelativeCechSectionComparison :
    RelativeCechConeComparison.relativeDualCone
        firstChartPulledbackComplementToAmbientCechMap ⟶
      CochainComplex.mappingCone
        (relativeCochainRestrictionInt ℚ firstChartHyperplanePair) := by
  let s := ((chainPairFunctor ℚ).obj firstChartHyperplanePair).hom
  change RelativeCechConeComparison.relativeDualCone
      firstChartPulledbackComplementToAmbientCechMap ⟶
    RelativeCechConeComparison.relativeDualCone s
  exact RelativeCechConeComparison.comparison
    s firstChartPulledbackComplementToAmbientCechMap
    firstChartComplementCechUniversalMemberSection
    firstChartAmbientCechUniversalMemberSection
    (by
      change SSet.chainComplexMap
          (TopCat.toSSet.map firstChartHyperplanePair.hom)
          (ModuleCat.of ℚ ℚ) ≫
            firstChartAmbientCechUniversalMemberSection =
        firstChartComplementCechUniversalMemberSection ≫
          firstChartPulledbackComplementToAmbientCechMap
      exact firstChartUniversalMemberSection_square)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The ordinary Čech comparison followed by the distinguished-singleton comparison is
strictly the identity.  Thus the latter is the actual inverse on cohomology, without a chosen
inverse or an extra comparison hypothesis. -/
lemma firstChartRelativeCechComparison_comp_sectionComparison :
    firstChartRelativeCechComparison ≫
        firstChartRelativeCechSectionComparison = 𝟙 _ := by
  cases firstChartPulledbackComplementCover_eq_family
  let c := rationalPullbackCoverNormalizedTotalMap
    firstChartHyperplanePair.hom firstChartPulledbackProjectiveCover
  let s := SSet.chainComplexMap (TopCat.toSSet.map firstChartHyperplanePair.hom)
    (ModuleCat.of ℚ ℚ)
  let q₀ := rationalOpenCoverNormalizedCechTotalToSingular
    firstChartHyperplanePair.snd
      (pullbackCover firstChartHyperplanePair.hom firstChartPulledbackProjectiveCover)
  let q₁ := rationalOpenCoverNormalizedCechTotalToSingular
    firstChartHyperplanePair.fst firstChartPulledbackProjectiveCover
  let u₀ := firstChartComplementCechUniversalMemberSection
  let u₁ := firstChartAmbientCechUniversalMemberSection
  have hc : c ≫ q₁ = q₀ ≫ s :=
    rationalPullbackCoverNormalizedCechToSingular_naturality
      firstChartHyperplanePair.hom firstChartPulledbackProjectiveCover
  have hs : s ≫ u₁ = u₀ ≫ c := by
    change SSet.chainComplexMap
        (TopCat.toSSet.map firstChartHyperplanePair.hom)
        (ModuleCat.of ℚ ℚ) ≫
          firstChartAmbientCechUniversalMemberSection =
      firstChartComplementCechUniversalMemberSection ≫
        firstChartPulledbackComplementToAmbientCechMap
    exact firstChartUniversalMemberSection_square
  change RelativeCechConeComparison.comparison c s q₀ q₁ hc ≫
      RelativeCechConeComparison.comparison s c u₀ u₁ hs = 𝟙 _
  unfold RelativeCechConeComparison.comparison
  rw [← CochainComplex.mappingCone.map_comp]
  have huq₁ : u₁ ≫ q₁ = 𝟙 _ := by
    dsimp [u₁, q₁, firstChartAmbientCechUniversalMemberSection]
    exact rationalOpenCoverUniversalMemberSection_comp_toSingular
      firstChartHyperplanePair.fst firstChartPulledbackProjectiveCover 1
      firstChartPulledbackProjectiveCover_one_eq_univ
  have h₁ : RelativeCechConeComparison.dualMapInt q₁ ≫
      RelativeCechConeComparison.dualMapInt u₁ = 𝟙 _ := by
    rw [← RelativeCechConeComparison.dualMapInt_comp, huq₁,
      RelativeCechConeComparison.dualMapInt_id]
  have huq₀ : u₀ ≫ q₀ = 𝟙 _ := by
    dsimp [u₀, q₀, firstChartComplementCechUniversalMemberSection]
    exact rationalOpenCoverUniversalMemberSection_comp_toSingular
      firstChartHyperplanePair.snd
      (pullbackCover firstChartHyperplanePair.hom firstChartPulledbackProjectiveCover) 1
      firstChartPulledbackComplementCover_one_eq_univ
  have h₀ : RelativeCechConeComparison.dualMapInt q₀ ≫
      RelativeCechConeComparison.dualMapInt u₀ = 𝟙 _ := by
    rw [← RelativeCechConeComparison.dualMapInt_comp, huq₀,
      RelativeCechConeComparison.dualMapInt_id]
  simpa [RelativeCechConeComparison.relativeDualCone, s, h₁, h₀] using
    (CochainComplex.mappingCone.map_id
      (RelativeCechConeComparison.dualMapInt s))

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the global ambient degree-two functional on the distinguished singleton
section of the first pulled-back chart gives zero.  This is the ambient component of the
raw local comparison. -/
lemma firstChartAmbientSection_globalFunctional_zero :
    firstChartAmbientCechUniversalMemberSection.f 2 ≫
      firstChartAmbientCechMap.f 2 ≫
        coordinateProjectiveCoverTotalFunctional = 0 := by
  unfold firstChartAmbientCechUniversalMemberSection
    rationalOpenCoverUniversalMemberSection
    firstChartAmbientCechMap rationalPullbackCoverNormalizedTotalMap
  simp only [Category.assoc]
  rw [HomologicalComplex₂.ιTotal_map_assoc]
  have hz :
      ((rationalOpenCoverIntersectionChainModels coordinateHyperplaneSupportPair.fst
        projectiveCover).cechComplex TupleClass.strictMono).ιTotal
          (ComplexShape.down ℕ) 0 2 2 (by norm_num) ≫
        coordinateProjectiveCoverTotalFunctional = 0 :=
    coordinateProjectiveCoverTotalFunctional_zero
  rw [hz, comp_zero, comp_zero]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- On the distinguished complement member, the inverse of the universal-member
identification followed by the global singleton-to-chart map is the identity of the punctured
first chart. -/
lemma firstChartComplementUniversalMemberToLocal_eq_id :
    (openCoverUniversalMemberIso firstChartHyperplanePair.snd
        (pullbackCover
          (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
          coordinateHyperplaneComplementCover) 1
        firstChartPulledbackComplementCover_one_eq_univ).inv ≫
      pullbackOpenCoverIntersectionMap
        (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
        coordinateHyperplaneComplementCover
        (tupleSupport (singletonStrictCechTuple (1 : Fin 3)).1) ≫
      complementCoverSingletonOneToFirstChartComplement = 𝟙 _ := by
  apply (cancel_epi (openCoverUniversalMemberIso firstChartHyperplanePair.snd
    (pullbackCover (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
      coordinateHyperplaneComplementCover) 1
    firstChartPulledbackComplementCover_one_eq_univ).hom).mp
  simp only [Iso.hom_inv_id_assoc, Category.comp_id]
  rw [openCoverUniversalMemberIso_hom]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply (ComplexPoint.openHomeomorph analyticPlane (chartOpen 1)).injective
  apply Subtype.ext
  change Point.map (openInclusion analyticPlane (chartOpen 1))
      (complementCoverSingletonToChart 1
        (pullbackOpenCoverIntersectionMap
          (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
          coordinateHyperplaneComplementCover
          (tupleSupport (singletonStrictCechTuple (1 : Fin 3)).1) z)) =
    Point.map (openInclusion analyticPlane (chartOpen 1)) z.1.1
  rw [complementCoverSingletonToChart_map_openInclusion]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The distinguished complement-member chain section, followed by the global singleton map,
evaluates the global singleton winding functional as the literal first normal winding cochain. -/
lemma firstChartComplementSection_singletonWinding :
    (rationalOpenCoverUniversalMemberChainMap firstChartHyperplanePair.snd
        (pullbackCover
          (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
          coordinateHyperplaneComplementCover) 1
        firstChartPulledbackComplementCover_one_eq_univ).f 1 ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map (pullbackOpenCoverIntersectionMap
          (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
          coordinateHyperplaneComplementCover
          (tupleSupport (singletonStrictCechTuple (1 : Fin 3)).1)))
        (ModuleCat.of ℚ ℚ)).f 1 ≫
      complementCoverSingletonOneWindingTuple =
    ChernWinding.windingIntegerCochain
      firstNormalOnComplement firstNormalOnComplement_ne_zero := by
  dsimp [complementCoverSingletonOneWindingTuple]
  unfold complementCoverSingletonOneWinding
    rationalOpenCoverUniversalMemberChainMap
  change
    (SSet.chainComplexMap
        (TopCat.toSSet.map (openCoverUniversalMemberIso firstChartHyperplanePair.snd
          (pullbackCover
            (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
            coordinateHyperplaneComplementCover) 1
          firstChartPulledbackComplementCover_one_eq_univ).inv)
        (ModuleCat.of ℚ ℚ)).f 1 ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map (pullbackOpenCoverIntersectionMap
          (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
          coordinateHyperplaneComplementCover
          (tupleSupport (singletonStrictCechTuple (1 : Fin 3)).1)))
        (ModuleCat.of ℚ ℚ)).f 1 ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map complementCoverSingletonOneToFirstChartComplement)
        (ModuleCat.of ℚ ℚ)).f 1 ≫
      ChernWinding.windingIntegerCochain
        firstNormalOnComplement firstNormalOnComplement_ne_zero = _
  have hchain := congrArg
    (fun h ↦ SSet.chainComplexMap (TopCat.toSSet.map h) (ModuleCat.of ℚ ℚ))
    firstChartComplementUniversalMemberToLocal_eq_id
  unfold SSet.chainComplexMap at hchain
  simp only [Functor.map_comp] at hchain
  rw [TopCat.toSSet.map_id] at hchain
  have hchain' := hchain.trans
    (((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map_id _)
  have hf := congrArg (fun k ↦ k.f 1 ≫
    ChernWinding.windingIntegerCochain
      firstNormalOnComplement firstNormalOnComplement_ne_zero) hchain'
  simpa only [SSet.chainComplexMap, HomologicalComplex.comp_f, Category.assoc,
    HomologicalComplex.id_f, Category.id_comp] using hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The full global complement functional, pulled back along the distinguished first-chart
singleton section, is the literal first normal winding cochain.  In particular, the pair
correction part disappears because the section lands in outer Cech degree zero. -/
lemma firstChartComplementSection_globalFunctional :
    firstChartComplementCechUniversalMemberSection.f 1 ≫
      firstChartComplementCechMap.f 1 ≫
        coordinateHyperplaneComplementFullFunctional =
      ChernWinding.windingIntegerCochain
        firstNormalOnComplement firstNormalOnComplement_ne_zero := by
  unfold firstChartComplementCechUniversalMemberSection
    rationalOpenCoverUniversalMemberSection
    firstChartComplementCechMap rationalPullbackCoverNormalizedTotalMap
  simp only [Category.assoc]
  rw [HomologicalComplex₂.ιTotal_map_assoc]
  rw [coordinateHyperplaneComplementFullFunctional_singleton]
  unfold rationalOpenCoverUniversalMemberColumnMap
    rationalPullbackCoverNormalizedBicomplexMap
  simp only [HomologicalComplex.comp_f, Category.assoc]
  let M := fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
    (rationalOpenCoverIntersectionChainModels firstChartHyperplanePair.snd
      firstChartPulledbackComplementCover).model (tupleSupport b.1)
  let N := fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
    coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1)
  let eta : ∀ b, M b ⟶ N b := fun b ↦
    SSet.chainComplexMap
      (TopCat.toSSet.map (pullbackOpenCoverIntersectionMap
        (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
        coordinateHyperplaneComplementCover (tupleSupport b.1)))
      (ModuleCat.of ℚ ℚ)
  have hsigma :
      Sigma.ι M (singletonStrictCechTuple (1 : Fin 3)) ≫
          SupportChainModels.Hom.cechObjectMap
            (rationalPullbackCoverLocalMap
              (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
              coordinateHyperplaneComplementCover)
            TupleClass.strictMono 0 =
        eta (singletonStrictCechTuple (1 : Fin 3)) ≫
          Sigma.ι N (singletonStrictCechTuple (1 : Fin 3)) := by
    unfold SupportChainModels.Hom.cechObjectMap
    exact Limits.Sigma.ι_map _ _
  have hsigma1 := congrArg (fun k ↦ k.f 1) hsigma
  simp only [HomologicalComplex.comp_f] at hsigma1
  have hsigma1_assoc := congrArg
    (fun k ↦ k ≫ coordinateHyperplaneComplementSingletonDegreeDesc) hsigma1
  simp only [Category.assoc] at hsigma1_assoc
  let u := rationalOpenCoverUniversalMemberChainMap firstChartHyperplanePair.snd
    firstChartPulledbackComplementCover 1
    firstChartPulledbackComplementCover_one_eq_univ
  change u.f 1 ≫
      (Sigma.ι M (singletonStrictCechTuple (1 : Fin 3))).f 1 ≫
        ((rationalPullbackCoverLocalMap
          (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
          coordinateHyperplaneComplementCover).cechObjectMap
          TupleClass.strictMono 0).f 1 ≫
          coordinateHyperplaneComplementSingletonDegreeDesc = _
  have htotal := congrArg (fun k ↦ u.f 1 ≫ k) hsigma1_assoc
  rw [htotal]
  have hdesc :
      (Sigma.ι N (singletonStrictCechTuple (1 : Fin 3))).f 1 ≫
          coordinateHyperplaneComplementSingletonDegreeDesc =
        complementCoverSingletonOneWindingTuple := by
    let a1 : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} :=
      ⟨![1], by decide⟩
    have ha : singletonStrictCechTuple (1 : Fin 3) = a1 := by
      apply Subtype.ext
      rfl
    cases ha
    dsimp [a1, N]
    exact coordinateHyperplaneComplementSingletonDegreeDesc_firstChart
  rw [hdesc]
  exact firstChartComplementSection_singletonWinding

abbrev A := coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex
abbrev B := coordinateHyperplaneComplementCechTotal.linearDualCochainComplex

noncomputable def coordinateProjectiveCoverCochainIntHom :
    ModuleCat.of ℚ ℚ ⟶
      (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat).X (ComplexShape.embeddingUpNat.f 2) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ coordinateProjectiveCoverCochain) ≫
    (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extendXIso
      ComplexShape.embeddingUpNat (i := 2) rfl).inv

lemma coordinateProjectiveCoverCochainIntHom_closed :
    coordinateProjectiveCoverCochainIntHom ≫
      (A.extend ComplexShape.embeddingUpNat).d
        (ComplexShape.embeddingUpNat.f 2) (ComplexShape.embeddingUpNat.f 3) = 0 := by
  dsimp [coordinateProjectiveCoverCochainIntHom]
  rw [Category.assoc]
  have h := HomologicalComplex.extend.comp_d_eq_zero_iff A ComplexShape.embeddingUpNat
    (j := 2) (k := 3) (j' := (2 : ℤ)) (k' := (3 : ℤ)) rfl (by norm_num) (by norm_num)
    (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ coordinateProjectiveCoverCochain))
  apply h.mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change A.d 2 3 (x • coordinateProjectiveCoverCochain) = 0
  rw [map_smul, coordinateProjectiveCoverCochain_closed, smul_zero]

noncomputable def coordinateHyperplaneComplementFullPartIntHom :
    ModuleCat.of ℚ ℚ ⟶
      (coordinateHyperplaneComplementCechTotal.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat).X (ComplexShape.embeddingUpNat.f 1) :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ coordinateHyperplaneComplementFullPart) ≫
    (coordinateHyperplaneComplementCechTotal.linearDualCochainComplex.extendXIso
      ComplexShape.embeddingUpNat (i := 1) rfl).inv

set_option backward.isDefEq.respectTransparency false in
/-- On the extended integer-indexed dual complexes, the complement component of the global
relative Cech cocycle evaluates under the distinguished first-chart section to the literal
extended winding cochain. -/
lemma firstChartComplementSection_globalCochainInt :
    (RelativeCechConeComparison.dualMapInt
        firstChartComplementCechUniversalMemberSection).f
        (ComplexShape.embeddingUpNat.f 1)
      ((RelativeCechConeComparison.dualMapInt firstChartComplementCechMap).f
        (ComplexShape.embeddingUpNat.f 1)
        (coordinateHyperplaneComplementFullPartIntHom.hom 1)) =
      ChernWinding.extendedWindingIntegerCochainElement
        (X := firstChartHyperplanePair)
        firstNormalOnComplement firstNormalOnComplement_ne_zero := by
  dsimp [RelativeCechConeComparison.dualMapInt]
  rw [HomologicalComplex.extendMap_f _ _ (i := 1)
    (i' := ComplexShape.embeddingUpNat.f 1) rfl]
  rw [HomologicalComplex.extendMap_f _ _ (i := 1)
    (i' := ComplexShape.embeddingUpNat.f 1) rfl]
  dsimp [coordinateHyperplaneComplementFullPartIntHom,
    ChernWinding.extendedWindingIntegerCochainElement]
  simp only [LinearMap.toSpanSingleton_apply, one_smul]
  simp
  apply congrArg _
  apply LinearMap.ext
  intro x
  dsimp [coordinateHyperplaneComplementFullPart,
    ChernWinding.pairWindingIntegerCochainHom,
    ChernWinding.pairWindingIntegerCochainElement]
  simp only [LinearMap.toSpanSingleton_apply, one_smul]
  change coordinateHyperplaneComplementFullFunctional.hom
      (firstChartComplementCechMap.f 1
        (firstChartComplementCechUniversalMemberSection.f 1 x)) =
    (ChernWinding.windingIntegerCochain
      firstNormalOnComplement firstNormalOnComplement_ne_zero).hom x
  have hx := LinearMap.congr_fun
    (congrArg (fun f ↦ f.hom) firstChartComplementSection_globalFunctional) x
  simpa only [LinearMap.coe_comp, Function.comp_apply,
    HomologicalComplex.comp_f, ModuleCat.hom_comp,
    ConcreteCategory.comp_apply] using hx

set_option backward.isDefEq.respectTransparency false in
/-- The extended dual of the first-chart distinguished singleton section annihilates the
ambient component of the global coordinate cocycle. -/
lemma firstChartAmbientSection_globalCochainInt_zero :
    (RelativeCechConeComparison.dualMapInt
        firstChartAmbientCechUniversalMemberSection).f
        (ComplexShape.embeddingUpNat.f 2)
      ((RelativeCechConeComparison.dualMapInt firstChartAmbientCechMap).f
        (ComplexShape.embeddingUpNat.f 2)
        (coordinateProjectiveCoverCochainIntHom.hom 1)) = 0 := by
  dsimp [RelativeCechConeComparison.dualMapInt]
  rw [HomologicalComplex.extendMap_f _ _ (i := 2)
    (i' := ComplexShape.embeddingUpNat.f 2) rfl]
  rw [HomologicalComplex.extendMap_f _ _ (i := 2)
    (i' := ComplexShape.embeddingUpNat.f 2) rfl]
  dsimp [coordinateProjectiveCoverCochainIntHom]
  simp only [LinearMap.toSpanSingleton_apply, one_smul]
  simp
  have hz : (firstChartAmbientCechUniversalMemberSection.f 2 ≫
      firstChartAmbientCechMap.f 2 ≫
        coordinateProjectiveCoverTotalFunctional).hom = 0 :=
    congrArg (fun f ↦ f.hom) firstChartAmbientSection_globalFunctional_zero
  have hzdual :
      (firstChartAmbientCechUniversalMemberSection.f 2).hom.dualMap
        ((firstChartAmbientCechMap.f 2).hom.dualMap
          coordinateProjectiveCoverCochain) = 0 := by
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hz x
    simpa only [coordinateProjectiveCoverCochain,
      LinearMap.dualMap_apply', LinearMap.coe_comp,
      Function.comp_apply, HomologicalComplex.comp_f, ModuleCat.hom_comp,
      LinearMap.zero_apply] using hx
  rw [hzdual, map_zero]

/-- The degree of the complement component agrees with the predecessor of the ambient
degree.  We keep this equality visible because the object field of a mapping cone is not
stable under unfolding arithmetic-definitional equalities. -/
lemma embeddingUpNat_one_eq_two_sub_one :
    ComplexShape.embeddingUpNat.f 1 = ComplexShape.embeddingUpNat.f 2 - 1 := by
  norm_num [ComplexShape.embeddingUpNat_f]

/-- The global relative Čech cochain with its lower-degree component explicitly transported
to the predecessor degree required by the mapping cone. -/
noncomputable def coordinateHyperplaneRelativeCechRawElement :
    (CochainComplex.mappingCone
      (RelativeCechConeComparison.dualMapInt
        coordinateHyperplaneComplementToAmbientCechMap)).X
          (ComplexShape.embeddingUpNat.f 2 - 1) :=
  RelativeCechConeComparison.coneCochainOfEq
    (RelativeCechConeComparison.dualMapInt coordinateHyperplaneComplementToAmbientCechMap)
    (ComplexShape.embeddingUpNat.f 2) (ComplexShape.embeddingUpNat.f 1)
    embeddingUpNat_one_eq_two_sub_one
    (coordinateProjectiveCoverCochainIntHom.hom 1)
    (coordinateHyperplaneComplementFullPartIntHom.hom 1)

/-- The same raw element in the literal degree used by cycles and homology. -/
noncomputable def coordinateHyperplaneRelativeCechRawElementDegreeOne :
    (CochainComplex.mappingCone
      (RelativeCechConeComparison.dualMapInt
        coordinateHyperplaneComplementToAmbientCechMap)).X
          (ComplexShape.embeddingUpNat.f 1) :=
  ((CochainComplex.mappingCone
    (RelativeCechConeComparison.dualMapInt
      coordinateHyperplaneComplementToAmbientCechMap)).XIsoOfEq
        embeddingUpNat_one_eq_two_sub_one).inv.hom
    coordinateHyperplaneRelativeCechRawElement

/-- The linear span map of the explicit raw cone element.  It is recorded as a structure
rather than through `LinearMap.toSpanSingleton` so its value is stable when the mapping-cone
object is unfolded. -/
noncomputable def coordinateHyperplaneRelativeCechCochainLinearMap :
    ℚ →ₗ[ℚ]
      (CochainComplex.mappingCone
        (RelativeCechConeComparison.dualMapInt
          coordinateHyperplaneComplementToAmbientCechMap)).X
            (ComplexShape.embeddingUpNat.f 1) where
  toFun x := x • coordinateHyperplaneRelativeCechRawElementDegreeOne
  map_add' x y := by rw [add_smul]
  map_smul' x y := by simp [smul_smul]

@[simp]
lemma coordinateHyperplaneRelativeCechCochainLinearMap_apply (x : ℚ) :
    coordinateHyperplaneRelativeCechCochainLinearMap x =
      x • coordinateHyperplaneRelativeCechRawElementDegreeOne := rfl

noncomputable def coordinateHyperplaneRelativeCechCochainHom :
    ModuleCat.of ℚ ℚ ⟶
      (CochainComplex.mappingCone
        (RelativeCechConeComparison.dualMapInt coordinateHyperplaneComplementToAmbientCechMap)).X
          (ComplexShape.embeddingUpNat.f 1) :=
  ModuleCat.ofHom coordinateHyperplaneRelativeCechCochainLinearMap

@[simp]
lemma coordinateHyperplaneRelativeCechCochainHom_apply (x : ℚ) :
    coordinateHyperplaneRelativeCechCochainHom.hom x =
      x • coordinateHyperplaneRelativeCechRawElementDegreeOne := rfl

lemma coordinateHyperplaneRelativeCechCochainHom_closed :
    coordinateHyperplaneRelativeCechCochainHom ≫
      (CochainComplex.mappingCone
        (RelativeCechConeComparison.dualMapInt coordinateHyperplaneComplementToAmbientCechMap)).d
        (ComplexShape.embeddingUpNat.f 2 - 1) (ComplexShape.embeddingUpNat.f 2) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (CochainComplex.mappingCone
    (RelativeCechConeComparison.dualMapInt coordinateHyperplaneComplementToAmbientCechMap)).d
      (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2)
    (x • coordinateHyperplaneRelativeCechRawElementDegreeOne) = 0
  simp only [map_smul]
  have hcRaw : (CochainComplex.mappingCone
      (RelativeCechConeComparison.dualMapInt coordinateHyperplaneComplementToAmbientCechMap)).d
      (ComplexShape.embeddingUpNat.f 2 - 1) (ComplexShape.embeddingUpNat.f 2)
      coordinateHyperplaneRelativeCechRawElement = 0 := by
    unfold coordinateHyperplaneRelativeCechRawElement
      RelativeCechConeComparison.coneCochainOfEq
    apply RelativeCechConeComparison.coneCochain_closed
    · exact congrArg (fun f => f.hom 1) coordinateProjectiveCoverCochainIntHom_closed
    · change (RelativeCechConeComparison.dualMapInt
          coordinateHyperplaneComplementToAmbientCechMap).f
            (ComplexShape.embeddingUpNat.f 2)
          (coordinateProjectiveCoverCochainIntHom.hom 1) = -
        (coordinateHyperplaneComplementCechTotal.linearDualCochainComplex.extend
          ComplexShape.embeddingUpNat).d (ComplexShape.embeddingUpNat.f 2 - 1)
            (ComplexShape.embeddingUpNat.f 2)
          (((coordinateHyperplaneComplementCechTotal.linearDualCochainComplex.extend
            ComplexShape.embeddingUpNat).XIsoOfEq
              embeddingUpNat_one_eq_two_sub_one).hom.hom
            (coordinateHyperplaneComplementFullPartIntHom.hom 1))
      have hd := ConcreteCategory.congr_hom
        ((coordinateHyperplaneComplementCechTotal.linearDualCochainComplex.extend
          ComplexShape.embeddingUpNat).XIsoOfEq_hom_comp_d
            embeddingUpNat_one_eq_two_sub_one (ComplexShape.embeddingUpNat.f 2))
        (coordinateHyperplaneComplementFullPartIntHom.hom 1)
      change _ = -((((coordinateHyperplaneComplementCechTotal.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat).XIsoOfEq
          embeddingUpNat_one_eq_two_sub_one).hom ≫
        (coordinateHyperplaneComplementCechTotal.linearDualCochainComplex.extend
          ComplexShape.embeddingUpNat).d (ComplexShape.embeddingUpNat.f 2 - 1)
            (ComplexShape.embeddingUpNat.f 2)).hom
          (coordinateHyperplaneComplementFullPartIntHom.hom 1))
      rw [hd]
      change (HomologicalComplex.extendMap
        (HomologicalComplex.linearDualMap coordinateHyperplaneComplementToAmbientCechMap)
        ComplexShape.embeddingUpNat).f (ComplexShape.embeddingUpNat.f 2)
          (coordinateProjectiveCoverCochainIntHom.hom 1) = _
      rw [HomologicalComplex.extendMap_f _ _ (i := 2)
        (i' := ComplexShape.embeddingUpNat.f 2) rfl]
      rw [coordinateHyperplaneComplementCechTotal.linearDualCochainComplex.extend_d_eq
        ComplexShape.embeddingUpNat (i := 1) (j := 2) rfl rfl]
      dsimp [coordinateProjectiveCoverCochainIntHom,
        coordinateHyperplaneComplementFullPartIntHom]
      simp only [LinearMap.toSpanSingleton_apply, one_smul]
      simp only [LinearMap.dualMap_apply']
      have ha0 :
          (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extendXIso
            ComplexShape.embeddingUpNat (i := 2) rfl).hom.hom
            ((coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extendXIso
              ComplexShape.embeddingUpNat (i := 2) rfl).inv.hom
              coordinateProjectiveCoverCochain) =
          coordinateProjectiveCoverCochain := by
        simp
      have hb0 :
          (coordinateHyperplaneComplementCechTotal.linearDualCochainComplex.extendXIso
            ComplexShape.embeddingUpNat (i := 1) rfl).hom.hom
            ((coordinateHyperplaneComplementCechTotal.linearDualCochainComplex.extendXIso
              ComplexShape.embeddingUpNat (i := 1) rfl).inv.hom
              coordinateHyperplaneComplementFullPart) =
          coordinateHyperplaneComplementFullPart := by
        simp
      rw [ha0, hb0]
      change (coordinateHyperplaneComplementCechTotal.linearDualCochainComplex.extendXIso
          ComplexShape.embeddingUpNat (i := 2) rfl).inv.hom
          ((coordinateHyperplaneComplementToAmbientCechMap.f 2 ≫
            coordinateProjectiveCoverTotalFunctional).hom) = -
        (coordinateHyperplaneComplementCechTotal.linearDualCochainComplex.extendXIso
          ComplexShape.embeddingUpNat (i := 2) rfl).inv.hom
          ((coordinateHyperplaneComplementCechTotal.d 2 1 ≫
            coordinateHyperplaneComplementFullFunctional).hom)
      have h := congrArg (fun f => f.hom)
        coordinateHyperplaneComplementRelativeTotalCompatibility
      change (coordinateHyperplaneComplementToAmbientCechMap.f 2 ≫
          coordinateProjectiveCoverTotalFunctional).hom +
          (coordinateHyperplaneComplementCechTotal.d 2 1 ≫
            coordinateHyperplaneComplementFullFunctional).hom = 0 at h
      simpa only [map_neg] using congrArg (fun z =>
        (coordinateHyperplaneComplementCechTotal.linearDualCochainComplex.extendXIso
          ComplexShape.embeddingUpNat (i := 2) rfl).inv.hom z)
        (add_eq_zero_iff_eq_neg.mp h)
  have hc : (CochainComplex.mappingCone
      (RelativeCechConeComparison.dualMapInt coordinateHyperplaneComplementToAmbientCechMap)).d
      (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2)
      coordinateHyperplaneRelativeCechRawElementDegreeOne = 0 := by
    unfold coordinateHyperplaneRelativeCechRawElementDegreeOne
    change ((((CochainComplex.mappingCone
      (RelativeCechConeComparison.dualMapInt
        coordinateHyperplaneComplementToAmbientCechMap)).XIsoOfEq
          embeddingUpNat_one_eq_two_sub_one).inv ≫
      (CochainComplex.mappingCone
        (RelativeCechConeComparison.dualMapInt
          coordinateHyperplaneComplementToAmbientCechMap)).d
            (ComplexShape.embeddingUpNat.f 1)
            (ComplexShape.embeddingUpNat.f 2)).hom
      coordinateHyperplaneRelativeCechRawElement) = 0
    rw [(CochainComplex.mappingCone
      (RelativeCechConeComparison.dualMapInt
        coordinateHyperplaneComplementToAmbientCechMap)).XIsoOfEq_inv_comp_d
          embeddingUpNat_one_eq_two_sub_one (ComplexShape.embeddingUpNat.f 2)]
    exact hcRaw
  rw [hc, smul_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Pulling the explicit global relative Čech cochain to the first chart and then evaluating
on its distinguished cover member gives the literal local winding cocycle.  The final
`XIsoOfEq.inv` is the explicit transport from the predecessor degree `f 2 - 1` to `f 1`;
no reduction of the internal `mappingCone.X` arithmetic is used. -/
theorem firstChartSectionComparison_global_raw_transport :
    let localCone := CochainComplex.mappingCone
      (relativeCochainRestrictionInt ℚ firstChartHyperplanePair)
    ((localCone.XIsoOfEq embeddingUpNat_one_eq_two_sub_one).inv.hom
      (firstChartRelativeCechSectionComparison.f
        (ComplexShape.embeddingUpNat.f 2 - 1)
        (coordinateHyperplaneToFirstChartRelativeCechConeMap.f
          (ComplexShape.embeddingUpNat.f 2 - 1)
          coordinateHyperplaneRelativeCechRawElement))) =
      ChernWinding.rawRelativeWindingCochain
        (X := firstChartHyperplanePair)
        firstNormalOnComplement firstNormalOnComplement_ne_zero := by
  dsimp only
  rw [show coordinateHyperplaneToFirstChartRelativeCechConeMap.f
      (ComplexShape.embeddingUpNat.f 2 - 1)
      coordinateHyperplaneRelativeCechRawElement =
    RelativeCechConeComparison.coneCochainOfEq
      (RelativeCechConeComparison.dualMapInt
        firstChartPulledbackComplementToAmbientCechMap)
      (ComplexShape.embeddingUpNat.f 2) (ComplexShape.embeddingUpNat.f 1)
      embeddingUpNat_one_eq_two_sub_one
      ((RelativeCechConeComparison.dualMapInt firstChartAmbientCechMap).f
        (ComplexShape.embeddingUpNat.f 2)
        (coordinateProjectiveCoverCochainIntHom.hom 1))
      ((RelativeCechConeComparison.dualMapInt firstChartComplementCechMap).f
        (ComplexShape.embeddingUpNat.f 1)
        (coordinateHyperplaneComplementFullPartIntHom.hom 1)) from
    RelativeCechConeComparison.comparison_coneCochainOfEq
      firstChartPulledbackComplementToAmbientCechMap
      coordinateHyperplaneComplementToAmbientCechMap
      firstChartComplementCechMap firstChartAmbientCechMap
      firstChartRelativeCechSquare
      (ComplexShape.embeddingUpNat.f 2) (ComplexShape.embeddingUpNat.f 1)
      embeddingUpNat_one_eq_two_sub_one
      (coordinateProjectiveCoverCochainIntHom.hom 1)
      (coordinateHyperplaneComplementFullPartIntHom.hom 1)]
  rw [show firstChartRelativeCechSectionComparison.f
      (ComplexShape.embeddingUpNat.f 2 - 1) _ =
    RelativeCechConeComparison.coneCochainOfEq
      (relativeCochainRestrictionInt ℚ firstChartHyperplanePair)
      (ComplexShape.embeddingUpNat.f 2) (ComplexShape.embeddingUpNat.f 1)
      embeddingUpNat_one_eq_two_sub_one
      ((RelativeCechConeComparison.dualMapInt
        firstChartAmbientCechUniversalMemberSection).f
          (ComplexShape.embeddingUpNat.f 2)
        ((RelativeCechConeComparison.dualMapInt firstChartAmbientCechMap).f
          (ComplexShape.embeddingUpNat.f 2)
          (coordinateProjectiveCoverCochainIntHom.hom 1)))
      ((RelativeCechConeComparison.dualMapInt
        firstChartComplementCechUniversalMemberSection).f
          (ComplexShape.embeddingUpNat.f 1)
        ((RelativeCechConeComparison.dualMapInt firstChartComplementCechMap).f
          (ComplexShape.embeddingUpNat.f 1)
          (coordinateHyperplaneComplementFullPartIntHom.hom 1))) from
    RelativeCechConeComparison.comparison_coneCochainOfEq
      ((chainPairFunctor ℚ).obj firstChartHyperplanePair).hom
      firstChartPulledbackComplementToAmbientCechMap
      firstChartComplementCechUniversalMemberSection
      firstChartAmbientCechUniversalMemberSection
      (by
        change SSet.chainComplexMap
            (TopCat.toSSet.map firstChartHyperplanePair.hom)
            (ModuleCat.of ℚ ℚ) ≫
              firstChartAmbientCechUniversalMemberSection =
          firstChartComplementCechUniversalMemberSection ≫
            firstChartPulledbackComplementToAmbientCechMap
        exact firstChartUniversalMemberSection_square)
      (ComplexShape.embeddingUpNat.f 2) (ComplexShape.embeddingUpNat.f 1)
      embeddingUpNat_one_eq_two_sub_one
      ((RelativeCechConeComparison.dualMapInt firstChartAmbientCechMap).f
        (ComplexShape.embeddingUpNat.f 2)
        (coordinateProjectiveCoverCochainIntHom.hom 1))
      ((RelativeCechConeComparison.dualMapInt firstChartComplementCechMap).f
        (ComplexShape.embeddingUpNat.f 1)
        (coordinateHyperplaneComplementFullPartIntHom.hom 1))]
  rw [firstChartAmbientSection_globalCochainInt_zero,
    firstChartComplementSection_globalCochainInt]
  rw [RelativeCechConeComparison.XIsoOfEq_inv_coneCochainOfEq_zero]
  exact
    (ChernWinding.rawRelativeWindingCochain_eq_inr_extendedWindingIntegerCochainElement
      (X := firstChartHyperplanePair)
      firstNormalOnComplement firstNormalOnComplement_ne_zero).symm

noncomputable def coordinateHyperplaneRelativeCechCocycle :
    ModuleCat.of ℚ ℚ ⟶
      coordinateHyperplaneRelativeCechCone.cycles (ComplexShape.embeddingUpNat.f 1) :=
  coordinateHyperplaneRelativeCechCone.liftCycles
    coordinateHyperplaneRelativeCechCochainHom
    (ComplexShape.embeddingUpNat.f 2) (by norm_num)
    coordinateHyperplaneRelativeCechCochainHom_closed

noncomputable def coordinateHyperplaneRelativeCechHomologyClass :
    coordinateHyperplaneRelativeCechCone.homology (ComplexShape.embeddingUpNat.f 1) :=
  (coordinateHyperplaneRelativeCechCocycle ≫
    coordinateHyperplaneRelativeCechCone.homologyπ (ComplexShape.embeddingUpNat.f 1)).hom 1

noncomputable def coordinateHyperplaneRelativeSingularConeClass :
    (CochainComplex.mappingCone
      (relativeCochainRestrictionInt ℚ coordinateHyperplaneSupportPair)).homology
        (ComplexShape.embeddingUpNat.f 1) := by
  let e := asIso (HomologicalComplex.homologyMap
    coordinateHyperplaneRelativeCechComparison (ComplexShape.embeddingUpNat.f 1))
  exact e.inv.hom coordinateHyperplaneRelativeCechHomologyClass

lemma coordinateHyperplaneRelativeCechComparison_homologyMap_class :
    HomologicalComplex.homologyMap coordinateHyperplaneRelativeCechComparison
        (ComplexShape.embeddingUpNat.f 1)
        coordinateHyperplaneRelativeSingularConeClass =
      coordinateHyperplaneRelativeCechHomologyClass := by
  dsimp [coordinateHyperplaneRelativeSingularConeClass]
  simp

noncomputable def coordinateProjectiveCoverCochainIntCocycle :
    ModuleCat.of ℚ ℚ ⟶
      (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat).cycles (ComplexShape.embeddingUpNat.f 2) :=
  (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extend
    ComplexShape.embeddingUpNat).liftCycles
    coordinateProjectiveCoverCochainIntHom (ComplexShape.embeddingUpNat.f 3)
    (by norm_num) coordinateProjectiveCoverCochainIntHom_closed

noncomputable def coordinateProjectiveCoverCochainIntClass :
    (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extend
      ComplexShape.embeddingUpNat).homology (2 : ℤ) :=
  (coordinateProjectiveCoverCochainIntCocycle ≫
    (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extend
      ComplexShape.embeddingUpNat).homologyπ (2 : ℤ)).hom 1

lemma coordinateProjectiveCoverCochainIntClass_toNat :
    ((coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extendHomologyIso
      ComplexShape.embeddingUpNat (j := 2) (j' := (2 : ℤ)) (by norm_num)).hom.hom
      coordinateProjectiveCoverCochainIntClass) =
      coordinateProjectiveCoverCochainClass := by
  have hπ := ConcreteCategory.congr_hom
    ((coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex).homologyπ_extendHomologyIso_hom
      ComplexShape.embeddingUpNat
      (j := 2) (j' := (2 : ℤ)) (by norm_num))
    (coordinateProjectiveCoverCochainIntCocycle.hom 1)
  change ((coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extendHomologyIso
    ComplexShape.embeddingUpNat (j := 2) (j' := (2 : ℤ)) (by norm_num)).hom.hom
      (((coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat).homologyπ (2 : ℤ)).hom
        ((coordinateProjectiveCoverCochainIntCocycle).hom 1))) =
    (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.homologyπ 2).hom
      (coordinateProjectiveCoverCocycle.hom 1)
  change (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extendHomologyIso
      ComplexShape.embeddingUpNat (j := 2) (j' := (2 : ℤ)) (by norm_num)).hom.hom
      (((coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat).homologyπ (2 : ℤ)).hom
        ((coordinateProjectiveCoverCochainIntCocycle).hom 1)) =
    (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.homologyπ 2).hom
      ((coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extendCyclesIso
        ComplexShape.embeddingUpNat (j := 2) rfl).hom.hom
        ((coordinateProjectiveCoverCochainIntCocycle).hom 1)) at hπ
  rw [hπ]
  apply congrArg (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.homologyπ 2).hom
  apply (ModuleCat.mono_iff_injective
    (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.iCycles 2)).mp inferInstance
  have hi := ConcreteCategory.congr_hom
    (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extendCyclesIso_hom_iCycles
      ComplexShape.embeddingUpNat (j := 2) (j' := (2 : ℤ)) rfl)
    ((coordinateProjectiveCoverCochainIntCocycle).hom 1)
  change (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.iCycles 2).hom
      ((coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extendCyclesIso
        ComplexShape.embeddingUpNat (j := 2) (j' := (2 : ℤ)) rfl).hom.hom
        ((coordinateProjectiveCoverCochainIntCocycle).hom 1)) =
    (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extendXIso
        ComplexShape.embeddingUpNat (i := 2) (i' := (2 : ℤ)) (by norm_num)).hom.hom
      (((coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat).iCycles (2 : ℤ)).hom
        ((coordinateProjectiveCoverCochainIntCocycle).hom 1)) at hi
  change (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.iCycles 2).hom
      ((coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extendCyclesIso
        ComplexShape.embeddingUpNat (j := 2) (j' := (2 : ℤ)) rfl).hom.hom
        ((coordinateProjectiveCoverCochainIntCocycle).hom 1)) =
    (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.iCycles 2).hom
      ((coordinateProjectiveCoverCocycle).hom 1)
  rw [hi]
  change (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extendXIso
        ComplexShape.embeddingUpNat (i := 2) (i' := (2 : ℤ)) rfl).hom.hom
      (((coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat).iCycles (2 : ℤ)).hom
        ((coordinateProjectiveCoverCochainIntCocycle).hom 1)) =
    (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.iCycles 2).hom
      ((coordinateProjectiveCoverCocycle).hom 1)
  have hint := ConcreteCategory.congr_hom
    ((coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extend
      ComplexShape.embeddingUpNat).liftCycles_i
      coordinateProjectiveCoverCochainIntHom (ComplexShape.embeddingUpNat.f 3)
      (by norm_num) coordinateProjectiveCoverCochainIntHom_closed) 1
  change ((coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extend
      ComplexShape.embeddingUpNat).iCycles (2 : ℤ)).hom
      ((coordinateProjectiveCoverCochainIntCocycle).hom 1) =
    coordinateProjectiveCoverCochainIntHom.hom 1 at hint
  rw [hint]
  have hco := ConcreteCategory.congr_hom
    (HomologicalComplex.liftCycles_i
      coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex
      (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ coordinateProjectiveCoverCochain))
      3 (by norm_num) (by
        ext
        change coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.d 2 3
          (LinearMap.toSpanSingleton ℚ _ coordinateProjectiveCoverCochain 1) = 0
        rw [LinearMap.toSpanSingleton_apply]
        simpa using coordinateProjectiveCoverCochain_closed)) 1
  simp only [ConcreteCategory.comp_apply] at hco
  have hco' : (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.iCycles 2).hom
      ((coordinateProjectiveCoverCocycle).hom 1) = coordinateProjectiveCoverCochain := by
    simpa [coordinateProjectiveCoverCocycle,
      LinearMap.toSpanSingleton_apply, one_smul] using hco
  rw [hco']
  let e₁ := coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extendXIso
    ComplexShape.embeddingUpNat (i := 2) rfl
  let e₂ := coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extendXIso
    ComplexShape.embeddingUpNat (i := 2) (i' := (2 : ℤ)) (by norm_num)
  have he : e₁ = e₂ := by
    dsimp [e₁, e₂]
    congr
  simp [coordinateProjectiveCoverCochainIntHom,
    LinearMap.toSpanSingleton_apply, one_smul]
  change e₂.hom.hom (e₁.inv.hom coordinateProjectiveCoverCochain) =
    coordinateProjectiveCoverCochain
  rw [he]
  exact ConcreteCategory.congr_hom e₂.inv_hom_id coordinateProjectiveCoverCochain

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma coordinateHyperplaneRelativeCechCochainHom_connecting :
    coordinateHyperplaneRelativeCechCochainHom ≫
        (CochainComplex.mappingCone.triangle
          (RelativeCechConeComparison.dualMapInt
            coordinateHyperplaneComplementToAmbientCechMap)).mor₃.f
              ((2 : ℤ) - 1) ≫
        (CochainComplex.shiftFunctorObjXIso
          (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extend
            ComplexShape.embeddingUpNat)
          (1 : ℤ) ((2 : ℤ) - 1) (2 : ℤ) (by omega)).hom =
      -coordinateProjectiveCoverCochainIntHom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (((CochainComplex.mappingCone.triangle
      (RelativeCechConeComparison.dualMapInt
        coordinateHyperplaneComplementToAmbientCechMap)).mor₃.f ((2 : ℤ) - 1) ≫
    (CochainComplex.shiftFunctorObjXIso
      (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat) 1 ((2 : ℤ) - 1) 2 (by omega)).hom).hom
      (x • RelativeCechConeComparison.coneCochain
        (RelativeCechConeComparison.dualMapInt
          coordinateHyperplaneComplementToAmbientCechMap)
        (2 : ℤ)
        (coordinateProjectiveCoverCochainIntHom.hom 1)
        (coordinateHyperplaneComplementFullPartIntHom.hom 1))) =
    (-coordinateProjectiveCoverCochainIntHom).hom x
  have hcone :
      (((CochainComplex.mappingCone.triangle
          (RelativeCechConeComparison.dualMapInt
            coordinateHyperplaneComplementToAmbientCechMap)).mor₃.f ((2 : ℤ) - 1) ≫
        (CochainComplex.shiftFunctorObjXIso
          (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extend
            ComplexShape.embeddingUpNat) 1 ((2 : ℤ) - 1) 2 (by omega)).hom).hom
          (RelativeCechConeComparison.coneCochain
            (RelativeCechConeComparison.dualMapInt
              coordinateHyperplaneComplementToAmbientCechMap)
            (2 : ℤ)
            (coordinateProjectiveCoverCochainIntHom.hom 1)
            (coordinateHyperplaneComplementFullPartIntHom.hom 1))) =
        -(coordinateProjectiveCoverCochainIntHom.hom 1) := by
    have hraw :=
      AlgebraicTopology.RelativeCechConeComparison.coneCochain_connecting
      (RelativeCechConeComparison.dualMapInt
        coordinateHyperplaneComplementToAmbientCechMap)
      (2 : ℤ)
      (coordinateProjectiveCoverCochainIntHom.hom 1)
      (coordinateHyperplaneComplementFullPartIntHom.hom 1)
    simpa only using hraw
  rw [map_smul, hcone]
  simp [coordinateProjectiveCoverCochainIntHom,
    LinearMap.toSpanSingleton_apply]

set_option maxHeartbeats 1000000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma coordinateHyperplaneRelativeCechConnecting :
    (HomologicalComplex.homologyFunctor (ModuleCat ℚ) ℤᵘᵖ 0).shiftMap
        (CochainComplex.mappingCone.triangle
          (RelativeCechConeComparison.dualMapInt
            coordinateHyperplaneComplementToAmbientCechMap)).mor₃
        (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2) (by norm_num)
        coordinateHyperplaneRelativeCechHomologyClass =
      - coordinateProjectiveCoverCochainIntClass := by
  let δ := RelativeCechConeComparison.dualMapInt
    coordinateHyperplaneComplementToAmbientCechMap
  let T := CochainComplex.mappingCone.triangle δ
  let H := HomologicalComplex.homologyFunctor (ModuleCat ℚ) ℤᵘᵖ 0
  let c : ModuleCat.of ℚ ℚ ⟶ T.obj₃.X (1 : ℤ) :=
    coordinateHyperplaneRelativeCechCochainHom
  have hc : c ≫ T.obj₃.d (1 : ℤ) (2 : ℤ) = 0 := by
    dsimp [c, T, δ]
    convert coordinateHyperplaneRelativeCechCochainHom_closed using 1 <;> rfl
  let xc : ModuleCat.of ℚ ℚ ⟶ T.obj₃.cycles (1 : ℤ) :=
    T.obj₃.liftCycles c (2 : ℤ) (by norm_num) hc
  let a : ModuleCat.of ℚ ℚ ⟶ T.obj₁.X (2 : ℤ) :=
    coordinateProjectiveCoverCochainIntHom
  have ha : a ≫ T.obj₁.d (2 : ℤ) (3 : ℤ) = 0 := by
    change coordinateProjectiveCoverCochainIntHom ≫
      (coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extend
        ComplexShape.embeddingUpNat).d (2 : ℤ) (3 : ℤ) = 0
    simpa using coordinateProjectiveCoverCochainIntHom_closed
  let ac : ModuleCat.of ℚ ℚ ⟶ T.obj₁.cycles (2 : ℤ) :=
    T.obj₁.liftCycles a (3 : ℤ) (by norm_num) ha
  have hraw : c ≫ T.mor₃.f (1 : ℤ) ≫
      (T.obj₁.shiftFunctorObjXIso (1 : ℤ) (1 : ℤ) (2 : ℤ) (by omega)).hom =
        -a := by
    simpa [c, a, T, δ] using coordinateHyperplaneRelativeCechCochainHom_connecting
  have hlift
      (hu : (c ≫ T.mor₃.f (1 : ℤ) ≫
        (T.obj₁.shiftFunctorObjXIso (1 : ℤ) (1 : ℤ) (2 : ℤ) (by omega)).hom) ≫
          T.obj₁.d (2 : ℤ) (3 : ℤ) = 0) :
      T.obj₁.liftCycles
          (c ≫ T.mor₃.f (1 : ℤ) ≫
            (T.obj₁.shiftFunctorObjXIso
              (1 : ℤ) (1 : ℤ) (2 : ℤ) (by omega)).hom)
          (3 : ℤ) (by norm_num) hu = -ac := by
    apply (cancel_mono (T.obj₁.iCycles (2 : ℤ))).1
    rw [T.obj₁.liftCycles_i]
    rw [Preadditive.neg_comp]
    dsimp [ac]
    rw [T.obj₁.liftCycles_i]
    exact hraw
  have hmor :
      xc ≫ T.obj₃.homologyπ (1 : ℤ) ≫
          H.shiftMap T.mor₃
            (1 : ℤ) (2 : ℤ) (by omega) =
        -(ac ≫ T.obj₁.homologyπ (2 : ℤ)) := by
    dsimp [H, Functor.shiftMap, CochainComplex.homologyFunctor_shift]
    rw [HomologicalComplex.homologyπ_naturality_assoc]
    rw [HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
    rw [T.obj₁.liftCycles_shift_homologyπ_assoc _ _ _ _
      (2 : ℤ) (by omega) (3 : ℤ) (by norm_num)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [hlift]
    simp only [Preadditive.neg_comp]
    congr 1
  have hclassC : coordinateHyperplaneRelativeCechHomologyClass =
      (xc ≫ T.obj₃.homologyπ (1 : ℤ)).hom 1 := by
    rfl
  have hclassA : coordinateProjectiveCoverCochainIntClass =
      (ac ≫ T.obj₁.homologyπ (2 : ℤ)).hom 1 := by
    rfl
  rw [hclassC, hclassA]
  exact ConcreteCategory.congr_hom hmor 1

set_option maxHeartbeats 1000000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the relative Čech--singular comparison identifies the ambient image of the
singular cone connecting class with the negative explicit ambient Čech class. -/
lemma coordinateHyperplaneRelativeSingularConnecting_toCech :
    (HomologicalComplex.homologyMap
      (RelativeCechConeComparison.dualMapInt coordinateProjectiveCoverToSingular)
      (ComplexShape.embeddingUpNat.f 2)).hom
      ((HomologicalComplex.homologyFunctor (ModuleCat ℚ) ℤᵘᵖ 0).shiftMap
        (CochainComplex.mappingCone.triangle
          (relativeCochainRestrictionInt ℚ coordinateHyperplaneSupportPair)).mor₃
        (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2) (by norm_num)
        coordinateHyperplaneRelativeSingularConeClass) =
      -coordinateProjectiveCoverCochainIntClass := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat ℚ) ℤᵘᵖ 0
  have htriangle := RelativeCechConeComparison.comparison_connecting
    coordinateHyperplaneComplementToAmbientCechMap
    (SSet.chainComplexMap (TopCat.toSSet.map coordinateHyperplaneSupportPair.hom)
      (ModuleCat.of ℚ ℚ))
    (rationalOpenCoverNormalizedCechTotalToSingular
      coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover)
    coordinateProjectiveCoverToSingular
    (rationalPullbackCoverNormalizedCechToSingular_naturality
      coordinateHyperplaneSupportPair.hom projectiveCover)
  have hhom := congrArg
    (fun f ↦ H.shiftMap f (ComplexShape.embeddingUpNat.f 1)
      (ComplexShape.embeddingUpNat.f 2) (by norm_num)) htriangle
  rw [Functor.shiftMap_comp', Functor.shiftMap_comp] at hhom
  have hpoint := ConcreteCategory.congr_hom hhom
    coordinateHyperplaneRelativeSingularConeClass
  simp only [ConcreteCategory.comp_apply] at hpoint
  change
    (HomologicalComplex.homologyMap coordinateHyperplaneRelativeCechComparison
      (ComplexShape.embeddingUpNat.f 1)).hom coordinateHyperplaneRelativeSingularConeClass |> fun z ↦
        (H.shiftMap
          (CochainComplex.mappingCone.triangle
            (RelativeCechConeComparison.dualMapInt
              coordinateHyperplaneComplementToAmbientCechMap)).mor₃
          (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2)
          (by norm_num)).hom z =
      (HomologicalComplex.homologyMap
        (RelativeCechConeComparison.dualMapInt coordinateProjectiveCoverToSingular)
        (ComplexShape.embeddingUpNat.f 2)).hom
        ((H.shiftMap
          (CochainComplex.mappingCone.triangle
            (relativeCochainRestrictionInt ℚ coordinateHyperplaneSupportPair)).mor₃
          (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2)
          (by norm_num)).hom
          coordinateHyperplaneRelativeSingularConeClass) at hpoint
  have hclass :
      (HomologicalComplex.homologyMap coordinateHyperplaneRelativeCechComparison
        (ComplexShape.embeddingUpNat.f 1)).hom coordinateHyperplaneRelativeSingularConeClass =
        coordinateHyperplaneRelativeCechHomologyClass := by
    simpa only using coordinateHyperplaneRelativeCechComparison_homologyMap_class
  rw [hclass, coordinateHyperplaneRelativeCechConnecting] at hpoint
  exact hpoint.symm

/-- The explicit ordinary singular cochain class in the same integer-extended grading used by
the relative mapping cone. -/
noncomputable def coordinateProjectiveCoverSingularCochainIntClass :
    ((SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex.extend
      ComplexShape.embeddingUpNat).homology (ComplexShape.embeddingUpNat.f 2) :=
  ((SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex.extendHomologyIso
    ComplexShape.embeddingUpNat (j := 2) (j' := ComplexShape.embeddingUpNat.f 2) rfl).inv.hom
      coordinateProjectiveCoverSingularCochainClass

set_option maxHeartbeats 1000000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The integer-extended singular class maps to the displayed ambient Čech class under the
actual dual Čech augmentation. -/
lemma coordinateProjectiveCoverSingularCochainIntClass_toCech :
    (HomologicalComplex.homologyMap
      (RelativeCechConeComparison.dualMapInt coordinateProjectiveCoverToSingular)
      (ComplexShape.embeddingUpNat.f 2)).hom
      coordinateProjectiveCoverSingularCochainIntClass =
        coordinateProjectiveCoverCochainIntClass := by
  let K := (SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex
  let L := coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex
  let φ := HomologicalComplex.linearDualMap coordinateProjectiveCoverToSingular
  let eK := K.extendHomologyIso ComplexShape.embeddingUpNat
    (j := 2) (j' := ComplexShape.embeddingUpNat.f 2) rfl
  let eL := L.extendHomologyIso ComplexShape.embeddingUpNat
    (j := 2) (j' := ComplexShape.embeddingUpNat.f 2) rfl
  have hnat := HomologicalComplex.extendHomologyIso_hom_naturality φ
    ComplexShape.embeddingUpNat (j := 2) (j' := ComplexShape.embeddingUpNat.f 2) rfl
  have hnat' := ConcreteCategory.congr_hom hnat
    coordinateProjectiveCoverSingularCochainIntClass
  have hsing :
      (HomologicalComplex.homologyMap φ 2).hom
        coordinateProjectiveCoverSingularCochainClass =
          coordinateProjectiveCoverCochainClass := by
    letI : QuasiIso coordinateProjectiveCoverToSingular :=
      projectiveCover_rationalNormalizedCechToSingular_quasiIso
    rw [← HomologicalComplex.linearDualCohomologyEquivOfQuasiIso_apply]
    simp [coordinateProjectiveCoverSingularCochainClass]
  apply eL.toLinearEquiv.injective
  change eL.hom.hom
      ((HomologicalComplex.homologyMap
        (RelativeCechConeComparison.dualMapInt coordinateProjectiveCoverToSingular)
        (ComplexShape.embeddingUpNat.f 2)).hom
        coordinateProjectiveCoverSingularCochainIntClass) =
    eL.hom.hom coordinateProjectiveCoverCochainIntClass
  change eL.hom.hom
      ((HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
        (ComplexShape.embeddingUpNat.f 2)).hom
        coordinateProjectiveCoverSingularCochainIntClass) = _
  rw [show eL.hom.hom
      ((HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
        (ComplexShape.embeddingUpNat.f 2)).hom
        coordinateProjectiveCoverSingularCochainIntClass) =
      (HomologicalComplex.homologyMap φ 2).hom
        (eK.hom.hom coordinateProjectiveCoverSingularCochainIntClass) from hnat']
  let eK' := (SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex.extendHomologyIso
    ComplexShape.embeddingUpNat (j := 2) (j' := ComplexShape.embeddingUpNat.f 2) rfl
  have heK : eK = eK' := by
    dsimp [eK, eK', K]
  rw [show eK.hom.hom coordinateProjectiveCoverSingularCochainIntClass =
      coordinateProjectiveCoverSingularCochainClass by
    change eK.hom.hom (eK'.inv.hom coordinateProjectiveCoverSingularCochainClass) = _
    rw [← heK]
    exact ConcreteCategory.congr_hom eK.inv_hom_id
      coordinateProjectiveCoverSingularCochainClass]
  rw [hsing]
  exact coordinateProjectiveCoverCochainIntClass_toNat.symm

set_option maxHeartbeats 1000000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The singular connecting morphism reads the negative ambient singular cocycle.  Injectivity
here is not an assumption: it comes from the proved Čech augmentation quasi-isomorphism. -/
lemma coordinateHyperplaneRelativeSingularConnecting :
    (HomologicalComplex.homologyFunctor (ModuleCat ℚ) ℤᵘᵖ 0).shiftMap
        (CochainComplex.mappingCone.triangle
          (relativeCochainRestrictionInt ℚ coordinateHyperplaneSupportPair)).mor₃
        (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2) (by norm_num)
        coordinateHyperplaneRelativeSingularConeClass =
      -coordinateProjectiveCoverSingularCochainIntClass := by
  let d := RelativeCechConeComparison.dualMapInt coordinateProjectiveCoverToSingular
  letI : QuasiIso coordinateProjectiveCoverToSingular :=
    projectiveCover_rationalNormalizedCechToSingular_quasiIso
  letI : QuasiIso (HomologicalComplex.linearDualMap coordinateProjectiveCoverToSingular) :=
    HomologicalComplex.linearDualMap_quasiIso coordinateProjectiveCoverToSingular
  letI : QuasiIso d :=
    (HomologicalComplex.quasiIso_extendMap_iff
      (HomologicalComplex.linearDualMap coordinateProjectiveCoverToSingular)
      ComplexShape.embeddingUpNat).mpr inferInstance
  apply (ModuleCat.mono_iff_injective
    (HomologicalComplex.homologyMap d (ComplexShape.embeddingUpNat.f 2))).mp inferInstance
  change (HomologicalComplex.homologyMap d (ComplexShape.embeddingUpNat.f 2)).hom
      ((HomologicalComplex.homologyFunctor (ModuleCat ℚ) ℤᵘᵖ 0).shiftMap
        (CochainComplex.mappingCone.triangle
          (relativeCochainRestrictionInt ℚ coordinateHyperplaneSupportPair)).mor₃
        (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2) (by norm_num)
        coordinateHyperplaneRelativeSingularConeClass) =
    (HomologicalComplex.homologyMap d (ComplexShape.embeddingUpNat.f 2)).hom
      (-coordinateProjectiveCoverSingularCochainIntClass)
  rw [show (HomologicalComplex.homologyMap d (ComplexShape.embeddingUpNat.f 2)).hom
      ((HomologicalComplex.homologyFunctor (ModuleCat ℚ) ℤᵘᵖ 0).shiftMap
        (CochainComplex.mappingCone.triangle
          (relativeCochainRestrictionInt ℚ coordinateHyperplaneSupportPair)).mor₃
        (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2) (by norm_num)
        coordinateHyperplaneRelativeSingularConeClass) =
      -coordinateProjectiveCoverCochainIntClass from
    coordinateHyperplaneRelativeSingularConnecting_toCech]
  rw [map_neg, coordinateProjectiveCoverSingularCochainIntClass_toCech]

noncomputable def coordinateHyperplaneRelativeCechClass :
    RelativeCohomology ℚ coordinateHyperplaneSupportPair 2 :=
  relativeCochainConeCohomologyEquivCanonical ℚ coordinateHyperplaneSupportPair 2
    coordinateHyperplaneRelativeSingularConeClass

/-
The preceding class is a literal relative Čech--singular cone class.  Its inverse image under
`coordinateHyperplaneRelativeCechComparison` is canonical, but is obtained via `asIso` from the
proved quasi-isomorphism; this is an abstract homology transport, not a newly selected raw
singular cochain.  The comparison with the separately defined algebraic cycle-class construction
is supplied by `ProjectivePlaneExplicitClassNormalizationContinuation`, which proves the local
winding normalization and then performs the ordinary/hypercohomology transport.
-/

/-- The explicit cone class viewed as singular cohomology with support in the literal
coordinate zero-locus.  This is just the definitional identification
`CohomologyWithSupport = RelativeCohomology` for the displayed pair. -/
noncomputable def coordinateHyperplaneExplicitSupportedSingularClass :
    CohomologyWithSupport ℚ analyticPlaneTop coordinateHyperplaneAnalyticSupport 2 :=
  coordinateHyperplaneRelativeCechClass

/-- The global relative singular cone class, reindexed at the degree used by the canonical
degree-two cone comparison. -/
noncomputable def coordinateHyperplaneRelativeSingularConeClassDegreeTwo :
    (CochainComplex.mappingCone
      (relativeCochainRestrictionInt ℚ coordinateHyperplaneSupportPair)).homology
        ((2 : ℤ) - 1) := by
  convert coordinateHyperplaneRelativeSingularConeClass using 1 <;> norm_num

/-- The homology class of the literal first-chart cone cocycle `(0, wind(X₀/X₁))`, before
applying the canonical cone-to-relative-cohomology equivalence. -/
noncomputable def firstChartHyperplaneRelativeConeClass :
    (CochainComplex.mappingCone
      (relativeCochainRestrictionInt ℚ firstChartHyperplanePair)).homology
        ((2 : ℤ) - 1) := by
  convert
    (ChernWinding.rawRelativeWindingCocycle
        (X := firstChartHyperplanePair)
        firstNormalOnComplement firstNormalOnComplement_ne_zero ≫
      (CochainComplex.mappingCone
        (relativeCochainRestrictionInt ℚ firstChartHyperplanePair)).homologyπ
          (ComplexShape.embeddingUpNat.f 1)).hom 1 using 1 <;> norm_num

/-- The homology class of the literal second-chart cone cocycle `(0, wind(X₀/X₂))`, in
the degree used by the canonical degree-two cone comparison. -/
noncomputable def secondChartHyperplaneRelativeConeClass :
    (CochainComplex.mappingCone
      (relativeCochainRestrictionInt ℚ secondChartHyperplanePair)).homology
        ((2 : ℤ) - 1) := by
  convert
    (ChernWinding.rawRelativeWindingCocycle
        (X := secondChartHyperplanePair)
        secondNormalOnComplement secondNormalOnComplement_ne_zero ≫
      (CochainComplex.mappingCone
        (relativeCochainRestrictionInt ℚ secondChartHyperplanePair)).homologyπ
          (ComplexShape.embeddingUpNat.f 1)).hom 1 using 1 <;> norm_num

/-- Restricting the global explicit supported class to the first affine chart is equivalent to
the remaining chain-level statement that the induced cone-homology map sends the global class
to the literal local winding cocycle.  Thus this theorem introduces no comparison hypothesis;
it isolates exactly the equality still required from the normalized Čech restriction map. -/
lemma coordinateHyperplaneExplicitSupportedSingularClass_restrict_first_iff_cone :
    relativeCohomologyMap ℚ 2 firstChartToCoordinateHyperplaneSupportPair
        coordinateHyperplaneExplicitSupportedSingularClass =
          firstChartHyperplaneRelativeSingularClass ↔
      (HomologicalComplex.homologyMap
        (relativeCochainConeMap ℚ firstChartToCoordinateHyperplaneSupportPair)
        ((2 : ℤ) - 1)).hom
          coordinateHyperplaneRelativeSingularConeClassDegreeTwo =
        firstChartHyperplaneRelativeConeClass := by
  have hnat := relativeCochainConeCohomologyEquivCanonical_naturality ℚ
    firstChartToCoordinateHyperplaneSupportPair 2
      coordinateHyperplaneRelativeSingularConeClassDegreeTwo
  have ha :
      relativeCochainConeCohomologyEquivCanonical ℚ
          coordinateHyperplaneSupportPair 2
            coordinateHyperplaneRelativeSingularConeClassDegreeTwo =
        coordinateHyperplaneExplicitSupportedSingularClass := by
    dsimp [coordinateHyperplaneRelativeSingularConeClassDegreeTwo]
    rfl
  have hb :
      relativeCochainConeCohomologyEquivCanonical ℚ
          firstChartHyperplanePair 2 firstChartHyperplaneRelativeConeClass =
        firstChartHyperplaneRelativeSingularClass := by
    dsimp [firstChartHyperplaneRelativeConeClass]
    rfl
  constructor
  · intro h
    apply (relativeCochainConeCohomologyEquivCanonical ℚ
      firstChartHyperplanePair 2).injective
    calc
      _ = relativeCohomologyMap ℚ 2 firstChartToCoordinateHyperplaneSupportPair
          (relativeCochainConeCohomologyEquivCanonical ℚ
            coordinateHyperplaneSupportPair 2
              coordinateHyperplaneRelativeSingularConeClassDegreeTwo) := hnat
      _ = relativeCohomologyMap ℚ 2 firstChartToCoordinateHyperplaneSupportPair
          coordinateHyperplaneExplicitSupportedSingularClass := congrArg _ ha
      _ = firstChartHyperplaneRelativeSingularClass := h
      _ = relativeCochainConeCohomologyEquivCanonical ℚ
          firstChartHyperplanePair 2 firstChartHyperplaneRelativeConeClass := hb.symm
  · intro h
    rw [← ha, ← hb, ← hnat]
    exact congrArg
      (relativeCochainConeCohomologyEquivCanonical ℚ firstChartHyperplanePair 2) h

/-- The second-chart supported restriction statement is equivalent to the corresponding bare
cone-homology identity.  This is the symmetric reduction of
`coordinateHyperplaneExplicitSupportedSingularClass_restrict_first_iff_cone`. -/
lemma coordinateHyperplaneExplicitSupportedSingularClass_restrict_second_iff_cone :
    relativeCohomologyMap ℚ 2 secondChartToCoordinateHyperplaneSupportPair
        coordinateHyperplaneExplicitSupportedSingularClass =
          secondChartHyperplaneRelativeSingularClass ↔
      (HomologicalComplex.homologyMap
        (relativeCochainConeMap ℚ secondChartToCoordinateHyperplaneSupportPair)
        ((2 : ℤ) - 1)).hom
          coordinateHyperplaneRelativeSingularConeClassDegreeTwo =
        secondChartHyperplaneRelativeConeClass := by
  have hnat := relativeCochainConeCohomologyEquivCanonical_naturality ℚ
    secondChartToCoordinateHyperplaneSupportPair 2
      coordinateHyperplaneRelativeSingularConeClassDegreeTwo
  have ha :
      relativeCochainConeCohomologyEquivCanonical ℚ
          coordinateHyperplaneSupportPair 2
            coordinateHyperplaneRelativeSingularConeClassDegreeTwo =
        coordinateHyperplaneExplicitSupportedSingularClass := by
    dsimp [coordinateHyperplaneRelativeSingularConeClassDegreeTwo]
    rfl
  have hb :
      relativeCochainConeCohomologyEquivCanonical ℚ
          secondChartHyperplanePair 2 secondChartHyperplaneRelativeConeClass =
        secondChartHyperplaneRelativeSingularClass := by
    dsimp [secondChartHyperplaneRelativeConeClass]
    rfl
  constructor
  · intro h
    apply (relativeCochainConeCohomologyEquivCanonical ℚ
      secondChartHyperplanePair 2).injective
    calc
      _ = relativeCohomologyMap ℚ 2 secondChartToCoordinateHyperplaneSupportPair
          (relativeCochainConeCohomologyEquivCanonical ℚ
            coordinateHyperplaneSupportPair 2
              coordinateHyperplaneRelativeSingularConeClassDegreeTwo) := hnat
      _ = relativeCohomologyMap ℚ 2 secondChartToCoordinateHyperplaneSupportPair
          coordinateHyperplaneExplicitSupportedSingularClass := congrArg _ ha
      _ = secondChartHyperplaneRelativeSingularClass := h
      _ = relativeCochainConeCohomologyEquivCanonical ℚ
          secondChartHyperplanePair 2 secondChartHyperplaneRelativeConeClass := hb.symm
  · intro h
    rw [← ha, ← hb, ← hnat]
    exact congrArg
      (relativeCochainConeCohomologyEquivCanonical ℚ secondChartHyperplanePair 2) h

/-- The global explicit relative Čech class pulled back to the normalized Čech model on
the first affine chart. -/
noncomputable def coordinateHyperplaneRelativeCechClassOnFirstChart :
    (RelativeCechConeComparison.relativeDualCone
      firstChartPulledbackComplementToAmbientCechMap).homology ((2 : ℤ) - 1) :=
  (HomologicalComplex.homologyMap
    coordinateHyperplaneToFirstChartRelativeCechConeMap ((2 : ℤ) - 1)).hom
      coordinateHyperplaneRelativeCechHomologyClass

set_option backward.isDefEq.respectTransparency false in
/-- Degree-normalized form of `firstChartSectionComparison_global_raw_transport`. -/
lemma firstChartSectionComparison_global_raw :
    firstChartRelativeCechSectionComparison.f
        (ComplexShape.embeddingUpNat.f 1)
      (coordinateHyperplaneToFirstChartRelativeCechConeMap.f
        (ComplexShape.embeddingUpNat.f 1)
        coordinateHyperplaneRelativeCechRawElementDegreeOne) =
      ChernWinding.rawRelativeWindingCochain
        (X := firstChartHyperplanePair)
        firstNormalOnComplement firstNormalOnComplement_ne_zero := by
  have h := firstChartSectionComparison_global_raw_transport
  norm_num [coordinateHyperplaneRelativeCechRawElementDegreeOne,
    ComplexShape.embeddingUpNat_f, HomologicalComplex.XIsoOfEq] at h ⊢
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The preceding evaluation is an equality of the full one-dimensional cochain maps. -/
lemma firstChartSectionComparison_global_cochainHom :
    coordinateHyperplaneRelativeCechCochainHom ≫
        coordinateHyperplaneToFirstChartRelativeCechConeMap.f
          (ComplexShape.embeddingUpNat.f 1) ≫
        firstChartRelativeCechSectionComparison.f
          (ComplexShape.embeddingUpNat.f 1) =
      ChernWinding.rawRelativeWindingCochainHom
        (X := firstChartHyperplanePair)
        firstNormalOnComplement firstNormalOnComplement_ne_zero := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ConcreteCategory.comp_apply]
  have hx :
      (ChernWinding.rawRelativeWindingCochainHom
        (X := firstChartHyperplanePair)
        firstNormalOnComplement firstNormalOnComplement_ne_zero).hom x =
      x • ChernWinding.rawRelativeWindingCochain
        (X := firstChartHyperplanePair)
        firstNormalOnComplement firstNormalOnComplement_ne_zero := by
    simpa [ChernWinding.rawRelativeWindingCochain] using
      (map_smul
        (ChernWinding.rawRelativeWindingCochainHom
          (X := firstChartHyperplanePair)
          firstNormalOnComplement firstNormalOnComplement_ne_zero).hom
        x (1 : ℚ))
  rw [coordinateHyperplaneRelativeCechCochainHom_apply, hx,
    map_smul, map_smul]
  exact congrArg (fun z ↦ x • z) firstChartSectionComparison_global_raw

set_option backward.isDefEq.respectTransparency false in
/-- The raw equality lifts to the corresponding maps into the cycle objects. -/
lemma firstChartSectionComparison_global_cycles :
    coordinateHyperplaneRelativeCechCocycle ≫
        HomologicalComplex.cyclesMap
          coordinateHyperplaneToFirstChartRelativeCechConeMap
          (ComplexShape.embeddingUpNat.f 1) ≫
        HomologicalComplex.cyclesMap firstChartRelativeCechSectionComparison
          (ComplexShape.embeddingUpNat.f 1) =
      ChernWinding.rawRelativeWindingCocycle
        (X := firstChartHyperplanePair)
        firstNormalOnComplement firstNormalOnComplement_ne_zero := by
  apply (cancel_mono ((CochainComplex.mappingCone
    (relativeCochainRestrictionInt ℚ firstChartHyperplanePair)).iCycles
      (ComplexShape.embeddingUpNat.f 1))).1
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
  rw [HomologicalComplex.cyclesMap_i_assoc]
  dsimp [coordinateHyperplaneRelativeCechCocycle,
    ChernWinding.rawRelativeWindingCocycle]
  rw [HomologicalComplex.liftCycles_i_assoc,
    HomologicalComplex.liftCycles_i]
  exact firstChartSectionComparison_global_cochainHom

set_option backward.isDefEq.respectTransparency false in
/-- The distinguished section sends the pulled-back global Čech class to the literal local
winding class. -/
lemma firstChartSectionComparison_homologyMap_global_class :
    (HomologicalComplex.homologyMap firstChartRelativeCechSectionComparison
      (ComplexShape.embeddingUpNat.f 1)).hom
        coordinateHyperplaneRelativeCechClassOnFirstChart =
      firstChartHyperplaneRelativeConeClass := by
  have hπ :
      coordinateHyperplaneRelativeCechCocycle ≫
          HomologicalComplex.cyclesMap
            coordinateHyperplaneToFirstChartRelativeCechConeMap
            (ComplexShape.embeddingUpNat.f 1) ≫
          HomologicalComplex.cyclesMap firstChartRelativeCechSectionComparison
            (ComplexShape.embeddingUpNat.f 1) ≫
          (CochainComplex.mappingCone
            (relativeCochainRestrictionInt ℚ firstChartHyperplanePair)).homologyπ
              (ComplexShape.embeddingUpNat.f 1) =
        ChernWinding.rawRelativeWindingCocycle
            (X := firstChartHyperplanePair)
            firstNormalOnComplement firstNormalOnComplement_ne_zero ≫
          (CochainComplex.mappingCone
            (relativeCochainRestrictionInt ℚ firstChartHyperplanePair)).homologyπ
              (ComplexShape.embeddingUpNat.f 1) := by
    simpa only [Category.assoc] using congrArg
      (fun f ↦ f ≫ (CochainComplex.mappingCone
        (relativeCochainRestrictionInt ℚ firstChartHyperplanePair)).homologyπ
          (ComplexShape.embeddingUpNat.f 1)) firstChartSectionComparison_global_cycles
  have hnat :
      coordinateHyperplaneRelativeCechCocycle ≫
          coordinateHyperplaneRelativeCechCone.homologyπ
            (ComplexShape.embeddingUpNat.f 1) ≫
          HomologicalComplex.homologyMap
            coordinateHyperplaneToFirstChartRelativeCechConeMap
            (ComplexShape.embeddingUpNat.f 1) ≫
          HomologicalComplex.homologyMap firstChartRelativeCechSectionComparison
            (ComplexShape.embeddingUpNat.f 1) =
        coordinateHyperplaneRelativeCechCocycle ≫
          HomologicalComplex.cyclesMap
            coordinateHyperplaneToFirstChartRelativeCechConeMap
            (ComplexShape.embeddingUpNat.f 1) ≫
          HomologicalComplex.cyclesMap firstChartRelativeCechSectionComparison
            (ComplexShape.embeddingUpNat.f 1) ≫
          (CochainComplex.mappingCone
            (relativeCochainRestrictionInt ℚ firstChartHyperplanePair)).homologyπ
              (ComplexShape.embeddingUpNat.f 1) := by
    rw [HomologicalComplex.homologyπ_naturality_assoc]
    simpa only [Category.assoc] using congrArg
      (fun f ↦ coordinateHyperplaneRelativeCechCocycle ≫
        HomologicalComplex.cyclesMap
          coordinateHyperplaneToFirstChartRelativeCechConeMap
          (ComplexShape.embeddingUpNat.f 1) ≫ f)
      (HomologicalComplex.homologyπ_naturality
        (K := RelativeCechConeComparison.relativeDualCone
          firstChartPulledbackComplementToAmbientCechMap)
        (L := CochainComplex.mappingCone
          (relativeCochainRestrictionInt ℚ firstChartHyperplanePair))
        (i := ComplexShape.embeddingUpNat.f 1)
        firstChartRelativeCechSectionComparison)
  change ((coordinateHyperplaneRelativeCechCocycle ≫
      coordinateHyperplaneRelativeCechCone.homologyπ
        (ComplexShape.embeddingUpNat.f 1) ≫
      HomologicalComplex.homologyMap
        coordinateHyperplaneToFirstChartRelativeCechConeMap
        (ComplexShape.embeddingUpNat.f 1) ≫
      HomologicalComplex.homologyMap firstChartRelativeCechSectionComparison
        (ComplexShape.embeddingUpNat.f 1)).hom 1) =
    ((ChernWinding.rawRelativeWindingCocycle
        (X := firstChartHyperplanePair)
        firstNormalOnComplement firstNormalOnComplement_ne_zero ≫
      (CochainComplex.mappingCone
        (relativeCochainRestrictionInt ℚ firstChartHyperplanePair)).homologyπ
          (ComplexShape.embeddingUpNat.f 1)).hom 1)
  rw [ConcreteCategory.congr_hom hnat 1]
  exact ConcreteCategory.congr_hom hπ 1

set_option backward.isDefEq.respectTransparency false in
/-- The pulled-back global Čech class is the image of the literal first-chart winding class.
The reverse singleton comparison is the inverse on homology because the forward comparison is
a quasi-isomorphism and their composite is strictly the identity. -/
lemma coordinateHyperplaneRelativeCechClassOnFirstChart_eq_localWinding :
    coordinateHyperplaneRelativeCechClassOnFirstChart =
      (HomologicalComplex.homologyMap firstChartRelativeCechComparison
        (ComplexShape.embeddingUpNat.f 1)).hom
          firstChartHyperplaneRelativeConeClass := by
  let f := HomologicalComplex.homologyMap firstChartRelativeCechComparison
    (ComplexShape.embeddingUpNat.f 1)
  let s := HomologicalComplex.homologyMap firstChartRelativeCechSectionComparison
    (ComplexShape.embeddingUpNat.f 1)
  have hfs : f ≫ s = 𝟙 _ := by
    have h := congrArg
      (fun k ↦ HomologicalComplex.homologyMap k
        (ComplexShape.embeddingUpNat.f 1))
      firstChartRelativeCechComparison_comp_sectionComparison
    simpa [f, s, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_id] using h
  have hsf : s ≫ f = 𝟙 _ := by
    apply (cancel_epi f).1
    rw [← Category.assoc, hfs, Category.id_comp, Category.comp_id]
  calc
    coordinateHyperplaneRelativeCechClassOnFirstChart =
        (s ≫ f).hom coordinateHyperplaneRelativeCechClassOnFirstChart := by
          rw [hsf]
          rfl
    _ = f.hom (s.hom coordinateHyperplaneRelativeCechClassOnFirstChart) := rfl
    _ = f.hom firstChartHyperplaneRelativeConeClass := by
      rw [firstChartSectionComparison_homologyMap_global_class]
    _ = _ := rfl

/-- The first-chart image of the global singular cone class has, after the local
Čech--singular comparison, exactly the pulled-back global relative Čech class. -/
lemma coordinateHyperplaneRelativeSingularConeClass_firstChart_toCech :
    (HomologicalComplex.homologyMap firstChartRelativeCechComparison
      ((2 : ℤ) - 1)).hom
        ((HomologicalComplex.homologyMap
          (relativeCochainConeMap ℚ firstChartToCoordinateHyperplaneSupportPair)
          ((2 : ℤ) - 1)).hom coordinateHyperplaneRelativeSingularConeClassDegreeTwo) =
      coordinateHyperplaneRelativeCechClassOnFirstChart := by
  have hnat := congrArg
    (fun f ↦ HomologicalComplex.homologyMap f ((2 : ℤ) - 1))
    coordinateHyperplaneRelativeCechComparison_firstChart_naturality
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp] at hnat
  have hpoint := ConcreteCategory.congr_hom hnat
    coordinateHyperplaneRelativeSingularConeClassDegreeTwo
  simp only [ConcreteCategory.comp_apply] at hpoint
  have hglobal :
      (HomologicalComplex.homologyMap coordinateHyperplaneRelativeCechComparison
        ((2 : ℤ) - 1)).hom coordinateHyperplaneRelativeSingularConeClassDegreeTwo =
        coordinateHyperplaneRelativeCechHomologyClass := by
    change (HomologicalComplex.homologyMap coordinateHyperplaneRelativeCechComparison
      (ComplexShape.embeddingUpNat.f 1)).hom
        coordinateHyperplaneRelativeSingularConeClass =
      coordinateHyperplaneRelativeCechHomologyClass
    exact coordinateHyperplaneRelativeCechComparison_homologyMap_class
  rw [hglobal] at hpoint
  dsimp [coordinateHyperplaneRelativeCechClassOnFirstChart]
  exact hpoint.symm

/-- The first-chart singular restriction identity is equivalent to one concrete local Čech
homology equality.  The latter is now proved from the explicit cochain calculation above; this
iff theorem records the exact transport through the Čech--singular comparison. -/
lemma coordinateHyperplaneRelativeSingularConeClass_restrict_first_iff_localCech :
    (HomologicalComplex.homologyMap
        (relativeCochainConeMap ℚ firstChartToCoordinateHyperplaneSupportPair)
        ((2 : ℤ) - 1)).hom coordinateHyperplaneRelativeSingularConeClassDegreeTwo =
        firstChartHyperplaneRelativeConeClass ↔
      coordinateHyperplaneRelativeCechClassOnFirstChart =
        (HomologicalComplex.homologyMap firstChartRelativeCechComparison
          ((2 : ℤ) - 1)).hom firstChartHyperplaneRelativeConeClass := by
  constructor
  · intro h
    rw [← coordinateHyperplaneRelativeSingularConeClass_firstChart_toCech, h]
  · intro h
    let e := asIso (HomologicalComplex.homologyMap firstChartRelativeCechComparison
      ((2 : ℤ) - 1))
    have heq :
        (HomologicalComplex.homologyMap firstChartRelativeCechComparison
          ((2 : ℤ) - 1)).hom
            ((HomologicalComplex.homologyMap
              (relativeCochainConeMap ℚ firstChartToCoordinateHyperplaneSupportPair)
              ((2 : ℤ) - 1)).hom coordinateHyperplaneRelativeSingularConeClassDegreeTwo) =
          (HomologicalComplex.homologyMap firstChartRelativeCechComparison
            ((2 : ℤ) - 1)).hom firstChartHyperplaneRelativeConeClass := by
      rw [coordinateHyperplaneRelativeSingularConeClass_firstChart_toCech]
      exact h
    have hinv := congrArg (fun z ↦ e.inv.hom z) heq
    simpa [e] using hinv

/-- The global relative singular cone class restricts to the literal first-chart winding
class. -/
lemma coordinateHyperplaneRelativeSingularConeClass_restrict_first :
    (HomologicalComplex.homologyMap
        (relativeCochainConeMap ℚ firstChartToCoordinateHyperplaneSupportPair)
        ((2 : ℤ) - 1)).hom coordinateHyperplaneRelativeSingularConeClassDegreeTwo =
      firstChartHyperplaneRelativeConeClass :=
  coordinateHyperplaneRelativeSingularConeClass_restrict_first_iff_localCech.mpr
    coordinateHyperplaneRelativeCechClassOnFirstChart_eq_localWinding

/-- The explicit supported singular class restricts to the literal winding class on the
first affine chart. -/
lemma coordinateHyperplaneExplicitSupportedSingularClass_restrict_first :
    relativeCohomologyMap ℚ 2 firstChartToCoordinateHyperplaneSupportPair
        coordinateHyperplaneExplicitSupportedSingularClass =
      firstChartHyperplaneRelativeSingularClass :=
  coordinateHyperplaneExplicitSupportedSingularClass_restrict_first_iff_cone.mpr
    coordinateHyperplaneRelativeSingularConeClass_restrict_first

/-- Forgetting support gives the ordinary singular class attached to the explicit relative
Čech--singular cocycle. -/
noncomputable def coordinateHyperplaneExplicitOrdinarySingularClass :
    Cohomology ℚ analyticPlaneTop 2 :=
  forgetSupport ℚ analyticPlaneTop coordinateHyperplaneAnalyticSupport 2
    coordinateHyperplaneExplicitSupportedSingularClass

/-! The preceding class is induced by a literal cochain in the ordinary singular cochain
complex.  We do not choose an arbitrary preimage of the homology quotient.  Instead, projectivity
of rational chain groups upgrades the proved Čech-to-singular quasi-isomorphism to a chain
homotopy equivalence.  Applying its reverse chain map and then dualizing gives a chain-level map
from the displayed Čech cochains to ordinary singular cochains.  Thus the cochain below is the
literal winding/overlap functional precomposed with one fixed singular-to-Čech chain map.

The homotopy inverse itself is selected from a proved existence theorem.  This selection is not
a hypothesis and the resulting map satisfies the full chain-map and homotopy-inverse laws, but it
is the one remaining non-formula-level ingredient in evaluation on an arbitrary singular
simplex. -/

lemma coordinateProjectiveCoverToSingular_homotopyEquivalences :
    HomologicalComplex.homotopyEquivalences (ModuleCat ℚ) (ComplexShape.down ℕ)
      coordinateProjectiveCoverToSingular := by
  letI : QuasiIso coordinateProjectiveCoverToSingular :=
    projectiveCover_rationalNormalizedCechToSingular_quasiIso
  exact (ChainComplex.quasiIso_iff_of_projective
    coordinateProjectiveCoverToSingular).mp inferInstance

/-- A chain-homotopy equivalence whose forward map is the geometric augmentation from the
coordinate Čech total complex to ordinary singular chains. -/
noncomputable def coordinateProjectiveCoverSingularHomotopyEquiv :
    HomotopyEquiv
      coordinateHyperplaneAmbientCechTotal
      (SingularChainComplex ℚ analyticPlaneTop) :=
  coordinateProjectiveCoverToSingular_homotopyEquivalences.choose

lemma coordinateProjectiveCoverSingularHomotopyEquiv_hom :
    coordinateProjectiveCoverSingularHomotopyEquiv.hom =
      coordinateProjectiveCoverToSingular :=
  coordinateProjectiveCoverToSingular_homotopyEquivalences.choose_spec

/-- Contravariant dual of the chain equivalence.  Its inverse is the chain-level transfer from
the explicit coordinate Čech cochain complex to ordinary singular cochains. -/
noncomputable def coordinateProjectiveCoverDualHomotopyEquiv :
    HomotopyEquiv
      (SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex
      coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex :=
  HomologicalComplex.linearDualHomotopyEquiv
    coordinateProjectiveCoverSingularHomotopyEquiv

lemma coordinateProjectiveCoverDualHomotopyEquiv_hom :
    coordinateProjectiveCoverDualHomotopyEquiv.hom =
      HomologicalComplex.linearDualMap coordinateProjectiveCoverToSingular := by
  dsimp [coordinateProjectiveCoverDualHomotopyEquiv,
    HomologicalComplex.linearDualHomotopyEquiv]
  rw [coordinateProjectiveCoverSingularHomotopyEquiv_hom]
  rfl

/-- The explicit coordinate Čech cocycle transferred at chain level to a singular cocycle. -/
noncomputable def coordinateHyperplaneExplicitOrdinaryCocycle :
    ModuleCat.of ℚ ℚ ⟶
      (SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex.cycles 2 :=
  coordinateProjectiveCoverCocycle ≫
    HomologicalComplex.cyclesMap coordinateProjectiveCoverDualHomotopyEquiv.inv 2

/-- The ordinary singular cochain is obtained by evaluating the transferred cocycle in the
cycle subobject. -/
noncomputable def coordinateHyperplaneExplicitOrdinaryRawCochain :
    (SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex.X 2 :=
  ((SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex.iCycles 2).hom
    (coordinateHyperplaneExplicitOrdinaryCocycle.hom 1)

/-- At cochain level, the ordinary representative is exactly the explicit coordinate Čech
functional acted on by the reverse map of the dual chain-homotopy equivalence. -/
lemma coordinateHyperplaneExplicitOrdinaryRawCochain_eq_transfer :
    coordinateHyperplaneExplicitOrdinaryRawCochain =
      coordinateProjectiveCoverDualHomotopyEquiv.inv.f 2
        coordinateProjectiveCoverCochain := by
  have hi := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i coordinateProjectiveCoverDualHomotopyEquiv.inv 2)
    (coordinateProjectiveCoverCocycle.hom 1)
  have hc := ConcreteCategory.congr_hom coordinateProjectiveCoverCocycle_iCycles 1
  simp only [ConcreteCategory.comp_apply] at hi hc
  change ((SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex.iCycles 2).hom
      ((HomologicalComplex.cyclesMap coordinateProjectiveCoverDualHomotopyEquiv.inv 2).hom
        (coordinateProjectiveCoverCocycle.hom 1)) = _
  rw [hi]
  congr 1
  simpa [LinearMap.toSpanSingleton_apply] using hc

/-- Evaluation formula on an arbitrary rational singular two-chain. -/
lemma coordinateHyperplaneExplicitOrdinaryRawCochain_apply
    (c : (SingularChainComplex ℚ analyticPlaneTop).X 2) :
    (show Module.Dual ℚ ((SingularChainComplex ℚ analyticPlaneTop).X 2) from
      coordinateHyperplaneExplicitOrdinaryRawCochain) c =
      (show Module.Dual ℚ (coordinateHyperplaneAmbientCechTotal.X 2) from
        coordinateProjectiveCoverCochain)
          ((coordinateProjectiveCoverSingularHomotopyEquiv.inv.f 2).hom c) := by
  rw [coordinateHyperplaneExplicitOrdinaryRawCochain_eq_transfer]
  rfl

/-- The cochain-complex cohomology class of the transferred singular cocycle. -/
noncomputable def coordinateHyperplaneExplicitOrdinaryCochainClass :
    (SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex.homology 2 :=
  (coordinateHyperplaneExplicitOrdinaryCocycle ≫
    (SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex.homologyπ 2).hom 1

lemma coordinateHyperplaneExplicitOrdinaryCochainClass_eq_homologyMap_inv :
    coordinateHyperplaneExplicitOrdinaryCochainClass =
      (HomologicalComplex.homologyMap coordinateProjectiveCoverDualHomotopyEquiv.inv 2).hom
        coordinateProjectiveCoverCochainClass := by
  have hnat := HomologicalComplex.homologyπ_naturality
    coordinateProjectiveCoverDualHomotopyEquiv.inv 2
  have hcomp :
      coordinateProjectiveCoverCocycle ≫
          HomologicalComplex.cyclesMap coordinateProjectiveCoverDualHomotopyEquiv.inv 2 ≫
          (SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex.homologyπ 2 =
          coordinateProjectiveCoverCocycle ≫
          coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.homologyπ 2 ≫
          HomologicalComplex.homologyMap
            coordinateProjectiveCoverDualHomotopyEquiv.inv 2 := by
    simpa only [Category.assoc] using
      congrArg (fun f ↦ coordinateProjectiveCoverCocycle ≫ f) hnat.symm
  simpa only [coordinateHyperplaneExplicitOrdinaryCochainClass,
    coordinateHyperplaneExplicitOrdinaryCocycle,
    coordinateProjectiveCoverCochainClass, Category.assoc,
    ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom hcomp 1

/-- Restriction of the transferred ordinary cocycle back to the coordinate Čech model is the
class of the literal winding/overlap cocycle. -/
lemma coordinateHyperplaneExplicitOrdinaryCochainClass_toCech :
    (HomologicalComplex.homologyMap
      (HomologicalComplex.linearDualMap coordinateProjectiveCoverToSingular) 2).hom
        coordinateHyperplaneExplicitOrdinaryCochainClass =
      coordinateProjectiveCoverCochainClass := by
  rw [← coordinateProjectiveCoverDualHomotopyEquiv_hom,
    coordinateHyperplaneExplicitOrdinaryCochainClass_eq_homologyMap_inv]
  change (coordinateProjectiveCoverDualHomotopyEquiv.toHomologyIso 2).hom.hom
      ((coordinateProjectiveCoverDualHomotopyEquiv.toHomologyIso 2).inv.hom
        coordinateProjectiveCoverCochainClass) = coordinateProjectiveCoverCochainClass
  exact ConcreteCategory.congr_hom
    (coordinateProjectiveCoverDualHomotopyEquiv.toHomologyIso 2).inv_hom_id
    coordinateProjectiveCoverCochainClass

lemma coordinateHyperplaneExplicitOrdinaryRawCochain_closed :
    ((SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex.d 2 3).hom
      coordinateHyperplaneExplicitOrdinaryRawCochain = 0 :=
  by
    change ((SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex.d 2 3).hom
      (((SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex.iCycles 2).hom
        (coordinateHyperplaneExplicitOrdinaryCocycle.hom 1)) = 0
    rw [← ConcreteCategory.comp_apply,
      (SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex.iCycles_d]
    rfl

/-- Taking the cohomology class directly from the displayed raw singular cochain recovers the
class defined above from its explicit factorization through the cycle object. -/
lemma coordinateHyperplaneExplicitOrdinaryRawCochain_cochainCohomologyClass :
    cochainCohomologyClass ℚ analyticPlaneTop 2
        coordinateHyperplaneExplicitOrdinaryRawCochain
        coordinateHyperplaneExplicitOrdinaryRawCochain_closed =
      coordinateHyperplaneExplicitOrdinaryCochainClass := by
  let K := (SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex
  let x := (cochainCycle ℚ analyticPlaneTop 2
      coordinateHyperplaneExplicitOrdinaryRawCochain
      coordinateHyperplaneExplicitOrdinaryRawCochain_closed).hom 1
  let y := coordinateHyperplaneExplicitOrdinaryCocycle.hom 1
  have hxy : x = y := by
    apply (ModuleCat.mono_iff_injective (K.iCycles 2)).mp inferInstance
    change (K.iCycles 2).hom x = (K.iCycles 2).hom y
    have hx : (K.iCycles 2).hom x =
        coordinateHyperplaneExplicitOrdinaryRawCochain := by
      dsimp [x, cochainCycle]
      rw [← ConcreteCategory.comp_apply, K.liftCycles_i]
      simp [cochainElementHom]
    rw [hx]
    rfl
  change (K.homologyπ 2).hom x = (K.homologyπ 2).hom y
  exact congrArg (K.homologyπ 2).hom hxy

/-! The ordinary cochain can be sent directly through the proved Betti comparison.  This is
the same class as the earlier supported construction, but the definition now exhibits the
singular cochain and its differential explicitly. -/

noncomputable def coordinateHyperplaneExplicitHypercohomologyClass_of_literalCochain
    [T2Space (ComplexPoint planeOver)]
    [∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U] :
    H^2(planeOver; ℚ) := by
  letI : IsIntegral planeOver.left := by
    change IsIntegral plane
    infer_instance
  letI : Smooth planeOver.hom := by
    change Smooth planeOver.hom
    infer_instance
  letI : SmoothOfRelativeDimension 2 planeOver.hom := by
    change SmoothOfRelativeDimension 2 planeOver.hom
    infer_instance
  exact hypercohomologyClassOfSingularCochain_of_smoothOfRelativeDimension
    planeOver 2 2 coordinateHyperplaneExplicitOrdinaryRawCochain
      coordinateHyperplaneExplicitOrdinaryRawCochain_closed

set_option maxHeartbeats 1000000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit supported cocycle has the same ordinary singular class as the ambient coordinate
Čech cocycle.  The two minus signs are exposed: canonical cone-to-absolute inclusion is the
negative connecting map, while the explicit singular connecting calculation is also negative. -/
lemma coordinateHyperplaneExplicitOrdinarySingularClass_eq_coordinateProjectiveCoverSingularClass :
    coordinateHyperplaneExplicitOrdinarySingularClass =
      coordinateProjectiveCoverSingularClass := by
  let K := SingularChainComplex ℚ analyticPlaneTop
  let f := coordinateProjectiveCoverToSingular
  let e := HomologicalComplex.linearDualHomologyEquiv K 2
  letI : QuasiIso f := projectiveCover_rationalNormalizedCechToSingular_quasiIso
  apply e.symm.injective
  apply (HomologicalComplex.linearDualCohomologyEquivOfQuasiIso f 2).injective
  rw [HomologicalComplex.linearDualCohomologyEquivOfQuasiIso_apply,
    HomologicalComplex.linearDualCohomologyEquivOfQuasiIso_apply]
  have hr :
      (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap f) 2).hom
          (e.symm coordinateProjectiveCoverSingularClass) =
        coordinateProjectiveCoverCochainClass := by
    rw [show e.symm coordinateProjectiveCoverSingularClass =
        coordinateProjectiveCoverSingularCochainClass by
      dsimp [coordinateProjectiveCoverSingularClass, e, K]
      exact (HomologicalComplex.linearDualHomologyEquiv
        (SingularChainComplex ℚ analyticPlaneTop) 2).symm_apply_apply _]
    rw [← HomologicalComplex.linearDualCohomologyEquivOfQuasiIso_apply]
    rw [show coordinateProjectiveCoverSingularCochainClass =
        (HomologicalComplex.linearDualCohomologyEquivOfQuasiIso f 2).symm
          coordinateProjectiveCoverCochainClass by
      rfl]
    exact (HomologicalComplex.linearDualCohomologyEquivOfQuasiIso f 2).apply_symm_apply _
  rw [hr]
  let a := coordinateHyperplaneRelativeSingularConeClass
  let b := (relativeDualCochainHomologyIsoCone ℚ coordinateHyperplaneSupportPair 2).inv.hom a
  let ec := (relativeDualCochainShortComplexNat ℚ coordinateHyperplaneSupportPair).X₂.extendHomologyIso
    ComplexShape.embeddingUpNat (j := 2) (j' := (2 : ℤ)) rfl
  have hclass :
      e.symm coordinateHyperplaneExplicitOrdinarySingularClass =
        ec.hom.hom ((HomologicalComplex.homologyMap
          (relativeDualCochainShortComplexInt ℚ coordinateHyperplaneSupportPair).f (2 : ℤ)).hom b) := by
    apply e.injective
    rw [e.apply_symm_apply]
    change coordinateHyperplaneExplicitOrdinarySingularClass = _
    change AlgebraicTopology.Singular.relativeCohomologyToAbsolute ℚ
      coordinateHyperplaneSupportPair 2
      (relativeCochainConeCohomologyEquivCanonical ℚ coordinateHyperplaneSupportPair 2 a) = _
    rw [← relativeCochainConeCohomologyEquivCanonical_toAbsolute]
    rfl
  rw [hclass]
  let S := relativeDualCochainShortComplexInt ℚ coordinateHyperplaneSupportPair
  let T := CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ coordinateHyperplaneSupportPair)
  let H := HomologicalComplex.homologyFunctor (ModuleCat ℚ) ℤᵘᵖ 0
  have hcanon :
      (relativeCochainConeHomologyIsoDualRelativeInt ℚ coordinateHyperplaneSupportPair 2).hom ≫
          HomologicalComplex.homologyMap S.f (2 : ℤ) =
        (relativeDualCochainHomologyIsoCone ℚ coordinateHyperplaneSupportPair 2).inv ≫
          HomologicalComplex.homologyMap S.f (2 : ℤ) := by
    exact relativeCochainCone_legacy_canonical_inclusion ℚ coordinateHyperplaneSupportPair 2
  have hincl := relativeCochainConeHomologyIsoDualRelativeInt_inclusion
    ℚ coordinateHyperplaneSupportPair 2
  have hpos :
      (HomologicalComplex.homologyMap S.f (2 : ℤ)).hom b =
        -(H.shiftMap (CochainComplex.mappingCone.triangle
          (relativeCochainRestrictionInt ℚ coordinateHyperplaneSupportPair)).mor₃
          ((2 : ℤ) - 1) (2 : ℤ) (by omega)).hom a := by
    have hc := ConcreteCategory.congr_hom hcanon a
    have hi := ConcreteCategory.congr_hom hincl a
    dsimp [S, b, H, T] at hc hi ⊢
    rw [hc.symm]
    have hneg := congrArg Neg.neg hi
    simp only [neg_neg] at hneg
    change (HomologicalComplex.homologyMap S.f 2).hom
      ((relativeCochainConeHomologyIsoDualRelativeInt ℚ coordinateHyperplaneSupportPair 2).hom.hom a) =
      - (H.shiftMap (CochainComplex.mappingCone.triangle
        (relativeCochainRestrictionInt ℚ coordinateHyperplaneSupportPair)).mor₃
        ((2 : ℤ) - 1) (2 : ℤ) (by omega)).hom a at hneg
    exact hneg
  let φ := HomologicalComplex.linearDualMap f
  let eK := (SingularChainComplex ℚ analyticPlaneTop).linearDualCochainComplex.extendHomologyIso
    ComplexShape.embeddingUpNat (j := 2) (j' := (2 : ℤ)) rfl
  let eL := coordinateHyperplaneAmbientCechTotal.linearDualCochainComplex.extendHomologyIso
    ComplexShape.embeddingUpNat (j := 2) (j' := (2 : ℤ)) rfl
  have hmapInt :
      (HomologicalComplex.homologyMap
        (RelativeCechConeComparison.dualMapInt f) (ComplexShape.embeddingUpNat.f 2)).hom
          ((HomologicalComplex.homologyMap S.f (2 : ℤ)).hom b) =
        coordinateProjectiveCoverCochainIntClass := by
    rw [hpos, map_neg]
    change -(HomologicalComplex.homologyMap
      (RelativeCechConeComparison.dualMapInt coordinateProjectiveCoverToSingular)
      (ComplexShape.embeddingUpNat.f 2)).hom
        ((H.shiftMap
          (CochainComplex.mappingCone.triangle
            (relativeCochainRestrictionInt ℚ coordinateHyperplaneSupportPair)).mor₃
          (ComplexShape.embeddingUpNat.f 1) (ComplexShape.embeddingUpNat.f 2) (by norm_num)).hom a) =
      coordinateProjectiveCoverCochainIntClass
    have hconn := congrArg Neg.neg
      coordinateHyperplaneRelativeSingularConnecting_toCech
    simpa [f, H, neg_neg] using hconn
  have hnat := HomologicalComplex.extendHomologyIso_hom_naturality φ
    ComplexShape.embeddingUpNat (j := 2) (j' := (2 : ℤ)) rfl
  have hnat' := ConcreteCategory.congr_hom hnat
    ((HomologicalComplex.homologyMap S.f (2 : ℤ)).hom b)
  simp only [ConcreteCategory.comp_apply] at hnat'
  change eL.hom.hom
      ((HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
        (ComplexShape.embeddingUpNat.f 2)).hom
        ((HomologicalComplex.homologyMap S.f (2 : ℤ)).hom b)) =
    (HomologicalComplex.homologyMap φ 2).hom
      (ec.hom.hom ((HomologicalComplex.homologyMap S.f (2 : ℤ)).hom b)) at hnat'
  have hmapExt :
      (HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
        (ComplexShape.embeddingUpNat.f 2)).hom
        ((HomologicalComplex.homologyMap S.f (2 : ℤ)).hom b) =
      coordinateProjectiveCoverCochainIntClass := by
    simpa [φ, f, RelativeCechConeComparison.dualMapInt] using hmapInt
  rw [← hnat', hmapExt, coordinateProjectiveCoverCochainIntClass_toNat]

/-- The chain-level transferred cocycle represents exactly the singular cochain-complex class
obtained from the coordinate Čech cocycle. -/
lemma coordinateHyperplaneExplicitOrdinaryCochainClass_eq_coordinateProjectiveCoverSingularCochainClass :
    coordinateHyperplaneExplicitOrdinaryCochainClass =
      coordinateProjectiveCoverSingularCochainClass := by
  letI : QuasiIso coordinateProjectiveCoverToSingular :=
    projectiveCover_rationalNormalizedCechToSingular_quasiIso
  letI : QuasiIso (HomologicalComplex.linearDualMap
      coordinateProjectiveCoverToSingular) :=
    HomologicalComplex.linearDualMap_quasiIso coordinateProjectiveCoverToSingular
  apply (ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap
    (HomologicalComplex.linearDualMap coordinateProjectiveCoverToSingular) 2)).mp
      inferInstance
  rw [coordinateHyperplaneExplicitOrdinaryCochainClass_toCech]
  rw [← HomologicalComplex.linearDualCohomologyEquivOfQuasiIso_apply]
  symm
  change (HomologicalComplex.linearDualCohomologyEquivOfQuasiIso
      coordinateProjectiveCoverToSingular 2)
      ((HomologicalComplex.linearDualCohomologyEquivOfQuasiIso
        coordinateProjectiveCoverToSingular 2).symm coordinateProjectiveCoverCochainClass) =
    coordinateProjectiveCoverCochainClass
  exact (HomologicalComplex.linearDualCohomologyEquivOfQuasiIso
    coordinateProjectiveCoverToSingular 2).apply_symm_apply _

/-- The displayed ordinary singular cochain represents the ordinary class obtained by forgetting
support from the explicit relative Čech--singular cocycle. -/
lemma coordinateHyperplaneExplicitOrdinaryRawCochain_class :
    (ordinarySingularCohomologyEquivCohomology ℚ analyticPlaneTop 2)
      coordinateHyperplaneExplicitOrdinaryCochainClass =
      coordinateHyperplaneExplicitOrdinarySingularClass := by
  rw [coordinateHyperplaneExplicitOrdinaryCochainClass_eq_coordinateProjectiveCoverSingularCochainClass]
  change coordinateProjectiveCoverSingularClass =
    coordinateHyperplaneExplicitOrdinarySingularClass
  exact
    coordinateHyperplaneExplicitOrdinarySingularClass_eq_coordinateProjectiveCoverSingularClass.symm

set_option maxRecDepth 100000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Betti comparison sends the hypercohomology class constructed directly from the displayed
ordinary singular cochain to the previously constructed explicit ordinary singular class. -/
lemma planeBettiComparison_coordinateHyperplaneExplicitHypercohomologyClass_of_literalCochain
    [T2Space (ComplexPoint analyticPlane)]
    [∀ U : TopologicalSpace.Opens (ComplexPoint analyticPlane), ParacompactSpace U]
    [T2Space (ComplexPoint planeOver)]
    [∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U] :
    AlgebraicGeometry.ProjectivePlane.planeBettiComparison_of_smoothOfRelativeDimension
        coordinateHyperplaneExplicitHypercohomologyClass_of_literalCochain =
      coordinateHyperplaneExplicitOrdinarySingularClass := by
  change (AlgebraicGeometry.ComplexPoint.rationalCohomologyEquivSingularCohomology_of_smoothOfRelativeDimension
      planeOver 2 2)
      ((AlgebraicGeometry.ComplexPoint.rationalCohomologyEquivSingularCohomology_of_smoothOfRelativeDimension
        planeOver 2 2).symm
        (ordinarySingularCohomologyEquivCohomology ℚ analyticPlaneTop 2
          (cochainCohomologyClass ℚ analyticPlaneTop 2
            coordinateHyperplaneExplicitOrdinaryRawCochain
            coordinateHyperplaneExplicitOrdinaryRawCochain_closed))) = _
  rw [Equiv.apply_symm_apply]
  rw [coordinateHyperplaneExplicitOrdinaryRawCochain_cochainCohomologyClass]
  exact coordinateHyperplaneExplicitOrdinaryRawCochain_class

/-- Transport the explicit ordinary singular class to constant-sheaf hypercohomology.  The
only hypotheses here are the separatedness and hereditary-paracompactness hypotheses required
by the proved Betti comparison; no cycle-class or Chern-class statement is used. -/
noncomputable def coordinateHyperplaneExplicitHypercohomologyClass_of_topologicalHypotheses
    [T2Space (ComplexPoint analyticPlane)]
    [∀ U : TopologicalSpace.Opens (ComplexPoint analyticPlane), ParacompactSpace U] :
    H2 := by
  letI : T2Space (ComplexPoint planeOver) := by
    change T2Space (ComplexPoint analyticPlane)
    infer_instance
  letI : ∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U := by
    change ∀ U : TopologicalSpace.Opens (ComplexPoint analyticPlane), ParacompactSpace U
    infer_instance
  exact (AlgebraicGeometry.ProjectivePlane.planeBettiComparison_of_smoothOfRelativeDimension).symm
    coordinateHyperplaneExplicitOrdinarySingularClass

/-- The same hypercohomology class with the standard projective direct-`Proj` topological
hypotheses discharged.  The only input is projectivity of the chosen direct-`Proj` structure
morphism; the hyperplane smoothness/projectivity assumptions are not used in this explicit
singular construction. -/
noncomputable def coordinateHyperplaneExplicitHypercohomologyClass_of_isProjective
    : H2 := by
  letI : IsProjective analyticPlane.hom := by
    change IsProjective planeOver.hom
    infer_instance
  letI : SmoothOfRelativeDimension 2 analyticPlane.hom := by
    change SmoothOfRelativeDimension 2 planeOver.hom
    infer_instance
  letI : T2Space (ComplexPoint analyticPlane) :=
    @IsProjective.complexPoint_t2Space analyticPlane inferInstance
  letI : ∀ U : TopologicalSpace.Opens (ComplexPoint analyticPlane), ParacompactSpace U :=
    fun U ↦ ComplexPoint.openParacompactSpace_of_smoothOfRelativeDimension analyticPlane 2 U
  exact coordinateHyperplaneExplicitHypercohomologyClass_of_topologicalHypotheses

/-- The direct literal-cochain construction with the same canonical projective topological
instances used by `coordinateHyperplaneExplicitHypercohomologyClass_of_isProjective`. -/
noncomputable def coordinateHyperplaneExplicitHypercohomologyClass_of_literalCochain_isProjective
    [IsProjective planeOver.hom] : H2 := by
  letI : T2Space (ComplexPoint planeOver) :=
    @IsProjective.complexPoint_t2Space planeOver inferInstance
  letI : ∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U :=
    fun U ↦ ComplexPoint.openParacompactSpace_of_smoothOfRelativeDimension planeOver 2 U
  exact coordinateHyperplaneExplicitHypercohomologyClass_of_literalCochain

set_option maxRecDepth 100000 in
@[simp]
lemma planeBettiComparison_coordinateHyperplaneExplicitHypercohomologyClass
    [T2Space (ComplexPoint analyticPlane)]
    [∀ U : TopologicalSpace.Opens (ComplexPoint analyticPlane), ParacompactSpace U]
    [T2Space (ComplexPoint planeOver)]
    [∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U] :
    AlgebraicGeometry.ProjectivePlane.planeBettiComparison_of_smoothOfRelativeDimension
      (coordinateHyperplaneExplicitHypercohomologyClass_of_topologicalHypotheses) =
      coordinateHyperplaneExplicitOrdinarySingularClass := by
  exact (AlgebraicGeometry.ProjectivePlane.planeBettiComparison_of_smoothOfRelativeDimension).apply_symm_apply _

set_option maxRecDepth 100000 in
/-- The hypercohomology class obtained directly from the displayed singular cochain is exactly
the earlier class obtained from the supported relative Čech--singular construction. -/
lemma coordinateHyperplaneExplicitHypercohomologyClass_of_literalCochain_eq_of_topologicalHypotheses
    [T2Space (ComplexPoint analyticPlane)]
    [∀ U : TopologicalSpace.Opens (ComplexPoint analyticPlane), ParacompactSpace U]
    [T2Space (ComplexPoint planeOver)]
    [∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U] :
    coordinateHyperplaneExplicitHypercohomologyClass_of_literalCochain =
      coordinateHyperplaneExplicitHypercohomologyClass_of_topologicalHypotheses := by
  apply AlgebraicGeometry.ProjectivePlane.planeBettiComparison_of_smoothOfRelativeDimension.injective
  rw [planeBettiComparison_coordinateHyperplaneExplicitHypercohomologyClass_of_literalCochain,
    planeBettiComparison_coordinateHyperplaneExplicitHypercohomologyClass]

set_option maxRecDepth 100000 in
/-- With the canonical topological instances supplied by projectivity, the hypercohomology class
constructed directly from the literal global singular cochain is the existing explicit class. -/
lemma coordinateHyperplaneExplicitHypercohomologyClass_of_literalCochain_isProjective_eq
    [IsProjective planeOver.hom] :
    coordinateHyperplaneExplicitHypercohomologyClass_of_literalCochain_isProjective =
      coordinateHyperplaneExplicitHypercohomologyClass_of_isProjective := by
  letI : T2Space (ComplexPoint planeOver) :=
    @IsProjective.complexPoint_t2Space planeOver inferInstance
  letI : ∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U :=
    fun U ↦ ComplexPoint.openParacompactSpace_of_smoothOfRelativeDimension planeOver 2 U
  letI : T2Space (ComplexPoint analyticPlane) := by
    change T2Space (ComplexPoint planeOver)
    infer_instance
  letI : ∀ U : TopologicalSpace.Opens (ComplexPoint analyticPlane), ParacompactSpace U := by
    change ∀ U : TopologicalSpace.Opens (ComplexPoint planeOver), ParacompactSpace U
    infer_instance
  exact
    coordinateHyperplaneExplicitHypercohomologyClass_of_literalCochain_eq_of_topologicalHypotheses

set_option maxRecDepth 100000 in
@[simp]
lemma planeBettiComparison_coordinateHyperplaneExplicitHypercohomologyClass_of_isProjective
    [IsProjective planeOver.hom] :
    AlgebraicGeometry.ProjectivePlane.planeBettiComparison_of_smoothOfRelativeDimension_canonical
        (coordinateHyperplaneExplicitHypercohomologyClass_of_isProjective) =
      coordinateHyperplaneExplicitOrdinarySingularClass := by
  exact (AlgebraicGeometry.ProjectivePlane.planeBettiComparison_of_smoothOfRelativeDimension_canonical).apply_symm_apply _

/-!
The explicit Čech construction and the normalized smooth-closed construction use the same
dimension-two Betti equivalence.  This is a useful exact reduction: identifying the two
hypercohomology classes is equivalent to identifying their ordinary singular classes.  The
local-normalization comparison and the resulting equality are proved in
`ProjectivePlaneExplicitClassNormalizationContinuation`.
-/

set_option maxRecDepth 100000 in
lemma coordinateHyperplaneExplicitHypercohomologyClass_eq_hyperplaneHypercohomologyClass_iff_singular
    [SmoothOfRelativeDimension 1 hyperplaneOver.hom] :
    coordinateHyperplaneExplicitHypercohomologyClass_of_isProjective =
        AlgebraicGeometry.ProjectivePlane.hyperplaneHypercohomologyClass ↔
      coordinateHyperplaneExplicitOrdinarySingularClass =
        AlgebraicGeometry.ProjectivePlane.hyperplaneOrdinarySingularClass := by
  constructor
  · intro h
    rw [← planeBettiComparison_coordinateHyperplaneExplicitHypercohomologyClass_of_isProjective,
      ← AlgebraicGeometry.ProjectivePlane.planeBettiComparison_hyperplaneHypercohomologyClass]
    exact congrArg
      AlgebraicGeometry.ProjectivePlane.planeBettiComparison_of_smoothOfRelativeDimension_canonical
      h
  · intro h
    apply AlgebraicGeometry.ProjectivePlane.planeBettiComparison_of_smoothOfRelativeDimension_canonical.injective
    rw [planeBettiComparison_coordinateHyperplaneExplicitHypercohomologyClass_of_isProjective,
      AlgebraicGeometry.ProjectivePlane.planeBettiComparison_hyperplaneHypercohomologyClass]
    exact h

end AlgebraicGeometry.ProjectivePlane.CoordinateCharts
