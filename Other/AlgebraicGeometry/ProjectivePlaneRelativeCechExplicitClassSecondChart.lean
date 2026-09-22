import Other.AlgebraicGeometry.ProjectivePlaneRelativeCechExplicitClass

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

/-! ## Pulling the relative Čech model back to the second affine chart -/

/-- The projective three-chart cover pulled back to the second affine chart. -/
def secondChartPulledbackProjectiveCover (i : Fin 3) :
    Set secondChartHyperplanePair.fst :=
  pullbackCover (TopPair.Hom.fst secondChartToCoordinateHyperplaneSupportPair)
    projectiveCover i

/-- The global hyperplane-complement cover pulled back to the punctured second chart. -/
def secondChartPulledbackComplementCover (i : Fin 3) :
    Set secondChartHyperplanePair.snd :=
  pullbackCover (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
    coordinateHyperplaneComplementCover i

/-- The member indexed by `2` of the projective cover pulled back to the second affine
chart is the whole chart.  This is the point-set input for the extra-degeneracy which
contracts the pulled-back ordered Čech direction onto the local chart cocycle. -/
lemma secondChartPulledbackProjectiveCover_two_eq_univ :
    secondChartPulledbackProjectiveCover 2 = Set.univ := by
  ext z
  simp only [secondChartPulledbackProjectiveCover, pullbackCover,
    Set.mem_univ, iff_true]
  change Point.map (openInclusion analyticPlane (chartOpen 2)) z ∈
    Point.overOpen (chartOpen 2)
  exact (ComplexPoint.openEquiv analyticPlane (chartOpen 2) z).2

/-- The same distinguished member is also the whole punctured second chart after pulling
back the complement cover. -/
lemma secondChartPulledbackComplementCover_two_eq_univ :
    secondChartPulledbackComplementCover 2 = Set.univ := by
  ext z
  simp only [secondChartPulledbackComplementCover, pullbackCover,
    coordinateHyperplaneComplementCover, Set.mem_preimage, Set.mem_univ, iff_true]
  change Point.map (openInclusion analyticPlane (chartOpen 2)) z.1 ∈
    Point.overOpen (chartOpen 2)
  exact (ComplexPoint.openEquiv analyticPlane (chartOpen 2) z.1).2

/-- Pulling back the ambient cover and then restricting to the punctured chart gives the
same family as pulling back the global complement cover. -/
lemma secondChartPulledbackComplementCover_eq (i : Fin 3) :
    secondChartPulledbackComplementCover i =
      pullbackCover secondChartHyperplanePair.hom
        secondChartPulledbackProjectiveCover i := by
  ext z
  change (TopPair.Hom.fst secondChartToCoordinateHyperplaneSupportPair)
      (secondChartHyperplanePair.hom z) ∈ projectiveCover i ↔
    (TopPair.Hom.fst secondChartToCoordinateHyperplaneSupportPair)
      (secondChartHyperplanePair.hom z) ∈ projectiveCover i
  rfl

lemma secondChartPulledbackComplementCover_eq_family :
    secondChartPulledbackComplementCover =
      pullbackCover secondChartHyperplanePair.hom
        secondChartPulledbackProjectiveCover := by
  funext i
  exact secondChartPulledbackComplementCover_eq i

abbrev secondChartPulledbackAmbientCechTotal :=
  (rationalOpenCoverIntersectionChainModels secondChartHyperplanePair.fst
    secondChartPulledbackProjectiveCover).cechTotal TupleClass.strictMono

abbrev secondChartPulledbackComplementCechTotal :=
  (rationalOpenCoverIntersectionChainModels secondChartHyperplanePair.snd
    secondChartPulledbackComplementCover).cechTotal TupleClass.strictMono

/-- The literal singleton-`2` section from singular chains on the second affine chart into its
pulled-back normalized projective Čech total. -/
def secondChartAmbientCechUniversalMemberSection :
    (TopCat.toSSet.obj secondChartHyperplanePair.fst).chainComplex
        (ModuleCat.of ℚ ℚ) ⟶
      secondChartPulledbackAmbientCechTotal :=
  rationalOpenCoverUniversalMemberSection secondChartHyperplanePair.fst
    secondChartPulledbackProjectiveCover 2
    secondChartPulledbackProjectiveCover_two_eq_univ

/-- The corresponding singleton-`2` section on the punctured second chart. -/
def secondChartComplementCechUniversalMemberSection :
    (TopCat.toSSet.obj secondChartHyperplanePair.snd).chainComplex
        (ModuleCat.of ℚ ℚ) ⟶
      secondChartPulledbackComplementCechTotal :=
  rationalOpenCoverUniversalMemberSection secondChartHyperplanePair.snd
    secondChartPulledbackComplementCover 2
    secondChartPulledbackComplementCover_two_eq_univ

/-- Normalized Čech chains on the pulled-back ambient cover map to the global ambient
normalized Čech chains. -/
def secondChartAmbientCechMap :
    secondChartPulledbackAmbientCechTotal ⟶ coordinateHyperplaneAmbientCechTotal :=
  rationalPullbackCoverNormalizedTotalMap
    (TopPair.Hom.fst secondChartToCoordinateHyperplaneSupportPair) projectiveCover

/-- Normalized Čech chains on the pulled-back complement cover map to the global complement
normalized Čech chains. -/
def secondChartComplementCechMap :
    secondChartPulledbackComplementCechTotal ⟶ coordinateHyperplaneComplementCechTotal :=
  rationalPullbackCoverNormalizedTotalMap
    (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
      coordinateHyperplaneComplementCover

/-- Restriction from the pulled-back complement Čech chains to the pulled-back ambient
Čech chains. -/
def secondChartPulledbackComplementToAmbientCechMap :
    secondChartPulledbackComplementCechTotal ⟶ secondChartPulledbackAmbientCechTotal :=
  rationalPullbackCoverNormalizedTotalMap secondChartHyperplanePair.hom
    secondChartPulledbackProjectiveCover

/-- The singleton sections on the punctured and unpunctured second chart form the expected
chain square.  The proof transports only along the proved equality between the displayed
complement cover and the literal pullback cover. -/
lemma secondChartUniversalMemberSection_square :
    SSet.chainComplexMap
        (TopCat.toSSet.map secondChartHyperplanePair.hom)
        (ModuleCat.of ℚ ℚ) ≫
      secondChartAmbientCechUniversalMemberSection =
    secondChartComplementCechUniversalMemberSection ≫
      secondChartPulledbackComplementToAmbientCechMap := by
  unfold secondChartAmbientCechUniversalMemberSection
    secondChartComplementCechUniversalMemberSection
    secondChartPulledbackComplementToAmbientCechMap
  cases secondChartPulledbackComplementCover_eq_family
  exact rationalOpenCoverUniversalMemberSection_naturality
    secondChartHyperplanePair.fst secondChartHyperplanePair.snd
    secondChartHyperplanePair.hom secondChartPulledbackProjectiveCover 2
    secondChartPulledbackProjectiveCover_two_eq_univ

/-- On every cover intersection, the two composites from the punctured second chart to the
global projective plane agree. -/
lemma secondChartPullbackOpenCoverIntersection_square (s : Finset (Fin 3)) :
    pullbackOpenCoverIntersectionMap secondChartHyperplanePair.hom
        secondChartPulledbackProjectiveCover s ≫
      pullbackOpenCoverIntersectionMap
        (TopPair.Hom.fst secondChartToCoordinateHyperplaneSupportPair)
        projectiveCover s =
    pullbackOpenCoverIntersectionMap
        (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
        coordinateHyperplaneComplementCover s ≫
      pullbackOpenCoverIntersectionMap coordinateHyperplaneSupportPair.hom
        projectiveCover s := by
  ext z
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The preceding point-set square induces a square of local singular-chain models. -/
lemma secondChartRelativeCechLocalSquare :
    rationalPullbackCoverLocalMap secondChartHyperplanePair.hom
        secondChartPulledbackProjectiveCover ≫
      rationalPullbackCoverLocalMap
        (TopPair.Hom.fst secondChartToCoordinateHyperplaneSupportPair) projectiveCover =
    rationalPullbackCoverLocalMap
        (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
        coordinateHyperplaneComplementCover ≫
      rationalPullbackCoverLocalMap coordinateHyperplaneSupportPair.hom projectiveCover := by
  apply NatTrans.ext
  funext s
  change
    SSet.chainComplexMap
        (TopCat.toSSet.map (pullbackOpenCoverIntersectionMap
          secondChartHyperplanePair.hom secondChartPulledbackProjectiveCover s.unop.1))
        (ModuleCat.of ℚ ℚ) ≫
      SSet.chainComplexMap
        (TopCat.toSSet.map (pullbackOpenCoverIntersectionMap
          (TopPair.Hom.fst secondChartToCoordinateHyperplaneSupportPair)
          projectiveCover s.unop.1)) (ModuleCat.of ℚ ℚ) =
    SSet.chainComplexMap
        (TopCat.toSSet.map (pullbackOpenCoverIntersectionMap
          (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
          coordinateHyperplaneComplementCover s.unop.1)) (ModuleCat.of ℚ ℚ) ≫
      SSet.chainComplexMap
        (TopCat.toSSet.map (pullbackOpenCoverIntersectionMap
          coordinateHyperplaneSupportPair.hom projectiveCover s.unop.1))
        (ModuleCat.of ℚ ℚ)
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  let a₀ := pullbackOpenCoverIntersectionMap secondChartHyperplanePair.hom
    secondChartPulledbackProjectiveCover s.unop.1
  let a₁ := pullbackOpenCoverIntersectionMap
    (TopPair.Hom.fst secondChartToCoordinateHyperplaneSupportPair)
    projectiveCover s.unop.1
  let b₀ := pullbackOpenCoverIntersectionMap
    (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
    coordinateHyperplaneComplementCover s.unop.1
  let b₁ := pullbackOpenCoverIntersectionMap coordinateHyperplaneSupportPair.hom
    projectiveCover s.unop.1
  change F.map (TopCat.toSSet.map a₀) ≫ F.map (TopCat.toSSet.map a₁) =
    F.map (TopCat.toSSet.map b₀) ≫ F.map (TopCat.toSSet.map b₁)
  calc
    _ = F.map (TopCat.toSSet.map a₀ ≫ TopCat.toSSet.map a₁) := by
      rw [F.map_comp]
    _ = F.map (TopCat.toSSet.map (a₀ ≫ a₁)) := by
      rw [TopCat.toSSet.map_comp]
    _ = F.map (TopCat.toSSet.map (b₀ ≫ b₁)) := by
      exact congrArg (fun h ↦ F.map (TopCat.toSSet.map h)) (by
        simpa [a₀, a₁, b₀, b₁] using
          secondChartPullbackOpenCoverIntersection_square s.unop.1)
    _ = F.map (TopCat.toSSet.map b₀ ≫ TopCat.toSSet.map b₁) := by
      rw [TopCat.toSSet.map_comp]
    _ = _ := by rw [F.map_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The local square remains commutative after forming normalized ordered Čech bicomplexes. -/
lemma secondChartRelativeCechBicomplexSquare :
    rationalPullbackCoverNormalizedBicomplexMap secondChartHyperplanePair.hom
        secondChartPulledbackProjectiveCover ≫
      rationalPullbackCoverNormalizedBicomplexMap
        (TopPair.Hom.fst secondChartToCoordinateHyperplaneSupportPair) projectiveCover =
    rationalPullbackCoverNormalizedBicomplexMap
        (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
        coordinateHyperplaneComplementCover ≫
      rationalPullbackCoverNormalizedBicomplexMap
        coordinateHyperplaneSupportPair.hom projectiveCover := by
  unfold rationalPullbackCoverNormalizedBicomplexMap
  rw [← AlgebraicTopology.SupportChainModels.Hom.cechMap_comp,
    secondChartRelativeCechLocalSquare,
    AlgebraicTopology.SupportChainModels.Hom.cechMap_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The normalized total Čech maps form the chain square required for the relative-cone
comparison. -/
lemma secondChartRelativeCechSquare :
    secondChartPulledbackComplementToAmbientCechMap ≫ secondChartAmbientCechMap =
      secondChartComplementCechMap ≫ coordinateHyperplaneComplementToAmbientCechMap := by
  unfold secondChartPulledbackComplementToAmbientCechMap secondChartAmbientCechMap
    secondChartComplementCechMap coordinateHyperplaneComplementToAmbientCechMap
    rationalPullbackCoverNormalizedTotalMap
  let a₀ := rationalPullbackCoverNormalizedBicomplexMap secondChartHyperplanePair.hom
    secondChartPulledbackProjectiveCover
  let a₁ := rationalPullbackCoverNormalizedBicomplexMap
    (TopPair.Hom.fst secondChartToCoordinateHyperplaneSupportPair) projectiveCover
  let b₀ := rationalPullbackCoverNormalizedBicomplexMap
    (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
    coordinateHyperplaneComplementCover
  let b₁ := rationalPullbackCoverNormalizedBicomplexMap
    coordinateHyperplaneSupportPair.hom projectiveCover
  change HomologicalComplex₂.total.map a₀ (ComplexShape.down ℕ) ≫
      HomologicalComplex₂.total.map a₁ (ComplexShape.down ℕ) =
    HomologicalComplex₂.total.map b₀ (ComplexShape.down ℕ) ≫
      HomologicalComplex₂.total.map b₁ (ComplexShape.down ℕ)
  calc
    _ = HomologicalComplex₂.total.map (a₀ ≫ a₁) (ComplexShape.down ℕ) :=
      (HomologicalComplex₂.total.map_comp a₀ a₁ (ComplexShape.down ℕ)).symm
    _ = HomologicalComplex₂.total.map (b₀ ≫ b₁) (ComplexShape.down ℕ) := by
      exact congrArg (fun k ↦ HomologicalComplex₂.total.map k (ComplexShape.down ℕ))
        secondChartRelativeCechBicomplexSquare
    _ = _ := HomologicalComplex₂.total.map_comp b₀ b₁ (ComplexShape.down ℕ)

/-- The contravariant map from the global coordinate-hyperplane relative Čech cone to
the relative Čech cone of the cover pulled back to the second affine chart. -/
def coordinateHyperplaneToSecondChartRelativeCechConeMap :
    RelativeCechConeComparison.relativeDualCone
        coordinateHyperplaneComplementToAmbientCechMap ⟶
      RelativeCechConeComparison.relativeDualCone
        secondChartPulledbackComplementToAmbientCechMap :=
  RelativeCechConeComparison.comparison
    secondChartPulledbackComplementToAmbientCechMap
    coordinateHyperplaneComplementToAmbientCechMap
    secondChartComplementCechMap secondChartAmbientCechMap
    secondChartRelativeCechSquare
/-- The literal second-chart relative singular cone compared with the normalized Čech cone
of the pulled-back projective cover. -/
def secondChartRelativeCechComparison :
    CochainComplex.mappingCone
        (relativeCochainRestrictionInt ℚ secondChartHyperplanePair) ⟶
      RelativeCechConeComparison.relativeDualCone
        secondChartPulledbackComplementToAmbientCechMap :=
  rationalTopPairCoverRelativeCochainConeComparison
    secondChartHyperplanePair secondChartPulledbackProjectiveCover

noncomputable instance secondChartRelativeCechComparison_quasiIso :
    QuasiIso secondChartRelativeCechComparison :=
  rationalTopPairCoverRelativeCochainConeComparison_quasiIso
    secondChartHyperplanePair secondChartPulledbackProjectiveCover
    (isOpen_pullbackCover
      (TopPair.Hom.fst secondChartToCoordinateHyperplaneSupportPair)
      projectiveCover isOpen_projectiveCover)
    (iUnion_pullbackCover
      (TopPair.Hom.fst secondChartToCoordinateHyperplaneSupportPair)
      projectiveCover iUnion_projectiveCover)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality of the relative Čech--singular comparison for restriction to the second affine
chart.  This is the specialization of `RelativeCechConeComparison.comparison_naturality` to
the four concrete normalized Čech and singular chain maps above. -/
lemma coordinateHyperplaneRelativeCechComparison_secondChart_naturality :
    coordinateHyperplaneRelativeCechComparison ≫
        coordinateHyperplaneToSecondChartRelativeCechConeMap =
      relativeCochainConeMap ℚ secondChartToCoordinateHyperplaneSupportPair ≫
        secondChartRelativeCechComparison := by
  let sG := ((chainPairFunctor ℚ).obj coordinateHyperplaneSupportPair).hom
  let sL := ((chainPairFunctor ℚ).obj secondChartHyperplanePair).hom
  let rS₀ := ((chainPairFunctor ℚ).map
    secondChartToCoordinateHyperplaneSupportPair).left
  let rS₁ := ((chainPairFunctor ℚ).map
    secondChartToCoordinateHyperplaneSupportPair).right
  let qG₀ := rationalOpenCoverNormalizedCechTotalToSingular
    coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
  let qG₁ := rationalOpenCoverNormalizedCechTotalToSingular
    coordinateHyperplaneSupportPair.fst projectiveCover
  let qL₀ := rationalOpenCoverNormalizedCechTotalToSingular
    secondChartHyperplanePair.snd
      (pullbackCover secondChartHyperplanePair.hom secondChartPulledbackProjectiveCover)
  let qL₁ := rationalOpenCoverNormalizedCechTotalToSingular
    secondChartHyperplanePair.fst secondChartPulledbackProjectiveCover
  exact RelativeCechConeComparison.comparison_naturality
    coordinateHyperplaneComplementToAmbientCechMap sG
    secondChartPulledbackComplementToAmbientCechMap sL
    qG₀ qG₁ qL₀ qL₁
    secondChartComplementCechMap secondChartAmbientCechMap rS₀ rS₁
    (rationalPullbackCoverNormalizedCechToSingular_naturality
      coordinateHyperplaneSupportPair.hom projectiveCover)
    (rationalPullbackCoverNormalizedCechToSingular_naturality
      secondChartHyperplanePair.hom secondChartPulledbackProjectiveCover)
    secondChartRelativeCechSquare
    ((chainPairFunctor ℚ).map secondChartToCoordinateHyperplaneSupportPair).w.symm
    (rationalPullbackCoverNormalizedCechToSingular_naturality
      (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
      coordinateHyperplaneComplementCover)
    (rationalPullbackCoverNormalizedCechToSingular_naturality
      (TopPair.Hom.fst secondChartToCoordinateHyperplaneSupportPair) projectiveCover)
/-! The concrete prepend map for the second pulled-back cover.  This is the geometric map used by
the eventual extra-degeneracy contraction; its construction is fully explicit, including the
support-enlarging intersection isomorphism. -/

noncomputable def secondChartUniversalMemberPrependMap (n : ℕ) :
    (rationalOpenCoverIntersectionChainModels secondChartHyperplanePair.fst
        secondChartPulledbackProjectiveCover).cechObject TupleClass.all n ⟶
      (rationalOpenCoverIntersectionChainModels secondChartHyperplanePair.fst
        secondChartPulledbackProjectiveCover).cechObject TupleClass.all (n + 1) :=
  universalMemberPrependMap secondChartHyperplanePair.fst
    secondChartPulledbackProjectiveCover 2 n
    secondChartPulledbackProjectiveCover_two_eq_univ

/-! The singleton sections also give a comparison in the reverse direction, from the
pulled-back relative Čech cone to the literal relative singular-cochain cone.  Unlike an
abstract inverse obtained from `asIso`, this map is concrete enough to evaluate the global
coordinate cocycle on the distinguished chart member. -/

noncomputable def secondChartRelativeCechSectionComparison :
    RelativeCechConeComparison.relativeDualCone
        secondChartPulledbackComplementToAmbientCechMap ⟶
      CochainComplex.mappingCone
        (relativeCochainRestrictionInt ℚ secondChartHyperplanePair) := by
  let s := ((chainPairFunctor ℚ).obj secondChartHyperplanePair).hom
  change RelativeCechConeComparison.relativeDualCone
      secondChartPulledbackComplementToAmbientCechMap ⟶
    RelativeCechConeComparison.relativeDualCone s
  exact RelativeCechConeComparison.comparison
    s secondChartPulledbackComplementToAmbientCechMap
    secondChartComplementCechUniversalMemberSection
    secondChartAmbientCechUniversalMemberSection
    (by
      change SSet.chainComplexMap
          (TopCat.toSSet.map secondChartHyperplanePair.hom)
          (ModuleCat.of ℚ ℚ) ≫
            secondChartAmbientCechUniversalMemberSection =
        secondChartComplementCechUniversalMemberSection ≫
          secondChartPulledbackComplementToAmbientCechMap
      exact secondChartUniversalMemberSection_square)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The ordinary Čech comparison followed by the distinguished-singleton comparison is
strictly the identity.  Thus the latter is the actual inverse on cohomology, without a chosen
inverse or an extra comparison hypothesis. -/
lemma secondChartRelativeCechComparison_comp_sectionComparison :
    secondChartRelativeCechComparison ≫
        secondChartRelativeCechSectionComparison = 𝟙 _ := by
  cases secondChartPulledbackComplementCover_eq_family
  let c := rationalPullbackCoverNormalizedTotalMap
    secondChartHyperplanePair.hom secondChartPulledbackProjectiveCover
  let s := SSet.chainComplexMap (TopCat.toSSet.map secondChartHyperplanePair.hom)
    (ModuleCat.of ℚ ℚ)
  let q₀ := rationalOpenCoverNormalizedCechTotalToSingular
    secondChartHyperplanePair.snd
      (pullbackCover secondChartHyperplanePair.hom secondChartPulledbackProjectiveCover)
  let q₁ := rationalOpenCoverNormalizedCechTotalToSingular
    secondChartHyperplanePair.fst secondChartPulledbackProjectiveCover
  let u₀ := secondChartComplementCechUniversalMemberSection
  let u₁ := secondChartAmbientCechUniversalMemberSection
  have hc : c ≫ q₁ = q₀ ≫ s :=
    rationalPullbackCoverNormalizedCechToSingular_naturality
      secondChartHyperplanePair.hom secondChartPulledbackProjectiveCover
  have hs : s ≫ u₁ = u₀ ≫ c := by
    change SSet.chainComplexMap
        (TopCat.toSSet.map secondChartHyperplanePair.hom)
        (ModuleCat.of ℚ ℚ) ≫
          secondChartAmbientCechUniversalMemberSection =
      secondChartComplementCechUniversalMemberSection ≫
        secondChartPulledbackComplementToAmbientCechMap
    exact secondChartUniversalMemberSection_square
  change RelativeCechConeComparison.comparison c s q₀ q₁ hc ≫
      RelativeCechConeComparison.comparison s c u₀ u₁ hs = 𝟙 _
  unfold RelativeCechConeComparison.comparison
  rw [← CochainComplex.mappingCone.map_comp]
  have huq₁ : u₁ ≫ q₁ = 𝟙 _ := by
    dsimp [u₁, q₁, secondChartAmbientCechUniversalMemberSection]
    exact rationalOpenCoverUniversalMemberSection_comp_toSingular
      secondChartHyperplanePair.fst secondChartPulledbackProjectiveCover 2
      secondChartPulledbackProjectiveCover_two_eq_univ
  have h₁ : RelativeCechConeComparison.dualMapInt q₁ ≫
      RelativeCechConeComparison.dualMapInt u₁ = 𝟙 _ := by
    rw [← RelativeCechConeComparison.dualMapInt_comp, huq₁,
      RelativeCechConeComparison.dualMapInt_id]
  have huq₀ : u₀ ≫ q₀ = 𝟙 _ := by
    dsimp [u₀, q₀, secondChartComplementCechUniversalMemberSection]
    exact rationalOpenCoverUniversalMemberSection_comp_toSingular
      secondChartHyperplanePair.snd
      (pullbackCover secondChartHyperplanePair.hom secondChartPulledbackProjectiveCover) 2
      secondChartPulledbackComplementCover_two_eq_univ
  have h₀ : RelativeCechConeComparison.dualMapInt q₀ ≫
      RelativeCechConeComparison.dualMapInt u₀ = 𝟙 _ := by
    rw [← RelativeCechConeComparison.dualMapInt_comp, huq₀,
      RelativeCechConeComparison.dualMapInt_id]
  simpa [RelativeCechConeComparison.relativeDualCone, s, h₁, h₀] using
    (CochainComplex.mappingCone.map_id
      (RelativeCechConeComparison.dualMapInt s))

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the global ambient degree-two functional on the distinguished singleton
section of the second pulled-back chart gives zero.  This is the ambient component of the
raw local comparison. -/
lemma secondChartAmbientSection_globalFunctional_zero :
    secondChartAmbientCechUniversalMemberSection.f 2 ≫
      secondChartAmbientCechMap.f 2 ≫
        coordinateProjectiveCoverTotalFunctional = 0 := by
  unfold secondChartAmbientCechUniversalMemberSection
    rationalOpenCoverUniversalMemberSection
    secondChartAmbientCechMap rationalPullbackCoverNormalizedTotalMap
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
second chart. -/
lemma secondChartComplementUniversalMemberToLocal_eq_id :
    (openCoverUniversalMemberIso secondChartHyperplanePair.snd
        (pullbackCover
          (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
          coordinateHyperplaneComplementCover) 2
        secondChartPulledbackComplementCover_two_eq_univ).inv ≫
      pullbackOpenCoverIntersectionMap
        (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
        coordinateHyperplaneComplementCover
        (tupleSupport (singletonStrictCechTuple (2 : Fin 3)).1) ≫
      complementCoverSingletonTwoToSecondChartComplement = 𝟙 _ := by
  apply (cancel_epi (openCoverUniversalMemberIso secondChartHyperplanePair.snd
    (pullbackCover (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
      coordinateHyperplaneComplementCover) 2
    secondChartPulledbackComplementCover_two_eq_univ).hom).mp
  simp only [Iso.hom_inv_id_assoc, Category.comp_id]
  rw [openCoverUniversalMemberIso_hom]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply (ComplexPoint.openHomeomorph analyticPlane (chartOpen 2)).injective
  apply Subtype.ext
  change Point.map (openInclusion analyticPlane (chartOpen 2))
      (complementCoverSingletonToChart 2
        (pullbackOpenCoverIntersectionMap
          (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
          coordinateHyperplaneComplementCover
          (tupleSupport (singletonStrictCechTuple (2 : Fin 3)).1) z)) =
    Point.map (openInclusion analyticPlane (chartOpen 2)) z.1.1
  rw [complementCoverSingletonToChart_map_openInclusion]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The distinguished complement-member chain section, followed by the global singleton map,
evaluates the global singleton winding functional as the literal first normal winding cochain. -/
lemma secondChartComplementSection_singletonWinding :
    (rationalOpenCoverUniversalMemberChainMap secondChartHyperplanePair.snd
        (pullbackCover
          (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
          coordinateHyperplaneComplementCover) 2
        secondChartPulledbackComplementCover_two_eq_univ).f 1 ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map (pullbackOpenCoverIntersectionMap
          (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
          coordinateHyperplaneComplementCover
          (tupleSupport (singletonStrictCechTuple (2 : Fin 3)).1)))
        (ModuleCat.of ℚ ℚ)).f 1 ≫
      complementCoverSingletonTwoWindingTuple =
    ChernWinding.windingIntegerCochain
      secondNormalOnComplement secondNormalOnComplement_ne_zero := by
  dsimp [complementCoverSingletonTwoWindingTuple]
  unfold complementCoverSingletonTwoWinding
    rationalOpenCoverUniversalMemberChainMap
  change
    (SSet.chainComplexMap
        (TopCat.toSSet.map (openCoverUniversalMemberIso secondChartHyperplanePair.snd
          (pullbackCover
            (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
            coordinateHyperplaneComplementCover) 2
          secondChartPulledbackComplementCover_two_eq_univ).inv)
        (ModuleCat.of ℚ ℚ)).f 1 ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map (pullbackOpenCoverIntersectionMap
          (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
          coordinateHyperplaneComplementCover
          (tupleSupport (singletonStrictCechTuple (2 : Fin 3)).1)))
        (ModuleCat.of ℚ ℚ)).f 1 ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map complementCoverSingletonTwoToSecondChartComplement)
        (ModuleCat.of ℚ ℚ)).f 1 ≫
      ChernWinding.windingIntegerCochain
        secondNormalOnComplement secondNormalOnComplement_ne_zero = _
  have hchain := congrArg
    (fun h ↦ SSet.chainComplexMap (TopCat.toSSet.map h) (ModuleCat.of ℚ ℚ))
    secondChartComplementUniversalMemberToLocal_eq_id
  unfold SSet.chainComplexMap at hchain
  simp only [Functor.map_comp] at hchain
  rw [TopCat.toSSet.map_id] at hchain
  have hchain' := hchain.trans
    (((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map_id _)
  have hf := congrArg (fun k ↦ k.f 1 ≫
    ChernWinding.windingIntegerCochain
      secondNormalOnComplement secondNormalOnComplement_ne_zero) hchain'
  simpa only [SSet.chainComplexMap, HomologicalComplex.comp_f, Category.assoc,
    HomologicalComplex.id_f, Category.id_comp] using hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The full global complement functional, pulled back along the distinguished second-chart
singleton section, is the literal first normal winding cochain.  In particular, the pair
correction part disappears because the section lands in outer Cech degree zero. -/
lemma secondChartComplementSection_globalFunctional :
    secondChartComplementCechUniversalMemberSection.f 1 ≫
      secondChartComplementCechMap.f 1 ≫
        coordinateHyperplaneComplementFullFunctional =
      ChernWinding.windingIntegerCochain
        secondNormalOnComplement secondNormalOnComplement_ne_zero := by
  unfold secondChartComplementCechUniversalMemberSection
    rationalOpenCoverUniversalMemberSection
    secondChartComplementCechMap rationalPullbackCoverNormalizedTotalMap
  simp only [Category.assoc]
  rw [HomologicalComplex₂.ιTotal_map_assoc]
  rw [coordinateHyperplaneComplementFullFunctional_singleton]
  unfold rationalOpenCoverUniversalMemberColumnMap
    rationalPullbackCoverNormalizedBicomplexMap
  simp only [HomologicalComplex.comp_f, Category.assoc]
  let M := fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
    (rationalOpenCoverIntersectionChainModels secondChartHyperplanePair.snd
      secondChartPulledbackComplementCover).model (tupleSupport b.1)
  let N := fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
    coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1)
  let eta : ∀ b, M b ⟶ N b := fun b ↦
    SSet.chainComplexMap
      (TopCat.toSSet.map (pullbackOpenCoverIntersectionMap
        (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
        coordinateHyperplaneComplementCover (tupleSupport b.1)))
      (ModuleCat.of ℚ ℚ)
  have hsigma :
      Sigma.ι M (singletonStrictCechTuple (2 : Fin 3)) ≫
          SupportChainModels.Hom.cechObjectMap
            (rationalPullbackCoverLocalMap
              (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
              coordinateHyperplaneComplementCover)
            TupleClass.strictMono 0 =
        eta (singletonStrictCechTuple (2 : Fin 3)) ≫
          Sigma.ι N (singletonStrictCechTuple (2 : Fin 3)) := by
    unfold SupportChainModels.Hom.cechObjectMap
    exact Limits.Sigma.ι_map _ _
  have hsigma2 := congrArg (fun k ↦ k.f 1) hsigma
  simp only [HomologicalComplex.comp_f] at hsigma2
  have hsigma2_assoc := congrArg
    (fun k ↦ k ≫ coordinateHyperplaneComplementSingletonDegreeDesc) hsigma2
  simp only [Category.assoc] at hsigma2_assoc
  let u := rationalOpenCoverUniversalMemberChainMap secondChartHyperplanePair.snd
    secondChartPulledbackComplementCover 2
    secondChartPulledbackComplementCover_two_eq_univ
  change u.f 1 ≫
      (Sigma.ι M (singletonStrictCechTuple (2 : Fin 3))).f 1 ≫
        ((rationalPullbackCoverLocalMap
          (TopPair.Hom.snd secondChartToCoordinateHyperplaneSupportPair)
          coordinateHyperplaneComplementCover).cechObjectMap
          TupleClass.strictMono 0).f 1 ≫
          coordinateHyperplaneComplementSingletonDegreeDesc = _
  have htotal := congrArg (fun k ↦ u.f 1 ≫ k) hsigma2_assoc
  rw [htotal]
  have hdesc :
      (Sigma.ι N (singletonStrictCechTuple (2 : Fin 3))).f 1 ≫
          coordinateHyperplaneComplementSingletonDegreeDesc =
        complementCoverSingletonTwoWindingTuple := by
    let a2 : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} :=
      ⟨![2], by decide⟩
    have ha : singletonStrictCechTuple (2 : Fin 3) = a2 := by
      apply Subtype.ext
      rfl
    cases ha
    dsimp [a2, N]
    exact coordinateHyperplaneComplementSingletonDegreeDesc_secondChart
  rw [hdesc]
  exact secondChartComplementSection_singletonWinding

set_option backward.isDefEq.respectTransparency false in
/-- On the extended integer-indexed dual complexes, the complement component of the global
relative Cech cocycle evaluates under the distinguished second-chart section to the literal
extended winding cochain. -/
lemma secondChartComplementSection_globalCochainInt :
    (RelativeCechConeComparison.dualMapInt
        secondChartComplementCechUniversalMemberSection).f
        (ComplexShape.embeddingUpNat.f 1)
      ((RelativeCechConeComparison.dualMapInt secondChartComplementCechMap).f
        (ComplexShape.embeddingUpNat.f 1)
        (coordinateHyperplaneComplementFullPartIntHom.hom 1)) =
      ChernWinding.extendedWindingIntegerCochainElement
        (X := secondChartHyperplanePair)
        secondNormalOnComplement secondNormalOnComplement_ne_zero := by
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
      (secondChartComplementCechMap.f 1
        (secondChartComplementCechUniversalMemberSection.f 1 x)) =
    (ChernWinding.windingIntegerCochain
      secondNormalOnComplement secondNormalOnComplement_ne_zero).hom x
  have hx := LinearMap.congr_fun
    (congrArg (fun f ↦ f.hom) secondChartComplementSection_globalFunctional) x
  simpa only [LinearMap.coe_comp, Function.comp_apply,
    HomologicalComplex.comp_f, ModuleCat.hom_comp,
    ConcreteCategory.comp_apply] using hx

set_option backward.isDefEq.respectTransparency false in
/-- The extended dual of the second-chart distinguished singleton section annihilates the
ambient component of the global coordinate cocycle. -/
lemma secondChartAmbientSection_globalCochainInt_zero :
    (RelativeCechConeComparison.dualMapInt
        secondChartAmbientCechUniversalMemberSection).f
        (ComplexShape.embeddingUpNat.f 2)
      ((RelativeCechConeComparison.dualMapInt secondChartAmbientCechMap).f
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
  have hz : (secondChartAmbientCechUniversalMemberSection.f 2 ≫
      secondChartAmbientCechMap.f 2 ≫
        coordinateProjectiveCoverTotalFunctional).hom = 0 :=
    congrArg (fun f ↦ f.hom) secondChartAmbientSection_globalFunctional_zero
  have hzdual :
      (secondChartAmbientCechUniversalMemberSection.f 2).hom.dualMap
        ((secondChartAmbientCechMap.f 2).hom.dualMap
          coordinateProjectiveCoverCochain) = 0 := by
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hz x
    simpa only [coordinateProjectiveCoverCochain,
      LinearMap.dualMap_apply', LinearMap.coe_comp,
      Function.comp_apply, HomologicalComplex.comp_f, ModuleCat.hom_comp,
      LinearMap.zero_apply] using hx
  rw [hzdual, map_zero]
set_option backward.isDefEq.respectTransparency false in
/-- Pulling the explicit global relative Čech cochain to the second chart and then evaluating
on its distinguished cover member gives the literal local winding cocycle.  The final
`XIsoOfEq.inv` is the explicit transport from the predecessor degree `f 2 - 1` to `f 1`;
no reduction of the internal `mappingCone.X` arithmetic is used. -/
theorem secondChartSectionComparison_global_raw_transport :
    let localCone := CochainComplex.mappingCone
      (relativeCochainRestrictionInt ℚ secondChartHyperplanePair)
    ((localCone.XIsoOfEq embeddingUpNat_one_eq_two_sub_one).inv.hom
      (secondChartRelativeCechSectionComparison.f
        (ComplexShape.embeddingUpNat.f 2 - 1)
        (coordinateHyperplaneToSecondChartRelativeCechConeMap.f
          (ComplexShape.embeddingUpNat.f 2 - 1)
          coordinateHyperplaneRelativeCechRawElement))) =
      ChernWinding.rawRelativeWindingCochain
        (X := secondChartHyperplanePair)
        secondNormalOnComplement secondNormalOnComplement_ne_zero := by
  dsimp only
  rw [show coordinateHyperplaneToSecondChartRelativeCechConeMap.f
      (ComplexShape.embeddingUpNat.f 2 - 1)
      coordinateHyperplaneRelativeCechRawElement =
    RelativeCechConeComparison.coneCochainOfEq
      (RelativeCechConeComparison.dualMapInt
        secondChartPulledbackComplementToAmbientCechMap)
      (ComplexShape.embeddingUpNat.f 2) (ComplexShape.embeddingUpNat.f 1)
      embeddingUpNat_one_eq_two_sub_one
      ((RelativeCechConeComparison.dualMapInt secondChartAmbientCechMap).f
        (ComplexShape.embeddingUpNat.f 2)
        (coordinateProjectiveCoverCochainIntHom.hom 1))
      ((RelativeCechConeComparison.dualMapInt secondChartComplementCechMap).f
        (ComplexShape.embeddingUpNat.f 1)
        (coordinateHyperplaneComplementFullPartIntHom.hom 1)) from
    RelativeCechConeComparison.comparison_coneCochainOfEq
      secondChartPulledbackComplementToAmbientCechMap
      coordinateHyperplaneComplementToAmbientCechMap
      secondChartComplementCechMap secondChartAmbientCechMap
      secondChartRelativeCechSquare
      (ComplexShape.embeddingUpNat.f 2) (ComplexShape.embeddingUpNat.f 1)
      embeddingUpNat_one_eq_two_sub_one
      (coordinateProjectiveCoverCochainIntHom.hom 1)
      (coordinateHyperplaneComplementFullPartIntHom.hom 1)]
  rw [show secondChartRelativeCechSectionComparison.f
      (ComplexShape.embeddingUpNat.f 2 - 1) _ =
    RelativeCechConeComparison.coneCochainOfEq
      (relativeCochainRestrictionInt ℚ secondChartHyperplanePair)
      (ComplexShape.embeddingUpNat.f 2) (ComplexShape.embeddingUpNat.f 1)
      embeddingUpNat_one_eq_two_sub_one
      ((RelativeCechConeComparison.dualMapInt
        secondChartAmbientCechUniversalMemberSection).f
          (ComplexShape.embeddingUpNat.f 2)
        ((RelativeCechConeComparison.dualMapInt secondChartAmbientCechMap).f
          (ComplexShape.embeddingUpNat.f 2)
          (coordinateProjectiveCoverCochainIntHom.hom 1)))
      ((RelativeCechConeComparison.dualMapInt
        secondChartComplementCechUniversalMemberSection).f
          (ComplexShape.embeddingUpNat.f 1)
        ((RelativeCechConeComparison.dualMapInt secondChartComplementCechMap).f
          (ComplexShape.embeddingUpNat.f 1)
          (coordinateHyperplaneComplementFullPartIntHom.hom 1))) from
    RelativeCechConeComparison.comparison_coneCochainOfEq
      ((chainPairFunctor ℚ).obj secondChartHyperplanePair).hom
      secondChartPulledbackComplementToAmbientCechMap
      secondChartComplementCechUniversalMemberSection
      secondChartAmbientCechUniversalMemberSection
      (by
        change SSet.chainComplexMap
            (TopCat.toSSet.map secondChartHyperplanePair.hom)
            (ModuleCat.of ℚ ℚ) ≫
              secondChartAmbientCechUniversalMemberSection =
          secondChartComplementCechUniversalMemberSection ≫
            secondChartPulledbackComplementToAmbientCechMap
        exact secondChartUniversalMemberSection_square)
      (ComplexShape.embeddingUpNat.f 2) (ComplexShape.embeddingUpNat.f 1)
      embeddingUpNat_one_eq_two_sub_one
      ((RelativeCechConeComparison.dualMapInt secondChartAmbientCechMap).f
        (ComplexShape.embeddingUpNat.f 2)
        (coordinateProjectiveCoverCochainIntHom.hom 1))
      ((RelativeCechConeComparison.dualMapInt secondChartComplementCechMap).f
        (ComplexShape.embeddingUpNat.f 1)
        (coordinateHyperplaneComplementFullPartIntHom.hom 1))]
  rw [secondChartAmbientSection_globalCochainInt_zero,
    secondChartComplementSection_globalCochainInt]
  rw [RelativeCechConeComparison.XIsoOfEq_inv_coneCochainOfEq_zero]
  exact
    (ChernWinding.rawRelativeWindingCochain_eq_inr_extendedWindingIntegerCochainElement
      (X := secondChartHyperplanePair)
      secondNormalOnComplement secondNormalOnComplement_ne_zero).symm

/-- The global explicit relative Čech class pulled back to the normalized Čech model on
the second affine chart. -/
noncomputable def coordinateHyperplaneRelativeCechClassOnSecondChart :
    (RelativeCechConeComparison.relativeDualCone
      secondChartPulledbackComplementToAmbientCechMap).homology ((2 : ℤ) - 1) :=
  (HomologicalComplex.homologyMap
    coordinateHyperplaneToSecondChartRelativeCechConeMap ((2 : ℤ) - 1)).hom
      coordinateHyperplaneRelativeCechHomologyClass

set_option backward.isDefEq.respectTransparency false in
/-- Degree-normalized form of `secondChartSectionComparison_global_raw_transport`. -/
lemma secondChartSectionComparison_global_raw :
    secondChartRelativeCechSectionComparison.f
        (ComplexShape.embeddingUpNat.f 1)
      (coordinateHyperplaneToSecondChartRelativeCechConeMap.f
        (ComplexShape.embeddingUpNat.f 1)
        coordinateHyperplaneRelativeCechRawElementDegreeOne) =
      ChernWinding.rawRelativeWindingCochain
        (X := secondChartHyperplanePair)
        secondNormalOnComplement secondNormalOnComplement_ne_zero := by
  have h := secondChartSectionComparison_global_raw_transport
  norm_num [coordinateHyperplaneRelativeCechRawElementDegreeOne,
    ComplexShape.embeddingUpNat_f, HomologicalComplex.XIsoOfEq] at h ⊢
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The preceding evaluation is an equality of the full one-dimensional cochain maps. -/
lemma secondChartSectionComparison_global_cochainHom :
    coordinateHyperplaneRelativeCechCochainHom ≫
        coordinateHyperplaneToSecondChartRelativeCechConeMap.f
          (ComplexShape.embeddingUpNat.f 1) ≫
        secondChartRelativeCechSectionComparison.f
          (ComplexShape.embeddingUpNat.f 1) =
      ChernWinding.rawRelativeWindingCochainHom
        (X := secondChartHyperplanePair)
        secondNormalOnComplement secondNormalOnComplement_ne_zero := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ConcreteCategory.comp_apply]
  have hx :
      (ChernWinding.rawRelativeWindingCochainHom
        (X := secondChartHyperplanePair)
        secondNormalOnComplement secondNormalOnComplement_ne_zero).hom x =
      x • ChernWinding.rawRelativeWindingCochain
        (X := secondChartHyperplanePair)
        secondNormalOnComplement secondNormalOnComplement_ne_zero := by
    simpa [ChernWinding.rawRelativeWindingCochain] using
      (map_smul
        (ChernWinding.rawRelativeWindingCochainHom
          (X := secondChartHyperplanePair)
          secondNormalOnComplement secondNormalOnComplement_ne_zero).hom
        x (1 : ℚ))
  rw [coordinateHyperplaneRelativeCechCochainHom_apply, hx,
    map_smul, map_smul]
  exact congrArg (fun z ↦ x • z) secondChartSectionComparison_global_raw

set_option backward.isDefEq.respectTransparency false in
/-- The raw equality lifts to the corresponding maps into the cycle objects. -/
lemma secondChartSectionComparison_global_cycles :
    coordinateHyperplaneRelativeCechCocycle ≫
        HomologicalComplex.cyclesMap
          coordinateHyperplaneToSecondChartRelativeCechConeMap
          (ComplexShape.embeddingUpNat.f 1) ≫
        HomologicalComplex.cyclesMap secondChartRelativeCechSectionComparison
          (ComplexShape.embeddingUpNat.f 1) =
      ChernWinding.rawRelativeWindingCocycle
        (X := secondChartHyperplanePair)
        secondNormalOnComplement secondNormalOnComplement_ne_zero := by
  apply (cancel_mono ((CochainComplex.mappingCone
    (relativeCochainRestrictionInt ℚ secondChartHyperplanePair)).iCycles
      (ComplexShape.embeddingUpNat.f 1))).1
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
  rw [HomologicalComplex.cyclesMap_i_assoc]
  dsimp [coordinateHyperplaneRelativeCechCocycle,
    ChernWinding.rawRelativeWindingCocycle]
  rw [HomologicalComplex.liftCycles_i_assoc,
    HomologicalComplex.liftCycles_i]
  exact secondChartSectionComparison_global_cochainHom

set_option backward.isDefEq.respectTransparency false in
/-- The distinguished section sends the pulled-back global Čech class to the literal local
winding class. -/
lemma secondChartSectionComparison_homologyMap_global_class :
    (HomologicalComplex.homologyMap secondChartRelativeCechSectionComparison
      (ComplexShape.embeddingUpNat.f 1)).hom
        coordinateHyperplaneRelativeCechClassOnSecondChart =
      secondChartHyperplaneRelativeConeClass := by
  have hπ :
      coordinateHyperplaneRelativeCechCocycle ≫
          HomologicalComplex.cyclesMap
            coordinateHyperplaneToSecondChartRelativeCechConeMap
            (ComplexShape.embeddingUpNat.f 1) ≫
          HomologicalComplex.cyclesMap secondChartRelativeCechSectionComparison
            (ComplexShape.embeddingUpNat.f 1) ≫
          (CochainComplex.mappingCone
            (relativeCochainRestrictionInt ℚ secondChartHyperplanePair)).homologyπ
              (ComplexShape.embeddingUpNat.f 1) =
        ChernWinding.rawRelativeWindingCocycle
            (X := secondChartHyperplanePair)
            secondNormalOnComplement secondNormalOnComplement_ne_zero ≫
          (CochainComplex.mappingCone
            (relativeCochainRestrictionInt ℚ secondChartHyperplanePair)).homologyπ
              (ComplexShape.embeddingUpNat.f 1) := by
    simpa only [Category.assoc] using congrArg
      (fun f ↦ f ≫ (CochainComplex.mappingCone
        (relativeCochainRestrictionInt ℚ secondChartHyperplanePair)).homologyπ
          (ComplexShape.embeddingUpNat.f 1)) secondChartSectionComparison_global_cycles
  have hnat :
      coordinateHyperplaneRelativeCechCocycle ≫
          coordinateHyperplaneRelativeCechCone.homologyπ
            (ComplexShape.embeddingUpNat.f 1) ≫
          HomologicalComplex.homologyMap
            coordinateHyperplaneToSecondChartRelativeCechConeMap
            (ComplexShape.embeddingUpNat.f 1) ≫
          HomologicalComplex.homologyMap secondChartRelativeCechSectionComparison
            (ComplexShape.embeddingUpNat.f 1) =
        coordinateHyperplaneRelativeCechCocycle ≫
          HomologicalComplex.cyclesMap
            coordinateHyperplaneToSecondChartRelativeCechConeMap
            (ComplexShape.embeddingUpNat.f 1) ≫
          HomologicalComplex.cyclesMap secondChartRelativeCechSectionComparison
            (ComplexShape.embeddingUpNat.f 1) ≫
          (CochainComplex.mappingCone
            (relativeCochainRestrictionInt ℚ secondChartHyperplanePair)).homologyπ
              (ComplexShape.embeddingUpNat.f 1) := by
    rw [HomologicalComplex.homologyπ_naturality_assoc]
    simpa only [Category.assoc] using congrArg
      (fun f ↦ coordinateHyperplaneRelativeCechCocycle ≫
        HomologicalComplex.cyclesMap
          coordinateHyperplaneToSecondChartRelativeCechConeMap
          (ComplexShape.embeddingUpNat.f 1) ≫ f)
      (HomologicalComplex.homologyπ_naturality
        (K := RelativeCechConeComparison.relativeDualCone
          secondChartPulledbackComplementToAmbientCechMap)
        (L := CochainComplex.mappingCone
          (relativeCochainRestrictionInt ℚ secondChartHyperplanePair))
        (i := ComplexShape.embeddingUpNat.f 1)
        secondChartRelativeCechSectionComparison)
  change ((coordinateHyperplaneRelativeCechCocycle ≫
      coordinateHyperplaneRelativeCechCone.homologyπ
        (ComplexShape.embeddingUpNat.f 1) ≫
      HomologicalComplex.homologyMap
        coordinateHyperplaneToSecondChartRelativeCechConeMap
        (ComplexShape.embeddingUpNat.f 1) ≫
      HomologicalComplex.homologyMap secondChartRelativeCechSectionComparison
        (ComplexShape.embeddingUpNat.f 1)).hom 1) =
    ((ChernWinding.rawRelativeWindingCocycle
        (X := secondChartHyperplanePair)
        secondNormalOnComplement secondNormalOnComplement_ne_zero ≫
      (CochainComplex.mappingCone
        (relativeCochainRestrictionInt ℚ secondChartHyperplanePair)).homologyπ
          (ComplexShape.embeddingUpNat.f 1)).hom 1)
  rw [ConcreteCategory.congr_hom hnat 1]
  exact ConcreteCategory.congr_hom hπ 1

set_option backward.isDefEq.respectTransparency false in
/-- The pulled-back global Čech class is the image of the literal second-chart winding class.
The reverse singleton comparison is the inverse on homology because the forward comparison is
a quasi-isomorphism and their composite is strictly the identity. -/
lemma coordinateHyperplaneRelativeCechClassOnSecondChart_eq_localWinding :
    coordinateHyperplaneRelativeCechClassOnSecondChart =
      (HomologicalComplex.homologyMap secondChartRelativeCechComparison
        (ComplexShape.embeddingUpNat.f 1)).hom
          secondChartHyperplaneRelativeConeClass := by
  let f := HomologicalComplex.homologyMap secondChartRelativeCechComparison
    (ComplexShape.embeddingUpNat.f 1)
  let s := HomologicalComplex.homologyMap secondChartRelativeCechSectionComparison
    (ComplexShape.embeddingUpNat.f 1)
  have hfs : f ≫ s = 𝟙 _ := by
    have h := congrArg
      (fun k ↦ HomologicalComplex.homologyMap k
        (ComplexShape.embeddingUpNat.f 1))
      secondChartRelativeCechComparison_comp_sectionComparison
    simpa [f, s, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_id] using h
  have hsf : s ≫ f = 𝟙 _ := by
    apply (cancel_epi f).1
    rw [← Category.assoc, hfs, Category.id_comp, Category.comp_id]
  calc
    coordinateHyperplaneRelativeCechClassOnSecondChart =
        (s ≫ f).hom coordinateHyperplaneRelativeCechClassOnSecondChart := by
          rw [hsf]
          rfl
    _ = f.hom (s.hom coordinateHyperplaneRelativeCechClassOnSecondChart) := rfl
    _ = f.hom secondChartHyperplaneRelativeConeClass := by
      rw [secondChartSectionComparison_homologyMap_global_class]
    _ = _ := rfl

/-- The second-chart image of the global singular cone class has, after the local
Čech--singular comparison, exactly the pulled-back global relative Čech class. -/
lemma coordinateHyperplaneRelativeSingularConeClass_secondChart_toCech :
    (HomologicalComplex.homologyMap secondChartRelativeCechComparison
      ((2 : ℤ) - 1)).hom
        ((HomologicalComplex.homologyMap
          (relativeCochainConeMap ℚ secondChartToCoordinateHyperplaneSupportPair)
          ((2 : ℤ) - 1)).hom coordinateHyperplaneRelativeSingularConeClassDegreeTwo) =
      coordinateHyperplaneRelativeCechClassOnSecondChart := by
  have hnat := congrArg
    (fun f ↦ HomologicalComplex.homologyMap f ((2 : ℤ) - 1))
    coordinateHyperplaneRelativeCechComparison_secondChart_naturality
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
  dsimp [coordinateHyperplaneRelativeCechClassOnSecondChart]
  exact hpoint.symm

/-- The second-chart singular restriction identity is equivalent to one concrete local Čech
homology equality.  The latter is now proved from the explicit cochain calculation above; this
iff theorem records the exact transport through the Čech--singular comparison. -/
lemma coordinateHyperplaneRelativeSingularConeClass_restrict_second_iff_localCech :
    (HomologicalComplex.homologyMap
        (relativeCochainConeMap ℚ secondChartToCoordinateHyperplaneSupportPair)
        ((2 : ℤ) - 1)).hom coordinateHyperplaneRelativeSingularConeClassDegreeTwo =
        secondChartHyperplaneRelativeConeClass ↔
      coordinateHyperplaneRelativeCechClassOnSecondChart =
        (HomologicalComplex.homologyMap secondChartRelativeCechComparison
          ((2 : ℤ) - 1)).hom secondChartHyperplaneRelativeConeClass := by
  constructor
  · intro h
    rw [← coordinateHyperplaneRelativeSingularConeClass_secondChart_toCech, h]
  · intro h
    let e := asIso (HomologicalComplex.homologyMap secondChartRelativeCechComparison
      ((2 : ℤ) - 1))
    have heq :
        (HomologicalComplex.homologyMap secondChartRelativeCechComparison
          ((2 : ℤ) - 1)).hom
            ((HomologicalComplex.homologyMap
              (relativeCochainConeMap ℚ secondChartToCoordinateHyperplaneSupportPair)
              ((2 : ℤ) - 1)).hom coordinateHyperplaneRelativeSingularConeClassDegreeTwo) =
          (HomologicalComplex.homologyMap secondChartRelativeCechComparison
            ((2 : ℤ) - 1)).hom secondChartHyperplaneRelativeConeClass := by
      rw [coordinateHyperplaneRelativeSingularConeClass_secondChart_toCech]
      exact h
    have hinv := congrArg (fun z ↦ e.inv.hom z) heq
    simpa [e] using hinv

/-- The global relative singular cone class restricts to the literal second-chart winding
class. -/
lemma coordinateHyperplaneRelativeSingularConeClass_restrict_second :
    (HomologicalComplex.homologyMap
        (relativeCochainConeMap ℚ secondChartToCoordinateHyperplaneSupportPair)
        ((2 : ℤ) - 1)).hom coordinateHyperplaneRelativeSingularConeClassDegreeTwo =
      secondChartHyperplaneRelativeConeClass :=
  coordinateHyperplaneRelativeSingularConeClass_restrict_second_iff_localCech.mpr
    coordinateHyperplaneRelativeCechClassOnSecondChart_eq_localWinding

/-- The explicit supported singular class restricts to the literal winding class on the
second affine chart. -/
lemma coordinateHyperplaneExplicitSupportedSingularClass_restrict_second :
    relativeCohomologyMap ℚ 2 secondChartToCoordinateHyperplaneSupportPair
        coordinateHyperplaneExplicitSupportedSingularClass =
      secondChartHyperplaneRelativeSingularClass :=
  coordinateHyperplaneExplicitSupportedSingularClass_restrict_second_iff_cone.mpr
    coordinateHyperplaneRelativeSingularConeClass_restrict_second

end AlgebraicGeometry.ProjectivePlane.CoordinateCharts
