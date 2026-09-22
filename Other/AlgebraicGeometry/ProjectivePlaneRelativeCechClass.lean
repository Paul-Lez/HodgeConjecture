/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectivePlaneRationalCechCocycle
public import Other.AlgebraicTopology.RelativeCechConeComparison
public import Other.AlgebraicTopology.RationalOpenCoverUniversalMemberNaturality
public import Other.AlgebraicTopology.WindingCochainTransition
public import Other.AlgebraicTopology.WindingRelativeInverse

/-!
# The relative Čech model for the coordinate hyperplane

This file fixes the literal topological pair consisting of the analytic projective plane and
the complement of the scheme-theoretic hyperplane `X₀ = 0`.  It also fixes the pulled-back
three-chart normalized Čech model and its relative cochain cone.

The last part places the two already constructed normal winding cochains in the singleton
columns of the complement Čech complex and constructs the pair-overlap logarithmic corrections
explicitly.  The actual `01`/`02`/`12` restriction identities, triple-overlap coherence, and
the final total-differential compatibility with the restricted ambient cochain are proved in the
companion compatibility module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectivePlane.CoordinateCharts

open AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "analyticPlaneTop" => (TopCat.of (ComplexPoint analyticPlane))

/-- The actual analytic support of the displayed closed immersion `X₀ = 0`. -/
abbrev coordinateHyperplaneAnalyticSupport : Set (ComplexPoint analyticPlane) :=
  Set.range (Point.map hyperplaneOverι)

/-- The literal pair `(ℙ²(ℂ), ℙ²(ℂ) \setminus V(X₀))`. -/
abbrev coordinateHyperplaneSupportPair : TopPair :=
  TopPair.ofSubset (X := analyticPlaneTop) coordinateHyperplaneAnalyticSupportᶜ

/-- The first standard affine chart, together with the complement of `X₀ = 0`, maps to the
global support pair.  The map on the punctured member is well-defined by the proved equality
between the nonvanishing locus of `X₀/X₁` and the inverse image of the hyperplane complement. -/
def firstChartToCoordinateHyperplaneSupportPair :
    firstChartHyperplanePair ⟶ coordinateHyperplaneSupportPair := by
  let j := openInclusion analyticPlane (chartOpen 1)
  refine TopPair.ofHom (TopCat.ofHom ⟨Point.map j, Point.continuous_map j⟩) ?_ ?_
  · let hmem : ∀ z : firstChartHyperplanePair.snd,
        Point.map j z.1 ∈ coordinateHyperplaneAnalyticSupportᶜ := by
      intro z
      exact (mem_firstNormalComplement_iff_not_mem_hyperplane z.1).mp z.2
    exact TopCat.ofHom
      ⟨fun z ↦ ⟨Point.map j z.1, hmem z⟩,
        ((Point.continuous_map j).comp continuous_subtype_val).subtype_mk hmem⟩
  · ext z
    rfl

/-- The second standard affine chart gives the analogous map to the global support pair. -/
def secondChartToCoordinateHyperplaneSupportPair :
    secondChartHyperplanePair ⟶ coordinateHyperplaneSupportPair := by
  let j := openInclusion analyticPlane (chartOpen 2)
  refine TopPair.ofHom (TopCat.ofHom ⟨Point.map j, Point.continuous_map j⟩) ?_ ?_
  · let hmem : ∀ z : secondChartHyperplanePair.snd,
        Point.map j z.1 ∈ coordinateHyperplaneAnalyticSupportᶜ := by
      intro z
      exact (mem_secondNormalComplement_iff_not_mem_hyperplane z.1).mp z.2
    exact TopCat.ofHom
      ⟨fun z ↦ ⟨Point.map j z.1, hmem z⟩,
        ((Point.continuous_map j).comp continuous_subtype_val).subtype_mk hmem⟩
  · ext z
    rfl

/-- Set-level support compatibility of the first chart pair map. -/
lemma firstChartToCoordinateHyperplaneSupportPair_preimage_complement :
    (Point.map (openInclusion analyticPlane (chartOpen 1))) ⁻¹'
        coordinateHyperplaneAnalyticSupportᶜ = firstNormalComplement :=
  firstNormalComplement_eq_preimage_hyperplaneSupportComplement.symm

/-- Set-level support compatibility of the second chart pair map. -/
lemma secondChartToCoordinateHyperplaneSupportPair_preimage_complement :
    (Point.map (openInclusion analyticPlane (chartOpen 2))) ⁻¹'
        coordinateHyperplaneAnalyticSupportᶜ = secondNormalComplement :=
  secondNormalComplement_eq_preimage_hyperplaneSupportComplement.symm

/-- The two maps of support pairs agree on the actual chart overlap.  This is the pair-level
commutativity needed to compare the two local relative winding classes inside a global Čech
class. -/
lemma overlapToFirstChartPair_comp_global_eq_overlapToSecondChartPair_comp_global :
    overlapToFirstChartPair ≫ firstChartToCoordinateHyperplaneSupportPair =
      overlapToSecondChartPair ≫ secondChartToCoordinateHyperplaneSupportPair := by
  apply MorphismProperty.Arrow.Hom.ext
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    change Point.map (openInclusion analyticPlane (chartOpen 1))
        (Point.map overlapToFirstChartOver z.1) =
      Point.map (openInclusion analyticPlane (chartOpen 2))
        (Point.map overlapToSecondChartOver z.1)
    rw [← Point.map_comp_apply, ← Point.map_comp_apply,
      overlapToFirstChartOver_comp_openInclusion,
      overlapToSecondChartOver_comp_openInclusion]
  · change complexAnalytification.map overlapToFirstChartOver ≫
        complexAnalytification.map (openInclusion analyticPlane (chartOpen 1)) =
      complexAnalytification.map overlapToSecondChartOver ≫
        complexAnalytification.map (openInclusion analyticPlane (chartOpen 2))
    rw [← Functor.map_comp, ← Functor.map_comp,
      overlapToFirstChartOver_comp_openInclusion,
      overlapToSecondChartOver_comp_openInclusion]

/-- The pullback of the three standard projective charts to the hyperplane complement. -/
def coordinateHyperplaneComplementCover (i : Fin 3) :
    Set coordinateHyperplaneSupportPair.snd :=
  pullbackCover coordinateHyperplaneSupportPair.hom projectiveCover i

@[simp]
lemma mem_coordinateHyperplaneComplementCover (i : Fin 3)
    (z : coordinateHyperplaneSupportPair.snd) :
    z ∈ coordinateHyperplaneComplementCover i ↔ z.1 ∈ projectiveCover i :=
  Iff.rfl

/-- Rational intersection chains for the ambient three-chart cover. -/
abbrev coordinateHyperplaneAmbientCoverChainModels :=
  rationalOpenCoverIntersectionChainModels analyticPlaneTop projectiveCover

/-- Rational intersection chains for the pulled-back cover of the complement. -/
abbrev coordinateHyperplaneComplementCoverChainModels :=
  rationalOpenCoverIntersectionChainModels coordinateHyperplaneSupportPair.snd
    coordinateHyperplaneComplementCover

/-- The normalized rational Čech total for the ambient projective plane. -/
abbrev coordinateHyperplaneAmbientCechTotal : ChainComplex (ModuleCat ℚ) ℕ :=
  coordinateHyperplaneAmbientCoverChainModels.cechTotal TupleClass.strictMono

/-- The normalized rational Čech total for the hyperplane complement. -/
abbrev coordinateHyperplaneComplementCechTotal : ChainComplex (ModuleCat ℚ) ℕ :=
  coordinateHyperplaneComplementCoverChainModels.cechTotal TupleClass.strictMono

/-- Restriction from complement Čech chains to ambient Čech chains. -/
def coordinateHyperplaneComplementToAmbientCechMap :
    coordinateHyperplaneComplementCechTotal ⟶ coordinateHyperplaneAmbientCechTotal :=
  rationalPullbackCoverNormalizedTotalMap coordinateHyperplaneSupportPair.hom projectiveCover

/-! ## Pulling the relative Čech model back to the first affine chart -/

/-- The projective three-chart cover pulled back to the first affine chart. -/
def firstChartPulledbackProjectiveCover (i : Fin 3) :
    Set firstChartHyperplanePair.fst :=
  pullbackCover (TopPair.Hom.fst firstChartToCoordinateHyperplaneSupportPair)
    projectiveCover i

/-- The global hyperplane-complement cover pulled back to the punctured first chart. -/
def firstChartPulledbackComplementCover (i : Fin 3) :
    Set firstChartHyperplanePair.snd :=
  pullbackCover (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
    coordinateHyperplaneComplementCover i

/-- The member indexed by `1` of the projective cover pulled back to the first affine
chart is the whole chart.  This is the point-set input for the extra-degeneracy which
contracts the pulled-back ordered Čech direction onto the local chart cocycle. -/
lemma firstChartPulledbackProjectiveCover_one_eq_univ :
    firstChartPulledbackProjectiveCover 1 = Set.univ := by
  ext z
  simp only [firstChartPulledbackProjectiveCover, pullbackCover,
    Set.mem_univ, iff_true]
  change Point.map (openInclusion analyticPlane (chartOpen 1)) z ∈
    Point.overOpen (chartOpen 1)
  exact (ComplexPoint.openEquiv analyticPlane (chartOpen 1) z).2

/-- The same distinguished member is also the whole punctured first chart after pulling
back the complement cover. -/
lemma firstChartPulledbackComplementCover_one_eq_univ :
    firstChartPulledbackComplementCover 1 = Set.univ := by
  ext z
  simp only [firstChartPulledbackComplementCover, pullbackCover,
    coordinateHyperplaneComplementCover, Set.mem_preimage, Set.mem_univ, iff_true]
  change Point.map (openInclusion analyticPlane (chartOpen 1)) z.1 ∈
    Point.overOpen (chartOpen 1)
  exact (ComplexPoint.openEquiv analyticPlane (chartOpen 1) z.1).2

/-- Pulling back the ambient cover and then restricting to the punctured chart gives the
same family as pulling back the global complement cover. -/
lemma firstChartPulledbackComplementCover_eq (i : Fin 3) :
    firstChartPulledbackComplementCover i =
      pullbackCover firstChartHyperplanePair.hom
        firstChartPulledbackProjectiveCover i := by
  ext z
  change (TopPair.Hom.fst firstChartToCoordinateHyperplaneSupportPair)
      (firstChartHyperplanePair.hom z) ∈ projectiveCover i ↔
    (TopPair.Hom.fst firstChartToCoordinateHyperplaneSupportPair)
      (firstChartHyperplanePair.hom z) ∈ projectiveCover i
  rfl

lemma firstChartPulledbackComplementCover_eq_family :
    firstChartPulledbackComplementCover =
      pullbackCover firstChartHyperplanePair.hom
        firstChartPulledbackProjectiveCover := by
  funext i
  exact firstChartPulledbackComplementCover_eq i

abbrev firstChartPulledbackAmbientCechTotal :=
  (rationalOpenCoverIntersectionChainModels firstChartHyperplanePair.fst
    firstChartPulledbackProjectiveCover).cechTotal TupleClass.strictMono

abbrev firstChartPulledbackComplementCechTotal :=
  (rationalOpenCoverIntersectionChainModels firstChartHyperplanePair.snd
    firstChartPulledbackComplementCover).cechTotal TupleClass.strictMono

/-- The literal singleton-`1` section from singular chains on the first affine chart into its
pulled-back normalized projective Čech total. -/
def firstChartAmbientCechUniversalMemberSection :
    (TopCat.toSSet.obj firstChartHyperplanePair.fst).chainComplex
        (ModuleCat.of ℚ ℚ) ⟶
      firstChartPulledbackAmbientCechTotal :=
  rationalOpenCoverUniversalMemberSection firstChartHyperplanePair.fst
    firstChartPulledbackProjectiveCover 1
    firstChartPulledbackProjectiveCover_one_eq_univ

/-- The corresponding singleton-`1` section on the punctured first chart. -/
def firstChartComplementCechUniversalMemberSection :
    (TopCat.toSSet.obj firstChartHyperplanePair.snd).chainComplex
        (ModuleCat.of ℚ ℚ) ⟶
      firstChartPulledbackComplementCechTotal :=
  rationalOpenCoverUniversalMemberSection firstChartHyperplanePair.snd
    firstChartPulledbackComplementCover 1
    firstChartPulledbackComplementCover_one_eq_univ

/-- Normalized Čech chains on the pulled-back ambient cover map to the global ambient
normalized Čech chains. -/
def firstChartAmbientCechMap :
    firstChartPulledbackAmbientCechTotal ⟶ coordinateHyperplaneAmbientCechTotal :=
  rationalPullbackCoverNormalizedTotalMap
    (TopPair.Hom.fst firstChartToCoordinateHyperplaneSupportPair) projectiveCover

/-- Normalized Čech chains on the pulled-back complement cover map to the global complement
normalized Čech chains. -/
def firstChartComplementCechMap :
    firstChartPulledbackComplementCechTotal ⟶ coordinateHyperplaneComplementCechTotal :=
  rationalPullbackCoverNormalizedTotalMap
    (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
      coordinateHyperplaneComplementCover

/-- Restriction from the pulled-back complement Čech chains to the pulled-back ambient
Čech chains. -/
def firstChartPulledbackComplementToAmbientCechMap :
    firstChartPulledbackComplementCechTotal ⟶ firstChartPulledbackAmbientCechTotal :=
  rationalPullbackCoverNormalizedTotalMap firstChartHyperplanePair.hom
    firstChartPulledbackProjectiveCover

/-- The singleton sections on the punctured and unpunctured first chart form the expected
chain square.  The proof transports only along the proved equality between the displayed
complement cover and the literal pullback cover. -/
lemma firstChartUniversalMemberSection_square :
    SSet.chainComplexMap
        (TopCat.toSSet.map firstChartHyperplanePair.hom)
        (ModuleCat.of ℚ ℚ) ≫
      firstChartAmbientCechUniversalMemberSection =
    firstChartComplementCechUniversalMemberSection ≫
      firstChartPulledbackComplementToAmbientCechMap := by
  unfold firstChartAmbientCechUniversalMemberSection
    firstChartComplementCechUniversalMemberSection
    firstChartPulledbackComplementToAmbientCechMap
  cases firstChartPulledbackComplementCover_eq_family
  exact rationalOpenCoverUniversalMemberSection_naturality
    firstChartHyperplanePair.fst firstChartHyperplanePair.snd
    firstChartHyperplanePair.hom firstChartPulledbackProjectiveCover 1
    firstChartPulledbackProjectiveCover_one_eq_univ

/-- On every cover intersection, the two composites from the punctured first chart to the
global projective plane agree. -/
lemma firstChartPullbackOpenCoverIntersection_square (s : Finset (Fin 3)) :
    pullbackOpenCoverIntersectionMap firstChartHyperplanePair.hom
        firstChartPulledbackProjectiveCover s ≫
      pullbackOpenCoverIntersectionMap
        (TopPair.Hom.fst firstChartToCoordinateHyperplaneSupportPair)
        projectiveCover s =
    pullbackOpenCoverIntersectionMap
        (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
        coordinateHyperplaneComplementCover s ≫
      pullbackOpenCoverIntersectionMap coordinateHyperplaneSupportPair.hom
        projectiveCover s := by
  ext z
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The preceding point-set square induces a square of local singular-chain models. -/
lemma firstChartRelativeCechLocalSquare :
    rationalPullbackCoverLocalMap firstChartHyperplanePair.hom
        firstChartPulledbackProjectiveCover ≫
      rationalPullbackCoverLocalMap
        (TopPair.Hom.fst firstChartToCoordinateHyperplaneSupportPair) projectiveCover =
    rationalPullbackCoverLocalMap
        (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
        coordinateHyperplaneComplementCover ≫
      rationalPullbackCoverLocalMap coordinateHyperplaneSupportPair.hom projectiveCover := by
  apply NatTrans.ext
  funext s
  change
    SSet.chainComplexMap
        (TopCat.toSSet.map (pullbackOpenCoverIntersectionMap
          firstChartHyperplanePair.hom firstChartPulledbackProjectiveCover s.unop.1))
        (ModuleCat.of ℚ ℚ) ≫
      SSet.chainComplexMap
        (TopCat.toSSet.map (pullbackOpenCoverIntersectionMap
          (TopPair.Hom.fst firstChartToCoordinateHyperplaneSupportPair)
          projectiveCover s.unop.1)) (ModuleCat.of ℚ ℚ) =
    SSet.chainComplexMap
        (TopCat.toSSet.map (pullbackOpenCoverIntersectionMap
          (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
          coordinateHyperplaneComplementCover s.unop.1)) (ModuleCat.of ℚ ℚ) ≫
      SSet.chainComplexMap
        (TopCat.toSSet.map (pullbackOpenCoverIntersectionMap
          coordinateHyperplaneSupportPair.hom projectiveCover s.unop.1))
        (ModuleCat.of ℚ ℚ)
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  let a₀ := pullbackOpenCoverIntersectionMap firstChartHyperplanePair.hom
    firstChartPulledbackProjectiveCover s.unop.1
  let a₁ := pullbackOpenCoverIntersectionMap
    (TopPair.Hom.fst firstChartToCoordinateHyperplaneSupportPair)
    projectiveCover s.unop.1
  let b₀ := pullbackOpenCoverIntersectionMap
    (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
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
          firstChartPullbackOpenCoverIntersection_square s.unop.1)
    _ = F.map (TopCat.toSSet.map b₀ ≫ TopCat.toSSet.map b₁) := by
      rw [TopCat.toSSet.map_comp]
    _ = _ := by rw [F.map_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The local square remains commutative after forming normalized ordered Čech bicomplexes. -/
lemma firstChartRelativeCechBicomplexSquare :
    rationalPullbackCoverNormalizedBicomplexMap firstChartHyperplanePair.hom
        firstChartPulledbackProjectiveCover ≫
      rationalPullbackCoverNormalizedBicomplexMap
        (TopPair.Hom.fst firstChartToCoordinateHyperplaneSupportPair) projectiveCover =
    rationalPullbackCoverNormalizedBicomplexMap
        (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
        coordinateHyperplaneComplementCover ≫
      rationalPullbackCoverNormalizedBicomplexMap
        coordinateHyperplaneSupportPair.hom projectiveCover := by
  unfold rationalPullbackCoverNormalizedBicomplexMap
  rw [← AlgebraicTopology.SupportChainModels.Hom.cechMap_comp,
    firstChartRelativeCechLocalSquare,
    AlgebraicTopology.SupportChainModels.Hom.cechMap_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The normalized total Čech maps form the chain square required for the relative-cone
comparison. -/
lemma firstChartRelativeCechSquare :
    firstChartPulledbackComplementToAmbientCechMap ≫ firstChartAmbientCechMap =
      firstChartComplementCechMap ≫ coordinateHyperplaneComplementToAmbientCechMap := by
  unfold firstChartPulledbackComplementToAmbientCechMap firstChartAmbientCechMap
    firstChartComplementCechMap coordinateHyperplaneComplementToAmbientCechMap
    rationalPullbackCoverNormalizedTotalMap
  let a₀ := rationalPullbackCoverNormalizedBicomplexMap firstChartHyperplanePair.hom
    firstChartPulledbackProjectiveCover
  let a₁ := rationalPullbackCoverNormalizedBicomplexMap
    (TopPair.Hom.fst firstChartToCoordinateHyperplaneSupportPair) projectiveCover
  let b₀ := rationalPullbackCoverNormalizedBicomplexMap
    (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
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
        firstChartRelativeCechBicomplexSquare
    _ = _ := HomologicalComplex₂.total.map_comp b₀ b₁ (ComplexShape.down ℕ)

/-- The contravariant map from the global coordinate-hyperplane relative Čech cone to
the relative Čech cone of the cover pulled back to the first affine chart. -/
def coordinateHyperplaneToFirstChartRelativeCechConeMap :
    RelativeCechConeComparison.relativeDualCone
        coordinateHyperplaneComplementToAmbientCechMap ⟶
      RelativeCechConeComparison.relativeDualCone
        firstChartPulledbackComplementToAmbientCechMap :=
  RelativeCechConeComparison.comparison
    firstChartPulledbackComplementToAmbientCechMap
    coordinateHyperplaneComplementToAmbientCechMap
    firstChartComplementCechMap firstChartAmbientCechMap
    firstChartRelativeCechSquare

/-- The relative normalized Čech cochain cone.  Its degree `n - 1` computes relative degree
`n`, consistently with the repository's singular restriction-cone convention. -/
abbrev coordinateHyperplaneRelativeCechCone : CochainComplex (ModuleCat ℚ) ℤ :=
  RelativeCechConeComparison.relativeDualCone
    coordinateHyperplaneComplementToAmbientCechMap

/-- The canonical comparison from the literal supported singular-cochain cone to the normalized
relative Čech cone. -/
def coordinateHyperplaneRelativeCechComparison :
    CochainComplex.mappingCone
        (relativeCochainRestrictionInt ℚ coordinateHyperplaneSupportPair) ⟶
      coordinateHyperplaneRelativeCechCone :=
  rationalTopPairCoverRelativeCochainConeComparison
    coordinateHyperplaneSupportPair projectiveCover

noncomputable instance coordinateHyperplaneRelativeCechComparison_quasiIso :
    QuasiIso coordinateHyperplaneRelativeCechComparison :=
  rationalTopPairCoverRelativeCochainConeComparison_quasiIso
    coordinateHyperplaneSupportPair projectiveCover
    isOpen_projectiveCover iUnion_projectiveCover

/-- The literal first-chart relative singular cone compared with the normalized Čech cone
of the pulled-back projective cover. -/
def firstChartRelativeCechComparison :
    CochainComplex.mappingCone
        (relativeCochainRestrictionInt ℚ firstChartHyperplanePair) ⟶
      RelativeCechConeComparison.relativeDualCone
        firstChartPulledbackComplementToAmbientCechMap :=
  rationalTopPairCoverRelativeCochainConeComparison
    firstChartHyperplanePair firstChartPulledbackProjectiveCover

noncomputable instance firstChartRelativeCechComparison_quasiIso :
    QuasiIso firstChartRelativeCechComparison :=
  rationalTopPairCoverRelativeCochainConeComparison_quasiIso
    firstChartHyperplanePair firstChartPulledbackProjectiveCover
    (isOpen_pullbackCover
      (TopPair.Hom.fst firstChartToCoordinateHyperplaneSupportPair)
      projectiveCover isOpen_projectiveCover)
    (iUnion_pullbackCover
      (TopPair.Hom.fst firstChartToCoordinateHyperplaneSupportPair)
      projectiveCover iUnion_projectiveCover)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality of the relative Čech--singular comparison for restriction to the first affine
chart.  This is the specialization of `RelativeCechConeComparison.comparison_naturality` to
the four concrete normalized Čech and singular chain maps above. -/
lemma coordinateHyperplaneRelativeCechComparison_firstChart_naturality :
    coordinateHyperplaneRelativeCechComparison ≫
        coordinateHyperplaneToFirstChartRelativeCechConeMap =
      relativeCochainConeMap ℚ firstChartToCoordinateHyperplaneSupportPair ≫
        firstChartRelativeCechComparison := by
  let sG := ((chainPairFunctor ℚ).obj coordinateHyperplaneSupportPair).hom
  let sL := ((chainPairFunctor ℚ).obj firstChartHyperplanePair).hom
  let rS₀ := ((chainPairFunctor ℚ).map
    firstChartToCoordinateHyperplaneSupportPair).left
  let rS₁ := ((chainPairFunctor ℚ).map
    firstChartToCoordinateHyperplaneSupportPair).right
  let qG₀ := rationalOpenCoverNormalizedCechTotalToSingular
    coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
  let qG₁ := rationalOpenCoverNormalizedCechTotalToSingular
    coordinateHyperplaneSupportPair.fst projectiveCover
  let qL₀ := rationalOpenCoverNormalizedCechTotalToSingular
    firstChartHyperplanePair.snd
      (pullbackCover firstChartHyperplanePair.hom firstChartPulledbackProjectiveCover)
  let qL₁ := rationalOpenCoverNormalizedCechTotalToSingular
    firstChartHyperplanePair.fst firstChartPulledbackProjectiveCover
  exact RelativeCechConeComparison.comparison_naturality
    coordinateHyperplaneComplementToAmbientCechMap sG
    firstChartPulledbackComplementToAmbientCechMap sL
    qG₀ qG₁ qL₀ qL₁
    firstChartComplementCechMap firstChartAmbientCechMap rS₀ rS₁
    (rationalPullbackCoverNormalizedCechToSingular_naturality
      coordinateHyperplaneSupportPair.hom projectiveCover)
    (rationalPullbackCoverNormalizedCechToSingular_naturality
      firstChartHyperplanePair.hom firstChartPulledbackProjectiveCover)
    firstChartRelativeCechSquare
    ((chainPairFunctor ℚ).map firstChartToCoordinateHyperplaneSupportPair).w.symm
    (rationalPullbackCoverNormalizedCechToSingular_naturality
      (TopPair.Hom.snd firstChartToCoordinateHyperplaneSupportPair)
      coordinateHyperplaneComplementCover)
    (rationalPullbackCoverNormalizedCechToSingular_naturality
      (TopPair.Hom.fst firstChartToCoordinateHyperplaneSupportPair) projectiveCover)

/-- A singleton intersection in the pulled-back complement cover, mapped to its standard
analytic affine chart. -/
def complementCoverSingletonToChart (i : Fin 3) :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({i} : Finset (Fin 3))) ⟶
      TopCat.of (ComplexPoint (analyticChart i)) :=
  TopCat.ofHom
    { toFun := fun z ↦
        (ComplexPoint.openHomeomorph analyticPlane (chartOpen i)).symm
          ⟨z.1.1, by
            change z.1.1 ∈ projectiveCover i
            exact (mem_openCoverIntersection_iff
              coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
              ({i} : Finset (Fin 3)) z.1).mp z.2 i (by simp)⟩
      continuous_toFun := by
        fun_prop }

lemma complementCoverSingletonToChart_map_openInclusion (i : Fin 3)
    (z : openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({i} : Finset (Fin 3))) :
    Point.map (openInclusion analyticPlane (chartOpen i))
        (complementCoverSingletonToChart i z) = z.1.1 := by
  exact congrArg Subtype.val
    ((ComplexPoint.openHomeomorph analyticPlane (chartOpen i)).apply_symm_apply
      ⟨z.1.1, by
        change z.1.1 ∈ projectiveCover i
        exact (mem_openCoverIntersection_iff
          coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
          ({i} : Finset (Fin 3)) z.1).mp z.2 i (by simp)⟩)

/-! The same point map for an arbitrary pulled-back finite intersection.  We keep this
construction separate from the singleton definitions above so that the pair-overlap correction
cochains below are maps of the actual complement intersections, rather than selected
representatives or abstract identifications. -/

def complementCoverIntersectionToChart (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ s) :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover s) ⟶
      TopCat.of (ComplexPoint (analyticChart i)) :=
  TopCat.ofHom
    { toFun := fun z ↦
        (ComplexPoint.openHomeomorph analyticPlane (chartOpen i)).symm
          ⟨z.1.1, by
            change z.1.1 ∈ projectiveCover i
            exact (mem_openCoverIntersection_iff
              coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
              s z.1).mp z.2 i hi⟩
      continuous_toFun := by
        fun_prop }

lemma complementCoverIntersectionToChart_map_openInclusion
    (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ s)
    (z : openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover s) :
    Point.map (openInclusion analyticPlane (chartOpen i))
        (complementCoverIntersectionToChart s i hi z) = z.1.1 := by
  exact congrArg Subtype.val
    ((ComplexPoint.openHomeomorph analyticPlane (chartOpen i)).apply_symm_apply
      ⟨z.1.1, by
        change z.1.1 ∈ projectiveCover i
        exact (mem_openCoverIntersection_iff
          coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
          s z.1).mp z.2 i hi⟩)

lemma complementCoverIntersectionToChart_naturality
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (i : Fin 3) (hi : i ∈ s)
    (z : openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover t) :
    complementCoverIntersectionToChart s i hi
        (openCoverIntersectionInclusion coordinateHyperplaneSupportPair.snd
          coordinateHyperplaneComplementCover hst z) =
      complementCoverIntersectionToChart t i (hst hi) z := by
  apply (ComplexPoint.openHomeomorph analyticPlane (chartOpen i)).injective
  apply Subtype.ext
  change Point.map (openInclusion analyticPlane (chartOpen i))
      (complementCoverIntersectionToChart s i hi
        (openCoverIntersectionInclusion coordinateHyperplaneSupportPair.snd
          coordinateHyperplaneComplementCover hst z)) =
    Point.map (openInclusion analyticPlane (chartOpen i))
      (complementCoverIntersectionToChart t i (hst hi) z)
  rw [complementCoverIntersectionToChart_map_openInclusion,
    complementCoverIntersectionToChart_map_openInclusion]
  rfl

def complementCoverIntersectionToFirstChartComplement
    (s : Finset (Fin 3)) (hs : (1 : Fin 3) ∈ s) :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover s) ⟶ firstChartHyperplanePair.snd :=
  TopCat.ofHom
    { toFun := fun z ↦ ⟨complementCoverIntersectionToChart s 1 hs z, by
          rw [mem_firstNormalComplement_iff_not_mem_hyperplane]
          rw [complementCoverIntersectionToChart_map_openInclusion]
          exact z.1.2⟩
      continuous_toFun := by
        fun_prop }

def complementCoverIntersectionToSecondChartComplement
    (s : Finset (Fin 3)) (hs : (2 : Fin 3) ∈ s) :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover s) ⟶ secondChartHyperplanePair.snd :=
  TopCat.ofHom
    { toFun := fun z ↦ ⟨complementCoverIntersectionToChart s 2 hs z, by
          rw [mem_secondNormalComplement_iff_not_mem_hyperplane]
          rw [complementCoverIntersectionToChart_map_openInclusion]
          exact z.1.2⟩
      continuous_toFun := by
        fun_prop }

/-- The first normal function pulled back to any complement intersection containing `1`. -/
def complementCoverIntersectionFirstNormal
    (s : Finset (Fin 3)) (hs : (1 : Fin 3) ∈ s) :
    C(TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover s), ℂ) :=
  firstNormalOnComplement.comp
    (ChernWinding.topMap (complementCoverIntersectionToFirstChartComplement s hs))

lemma complementCoverIntersectionFirstNormal_ne_zero
    (s : Finset (Fin 3)) (hs : (1 : Fin 3) ∈ s) :
    ∀ z, complementCoverIntersectionFirstNormal s hs z ≠ 0 := by
  intro z
  exact firstNormalOnComplement_ne_zero _

/-- The second normal function pulled back to any complement intersection containing `2`. -/
def complementCoverIntersectionSecondNormal
    (s : Finset (Fin 3)) (hs : (2 : Fin 3) ∈ s) :
    C(TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover s), ℂ) :=
  secondNormalOnComplement.comp
    (ChernWinding.topMap (complementCoverIntersectionToSecondChartComplement s hs))

lemma complementCoverIntersectionSecondNormal_ne_zero
    (s : Finset (Fin 3)) (hs : (2 : Fin 3) ∈ s) :
    ∀ z, complementCoverIntersectionSecondNormal s hs z ≠ 0 := by
  intro z
  exact secondNormalOnComplement_ne_zero _

/-! ### Literal functions on the three pair intersections -/

/-- The map from a pulled-back complement intersection to the corresponding ambient-cover
intersection. -/
def complementCoverIntersectionToAmbientIntersection (s : Finset (Fin 3)) :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover s) ⟶
      TopCat.of (openCoverIntersection analyticPlaneTop projectiveCover s) :=
  pullbackOpenCoverIntersectionMap coordinateHyperplaneSupportPair.hom projectiveCover s

/-- The `01` complement intersection mapped to the named analytic `01` overlap. -/
def complementCoverPair01ToAnalyticPair :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({0, 1} : Finset (Fin 3))) ⟶
      TopCat.of (ComplexPoint analyticPair01) :=
  complementCoverIntersectionToAmbientIntersection ({0, 1} : Finset (Fin 3)) ≫
    projectiveCoverPair01ToAnalyticPair

/-- The `02` complement intersection mapped to the named analytic `02` overlap. -/
def complementCoverPair02ToAnalyticPair :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({0, 2} : Finset (Fin 3))) ⟶
      TopCat.of (ComplexPoint analyticPair02) :=
  complementCoverIntersectionToAmbientIntersection ({0, 2} : Finset (Fin 3)) ≫
    projectiveCoverPair02ToAnalyticPair

/-- The `12` complement intersection mapped to the actual analytic `12` overlap. -/
def complementCoverPair12ToAnalyticOverlap :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({1, 2} : Finset (Fin 3))) ⟶
      TopCat.of (ComplexPoint analyticOverlap) :=
  complementCoverIntersectionToAmbientIntersection ({1, 2} : Finset (Fin 3)) ≫
    projectiveCoverPair12ToAnalyticPair

lemma complementCoverPair01ToAnalyticPair_map_openInclusion
    (z : openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({0, 1} : Finset (Fin 3))) :
    Point.map (openInclusion analyticPlane pair01Open)
        (complementCoverPair01ToAnalyticPair z) = z.1.1 := by
  let zO : {z : ComplexPoint analyticPlane // z ∈ Point.overOpen pair01Open} :=
    ⟨z.1.1, by
      rw [← projectiveCover_pair01_intersection]
      exact (complementCoverIntersectionToAmbientIntersection
        ({0, 1} : Finset (Fin 3)) z).2⟩
  change Point.map (openInclusion analyticPlane pair01Open)
      ((ComplexPoint.openHomeomorph analyticPlane pair01Open).symm zO) = z.1.1
  exact congrArg Subtype.val
    ((ComplexPoint.openHomeomorph analyticPlane pair01Open).apply_symm_apply zO)

lemma complementCoverPair02ToAnalyticPair_map_openInclusion
    (z : openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({0, 2} : Finset (Fin 3))) :
    Point.map (openInclusion analyticPlane pair02Open)
        (complementCoverPair02ToAnalyticPair z) = z.1.1 := by
  let zO : {z : ComplexPoint analyticPlane // z ∈ Point.overOpen pair02Open} :=
    ⟨z.1.1, by
      rw [← projectiveCover_pair02_intersection]
      exact (complementCoverIntersectionToAmbientIntersection
        ({0, 2} : Finset (Fin 3)) z).2⟩
  change Point.map (openInclusion analyticPlane pair02Open)
      ((ComplexPoint.openHomeomorph analyticPlane pair02Open).symm zO) = z.1.1
  exact congrArg Subtype.val
    ((ComplexPoint.openHomeomorph analyticPlane pair02Open).apply_symm_apply zO)

lemma complementCoverPair12ToAnalyticOverlap_map_openInclusion
    (z : openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({1, 2} : Finset (Fin 3))) :
    Point.map (openInclusion analyticPlane overlapOpen)
        (complementCoverPair12ToAnalyticOverlap z) = z.1.1 := by
  let zO : {z : ComplexPoint analyticPlane // z ∈ Point.overOpen overlapOpen} :=
    ⟨z.1.1, by
      rw [← projectiveCover_pair12_intersection]
      exact (complementCoverIntersectionToAmbientIntersection
        ({1, 2} : Finset (Fin 3)) z).2⟩
  change Point.map (openInclusion analyticPlane overlapOpen)
      ((ComplexPoint.openHomeomorph analyticPlane overlapOpen).symm zO) = z.1.1
  exact congrArg Subtype.val
    ((ComplexPoint.openHomeomorph analyticPlane overlapOpen).apply_symm_apply zO)

lemma complementCoverPair12ToFirstChart_comm
    (z : openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({1, 2} : Finset (Fin 3))) :
    overlapToFirstChart (complementCoverPair12ToAnalyticOverlap z) =
      complementCoverIntersectionToChart ({1, 2} : Finset (Fin 3)) 1 (by simp) z := by
  apply (ComplexPoint.openHomeomorph analyticPlane (chartOpen 1)).injective
  apply Subtype.ext
  change Point.map (openInclusion analyticPlane (chartOpen 1))
      (Point.map overlapToFirstChartOver (complementCoverPair12ToAnalyticOverlap z)) =
    Point.map (openInclusion analyticPlane (chartOpen 1))
      (complementCoverIntersectionToChart ({1, 2} : Finset (Fin 3)) 1 (by simp) z)
  rw [← Point.map_comp_apply, overlapToFirstChartOver_comp_openInclusion,
    complementCoverPair12ToAnalyticOverlap_map_openInclusion,
    complementCoverIntersectionToChart_map_openInclusion]

lemma complementCoverPair12ToSecondChart_comm
    (z : openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({1, 2} : Finset (Fin 3))) :
    overlapToSecondChart (complementCoverPair12ToAnalyticOverlap z) =
      complementCoverIntersectionToChart ({1, 2} : Finset (Fin 3)) 2 (by simp) z := by
  apply (ComplexPoint.openHomeomorph analyticPlane (chartOpen 2)).injective
  apply Subtype.ext
  change Point.map (openInclusion analyticPlane (chartOpen 2))
      (Point.map overlapToSecondChartOver (complementCoverPair12ToAnalyticOverlap z)) =
    Point.map (openInclusion analyticPlane (chartOpen 2))
      (complementCoverIntersectionToChart ({1, 2} : Finset (Fin 3)) 2 (by simp) z)
  rw [← Point.map_comp_apply, overlapToSecondChartOver_comp_openInclusion,
    complementCoverPair12ToAnalyticOverlap_map_openInclusion,
    complementCoverIntersectionToChart_map_openInclusion]

/-! The `01` and `02` pair intersections also map to the punctured affine charts.  The
scheme-theoretic restriction calculations below identify the inverse transition with the actual
normal coordinate; these are the local identities needed by the relative totalization. -/

lemma pair01Open_le_firstChart : pair01Open ≤ chartOpen 1 := by
  exact Proj.basicOpen_mono Grading (MvPolynomial.X 1)
    (MvPolynomial.X 0 * MvPolynomial.X 1) ⟨MvPolynomial.X 0, by ring⟩

lemma pair02Open_le_secondChart : pair02Open ≤ chartOpen 2 := by
  exact Proj.basicOpen_mono Grading (MvPolynomial.X 2)
    (MvPolynomial.X 0 * MvPolynomial.X 2) ⟨MvPolynomial.X 0, by ring⟩

noncomputable def pair01ToFirstChartOver : analyticPair01 ⟶ analyticChart 1 :=
  Over.homMk (plane.homOfLE pair01Open_le_firstChart) (by
    dsimp [analyticPair01, analyticChart, analyticPlane, openScheme]
    rw [← Category.assoc, Scheme.homOfLE_ι])

noncomputable def pair02ToSecondChartOver : analyticPair02 ⟶ analyticChart 2 :=
  Over.homMk (plane.homOfLE pair02Open_le_secondChart) (by
    dsimp [analyticPair02, analyticChart, analyticPlane, openScheme]
    rw [← Category.assoc, Scheme.homOfLE_ι])

noncomputable def pair01ToFirstChart : ComplexPoint analyticPair01 →
    ComplexPoint (analyticChart 1) :=
  Point.map pair01ToFirstChartOver

noncomputable def pair02ToSecondChart : ComplexPoint analyticPair02 →
    ComplexPoint (analyticChart 2) :=
  Point.map pair02ToSecondChartOver

lemma continuous_pair01ToFirstChart : Continuous pair01ToFirstChart :=
  Point.continuous_map pair01ToFirstChartOver

lemma continuous_pair02ToSecondChart : Continuous pair02ToSecondChart :=
  Point.continuous_map pair02ToSecondChartOver

lemma pair01ToFirstChartOver_comp_openInclusion :
    pair01ToFirstChartOver ≫ openInclusion analyticPlane (chartOpen 1) =
      openInclusion analyticPlane pair01Open := by
  apply Over.OverMorphism.ext
  dsimp [pair01ToFirstChartOver, analyticPair01, analyticChart, openScheme,
    analyticPlane, openInclusion]
  exact Scheme.homOfLE_ι plane pair01Open_le_firstChart

lemma pair02ToSecondChartOver_comp_openInclusion :
    pair02ToSecondChartOver ≫ openInclusion analyticPlane (chartOpen 2) =
      openInclusion analyticPlane pair02Open := by
  apply Over.OverMorphism.ext
  dsimp [pair02ToSecondChartOver, analyticPair02, analyticChart, openScheme,
    analyticPlane, openInclusion]
  exact Scheme.homOfLE_ι plane pair02Open_le_secondChart

lemma complementCoverPair01ToFirstChart_comm
    (z : openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({0, 1} : Finset (Fin 3))) :
    pair01ToFirstChart (complementCoverPair01ToAnalyticPair z) =
      complementCoverIntersectionToChart ({0, 1} : Finset (Fin 3)) 1 (by simp) z := by
  apply (ComplexPoint.openHomeomorph analyticPlane (chartOpen 1)).injective
  apply Subtype.ext
  change Point.map (openInclusion analyticPlane (chartOpen 1))
      (Point.map pair01ToFirstChartOver (complementCoverPair01ToAnalyticPair z)) =
    Point.map (openInclusion analyticPlane (chartOpen 1))
      (complementCoverIntersectionToChart ({0, 1} : Finset (Fin 3)) 1 (by simp) z)
  rw [← Point.map_comp_apply, pair01ToFirstChartOver_comp_openInclusion,
    complementCoverPair01ToAnalyticPair_map_openInclusion,
    complementCoverIntersectionToChart_map_openInclusion]

lemma complementCoverPair02ToSecondChart_comm
    (z : openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({0, 2} : Finset (Fin 3))) :
    pair02ToSecondChart (complementCoverPair02ToAnalyticPair z) =
      complementCoverIntersectionToChart ({0, 2} : Finset (Fin 3)) 2 (by simp) z := by
  apply (ComplexPoint.openHomeomorph analyticPlane (chartOpen 2)).injective
  apply Subtype.ext
  change Point.map (openInclusion analyticPlane (chartOpen 2))
      (Point.map pair02ToSecondChartOver (complementCoverPair02ToAnalyticPair z)) =
    Point.map (openInclusion analyticPlane (chartOpen 2))
      (complementCoverIntersectionToChart ({0, 2} : Finset (Fin 3)) 2 (by simp) z)
  rw [← Point.map_comp_apply, pair02ToSecondChartOver_comp_openInclusion,
    complementCoverPair02ToAnalyticPair_map_openInclusion,
    complementCoverIntersectionToChart_map_openInclusion]

set_option maxHeartbeats 600000 in
noncomputable def pair01InverseRestrictionElement :
    HomogeneousLocalization.Away Grading (MvPolynomial.X 0 * MvPolynomial.X 1) :=
  HomogeneousLocalization.awayMap
    (f := MvPolynomial.X 1) (x := MvPolynomial.X 0 * MvPolynomial.X 1)
    Grading coordinateZero_homogeneous (by ring)
    (Other.ProjectiveChart.gen ℂ 1 0)

set_option maxHeartbeats 5000000 in
lemma pair01InverseElement_eq_restriction :
    pair01InverseElement = pair01InverseRestrictionElement := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1))
  dsimp [pair01InverseElement, pair01InverseRestrictionElement,
    Other.ProjectiveChart.gen]
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp
  ring

set_option maxHeartbeats 5000000 in
noncomputable def pair02InverseRestrictionElement :
    HomogeneousLocalization.Away Grading (MvPolynomial.X 0 * MvPolynomial.X 2) :=
  HomogeneousLocalization.awayMap
    (f := MvPolynomial.X 2) (x := MvPolynomial.X 0 * MvPolynomial.X 2)
    Grading coordinateZero_homogeneous (by ring)
    (Other.ProjectiveChart.gen ℂ 2 0)

set_option maxHeartbeats 5000000 in
lemma pair02InverseElement_eq_restriction :
    pair02InverseElement = pair02InverseRestrictionElement := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 2))
  dsimp [pair02InverseElement, pair02InverseRestrictionElement,
    Other.ProjectiveChart.gen]
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp
  ring

set_option maxHeartbeats 5000000 in
lemma pair01InverseGlobalSection_eq_restrict :
    pair01GlobalSection pair01InverseElement =
      plane.presheaf.map (homOfLE pair01Open_le_firstChart).op
        firstNormalGlobalSection := by
  rw [pair01InverseElement_eq_restriction]
  change
    (CommRingCat.ofHom
        (HomogeneousLocalization.awayMap
          (f := MvPolynomial.X 1) (x := MvPolynomial.X 0 * MvPolynomial.X 1)
          Grading coordinateZero_homogeneous (by ring)) ≫
      Proj.awayToSection Grading (MvPolynomial.X 0 * MvPolynomial.X 1)).hom
        (Other.ProjectiveChart.gen ℂ 1 0) =
      (Proj.awayToSection Grading (MvPolynomial.X 1) ≫
        plane.presheaf.map (homOfLE pair01Open_le_firstChart).op).hom
          (Other.ProjectiveChart.gen ℂ 1 0)
  rw [Proj.awayMap_awayToSection Grading coordinateZero_homogeneous (by ring)]
  rfl

set_option maxHeartbeats 5000000 in
lemma pair02InverseGlobalSection_eq_restrict :
    pair02GlobalSection pair02InverseElement =
      plane.presheaf.map (homOfLE pair02Open_le_secondChart).op
        secondNormalGlobalSection := by
  rw [pair02InverseElement_eq_restriction]
  change
    (CommRingCat.ofHom
        (HomogeneousLocalization.awayMap
          (f := MvPolynomial.X 2) (x := MvPolynomial.X 0 * MvPolynomial.X 2)
          Grading coordinateZero_homogeneous (by ring)) ≫
      Proj.awayToSection Grading (MvPolynomial.X 0 * MvPolynomial.X 2)).hom
        (Other.ProjectiveChart.gen ℂ 2 0) =
      (Proj.awayToSection Grading (MvPolynomial.X 2) ≫
        plane.presheaf.map (homOfLE pair02Open_le_secondChart).op).hom
          (Other.ProjectiveChart.gen ℂ 2 0)
  rw [Proj.awayMap_awayToSection Grading coordinateZero_homogeneous (by ring)]
  rfl

set_option maxHeartbeats 5000000 in
lemma pair01InverseValue_eq_firstNormalValue (z : ComplexPoint analyticPair01) :
    Point.evaluate ⊤ (pair01Section pair01InverseElement) z =
      firstNormalValue (pair01ToFirstChart z) := by
  change Point.evaluate ⊤ (pair01Open.topIso.inv
      (pair01GlobalSection pair01InverseElement)) z =
    Point.evaluate ⊤ ((chartOpen 1).topIso.inv firstNormalGlobalSection)
      (Point.map pair01ToFirstChartOver z)
  dsimp only [analyticPair01, analyticChart, analyticPlane, openScheme] at z ⊢
  rw [evaluate_topIso_inv (X := Over.mk structureMap) pair01Open
      (pair01GlobalSection pair01InverseElement) z,
    evaluate_topIso_inv (X := Over.mk structureMap) (chartOpen 1)
      firstNormalGlobalSection (Point.map pair01ToFirstChartOver z)]
  rw [← Point.map_comp_apply, pair01ToFirstChartOver_comp_openInclusion,
    pair01InverseGlobalSection_eq_restrict]
  exact (Point.evaluate_res pair01Open_le_firstChart firstNormalGlobalSection
    (Point.map (openInclusion analyticPlane pair01Open) z)
    (openEquiv analyticPlane pair01Open z).2).symm

set_option maxHeartbeats 5000000 in
lemma pair02InverseValue_eq_secondNormalValue (z : ComplexPoint analyticPair02) :
    Point.evaluate ⊤ (pair02Section pair02InverseElement) z =
      secondNormalCoordinate (pair02ToSecondChart z) := by
  change Point.evaluate ⊤ (pair02Open.topIso.inv
      (pair02GlobalSection pair02InverseElement)) z =
    Point.evaluate ⊤ ((chartOpen 2).topIso.inv secondNormalGlobalSection)
      (Point.map pair02ToSecondChartOver z)
  dsimp only [analyticPair02, analyticChart, analyticPlane, openScheme] at z ⊢
  rw [evaluate_topIso_inv (X := Over.mk structureMap) pair02Open
      (pair02GlobalSection pair02InverseElement) z,
    evaluate_topIso_inv (X := Over.mk structureMap) (chartOpen 2)
      secondNormalGlobalSection (Point.map pair02ToSecondChartOver z)]
  rw [← Point.map_comp_apply, pair02ToSecondChartOver_comp_openInclusion,
    pair02InverseGlobalSection_eq_restrict]
  exact (Point.evaluate_res pair02Open_le_secondChart secondNormalGlobalSection
    (Point.map (openInclusion analyticPlane pair02Open) z)
    (openEquiv analyticPlane pair02Open z).2).symm

set_option maxHeartbeats 5000000 in
lemma pair01InverseValue_eq_inv_pair01Value (z : ComplexPoint analyticPair01) :
    Point.evaluate ⊤ (pair01Section pair01InverseElement) z = (pair01Value z)⁻¹ := by
  apply mul_left_cancel₀ (pair01Value_ne_zero z)
  rw [mul_inv_cancel₀ (pair01Value_ne_zero z)]
  have heval := congrArg
    (fun u ↦ (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom u) pair01Section_mul_inverse
  rw [map_mul, map_one] at heval
  change Point.evaluationHom ⊤ ⟨z, trivial⟩ (pair01Section pair01Element) *
      Point.evaluationHom ⊤ ⟨z, trivial⟩ (pair01Section pair01InverseElement) = 1 at heval
  rw [Point.evaluationHom_apply, Point.evaluationHom_apply] at heval
  simpa only [pair01Value] using heval

set_option maxHeartbeats 5000000 in
lemma pair02InverseValue_eq_inv_pair02Value (z : ComplexPoint analyticPair02) :
    Point.evaluate ⊤ (pair02Section pair02InverseElement) z = (pair02Value z)⁻¹ := by
  apply mul_left_cancel₀ (pair02Value_ne_zero z)
  rw [mul_inv_cancel₀ (pair02Value_ne_zero z)]
  have heval := congrArg
    (fun u ↦ (Point.evaluationHom ⊤ ⟨z, trivial⟩).hom u) pair02Section_mul_inverse
  rw [map_mul, map_one] at heval
  change Point.evaluationHom ⊤ ⟨z, trivial⟩ (pair02Section pair02Element) *
      Point.evaluationHom ⊤ ⟨z, trivial⟩ (pair02Section pair02InverseElement) = 1 at heval
  rw [Point.evaluationHom_apply, Point.evaluationHom_apply] at heval
  simpa only [pair02Value] using heval

/-- The ambient transition `X₁/X₀`, restricted to the actual `01` complement overlap. -/
def complementCoverPair01Transition :
    C(TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({0, 1} : Finset (Fin 3))), ℂ) :=
  pair01Transition.comp (ChernWinding.topMap complementCoverPair01ToAnalyticPair)

lemma complementCoverPair01Transition_ne_zero :
    ∀ z, complementCoverPair01Transition z ≠ 0 :=
  fun z ↦ pair01Transition_ne_zero _

/-- The ambient transition `X₂/X₀`, restricted to the actual `02` complement overlap. -/
def complementCoverPair02Transition :
    C(TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({0, 2} : Finset (Fin 3))), ℂ) :=
  pair02Transition.comp (ChernWinding.topMap complementCoverPair02ToAnalyticPair)

lemma complementCoverPair02Transition_ne_zero :
    ∀ z, complementCoverPair02Transition z ≠ 0 :=
  fun z ↦ pair02Transition_ne_zero _

/-- The literal pointwise inverse of the `01` transition on the pulled-back complement
intersection. -/
def complementCoverPair01InverseTransition :=
  ChernWinding.nowhereZeroContinuousMapInv complementCoverPair01Transition
    complementCoverPair01Transition_ne_zero

lemma complementCoverPair01InverseTransition_ne_zero :
    ∀ z, complementCoverPair01InverseTransition z ≠ 0 :=
  ChernWinding.nowhereZeroContinuousMapInv_ne_zero
    complementCoverPair01Transition complementCoverPair01Transition_ne_zero

/-- On the actual pulled-back `01` intersection, the first affine normal coordinate `X₀/X₁`
is literally the inverse of the ambient transition `X₁/X₀`. -/
lemma complementCoverIntersectionFirstNormal_pair01 :
    complementCoverIntersectionFirstNormal ({0, 1} : Finset (Fin 3)) (by simp) =
      complementCoverPair01InverseTransition := by
  ext z
  change firstNormalValue
      (complementCoverIntersectionToChart ({0, 1} : Finset (Fin 3)) 1 (by simp) z) =
    (pair01Value (complementCoverPair01ToAnalyticPair z))⁻¹
  rw [← complementCoverPair01ToFirstChart_comm]
  exact pair01InverseValue_eq_firstNormalValue
      (complementCoverPair01ToAnalyticPair z) |>.symm.trans
        (pair01InverseValue_eq_inv_pair01Value
          (complementCoverPair01ToAnalyticPair z))

lemma complementCoverPair01_transition_mul_inverse (z) :
    ChernWinding.constantOneContinuousMap
        (TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
          coordinateHyperplaneComplementCover ({0, 1} : Finset (Fin 3)))) z =
      complementCoverPair01Transition z * complementCoverPair01InverseTransition z := by
  change 1 = complementCoverPair01Transition z * (complementCoverPair01Transition z)⁻¹
  exact (mul_inv_cancel₀ (complementCoverPair01Transition_ne_zero z)).symm

/-- The degree-zero principal-log correction for the inverse pair on `01`. -/
def complementCoverPair01Correction :
    (ChernWinding.singularChains (TopCat.of (openCoverIntersection
      coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
      ({0, 1} : Finset (Fin 3))))).X 0 ⟶ ModuleCat.of ℚ ℚ :=
  ChernWinding.pointLogProductDefectVertexCochain
    complementCoverPair01Transition complementCoverPair01InverseTransition
    (ChernWinding.constantOneContinuousMap (TopCat.of (openCoverIntersection
      coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
      ({0, 1} : Finset (Fin 3)))))
    complementCoverPair01Transition_ne_zero
    complementCoverPair01InverseTransition_ne_zero
    (ChernWinding.constantOneContinuousMap_ne_zero _)
    complementCoverPair01_transition_mul_inverse

/-- The raw inverse-transition equation on the actual pulled-back `01` intersection. -/
lemma complementCoverPair01_inverse_localEquation :
    ChernWinding.windingIntegerCochain complementCoverPair01Transition
        complementCoverPair01Transition_ne_zero +
      ChernWinding.windingIntegerCochain complementCoverPair01InverseTransition
        complementCoverPair01InverseTransition_ne_zero =
      (ChernWinding.singularChains (TopCat.of (openCoverIntersection
        coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
        ({0, 1} : Finset (Fin 3))))).d 1 0 ≫ complementCoverPair01Correction := by
  change ChernWinding.windingIntegerCochain complementCoverPair01Transition
        complementCoverPair01Transition_ne_zero +
      ChernWinding.windingIntegerCochain
        (ChernWinding.nowhereZeroContinuousMapInv complementCoverPair01Transition
          complementCoverPair01Transition_ne_zero)
        (ChernWinding.nowhereZeroContinuousMapInv_ne_zero
          complementCoverPair01Transition complementCoverPair01Transition_ne_zero) = _
  rw [ChernWinding.windingIntegerCochain_inv_eq_neg_add_coboundary]
  dsimp [complementCoverPair01Correction]
  abel

/-- The literal pointwise inverse of the `02` transition on the pulled-back complement
intersection. -/
def complementCoverPair02InverseTransition :=
  ChernWinding.nowhereZeroContinuousMapInv complementCoverPair02Transition
    complementCoverPair02Transition_ne_zero

lemma complementCoverPair02InverseTransition_ne_zero :
    ∀ z, complementCoverPair02InverseTransition z ≠ 0 :=
  ChernWinding.nowhereZeroContinuousMapInv_ne_zero
    complementCoverPair02Transition complementCoverPair02Transition_ne_zero

/-- On the actual pulled-back `02` intersection, the second affine normal coordinate `X₀/X₂`
is literally the inverse of the ambient transition `X₂/X₀`. -/
lemma complementCoverIntersectionSecondNormal_pair02 :
    complementCoverIntersectionSecondNormal ({0, 2} : Finset (Fin 3)) (by simp) =
      complementCoverPair02InverseTransition := by
  ext z
  change secondNormalCoordinate
      (complementCoverIntersectionToChart ({0, 2} : Finset (Fin 3)) 2 (by simp) z) =
    (pair02Value (complementCoverPair02ToAnalyticPair z))⁻¹
  rw [← complementCoverPair02ToSecondChart_comm]
  exact pair02InverseValue_eq_secondNormalValue
      (complementCoverPair02ToAnalyticPair z) |>.symm.trans
        (pair02InverseValue_eq_inv_pair02Value
          (complementCoverPair02ToAnalyticPair z))

lemma complementCoverPair02_transition_mul_inverse (z) :
    ChernWinding.constantOneContinuousMap
        (TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
          coordinateHyperplaneComplementCover ({0, 2} : Finset (Fin 3)))) z =
      complementCoverPair02Transition z * complementCoverPair02InverseTransition z := by
  change 1 = complementCoverPair02Transition z * (complementCoverPair02Transition z)⁻¹
  exact (mul_inv_cancel₀ (complementCoverPair02Transition_ne_zero z)).symm

/-- The degree-zero principal-log correction for the inverse pair on `02`. -/
def complementCoverPair02Correction :
    (ChernWinding.singularChains (TopCat.of (openCoverIntersection
      coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
      ({0, 2} : Finset (Fin 3))))).X 0 ⟶ ModuleCat.of ℚ ℚ :=
  ChernWinding.pointLogProductDefectVertexCochain
    complementCoverPair02Transition complementCoverPair02InverseTransition
    (ChernWinding.constantOneContinuousMap (TopCat.of (openCoverIntersection
      coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
      ({0, 2} : Finset (Fin 3)))))
    complementCoverPair02Transition_ne_zero
    complementCoverPair02InverseTransition_ne_zero
    (ChernWinding.constantOneContinuousMap_ne_zero _)
    complementCoverPair02_transition_mul_inverse

/-- The raw inverse-transition equation on the actual pulled-back `02` intersection. -/
lemma complementCoverPair02_inverse_localEquation :
    ChernWinding.windingIntegerCochain complementCoverPair02Transition
        complementCoverPair02Transition_ne_zero +
      ChernWinding.windingIntegerCochain complementCoverPair02InverseTransition
        complementCoverPair02InverseTransition_ne_zero =
      (ChernWinding.singularChains (TopCat.of (openCoverIntersection
        coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
        ({0, 2} : Finset (Fin 3))))).d 1 0 ≫ complementCoverPair02Correction := by
  change ChernWinding.windingIntegerCochain complementCoverPair02Transition
        complementCoverPair02Transition_ne_zero +
      ChernWinding.windingIntegerCochain
        (ChernWinding.nowhereZeroContinuousMapInv complementCoverPair02Transition
          complementCoverPair02Transition_ne_zero)
        (ChernWinding.nowhereZeroContinuousMapInv_ne_zero
          complementCoverPair02Transition complementCoverPair02Transition_ne_zero) = _
  rw [ChernWinding.windingIntegerCochain_inv_eq_neg_add_coboundary]
  dsimp [complementCoverPair02Correction]
  abel

/-- The ambient transition `X₂/X₁`, restricted to the actual `12` complement overlap. -/
def complementCoverPair12Transition :
    C(TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({1, 2} : Finset (Fin 3))), ℂ) :=
  pair12Transition.comp (ChernWinding.topMap complementCoverPair12ToAnalyticOverlap)

lemma complementCoverPair12Transition_ne_zero :
    ∀ z, complementCoverPair12Transition z ≠ 0 :=
  fun z ↦ pair12Transition_ne_zero _

/-- The inverse transition `X₁/X₂`, pulled back from the ambient `12` overlap. -/
def complementCoverPair12Unit :
    C(TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({1, 2} : Finset (Fin 3))), ℂ) :=
  overlapUnitOnAmbient.comp (ChernWinding.topMap complementCoverPair12ToAnalyticOverlap)

lemma complementCoverPair12Unit_ne_zero :
    ∀ z, complementCoverPair12Unit z ≠ 0 :=
  fun z ↦ overlapUnitOnAmbient_ne_zero _

/-- On the actual `12` complement overlap, the two transition functions multiply to one. -/
lemma complementCoverPair12_transition_mul_unit (z) :
    ChernWinding.constantOneContinuousMap
        (TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
          coordinateHyperplaneComplementCover ({1, 2} : Finset (Fin 3)))) z =
      complementCoverPair12Transition z * complementCoverPair12Unit z := by
  let w := complementCoverPair12ToAnalyticOverlap z
  have h := congrArg
    (fun s ↦ (Point.evaluationHom ⊤ ⟨w, trivial⟩).hom s)
    overlapUnitSection_mul_inverse
  have hmul := map_mul (Point.evaluationHom ⊤ ⟨w, trivial⟩).hom
    overlapUnitSection overlapUnitInverseSection
  have hunit := Point.evaluationHom_apply ⊤ ⟨w, trivial⟩ overlapUnitSection
  have hinv := Point.evaluationHom_apply ⊤ ⟨w, trivial⟩ overlapUnitInverseSection
  have hone := map_one (Point.evaluationHom ⊤ ⟨w, trivial⟩).hom
  have hvalue :
      (Point.evaluationHom ⊤ ⟨w, trivial⟩).hom overlapUnitSection *
          (Point.evaluationHom ⊤ ⟨w, trivial⟩).hom overlapUnitInverseSection = 1 := by
    exact hmul.symm.trans (h.trans hone)
  change 1 = pair12Value w * overlapUnitValue w
  rw [mul_comm]
  change 1 =
    Point.evaluate ⊤ overlapUnitSection w *
      Point.evaluate ⊤ overlapUnitInverseSection w
  rw [← hunit, ← hinv]
  exact hvalue.symm

/-- On the literal pulled-back `12` intersection, the two chart normal coordinates satisfy
the expected transition equation.  Both sides are the actual functions obtained from the
scheme charts; no equality of functions is supplied as input. -/
lemma complementCoverPair12_normal_transition (z) :
    complementCoverIntersectionSecondNormal ({1, 2} : Finset (Fin 3)) (by simp) z =
      complementCoverIntersectionFirstNormal ({1, 2} : Finset (Fin 3)) (by simp) z *
        complementCoverPair12Unit z := by
  change secondNormalCoordinate
      (complementCoverIntersectionToChart ({1, 2} : Finset (Fin 3)) 2 (by simp) z) =
    firstNormalValue
        (complementCoverIntersectionToChart ({1, 2} : Finset (Fin 3)) 1 (by simp) z) *
      overlapUnitValue (complementCoverPair12ToAnalyticOverlap z)
  rw [← complementCoverPair12ToFirstChart_comm,
    ← complementCoverPair12ToSecondChart_comm,
    ← overlapFirstNormalValue_eq_firstNormalValue,
    ← overlapSecondNormalValue_eq_secondNormalValue]
  exact overlapNormalValue_transition _

/-- The explicit degree-zero branch correction on the pulled-back `12` complement overlap. -/
def complementCoverPair12Correction :
    (ChernWinding.singularChains (TopCat.of (openCoverIntersection
      coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
      ({1, 2} : Finset (Fin 3))))).X 0 ⟶ ModuleCat.of ℚ ℚ :=
  ChernWinding.windingIntegerCochainInverseProductCorrection
    complementCoverPair12Transition complementCoverPair12Unit
    (complementCoverIntersectionFirstNormal ({1, 2} : Finset (Fin 3)) (by simp))
    (complementCoverIntersectionSecondNormal ({1, 2} : Finset (Fin 3)) (by simp))
    complementCoverPair12Transition_ne_zero complementCoverPair12Unit_ne_zero
    (complementCoverIntersectionFirstNormal_ne_zero
      ({1, 2} : Finset (Fin 3)) (by simp))
    (complementCoverIntersectionSecondNormal_ne_zero
      ({1, 2} : Finset (Fin 3)) (by simp))
    complementCoverPair12_transition_mul_unit complementCoverPair12_normal_transition

/-- The complete raw `12` local equation: the ambient transition winding plus the difference
of the two singleton normal windings is the singular coboundary of the displayed correction. -/
lemma complementCoverPair12_localEquation :
    ChernWinding.windingIntegerCochain complementCoverPair12Transition
        complementCoverPair12Transition_ne_zero +
      ChernWinding.windingIntegerCochain
        (complementCoverIntersectionSecondNormal ({1, 2} : Finset (Fin 3)) (by simp))
        (complementCoverIntersectionSecondNormal_ne_zero
          ({1, 2} : Finset (Fin 3)) (by simp)) -
      ChernWinding.windingIntegerCochain
        (complementCoverIntersectionFirstNormal ({1, 2} : Finset (Fin 3)) (by simp))
        (complementCoverIntersectionFirstNormal_ne_zero
          ({1, 2} : Finset (Fin 3)) (by simp)) =
      (ChernWinding.singularChains (TopCat.of (openCoverIntersection
        coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
        ({1, 2} : Finset (Fin 3))))).d 1 0 ≫ complementCoverPair12Correction := by
  exact ChernWinding.windingIntegerCochain_add_normalDifference_eq_coboundary
    complementCoverPair12Transition complementCoverPair12Unit
    (complementCoverIntersectionFirstNormal ({1, 2} : Finset (Fin 3)) (by simp))
    (complementCoverIntersectionSecondNormal ({1, 2} : Finset (Fin 3)) (by simp))
    complementCoverPair12Transition_ne_zero complementCoverPair12Unit_ne_zero
    (complementCoverIntersectionFirstNormal_ne_zero
      ({1, 2} : Finset (Fin 3)) (by simp))
    (complementCoverIntersectionSecondNormal_ne_zero
      ({1, 2} : Finset (Fin 3)) (by simp))
    complementCoverPair12_transition_mul_unit complementCoverPair12_normal_transition

/-! ### The alternating correction identity on the complement triple intersection -/

def complementCoverTripleToPair01 :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({0, 1, 2} : Finset (Fin 3))) ⟶
      TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
        coordinateHyperplaneComplementCover ({0, 1} : Finset (Fin 3))) :=
  openCoverIntersectionInclusion coordinateHyperplaneSupportPair.snd
    coordinateHyperplaneComplementCover (by decide)

def complementCoverTripleToPair02 :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({0, 1, 2} : Finset (Fin 3))) ⟶
      TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
        coordinateHyperplaneComplementCover ({0, 2} : Finset (Fin 3))) :=
  openCoverIntersectionInclusion coordinateHyperplaneSupportPair.snd
    coordinateHyperplaneComplementCover (by decide)

def complementCoverTripleToPair12 :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({0, 1, 2} : Finset (Fin 3))) ⟶
      TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
        coordinateHyperplaneComplementCover ({1, 2} : Finset (Fin 3))) :=
  openCoverIntersectionInclusion coordinateHyperplaneSupportPair.snd
    coordinateHyperplaneComplementCover (by decide)

def complementCoverTripleToAnalyticTriple :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({0, 1, 2} : Finset (Fin 3))) ⟶
      analyticTripleTop :=
  complementCoverIntersectionToAmbientIntersection ({0, 1, 2} : Finset (Fin 3)) ≫
    projectiveCoverTripleToAnalyticTriple

lemma complementCoverTripleToPair01_comm :
    complementCoverTripleToPair01 ≫ complementCoverPair01ToAnalyticPair =
      complementCoverTripleToAnalyticTriple ≫ tripleToPair01Top := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  have hnat :
      complementCoverIntersectionToAmbientIntersection ({0, 1} : Finset (Fin 3))
          (complementCoverTripleToPair01 z) =
        projectiveCoverTripleToPair01
          (complementCoverIntersectionToAmbientIntersection
            ({0, 1, 2} : Finset (Fin 3)) z) := rfl
  change projectiveCoverPair01ToAnalyticPair
      (complementCoverIntersectionToAmbientIntersection ({0, 1} : Finset (Fin 3))
        (complementCoverTripleToPair01 z)) =
    tripleToPair01Top (projectiveCoverTripleToAnalyticTriple
      (complementCoverIntersectionToAmbientIntersection
        ({0, 1, 2} : Finset (Fin 3)) z))
  rw [hnat]
  exact ConcreteCategory.congr_hom projectiveCoverTripleToPair01_comm _

lemma complementCoverTripleToPair02_comm :
    complementCoverTripleToPair02 ≫ complementCoverPair02ToAnalyticPair =
      complementCoverTripleToAnalyticTriple ≫ tripleToPair02Top := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  have hnat :
      complementCoverIntersectionToAmbientIntersection ({0, 2} : Finset (Fin 3))
          (complementCoverTripleToPair02 z) =
        projectiveCoverTripleToPair02
          (complementCoverIntersectionToAmbientIntersection
            ({0, 1, 2} : Finset (Fin 3)) z) := rfl
  change projectiveCoverPair02ToAnalyticPair
      (complementCoverIntersectionToAmbientIntersection ({0, 2} : Finset (Fin 3))
        (complementCoverTripleToPair02 z)) =
    tripleToPair02Top (projectiveCoverTripleToAnalyticTriple
      (complementCoverIntersectionToAmbientIntersection
        ({0, 1, 2} : Finset (Fin 3)) z))
  rw [hnat]
  exact ConcreteCategory.congr_hom projectiveCoverTripleToPair02_comm _

lemma complementCoverTripleToPair12_comm :
    complementCoverTripleToPair12 ≫ complementCoverPair12ToAnalyticOverlap =
      complementCoverTripleToAnalyticTriple ≫ tripleToOverlapTop := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  have hnat :
      complementCoverIntersectionToAmbientIntersection ({1, 2} : Finset (Fin 3))
          (complementCoverTripleToPair12 z) =
        projectiveCoverTripleToPair12
          (complementCoverIntersectionToAmbientIntersection
            ({0, 1, 2} : Finset (Fin 3)) z) := rfl
  change projectiveCoverPair12ToAnalyticPair
      (complementCoverIntersectionToAmbientIntersection ({1, 2} : Finset (Fin 3))
        (complementCoverTripleToPair12 z)) =
    tripleToOverlapTop (projectiveCoverTripleToAnalyticTriple
      (complementCoverIntersectionToAmbientIntersection
        ({0, 1, 2} : Finset (Fin 3)) z))
  rw [hnat]
  exact ConcreteCategory.congr_hom projectiveCoverTripleToPair12_comm _

abbrev coordinateHyperplaneComplementTripleTop : TopCat :=
  TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
    coordinateHyperplaneComplementCover ({0, 1, 2} : Finset (Fin 3)))

def complementCoverTriple01Transition : C(coordinateHyperplaneComplementTripleTop, ℂ) :=
  complementCoverPair01Transition.comp (ChernWinding.topMap complementCoverTripleToPair01)

def complementCoverTriple02Transition : C(coordinateHyperplaneComplementTripleTop, ℂ) :=
  complementCoverPair02Transition.comp (ChernWinding.topMap complementCoverTripleToPair02)

def complementCoverTriple12Transition : C(coordinateHyperplaneComplementTripleTop, ℂ) :=
  complementCoverPair12Transition.comp (ChernWinding.topMap complementCoverTripleToPair12)

def complementCoverTriple01Inverse : C(coordinateHyperplaneComplementTripleTop, ℂ) :=
  complementCoverPair01InverseTransition.comp
    (ChernWinding.topMap complementCoverTripleToPair01)

def complementCoverTriple02Inverse : C(coordinateHyperplaneComplementTripleTop, ℂ) :=
  complementCoverPair02InverseTransition.comp
    (ChernWinding.topMap complementCoverTripleToPair02)

def complementCoverTriple12Inverse : C(coordinateHyperplaneComplementTripleTop, ℂ) :=
  complementCoverPair12Unit.comp (ChernWinding.topMap complementCoverTripleToPair12)

def complementCoverTripleFirstNormal : C(coordinateHyperplaneComplementTripleTop, ℂ) :=
  (complementCoverIntersectionFirstNormal ({1, 2} : Finset (Fin 3)) (by simp)).comp
    (ChernWinding.topMap complementCoverTripleToPair12)

def complementCoverTripleSecondNormal : C(coordinateHyperplaneComplementTripleTop, ℂ) :=
  (complementCoverIntersectionSecondNormal ({1, 2} : Finset (Fin 3)) (by simp)).comp
    (ChernWinding.topMap complementCoverTripleToPair12)

lemma complementCoverTriple01Transition_eq :
    complementCoverTriple01Transition =
      triple01Transition.comp (ChernWinding.topMap complementCoverTripleToAnalyticTriple) := by
  ext z
  have hc := ConcreteCategory.congr_hom complementCoverTripleToPair01_comm z
  change complementCoverPair01ToAnalyticPair (complementCoverTripleToPair01 z) =
    tripleToPair01Top (complementCoverTripleToAnalyticTriple z) at hc
  change pair01Transition (complementCoverPair01ToAnalyticPair
      (complementCoverTripleToPair01 z)) =
    triple01Transition (complementCoverTripleToAnalyticTriple z)
  rw [hc]
  exact DFunLike.congr_fun pair01Transition_restricts
    (complementCoverTripleToAnalyticTriple z)

lemma complementCoverTriple02Transition_eq :
    complementCoverTriple02Transition =
      triple02Transition.comp (ChernWinding.topMap complementCoverTripleToAnalyticTriple) := by
  ext z
  have hc := ConcreteCategory.congr_hom complementCoverTripleToPair02_comm z
  change complementCoverPair02ToAnalyticPair (complementCoverTripleToPair02 z) =
    tripleToPair02Top (complementCoverTripleToAnalyticTriple z) at hc
  change pair02Transition (complementCoverPair02ToAnalyticPair
      (complementCoverTripleToPair02 z)) =
    triple02Transition (complementCoverTripleToAnalyticTriple z)
  rw [hc]
  exact DFunLike.congr_fun pair02Transition_restricts
    (complementCoverTripleToAnalyticTriple z)

lemma complementCoverTriple12Transition_eq :
    complementCoverTriple12Transition =
      triple12Transition.comp (ChernWinding.topMap complementCoverTripleToAnalyticTriple) := by
  ext z
  have hc := ConcreteCategory.congr_hom complementCoverTripleToPair12_comm z
  change complementCoverPair12ToAnalyticOverlap (complementCoverTripleToPair12 z) =
    tripleToOverlapTop (complementCoverTripleToAnalyticTriple z) at hc
  change pair12Transition (complementCoverPair12ToAnalyticOverlap
      (complementCoverTripleToPair12 z)) =
    triple12Transition (complementCoverTripleToAnalyticTriple z)
  rw [hc]
  exact DFunLike.congr_fun pair12Transition_restricts
    (complementCoverTripleToAnalyticTriple z)

lemma complementCoverTriple_transition_product (z) :
    complementCoverTriple02Transition z =
      complementCoverTriple01Transition z * complementCoverTriple12Transition z := by
  rw [complementCoverTriple01Transition_eq, complementCoverTriple02Transition_eq,
    complementCoverTriple12Transition_eq]
  exact tripleTransition_product _

lemma complementCoverTripleFirstNormal_eq_inverse :
    complementCoverTripleFirstNormal = complementCoverTriple01Inverse := by
  ext z
  change firstNormalValue
      (complementCoverIntersectionToChart ({1, 2} : Finset (Fin 3)) 1 (by simp)
        (complementCoverTripleToPair12 z)) =
    complementCoverPair01InverseTransition (complementCoverTripleToPair01 z)
  rw [show complementCoverTripleToPair12 =
      openCoverIntersectionInclusion coordinateHyperplaneSupportPair.snd
        coordinateHyperplaneComplementCover
        (by decide : ({1, 2} : Finset (Fin 3)) ⊆ {0, 1, 2}) from rfl,
    complementCoverIntersectionToChart_naturality]
  rw [← complementCoverIntersectionToChart_naturality
    (show ({0, 1} : Finset (Fin 3)) ⊆ {0, 1, 2} by decide) 1 (by simp) z]
  change complementCoverIntersectionFirstNormal ({0, 1} : Finset (Fin 3)) (by simp)
      (complementCoverTripleToPair01 z) = _
  rw [complementCoverIntersectionFirstNormal_pair01]

lemma complementCoverTripleSecondNormal_eq_inverse :
    complementCoverTripleSecondNormal = complementCoverTriple02Inverse := by
  ext z
  change secondNormalCoordinate
      (complementCoverIntersectionToChart ({1, 2} : Finset (Fin 3)) 2 (by simp)
        (complementCoverTripleToPair12 z)) =
    complementCoverPair02InverseTransition (complementCoverTripleToPair02 z)
  rw [show complementCoverTripleToPair12 =
      openCoverIntersectionInclusion coordinateHyperplaneSupportPair.snd
        coordinateHyperplaneComplementCover
        (by decide : ({1, 2} : Finset (Fin 3)) ⊆ {0, 1, 2}) from rfl,
    complementCoverIntersectionToChart_naturality]
  rw [← complementCoverIntersectionToChart_naturality
    (show ({0, 2} : Finset (Fin 3)) ⊆ {0, 1, 2} by decide) 2 (by simp) z]
  change complementCoverIntersectionSecondNormal ({0, 2} : Finset (Fin 3)) (by simp)
      (complementCoverTripleToPair02 z) = _
  rw [complementCoverIntersectionSecondNormal_pair02]

lemma complementCoverTriple01Transition_ne_zero :
    ∀ z, complementCoverTriple01Transition z ≠ 0 :=
  fun z ↦ complementCoverPair01Transition_ne_zero _

lemma complementCoverTriple02Transition_ne_zero :
    ∀ z, complementCoverTriple02Transition z ≠ 0 :=
  fun z ↦ complementCoverPair02Transition_ne_zero _

lemma complementCoverTriple12Transition_ne_zero :
    ∀ z, complementCoverTriple12Transition z ≠ 0 :=
  fun z ↦ complementCoverPair12Transition_ne_zero _

lemma complementCoverTriple01Inverse_ne_zero :
    ∀ z, complementCoverTriple01Inverse z ≠ 0 :=
  fun z ↦ complementCoverPair01InverseTransition_ne_zero _

lemma complementCoverTriple02Inverse_ne_zero :
    ∀ z, complementCoverTriple02Inverse z ≠ 0 :=
  fun z ↦ complementCoverPair02InverseTransition_ne_zero _

lemma complementCoverTriple12Inverse_ne_zero :
    ∀ z, complementCoverTriple12Inverse z ≠ 0 :=
  fun z ↦ complementCoverPair12Unit_ne_zero _

lemma complementCoverTriple01_mul_inverse (z) :
    ChernWinding.constantOneContinuousMap coordinateHyperplaneComplementTripleTop z =
      complementCoverTriple01Transition z * complementCoverTriple01Inverse z := by
  exact complementCoverPair01_transition_mul_inverse (complementCoverTripleToPair01 z)

lemma complementCoverTriple02_mul_inverse (z) :
    ChernWinding.constantOneContinuousMap coordinateHyperplaneComplementTripleTop z =
      complementCoverTriple02Transition z * complementCoverTriple02Inverse z := by
  exact complementCoverPair02_transition_mul_inverse (complementCoverTripleToPair02 z)

lemma complementCoverTriple12_mul_inverse (z) :
    ChernWinding.constantOneContinuousMap coordinateHyperplaneComplementTripleTop z =
      complementCoverTriple12Transition z * complementCoverTriple12Inverse z := by
  exact complementCoverPair12_transition_mul_unit (complementCoverTripleToPair12 z)

lemma complementCoverTriple_inverse_product (z) :
    complementCoverTriple02Inverse z =
      complementCoverTriple01Inverse z * complementCoverTriple12Inverse z := by
  apply mul_left_cancel₀ (complementCoverTriple02Transition_ne_zero z)
  calc
    complementCoverTriple02Transition z * complementCoverTriple02Inverse z = 1 :=
      (complementCoverTriple02_mul_inverse z).symm
    _ = (complementCoverTriple01Transition z * complementCoverTriple01Inverse z) *
        (complementCoverTriple12Transition z * complementCoverTriple12Inverse z) := by
      rw [← complementCoverTriple01_mul_inverse z,
        ← complementCoverTriple12_mul_inverse z]
      change (1 : ℂ) = 1 * 1
      ring
    _ = complementCoverTriple02Transition z *
        (complementCoverTriple01Inverse z * complementCoverTriple12Inverse z) := by
      rw [complementCoverTriple_transition_product z]
      ring

lemma complementCoverTriple_constantOne_pointLog (z) :
    ChernWinding.pointLog
      (ChernWinding.constantOneContinuousMap coordinateHyperplaneComplementTripleTop) z = 0 := by
  change Complex.log 1 = 0
  exact Complex.log_one

def complementCoverTriple01Correction :
    (ChernWinding.singularChains coordinateHyperplaneComplementTripleTop).X 0 ⟶
      ModuleCat.of ℚ ℚ :=
  ChernWinding.pointLogProductDefectVertexCochain
    complementCoverTriple01Transition complementCoverTriple01Inverse
    (ChernWinding.constantOneContinuousMap coordinateHyperplaneComplementTripleTop)
    complementCoverTriple01Transition_ne_zero complementCoverTriple01Inverse_ne_zero
    (ChernWinding.constantOneContinuousMap_ne_zero _)
    complementCoverTriple01_mul_inverse

def complementCoverTriple02Correction :
    (ChernWinding.singularChains coordinateHyperplaneComplementTripleTop).X 0 ⟶
      ModuleCat.of ℚ ℚ :=
  ChernWinding.pointLogProductDefectVertexCochain
    complementCoverTriple02Transition complementCoverTriple02Inverse
    (ChernWinding.constantOneContinuousMap coordinateHyperplaneComplementTripleTop)
    complementCoverTriple02Transition_ne_zero complementCoverTriple02Inverse_ne_zero
    (ChernWinding.constantOneContinuousMap_ne_zero _)
    complementCoverTriple02_mul_inverse

def complementCoverTriple12Correction :
    (ChernWinding.singularChains coordinateHyperplaneComplementTripleTop).X 0 ⟶
      ModuleCat.of ℚ ℚ :=
  ChernWinding.windingIntegerCochainInverseProductCorrection
    complementCoverTriple12Transition complementCoverTriple12Inverse
    complementCoverTriple01Inverse complementCoverTriple02Inverse
    complementCoverTriple12Transition_ne_zero complementCoverTriple12Inverse_ne_zero
    complementCoverTriple01Inverse_ne_zero complementCoverTriple02Inverse_ne_zero
    complementCoverTriple12_mul_inverse complementCoverTriple_inverse_product

def complementCoverTripleDefect :
    (ChernWinding.singularChains coordinateHyperplaneComplementTripleTop).X 0 ⟶
      ModuleCat.of ℚ ℚ :=
  ChernWinding.pointLogProductDefectVertexCochain
    complementCoverTriple01Transition complementCoverTriple12Transition
    complementCoverTriple02Transition complementCoverTriple01Transition_ne_zero
    complementCoverTriple12Transition_ne_zero complementCoverTriple02Transition_ne_zero
    complementCoverTriple_transition_product

/-- The exact alternating triple-overlap identity for the three positive pair corrections. -/
lemma complementCoverTriple_correction_relation :
    complementCoverTriple01Correction - complementCoverTriple02Correction +
        complementCoverTriple12Correction = complementCoverTripleDefect := by
  exact ChernWinding.pointLogProductDefectVertexCochain_alternating_inverse
    complementCoverTriple01Transition complementCoverTriple12Transition
    complementCoverTriple02Transition complementCoverTriple01Inverse
    complementCoverTriple12Inverse complementCoverTriple02Inverse
    (ChernWinding.constantOneContinuousMap coordinateHyperplaneComplementTripleTop)
    complementCoverTriple01Transition_ne_zero complementCoverTriple12Transition_ne_zero
    complementCoverTriple02Transition_ne_zero complementCoverTriple01Inverse_ne_zero
    complementCoverTriple12Inverse_ne_zero complementCoverTriple02Inverse_ne_zero
    (ChernWinding.constantOneContinuousMap_ne_zero _)
    complementCoverTriple_transition_product complementCoverTriple01_mul_inverse
    complementCoverTriple12_mul_inverse complementCoverTriple02_mul_inverse
    complementCoverTriple_inverse_product complementCoverTriple_constantOne_pointLog

lemma complementCoverPair01Correction_restricts :
    (SSet.chainComplexMap (TopCat.toSSet.map complementCoverTripleToPair01)
      (ModuleCat.of ℚ ℚ)).f 0 ≫ complementCoverPair01Correction =
        complementCoverTriple01Correction := by
  let onePair := ChernWinding.constantOneContinuousMap
    (TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({0, 1} : Finset (Fin 3))))
  let onePull := onePair.comp (ChernWinding.topMap complementCoverTripleToPair01)
  let honePull : ∀ z, onePull z ≠ 0 := fun _ ↦ one_ne_zero
  let hmulPull : ∀ z, onePull z =
      complementCoverTriple01Transition z * complementCoverTriple01Inverse z :=
    fun z ↦ complementCoverPair01_transition_mul_inverse _
  have hnat := ChernWinding.chainComplexMap_comp_pointLogProductDefectVertexCochain
    complementCoverTripleToPair01 complementCoverPair01Transition
    complementCoverPair01InverseTransition onePair complementCoverPair01Transition_ne_zero
    complementCoverPair01InverseTransition_ne_zero
    (ChernWinding.constantOneContinuousMap_ne_zero _) complementCoverPair01_transition_mul_inverse
    complementCoverTriple01Transition_ne_zero complementCoverTriple01Inverse_ne_zero
    honePull hmulPull
  rw [complementCoverPair01Correction, hnat]
  exact ChernWinding.pointLogProductDefectVertexCochain_congr
    complementCoverTriple01Transition complementCoverTriple01Inverse onePull
    complementCoverTriple01Transition complementCoverTriple01Inverse
    (ChernWinding.constantOneContinuousMap coordinateHyperplaneComplementTripleTop)
    complementCoverTriple01Transition_ne_zero complementCoverTriple01Inverse_ne_zero honePull
    complementCoverTriple01Transition_ne_zero complementCoverTriple01Inverse_ne_zero
    (ChernWinding.constantOneContinuousMap_ne_zero _) hmulPull
    complementCoverTriple01_mul_inverse rfl rfl (by ext z; rfl)

lemma complementCoverPair02Correction_restricts :
    (SSet.chainComplexMap (TopCat.toSSet.map complementCoverTripleToPair02)
      (ModuleCat.of ℚ ℚ)).f 0 ≫ complementCoverPair02Correction =
        complementCoverTriple02Correction := by
  let onePair := ChernWinding.constantOneContinuousMap
    (TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({0, 2} : Finset (Fin 3))))
  let onePull := onePair.comp (ChernWinding.topMap complementCoverTripleToPair02)
  let honePull : ∀ z, onePull z ≠ 0 := fun _ ↦ one_ne_zero
  let hmulPull : ∀ z, onePull z =
      complementCoverTriple02Transition z * complementCoverTriple02Inverse z :=
    fun z ↦ complementCoverPair02_transition_mul_inverse _
  have hnat := ChernWinding.chainComplexMap_comp_pointLogProductDefectVertexCochain
    complementCoverTripleToPair02 complementCoverPair02Transition
    complementCoverPair02InverseTransition onePair complementCoverPair02Transition_ne_zero
    complementCoverPair02InverseTransition_ne_zero
    (ChernWinding.constantOneContinuousMap_ne_zero _) complementCoverPair02_transition_mul_inverse
    complementCoverTriple02Transition_ne_zero complementCoverTriple02Inverse_ne_zero
    honePull hmulPull
  rw [complementCoverPair02Correction, hnat]
  exact ChernWinding.pointLogProductDefectVertexCochain_congr
    complementCoverTriple02Transition complementCoverTriple02Inverse onePull
    complementCoverTriple02Transition complementCoverTriple02Inverse
    (ChernWinding.constantOneContinuousMap coordinateHyperplaneComplementTripleTop)
    complementCoverTriple02Transition_ne_zero complementCoverTriple02Inverse_ne_zero honePull
    complementCoverTriple02Transition_ne_zero complementCoverTriple02Inverse_ne_zero
    (ChernWinding.constantOneContinuousMap_ne_zero _) hmulPull
    complementCoverTriple02_mul_inverse rfl rfl (by ext z; rfl)

lemma complementCoverPair12Correction_restricts :
    (SSet.chainComplexMap (TopCat.toSSet.map complementCoverTripleToPair12)
      (ModuleCat.of ℚ ℚ)).f 0 ≫ complementCoverPair12Correction =
        complementCoverTriple12Correction := by
  rw [complementCoverPair12Correction]
  exact ChernWinding.chainComplexMap_comp_windingIntegerCochainInverseProductCorrection_congr
    complementCoverTripleToPair12 complementCoverPair12Transition complementCoverPair12Unit
    (complementCoverIntersectionFirstNormal ({1, 2} : Finset (Fin 3)) (by simp))
    (complementCoverIntersectionSecondNormal ({1, 2} : Finset (Fin 3)) (by simp))
    complementCoverPair12Transition_ne_zero
    complementCoverPair12Unit_ne_zero
    (complementCoverIntersectionFirstNormal_ne_zero
      ({1, 2} : Finset (Fin 3)) (by simp))
    (complementCoverIntersectionSecondNormal_ne_zero
      ({1, 2} : Finset (Fin 3)) (by simp))
    complementCoverPair12_transition_mul_unit complementCoverPair12_normal_transition
    complementCoverTriple12Transition_ne_zero complementCoverTriple12Inverse_ne_zero
    (fun z : coordinateHyperplaneComplementTripleTop ↦
      complementCoverIntersectionFirstNormal_ne_zero
        ({1, 2} : Finset (Fin 3)) (by simp) (complementCoverTripleToPair12 z))
    (fun z : coordinateHyperplaneComplementTripleTop ↦
      complementCoverIntersectionSecondNormal_ne_zero
        ({1, 2} : Finset (Fin 3)) (by simp) (complementCoverTripleToPair12 z))
    (fun z : coordinateHyperplaneComplementTripleTop ↦
      complementCoverPair12_transition_mul_unit (complementCoverTripleToPair12 z))
    (fun z : coordinateHyperplaneComplementTripleTop ↦
      complementCoverPair12_normal_transition (complementCoverTripleToPair12 z))
    complementCoverTriple12Transition
    complementCoverTriple12Inverse complementCoverTriple01Inverse complementCoverTriple02Inverse
    complementCoverTriple12Transition_ne_zero complementCoverTriple12Inverse_ne_zero
    complementCoverTriple01Inverse_ne_zero complementCoverTriple02Inverse_ne_zero
    complementCoverTriple12_mul_inverse complementCoverTriple_inverse_product rfl rfl
    complementCoverTripleFirstNormal_eq_inverse complementCoverTripleSecondNormal_eq_inverse

/-- The three literal pair-overlap corrections restrict to the complement triple intersection
with the expected alternating sum. -/
lemma complementCoverPairCorrections_triple_relation :
    (SSet.chainComplexMap (TopCat.toSSet.map complementCoverTripleToPair01)
        (ModuleCat.of ℚ ℚ)).f 0 ≫ complementCoverPair01Correction -
      (SSet.chainComplexMap (TopCat.toSSet.map complementCoverTripleToPair02)
        (ModuleCat.of ℚ ℚ)).f 0 ≫ complementCoverPair02Correction +
      (SSet.chainComplexMap (TopCat.toSSet.map complementCoverTripleToPair12)
        (ModuleCat.of ℚ ℚ)).f 0 ≫ complementCoverPair12Correction =
        complementCoverTripleDefect := by
  rw [complementCoverPair01Correction_restricts,
    complementCoverPair02Correction_restricts,
    complementCoverPair12Correction_restricts]
  exact complementCoverTriple_correction_relation

/-! The three signed degree-zero pair corrections as a normalized Čech column. -/

lemma strictMono_finTwo_to_finThree_classify (a : Fin 2 → Fin 3)
    (ha : TupleClass.strictMono.mem 1 a) :
    a = ![0, 1] ∨ a = ![0, 2] ∨ a = ![1, 2] := by
  have hlt : a 0 < a 1 := ha (by decide)
  generalize hx : a 0 = x
  generalize hy : a 1 = y
  fin_cases x <;> fin_cases y
  all_goals simp [hx, hy] at hlt
  · exact Or.inl (by funext i; fin_cases i <;> simp [hx, hy])
  · exact Or.inr (Or.inl (by funext i; fin_cases i <;> simp [hx, hy]))
  · exact Or.inr (Or.inr (by funext i; fin_cases i <;> simp [hx, hy]))

noncomputable def complementCoverPair01CorrectionTuple :
    ((coordinateHyperplaneComplementCoverChainModels.model
      (tupleSupport (![0, 1] : Fin 2 → Fin 3))).X 0) ⟶ ModuleCat.of ℚ ℚ := by
  change (ChernWinding.singularChains (TopCat.of (openCoverIntersection
      coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
      ({0, 1} : Finset (Fin 3))))).X 0 ⟶ ModuleCat.of ℚ ℚ
  exact complementCoverPair01Correction

noncomputable def complementCoverPair02CorrectionTuple :
    ((coordinateHyperplaneComplementCoverChainModels.model
      (tupleSupport (![0, 2] : Fin 2 → Fin 3))).X 0) ⟶ ModuleCat.of ℚ ℚ := by
  change (ChernWinding.singularChains (TopCat.of (openCoverIntersection
      coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
      ({0, 2} : Finset (Fin 3))))).X 0 ⟶ ModuleCat.of ℚ ℚ
  exact complementCoverPair02Correction

noncomputable def complementCoverPair12CorrectionTuple :
    ((coordinateHyperplaneComplementCoverChainModels.model
      (tupleSupport (![1, 2] : Fin 2 → Fin 3))).X 0) ⟶ ModuleCat.of ℚ ℚ := by
  change (ChernWinding.singularChains (TopCat.of (openCoverIntersection
      coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
      ({1, 2} : Finset (Fin 3))))).X 0 ⟶ ModuleCat.of ℚ ℚ
  exact complementCoverPair12Correction

noncomputable def coordinateHyperplaneComplementPairCorrection
    (a : {a : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 a}) :
    ((coordinateHyperplaneComplementCoverChainModels.model
      (tupleSupport a.1)).X 0) ⟶ ModuleCat.of ℚ ℚ := by
  rcases a with ⟨a, ha⟩
  classical
  by_cases h01 : a = ![0, 1]
  · subst a
    exact complementCoverPair01CorrectionTuple
  by_cases h02 : a = ![0, 2]
  · subst a
    exact complementCoverPair02CorrectionTuple
  by_cases h12 : a = ![1, 2]
  · subst a
    exact complementCoverPair12CorrectionTuple
  exact False.elim
    (h12 (((strictMono_finTwo_to_finThree_classify a ha).resolve_left h01).resolve_left h02))

noncomputable def coordinateHyperplaneComplementPairCorrectionDegreeDesc :
    ((coordinateHyperplaneComplementCoverChainModels.cechObject
      TupleClass.strictMono 1).X 0) ⟶ ModuleCat.of ℚ ℚ :=
  (isColimitCofanMkObjOfIsColimit
    (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 0)
    (fun a : {a : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 a} ↦
      coordinateHyperplaneComplementCoverChainModels.model (tupleSupport a.1))
    (fun a ↦ Sigma.ι
      (fun b : {b : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 b} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1)) a)
    (coproductIsCoproduct _)).desc
      (Cofan.mk (ModuleCat.of ℚ ℚ)
        (fun a ↦ coordinateHyperplaneComplementPairCorrection a))

/-- Evaluation of the descended pair correction on a normalized two-chart summand. -/
lemma coordinateHyperplaneComplementPairCorrectionDegreeDesc_ι
    (a : {a : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 a}) :
    (Sigma.ι
      (fun b : {b : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 b} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1)) a).f 0 ≫
      coordinateHyperplaneComplementPairCorrectionDegreeDesc =
        coordinateHyperplaneComplementPairCorrection a := by
  change (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 0).map
      (Sigma.ι
        (fun b : {b : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 b} ↦
          coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1)) a) ≫
      coordinateHyperplaneComplementPairCorrectionDegreeDesc =
        coordinateHyperplaneComplementPairCorrection a
  exact (isColimitCofanMkObjOfIsColimit
    (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 0)
    (fun b : {b : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 b} ↦
      coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1))
    (fun b ↦ Sigma.ι
      (fun c : {c : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 c} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport c.1)) b)
    (coproductIsCoproduct _)).fac
      (Cofan.mk (ModuleCat.of ℚ ℚ)
        (fun b ↦ coordinateHyperplaneComplementPairCorrection b)) ⟨a⟩

/-- The singleton `D₊(X₁)` of the pulled-back cover maps to the punctured first affine chart. -/
def complementCoverSingletonOneToFirstChartComplement :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({1} : Finset (Fin 3))) ⟶
      firstChartHyperplanePair.snd :=
  TopCat.ofHom
    { toFun := fun z ↦ ⟨complementCoverSingletonToChart 1 z, by
          rw [mem_firstNormalComplement_iff_not_mem_hyperplane]
          rw [complementCoverSingletonToChart_map_openInclusion]
          exact z.1.2⟩
      continuous_toFun := by
        fun_prop }

/-- The singleton `D₊(X₂)` of the pulled-back cover maps to the punctured second affine chart. -/
def complementCoverSingletonTwoToSecondChartComplement :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({2} : Finset (Fin 3))) ⟶
      secondChartHyperplanePair.snd :=
  TopCat.ofHom
    { toFun := fun z ↦ ⟨complementCoverSingletonToChart 2 z, by
          rw [mem_secondNormalComplement_iff_not_mem_hyperplane]
          rw [complementCoverSingletonToChart_map_openInclusion]
          exact z.1.2⟩
      continuous_toFun := by
        fun_prop }

def complementCoverPair01ToSingletonOne :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({0, 1} : Finset (Fin 3))) ⟶
      TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
        coordinateHyperplaneComplementCover ({1} : Finset (Fin 3))) :=
  openCoverIntersectionInclusion coordinateHyperplaneSupportPair.snd
    coordinateHyperplaneComplementCover (by decide)

def complementCoverPair02ToSingletonTwo :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({0, 2} : Finset (Fin 3))) ⟶
      TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
        coordinateHyperplaneComplementCover ({2} : Finset (Fin 3))) :=
  openCoverIntersectionInclusion coordinateHyperplaneSupportPair.snd
    coordinateHyperplaneComplementCover (by decide)

def complementCoverPair12ToSingletonOne :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({1, 2} : Finset (Fin 3))) ⟶
      TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
        coordinateHyperplaneComplementCover ({1} : Finset (Fin 3))) :=
  openCoverIntersectionInclusion coordinateHyperplaneSupportPair.snd
    coordinateHyperplaneComplementCover (by decide)

def complementCoverPair12ToSingletonTwo :
    TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({1, 2} : Finset (Fin 3))) ⟶
      TopCat.of (openCoverIntersection coordinateHyperplaneSupportPair.snd
        coordinateHyperplaneComplementCover ({2} : Finset (Fin 3))) :=
  openCoverIntersectionInclusion coordinateHyperplaneSupportPair.snd
    coordinateHyperplaneComplementCover (by decide)

lemma complementCoverPair01ToSingletonOne_comm :
    complementCoverPair01ToSingletonOne ≫
        complementCoverSingletonOneToFirstChartComplement =
      complementCoverIntersectionToFirstChartComplement
        ({0, 1} : Finset (Fin 3)) (by simp) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact complementCoverIntersectionToChart_naturality
    (show ({1} : Finset (Fin 3)) ⊆ {0, 1} by decide) 1 (by simp) z

lemma complementCoverPair02ToSingletonTwo_comm :
    complementCoverPair02ToSingletonTwo ≫
        complementCoverSingletonTwoToSecondChartComplement =
      complementCoverIntersectionToSecondChartComplement
        ({0, 2} : Finset (Fin 3)) (by simp) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact complementCoverIntersectionToChart_naturality
    (show ({2} : Finset (Fin 3)) ⊆ {0, 2} by decide) 2 (by simp) z

lemma complementCoverPair12ToSingletonOne_comm :
    complementCoverPair12ToSingletonOne ≫
        complementCoverSingletonOneToFirstChartComplement =
      complementCoverIntersectionToFirstChartComplement
        ({1, 2} : Finset (Fin 3)) (by simp) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact complementCoverIntersectionToChart_naturality
    (show ({1} : Finset (Fin 3)) ⊆ {1, 2} by decide) 1 (by simp) z

lemma complementCoverPair12ToSingletonTwo_comm :
    complementCoverPair12ToSingletonTwo ≫
        complementCoverSingletonTwoToSecondChartComplement =
      complementCoverIntersectionToSecondChartComplement
        ({1, 2} : Finset (Fin 3)) (by simp) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact complementCoverIntersectionToChart_naturality
    (show ({2} : Finset (Fin 3)) ⊆ {1, 2} by decide) 2 (by simp) z

/-- The actual winding functional `wind(X₀/X₁)` on the singleton `D₊(X₁)` in the complement
cover. -/
def complementCoverSingletonOneWinding :
    ((TopCat.toSSet.obj (TopCat.of
      (openCoverIntersection coordinateHyperplaneSupportPair.snd
        coordinateHyperplaneComplementCover ({1} : Finset (Fin 3))))).chainComplex
          (ModuleCat.of ℚ ℚ)).X 1 ⟶ ModuleCat.of ℚ ℚ :=
  (SSet.chainComplexMap
      (TopCat.toSSet.map complementCoverSingletonOneToFirstChartComplement)
      (ModuleCat.of ℚ ℚ)).f 1 ≫
    ChernWinding.windingIntegerCochain
      firstNormalOnComplement firstNormalOnComplement_ne_zero

/-- The actual winding functional `wind(X₀/X₂)` on the singleton `D₊(X₂)` in the complement
cover. -/
def complementCoverSingletonTwoWinding :
    ((TopCat.toSSet.obj (TopCat.of
      (openCoverIntersection coordinateHyperplaneSupportPair.snd
        coordinateHyperplaneComplementCover ({2} : Finset (Fin 3))))).chainComplex
          (ModuleCat.of ℚ ℚ)).X 1 ⟶ ModuleCat.of ℚ ℚ :=
  (SSet.chainComplexMap
      (TopCat.toSSet.map complementCoverSingletonTwoToSecondChartComplement)
      (ModuleCat.of ℚ ℚ)).f 1 ≫
    ChernWinding.windingIntegerCochain
      secondNormalOnComplement secondNormalOnComplement_ne_zero

lemma complementCoverSingletonOneWinding_closed :
    ((TopCat.toSSet.obj (TopCat.of
      (openCoverIntersection coordinateHyperplaneSupportPair.snd
        coordinateHyperplaneComplementCover ({1} : Finset (Fin 3))))).chainComplex
          (ModuleCat.of ℚ ℚ)).d 2 1 ≫ complementCoverSingletonOneWinding = 0 := by
  rw [complementCoverSingletonOneWinding, ← Category.assoc,
    ← (SSet.chainComplexMap
      (TopCat.toSSet.map complementCoverSingletonOneToFirstChartComplement)
      (ModuleCat.of ℚ ℚ)).comm 2 1, Category.assoc,
    ChernWinding.d_comp_windingIntegerCochain]
  simp

lemma complementCoverSingletonTwoWinding_closed :
    ((TopCat.toSSet.obj (TopCat.of
      (openCoverIntersection coordinateHyperplaneSupportPair.snd
        coordinateHyperplaneComplementCover ({2} : Finset (Fin 3))))).chainComplex
          (ModuleCat.of ℚ ℚ)).d 2 1 ≫ complementCoverSingletonTwoWinding = 0 := by
  rw [complementCoverSingletonTwoWinding, ← Category.assoc,
    ← (SSet.chainComplexMap
      (TopCat.toSSet.map complementCoverSingletonTwoToSecondChartComplement)
      (ModuleCat.of ℚ ℚ)).comm 2 1, Category.assoc,
    ChernWinding.d_comp_windingIntegerCochain]
  simp

lemma complementCoverSingletonOneWinding_restricts_pair01 :
    (SSet.chainComplexMap (TopCat.toSSet.map complementCoverPair01ToSingletonOne)
      (ModuleCat.of ℚ ℚ)).f 1 ≫ complementCoverSingletonOneWinding =
      ChernWinding.windingIntegerCochain
        (complementCoverIntersectionFirstNormal ({0, 1} : Finset (Fin 3)) (by simp))
        (complementCoverIntersectionFirstNormal_ne_zero
          ({0, 1} : Finset (Fin 3)) (by simp)) := by
  let hnormal : ∀ z, (firstNormalOnComplement.comp (ChernWinding.topMap
      (complementCoverIntersectionToFirstChartComplement
        ({0, 1} : Finset (Fin 3)) (by simp)))) z ≠ 0 :=
    fun z ↦ firstNormalOnComplement_ne_zero _
  rw [complementCoverSingletonOneWinding, ← Category.assoc, ← HomologicalComplex.comp_f]
  unfold SSet.chainComplexMap
  rw [← Functor.map_comp, ← Functor.map_comp,
    complementCoverPair01ToSingletonOne_comm,
    ChernWinding.chainComplexMap_comp_windingIntegerCochain (hgf := hnormal)]
  rfl

lemma complementCoverSingletonTwoWinding_restricts_pair02 :
    (SSet.chainComplexMap (TopCat.toSSet.map complementCoverPair02ToSingletonTwo)
      (ModuleCat.of ℚ ℚ)).f 1 ≫ complementCoverSingletonTwoWinding =
      ChernWinding.windingIntegerCochain
        (complementCoverIntersectionSecondNormal ({0, 2} : Finset (Fin 3)) (by simp))
        (complementCoverIntersectionSecondNormal_ne_zero
          ({0, 2} : Finset (Fin 3)) (by simp)) := by
  let hnormal : ∀ z, (secondNormalOnComplement.comp (ChernWinding.topMap
      (complementCoverIntersectionToSecondChartComplement
        ({0, 2} : Finset (Fin 3)) (by simp)))) z ≠ 0 :=
    fun z ↦ secondNormalOnComplement_ne_zero _
  rw [complementCoverSingletonTwoWinding, ← Category.assoc, ← HomologicalComplex.comp_f]
  unfold SSet.chainComplexMap
  rw [← Functor.map_comp, ← Functor.map_comp,
    complementCoverPair02ToSingletonTwo_comm,
    ChernWinding.chainComplexMap_comp_windingIntegerCochain (hgf := hnormal)]
  rfl

lemma complementCoverSingletonOneWinding_restricts_pair12 :
    (SSet.chainComplexMap (TopCat.toSSet.map complementCoverPair12ToSingletonOne)
      (ModuleCat.of ℚ ℚ)).f 1 ≫ complementCoverSingletonOneWinding =
      ChernWinding.windingIntegerCochain
        (complementCoverIntersectionFirstNormal ({1, 2} : Finset (Fin 3)) (by simp))
        (complementCoverIntersectionFirstNormal_ne_zero
          ({1, 2} : Finset (Fin 3)) (by simp)) := by
  let hnormal : ∀ z, (firstNormalOnComplement.comp (ChernWinding.topMap
      (complementCoverIntersectionToFirstChartComplement
        ({1, 2} : Finset (Fin 3)) (by simp)))) z ≠ 0 :=
    fun z ↦ firstNormalOnComplement_ne_zero _
  rw [complementCoverSingletonOneWinding, ← Category.assoc, ← HomologicalComplex.comp_f]
  unfold SSet.chainComplexMap
  rw [← Functor.map_comp, ← Functor.map_comp,
    complementCoverPair12ToSingletonOne_comm,
    ChernWinding.chainComplexMap_comp_windingIntegerCochain (hgf := hnormal)]
  rfl

lemma complementCoverSingletonTwoWinding_restricts_pair12 :
    (SSet.chainComplexMap (TopCat.toSSet.map complementCoverPair12ToSingletonTwo)
      (ModuleCat.of ℚ ℚ)).f 1 ≫ complementCoverSingletonTwoWinding =
      ChernWinding.windingIntegerCochain
        (complementCoverIntersectionSecondNormal ({1, 2} : Finset (Fin 3)) (by simp))
        (complementCoverIntersectionSecondNormal_ne_zero
          ({1, 2} : Finset (Fin 3)) (by simp)) := by
  let hnormal : ∀ z, (secondNormalOnComplement.comp (ChernWinding.topMap
      (complementCoverIntersectionToSecondChartComplement
        ({1, 2} : Finset (Fin 3)) (by simp)))) z ≠ 0 :=
    fun z ↦ secondNormalOnComplement_ne_zero _
  rw [complementCoverSingletonTwoWinding, ← Category.assoc, ← HomologicalComplex.comp_f]
  unfold SSet.chainComplexMap
  rw [← Functor.map_comp, ← Functor.map_comp,
    complementCoverPair12ToSingletonTwo_comm,
    ChernWinding.chainComplexMap_comp_windingIntegerCochain (hgf := hnormal)]
  rfl

/-- On the `01` face, the ambient transition winding plus the restricted singleton winding is
the coboundary of the displayed pair correction. -/
lemma complementCoverPair01_face_localEquation :
    ChernWinding.windingIntegerCochain complementCoverPair01Transition
        complementCoverPair01Transition_ne_zero +
      (SSet.chainComplexMap (TopCat.toSSet.map complementCoverPair01ToSingletonOne)
        (ModuleCat.of ℚ ℚ)).f 1 ≫ complementCoverSingletonOneWinding =
      (ChernWinding.singularChains (TopCat.of (openCoverIntersection
        coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
        ({0, 1} : Finset (Fin 3))))).d 1 0 ≫ complementCoverPair01Correction := by
  rw [complementCoverSingletonOneWinding_restricts_pair01]
  have hwind : ChernWinding.windingIntegerCochain
      (complementCoverIntersectionFirstNormal ({0, 1} : Finset (Fin 3)) (by simp))
      (complementCoverIntersectionFirstNormal_ne_zero
        ({0, 1} : Finset (Fin 3)) (by simp)) =
      ChernWinding.windingIntegerCochain complementCoverPair01InverseTransition
        complementCoverPair01InverseTransition_ne_zero :=
    AlgebraicTopology.Singular.CechWinding.windingIntegerCochain_congr _ _ _ _
      complementCoverIntersectionFirstNormal_pair01
  rw [hwind]
  exact complementCoverPair01_inverse_localEquation

/-- On the `02` face, the ambient transition winding plus the restricted singleton winding is
the coboundary of the displayed pair correction. -/
lemma complementCoverPair02_face_localEquation :
    ChernWinding.windingIntegerCochain complementCoverPair02Transition
        complementCoverPair02Transition_ne_zero +
      (SSet.chainComplexMap (TopCat.toSSet.map complementCoverPair02ToSingletonTwo)
        (ModuleCat.of ℚ ℚ)).f 1 ≫ complementCoverSingletonTwoWinding =
      (ChernWinding.singularChains (TopCat.of (openCoverIntersection
        coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
        ({0, 2} : Finset (Fin 3))))).d 1 0 ≫ complementCoverPair02Correction := by
  rw [complementCoverSingletonTwoWinding_restricts_pair02]
  have hwind : ChernWinding.windingIntegerCochain
      (complementCoverIntersectionSecondNormal ({0, 2} : Finset (Fin 3)) (by simp))
      (complementCoverIntersectionSecondNormal_ne_zero
        ({0, 2} : Finset (Fin 3)) (by simp)) =
      ChernWinding.windingIntegerCochain complementCoverPair02InverseTransition
        complementCoverPair02InverseTransition_ne_zero :=
    AlgebraicTopology.Singular.CechWinding.windingIntegerCochain_congr _ _ _ _
      complementCoverIntersectionSecondNormal_pair02
  rw [hwind]
  exact complementCoverPair02_inverse_localEquation

/-- On the `12` face, the ambient transition winding plus the alternating restrictions of the
two singleton windings is the coboundary of the displayed pair correction. -/
lemma complementCoverPair12_face_localEquation :
    ChernWinding.windingIntegerCochain complementCoverPair12Transition
        complementCoverPair12Transition_ne_zero +
      ((SSet.chainComplexMap (TopCat.toSSet.map complementCoverPair12ToSingletonTwo)
          (ModuleCat.of ℚ ℚ)).f 1 ≫ complementCoverSingletonTwoWinding -
        (SSet.chainComplexMap (TopCat.toSSet.map complementCoverPair12ToSingletonOne)
          (ModuleCat.of ℚ ℚ)).f 1 ≫ complementCoverSingletonOneWinding) =
      (ChernWinding.singularChains (TopCat.of (openCoverIntersection
        coordinateHyperplaneSupportPair.snd coordinateHyperplaneComplementCover
        ({1, 2} : Finset (Fin 3))))).d 1 0 ≫ complementCoverPair12Correction := by
  rw [complementCoverSingletonTwoWinding_restricts_pair12,
    complementCoverSingletonOneWinding_restricts_pair12]
  simpa only [sub_eq_add_neg, add_assoc] using complementCoverPair12_localEquation

noncomputable def complementCoverSingletonOneWindingTuple :
    ((coordinateHyperplaneComplementCoverChainModels.model
      (tupleSupport (![1] : Fin 1 → Fin 3))).X 1) ⟶ ModuleCat.of ℚ ℚ := by
  change ((TopCat.toSSet.obj (TopCat.of
    (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({1} : Finset (Fin 3))))).chainComplex
        (ModuleCat.of ℚ ℚ)).X 1 ⟶ ModuleCat.of ℚ ℚ
  exact complementCoverSingletonOneWinding

noncomputable def complementCoverSingletonTwoWindingTuple :
    ((coordinateHyperplaneComplementCoverChainModels.model
      (tupleSupport (![2] : Fin 1 → Fin 3))).X 1) ⟶ ModuleCat.of ℚ ℚ := by
  change ((TopCat.toSSet.obj (TopCat.of
    (openCoverIntersection coordinateHyperplaneSupportPair.snd
      coordinateHyperplaneComplementCover ({2} : Finset (Fin 3))))).chainComplex
        (ModuleCat.of ℚ ℚ)).X 1 ⟶ ModuleCat.of ℚ ℚ
  exact complementCoverSingletonTwoWinding

lemma finOne_to_finThree_classify (a : Fin 1 → Fin 3) :
    a = ![0] ∨ a = ![1] ∨ a = ![2] := by
  generalize h : a 0 = i
  fin_cases i
  · exact Or.inl (by
      funext j
      fin_cases j
      exact h)
  · exact Or.inr (Or.inl (by
      funext j
      fin_cases j
      exact h))
  · exact Or.inr (Or.inr (by
      funext j
      fin_cases j
      exact h))

/-- The singleton-column part of the complement trivialization: zero on `D₊(X₀)`, and the
literal winding cochains of `X₀/X₁` and `X₀/X₂` on the other two charts. -/
noncomputable def coordinateHyperplaneComplementSingletonCochain
    (a : {a : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 a}) :
    ((coordinateHyperplaneComplementCoverChainModels.model
      (tupleSupport a.1)).X 1) ⟶ ModuleCat.of ℚ ℚ := by
  rcases a with ⟨a, ha⟩
  classical
  by_cases h0 : a = ![0]
  · subst a
    exact 0
  by_cases h1 : a = ![1]
  · subst a
    exact complementCoverSingletonOneWindingTuple
  by_cases h2 : a = ![2]
  · subst a
    exact complementCoverSingletonTwoWindingTuple
  exact False.elim (h2 (((finOne_to_finThree_classify a).resolve_left h0).resolve_left h1))

lemma coordinateHyperplaneComplementSingletonCochain_closed
    (a : {a : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 a}) :
    (coordinateHyperplaneComplementCoverChainModels.model
      (tupleSupport a.1)).d 2 1 ≫
        coordinateHyperplaneComplementSingletonCochain a = 0 := by
  rcases a with ⟨a, ha⟩
  classical
  rcases finOne_to_finThree_classify a with h0 | h1 | h2
  · subst a
    simp [coordinateHyperplaneComplementSingletonCochain]
  · subst a
    exact complementCoverSingletonOneWinding_closed
  · subst a
    exact complementCoverSingletonTwoWinding_closed

/-- Descend the singleton winding functionals from the coproduct presentation of the normalized
Čech column of outer degree zero. -/
noncomputable def coordinateHyperplaneComplementSingletonDegreeDesc :
    ((coordinateHyperplaneComplementCoverChainModels.cechObject
      TupleClass.strictMono 0).X 1) ⟶ ModuleCat.of ℚ ℚ :=
  (isColimitCofanMkObjOfIsColimit
    (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 1)
    (fun a : {a : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 a} ↦
      coordinateHyperplaneComplementCoverChainModels.model (tupleSupport a.1))
    (fun a ↦ Sigma.ι
      (fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1)) a)
    (coproductIsCoproduct _)).desc
      (Cofan.mk (ModuleCat.of ℚ ℚ)
        (fun a ↦ coordinateHyperplaneComplementSingletonCochain a))

lemma coordinateHyperplaneComplementSingletonDegreeDesc_ι
    (a : {a : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 a}) :
    (Sigma.ι
      (fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1)) a).f 1 ≫
      coordinateHyperplaneComplementSingletonDegreeDesc =
        coordinateHyperplaneComplementSingletonCochain a := by
  change (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 1).map
      (Sigma.ι
        (fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
          coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1)) a) ≫
      coordinateHyperplaneComplementSingletonDegreeDesc =
        coordinateHyperplaneComplementSingletonCochain a
  exact (isColimitCofanMkObjOfIsColimit
    (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 1)
    (fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
      coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1))
    (fun b ↦ Sigma.ι
      (fun c : {c : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 c} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport c.1)) b)
    (coproductIsCoproduct _)).fac
      (Cofan.mk (ModuleCat.of ℚ ℚ)
        (fun b ↦ coordinateHyperplaneComplementSingletonCochain b)) ⟨a⟩

set_option backward.isDefEq.respectTransparency false in
lemma coordinateHyperplaneComplementSingletonDegreeDesc_closed :
    ((coordinateHyperplaneComplementCoverChainModels.cechComplex
      TupleClass.strictMono).X 0).d 2 1 ≫
        coordinateHyperplaneComplementSingletonDegreeDesc = 0 := by
  change (coordinateHyperplaneComplementCoverChainModels.cechObject
    TupleClass.strictMono 0).d 2 1 ≫
      coordinateHyperplaneComplementSingletonDegreeDesc = 0
  apply (isColimitCofanMkObjOfIsColimit
    (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) 2)
    (fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
      coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1))
    (fun b ↦ Sigma.ι
      (fun c : {c : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 c} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport c.1)) b)
    (coproductIsCoproduct _)).hom_ext
  rintro ⟨a⟩
  change (Sigma.ι
      (fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1)) a).f 2 ≫
      (coordinateHyperplaneComplementCoverChainModels.cechObject
        TupleClass.strictMono 0).d 2 1 ≫
      coordinateHyperplaneComplementSingletonDegreeDesc = 0
  rw [← Category.assoc,
    (Sigma.ι
      (fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1)) a).comm 2 1,
    Category.assoc, coordinateHyperplaneComplementSingletonDegreeDesc_ι]
  exact coordinateHyperplaneComplementSingletonCochain_closed a

set_option backward.isDefEq.respectTransparency false in
lemma coordinateHyperplaneComplementCoverChainModels_ι_comp_outer_d (p : ℕ)
    (a : {a : Fin (p + 2) → Fin 3 // TupleClass.strictMono.mem (p + 1) a}) :
    Sigma.ι
        (fun b : {b : Fin (p + 2) → Fin 3 // TupleClass.strictMono.mem (p + 1) b} ↦
          coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1)) a ≫
        (coordinateHyperplaneComplementCoverChainModels.cechComplex
          TupleClass.strictMono).d (p + 1) p =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ i.val) •
        (coordinateHyperplaneComplementCoverChainModels.face (by
          rw [tupleSupport_subset_iff]
          exact Set.range_comp_subset_range i.succAbove a.1) ≫
          Sigma.ι
            (fun b : {b : Fin (p + 1) → Fin 3 // TupleClass.strictMono.mem p b} ↦
              coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1))
            ⟨Fin.removeNth i a.1,
              TupleClass.strictMono.removeNth_mem p a.1 i a.2⟩) := by
  rw [SupportChainModels.cechComplex_d,
    SupportChainModels.ι_realize,
    OrderedCechTuple.boundary_single, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show Finsupp.single (Fin.removeNth i a.1) ((-1 : ℤ) ^ i.val * 1) =
      ((-1 : ℤ) ^ i.val) • Finsupp.single (Fin.removeNth i a.1) 1 by simp,
    map_zsmul]
  congr 1
  rw [SupportChainModels.realizeAux_single]
  unfold SupportChainModels.faceOrZero
  rw [dif_pos (by
    rw [tupleSupport_subset_iff]
    exact Set.range_comp_subset_range i.succAbove a.1),
    SupportChainModels.ιOrZero_of_mem]

lemma coordinateHyperplaneComplementPairCorrectionDegreeDesc_vertical
    (a : {a : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 a}) :
    (Sigma.ι
      (fun b : {b : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 b} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1)) a).f 1 ≫
      ((coordinateHyperplaneComplementCoverChainModels.cechComplex
        TupleClass.strictMono).X 1).d 1 0 ≫
      coordinateHyperplaneComplementPairCorrectionDegreeDesc =
        (coordinateHyperplaneComplementCoverChainModels.model
          (tupleSupport a.1)).d 1 0 ≫ coordinateHyperplaneComplementPairCorrection a := by
  change (Sigma.ι
      (fun b : {b : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 b} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1)) a).f 1 ≫
      (coordinateHyperplaneComplementCoverChainModels.cechObject
        TupleClass.strictMono 1).d 1 0 ≫
      coordinateHyperplaneComplementPairCorrectionDegreeDesc = _
  rw [← Category.assoc,
    (Sigma.ι
      (fun b : {b : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 b} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1)) a).comm 1 0,
    Category.assoc, coordinateHyperplaneComplementPairCorrectionDegreeDesc_ι]

/-- The restriction of the ambient pair winding, expressed on each literal complement-cover
pair intersection. -/
noncomputable def coordinateHyperplaneComplementAmbientPairWinding
    (a : {a : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 a}) :
    ((coordinateHyperplaneComplementCoverChainModels.model
      (tupleSupport a.1)).X 1) ⟶ ModuleCat.of ℚ ℚ := by
  rcases a with ⟨a, ha⟩
  classical
  by_cases h01 : a = ![0, 1]
  · subst a
    exact ChernWinding.windingIntegerCochain complementCoverPair01Transition
      complementCoverPair01Transition_ne_zero
  by_cases h02 : a = ![0, 2]
  · subst a
    exact ChernWinding.windingIntegerCochain complementCoverPair02Transition
      complementCoverPair02Transition_ne_zero
  by_cases h12 : a = ![1, 2]
  · subst a
    exact ChernWinding.windingIntegerCochain complementCoverPair12Transition
      complementCoverPair12Transition_ne_zero
  exact False.elim
    (h12 (((strictMono_finTwo_to_finThree_classify a ha).resolve_left h01).resolve_left h02))

lemma projectiveCoverPair01Winding_restricts_complement :
    (SSet.chainComplexMap (TopCat.toSSet.map
      (complementCoverIntersectionToAmbientIntersection ({0, 1} : Finset (Fin 3))))
      (ModuleCat.of ℚ ℚ)).f 1 ≫ projectiveCoverPair01Winding =
      ChernWinding.windingIntegerCochain complementCoverPair01Transition
        complementCoverPair01Transition_ne_zero := by
  let hnormal : ∀ z, (pair01Transition.comp
      (ChernWinding.topMap complementCoverPair01ToAnalyticPair)) z ≠ 0 :=
    fun z ↦ pair01Transition_ne_zero _
  rw [projectiveCoverPair01Winding, ← Category.assoc, ← HomologicalComplex.comp_f]
  unfold SSet.chainComplexMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  change (SSet.chainComplexMap (TopCat.toSSet.map
      (complementCoverIntersectionToAmbientIntersection ({0, 1} : Finset (Fin 3)) ≫
        projectiveCoverPair01ToAnalyticPair)) (ModuleCat.of ℚ ℚ)).f 1 ≫
      ChernWinding.windingIntegerCochain pair01Transition pair01Transition_ne_zero = _
  rw [ChernWinding.chainComplexMap_comp_windingIntegerCochain
    (g := pair01Transition) (hg := pair01Transition_ne_zero)
    (f := complementCoverIntersectionToAmbientIntersection ({0, 1} : Finset (Fin 3)) ≫
      projectiveCoverPair01ToAnalyticPair) (hgf := hnormal)]
  rfl

lemma projectiveCoverPair02Winding_restricts_complement :
    (SSet.chainComplexMap (TopCat.toSSet.map
      (complementCoverIntersectionToAmbientIntersection ({0, 2} : Finset (Fin 3))))
      (ModuleCat.of ℚ ℚ)).f 1 ≫ projectiveCoverPair02Winding =
      ChernWinding.windingIntegerCochain complementCoverPair02Transition
        complementCoverPair02Transition_ne_zero := by
  let hnormal : ∀ z, (pair02Transition.comp
      (ChernWinding.topMap complementCoverPair02ToAnalyticPair)) z ≠ 0 :=
    fun z ↦ pair02Transition_ne_zero _
  rw [projectiveCoverPair02Winding, ← Category.assoc, ← HomologicalComplex.comp_f]
  unfold SSet.chainComplexMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  change (SSet.chainComplexMap (TopCat.toSSet.map
      (complementCoverIntersectionToAmbientIntersection ({0, 2} : Finset (Fin 3)) ≫
        projectiveCoverPair02ToAnalyticPair)) (ModuleCat.of ℚ ℚ)).f 1 ≫
      ChernWinding.windingIntegerCochain pair02Transition pair02Transition_ne_zero = _
  rw [ChernWinding.chainComplexMap_comp_windingIntegerCochain
    (g := pair02Transition) (hg := pair02Transition_ne_zero)
    (f := complementCoverIntersectionToAmbientIntersection ({0, 2} : Finset (Fin 3)) ≫
      projectiveCoverPair02ToAnalyticPair) (hgf := hnormal)]
  rfl

lemma projectiveCoverPair12Winding_restricts_complement :
    (SSet.chainComplexMap (TopCat.toSSet.map
      (complementCoverIntersectionToAmbientIntersection ({1, 2} : Finset (Fin 3))))
      (ModuleCat.of ℚ ℚ)).f 1 ≫ projectiveCoverPair12Winding =
      ChernWinding.windingIntegerCochain complementCoverPair12Transition
        complementCoverPair12Transition_ne_zero := by
  let hnormal : ∀ z, (pair12Transition.comp
      (ChernWinding.topMap complementCoverPair12ToAnalyticOverlap)) z ≠ 0 :=
    fun z ↦ pair12Transition_ne_zero _
  rw [projectiveCoverPair12Winding, ← Category.assoc, ← HomologicalComplex.comp_f]
  unfold SSet.chainComplexMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  change (SSet.chainComplexMap (TopCat.toSSet.map
      (complementCoverIntersectionToAmbientIntersection ({1, 2} : Finset (Fin 3)) ≫
        projectiveCoverPair12ToAnalyticPair)) (ModuleCat.of ℚ ℚ)).f 1 ≫
      ChernWinding.windingIntegerCochain pair12Transition pair12Transition_ne_zero = _
  rw [ChernWinding.chainComplexMap_comp_windingIntegerCochain
    (g := pair12Transition) (hg := pair12Transition_ne_zero)
    (f := complementCoverIntersectionToAmbientIntersection ({1, 2} : Finset (Fin 3)) ≫
      projectiveCoverPair12ToAnalyticPair) (hgf := hnormal)]
  rfl

lemma projectiveCoverTripleDefect_restricts_complement :
    (SSet.chainComplexMap (TopCat.toSSet.map
      (complementCoverIntersectionToAmbientIntersection ({0, 1, 2} : Finset (Fin 3))))
      (ModuleCat.of ℚ ℚ)).f 0 ≫ projectiveCoverTripleDefect =
      complementCoverTripleDefect := by
  let h01 : ∀ z, (triple01Transition.comp
      (ChernWinding.topMap complementCoverTripleToAnalyticTriple)) z ≠ 0 :=
    fun z ↦ triple01Transition_ne_zero _
  let h12 : ∀ z, (triple12Transition.comp
      (ChernWinding.topMap complementCoverTripleToAnalyticTriple)) z ≠ 0 :=
    fun z ↦ triple12Transition_ne_zero _
  let h02 : ∀ z, (triple02Transition.comp
      (ChernWinding.topMap complementCoverTripleToAnalyticTriple)) z ≠ 0 :=
    fun z ↦ triple02Transition_ne_zero _
  let hmul : ∀ z, (triple02Transition.comp
      (ChernWinding.topMap complementCoverTripleToAnalyticTriple)) z =
        (triple01Transition.comp
          (ChernWinding.topMap complementCoverTripleToAnalyticTriple)) z *
        (triple12Transition.comp
          (ChernWinding.topMap complementCoverTripleToAnalyticTriple)) z :=
    fun z ↦ tripleTransition_product _
  rw [projectiveCoverTripleDefect, ← Category.assoc, ← HomologicalComplex.comp_f]
  unfold SSet.chainComplexMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  change (SSet.chainComplexMap (TopCat.toSSet.map complementCoverTripleToAnalyticTriple)
      (ModuleCat.of ℚ ℚ)).f 0 ≫
      ChernWinding.pointLogProductDefectVertexCochain
        triple01Transition triple12Transition triple02Transition
        triple01Transition_ne_zero triple12Transition_ne_zero triple02Transition_ne_zero
        tripleTransition_product = _
  rw [ChernWinding.chainComplexMap_comp_pointLogProductDefectVertexCochain
    complementCoverTripleToAnalyticTriple triple01Transition triple12Transition
    triple02Transition triple01Transition_ne_zero triple12Transition_ne_zero
    triple02Transition_ne_zero tripleTransition_product h01 h12 h02 hmul]
  exact ChernWinding.pointLogProductDefectVertexCochain_congr
    (triple01Transition.comp (ChernWinding.topMap complementCoverTripleToAnalyticTriple))
    (triple12Transition.comp (ChernWinding.topMap complementCoverTripleToAnalyticTriple))
    (triple02Transition.comp (ChernWinding.topMap complementCoverTripleToAnalyticTriple))
    complementCoverTriple01Transition complementCoverTriple12Transition
    complementCoverTriple02Transition h01 h12 h02
    complementCoverTriple01Transition_ne_zero complementCoverTriple12Transition_ne_zero
    complementCoverTriple02Transition_ne_zero hmul complementCoverTriple_transition_product
    complementCoverTriple01Transition_eq.symm complementCoverTriple12Transition_eq.symm
    complementCoverTriple02Transition_eq.symm

noncomputable def complementCoverTripleDefectTuple :
    ((coordinateHyperplaneComplementCoverChainModels.model
      (tupleSupport (![0, 1, 2] : Fin 3 → Fin 3))).X 0) ⟶ ModuleCat.of ℚ ℚ := by
  change (ChernWinding.singularChains coordinateHyperplaneComplementTripleTop).X 0 ⟶
    ModuleCat.of ℚ ℚ
  exact complementCoverTripleDefect

set_option maxHeartbeats 1000000 in
lemma coordinateHyperplaneComplementTriple_correction_transport
    (a12 a02 a01 : {a : Fin 2 → Fin 3 // TupleClass.strictMono.mem 1 a})
    (h12 : a12 = ⟨![1, 2], by decide⟩)
    (h02 : a02 = ⟨![0, 2], by decide⟩)
    (h01 : a01 = ⟨![0, 1], by decide⟩)
    (hs12 : (tupleSupport a12.1).1 ⊆
      (tupleSupport (![0, 1, 2] : Fin 3 → Fin 3)).1)
    (hs02 : (tupleSupport a02.1).1 ⊆
      (tupleSupport (![0, 1, 2] : Fin 3 → Fin 3)).1)
    (hs01 : (tupleSupport a01.1).1 ⊆
      (tupleSupport (![0, 1, 2] : Fin 3 → Fin 3)).1) :
    (coordinateHyperplaneComplementCoverChainModels.face hs12).f 0 ≫
        coordinateHyperplaneComplementPairCorrection a12 -
      (coordinateHyperplaneComplementCoverChainModels.face hs02).f 0 ≫
        coordinateHyperplaneComplementPairCorrection a02 +
      (coordinateHyperplaneComplementCoverChainModels.face hs01).f 0 ≫
        coordinateHyperplaneComplementPairCorrection a01 -
      complementCoverTripleDefectTuple = 0 := by
  subst a12
  subst a02
  subst a01
  change
    (SSet.chainComplexMap (TopCat.toSSet.map complementCoverTripleToPair12)
        (ModuleCat.of ℚ ℚ)).f 0 ≫ complementCoverPair12Correction -
      (SSet.chainComplexMap (TopCat.toSSet.map complementCoverTripleToPair02)
        (ModuleCat.of ℚ ℚ)).f 0 ≫ complementCoverPair02Correction +
      (SSet.chainComplexMap (TopCat.toSSet.map complementCoverTripleToPair01)
        (ModuleCat.of ℚ ℚ)).f 0 ≫ complementCoverPair01Correction -
      complementCoverTripleDefect = 0
  rw [← complementCoverPairCorrections_triple_relation]
  abel

set_option backward.isDefEq.respectTransparency false in
lemma coordinateHyperplaneComplementPairCorrection_outer_triple :
    (Sigma.ι
      (fun b : {b : Fin 3 → Fin 3 // TupleClass.strictMono.mem 2 b} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1))
      ⟨![0, 1, 2], by decide⟩).f 0 ≫
        ((coordinateHyperplaneComplementCoverChainModels.cechComplex
          TupleClass.strictMono).d 2 1).f 0 ≫
        coordinateHyperplaneComplementPairCorrectionDegreeDesc -
      complementCoverTripleDefectTuple = 0 := by
  rw [← Category.assoc, ← HomologicalComplex.comp_f,
    coordinateHyperplaneComplementCoverChainModels_ι_comp_outer_d 1
      ⟨![0, 1, 2], by decide⟩]
  rw [Fin.sum_univ_three, HomologicalComplex.add_f_apply,
    HomologicalComplex.add_f_apply, HomologicalComplex.zsmul_f_apply,
    HomologicalComplex.zsmul_f_apply, HomologicalComplex.zsmul_f_apply]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  norm_num
  rw [coordinateHyperplaneComplementPairCorrectionDegreeDesc_ι,
    coordinateHyperplaneComplementPairCorrectionDegreeDesc_ι,
    coordinateHyperplaneComplementPairCorrectionDegreeDesc_ι]
  simpa [sub_eq_add_neg] using coordinateHyperplaneComplementTriple_correction_transport
    ⟨Fin.removeNth 0 (![0, 1, 2] : Fin 3 → Fin 3), by decide⟩
    ⟨Fin.removeNth 1 (![0, 1, 2] : Fin 3 → Fin 3), by decide⟩
    ⟨Fin.removeNth 2 (![0, 1, 2] : Fin 3 → Fin 3), by decide⟩
    (by apply Subtype.ext; decide) (by apply Subtype.ext; decide)
    (by apply Subtype.ext; decide)
    (by
      rw [tupleSupport_subset_iff]
      exact Set.range_comp_subset_range
        (0 : Fin 3).succAbove (![0, 1, 2] : Fin 3 → Fin 3))
    (by
      rw [tupleSupport_subset_iff]
      exact Set.range_comp_subset_range
        (1 : Fin 3).succAbove (![0, 1, 2] : Fin 3 → Fin 3))
    (by
      rw [tupleSupport_subset_iff]
      exact Set.range_comp_subset_range
        (2 : Fin 3).succAbove (![0, 1, 2] : Fin 3 → Fin 3))

/-- The degree-one functional containing exactly the singleton winding part of the desired
complement cochain.  Its pair-overlap degree-zero component is currently zero, so this is not
yet the full cochain `β` satisfying `res(α) + dβ = 0`. -/
noncomputable def coordinateHyperplaneComplementSingletonFunctional :
    coordinateHyperplaneComplementCechTotal.X 1 ⟶ ModuleCat.of ℚ ℚ :=
  (coordinateHyperplaneComplementCoverChainModels.cechComplex
    TupleClass.strictMono).totalDesc
      (fun p q hpq ↦ by
        change p + q = 1 at hpq
        rcases p with _ | p
        · have hq : q = 1 := by omega
          subst q
          rw [SupportChainModels.cechComplex_X]
          exact coordinateHyperplaneComplementSingletonDegreeDesc
        rcases p with _ | p
        · have hq : q = 0 := by omega
          subst q
          exact 0
        omega)

/-- The literal degree-one complement cochain formed from the two known local normal winding
cochains.  This declaration contains no selected representative and no equality hypothesis. -/
noncomputable def coordinateHyperplaneComplementSingletonPart :
    coordinateHyperplaneComplementCechTotal.linearDualCochainComplex.X 1 :=
  coordinateHyperplaneComplementSingletonFunctional.hom

/-- The explicit degree-one complement functional with both components: the two singleton
normal winding cochains and the three signed degree-zero pair corrections.  This is a literal
functional on the normalized Čech total.  All three pair restriction identities and their
triple-overlap coherence are proved above; its final coboundary equation with the restricted
ambient functional is assembled and proved in `ProjectivePlaneRelativeCechCompatibility`. -/
noncomputable def coordinateHyperplaneComplementFullFunctional :
    coordinateHyperplaneComplementCechTotal.X 1 ⟶ ModuleCat.of ℚ ℚ :=
  (coordinateHyperplaneComplementCoverChainModels.cechComplex
    TupleClass.strictMono).totalDesc
      (fun p q hpq ↦ by
        change p + q = 1 at hpq
        rcases p with _ | p
        · have hq : q = 1 := by omega
          subst q
          rw [SupportChainModels.cechComplex_X]
          exact coordinateHyperplaneComplementSingletonDegreeDesc
        rcases p with _ | p
        · have hq : q = 0 := by omega
          subst q
          rw [SupportChainModels.cechComplex_X]
          exact coordinateHyperplaneComplementPairCorrectionDegreeDesc
        omega)

lemma coordinateHyperplaneComplementFullFunctional_singleton :
    (coordinateHyperplaneComplementCoverChainModels.cechComplex
      TupleClass.strictMono).ιTotal (ComplexShape.down ℕ) 0 1 1 (by norm_num) ≫
        coordinateHyperplaneComplementFullFunctional =
      coordinateHyperplaneComplementSingletonDegreeDesc := by
  rw [coordinateHyperplaneComplementFullFunctional, HomologicalComplex₂.ι_totalDesc]
  rfl

/-- On the actual `D₊(X₁)` singleton summand, the descended degree-one complement component
is exactly the pullback of the literal first-chart winding functional.  This is the raw component
calculation needed by a future one-chart contraction map. -/
lemma coordinateHyperplaneComplementSingletonDegreeDesc_firstChart :
    (Sigma.ι
      (fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1))
      ⟨![1], by decide⟩).f 1 ≫
      coordinateHyperplaneComplementSingletonDegreeDesc =
        complementCoverSingletonOneWindingTuple := by
  rw [coordinateHyperplaneComplementSingletonDegreeDesc_ι]
  simp [coordinateHyperplaneComplementSingletonCochain]

/-- The symmetric raw singleton calculation on `D₊(X₂)`. -/
lemma coordinateHyperplaneComplementSingletonDegreeDesc_secondChart :
    (Sigma.ι
      (fun b : {b : Fin 1 → Fin 3 // TupleClass.strictMono.mem 0 b} ↦
        coordinateHyperplaneComplementCoverChainModels.model (tupleSupport b.1))
      ⟨![2], by decide⟩).f 1 ≫
      coordinateHyperplaneComplementSingletonDegreeDesc =
        complementCoverSingletonTwoWindingTuple := by
  rw [coordinateHyperplaneComplementSingletonDegreeDesc_ι]
  simp [coordinateHyperplaneComplementSingletonCochain]


lemma coordinateHyperplaneComplementFullFunctional_pair :
    (coordinateHyperplaneComplementCoverChainModels.cechComplex
      TupleClass.strictMono).ιTotal (ComplexShape.down ℕ) 1 0 1 (by norm_num) ≫
        coordinateHyperplaneComplementFullFunctional =
      coordinateHyperplaneComplementPairCorrectionDegreeDesc := by
  rw [coordinateHyperplaneComplementFullFunctional, HomologicalComplex₂.ι_totalDesc]
  rfl


/-- The same fully explicit complement functional as an element of the linear-dual cochain
complex. -/
noncomputable def coordinateHyperplaneComplementFullPart :
    coordinateHyperplaneComplementCechTotal.linearDualCochainComplex.X 1 :=
  coordinateHyperplaneComplementFullFunctional.hom

end AlgebraicGeometry.ProjectivePlane.CoordinateCharts
