/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Other.AlgebraicGeometry.ProjectivePlaneAnalyticNormalization
import Other.AlgebraicGeometry.ProjectivePlaneExplicitClassSheafRestriction
import Other.AlgebraicTopology.NormalChartWindingClass
import Other.AlgebraicTopology.WindingRelativeClassNaturality

/-!
# Local normalization of the explicit coordinate-hyperplane cocycle

On each of the two standard affine charts meeting `X₀ = 0`, restriction of the literal
winding class to an explicit flattened neighborhood is the normalized normal-projection
coclass.  This is the local comparison needed to identify the explicit supported sheaf section
with the canonical smooth-closed support section.
-/

@[expose] noncomputable section

open CategoryTheory Topology TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ProjectivePlane.CoordinateCharts

open AlgebraicGeometry.ComplexPoint
open AlgebraicGeometry.ProjectivePlane.AnalyticNormalization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Inclusion of a flattened first-chart neighborhood into the whole punctured first chart. -/
def firstFlattenedNeighborhoodToChartPair
    (x : ComplexPoint (analyticChart 1)) (hx : x ∈ (chartFlattening 1).source) :
    ChernWinding.supportPair
        ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx :
          Opens (ComplexPoint (analyticChart 1))) : Set _)
        (chartHyperplaneSupport 1) ⟶ firstChartHyperplanePair := by
  let hmem : ∀ w : (ChernWinding.supportPair
      ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx :
        Opens (ComplexPoint (analyticChart 1))) : Set _)
      (chartHyperplaneSupport 1)).snd, w.1.1 ∈ firstNormalComplement := by
    intro w
    change chartCoordinateValue 1 0 w.1.1 ≠ 0
    exact w.2
  refine TopPair.ofHom
    (TopCat.ofHom ⟨fun w ↦ w.1, continuous_subtype_val⟩)
    (TopCat.ofHom ⟨fun w ↦ ⟨w.1.1, hmem w⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk hmem⟩) rfl

/-- Inclusion of a flattened second-chart neighborhood into the whole punctured second chart. -/
def secondFlattenedNeighborhoodToChartPair
    (x : ComplexPoint (analyticChart 2)) (hx : x ∈ (chartFlattening 2).source) :
    ChernWinding.supportPair
        ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx :
          Opens (ComplexPoint (analyticChart 2))) : Set _)
        (chartHyperplaneSupport 2) ⟶ secondChartHyperplanePair := by
  let hmem : ∀ w : (ChernWinding.supportPair
      ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx :
        Opens (ComplexPoint (analyticChart 2))) : Set _)
      (chartHyperplaneSupport 2)).snd, w.1.1 ∈ secondNormalComplement := by
    intro w
    change chartCoordinateValue 2 0 w.1.1 ≠ 0
    exact w.2
  refine TopPair.ofHom
    (TopCat.ofHom ⟨fun w ↦ w.1, continuous_subtype_val⟩)
    (TopCat.ofHom ⟨fun w ↦ ⟨w.1.1, hmem w⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk hmem⟩) rfl

lemma firstNormalOnComplement_pullback_flattened
    (x : ComplexPoint (analyticChart 1)) (hx : x ∈ (chartFlattening 1).source) :
    firstNormalOnComplement.comp
        (ChernWinding.topMap
          (TopPair.Hom.snd (firstFlattenedNeighborhoodToChartPair x hx))) =
      ChernWinding.flattenedNormalCoordinate (Fin 1 → ℂ) (chartFlattening 1)
        (chartFlattening_support_iff 1) x hx := by
  ext w
  symm
  change ((chartFlattening 1 w.1.1).2) 0 = chartCoordinateValue 1 0 w.1.1
  rw [chartFlattening_normal_eq_coordinate]

lemma secondNormalOnComplement_pullback_flattened
    (x : ComplexPoint (analyticChart 2)) (hx : x ∈ (chartFlattening 2).source) :
    secondNormalOnComplement.comp
        (ChernWinding.topMap
          (TopPair.Hom.snd (secondFlattenedNeighborhoodToChartPair x hx))) =
      ChernWinding.flattenedNormalCoordinate (Fin 1 → ℂ) (chartFlattening 2)
        (chartFlattening_support_iff 2) x hx := by
  ext w
  symm
  change ((chartFlattening 2 w.1.1).2) 0 = chartCoordinateValue 2 0 w.1.1
  rw [chartFlattening_normal_eq_coordinate]

private lemma windingRelativeCochainClass_congr
    {P : TopPair} (g h : C(P.snd, ℂ))
    (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0) (e : g = h) :
    ChernWinding.windingRelativeCochainClass (X := P) g hg =
      ChernWinding.windingRelativeCochainClass (X := P) h hh := by
  subst h
  rfl

/-- The literal first-chart winding class has the canonical positive normal normalization on
every explicit flattened neighborhood centered on the hyperplane. -/
theorem firstChartHyperplaneRelativeSingularClass_restrict_flattened
    (x : ComplexPoint (analyticChart 1)) (hx : x ∈ (chartFlattening 1).source)
    (h0 : (chartFlattening 1 x).2 = 0) :
    relativeCohomologyMap ℚ 2 (firstFlattenedNeighborhoodToChartPair x hx)
        firstChartHyperplaneRelativeSingularClass =
      chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (chartFlattening 1)
        (chartHyperplaneSupport 1) (chartFlattening_support_iff 1)
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx)
        (flattenedSupportNeighborhood_subset_source
          (Fin 1 → ℂ) 1 (chartFlattening 1) x hx) := by
  rw [show firstChartHyperplaneRelativeSingularClass =
      ChernWinding.windingRelativeCochainClass
        (X := firstChartHyperplanePair)
        firstNormalOnComplement firstNormalOnComplement_ne_zero from rfl]
  rw [ChernWinding.relativeCohomologyMap_windingRelativeCochainClass]
  exact (windingRelativeCochainClass_congr _ _ _ _
    (firstNormalOnComplement_pullback_flattened x hx)).trans
      (ChernWinding.flattenedNormalCoordinate_cochainClass_eq_chartNormalProjectionCoclass
        (Fin 1 → ℂ) (chartFlattening 1) (chartFlattening_support_iff 1) x hx h0)

/-- The literal second-chart winding class has the same canonical positive normal
normalization. -/
theorem secondChartHyperplaneRelativeSingularClass_restrict_flattened
    (x : ComplexPoint (analyticChart 2)) (hx : x ∈ (chartFlattening 2).source)
    (h0 : (chartFlattening 2 x).2 = 0) :
    relativeCohomologyMap ℚ 2 (secondFlattenedNeighborhoodToChartPair x hx)
        secondChartHyperplaneRelativeSingularClass =
      chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (chartFlattening 2)
        (chartHyperplaneSupport 2) (chartFlattening_support_iff 2)
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx)
        (flattenedSupportNeighborhood_subset_source
          (Fin 1 → ℂ) 1 (chartFlattening 2) x hx) := by
  rw [show secondChartHyperplaneRelativeSingularClass =
      ChernWinding.windingRelativeCochainClass
        (X := secondChartHyperplanePair)
        secondNormalOnComplement secondNormalOnComplement_ne_zero from rfl]
  rw [ChernWinding.relativeCohomologyMap_windingRelativeCochainClass]
  exact (windingRelativeCochainClass_congr _ _ _ _
    (secondNormalOnComplement_pullback_flattened x hx)).trans
      (ChernWinding.flattenedNormalCoordinate_cochainClass_eq_chartNormalProjectionCoclass
        (Fin 1 → ℂ) (chartFlattening 2) (chartFlattening_support_iff 2) x hx h0)

private def firstFlattenedNeighborhoodToTopChartPair
    (x : ComplexPoint (analyticChart 1)) (hx : x ∈ (chartFlattening 1).source) :
    neighborhoodSupportComplementPair
        ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx :
          Opens (ComplexPoint (analyticChart 1))) : Set _)
        firstNormalComplementᶜ ⟶ firstChartHyperplanePair :=
  neighborhoodSupportInclusionPairMap
      (show (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx :
        Opens (ComplexPoint (analyticChart 1))) ≤ ⊤ from le_top)
      firstNormalComplementᶜ ≫
    (topOpenComplementSupportPairIso
      (TopCat.of (ComplexPoint (analyticChart 1))) firstNormalComplement).hom

private def secondFlattenedNeighborhoodToTopChartPair
    (x : ComplexPoint (analyticChart 2)) (hx : x ∈ (chartFlattening 2).source) :
    neighborhoodSupportComplementPair
        ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx :
          Opens (ComplexPoint (analyticChart 2))) : Set _)
        secondNormalComplementᶜ ⟶ secondChartHyperplanePair :=
  neighborhoodSupportInclusionPairMap
      (show (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx :
        Opens (ComplexPoint (analyticChart 2))) ≤ ⊤ from le_top)
      secondNormalComplementᶜ ≫
    (topOpenComplementSupportPairIso
      (TopCat.of (ComplexPoint (analyticChart 2))) secondNormalComplement).hom

private lemma chartFlattening_support_iff_firstComplement
    (z : ComplexPoint (analyticChart 1)) (hz : z ∈ (chartFlattening 1).source) :
    z ∈ firstNormalComplementᶜ ↔ (chartFlattening 1 z).2 = 0 := by
  rw [← chartHyperplaneSupport_one_eq_compl]
  exact chartFlattening_support_iff 1 z hz

private lemma chartFlattening_support_iff_secondComplement
    (z : ComplexPoint (analyticChart 2)) (hz : z ∈ (chartFlattening 2).source) :
    z ∈ secondNormalComplementᶜ ↔ (chartFlattening 2 z).2 = 0 := by
  rw [← chartHyperplaneSupport_two_eq_compl]
  exact chartFlattening_support_iff 2 z hz

private lemma firstTopNormal_pullback_flattened
    (x : ComplexPoint (analyticChart 1)) (hx : x ∈ (chartFlattening 1).source) :
    firstNormalOnComplement.comp
        (ChernWinding.topMap
          (TopPair.Hom.snd (firstFlattenedNeighborhoodToTopChartPair x hx))) =
      ChernWinding.flattenedNormalCoordinate (Fin 1 → ℂ) (chartFlattening 1)
        chartFlattening_support_iff_firstComplement x hx := by
  ext w
  symm
  change ((chartFlattening 1 w.1.1).2) 0 = chartCoordinateValue 1 0 w.1.1
  rw [chartFlattening_normal_eq_coordinate]

private lemma secondTopNormal_pullback_flattened
    (x : ComplexPoint (analyticChart 2)) (hx : x ∈ (chartFlattening 2).source) :
    secondNormalOnComplement.comp
        (ChernWinding.topMap
          (TopPair.Hom.snd (secondFlattenedNeighborhoodToTopChartPair x hx))) =
      ChernWinding.flattenedNormalCoordinate (Fin 1 → ℂ) (chartFlattening 2)
        chartFlattening_support_iff_secondComplement x hx := by
  ext w
  symm
  change ((chartFlattening 2 w.1.1).2) 0 = chartCoordinateValue 2 0 w.1.1
  rw [chartFlattening_normal_eq_coordinate]

/-- Restricting the top-open version of the first winding class to a flattened neighborhood
is exactly the normal-projection coclass. -/
theorem firstChartHyperplaneTopClass_restrict_flattened
    (x : ComplexPoint (analyticChart 1)) (hx : x ∈ (chartFlattening 1).source)
    (h0 : (chartFlattening 1 x).2 = 0) :
    relativeCohomologyMap ℚ 2
        (neighborhoodSupportInclusionPairMap
          (show (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx :
            Opens (ComplexPoint (analyticChart 1))) ≤ ⊤ from le_top)
          firstNormalComplementᶜ)
        (relativeCohomologyMap ℚ 2
          (topOpenComplementSupportPairIso
            (TopCat.of (ComplexPoint (analyticChart 1))) firstNormalComplement).hom
          firstChartHyperplaneRelativeSingularClass) =
      chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (chartFlattening 1)
        firstNormalComplementᶜ chartFlattening_support_iff_firstComplement
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx)
        (flattenedSupportNeighborhood_subset_source
          (Fin 1 → ℂ) 1 (chartFlattening 1) x hx) := by
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  change relativeCohomologyMap ℚ 2 (firstFlattenedNeighborhoodToTopChartPair x hx)
      firstChartHyperplaneRelativeSingularClass = _
  rw [show firstChartHyperplaneRelativeSingularClass =
      ChernWinding.windingRelativeCochainClass
        (X := firstChartHyperplanePair)
        firstNormalOnComplement firstNormalOnComplement_ne_zero from rfl]
  rw [ChernWinding.relativeCohomologyMap_windingRelativeCochainClass]
  exact (windingRelativeCochainClass_congr _ _ _ _
    (firstTopNormal_pullback_flattened x hx)).trans
      (ChernWinding.flattenedNormalCoordinate_cochainClass_eq_chartNormalProjectionCoclass
        (Fin 1 → ℂ) (chartFlattening 1)
        chartFlattening_support_iff_firstComplement x hx h0)

/-- Restricting the top-open version of the second winding class to a flattened neighborhood
is exactly the normal-projection coclass. -/
theorem secondChartHyperplaneTopClass_restrict_flattened
    (x : ComplexPoint (analyticChart 2)) (hx : x ∈ (chartFlattening 2).source)
    (h0 : (chartFlattening 2 x).2 = 0) :
    relativeCohomologyMap ℚ 2
        (neighborhoodSupportInclusionPairMap
          (show (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx :
            Opens (ComplexPoint (analyticChart 2))) ≤ ⊤ from le_top)
          secondNormalComplementᶜ)
        (relativeCohomologyMap ℚ 2
          (topOpenComplementSupportPairIso
            (TopCat.of (ComplexPoint (analyticChart 2))) secondNormalComplement).hom
          secondChartHyperplaneRelativeSingularClass) =
      chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (chartFlattening 2)
        secondNormalComplementᶜ chartFlattening_support_iff_secondComplement
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx)
        (flattenedSupportNeighborhood_subset_source
          (Fin 1 → ℂ) 1 (chartFlattening 2) x hx) := by
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  change relativeCohomologyMap ℚ 2 (secondFlattenedNeighborhoodToTopChartPair x hx)
      secondChartHyperplaneRelativeSingularClass = _
  rw [show secondChartHyperplaneRelativeSingularClass =
      ChernWinding.windingRelativeCochainClass
        (X := secondChartHyperplanePair)
        secondNormalOnComplement secondNormalOnComplement_ne_zero from rfl]
  rw [ChernWinding.relativeCohomologyMap_windingRelativeCochainClass]
  exact (windingRelativeCochainClass_congr _ _ _ _
    (secondTopNormal_pullback_flattened x hx)).trans
      (ChernWinding.flattenedNormalCoordinate_cochainClass_eq_chartNormalProjectionCoclass
        (Fin 1 → ℂ) (chartFlattening 2)
        chartFlattening_support_iff_secondComplement x hx h0)

/-- The intrinsic first-chart winding sheaf section restricts on a flattened neighborhood
to the sheafification of the normalized normal-projection coclass. -/
theorem firstChartHyperplaneWindingSheafSection_restrict_flattened
    (x : ComplexPoint (analyticChart 1)) (hx : x ∈ (chartFlattening 1).source)
    (h0 : (chartFlattening 1 x).2 = 0) :
    (supportRelativeCohomologySheaf
      (TopCat.of (ComplexPoint (analyticChart 1))) firstNormalComplementᶜ 2).obj.map
      (homOfLE (show
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx :
          Opens (ComplexPoint (analyticChart 1))) ≤ ⊤ from le_top)).op
      firstChartHyperplaneWindingSheafSection =
    (supportRelativeCohomologyToSheaf
      (TopCat.of (ComplexPoint (analyticChart 1))) firstNormalComplementᶜ 2).app
      (op (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx))
      (chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (chartFlattening 1)
        firstNormalComplementᶜ chartFlattening_support_iff_firstComplement
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx)
        (flattenedSupportNeighborhood_subset_source
          (Fin 1 → ℂ) 1 (chartFlattening 1) x hx)) := by
  let a := relativeCohomologyMap ℚ 2
    (topOpenComplementSupportPairIso
      (TopCat.of (ComplexPoint (analyticChart 1))) firstNormalComplement).hom
    firstChartHyperplaneRelativeSingularClass
  have h := ConcreteCategory.congr_hom
    ((supportRelativeCohomologyToSheaf
      (TopCat.of (ComplexPoint (analyticChart 1))) firstNormalComplementᶜ 2).naturality
      (homOfLE (show
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx :
          Opens (ComplexPoint (analyticChart 1))) ≤ ⊤ from le_top)).op) a
  simp only [ConcreteCategory.comp_apply] at h
  unfold firstChartHyperplaneWindingSheafSection
  calc
    _ = (supportRelativeCohomologyToSheaf
        (TopCat.of (ComplexPoint (analyticChart 1))) firstNormalComplementᶜ 2).app
        (op (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx))
        (relativeCohomologyMap ℚ 2
          (neighborhoodSupportInclusionPairMap
            (show (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx :
              Opens (ComplexPoint (analyticChart 1))) ≤ ⊤ from le_top)
            firstNormalComplementᶜ) a) := h.symm
    _ = _ := congrArg _ (firstChartHyperplaneTopClass_restrict_flattened x hx h0)

/-- The analogous normalized restriction statement on the second affine chart. -/
theorem secondChartHyperplaneWindingSheafSection_restrict_flattened
    (x : ComplexPoint (analyticChart 2)) (hx : x ∈ (chartFlattening 2).source)
    (h0 : (chartFlattening 2 x).2 = 0) :
    (supportRelativeCohomologySheaf
      (TopCat.of (ComplexPoint (analyticChart 2))) secondNormalComplementᶜ 2).obj.map
      (homOfLE (show
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx :
          Opens (ComplexPoint (analyticChart 2))) ≤ ⊤ from le_top)).op
      secondChartHyperplaneWindingSheafSection =
    (supportRelativeCohomologyToSheaf
      (TopCat.of (ComplexPoint (analyticChart 2))) secondNormalComplementᶜ 2).app
      (op (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx))
      (chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (chartFlattening 2)
        secondNormalComplementᶜ chartFlattening_support_iff_secondComplement
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx)
        (flattenedSupportNeighborhood_subset_source
          (Fin 1 → ℂ) 1 (chartFlattening 2) x hx)) := by
  let a := relativeCohomologyMap ℚ 2
    (topOpenComplementSupportPairIso
      (TopCat.of (ComplexPoint (analyticChart 2))) secondNormalComplement).hom
    secondChartHyperplaneRelativeSingularClass
  have h := ConcreteCategory.congr_hom
    ((supportRelativeCohomologyToSheaf
      (TopCat.of (ComplexPoint (analyticChart 2))) secondNormalComplementᶜ 2).naturality
      (homOfLE (show
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx :
          Opens (ComplexPoint (analyticChart 2))) ≤ ⊤ from le_top)).op) a
  simp only [ConcreteCategory.comp_apply] at h
  unfold secondChartHyperplaneWindingSheafSection
  calc
    _ = (supportRelativeCohomologyToSheaf
        (TopCat.of (ComplexPoint (analyticChart 2))) secondNormalComplementᶜ 2).app
        (op (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx))
        (relativeCohomologyMap ℚ 2
          (neighborhoodSupportInclusionPairMap
            (show (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx :
              Opens (ComplexPoint (analyticChart 2))) ≤ ⊤ from le_top)
            secondNormalComplementᶜ) a) := h.symm
    _ = _ := congrArg _ (secondChartHyperplaneTopClass_restrict_flattened x hx h0)

lemma firstFlattened_image_subset_ambientSource
    (x : ComplexPoint (analyticChart 1)) (hx : x ∈ (chartFlattening 1).source) :
    (firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
      (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx) : Set _) ⊆
        (ambientChartFlattening 1).source := by
  rintro y ⟨z, hz, rfl⟩
  exact ⟨z, flattenedSupportNeighborhood_subset_source
    (Fin 1 → ℂ) 1 (chartFlattening 1) x hx hz, rfl⟩

set_option maxHeartbeats 800000 in
/-- Open-embedding transport of the intrinsic first-chart normal coclass is literally the
ambient lifted-chart normal coclass. -/
theorem firstChartNormalCoclass_openTransport
    (x : ComplexPoint (analyticChart 1)) (hx : x ∈ (chartFlattening 1).source) :
    (supportRelativeCohomologyPresheafOpenIso firstChartAnalyticOpenEmbeddingMap
      firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding
      coordinateHyperplaneAnalyticSupport firstNormalComplementᶜ
      firstChartAnalyticOpenEmbeddingMap_preimage_support 2).inv.app
      (op (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx))
      (chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (chartFlattening 1)
        firstNormalComplementᶜ chartFlattening_support_iff_firstComplement
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx)
        (flattenedSupportNeighborhood_subset_source
          (Fin 1 → ℂ) 1 (chartFlattening 1) x hx)) =
    chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (ambientChartFlattening 1)
      coordinateHyperplaneAnalyticSupport ambientChartFlattening_one_support_iff
      (firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx))
      (firstFlattened_image_subset_ambientSource x hx) := by
  rw [supportRelativeCohomologyPresheafOpenIso_inv_app]
  unfold chartNormalProjectionCoclass
  let E := neighborhoodSupportPairImageIso firstChartAnalyticOpenEmbeddingMap
    firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.isEmbedding
    ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx :
      Opens (ComplexPoint (analyticChart 1))) : Set _)
    firstNormalComplementᶜ coordinateHyperplaneAnalyticSupport
    (fun y _ ↦ by rw [← firstChartAnalyticOpenEmbeddingMap_preimage_support]; rfl)
  let P := E.inv
  let Q := chartNormalProjectionPair (Fin 1 → ℂ) 1 (chartFlattening 1)
    firstNormalComplementᶜ chartFlattening_support_iff_firstComplement
    ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx :
      Opens (ComplexPoint (analyticChart 1))) : Set _)
    (flattenedSupportNeighborhood_subset_source
      (Fin 1 → ℂ) 1 (chartFlattening 1) x hx)
  let Q' := chartNormalProjectionPair (Fin 1 → ℂ) 1 (ambientChartFlattening 1)
    coordinateHyperplaneAnalyticSupport ambientChartFlattening_one_support_iff
    (firstChartAnalyticOpenEmbeddingMap ''
      ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx :
        Opens (ComplexPoint (analyticChart 1))) : Set _))
    (by
      rintro y ⟨z, hz, rfl⟩
      exact ⟨z, flattenedSupportNeighborhood_subset_source
        (Fin 1 → ℂ) 1 (chartFlattening 1) x hx hz, rfl⟩)
  have hImage : ∀ w : {z : ComplexPoint (analyticChart 1) //
      z ∈ (flattenedSupportNeighborhood (Fin 1 → ℂ) 1
        (chartFlattening 1) x hx : Set (ComplexPoint (analyticChart 1)))},
      ((firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.homeomorphImage
        ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx :
          Opens (ComplexPoint (analyticChart 1))) : Set _) w : _) : _) =
        firstChartAnalyticOpenEmbeddingMap (w : ComplexPoint (analyticChart 1)) := by
    intro w
    rfl
  have hComplementImage : ∀ w : {z : {y : ComplexPoint (analyticChart 1) //
      y ∈ (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx :
        Set (ComplexPoint (analyticChart 1)))} |
        (z : ComplexPoint (analyticChart 1)) ∉ firstNormalComplementᶜ},
      ((neighborhoodSupportComplementImageHomeomorph
        firstChartAnalyticOpenEmbeddingMap
        firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.isEmbedding
        ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx :
          Opens (ComplexPoint (analyticChart 1))) : Set _)
        firstNormalComplementᶜ coordinateHyperplaneAnalyticSupport
        (fun y _ ↦ by rw [← firstChartAnalyticOpenEmbeddingMap_preimage_support]; rfl)
        w : _) : _) = firstChartAnalyticOpenEmbeddingMap
          (w : ComplexPoint (analyticChart 1)) := by
    intro w
    rfl
  have hchart (z : ComplexPoint (analyticChart 1)) :
      firstChartAnalyticOpenEmbeddingMap z = chartEmbeddingMap 1 z := by
    rfl
  have hQ : Q = E.hom ≫ Q' := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w
      apply Subtype.ext
      simp [Q, Q', E, chartNormalProjectionPair,
        neighborhoodSupportPairImageIso, neighborhoodSupportComplementImageHomeomorph,
        TopPair.ofHom, MorphismProperty.Comma.Hom.hom,
        MorphismProperty.Arrow.homMk, CategoryTheory.Arrow.homMk,
        TopCat.hom_comp, TopCat.hom_ofHom,
        CategoryTheory.ConcreteCategory.hom_ofHom,
        ambientChartFlattening_apply, hImage, hComplementImage]
      change (chartFlattening 1 w.1.1).2 =
        (ambientChartFlattening 1 (firstChartAnalyticOpenEmbeddingMap w.1.1)).2
      rw [hchart (w.1.1)]
      rw [ambientChartFlattening_apply]
    · ext w
      simp [Q, Q', E, chartNormalProjectionPair,
        neighborhoodSupportPairImageIso, neighborhoodSupportComplementImageHomeomorph,
        TopPair.ofHom, MorphismProperty.Comma.Hom.hom,
        MorphismProperty.Arrow.homMk, CategoryTheory.Arrow.homMk,
        TopCat.hom_comp, TopCat.hom_ofHom,
        CategoryTheory.ConcreteCategory.hom_ofHom,
        ambientChartFlattening_apply, hImage, hComplementImage]
      congr 1
      ext z
      change (chartFlattening 1 z.1).2 =
        (ambientChartFlattening 1 (firstChartAnalyticOpenEmbeddingMap z.1)).2
      rw [hchart (z.1), ambientChartFlattening_apply]
  have hPQ : P ≫ Q = Q' := by
    rw [hQ]
    dsimp only [P]
    simpa only [Category.assoc] using E.inv_hom_id_assoc Q'
  change (relativeCohomologyMap ℚ 2 P) ((relativeCohomologyMap ℚ 2 Q) _) =
    (relativeCohomologyMap ℚ 2 Q') _
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hPQ]

lemma secondFlattened_image_subset_ambientSource
    (x : ComplexPoint (analyticChart 2)) (hx : x ∈ (chartFlattening 2).source) :
    (secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
      (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx) : Set _) ⊆
        (ambientChartFlattening 2).source := by
  rintro y ⟨z, hz, rfl⟩
  exact ⟨z, flattenedSupportNeighborhood_subset_source
    (Fin 1 → ℂ) 1 (chartFlattening 2) x hx hz, rfl⟩

set_option maxHeartbeats 800000 in
/-- Open-embedding transport of the intrinsic second-chart normal coclass is literally the
ambient lifted-chart normal coclass. -/
theorem secondChartNormalCoclass_openTransport
    (x : ComplexPoint (analyticChart 2)) (hx : x ∈ (chartFlattening 2).source) :
    (supportRelativeCohomologyPresheafOpenIso secondChartAnalyticOpenEmbeddingMap
      secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding
      coordinateHyperplaneAnalyticSupport secondNormalComplementᶜ
      secondChartAnalyticOpenEmbeddingMap_preimage_support 2).inv.app
      (op (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx))
      (chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (chartFlattening 2)
        secondNormalComplementᶜ chartFlattening_support_iff_secondComplement
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx)
        (flattenedSupportNeighborhood_subset_source
          (Fin 1 → ℂ) 1 (chartFlattening 2) x hx)) =
    chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (ambientChartFlattening 2)
      coordinateHyperplaneAnalyticSupport ambientChartFlattening_two_support_iff
      (secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx))
      (secondFlattened_image_subset_ambientSource x hx) := by
  rw [supportRelativeCohomologyPresheafOpenIso_inv_app]
  unfold chartNormalProjectionCoclass
  let E := neighborhoodSupportPairImageIso secondChartAnalyticOpenEmbeddingMap
    secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.isEmbedding
    ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx :
      Opens (ComplexPoint (analyticChart 2))) : Set _)
    secondNormalComplementᶜ coordinateHyperplaneAnalyticSupport
    (fun y _ ↦ by rw [← secondChartAnalyticOpenEmbeddingMap_preimage_support]; rfl)
  let P := E.inv
  let Q := chartNormalProjectionPair (Fin 1 → ℂ) 1 (chartFlattening 2)
    secondNormalComplementᶜ chartFlattening_support_iff_secondComplement
    ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx :
      Opens (ComplexPoint (analyticChart 2))) : Set _)
    (flattenedSupportNeighborhood_subset_source
      (Fin 1 → ℂ) 1 (chartFlattening 2) x hx)
  let Q' := chartNormalProjectionPair (Fin 1 → ℂ) 1 (ambientChartFlattening 2)
    coordinateHyperplaneAnalyticSupport ambientChartFlattening_two_support_iff
    (secondChartAnalyticOpenEmbeddingMap ''
      ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx :
        Opens (ComplexPoint (analyticChart 2))) : Set _))
    (by
      rintro y ⟨z, hz, rfl⟩
      exact ⟨z, flattenedSupportNeighborhood_subset_source
        (Fin 1 → ℂ) 1 (chartFlattening 2) x hx hz, rfl⟩)
  have hImage : ∀ w : {z : ComplexPoint (analyticChart 2) //
      z ∈ (flattenedSupportNeighborhood (Fin 1 → ℂ) 1
        (chartFlattening 2) x hx : Set (ComplexPoint (analyticChart 2)))},
      ((secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.homeomorphImage
        ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx :
          Opens (ComplexPoint (analyticChart 2))) : Set _) w : _) : _) =
        secondChartAnalyticOpenEmbeddingMap (w : ComplexPoint (analyticChart 2)) := by
    intro w
    rfl
  have hComplementImage : ∀ w : {z : {y : ComplexPoint (analyticChart 2) //
      y ∈ (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx :
        Set (ComplexPoint (analyticChart 2)))} |
        (z : ComplexPoint (analyticChart 2)) ∉ secondNormalComplementᶜ},
      ((neighborhoodSupportComplementImageHomeomorph
        secondChartAnalyticOpenEmbeddingMap
        secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.isEmbedding
        ((flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx :
          Opens (ComplexPoint (analyticChart 2))) : Set _)
        secondNormalComplementᶜ coordinateHyperplaneAnalyticSupport
        (fun y _ ↦ by rw [← secondChartAnalyticOpenEmbeddingMap_preimage_support]; rfl)
        w : _) : _) = secondChartAnalyticOpenEmbeddingMap
          (w : ComplexPoint (analyticChart 2)) := by
    intro w
    rfl
  have hchart (z : ComplexPoint (analyticChart 2)) :
      secondChartAnalyticOpenEmbeddingMap z = chartEmbeddingMap 2 z := by
    rfl
  have hQ : Q = E.hom ≫ Q' := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w
      apply Subtype.ext
      simp [Q, Q', E, chartNormalProjectionPair,
        neighborhoodSupportPairImageIso, neighborhoodSupportComplementImageHomeomorph,
        TopPair.ofHom, MorphismProperty.Comma.Hom.hom,
        MorphismProperty.Arrow.homMk, CategoryTheory.Arrow.homMk,
        TopCat.hom_comp, TopCat.hom_ofHom,
        CategoryTheory.ConcreteCategory.hom_ofHom,
        ambientChartFlattening_apply, hImage, hComplementImage]
      change (chartFlattening 2 w.1.1).2 =
        (ambientChartFlattening 2 (secondChartAnalyticOpenEmbeddingMap w.1.1)).2
      rw [hchart (w.1.1)]
      rw [ambientChartFlattening_apply]
    · ext w
      simp [Q, Q', E, chartNormalProjectionPair,
        neighborhoodSupportPairImageIso, neighborhoodSupportComplementImageHomeomorph,
        TopPair.ofHom, MorphismProperty.Comma.Hom.hom,
        MorphismProperty.Arrow.homMk, CategoryTheory.Arrow.homMk,
        TopCat.hom_comp, TopCat.hom_ofHom,
        CategoryTheory.ConcreteCategory.hom_ofHom,
        ambientChartFlattening_apply, hImage, hComplementImage]
      congr 1
      ext z
      change (chartFlattening 2 z.1).2 =
        (ambientChartFlattening 2 (secondChartAnalyticOpenEmbeddingMap z.1)).2
      rw [hchart (z.1), ambientChartFlattening_apply]
  have hPQ : P ≫ Q = Q' := by
    rw [hQ]
    dsimp only [P]
    simpa only [Category.assoc] using E.inv_hom_id_assoc Q'
  change (relativeCohomologyMap ℚ 2 P) ((relativeCohomologyMap ℚ 2 Q) _) =
    (relativeCohomologyMap ℚ 2 Q') _
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hPQ]

/-- On the ambient image of a flattened first-chart neighborhood, the global explicit
section is the sheafification of the transported normal-projection coclass. -/
theorem coordinateHyperplaneExplicitSupportedSheafSection_restrict_firstFlattened
    (x : ComplexPoint (analyticChart 1)) (hx : x ∈ (chartFlattening 1).source)
    (h0 : (chartFlattening 1 x).2 = 0) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).obj.map
      (homOfLE (show
        firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
          (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx) ≤ ⊤
        from le_top)).op
      coordinateHyperplaneExplicitSupportedSheafSection =
    (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).app
      (op (firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx)))
      ((supportRelativeCohomologyPresheafOpenIso firstChartAnalyticOpenEmbeddingMap
        firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding
        coordinateHyperplaneAnalyticSupport firstNormalComplementᶜ
        firstChartAnalyticOpenEmbeddingMap_preimage_support 2).inv.app
        (op (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx))
        (chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (chartFlattening 1)
          firstNormalComplementᶜ chartFlattening_support_iff_firstComplement
          (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx)
          (flattenedSupportNeighborhood_subset_source
            (Fin 1 → ℂ) 1 (chartFlattening 1) x hx))) := by
  let W := flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) x hx
  have hchart := coordinateHyperplaneExplicitSupportedSheafSection_restrict_first
  have hres := congrArg
    (fun s ↦ (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).obj.map
      (firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.map
        (homOfLE (show W ≤ (⊤ : Opens (ComplexPoint (analyticChart 1))) from le_top))).op s)
    hchart
  have hopen := supportRelativeCohomologySectionOpenImage_restrict
    firstChartAnalyticOpenEmbeddingMap firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding
    coordinateHyperplaneAnalyticSupport firstNormalComplementᶜ
    firstChartAnalyticOpenEmbeddingMap_preimage_support 2
    firstChartHyperplaneWindingSheafSection W
  rw [firstChartHyperplaneWindingSheafSection_restrict_flattened x hx h0] at hopen
  rw [supportRelativeCohomologySheafOpenIso_unit_apply] at hopen
  change _ = (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint analyticPlane))
    coordinateHyperplaneAnalyticSupport 2).app _ _
  calc
    _ = (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
        coordinateHyperplaneAnalyticSupport 2).obj.map
        (firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.map
          (homOfLE (show W ≤ (⊤ : Opens (ComplexPoint (analyticChart 1))) from le_top))).op
        ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
          coordinateHyperplaneAnalyticSupport 2).obj.map
          (homOfLE (show
            firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
              (⊤ : Opens (ComplexPoint (analyticChart 1))) ≤ ⊤ from le_top)).op
          coordinateHyperplaneExplicitSupportedSheafSection) := by
            rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
            congr 2
    _ = _ := hres
    _ = _ := hopen

/-- The corresponding ambient normalized restriction on a flattened second-chart
neighborhood. -/
theorem coordinateHyperplaneExplicitSupportedSheafSection_restrict_secondFlattened
    (x : ComplexPoint (analyticChart 2)) (hx : x ∈ (chartFlattening 2).source)
    (h0 : (chartFlattening 2 x).2 = 0) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).obj.map
      (homOfLE (show
        secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
          (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx) ≤ ⊤
        from le_top)).op
      coordinateHyperplaneExplicitSupportedSheafSection =
    (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).app
      (op (secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx)))
      ((supportRelativeCohomologyPresheafOpenIso secondChartAnalyticOpenEmbeddingMap
        secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding
        coordinateHyperplaneAnalyticSupport secondNormalComplementᶜ
        secondChartAnalyticOpenEmbeddingMap_preimage_support 2).inv.app
        (op (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx))
        (chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (chartFlattening 2)
          secondNormalComplementᶜ chartFlattening_support_iff_secondComplement
          (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx)
          (flattenedSupportNeighborhood_subset_source
            (Fin 1 → ℂ) 1 (chartFlattening 2) x hx))) := by
  let W := flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) x hx
  have hchart := coordinateHyperplaneExplicitSupportedSheafSection_restrict_second
  have hres := congrArg
    (fun s ↦ (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).obj.map
      (secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.map
        (homOfLE (show W ≤ (⊤ : Opens (ComplexPoint (analyticChart 2))) from le_top))).op s)
    hchart
  have hopen := supportRelativeCohomologySectionOpenImage_restrict
    secondChartAnalyticOpenEmbeddingMap secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding
    coordinateHyperplaneAnalyticSupport secondNormalComplementᶜ
    secondChartAnalyticOpenEmbeddingMap_preimage_support 2
    secondChartHyperplaneWindingSheafSection W
  rw [secondChartHyperplaneWindingSheafSection_restrict_flattened x hx h0] at hopen
  rw [supportRelativeCohomologySheafOpenIso_unit_apply] at hopen
  change _ = (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint analyticPlane))
    coordinateHyperplaneAnalyticSupport 2).app _ _
  calc
    _ = (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
        coordinateHyperplaneAnalyticSupport 2).obj.map
        (secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.map
          (homOfLE (show W ≤ (⊤ : Opens (ComplexPoint (analyticChart 2))) from le_top))).op
        ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
          coordinateHyperplaneAnalyticSupport 2).obj.map
          (homOfLE (show
            secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
              (⊤ : Opens (ComplexPoint (analyticChart 2))) ≤ ⊤ from le_top)).op
          coordinateHyperplaneExplicitSupportedSheafSection) := by
            rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
            congr 2
    _ = _ := hres
    _ = _ := hopen

end AlgebraicGeometry.ProjectivePlane.CoordinateCharts
