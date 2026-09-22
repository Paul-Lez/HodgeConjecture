import Other.AlgebraicGeometry.ProjectivePlaneExplicitClassNormalization

@[expose] noncomputable section

open CategoryTheory Topology TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ProjectivePlane.CoordinateCharts

open AlgebraicGeometry.ComplexPoint
open AlgebraicGeometry.ProjectivePlane.AnalyticNormalization

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance hyperplaneOverι_isClosedImmersion_local :
    IsClosedImmersion hyperplaneOverι.left := by
  change IsClosedImmersion hyperplaneι
  infer_instance

private lemma explicitSection_restrict_firstAmbient
    (q : ComplexPoint (analyticChart 1)) (hq : q ∈ (chartFlattening 1).source)
    (h0 : (chartFlattening 1 q).2 = 0) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).obj.map
      (homOfLE (show firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) q hq) ≤ ⊤ from le_top)).op
      coordinateHyperplaneExplicitSupportedSheafSection =
    (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).app
      (op (firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) q hq)))
      (chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (ambientChartFlattening 1)
        coordinateHyperplaneAnalyticSupport ambientChartFlattening_one_support_iff
        (firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
          (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) q hq))
        (firstFlattened_image_subset_ambientSource q hq)) := by
  let U := firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
    (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) q hq)
  let ηU := (supportRelativeCohomologyToSheaf
    (TopCat.of (ComplexPoint analyticPlane)) coordinateHyperplaneAnalyticSupport 2).app (op U)
  exact (coordinateHyperplaneExplicitSupportedSheafSection_restrict_firstFlattened q hq h0).trans
    (congrArg ηU (firstChartNormalCoclass_openTransport q hq))

set_option maxHeartbeats 1600000 in
private lemma explicitGerm_eq_firstAmbient
    (z : ComplexPoint hyperplaneOver) (q : ComplexPoint (analyticChart 1))
    (hcenter : chartEmbeddingMap 1 q = Point.map hyperplaneOverι z) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).presheaf.Γgerm
        (Point.map hyperplaneOverι z) coordinateHyperplaneExplicitSupportedSheafSection =
      supportRelativeCohomologyGerm (TopCat.of (ComplexPoint analyticPlane))
        coordinateHyperplaneAnalyticSupport 2
        (firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
          (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) q
            (by simpa [chartFlattening] using (show q ∈ (Set.univ : Set _) from trivial))))
        (Point.map hyperplaneOverι z) (by
          refine ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, ?_⟩
          exact hcenter)
        (chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (ambientChartFlattening 1)
          coordinateHyperplaneAnalyticSupport ambientChartFlattening_one_support_iff
          _ (firstFlattened_image_subset_ambientSource q _)) := by
  let hqsrc : q ∈ (chartFlattening 1).source := by
    simpa [chartFlattening] using (show q ∈ (Set.univ : Set _) from trivial)
  let V := flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) q hqsrc
  let U := firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj V
  have h0 : (chartFlattening 1 q).2 = 0 := by
    rw [← ambientChartFlattening_apply 1 q]
    exact (ambientChartFlattening_one_support_iff _ ⟨q, hqsrc, rfl⟩).mp
      ⟨z, hcenter.symm⟩
  have hres := explicitSection_restrict_firstAmbient q hqsrc h0
  have hg := congrArg
    ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).presheaf.germ U
      (Point.map hyperplaneOverι z) (by
        exact ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, hcenter⟩)) hres
  dsimp [U, V] at hg
  calc
    _ = (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
        coordinateHyperplaneAnalyticSupport 2).presheaf.germ U
        (Point.map hyperplaneOverι z) (by
          exact ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, hcenter⟩)
        ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
          coordinateHyperplaneAnalyticSupport 2).obj.map
          (homOfLE (show U ≤ ⊤ from le_top)).op
          coordinateHyperplaneExplicitSupportedSheafSection) := by
      exact ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
        coordinateHyperplaneAnalyticSupport 2).presheaf.germ_res_apply
        (homOfLE (show U ≤ ⊤ from le_top))
        (Point.map hyperplaneOverι z) (by
          exact ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, hcenter⟩)
        coordinateHyperplaneExplicitSupportedSheafSection).symm
    _ = _ := hg
    _ = _ := rfl

set_option maxHeartbeats 1600000 in
private lemma explicitGerm_eq_firstAmbient_analytic
    (z : ComplexPoint hyperplaneOver) (q : ComplexPoint (analyticChart 1))
    (hcenter : chartEmbeddingMap 1 q = Point.map hyperplaneAnalyticι z) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).presheaf.Γgerm
        (Point.map hyperplaneAnalyticι z) coordinateHyperplaneExplicitSupportedSheafSection =
      supportRelativeCohomologyGerm (TopCat.of (ComplexPoint analyticPlane))
        coordinateHyperplaneAnalyticSupport 2
        (firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
          (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) q
            (by simpa [chartFlattening] using (show q ∈ (Set.univ : Set _) from trivial))))
        (Point.map hyperplaneAnalyticι z) (by
          refine ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, ?_⟩
          exact hcenter)
        (chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (ambientChartFlattening 1)
          coordinateHyperplaneAnalyticSupport ambientChartFlattening_one_support_iff
          _ (firstFlattened_image_subset_ambientSource q _)) := by
  let hqsrc : q ∈ (chartFlattening 1).source := by
    simpa [chartFlattening] using (show q ∈ (Set.univ : Set _) from trivial)
  let V := flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) q hqsrc
  let U := firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj V
  have hcenterOver : chartEmbeddingMap 1 q = Point.map hyperplaneOverι z := by
    rw [← hyperplaneAnalyticι_eq_hyperplaneOverι]
    exact hcenter
  have h0 : (chartFlattening 1 q).2 = 0 := by
    rw [← ambientChartFlattening_apply 1 q]
    exact (ambientChartFlattening_one_support_iff _ ⟨q, hqsrc, rfl⟩).mp
      ⟨z, hcenterOver.symm⟩
  have hres := explicitSection_restrict_firstAmbient q hqsrc h0
  have hg := congrArg
    ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).presheaf.germ U
      (Point.map hyperplaneAnalyticι z) (by
        exact ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, hcenter⟩)) hres
  dsimp [U, V] at hg
  calc
    _ = (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
        coordinateHyperplaneAnalyticSupport 2).presheaf.germ U
        (Point.map hyperplaneAnalyticι z) (by
          exact ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, hcenter⟩)
        ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
          coordinateHyperplaneAnalyticSupport 2).obj.map
          (homOfLE (show U ≤ ⊤ from le_top)).op
          coordinateHyperplaneExplicitSupportedSheafSection) := by
      exact ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
        coordinateHyperplaneAnalyticSupport 2).presheaf.germ_res_apply
        (homOfLE (show U ≤ ⊤ from le_top))
        (Point.map hyperplaneAnalyticι z) (by
          exact ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, hcenter⟩)
        coordinateHyperplaneExplicitSupportedSheafSection).symm
    _ = _ := hg
    _ = _ := rfl

private lemma explicitSection_restrict_secondAmbient
    (q : ComplexPoint (analyticChart 2)) (hq : q ∈ (chartFlattening 2).source)
    (h0 : (chartFlattening 2 q).2 = 0) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).obj.map
      (homOfLE (show secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) q hq) ≤ ⊤ from le_top)).op
      coordinateHyperplaneExplicitSupportedSheafSection =
    (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).app
      (op (secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) q hq)))
      (chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (ambientChartFlattening 2)
        coordinateHyperplaneAnalyticSupport ambientChartFlattening_two_support_iff
        (secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
          (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) q hq))
        (secondFlattened_image_subset_ambientSource q hq)) := by
  let U := secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
    (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) q hq)
  let ηU := (supportRelativeCohomologyToSheaf
    (TopCat.of (ComplexPoint analyticPlane)) coordinateHyperplaneAnalyticSupport 2).app (op U)
  exact (coordinateHyperplaneExplicitSupportedSheafSection_restrict_secondFlattened q hq h0).trans
    (congrArg ηU (secondChartNormalCoclass_openTransport q hq))

set_option maxHeartbeats 1600000 in
private lemma explicitGerm_eq_secondAmbient
    (z : ComplexPoint hyperplaneOver) (q : ComplexPoint (analyticChart 2))
    (hcenter : chartEmbeddingMap 2 q = Point.map hyperplaneOverι z) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).presheaf.Γgerm
        (Point.map hyperplaneOverι z) coordinateHyperplaneExplicitSupportedSheafSection =
      supportRelativeCohomologyGerm (TopCat.of (ComplexPoint analyticPlane))
        coordinateHyperplaneAnalyticSupport 2
        (secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
          (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) q
            (by simpa [chartFlattening] using (show q ∈ (Set.univ : Set _) from trivial))))
        (Point.map hyperplaneOverι z) (by
          refine ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, ?_⟩
          exact hcenter)
        (chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (ambientChartFlattening 2)
          coordinateHyperplaneAnalyticSupport ambientChartFlattening_two_support_iff
          _ (secondFlattened_image_subset_ambientSource q _)) := by
  let hqsrc : q ∈ (chartFlattening 2).source := by
    simpa [chartFlattening] using (show q ∈ (Set.univ : Set _) from trivial)
  let V := flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) q hqsrc
  let U := secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj V
  have h0 : (chartFlattening 2 q).2 = 0 := by
    rw [← ambientChartFlattening_apply 2 q]
    exact (ambientChartFlattening_two_support_iff _ ⟨q, hqsrc, rfl⟩).mp
      ⟨z, hcenter.symm⟩
  have hres := explicitSection_restrict_secondAmbient q hqsrc h0
  have hg := congrArg
    ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).presheaf.germ U
      (Point.map hyperplaneOverι z) (by
        exact ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, hcenter⟩)) hres
  dsimp [U, V] at hg
  calc
    _ = (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
        coordinateHyperplaneAnalyticSupport 2).presheaf.germ U
        (Point.map hyperplaneOverι z) (by
          exact ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, hcenter⟩)
        ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
          coordinateHyperplaneAnalyticSupport 2).obj.map
          (homOfLE (show U ≤ ⊤ from le_top)).op
          coordinateHyperplaneExplicitSupportedSheafSection) := by
      exact ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
        coordinateHyperplaneAnalyticSupport 2).presheaf.germ_res_apply
        (homOfLE (show U ≤ ⊤ from le_top))
        (Point.map hyperplaneOverι z) (by
          exact ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, hcenter⟩)
        coordinateHyperplaneExplicitSupportedSheafSection).symm
    _ = _ := hg
    _ = _ := rfl

set_option maxHeartbeats 1600000 in
private lemma explicitGerm_eq_secondAmbient_analytic
    (z : ComplexPoint hyperplaneOver) (q : ComplexPoint (analyticChart 2))
    (hcenter : chartEmbeddingMap 2 q = Point.map hyperplaneAnalyticι z) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).presheaf.Γgerm
        (Point.map hyperplaneAnalyticι z) coordinateHyperplaneExplicitSupportedSheafSection =
      supportRelativeCohomologyGerm (TopCat.of (ComplexPoint analyticPlane))
        coordinateHyperplaneAnalyticSupport 2
        (secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
          (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) q
            (by simpa [chartFlattening] using (show q ∈ (Set.univ : Set _) from trivial))))
        (Point.map hyperplaneAnalyticι z) (by
          refine ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, ?_⟩
          exact hcenter)
        (chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (ambientChartFlattening 2)
          coordinateHyperplaneAnalyticSupport ambientChartFlattening_two_support_iff
          _ (secondFlattened_image_subset_ambientSource q _)) := by
  let hqsrc : q ∈ (chartFlattening 2).source := by
    simpa [chartFlattening] using (show q ∈ (Set.univ : Set _) from trivial)
  let V := flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) q hqsrc
  let U := secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj V
  have hcenterOver : chartEmbeddingMap 2 q = Point.map hyperplaneOverι z := by
    rw [← hyperplaneAnalyticι_eq_hyperplaneOverι]
    exact hcenter
  have h0 : (chartFlattening 2 q).2 = 0 := by
    rw [← ambientChartFlattening_apply 2 q]
    exact (ambientChartFlattening_two_support_iff _ ⟨q, hqsrc, rfl⟩).mp
      ⟨z, hcenterOver.symm⟩
  have hres := explicitSection_restrict_secondAmbient q hqsrc h0
  have hg := congrArg
    ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
      coordinateHyperplaneAnalyticSupport 2).presheaf.germ U
      (Point.map hyperplaneAnalyticι z) (by
        exact ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, hcenter⟩)) hres
  dsimp [U, V] at hg
  calc
    _ = (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
        coordinateHyperplaneAnalyticSupport 2).presheaf.germ U
        (Point.map hyperplaneAnalyticι z) (by
          exact ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, hcenter⟩)
        ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
          coordinateHyperplaneAnalyticSupport 2).obj.map
          (homOfLE (show U ≤ ⊤ from le_top)).op
          coordinateHyperplaneExplicitSupportedSheafSection) := by
      exact ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint analyticPlane))
        coordinateHyperplaneAnalyticSupport 2).presheaf.germ_res_apply
        (homOfLE (show U ≤ ⊤ from le_top))
        (Point.map hyperplaneAnalyticι z) (by
          exact ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, hcenter⟩)
        coordinateHyperplaneExplicitSupportedSheafSection).symm
    _ = _ := hg
    _ = _ := rfl

private lemma exists_open_ambientChartFlattening_canonicalOver_coclass_eq
    (i : Fin 3) (q : ComplexPoint (analyticChart i))
    (z : ComplexPoint hyperplaneOver)
    (hcenter : chartEmbeddingMap i q = Point.map hyperplaneAnalyticι z)
    (hS : ∀ y ∈ (ambientChartFlattening i).source,
      y ∈ Set.range (Point.map hyperplaneAnalyticι) ↔
        (ambientChartFlattening i y).2 = 0) :
    ∃ (W : TopologicalSpace.Opens (ComplexPoint analyticPlane))
      (hW : (W : Set _) ⊆ (ambientChartFlattening i).source)
      (hW' : (W : Set _) ⊆
        (canonicalHyperplaneFlattening z).source),
      chartEmbeddingMap i q ∈ W ∧
      chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (ambientChartFlattening i)
        (Set.range (Point.map hyperplaneOverι)) hS W hW =
      chartNormalProjectionCoclass (Fin 1 → ℂ) 1
        (canonicalHyperplaneFlattening z)
        (Set.range (Point.map hyperplaneAnalyticι))
        (by
          rw [canonicalHyperplaneFlattening]
          exact ComplexPoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff
            analyticPlane hyperplaneOver hyperplaneAnalyticι 1 2 z) W hW' := by
  have hcA : chartEmbeddingMap i q = Point.map hyperplaneAnalyticι z := by
    rw [hyperplaneAnalyticι_eq_hyperplaneOverι]
    exact hcenter
  have hSA : ∀ y ∈ (ambientChartFlattening i).source,
      y ∈ Set.range (Point.map hyperplaneAnalyticι) ↔
        (ambientChartFlattening i y).2 = 0 := by
    intro y hy
    rw [hyperplaneAnalyticι_eq_hyperplaneOverι]
    exact hS y hy
  obtain ⟨W, hW, hW', hxW, heq⟩ :=
    exists_open_ambientChartFlattening_canonical_coclass_eq i q z hcA hSA
  refine ⟨W, hW, ?_, hxW, ?_⟩
  · simpa only [canonicalHyperplaneFlattening,
      hyperplaneAnalyticι_eq_hyperplaneOverι] using hW'
  · have hsupport : Set.range (Point.map hyperplaneAnalyticι) =
        Set.range (Point.map hyperplaneOverι) := by
      rw [hyperplaneAnalyticι_eq_hyperplaneOverι]
      rfl
    cases hsupport
    exact heq

private lemma canonical_coclass_eq_smooth_over
    (z : ComplexPoint hyperplaneOver)
    (W : Set (ComplexPoint analyticPlane))
    (hW : W ⊆ (canonicalHyperplaneFlattening z).source) :
    chartNormalProjectionCoclass (Fin 1 → ℂ) 1
        (canonicalHyperplaneFlattening z)
        (Set.range (Point.map hyperplaneAnalyticι))
        (by
          rw [canonicalHyperplaneFlattening]
          exact ComplexPoint.closedImmersionHolomorphicFlatteningChart_mem_range_iff
            analyticPlane hyperplaneOver hyperplaneAnalyticι 1 2 z) W hW =
      smoothClosedSupportChartCoclass analyticPlane hyperplaneOver hyperplaneAnalyticι
        1 2 z W (by
          simpa only [canonicalHyperplaneFlattening] using hW) := by
  unfold smoothClosedSupportChartCoclass
  rfl

set_option maxHeartbeats 1600000 in
private lemma ambientGerm_eq_canonical
    (i : Fin 3) (q : ComplexPoint (analyticChart i))
    (z : ComplexPoint hyperplaneOver)
    (hcenter : chartEmbeddingMap i q = Point.map hyperplaneAnalyticι z)
    (hS : ∀ y ∈ (ambientChartFlattening i).source,
      y ∈ Set.range (Point.map hyperplaneAnalyticι) ↔
        (ambientChartFlattening i y).2 = 0)
    (U : TopologicalSpace.Opens (ComplexPoint analyticPlane))
    (hU : (U : Set _) ⊆ (ambientChartFlattening i).source)
    (hxU : Point.map hyperplaneAnalyticι z ∈ U) :
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint analyticPlane))
      (Set.range (Point.map hyperplaneAnalyticι)) 2 U
        (Point.map hyperplaneAnalyticι z) hxU
      (chartNormalProjectionCoclass (Fin 1 → ℂ) 1 (ambientChartFlattening i)
        (Set.range (Point.map hyperplaneAnalyticι)) hS U hU) =
      smoothClosedSupportChartCoclassGerm analyticPlane hyperplaneOver
        hyperplaneAnalyticι 1 2 z (Point.map hyperplaneAnalyticι z) (by
          exact mem_smoothClosedSupportChartOpen analyticPlane hyperplaneOver
            hyperplaneAnalyticι 1 2 z) := by
  obtain ⟨W, hW, hW', hxW, heq⟩ :=
    exists_open_ambientChartFlattening_canonical_coclass_eq i q z hcenter hS
  let C := smoothClosedSupportChartOpen analyticPlane hyperplaneOver
    hyperplaneAnalyticι 1 2 z
  have hW'C : (W : Set (ComplexPoint analyticPlane)) ⊆ C := by
    change (W : Set (ComplexPoint analyticPlane)) ⊆
      (closedImmersionHolomorphicFlatteningChart analyticPlane hyperplaneOver
        hyperplaneAnalyticι 1 2 z).source
    exact hW'
  have hxC : Point.map hyperplaneAnalyticι z ∈ C := by
    exact mem_smoothClosedSupportChartOpen analyticPlane hyperplaneOver
      hyperplaneAnalyticι 1 2 z
  have hxWcenter : Point.map hyperplaneAnalyticι z ∈ W := by
    rw [← hcenter]
    exact hxW
  let T := U ⊓ C ⊓ W
  have hTU : T ≤ U := by
    exact (inf_le_left.trans inf_le_left)
  have hTC : T ≤ C := by
    exact (inf_le_left.trans inf_le_right)
  have hTW : T ≤ W := inf_le_right
  have hTUs : (T : Set (ComplexPoint analyticPlane)) ⊆
      (ambientChartFlattening i).source := by
    exact (show (T : Set (ComplexPoint analyticPlane)) ⊆ (U : Set _) from hTU).trans hU
  have hTUset : (T : Set (ComplexPoint analyticPlane)) ⊆ (U : Set _) := hTU
  have hTWs : (T : Set (ComplexPoint analyticPlane)) ⊆ (W : Set _) := hTW
  have hTCs : (T : Set (ComplexPoint analyticPlane)) ⊆ (C : Set _) := hTC
  have hxT : Point.map hyperplaneAnalyticι z ∈ T := ⟨⟨hxU, hxC⟩, hxWcenter⟩
  unfold smoothClosedSupportChartCoclassGerm
  apply supportRelativeCohomologyGerm_eq_of_restrict_eq
    (TopCat.of (ComplexPoint analyticPlane)) (Set.range (Point.map hyperplaneAnalyticι)) 2
    (U := U) (V := C) (W := T) hTU hTC
      (Point.map hyperplaneAnalyticι z) hxT
  calc
    _ = chartNormalProjectionCoclass (Fin 1 → ℂ) 1
        (ambientChartFlattening i) (Set.range (Point.map hyperplaneAnalyticι)) hS T
        hTUs :=
      chartNormalProjectionCoclass_restrict (Fin 1 → ℂ) 1
        (ambientChartFlattening i) (Set.range (Point.map hyperplaneAnalyticι)) hS
        hTUset hU
    _ = relativeCohomologyMap ℚ 2
        (neighborhoodSupportInclusionPairMap hTWs (Set.range (Point.map hyperplaneAnalyticι)))
        (chartNormalProjectionCoclass (Fin 1 → ℂ) 1
          (ambientChartFlattening i) (Set.range (Point.map hyperplaneAnalyticι)) hS W hW) := by
      exact (chartNormalProjectionCoclass_restrict (Fin 1 → ℂ) 1
        (ambientChartFlattening i) (Set.range (Point.map hyperplaneAnalyticι)) hS hTWs hW).symm
    _ = relativeCohomologyMap ℚ 2
        (neighborhoodSupportInclusionPairMap hTWs (Set.range (Point.map hyperplaneAnalyticι)))
        (chartNormalProjectionCoclass (Fin 1 → ℂ) 1
          (canonicalHyperplaneFlattening z)
          (Set.range (Point.map hyperplaneAnalyticι)) _ W hW') := by
      exact congrArg
        (relativeCohomologyMap ℚ 2
          (neighborhoodSupportInclusionPairMap hTWs (Set.range (Point.map hyperplaneAnalyticι)))) heq
    _ = relativeCohomologyMap ℚ 2
        (neighborhoodSupportInclusionPairMap hTWs (Set.range (Point.map hyperplaneAnalyticι)))
        (smoothClosedSupportChartCoclass analyticPlane hyperplaneOver
          hyperplaneAnalyticι 1 2 z W hW'C) := by
      rw [canonical_coclass_eq_smooth_over z W hW']
    _ = smoothClosedSupportChartCoclass analyticPlane hyperplaneOver
        hyperplaneAnalyticι 1 2 z T hTCs :=
      by
        exact smoothClosedSupportChartCoclass_restrict analyticPlane hyperplaneOver
          hyperplaneAnalyticι 1 2 z hTWs hW'C
    _ = relativeCohomologyMap ℚ 2
        (neighborhoodSupportInclusionPairMap hTC (Set.range (Point.map hyperplaneAnalyticι)))
        (smoothClosedSupportChartCoclass analyticPlane hyperplaneOver
          hyperplaneAnalyticι 1 2 z C (le_refl _)) := by
      exact (smoothClosedSupportChartCoclass_restrict analyticPlane hyperplaneOver
        hyperplaneAnalyticι 1 2 z hTCs (le_refl _)).symm

set_option maxHeartbeats 1600000 in
theorem coordinateHyperplaneExplicitSupportedSheafSection_eq_smoothClosedSupportCoclassSection :
    coordinateHyperplaneExplicitSupportedSheafSection =
      smoothClosedSupportCoclassSection analyticPlane hyperplaneOver
        hyperplaneAnalyticι 1 2 := by
  have hsupport : Set.range (Point.map hyperplaneAnalyticι) =
      Set.range (Point.map hyperplaneOverι) := by
    rw [hyperplaneAnalyticι_eq_hyperplaneOverι]
    rfl
  cases hsupport
  apply smoothClosedSupportCoclassSection_unique_of_normalization
    (X := analyticPlane) (Y := hyperplaneOver) (i := hyperplaneAnalyticι)
    (m := 1) (d := 2)
  · intro z
    obtain ⟨i, q, hq⟩ := hyperplaneSupport_mem_chart_one_or_two
      (Point.map hyperplaneOverι z) ⟨z, rfl⟩
    fin_cases i
    · have hcenter : chartEmbeddingMap 1 q = Point.map hyperplaneAnalyticι z := by
        rw [hyperplaneAnalyticι_eq_hyperplaneOverι]
        exact hq.symm
      have he := explicitGerm_eq_firstAmbient_analytic z q hcenter
      let hqsrc : q ∈ (chartFlattening 1).source := by
        simpa [chartFlattening] using (show q ∈ (Set.univ : Set _) from trivial)
      let U₀ := firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 1) q hqsrc)
      have hU₀ : (U₀ : Set (ComplexPoint analyticPlane)) ⊆
          (ambientChartFlattening 1).source := by
        exact firstFlattened_image_subset_ambientSource q hqsrc
      have hxU₀ : Point.map hyperplaneAnalyticι z ∈ U₀ := by
        rw [← hcenter]
        exact ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, rfl⟩
      have ha := ambientGerm_eq_canonical 1 q z hcenter
        ambientChartFlattening_one_support_iff_analytic U₀ hU₀ hxU₀
      have he' := he
      dsimp [U₀] at he'
      exact he'.trans ha
    · have hcenter : chartEmbeddingMap 2 q = Point.map hyperplaneAnalyticι z := by
        rw [hyperplaneAnalyticι_eq_hyperplaneOverι]
        exact hq.symm
      have he := explicitGerm_eq_secondAmbient_analytic z q hcenter
      let hqsrc : q ∈ (chartFlattening 2).source := by
        simpa [chartFlattening] using (show q ∈ (Set.univ : Set _) from trivial)
      let U₀ := secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
        (flattenedSupportNeighborhood (Fin 1 → ℂ) 1 (chartFlattening 2) q hqsrc)
      have hU₀ : (U₀ : Set (ComplexPoint analyticPlane)) ⊆
          (ambientChartFlattening 2).source := by
        exact secondFlattened_image_subset_ambientSource q hqsrc
      have hxU₀ : Point.map hyperplaneAnalyticι z ∈ U₀ := by
        rw [← hcenter]
        exact ⟨q, mem_flattenedSupportNeighborhood _ _ _ _ _, rfl⟩
      have ha := ambientGerm_eq_canonical 2 q z hcenter
        ambientChartFlattening_two_support_iff_analytic U₀ hU₀ hxU₀
      have he' := he
      dsimp [U₀] at he'
      exact he'.trans ha
  · intro x hx
    unfold coordinateHyperplaneExplicitSupportedSheafSection
    change supportRelativeCohomologyGerm (TopCat.of (ComplexPoint analyticPlane))
      (Set.range (Point.map hyperplaneAnalyticι)) 2 ⊤ x (by trivial) _ = 0
    apply supportRelativeCohomologyGerm_eq_zero_of_not_mem
      (TopCat.of (ComplexPoint analyticPlane))
      (Set.range (Point.map hyperplaneAnalyticι)) 2
      (isClosedEmbedding_map_of_closedImmersion hyperplaneAnalyticι).isClosed_range
      (⊤ : Opens (ComplexPoint analyticPlane)) x trivial hx _

end AlgebraicGeometry.ProjectivePlane.CoordinateCharts
