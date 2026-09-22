/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Other.AlgebraicGeometry.ProjectivePlaneRelativeCechExplicitClassSecondChart
import HodgeConjecture.Lemmas.AlgebraicTopology.SupportRelativeCohomologyOpenTransport
import Other.AlgebraicTopology.TopOpenRelativeCochainNormalization

/-!
# Sheaf restrictions of the explicit coordinate-hyperplane class

The explicit relative class on the analytic projective plane restricts on the two standard
affine charts to the literal winding classes.  This file records the corresponding statement
after applying the actual relative-cohomology sheafification map.  The chart classes are first
sheafified intrinsically and then transported along the open embeddings of the charts.
-/

@[expose] noncomputable section

open CategoryTheory Topology TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ProjectivePlane.CoordinateCharts

open AlgebraicGeometry.ComplexPoint

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "analyticPlaneTop" => (TopCat.of (ComplexPoint analyticPlane))

/-- The coordinate hyperplane, as a closed analytic support. -/
def coordinateHyperplaneAnalyticClosedSupport : Closeds (ComplexPoint analyticPlane) :=
  ⟨coordinateHyperplaneAnalyticSupport,
    (isClosedEmbedding_map_of_closedImmersion hyperplaneOverι).isClosed_range⟩

lemma isOpen_firstNormalComplement : IsOpen firstNormalComplement := by
  exact isOpen_ne_fun continuous_firstNormalValue continuous_const

lemma isOpen_secondNormalComplement : IsOpen secondNormalComplement := by
  exact isOpen_ne_fun continuous_secondNormalCoordinate continuous_const

/-- The zero set of `X₀/X₁` inside the first chart. -/
def firstChartHyperplaneAnalyticClosedSupport :
    Closeds (ComplexPoint (analyticChart 1)) :=
  ⟨firstNormalComplementᶜ, isOpen_firstNormalComplement.isClosed_compl⟩

/-- The zero set of `X₀/X₂` inside the second chart. -/
def secondChartHyperplaneAnalyticClosedSupport :
    Closeds (ComplexPoint (analyticChart 2)) :=
  ⟨secondNormalComplementᶜ, isOpen_secondNormalComplement.isClosed_compl⟩

/-- The analytic open embedding of the first chart into the plane. -/
def firstChartAnalyticOpenEmbeddingMap :
    TopCat.of (ComplexPoint (analyticChart 1)) ⟶ analyticPlaneTop :=
  TopCat.ofHom ⟨Point.map (openInclusion analyticPlane (chartOpen 1)),
    Point.continuous_map (openInclusion analyticPlane (chartOpen 1))⟩

lemma firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding :
    IsOpenEmbedding firstChartAnalyticOpenEmbeddingMap := by
  simpa [firstChartAnalyticOpenEmbeddingMap] using
      (isOpenEmbedding_map_open analyticPlane (chartOpen 1))

/-- The analytic open embedding of the second chart into the plane. -/
def secondChartAnalyticOpenEmbeddingMap :
    TopCat.of (ComplexPoint (analyticChart 2)) ⟶ analyticPlaneTop :=
  TopCat.ofHom ⟨Point.map (openInclusion analyticPlane (chartOpen 2)),
    Point.continuous_map (openInclusion analyticPlane (chartOpen 2))⟩

lemma secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding :
    IsOpenEmbedding secondChartAnalyticOpenEmbeddingMap := by
  simpa [secondChartAnalyticOpenEmbeddingMap] using
      (isOpenEmbedding_map_open analyticPlane (chartOpen 2))

lemma firstChartAnalyticOpenEmbeddingMap_preimage_support :
    firstChartAnalyticOpenEmbeddingMap ⁻¹'
        coordinateHyperplaneAnalyticSupport = firstNormalComplementᶜ := by
  ext z
  have h := mem_firstNormalComplement_iff_not_mem_hyperplane z
  change Point.map (openInclusion analyticPlane (chartOpen 1)) z ∈
    Set.range (Point.map hyperplaneOverι) ↔ z ∉ firstNormalComplement
  simpa only [not_not] using (not_congr h).symm

lemma secondChartAnalyticOpenEmbeddingMap_preimage_support :
    secondChartAnalyticOpenEmbeddingMap ⁻¹'
        coordinateHyperplaneAnalyticSupport = secondNormalComplementᶜ := by
  ext z
  have h := mem_secondNormalComplement_iff_not_mem_hyperplane z
  change Point.map (openInclusion analyticPlane (chartOpen 2)) z ∈
    Set.range (Point.map hyperplaneOverι) ↔ z ∉ secondNormalComplement
  simpa only [not_not] using (not_congr h).symm

/-- The top-open support pair with its subtype witnesses removed. -/
def topOpenSupportPairIso (Y : TopCat.{0}) (S : Set Y) :
    neighborhoodSupportComplementPair ((⊤ : Opens Y) : Set Y) S ≅
      TopPair.ofSubset Sᶜ where
  hom := TopPair.ofHom (Opens.inclusionTopIso Y).hom
    (TopCat.ofHom ⟨fun w ↦ ⟨w.1.1, w.2⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun w ↦ w.2)⟩)
      (by ext w; rfl)
  inv := TopPair.ofHom (Opens.inclusionTopIso Y).inv
    (TopCat.ofHom ⟨fun u ↦ ⟨⟨u.1, trivial⟩, u.2⟩,
      (continuous_subtype_val.subtype_mk (fun _ ↦ trivial)).subtype_mk (fun u ↦ u.2)⟩)
      (by ext u; rfl)
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

/- The explicit top-open pair has the same underlying arrow as the canonical
   closed-support normalization pair.  This checks both pair components, so
   no subtype witness is hidden in later transport. -/
lemma topOpenSupportPairIso_hom_eq_topOpenNeighborhoodSupportPairIso_hom :
    (topOpenSupportPairIso analyticPlaneTop coordinateHyperplaneAnalyticSupport).hom =
      (topOpenNeighborhoodSupportPairIso analyticPlaneTop
        coordinateHyperplaneAnalyticClosedSupport).hom := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

/-- Removing the top-open subtype witnesses when the displayed support is the complement of
the subset used in an ordinary pair.  This direct form avoids a dependent transport across
`(Uᶜ)ᶜ = U`. -/
def topOpenComplementSupportPairIso (Y : TopCat.{0}) (U : Set Y) :
    neighborhoodSupportComplementPair ((⊤ : Opens Y) : Set Y) Uᶜ ≅
      TopPair.ofSubset U where
  hom := TopPair.ofHom (Opens.inclusionTopIso Y).hom
    (TopCat.ofHom ⟨fun w ↦ ⟨w.1.1, by simpa using w.2⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        (fun w ↦ by simpa using w.2)⟩) (by ext w; rfl)
  inv := TopPair.ofHom (Opens.inclusionTopIso Y).inv
    (TopCat.ofHom ⟨fun u ↦ ⟨⟨u.1, trivial⟩, by simpa using u.2⟩,
      (continuous_subtype_val.subtype_mk (fun _ ↦ trivial)).subtype_mk
        (fun u ↦ by simpa using u.2)⟩) (by ext u; rfl)
  hom_inv_id := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl
  inv_hom_id := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl

/-- Sheafification of the explicit global supported class, after removing the harmless
top-open subtype witnesses. -/
def coordinateHyperplaneExplicitSupportedSheafSection :
    (supportRelativeCohomologySheaf analyticPlaneTop
      coordinateHyperplaneAnalyticSupport 2).obj.obj (op ⊤) :=
  (supportRelativeCohomologyToSheaf analyticPlaneTop
      coordinateHyperplaneAnalyticSupport 2).app (op ⊤)
    (relativeCohomologyMap ℚ 2
      (topOpenSupportPairIso analyticPlaneTop coordinateHyperplaneAnalyticSupport).hom
      coordinateHyperplaneExplicitSupportedSingularClass)

/-- Intrinsic sheafification of the literal first-chart winding class. -/
def firstChartHyperplaneWindingSheafSection :
    (supportRelativeCohomologySheaf
      (TopCat.of (ComplexPoint (analyticChart 1))) firstNormalComplementᶜ 2).obj.obj (op ⊤) :=
    (supportRelativeCohomologyToSheaf
      (TopCat.of (ComplexPoint (analyticChart 1))) firstNormalComplementᶜ 2).app (op ⊤)
    (relativeCohomologyMap ℚ 2
      (topOpenComplementSupportPairIso
        (TopCat.of (ComplexPoint (analyticChart 1))) firstNormalComplement).hom
      firstChartHyperplaneRelativeSingularClass)

/-- Intrinsic sheafification of the literal second-chart winding class. -/
def secondChartHyperplaneWindingSheafSection :
    (supportRelativeCohomologySheaf
      (TopCat.of (ComplexPoint (analyticChart 2))) secondNormalComplementᶜ 2).obj.obj (op ⊤) :=
    (supportRelativeCohomologyToSheaf
      (TopCat.of (ComplexPoint (analyticChart 2))) secondNormalComplementᶜ 2).app (op ⊤)
    (relativeCohomologyMap ℚ 2
      (topOpenComplementSupportPairIso
        (TopCat.of (ComplexPoint (analyticChart 2))) secondNormalComplement).hom
      secondChartHyperplaneRelativeSingularClass)

private lemma firstChart_pair_composite :
    neighborhoodSupportInclusionPairMap
        (show
          (firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
            (⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 1)))) :
              Set (ComplexPoint analyticPlane)) ⊆
            ((⊤ : Opens (ComplexPoint analyticPlane)) : Set _) from le_top)
        coordinateHyperplaneAnalyticSupport ≫
      (topOpenSupportPairIso analyticPlaneTop coordinateHyperplaneAnalyticSupport).hom =
    (neighborhoodSupportPairImageIso firstChartAnalyticOpenEmbeddingMap
        firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.isEmbedding
        ((⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 1)))) : Set _)
        firstNormalComplementᶜ coordinateHyperplaneAnalyticSupport
        (fun y _ ↦ by
          rw [← firstChartAnalyticOpenEmbeddingMap_preimage_support]
          rfl)).inv ≫
      (topOpenComplementSupportPairIso
        (TopCat.of (ComplexPoint (analyticChart 1))) firstNormalComplement).hom ≫
      firstChartToCoordinateHyperplaneSupportPair := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext z
  · let zi : firstChartAnalyticOpenEmbeddingMap ''
        ((⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 1)))) : Set _) := ⟨z.1.1, z.1.2⟩
    have hzi :=
      (firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.isEmbedding.homeomorphImage
        ((⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 1)))) : Set _)).apply_symm_apply zi
    exact Subtype.ext (congrArg Subtype.val hzi).symm
  · let zi : firstChartAnalyticOpenEmbeddingMap ''
        ((⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 1)))) : Set _) := ⟨z.1, z.2⟩
    have hzi :=
      (firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.isEmbedding.homeomorphImage
        ((⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 1)))) : Set _)).apply_symm_apply zi
    exact (congrArg Subtype.val hzi).symm

private lemma secondChart_pair_composite :
    neighborhoodSupportInclusionPairMap
        (show
          (secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
            (⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 2)))) :
              Set (ComplexPoint analyticPlane)) ⊆
            ((⊤ : Opens (ComplexPoint analyticPlane)) : Set _) from le_top)
        coordinateHyperplaneAnalyticSupport ≫
      (topOpenSupportPairIso analyticPlaneTop coordinateHyperplaneAnalyticSupport).hom =
    (neighborhoodSupportPairImageIso secondChartAnalyticOpenEmbeddingMap
        secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.isEmbedding
        ((⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 2)))) : Set _)
        secondNormalComplementᶜ coordinateHyperplaneAnalyticSupport
        (fun y _ ↦ by
          rw [← secondChartAnalyticOpenEmbeddingMap_preimage_support]
          rfl)).inv ≫
      (topOpenComplementSupportPairIso
        (TopCat.of (ComplexPoint (analyticChart 2))) secondNormalComplement).hom ≫
      secondChartToCoordinateHyperplaneSupportPair := by
  apply MorphismProperty.Arrow.Hom.ext <;> ext z
  · let zi : secondChartAnalyticOpenEmbeddingMap ''
        ((⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 2)))) : Set _) := ⟨z.1.1, z.1.2⟩
    have hzi :=
      (secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.isEmbedding.homeomorphImage
        ((⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 2)))) : Set _)).apply_symm_apply zi
    exact Subtype.ext (congrArg Subtype.val hzi).symm
  · let zi : secondChartAnalyticOpenEmbeddingMap ''
        ((⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 2)))) : Set _) := ⟨z.1, z.2⟩
    have hzi :=
      (secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.isEmbedding.homeomorphImage
        ((⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 2)))) : Set _)).apply_symm_apply zi
    exact (congrArg Subtype.val hzi).symm

private lemma coordinateHyperplaneExplicitTopClass_restrict_first :
    relativeCohomologyMap ℚ 2
        (neighborhoodSupportInclusionPairMap
          (show
            (firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
              (⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 1)))) :
                Set (ComplexPoint analyticPlane)) ⊆
              ((⊤ : Opens (ComplexPoint analyticPlane)) : Set _) from le_top)
          coordinateHyperplaneAnalyticSupport)
        (relativeCohomologyMap ℚ 2
          (topOpenSupportPairIso analyticPlaneTop coordinateHyperplaneAnalyticSupport).hom
          coordinateHyperplaneExplicitSupportedSingularClass) =
      (supportRelativeCohomologyPresheafOpenIso
        firstChartAnalyticOpenEmbeddingMap
        firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding
        coordinateHyperplaneAnalyticSupport firstNormalComplementᶜ
        firstChartAnalyticOpenEmbeddingMap_preimage_support 2).inv.app (op ⊤)
        (relativeCohomologyMap ℚ 2
          (topOpenComplementSupportPairIso
            (TopCat.of (ComplexPoint (analyticChart 1))) firstNormalComplement).hom
          firstChartHyperplaneRelativeSingularClass) := by
  rw [supportRelativeCohomologyPresheafOpenIso_inv_app]
  rw [← coordinateHyperplaneExplicitSupportedSingularClass_restrict_first]
  simp only [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  rw [firstChart_pair_composite]
  rfl

private lemma coordinateHyperplaneExplicitTopClass_restrict_second :
    relativeCohomologyMap ℚ 2
        (neighborhoodSupportInclusionPairMap
          (show
            (secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
              (⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 2)))) :
                Set (ComplexPoint analyticPlane)) ⊆
              ((⊤ : Opens (ComplexPoint analyticPlane)) : Set _) from le_top)
          coordinateHyperplaneAnalyticSupport)
        (relativeCohomologyMap ℚ 2
          (topOpenSupportPairIso analyticPlaneTop coordinateHyperplaneAnalyticSupport).hom
          coordinateHyperplaneExplicitSupportedSingularClass) =
      (supportRelativeCohomologyPresheafOpenIso
        secondChartAnalyticOpenEmbeddingMap
        secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding
        coordinateHyperplaneAnalyticSupport secondNormalComplementᶜ
        secondChartAnalyticOpenEmbeddingMap_preimage_support 2).inv.app (op ⊤)
        (relativeCohomologyMap ℚ 2
          (topOpenComplementSupportPairIso
            (TopCat.of (ComplexPoint (analyticChart 2))) secondNormalComplement).hom
          secondChartHyperplaneRelativeSingularClass) := by
  rw [supportRelativeCohomologyPresheafOpenIso_inv_app]
  rw [← coordinateHyperplaneExplicitSupportedSingularClass_restrict_second]
  simp only [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  rw [secondChart_pair_composite]
  rfl

/-- Restricting the sheafification of the global explicit class to the actual image of the
first affine chart gives the transported sheafification of the literal winding cocycle
`(0, windingIndex(X₀/X₁))`. -/
theorem coordinateHyperplaneExplicitSupportedSheafSection_restrict_first :
    (supportRelativeCohomologySheaf analyticPlaneTop
      coordinateHyperplaneAnalyticSupport 2).obj.map
      (homOfLE (show
        firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
          (⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 1)))) ≤ ⊤ from le_top)).op
      coordinateHyperplaneExplicitSupportedSheafSection =
    (supportRelativeCohomologySheafOpenIso
      firstChartAnalyticOpenEmbeddingMap
      firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding
      coordinateHyperplaneAnalyticSupport firstNormalComplementᶜ
      firstChartAnalyticOpenEmbeddingMap_preimage_support 2).hom.hom.app (op ⊤)
      firstChartHyperplaneWindingSheafSection := by
  have hglobal := ConcreteCategory.congr_hom
    ((supportRelativeCohomologyToSheaf analyticPlaneTop
      coordinateHyperplaneAnalyticSupport 2).naturality
      (homOfLE (show
        firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
          (⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 1)))) ≤ ⊤ from le_top)).op)
    (relativeCohomologyMap ℚ 2
      (topOpenSupportPairIso analyticPlaneTop coordinateHyperplaneAnalyticSupport).hom
      coordinateHyperplaneExplicitSupportedSingularClass)
  have hlocal := supportRelativeCohomologySheafOpenIso_unit_apply
    firstChartAnalyticOpenEmbeddingMap
    firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding
    coordinateHyperplaneAnalyticSupport firstNormalComplementᶜ
    firstChartAnalyticOpenEmbeddingMap_preimage_support 2 ⊤
    (relativeCohomologyMap ℚ 2
      (topOpenComplementSupportPairIso
        (TopCat.of (ComplexPoint (analyticChart 1))) firstNormalComplement).hom
      firstChartHyperplaneRelativeSingularClass)
  have hclass := congrArg
    (fun a ↦ (supportRelativeCohomologyToSheaf analyticPlaneTop
      coordinateHyperplaneAnalyticSupport 2).app
        (op (firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj ⊤)) a)
    coordinateHyperplaneExplicitTopClass_restrict_first
  dsimp only [coordinateHyperplaneExplicitSupportedSheafSection,
    firstChartHyperplaneWindingSheafSection]
  have hcomp := ConcreteCategory.comp_apply
    ((supportRelativeCohomologyToSheaf analyticPlaneTop
      coordinateHyperplaneAnalyticSupport 2).app (op ⊤))
    ((supportRelativeCohomologySheaf analyticPlaneTop
      coordinateHyperplaneAnalyticSupport 2).obj.map
      (homOfLE (show
        firstChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
          (⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 1)))) ≤ ⊤ from le_top)).op)
    (relativeCohomologyMap ℚ 2
      (topOpenSupportPairIso analyticPlaneTop coordinateHyperplaneAnalyticSupport).hom
      coordinateHyperplaneExplicitSupportedSingularClass)
  exact hcomp.symm.trans (hglobal.symm.trans (hclass.trans hlocal.symm))

/-- Restricting the global explicit sheaf section to the second affine chart gives the
transported literal winding cocycle `(0, windingIndex(X₀/X₂))`. -/
theorem coordinateHyperplaneExplicitSupportedSheafSection_restrict_second :
    (supportRelativeCohomologySheaf analyticPlaneTop
      coordinateHyperplaneAnalyticSupport 2).obj.map
      (homOfLE (show
        secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
          (⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 2)))) ≤ ⊤ from le_top)).op
      coordinateHyperplaneExplicitSupportedSheafSection =
    (supportRelativeCohomologySheafOpenIso
      secondChartAnalyticOpenEmbeddingMap
      secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding
      coordinateHyperplaneAnalyticSupport secondNormalComplementᶜ
      secondChartAnalyticOpenEmbeddingMap_preimage_support 2).hom.hom.app (op ⊤)
      secondChartHyperplaneWindingSheafSection := by
  have hglobal := ConcreteCategory.congr_hom
    ((supportRelativeCohomologyToSheaf analyticPlaneTop
      coordinateHyperplaneAnalyticSupport 2).naturality
      (homOfLE (show
        secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
          (⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 2)))) ≤ ⊤ from le_top)).op)
    (relativeCohomologyMap ℚ 2
      (topOpenSupportPairIso analyticPlaneTop coordinateHyperplaneAnalyticSupport).hom
      coordinateHyperplaneExplicitSupportedSingularClass)
  have hlocal := supportRelativeCohomologySheafOpenIso_unit_apply
    secondChartAnalyticOpenEmbeddingMap
    secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding
    coordinateHyperplaneAnalyticSupport secondNormalComplementᶜ
    secondChartAnalyticOpenEmbeddingMap_preimage_support 2 ⊤
    (relativeCohomologyMap ℚ 2
      (topOpenComplementSupportPairIso
        (TopCat.of (ComplexPoint (analyticChart 2))) secondNormalComplement).hom
      secondChartHyperplaneRelativeSingularClass)
  have hclass := congrArg
    (fun a ↦ (supportRelativeCohomologyToSheaf analyticPlaneTop
      coordinateHyperplaneAnalyticSupport 2).app
        (op (secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj ⊤)) a)
    coordinateHyperplaneExplicitTopClass_restrict_second
  dsimp only [coordinateHyperplaneExplicitSupportedSheafSection,
    secondChartHyperplaneWindingSheafSection]
  have hcomp := ConcreteCategory.comp_apply
    ((supportRelativeCohomologyToSheaf analyticPlaneTop
      coordinateHyperplaneAnalyticSupport 2).app (op ⊤))
    ((supportRelativeCohomologySheaf analyticPlaneTop
      coordinateHyperplaneAnalyticSupport 2).obj.map
      (homOfLE (show
        secondChartAnalyticOpenEmbeddingMap_isOpenEmbedding.functor.obj
          (⊤ : Opens (TopCat.of (ComplexPoint (analyticChart 2)))) ≤ ⊤ from le_top)).op)
    (relativeCohomologyMap ℚ 2
      (topOpenSupportPairIso analyticPlaneTop coordinateHyperplaneAnalyticSupport).hom
      coordinateHyperplaneExplicitSupportedSingularClass)
  exact hcomp.symm.trans (hglobal.symm.trans (hclass.trans hlocal.symm))

end AlgebraicGeometry.ProjectivePlane.CoordinateCharts
