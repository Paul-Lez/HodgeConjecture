/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SmoothClosedSupportLocalHomology
public import Other.AlgebraicGeometry.HolomorphicClosedImmersionCharts
public import Other.AlgebraicTopology.NormalProjectionOverlap

/-!
# Exactly normalized smooth-support coclasses on actual overlaps

The previously constructed local normal coclass is the pullback of the fixed complex
normal coclass along the actual normal coordinate projection. The actual holomorphic
closed-immersion charts prove that these coclasses agree on sufficiently small common
ambient neighborhoods. No transition compatibility or purity equivalence is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable {X Y : Scheme}
  (structureMapX : X ⟶ Spec (.of ℂ)) (structureMapY : Y ⟶ Spec (.of ℂ))
  (i : Y ⟶ X) (hi : i ≫ structureMapX = structureMapY) (m d : ℕ)
  [SmoothOfRelativeDimension m structureMapY] [SmoothOfRelativeDimension d structureMapX]
  [IsClosedImmersion i] (z : ComplexPoint Y structureMapY)

/-- Actual normal-projection coclass on any subset of a holomorphic flattening chart. -/
def smoothClosedSupportChartCoclass (W : Set (ComplexPoint X structureMapX))
    (hW : W ⊆ (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z).source) :
    RelativeCohomology ℚ (neighborhoodSupportComplementPair W (Set.range (Point.map i hi)))
      (2 * (d - m)) :=
  chartNormalProjectionCoclass (Fin m → ℂ) (d - m)
    (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z)
    (Set.range (Point.map i hi))
    (closedImmersionHolomorphicFlatteningChart_mem_range_iff structureMapX structureMapY i hi m d z) W hW

/-- Restriction is the map induced by the actual inclusion of support-complement pairs. -/
theorem smoothClosedSupportChartCoclass_restrict
    {W V : Set (ComplexPoint X structureMapX)} (hWV : W ⊆ V)
    (hV : V ⊆ (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z).source) :
    relativeCohomologyMap ℚ (2 * (d - m))
      (neighborhoodSupportInclusionPairMap hWV (Set.range (Point.map i hi)))
      (smoothClosedSupportChartCoclass structureMapX structureMapY i hi m d z V hV) =
    smoothClosedSupportChartCoclass structureMapX structureMapY i hi m d z W (hWV.trans hV) :=
  chartNormalProjectionCoclass_restrict _ _ _ _ _ hWV hV

/-- The old local pair-model coclass is exactly the actual chart-projection coclass.
The proof uses the explicit radial normal fiber, including its complex normalization. -/
theorem smoothClosedSupportNormalCoclass_eq_projection
    (V : Opens (ComplexPoint X structureMapX)) (hzV : Point.map i hi z ∈ V) :
    smoothClosedSupportNormalCoclass structureMapX structureMapY i hi m d z V hzV =
    chartNormalProjectionCoclass (Fin m → ℂ) (d - m)
      (smoothClosedSupportRestrictionChart structureMapX structureMapY i hi m d z V)
      (Set.range (Point.map i hi))
      (smoothClosedSupportRestrictionChart_mem_range_iff structureMapX structureMapY i hi m d z V)
      (smoothClosedSupportNeighborhood structureMapX structureMapY i hi m d z V hzV)
      (flattenedSupportNeighborhood_subset_source _ _ _ _ _) := by
  apply chartNormalProjectionCoclass_unique
    (Fin m → ℂ) (d - m)
    (smoothClosedSupportRestrictionChart structureMapX structureMapY i hi m d z V)
    (Set.range (Point.map i hi))
    (smoothClosedSupportRestrictionChart_mem_range_iff structureMapX structureMapY i hi m d z V)
    (Point.map i hi z)
    (smoothClosedSupportRestrictionChart_mem_source structureMapX structureMapY i hi m d z V hzV)
    (congrArg Prod.snd (smoothClosedSupportRestrictionChart_center structureMapX structureMapY i hi m d z V))
  exact smoothClosedSupportNormalCoclass_apply_class structureMapX structureMapY i hi m d z V hzV

/-- On a common smaller neighborhood, restriction of the old local coclass is exactly
the holomorphic-chart coclass. Both maps are the same literal normal projection. -/
theorem smoothClosedSupportNormalCoclass_restrict_eq_chart
    (V : Opens (ComplexPoint X structureMapX)) (hzV : Point.map i hi z ∈ V)
    (W : Set (ComplexPoint X structureMapX))
    (hWV : W ⊆ smoothClosedSupportNeighborhood structureMapX structureMapY i hi m d z V hzV)
    (hW : W ⊆ (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z).source) :
    relativeCohomologyMap ℚ (2 * (d - m))
      (neighborhoodSupportInclusionPairMap hWV (Set.range (Point.map i hi)))
      (smoothClosedSupportNormalCoclass structureMapX structureMapY i hi m d z V hzV) =
    smoothClosedSupportChartCoclass structureMapX structureMapY i hi m d z W hW := by
  rw [smoothClosedSupportNormalCoclass_eq_projection]
  exact chartNormalProjectionCoclass_restrict (Fin m → ℂ) (d - m)
    (smoothClosedSupportRestrictionChart structureMapX structureMapY i hi m d z V)
    (Set.range (Point.map i hi))
    (smoothClosedSupportRestrictionChart_mem_range_iff structureMapX structureMapY i hi m d z V)
    hWV (flattenedSupportNeighborhood_subset_source _ _ _ _ _)

variable (z' : ComplexPoint Y structureMapY)

/-- Exactly normalized ambient coclass agreement for the actual closed-immersion charts.
The only inputs are smoothness, the closed immersion, and membership in its actual chart
overlap and image. Holomorphicity and invertibility of the normal derivative are proved. -/
theorem exists_open_smoothClosedSupportChartCoclass_eq
    (x : ComplexPoint X structureMapX) (hxS : x ∈ Set.range (Point.map i hi))
    (hx : x ∈ (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z).source)
    (hx' : x ∈ (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z').source) :
    ∃ (W : Opens (ComplexPoint X structureMapX))
      (hW : (W : Set _) ⊆ (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z).source)
      (hW' : (W : Set _) ⊆ (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z').source),
      x ∈ W ∧ smoothClosedSupportChartCoclass structureMapX structureMapY i hi m d z W hW =
        smoothClosedSupportChartCoclass structureMapX structureMapY i hi m d z' W hW' := by
  let e := closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z
  let e' := closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z'
  have ht : e x ∈ (closedImmersionNormalTransition structureMapX structureMapY i hi m d z z').source := by
    refine ⟨e.map_source hx, ?_⟩
    change e.symm (e x) ∈ e'.source
    rw [e.left_inv hx]
    exact hx'
  exact exists_open_chartNormalProjectionCoclass_eq (d - m) e e' (Set.range (Point.map i hi))
    (closedImmersionHolomorphicFlatteningChart_mem_range_iff structureMapX structureMapY i hi m d z)
    (closedImmersionHolomorphicFlatteningChart_mem_range_iff structureMapX structureMapY i hi m d z')
    x hx ((closedImmersionHolomorphicFlatteningChart_mem_range_iff
      structureMapX structureMapY i hi m d z x hx).mp hxS) hx'
    (analyticAt_closedImmersionNormalTransition structureMapX structureMapY i hi m d z z' (e x) ht)
    (analyticAt_closedImmersionNormalTransition_symm structureMapX structureMapY i hi m d z z' (e x) ht)

/-- Ambient overlap agreement remains cofinal inside any prescribed common open. -/
theorem exists_open_smoothClosedSupportChartCoclass_eq_within
    (x : ComplexPoint X structureMapX) (hxS : x ∈ Set.range (Point.map i hi))
    (hx : x ∈ (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z).source)
    (hx' : x ∈ (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z').source)
    (U : Opens (ComplexPoint X structureMapX)) (hxU : x ∈ U) :
    ∃ (W : Opens (ComplexPoint X structureMapX))
      (hW : (W : Set _) ⊆ (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z).source)
      (hW' : (W : Set _) ⊆ (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z').source),
      x ∈ W ∧ W ≤ U ∧
      smoothClosedSupportChartCoclass structureMapX structureMapY i hi m d z W hW =
        smoothClosedSupportChartCoclass structureMapX structureMapY i hi m d z' W hW' := by
  obtain ⟨W₀, hW₀, hW₀', hxW₀, heq⟩ := exists_open_smoothClosedSupportChartCoclass_eq
    structureMapX structureMapY i hi m d z z' x hxS hx hx'
  let W := W₀ ⊓ U
  have hWW₀ : (W : Set (ComplexPoint X structureMapX)) ⊆ (W₀ : Set (ComplexPoint X structureMapX)) :=
    fun _ hy => hy.1
  refine ⟨W, hWW₀.trans hW₀, hWW₀.trans hW₀', ⟨hxW₀, hxU⟩, inf_le_right, ?_⟩
  have h := congrArg (relativeCohomologyMap ℚ (2 * (d - m))
    (neighborhoodSupportInclusionPairMap hWW₀ (Set.range (Point.map i hi)))) heq
  simpa only [smoothClosedSupportChartCoclass_restrict] using h

/-- The original exactly normalized local normal coclasses agree after actual pair
restriction on sufficiently small ambient overlaps of the holomorphic chart loci.
This is a comparison theorem for the old classes, not a new definition of their duality. -/
theorem exists_open_smoothClosedSupportNormalCoclass_restrict_eq
    (V V' : Opens (ComplexPoint X structureMapX))
    (hzV : Point.map i hi z ∈ V) (hzV' : Point.map i hi z' ∈ V')
    (x : ComplexPoint X structureMapX) (hxS : x ∈ Set.range (Point.map i hi))
    (hx : x ∈ (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z).source)
    (hx' : x ∈ (closedImmersionHolomorphicFlatteningChart structureMapX structureMapY i hi m d z').source)
    (hxV : x ∈ smoothClosedSupportNeighborhood structureMapX structureMapY i hi m d z V hzV)
    (hxV' : x ∈ smoothClosedSupportNeighborhood structureMapX structureMapY i hi m d z' V' hzV') :
    ∃ (W : Opens (ComplexPoint X structureMapX))
      (hWV : (W : Set (ComplexPoint X structureMapX)) ⊆
        (smoothClosedSupportNeighborhood structureMapX structureMapY i hi m d z V hzV : Set (ComplexPoint X structureMapX)))
      (hWV' : (W : Set (ComplexPoint X structureMapX)) ⊆
        (smoothClosedSupportNeighborhood structureMapX structureMapY i hi m d z' V' hzV' : Set (ComplexPoint X structureMapX))),
      x ∈ W ∧
      relativeCohomologyMap ℚ (2 * (d - m))
        (neighborhoodSupportInclusionPairMap hWV (Set.range (Point.map i hi)))
        (smoothClosedSupportNormalCoclass structureMapX structureMapY i hi m d z V hzV) =
      relativeCohomologyMap ℚ (2 * (d - m))
        (neighborhoodSupportInclusionPairMap hWV' (Set.range (Point.map i hi)))
        (smoothClosedSupportNormalCoclass structureMapX structureMapY i hi m d z' V' hzV') := by
  obtain ⟨W, hW, hW', hxW, hWU, heq⟩ := exists_open_smoothClosedSupportChartCoclass_eq_within
    structureMapX structureMapY i hi m d z z' x hxS hx hx'
    (smoothClosedSupportNeighborhood structureMapX structureMapY i hi m d z V hzV ⊓
      smoothClosedSupportNeighborhood structureMapX structureMapY i hi m d z' V' hzV') ⟨hxV, hxV'⟩
  have hWV : (W : Set (ComplexPoint X structureMapX)) ⊆
      (smoothClosedSupportNeighborhood structureMapX structureMapY i hi m d z V hzV : Set (ComplexPoint X structureMapX)) :=
    fun _ hy => (hWU hy).1
  have hWV' : (W : Set (ComplexPoint X structureMapX)) ⊆
      (smoothClosedSupportNeighborhood structureMapX structureMapY i hi m d z' V' hzV' : Set (ComplexPoint X structureMapX)) :=
    fun _ hy => (hWU hy).2
  refine ⟨W, hWV, hWV', hxW, ?_⟩
  rw [smoothClosedSupportNormalCoclass_restrict_eq_chart structureMapX structureMapY i hi m d z V hzV W hWV hW,
    smoothClosedSupportNormalCoclass_restrict_eq_chart structureMapX structureMapY i hi m d z' V' hzV' W hWV' hW']
  exact heq

end AlgebraicGeometry.ComplexPoint
