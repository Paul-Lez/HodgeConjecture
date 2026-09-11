/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingNormalChartTransport

/-!
# The glued coclass restricts to the normal-projection coclass of a flattening chart

This file discharges the third input of `HasGenericFlatteningCharts` (§4.3 step 4 item 3 of
`docs/DIVISOR_HANDOFF.md`): at every point `q` of the smooth-support open lying on the component
`Z_x`, there is a holomorphic chart of `X^an` flattening `Z_x` at `q` such that the repository's
glued coclass section `cycleComponentSmoothSupportCoclassSection` restricts, on the flattened
neighbourhood of the chart, to the chart's own normal-projection coclass — the field
`coclass_restrict` of `GenericWindingChartData`, verbatim.

The chart is the repository's canonical flattening chart
`closedImmersionHolomorphicFlatteningChart` of the smooth-locus closed immersion, transported to
`X^an` through the analytic open embedding `cycleComponentSmoothClosedLiftAmbientMap`
(`openEmbeddingTransportChart`).  The coclass identity is a *section* identity, not just a germ
one; it is obtained from the chart-level normalisation
`smoothClosedSupportCoclassSection_restrict_chart` upstairs by

* `chartNormalProjectionCoclass_transport`: the pull-back of the normal-projection coclass of a
  chart along the pair homeomorphism of an open embedding is the normal-projection coclass of the
  transported chart (both are pulled back from the same standard class along the same map);
* `supportRelativeCohomologySectionOnOpen_restrict_flattened`: the section transported through
  `supportRelativeCohomologySheafOpenIso` restricts on the flattened neighbourhood of the
  transported chart to the sheafification of that chart's coclass.

The degree rewrite `d - (d - 1) = 1` inside `cycleComponentSmoothClosedLiftCoclassSection` is
handled once, by `subst`, in `nonempty_transportedFlatteningChart_cast`.

`FlatteningChartWithCoclass.restrict` shrinks such a chart to any open neighbourhood `V` of `q`
(inside the flattened neighbourhood of the original chart), preserving all the fields; this is
what the remaining obligations (`le_analytic`, a unit on the chart) need.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology Opposite Order

namespace AlgebraicTopology.Singular

/-! ### Transporting a flattening chart along an open embedding -/

section ChartTransport

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] [Nonempty M]
  (f : M → N) (hf : IsOpenEmbedding f)
  (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)
  (e : OpenPartialHomeomorph M (E × (Fin c → ℂ)))

/-- The source of a chart, as an open set. -/
def chartSourceOpens : Opens M := ⟨e.source, e.open_source⟩

/-- A chart of the open piece, viewed as a chart of the ambient space through the inverse of
the open embedding. -/
def openEmbeddingTransportChart : OpenPartialHomeomorph N (E × (Fin c → ℂ)) :=
  (hf.toOpenPartialHomeomorph f).symm.trans e

theorem openEmbeddingTransportChart_apply (w : M) :
    openEmbeddingTransportChart f hf E c e (f w) = e w := by
  rw [openEmbeddingTransportChart, OpenPartialHomeomorph.trans_apply,
    hf.toOpenPartialHomeomorph_left_inv]

theorem openEmbeddingTransportChart_source :
    (openEmbeddingTransportChart f hf E c e).source = f '' e.source := by
  ext y
  rw [openEmbeddingTransportChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, hf.toOpenPartialHomeomorph_target]
  constructor
  · rintro ⟨⟨w, rfl⟩, hw⟩
    refine ⟨w, ?_, rfl⟩
    rwa [Set.mem_preimage, hf.toOpenPartialHomeomorph_left_inv] at hw
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨w, rfl⟩, ?_⟩
    rwa [Set.mem_preimage, hf.toOpenPartialHomeomorph_left_inv]

theorem openEmbeddingTransportChart_source_subset_range :
    (openEmbeddingTransportChart f hf E c e).source ⊆ Set.range f := by
  rw [openEmbeddingTransportChart_source]
  exact Set.image_subset_range f e.source

theorem mem_openEmbeddingTransportChart_source (w : M) (hw : w ∈ e.source) :
    f w ∈ (openEmbeddingTransportChart f hf E c e).source := by
  rw [openEmbeddingTransportChart_source]
  exact ⟨w, hw, rfl⟩

variable (B : Set M) (S : Set N) (hB : f ⁻¹' S = B)
  (hS : ∀ y ∈ e.source, y ∈ B ↔ (e y).2 = 0)

include hB hS in
/-- The transported chart flattens the ambient support. -/
theorem openEmbeddingTransportChart_mem_support_iff :
    ∀ y ∈ (openEmbeddingTransportChart f hf E c e).source,
      y ∈ S ↔ (openEmbeddingTransportChart f hf E c e y).2 = 0 := by
  intro y hy
  rw [openEmbeddingTransportChart_source] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  rw [openEmbeddingTransportChart_apply, ← hS w hw, ← hB]
  rfl

theorem image_subset_openEmbeddingTransportChart_source (W : Set M) (hW : W ⊆ e.source) :
    f '' W ⊆ (openEmbeddingTransportChart f hf E c e).source :=
  (Set.image_mono hW).trans (openEmbeddingTransportChart_source f hf E c e).symm.subset

/-- The normal projection of the transported chart, precomposed with the pair homeomorphism of
the open embedding, is the normal projection of the original chart. -/
theorem chartNormalProjectionPair_transport (W : Set M) (hW : W ⊆ e.source) :
    (neighborhoodSupportPairImageIso f hf.isEmbedding W B S
        (fun w _ => by rw [← hB]; rfl)).inv ≫
      chartNormalProjectionPair E c e B hS W hW =
    chartNormalProjectionPair E c (openEmbeddingTransportChart f hf E c e) S
      (openEmbeddingTransportChart_mem_support_iff f hf E c e B S hB hS) (f '' W)
      (image_subset_openEmbeddingTransportChart_source f hf E c e W hW) := by
  have key : ∀ v : f '' W, (e ((hf.isEmbedding.homeomorphImage W).symm v).1).2 =
      (openEmbeddingTransportChart f hf E c e v.1).2 := by
    intro v
    have h : f ((hf.isEmbedding.homeomorphImage W).symm v).1 = v.1 :=
      congrArg Subtype.val ((hf.isEmbedding.homeomorphImage W).apply_symm_apply v)
    conv_rhs => rw [← h, openEmbeddingTransportChart_apply]
  apply MorphismProperty.Arrow.Hom.ext
  · ext v
    exact key v
  · ext v
    exact key v.1

/-- **Transport of the normal-projection coclass.**  Pulling back the coclass of a chart along
the pair homeomorphism of an open embedding gives the coclass of the transported chart. -/
theorem chartNormalProjectionCoclass_transport (W : Set M) (hW : W ⊆ e.source) :
    relativeCohomologyMap ℚ (2 * c)
      (neighborhoodSupportPairImageIso f hf.isEmbedding W B S
        (fun w _ => by rw [← hB]; rfl)).inv
      (chartNormalProjectionCoclass E c e B hS W hW) =
    chartNormalProjectionCoclass E c (openEmbeddingTransportChart f hf E c e) S
      (openEmbeddingTransportChart_mem_support_iff f hf E c e B S hB hS) (f '' W)
      (image_subset_openEmbeddingTransportChart_source f hf E c e W hW) := by
  unfold chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    chartNormalProjectionPair_transport f hf E c e B S hB hS W hW]

end ChartTransport

/-! ### Transporting the sheafified section -/

section SheafTransport

variable {X Y : TopCat.{0}} (f : Y ⟶ X) (hf : IsOpenEmbedding f)
  (S : Set X) (B : Set Y) (hB : f ⁻¹' S = B)

/-- If the auxiliary section is the sheafification of a class on `V`, its transport restricts on
the image of `V` to the sheafification of the pulled-back class. -/
theorem supportRelativeCohomologySectionOnOpen_restrict_eq_toSheaf (n : ℕ) (U : Opens X)
    (hU : hf.functor.obj ⊤ = U)
    (s : (supportRelativeCohomologySheaf Y B n).obj.obj (op ⊤)) (V : Opens Y)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set Y) B) n)
    (hs : (supportRelativeCohomologySheaf Y B n).obj.map (homOfLE (show V ≤ ⊤ from le_top)).op s =
      (supportRelativeCohomologyToSheaf Y B n).app (op V) a)
    (hV : hf.functor.obj V ≤ U) :
    (supportRelativeCohomologySheaf X S n).obj.map (homOfLE hV).op
      (supportRelativeCohomologySectionOnOpen f hf S B hB n U hU s) =
    (supportRelativeCohomologyToSheaf X S n).app (op (hf.functor.obj V))
      (relativeCohomologyMap ℚ n
        (neighborhoodSupportPairImageIso f hf.isEmbedding (V : Set Y) B S
          (fun y _ => by rw [← hB]; rfl)).inv a) := by
  rw [supportRelativeCohomologySectionOnOpen_restrict, hs,
    supportRelativeCohomologySheafOpenIso_unit_apply,
    supportRelativeCohomologyPresheafOpenIso_inv_app]

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)
  (e : OpenPartialHomeomorph Y (E × (Fin c → ℂ)))
  (hS : ∀ y ∈ e.source, y ∈ B ↔ (e y).2 = 0) [Nonempty Y]

theorem flattenedSupportNeighborhood_openEmbeddingTransportChart_le (U : Opens X)
    (hU : hf.functor.obj ⊤ = U) (q : X)
    (hq : q ∈ (openEmbeddingTransportChart f hf E c e).source) :
    flattenedSupportNeighborhood E c (openEmbeddingTransportChart f hf E c e) q hq ≤ U := by
  intro y hy
  obtain ⟨w, rfl⟩ := openEmbeddingTransportChart_source_subset_range f hf E c e
    (flattenedSupportNeighborhood_subset_source E c _ q hq hy)
  rw [← hU]
  exact ⟨w, trivial, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **Transport of the chart normalisation.**  If the auxiliary section is, on the whole source
of a flattening chart, the sheafification of that chart's normal-projection coclass, then its
transport is, on the flattened neighbourhood of the transported chart at any of its points, the
sheafification of the transported chart's normal-projection coclass. -/
theorem supportRelativeCohomologySectionOnOpen_restrict_flattened (U : Opens X)
    (hU : hf.functor.obj ⊤ = U)
    (s : (supportRelativeCohomologySheaf Y B (2 * c)).obj.obj (op ⊤))
    (hs : (supportRelativeCohomologySheaf Y B (2 * c)).obj.map
        (homOfLE (show chartSourceOpens E c e ≤ ⊤ from le_top)).op s =
      (supportRelativeCohomologyToSheaf Y B (2 * c)).app (op (chartSourceOpens E c e))
        (chartNormalProjectionCoclass E c e B hS (chartSourceOpens E c e) subset_rfl))
    (q : X) (hq : q ∈ (openEmbeddingTransportChart f hf E c e).source) :
    (supportRelativeCohomologySheaf X S (2 * c)).obj.map
      (homOfLE (flattenedSupportNeighborhood_openEmbeddingTransportChart_le
        f hf E c e U hU q hq)).op
      (supportRelativeCohomologySectionOnOpen f hf S B hB (2 * c) U hU s) =
    (supportRelativeCohomologyToSheaf X S (2 * c)).app
      (op (flattenedSupportNeighborhood E c (openEmbeddingTransportChart f hf E c e) q hq))
      (chartNormalProjectionCoclass E c (openEmbeddingTransportChart f hf E c e) S
        (openEmbeddingTransportChart_mem_support_iff f hf E c e B S hB hS)
        (flattenedSupportNeighborhood E c (openEmbeddingTransportChart f hf E c e) q hq)
        (flattenedSupportNeighborhood_subset_source E c _ q hq)) := by
  have hV : hf.functor.obj (chartSourceOpens E c e) ≤ U := by
    intro y hy
    obtain ⟨w, _, rfl⟩ := hy
    rw [← hU]
    exact ⟨w, trivial, rfl⟩
  have hle : flattenedSupportNeighborhood E c (openEmbeddingTransportChart f hf E c e) q hq ≤
      hf.functor.obj (chartSourceOpens E c e) := by
    intro y hy
    have h := flattenedSupportNeighborhood_subset_source E c _ q hq hy
    rw [openEmbeddingTransportChart_source] at h
    exact h
  have h1 := supportRelativeCohomologySectionOnOpen_restrict_eq_toSheaf f hf S B hB (2 * c) U hU
    s (chartSourceOpens E c e) _ hs hV
  rw [chartNormalProjectionCoclass_transport f hf E c e B S hB hS
    (chartSourceOpens E c e : Set Y) subset_rfl] at h1
  have hcomp : (homOfLE (flattenedSupportNeighborhood_openEmbeddingTransportChart_le
      f hf E c e U hU q hq)).op = (homOfLE hV).op ≫ (homOfLE hle).op := Subsingleton.elim _ _
  rw [hcomp, Functor.map_comp, ConcreteCategory.comp_apply, h1]
  have h2 := ConcreteCategory.congr_hom
    ((supportRelativeCohomologyToSheaf X S (2 * c)).naturality (homOfLE hle).op)
    (chartNormalProjectionCoclass E c (openEmbeddingTransportChart f hf E c e) S
      (openEmbeddingTransportChart_mem_support_iff f hf E c e B S hB hS)
      (f '' (chartSourceOpens E c e : Set Y))
      (image_subset_openEmbeddingTransportChart_source f hf E c e _ subset_rfl))
  simp only [ConcreteCategory.comp_apply] at h2
  rw [← h2]
  congr 1
  exact chartNormalProjectionCoclass_restrict E c (openEmbeddingTransportChart f hf E c e) S
    (openEmbeddingTransportChart_mem_support_iff f hf E c e B S hB hS) hle _

end SheafTransport

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

/-! ### The transported flattening chart of a smooth closed immersion -/

section GeneralOpenTransport

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]
  {M : TopCat.{0}} (f : TopCat.of (ComplexPoint X) ⟶ M)
  (hf : IsOpenEmbedding f) (S : Set M)
  (hS : f ⁻¹' S = Set.range (Point.map i))
  (U : Opens M) (hU : hf.functor.obj ⊤ = U)

/-- A flattening chart of the transported support at `q`, in tangent dimension `m` and normal
dimension `c`, on whose flattened neighbourhood the transport of the auxiliary section `s` is
the sheafification of the chart's normal-projection coclass. -/
structure TransportedFlatteningChart (q : M) (c : ℕ)
    (s : (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (Set.range (Point.map i)) (2 * c)).obj.obj (op ⊤)) where
  /-- a holomorphic chart of the ambient space flattening the support -/
  chart : OpenPartialHomeomorph M ((Fin m → ℂ) × (Fin c → ℂ))
  mem_source : q ∈ chart.source
  flattens : ∀ y ∈ chart.source, y ∈ S ↔ (chart y).2 = 0
  center : (chart q).2 = 0
  le : flattenedSupportNeighborhood (Fin m → ℂ) c chart q mem_source ≤ U
  coclass_restrict :
    (supportRelativeCohomologySheaf M S (2 * c)).obj.map (homOfLE le).op
      (supportRelativeCohomologySectionOnOpen f hf S (Set.range (Point.map i)) hS (2 * c) U hU
        s) =
    (supportRelativeCohomologyToSheaf M S (2 * c)).app
      (op (flattenedSupportNeighborhood (Fin m → ℂ) c chart q mem_source))
      (chartNormalProjectionCoclass (Fin m → ℂ) c chart S flattens
        (flattenedSupportNeighborhood (Fin m → ℂ) c chart q mem_source)
        (flattenedSupportNeighborhood_subset_source (Fin m → ℂ) c chart q mem_source))

set_option maxHeartbeats 1000000 in
/-- The canonical flattening chart of the closed immersion at `z`, transported through the open
embedding, carries the normalised smooth-support section. -/
theorem nonempty_transportedFlatteningChart (z : ComplexPoint Y) :
    Nonempty (TransportedFlatteningChart X Y i m f hf S hS U hU (f (Point.map i z)) (d - m)
      (smoothClosedSupportCoclassSection X Y i m d)) := by
  haveI : Nonempty (TopCat.of (ComplexPoint X)) := ⟨Point.map i z⟩
  let e := closedImmersionHolomorphicFlatteningChart X Y i m d z
  have hmem : f (Point.map i z) ∈ (openEmbeddingTransportChart f hf (Fin m → ℂ) (d - m) e).source :=
    mem_openEmbeddingTransportChart_source f hf (Fin m → ℂ) (d - m) e _
      (closedImmersionHolomorphicFlatteningChart_mem_source X Y i m d z)
  exact ⟨{
    chart := openEmbeddingTransportChart f hf (Fin m → ℂ) (d - m) e
    mem_source := hmem
    flattens := openEmbeddingTransportChart_mem_support_iff f hf (Fin m → ℂ) (d - m) e _ S hS
      (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z)
    center := by
      rw [openEmbeddingTransportChart_apply]
      exact congrArg Prod.snd (closedImmersionHolomorphicFlatteningChart_center X Y i m d z)
    le := flattenedSupportNeighborhood_openEmbeddingTransportChart_le f hf (Fin m → ℂ) (d - m) e
      U hU _ hmem
    coclass_restrict := supportRelativeCohomologySectionOnOpen_restrict_flattened f hf S _ hS
      (Fin m → ℂ) (d - m) e (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z)
      U hU (smoothClosedSupportCoclassSection X Y i m d)
      (smoothClosedSupportCoclassSection_restrict_chart X Y i m d z) _ hmem }⟩

/-- The same, with the normal dimension rewritten along any equation `d - m = c`; this absorbs
the degree rewrite inside `cycleComponentSmoothClosedLiftCoclassSection`. -/
theorem nonempty_transportedFlatteningChart_cast (z : ComplexPoint Y) (c : ℕ) (hc : d - m = c) :
    Nonempty (TransportedFlatteningChart X Y i m f hf S hS U hU (f (Point.map i z)) c
      (hc ▸ smoothClosedSupportCoclassSection X Y i m d)) := by
  subst hc
  exact nonempty_transportedFlatteningChart X Y i m d f hf S hS U hU z

end GeneralOpenTransport

/-! ### The component case -/

section Component

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernWindingChartCoclassRestrictTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

variable (x : X.left) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- A flattening chart of the component `Z_x` at `q`, small enough to lie in the smooth-support
open, on whose flattened neighbourhood the glued coclass section is the chart's normal-projection
coclass: exactly the chart fields and the field `coclass_restrict` of
`GenericWindingChartData`. -/
structure FlatteningChartWithCoclass (q : ComplexPoint X) where
  /-- a holomorphic chart flattening the component of `x` -/
  chart : OpenPartialHomeomorph (ComplexPoint X) ((Fin (d - 1) → ℂ) × (Fin 1 → ℂ))
  mem_source : q ∈ chart.source
  /-- the chart flattens the component onto `{normal = 0}` -/
  flattens : ∀ y ∈ chart.source, y ∈ cycleComponentSupport X x ↔ (chart y).2 = 0
  /-- the chart is centred on the component -/
  center : (chart q).2 = 0
  le : flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 chart q mem_source ≤
    cycleComponentSmoothSupportAmbientOpen X x
  /-- **the glued coclass section restricts to the chart's normal-projection coclass** -/
  coclass_restrict : ∀ hx : coheight x = ((1 : ℕ) : ℕ∞),
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * 1)).obj.map (homOfLE le).op
        (cycleComponentSmoothSupportCoclassSection X x (d := d) hx) =
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * 1)).app
        (op (flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 chart q mem_source))
        (chartNormalProjectionCoclass (Fin (d - 1) → ℂ) 1 chart (cycleComponentSupport X x)
          flattens (flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 chart q mem_source)
          (flattenedSupportNeighborhood_subset_source (Fin (d - 1) → ℂ) 1 chart q mem_source))

set_option maxHeartbeats 1000000 in
/-- **Existence of flattening charts carrying the coclass.**  At every point of the smooth-support
open lying on the component, the transported canonical flattening chart of the smooth-locus
closed immersion is a `FlatteningChartWithCoclass`. -/
theorem exists_flatteningChartWithCoclass (hx : coheight x = ((1 : ℕ) : ℕ∞))
    (q : ComplexPoint X) (hq : q ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (hqS : q ∈ cycleComponentSupport X x) :
    Nonempty (FlatteningChartWithCoclass X x d q) := by
  let := cycleComponentSmoothClosedLiftStructureMap_smoothOfRelativeDimension X x (d := d) hx
  have hq' : q ∈ (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).functor.obj ⊤ := by
    rw [cycleComponentSmoothClosedLiftAmbientMap_imageOpen]
    exact hq
  obtain ⟨q', -, rfl⟩ := hq'
  have hq'S : q' ∈ Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)) := by
    rw [← cycleComponentSmoothClosedLiftAmbientMap_support]
    exact hqS
  obtain ⟨z, rfl⟩ := hq'S
  obtain ⟨T⟩ := nonempty_transportedFlatteningChart_cast
    (cycleComponentSmoothLocusAmbientOpenOver X x) (cycleComponentSmoothLocusOver X x)
    (cycleComponentSmoothLocusClosedLiftOver X x) (d - 1) d
    (cycleComponentSmoothClosedLiftAmbientMap X x)
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
    (cycleComponentSupport X x) (cycleComponentSmoothClosedLiftAmbientMap_support X x)
    (cycleComponentSmoothSupportAmbientOpen X x)
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x) z 1
    (cycleComponentSmoothClosedLift_codimension X x (d := d) hx)
  exact ⟨{
    chart := T.chart
    mem_source := T.mem_source
    flattens := T.flattens
    center := T.center
    le := T.le
    coclass_restrict := fun _ => T.coclass_restrict }⟩

namespace FlatteningChartWithCoclass

variable {X x d} {q : ComplexPoint X} (F : FlatteningChartWithCoclass X x d q)
  (V : Opens (ComplexPoint X))

/-- The flattened neighbourhood of the chart. -/
abbrev flattened : Opens (ComplexPoint X) :=
  flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 F.chart q F.mem_source

/-- The chart restricted to `V ⊓ flattened`. -/
def restrictChart : OpenPartialHomeomorph (ComplexPoint X) ((Fin (d - 1) → ℂ) × (Fin 1 → ℂ)) :=
  F.chart.restrOpen ((V ⊓ F.flattened : Opens (ComplexPoint X)) : Set (ComplexPoint X))
    (V ⊓ F.flattened).isOpen

@[simp] theorem restrictChart_apply (y : ComplexPoint X) : F.restrictChart V y = F.chart y := rfl

theorem restrictChart_source :
    (F.restrictChart V).source =
      F.chart.source ∩ ((V ⊓ F.flattened : Opens (ComplexPoint X)) : Set (ComplexPoint X)) :=
  OpenPartialHomeomorph.restrOpen_source _ _ _

theorem restrictChart_source_subset : (F.restrictChart V).source ⊆ V := by
  rw [restrictChart_source]
  exact fun _ hy => hy.2.1

theorem restrictChart_source_subset_flattened : (F.restrictChart V).source ⊆ F.flattened := by
  rw [restrictChart_source]
  exact fun _ hy => hy.2.2

theorem mem_restrictChart_source (hq : q ∈ V) : q ∈ (F.restrictChart V).source := by
  rw [restrictChart_source]
  exact ⟨F.mem_source, hq, mem_flattenedSupportNeighborhood _ _ _ _ _⟩

theorem restrictChart_flattens :
    ∀ y ∈ (F.restrictChart V).source,
      y ∈ cycleComponentSupport X x ↔ (F.restrictChart V y).2 = 0 := by
  intro y hy
  rw [restrictChart_source] at hy
  exact F.flattens y hy.1

theorem flattened_restrictChart_le (hq : q ∈ V) :
    flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 (F.restrictChart V) q
      (F.mem_restrictChart_source V hq) ≤ F.flattened :=
  fun _ hy => F.restrictChart_source_subset_flattened V
    (flattenedSupportNeighborhood_subset_source _ _ _ _ _ hy)

theorem flattened_restrictChart_le_self (hq : q ∈ V) :
    flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 (F.restrictChart V) q
      (F.mem_restrictChart_source V hq) ≤ V :=
  fun _ hy => F.restrictChart_source_subset V
    (flattenedSupportNeighborhood_subset_source _ _ _ _ _ hy)

set_option maxHeartbeats 1000000 in
/-- **Shrinking.**  Restricting the chart to an open neighbourhood `V` of `q` (inside the
flattened neighbourhood of the original chart) gives again a `FlatteningChartWithCoclass`, whose
chart source lies in `V` (`restrictChart_source_subset`) and whose flattened neighbourhood lies
in `V` (`flattened_restrictChart_le_self`). -/
def restrict (hq : q ∈ V) : FlatteningChartWithCoclass X x d q where
  chart := F.restrictChart V
  mem_source := F.mem_restrictChart_source V hq
  flattens := F.restrictChart_flattens V
  center := F.center
  le := (F.flattened_restrictChart_le V hq).trans F.le
  coclass_restrict := fun hx => by
    have hcomp : (homOfLE ((F.flattened_restrictChart_le V hq).trans F.le)).op =
        (homOfLE F.le).op ≫ (homOfLE (F.flattened_restrictChart_le V hq)).op :=
      Subsingleton.elim _ _
    rw [hcomp, Functor.map_comp, ConcreteCategory.comp_apply, F.coclass_restrict hx]
    have h2 := ConcreteCategory.congr_hom
      ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * 1)).naturality
          (homOfLE (F.flattened_restrictChart_le V hq)).op)
      (chartNormalProjectionCoclass (Fin (d - 1) → ℂ) 1 F.chart (cycleComponentSupport X x)
        F.flattens F.flattened (flattenedSupportNeighborhood_subset_source _ _ _ _ _))
    simp only [ConcreteCategory.comp_apply] at h2
    rw [← h2]
    congr 1
    exact chartNormalProjectionCoclass_restrict (Fin (d - 1) → ℂ) 1 F.chart
      (cycleComponentSupport X x) F.flattens (F.flattened_restrictChart_le V hq) _

@[simp] theorem restrict_chart (hq : q ∈ V) : (F.restrict V hq).chart = F.restrictChart V := rfl

theorem restrict_chart_source_subset (hq : q ∈ V) : (F.restrict V hq).chart.source ⊆ V :=
  F.restrictChart_source_subset V

theorem restrict_flattened_le (hq : q ∈ V) :
    flattenedSupportNeighborhood (Fin (d - 1) → ℂ) 1 (F.restrict V hq).chart q
      (F.restrict V hq).mem_source ≤ V :=
  F.flattened_restrictChart_le_self V hq

end FlatteningChartWithCoclass

end Component

end AlgebraicGeometry.ComplexPoint
