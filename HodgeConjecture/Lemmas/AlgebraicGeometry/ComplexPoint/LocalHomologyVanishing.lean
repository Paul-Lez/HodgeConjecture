/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.LocalOrientation
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.EuclideanVanishing
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.ChainHomology

/-!
# Local homology concentration on a smooth complex scheme

The actual compressed-chart map is an isomorphism in every local-homology degree, by
neighborhood excision. Euclidean local homology vanishing therefore proves concentration
in real dimension `2*d`, and stalk exactness gives the corresponding homology-sheaf
vanishing. No local vanishing or bounded-model data is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicTopology.Singular

/-- The compressed complex chart induces an isomorphism in every local-homology degree. -/
theorem chartModelEmbedding_relativeHomologyMap_bijective_degree
    {M : Type} [TopologicalSpace M] [T1Space M]
    (d : ℕ) (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (hx : x ∈ e.source) (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n (chartModelEmbeddingPair d e x hx)) := by
  have htarget : Function.Bijective
      (relativeHomologyMap ℚ n (standardComplexChartTargetPairIso d e x hx).hom) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  have hexcision := neighborhoodPointComplement_relativeHomologyMap_bijective
    (chartModelEmbedding d e x hx).target x (chartModelEmbedding d e x hx).open_target
      (chartModelEmbedding_mem_target d e x hx) n
  rw [← standardComplexChartTargetPairIso_hom_comp_neighborhoodMap d e x hx,
    relativeHomologyMap_comp]
  exact hexcision.comp htarget

/-- The actual chart map, bundled as an isomorphism on relative homology. -/
def chartModelEmbeddingRelativeHomologyIso
    {M : Type} [TopologicalSpace M] [T1Space M]
    (d : ℕ) (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (hx : x ∈ e.source) (n : ℕ) :
    RelativeHomology ℚ (standardComplexPuncturedPair d) n ≅
      RelativeHomology ℚ (pointComplementPair x) n := by
  let f := (relativeHomologyFunctor ℚ n).map (chartModelEmbeddingPair d e x hx)
  have : IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr
    (chartModelEmbedding_relativeHomologyMap_bijective_degree d e x hx n)
  exact asIso f

/-- Complex coordinate space has local homology only in twice its complex dimension. -/
theorem standardComplexLocalHomology_isZero_of_ne (d n : ℕ) (hn : n ≠ 2 * d) :
    IsZero (RelativeHomology ℚ (standardComplexPuncturedPair d) n) :=
  (standardLocalHomology_isZero_of_ne (d * 2) n (by omega)).of_iso
    ((relativeHomologyFunctor ℚ n).mapIso (standardComplexRealPairIso d))

/-- A complex coordinate chart proves local homology vanishing outside its real dimension. -/
theorem localHomology_isZero_of_complexChart
    {M : Type} [TopologicalSpace M] [T1Space M]
    (d : ℕ) (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M)
    (hx : x ∈ e.source) (n : ℕ) (hn : n ≠ 2 * d) :
    IsZero (RelativeHomology ℚ (pointComplementPair x) n) :=
  (standardComplexLocalHomology_isZero_of_ne d n hn).of_iso
    (chartModelEmbeddingRelativeHomologyIso d e x hx n).symm

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicTopology.Singular

variable (X : Over (Spec (.of ℂ))) (d : ℕ)

noncomputable local instance complexLocalHomologyAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

/-- Local homology of a smooth complex scheme is concentrated in its real dimension. -/
theorem localHomology_isZero_of_ne [SmoothOfRelativeDimension d X.hom]
    [T1Space (ComplexPoint X)] (z : ComplexPoint X)
    (n : ℕ) (hn : n ≠ 2 * d) :
    IsZero (RelativeHomology ℚ (pointComplementPair z) n) :=
  localHomology_isZero_of_complexChart d (localChart X d z) z
    (mem_localChart_source X d z) n hn

/-- The homology sheaf of the actual relative-chain complex vanishes off the complex
orientation degree. This supplies the concentration theorem needed by canonical truncation. -/
theorem singularChainHomologySheaf_isZero_of_ne [SmoothOfRelativeDimension d X.hom]
    [T2Space (ComplexPoint X)] (n : ℕ) (hn : n ≠ 2 * d) :
    IsZero (singularChainHomologySheaf ℚ (TopCat.of (ComplexPoint X)) n) :=
  singularChainHomologySheaf_isZero_of_localHomology_isZero ℚ
    (TopCat.of (ComplexPoint X)) n
      (fun z ↦ localHomology_isZero_of_ne X d z n hn)

end AlgebraicGeometry.ComplexPoint
