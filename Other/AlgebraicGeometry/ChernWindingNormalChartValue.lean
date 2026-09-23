/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingNormalChartBoundary
public import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.NormalProjectionCoclass
public import HodgeConjecture.Lemmas.LinearAlgebra.ComplexOrientation

/-!
# The winding number of the normal coordinate on a flattening chart

This file proves the *entire* Lelong–Poincaré normalisation, in purely topological form:

> on the flattened-support neighbourhood of a chart that flattens a codimension-one support, the
> winding number of the **normal coordinate** along the boundary of the local normal class is `1`.

`ChernWinding.windingPeriod_flattenedSupportNormalClass`.

The proof is a chain of four transports, each of which is a lemma already in the repository or in
`ChernWindingNormalChartBoundary.lean`:

* `flattenedSupportNormalClass_eq_normalFiber` writes the local normal class as the image of
  `standardComplexLocalClass ℚ 1` under `Ψ := normalSliceSection ≫ flattenedSupportPairIso.hom`;
* `relativeSingularBoundary_naturality` moves the connecting map `∂` across `Ψ`;
* `normalFiber_comp_chartNormalProjection` identifies `Ψ ≫ chartNormalProjectionPair` with the
  recentred radial compression `centeredComplexEmbeddingPair 1 (univBall 0 r) … 0`, and
  `centeredComplexUnivBall_preserves_standardComplexLocalClass` says that compression fixes
  `standardComplexLocalClass ℚ 1` — so the radial compression built into
  `flattenedSupportEmbedding` costs nothing;
* `relativeSingularBoundary_standardComplexLocalClass` and
  `windingPeriod_standardPuncturedBoundaryClass` finish, with the sign `+1`.

The only hypothesis is `hcoord`: the given nowhere vanishing function *is* the normal coordinate
of the chart, i.e. `g w = (e w).2 0`, expressed through the repository's own
`chartNormalProjectionPair`.
-/



private lemma piCoordCLE_one_re (z : Fin 1 → ℂ) :
    (Complex.piCoordCLE 1 z) 0 = (z 0).re := by
  simp only [Nat.reduceMul, Complex.piCoordCLE, Complex.piBasisOneI, Module.Basis.smulTower', Complex.basisOneI,
    Fin.isValue, Complex.real_smul, Module.Basis.equivFunL_apply, Module.Basis.repr_reindex,
    Equiv.coe_prodComm, Finsupp.mapDomain_equiv_apply]
  rw [show finProdFinEquiv.symm 0 = Prod.swap (finProdFinEquiv.symm 0) by decide]
  rw [Finsupp.mapDomain_apply Prod.swap_injective]
  simp [Module.Basis.smulTower', Complex.basisOneI, show (finProdFinEquiv (m := 2) (n := 1)).symm 0 = (0, 0) by decide]

private lemma piCoordCLE_one_im (z : Fin 1 → ℂ) :
    (Complex.piCoordCLE 1 z) 1 = (z 0).im := by
  simp only [Nat.reduceMul, Complex.piCoordCLE, Complex.piBasisOneI, Module.Basis.smulTower', Complex.basisOneI,
    Fin.isValue, Complex.real_smul, Module.Basis.equivFunL_apply, Module.Basis.repr_reindex,
    Equiv.coe_prodComm, Finsupp.mapDomain_equiv_apply]
  rw [show finProdFinEquiv.symm 1 = Prod.swap (finProdFinEquiv.symm 1) by decide]
  rw [Finsupp.mapDomain_apply Prod.swap_injective]
  simp [Module.Basis.smulTower', Complex.basisOneI, show (finProdFinEquiv (m := 2) (n := 1)).symm 1 = (1, 0) by decide]

@[expose] public noncomputable section

open CategoryTheory Limits Simplicial AlgebraicTopology.Singular

namespace ChernWinding

/-! ### The coordinate on the standard complex punctured line -/

/-- The single complex coordinate of the standard complex punctured line. -/
def complexLineCoordinate : C((puncturedPair ℂ 1).snd, ℂ) :=
  ⟨fun z => Subtype.val z 0, (continuous_apply 0).comp continuous_subtype_val⟩

theorem complexLineCoordinate_apply (z : (puncturedPair ℂ 1).snd) :
    complexLineCoordinate z = Subtype.val z 0 := rfl

theorem complexLineCoordinate_ne_zero (z : (puncturedPair ℂ 1).snd) :
    complexLineCoordinate z ≠ 0 := by
  intro h
  refine z.2 (funext fun j => ?_)
  obtain rfl : j = 0 := Subsingleton.elim _ _
  exact h

theorem complexLineCoordinate_standardRealToComplex (v : (puncturedPair ℝ 2).snd) :
    complexLineCoordinate (((standardComplexRealPairIso 1).inv).left v) = complexCoordinate v := by
  show ((complexRealHomeomorph 1).symm (Subtype.val v)) 0 = complexCoordinateFun (Subtype.val v)
  apply Complex.ext
  · calc
      (((complexRealHomeomorph 1).symm (Subtype.val v)) 0).re =
          (Complex.piCoordCLE 1 ((complexRealHomeomorph 1).symm (Subtype.val v))) 0 :=
            (piCoordCLE_one_re _).symm
      _ = (Subtype.val v) 0 := by
        simpa [complexRealHomeomorph] using congrFun ((complexRealHomeomorph 1).right_inv (Subtype.val v)) 0
      _ = (complexCoordinateFun (Subtype.val v)).re := by simp [complexCoordinateFun]
  · calc
      (((complexRealHomeomorph 1).symm (Subtype.val v)) 0).im =
          (Complex.piCoordCLE 1 ((complexRealHomeomorph 1).symm (Subtype.val v))) 1 :=
            (piCoordCLE_one_im _).symm
      _ = (Subtype.val v) 1 := by
        simpa [complexRealHomeomorph] using congrFun ((complexRealHomeomorph 1).right_inv (Subtype.val v)) 1
      _ = (complexCoordinateFun (Subtype.val v)).im := by simp [complexCoordinateFun]

/-! ### The winding number of the normal coordinate -/

section

variable {M : Type} [TopologicalSpace M] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (e : OpenPartialHomeomorph M (E × (Fin 1 → ℂ))) (S : Set M)
  (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
  (x : M) (hx : x ∈ e.source) (h0 : (e x).2 = 0)

/-- The normal projection of the flattened-support neighbourhood onto the standard complex
punctured line. -/
abbrev flattenedNormalProjection :
    neighborhoodSupportComplementPair
      ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M) S ⟶
      puncturedPair ℂ 1 :=
  chartNormalProjectionPair E 1 e S hS (flattenedSupportNeighborhood E 1 e x hx)
    (flattenedSupportNeighborhood_subset_source E 1 e x hx)

set_option maxHeartbeats 1000000 in
/-- The local normal class of the flattened-support neighbourhood, in the degree `1 + 1` in which
the connecting map of the pair is stated. -/
def flattenedNormalClass :
    RelativeHomology ℚ (neighborhoodSupportComplementPair
      ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M) S) (1 + 1) :=
  flattenedSupportNormalClass E 1 e x hx S hS h0

set_option maxHeartbeats 1000000 in
theorem flattenedNormalClass_eq_normalFiber :
    flattenedNormalClass E e S hS x hx h0 =
      relativeHomologyMap ℚ (1 + 1)
        (normalSliceSection E 1 ≫ (flattenedSupportPairIso E 1 e x hx S hS h0).hom)
        (standardComplexLocalClass ℚ 1) :=
  flattenedSupportNormalClass_eq_normalFiber E 1 e S hS x hx h0

/-- The normal slice section, followed by the normal projection, is the recentred radial
compression of the chart. -/
theorem normalSliceSection_comp_flattenedNormalProjection :
    (normalSliceSection E 1 ≫ (flattenedSupportPairIso E 1 e x hx S hS h0).hom) ≫
        flattenedNormalProjection E e S hS x hx =
      centeredComplexEmbeddingPair 1
        (OpenPartialHomeomorph.univBall (0 : Fin 1 → ℂ) (flattenedSupportRadius E 1 e x hx))
        (continuous_complexUnivBall 1 _ _) (injective_complexUnivBall 1 _ _) 0 := by
  rw [Category.assoc]
  exact normalFiber_comp_chartNormalProjection E 1 e S hS x hx h0

/-- **The Lelong–Poincaré normalisation, in topological form.**  On the flattened-support
neighbourhood of a chart flattening a codimension-one support, the winding number of the normal
coordinate along the boundary of the local normal class is `1`. -/
theorem windingPeriod_flattenedNormalClass
    (g : C((neighborhoodSupportComplementPair
      ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M) S).snd, ℂ))
    (hg : ∀ y, g y ≠ 0)
    (hcoord : ∀ w, g w =
      complexLineCoordinate ((flattenedNormalProjection E e S hS x hx).left w)) :
    windingPeriod g hg
        ((relativeSingularBoundary (neighborhoodSupportComplementPair
          ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M) S) 1).hom
          (flattenedNormalClass E e S hS x hx h0)) = 1 := by
  set Ψ : puncturedPair ℂ 1 ⟶
      neighborhoodSupportComplementPair
      ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M) S :=
    normalSliceSection E 1 ≫ (flattenedSupportPairIso E 1 e x hx S hS h0).hom with hΨ
  set Θ : puncturedPair ℂ 1 ⟶ puncturedPair ℂ 1 :=
    centeredComplexEmbeddingPair 1
      (OpenPartialHomeomorph.univBall (0 : Fin 1 → ℂ) (flattenedSupportRadius E 1 e x hx))
      (continuous_complexUnivBall 1 _ _) (injective_complexUnivBall 1 _ _) 0 with hΘ
  have hcomp : Ψ ≫ flattenedNormalProjection E e S hS x hx = Θ :=
    normalSliceSection_comp_flattenedNormalProjection E e S hS x hx h0
  have hgΨ : ∀ z, (g.comp (topMap Ψ.left)) z ≠ 0 := fun z => hg _
  have hfun : g.comp (topMap Ψ.left) = complexLineCoordinate.comp (topMap Θ.left) := by
    refine ContinuousMap.ext fun z => ?_
    show g (Ψ.left z) = complexLineCoordinate (Θ.left z)
    rw [hcoord (Ψ.left z), ← hcomp]
    rfl
  have hΘne : ∀ z, (complexLineCoordinate.comp (topMap Θ.left)) z ≠ 0 := by
    intro z
    show complexLineCoordinate (Θ.left z) ≠ 0
    exact complexLineCoordinate_ne_zero _
  have hreal : ∀ v, (complexLineCoordinate.comp
      (topMap ((standardComplexRealPairIso 1).inv).left)) v ≠ 0 := by
    intro v
    show complexLineCoordinate (((standardComplexRealPairIso 1).inv).left v) ≠ 0
    exact complexLineCoordinate_ne_zero _
  rw [flattenedNormalClass_eq_normalFiber E e S hS x hx h0, ← hΨ,
    relativeSingularBoundary_relativeHomologyMap Ψ 1 (standardComplexLocalClass ℚ 1),
    ← homologyMap_eq_chainPairFunctor_left Ψ 1,
    ← windingPeriod_map g Ψ.left hg hgΨ,
    windingPeriod_congr hgΨ hΘne hfun,
    windingPeriod_map complexLineCoordinate Θ.left complexLineCoordinate_ne_zero hΘne,
    homologyMap_eq_chainPairFunctor_left Θ 1,
    ← relativeSingularBoundary_relativeHomologyMap Θ 1 (standardComplexLocalClass ℚ 1),
    centeredComplexUnivBall_preserves_standardComplexLocalClass 1 (0 : Fin 1 → ℂ)
      (flattenedSupportRadius E 1 e x hx) (flattenedSupportRadius_pos E 1 e x hx) 0,
    relativeSingularBoundary_standardComplexLocalClass,
    ← windingPeriod_map complexLineCoordinate ((standardComplexRealPairIso 1).inv).left
      complexLineCoordinate_ne_zero hreal,
    windingPeriod_congr hreal complexCoordinate_ne_zero
      (ContinuousMap.ext complexLineCoordinate_standardRealToComplex)]
  exact windingPeriod_standardPuncturedBoundaryClass

end

end ChernWinding
