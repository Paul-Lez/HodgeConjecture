/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.LinearDualQuasiIso
public import HodgeConjecture.Lemmas.AlgebraicTopology.MappingConeQuasiIso
public import HodgeConjecture.Definitions.AlgebraicTopology.RelativeCochainCone
public import Other.AlgebraicTopology.FiniteGoodCoverNerveHomology
public import Other.AlgebraicTopology.RationalOpenCoverOrderedCechBicomplex

/-!
# Relative comparisons obtained from natural absolute chain models

Suppose `C₀ ⟶ C₁` is a chain model for a map `S₀ ⟶ S₁`, and the two
augmentations `Cᵢ ⟶ Sᵢ` are quasi-isomorphisms.  Algebraic duality reverses
the square.  Taking the mapping cones of the resulting restriction maps
therefore gives a canonical comparison from relative singular cochains to
relative cochains in the model `C`.

The commutative square is an explicit argument of every construction below.
In particular, these declarations do not package naturality of any concrete
Čech augmentation as an instance or an assumption hidden in a structure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicTopology

variable {R : Type u} [Field R]

namespace RelativeCechConeComparison

variable {C₀ C₁ S₀ S₁ : ChainComplex (ModuleCat.{u} R) ℕ}

/-- The algebraic-dual cochain map, extended by zero to integer degrees. -/
public def dualMapInt {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) :
    (L.linearDualCochainComplex.extend ComplexShape.embeddingUpNat) ⟶
      (K.linearDualCochainComplex.extend ComplexShape.embeddingUpNat) :=
  HomologicalComplex.extendMap (HomologicalComplex.linearDualMap f)
    ComplexShape.embeddingUpNat

@[simp]
public lemma dualMapInt_id (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    dualMapInt (𝟙 K) = 𝟙 _ := by
  simp [dualMapInt]

@[simp]
public lemma dualMapInt_comp {K L M : ChainComplex (ModuleCat.{u} R) ℕ}
    (f : K ⟶ L) (g : L ⟶ M) :
    dualMapInt (f ≫ g) = dualMapInt g ≫ dualMapInt f := by
  simp [dualMapInt, ← HomologicalComplex.extendMap_comp]

/-- Dualizing a strictly commutative chain square gives the strictly
commutative cochain square needed to map restriction cones. -/
public lemma dualSquare
    (c : C₀ ⟶ C₁) (s : S₀ ⟶ S₁)
    (q₀ : C₀ ⟶ S₀) (q₁ : C₁ ⟶ S₁)
    (h : c ≫ q₁ = q₀ ≫ s) :
    dualMapInt s ≫ dualMapInt q₀ =
      dualMapInt q₁ ≫ dualMapInt c := by
  rw [← dualMapInt_comp, ← dualMapInt_comp, h]

/-- The relative cochain complex associated to a chain map: the mapping cone
of its algebraic-dual restriction map, in integer degrees.  Cone degree
`n - 1` represents relative cohomological degree `n`. -/
public def relativeDualCone {K L : ChainComplex (ModuleCat.{u} R) ℕ}
    (f : K ⟶ L) : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.mappingCone (dualMapInt f)

/-- A natural square of absolute chain models induces the canonical map from
the singular relative-cochain cone to the model relative-cochain cone. -/
public def comparison
    (c : C₀ ⟶ C₁) (s : S₀ ⟶ S₁)
    (q₀ : C₀ ⟶ S₀) (q₁ : C₁ ⟶ S₁)
    (h : c ≫ q₁ = q₀ ≫ s) :
    relativeDualCone s ⟶ relativeDualCone c :=
  CochainComplex.mappingCone.map (dualMapInt s) (dualMapInt c)
    (dualMapInt q₁) (dualMapInt q₀) (dualSquare c s q₀ q₁ h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality of `comparison` for a commutative cube of chain complexes.  The six face
equalities are explicit arguments: no naturality of a concrete chain model is hidden in this
statement. -/
public lemma comparison_naturality
    {C₀' C₁' S₀' S₁' : ChainComplex (ModuleCat.{u} R) ℕ}
    (c : C₀ ⟶ C₁) (s : S₀ ⟶ S₁)
    (c' : C₀' ⟶ C₁') (s' : S₀' ⟶ S₁')
    (q₀ : C₀ ⟶ S₀) (q₁ : C₁ ⟶ S₁)
    (q₀' : C₀' ⟶ S₀') (q₁' : C₁' ⟶ S₁')
    (rC₀ : C₀' ⟶ C₀) (rC₁ : C₁' ⟶ C₁)
    (rS₀ : S₀' ⟶ S₀) (rS₁ : S₁' ⟶ S₁)
    (hc : c ≫ q₁ = q₀ ≫ s) (hc' : c' ≫ q₁' = q₀' ≫ s')
    (hC : c' ≫ rC₁ = rC₀ ≫ c) (hS : s' ≫ rS₁ = rS₀ ≫ s)
    (h₀ : rC₀ ≫ q₀ = q₀' ≫ rS₀)
    (h₁ : rC₁ ≫ q₁ = q₁' ≫ rS₁) :
    comparison c s q₀ q₁ hc ≫ comparison c' c rC₀ rC₁ hC =
      comparison s' s rS₀ rS₁ hS ≫ comparison c' s' q₀' q₁' hc' := by
  unfold comparison
  rw [← CochainComplex.mappingCone.map_comp,
      ← CochainComplex.mappingCone.map_comp]
  congr 1
  · rw [← dualMapInt_comp, h₁, dualMapInt_comp]
  · rw [← dualMapInt_comp, h₀, dualMapInt_comp]

@[reassoc]
public theorem comparison_connecting
    (c : C₀ ⟶ C₁) (s : S₀ ⟶ S₁)
    (q₀ : C₀ ⟶ S₀) (q₁ : C₁ ⟶ S₁)
    (h : c ≫ q₁ = q₀ ≫ s) :
    comparison c s q₀ q₁ h ≫
        (CochainComplex.mappingCone.triangle (dualMapInt c)).mor₃ =
      (CochainComplex.mappingCone.triangle (dualMapInt s)).mor₃ ≫
        (dualMapInt q₁)⟦(1 : ℤ)⟧' := by
  have hh := (CochainComplex.mappingCone.triangleMap
    (dualMapInt s) (dualMapInt c) (dualMapInt q₁) (dualMapInt q₀)
    (dualSquare c s q₀ q₁ h)).comm₃
  change (CochainComplex.mappingCone.triangle (dualMapInt s)).mor₃ ≫
      (dualMapInt q₁)⟦(1 : ℤ)⟧' =
    comparison c s q₀ q₁ h ≫
      (CochainComplex.mappingCone.triangle (dualMapInt c)).mor₃ at hh
  exact hh.symm

local instance relativeCechConeComparisonDerivedCategory :
    HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard (ModuleCat.{u} R)

set_option linter.style.haveILetI false in
/-- If both absolute augmentations are quasi-isomorphisms, so is the induced
relative comparison.  No condition on the horizontal maps is required beyond
the displayed strict naturality square. -/
public theorem comparison_quasiIso
    (c : C₀ ⟶ C₁) (s : S₀ ⟶ S₁)
    (q₀ : C₀ ⟶ S₀) (q₁ : C₁ ⟶ S₁)
    (h : c ≫ q₁ = q₀ ≫ s)
    [QuasiIso q₀] [QuasiIso q₁] :
    QuasiIso (comparison c s q₀ q₁ h) := by
  letI : QuasiIso (HomologicalComplex.linearDualMap q₀) :=
    HomologicalComplex.linearDualMap_quasiIso q₀
  letI : QuasiIso (HomologicalComplex.linearDualMap q₁) :=
    HomologicalComplex.linearDualMap_quasiIso q₁
  letI : QuasiIso (dualMapInt q₀) :=
    (HomologicalComplex.quasiIso_extendMap_iff
      (HomologicalComplex.linearDualMap q₀) ComplexShape.embeddingUpNat).mpr inferInstance
  letI : QuasiIso (dualMapInt q₁) :=
    (HomologicalComplex.quasiIso_extendMap_iff
      (HomologicalComplex.linearDualMap q₁) ComplexShape.embeddingUpNat).mpr inferInstance
  exact CochainComplex.mappingCone.map_quasiIso_of_vertical_quasiIso
    (dualMapInt s) (dualMapInt c) (dualMapInt q₁) (dualMapInt q₀)
      (dualSquare c s q₀ q₁ h)

end RelativeCechConeComparison

namespace Singular

variable {X Y : TopCat} {ι : Type} [LinearOrder ι]

/-- Pull an indexed family of subsets back along a continuous map.  For the
supported comparison, `f` is the inclusion of the open complement. -/
public def pullbackCover (f : Y ⟶ X) (U : ι → Set X) (i : ι) : Set Y :=
  f ⁻¹' U i

omit [LinearOrder ι] in
@[simp]
public lemma mem_pullbackCover (f : Y ⟶ X) (U : ι → Set X) (i : ι) (y : Y) :
    y ∈ pullbackCover f U i ↔ f y ∈ U i :=
  Iff.rfl

/-- A pulled-back finite intersection maps canonically to the corresponding
intersection in the target. -/
public def pullbackOpenCoverIntersectionMap (f : Y ⟶ X) (U : ι → Set X)
    (s : Finset ι) :
    TopCat.of (openCoverIntersection Y (pullbackCover f U) s) ⟶
      TopCat.of (openCoverIntersection X U s) :=
  TopCat.ofHom
    { toFun := fun y ↦ ⟨f y.1, by
        rw [mem_openCoverIntersection_iff]
        intro i hi
        exact (mem_openCoverIntersection_iff Y (pullbackCover f U) s y.1).mp
          y.2 i hi⟩
      continuous_toFun := by fun_prop }

omit [LinearOrder ι] in
@[reassoc]
public lemma pullbackOpenCoverIntersectionMap_naturality (f : Y ⟶ X)
    (U : ι → Set X) {s t : Finset ι} (hst : s ⊆ t) :
    openCoverIntersectionInclusion Y (pullbackCover f U) hst ≫
        pullbackOpenCoverIntersectionMap f U s =
      pullbackOpenCoverIntersectionMap f U t ≫
        openCoverIntersectionInclusion X U hst := by
  ext y
  rfl

/-- Rational local intersection chains are natural under pullback of the
cover.  This is the concrete local map used for the inclusion of an open
complement. -/
public def rationalPullbackCoverLocalMap (f : Y ⟶ X) (U : ι → Set X) :
    SupportChainModels.Hom
      (rationalOpenCoverIntersectionChainModels Y (pullbackCover f U))
      (rationalOpenCoverIntersectionChainModels X U) where
  app s := SSet.chainComplexMap
    (TopCat.toSSet.map (pullbackOpenCoverIntersectionMap f U s.unop.1))
    (ModuleCat.of ℚ ℚ)
  naturality s t g := by
    dsimp [rationalOpenCoverIntersectionChainModels]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg
      (fun h ↦ SSet.chainComplexMap (TopCat.toSSet.map h) (ModuleCat.of ℚ ℚ))
      (pullbackOpenCoverIntersectionMap_naturality f U (leOfHom g.unop))

@[simp]
public lemma rationalPullbackCoverLocalMap_app (f : Y ⟶ X)
    (U : ι → Set X) (s : (CoverSupport ι)ᵒᵖ) :
    (rationalPullbackCoverLocalMap f U).app s =
      SSet.chainComplexMap
        (TopCat.toSSet.map
          (pullbackOpenCoverIntersectionMap f U s.unop.1))
        (ModuleCat.of ℚ ℚ) :=
  rfl

/-- The map on normalized ordered Čech bicomplexes induced by a continuous
map and the pulled-back cover. -/
public def rationalPullbackCoverNormalizedBicomplexMap (f : Y ⟶ X)
    (U : ι → Set X) :
    (rationalOpenCoverIntersectionChainModels Y
        (pullbackCover f U)).cechComplex TupleClass.strictMono ⟶
      (rationalOpenCoverIntersectionChainModels X U).cechComplex
        TupleClass.strictMono :=
  (rationalPullbackCoverLocalMap f U).cechMap TupleClass.strictMono

/-- The corresponding covariant map of normalized rational Čech chain
totals. -/
public def rationalPullbackCoverNormalizedTotalMap (f : Y ⟶ X)
    (U : ι → Set X) :
    (rationalOpenCoverIntersectionChainModels Y
        (pullbackCover f U)).cechTotal TupleClass.strictMono ⟶
      (rationalOpenCoverIntersectionChainModels X U).cechTotal
        TupleClass.strictMono :=
  HomologicalComplex₂.total.map
    (rationalPullbackCoverNormalizedBicomplexMap f U)
    (ComplexShape.down ℕ)

omit [LinearOrder ι] in
/-- Pulling back an open cover along `f` again gives an open family. -/
public lemma isOpen_pullbackCover (f : Y ⟶ X) (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (i : ι) :
    IsOpen (pullbackCover f U i) :=
  (hU i).preimage f.hom.continuous

omit [LinearOrder ι] in
/-- A cover of the target pulls back to a cover of the source. -/
public lemma iUnion_pullbackCover (f : Y ⟶ X) (U : ι → Set X)
    (hU : ⋃ i, U i = Set.univ) :
    ⋃ i, pullbackCover f U i = Set.univ := by
  ext y
  simp only [Set.mem_iUnion, pullbackCover, Set.mem_preimage, Set.mem_univ, iff_true]
  have hy : f y ∈ ⋃ i, U i := by rw [hU]; trivial
  simpa only [Set.mem_iUnion] using hy

/-- The map from one member of a pulled-back cover to the corresponding
target cover member. -/
public def pullbackCoverMemberMap (f : Y ⟶ X) (U : ι → Set X) (i : ι) :
    TopCat.of (pullbackCover f U i) ⟶ TopCat.of (U i) :=
  TopCat.ofHom
    { toFun := fun y ↦ ⟨f y.1, y.2⟩
      continuous_toFun := by fun_prop }

omit [LinearOrder ι] in
@[reassoc]
public lemma pullbackCoverMemberMap_comp_inclusion (f : Y ⟶ X)
    (U : ι → Set X) (i : ι) :
    pullbackCoverMemberMap f U i ≫ topologicalSubsetInclusion X (U i) =
      topologicalSubsetInclusion Y (pullbackCover f U i) ≫ f := by
  ext y
  rfl

/-- A map carries simplices small for a pulled-back cover to simplices small
for the target cover. -/
public def pullbackCoverSmallSingularMap (f : Y ⟶ X) (U : ι → Set X) :
    (coverSmallSingularSubcomplex Y (pullbackCover f U) : SSet) ⟶
      (coverSmallSingularSubcomplex X U : SSet) := by
  refine SSet.Subcomplex.lift
    ((coverSmallSingularSubcomplex Y (pullbackCover f U)).ι ≫
      TopCat.toSSet.map f) ?_
  intro n z hz
  obtain ⟨a, rfl⟩ := hz
  have ha := a.2
  rw [mem_coverSmallSingularSubcomplex_iff] at ha ⊢
  obtain ⟨i, hi⟩ := ha
  refine ⟨i, ?_⟩
  change (TopCat.toSSet.map f).app n a.1 ∈
    Set.range ((TopCat.toSSet.map (topologicalSubsetInclusion X (U i))).app n)
  change a.1 ∈ Set.range
    ((TopCat.toSSet.map
      (topologicalSubsetInclusion Y (pullbackCover f U i))).app n) at hi
  obtain ⟨b, hb⟩ := hi
  refine ⟨(TopCat.toSSet.map (pullbackCoverMemberMap f U i)).app n b, ?_⟩
  rw [← hb]
  apply (X.toSSetObjEquiv n).injective
  ext t
  rfl

omit [LinearOrder ι] in
@[reassoc (attr := simp)]
public lemma pullbackCoverSmallSingularMap_comp_inclusion (f : Y ⟶ X)
    (U : ι → Set X) :
    pullbackCoverSmallSingularMap f U ≫
        (coverSmallSingularSubcomplex X U).ι =
      (coverSmallSingularSubcomplex Y (pullbackCover f U)).ι ≫
        TopCat.toSSet.map f :=
  SSet.Subcomplex.lift_ι _ _

omit [LinearOrder ι] in
@[reassoc]
public lemma pullbackCoverMemberToSmall_naturality (f : Y ⟶ X)
    (U : ι → Set X) (i : ι) :
    TopCat.toSSet.map (pullbackCoverMemberMap f U i) ≫
        coverMemberToSmallSingularSet X U i =
      coverMemberToSmallSingularSet Y (pullbackCover f U) i ≫
        pullbackCoverSmallSingularMap f U := by
  apply (cancel_mono (coverSmallSingularSubcomplex X U).ι).1
  rw [Category.assoc, Category.assoc,
    coverMemberToSmallSingularSet_comp_inclusion,
    pullbackCoverSmallSingularMap_comp_inclusion,
    coverMemberToSmallSingularSet_comp_inclusion_assoc,
    ← Functor.map_comp, ← Functor.map_comp,
    pullbackCoverMemberMap_comp_inclusion]

/-- The canonical morphism between the cover-small presentation arrows for
a pulled-back cover and the original cover. -/
public def pullbackCoverSmallPresentationMap (f : Y ⟶ X) (U : ι → Set X) :
    Arrow.mk (coverSmallPresentation Y (pullbackCover f U)) ⟶
      Arrow.mk (coverSmallPresentation X U) where
  left := Limits.Sigma.map fun i ↦
    TopCat.toSSet.map (pullbackCoverMemberMap f U i)
  right := pullbackCoverSmallSingularMap f U
  w := by
    simp only [Functor.id_obj, Functor.id_map]
    change Limits.Sigma.map (fun i ↦
        TopCat.toSSet.map (pullbackCoverMemberMap f U i)) ≫
          coverSmallPresentation X U =
      coverSmallPresentation Y (pullbackCover f U) ≫
        pullbackCoverSmallSingularMap f U
    apply Limits.Sigma.hom_ext
    intro i
    rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc,
      coverSmallPresentation_iota, ← Category.assoc,
      coverSmallPresentation_iota,
      pullbackCoverMemberToSmall_naturality]

@[simp]
public lemma pullbackCoverSmallPresentationMap_left (f : Y ⟶ X)
    (U : ι → Set X) :
    (pullbackCoverSmallPresentationMap f U).left =
      Limits.Sigma.map (fun i ↦
        TopCat.toSSet.map (pullbackCoverMemberMap f U i)) :=
  rfl

@[simp]
public lemma pullbackCoverSmallPresentationMap_right (f : Y ⟶ X)
    (U : ι → Set X) :
    (pullbackCoverSmallPresentationMap f U).right =
      pullbackCoverSmallSingularMap f U :=
  rfl

@[reassoc]
public lemma pullbackOpenCoverIntersectionMap_comp_tupleMember
    (f : Y ⟶ X) (U : ι → Set X) {n : SimplexCategoryᵒᵖ}
    (a : OpenCoverCechTuple (ι := ι) n)
    (i : Fin (n.unop.len + 1)) :
    pullbackOpenCoverIntersectionMap f U (tupleSupport a.1).1 ≫
        openCoverTupleIntersectionToMember X U a i =
      openCoverTupleIntersectionToMember Y (pullbackCover f U) a i ≫
        pullbackCoverMemberMap f U (a.1 i) := by
  ext z
  rfl

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordered-intersection map to the actual Čech nerve is natural under
pullback of a cover. -/
@[reassoc]
public lemma pullbackOpenCoverTupleIntersectionToCechSummand_naturality
    (f : Y ⟶ X) (U : ι → Set X) {n : SimplexCategoryᵒᵖ}
    (a : OpenCoverCechTuple (ι := ι) n) :
    TopCat.toSSet.map
        (pullbackOpenCoverIntersectionMap f U (tupleSupport a.1).1) ≫
      openCoverTupleIntersectionToCechSummand X U a =
    openCoverTupleIntersectionToCechSummand Y (pullbackCover f U) a ≫
      (Arrow.mapAugmentedCechNerve
        (pullbackCoverSmallPresentationMap f U)).left.app n := by
  apply WidePullback.hom_ext
  · intro i
    simp only [openCoverTupleIntersectionToCechSummand,
      Arrow.mapAugmentedCechNerve_left,
      Arrow.mapCechNerve_app, WidePullback.lift_π,
      WidePullback.lift_π_assoc, Category.assoc,
      pullbackCoverSmallPresentationMap_left]
    dsimp [openCoverTupleIntersectionToPresentationLeg,
      pullbackCoverSmallPresentationMap]
    rw [Category.assoc, Limits.Sigma.ι_map,
      ← Category.assoc, ← Category.assoc]
    simp only [← Functor.map_comp]
    rw [pullbackOpenCoverIntersectionMap_comp_tupleMember]
  · simp only [openCoverTupleIntersectionToCechSummand,
      Arrow.mapAugmentedCechNerve_left,
      Arrow.mapCechNerve_app, WidePullback.lift_base,
      WidePullback.lift_base_assoc, Category.assoc,
      pullbackCoverSmallPresentationMap_right]
    dsimp [openCoverTupleIntersectionToSmall,
      pullbackCoverSmallPresentationMap]
    rw [← Category.assoc, ← Functor.map_comp,
      pullbackOpenCoverIntersectionMap_comp_tupleMember,
      Functor.map_comp, Category.assoc,
      pullbackCoverMemberToSmall_naturality, ← Category.assoc]

/-- Rational chains on augmented Čech nerves are functorial in a morphism
of presentation arrows. -/
public def rationalCechAugmentedChainsMap {A B : Arrow SSet} (F : A ⟶ B) :
    rationalCechAugmentedChains A ⟶ rationalCechAugmentedChains B :=
  ((SimplicialObject.Augmented.whiskering SSet
      (ChainComplex (ModuleCat ℚ) ℕ)).obj
    ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ))).map
      (Arrow.mapAugmentedCechNerve F)

/-- The induced map of rational Čech bicomplexes. -/
public def rationalCechBicomplexMap {A B : Arrow SSet} (F : A ⟶ B) :
    rationalCechBicomplex A ⟶ rationalCechBicomplex B :=
  (alternatingFaceMapComplex (ChainComplex (ModuleCat ℚ) ℕ)).map
    (SimplicialObject.Augmented.drop.map
      (rationalCechAugmentedChainsMap F))

@[simp]
public lemma rationalCechBicomplexMap_f {A B : Arrow SSet} (F : A ⟶ B)
    (p : ℕ) :
    (rationalCechBicomplexMap F).f p =
      SSet.chainComplexMap
        ((Arrow.mapAugmentedCechNerve F).left.app
          (Opposite.op (SimplexCategory.mk p)))
        (ModuleCat.of ℚ ℚ) :=
  rfl

/-- Functoriality of the direct-sum total of the rational Čech
bicomplex. -/
public def rationalCechTotalMap {A B : Arrow SSet} (F : A ⟶ B) :
    (rationalCechBicomplex A).total (ComplexShape.down ℕ) ⟶
      (rationalCechBicomplex B).total (ComplexShape.down ℕ) :=
  HomologicalComplex₂.total.map (rationalCechBicomplexMap F)
    (ComplexShape.down ℕ)

/-- Rational chains preserve the tuple-level pullback-cover naturality
square. -/
@[reassoc]
public lemma rationalPullbackCoverTupleChainMap_naturality
    (f : Y ⟶ X) (U : ι → Set X) {n : SimplexCategoryᵒᵖ}
    (a : OpenCoverCechTuple (ι := ι) n) :
    SSet.chainComplexMap
        (TopCat.toSSet.map
          (pullbackOpenCoverIntersectionMap f U (tupleSupport a.1).1))
        (ModuleCat.of ℚ ℚ) ≫
      SSet.chainComplexMap
        (openCoverTupleIntersectionToCechSummand X U a)
        (ModuleCat.of ℚ ℚ) =
      SSet.chainComplexMap
        (openCoverTupleIntersectionToCechSummand Y (pullbackCover f U) a)
        (ModuleCat.of ℚ ℚ) ≫
      SSet.chainComplexMap
        ((Arrow.mapAugmentedCechNerve
          (pullbackCoverSmallPresentationMap f U)).left.app n)
        (ModuleCat.of ℚ ℚ) := by
  change ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map
        (TopCat.toSSet.map
          (pullbackOpenCoverIntersectionMap f U (tupleSupport a.1).1)) ≫
      ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).map
          (openCoverTupleIntersectionToCechSummand X U a) =
    ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map
        (openCoverTupleIntersectionToCechSummand Y (pullbackCover f U) a) ≫
      ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).map
          ((Arrow.mapAugmentedCechNerve
            (pullbackCoverSmallPresentationMap f U)).left.app n)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg
    (fun h ↦ SSet.chainComplexMap h (ModuleCat.of ℚ ℚ))
    (pullbackOpenCoverTupleIntersectionToCechSummand_naturality f U a)

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordered-intersection column identification is natural for a
pulled-back cover. -/
public lemma rationalOpenCoverOrderedCechColumnIso_naturality
    (f : Y ⟶ X) (U : ι → Set X) (p : ℕ) :
    (rationalPullbackCoverLocalMap f U).cechObjectMap TupleClass.all p ≫
        (rationalOpenCoverOrderedCechColumnIso X U p).hom =
      (rationalOpenCoverOrderedCechColumnIso Y (pullbackCover f U) p).hom ≫
        (rationalCechBicomplexMap
          (pullbackCoverSmallPresentationMap f U)).f p := by
  apply Limits.Sigma.hom_ext
  intro a
  dsimp only [SupportChainModels.Hom.cechObjectMap]
  rw [Limits.Sigma.ι_map_assoc,
    rationalOpenCoverOrderedCechColumnIso_model_hom_ι,
    ← Category.assoc,
    rationalOpenCoverOrderedCechColumnIso_model_hom_ι]
  rw [rationalPullbackCoverLocalMap_app, rationalCechBicomplexMap_f]
  exact rationalPullbackCoverTupleChainMap_naturality
    (n := Opposite.op (SimplexCategory.mk p)) f U a

/-- Naturality of the full ordered-intersection bicomplex identification. -/
@[reassoc]
public lemma rationalOpenCoverOrderedCechBicomplexIso_naturality
    (f : Y ⟶ X) (U : ι → Set X) :
    (rationalPullbackCoverLocalMap f U).cechMap TupleClass.all ≫
        (rationalOpenCoverOrderedCechBicomplexIso X U).hom =
      (rationalOpenCoverOrderedCechBicomplexIso Y
          (pullbackCover f U)).hom ≫
        rationalCechBicomplexMap (pullbackCoverSmallPresentationMap f U) := by
  apply HomologicalComplex.Hom.ext
  funext p
  exact rationalOpenCoverOrderedCechColumnIso_naturality f U p

/-- Naturality of the totalized ordered-intersection identification. -/
@[reassoc]
public lemma rationalOpenCoverOrderedCechTotalIso_naturality
    (f : Y ⟶ X) (U : ι → Set X) :
    HomologicalComplex₂.total.map
        ((rationalPullbackCoverLocalMap f U).cechMap TupleClass.all)
        (ComplexShape.down ℕ) ≫
      (rationalOpenCoverOrderedCechTotalIso X U).hom =
    (rationalOpenCoverOrderedCechTotalIso Y
        (pullbackCover f U)).hom ≫
      rationalCechTotalMap (pullbackCoverSmallPresentationMap f U) := by
  unfold rationalOpenCoverOrderedCechTotalIso rationalCechTotalMap
  change HomologicalComplex₂.total.map
        ((rationalPullbackCoverLocalMap f U).cechMap TupleClass.all)
        (ComplexShape.down ℕ) ≫
      HomologicalComplex₂.total.map
        (rationalOpenCoverOrderedCechBicomplexIso X U).hom
        (ComplexShape.down ℕ) =
    HomologicalComplex₂.total.map
        (rationalOpenCoverOrderedCechBicomplexIso Y
          (pullbackCover f U)).hom (ComplexShape.down ℕ) ≫
      HomologicalComplex₂.total.map
        (rationalCechBicomplexMap (pullbackCoverSmallPresentationMap f U))
        (ComplexShape.down ℕ)
  rw [← HomologicalComplex₂.total.map_comp,
    rationalOpenCoverOrderedCechBicomplexIso_naturality,
    HomologicalComplex₂.total.map_comp]

/-- The rational outer Čech augmentation is strictly natural in the
presentation arrow. -/
@[reassoc]
public lemma rationalCechOuterAugmentation_naturality {A B : Arrow SSet}
    (F : A ⟶ B) :
    rationalCechBicomplexMap F ≫ rationalCechOuterAugmentation B =
      rationalCechOuterAugmentation A ≫
        (ChainComplex.single₀ (ChainComplex (ModuleCat ℚ) ℕ)).map
          (SSet.chainComplexMap F.right (ModuleCat.of ℚ ℚ)) := by
  exact AlternatingFaceMapComplex.ε.naturality
    (rationalCechAugmentedChainsMap F)

/-- The totalized rational Čech augmentation is strictly natural in the
presentation arrow. -/
@[reassoc]
public lemma rationalCechTotalAugmentation_naturality {A B : Arrow SSet}
    (F : A ⟶ B) :
    rationalCechTotalMap F ≫ rationalCechTotalAugmentation B =
      rationalCechTotalAugmentation A ≫
        HomologicalComplex₂.total.map
          ((ChainComplex.single₀ (ChainComplex (ModuleCat ℚ) ℕ)).map
            (SSet.chainComplexMap F.right (ModuleCat.of ℚ ℚ)))
          (ComplexShape.down ℕ) := by
  unfold rationalCechTotalMap rationalCechTotalAugmentation
  rw [← HomologicalComplex₂.total.map_comp,
    rationalCechOuterAugmentation_naturality,
    HomologicalComplex₂.total.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical projection from a horizontal-degree-zero total is natural
in its unique nonzero chain complex. -/
@[reassoc]
public lemma firstQuadrantTotalToSingleZeroGeneric_naturality
    {K L : ChainComplex (ModuleCat ℚ) ℕ} (g : K ⟶ L) :
    HomologicalComplex₂.total.map
        ((ChainComplex.single₀ (ChainComplex (ModuleCat ℚ) ℕ)).map g)
        (ComplexShape.down ℕ) ≫
      firstQuadrantTotalToSingleZeroGeneric L =
    firstQuadrantTotalToSingleZeroGeneric K ≫ g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f]
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map]
  rcases p with _ | p
  · have hqn : q = n := by simpa using hpq
    subst q
    dsimp only [firstQuadrantTotalToSingleZeroGeneric]
    simp only [Category.assoc, HomologicalComplex₂.ι_totalDesc,
      HomologicalComplex₂.ι_totalDesc_assoc]
    simp [firstQuadrantSingleZeroTotalComponentGeneric,
      firstQuadrantSingleZeroColumnIsoGeneric]
  · have hz : IsZero
        (((firstQuadrantSingleZeroBicomplexGeneric K).X (p + 1)).X q) :=
      (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) q).map_isZero
        (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.down ℕ) 0 K (p + 1) (by lia))
    exact hz.eq_of_src _ _

/-- The rational Čech augmentation all the way to the target chain complex
is strictly natural in the presentation arrow. -/
@[reassoc]
public lemma rationalCechTotalAugmentationToTarget_naturality
    {A B : Arrow SSet} (F : A ⟶ B) :
    rationalCechTotalMap F ≫ rationalCechTotalAugmentationToTarget B =
      rationalCechTotalAugmentationToTarget A ≫
        SSet.chainComplexMap F.right (ModuleCat.of ℚ ℚ) := by
  unfold rationalCechTotalAugmentationToTarget
  rw [← Category.assoc, rationalCechTotalAugmentation_naturality,
    Category.assoc, firstQuadrantTotalToSingleZeroGeneric_naturality,
    ← Category.assoc]

/-- Rational chains on the small-subcomplex map commute with the inclusions
into all singular chains. -/
@[reassoc]
public lemma pullbackCoverSmallRationalChains_comp_inclusion
    (f : Y ⟶ X) (U : ι → Set X) :
    SSet.chainComplexMap (pullbackCoverSmallSingularMap f U)
        (ModuleCat.of ℚ ℚ) ≫
      coverSmallRationalSingularChainInclusion X U =
    coverSmallRationalSingularChainInclusion Y (pullbackCover f U) ≫
      SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) := by
  change ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (pullbackCoverSmallSingularMap f U) ≫
        ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
          (ModuleCat.of ℚ ℚ)).map
            (coverSmallSingularSubcomplex X U).ι =
    ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map
        (coverSmallSingularSubcomplex Y (pullbackCover f U)).ι ≫
      ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
        (ModuleCat.of ℚ ℚ)).map (TopCat.toSSet.map f)
  rw [← Functor.map_comp, ← Functor.map_comp,
    pullbackCoverSmallSingularMap_comp_inclusion]

/-- Naturality of the actual (unnormalized presentation-arrow) rational
Čech total augmentation for a pulled-back cover. -/
@[reassoc]
public lemma pullbackCoverActualCechToSingular_naturality
    (f : Y ⟶ X) (U : ι → Set X) :
    rationalCechTotalMap (pullbackCoverSmallPresentationMap f U) ≫
        rationalCechTotalAugmentationToTarget
          (Arrow.mk (coverSmallPresentation X U)) ≫
        coverSmallRationalSingularChainInclusion X U =
      rationalCechTotalAugmentationToTarget
          (Arrow.mk (coverSmallPresentation Y (pullbackCover f U))) ≫
        coverSmallRationalSingularChainInclusion Y (pullbackCover f U) ≫
        SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) := by
  rw [← Category.assoc,
    rationalCechTotalAugmentationToTarget_naturality]
  dsimp [pullbackCoverSmallPresentationMap]
  rw [Category.assoc, pullbackCoverSmallRationalChains_comp_inclusion,
    ← Category.assoc]

/-- The normalized ordered-intersection Čech augmentation to ordinary
rational singular chains is strictly natural for pullback covers.  This is
the chain square needed by `RelativeCechConeComparison.comparison`. -/
@[reassoc]
public lemma rationalPullbackCoverNormalizedCechToSingular_naturality
    (f : Y ⟶ X) (U : ι → Set X) :
    rationalPullbackCoverNormalizedTotalMap f U ≫
        rationalOpenCoverNormalizedCechTotalToSingular X U =
      rationalOpenCoverNormalizedCechTotalToSingular Y (pullbackCover f U) ≫
        SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) := by
  unfold rationalOpenCoverNormalizedCechTotalToSingular
    rationalOpenCoverNormalizedCechTotalAugmentation
    rationalPullbackCoverNormalizedTotalMap
    rationalPullbackCoverNormalizedBicomplexMap
  simp only [Category.assoc]
  rw [SupportChainModels.Hom.totalCechMap_comp_totalNormalizedInclusion_assoc,
    rationalOpenCoverOrderedCechTotalIso_naturality_assoc,
    pullbackCoverActualCechToSingular_naturality]

/-- The canonical comparison from the relative rational singular-cochain
cone of a continuous map to the relative normalized Čech-cochain cone for a
cover of its target and the pulled-back cover of its source. -/
public def rationalPullbackCoverRelativeComparison (f : Y ⟶ X)
    (U : ι → Set X) :
    RelativeCechConeComparison.relativeDualCone
        (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)) ⟶
      RelativeCechConeComparison.relativeDualCone
        (rationalPullbackCoverNormalizedTotalMap f U) :=
  RelativeCechConeComparison.comparison
    (rationalPullbackCoverNormalizedTotalMap f U)
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ))
    (rationalOpenCoverNormalizedCechTotalToSingular Y (pullbackCover f U))
    (rationalOpenCoverNormalizedCechTotalToSingular X U)
    (rationalPullbackCoverNormalizedCechToSingular_naturality f U)

set_option linter.style.haveILetI false in
/-- For an open cover of the target, the relative Čech-to-singular comparison
is a quasi-isomorphism.  Openness and the covering identity for the pulled-back
family are proved from the displayed hypotheses, rather than assumed. -/
public theorem rationalPullbackCoverRelativeComparison_quasiIso
    (f : Y ⟶ X) (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (rationalPullbackCoverRelativeComparison f U) := by
  letI : QuasiIso
      (rationalOpenCoverNormalizedCechTotalToSingular X U) :=
    rationalOpenCoverNormalizedCechTotalToSingular_quasiIso X U hUopen hUcover
  letI : QuasiIso
      (rationalOpenCoverNormalizedCechTotalToSingular Y (pullbackCover f U)) :=
    rationalOpenCoverNormalizedCechTotalToSingular_quasiIso Y (pullbackCover f U)
      (isOpen_pullbackCover f U hUopen) (iUnion_pullbackCover f U hUcover)
  exact RelativeCechConeComparison.comparison_quasiIso
    (rationalPullbackCoverNormalizedTotalMap f U)
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ))
    (rationalOpenCoverNormalizedCechTotalToSingular Y (pullbackCover f U))
    (rationalOpenCoverNormalizedCechTotalToSingular X U)
    (rationalPullbackCoverNormalizedCechToSingular_naturality f U)

/-- For a literal topological pair, the source of the pullback-cover
comparison is definitionally the repository's singular restriction cone.
Thus this specialization introduces no comparison isomorphism or model
identification as an extra hypothesis. -/
public def rationalTopPairCoverRelativeCochainConeComparison
    (P : TopPair) (U : ι → Set P.fst) :
    CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ P) ⟶
      RelativeCechConeComparison.relativeDualCone
        (rationalPullbackCoverNormalizedTotalMap P.hom U) :=
  rationalPullbackCoverRelativeComparison P.hom U

/-- The literal relative singular-cochain cone is quasi-isomorphic to the
relative normalized Čech-cochain cone for any displayed open cover of the
ambient member of the pair. -/
public theorem rationalTopPairCoverRelativeCochainConeComparison_quasiIso
    (P : TopPair) (U : ι → Set P.fst)
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (rationalTopPairCoverRelativeCochainConeComparison P U) :=
  rationalPullbackCoverRelativeComparison_quasiIso P.hom U hUopen hUcover

end Singular

end AlgebraicTopology
