/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
https://www.apache.org/licenses/LICENSE-2.0
-/
module

public import Other.AlgebraicTopology.SingularTriadExcision
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The singular Mayer--Vietoris sequence

For an arbitrary pair of subsets, singular chains give a short exact sequence

`0 → C(U ∩ V; ℚ) → C(U; ℚ) ⊞ C(V; ℚ) → C(U; ℚ) + C(V; ℚ) → 0`.

The first map has signs `(i, -j)` and the second map is addition. The overlap is identified
geometrically using the images of singular simplices, not by defining it to be a kernel.
For an open cover `X = U ∪ V`, the proved subdivision theorem identifies the last chain model
with ambient homology. We construct the connecting map and prove exactness at every term.

This supplies the ordinary singular Mayer--Vietoris primitive needed for local-to-global
orientation arguments. It does not yet prove the relative compact-support gluing theorem,
dimension vanishing for manifolds or singular complex varieties, or existence of a general
fundamental class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology.Singular

instance rationalSimplicialChains_preservesColimitsOfShape {J : Type} [Category J] :
    PreservesColimitsOfShape J ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)) := by
  let : PreservesColimitsOfShape J (sigmaConst.obj (ModuleCat.of ℚ ℚ)) :=
    (sigmaConstAdj (ModuleCat.of ℚ ℚ)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape J
    (((evaluation _ _).obj (Opposite.op (SimplexCategory.mk n))) ⋙
      sigmaConst.obj (ModuleCat.of ℚ ℚ))
  infer_instance

variable {K : SSet} (A B : K.Subcomplex)

/-- Singular chains of an intersection and union form a pushout square. -/
theorem subcomplexChainSquare_isPushout :
    IsPushout
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
        (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
        (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))
        (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B))
        (ModuleCat.of ℚ ℚ)) :=
  (SSet.Subcomplex.BicartSq.isPushout
    (show SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) from ⟨rfl, rfl⟩)).map
      ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ))

/-- The intersection-to-sum and sum-to-union singular-chain maps, with signs `(i,-j)`
and `(k,l)`. The union here is a union of simplicial subcomplexes. -/
def subcomplexMayerVietorisShortComplex : ShortComplex (ChainCategory ℚ) :=
  (subcomplexChainSquare_isPushout A B).shortComplex

set_option backward.isDefEq.respectTransparency false in
/-- The Mayer--Vietoris chain sequence is short exact without a geometric hypothesis. -/
theorem subcomplexMayerVietorisShortComplex_shortExact :
    (subcomplexMayerVietorisShortComplex A B).ShortExact where
  exact := (subcomplexChainSquare_isPushout A B).exact_shortComplex
  epi_g := (subcomplexChainSquare_isPushout A B).epi_shortComplex_g
  mono_f := by
    change Mono (biprod.lift _ _)
    have : Mono (SSet.chainComplexMap
        (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
        (ModuleCat.of ℚ ℚ)) := by
      dsimp [SSet.chainComplexMap, SSet.chainComplexFunctor]
      apply +allowSynthFailures Functor.map_mono
      apply +allowSynthFailures Functor.map_mono
      dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
      infer_instance
    exact mono_of_mono_fac (biprod.lift_fst _ _)

section Subsets

variable (X : TopCat) (U V : Set X)

/-- The simplicial subcomplex of singular simplices contained in a specified subset. -/
def subsetSingularSubcomplex : (TopCat.toSSet.obj X).Subcomplex :=
  SSet.Subcomplex.range (TopCat.toSSet.map (topologicalSubsetInclusion X U))

/-- A simplex belongs to the subcomplex of `U` precisely when its values belong to `U`. -/
theorem mem_subsetSingularSubcomplex_iff {n : SimplexCategoryᵒᵖ}
    (s : (TopCat.toSSet.obj X).obj n) :
    s ∈ (subsetSingularSubcomplex X U).obj n ↔
      ∀ t, X.toSSetObjEquiv n s t ∈ U := by
  constructor
  · rintro ⟨a, rfl⟩ t
    exact ((TopCat.of U).toSSetObjEquiv n a t).2
  · intro hs
    refine ⟨((TopCat.of U).toSSetObjEquiv n).symm
      ⟨fun t ↦ ⟨X.toSSetObjEquiv n s t, hs t⟩,
        (X.toSSetObjEquiv n s).continuous.subtype_mk _⟩, ?_⟩
    apply (X.toSSetObjEquiv n).injective
    ext t
    rfl

/-- Singular simplices preserve intersections of subsets, as an equality of subcomplexes. -/
theorem subsetSingularSubcomplex_inter :
    subsetSingularSubcomplex X (U ∩ V) =
      subsetSingularSubcomplex X U ⊓ subsetSingularSubcomplex X V := by
  ext n s
  change s ∈ (subsetSingularSubcomplex X (U ∩ V)).obj n ↔
    s ∈ (subsetSingularSubcomplex X U).obj n ∧
      s ∈ (subsetSingularSubcomplex X V).obj n
  simp only [mem_subsetSingularSubcomplex_iff, Set.mem_inter_iff, forall_and]

/-- The union of the two singular subcomplexes consists of the chains small for the cover. -/
theorem subsetSingularSubcomplex_sup :
    subsetSingularSubcomplex X U ⊔ subsetSingularSubcomplex X V =
      coverSmallSingularSubcomplex X (fun b : Bool ↦ if b then U else V) := by
  simp [coverSmallSingularSubcomplex, subsetSingularSubcomplex, iSup_bool_eq]

/-- Inclusion of a subspace is injective on singular simplices. -/
theorem subsetSingularMap_mono :
    Mono (TopCat.toSSet.map (topologicalSubsetInclusion X U)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [CategoryTheory.mono_iff_injective]
  intro a b hab
  apply ((TopCat.of U).toSSetObjEquiv n).injective
  ext t
  exact congrArg (fun s ↦ X.toSSetObjEquiv n s t) hab

set_option backward.isDefEq.respectTransparency false in
/-- The singular set of a subset is canonically its image subcomplex, without any choice of
homology generators. -/
def subsetSingularIso : TopCat.toSSet.obj (TopCat.of U) ≅ subsetSingularSubcomplex X U := by
  let f := TopCat.toSSet.map (topologicalSubsetInclusion X U)
  let : Mono f := subsetSingularMap_mono X U
  let : Mono (SSet.Subcomplex.toRange f) :=
    mono_of_mono_fac (SSet.Subcomplex.toRange_ι f)
  exact asIso (SSet.Subcomplex.toRange f)

/-- The two-open small singular set, before any openness assumptions. -/
abbrev TwoSubsetSmallSingularSet : SSet :=
  (subsetSingularSubcomplex X U ⊔ subsetSingularSubcomplex X V :
    (TopCat.toSSet.obj X).Subcomplex)

/-- Inclusion of the intersection into the first subset. -/
def subsetIntersectionToLeft : TopCat.of ↥(U ∩ V) ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1, x.2.1⟩, by fun_prop⟩

/-- Inclusion of the intersection into the second subset. -/
def subsetIntersectionToRight : TopCat.of ↥(U ∩ V) ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.1, x.2.2⟩, by fun_prop⟩

/-- Inclusion of the first subset's singular set into the small singular set. -/
def subsetLeftToSmallSingularSet :
    TopCat.toSSet.obj (TopCat.of U) ⟶ TwoSubsetSmallSingularSet X U V :=
  (subsetSingularIso X U).hom ≫ SSet.Subcomplex.homOfLE le_sup_left

/-- Inclusion of the second subset's singular set into the small singular set. -/
def subsetRightToSmallSingularSet :
    TopCat.toSSet.obj (TopCat.of V) ⟶ TwoSubsetSmallSingularSet X U V :=
  (subsetSingularIso X V).hom ≫ SSet.Subcomplex.homOfLE le_sup_right

set_option backward.isDefEq.respectTransparency false in
/-- Singular sets of an intersection and two cover members push out to the small singular set.
In particular the overlap, rather than an abstract kernel, is the relation object. -/
theorem subsetSmallSingularSquare_isPushout :
    IsPushout (TopCat.toSSet.map (subsetIntersectionToLeft X U V))
      (TopCat.toSSet.map (subsetIntersectionToRight X U V))
      (subsetLeftToSmallSingularSet X U V) (subsetRightToSmallSingularSet X U V) := by
  let A := subsetSingularSubcomplex X U
  let B := subsetSingularSubcomplex X V
  have h := SSet.Subcomplex.BicartSq.isPushout
    (show SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) from ⟨rfl, rfl⟩)
  apply h.of_iso'
    (subsetSingularIso X (U ∩ V) ≪≫
      SSet.Subcomplex.eqToIso (subsetSingularSubcomplex_inter X U V))
    (subsetSingularIso X U) (subsetSingularIso X V) (Iso.refl _)
  · ext n s
    rfl
  · ext n s
    rfl
  · simp [subsetLeftToSmallSingularSet]
  · simp [subsetRightToSmallSingularSet]

/-- The pushout of singular-chain complexes resolving two-subset small chains. -/
theorem subsetSmallChainSquare_isPushout :
    IsPushout
      (SSet.chainComplexMap (TopCat.toSSet.map (subsetIntersectionToLeft X U V))
        (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap (TopCat.toSSet.map (subsetIntersectionToRight X U V))
        (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap (subsetLeftToSmallSingularSet X U V) (ModuleCat.of ℚ ℚ))
      (SSet.chainComplexMap (subsetRightToSmallSingularSet X U V) (ModuleCat.of ℚ ℚ)) :=
  (subsetSmallSingularSquare_isPushout X U V).map
    ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ))

/-- The actual small-chain Mayer--Vietoris sequence
`C(U ∩ V) → C(U) ⊞ C(V) → C(U) + C(V)`, with maps `(i,-j)` and addition. -/
def singularMayerVietorisShortComplex : ShortComplex (ChainCategory ℚ) :=
  (subsetSmallChainSquare_isPushout X U V).shortComplex

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the singular Mayer--Vietoris chain sequence; no exactness hypothesis is used. -/
theorem singularMayerVietorisShortComplex_shortExact :
    (singularMayerVietorisShortComplex X U V).ShortExact where
  exact := (subsetSmallChainSquare_isPushout X U V).exact_shortComplex
  epi_g := (subsetSmallChainSquare_isPushout X U V).epi_shortComplex_g
  mono_f := by
    let f := TopCat.toSSet.map (subsetIntersectionToLeft X U V)
    have : Mono f := by
      rw [NatTrans.mono_iff_mono_app]
      intro n
      rw [CategoryTheory.mono_iff_injective]
      intro a b hab
      apply ((TopCat.of ↥(U ∩ V)).toSSetObjEquiv n).injective
      ext t
      exact congrArg (fun s ↦ ((TopCat.of U).toSSetObjEquiv n s t).1) hab
    have : Mono (SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)) := by
      dsimp [SSet.chainComplexMap, SSet.chainComplexFunctor]
      apply +allowSynthFailures Functor.map_mono
      apply +allowSynthFailures Functor.map_mono
      dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
      infer_instance
    exact mono_of_mono_fac (biprod.lift_fst _ _)

/-- Inclusion of the two-subset small-chain model into all ambient singular chains. -/
def twoSubsetSmallChainInclusion :
    (singularMayerVietorisShortComplex X U V).X₃ ⟶
      (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ) :=
  SSet.chainComplexMap
    (subsetSingularSubcomplex X U ⊔ subsetSingularSubcomplex X V).ι
    (ModuleCat.of ℚ ℚ)

set_option backward.isDefEq.respectTransparency false in
/-- The geometric small-chain theorem makes the final object of the Mayer--Vietoris chain
sequence compute ambient homology for every two-open cover. -/
theorem twoSubsetSmallChainInclusion_homology_isIso
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (twoSubsetSmallChainInclusion X U V) n) := by
  have hopen : ∀ b : Bool, IsOpen (if b then U else V) := fun b ↦ by
    cases b <;> assumption
  have hcover : ⋃ b : Bool, (if b then U else V) = Set.univ := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    rcases (hUV.symm ▸ Set.mem_univ x : x ∈ U ∪ V) with hx | hx
    · exact Set.mem_iUnion.mpr ⟨true, hx⟩
    · exact Set.mem_iUnion.mpr ⟨false, hx⟩
  change IsIso (HomologicalComplex.homologyMap
    (SSet.chainComplexMap
      (subsetSingularSubcomplex X U ⊔ subsetSingularSubcomplex X V).ι
        (ModuleCat.of ℚ ℚ)) n)
  rw [subsetSingularSubcomplex_sup]
  change IsIso (HomologicalComplex.homologyMap
    (coverSmallRationalSingularChainInclusion X (fun b : Bool ↦ if b then U else V)) n)
  rw [← coverSmallRationalSingularHomologyIso_of_openCover_hom X
    (fun b : Bool ↦ if b then U else V) hopen hcover n]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparison from two-open small homology to ambient homology. -/
def twoSubsetSmallHomologyIso
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    (singularMayerVietorisShortComplex X U V).X₃.homology n ≅ Homology ℚ X n := by
  let : IsIso (HomologicalComplex.homologyMap (twoSubsetSmallChainInclusion X U V) n) :=
    twoSubsetSmallChainInclusion_homology_isIso X U V hU hV hUV n
  exact asIso (HomologicalComplex.homologyMap (twoSubsetSmallChainInclusion X U V) n)

/-- The Mayer--Vietoris connecting map `Hₙ₊₁(X;ℚ) → Hₙ(U∩V;ℚ)`. It is constructed
from the short exact chain sequence and the proven open-cover comparison. -/
def singularMayerVietorisBoundary
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    Homology ℚ X (n + 1) ⟶ Homology ℚ (TopCat.of ↥(U ∩ V)) n :=
  (twoSubsetSmallHomologyIso X U V hU hV hUV (n + 1)).inv ≫
    (singularMayerVietorisShortComplex_shortExact X U V).δ (n + 1) n
      (ComplexShape.down_mk (n + 1) n (by omega))

/-- The sum of the two inclusion maps on chains, followed by ambient inclusion. -/
def singularMayerVietorisSumChainMap :
    (singularMayerVietorisShortComplex X U V).X₂ ⟶
      (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ) :=
  (singularMayerVietorisShortComplex X U V).g ≫ twoSubsetSmallChainInclusion X U V

set_option backward.isDefEq.respectTransparency false in
/-- The ambient map of the Mayer--Vietoris sequence is exactly the sum of the actual two
subset-inclusion chain maps. -/
theorem singularMayerVietorisSumChainMap_eq :
    singularMayerVietorisSumChainMap X U V =
      biprod.desc
        (SSet.chainComplexMap (TopCat.toSSet.map (topologicalSubsetInclusion X U))
          (ModuleCat.of ℚ ℚ))
        (SSet.chainComplexMap (TopCat.toSSet.map (topologicalSubsetInclusion X V))
          (ModuleCat.of ℚ ℚ)) := by
  apply biprod.hom_ext'
  · simp only [singularMayerVietorisSumChainMap, singularMayerVietorisShortComplex,
      CommSq.shortComplex_g, biprod.inl_desc_assoc, biprod.inl_desc]
    change ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map _ ≫
      ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map _ = _
    rw [← Functor.map_comp]
    rfl
  · simp only [singularMayerVietorisSumChainMap, singularMayerVietorisShortComplex,
      CommSq.shortComplex_g, biprod.inr_desc_assoc, biprod.inr_desc]
    change ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map _ ≫
      ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map _ = _
    rw [← Functor.map_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Consecutive overlap and sum maps in the Mayer--Vietoris sequence compose to zero. -/
theorem singularMayerVietoris_overlap_sum (n : ℕ) :
    HomologicalComplex.homologyMap (singularMayerVietorisShortComplex X U V).f n ≫
      HomologicalComplex.homologyMap (singularMayerVietorisSumChainMap X U V) n = 0 := by
  rw [← HomologicalComplex.homologyMap_comp, singularMayerVietorisSumChainMap,
    ← Category.assoc, (singularMayerVietorisShortComplex X U V).zero, zero_comp,
    HomologicalComplex.homologyMap_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at `Hₙ(C(U) ⊞ C(V))` in the singular Mayer--Vietoris sequence. This is canonically
`Hₙ(U) ⊞ Hₙ(V)` because homology preserves finite biproducts. -/
theorem singularMayerVietoris_exact_sum
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (singularMayerVietorisShortComplex X U V).f n)
      (HomologicalComplex.homologyMap (singularMayerVietorisSumChainMap X U V) n)
      (singularMayerVietoris_overlap_sum X U V n)).Exact := by
  let e := twoSubsetSmallHomologyIso X U V hU hV hUV n
  let S := (singularMayerVietorisShortComplex X U V).map
    (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n)
  have hS : S.Exact :=
    (singularMayerVietorisShortComplex_shortExact X U V).homology_exact₂ n
  refine (ShortComplex.exact_iff_of_iso ?_).mp hS
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp [S]) ?_
  change 𝟙 _ ≫ HomologicalComplex.homologyMap
      ((singularMayerVietorisShortComplex X U V).g ≫ twoSubsetSmallChainInclusion X U V) n =
    HomologicalComplex.homologyMap (singularMayerVietorisShortComplex X U V).g n ≫
      HomologicalComplex.homologyMap (twoSubsetSmallChainInclusion X U V) n
  simp [HomologicalComplex.homologyMap_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The ambient sum map followed by the constructed Mayer--Vietoris boundary is zero. -/
theorem singularMayerVietoris_sum_boundary
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    HomologicalComplex.homologyMap (singularMayerVietorisSumChainMap X U V) (n + 1) ≫
      singularMayerVietorisBoundary X U V hU hV hUV n = 0 := by
  let e := twoSubsetSmallHomologyIso X U V hU hV hUV (n + 1)
  rw [singularMayerVietorisSumChainMap, HomologicalComplex.homologyMap_comp]
  change (HomologicalComplex.homologyMap (singularMayerVietorisShortComplex X U V).g
      (n + 1) ≫ e.hom) ≫ (e.inv ≫ _) = 0
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (singularMayerVietorisShortComplex_shortExact X U V).comp_δ
    (n + 1) n (ComplexShape.down_mk (n + 1) n (by omega))

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at ambient homology: an ambient class has zero Mayer--Vietoris boundary exactly
when it is the sum of classes from the two open subsets. -/
theorem singularMayerVietoris_exact_ambient
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (singularMayerVietorisSumChainMap X U V) (n + 1))
      (singularMayerVietorisBoundary X U V hU hV hUV n)
      (singularMayerVietoris_sum_boundary X U V hU hV hUV n)).Exact := by
  let hS := singularMayerVietorisShortComplex_shortExact X U V
  let e := twoSubsetSmallHomologyIso X U V hU hV hUV (n + 1)
  have h := hS.homology_exact₃ (n + 1) n
    (ComplexShape.down_mk (n + 1) n (by omega))
  refine (ShortComplex.exact_iff_of_iso ?_).mp h
  refine ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) ?_ ?_
  · change 𝟙 _ ≫ HomologicalComplex.homologyMap
      ((singularMayerVietorisShortComplex X U V).g ≫ twoSubsetSmallChainInclusion X U V)
        (n + 1) = _
    simp [HomologicalComplex.homologyMap_comp, e, twoSubsetSmallHomologyIso]
  · change e.hom ≫ (e.inv ≫ _) = _ ≫ 𝟙 _
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The constructed Mayer--Vietoris boundary followed by the overlap inclusion map is zero. -/
theorem singularMayerVietoris_boundary_overlap
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    singularMayerVietorisBoundary X U V hU hV hUV n ≫
      HomologicalComplex.homologyMap (singularMayerVietorisShortComplex X U V).f n = 0 := by
  rw [singularMayerVietorisBoundary, Category.assoc,
    (singularMayerVietorisShortComplex_shortExact X U V).δ_comp, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at overlap homology in the singular Mayer--Vietoris sequence. -/
theorem singularMayerVietoris_exact_overlap
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (n : ℕ) :
    (ShortComplex.mk
      (singularMayerVietorisBoundary X U V hU hV hUV n)
      (HomologicalComplex.homologyMap (singularMayerVietorisShortComplex X U V).f n)
      (singularMayerVietoris_boundary_overlap X U V hU hV hUV n)).Exact := by
  let hS := singularMayerVietorisShortComplex_shortExact X U V
  let e := twoSubsetSmallHomologyIso X U V hU hV hUV (n + 1)
  have h := hS.homology_exact₁ (n + 1) n
    (ComplexShape.down_mk (n + 1) n (by omega))
  refine (ShortComplex.exact_iff_of_iso ?_).mp h
  refine ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) ?_ (by simp)
  change e.hom ≫ (e.inv ≫ _) = _ ≫ 𝟙 _
  simp

local instance homologyFunctor_preservesBinaryBiproducts (n : ℕ) :
    PreservesBinaryBiproducts
      (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- The homology of the chain biproduct is canonically the biproduct of the subset homologies. -/
def singularMayerVietorisHomologySumIso (n : ℕ) :
    (singularMayerVietorisShortComplex X U V).X₂.homology n ≅
      Homology ℚ (TopCat.of U) n ⊞ Homology ℚ (TopCat.of V) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapBiprod _ _

set_option backward.isDefEq.respectTransparency false in
/-- Under the canonical biproduct identification, the overlap map is the difference of the
two actual inclusion-induced homology maps. -/
theorem singularMayerVietoris_overlap_map_eq (n : ℕ) :
    HomologicalComplex.homologyMap (singularMayerVietorisShortComplex X U V).f n ≫
      (singularMayerVietorisHomologySumIso X U V n).hom =
        biprod.lift
          (HomologicalComplex.homologyMap
            (SSet.chainComplexMap (TopCat.toSSet.map (subsetIntersectionToLeft X U V))
              (ModuleCat.of ℚ ℚ)) n)
          (-HomologicalComplex.homologyMap
            (SSet.chainComplexMap (TopCat.toSSet.map (subsetIntersectionToRight X U V))
              (ModuleCat.of ℚ ℚ)) n) := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n
  change F.map (biprod.lift _ (-_)) ≫ (F.mapBiprod _ _).hom = _
  rw [biprod.map_lift_mapBiprod, F.map_neg]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Under the canonical biproduct identification, the ambient map is the sum of the actual
subset-inclusion maps on homology. -/
theorem singularMayerVietoris_sum_map_eq (n : ℕ) :
    (singularMayerVietorisHomologySumIso X U V n).inv ≫
      HomologicalComplex.homologyMap (singularMayerVietorisSumChainMap X U V) n =
        biprod.desc
          (HomologicalComplex.homologyMap
            (SSet.chainComplexMap (TopCat.toSSet.map (topologicalSubsetInclusion X U))
              (ModuleCat.of ℚ ℚ)) n)
          (HomologicalComplex.homologyMap
            (SSet.chainComplexMap (TopCat.toSSet.map (topologicalSubsetInclusion X V))
              (ModuleCat.of ℚ ℚ)) n) := by
  rw [singularMayerVietorisSumChainMap_eq]
  exact biprod.mapBiprod_inv_map_desc
    (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n) _ _ _ _

end Subsets

end AlgebraicTopology.Singular
