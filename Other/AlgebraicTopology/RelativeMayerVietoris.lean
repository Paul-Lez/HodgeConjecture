/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
https://www.apache.org/licenses/LICENSE-2.0
-/
module

public import Other.AlgebraicTopology.SingularMayerVietoris
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-!
# Relative Mayer--Vietoris and closed supports

For open subsets `U,V ⊆ X`, this file constructs the exact sequence

`… → Hₙ(X,U∩V) → Hₙ(X,U) ⊕ Hₙ(X,V) → Hₙ(X,U∪V) → Hₙ₋₁(X,U∩V) → …`.

The first map has signs `(restriction,-restriction)` and the second adds the two restrictions.
Their quotient-projection identities are proved, so neither map is supplied as arbitrary data.
The chain sequence comes from the snake lemma applied to the actual two-subset small-chain
sequence and the ambient split sequence. The final comparison uses the proved triad excision
theorem, rather than identifying the small quotient with the union quotient by definition.

For closed supports `K,L`, putting `U = Kᶜ`, `V = Lᶜ` yields the support sequence with
`K∪L` on the left and `K∩L` on the right. No compactness is needed for this exact sequence.
Compact-support orientation gluing still additionally needs dimension vanishing and local
normalization; none of those conclusions is claimed here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology.Singular

section Abelian

variable {C : Type*} [Category C] [Abelian C]
  {S T : ShortComplex C} (f : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact)

/-- The snake-lemma diagram formed using the actual kernel and cokernel of a map of exact
sequences. No connecting or exactness datum is supplied. -/
def shortExactMapSnakeInput : ShortComplex.SnakeInput C where
  L₀ := kernel f
  L₁ := S
  L₂ := T
  L₃ := cokernel f
  v₀₁ := kernel.ι f
  v₁₂ := f
  v₂₃ := cokernel.π f
  w₀₂ := kernel.condition f
  w₁₃ := cokernel.condition f
  h₀ := kernelIsKernel f
  h₃ := cokernelIsCokernel f
  L₁_exact := hS.exact
  epi_L₁_g := hS.epi_g
  L₂_exact := hT.exact
  mono_L₂_f := hT.mono_f

set_option backward.isDefEq.respectTransparency false in
include hS hT in
/-- Quotienting a map of short exact sequences whose third vertical map is mono gives a
short exact sequence of cokernels. This is the precise snake-lemma step in relative gluing. -/
theorem cokernel_shortExact_of_shortExact_of_mono_third [Mono f.τ₃] :
    (cokernel f).ShortExact := by
  let D := shortExactMapSnakeInput f hS hT
  have hzero : IsZero D.L₀.X₃ := by
    apply IsZero.of_mono_eq_zero D.v₀₁.τ₃
    apply (cancel_mono f.τ₃).mp
    rw [zero_comp]
    exact D.w₀₂_τ₃
  refine { exact := D.L₃_exact, mono_f := ?_, epi_g := ?_ }
  · exact (D.L₂'.exact_iff_mono (hzero.eq_of_src _ _)).mp D.L₂'_exact
  · let : Epi D.L₂.g := hT.epi_g
    exact D.epi_L₃_g

variable {P₁ P₂ Q₁ Q₂ : C} (a : P₁ ⟶ Q₁) (b : P₂ ⟶ Q₂)

/-- The componentwise quotient maps give a cokernel cofork for a binary biproduct map. -/
def cokernelBiprodMapCofork : CokernelCofork (biprod.map a b) :=
  CokernelCofork.ofπ (biprod.map (cokernel.π a) (cokernel.π b)) (by
    ext <;> simp)

set_option backward.isDefEq.respectTransparency false in
/-- Binary biproducts commute with cokernels, proved by the two quotient universal properties. -/
def cokernelBiprodMapCofork_isColimit : IsColimit (cokernelBiprodMapCofork a b) := by
  apply Cofork.IsColimit.mk _
    (fun s ↦ biprod.desc
      (cokernel.desc a (biprod.inl ≫ s.π) (by
        have h := biprod.inl ≫= s.condition
        simpa only [Category.assoc, biprod.inl_map_assoc, zero_comp, comp_zero] using h))
      (cokernel.desc b (biprod.inr ≫ s.π) (by
        have h := biprod.inr ≫= s.condition
        simpa only [Category.assoc, biprod.inr_map_assoc, zero_comp, comp_zero] using h)))
  · intro s
    apply biprod.hom_ext' <;> simp [cokernelBiprodMapCofork]
  · intro s m hm
    apply biprod.hom_ext'
    · apply (cancel_epi (cokernel.π a)).mp
      simpa [cokernelBiprodMapCofork] using biprod.inl ≫= hm
    · apply (cancel_epi (cokernel.π b)).mp
      simpa [cokernelBiprodMapCofork] using biprod.inr ≫= hm

/-- The canonical isomorphism `coker(a ⊞ b) ≅ coker(a) ⊞ coker(b)`. -/
def cokernelBiprodMapIso : cokernel (biprod.map a b) ≅ cokernel a ⊞ cokernel b :=
  (cokernelIsCokernel (biprod.map a b)).coconePointUniqueUpToIso
    (cokernelBiprodMapCofork_isColimit a b)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem cokernelBiprodMapIso_projection :
    cokernel.π (biprod.map a b) ≫ (cokernelBiprodMapIso a b).hom =
      biprod.map (cokernel.π a) (cokernel.π b) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel (biprod.map a b))
    (cokernelBiprodMapCofork_isColimit a b) WalkingParallelPair.one

end Abelian

section Subsets

variable (X : TopCat) (U V : Set X)

/-- The split ambient sequence with maps `(id,-id)` and addition. -/
def ambientDiagonalShortComplex : ShortComplex (ChainCategory ℚ) :=
  (IsPushout.of_id_fst
    (f := 𝟙 ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)))).shortComplex

set_option backward.isDefEq.respectTransparency false in
/-- The ambient diagonal sequence is short exact by its identity-map pushout. -/
theorem ambientDiagonalShortComplex_shortExact :
    (ambientDiagonalShortComplex X).ShortExact where
  exact := (IsPushout.of_id_fst
    (f := 𝟙 ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)))).exact_shortComplex
  epi_g := (IsPushout.of_id_fst
    (f := 𝟙 ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)))).epi_shortComplex_g
  mono_f := by
    constructor
    intro Z f g h
    have hh := congrArg (fun k ↦ k ≫ biprod.fst) h
    simp only [ambientDiagonalShortComplex, CommSq.shortComplex_f, Category.assoc,
      biprod.lift_fst] at hh
    change f ≫ 𝟙 _ = g ≫ 𝟙 _ at hh
    simpa only [Category.comp_id] using hh

/-- The ambient singular-chain inclusion of a subset. -/
abbrev subsetAmbientChainMap (A : Set X) :
    (TopCat.toSSet.obj (TopCat.of A)).chainComplex (ModuleCat.of ℚ ℚ) ⟶
      (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ) :=
  SSet.chainComplexMap (TopCat.toSSet.map (topologicalSubsetInclusion X A))
    (ModuleCat.of ℚ ℚ)

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion of the intersection through the first member agrees with direct inclusion. -/
theorem subsetIntersectionChainMap_left_comp :
    SSet.chainComplexMap (TopCat.toSSet.map (subsetIntersectionToLeft X U V))
        (ModuleCat.of ℚ ℚ) ≫ subsetAmbientChainMap X U =
      subsetAmbientChainMap X (U ∩ V) := by
  let F := TopCat.toSSet ⋙
    (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  change F.map _ ≫ F.map _ = F.map _
  rw [← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion of the intersection through the second member agrees with direct inclusion. -/
theorem subsetIntersectionChainMap_right_comp :
    SSet.chainComplexMap (TopCat.toSSet.map (subsetIntersectionToRight X U V))
        (ModuleCat.of ℚ ℚ) ≫ subsetAmbientChainMap X V =
      subsetAmbientChainMap X (U ∩ V) := by
  let F := TopCat.toSSet ⋙
    (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  change F.map _ ≫ F.map _ = F.map _
  rw [← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The geometric morphism from the two-subset small-chain exact sequence to the ambient
diagonal exact sequence. Its three components are actual inclusion chain maps. -/
def subsetMayerVietorisToAmbient :
    singularMayerVietorisShortComplex X U V ⟶ ambientDiagonalShortComplex X :=
  ShortComplex.homMk
    (subsetAmbientChainMap X (U ∩ V))
    (biprod.map (subsetAmbientChainMap X U) (subsetAmbientChainMap X V))
    (twoSubsetSmallChainInclusion X U V)
    (by
      apply biprod.hom_ext
      · simp only [Category.assoc, ambientDiagonalShortComplex, CommSq.shortComplex_f,
          biprod.lift_fst, singularMayerVietorisShortComplex,
          biprod.map_fst, biprod.lift_fst_assoc]
        exact (subsetIntersectionChainMap_left_comp X U V).symm
      · simp only [Category.assoc, ambientDiagonalShortComplex, CommSq.shortComplex_f,
          biprod.lift_snd, Preadditive.comp_neg,
          singularMayerVietorisShortComplex, biprod.map_snd, biprod.lift_snd_assoc,
          Preadditive.neg_comp]
        exact congrArg Neg.neg (subsetIntersectionChainMap_right_comp X U V).symm)
    (by
      change biprod.map (subsetAmbientChainMap X U) (subsetAmbientChainMap X V) ≫
          biprod.desc (𝟙 _) (𝟙 _) =
        singularMayerVietorisSumChainMap X U V
      rw [singularMayerVietorisSumChainMap_eq]
      apply biprod.hom_ext' <;> simp)

set_option backward.isDefEq.respectTransparency false in
/-- Small-chain inclusion, the last vertical map of the quotient diagram, is a monomorphism
without openness assumptions. -/
theorem subsetMayerVietorisToAmbient_mono_third :
    Mono (subsetMayerVietorisToAmbient X U V).τ₃ := by
  change Mono (SSet.chainComplexMap
    (subsetSingularSubcomplex X U ⊔ subsetSingularSubcomplex X V).ι
      (ModuleCat.of ℚ ℚ))
  dsimp [SSet.chainComplexMap, SSet.chainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono
  apply +allowSynthFailures Functor.map_mono
  dsimp [SSet, SimplicialObject.whiskering, SimplicialObject]
  infer_instance

/-- The quotient Mayer--Vietoris chain sequence, constructed as the componentwise cokernel
of the actual subset-inclusion diagram. -/
def relativeMayerVietorisSmallShortComplex : ShortComplex (ChainCategory ℚ) :=
  cokernel (subsetMayerVietorisToAmbient X U V)

set_option backward.isDefEq.respectTransparency false in
/-- The quotient sequence of relative chain models is short exact, by the snake lemma. -/
theorem relativeMayerVietorisSmallShortComplex_shortExact :
    (relativeMayerVietorisSmallShortComplex X U V).ShortExact := by
  let : Mono (subsetMayerVietorisToAmbient X U V).τ₃ :=
    subsetMayerVietorisToAmbient_mono_third X U V
  exact cokernel_shortExact_of_shortExact_of_mono_third
    (subsetMayerVietorisToAmbient X U V)
    (singularMayerVietorisShortComplex_shortExact X U V)
    (ambientDiagonalShortComplex_shortExact X)

set_option backward.isDefEq.respectTransparency false in
/-- The left quotient chain model is exactly relative chains modulo the intersection. -/
def relativeMayerVietorisSmallLeftIso :
    (relativeMayerVietorisSmallShortComplex X U V).X₁ ≅
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset (U ∩ V)) :=
  PreservesCokernel.iso ShortComplex.π₁ (subsetMayerVietorisToAmbient X U V)

set_option backward.isDefEq.respectTransparency false in
/-- The middle quotient chain model is the biproduct of the two ordinary relative complexes. -/
def relativeMayerVietorisSmallMiddleIso :
    (relativeMayerVietorisSmallShortComplex X U V).X₂ ≅
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset U) ⊞
        (relativeChainFunctor ℚ).obj (TopPair.ofSubset V) :=
  PreservesCokernel.iso ShortComplex.π₂ (subsetMayerVietorisToAmbient X U V) ≪≫
    cokernelBiprodMapIso (subsetAmbientChainMap X U) (subsetAmbientChainMap X V)

set_option backward.isDefEq.respectTransparency false in
/-- The final quotient chain model is the established sum-relative triad complex. -/
def relativeMayerVietorisSmallRightIso :
    (relativeMayerVietorisSmallShortComplex X U V).X₃ ≅
      triadRelativeChainComplex ℚ X U V := by
  let : Epi (singularMayerVietorisShortComplex X U V).g :=
    (singularMayerVietorisShortComplex_shortExact X U V).epi_g
  refine PreservesCokernel.iso ShortComplex.π₃ (subsetMayerVietorisToAmbient X U V) ≪≫
    (cokernelEpiComp (singularMayerVietorisShortComplex X U V).g
      (twoSubsetSmallChainInclusion X U V)).symm ≪≫ ?_
  exact cokernelIsoOfEq (singularMayerVietorisSumChainMap_eq X U V)

set_option backward.isDefEq.respectTransparency false in
/-- The left endpoint comparison carries the componentwise cokernel projection to the actual
relative-chain projection. -/
@[reassoc]
theorem relativeMayerVietorisSmallLeftIso_projection :
    (cokernel.π (subsetMayerVietorisToAmbient X U V)).τ₁ ≫
      (relativeMayerVietorisSmallLeftIso X U V).hom =
        relativeChainProjection ℚ (TopPair.ofSubset (U ∩ V)) :=
  PreservesCokernel.π_iso_hom ShortComplex.π₁ (subsetMayerVietorisToAmbient X U V)

set_option backward.isDefEq.respectTransparency false in
/-- The middle comparison respects both actual quotient projections. -/
@[reassoc]
theorem relativeMayerVietorisSmallMiddleIso_projection :
    (cokernel.π (subsetMayerVietorisToAmbient X U V)).τ₂ ≫
      (relativeMayerVietorisSmallMiddleIso X U V).hom =
        biprod.map (relativeChainProjection ℚ (TopPair.ofSubset U))
          (relativeChainProjection ℚ (TopPair.ofSubset V)) := by
  change ShortComplex.π₂.map (cokernel.π (subsetMayerVietorisToAmbient X U V)) ≫
    (PreservesCokernel.iso ShortComplex.π₂ (subsetMayerVietorisToAmbient X U V)).hom ≫
      (cokernelBiprodMapIso (subsetAmbientChainMap X U) (subsetAmbientChainMap X V)).hom = _
  erw [PreservesCokernel.π_iso_hom_assoc, cokernelBiprodMapIso_projection]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The final comparison carries the quotient projection to the actual triad projection. -/
@[reassoc]
theorem relativeMayerVietorisSmallRightIso_projection :
    (cokernel.π (subsetMayerVietorisToAmbient X U V)).τ₃ ≫
      (relativeMayerVietorisSmallRightIso X U V).hom =
        triadRelativeChainProjection ℚ X U V := by
  dsimp only [relativeMayerVietorisSmallRightIso, Iso.trans_hom, Iso.symm_hom]
  have h : (cokernel.π (subsetMayerVietorisToAmbient X U V)).τ₃ ≫
      (PreservesCokernel.iso ShortComplex.π₃ (subsetMayerVietorisToAmbient X U V)).hom =
        cokernel.π (twoSubsetSmallChainInclusion X U V) :=
    PreservesCokernel.π_iso_hom ShortComplex.π₃ (subsetMayerVietorisToAmbient X U V)
  rw [← Category.assoc, ← Category.assoc]
  erw [h]
  simp [cokernelEpiComp, triadRelativeChainProjection]

/-- The first relative Mayer--Vietoris map, with signs `(restriction,-restriction)`. -/
def relativeMayerVietorisLeftChainMap :
    (relativeChainFunctor ℚ).obj (TopPair.ofSubset (U ∩ V)) ⟶
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset U) ⊞
        (relativeChainFunctor ℚ).obj (TopPair.ofSubset V) :=
  (relativeMayerVietorisSmallLeftIso X U V).inv ≫
    (relativeMayerVietorisSmallShortComplex X U V).f ≫
      (relativeMayerVietorisSmallMiddleIso X U V).hom

/-- The second relative Mayer--Vietoris map, adding the two restrictions to the union pair. -/
def relativeMayerVietorisRightChainMap :
    ((relativeChainFunctor ℚ).obj (TopPair.ofSubset U) ⊞
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset V)) ⟶
        (relativeChainFunctor ℚ).obj (TopPair.ofSubset (U ∪ V)) :=
  (relativeMayerVietorisSmallMiddleIso X U V).inv ≫
    (relativeMayerVietorisSmallShortComplex X U V).g ≫
      (relativeMayerVietorisSmallRightIso X U V).hom ≫
        triadToUnionRelativeChainMap ℚ X U V

set_option backward.isDefEq.respectTransparency false in
/-- The first map is induced by the signed diagonal on ambient chains. This identifies it as
the actual pair of support restrictions, not a separately supplied homomorphism. -/
theorem relativeMayerVietorisLeftChainMap_projection :
    relativeChainProjection ℚ (TopPair.ofSubset (U ∩ V)) ≫
      relativeMayerVietorisLeftChainMap X U V =
        biprod.lift (relativeChainProjection ℚ (TopPair.ofSubset U))
          (-relativeChainProjection ℚ (TopPair.ofSubset V)) := by
  rw [← relativeMayerVietorisSmallLeftIso_projection X U V,
    relativeMayerVietorisLeftChainMap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  erw [(cokernel.π (subsetMayerVietorisToAmbient X U V)).comm₁₂_assoc,
    relativeMayerVietorisSmallMiddleIso_projection]
  change biprod.lift (𝟙 _) (-𝟙 _) ≫ biprod.map _ _ = _
  apply biprod.hom_ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- The second map is induced by addition of ambient chains followed by the union quotient.
This identifies its two components as actual relative restriction maps. -/
theorem relativeMayerVietorisRightChainMap_projection :
    biprod.map (relativeChainProjection ℚ (TopPair.ofSubset U))
        (relativeChainProjection ℚ (TopPair.ofSubset V)) ≫
      relativeMayerVietorisRightChainMap X U V =
        biprod.desc (relativeChainProjection ℚ (TopPair.ofSubset (U ∪ V)))
          (relativeChainProjection ℚ (TopPair.ofSubset (U ∪ V))) := by
  rw [← relativeMayerVietorisSmallMiddleIso_projection X U V,
    relativeMayerVietorisRightChainMap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  erw [(cokernel.π (subsetMayerVietorisToAmbient X U V)).comm₂₃_assoc,
    relativeMayerVietorisSmallRightIso_projection_assoc,
    triadRelativeChainProjection_triadToUnionRelativeChainMap]
  change biprod.desc (𝟙 _) (𝟙 _) ≫ _ = _
  apply biprod.hom_ext' <;> simp

/-- The final quotient-chain model maps canonically to chains relative to the union. -/
def relativeMayerVietorisRightComparison :
    (relativeMayerVietorisSmallShortComplex X U V).X₃ ⟶
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset (U ∪ V)) :=
  (relativeMayerVietorisSmallRightIso X U V).hom ≫ triadToUnionRelativeChainMap ℚ X U V

set_option backward.isDefEq.respectTransparency false in
/-- Excision proves the comparison with the union relative complex is a quasi-isomorphism
for open subsets, with no comparison hypothesis supplied. -/
theorem relativeMayerVietorisRightComparison_quasiIso (hU : IsOpen U) (hV : IsOpen V) :
    QuasiIso (relativeMayerVietorisRightComparison X U V) := by
  let : QuasiIso (triadToUnionRelativeChainMap ℚ X U V) :=
    triadToUnionRelativeChainMap_quasiIso_of_isOpen X U V hU hV
  change QuasiIso ((relativeMayerVietorisSmallRightIso X U V).hom ≫ _)
  infer_instance

/-- The left endpoint homology comparison. -/
def relativeMayerVietorisLeftHomologyIso (n : ℕ) :
    (relativeMayerVietorisSmallShortComplex X U V).X₁.homology n ≅
      RelativeHomology ℚ (TopPair.ofSubset (U ∩ V)) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapIso
    (relativeMayerVietorisSmallLeftIso X U V)

/-- The middle endpoint homology comparison, before decomposing the chain biproduct. -/
def relativeMayerVietorisMiddleHomologyIso (n : ℕ) :
    (relativeMayerVietorisSmallShortComplex X U V).X₂.homology n ≅
      ((relativeChainFunctor ℚ).obj (TopPair.ofSubset U) ⊞
        (relativeChainFunctor ℚ).obj (TopPair.ofSubset V)).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).mapIso
    (relativeMayerVietorisSmallMiddleIso X U V)

set_option backward.isDefEq.respectTransparency false in
/-- The final endpoint homology comparison, constructed using the proved excision map. -/
def relativeMayerVietorisRightHomologyIso (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    (relativeMayerVietorisSmallShortComplex X U V).X₃.homology n ≅
      RelativeHomology ℚ (TopPair.ofSubset (U ∪ V)) n := by
  let : QuasiIso (relativeMayerVietorisRightComparison X U V) :=
    relativeMayerVietorisRightComparison_quasiIso X U V hU hV
  exact asIso (HomologicalComplex.homologyMap (relativeMayerVietorisRightComparison X U V) n)

/-- The relative Mayer--Vietoris connecting map, constructed from the quotient exact sequence
and the canonical excision comparison. -/
def relativeMayerVietorisBoundary (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    RelativeHomology ℚ (TopPair.ofSubset (U ∪ V)) (n + 1) ⟶
      RelativeHomology ℚ (TopPair.ofSubset (U ∩ V)) n :=
  (relativeMayerVietorisRightHomologyIso X U V hU hV (n + 1)).inv ≫
    (relativeMayerVietorisSmallShortComplex_shortExact X U V).δ (n + 1) n
      (ComplexShape.down_mk (n + 1) n (by omega)) ≫
        (relativeMayerVietorisLeftHomologyIso X U V n).hom

set_option backward.isDefEq.respectTransparency false in
/-- The first actual homology map is the transported map of the quotient sequence. -/
theorem relativeMayerVietorisLeftHomologyMap_eq (n : ℕ) :
    HomologicalComplex.homologyMap (relativeMayerVietorisLeftChainMap X U V) n =
      (relativeMayerVietorisLeftHomologyIso X U V n).inv ≫
        HomologicalComplex.homologyMap (relativeMayerVietorisSmallShortComplex X U V).f n ≫
          (relativeMayerVietorisMiddleHomologyIso X U V n).hom := by
  simp only [relativeMayerVietorisLeftChainMap, HomologicalComplex.homologyMap_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The second actual homology map is the transported map of the quotient sequence. -/
theorem relativeMayerVietorisRightHomologyMap_eq
    (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeMayerVietorisRightChainMap X U V) n =
      (relativeMayerVietorisMiddleHomologyIso X U V n).inv ≫
        HomologicalComplex.homologyMap (relativeMayerVietorisSmallShortComplex X U V).g n ≫
          (relativeMayerVietorisRightHomologyIso X U V hU hV n).hom := by
  simp only [relativeMayerVietorisRightChainMap, HomologicalComplex.homologyMap_comp,
    relativeMayerVietorisRightHomologyIso, relativeMayerVietorisRightComparison]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of the left map with the endpoint homology comparisons. -/
theorem relativeMayerVietorisLeftHomologyIso_comm (n : ℕ) :
    (relativeMayerVietorisLeftHomologyIso X U V n).hom ≫
        HomologicalComplex.homologyMap (relativeMayerVietorisLeftChainMap X U V) n =
      HomologicalComplex.homologyMap (relativeMayerVietorisSmallShortComplex X U V).f n ≫
        (relativeMayerVietorisMiddleHomologyIso X U V n).hom := by
  rw [relativeMayerVietorisLeftHomologyMap_eq, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of the right map with the endpoint homology comparisons. -/
theorem relativeMayerVietorisRightHomologyIso_comm
    (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    (relativeMayerVietorisMiddleHomologyIso X U V n).hom ≫
        HomologicalComplex.homologyMap (relativeMayerVietorisRightChainMap X U V) n =
      HomologicalComplex.homologyMap (relativeMayerVietorisSmallShortComplex X U V).g n ≫
        (relativeMayerVietorisRightHomologyIso X U V hU hV n).hom := by
  rw [relativeMayerVietorisRightHomologyMap_eq X U V hU hV, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of the connecting map with the endpoint homology comparisons. -/
theorem relativeMayerVietorisBoundary_comm
    (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    (relativeMayerVietorisRightHomologyIso X U V hU hV (n + 1)).hom ≫
        relativeMayerVietorisBoundary X U V hU hV n =
      (relativeMayerVietorisSmallShortComplex_shortExact X U V).δ (n + 1) n
          (ComplexShape.down_mk (n + 1) n (by omega)) ≫
        (relativeMayerVietorisLeftHomologyIso X U V n).hom := by
  rw [relativeMayerVietorisBoundary, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Consecutive actual relative chain maps compose to zero. -/
theorem relativeMayerVietorisLeftRight_comp :
    relativeMayerVietorisLeftChainMap X U V ≫ relativeMayerVietorisRightChainMap X U V = 0 := by
  simp only [relativeMayerVietorisLeftChainMap, relativeMayerVietorisRightChainMap,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (relativeMayerVietorisSmallShortComplex X U V).f,
    (relativeMayerVietorisSmallShortComplex X U V).zero, zero_comp, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at the direct sum of the relative homology groups. -/
theorem relativeMayerVietoris_exact_middle (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (relativeMayerVietorisLeftChainMap X U V) n)
      (HomologicalComplex.homologyMap (relativeMayerVietorisRightChainMap X U V) n)
      (by rw [← HomologicalComplex.homologyMap_comp, relativeMayerVietorisLeftRight_comp,
        HomologicalComplex.homologyMap_zero])).Exact := by
  have h := (relativeMayerVietorisSmallShortComplex_shortExact X U V).homology_exact₂ n
  refine (ShortComplex.exact_iff_of_iso ?_).mp h
  refine ShortComplex.isoMk (relativeMayerVietorisLeftHomologyIso X U V n)
    (relativeMayerVietorisMiddleHomologyIso X U V n)
    (relativeMayerVietorisRightHomologyIso X U V hU hV n) ?_ ?_
  · exact relativeMayerVietorisLeftHomologyIso_comm X U V n
  · exact relativeMayerVietorisRightHomologyIso_comm X U V hU hV n

set_option backward.isDefEq.respectTransparency false in
/-- The relative right map followed by the connecting map is zero. -/
theorem relativeMayerVietoris_right_boundary (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeMayerVietorisRightChainMap X U V) (n + 1) ≫
      relativeMayerVietorisBoundary X U V hU hV n = 0 := by
  rw [relativeMayerVietorisRightHomologyMap_eq X U V hU hV, relativeMayerVietorisBoundary]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (HomologicalComplex.homologyMap
    (relativeMayerVietorisSmallShortComplex X U V).g (n + 1)),
    (relativeMayerVietorisSmallShortComplex_shortExact X U V).comp_δ,
    zero_comp, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at relative homology modulo the union. -/
theorem relativeMayerVietoris_exact_union (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (relativeMayerVietorisRightChainMap X U V) (n + 1))
      (relativeMayerVietorisBoundary X U V hU hV n)
      (relativeMayerVietoris_right_boundary X U V hU hV n)).Exact := by
  have h := (relativeMayerVietorisSmallShortComplex_shortExact X U V).homology_exact₃
    (n + 1) n (ComplexShape.down_mk (n + 1) n (by omega))
  refine (ShortComplex.exact_iff_of_iso ?_).mp h
  refine ShortComplex.isoMk (relativeMayerVietorisMiddleHomologyIso X U V (n + 1))
    (relativeMayerVietorisRightHomologyIso X U V hU hV (n + 1))
    (relativeMayerVietorisLeftHomologyIso X U V n) ?_ ?_
  · exact relativeMayerVietorisRightHomologyIso_comm X U V hU hV (n + 1)
  · exact relativeMayerVietorisBoundary_comm X U V hU hV n

set_option backward.isDefEq.respectTransparency false in
/-- The connecting map followed by the left relative map is zero. -/
theorem relativeMayerVietoris_boundary_left (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    relativeMayerVietorisBoundary X U V hU hV n ≫
      HomologicalComplex.homologyMap (relativeMayerVietorisLeftChainMap X U V) n = 0 := by
  rw [relativeMayerVietorisLeftHomologyMap_eq, relativeMayerVietorisBoundary]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc ((relativeMayerVietorisSmallShortComplex_shortExact X U V).δ
      (n + 1) n (ComplexShape.down_mk (n + 1) n (by omega))),
    (relativeMayerVietorisSmallShortComplex_shortExact X U V).δ_comp,
    zero_comp, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at relative homology modulo the intersection. -/
theorem relativeMayerVietoris_exact_intersection (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    (ShortComplex.mk
      (relativeMayerVietorisBoundary X U V hU hV n)
      (HomologicalComplex.homologyMap (relativeMayerVietorisLeftChainMap X U V) n)
      (relativeMayerVietoris_boundary_left X U V hU hV n)).Exact := by
  have h := (relativeMayerVietorisSmallShortComplex_shortExact X U V).homology_exact₁
    (n + 1) n (ComplexShape.down_mk (n + 1) n (by omega))
  refine (ShortComplex.exact_iff_of_iso ?_).mp h
  refine ShortComplex.isoMk (relativeMayerVietorisRightHomologyIso X U V hU hV (n + 1))
    (relativeMayerVietorisLeftHomologyIso X U V n)
    (relativeMayerVietorisMiddleHomologyIso X U V n) ?_ ?_
  · exact relativeMayerVietorisBoundary_comm X U V hU hV n
  · exact relativeMayerVietorisLeftHomologyIso_comm X U V n

local instance relativeHomologyFunctor_preservesBinaryBiproducts (n : ℕ) :
    PreservesBinaryBiproducts
      (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

end Subsets

section ClosedSupports

variable (X : TopCat) (K L : Set X)

/-- The signed pair of restrictions from the union of supports to the two supports.
The left complement is written `Kᶜ ∩ Lᶜ = (K ∪ L)ᶜ` to avoid equality transports. -/
abbrev supportedMayerVietorisLeftChainMap :
    (relativeChainFunctor ℚ).obj (TopPair.ofSubset (Kᶜ ∩ Lᶜ)) ⟶
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset Kᶜ) ⊞
        (relativeChainFunctor ℚ).obj (TopPair.ofSubset Lᶜ) :=
  relativeMayerVietorisLeftChainMap X Kᶜ Lᶜ

/-- The sum of restrictions from the two supports to their intersection. -/
abbrev supportedMayerVietorisRightChainMap :
    ((relativeChainFunctor ℚ).obj (TopPair.ofSubset Kᶜ) ⊞
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset Lᶜ)) ⟶
        (relativeChainFunctor ℚ).obj (TopPair.ofSubset (Kᶜ ∪ Lᶜ)) :=
  relativeMayerVietorisRightChainMap X Kᶜ Lᶜ

/-- The connecting map for homology supported on two closed subsets. -/
abbrev supportedMayerVietorisBoundary (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    RelativeHomology ℚ (TopPair.ofSubset (Kᶜ ∪ Lᶜ)) (n + 1) ⟶
      RelativeHomology ℚ (TopPair.ofSubset (Kᶜ ∩ Lᶜ)) n :=
  relativeMayerVietorisBoundary X Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl n

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the support sequence at the direct sum of homology groups supported on
`K` and `L`. The only geometric hypotheses are closedness of the two supports. -/
theorem supportedMayerVietoris_exact_middle (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (supportedMayerVietorisLeftChainMap X K L) n)
      (HomologicalComplex.homologyMap (supportedMayerVietorisRightChainMap X K L) n)
      (by
        rw [← HomologicalComplex.homologyMap_comp, relativeMayerVietorisLeftRight_comp,
          HomologicalComplex.homologyMap_zero])).Exact :=
  relativeMayerVietoris_exact_middle X Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl n

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the support sequence at homology supported on the intersection. -/
theorem supportedMayerVietoris_exact_intersection
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (supportedMayerVietorisRightChainMap X K L) (n + 1))
      (supportedMayerVietorisBoundary X K L hK hL n)
      (by
        exact relativeMayerVietoris_right_boundary X Kᶜ Lᶜ
          hK.isOpen_compl hL.isOpen_compl n)).Exact :=
  relativeMayerVietoris_exact_union X Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl n

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the support sequence at homology supported on the union. -/
theorem supportedMayerVietoris_exact_union
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ) :
    (ShortComplex.mk
      (supportedMayerVietorisBoundary X K L hK hL n)
      (HomologicalComplex.homologyMap (supportedMayerVietorisLeftChainMap X K L) n)
      (by
        exact relativeMayerVietoris_boundary_left X Kᶜ Lᶜ
          hK.isOpen_compl hL.isOpen_compl n)).Exact :=
  relativeMayerVietoris_exact_intersection X Kᶜ Lᶜ hK.isOpen_compl hL.isOpen_compl n

end ClosedSupports

end AlgebraicTopology.Singular
