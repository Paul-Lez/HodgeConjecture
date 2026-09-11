/-
Copyright 2026 Paul Lezeau and The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Other.AlgebraicTopology.IntegralCechTotalAugmentation
public import Other.AlgebraicTopology.OrderedCechNormalization

import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.Topology.Category.TopCat.EpiMono

/-!
This module generalizes the ordered-intersection decomposition in Paul Lezeau's
`sphere-six-complex`, file `BoundarySevenCechOrderedTarget.lean`, commit
`b200b3fa92c64b73f3f212026f191f85364f05e3`.  The tuple model and its normalization are from
Chris Birkbeck's pull request #185, commit `5701e7211a1129650185feda1660fb44fbde9aef`.

# Ordered-intersection model of a cover Čech bicomplex

For any family of subsets `U`, the iterated wide pullback in the Čech nerve of the canonical
presentation of cover-small singular simplices is the coproduct, over all ordered tuples of
indices, of the singular simplicial sets of their common intersections.  Repetitions are kept,
so this statement needs no nonemptiness or acyclicity assumption on any intersection.

The intersection singular chain complexes and their inclusion maps form the generic
`SupportChainModels` input used by ordered Čech normalization.  This file makes the geometric
input and the objectwise Čech decomposition explicit.  It does not assert sheafification,
flasqueness, or a hypercohomology comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Simplicial
open AlgebraicTopology.OrderedCechTuple

namespace AlgebraicTopology

namespace Singular

variable {ι : Type} [LinearOrder ι] (X : TopCat) (U : ι → Set X)

/-- The intersection of the cover members selected by `s`.  The empty intersection is the
whole ambient space. -/
public def openCoverIntersection (s : Finset ι) : Set X :=
  ⋂ i ∈ s, U i

omit [LinearOrder ι] in
@[simp]
public theorem mem_openCoverIntersection_iff (s : Finset ι) (x : X) :
    x ∈ openCoverIntersection X U s ↔ ∀ i ∈ s, x ∈ U i := by
  simp [openCoverIntersection]

/-- Inclusion of a smaller geometric intersection into a larger one, contravariant in the
finite support. -/
public def openCoverIntersectionInclusion {s t : Finset ι} (hst : s ⊆ t) :
    TopCat.of (openCoverIntersection X U t) ⟶
      TopCat.of (openCoverIntersection X U s) :=
  TopCat.ofHom
    { toFun := fun x ↦ ⟨x.1, by
        rw [mem_openCoverIntersection_iff]
        intro i hi
        exact (mem_openCoverIntersection_iff X U t x.1).mp x.2 i (hst hi)⟩
      continuous_toFun := by fun_prop }

omit [LinearOrder ι] in
public theorem openCoverIntersectionInclusion_refl (s : Finset ι) :
    openCoverIntersectionInclusion X U (Finset.Subset.refl s) = 𝟙 _ := by
  ext x
  rfl

omit [LinearOrder ι] in
@[reassoc]
public theorem openCoverIntersectionInclusion_comp {r s t : Finset ι}
    (hrs : r ⊆ s) (hst : s ⊆ t) :
    openCoverIntersectionInclusion X U hst ≫
        openCoverIntersectionInclusion X U hrs =
      openCoverIntersectionInclusion X U (hrs.trans hst) := by
  ext x
  rfl

/-- Integral singular chains on all nonempty finite supports, with maps induced by inclusions
of intersections. -/
public def openCoverIntersectionChainModels : SupportChainModels ι where
  obj s := IntegralSingularChainComplexObj
    (TopCat.of (openCoverIntersection X U s.unop.1))
  map {s t} f := integralSingularChainMapObj
    (openCoverIntersectionInclusion X U (leOfHom f.unop))
  map_id s := by
    unfold integralSingularChainMapObj
    rw [openCoverIntersectionInclusion_refl]
    simp
  map_comp {r s t} f g := by
    unfold integralSingularChainMapObj
    rw [← Functor.map_comp, openCoverIntersectionInclusion_comp]

/-- An ordered tuple of cover indices in one outer Čech degree.  The proof component aligns this
index exactly with `TupleClass.all`. -/
public abbrev OpenCoverCechTuple (n : SimplexCategoryᵒᵖ) :=
  {_a : Fin (n.unop.len + 1) → ι // True}

/-- The common intersection belonging to an ordered Čech tuple. -/
public abbrev openCoverTupleIntersection {n : SimplexCategoryᵒᵖ}
    (a : OpenCoverCechTuple (ι := ι) n) : Set X :=
  openCoverIntersection X U (tupleSupport a.1).1

@[simp]
public theorem openCoverCechTuple_mem_support {n : SimplexCategoryᵒᵖ}
    (a : OpenCoverCechTuple (ι := ι) n) (i : Fin (n.unop.len + 1)) :
    a.1 i ∈ (tupleSupport a.1).1 :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- Inclusion of a tuple intersection into the cover member selected in slot `i`. -/
public def openCoverTupleIntersectionToMember {n : SimplexCategoryᵒᵖ}
    (a : OpenCoverCechTuple (ι := ι) n) (i : Fin (n.unop.len + 1)) :
    TopCat.of (openCoverTupleIntersection X U a) ⟶ TopCat.of (U (a.1 i)) :=
  TopCat.ofHom
    { toFun := fun x ↦ ⟨x.1,
        (mem_openCoverIntersection_iff X U _ x.1).mp x.2 _
          (openCoverCechTuple_mem_support a i)⟩
      continuous_toFun := by fun_prop }

@[reassoc]
public theorem openCoverTupleIntersectionToMember_comp_inclusion
    {n : SimplexCategoryᵒᵖ} (a : OpenCoverCechTuple (ι := ι) n)
    (i : Fin (n.unop.len + 1)) :
    openCoverTupleIntersectionToMember X U a i ≫
        topologicalSubsetInclusion X (U (a.1 i)) =
      topologicalSubsetInclusion X (openCoverTupleIntersection X U a) := by
  ext x
  rfl

/-- The selected intersection leg into the coproduct presentation source. -/
public def openCoverTupleIntersectionToPresentationLeg
    {n : SimplexCategoryᵒᵖ} (a : OpenCoverCechTuple (ι := ι) n)
    (i : Fin (n.unop.len + 1)) :
    TopCat.toSSet.obj (TopCat.of (openCoverTupleIntersection X U a)) ⟶
      coverSmallPresentationSource X U :=
  TopCat.toSSet.map (openCoverTupleIntersectionToMember X U a i) ≫
    Sigma.ι (fun j : ι ↦ TopCat.toSSet.obj (TopCat.of (U j))) (a.1 i)

/-- The common map from a tuple intersection into cover-small singular simplices. -/
public def openCoverTupleIntersectionToSmall
    {n : SimplexCategoryᵒᵖ} (a : OpenCoverCechTuple (ι := ι) n) :
    TopCat.toSSet.obj (TopCat.of (openCoverTupleIntersection X U a)) ⟶
      coverSmallSingularSubcomplex X U :=
  TopCat.toSSet.map (openCoverTupleIntersectionToMember X U a 0) ≫
    coverMemberToSmallSingularSet X U (a.1 0)

public theorem openCoverTupleIntersectionToPresentationLeg_condition
    {n : SimplexCategoryᵒᵖ} (a : OpenCoverCechTuple (ι := ι) n)
    (i : Fin (n.unop.len + 1)) :
    openCoverTupleIntersectionToPresentationLeg X U a i ≫
        coverSmallPresentation X U =
      openCoverTupleIntersectionToSmall X U a := by
  rw [← cancel_mono (coverSmallSingularSubcomplex X U).ι]
  simp only [openCoverTupleIntersectionToPresentationLeg, Category.assoc,
    coverSmallPresentation_iota_assoc,
    coverMemberToSmallSingularSet_comp_inclusion,
    openCoverTupleIntersectionToSmall]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- One ordered intersection determines a point of the corresponding Čech wide pullback. -/
public def openCoverTupleIntersectionToCechSummand
    {n : SimplexCategoryᵒᵖ} (a : OpenCoverCechTuple (ι := ι) n) :
    TopCat.toSSet.obj (TopCat.of (openCoverTupleIntersection X U a)) ⟶
      (Arrow.mk (coverSmallPresentation X U)).augmentedCechNerve.left.obj n :=
  WidePullback.lift (openCoverTupleIntersectionToSmall X U a)
    (openCoverTupleIntersectionToPresentationLeg X U a)
    (openCoverTupleIntersectionToPresentationLeg_condition X U a)

/-- The coproduct map from all ordered intersections to one object of the actual Čech nerve. -/
public def openCoverOrderedCechMap (n : SimplexCategoryᵒᵖ) :
    (∐ fun a : OpenCoverCechTuple (ι := ι) n ↦
      TopCat.toSSet.obj (TopCat.of (openCoverTupleIntersection X U a))) ⟶
      (Arrow.mk (coverSmallPresentation X U)).augmentedCechNerve.left.obj n :=
  Sigma.desc (openCoverTupleIntersectionToCechSummand X U)

/-- Projection from an actual Čech wide pullback to a selected presentation leg. -/
public def openCoverCechProjection (n : SimplexCategoryᵒᵖ)
    (i : Fin (n.unop.len + 1)) :
    (Arrow.mk (coverSmallPresentation X U)).augmentedCechNerve.left.obj n ⟶
      coverSmallPresentationSource X U :=
  WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ coverSmallPresentation X U) i

@[reassoc]
public theorem openCoverOrderedCechMap_projection
    {n : SimplexCategoryᵒᵖ} (a : OpenCoverCechTuple (ι := ι) n)
    (i : Fin (n.unop.len + 1)) :
    Sigma.ι (fun b : OpenCoverCechTuple (ι := ι) n ↦
        TopCat.toSSet.obj (TopCat.of (openCoverTupleIntersection X U b))) a ≫
        openCoverOrderedCechMap X U n ≫ openCoverCechProjection X U n i =
      TopCat.toSSet.map (openCoverTupleIntersectionToMember X U a i) ≫
        Sigma.ι (fun j : ι ↦ TopCat.toSSet.obj (TopCat.of (U j))) (a.1 i) := by
  rw [← Category.assoc, openCoverOrderedCechMap, Sigma.ι_desc]
  change WidePullback.lift (openCoverTupleIntersectionToSmall X U a)
      (openCoverTupleIntersectionToPresentationLeg X U a)
      (openCoverTupleIntersectionToPresentationLeg_condition X U a) ≫
        WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦
          coverSmallPresentation X U) i = _
  rw [WidePullback.lift_π]
  rfl

private def openCoverSSetCoproductAppIsColimit {κ : Type}
    (Y : κ → SSet) (q : SimplexCategoryᵒᵖ) :
    IsColimit (Cofan.mk ((∐ Y).obj q) (fun i ↦ (Sigma.ι Y i).app q)) :=
  isColimitCofanMkObjOfIsColimit ((evaluation _ _).obj q) Y
    (fun i ↦ Sigma.ι Y i) (coproductIsCoproduct Y)

private theorem openCoverSSetCoproduct_app_jointly_surjective {κ : Type}
    (Y : κ → SSet) (q : SimplexCategoryᵒᵖ) (x : (∐ Y).obj q) :
    ∃ i y, (Sigma.ι Y i).app q y = x :=
  Cofan.inj_jointly_surjective_of_isColimit
    (openCoverSSetCoproductAppIsColimit Y q) x

private theorem openCoverSSetCoproduct_app_index_eq {κ : Type}
    (Y : κ → SSet) (q : SimplexCategoryᵒᵖ) {i j : κ}
    (x : (Y i).obj q) (y : (Y j).obj q)
    (h : (Sigma.ι Y i).app q x = (Sigma.ι Y j).app q y) : i = j :=
  Cofan.eq_of_inj_apply_eq_of_isColimit
    (openCoverSSetCoproductAppIsColimit Y q) x y h

private theorem openCoverSSetCoproduct_app_injective {κ : Type}
    (Y : κ → SSet) (q : SimplexCategoryᵒᵖ) (i : κ) :
    Function.Injective ((Sigma.ι Y i).app q) :=
  Cofan.inj_injective_of_isColimit
    (openCoverSSetCoproductAppIsColimit Y q) i

omit [LinearOrder ι] in
private theorem openCoverCech_app_ext {n q : SimplexCategoryᵒᵖ}
    (x y : ((Arrow.mk (coverSmallPresentation X U)).augmentedCechNerve.left.obj n).obj q)
    (h : ∀ i, (openCoverCechProjection X U n i).app q x =
      (openCoverCechProjection X U n i).app q y) : x = y := by
  let arrows := fun _ : Fin (n.unop.len + 1) ↦ coverSmallPresentation X U
  let D := WidePullbackShape.wideCospan
    (coverSmallSingularSubcomplex X U : SSet)
    (fun _ : Fin (n.unop.len + 1) ↦ coverSmallPresentationSource X U) arrows
  let ev := (evaluation SimplexCategoryᵒᵖ (Type 0)).obj q
  have hlim : IsLimit (Functor.mapCone ev (limit.cone D)) :=
    isLimitOfPreserves ev (limit.isLimit D)
  apply (Types.isLimitEquivSections hlim).injective
  ext j
  cases j with
  | none =>
      have hx := congrArg (fun k ↦ k.app q x) (WidePullback.π_arrow arrows 0)
      have hy := congrArg (fun k ↦ k.app q y) (WidePullback.π_arrow arrows 0)
      exact hx.symm.trans
        ((congrArg (fun z ↦ (arrows 0).app q z) (h 0)).trans hy)
  | some i => exact h i

private theorem openCoverTupleIntersectionToMember_app_injective
    {n q : SimplexCategoryᵒᵖ} (a : OpenCoverCechTuple (ι := ι) n)
    (i : Fin (n.unop.len + 1)) :
    Function.Injective
      ((TopCat.toSSet.map (openCoverTupleIntersectionToMember X U a i)).app q) := by
  let : Mono (openCoverTupleIntersectionToMember X U a i) :=
    (TopCat.mono_iff_injective _).mpr
      (fun _ _ h ↦ Subtype.ext
        (congrArg (fun z : U (a.1 i) ↦ z.1) h))
  let : Mono (TopCat.toSSet.map
      (openCoverTupleIntersectionToMember X U a i)) :=
    Functor.map_mono TopCat.toSSet _
  exact (CategoryTheory.mono_iff_injective _).mp inferInstance

public theorem openCoverOrderedCechMap_app_injective (n q : SimplexCategoryᵒᵖ) :
    Function.Injective ((openCoverOrderedCechMap X U n).app q) := by
  let A := fun a : OpenCoverCechTuple (ι := ι) n ↦
    TopCat.toSSet.obj (TopCat.of (openCoverTupleIntersection X U a))
  let B := fun j : ι ↦ TopCat.toSSet.obj (TopCat.of (U j))
  intro x y hxy
  obtain ⟨a, xa, rfl⟩ := openCoverSSetCoproduct_app_jointly_surjective A q x
  obtain ⟨b, xb, rfl⟩ := openCoverSSetCoproduct_app_jointly_surjective A q y
  have hcoord (i : Fin (n.unop.len + 1)) :
      (Sigma.ι B (a.1 i)).app q
          ((TopCat.toSSet.map
            (openCoverTupleIntersectionToMember X U a i)).app q xa) =
        (Sigma.ι B (b.1 i)).app q
          ((TopCat.toSSet.map
            (openCoverTupleIntersectionToMember X U b i)).app q xb) := by
    have hproj := congrArg (fun z ↦ (openCoverCechProjection X U n i).app q z) hxy
    have ha := congrArg (fun k ↦ k.app q xa)
      (openCoverOrderedCechMap_projection X U a i)
    have hb := congrArg (fun k ↦ k.app q xb)
      (openCoverOrderedCechMap_projection X U b i)
    exact ha.symm.trans (hproj.trans hb)
  have hab : a = b := by
    ext i
    exact openCoverSSetCoproduct_app_index_eq B q _ _ (hcoord i)
  subst b
  have hmember :
      (TopCat.toSSet.map
        (openCoverTupleIntersectionToMember X U a 0)).app q xa =
      (TopCat.toSSet.map
        (openCoverTupleIntersectionToMember X U a 0)).app q xb :=
    openCoverSSetCoproduct_app_injective B q (a.1 0) (hcoord 0)
  have habSimplex : xa = xb :=
    openCoverTupleIntersectionToMember_app_injective X U a 0 hmember
  exact congrArg ((Sigma.ι A a).app q) habSimplex

omit [LinearOrder ι] in
private theorem openCoverPresentation_iota (j : ι) :
    Sigma.ι (fun k : ι ↦ TopCat.toSSet.obj (TopCat.of (U k))) j ≫
        coverSmallPresentation X U =
      coverMemberToSmallSingularSet X U j := by
  rw [coverSmallPresentation, Sigma.ι_desc]

private theorem openCoverToSSetObjEquiv_map_apply {Y Z : TopCat}
    (f : Y ⟶ Z) (q : SimplexCategoryᵒᵖ) (x : (TopCat.toSSet.obj Y).obj q)
    (z : stdSimplex ℝ (Fin (q.unop.len + 1))) :
    (TopCat.toSSetObjEquiv Z q) ((TopCat.toSSet.map f).app q x) z =
      f ((TopCat.toSSetObjEquiv Y q x) z) := by
  rfl

public theorem openCoverOrderedCechMap_app_surjective (n q : SimplexCategoryᵒᵖ) :
    Function.Surjective ((openCoverOrderedCechMap X U n).app q) := by
  let A := fun a : OpenCoverCechTuple (ι := ι) n ↦
    TopCat.toSSet.obj (TopCat.of (openCoverTupleIntersection X U a))
  let B := fun j : ι ↦ TopCat.toSSet.obj (TopCat.of (U j))
  intro x
  have hex (i : Fin (n.unop.len + 1)) :
      ∃ j y, (Sigma.ι B j).app q y =
        (openCoverCechProjection X U n i).app q x :=
    openCoverSSetCoproduct_app_jointly_surjective B q _
  choose a y hy using hex
  let arrows := fun _ : Fin (n.unop.len + 1) ↦ coverSmallPresentation X U
  have hsmall (i : Fin (n.unop.len + 1)) :
      (coverMemberToSmallSingularSet X U (a i)).app q (y i) =
        (coverMemberToSmallSingularSet X U (a 0)).app q (y 0) := by
    have hpresi := congrArg (fun k ↦ k.app q (y i))
      (openCoverPresentation_iota X U (a i))
    have hpres0 := congrArg (fun k ↦ k.app q (y 0))
      (openCoverPresentation_iota X U (a 0))
    have hyi := congrArg (fun z ↦ (coverSmallPresentation X U).app q z) (hy i)
    have hy0 := congrArg (fun z ↦ (coverSmallPresentation X U).app q z) (hy 0)
    have hpi := congrArg (fun k ↦ k.app q x) (WidePullback.π_arrow arrows i)
    have hp0 := congrArg (fun k ↦ k.app q x) (WidePullback.π_arrow arrows 0)
    exact hpresi.symm.trans
      (hyi.trans (hpi.trans (hp0.symm.trans (hy0.symm.trans hpres0))))
  have hfull (i : Fin (n.unop.len + 1)) :
      (TopCat.toSSet.map (topologicalSubsetInclusion X (U (a i)))).app q (y i) =
        (TopCat.toSSet.map (topologicalSubsetInclusion X (U (a 0)))).app q (y 0) := by
    have hi := congrArg (fun k ↦ k.app q (y i))
      (coverMemberToSmallSingularSet_comp_inclusion X U (a i))
    have h0 := congrArg (fun k ↦ k.app q (y 0))
      (coverMemberToSmallSingularSet_comp_inclusion X U (a 0))
    exact hi.symm.trans
      ((congrArg (fun z ↦ (coverSmallSingularSubcomplex X U).ι.app q z)
        (hsmall i)).trans h0)
  let y0Map := TopCat.toSSetObjEquiv (TopCat.of (U (a 0))) q (y 0)
  let aTuple : OpenCoverCechTuple (ι := ι) n := ⟨a, trivial⟩
  let zMap : C(stdSimplex ℝ (Fin (q.unop.len + 1)),
      openCoverTupleIntersection X U aTuple) :=
    { toFun := fun p ↦ ⟨(y0Map p).1, by
        rw [mem_openCoverIntersection_iff]
        intro j hj
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
        have heq := congrArg
          (fun s ↦ (TopCat.toSSetObjEquiv X q s) p) (hfull i)
        rw [openCoverToSSetObjEquiv_map_apply,
          openCoverToSSetObjEquiv_map_apply] at heq
        change ((TopCat.toSSetObjEquiv (TopCat.of (U (a i))) q (y i)) p).1 =
          (y0Map p).1 at heq
        rw [← heq]
        exact ((TopCat.toSSetObjEquiv (TopCat.of (U (a i))) q (y i)) p).2⟩
      continuous_toFun := by fun_prop }
  let z := (TopCat.toSSetObjEquiv
    (TopCat.of (openCoverTupleIntersection X U aTuple)) q).symm zMap
  have hz (i : Fin (n.unop.len + 1)) :
      (TopCat.toSSet.map
        (openCoverTupleIntersectionToMember X U aTuple i)).app q z = y i := by
    apply (TopCat.toSSetObjEquiv (TopCat.of (U (a i))) q).injective
    ext p
    have heq := congrArg
      (fun s ↦ (TopCat.toSSetObjEquiv X q s) p) (hfull i)
    rw [openCoverToSSetObjEquiv_map_apply,
      openCoverToSSetObjEquiv_map_apply] at heq
    rw [openCoverToSSetObjEquiv_map_apply]
    simp only [z]
    exact heq.symm
  refine ⟨(Sigma.ι A aTuple).app q z, ?_⟩
  apply openCoverCech_app_ext X U
  intro i
  calc
    (openCoverCechProjection X U n i).app q
        ((openCoverOrderedCechMap X U n).app q ((Sigma.ι A aTuple).app q z)) =
      (Sigma.ι B (a i)).app q
        ((TopCat.toSSet.map
          (openCoverTupleIntersectionToMember X U aTuple i)).app q z) := by
            simpa using congrArg (fun k ↦ k.app q z)
              (openCoverOrderedCechMap_projection X U aTuple i)
    _ = (Sigma.ι B (a i)).app q (y i) := congrArg _ (hz i)
    _ = (openCoverCechProjection X U n i).app q x := hy i

/-- Objectwise, the actual Čech nerve of the cover-small presentation is the coproduct of the
singular simplicial sets of all ordered intersections. -/
public def openCoverOrderedCechIso (n : SimplexCategoryᵒᵖ) :
    (∐ fun a : OpenCoverCechTuple (ι := ι) n ↦
      TopCat.toSSet.obj (TopCat.of (openCoverTupleIntersection X U a))) ≅
      (Arrow.mk (coverSmallPresentation X U)).augmentedCechNerve.left.obj n := by
  let : ∀ q, IsIso ((openCoverOrderedCechMap X U n).app q) := fun q ↦
    (CategoryTheory.isIso_iff_bijective _).mpr
      ⟨openCoverOrderedCechMap_app_injective X U n q,
        openCoverOrderedCechMap_app_surjective X U n q⟩
  let : IsIso (openCoverOrderedCechMap X U n) :=
    NatIso.isIso_of_isIso_app (openCoverOrderedCechMap X U n)
  exact asIso (openCoverOrderedCechMap X U n)

@[simp]
public theorem openCoverOrderedCechIso_hom (n : SimplexCategoryᵒᵖ) :
    (openCoverOrderedCechIso X U n).hom = openCoverOrderedCechMap X U n :=
  rfl

@[reassoc]
public theorem openCoverOrderedCechIso_hom_summand
    {n : SimplexCategoryᵒᵖ} (a : OpenCoverCechTuple (ι := ι) n) :
    Sigma.ι (fun b : OpenCoverCechTuple (ι := ι) n ↦
        TopCat.toSSet.obj (TopCat.of (openCoverTupleIntersection X U b))) a ≫
        (openCoverOrderedCechIso X U n).hom =
      openCoverTupleIntersectionToCechSummand X U a := by
  rw [openCoverOrderedCechIso_hom, openCoverOrderedCechMap, Sigma.ι_desc]

/-! ### Compatibility with the outer Čech faces -/

/-- Delete one entry of an ordered tuple. -/
public def openCoverCechTupleFace {p : ℕ}
    (a : {_a : Fin (p + 2) → ι // True}) (i : Fin (p + 2)) :
    {_b : Fin (p + 1) → ι // True} :=
  ⟨Fin.removeNth i a.1, trivial⟩

/-- The support of a tuple face is contained in the support of the tuple. -/
public theorem openCoverCechTupleFace_support_subset {p : ℕ}
    (a : {_a : Fin (p + 2) → ι // True}) (i : Fin (p + 2)) :
    (tupleSupport (openCoverCechTupleFace a i).1).1 ⊆
      (tupleSupport a.1).1 := by
  rw [tupleSupport_subset_iff]
  exact Set.range_comp_subset_range i.succAbove a.1

/-- Inclusion of the intersection of all entries of a tuple into the intersection belonging to
one of its faces. -/
public def openCoverTupleFaceIntersectionInclusion {p : ℕ}
    (a : {_a : Fin (p + 2) → ι // True}) (i : Fin (p + 2)) :
    TopCat.of (openCoverTupleIntersection X U
      (n := Opposite.op (SimplexCategory.mk (p + 1))) a) ⟶
      TopCat.of (openCoverTupleIntersection X U
        (n := Opposite.op (SimplexCategory.mk p))
        (openCoverCechTupleFace a i)) :=
  openCoverIntersectionInclusion X U
    (openCoverCechTupleFace_support_subset a i)

@[reassoc]
public theorem openCoverTupleFaceIntersectionInclusion_comp_member {p : ℕ}
    (a : {_a : Fin (p + 2) → ι // True}) (i : Fin (p + 2))
    (j : Fin (p + 1)) :
    openCoverTupleFaceIntersectionInclusion X U a i ≫
        openCoverTupleIntersectionToMember X U
          (n := Opposite.op (SimplexCategory.mk p))
          (openCoverCechTupleFace a i) j =
      openCoverTupleIntersectionToMember X U
        (n := Opposite.op (SimplexCategory.mk (p + 1)))
        a (i.succAbove j) := by
  ext x
  rfl

/-- The wide-pullback lift of one ordered intersection has its prescribed selected leg. -/
@[reassoc]
public theorem openCoverTupleIntersectionToCechSummand_comp_projection
    {n : SimplexCategoryᵒᵖ} (a : OpenCoverCechTuple (ι := ι) n)
    (j : Fin (n.unop.len + 1)) :
    openCoverTupleIntersectionToCechSummand X U a ≫
        openCoverCechProjection X U n j =
      TopCat.toSSet.map (openCoverTupleIntersectionToMember X U a j) ≫
        Sigma.ι (fun k : ι ↦ TopCat.toSSet.obj (TopCat.of (U k))) (a.1 j) := by
  change WidePullback.lift _ _ _ ≫ WidePullback.π _ j = _
  rw [WidePullback.lift_π]
  rfl

omit [LinearOrder ι] in
set_option backward.isDefEq.respectTransparency false in
/-- A Čech face followed by a selected projection is the corresponding undeleted projection. -/
@[reassoc]
public theorem openCoverCech_δ_comp_projection {p : ℕ}
    (i : Fin (p + 2)) (j : Fin (p + 1)) :
    (Arrow.mk (coverSmallPresentation X U)).cechNerve.δ i ≫
        openCoverCechProjection X U (Opposite.op (SimplexCategory.mk p)) j =
      openCoverCechProjection X U
        (Opposite.op (SimplexCategory.mk (p + 1))) (i.succAbove j) := by
  change WidePullback.lift
      (WidePullback.base
        (fun _ : Fin (p + 2) ↦ coverSmallPresentation X U))
      (fun k : Fin (p + 1) ↦
        WidePullback.π
          (fun _ : Fin (p + 2) ↦ coverSmallPresentation X U)
          (((SimplexCategory.δ i).op.unop.toOrderHom) k)) _ ≫
        WidePullback.π
          (fun _ : Fin (p + 1) ↦ coverSmallPresentation X U) j =
    WidePullback.π
      (fun _ : Fin (p + 2) ↦ coverSmallPresentation X U) (i.succAbove j)
  rw [WidePullback.lift_π]
  rfl

omit [LinearOrder ι] in
/-- Every selected projection followed by the presentation map is the base map of the Čech
wide pullback. -/
@[reassoc]
public theorem openCoverCechProjection_comp_presentation
    (n : SimplexCategoryᵒᵖ) (j : Fin (n.unop.len + 1)) :
    openCoverCechProjection X U n j ≫ coverSmallPresentation X U =
      WidePullback.base
        (fun _ : Fin (n.unop.len + 1) ↦ coverSmallPresentation X U) :=
  WidePullback.π_arrow (fun _ : Fin (n.unop.len + 1) ↦ coverSmallPresentation X U) j

set_option backward.isDefEq.respectTransparency false in
/-- The ordered-intersection summands commute with every outer face of the actual Čech nerve. -/
@[reassoc]
public theorem openCoverTupleIntersectionToCechSummand_comp_δ {p : ℕ}
    (a : {_a : Fin (p + 2) → ι // True}) (i : Fin (p + 2)) :
    TopCat.toSSet.map (openCoverTupleFaceIntersectionInclusion X U a i) ≫
        openCoverTupleIntersectionToCechSummand X U
          (n := Opposite.op (SimplexCategory.mk p))
          (openCoverCechTupleFace a i) =
      openCoverTupleIntersectionToCechSummand X U
          (n := Opposite.op (SimplexCategory.mk (p + 1))) a ≫
        (Arrow.mk (coverSmallPresentation X U)).cechNerve.δ i := by
  have hproj (j : Fin (p + 1)) :
      (TopCat.toSSet.map (openCoverTupleFaceIntersectionInclusion X U a i) ≫
          openCoverTupleIntersectionToCechSummand X U
            (n := Opposite.op (SimplexCategory.mk p))
            (openCoverCechTupleFace a i)) ≫
          openCoverCechProjection X U
            (Opposite.op (SimplexCategory.mk p)) j =
        (openCoverTupleIntersectionToCechSummand X U
            (n := Opposite.op (SimplexCategory.mk (p + 1))) a ≫
          (Arrow.mk (coverSmallPresentation X U)).cechNerve.δ i) ≫
          openCoverCechProjection X U
            (Opposite.op (SimplexCategory.mk p)) j := by
    rw [Category.assoc,
      openCoverTupleIntersectionToCechSummand_comp_projection]
    rw [Category.assoc, openCoverCech_δ_comp_projection,
      openCoverTupleIntersectionToCechSummand_comp_projection]
    rw [← Category.assoc, ← Functor.map_comp,
      openCoverTupleFaceIntersectionInclusion_comp_member]
    rfl
  ext q x
  apply openCoverCech_app_ext X U
  intro j
  exact ConcreteCategory.congr_hom (congr_app (hproj j) q) x

/-! ### Passing the objectwise decomposition to integral chain complexes -/

/-- Integral simplicial chains preserve coproducts.  This is proved degreewise: evaluation of a
simplicial set preserves colimits, and the free abelian-group functor is a left adjoint. -/
public noncomputable instance integralChainsPreservesCoproducts (κ : Type) :
    PreservesColimitsOfShape (Discrete κ)
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro q
  let adj := sigmaConstAdj (AddCommGrpCat.of ℤ)
  let : PreservesColimitsOfShape (Discrete κ)
      (sigmaConst.obj (AddCommGrpCat.of ℤ)) :=
    adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  change PreservesColimitsOfShape (Discrete κ)
    ((evaluation SimplexCategoryᵒᵖ (Type 0)).obj
      (Opposite.op (SimplexCategory.mk q)) ⋙
        sigmaConst.obj (AddCommGrpCat.of ℤ))
  infer_instance

/-- The coproduct of the integral chain complexes is canonically the integral chain complex of
the coproduct of simplicial sets. -/
public def integralChainsCoproductDiagramIso {κ : Type} (Y : κ → SSet) :
    Discrete.functor (fun i ↦
      ((SSet.chainComplexFunctor AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)).obj (Y i)) ≅
      Discrete.functor Y ⋙
        (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    rintro ⟨A⟩ ⟨B⟩ ⟨⟨h⟩⟩
    change A = B at h
    subst B
    simp)

@[simp]
public theorem integralChainsCoproductDiagramIso_hom_app {κ : Type}
    (Y : κ → SSet) (i : κ) :
    (integralChainsCoproductDiagramIso Y).hom.app (Discrete.mk i) = 𝟙 _ :=
  rfl

public def integralChainsCoproductIso {κ : Type} (Y : κ → SSet) :
    (∐ fun i ↦ (Y i).chainComplex (AddCommGrpCat.of ℤ)) ≅
      (∐ Y).chainComplex (AddCommGrpCat.of ℤ) := by
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  exact (HasColimit.isoOfNatIso (integralChainsCoproductDiagramIso Y)).trans
    (preservesColimitIso F (Discrete.functor Y)).symm

@[reassoc]
public theorem integralChainsCoproductIso_hom_ι {κ : Type}
    (Y : κ → SSet) (i : κ) :
    Sigma.ι (fun j ↦ (Y j).chainComplex (AddCommGrpCat.of ℤ)) i ≫
        (integralChainsCoproductIso Y).hom =
      SSet.chainComplexMap (Sigma.ι Y i) (AddCommGrpCat.of ℤ) := by
  simp only [integralChainsCoproductIso, Iso.trans_hom, ← Category.assoc,
    HasColimit.isoOfNatIso_ι_hom, integralChainsCoproductDiagramIso_hom_app,
    Category.id_comp, Iso.symm_hom, ι_preservesColimitIso_inv]

/-- In every outer degree, the generic ordered-intersection chain object is canonically
isomorphic to the corresponding column of the actual Čech bicomplex. -/
public abbrev openCoverOrderedIntersectionSSet (p : ℕ)
    (a : {_a : Fin (p + 1) → ι // True}) : SSet :=
  TopCat.toSSet.obj (TopCat.of
    (openCoverTupleIntersection X U
      (n := Opposite.op (SimplexCategory.mk p)) a))

public def openCoverOrderedCechColumnIso (p : ℕ) :
    (openCoverIntersectionChainModels X U).cechObject TupleClass.all p ≅
      (integralCechBicomplex (Arrow.mk (coverSmallPresentation X U))).X p :=
  integralChainsCoproductIso
      (openCoverOrderedIntersectionSSet X U p) ≪≫
    ((SSet.chainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)).mapIso
        (openCoverOrderedCechIso X U (Opposite.op (SimplexCategory.mk p)))

@[reassoc]
public theorem openCoverOrderedCechColumnIso_hom_ι (p : ℕ)
    (a : {_a : Fin (p + 1) → ι // True}) :
    Sigma.ι (fun b ↦
        (openCoverOrderedIntersectionSSet X U p b).chainComplex
          (AddCommGrpCat.of ℤ)) a ≫
        (openCoverOrderedCechColumnIso X U p).hom =
      SSet.chainComplexMap
        (openCoverTupleIntersectionToCechSummand X U
          (n := Opposite.op (SimplexCategory.mk p)) a)
        (AddCommGrpCat.of ℤ) := by
  change Sigma.ι (fun b ↦
      (openCoverOrderedIntersectionSSet X U p b).chainComplex
        (AddCommGrpCat.of ℤ)) a ≫
      ((integralChainsCoproductIso
          (openCoverOrderedIntersectionSSet X U p)).hom ≫
        ((SSet.chainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map
            (openCoverOrderedCechIso X U
              (Opposite.op (SimplexCategory.mk p))).hom) = _
  rw [← Category.assoc, integralChainsCoproductIso_hom_ι]
  change SSet.chainComplexMap
      (Sigma.ι (openCoverOrderedIntersectionSSet X U p) a)
        (AddCommGrpCat.of ℤ) ≫
      SSet.chainComplexMap
        (openCoverOrderedCechIso X U
          (Opposite.op (SimplexCategory.mk p))).hom
        (AddCommGrpCat.of ℤ) = _
  rw [← Functor.map_comp, openCoverOrderedCechIso_hom, openCoverOrderedCechMap, Sigma.ι_desc]

set_option backward.isDefEq.respectTransparency false in
/-- The summand formula for the column isomorphism, stated in the exact
`SupportChainModels.cechObject` presentation. -/
@[reassoc]
public theorem openCoverOrderedCechColumnIso_model_hom_ι (p : ℕ)
    (a : {_a : Fin (p + 1) → ι // TupleClass.all.mem p _a}) :
    Sigma.ι (fun b : {_b : Fin (p + 1) → ι // TupleClass.all.mem p _b} ↦
        (openCoverIntersectionChainModels X U).model (tupleSupport b.1)) a ≫
        (openCoverOrderedCechColumnIso X U p).hom =
      SSet.chainComplexMap
        (openCoverTupleIntersectionToCechSummand X U
          (n := Opposite.op (SimplexCategory.mk p)) a)
        (AddCommGrpCat.of ℤ) := by
  change Sigma.ι (fun b ↦
      (openCoverOrderedIntersectionSSet X U p b).chainComplex
        (AddCommGrpCat.of ℤ)) a ≫
        (openCoverOrderedCechColumnIso X U p).hom = _
  rw [openCoverOrderedCechColumnIso_hom_ι]

set_option backward.isDefEq.respectTransparency false in
/-- On one ordered summand, the differential of the generic tuple model is the signed sum of
the inclusions into its tuple faces. -/
@[reassoc]
public theorem openCoverIntersectionChainModels_ι_comp_d (p : ℕ)
    (a : {_a : Fin (p + 2) → ι // TupleClass.all.mem (p + 1) _a}) :
    Sigma.ι (fun b : {_b : Fin (p + 2) → ι // TupleClass.all.mem (p + 1) _b} ↦
        (openCoverIntersectionChainModels X U).model (tupleSupport b.1)) a ≫
        ((openCoverIntersectionChainModels X U).cechComplex TupleClass.all).d
          (p + 1) p =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ i.val) •
        ((openCoverIntersectionChainModels X U).face
            (openCoverCechTupleFace_support_subset a i) ≫
          Sigma.ι (fun b : {_b : Fin (p + 1) → ι // TupleClass.all.mem p _b} ↦
            (openCoverIntersectionChainModels X U).model (tupleSupport b.1))
              (openCoverCechTupleFace a i)) := by
  rw [SupportChainModels.cechComplex_d, SupportChainModels.ι_realize, boundary_single, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show Finsupp.single (Fin.removeNth i a.1) ((-1 : ℤ) ^ i.val * 1) =
      ((-1 : ℤ) ^ i.val) • Finsupp.single (Fin.removeNth i a.1) 1 by simp, map_zsmul]
  congr 1
  rw [SupportChainModels.realizeAux_single]
  unfold SupportChainModels.faceOrZero
  rw [dif_pos (by
    rw [tupleSupport_subset_iff]
    exact Set.range_comp_subset_range i.succAbove a.1), SupportChainModels.ιOrZero_of_mem]
  rfl

omit [LinearOrder ι] in
set_option backward.isDefEq.respectTransparency false in
/-- The outer differential of the actual integral Čech bicomplex is the alternating sum of its
Čech face maps. -/
public theorem integralCechBicomplex_d_eq_sum_faces (p : ℕ) :
    (integralCechBicomplex (Arrow.mk (coverSmallPresentation X U))).d (p + 1) p =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ i.val) •
        (SimplicialObject.Augmented.drop.obj
          (integralCechAugmentedChains
            (Arrow.mk (coverSmallPresentation X U)))).δ i := by
  change (AlternatingFaceMapComplex.obj
    (SimplicialObject.Augmented.drop.obj
      (integralCechAugmentedChains
        (Arrow.mk (coverSmallPresentation X U))))).d (p + 1) p = _
  rw [AlternatingFaceMapComplex.obj_d_eq]

omit [LinearOrder ι] in
/-- The face maps in the chain-valued Čech nerve are the chain maps induced by the underlying
simplicial-set Čech faces. -/
public theorem integralCechAugmentedChains_δ (p : ℕ) (i : Fin (p + 2)) :
    (SimplicialObject.Augmented.drop.obj
      (integralCechAugmentedChains
        (Arrow.mk (coverSmallPresentation X U)))).δ i =
      SSet.chainComplexMap
        ((Arrow.mk (coverSmallPresentation X U)).cechNerve.δ i)
        (AddCommGrpCat.of ℤ) := by
  rfl

/-! ### The bicomplex and total-complex isomorphisms -/

set_option backward.isDefEq.respectTransparency false in
/-- The chain map from one ordered-intersection summand into the matching column of the actual
Čech bicomplex. -/
public def openCoverTupleCechSummandChainMap (p : ℕ)
    (a : {_a : Fin (p + 1) → ι // TupleClass.all.mem p _a}) :
    (openCoverIntersectionChainModels X U).model (tupleSupport a.1) ⟶
      (integralCechBicomplex (Arrow.mk (coverSmallPresentation X U))).X p :=
  SSet.chainComplexMap
    (openCoverTupleIntersectionToCechSummand X U
      (n := Opposite.op (SimplexCategory.mk p)) a)
    (AddCommGrpCat.of ℤ)

/-- A geometric model face is the singular-chain map induced by the inclusion of tuple
intersections. -/
public theorem openCoverIntersectionChainModels_face_eq (p : ℕ)
    (a : {_a : Fin (p + 2) → ι // TupleClass.all.mem (p + 1) _a})
    (i : Fin (p + 2)) :
    (openCoverIntersectionChainModels X U).face
        (openCoverCechTupleFace_support_subset a i) =
      SSet.chainComplexMap
        (TopCat.toSSet.map (openCoverTupleFaceIntersectionInclusion X U a i))
        (AddCommGrpCat.of ℤ) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Chain-level compatibility of one ordered-intersection summand with one outer Čech face. -/
@[reassoc]
public theorem openCoverTupleCechSummandChainMap_comp_face (p : ℕ)
    (a : {_a : Fin (p + 2) → ι // TupleClass.all.mem (p + 1) _a})
    (i : Fin (p + 2)) :
    openCoverTupleCechSummandChainMap X U (p + 1) a ≫
        (SimplicialObject.Augmented.drop.obj
          (integralCechAugmentedChains
            (Arrow.mk (coverSmallPresentation X U)))).δ i =
      (openCoverIntersectionChainModels X U).face
          (openCoverCechTupleFace_support_subset a i) ≫
        openCoverTupleCechSummandChainMap X U p (openCoverCechTupleFace a i) := by
  rw [openCoverIntersectionChainModels_face_eq]
  have h := congrArg
    (fun f ↦ ((SSet.chainComplexFunctor AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ)).map f)
    (openCoverTupleIntersectionToCechSummand_comp_δ X U a i).symm
  simpa only [openCoverTupleCechSummandChainMap,
    integralCechAugmentedChains_δ, Functor.map_comp] using h

set_option backward.isDefEq.respectTransparency false in
/-- The column isomorphism restricts to the canonical chain map on each geometric summand. -/
@[reassoc]
public theorem openCoverOrderedCechColumnIso_hom_ι_chainMap (p : ℕ)
    (a : {_a : Fin (p + 1) → ι // TupleClass.all.mem p _a}) :
    Sigma.ι (fun b : {_b : Fin (p + 1) → ι // TupleClass.all.mem p _b} ↦
        (openCoverIntersectionChainModels X U).model (tupleSupport b.1)) a ≫
        (openCoverOrderedCechColumnIso X U p).hom =
      openCoverTupleCechSummandChainMap X U p a :=
  openCoverOrderedCechColumnIso_model_hom_ι X U p a

set_option backward.isDefEq.respectTransparency false in
/-- The column isomorphisms commute with the outer differentials after restriction to any
ordered-intersection summand. -/
public theorem openCoverOrderedCechColumnIso_comm_ι (p : ℕ)
    (a : {_a : Fin (p + 2) → ι // TupleClass.all.mem (p + 1) _a}) :
    (Sigma.ι (fun b : {_b : Fin (p + 2) → ι // TupleClass.all.mem (p + 1) _b} ↦
        (openCoverIntersectionChainModels X U).model (tupleSupport b.1)) a ≫
      (openCoverOrderedCechColumnIso X U (p + 1)).hom) ≫
        (integralCechBicomplex (Arrow.mk (coverSmallPresentation X U))).d (p + 1) p =
      Sigma.ι (fun b : {_b : Fin (p + 2) → ι // TupleClass.all.mem (p + 1) _b} ↦
          (openCoverIntersectionChainModels X U).model (tupleSupport b.1)) a ≫
        (((openCoverIntersectionChainModels X U).cechComplex TupleClass.all).d (p + 1) p ≫
          (openCoverOrderedCechColumnIso X U p).hom) := by
  rw [← Category.assoc, openCoverOrderedCechColumnIso_hom_ι_chainMap,
    integralCechBicomplex_d_eq_sum_faces, Preadditive.comp_sum,
    openCoverIntersectionChainModels_ι_comp_d, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  congr 1
  rw [Category.assoc, openCoverOrderedCechColumnIso_hom_ι_chainMap]
  exact openCoverTupleCechSummandChainMap_comp_face X U p a i

set_option backward.isDefEq.respectTransparency false in
/-- The column isomorphisms commute with every differential of the two outer chain complexes. -/
public theorem openCoverOrderedCechColumnIso_comm (m n : ℕ)
    (hmn : (ComplexShape.down ℕ).Rel m n) :
    (openCoverOrderedCechColumnIso X U m).hom ≫
        (integralCechBicomplex (Arrow.mk (coverSmallPresentation X U))).d m n =
      ((openCoverIntersectionChainModels X U).cechComplex TupleClass.all).d m n ≫
        (openCoverOrderedCechColumnIso X U n).hom := by
  obtain rfl : m = n + 1 := hmn.symm
  apply Sigma.hom_ext
  intro a
  exact openCoverOrderedCechColumnIso_comm_ι X U n a

/-- The full ordered-intersection bicomplex is canonically isomorphic to the actual integral
Čech bicomplex of the cover-small presentation. -/
public def openCoverOrderedCechBicomplexIso :
    (openCoverIntersectionChainModels X U).cechComplex TupleClass.all ≅
      integralCechBicomplex (Arrow.mk (coverSmallPresentation X U)) :=
  HomologicalComplex.Hom.isoOfComponents
    (openCoverOrderedCechColumnIso X U)
    (openCoverOrderedCechColumnIso_comm X U)

/-- The corresponding direct-sum total complexes are canonically isomorphic. -/
public def openCoverOrderedCechTotalIso :
    (openCoverIntersectionChainModels X U).cechTotal TupleClass.all ≅
      (integralCechBicomplex
        (Arrow.mk (coverSmallPresentation X U))).total (ComplexShape.down ℕ) :=
  HomologicalComplex₂.total.mapIso (openCoverOrderedCechBicomplexIso X U)
    (ComplexShape.down ℕ)

/-- The normalized ordered-intersection total maps canonically to cover-small integral singular
chains: include normalized tuples, identify the full ordered bicomplex with the actual Čech
bicomplex, and apply its augmentation. -/
public def openCoverNormalizedCechTotalAugmentation :
    (openCoverIntersectionChainModels X U).cechTotal TupleClass.strictMono ⟶
      CoverSmallIntegralSingularChainComplex X U :=
  (openCoverIntersectionChainModels X U).totalNormalizedInclusion ≫
    (openCoverOrderedCechTotalIso X U).hom ≫
      integralCechTotalAugmentationToTarget
        (Arrow.mk (coverSmallPresentation X U))

set_option linter.style.haveILetI false in
/-- The normalized ordered-intersection total computes cover-small integral singular chains.
No acyclicity condition on intersections is used. -/
public theorem openCoverNormalizedCechTotalAugmentation_quasiIso :
    QuasiIso (openCoverNormalizedCechTotalAugmentation X U) := by
  let M := openCoverIntersectionChainModels X U
  letI : QuasiIso M.totalNormalizedInclusion :=
    M.totalNormalizationHomotopyEquiv.quasiIso_inv
  letI : IsIso (openCoverOrderedCechTotalIso X U).hom :=
    (openCoverOrderedCechTotalIso X U).isIso_hom
  letI : QuasiIso (integralCechTotalAugmentationToTarget
      (Arrow.mk (coverSmallPresentation X U))) :=
    coverSmallIntegralCechTotalAugmentationToTarget_quasiIso X U
  change QuasiIso
    (M.totalNormalizedInclusion ≫
      (openCoverOrderedCechTotalIso X U).hom ≫
        integralCechTotalAugmentationToTarget
          (Arrow.mk (coverSmallPresentation X U)))
  infer_instance

end Singular

end AlgebraicTopology
