/-
Copyright 2026 Dean Cureton, Chris Birkbeck, and The Formal Conjectures Authors.

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

public import FormalConjecturesForMathlib.AlgebraicTopology.FiniteGoodCoverHomology
public import Mathlib.Algebra.Category.FGModuleCat.Colimits

/-!
# The finite nerve model of a good cover

This file continues the ordered Čech construction adapted from
[`sphere-six-complex` pull request #185](https://github.com/deancureton/sphere-six-complex/pull/185)
by Chris Birkbeck. Empty intersections contribute the zero chain complex; inhabited
intersections contribute the integral singular chains of a point. The upstream repository is
released under the Apache License 2.0.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set

namespace AlgebraicTopology

set_option linter.style.haveILetI false in
/-- A finite coproduct of quasi-isomorphisms of nonnegative chain complexes is a
quasi-isomorphism.

This proof is ported from Dean Cureton's
[`BoundarySevenCechGlobalComparison.lean`](https://github.com/deancureton/sphere-six-complex/blob/895c0a0/SphereSixComplex/Topology/BoundarySevenCechGlobalComparison.lean),
under the Apache License 2.0. -/
public theorem quasiIso_finite_coproduct
    {I : Type} [Finite I]
    (K L : I → FirstQuadrantChainComplex)
    (f : ∀ i, K i ⟶ L i) (hf : ∀ i, QuasiIso (f i)) :
    QuasiIso (Limits.Sigma.map f) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat
    (ComplexShape.down ℕ) n
  let σK := sigmaComparison H K
  let σL := sigmaComparison H L
  haveI hfi (i : I) : IsIso (H.map (f i)) := by
    exact (quasiIsoAt_iff_isIso_homologyMap (f i) n).mp
      ((hf i).quasiIsoAt n)
  haveI : IsIso (Limits.Sigma.map fun i ↦ H.map (f i)) := inferInstance
  haveI : IsIso σK := by dsimp [σK]; infer_instance
  haveI : IsIso σL := by dsimp [σL]; infer_instance
  have hnat : σK ≫ H.map (Limits.Sigma.map f) =
      Limits.Sigma.map (fun i ↦ H.map (f i)) ≫ σL := by
    apply Sigma.hom_ext
    intro i
    simp only [← Category.assoc, σK, σL,
      Limits.ι_comp_sigmaComparison, ← H.map_comp, Limits.Sigma.ι_map]
    rw [Category.assoc, Limits.ι_comp_sigmaComparison, ← H.map_comp]
  haveI : IsIso (σK ≫ H.map (Limits.Sigma.map f)) := by
    rw [hnat]
    infer_instance
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ σK
    (H.map (Limits.Sigma.map f)) inferInstance inferInstance

/-- A finite categorical coproduct of finitely generated abelian groups is finitely generated. -/
public theorem module_finite_addCommGrp_finite_coproduct
    {I : Type} [Finite I] (A : I → AddCommGrpCat)
    (hA : ∀ i, Module.Finite ℤ ((A i : AddCommGrpCat) : Type)) :
    Module.Finite ℤ ((∐ A : AddCommGrpCat) : Type) := by
  let Z : I → ModuleCat ℤ := fun i ↦ ModuleCat.of ℤ (A i)
  let F := forget₂ (ModuleCat ℤ) AddCommGrpCat
  let σ := sigmaComparison F Z
  let _ (i : I) : Module.Finite ℤ (Z i) := hA i
  have htarget : Module.Finite ℤ (∐ Z : ModuleCat ℤ) := inferInstance
  have htarget' : Module.Finite ℤ (F.obj (∐ Z : ModuleCat ℤ)) := by
    change @Module.Finite ℤ ((∐ Z : ModuleCat ℤ) : Type) _ _
      (AddCommGroup.toIntModule ((∐ Z : ModuleCat ℤ) : Type))
    let hm : (∐ Z : ModuleCat ℤ).isModule =
        AddCommGroup.toIntModule ((∐ Z : ModuleCat ℤ) : Type) :=
      Subsingleton.elim _ _
    rw [← hm]
    exact htarget
  let _ : Module.Finite ℤ (F.obj (∐ Z : ModuleCat ℤ)) := htarget'
  let _ : IsIso σ := by dsimp [σ, F]; infer_instance
  change Module.Finite ℤ ((∐ fun i ↦ F.obj (Z i) : AddCommGrpCat) : Type)
  exact Module.Finite.equiv
    (asIso σ).symm.addCommGroupIsoToAddEquiv.toIntLinearEquiv

/-- Integral homology is finitely generated in every degree where the chain group is finitely
generated. -/
public theorem module_finite_integral_homology_of_finite_chain_group
    (C : ChainComplex AddCommGrpCat ℕ) (n : ℕ)
    (h : Module.Finite ℤ (C.X n)) : Module.Finite ℤ (C.homology n) := by
  let _ := h
  let i : C.cycles n →ₗ[ℤ] C.X n := (C.iCycles n).hom.toIntLinearMap
  have hi : Function.Injective i := by
    change Function.Injective (C.iCycles n).hom
    exact (AddCommGrpCat.mono_iff_injective (C.iCycles n)).mp inferInstance
  have hcycles : Module.Finite ℤ (C.cycles n) :=
    Module.Finite.of_injective i hi
  let _ := hcycles
  let q : C.cycles n →ₗ[ℤ] C.homology n := (C.homologyπ n).hom.toIntLinearMap
  have hq : Function.Surjective q := by
    change Function.Surjective (C.homologyπ n).hom
    exact (AddCommGrpCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance
  exact Module.Finite.of_surjective q hq

namespace Singular

variable {ι : Type} [LinearOrder ι] (X : TopCat) (U : ι → Set X)

/-- Integral singular chains of an empty topological space form a zero object. -/
public theorem integralSingularChainComplexObj_isZero_of_not_nonempty
    (A : Type) [TopologicalSpace A] (hA : ¬ Nonempty A) :
    IsZero (IntegralSingularChainComplexObj (TopCat.of A)) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.Hom.ext
  funext n
  apply Sigma.hom_ext
  rintro a
  let z : stdSimplex ℝ (Fin (n + 1)) :=
    ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0⟩
  exact (hA ⟨(TopCat.toSSetObjEquiv (TopCat.of A) _ a) z⟩).elim

/-- The local nerve space is a point exactly when the intersection is inhabited, and is empty
otherwise. -/
public abbrev goodCoverNerveLocalSpace (s : CoverSupport ι) :=
  {_u : PUnit // (openCoverIntersection X U s.1).Nonempty}

/-- An inclusion of supports induces the evident map of local nerve spaces. -/
public def goodCoverNerveSpaceFace {s t : CoverSupport ι} (hst : s.1 ⊆ t.1) :
    C(goodCoverNerveLocalSpace (X := X) (U := U) t,
      goodCoverNerveLocalSpace (X := X) (U := U) s) where
  toFun y := ⟨y.1, by
    obtain ⟨x, hx⟩ := y.2
    exact ⟨x, (mem_openCoverIntersection_iff X U s.1 x).2 fun i hi =>
      (mem_openCoverIntersection_iff X U t.1 x).1 hx i (hst hi)⟩⟩
  continuous_toFun := by fun_prop

omit [LinearOrder ι] in
public theorem goodCoverNerveSpaceFace_refl (s : CoverSupport ι) :
    TopCat.ofHom (goodCoverNerveSpaceFace (X := X) (U := U)
      (Finset.Subset.refl s.1)) = 𝟙 _ := by
  ext y

omit [LinearOrder ι] in
@[reassoc]
public theorem goodCoverNerveSpaceFace_comp {r s t : CoverSupport ι}
    (hrs : r.1 ⊆ s.1) (hst : s.1 ⊆ t.1) :
    TopCat.ofHom (goodCoverNerveSpaceFace (X := X) (U := U) hst) ≫
        TopCat.ofHom (goodCoverNerveSpaceFace (X := X) (U := U) hrs) =
      TopCat.ofHom (goodCoverNerveSpaceFace (X := X) (U := U) (hrs.trans hst)) := by
  ext y

/-- Singular chains of the local nerve space.  This is point chains for an inhabited
intersection and a zero object for an empty intersection. -/
public abbrev goodCoverNerveLocalModel (s : CoverSupport ι) :
    ChainComplex AddCommGrpCat ℕ :=
  IntegralSingularChainComplexObj
    (TopCat.of (goodCoverNerveLocalSpace (X := X) (U := U) s))

omit [LinearOrder ι] in
/-- Empty intersections contribute a zero local chain complex to the nerve model. -/
public theorem goodCoverNerveLocalModel_isZero_of_not_nonempty
    (s : CoverSupport ι) (hs : ¬ (openCoverIntersection X U s.1).Nonempty) :
    IsZero (goodCoverNerveLocalModel (X := X) (U := U) s) := by
  apply integralSingularChainComplexObj_isZero_of_not_nonempty
  rintro ⟨y⟩
  exact hs y.2

omit [LinearOrder ι] in
/-- Each chain group of a local point-or-empty nerve model is finitely generated. -/
public theorem goodCoverNerveLocalModel_X_module_finite
    (s : CoverSupport ι) (q : ℕ) :
    Module.Finite ℤ ((goodCoverNerveLocalModel (X := X) (U := U) s).X q) := by
  let Y := TopCat.of (goodCoverNerveLocalSpace (X := X) (U := U) s)
  let e := TopCat.toSSetObjEquiv Y (Opposite.op (SimplexCategory.mk q))
  let _ : Subsingleton ((TopCat.toSSet.obj Y).obj
      (Opposite.op (SimplexCategory.mk q))) :=
    ⟨fun a b ↦ e.injective (Subsingleton.elim _ _)⟩
  let _ : Finite ((TopCat.toSSet.obj Y).obj
      (Opposite.op (SimplexCategory.mk q))) := Finite.of_subsingleton
  change Module.Finite ℤ ((∐ fun _ : (TopCat.toSSet.obj Y).obj
    (Opposite.op (SimplexCategory.mk q)) ↦ AddCommGrpCat.of ℤ : AddCommGrpCat) : Type)
  apply module_finite_addCommGrp_finite_coproduct
  intro
  infer_instance

/-- Point-or-zero local models form a contravariant diagram on nonempty finite supports. -/
public def goodCoverNerveChainModels : SupportChainModels ι where
  model := goodCoverNerveLocalModel (X := X) (U := U)
  face {s t} hst := integralSingularChainMapObj
    (TopCat.ofHom (goodCoverNerveSpaceFace (X := X) (U := U) hst))
  face_id s := by
    unfold integralSingularChainMapObj
    rw [goodCoverNerveSpaceFace_refl]
    simp
  face_comp {r s t} hrs hst := by
    unfold integralSingularChainMapObj
    rw [← Functor.map_comp, goodCoverNerveSpaceFace_comp]

/-- The canonical map from an intersection to the corresponding point-or-empty nerve space. -/
public def openCoverIntersectionToNerve (s : CoverSupport ι) :
    C(openCoverIntersection X U s.1,
      goodCoverNerveLocalSpace (X := X) (U := U) s) where
  toFun x := ⟨PUnit.unit, ⟨x.1, x.2⟩⟩
  continuous_toFun := by fun_prop

omit [LinearOrder ι] in
@[reassoc]
public theorem openCoverIntersectionToNerve_naturality {s t : CoverSupport ι}
    (hst : s.1 ⊆ t.1) :
    openCoverIntersectionInclusion X U hst ≫
        TopCat.ofHom (openCoverIntersectionToNerve (X := X) (U := U) s) =
      TopCat.ofHom (openCoverIntersectionToNerve (X := X) (U := U) t) ≫
        TopCat.ofHom (goodCoverNerveSpaceFace (X := X) (U := U) hst) := by
  ext x

/-- The local singular-chain augmentation from an intersection to its nerve space. -/
public def goodCoverLocalAugmentation (s : CoverSupport ι) :
    (openCoverIntersectionChainModels X U).model s ⟶
      (goodCoverNerveChainModels X U).model s :=
  integralSingularChainMapObj
    (TopCat.ofHom (openCoverIntersectionToNerve (X := X) (U := U) s))

omit [LinearOrder ι] in
@[reassoc]
public theorem goodCoverLocalAugmentation_naturality {s t : CoverSupport ι}
    (hst : s.1 ⊆ t.1) :
    (openCoverIntersectionChainModels X U).face hst ≫
        goodCoverLocalAugmentation X U s =
      goodCoverLocalAugmentation X U t ≫
        (goodCoverNerveChainModels X U).face hst := by
  unfold goodCoverLocalAugmentation openCoverIntersectionChainModels
    goodCoverNerveChainModels integralSingularChainMapObj
  rw [← Functor.map_comp, ← Functor.map_comp,
    openCoverIntersectionToNerve_naturality]

end Singular

namespace SupportChainModels

variable {ι : Type} [LinearOrder ι] {M N : SupportChainModels ι}

/-- A natural morphism between contravariant diagrams of local chain models. -/
public structure Hom (M N : SupportChainModels ι) where
  /-- The map on a finite support. -/
  app : ∀ s, M.model s ⟶ N.model s
  /-- Compatibility with restriction to a smaller support. -/
  naturality : ∀ {s t : CoverSupport ι} (hst : s.1 ⊆ t.1),
    M.face hst ≫ app s = app t ≫ N.face hst

namespace Hom

variable (η : Hom M N)

/-- The coproduct of a natural local-model map over tuples in one Čech degree. -/
public def cechObjectMap (P : TupleClass ι) (n : ℕ) :
    M.cechObject P n ⟶ N.cechObject P n :=
  Limits.Sigma.map fun a : {a : Fin (n + 1) → ι // P.mem n a} ↦
    η.app (tupleSupport a.1)

@[reassoc]
public theorem faceOrZero_naturality {n m : ℕ}
    (a : Fin (n + 1) → ι) (b : Fin (m + 1) → ι) :
    M.faceOrZero a b ≫ η.app (tupleSupport b) =
      η.app (tupleSupport a) ≫ N.faceOrZero a b := by
  unfold SupportChainModels.faceOrZero
  split_ifs with h
  · exact η.naturality h
  · simp

@[reassoc]
public theorem realizeAux_naturality {n m : ℕ} (a : Fin (n + 1) → ι)
    (P : TupleClass ι) (w : OrderedCechTuple.Formal ι (m + 1)) :
    M.realizeAux a P w ≫ η.cechObjectMap P m =
      η.app (tupleSupport a) ≫ N.realizeAux a P w := by
  have hw := OrderedCechTuple.linearMap_apply_eq_of_forall_mem_support
    (L := (Preadditive.rightComp _ (η.cechObjectMap P m)).toIntLinearMap ∘ₗ
      M.realizeAux a P)
    (R := (Preadditive.leftComp _ (η.app (tupleSupport a))).toIntLinearMap ∘ₗ
      N.realizeAux a P)
    (w := w) fun b _ ↦ by
      change M.realizeAux a P (Finsupp.single b 1) ≫ η.cechObjectMap P m =
        η.app (tupleSupport a) ≫ N.realizeAux a P (Finsupp.single b 1)
      rw [M.realizeAux_single, N.realizeAux_single]
      by_cases hb : P.mem m b
      · rw [M.ιOrZero_of_mem P hb, N.ιOrZero_of_mem P hb]
        unfold cechObjectMap
        rw [Category.assoc, Limits.Sigma.ι_map, ← Category.assoc,
          η.faceOrZero_naturality, Category.assoc]
      · simp [SupportChainModels.ιOrZero, hb]
  exact hw

@[reassoc]
public theorem realize_naturality (P Q : TupleClass ι) {n m : ℕ}
    (T : OrderedCechTuple.Formal ι (n + 1) →ₗ[ℤ]
      OrderedCechTuple.Formal ι (m + 1)) :
    η.cechObjectMap P n ≫ N.realize P Q T =
      M.realize P Q T ≫ η.cechObjectMap Q m := by
  apply Sigma.hom_ext
  intro a
  unfold cechObjectMap
  rw [Limits.Sigma.ι_map_assoc, N.ι_realize, M.ι_realize_assoc]
  exact (η.realizeAux_naturality a.1 Q (T (Finsupp.single a.1 1))).symm

/-- A natural local-model map induces a map of ordered Čech bicomplexes. -/
public def cechMap (P : TupleClass ι) : M.cechComplex P ⟶ N.cechComplex P where
  f n := η.cechObjectMap P n
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [M.cechComplex_d, N.cechComplex_d]
    exact η.realize_naturality P P _

end Hom

end SupportChainModels

namespace Singular

variable {ι : Type} [LinearOrder ι] (X : TopCat) (U : ι → Set X)

/-- The intersection-to-nerve augmentations form a natural map of local chain models. -/
public def goodCoverNerveLocalMap :
    SupportChainModels.Hom (openCoverIntersectionChainModels X U)
      (goodCoverNerveChainModels X U) where
  app := goodCoverLocalAugmentation X U
  naturality := goodCoverLocalAugmentation_naturality X U

/-- The natural local augmentation on the normalized ordered Čech bicomplex. -/
public def goodCoverNerveBicomplexMap :
    (openCoverIntersectionChainModels X U).cechComplex TupleClass.strictMono ⟶
      (goodCoverNerveChainModels X U).cechComplex TupleClass.strictMono :=
  (goodCoverNerveLocalMap X U).cechMap TupleClass.strictMono

namespace FiniteGoodCover

variable {X U}

/-- Every bidegree of the normalized finite-nerve bicomplex is a finitely generated
abelian group. -/
public theorem nerveCechObject_X_module_finite (h : FiniteGoodCover X U)
    (p q : ℕ) : Module.Finite ℤ
      (((goodCoverNerveChainModels X U).cechObject
        TupleClass.strictMono p).X q) := by
  let _ : Finite ι := h.finite_index
  let I := {a : Fin (p + 1) → ι // TupleClass.strictMono.mem p a}
  let K : I → ChainComplex AddCommGrpCat ℕ := fun a ↦
    goodCoverNerveLocalModel (X := X) (U := U) (tupleSupport a.1)
  let F := HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) q
  let σ := sigmaComparison F K
  have hsource : Module.Finite ℤ ((∐ fun a ↦ F.obj (K a) : AddCommGrpCat) : Type) := by
    apply module_finite_addCommGrp_finite_coproduct
    intro a
    exact goodCoverNerveLocalModel_X_module_finite X U (tupleSupport a.1) q
  let _ : Module.Finite ℤ ((∐ fun a ↦ F.obj (K a) : AddCommGrpCat) : Type) :=
    hsource
  let _ : IsIso σ := by dsimp [σ, F]; infer_instance
  change Module.Finite ℤ (F.obj (∐ K))
  exact Module.Finite.equiv
    (asIso σ).addCommGroupIsoToAddEquiv.toIntLinearEquiv

/-- Every chain group of the totalized finite nerve model is finitely generated. -/
public theorem nerveTotal_X_module_finite (h : FiniteGoodCover X U) (n : ℕ) :
    Module.Finite ℤ
      (((goodCoverNerveChainModels X U).cechTotal TupleClass.strictMono).X n) := by
  let _ : Finite ι := h.finite_index
  change Module.Finite ℤ ((∐ fun pq : FirstQuadrantTotalFiber n ↦
    (((goodCoverNerveChainModels X U).cechObject
      TupleClass.strictMono pq.1.1).X pq.1.2) : AddCommGrpCat) : Type)
  apply module_finite_addCommGrp_finite_coproduct
  intro pq
  exact h.nerveCechObject_X_module_finite pq.1.1 pq.1.2

omit [LinearOrder ι] in
set_option linter.style.haveILetI false in
/-- For a finite good cover, every local intersection-to-nerve augmentation is a
quasi-isomorphism. -/
public theorem localAugmentation_quasiIso (h : FiniteGoodCover X U)
    (s : CoverSupport ι) : QuasiIso (goodCoverLocalAugmentation X U s) := by
  by_cases hs : (openCoverIntersection X U s.1).Nonempty
  · letI : ContractibleSpace (openCoverIntersection X U s.1) :=
      h.contractible_intersection s.1 s.2 hs
    letI : Nonempty (goodCoverNerveLocalSpace (X := X) (U := U) s) :=
      ⟨⟨PUnit.unit, hs⟩⟩
    exact singularChainMap_quasiIso_of_contractibleSpaces (AddCommGrpCat.of ℤ)
      (openCoverIntersectionToNerve (X := X) (U := U) s)
  · have hsource : IsZero ((openCoverIntersectionChainModels X U).model s) :=
      integralSingularChainComplexObj_isZero_of_not_nonempty
        (openCoverIntersection X U s.1) (by
          rintro ⟨x⟩
          exact hs ⟨x.1, x.2⟩)
    have htarget : IsZero ((goodCoverNerveChainModels X U).model s) :=
      goodCoverNerveLocalModel_isZero_of_not_nonempty X U s hs
    letI : IsIso (goodCoverLocalAugmentation X U s) :=
      hsource.isIso htarget _
    infer_instance

/-- Each vertical column of the normalized good-cover comparison is a quasi-isomorphism. -/
public theorem nerveBicomplexMap_column_quasiIso (h : FiniteGoodCover X U) (p : ℕ) :
    QuasiIso ((goodCoverNerveBicomplexMap X U).f p) := by
  let _ : Finite ι := h.finite_index
  change QuasiIso (Limits.Sigma.map fun a :
    {a : Fin (p + 1) → ι // TupleClass.strictMono.mem p a} ↦
      goodCoverLocalAugmentation X U (tupleSupport a.1))
  apply quasiIso_finite_coproduct
  intro a
  exact h.localAugmentation_quasiIso (tupleSupport a.1)

/-- The totalized normalized Čech comparison from intersection chains to the finite nerve
model. -/
public def nerveTotalMap (_h : FiniteGoodCover X U) :
    (openCoverIntersectionChainModels X U).cechTotal TupleClass.strictMono ⟶
      (goodCoverNerveChainModels X U).cechTotal TupleClass.strictMono :=
  HomologicalComplex₂.total.map (goodCoverNerveBicomplexMap X U)
    (ComplexShape.down ℕ)

/-- The normalized intersection-chain total is quasi-isomorphic to the finite nerve total. -/
public theorem nerveTotalMap_quasiIso (h : FiniteGoodCover X U) :
    QuasiIso (nerveTotalMap h) := by
  apply firstQuadrantTotal_quasiIso_of_columns
  exact h.nerveBicomplexMap_column_quasiIso

/-- The finite nerve total has the integral homology of the ambient space. -/
public def nerveHomologyIso (h : FiniteGoodCover X U) (n : ℕ) :
    ((goodCoverNerveChainModels X U).cechTotal
      TupleClass.strictMono).homology n ≅
        (IntegralSingularChainComplexObj X).homology n := by
  letI : QuasiIso (nerveTotalMap h) := h.nerveTotalMap_quasiIso
  exact (asIso (HomologicalComplex.homologyMap (nerveTotalMap h) n)).symm ≪≫
    h.normalizedCechHomologyIso n

/-- A space with a finite good cover has finitely generated integral singular homology in
every degree. -/
public theorem integralSingularHomology_module_finite
    (h : FiniteGoodCover X U) (n : ℕ) :
    Module.Finite ℤ ((IntegralSingularChainComplexObj X).homology n) := by
  let _ : Module.Finite ℤ
      (((goodCoverNerveChainModels X U).cechTotal TupleClass.strictMono).homology n) :=
    module_finite_integral_homology_of_finite_chain_group _ _
      (h.nerveTotal_X_module_finite n)
  exact Module.Finite.equiv
    (h.nerveHomologyIso n).addCommGroupIsoToAddEquiv.toIntLinearEquiv

end FiniteGoodCover

end Singular

end AlgebraicTopology
