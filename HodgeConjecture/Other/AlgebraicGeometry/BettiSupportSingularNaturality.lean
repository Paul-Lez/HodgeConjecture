/-
Copyright 2026 The Formal Conjectures Authors.

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

public import HodgeConjecture.Other.AlgebraicGeometry.BettiCohomologyWithSupportComparison

/-!
# Naturality of the supported Betti comparison

This file constructs restriction of singular cochains through direct image and proves its
naturality with sheafification. For a closed subset of a smooth complex-point space, it also
constructs a compatible quasi-isomorphism from singular cochains on the open complement to the
chosen injective resolution. The resulting morphism to the derived direct-image model is induced
by the actual restriction of singular cochains. This file does not yet identify its global-section
mapping cone with relative singular cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory Filter TopologicalSpace

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] {U X : TopCat.{u}} (j : U ⟶ X)

lemma contractibleOpenBasis_of_isOpenEmbedding
    (hj : Topology.IsOpenEmbedding j)
    (hX : ∀ (x : X) (V : Opens X), x ∈ V →
      ∃ (W : Opens X), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V) :
    ∀ (x : U) (V : Opens U), x ∈ V →
      ∃ (W : Opens U), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V := by
  intro x V hxV
  let Vi : Opens X := ⟨j '' (V : Set U), (hj.isOpen_iff_image_isOpen).mp V.2⟩
  have hjx : j x ∈ Vi := ⟨x, hxV, rfl⟩
  obtain ⟨W, hjxW, hWcontractible, hWVi⟩ := hX (j x) Vi hjx
  let W' : Opens U :=
    ⟨j ⁻¹' (W : Set X), W.2.preimage j.hom.continuous⟩
  have hWrange : (W : Set X) ⊆ Set.range j := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hWVi hy
    exact ⟨z, hzy⟩
  have hW'contractible : ContractibleSpace W' := by
    change ContractibleSpace (j ⁻¹' (W : Set X))
    exact (hj.toIsEmbedding.homeomorphOfSubsetRange hWrange).contractibleSpace_iff.mpr
      hWcontractible
  refine ⟨W', hjxW, hW'contractible, ?_⟩
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hWVi hy
  exact hj.toIsEmbedding.injective hzy ▸ hz

lemma locallyPathConnectedSpace_of_contractibleOpenBasis
    (hX : ∀ (x : X) (V : Opens X), x ∈ V →
      ∃ (W : Opens X), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V) :
    LocallyPathConnectedSpace X := by
  refine ⟨fun x ↦ hasBasis_self.mpr fun S hS ↦ ?_⟩
  obtain ⟨V, hVS, hVopen, hxV⟩ := mem_nhds_iff.mp hS
  let Vo : Opens X := ⟨V, hVopen⟩
  obtain ⟨W, hxW, hWcontractible, hWVo⟩ := hX x Vo hxV
  let : ContractibleSpace W := hWcontractible
  refine ⟨(W : Set X), W.2.mem_nhds hxW, ?_, ?_⟩
  · rw [isPathConnected_iff_pathConnectedSpace]
    infer_instance
  · exact fun y hy ↦ hVS (hWVo hy)

lemma constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis
    (hX : ∀ (x : X) (V : Opens X), x ∈ V →
      ∃ (W : Opens X), x ∈ W ∧ ContractibleSpace W ∧ W ≤ V) :
    QuasiIso (constantsToSingularCochainSheafComplex R X) := by
  let : LocallyPathConnectedSpace X :=
    locallyPathConnectedSpace_of_contractibleOpenBasis hX
  constructor
  intro n
  cases n with
  | zero => exact constantsToSingularCochainSheafComplex_quasiIsoAt_zero R X
  | succ n =>
      exact constantsToSingularCochainSheafComplex_quasiIsoAt_succ_of_contractibleOpenBasis
        R X hX n

def preimageOpenToOpen (V : Opens X) :
    (Opens.toTopCat U).obj ((Opens.map j).obj V) ⟶ (Opens.toTopCat X).obj V :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨j x.1, x.2⟩,
      Continuous.subtype_mk (j.hom.continuous.comp continuous_subtype_val) _⟩

noncomputable def preimageOpenChainMap (V : Opens X) :
    (openSingularChainComplexFunctor R U).obj ((Opens.map j).obj V) ⟶
      (openSingularChainComplexFunctor R X).obj V :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)).map (preimageOpenToOpen j V)

lemma preimageOpenChainMap_naturality {V W : Opens X} (i : V ⟶ W) :
    (openSingularChainComplexFunctor R U).map ((Opens.map j).map i) ≫
        preimageOpenChainMap R j W =
      preimageOpenChainMap R j V ≫ (openSingularChainComplexFunctor R X).map i := by
  let F := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj
    (ModuleCat.of R R)
  change F.map ((Opens.toTopCat U).map ((Opens.map j).map i)) ≫
      F.map (preimageOpenToOpen j W) =
    F.map (preimageOpenToOpen j V) ≫ F.map ((Opens.toTopCat X).map i)
  calc
    _ = F.map ((Opens.toTopCat U).map ((Opens.map j).map i) ≫
        preimageOpenToOpen j W) := (F.map_comp _ _).symm
    _ = F.map (preimageOpenToOpen j V ≫ (Opens.toTopCat X).map i) := by
      congr 1
    _ = _ := F.map_comp _ _

noncomputable def singularRestrictionToRawPushforward (n : ℕ) :
    singularCochainPresheaf R X n ⟶
      (Opens.map j).op ⋙ singularCochainPresheaf R U n where
  app V := AddCommGrpCat.ofHom
    ((preimageOpenChainMap R j V.unop).f n).hom.dualMap.toAddMonoidHom
  naturality {V W} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    change OpenCochains R X V n at φ
    apply LinearMap.ext
    intro c
    change φ
        (((((openSingularChainComplexFunctor R X).map i.unop).f n).hom)
          (((preimageOpenChainMap R j W.unop).f n).hom c)) =
      φ
        ((((preimageOpenChainMap R j V.unop).f n).hom)
          ((((openSingularChainComplexFunctor R U).map
            ((Opens.map j).map i.unop)).f n).hom c))
    exact congrArg φ (ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.f n) (preimageOpenChainMap_naturality R j i.unop)).symm c)

noncomputable def singularRestrictionPresheaf (n : ℕ) :
    singularCochainPresheaf R X n ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat j).obj
        (singularCochainSheaf R U n)).obj :=
  singularRestrictionToRawPushforward R j n ≫
    Functor.whiskerLeft (Opens.map j).op
      (toSheafify (Opens.grothendieckTopology U) (singularCochainPresheaf R U n))

noncomputable def singularRestrictionSheaf (n : ℕ) :
    singularCochainSheaf R X n ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat j).obj
        (singularCochainSheaf R U n) :=
  ⟨sheafifyLift (Opens.grothendieckTopology X)
    (singularRestrictionPresheaf R j n)
    ((TopCat.Sheaf.pushforward AddCommGrpCat j).obj
      (singularCochainSheaf R U n)).property⟩

lemma toSheafify_comp_singularRestrictionSheaf (n : ℕ) :
    toSheafify (Opens.grothendieckTopology X)
        (singularCochainPresheaf R X n) ≫
      (singularRestrictionSheaf R j n).hom =
        singularRestrictionPresheaf R j n := by
  exact toSheafify_sheafifyLift (J := Opens.grothendieckTopology X)
    (singularRestrictionPresheaf R j n)
    (((TopCat.Sheaf.pushforward AddCommGrpCat j).obj
      (singularCochainSheaf R U n)).property)

lemma singularRestrictionToRawPushforward_coboundary (n : ℕ) :
    singularCochainCoboundary R X n ≫ singularRestrictionToRawPushforward R j (n + 1) =
      singularRestrictionToRawPushforward R j n ≫
        Functor.whiskerLeft (Opens.map j).op (singularCochainCoboundary R U n) := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  change OpenCochains R X V n at φ
  apply LinearMap.ext
  intro c
  change φ
      (((((openSingularChainComplexFunctor R X).obj V.unop).d (n + 1) n).hom)
        (((preimageOpenChainMap R j V.unop).f (n + 1)).hom c)) =
    φ
      ((((preimageOpenChainMap R j V.unop).f n).hom)
        ((((openSingularChainComplexFunctor R U).obj
          ((Opens.map j).obj V.unop)).d (n + 1) n).hom c))
  exact congrArg φ (ConcreteCategory.congr_hom
    ((preimageOpenChainMap R j V.unop).comm (n + 1) n) c)

set_option backward.isDefEq.respectTransparency false in
lemma singularRestrictionPresheaf_coboundary (n : ℕ) :
    singularCochainCoboundary R X n ≫ singularRestrictionPresheaf R j (n + 1) =
      singularRestrictionPresheaf R j n ≫
        ((TopCat.Sheaf.pushforward AddCommGrpCat j).map
          (singularCochainSheafCoboundary R U n)).hom := by
  unfold singularRestrictionPresheaf
  change singularCochainCoboundary R X n ≫
        singularRestrictionToRawPushforward R j (n + 1) ≫
          Functor.whiskerLeft (Opens.map j).op
            (toSheafify (Opens.grothendieckTopology U)
              (singularCochainPresheaf R U (n + 1))) =
    singularRestrictionToRawPushforward R j n ≫
      Functor.whiskerLeft (Opens.map j).op
        (toSheafify (Opens.grothendieckTopology U)
          (singularCochainPresheaf R U n)) ≫
      Functor.whiskerLeft (Opens.map j).op
        ((singularCochainSheafCoboundary R U n).hom)
  calc
    _ = (singularCochainCoboundary R X n ≫
          singularRestrictionToRawPushforward R j (n + 1)) ≫
        Functor.whiskerLeft (Opens.map j).op
          (toSheafify (Opens.grothendieckTopology U)
            (singularCochainPresheaf R U (n + 1))) := (Category.assoc _ _ _).symm
    _ = (singularRestrictionToRawPushforward R j n ≫
          Functor.whiskerLeft (Opens.map j).op
            (singularCochainCoboundary R U n)) ≫
        Functor.whiskerLeft (Opens.map j).op
          (toSheafify (Opens.grothendieckTopology U)
            (singularCochainPresheaf R U (n + 1))) := by
      rw [singularRestrictionToRawPushforward_coboundary]
    _ = singularRestrictionToRawPushforward R j n ≫
        Functor.whiskerLeft (Opens.map j).op
          (singularCochainCoboundary R U n ≫
            toSheafify (Opens.grothendieckTopology U)
              (singularCochainPresheaf R U (n + 1))) := by
      rw [Category.assoc, Functor.whiskerLeft_comp]
    _ = singularRestrictionToRawPushforward R j n ≫
        Functor.whiskerLeft (Opens.map j).op
          (toSheafify (Opens.grothendieckTopology U)
            (singularCochainPresheaf R U n) ≫
              (singularCochainSheafCoboundary R U n).hom) := by
      rw [toSheafify_naturality]
      rfl
    _ = _ := by
      rw [Functor.whiskerLeft_comp]

noncomputable def singularRestrictionSheafComplex :
    singularCochainSheafComplex R X ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat j).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (singularCochainSheafComplex R U) where
  f n := singularRestrictionSheaf R j n
  comm' i k hik := by
    obtain rfl := hik
    rw [singularCochainSheafComplex_d, Functor.mapHomologicalComplex_obj_d,
      singularCochainSheafComplex_d]
    apply Sheaf.hom_ext
    let η := singularCochainCoboundary R X i ≫
      singularRestrictionPresheaf R j (i + 1)
    apply (sheafifyLift_unique (J := Opens.grothendieckTopology X) η
      (((TopCat.Sheaf.pushforward AddCommGrpCat j).obj
        (singularCochainSheaf R U (i + 1))).property) _ ?_).trans
    · apply (sheafifyLift_unique (J := Opens.grothendieckTopology X) η
        (((TopCat.Sheaf.pushforward AddCommGrpCat j).obj
          (singularCochainSheaf R U (i + 1))).property) _ ?_).symm
      unfold η
      change toSheafify (Opens.grothendieckTopology X)
          (singularCochainPresheaf R X i) ≫
          (singularCochainSheafCoboundary R X i).hom ≫
          (singularRestrictionSheaf R j (i + 1)).hom = _
      calc
        _ = (toSheafify (Opens.grothendieckTopology X)
              (singularCochainPresheaf R X i) ≫
              (singularCochainSheafCoboundary R X i).hom) ≫
            (singularRestrictionSheaf R j (i + 1)).hom :=
          (Category.assoc _ _ _).symm
        _ = (singularCochainCoboundary R X i ≫
              toSheafify (Opens.grothendieckTopology X)
                (singularCochainPresheaf R X (i + 1))) ≫
            (singularRestrictionSheaf R j (i + 1)).hom := by
          rw [toSheafify_naturality]
          rfl
        _ = singularCochainCoboundary R X i ≫
            (toSheafify (Opens.grothendieckTopology X)
              (singularCochainPresheaf R X (i + 1)) ≫
              (singularRestrictionSheaf R j (i + 1)).hom) :=
          Category.assoc _ _ _
        _ = _ := by rw [toSheafify_comp_singularRestrictionSheaf]
    · unfold η
      change toSheafify (Opens.grothendieckTopology X)
          (singularCochainPresheaf R X i) ≫
          (singularRestrictionSheaf R j i).hom ≫
          ((TopCat.Sheaf.pushforward AddCommGrpCat j).map
            (singularCochainSheafCoboundary R U i)).hom = _
      calc
        _ = (toSheafify (Opens.grothendieckTopology X)
              (singularCochainPresheaf R X i) ≫
              (singularRestrictionSheaf R j i).hom) ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat j).map
              (singularCochainSheafCoboundary R U i)).hom :=
          (Category.assoc _ _ _).symm
        _ = singularRestrictionPresheaf R j i ≫
            ((TopCat.Sheaf.pushforward AddCommGrpCat j).map
              (singularCochainSheafCoboundary R U i)).hom := by
          rw [toSheafify_comp_singularRestrictionSheaf]
        _ = _ := (singularRestrictionPresheaf_coboundary R j i).symm

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open Point

open AlgebraicTopology.Singular

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ)

lemma analyticComplement_contractibleOpenBasis
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) :
    ∀ (x : TopCat.of (AnalyticComplement structureMap Z))
      (V : Opens (TopCat.of (AnalyticComplement structureMap Z))), x ∈ V →
      ∃ (W : Opens (TopCat.of (AnalyticComplement structureMap Z))),
        x ∈ W ∧ ContractibleSpace W ∧ W ≤ V :=
  contractibleOpenBasis_of_isOpenEmbedding
    (analyticComplementInclusion structureMap Z)
    (analyticComplementInclusion_isOpenEmbedding structureMap Z hZ)
    (exists_contractibleOpen_le structureMap)

lemma complementConstantsToSingularCochain_quasiIso
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) :
    QuasiIso (constantsToSingularCochainSheafComplex ℚ
      (TopCat.of (AnalyticComplement structureMap Z))) :=
  constantsToSingularCochainSheafComplex_quasiIso_of_contractibleOpenBasis ℚ
    (analyticComplement_contractibleOpenBasis structureMap Z hZ)

def complementConstantRationalSingleComplex
    (Z : Set (ComplexPoint X structureMap)) :
    CochainComplex (AnalyticComplementAdditiveSheaf structureMap Z) ℕ :=
  (CochainComplex.single₀ (AnalyticComplementAdditiveSheaf structureMap Z)).obj
    (complementConstantRationalSheaf structureMap Z)

def complementSingularCochainSheafComplex
    (Z : Set (ComplexPoint X structureMap)) :
    CochainComplex (AnalyticComplementAdditiveSheaf structureMap Z) ℕ :=
  singularCochainSheafComplex ℚ (TopCat.of (AnalyticComplement structureMap Z))

def complementConstantsToSingularCochain
    (Z : Set (ComplexPoint X structureMap)) :
    complementConstantRationalSingleComplex structureMap Z ⟶
      complementSingularCochainSheafComplex structureMap Z :=
  constantsToSingularCochainSheafComplex ℚ
    (TopCat.of (AnalyticComplement structureMap Z))

def complementConstantsToSingularCochainInt
    (Z : Set (ComplexPoint X structureMap)) :
    (complementConstantRationalSingleComplex structureMap Z).extend
        ComplexShape.embeddingUpNat ⟶
      (complementSingularCochainSheafComplex structureMap Z).extend
        ComplexShape.embeddingUpNat :=
  HomologicalComplex.extendMap
    (complementConstantsToSingularCochain structureMap Z)
      ComplexShape.embeddingUpNat

lemma complementConstantsToSingularCochainInt_mono
    (Z : Set (ComplexPoint X structureMap)) :
    Mono (complementConstantsToSingularCochainInt structureMap Z) := by
  exact constantsToSingularCochainComplexInt_mono ℚ
    (TopCat.of (AnalyticComplement structureMap Z))

lemma complementConstantsToSingularCochainInt_quasiIso
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) :
    QuasiIso (complementConstantsToSingularCochainInt structureMap Z) := by
  apply (HomologicalComplex.quasiIso_extendMap_iff
    (complementConstantsToSingularCochain structureMap Z)
      ComplexShape.embeddingUpNat).mpr
  exact complementConstantsToSingularCochain_quasiIso structureMap Z hZ

def complementResolutionMapInt (Z : Set (ComplexPoint X structureMap)) :
    (complementConstantRationalSingleComplex structureMap Z).extend
        ComplexShape.embeddingUpNat ⟶
      (complementConstantRationalInjectiveResolution structureMap Z).cocomplex.extend
        ComplexShape.embeddingUpNat :=
  HomologicalComplex.extendMap
    (complementConstantRationalInjectiveResolution structureMap Z).ι
      ComplexShape.embeddingUpNat

set_option linter.style.haveILetI false in
def complementSingularToInjectiveResolutionInt
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) :
    (complementSingularCochainSheafComplex structureMap Z).extend
        ComplexShape.embeddingUpNat ⟶
      (complementConstantRationalInjectiveResolution structureMap Z).cocomplex.extend
        ComplexShape.embeddingUpNat := by
  let a := complementConstantsToSingularCochainInt structureMap Z
  let r := complementResolutionMapInt structureMap Z
  let I := (complementConstantRationalInjectiveResolution structureMap Z).cocomplex.extend
    ComplexShape.embeddingUpNat
  let : Mono a := complementConstantsToSingularCochainInt_mono structureMap Z
  let : QuasiIso a :=
    complementConstantsToSingularCochainInt_quasiIso structureMap Z hZ
  have hI : ∀ n : ℤ, Injective (I.X n) := by
    intro n
    dsimp [I]
    infer_instance
  exact CochainComplex.liftToInjective a r hI

set_option linter.style.haveILetI false in
lemma complementConstants_comp_singularToInjectiveResolutionInt
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) :
    complementConstantsToSingularCochainInt structureMap Z ≫
        complementSingularToInjectiveResolutionInt structureMap Z hZ =
      complementResolutionMapInt structureMap Z := by
  let a := complementConstantsToSingularCochainInt structureMap Z
  let r := complementResolutionMapInt structureMap Z
  let I := (complementConstantRationalInjectiveResolution structureMap Z).cocomplex.extend
    ComplexShape.embeddingUpNat
  let : Mono a := complementConstantsToSingularCochainInt_mono structureMap Z
  let : QuasiIso a :=
    complementConstantsToSingularCochainInt_quasiIso structureMap Z hZ
  have hI : ∀ n : ℤ, Injective (I.X n) := by
    intro n
    dsimp [I]
    infer_instance
  exact CochainComplex.comp_liftToInjective a r hI

def complementSingularToInjectiveResolution
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) :
    complementSingularCochainSheafComplex structureMap Z ⟶
      (complementConstantRationalInjectiveResolution structureMap Z).cocomplex :=
  (ComplexShape.embeddingUpNat.fullyFaithfulExtendFunctor
    (AnalyticComplementAdditiveSheaf structureMap Z)).preimage
      (complementSingularToInjectiveResolutionInt structureMap Z hZ)

lemma complementConstants_comp_singularToInjectiveResolution
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) :
    complementConstantsToSingularCochain structureMap Z ≫
        complementSingularToInjectiveResolution structureMap Z hZ =
      (complementConstantRationalInjectiveResolution structureMap Z).ι := by
  let E := ComplexShape.embeddingUpNat.extendFunctor
    (AnalyticComplementAdditiveSheaf structureMap Z)
  apply E.map_injective
  change HomologicalComplex.extendMap
      (complementConstantsToSingularCochain structureMap Z ≫
        complementSingularToInjectiveResolution structureMap Z hZ)
        ComplexShape.embeddingUpNat =
    HomologicalComplex.extendMap
      (complementConstantRationalInjectiveResolution structureMap Z).ι
        ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_comp]
  rw [show HomologicalComplex.extendMap
      (complementSingularToInjectiveResolution structureMap Z hZ)
        ComplexShape.embeddingUpNat =
      complementSingularToInjectiveResolutionInt structureMap Z hZ by
    exact (ComplexShape.embeddingUpNat.fullyFaithfulExtendFunctor
      (AnalyticComplementAdditiveSheaf structureMap Z)).map_preimage _]
  exact complementConstants_comp_singularToInjectiveResolutionInt
    structureMap Z hZ

set_option linter.style.haveILetI false in
lemma complementSingularToInjectiveResolutionInt_quasiIso
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) :
    QuasiIso (complementSingularToInjectiveResolutionInt structureMap Z hZ) := by
  let a := complementConstantsToSingularCochainInt structureMap Z
  let b := complementSingularToInjectiveResolutionInt structureMap Z hZ
  let r := complementResolutionMapInt structureMap Z
  let : QuasiIso a :=
    complementConstantsToSingularCochainInt_quasiIso structureMap Z hZ
  have hr : QuasiIso r := by
    apply (HomologicalComplex.quasiIso_extendMap_iff
      (complementConstantRationalInjectiveResolution structureMap Z).ι
        ComplexShape.embeddingUpNat).mpr
    infer_instance
  have hab : a ≫ b = r :=
    complementConstants_comp_singularToInjectiveResolutionInt structureMap Z hZ
  let : QuasiIso (a ≫ b) := hab ▸ hr
  exact quasiIso_of_comp_left a b

lemma complementSingularToInjectiveResolution_quasiIso
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) :
    QuasiIso (complementSingularToInjectiveResolution structureMap Z hZ) := by
  apply (HomologicalComplex.quasiIso_extendMap_iff
    (complementSingularToInjectiveResolution structureMap Z hZ)
      ComplexShape.embeddingUpNat).mp
  rw [show HomologicalComplex.extendMap
      (complementSingularToInjectiveResolution structureMap Z hZ)
        ComplexShape.embeddingUpNat =
      complementSingularToInjectiveResolutionInt structureMap Z hZ by
    exact (ComplexShape.embeddingUpNat.fullyFaithfulExtendFunctor
      (AnalyticComplementAdditiveSheaf structureMap Z)).map_preimage _]
  exact complementSingularToInjectiveResolutionInt_quasiIso structureMap Z hZ

def naturalSingularResolutionRestrictionNat
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) :
    singularCochainSheafComplex ℚ (TopCat.of (ComplexPoint X structureMap)) ⟶
      derivedPushforwardComplementConstantRationalComplexNat structureMap Z :=
  singularRestrictionSheafComplex ℚ
      (analyticComplementInclusion structureMap Z) ≫
    ((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticComplementInclusion structureMap Z)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
      (complementSingularToInjectiveResolution structureMap Z hZ)

def naturalSingularResolutionRestriction
    [IsIntegral X] [Smooth structureMap]
    (Z : Set (ComplexPoint X structureMap)) (hZ : IsClosed Z) :
    singularCochainSheafComplexInt structureMap ℚ ⟶
      derivedPushforwardComplementConstantRationalComplexInt structureMap Z :=
  HomologicalComplex.extendMap
    (naturalSingularResolutionRestrictionNat structureMap Z hZ)
      ComplexShape.embeddingUpNat

end AlgebraicGeometry.ComplexPoint
