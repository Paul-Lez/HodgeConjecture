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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.CohomologyFlasqueModel
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportedInjectiveModel
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.AmbientInjectiveResolution
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.SupportedSingularModel
public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.OpenRestrictedLowestCohomology
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularCohomologySheafComparison
public import HodgeConjecture.Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

/-!
# Cohomology of the analytic space with support in a closed set

`H^n_Z(X(ℂ); K)` is the sheaf cohomology of `X(ℂ)` with support in the closed set `Z` and
coefficients in the constant sheaf `K`. Forgetting the support lands in `H^n(X(ℂ); K)`. With
rational coefficients it is compared with the sheafified relative singular cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (K : Type) [Field K] (X : Over (Spec ↧ℂ))

local instance withSupportAnalyticHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

local instance withSupportAdditiveGroupsHasDerivedCategory :
    HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard AddCommGrpCat

local instance withSupportModuleHasDerivedCategory :
    HasDerivedCategory (ModuleCat K) :=
  HasDerivedCategory.standard _

local instance withSupportModuleSheafHasDerivedCategory :
    HasDerivedCategory
      (TopCat.Sheaf (ModuleCat K) (TopCat.of (ComplexPoint X))) :=
  HasDerivedCategory.standard _

set_option quotPrecheck false in
/-- `H_[Z]^n(X; K)` is the sheaf cohomology of the analytic space `X(ℂ)` with support in the closed
set `Z ⊆ X(ℂ)` and coefficients in the constant sheaf `K`, in degree `n`. -/
scoped notation:max "H_[" Z "]^" n:max "(" X "; " K ")" =>
  TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) Z
    ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of K)) n

variable (Z : Closeds (ComplexPoint X))

noncomputable def moduleInjectiveResolutionComplex :
    CochainComplex
      (TopCat.Sheaf (ModuleCat K) (TopCat.of (ComplexPoint X))) ℤ :=
  (injectiveResolution (C := TopCat.Sheaf (ModuleCat K) (TopCat.of (ComplexPoint X)))
    (constantModuleSheaf X K)).cocomplex.extend ComplexShape.embeddingUpNat

instance moduleInjectiveResolutionComplex_injective (q : ℤ) :
    Injective ((moduleInjectiveResolutionComplex K X).X q) :=
  CochainComplex.injective_extend_nat _
    (injectiveResolution (C := TopCat.Sheaf (ModuleCat K) (TopCat.of (ComplexPoint X)))
      (constantModuleSheaf X K)).injective q

instance moduleInjectiveResolutionComplex_isStrictlyGE :
    (moduleInjectiveResolutionComplex K X).IsStrictlyGE 0 := by
  dsimp only [moduleInjectiveResolutionComplex]
  infer_instance

instance moduleInjectiveResolutionComplex_isKInjective :
    (moduleInjectiveResolutionComplex K X).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ 0

def moduleInjectiveResolutionAugmentation :
    (constantModuleSheafComplexIntPlus X K).obj ⟶ moduleInjectiveResolutionComplex K X :=
  HomologicalComplex.extendMap
    (injectiveResolution (C := TopCat.Sheaf (ModuleCat K)
      (TopCat.of (ComplexPoint X))) (constantModuleSheaf X K)).ι
    ComplexShape.embeddingUpNat

instance moduleInjectiveResolutionAugmentation_quasiIso :
    QuasiIso (moduleInjectiveResolutionAugmentation K X) := by
  dsimp only [moduleInjectiveResolutionAugmentation]
  have h : QuasiIso (HomologicalComplex.extendMap
      (injectiveResolution (C := TopCat.Sheaf (ModuleCat K)
        (TopCat.of (ComplexPoint X))) (constantModuleSheaf X K)).ι
      ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr inferInstance
  exact h

instance moduleInjectiveResolutionAugmentation_mono :
    Mono (moduleInjectiveResolutionAugmentation K X) := by
  dsimp only [moduleInjectiveResolutionAugmentation]
  let a := (injectiveResolution (C := TopCat.Sheaf (ModuleCat K)
    (TopCat.of (ComplexPoint X))) (constantModuleSheaf X K)).ι
  have : Mono a := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    infer_instance
  exact CochainComplex.mono_extendMap_nat a

abbrev moduleInjectiveResolutionComplexPlus :
    CochainComplex.Plus
      (TopCat.Sheaf (ModuleCat K) (TopCat.of (ComplexPoint X))) :=
  ⟨moduleInjectiveResolutionComplex K X, ⟨0, inferInstance⟩⟩

def moduleInjectiveResolutionAugmentationPlus :
    constantModuleSheafComplexIntPlus X K ⟶ moduleInjectiveResolutionComplexPlus K X :=
  ⟨moduleInjectiveResolutionAugmentation K X⟩

noncomputable abbrev moduleForgetSheaf :
    TopCat.Sheaf (ModuleCat K) (TopCat.of (ComplexPoint X)) ⥤
      TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X)) :=
  CategoryTheory.sheafCompose (Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X)))
      (forget₂ (ModuleCat.{0} K) AddCommGrpCat.{0})

instance moduleForgetSheaf_additive :
    (moduleForgetSheaf K X).Additive := by
  dsimp only [moduleForgetSheaf]
  exact ModuleCatSheafification.moduleCat_sheafCompose_additive
    (J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) (R := K)

instance moduleForgetSheaf_preservesFiniteLimits :
    PreservesFiniteLimits (moduleForgetSheaf K X) := by
  dsimp only [moduleForgetSheaf]
  exact ModuleCatSheafification.moduleCat_sheafCompose_preservesFiniteLimits
    (J := Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) (R := K)

instance moduleForgetSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (moduleForgetSheaf K X) := by
  exact CategoryTheory.Sheaf.moduleForget_preservesFiniteColimits _
    (ModuleCatSheafification.integerForget_sheafCompose_preservesFiniteColimits _)

abbrev freeModuleYonedaSheaf :
    Opens (TopCat.of (ComplexPoint X)) ⥤
      TopCat.Sheaf (ModuleCat K) (TopCat.of (ComplexPoint X)) :=
  yoneda ⋙
    (Functor.whiskeringRight (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ
      (Type) (ModuleCat K)).obj (ModuleCat.free K) ⋙
    presheafToSheaf (Opens.grothendieckTopology
      (TopCat.of (ComplexPoint X))) (ModuleCat K)

instance moduleFree_preservesMonomorphisms :
    (ModuleCat.free K).PreservesMonomorphisms where
  preserves {X Y} f := by
    intro
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective (Finsupp.mapDomain f : (X →₀ K) → (Y →₀ K))
    exact Finsupp.mapDomain_injective
      (CategoryTheory.mono_iff_injective f |>.mp inferInstance)

def freeModuleYonedaSheafHomEquiv
    (U : Opens (TopCat.of (ComplexPoint X)))
    (F : TopCat.Sheaf (ModuleCat K) (TopCat.of (ComplexPoint X))) :
    ((freeModuleYonedaSheaf K X).obj U ⟶ F) ≃ F.presheaf.obj (op U) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology
      (TopCat.of (ComplexPoint X))) (ModuleCat K)).homEquiv _ _).trans <|
    ((ModuleCat.adj K).whiskerRight
      (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).homEquiv _ _ |>.trans yonedaEquiv

set_option backward.isDefEq.respectTransparency false in
lemma freeModuleYonedaSheafHomEquiv_naturality
    {U V : Opens (TopCat.of (ComplexPoint X))} (i : V ⟶ U)
    (F : TopCat.Sheaf (ModuleCat K) (TopCat.of (ComplexPoint X)))
    (g : (freeModuleYonedaSheaf K X).obj U ⟶ F) :
    freeModuleYonedaSheafHomEquiv K X V F
        ((freeModuleYonedaSheaf K X).map i ≫ g) =
      F.presheaf.map i.op (freeModuleYonedaSheafHomEquiv K X U F g) := by
  change yonedaEquiv
      (((ModuleCat.adj K).whiskerRight
        (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).homEquiv _ _
          (((sheafificationAdjunction (Opens.grothendieckTopology
            (TopCat.of (ComplexPoint X))) (ModuleCat K)).homEquiv _ _)
              ((presheafToSheaf (Opens.grothendieckTopology
                (TopCat.of (ComplexPoint X))) (ModuleCat K)).map
                (((Functor.whiskeringRight
                  (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ (Type)
                  (ModuleCat K)).obj (ModuleCat.free K)).map (yoneda.map i)) ≫ g))) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ i).symm

instance moduleInjectiveResolutionForget_isFlasque (q : ℤ) :
    TopCat.Sheaf.IsFlasque
      ((moduleForgetSheaf K X).obj ((moduleInjectiveResolutionComplex K X).X q)) := by
  let F := (moduleInjectiveResolutionComplex K X).X q
  constructor
  intro U V i
  rw [AddCommGrpCat.epi_iff_surjective]
  intro s
  let A := freeModuleYonedaSheaf K X
  let gV : A.obj V.unop ⟶ F :=
    (freeModuleYonedaSheafHomEquiv K X V.unop F).symm s
  let a : A.obj V.unop ⟶ A.obj U.unop := A.map i.unop
  let : Mono a := by
    let W := (Functor.whiskeringRight
      (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ (Type) (ModuleCat K)).obj
        (ModuleCat.free K)
    let S := presheafToSheaf (Opens.grothendieckTopology
      (TopCat.of (ComplexPoint X))) (ModuleCat K)
    change Mono (S.map (W.map (yoneda.map i.unop)))
    let : Mono (yoneda.map i.unop) := Functor.map_mono yoneda i.unop
    let : Mono (W.map (yoneda.map i.unop)) := Functor.map_mono W (yoneda.map i.unop)
    exact Functor.map_mono S (W.map (yoneda.map i.unop))
  let gU : A.obj U.unop ⟶ F := Injective.factorThru gV a
  refine ⟨freeModuleYonedaSheafHomEquiv K X U.unop F gU, ?_⟩
  change F.presheaf.map i (freeModuleYonedaSheafHomEquiv K X U.unop F gU) = s
  rw [show F.presheaf.map i (freeModuleYonedaSheafHomEquiv K X U.unop F gU) =
      freeModuleYonedaSheafHomEquiv K X V.unop F (a ≫ gU) by
    simpa only [a, A, Quiver.Hom.op_unop] using
      (freeModuleYonedaSheafHomEquiv_naturality K X i.unop F gU).symm]
  rw [Injective.comp_factorThru]
  change freeModuleYonedaSheafHomEquiv K X V.unop F
    ((freeModuleYonedaSheafHomEquiv K X V.unop F).symm s) = s
  exact (freeModuleYonedaSheafHomEquiv K X V.unop F).apply_symm_apply s

noncomputable abbrev moduleInjectiveResolutionForgetComplex :
    CochainComplex
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) ℤ :=
  ((moduleForgetSheaf K X).mapHomologicalComplex ℤᵘᵖ).obj
    (moduleInjectiveResolutionComplex K X)

instance constantModuleSheafForgetComplexIso_inv_hom_isIso :
    IsIso ((constantModuleSheafForgetComplexIso X K).inv.hom) :=
  (ObjectProperty.isIso_hom_iff _).2
    (constantModuleSheafForgetComplexIso X K).isIso_inv

noncomputable def moduleInjectiveResolutionForgetAugmentationPlain :
    (CochainComplex.singleFunctor
        (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) 0).obj
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of K)) ⟶
      moduleInjectiveResolutionForgetComplex K X :=
  (constantFieldSheafComplexIntIsoSingle K X).inv ≫
    (constantModuleSheafForgetComplexIso X K).inv.hom ≫
    ((moduleForgetSheaf K X).mapHomologicalComplex ℤᵘᵖ).map
      (moduleInjectiveResolutionAugmentation K X)

instance moduleInjectiveResolutionForgetAugmentationPlain_mono :
    Mono (moduleInjectiveResolutionForgetAugmentationPlain K X) := by
  dsimp only [moduleInjectiveResolutionForgetAugmentationPlain]
  let a := (constantFieldSheafComplexIntIsoSingle K X).inv
  let b := (constantModuleSheafForgetComplexIso X K).inv.hom
  let c := ((moduleForgetSheaf K X).mapHomologicalComplex ℤᵘᵖ).map
    (moduleInjectiveResolutionAugmentation K X)
  have ha : Mono a := by dsimp only [a]; infer_instance
  have hb : Mono b := by dsimp only [b]; infer_instance
  have hc : Mono c := Functor.map_mono _ _
  have hab : Mono (a ≫ b) :=
    @CategoryTheory.mono_comp _ _ _ _ _ a ha b hb
  exact @CategoryTheory.mono_comp _ _ _ _ _ (a ≫ b) hab c hc

instance moduleInjectiveResolutionForgetAugmentationPlain_quasiIso :
    QuasiIso (moduleInjectiveResolutionForgetAugmentationPlain K X) := by
  dsimp only [moduleInjectiveResolutionForgetAugmentationPlain]
  let a := (constantFieldSheafComplexIntIsoSingle K X).inv
  let b := (constantModuleSheafForgetComplexIso X K).inv.hom
  let c := ((moduleForgetSheaf K X).mapHomologicalComplex ℤᵘᵖ).map
    (moduleInjectiveResolutionAugmentation K X)
  have ha : QuasiIso a := quasiIso_of_isIso _
  have hb : QuasiIso b := quasiIso_of_isIso _
  have hc : QuasiIso c :=
    HomologicalComplex.quasiIso_map_of_preservesHomology
      (moduleInjectiveResolutionAugmentation K X) (moduleForgetSheaf K X)
  have hab : QuasiIso (a ≫ b) :=
    @quasiIso_comp _ _ _ _ _ _ _ _ a b _ _ _ ha hb
  exact @quasiIso_comp _ _ _ _ _ _ _ _ (a ≫ b) c _ _ _ hab hc

noncomputable def forgetSupportToModuleGlobalSectionsHomology (n : ℕ) :
    H_[Z]^n(X; K) →+
      (TopCat.Sheaf.globalSectionsComplex (TopCat.of (ComplexPoint X))
        (moduleInjectiveResolutionForgetComplex K X)).homology n :=
  letI Y := TopCat.of (ComplexPoint X)
  letI F := (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of K)
  letI S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y Z.compl ⊤
    (moduleInjectiveResolutionForgetComplex K X)
  letI e := @TopCat.Sheaf.relHAddEquivSupportedSectionsHomologyOfFlasque Y F
    (moduleInjectiveResolutionForgetComplex K X)
    (inferInstance : (moduleInjectiveResolutionForgetComplex K X).IsStrictlyGE 0)
    (moduleInjectiveResolutionForgetAugmentationPlain K X)
    (inferInstance : Mono (moduleInjectiveResolutionForgetAugmentationPlain K X))
    (inferInstance : QuasiIso (moduleInjectiveResolutionForgetAugmentationPlain K X))
    Z.compl ⊤ Z.compl (top_inf_eq _)
    (fun q => moduleInjectiveResolutionForget_isFlasque K X q) inferInstance n
  (HomologicalComplex.homologyMap S.f n).hom.comp e.toAddMonoidHom

noncomputable def moduleGlobalSectionsHomologyToHypercohomology (n : ℕ) :
    (TopCat.Sheaf.globalSectionsComplex (TopCat.of (ComplexPoint X))
      (moduleInjectiveResolutionForgetComplex K X)).homology n ≃+
      H^n(X; K) :=
  letI Y := TopCat.of (ComplexPoint X)
  letI : QuasiIso (moduleInjectiveResolutionAugmentationPlus K X).hom :=
    moduleInjectiveResolutionAugmentation_quasiIso K X
  letI e := TopCat.Sheaf.hypercohomologyIsoOfQuasiIsoToInjective
    (ModuleCat K) Y (moduleInjectiveResolutionAugmentationPlus K X) n
  letI G := TopCat.Sheaf.globalSectionsComplex Y (moduleInjectiveResolutionComplex K X)
  letI h := TopCat.Sheaf.homologicalComplexChangeOfFunctorIso
    (forget₂ (ModuleCat K) AddCommGrpCat) n
  (h.app G).addCommGroupIsoToAddEquiv.trans
    (((forget₂ (ModuleCat K) AddCommGrpCat).mapIso e.symm).addCommGroupIsoToAddEquiv)

/-- The additive map
`H_[Z]^n(X(ℂ); K) → H^n(Γ(X(ℂ), I(K)))` from cohomology with support in `Z` to the
degree-`n` homology of the global-sections complex of the injective resolution `I(K)` of the
constant sheaf `K`. It is induced by the inclusion of sections supported in `Z` into all global
sections. -/
def forgetSupportToGlobalSectionsHomology (n : ℕ) :
    H_[Z]^n(X; K) →+
      (TopCat.Sheaf.globalSectionsComplex (TopCat.of (ComplexPoint X))
        (TopCat.Sheaf.injectiveResolutionComplex
          (TopCat.of (ComplexPoint X))
          ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
            (AddCommGrpCat.of K)))).homology n :=
  letI Y := TopCat.of (ComplexPoint X)
  letI F := (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of K)
  letI I := TopCat.Sheaf.injectiveResolutionComplex Y F
  letI S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y Z.compl ⊤ I
  letI e := @TopCat.Sheaf.relHAddEquivSupportedSectionsHomology Y Z.compl ⊤ Z.compl
    (top_inf_eq _) inferInstance F I
    (TopCat.Sheaf.injectiveResolutionComplex_isKInjective Y F)
    (TopCat.Sheaf.injectiveResolutionAugmentation Y F)
    (TopCat.Sheaf.injectiveResolutionAugmentation_quasiIso Y F) n
  (HomologicalComplex.homologyMap S.f n).hom.comp e.toAddMonoidHom

set_option maxHeartbeats 1000000 in
/-- The map from cohomology with support to the global sections of the forgotten module resolution
agrees with the map obtained from the additive injective resolution. -/
lemma forgetSupportToModuleGlobalSectionsHomology_resolutionToInjective
    (n : ℕ) (x : H_[Z]^n(X; K)) :
    letI Y := TopCat.of (ComplexPoint X)
    letI F := (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of K)
    letI K' := moduleInjectiveResolutionForgetComplex K X
    letI i := moduleInjectiveResolutionForgetAugmentationPlain K X
    letI q := TopCat.Sheaf.resolutionToInjective Y F K' i
    HomologicalComplex.homologyMap
        (((TopCat.Sheaf.globalSections AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ).map q)
        n (forgetSupportToModuleGlobalSectionsHomology K X Z n x) =
      forgetSupportToGlobalSectionsHomology K X Z n x := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let F := (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of K)
  let K' := moduleInjectiveResolutionForgetComplex K X
  let i := moduleInjectiveResolutionForgetAugmentationPlain K X
  let q := TopCat.Sheaf.resolutionToInjective Y F K' i
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y Z.compl ⊤ K'
  let T := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y Z.compl ⊤
    (TopCat.Sheaf.injectiveResolutionComplex Y F)
  let s : S.X₁ ⟶ T.X₁ :=
    ((TopCat.Sheaf.supportEvaluation Y ⊤).mapHomologicalComplex ℤᵘᵖ).map
    (((TopCat.Sheaf.sheafSectionsSupportedOutside Y Z.compl).mapHomologicalComplex ℤᵘᵖ).map q)
  let g : S.X₂ ⟶ T.X₂ :=
    ((TopCat.Sheaf.globalSections AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ).map q
  let e : _ ≃+ T.X₁.homology n :=
    @TopCat.Sheaf.relHAddEquivSupportedSectionsHomology Y Z.compl ⊤ Z.compl
    (top_inf_eq _) inferInstance F (TopCat.Sheaf.injectiveResolutionComplex Y F)
    (TopCat.Sheaf.injectiveResolutionComplex_isKInjective Y F)
    (TopCat.Sheaf.injectiveResolutionAugmentation Y F)
    (TopCat.Sheaf.injectiveResolutionAugmentation_quasiIso Y F) n
  have hnat : S.f ≫ g = s ≫ T.f := by
    apply HomologicalComplex.Hom.ext
    funext j
    change (TopCat.Sheaf.supportEvaluation Y ⊤).map
          ((TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y Z.compl).app (K'.X j)) ≫
        (TopCat.Sheaf.supportEvaluation Y ⊤).map (q.f j) =
      (TopCat.Sheaf.supportEvaluation Y ⊤).map
          ((TopCat.Sheaf.sheafSectionsSupportedOutside Y Z.compl).map (q.f j)) ≫
        (TopCat.Sheaf.supportEvaluation Y ⊤).map
          ((TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y Z.compl).app
            ((TopCat.Sheaf.injectiveResolutionComplex Y F).X j))
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg ((TopCat.Sheaf.supportEvaluation Y ⊤).map)
      ((TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y Z.compl).naturality (q.f j)).symm
  have hnatH :
      HomologicalComplex.homologyMap (S.f ≫ g) n =
        HomologicalComplex.homologyMap (s ≫ T.f) n :=
    congrArg (fun k : S.X₁ ⟶ T.X₂ => HomologicalComplex.homologyMap k n) hnat
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hnatH
  have : QuasiIso s := by
    dsimp only [s]
    exact TopCat.Sheaf.supportedSections_map_resolutionToInjective_quasiIso
      Y F K' i Z.compl ⊤ (fun j => moduleInjectiveResolutionForget_isFlasque K X j)
  dsimp [forgetSupportToModuleGlobalSectionsHomology,
    forgetSupportToGlobalSectionsHomology,
    TopCat.Sheaf.relHAddEquivSupportedSectionsHomologyOfFlasque]
  change (HomologicalComplex.homologyMap g n).hom
      ((HomologicalComplex.homologyMap S.f n).hom
        ((inv (HomologicalComplex.homologyMap s n)).hom (e x))) =
    (HomologicalComplex.homologyMap T.f n).hom (e x)
  rw [show (HomologicalComplex.homologyMap g n).hom
        ((HomologicalComplex.homologyMap S.f n).hom
          ((inv (HomologicalComplex.homologyMap s n)).hom (e x))) =
      (HomologicalComplex.homologyMap T.f n).hom
        ((HomologicalComplex.homologyMap s n).hom
          ((inv (HomologicalComplex.homologyMap s n)).hom (e x))) from
    ConcreteCategory.congr_hom hnatH _]
  exact congrArg (HomologicalComplex.homologyMap T.f n).hom <|
    ConcreteCategory.congr_hom
      (IsIso.inv_hom_id (HomologicalComplex.homologyMap s n)) (e x)

/-- `H_[Z]^n(X(ℂ); K) → H^n(X(ℂ); K)`, forgetting the support. -/
def forgetSupport (n : ℕ) : H_[Z]^n(X; K) →+ H^n(X; K) :=
  (moduleGlobalSectionsHomologyToHypercohomology K X n).toAddMonoidHom.comp
    (forgetSupportToModuleGlobalSectionsHomology K X Z n)

/-- Forgetting the support `X(ℂ)` itself is injective. -/
lemma forgetSupport_injective_of_eq_top (hZ : Z = ⊤) (n : ℕ) :
    Function.Injective (forgetSupport K X Z n) := by
  subst Z
  let Y := TopCat.of (ComplexPoint X)
  let F := (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of K)
  let K' := moduleInjectiveResolutionForgetComplex K X
  let U : Opens Y := (⊤ : Closeds (ComplexPoint X)).compl
  let S := TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex Y U ⊤ K'
  let (i : ℤ) : IsIso (S.f.f i) := by
    dsimp [S, U, TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex,
      TopCat.Sheaf.supportRestrictionComplexShortComplex]
    have hU : (⊤ : Closeds (ComplexPoint X)).compl = (⊥ : Opens Y) := by
      ext
      simp
    rw [hU]
    change IsIso ((TopCat.Sheaf.supportEvaluation Y ⊤).map
      ((TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y ⊥).app (K'.X i)))
    let : IsIso ((TopCat.Sheaf.sheafSectionsSupportedOutsideInclusion Y ⊥).app (K'.X i)) := by
      change IsIso (kernel.ι ((TopCat.Sheaf.toOpenRestrictionPushforward Y ⊥).app (K'.X i)))
      rw [(TopCat.Sheaf.isZero_openRestrictionPushforward_bot Y (K'.X i)).eq_zero_of_tgt
        ((TopCat.Sheaf.toOpenRestrictionPushforward Y ⊥).app (K'.X i))]
      infer_instance
    exact Functor.map_isIso _ _
  let : IsIso S.f := HomologicalComplex.Hom.isIso_of_components S.f
  let e := @TopCat.Sheaf.relHAddEquivSupportedSectionsHomologyOfFlasque Y F K'
    (inferInstance : K'.IsStrictlyGE 0) (moduleInjectiveResolutionForgetAugmentationPlain K X)
    (inferInstance : Mono (moduleInjectiveResolutionForgetAugmentationPlain K X))
    (inferInstance : QuasiIso (moduleInjectiveResolutionForgetAugmentationPlain K X))
    U ⊤ U (top_inf_eq _)
    (fun q => moduleInjectiveResolutionForget_isFlasque K X q) inferInstance n
  have hSupported :
      Function.Injective
        (forgetSupportToModuleGlobalSectionsHomology K X (⊤ : Closeds (ComplexPoint X)) n) := by
    change Function.Injective ((HomologicalComplex.homologyMap S.f n).hom.comp e.toAddMonoidHom)
    exact ((AddCommGrpCat.mono_iff_injective _).mp inferInstance).comp e.injective
  dsimp [forgetSupport]
  exact (moduleGlobalSectionsHomologyToHypercohomology K X n).injective.comp hSupported

section Rational

variable [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- If the lower relative cohomology sheaves with support in `S` vanish, this identifies
`H_[S]^n(X; ℚ)` with the global sections of `𝓗_[S]^n(X; ℚ)`. -/
def rationalSupportAddEquivSupportedGlobalSheafSection
    (S : Closeds (ComplexPoint X)) (n : ℕ)
    (hH : ∀ j : ℕ, j < n → IsZero (𝓗_[S]^j(TopCat.of (ComplexPoint X); ℚ))) :
  H_[S]^n(X; ℚ) ≃+
      (𝓗_[S]^n(TopCat.of (ComplexPoint X); ℚ)).presheaf.obj (op ⊤) :=
  rationalSupportAddEquivSupportedRelativeCohomologySheafSection X S n hH

end Rational

end AlgebraicGeometry.ComplexPoint

end
