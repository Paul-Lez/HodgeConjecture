/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RelativeChernFrameRestriction

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CochainComplex.HomComplex
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
local instance originalRestrictionTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

variable (E : HolomorphicUnitExtension X d)
  (U : Opens (TopCat.of (ComplexPoint X)))
  (ℓU : E.middle.obj.obj (op U))
  (hℓU : E.projection.hom.app (op U) ℓU =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : U ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)

/-- The map from the restricted constant complex into the restricted inclusion cone induced by a
local lift of `1`.  The mapping-cone isomorphism is retained explicitly because restriction does
not commute definitionally with the cone construction. -/
def restrictedConeSection :
    ((restrictToOpen X U).mapHomologicalComplex (.up ℤ)).obj
        ((analyticSingleFunctor X).obj (𝓒(↧(ComplexPoint X); ℤ))) ⟶
      ((restrictToOpen X U).mapHomologicalComplex (.up ℤ)).obj E.inclusionCone :=
  (HomologicalComplex.singleMapHomologicalComplex (restrictToOpen X U) (.up ℤ) 0).hom.app
      (𝓒(↧(ComplexPoint X); ℤ)) ≫
  (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0).map
      (E.restrictedSection U ℓU) ≫
  (HomologicalComplex.singleMapHomologicalComplex (restrictToOpen X U) (.up ℤ) 0).inv.app
      E.middle ≫
    CochainComplex.mappingCone.inr
      (((restrictToOpen X U).mapHomologicalComplex (.up ℤ)).map E.singleShortComplex.f) ≫
    (CochainComplex.mappingCone.mapHomologicalComplexIso E.singleShortComplex.f
      (restrictToOpen X U)).inv

include hℓU in
lemma restrictedConeSection_comp_coneToInteger :
    restrictedConeSection X d E U ℓU ≫
      ((restrictToOpen X U).mapHomologicalComplex (.up ℤ)).map E.coneToInteger =
      𝟙 _ := by
  unfold restrictedConeSection
  let F := restrictToOpen X U
  let H := F.mapHomologicalComplex (.up ℤ)
  let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let C := CochainComplex.mappingCone.mapHomologicalComplexIso E.singleShortComplex.f F
  let D := CochainComplex.mappingCone.descShortComplex (E.singleShortComplex.map H)
  have hCD : C.hom ≫ D = H.map E.coneToInteger := by
    exact CochainComplex.mappingCone.mapHomologicalComplexIso_hom_descShortComplex
      (F := F) E.singleShortComplex
  have hcone : C.inv ≫ H.map E.coneToInteger = D := by
    rw [← hCD, Iso.inv_hom_id_assoc]
  have hD : CochainComplex.mappingCone.inr (H.map E.singleShortComplex.f) ≫ D =
      H.map E.singleShortComplex.g := by
    exact CochainComplex.mappingCone.inr_descShortComplex (E.singleShortComplex.map H)
  change I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫
      (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0).map
        (E.restrictedSection U ℓU) ≫
      I.inv.app E.middle ≫ CochainComplex.mappingCone.inr (H.map E.singleShortComplex.f) ≫
      C.inv ≫ H.map E.coneToInteger = 𝟙 _
  rw [hcone]
  rw [hD]
  have hnat := I.inv.naturality E.projection
  have hproj : I.inv.app E.middle ≫ H.map E.singleShortComplex.g =
      (F ⋙ HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat (TopCat.of U))
        (.up ℤ) 0).map E.projection ≫ I.inv.app (𝓒(↧(ComplexPoint X); ℤ)) := by
    exact hnat.symm
  have hsingle :
      (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0).map
          (F.map E.projection) =
        (F ⋙ HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat (TopCat.of U))
          (.up ℤ) 0).map E.projection := by
    rfl
  rw [hproj, ← hsingle]
  simp only [Functor.comp_obj]
  have hj :
      (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0).map
          (E.restrictedSection U ℓU) =
        (HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat (TopCat.of U))
          (.up ℤ) 0).map (E.restrictedSection U ℓU) := by
    rfl
  rw [hj]
  have hj2 :
      (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0).map
          (F.map E.projection) =
        (HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat (TopCat.of U))
          (.up ℤ) 0).map (F.map E.projection) := by
    rfl
  rw [hj2]
  have hmap2 := (HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat (TopCat.of U))
    (.up ℤ) 0).map_comp (E.restrictedSection U ℓU) (F.map E.projection)
  have hmap2' := congrArg (fun k ↦
      I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫ k ≫
        I.inv.app (𝓒(↧(ComplexPoint X); ℤ))) hmap2
  calc
    _ = I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫
        (HomologicalComplex.single (TopCat.Sheaf AddCommGrpCat (TopCat.of U))
          (.up ℤ) 0).map (E.restrictedSection U ℓU ≫ F.map E.projection) ≫
          I.inv.app (𝓒(↧(ComplexPoint X); ℤ)) := by
      simpa only [Category.assoc] using hmap2'.symm
    _ = _ := by
      rw [E.restrictedSection_comp_projection U ℓU hℓU]
      rw [CategoryTheory.Functor.map_id]
      exact (congrArg
        (fun f ↦ I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫ f)
        (Category.id_comp (I.inv.app (𝓒(↧(ComplexPoint X); ℤ))))).trans
        (I.hom_inv_id_app (𝓒(↧(ComplexPoint X); ℤ)))

variable (Ω : Opens (TopCat.of (ComplexPoint X)))
  (ℓΩ : E.middle.obj.obj (op Ω))
  (hℓΩ : E.projection.hom.app (op Ω) ℓΩ =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)

include hℓΩ in
lemma restrictedConeSection_comp_relativeConeMap :
    let F := restrictToOpen X U
    let H := F.mapHomologicalComplex (.up ℤ)
    let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
    let J := CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0
    restrictedConeSection X d E U ℓU ≫
        H.map (E.relativeConeMap Ω ℓΩ hℓΩ) =
      I.hom.app (𝓒(↧(ComplexPoint X); ℤ)) ≫
        J.map (E.restrictedSection U ℓU) ≫ I.inv.app E.middle ≫
        H.map ((analyticSingleFunctor X).map
          (E.restrictionFactorisation Ω ℓΩ hℓΩ)) ≫
        H.map (CochainComplex.mappingCone.inr
          ((analyticSingleFunctor X).map
            (restrictionUnit Ω (holomorphicUnitSheaf X d)))) := by
  dsimp only
  let F := restrictToOpen X U
  let H := F.mapHomologicalComplex (.up ℤ)
  let I := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let J := CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0
  unfold restrictedConeSection HolomorphicUnitExtension.relativeConeMap
  have hI :
      CochainComplex.mappingCone.inr
          (((restrictToOpen X U).mapHomologicalComplex (.up ℤ)).map E.singleShortComplex.f) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso E.singleShortComplex.f
          (restrictToOpen X U)).inv =
      ((restrictToOpen X U).mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCone.inr E.singleShortComplex.f) := by
    rw [← CochainComplex.mappingCone.map_inr E.singleShortComplex.f F]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have htrail :
      CochainComplex.mappingCone.inr
          (H.map E.singleShortComplex.f) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso E.singleShortComplex.f
          (restrictToOpen X U)).inv ≫
        H.map
          (CochainComplex.mappingCone.map E.singleShortComplex.f
            ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d)))
            (𝟙 E.singleShortComplex.X₁)
            ((analyticSingleFunctor X).map (E.restrictionFactorisation Ω ℓΩ hℓΩ))
            (E.singleShortComplex_f_comp_restrictionFactorisation Ω ℓΩ hℓΩ)) =
      H.map
          ((analyticSingleFunctor X).map (E.restrictionFactorisation Ω ℓΩ hℓΩ)) ≫
        H.map
          (CochainComplex.mappingCone.inr
            ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d)))) := by
    rw [← Category.assoc, hI, ← H.map_comp]
    simp [CochainComplex.mappingCone.map]
  have hp := congrArg (fun q ↦
    ((HomologicalComplex.singleMapHomologicalComplex (restrictToOpen X U) (.up ℤ) 0).hom.app
        (𝓒(↧(ComplexPoint X); ℤ)) ≫
      (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) 0).map
        (E.restrictedSection U ℓU) ≫
      (HomologicalComplex.singleMapHomologicalComplex (restrictToOpen X U) (.up ℤ) 0).inv.app
        E.middle) ≫ q) htrail
  simpa only [Category.assoc] using hp

/-! ### The literal overlap section on an arbitrary restricted open

The target of the restricted factorisation is the pullback to `U` of the
pushforward from `Ω`.  Its section on `U` is therefore obtained from a
section on `U ⊓ Ω` by the raw presheaf map, followed by the harmless equality
identifying the image of `⊤ : Opens U` with `U`. -/

def restrictedOverlapSection
    (Ω U : Opens (TopCat.of (ComplexPoint X)))
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    ((restrictToOpen X U).obj ((openRestrictionFunctor Ω).obj
      (holomorphicUnitSheaf X d))).obj.obj (op ⊤) := by
  dsimp [restrictToOpen, Topology.IsOpenEmbedding.sheafPullback,
    Functor.sheafPushforwardContinuous]
  let z := (TopCat.Sheaf.supportedOutsideIntersectionIso
    (TopCat.of (ComplexPoint X)) Ω U (holomorphicUnitSheaf X d)).inv w
  let e := eqToIso (congrArg op (TopCat.Sheaf.openRestrictionImage_top
    (TopCat.of (ComplexPoint X)) U))
  exact ((openRestrictionFunctor Ω).obj (holomorphicUnitSheaf X d)).obj.map e.inv z

def restrictedFrameFactorisation
    (Ω U : Opens (TopCat.of (ComplexPoint X)))
    (ℓU : E.middle.obj.obj (op U))
    (ℓΩ : E.middle.obj.obj (op Ω))
    (hℓΩ : E.projection.hom.app (op Ω) ℓΩ =
      (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection) :
    ((restrictToOpen X U).obj (𝓒(↧(ComplexPoint X); ℤ))) ⟶
      ((restrictToOpen X U).obj ((openRestrictionFunctor Ω).obj
        (holomorphicUnitSheaf X d))) :=
  E.restrictedSection U ℓU ≫
    (restrictToOpen X U).map (E.restrictionFactorisation Ω ℓΩ hℓΩ)

def restrictedOverlapUnitHom
    (Ω U : Opens (TopCat.of (ComplexPoint X)))
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω))) :
    ((restrictToOpen X U).obj (𝓒(↧(ComplexPoint X); ℤ))) ⟶
      ((restrictToOpen X U).obj ((openRestrictionFunctor Ω).obj
        (holomorphicUnitSheaf X d))) :=
  TopCat.Sheaf.openSheafRestrictionToConstant (TopCat.of (ComplexPoint X)) U
      (AddCommGrpCat.of ℤ) ≫
    TopCat.Sheaf.constHomOfSection
      ((restrictToOpen X U).obj ((openRestrictionFunctor Ω).obj
        (holomorphicUnitSheaf X d)))
      (restrictedOverlapSection X d Ω U w)

lemma restrictedSection_integerOne
    (U : Opens (TopCat.of (ComplexPoint X)))
    (ℓU : E.middle.obj.obj (op U)) :
    let einv : 𝓒[↧U; AddCommGrpCat.of ℤ] ⟶
        (restrictToOpen X U).obj (𝓒(↧(ComplexPoint X); ℤ)) :=
      TopCat.Sheaf.constantToOpenSheafRestriction (TopCat.of (ComplexPoint X)) U
        (AddCommGrpCat.of ℤ)
    let oneS := einv.hom.app (op ⊤) (TopCat.Sheaf.integerOne (Y := TopCat.of U))
    let eu : E.middle.obj.obj (op U) ≅
        ((restrictToOpen X U).obj E.middle).obj.obj (op ⊤) :=
      E.middle.obj.mapIso (eqToIso (congrArg op
        (TopCat.Sheaf.openRestrictionImage_top (TopCat.of (ComplexPoint X)) U))).symm
    (E.restrictedSection U ℓU).hom.app (op ⊤) oneS = eu.hom ℓU := by
  dsimp only
  unfold HolomorphicUnitExtension.restrictedSection
  rw [Adjunction.homEquiv_counit]
  change ((openRestrictionAdjunction U).counit.app ((restrictToOpen X U).obj E.middle)).hom.app
      (op ⊤)
      (((restrictToOpen X U).map (E.liftHom U ℓU)).hom.app (op ⊤)
        (((TopCat.Sheaf.constantToOpenSheafRestriction (TopCat.of (ComplexPoint X)) U
          (AddCommGrpCat.of ℤ)).hom.app (op ⊤)) TopCat.Sheaf.integerOne)) = _
  have hc := congrArg (fun f => f.app (op ⊤))
    (TopCat.Sheaf.toSheafify_constantToOpenSheafRestriction
      (TopCat.of (ComplexPoint X)) U (AddCommGrpCat.of ℤ))
  have hone := congrArg (fun f => f (1 : ℤ)) hc
  dsimp [TopCat.Sheaf.integerOne] at hone
  have hlift : (E.liftHom U ℓU).hom.app
      (op (U.isOpenEmbedding.isOpenMap.functor.obj ⊤))
      (((CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (TopCat.Sheaf.integerConstantPresheaf (TopCat.of (ComplexPoint X)))).app
          (op (U.isOpenEmbedding.isOpenMap.functor.obj ⊤))) (1 : ℤ)) =
    ((openRestrictionFunctor U).obj E.middle).obj.map
      (homOfLE (le_top : U.isOpenEmbedding.isOpenMap.functor.obj ⊤ ≤ ⊤)).op
      ((openRestrictionTopEval U).inv.app E.middle ℓU) := by
    rw [HolomorphicUnitExtension.liftHom]
    have hc2 := congrArg (fun f => f.app
      (op (U.isOpenEmbedding.isOpenMap.functor.obj ⊤)))
      (TopCat.Sheaf.toSheafify_constHomOfSection
        ((openRestrictionFunctor U).obj E.middle)
        ((openRestrictionTopEval U).inv.app E.middle ℓU))
    have hc2' := congrArg (fun f => f (1 : ℤ)) hc2
    dsimp [TopCat.Sheaf.constPresheafHomOfSection] at hc2'
    change (AddCommGrpCat.Hom.hom
        ((TopCat.Sheaf.constHomOfSection ((openRestrictionFunctor U).obj E.middle)
          ((openRestrictionTopEval U).inv.app E.middle ℓU)).hom.app
          (op (U.isOpenEmbedding.isOpenMap.functor.obj ⊤))))
        ((AddCommGrpCat.Hom.hom
          ((CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
            (TopCat.Sheaf.integerConstantPresheaf (TopCat.of (ComplexPoint X)))).app
            (op (U.isOpenEmbedding.isOpenMap.functor.obj ⊤)))) (1 : ℤ)) =
      1 • (AddCommGrpCat.Hom.hom (((openRestrictionFunctor U).obj E.middle).obj.map
        (homOfLE (le_top : U.isOpenEmbedding.isOpenMap.functor.obj ⊤ ≤ ⊤)).op))
        ((openRestrictionTopEval U).inv.app E.middle ℓU) at hc2'
    simpa only [one_smul, AddCommGrpCat.Hom.hom] using hc2'
  change ((openRestrictionAdjunction U).counit.app ((restrictToOpen X U).obj E.middle)).hom.app
      (op ⊤)
      ((E.liftHom U ℓU).hom.app
        (op (U.isOpenEmbedding.isOpenMap.functor.obj ⊤))
        ((ConcreteCategory.hom ((TopCat.Sheaf.constantToOpenSheafRestriction
          (TopCat.of (ComplexPoint X)) U (AddCommGrpCat.of ℤ)).hom.app (op ⊤)))
          ((ConcreteCategory.hom ((CategoryTheory.toSheafify
            (Opens.grothendieckTopology (TopCat.of U))
            (TopCat.Sheaf.integerConstantPresheaf (TopCat.of U))).app (op ⊤))) (1 : ℤ)))) = _
  have harg :
      ((ConcreteCategory.hom ((TopCat.Sheaf.constantToOpenSheafRestriction
        (TopCat.of (ComplexPoint X)) U (AddCommGrpCat.of ℤ)).hom.app (op ⊤)))
        ((ConcreteCategory.hom ((CategoryTheory.toSheafify
          (Opens.grothendieckTopology (TopCat.of U))
          (TopCat.Sheaf.integerConstantPresheaf (TopCat.of U))).app (op ⊤))) (1 : ℤ))) =
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (TopCat.Sheaf.integerConstantPresheaf (TopCat.of (ComplexPoint X)))).app
          (op (U.isOpenEmbedding.isOpenMap.functor.obj ⊤))) (1 : ℤ) := by
    exact hone
  rw [harg]
  have hcounit :
      ((openRestrictionAdjunction U).counit.app ((restrictToOpen X U).obj E.middle)).hom.app
          (op ⊤)
        (((openRestrictionFunctor U).obj E.middle).obj.map
          (homOfLE (le_top : U.isOpenEmbedding.isOpenMap.functor.obj ⊤ ≤ ⊤)).op
          ((openRestrictionTopEval U).inv.app E.middle ℓU)) =
      (E.middle.obj.mapIso (eqToIso (congrArg op
        (TopCat.Sheaf.openRestrictionImage_top (TopCat.of (ComplexPoint X)) U))).symm).hom ℓU := by
    dsimp [openRestrictionAdjunction, TopCat.Sheaf.openSheafRestrictionAdjunction,
      TopCat.Sheaf.openSheafRestrictionCounit, openRestrictionTopEval,
      TopCat.Sheaf.openRestrictionPushforwardTopEvaluationIso, restrictToOpen,
      Topology.IsOpenEmbedding.sheafPullback, Functor.sheafPushforwardContinuous,
      openRestrictionFunctor, TopCat.Sheaf.openRestrictionPushforward,
      TopCat.Sheaf.pushforward]
    change E.middle.obj.map _ (E.middle.obj.map _ (E.middle.obj.map _ ℓU)) =
      E.middle.obj.map _ ℓU
    change (E.middle.obj.map _ ≫ E.middle.obj.map _ ≫ E.middle.obj.map _) ℓU =
      (E.middle.obj.map _) ℓU
    rw [← E.middle.obj.map_comp, ← E.middle.obj.map_comp]
    congr 1
  exact (congrArg (fun z =>
    ((openRestrictionAdjunction U).counit.app ((restrictToOpen X U).obj E.middle)).hom.app
      (op ⊤) z) hlift).trans hcounit

lemma restrictedConstantMap_eq_constHomOfSection
    {U : Opens (TopCat.of (ComplexPoint X))}
    (F : TopCat.Sheaf AddCommGrpCat (TopCat.of U))
    (s : (restrictToOpen X U).obj (𝓒(↧(ComplexPoint X); ℤ)) ⟶ F) :
    s = TopCat.Sheaf.openSheafRestrictionToConstant (TopCat.of (ComplexPoint X)) U
      (AddCommGrpCat.of ℤ) ≫
      TopCat.Sheaf.constHomOfSection F
        ((s.hom.app (op ⊤))
          ((TopCat.Sheaf.constantToOpenSheafRestriction (TopCat.of (ComplexPoint X)) U
            (AddCommGrpCat.of ℤ)).hom.app (op ⊤)
            (TopCat.Sheaf.integerOne (Y := TopCat.of U)))) := by
  let e : ((restrictToOpen X U).obj (𝓒(↧(ComplexPoint X); ℤ))) ≅
      𝓒[↧U; AddCommGrpCat.of ℤ] :=
    { hom := TopCat.Sheaf.openSheafRestrictionToConstant (TopCat.of (ComplexPoint X)) U
        (AddCommGrpCat.of ℤ)
      inv := TopCat.Sheaf.constantToOpenSheafRestriction (TopCat.of (ComplexPoint X)) U
        (AddCommGrpCat.of ℤ)
      hom_inv_id := TopCat.Sheaf.openSheafRestrictionToConstant_constantToOpen
        (TopCat.of (ComplexPoint X)) U (AddCommGrpCat.of ℤ)
      inv_hom_id := TopCat.Sheaf.constantToOpen_openSheafRestrictionToConstant
        (TopCat.of (ComplexPoint X)) U (AddCommGrpCat.of ℤ) }
  let : IsIso e.inv := e.isIso_inv
  apply (cancel_epi e.inv).1
  have hs : e.inv ≫ s = TopCat.Sheaf.constHomOfSection F
      ((e.inv ≫ s).hom.app (op ⊤)
        (TopCat.Sheaf.integerOne (Y := TopCat.of U))) := by
    have h := TopCat.Sheaf.constHomOfSection_comp
      (TopCat.Sheaf.integerOne (Y := TopCat.of U)) (e.inv ≫ s)
    rw [TopCat.Sheaf.constHomOfSection_integerOne, Category.id_comp] at h
    exact h
  rw [hs]
  rw [← Category.assoc, e.inv_hom_id]
  congr 1

end AlgebraicGeometry.ComplexPoint
