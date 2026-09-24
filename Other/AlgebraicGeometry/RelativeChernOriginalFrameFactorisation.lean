/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RelativeChernOriginalRestriction

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CochainComplex.HomComplex
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
namespace AlgebraicGeometry.ComplexPoint
variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (E : HolomorphicUnitExtension X d)
variable (Ω U : Opens (TopCat.of (ComplexPoint X)))
  (ℓU : E.middle.obj.obj (op U))
  (ℓΩ : E.middle.obj.obj (op Ω))
  (hℓΩ : E.projection.hom.app (op Ω) ℓΩ =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)
  (hℓU : E.projection.hom.app (op U) ℓU =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : U ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)

include hℓU in
lemma restrictedFrameFactorisation_eq_overlapUnitHom
    (w : (holomorphicUnitSheaf X d).obj.obj (op (U ⊓ Ω)))
    (hw : E.inclusion.hom.app (op (U ⊓ Ω)) w =
      E.middle.obj.map (homOfLE (inf_le_right : U ⊓ Ω ≤ Ω)).op ℓΩ -
      E.middle.obj.map (homOfLE (inf_le_left : U ⊓ Ω ≤ U)).op ℓU) :
    restrictedFrameFactorisation X d E Ω U ℓU ℓΩ hℓΩ =
      restrictedOverlapUnitHom X d Ω U (-w) := by
  have hconst := restrictedConstantMap_eq_constHomOfSection X
    (F := (restrictToOpen X U).obj ((openRestrictionFunctor Ω).obj
      (holomorphicUnitSheaf X d)))
    (s := restrictedFrameFactorisation X d E Ω U ℓU ℓΩ hℓΩ)
  rw [hconst]
  unfold restrictedOverlapUnitHom
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
  let : IsIso e.hom := e.isIso_hom
  change e.hom ≫ _ = e.hom ≫ _
  apply (cancel_epi e.hom).2
  congr 1
  let j := ((restrictToOpen X U).map ((openRestrictionFunctor Ω).map E.inclusion)).hom.app (op ⊤)
  have hmonoΩ : Mono ((openRestrictionFunctor Ω).map E.inclusion) := by
    change Mono ((TopCat.Sheaf.pushforward AddCommGrpCat Ω.inclusion').map
      ((restrictToOpen X Ω).map E.inclusion))
    let : Mono ((restrictToOpen X Ω).map E.inclusion) :=
      (E.shortExact_map_restrictToOpen Ω).mono_f
    infer_instance
  have hmonoU : Mono ((restrictToOpen X U).map ((openRestrictionFunctor Ω).map E.inclusion)) := by
    let : Mono ((openRestrictionFunctor Ω).map E.inclusion) := hmonoΩ
    exact (restrictToOpen X U).map_mono _
  have hj : Function.Injective (ConcreteCategory.hom j) := by
    apply (AddCommGrpCat.mono_iff_injective j).mp
    let : Mono ((restrictToOpen X U).map ((openRestrictionFunctor Ω).map E.inclusion)) := hmonoU
    have hp : Mono (((restrictToOpen X U).map ((openRestrictionFunctor Ω).map E.inclusion)).hom) :=
      (Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mp inferInstance
    exact (NatTrans.mono_iff_mono_app _).mp hp (op ⊤)
  apply hj
  let oneS := ((TopCat.Sheaf.constantToOpenSheafRestriction (TopCat.of (ComplexPoint X)) U
    (AddCommGrpCat.of ℤ)).hom.app (op ⊤)) (TopCat.Sheaf.integerOne (Y := TopCat.of U))
  have hmap :
      restrictedFrameFactorisation X d E Ω U ℓU ℓΩ hℓΩ ≫
          (restrictToOpen X U).map ((openRestrictionFunctor Ω).map E.inclusion) =
        E.restrictedSection U ℓU ≫
          (restrictToOpen X U).map
            (E.restrictionFactorisation Ω ℓΩ hℓΩ ≫ (openRestrictionFunctor Ω).map E.inclusion) := by
    unfold restrictedFrameFactorisation
    rw [Category.assoc, (restrictToOpen X U).map_comp]
  have hs := congrArg (fun f =>
      (ConcreteCategory.hom (f.hom.app (op ⊤))) oneS) hmap
  dsimp [j] at hs
  have hs' :
      (ConcreteCategory.hom j)
          ((ConcreteCategory.hom ((restrictedFrameFactorisation X d E Ω U ℓU ℓΩ hℓΩ).hom.app (op ⊤))) oneS) =
        (ConcreteCategory.hom
          ((E.restrictedSection U ℓU ≫
            (restrictToOpen X U).map
              (E.restrictionFactorisation Ω ℓΩ hℓΩ ≫ (openRestrictionFunctor Ω).map E.inclusion)).hom.app
              (op ⊤))) oneS := by
    change (ConcreteCategory.hom
      ((restrictedFrameFactorisation X d E Ω U ℓU ℓΩ hℓΩ ≫
        (restrictToOpen X U).map ((openRestrictionFunctor Ω).map E.inclusion)).hom.app
        (op ⊤))) oneS = _
    exact hs
  rw [hs']
  rw [E.restrictionFactorisation_comp_inclusion Ω ℓΩ hℓΩ]
  have hfull :
      E.restrictedSection U ℓU ≫
          (restrictToOpen X U).map
            (restrictionUnit Ω E.middle - E.projection ≫ E.liftHom Ω ℓΩ) =
        E.restrictedSection U ℓU ≫ (restrictToOpen X U).map
            (restrictionUnit Ω E.middle) -
          (restrictToOpen X U).map (E.liftHom Ω ℓΩ) := by
    rw [Functor.map_sub, Preadditive.comp_sub,  (restrictToOpen X U).map_comp, ← Category.assoc,
      E.restrictedSection_comp_projection U ℓU hℓU,
      Category.id_comp]
  have hfsec := congrArg (fun f =>
      (ConcreteCategory.hom (f.hom.app (op ⊤))) oneS) hfull
  have hsecU := restrictedSection_integerOne X d E U ℓU
  dsimp only at hsecU
  rw [hfsec]
  have happ :
      (E.restrictedSection U ℓU ≫ (restrictToOpen X U).map (restrictionUnit Ω E.middle) -
          (restrictToOpen X U).map (E.liftHom Ω ℓΩ)).hom.app (op ⊤) =
        (E.restrictedSection U ℓU ≫ (restrictToOpen X U).map (restrictionUnit Ω E.middle)).hom.app
            (op ⊤) -
          ((restrictToOpen X U).map (E.liftHom Ω ℓΩ)).hom.app (op ⊤) := by
    rfl
  have happ' := congrArg (fun f => (ConcreteCategory.hom f) oneS) happ
  rw [happ']
  have happ2 :
      ConcreteCategory.hom
          ((E.restrictedSection U ℓU ≫ (restrictToOpen X U).map (restrictionUnit Ω E.middle)).hom.app
            (op ⊤) - ((restrictToOpen X U).map (E.liftHom Ω ℓΩ)).hom.app (op ⊤)) =
        ConcreteCategory.hom
          ((E.restrictedSection U ℓU ≫ (restrictToOpen X U).map (restrictionUnit Ω E.middle)).hom.app
            (op ⊤)) -
          ConcreteCategory.hom (((restrictToOpen X U).map (E.liftHom Ω ℓΩ)).hom.app (op ⊤)) := by
    rfl
  have happ2' := congrArg (fun f => f oneS) happ2
  rw [happ2']
  have hsub3 :
      (ConcreteCategory.hom
          ((E.restrictedSection U ℓU ≫ (restrictToOpen X U).map (restrictionUnit Ω E.middle)).hom.app
            (op ⊤)) -
        ConcreteCategory.hom (((restrictToOpen X U).map (E.liftHom Ω ℓΩ)).hom.app (op ⊤))) oneS =
        (ConcreteCategory.hom
          ((E.restrictedSection U ℓU ≫ (restrictToOpen X U).map (restrictionUnit Ω E.middle)).hom.app
            (op ⊤))) oneS -
        (ConcreteCategory.hom (((restrictToOpen X U).map (E.liftHom Ω ℓΩ)).hom.app (op ⊤))) oneS := by
    exact AddMonoidHom.sub_apply _ _ _
  rw [hsub3]
  have hfirst :
      (ConcreteCategory.hom
          ((E.restrictedSection U ℓU ≫ (restrictToOpen X U).map (restrictionUnit Ω E.middle)).hom.app
            (op ⊤))) oneS =
        (ConcreteCategory.hom (((restrictToOpen X U).map (restrictionUnit Ω E.middle)).hom.app
          (op ⊤)))
          ((ConcreteCategory.hom ((E.restrictedSection U ℓU).hom.app (op ⊤))) oneS) := by
    rfl
  rw [hfirst, hsecU]
  dsimp [restrictionUnit, HolomorphicUnitExtension.liftHom, restrictToOpen,
    Topology.IsOpenEmbedding.sheafPullback, Functor.sheafPushforwardContinuous,
    openRestrictionFunctor, TopCat.Sheaf.openRestrictionPushforward,
    TopCat.Sheaf.pushforward]
  let V := TopCat.Sheaf.openRestrictionImage (TopCat.of (ComplexPoint X)) U ⊤
  let em := TopCat.Sheaf.supportedOutsideIntersectionIso
    (TopCat.of (ComplexPoint X)) Ω V E.middle
  have hem : Function.Injective (ConcreteCategory.hom em.hom) := by
    exact (ConcreteCategory.bijective_of_isIso em.hom).1
  apply hem
  rw [map_sub]
  have hto := TopCat.Sheaf.toOpenRestrictionPushforward_intersection
    (TopCat.of (ComplexPoint X)) Ω V E.middle
  change (ConcreteCategory.hom
      ((((TopCat.Sheaf.toOpenRestrictionPushforward (TopCat.of (ComplexPoint X)) Ω).app E.middle).hom.app
        (op V)) ≫ em.hom)) _ - _ = _
  rw [hto]
  have honeV : oneS =
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        (TopCat.Sheaf.integerConstantPresheaf (TopCat.of (ComplexPoint X)))).app
        (op (TopCat.Sheaf.openRestrictionImage (TopCat.of (ComplexPoint X)) U ⊤)))
        (1 : ℤ) := by
    have hc := congrArg (fun f => f.app (op (⊤ : Opens (TopCat.of U))))
      (TopCat.Sheaf.toSheafify_constantToOpenSheafRestriction
        (TopCat.of (ComplexPoint X)) U (AddCommGrpCat.of ℤ))
    have hone := congrArg (fun f => f (1 : ℤ)) hc
    dsimp [TopCat.Sheaf.integerOne] at hone
    exact hone
  rw [honeV]
  dsimp [TopCat.Sheaf.constHomOfSection, TopCat.Sheaf.constPresheafHomOfSection]
  change _ - (ConcreteCategory.hom em.hom)
      ((ConcreteCategory.hom ((E.liftHom Ω ℓΩ).hom.app (op V)))
        (((CategoryTheory.toSheafify (Opens.grothendieckTopology (ComplexPoint X))
          (TopCat.Sheaf.integerConstantPresheaf (TopCat.of (ComplexPoint X)))).app (op V))
          (1 : ℤ))) = _
  have hliftV :
      (ConcreteCategory.hom em.hom)
          ((ConcreteCategory.hom ((E.liftHom Ω ℓΩ).hom.app (op V)))
            (((CategoryTheory.toSheafify (Opens.grothendieckTopology (ComplexPoint X))
              (TopCat.Sheaf.integerConstantPresheaf (TopCat.of (ComplexPoint X)))).app (op V))
              (1 : ℤ))) =
        (ConcreteCategory.hom (E.middle.obj.map
          (homOfLE (inf_le_right : V ⊓ Ω ≤ Ω)).op)) ℓΩ := by
    rw [HolomorphicUnitExtension.liftHom]
    have hc := congrArg (fun f => f.app (op V))
      (TopCat.Sheaf.toSheafify_constHomOfSection
        ((openRestrictionFunctor Ω).obj E.middle)
        ((openRestrictionTopEval Ω).inv.app E.middle ℓΩ))
    have hc' := congrArg (fun f => f (1 : ℤ)) hc
    dsimp [TopCat.Sheaf.constPresheafHomOfSection] at hc'
    change (ConcreteCategory.hom em.hom)
        ((AddCommGrpCat.Hom.hom
          ((TopCat.Sheaf.constHomOfSection ((openRestrictionFunctor Ω).obj E.middle)
            ((openRestrictionTopEval Ω).inv.app E.middle ℓΩ)).hom.app (op V)))
          ((AddCommGrpCat.Hom.hom
            ((CategoryTheory.toSheafify (Opens.grothendieckTopology (ComplexPoint X))
              (TopCat.Sheaf.integerConstantPresheaf (TopCat.of (ComplexPoint X)))).app (op V)))
            (1 : ℤ))) = _
    calc
      _ = (ConcreteCategory.hom em.hom)
          ((ConcreteCategory.hom (((openRestrictionFunctor Ω).obj E.middle).obj.map
            (homOfLE (show V ≤ (⊤ : Opens (TopCat.of (ComplexPoint X))) from le_top)).op))
            ((openRestrictionTopEval Ω).inv.app E.middle ℓΩ)) := by
        convert (congrArg (fun z => (ConcreteCategory.hom em.hom) z) hc') using 1 <;>
          simp only [one_smul, AddCommGrpCat.Hom.hom] <;> rfl
      _ = _ := by
        have hn := TopCat.Sheaf.supportedOutsideIntersectionIso_naturality
          (TopCat.of (ComplexPoint X)) Ω
            (homOfLE (show V ≤ (⊤ : Opens (TopCat.of (ComplexPoint X))) from le_top)) E.middle
        have hn' := congrArg (fun f => (ConcreteCategory.hom f)
          ((openRestrictionTopEval Ω).inv.app E.middle ℓΩ)) hn
        have ht :
            (ConcreteCategory.hom
              (TopCat.Sheaf.supportedOutsideIntersectionIso
                (TopCat.of (ComplexPoint X)) Ω ⊤ E.middle).hom)
                ((openRestrictionTopEval Ω).inv.app E.middle ℓΩ) =
              (ConcreteCategory.hom (E.middle.obj.map
                (homOfLE (inf_le_right : (⊤ : Opens (TopCat.of (ComplexPoint X))) ⊓ Ω ≤ Ω)).op)) ℓΩ := by
          dsimp [TopCat.Sheaf.supportedOutsideIntersectionIso, openRestrictionTopEval,
            TopCat.Sheaf.openRestrictionPushforwardTopEvaluationIso]
          change (E.middle.obj.map _ (E.middle.obj.map _ ℓΩ)) =
            E.middle.obj.map _ ℓΩ
          change (E.middle.obj.map _ ≫ E.middle.obj.map _) ℓΩ =
            (E.middle.obj.map _) ℓΩ
          rw [← E.middle.obj.map_comp]
          congr 1
        simp only [CategoryTheory.comp_apply] at hn'
        rw [ht] at hn'
        change _ = (ConcreteCategory.hom
          (E.middle.obj.map _ ≫ E.middle.obj.map _)) ℓΩ at hn'
        rw [← E.middle.obj.map_comp] at hn'
        convert hn' using 1
        congr 1
  rw [hliftV]
  dsimp [em, j, restrictedOverlapSection, restrictToOpen,
    Topology.IsOpenEmbedding.sheafPullback, Functor.sheafPushforwardContinuous,
    openRestrictionFunctor, TopCat.Sheaf.openRestrictionPushforward, TopCat.Sheaf.pushforward,
    TopCat.Sheaf.supportedOutsideIntersectionIso]
  change (E.middle.obj.map _ ≫ E.middle.obj.map _) ℓU -
      E.middle.obj.map _ ℓΩ =
    (((holomorphicUnitSheaf X d).obj.map _ ≫
      (holomorphicUnitSheaf X d).obj.map _) ≫
      E.inclusion.hom.app _ ≫ E.middle.obj.map _) (-w)
  rw [← (holomorphicUnitSheaf X d).obj.map_comp]
  rw [E.inclusion.hom.naturality_assoc]
  rw [← E.middle.obj.map_comp]
  rw [← E.middle.obj.map_comp]
  simp only [ConcreteCategory.comp_apply, map_neg, hw, map_sub, neg_sub]
  congr 1 <;>
    change E.middle.obj.map _ _ = (E.middle.obj.map _ ≫ E.middle.obj.map _) _
  all_goals
    rw [← E.middle.obj.map_comp]
    congr 1
end AlgebraicGeometry.ComplexPoint
