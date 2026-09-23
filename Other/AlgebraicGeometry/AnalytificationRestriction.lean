/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalytificationModules
public import Other.TauCeti.SheafOfModules.Restriction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over

/-!
# Restriction and local triviality for module analytification

This file proves the Beck--Chevalley comparison between module analytification and restriction to
an algebraic open.  It then transports a Tau Ceti local trivialization through that comparison,
showing that analytification sends algebraic line bundles to holomorphic line bundles.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

/-- Sheafification on the site over an open is obtained by transporting ordinary sheafification
along the equivalence `Over U ≌ Opens U`. -/
theorem opensOverHasSheafify {T : Type} [TopologicalSpace T] (U : Opens T) :
    HasSheafify ((Opens.grothendieckTopology T).over U) AddCommGrpCat.{0} :=
  CategoryTheory.Equivalence.hasSheafify
    ((Opens.grothendieckTopology T).over U)
    (Opens.grothendieckTopology U) U.overEquivalence AddCommGrpCat.{0}

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance underlyingContinuousMapSiteContinuous :
    (Opens.map (underlyingContinuousMap X)).IsContinuous
      (Opens.grothendieckTopology X.left)
      (Opens.grothendieckTopology (ComplexPoint X)) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreserving_opens_map (underlyingContinuousMap X))
    (coverPreserving_opens_map (underlyingContinuousMap X))

-- The upstream instance for `Opens.map` does not elaborate for the scheme carrier coercion here,
-- so we spell out its short filteredness proof.
local instance underlyingContinuousMapOpensMapFlat :
    RepresentablyFlat (Opens.map (underlyingContinuousMap X)) := by
  constructor
  intro U
  refine @IsCofiltered.mk _ _ ?_ ?_
  · constructor
    · intro V W
      exact ⟨⟨⟨PUnit.unit⟩, V.right ⊓ W.right,
        homOfLE <| le_inf V.hom.le W.hom.le⟩,
        StructuredArrow.homMk (homOfLE inf_le_left),
        StructuredArrow.homMk (homOfLE inf_le_right), trivial⟩
    · exact fun _ _ _ _ ↦ ⟨_, 𝟙 _, by simp [eq_iff_true_of_subsingleton]⟩
  · exact ⟨StructuredArrow.mk <| show U ⟶
      (Opens.map (underlyingContinuousMap X)).obj ⊤ from homOfLE le_top⟩

local instance underlyingContinuousMapOpensMapPreservesFiniteLimits :
    Limits.PreservesFiniteLimits (Opens.map (underlyingContinuousMap X)) :=
  preservesFiniteLimits_of_flat _

/-- The square formed by inverse image of opens and restriction to `U` commutes up to the
canonical binary-product comparison. -/
noncomputable def analyticOpenStarPostIso (U : X.left.Opens) :
    Opens.map (underlyingContinuousMap X) ⋙ Over.star (analyticOpen X U) ≅
      Over.star U ⋙ Over.post (Opens.map (underlyingContinuousMap X)) :=
  NatIso.ofComponents (fun W ↦ Over.isoMk
    ((preservesLimitIso (Opens.map (underlyingContinuousMap X))
      (Limits.pair U W) ≪≫
      Limits.HasLimit.isoOfNatIso
        (Limits.pairComp U W (Opens.map (underlyingContinuousMap X)))).symm)
      (Subsingleton.elim _ _))
    (fun _ ↦ by ext; exact Subsingleton.elim _ _)

local instance analyticOpenOverPostContinuous (U : X.left.Opens) :
    (Over.post (X := U) (Opens.map (underlyingContinuousMap X))).IsContinuous
      ((Opens.grothendieckTopology X.left).over U)
      ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U)) := by
  let F := Opens.map (underlyingContinuousMap X)
  letI : RepresentablyFlat F := by
    dsimp [F]
    infer_instance
  letI : Limits.PreservesFiniteLimits F := preservesFiniteLimits_of_flat F
  letI : RepresentablyFlat (Over.post (X := U) F) :=
    flat_of_preservesFiniteLimits (Over.post (X := U) F)
  apply Functor.isContinuous_of_coverPreserving
  · exact compatiblePreservingOfFlat _ _
  · exact (coverPreserving_opens_map (underlyingContinuousMap X)).overPost U

/-- The evaluation map from regular to holomorphic functions restricted over an algebraic open. -/
noncomputable def regularToHolomorphicRingSheafOver (U : X.left.Opens) :
    X.left.ringCatSheaf.over U ⟶
      ((Over.post (X := U) (Opens.map (underlyingContinuousMap X))).sheafPushforwardContinuous
        RingCat
        ((Opens.grothendieckTopology X.left).over U)
        ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U))).obj
          ((holomorphicRingSheaf X d).over (analyticOpen X U)) :=
  ((Over.forget U).sheafPushforwardContinuous RingCat
    ((Opens.grothendieckTopology X.left).over U)
    (Opens.grothendieckTopology X.left)).map (regularToHolomorphicRingSheaf X d)

/-- Direct image and restriction of scalars for the restricted regular-to-holomorphic map. -/
noncomputable def localHolomorphicModulePushforward (U : X.left.Opens) :
    SheafOfModules ((holomorphicRingSheaf X d).over (analyticOpen X U)) ⥤
      SheafOfModules (X.left.ringCatSheaf.over U) := by
  letI : (Over.post (X := U) (Opens.map (underlyingContinuousMap X))).IsContinuous
      ((Opens.grothendieckTopology X.left).over U)
      ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U)) :=
    analyticOpenOverPostContinuous X U
  exact @SheafOfModules.pushforward.{0}
    (Over U) inferInstance (Over (analyticOpen X U)) inferInstance
    ((Opens.grothendieckTopology X.left).over U)
    ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U))
    (Over.post (X := U) (Opens.map (underlyingContinuousMap X)))
    (X.left.ringCatSheaf.over U)
    ((holomorphicRingSheaf X d).over (analyticOpen X U))
    (analyticOpenOverPostContinuous X U)
    (regularToHolomorphicRingSheafOver X d U)

local instance analyticOpenOverHasSheafify (U : X.left.Opens) :
    HasSheafify
      ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U))
      AddCommGrpCat.{0} :=
  CategoryTheory.Equivalence.hasSheafify
    ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U))
    (Opens.grothendieckTopology (analyticOpen X U))
    (analyticOpen X U).overEquivalence AddCommGrpCat.{0}

local instance analyticOpenOverPostFinal (U : X.left.Opens) :
    (Over.post (X := U) (Opens.map (underlyingContinuousMap X))).Final where
  out Z := by
    let V : StructuredArrow Z (Over.post (X := U)
        (Opens.map (underlyingContinuousMap X))) :=
      StructuredArrow.mk (Y := Over.mk (𝟙 U)) (Over.homMk Z.hom)
    have hV : Limits.IsTerminal V :=
      Limits.IsTerminal.ofUniqueHom
        (fun W ↦ StructuredArrow.homMk (Over.homMk W.right.hom))
        (fun _ _ ↦ by
          apply StructuredArrow.hom_ext
          ext
          exact Subsingleton.elim _ _)
    exact isConnected_of_isTerminal _ hV

local instance localPresheafPushforwardIsRightAdjoint (U : X.left.Opens) :
    (PresheafOfModules.pushforward.{0}
      (regularToHolomorphicRingSheafOver X d U).hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top
      (regularToHolomorphicRingSheafOver X d U).hom)

local instance localHolomorphicModulePushforwardIsRightAdjoint (U : X.left.Opens) :
    (localHolomorphicModulePushforward X d U).IsRightAdjoint := by
  letI : HasSheafify
      ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U))
      AddCommGrpCat.{0} := analyticOpenOverHasSheafify X U
  letI : HasWeakSheafify
      ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U))
      AddCommGrpCat.{0} := HasSheafify.isRightAdjoint
  letI : (Over.post (X := U) (Opens.map (underlyingContinuousMap X))).IsContinuous
      ((Opens.grothendieckTopology X.left).over U)
      ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U)) :=
    analyticOpenOverPostContinuous X U
  let hW : ((Opens.grothendieckTopology (ComplexPoint X)).over
      (analyticOpen X U)).WEqualsLocallyBijective AddCommGrpCat.{0} := by
    infer_instance
  exact (@SheafOfModules.PullbackConstruction.adjunction
    (Over U) inferInstance (Over (analyticOpen X U)) inferInstance
    ((Opens.grothendieckTopology X.left).over U)
    ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U))
    (Over.post (X := U) (Opens.map (underlyingContinuousMap X)))
    (X.left.ringCatSheaf.over U)
    ((holomorphicRingSheaf X d).over (analyticOpen X U))
    (analyticOpenOverPostContinuous X U)
    (regularToHolomorphicRingSheafOver X d U)
    (localPresheafPushforwardIsRightAdjoint X d U)
    HasSheafify.isRightAdjoint hW).isRightAdjoint

/-- Pullback of module sheaves for the regular-to-holomorphic map restricted over `U`. -/
noncomputable def localModuleAnalytification (U : X.left.Opens) :
    SheafOfModules (X.left.ringCatSheaf.over U) ⥤
      SheafOfModules ((holomorphicRingSheaf X d).over (analyticOpen X U)) :=
  (localHolomorphicModulePushforward X d U).leftAdjoint

/-- The local analytification/direct-image adjunction. -/
noncomputable def localModuleAnalytificationAdjunction (U : X.left.Opens) :
    localModuleAnalytification X d U ⊣ localHolomorphicModulePushforward X d U :=
  Adjunction.ofIsRightAdjoint (localHolomorphicModulePushforward X d U)

/-- Local module analytification sends the structure sheaf to the holomorphic structure sheaf. -/
noncomputable def localModuleAnalytificationUnitIso (U : X.left.Opens) :
    (localModuleAnalytification X d U).obj
        (SheafOfModules.unit (X.left.ringCatSheaf.over U)) ≅
      SheafOfModules.unit ((holomorphicRingSheaf X d).over (analyticOpen X U)) := by
  letI : (Over.post (X := U) (Opens.map (underlyingContinuousMap X))).IsContinuous
      ((Opens.grothendieckTopology X.left).over U)
      ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U)) :=
    analyticOpenOverPostContinuous X U
  letI : (Over.post (X := U) (Opens.map (underlyingContinuousMap X))).Final :=
    analyticOpenOverPostFinal X U
  have hRA := localHolomorphicModulePushforwardIsRightAdjoint X d U
  dsimp [localHolomorphicModulePushforward] at hRA
  let f := @SheafOfModules.pullbackObjUnitToUnit
    (Over U) inferInstance (Over (analyticOpen X U)) inferInstance
    ((Opens.grothendieckTopology X.left).over U)
    ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U))
    (Over.post (X := U) (Opens.map (underlyingContinuousMap X)))
    (X.left.ringCatSheaf.over U)
    ((holomorphicRingSheaf X d).over (analyticOpen X U))
    (analyticOpenOverPostContinuous X U)
    (regularToHolomorphicRingSheafOver X d U) hRA
  have hf : IsIso f := @SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
    (Over U) inferInstance (Over (analyticOpen X U)) inferInstance
    ((Opens.grothendieckTopology X.left).over U)
    ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U))
    (Over.post (X := U) (Opens.map (underlyingContinuousMap X)))
    (X.left.ringCatSheaf.over U)
    ((holomorphicRingSheaf X d).over (analyticOpen X U))
    (analyticOpenOverPostContinuous X U)
    (regularToHolomorphicRingSheafOver X d U) hRA (analyticOpenOverPostFinal X U)
  exact @asIso _ _ _ _ f hf

/-- Local module analytification sends the standard free rank-one sheaf to the standard free
rank-one sheaf. -/
noncomputable def localModuleAnalytificationFreePUnitIso (U : X.left.Opens) :
    (localModuleAnalytification X d U).obj
        (SheafOfModules.free (R := X.left.ringCatSheaf.over U) PUnit) ≅
      SheafOfModules.free
        (R := (holomorphicRingSheaf X d).over (analyticOpen X U)) PUnit :=
  (localModuleAnalytification X d U).mapIso
      (TauCeti.SheafOfModules.freePUnitIsoUnit (X.left.ringCatSheaf.over U)) ≪≫
    localModuleAnalytificationUnitIso X d U ≪≫
      (TauCeti.SheafOfModules.freePUnitIsoUnit
        ((holomorphicRingSheaf X d).over (analyticOpen X U))).symm

noncomputable def globalThenOverRingMap (U : X.left.Opens) :=
  letI : (Opens.map (underlyingContinuousMap X)).IsContinuous
      (Opens.grothendieckTopology X.left)
      (Opens.grothendieckTopology (ComplexPoint X)) := underlyingContinuousMapSiteContinuous X
  regularToHolomorphicRingSheaf X d ≫
    ((Opens.map (underlyingContinuousMap X)).sheafPushforwardContinuous RingCat
      (Opens.grothendieckTopology X.left)
      (Opens.grothendieckTopology (ComplexPoint X))).map
        (SheafOfModules.pushforwardOver (R := holomorphicRingSheaf X d)
          (analyticOpen X U))

noncomputable def overThenLocalRingMap (U : X.left.Opens) :=
  letI : (Over.post (X := U) (Opens.map (underlyingContinuousMap X))).IsContinuous
      ((Opens.grothendieckTopology X.left).over U)
      ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U)) :=
    analyticOpenOverPostContinuous X U
  SheafOfModules.pushforwardOver (R := X.left.ringCatSheaf) U ≫
    ((Over.star U).sheafPushforwardContinuous RingCat
      (Opens.grothendieckTopology X.left)
      ((Opens.grothendieckTopology X.left).over U)).map
        (regularToHolomorphicRingSheafOver X d U)

noncomputable def globalCompositeModulePushforward (U : X.left.Opens) :
    SheafOfModules ((holomorphicRingSheaf X d).over (analyticOpen X U)) ⥤
      X.left.Modules :=
  @SheafOfModules.pushforward.{0}
    (Opens X.left) inferInstance (Over (analyticOpen X U)) inferInstance
    (Opens.grothendieckTopology X.left)
    ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U))
    (Opens.map (underlyingContinuousMap X) ⋙ Over.star (analyticOpen X U))
    X.left.ringCatSheaf
    ((holomorphicRingSheaf X d).over (analyticOpen X U))
    (@Functor.isContinuous_comp
      (Opens X.left) inferInstance (Opens (ComplexPoint X)) inferInstance
      (Over (analyticOpen X U)) inferInstance
      (Opens.map (underlyingContinuousMap X)) (Over.star (analyticOpen X U))
      (Opens.grothendieckTopology X.left)
      (Opens.grothendieckTopology (ComplexPoint X))
      ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U))
      (underlyingContinuousMapSiteContinuous X) inferInstance)
    (globalThenOverRingMap X d U)

noncomputable def localCompositeModulePushforward (U : X.left.Opens) :
    SheafOfModules ((holomorphicRingSheaf X d).over (analyticOpen X U)) ⥤
      X.left.Modules :=
  @SheafOfModules.pushforward.{0}
    (Opens X.left) inferInstance (Over (analyticOpen X U)) inferInstance
    (Opens.grothendieckTopology X.left)
    ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U))
    (Over.star U ⋙ Over.post (Opens.map (underlyingContinuousMap X)))
    X.left.ringCatSheaf
    ((holomorphicRingSheaf X d).over (analyticOpen X U))
    (@Functor.isContinuous_comp
      (Opens X.left) inferInstance (Over U) inferInstance
      (Over (analyticOpen X U)) inferInstance
      (Over.star U) (Over.post (Opens.map (underlyingContinuousMap X)))
      (Opens.grothendieckTopology X.left)
      ((Opens.grothendieckTopology X.left).over U)
      ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U))
      inferInstance (analyticOpenOverPostContinuous X U))
    (overThenLocalRingMap X d U)

noncomputable def globalPushforwardCompIso (U : X.left.Opens) :
    SheafOfModules.pushforward.{0}
        (SheafOfModules.pushforwardOver (R := holomorphicRingSheaf X d)
          (analyticOpen X U)) ⋙ holomorphicModulePushforward X d ≅
      globalCompositeModulePushforward X d U := by
  letI : (Opens.map (underlyingContinuousMap X)).IsContinuous
      (Opens.grothendieckTopology X.left)
      (Opens.grothendieckTopology (ComplexPoint X)) := underlyingContinuousMapSiteContinuous X
  exact SheafOfModules.pushforwardComp.{0} (regularToHolomorphicRingSheaf X d)
    (SheafOfModules.pushforwardOver (R := holomorphicRingSheaf X d)
      (analyticOpen X U))

noncomputable def localPushforwardCompIso (U : X.left.Opens) :
    localHolomorphicModulePushforward X d U ⋙
        SheafOfModules.pushforward.{0}
          (SheafOfModules.pushforwardOver (R := X.left.ringCatSheaf) U) ≅
      localCompositeModulePushforward X d U := by
  letI : (Over.post (X := U) (Opens.map (underlyingContinuousMap X))).IsContinuous
      ((Opens.grothendieckTopology X.left).over U)
      ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U)) :=
    analyticOpenOverPostContinuous X U
  exact SheafOfModules.pushforwardComp.{0}
    (SheafOfModules.pushforwardOver (R := X.left.ringCatSheaf) U)
    (regularToHolomorphicRingSheafOver X d U)

noncomputable def compositePushforwardIso (U : X.left.Opens) :
    globalCompositeModulePushforward X d U ≅ localCompositeModulePushforward X d U := by
  letI : (Opens.map (underlyingContinuousMap X)).IsContinuous
      (Opens.grothendieckTopology X.left)
      (Opens.grothendieckTopology (ComplexPoint X)) := underlyingContinuousMapSiteContinuous X
  letI : (Over.post (X := U) (Opens.map (underlyingContinuousMap X))).IsContinuous
      ((Opens.grothendieckTopology X.left).over U)
      ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U)) :=
    analyticOpenOverPostContinuous X U
  letI : (Opens.map (underlyingContinuousMap X) ⋙
      Over.star (analyticOpen X U)).IsContinuous
      (Opens.grothendieckTopology X.left)
      ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U)) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology (ComplexPoint X)) _
  letI : (Over.star U ⋙
      Over.post (X := U) (Opens.map (underlyingContinuousMap X))).IsContinuous
      (Opens.grothendieckTopology X.left)
      ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U)) :=
    Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology X.left).over U) _
  exact (@SheafOfModules.pushforwardCongr₂.{0}
    (Opens X.left) inferInstance (Over (analyticOpen X U)) inferInstance
    (Opens.grothendieckTopology X.left)
    ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U))
    (Opens.map (underlyingContinuousMap X) ⋙ Over.star (analyticOpen X U))
    (Over.star U ⋙ Over.post (Opens.map (underlyingContinuousMap X)))
    X.left.ringCatSheaf
    ((holomorphicRingSheaf X d).over (analyticOpen X U))
    (@Functor.isContinuous_comp
      (Opens X.left) inferInstance (Opens (ComplexPoint X)) inferInstance
      (Over (analyticOpen X U)) inferInstance
      (Opens.map (underlyingContinuousMap X)) (Over.star (analyticOpen X U))
      (Opens.grothendieckTopology X.left)
      (Opens.grothendieckTopology (ComplexPoint X))
      ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U))
      (underlyingContinuousMapSiteContinuous X) inferInstance)
    (@Functor.isContinuous_comp
      (Opens X.left) inferInstance (Over U) inferInstance
      (Over (analyticOpen X U)) inferInstance
      (Over.star U) (Over.post (Opens.map (underlyingContinuousMap X)))
      (Opens.grothendieckTopology X.left)
      ((Opens.grothendieckTopology X.left).over U)
      ((Opens.grothendieckTopology (ComplexPoint X)).over (analyticOpen X U))
      inferInstance (analyticOpenOverPostContinuous X U))
    (overThenLocalRingMap X d U)
    (globalThenOverRingMap X d U)
    (analyticOpenStarPostIso X U) (by
      ext W x
      have h := (regularToHolomorphicRingSheaf X d).hom.naturality
        (Limits.prod.snd : (U ⨯ W.unop) ⟶ W.unop).op
      have hx := congr_arg (fun f ↦ f x) (congr_arg RingCat.Hom.hom h)
      dsimp [overThenLocalRingMap, globalThenOverRingMap,
        regularToHolomorphicRingSheafOver, SheafOfModules.pushforwardOver,
        analyticOpenStarPostIso]
      change
        (holomorphicRingSheaf X d).obj.map
            ((analyticOpenStarPostIso X U).hom.app W.unop).left.op
              ((regularToHolomorphicRingSheaf X d).hom.app
                (Opposite.op (U ⨯ W.unop))
                  (X.left.ringCatSheaf.obj.map Limits.prod.snd.op x)) =
          (holomorphicRingSheaf X d).obj.map Limits.prod.snd.op
            ((regularToHolomorphicRingSheaf X d).hom.app W x)
      change
        (regularToHolomorphicRingSheaf X d).hom.app (Opposite.op (U ⨯ W.unop))
            (X.left.ringCatSheaf.obj.map Limits.prod.snd.op x) =
          (holomorphicRingSheaf X d).obj.map
              ((Opens.map (underlyingContinuousMap X)).map Limits.prod.snd).op
                ((regularToHolomorphicRingSheaf X d).hom.app W x) at hx
      rw [hx]
      have hm :
          (holomorphicRingSheaf X d).obj.map
                ((Opens.map (underlyingContinuousMap X)).map Limits.prod.snd).op ≫
              (holomorphicRingSheaf X d).obj.map
                ((analyticOpenStarPostIso X U).hom.app W.unop).left.op =
            (holomorphicRingSheaf X d).obj.map Limits.prod.snd.op := by
        erw [← (holomorphicRingSheaf X d).obj.map_comp]
        congr 1
      exact congr_arg (fun f ↦ f ((regularToHolomorphicRingSheaf X d).hom.app W x))
        (congr_arg RingCat.Hom.hom hm))).symm

noncomputable def restrictionRightAdjointIso (U : X.left.Opens) :=
  globalPushforwardCompIso X d U ≪≫ compositePushforwardIso X d U ≪≫
    (localPushforwardCompIso X d U).symm

/-- Module analytification commutes with restriction to an algebraic open, up to the local
regular-to-holomorphic pullback. -/
noncomputable def moduleAnalytificationOverIso (U : X.left.Opens) :
    moduleAnalytification X d ⋙
        SheafOfModules.overFunctor (holomorphicRingSheaf X d) (analyticOpen X U) ≅
      SheafOfModules.overFunctor X.left.ringCatSheaf U ⋙
        localModuleAnalytification X d U := by
  let adj₁ := (moduleAnalytificationAdjunction X d).comp
    (SheafOfModules.overPushforwardOverAdj
      (R := holomorphicRingSheaf X d) (analyticOpen X U))
  let adj₂ := (SheafOfModules.overPushforwardOverAdj
    (R := X.left.ringCatSheaf) U).comp (localModuleAnalytificationAdjunction X d U)
  exact ((conjugateIsoEquiv adj₁ adj₂).symm
    (restrictionRightAdjointIso X d U)).symm

/-- Pulling an algebraic open cover back to complex points gives an analytic open cover. -/
theorem analyticOpen_coversTop {I : Type} (U : I → X.left.Opens)
    (hU : (Opens.grothendieckTopology X.left).CoversTop U) :
    (Opens.grothendieckTopology (ComplexPoint X)).CoversTop (analyticOpen X ∘ U) := by
  rw [Opens.coversTop_iff] at hU ⊢
  exact hU.comap (underlyingContinuousMap X).hom

/-- Module analytification preserves invertible sheaves: algebraic local trivializations pull back
to holomorphic local trivializations on the inverse-image cover. -/
theorem moduleAnalytification_isInvertible (L : X.left.Modules)
    (hL : TauCeti.SheafOfModules.IsInvertible L) :
    TauCeti.SheafOfModules.IsInvertible ((moduleAnalytification X d).obj L) := by
  letI : ∀ U : X.left.Opens,
      HasSheafify ((Opens.grothendieckTopology X.left).over U) AddCommGrpCat.{0} :=
    fun U ↦ opensOverHasSheafify U
  letI : ∀ U : X.left.Opens,
      HasWeakSheafify ((Opens.grothendieckTopology X.left).over U) AddCommGrpCat.{0} :=
    fun _ ↦ HasSheafify.isRightAdjoint
  letI : ∀ U : X.left.Opens,
      ((Opens.grothendieckTopology X.left).over U).WEqualsLocallyBijective
        AddCommGrpCat.{0} := fun _ ↦ inferInstance
  letI : ∀ V : Opens (ComplexPoint X),
      HasSheafify ((Opens.grothendieckTopology (ComplexPoint X)).over V)
        AddCommGrpCat.{0} := fun V ↦ opensOverHasSheafify V
  letI : ∀ V : Opens (ComplexPoint X),
      HasWeakSheafify ((Opens.grothendieckTopology (ComplexPoint X)).over V)
        AddCommGrpCat.{0} := fun _ ↦ HasSheafify.isRightAdjoint
  letI : ∀ V : Opens (ComplexPoint X),
      ((Opens.grothendieckTopology (ComplexPoint X)).over V).WEqualsLocallyBijective
        AddCommGrpCat.{0} := fun _ ↦ inferInstance
  letI : TauCeti.SheafOfModules.IsInvertible L := hL
  let t := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible L
  let s : TauCeti.SheafOfModules.LocalTrivializations
      ((moduleAnalytification X d).obj L) :=
    { I := t.I
      X := fun i ↦ analyticOpen X (t.X i)
      coversTop := analyticOpen_coversTop X t.X t.coversTop
      iso := fun i ↦
        (localModuleAnalytificationFreePUnitIso X d (t.X i)).symm ≪≫
          (localModuleAnalytification X d (t.X i)).mapIso (t.iso i) ≪≫
            ((moduleAnalytificationOverIso X d (t.X i)).app L).symm }
  exact s.isInvertible

end AlgebraicGeometry.ComplexPoint
