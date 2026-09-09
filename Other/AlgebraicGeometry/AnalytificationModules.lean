/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RegularFunctionsHolomorphic
public import Other.AlgebraicGeometry.HolomorphicLineBundleModule
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Analytification of algebraic sheaves of modules

The evaluation map from regular functions to holomorphic functions gives a pullback
functor from algebraic modules to holomorphic modules. Its right adjoint takes the
direct image and restricts scalars along evaluation.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec ↧ℂ) (d : ℕ)
  [SmoothOfRelativeDimension d s]

local instance underlyingContinuousMap_siteContinuous :
    (Opens.map (underlyingContinuousMap s)).IsContinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X s))) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreserving_opens_map (underlyingContinuousMap s))
    (coverPreserving_opens_map (underlyingContinuousMap s))

/-- The structure-sheaf evaluation map with values in the category of rings. -/
def regularToHolomorphicRingSheaf :
    X.ringCatSheaf ⟶ (TopCat.Sheaf.pushforward RingCat
      (underlyingContinuousMap s)).obj (holomorphicRingSheaf s d) where
  hom := Functor.whiskerRight (regularToHolomorphicSheaf s d).hom
    (forget₂ CommRingCat RingCat)

local instance regularToHolomorphic_presheafPushforward_isRightAdjoint :
    (PresheafOfModules.pushforward.{0} (regularToHolomorphicRingSheaf s d).hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top (regularToHolomorphicRingSheaf s d).hom)

local instance regularToHolomorphic_pushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{0} (regularToHolomorphicRingSheaf s d)).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction
    (regularToHolomorphicRingSheaf s d)).isRightAdjoint

/-- The direct image of holomorphic modules, with the algebraic structure sheaf
acting by evaluation of regular functions. -/
def holomorphicModulePushforward :
    SheafOfModules (holomorphicRingSheaf s d) ⥤ X.Modules :=
  SheafOfModules.pushforward (regularToHolomorphicRingSheaf s d)

/-- Analytification of algebraic sheaves of modules by inverse image and extension
of scalars from regular to holomorphic functions. -/
def moduleAnalytification :
    X.Modules ⥤ SheafOfModules (holomorphicRingSheaf s d) :=
  SheafOfModules.pullback (regularToHolomorphicRingSheaf s d)

/-- Analytification is left adjoint to direct image with restriction of scalars. -/
def moduleAnalytificationAdjunction :
    moduleAnalytification s d ⊣ holomorphicModulePushforward s d :=
  SheafOfModules.pullbackPushforwardAdjunction (regularToHolomorphicRingSheaf s d)

instance moduleAnalytification_isLeftAdjoint :
    (moduleAnalytification s d).IsLeftAdjoint :=
  (moduleAnalytificationAdjunction s d).isLeftAdjoint

local instance underlyingContinuousMap_opensMap_final :
    (Opens.map (underlyingContinuousMap s)).Final where
  out U := by
    let V : StructuredArrow U (Opens.map (underlyingContinuousMap s)) :=
      StructuredArrow.mk (Y := ⊤) (homOfLE le_top)
    have hV : Limits.IsTerminal V :=
      Limits.IsTerminal.ofUniqueHom
        (fun W ↦ StructuredArrow.homMk (homOfLE le_top)) (fun _ _ ↦ by
          apply StructuredArrow.hom_ext
          exact Subsingleton.elim _ _)
    exact isConnected_of_isTerminal _ hV

/-- Analytification sends the algebraic structure sheaf, as a module, to the
holomorphic structure sheaf. -/
def moduleAnalytificationUnitIso :
    (moduleAnalytification s d).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit (holomorphicRingSheaf s d) :=
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit (regularToHolomorphicRingSheaf s d))
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal (regularToHolomorphicRingSheaf s d))

end AlgebraicGeometry.ComplexPoint
