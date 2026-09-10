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

variable (X : Over (Spec ↧ℂ)) (d : ℕ)
  [SmoothOfRelativeDimension d X.hom]

local instance underlyingContinuousMap_siteContinuous :
    (Opens.map (underlyingContinuousMap X)).IsContinuous
      (Opens.grothendieckTopology X.left) (Opens.grothendieckTopology
        (TopCat.of (ComplexPoint X))) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreserving_opens_map (underlyingContinuousMap X))
    (coverPreserving_opens_map (underlyingContinuousMap X))

/-- The structure-sheaf evaluation map with values in the category of rings. -/
def regularToHolomorphicRingSheaf :
    X.left.ringCatSheaf ⟶ (TopCat.Sheaf.pushforward RingCat
      (underlyingContinuousMap X)).obj (holomorphicRingSheaf X d) where
  hom := Functor.whiskerRight (regularToHolomorphicSheaf X d).hom
    (forget₂ CommRingCat RingCat)

local instance regularToHolomorphic_presheafPushforward_isRightAdjoint :
    (PresheafOfModules.pushforward.{0} (regularToHolomorphicRingSheaf X d).hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top (regularToHolomorphicRingSheaf X d).hom)

local instance regularToHolomorphic_pushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{0} (regularToHolomorphicRingSheaf X d)).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction
    (regularToHolomorphicRingSheaf X d)).isRightAdjoint

/-- The direct image of holomorphic modules, with the algebraic structure sheaf
acting by evaluation of regular functions. -/
def holomorphicModulePushforward :
    SheafOfModules (holomorphicRingSheaf X d) ⥤ X.left.Modules :=
  SheafOfModules.pushforward (regularToHolomorphicRingSheaf X d)

/-- Analytification of algebraic sheaves of modules by inverse image and extension
of scalars from regular to holomorphic functions. -/
def moduleAnalytification :
    X.left.Modules ⥤ SheafOfModules (holomorphicRingSheaf X d) :=
  SheafOfModules.pullback (regularToHolomorphicRingSheaf X d)

/-- Analytification is left adjoint to direct image with restriction of scalars. -/
def moduleAnalytificationAdjunction :
    moduleAnalytification X d ⊣ holomorphicModulePushforward X d :=
  SheafOfModules.pullbackPushforwardAdjunction (regularToHolomorphicRingSheaf X d)

instance moduleAnalytification_isLeftAdjoint :
    (moduleAnalytification X d).IsLeftAdjoint :=
  (moduleAnalytificationAdjunction X d).isLeftAdjoint

local instance underlyingContinuousMap_opensMap_final :
    (Opens.map (underlyingContinuousMap X)).Final where
  out U := by
    let V : StructuredArrow U (Opens.map (underlyingContinuousMap X)) :=
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
    (moduleAnalytification X d).obj (SheafOfModules.unit X.left.ringCatSheaf) ≅
      SheafOfModules.unit (holomorphicRingSheaf X d) :=
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit (regularToHolomorphicRingSheaf X d))
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal (regularToHolomorphicRingSheaf X d))

end AlgebraicGeometry.ComplexPoint
