/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.TauCeti.SheafOfModules.Restriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Pullback of invertible sheaves on schemes

An invertible sheaf is locally a free rank-one sheaf.  This file proves that inverse image along
an arbitrary morphism of schemes preserves that property.  The proof pulls a trivializing open
cover back along the underlying continuous map and compares restriction with inverse image around
the resulting Cartesian square of open subschemes.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme}

/-- The inverse-image functor on opens induced by a continuous map is final.  The terminal open in
the target supplies a terminal object in every structured-arrow category. -/
theorem opensMapFinal (f : X ⟶ Y) : (Opens.map f.base).Final := by
  constructor
  intro V
  let T : StructuredArrow V (Opens.map f.base) :=
    StructuredArrow.mk (Y := ⊤) (homOfLE le_top)
  have hT : Limits.IsTerminal T :=
    Limits.IsTerminal.ofUniqueHom
      (fun W ↦ StructuredArrow.homMk (homOfLE le_top))
      (fun _ _ ↦ by
        apply StructuredArrow.hom_ext
        exact Subsingleton.elim _ _)
  exact isConnected_of_isTerminal _ hT

/-- Pullback along a morphism of schemes sends the structure sheaf, viewed as its standard module,
to the structure sheaf of the source. -/
def pullbackUnitIso (f : X ⟶ Y) :
    (pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI : (Opens.map f.base).Final := opensMapFinal f
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  let p := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  have hp : IsIso p := @SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
    (Opens Y) inferInstance (Opens X) inferInstance
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    (Opens.map f.base) Y.ringCatSheaf X.ringCatSheaf inferInstance
    f.toRingCatSheafHom inferInstance (opensMapFinal f)
  exact @asIso _ _ _ _ p hp

/-- A Tau Ceti local rank-one trivialization over an open, expressed after passing from the
over-site to the corresponding open subscheme. -/
def localUnitIso {M : SheafOfModules Y.ringCatSheaf} (U : Y.Opens)
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) PUnit ≅ M.over U) :
    SheafOfModules.unit (U : Scheme).ringCatSheaf ≅ (restrictFunctor U.ι).obj M :=
  let E := overEquiv U
  ((E.functor.mapIso
      (TauCeti.SheafOfModules.freePUnitIsoUnit (Y.ringCatSheaf.over U)) ≪≫
        U.sheafOfModulesEquivOverUnit Y.ringCatSheaf).symm ≪≫
    E.functor.mapIso e ≪≫
      (overFunctorEquiv U).app M)

/-- Pull a chosen rank-one trivialization over `U` through the Cartesian square formed by `f` and
the inclusions of `U` and `f ⁻¹ U`. -/
def pullbackLocalUnitIso (f : X ⟶ Y) (M : SheafOfModules Y.ringCatSheaf) (U : Y.Opens)
    (e : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ (restrictFunctor U.ι).obj M) :
    SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf ≅
      (restrictFunctor (f ⁻¹ᵁ U).ι).obj ((pullback f).obj M) :=
  let V := f ⁻¹ᵁ U
  let g := f ∣_ U
  (pullbackUnitIso g).symm ≪≫
    (pullback g).mapIso e ≪≫
    (pullback g).mapIso ((restrictFunctorIsoPullback U.ι).app M) ≪≫
    (pullbackComp g U.ι).app M ≪≫
    (pullbackCongr (morphismRestrict_ι f U)).app M ≪≫
    ((pullbackComp V.ι f).app M).symm ≪≫
    ((restrictFunctorIsoPullback V.ι).app ((pullback f).obj M)).symm

/-- A local trivialization of `M` pulls back to a local trivialization of its inverse image. -/
def localTrivializationsPullback (f : X ⟶ Y) (M : SheafOfModules Y.ringCatSheaf)
    (t : TauCeti.SheafOfModules.LocalTrivializations M) :
    TauCeti.SheafOfModules.LocalTrivializations ((pullback f).obj M) where
  I := t.I
  X := fun i ↦ f ⁻¹ᵁ t.X i
  coversTop := by
    have ht := t.coversTop
    rw [Opens.coversTop_iff] at ht ⊢
    exact ht.comap f.base.hom
  iso i := by
    let U := t.X i
    let V := f ⁻¹ᵁ U
    let E := overEquiv V
    let eScheme := pullbackLocalUnitIso f M U (localUnitIso U (t.iso i))
    let eOver : SheafOfModules.unit (X.ringCatSheaf.over V) ≅
        ((pullback f).obj M).over V :=
      E.fullyFaithfulFunctor.preimageIso
        (V.sheafOfModulesEquivOverUnit X.ringCatSheaf ≪≫
          eScheme ≪≫
          ((overFunctorEquiv V).app ((pullback f).obj M)).symm)
    exact TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over V) ≪≫ eOver

/-- Inverse image along any morphism of schemes preserves invertible sheaves. -/
theorem pullback_isInvertible (f : X ⟶ Y) (M : SheafOfModules Y.ringCatSheaf)
    (hM : TauCeti.SheafOfModules.IsInvertible M) :
    TauCeti.SheafOfModules.IsInvertible ((pullback f).obj M) := by
  let _ : TauCeti.SheafOfModules.IsInvertible M := hM
  exact (localTrivializationsPullback f M
    (TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible M)).isInvertible

end AlgebraicGeometry.Scheme.Modules
