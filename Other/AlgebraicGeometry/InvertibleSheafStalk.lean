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

public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesStalk
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.RestrictModulesOver
public import Other.TauCeti.SheafOfModules.Free
public import Other.TauCeti.SheafOfModules.LocalTriviality
public import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Stalks of invertible sheaves

An invertible sheaf on a locally ringed space has stalk linearly equivalent to the local ring at
every point. The proof transports a local trivialization from the slice site to an open subspace,
takes its stalk, and then transports back along the open immersion's stalk-ring equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- The stalk of an invertible sheaf is a free module of rank one over the local ring. -/
theorem nonempty_stalkLinearEquiv_of_isInvertible (Y : LocallyRingedSpace.{u})
    (M : SheafOfModules.{u} Y.ringSheaf)
    [TauCeti.SheafOfModules.IsInvertible.{u, u, u} M] (y : Y) :
    Nonempty (((Y.stalkFunctor y).obj M) ≃ₗ[Y.presheaf.stalk y] Y.presheaf.stalk y) := by
  let t := TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible M
  obtain ⟨i, hy⟩ := ((Opens.coversTop_iff _ t.X).mp t.coversTop).exists_mem y
  let U := t.X i
  let YU := Y.restrict U.isOpenEmbedding
  let E := restrictOverEquiv Y U
  let eUnit : SheafOfModules.unit YU.ringSheaf ≅
      E.functor.obj (SheafOfModules.unit (Y.ringSheaf.over U)) :=
    (Y.ofRestrict U.isOpenEmbedding).pullbackModulesUnitIso.symm ≪≫
      restrictModulesObjIso Y U (SheafOfModules.unit Y.ringSheaf)
  let eLocal : SheafOfModules.free (R := YU.ringSheaf) PUnit ≅
      (Y.restrictModules U).obj M :=
    TauCeti.SheafOfModules.freePUnitIsoUnit YU.ringSheaf ≪≫ eUnit ≪≫
      E.functor.mapIso
        ((TauCeti.SheafOfModules.freePUnitIsoUnit (Y.ringSheaf.over U)).symm ≪≫ t.iso i) ≪≫
      (restrictModulesObjIso Y U M).symm
  let yU : YU := ⟨y, hy⟩
  let eStalk := (YU.stalkFunctor yU).mapIso eLocal
  let eFree :
      ((YU.stalkFunctor yU).obj (SheafOfModules.free (R := YU.ringSheaf) PUnit))
        ≃ₗ[YU.presheaf.stalk yU] YU.presheaf.stalk yU :=
    (basisStalkFree PUnit yU).repr ≪≫ₗ
      Finsupp.uniqueLinearEquiv (YU.presheaf.stalk yU) (YU.presheaf.stalk yU) PUnit.unit
  let eModule :
      ((YU.stalkFunctor yU).obj ((Y.restrictModules U).obj M))
        ≃ₗ[YU.presheaf.stalk yU] YU.presheaf.stalk yU :=
    eStalk.symm.toLinearEquiv ≪≫ₗ eFree
  let f := Y.ofRestrict U.isOpenEmbedding
  let eRing := f.stalkMapRingEquiv yU
  let forwardInvPair : RingHomInvPair (RingHomClass.toRingHom eRing)
      (RingHomClass.toRingHom eRing.symm) :=
    RingHomInvPair.of_ringEquiv eRing
  let backwardInvPair : RingHomInvPair (RingHomClass.toRingHom eRing.symm)
      (RingHomClass.toRingHom eRing) :=
    RingHomInvPair.symm _ _
  let ePull := f.stalkPullbackModulesSemilinearEquiv yU M
  let ePullMap := ePull.toLinearMap
    (σ' := RingHomClass.toRingHom eRing.symm)
  let ePullEquiv := ePull.toEquiv
    (σ' := RingHomClass.toRingHom eRing.symm)
  change Nonempty (((Y.stalkFunctor (f.base yU)).obj M) ≃ₗ[
    Y.presheaf.stalk (f.base yU)] Y.presheaf.stalk (f.base yU))
  refine ⟨{
    toFun := fun m ↦ eRing.symm (eModule (ePullMap m))
    invFun := fun r ↦ ePullEquiv.symm (eModule.symm (eRing r))
    left_inv := fun m ↦ by
      change ePullEquiv.symm
        (eModule.symm (eRing (eRing.symm (eModule (ePullMap m))))) = m
      rw [eRing.apply_symm_apply, eModule.symm_apply_apply]
      change ePullEquiv.symm (ePullEquiv m) = m
      exact ePullEquiv.symm_apply_apply m
    right_inv := fun r ↦ by
      change eRing.symm
        (eModule (ePullMap (ePullEquiv.symm (eModule.symm (eRing r))))) = r
      change eRing.symm
        (eModule (ePullEquiv (ePullEquiv.symm (eModule.symm (eRing r))))) = r
      rw [ePullEquiv.apply_symm_apply, eModule.apply_symm_apply, eRing.symm_apply_apply]
    map_add' := fun a b ↦ by rw [map_add, map_add, map_add]
    map_smul' := fun r m ↦ by
      rw [map_smulₛₗ, map_smul, smul_eq_mul, map_mul]
      change eRing.symm (eRing r) * eRing.symm (eModule (ePullMap m)) =
        r * eRing.symm (eModule (ePullMap m))
      rw [eRing.symm_apply_apply] }⟩

end AlgebraicGeometry.LocallyRingedSpace
