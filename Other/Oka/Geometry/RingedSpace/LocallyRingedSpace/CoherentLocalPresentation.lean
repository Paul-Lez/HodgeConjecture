/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Presentation
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.RestrictModulesOver

/-!
# Coherent sheaves on a locally ringed space are locally cokernels of finite free sheaves

A coherent sheaf of modules `M` on a locally ringed space `Y` is, near every point, the cokernel
of a morphism of finite free sheaves: there is an open `U ∋ y` and an exact sequence
`𝒪_U^I ⟶ 𝒪_U^K ⟶ M|_U ⟶ 0` with `I`, `K` finite
(`AlgebraicGeometry.LocallyRingedSpace.exists_restrictModules_isColimit_cokernelCofork`).

This is the finite presentation of `M` over the slice site
(`SheafOfModules.IsCoherent.isFinitePresentation`) transported to the open subspace `Y|_U` along
the equivalence `AlgebraicGeometry.LocallyRingedSpace.restrictOverEquiv`, which carries `M.over U`
to the restriction `(Y.restrictModules U).obj M`
(`AlgebraicGeometry.LocallyRingedSpace.restrictModulesObjIso`). The scheme-theoretic analogue is
`AlgebraicGeometry.Scheme.exists_restrictModules_isColimit_cokernelCofork`.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable (Y : LocallyRingedSpace.{u})

/-- The structure sheaf of the open subspace `Y|_V` corresponds to the structure sheaf of the
slice `Over V` under `AlgebraicGeometry.LocallyRingedSpace.restrictOverEquiv`. -/
noncomputable def restrictOverEquivUnitIso (V : Opens Y.toPresheafedSpace) :
    SheafOfModules.unit (Y.restrict V.isOpenEmbedding).ringSheaf ≅
      (restrictOverEquiv Y V).functor.obj (SheafOfModules.unit (Y.ringSheaf.over V)) :=
  (Y.ofRestrict V.isOpenEmbedding).pullbackModulesUnitIso.symm ≪≫
    restrictModulesObjIso Y V (SheafOfModules.unit Y.ringSheaf)

/-- **A coherent sheaf on a locally ringed space is locally a cokernel of finite free sheaves**:
every point has an open neighbourhood `U` with a cokernel presentation
`𝒪_U^I ⟶ 𝒪_U^K ⟶ M|_U ⟶ 0`, `I` and `K` finite. -/
theorem exists_restrictModules_isColimit_cokernelCofork
    (M : SheafOfModules.{u} Y.ringSheaf) [M.IsCoherent] (y : Y) :
    ∃ (U : Opens Y.toPresheafedSpace) (_ : y ∈ U) (I K : Type u) (_ : Finite I) (_ : Finite K)
      (ψ : SheafOfModules.free (R := (Y.restrict U.isOpenEmbedding).ringSheaf) I ⟶
        SheafOfModules.free K)
      (g : SheafOfModules.free K ⟶ (Y.restrictModules U).obj M)
      (H : ψ ≫ g = 0), Nonempty (IsColimit (CokernelCofork.ofπ g H)) := by
  haveI := SheafOfModules.IsCoherent.isFinitePresentation M
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have hcov : ⨆ i, q.X i = ⊤ := (Opens.coversTop_iff _ q.X).1 q.coversTop
  obtain ⟨i, hi⟩ : ∃ i, y ∈ q.X i := by
    have : y ∈ (⊤ : Opens Y.toPresheafedSpace) := trivial
    rw [← hcov] at this
    exact Opens.mem_iSup.1 this
  haveI := hq
  let P := (q.presentation i).map (restrictOverEquiv Y (q.X i)).functor
    (restrictOverEquivUnitIso Y (q.X i))
  let P' := P.ofIsIso (restrictModulesObjIso Y (q.X i) M).inv
  haveI : Finite P'.generators.I :=
    inferInstanceAs (Finite (q.presentation i).generators.I)
  haveI : Finite P'.relations.I :=
    inferInstanceAs (Finite (q.presentation i).relations.I)
  exact ⟨q.X i, hi, P'.relations.I, P'.generators.I, inferInstance, inferInstance, _, _, _,
    ⟨P'.isColimit⟩⟩

end AlgebraicGeometry.LocallyRingedSpace

end
