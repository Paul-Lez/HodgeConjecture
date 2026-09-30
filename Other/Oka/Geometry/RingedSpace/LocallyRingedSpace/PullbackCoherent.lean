/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.CoherentLocalPresentation
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.Coherent
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Free
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.LocallyFree
public import Other.Oka.AnalyticSpace.Restrict

/-!
# Pullbacks of coherent sheaves to spaces with coherent structure sheaf

Let `f : Z ⟶ Y` be a morphism of locally ringed spaces such that `𝒪_Z` is coherent. For every
coherent sheaf of `𝒪_Y`-modules `M`, the pullback `f^* M` is coherent
(`AlgebraicGeometry.LocallyRingedSpace.isCoherent_pullbackModules_of_isCoherentStructureSheaf`);
for instance for `Z` a locally noetherian scheme.

Near `f z`, `M` is a cokernel of a morphism of finite free sheaves
(`AlgebraicGeometry.LocallyRingedSpace.exists_restrictModules_isColimit_cokernelCofork`); pullback
preserves cokernels and finite free sheaves, finite free sheaves on open subspaces of `Z` are
coherent, and cokernels of morphisms between coherent sheaves are coherent. Coherence is local
(`AlgebraicGeometry.LocallyRingedSpace.isCoherent_of_isCoherent_restrictModules`).
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {Z Y : LocallyRingedSpace.{u}}

/-- On a locally ringed space with coherent structure sheaf, finite free sheaves on open
subspaces are coherent. -/
theorem isCoherent_free_restrict (hZ : Z.IsCoherentStructureSheaf) (W : Opens Z)
    (K : Type u) [Finite K] :
    (SheafOfModules.free (R := (Z.restrict W.isOpenEmbedding).ringSheaf) K).IsCoherent := by
  haveI : (SheafOfModules.unit Z.ringSheaf).IsCoherent := hZ
  haveI : (SheafOfModules.free (R := Z.ringSheaf) K).IsCoherent := SheafOfModules.IsCoherent.free K
  haveI := isCoherent_restrictModules (SheafOfModules.free (R := Z.ringSheaf) K) W
  exact SheafOfModules.IsCoherent.of_iso.{u}
    ((Z.ofRestrict W.isOpenEmbedding).pullbackModulesFreeIso K)

/-- The pullback of a cokernel of finite free sheaves along `f : Z ⟶ Y` is coherent if finite
free sheaves on `Z` are. -/
theorem isCoherent_pullbackModules_cokernel_of_isCoherent_free (f : Z ⟶ Y) {I K : Type u}
    [Finite I] (hK : (SheafOfModules.free (R := Z.ringSheaf) K).IsCoherent)
    (ψ : SheafOfModules.free (R := Y.ringSheaf) I ⟶ SheafOfModules.free K) :
    (f.pullbackModules.obj (cokernel ψ)).IsCoherent := by
  haveI : PreservesColimits f.pullbackModules :=
    f.pullbackModulesAdj.leftAdjoint_preservesColimits
  haveI : (f.pullbackModules.obj (SheafOfModules.free I)).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso
      (M := SheafOfModules.free (R := Z.ringSheaf) I) (f.pullbackModulesFreeIso I).symm
  haveI : (f.pullbackModules.obj (SheafOfModules.free K)).IsCoherent :=
    SheafOfModules.IsCoherent.of_iso
      (M := SheafOfModules.free (R := Z.ringSheaf) K) (f.pullbackModulesFreeIso K).symm
  haveI : (cokernel (f.pullbackModules.map ψ)).IsCoherent :=
    SheafOfModules.IsCoherent.cokernel _
  exact SheafOfModules.IsCoherent.of_iso (M := cokernel (f.pullbackModules.map ψ))
    (PreservesCokernel.iso f.pullbackModules ψ).symm

/-- The pullback of a sheaf presented by a colimit cokernel cofork of finite free sheaves along
`f : Z ⟶ Y` is coherent if finite free sheaves on `Z` are. -/
theorem isCoherent_pullbackModules_of_isColimit_of_isCoherent_free (f : Z ⟶ Y) {I K : Type u}
    [Finite I] (hK : (SheafOfModules.free (R := Z.ringSheaf) K).IsCoherent)
    (ψ : SheafOfModules.free (R := Y.ringSheaf) I ⟶ SheafOfModules.free K)
    {F : SheafOfModules.{u} Y.ringSheaf} (g : SheafOfModules.free K ⟶ F) (H : ψ ≫ g = 0)
    (hc : IsColimit (CokernelCofork.ofπ g H)) :
    (f.pullbackModules.obj F).IsCoherent :=
  haveI := isCoherent_pullbackModules_cokernel_of_isCoherent_free f hK ψ
  let e : F ≅ cokernel ψ := hc.coconePointUniqueUpToIso (colimit.isColimit _)
  SheafOfModules.IsCoherent.of_iso.{u} (M := f.pullbackModules.obj (cokernel ψ))
    (f.pullbackModules.mapIso e).symm

/-- **The pullback of a coherent sheaf to a locally ringed space with coherent structure sheaf is
coherent.** -/
theorem isCoherent_pullbackModules_of_isCoherentStructureSheaf (hZ : Z.IsCoherentStructureSheaf)
    (f : Z ⟶ Y) (M : SheafOfModules.{u} Y.ringSheaf) [M.IsCoherent] :
    (f.pullbackModules.obj M).IsCoherent := by
  refine isCoherent_of_isCoherent_restrictModules _ _ fun z ↦ ?_
  obtain ⟨U, hU, I, K, _, _, ψ, g, H, ⟨hc⟩⟩ :=
    exists_restrictModules_isColimit_cokernelCofork Y M (f.base z)
  refine ⟨(Opens.map f.base).obj U, hU, ?_⟩
  let e : (Z.restrictModules ((Opens.map f.base).obj U)).obj (f.pullbackModules.obj M) ≅
      (ComplexAnalytic.restrictHom f U).pullbackModules.obj ((Y.restrictModules U).obj M) :=
    (Hom.pullbackModulesComp _ f).app M ≪≫
      (Hom.pullbackModulesCongr (ComplexAnalytic.restrictHom_fac f U).symm).app M ≪≫
      ((Hom.pullbackModulesComp _ _).app M).symm
  have := isCoherent_pullbackModules_of_isColimit_of_isCoherent_free
    (ComplexAnalytic.restrictHom f U) (isCoherent_free_restrict hZ ((Opens.map f.base).obj U) K)
    ψ g H hc
  exact SheafOfModules.IsCoherent.of_iso.{u}
    (M := (ComplexAnalytic.restrictHom f U).pullbackModules.obj ((Y.restrictModules U).obj M))
    e.symm

end AlgebraicGeometry.LocallyRingedSpace

end
