/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.SheafAnalytificationCoherent
public import Other.Oka.AnalyticSpace.OpenSubspace
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.CoherentLocalPresentation

/-!
# Pullbacks of coherent sheaves to complex analytic spaces are coherent

Let `Z` be a complex analytic space, `Y` a locally ringed space and `f : Z ⟶ Y` a morphism of
locally ringed spaces. For every coherent sheaf of `𝒪_Y`-modules `M`, the pullback `f^* M` is a
coherent sheaf of `𝒪_Z`-modules (`ComplexAnalytic.isCoherent_pullbackModules_of_isCoherent`).

Near `f z`, `M` is a cokernel of finite free sheaves
(`AlgebraicGeometry.LocallyRingedSpace.exists_restrictModules_isColimit_cokernelCofork`), so over
the open `W = f⁻¹ U`, `f^* M` is the pullback along `f|_W : Z|_W ⟶ Y|_U` of such a cokernel,
which is coherent on the analytic space `Z|_W` by Oka's theorem
(`ComplexAnalytic.isCoherent_pullbackModules_of_isColimit`). Coherence is local
(`AlgebraicGeometry.LocallyRingedSpace.isCoherent_of_isCoherent_restrictModules`).
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

/-- Restricting a pullback `f^* M` to the preimage `f⁻¹ U` of an open `U` is pulling back the
restriction `M|_U` along `f|_{f⁻¹ U} : Z|_{f⁻¹ U} ⟶ Y|_U`. -/
noncomputable def restrictModulesPullbackModulesIso {Z Y : LocallyRingedSpace.{u}} (f : Z ⟶ Y)
    (U : Opens Y) (M : SheafOfModules.{u} Y.ringSheaf) :
    (Z.restrictModules ((Opens.map f.base).obj U)).obj (f.pullbackModules.obj M) ≅
      (restrictHom f U).pullbackModules.obj ((Y.restrictModules U).obj M) :=
  (LocallyRingedSpace.Hom.pullbackModulesComp _ f).app M ≪≫
    (LocallyRingedSpace.Hom.pullbackModulesCongr (restrictHom_fac f U).symm).app M ≪≫
    ((LocallyRingedSpace.Hom.pullbackModulesComp _ _).app M).symm

/-- **The pullback of a coherent sheaf to a complex analytic space is coherent**, along any
morphism of locally ringed spaces. -/
theorem isCoherent_pullbackModules_of_isCoherent {Z : AnalyticSpace.{u}}
    {Y : LocallyRingedSpace.{u}} (f : Z.toLocallyRingedSpace ⟶ Y)
    (M : SheafOfModules.{u} Y.ringSheaf) [M.IsCoherent] :
    (f.pullbackModules.obj M).IsCoherent := by
  refine LocallyRingedSpace.isCoherent_of_isCoherent_restrictModules _ _ fun z ↦ ?_
  obtain ⟨U, hU, I, K, _, _, ψ, g, H, ⟨hc⟩⟩ :=
    LocallyRingedSpace.exists_restrictModules_isColimit_cokernelCofork Y M (f.base z)
  refine ⟨(Opens.map f.base).obj U, hU, ?_⟩
  have : ((restrictHom f U).pullbackModules.obj ((Y.restrictModules U).obj M)).IsCoherent :=
    isCoherent_pullbackModules_of_isColimit (Z := Z.restrict ((Opens.map f.base).obj U))
      (restrictHom f U) ψ g H hc
  exact @SheafOfModules.IsCoherent.of_iso.{u} _ _ _ _ _ _ _ _ _ _
    (restrictModulesPullbackModulesIso f U M).symm this

end ComplexAnalytic

end
