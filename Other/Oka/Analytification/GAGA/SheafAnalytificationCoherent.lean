/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Stability
public import Other.Oka.AnalyticSpace.Coherent
public import Other.Oka.AlgebraicGeometry.Modules.CoherentLocalPresentation
public import Other.Oka.Analytification.GAGA.SheafAnalytification

/-!
# Coherence of analytifications of finitely presented sheaves

The pullback of a cokernel of a morphism of finite free sheaves along any morphism of locally
ringed spaces from a complex analytic space is coherent: pullback is right exact and sends free
sheaves to free sheaves, and finite free sheaves on an analytic space are coherent by Oka's
theorem (`ComplexAnalytic.AnalyticSpace.isCoherent_free`).

Applied to the comparison morphism `π : X^an ⟶ X` and to its restrictions over opens, this gives
coherence of `F^an` for `F` globally a cokernel of finite free sheaves, and coherence of
`F^an|_{π⁻¹ U}` whenever `F|_U` is such a cokernel.

## Main results

- `ComplexAnalytic.isCoherent_pullbackModules_cokernel`: the general statement.
- `ComplexAnalytic.isCoherent_analytificationModules_of_iso_cokernel`: `F^an` is coherent when
  `F` is a cokernel of finite free sheaves.
- `ComplexAnalytic.isCoherent_restrictModules_analytificationModules`: `F^an|_{π⁻¹ U}` is
  coherent when `F|_U` is a cokernel of finite free sheaves.
- `ComplexAnalytic.exists_isCoherent_restrictModules_analytificationModules`: for `F` coherent,
  `F^an` is coherent on a neighbourhood of every point of `X^an`.

The global statement `ComplexAnalytic.isCoherent_analytificationModules` is deduced from the
local one in `Other/Oka/Analytification/GAGA/SheafAnalytificationIsCoherent.lean`, by the locality of
coherence for open subspaces
(`AlgebraicGeometry.LocallyRingedSpace.isCoherent_of_isCoherent_restrictModules`).
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

open AnalyticSpace

/-- **The pullback of a cokernel of finite free sheaves to a complex analytic space is
coherent**, along any morphism of locally ringed spaces. -/
theorem isCoherent_pullbackModules_cokernel {Z : AnalyticSpace.{u}}
    {Y : LocallyRingedSpace.{u}} (f : Z.toLocallyRingedSpace ⟶ Y) {I K : Type u} [Finite I]
    [Finite K] (ψ : SheafOfModules.free (R := Y.ringSheaf) I ⟶ SheafOfModules.free K) :
    (f.pullbackModules.obj (cokernel ψ)).IsCoherent := by
  haveI : PreservesColimits f.pullbackModules := f.pullbackModulesAdj.leftAdjoint_preservesColimits
  haveI : (f.pullbackModules.obj (SheafOfModules.free I)).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso
      (M := SheafOfModules.free (R := Z.toLocallyRingedSpace.ringSheaf) I)
      (f.pullbackModulesFreeIso I).symm
  haveI : (SheafOfModules.free (R := Z.toLocallyRingedSpace.ringSheaf) K).IsCoherent :=
    Z.isCoherent_free K
  haveI : (f.pullbackModules.obj (SheafOfModules.free K)).IsCoherent :=
    SheafOfModules.IsCoherent.of_iso
      (M := SheafOfModules.free (R := Z.toLocallyRingedSpace.ringSheaf) K)
      (f.pullbackModulesFreeIso K).symm
  haveI : (cokernel (f.pullbackModules.map ψ)).IsCoherent :=
    SheafOfModules.IsCoherent.cokernel _
  exact SheafOfModules.IsCoherent.of_iso (M := cokernel (f.pullbackModules.map ψ))
    (PreservesCokernel.iso f.pullbackModules ψ).symm

/-- The pullback to a complex analytic space of a sheaf isomorphic to a cokernel of finite free
sheaves is coherent. -/
theorem isCoherent_pullbackModules_of_iso_cokernel {Z : AnalyticSpace.{u}}
    {Y : LocallyRingedSpace.{u}} (f : Z.toLocallyRingedSpace ⟶ Y) {I K : Type u} [Finite I]
    [Finite K] (ψ : SheafOfModules.free (R := Y.ringSheaf) I ⟶ SheafOfModules.free K)
    {F : SheafOfModules.{u} Y.ringSheaf} (e : F ≅ cokernel ψ) :
    (f.pullbackModules.obj F).IsCoherent :=
  haveI := isCoherent_pullbackModules_cokernel f ψ
  SheafOfModules.IsCoherent.of_iso.{u} (f.pullbackModules.mapIso e).symm

/-- The pullback to a complex analytic space of a sheaf presented by a colimit cokernel cofork
of finite free sheaves is coherent. -/
theorem isCoherent_pullbackModules_of_isColimit {Z : AnalyticSpace.{u}}
    {Y : LocallyRingedSpace.{u}} (f : Z.toLocallyRingedSpace ⟶ Y) {I K : Type u} [Finite I]
    [Finite K] (ψ : SheafOfModules.free (R := Y.ringSheaf) I ⟶ SheafOfModules.free K)
    {F : SheafOfModules.{u} Y.ringSheaf} (g : SheafOfModules.free K ⟶ F) (H : ψ ≫ g = 0)
    (hc : IsColimit (CokernelCofork.ofπ g H)) :
    (f.pullbackModules.obj F).IsCoherent :=
  isCoherent_pullbackModules_of_iso_cokernel f ψ
    (hc.coconePointUniqueUpToIso (colimit.isColimit _))

variable (X : SchemeLFTℂ.{u})

/-- **The analytification of a cokernel of finite free sheaves is coherent.** -/
theorem isCoherent_analytificationModules_of_iso_cokernel {I K : Type u} [Finite I] [Finite K]
    (ψ : SheafOfModules.free (R := X.obj.left.toLocallyRingedSpace.ringSheaf) I ⟶
      SheafOfModules.free K)
    {F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf} (e : F ≅ cokernel ψ) :
    ((analytificationModules X).obj F).IsCoherent :=
  isCoherent_pullbackModules_of_iso_cokernel (analytificationπLRS X) ψ e

/-- **The analytification over an open of a cokernel of finite free sheaves is coherent.** -/
theorem isCoherent_analytificationModulesRestrict_of_iso_cokernel
    (U : Opens (schemeToOverSpec.obj X.obj).left) {I K : Type u} [Finite I] [Finite K]
    (ψ : SheafOfModules.free
        (R := (X.obj.left.toLocallyRingedSpace.restrict U.isOpenEmbedding).ringSheaf) I ⟶
      SheafOfModules.free K)
    {F : SheafOfModules.{u} (X.obj.left.toLocallyRingedSpace.restrict U.isOpenEmbedding).ringSheaf}
    (e : F ≅ cokernel ψ) :
    ((analytificationModulesRestrict X U).obj F).IsCoherent :=
  isCoherent_pullbackModules_of_iso_cokernel (restrictπ (analytificationπ X) U).left ψ e

/-- **`F^an` is coherent over `π⁻¹ U` whenever `F|_U` is a cokernel of finite free sheaves**, for
an open `U ⊆ X`. This is the local form of the coherence of the analytification of a coherent
sheaf. -/
theorem isCoherent_restrictModules_analytificationModules
    (U : Opens (schemeToOverSpec.obj X.obj).left) {I K : Type u} [Finite I] [Finite K]
    (ψ : SheafOfModules.free
        (R := (X.obj.left.toLocallyRingedSpace.restrict U.isOpenEmbedding).ringSheaf) I ⟶
      SheafOfModules.free K)
    {F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf}
    (e : (X.obj.left.toLocallyRingedSpace.restrictModules U).obj F ≅ cokernel ψ) :
    (((analytification.obj X).toLocallyRingedSpace.restrictModules
      (analytificationPreimage X U)).obj ((analytificationModules X).obj F)).IsCoherent :=
  haveI : ((analytificationModulesRestrict X U).obj
      ((X.obj.left.toLocallyRingedSpace.restrictModules U).obj F)).IsCoherent :=
    isCoherent_analytificationModulesRestrict_of_iso_cokernel X U ψ e
  SheafOfModules.IsCoherent.of_iso.{u}
    (M := (analytificationModulesRestrict X U).obj
      ((X.obj.left.toLocallyRingedSpace.restrictModules U).obj F))
    ((analytificationModulesRestrictIso X U).app F).symm

/-- `ComplexAnalytic.isCoherent_restrictModules_analytificationModules`, for `F|_U` presented by a
colimit cokernel cofork of finite free sheaves. -/
theorem isCoherent_restrictModules_analytificationModules_of_isColimit
    (U : Opens (schemeToOverSpec.obj X.obj).left) {I K : Type u} [Finite I] [Finite K]
    (ψ : SheafOfModules.free
        (R := (X.obj.left.toLocallyRingedSpace.restrict U.isOpenEmbedding).ringSheaf) I ⟶
      SheafOfModules.free K)
    {F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf}
    (g : SheafOfModules.free K ⟶ (X.obj.left.toLocallyRingedSpace.restrictModules U).obj F)
    (H : ψ ≫ g = 0) (hc : IsColimit (CokernelCofork.ofπ g H)) :
    (((analytification.obj X).toLocallyRingedSpace.restrictModules
      (analytificationPreimage X U)).obj ((analytificationModules X).obj F)).IsCoherent :=
  isCoherent_restrictModules_analytificationModules X U ψ
    (hc.coconePointUniqueUpToIso (colimit.isColimit _))

/-- **The analytification of a coherent sheaf is locally coherent**: every point of `X^an` has an
open neighbourhood `V` (the preimage of an open of `X`) such that `F^an|_V` is coherent.

The passage from this to `((analytificationModules X).obj F).IsCoherent` is the locality of
coherence for open subspaces of `X^an`, i.e. the comparison between restriction to an open
subspace and `SheafOfModules.over`, which is not available here. -/
theorem exists_isCoherent_restrictModules_analytificationModules
    (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent]
    (w : analytification.obj X) :
    ∃ (V : (analytification.obj X).Opens) (_ : w ∈ V),
      (((analytification.obj X).toLocallyRingedSpace.restrictModules V).obj
        ((analytificationModules X).obj F)).IsCoherent := by
  obtain ⟨U, hU, I, K, _, _, ψ, g, H, ⟨hc⟩⟩ :=
    Scheme.exists_restrictModules_isColimit_cokernelCofork X.obj.left F
      ((analytificationπ X).left.base w)
  exact ⟨analytificationPreimage X U, hU,
    isCoherent_restrictModules_analytificationModules_of_isColimit X U ψ g H hc⟩

end ComplexAnalytic

end
