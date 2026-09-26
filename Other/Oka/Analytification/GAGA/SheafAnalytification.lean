/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.StalkFlat
public import Other.Oka.AnalyticSpace.PullbackModulesStalk
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesComp

/-!
# The analytification of sheaves of modules on a scheme locally of finite type over `ℂ`

For `X` a scheme locally of finite type over `ℂ` and `π : X^an ⟶ X` the comparison morphism,
the analytification of sheaves of modules is the pullback
`F ↦ F^an := π^* F`:

```
ComplexAnalytic.analytificationModules X :
  SheafOfModules 𝒪_X ⥤ SheafOfModules 𝒪_{X^an}
```

It is exact: right exact as a left adjoint, left exact because the stalk maps of `π` are
(faithfully) flat (`ComplexAnalytic.faithfullyFlat_stalkMap_analytificationπ`). It sends `𝒪_X`
to `𝒪_{X^an}` and free sheaves to free sheaves, and it is compatible with restriction to an open
`U ⊆ X`: `F^an|_{π⁻¹ U} ≅ (F|_U)^an`, where the right side is the pullback along the restricted
comparison morphism `π⁻¹ U ⟶ U`, itself an analytification of `U`
(`ComplexAnalytic.IsAnalytification.restrict`) with faithfully flat stalk maps.

## Main definitions

- `ComplexAnalytic.analytificationModules`: the analytification functor `F ↦ F^an`.
- `ComplexAnalytic.analytificationModulesAdj`: it is left adjoint to `π_*`.
- `ComplexAnalytic.analytificationModulesUnitIso`: `𝒪_X^an ≅ 𝒪_{X^an}`.
- `ComplexAnalytic.analytificationModulesFreeIso`: `(𝒪_X^(I))^an ≅ 𝒪_{X^an}^(I)`.
- `ComplexAnalytic.analytificationModulesRestrict`: the analytification over an open `U ⊆ X`.
- `ComplexAnalytic.analytificationModulesRestrictIso`: `F^an|_{π⁻¹ U} ≅ (F|_U)^an`.
- `ComplexAnalytic.SchemeLFTℂ.restrict`, `ComplexAnalytic.analytificationRestrictIso`: an open
  subscheme `X|_U`, and `(X|_U)^an ≅ π⁻¹ U`.
- `ComplexAnalytic.analytificationModulesRestrictSchemeIso`: the same compatibility with
  `(F|_U)^an` the analytification of sheaves on the scheme `X|_U`.

## Main results

- `ComplexAnalytic.preservesFiniteLimits_analytificationModules` and
  `ComplexAnalytic.preservesColimits_analytificationModules`: the analytification is exact.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

namespace ComplexAnalytic

open AnalyticSpace

variable (X : SchemeLFTℂ.{u})

/-- The comparison morphism `π : X^an ⟶ X`, as a morphism of locally ringed spaces. -/
abbrev analytificationπLRS :
    (analytification.obj X).toLocallyRingedSpace ⟶ X.obj.left.toLocallyRingedSpace :=
  (analytificationπ X).left

/-- **The analytification of a sheaf of modules** on a scheme `X` locally of finite type over
`ℂ`: the pullback `F ↦ π^* F` along the comparison morphism `π : X^an ⟶ X`. -/
def analytificationModules :
    SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf ⥤
      SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf :=
  (analytificationπLRS X).pullbackModules

/-- **The analytification of sheaves is left adjoint to pushforward along `X^an ⟶ X`.** -/
def analytificationModulesAdj :
    analytificationModules X ⊣
      SheafOfModules.pushforward.{u} (analytificationπLRS X).toRingSheafHom :=
  (analytificationπLRS X).pullbackModulesAdj

instance : (analytificationModules X).IsLeftAdjoint :=
  (analytificationModulesAdj X).isLeftAdjoint

/-- **The analytification of sheaves is right exact**: it is a left adjoint. -/
theorem preservesColimits_analytificationModules :
    PreservesColimits (analytificationModules X) :=
  (analytificationModulesAdj X).leftAdjoint_preservesColimits

/-- **The analytification of sheaves is left exact**, because the stalk maps of `X^an ⟶ X` are
flat (`ComplexAnalytic.flat_stalkMap_analytificationπ`). No finiteness hypothesis is needed. -/
theorem preservesFiniteLimits_analytificationModules :
    PreservesFiniteLimits (analytificationModules X) :=
  (analytificationπ X).left.preservesFiniteLimits_pullbackModules
    (flat_stalkMap_analytificationπ X)

instance : PreservesColimits (analytificationModules X) :=
  preservesColimits_analytificationModules X

instance : PreservesFiniteLimits (analytificationModules X) :=
  preservesFiniteLimits_analytificationModules X

/-- **The analytification of `𝒪_X` is `𝒪_{X^an}`.** -/
def analytificationModulesUnitIso :
    (analytificationModules X).obj
        (SheafOfModules.unit X.obj.left.toLocallyRingedSpace.ringSheaf) ≅
      SheafOfModules.unit (analytification.obj X).toLocallyRingedSpace.ringSheaf :=
  (analytificationπ X).left.pullbackModulesUnitIso

/-- **The analytification of a free sheaf is free**, on the same index type. -/
def analytificationModulesFreeIso (I : Type u) :
    (analytificationModules X).obj (SheafOfModules.free I) ≅ SheafOfModules.free I :=
  (analytificationπ X).left.pullbackModulesFreeIso I

/-- **The analytification commutes with the free-sheaf functor**, naturally in the index
type. -/
def freeFunctorCompAnalytificationModulesIso :
    SheafOfModules.freeFunctor ⋙ analytificationModules X ≅ SheafOfModules.freeFunctor :=
  (analytificationπ X).left.freeFunctorCompPullbackModulesIso

/-! ### Restriction to an open subscheme -/

variable (U : Opens (schemeToOverSpec.obj X.obj).left)

/-- The preimage `π⁻¹ U` of an open `U ⊆ X` in `X^an`. -/
abbrev analytificationPreimage : (analytification.obj X).Opens :=
  preimageOpens (analytificationπ X) U

/-- **The analytification over an open `U ⊆ X`**: the pullback along the restricted comparison
morphism `π⁻¹ U ⟶ U`, which is an analytification of `U`
(`ComplexAnalytic.isAnalytification_restrictπ_analytificationπ`). -/
def analytificationModulesRestrict :
    SheafOfModules.{u} (X.obj.left.toLocallyRingedSpace.restrict U.isOpenEmbedding).ringSheaf ⥤
      SheafOfModules.{u} ((analytification.obj X).restrict
        (analytificationPreimage X U)).toLocallyRingedSpace.ringSheaf :=
  (restrictπ (analytificationπ X) U).left.pullbackModules

/-- The restricted comparison morphism `π⁻¹ U ⟶ U` is an analytification of `U`. -/
theorem isAnalytification_restrictπ_analytificationπ :
    IsAnalytification (restrictπ (analytificationπ X) U) :=
  (isAnalytification_analytificationπ X).restrict U

/-- **The analytification over an open is left exact.** -/
theorem preservesFiniteLimits_analytificationModulesRestrict :
    PreservesFiniteLimits (analytificationModulesRestrict X U) :=
  (restrictπ (analytificationπ X) U).left.preservesFiniteLimits_pullbackModules
    fun w ↦ (faithfullyFlat_stalkMap_restrictπ_analytificationπ X U w).flat

/-- **The analytification over an open is right exact.** -/
theorem preservesColimits_analytificationModulesRestrict :
    PreservesColimits (analytificationModulesRestrict X U) :=
  (restrictπ (analytificationπ X) U).left.pullbackModulesAdj.leftAdjoint_preservesColimits

/-- **Analytification commutes with restriction to an open**: for an open `U ⊆ X`,
`F^an|_{π⁻¹ U} ≅ (F|_U)^an`, naturally in `F`. Restriction is pullback along the inclusion of
the open subspace (`AlgebraicGeometry.LocallyRingedSpace.restrictModules`). -/
def analytificationModulesRestrictIso :
    analytificationModules X ⋙
        (analytification.obj X).toLocallyRingedSpace.restrictModules
          (analytificationPreimage X U) ≅
      X.obj.left.toLocallyRingedSpace.restrictModules U ⋙
        analytificationModulesRestrict X U :=
  LocallyRingedSpace.Hom.pullbackModulesCommSqIso
    (congrArg CommaMorphism.left (restrictπ_comp (analytificationπ X) U)).symm

/-! ### The analytification of an open subscheme -/

/-- **An open subscheme `U` of `X`**, as a scheme locally of finite type over `ℂ`. -/
def SchemeLFTℂ.restrict (U : X.obj.left.Opens) : SchemeLFTℂ.{u} :=
  ⟨Over.mk (U.ι ≫ X.obj.hom), by
    haveI : LocallyOfFiniteType X.obj.hom := X.property
    change LocallyOfFiniteType (U.ι ≫ X.obj.hom)
    infer_instance⟩

/-- Over `Spec ℂ`, the open subscheme `U` of `X` is the open subspace `X|_U`; the underlying
isomorphism is the identity. -/
def schemeToOverSpecRestrictIso (U : X.obj.left.Opens) :
    schemeToOverSpec.obj (X.restrict U).obj ≅ overRestrict (schemeToOverSpec.obj X.obj) U :=
  Over.isoMk (Iso.refl _) rfl

/-- **The analytification of an open subscheme is the preimage**: `(X|_U)^an ≅ π⁻¹ U`, the
unique isomorphism compatible with the comparison morphisms to `U`. -/
def analytificationRestrictIso (U : X.obj.left.Opens) :
    analytification.obj (X.restrict U) ≅
      (analytification.obj X).restrict (analytificationPreimage X U) :=
  ((isAnalytification_analytificationπ (X.restrict U)).of_iso
    (schemeToOverSpecRestrictIso X U)).isoOfIsAnalytification
      (isAnalytification_restrictπ_analytificationπ X U)

/-- The isomorphism `(X|_U)^an ≅ π⁻¹ U` is compatible with the comparison morphisms to `U`. -/
@[reassoc]
theorem analytificationRestrictIso_hom_comp (U : X.obj.left.Opens) :
    (analytificationRestrictIso X U).hom.toLRSHom ≫ (restrictπ (analytificationπ X) U).left =
      (analytificationπ (X.restrict U)).left :=
  (congrArg CommaMorphism.left (IsAnalytification.isoOfIsAnalytification_hom_comp
    ((isAnalytification_analytificationπ (X.restrict U)).of_iso
      (schemeToOverSpecRestrictIso X U))
    (isAnalytification_restrictπ_analytificationπ X U))).trans (Category.comp_id _)

/-- **Analytification commutes with restriction to an open subscheme**: for an open `U ⊆ X`,
`F^an|_{π⁻¹ U} ≅ (F|_U)^an`, naturally in `F`, where `(F|_U)^an` is the analytification of
sheaves on the scheme `X|_U` and `π⁻¹ U` is identified with `(X|_U)^an` by
`ComplexAnalytic.analytificationRestrictIso`. -/
def analytificationModulesRestrictSchemeIso (U : X.obj.left.Opens) :
    analytificationModules X ⋙
        (analytification.obj X).toLocallyRingedSpace.restrictModules
          (analytificationPreimage X U) ⋙
        (analytificationRestrictIso X U).hom.toLRSHom.pullbackModules ≅
      X.obj.left.toLocallyRingedSpace.restrictModules U ⋙
        analytificationModules (X.restrict U) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (analytificationModulesRestrictIso X U) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (LocallyRingedSpace.Hom.pullbackModulesComp _ _ ≪≫
        LocallyRingedSpace.Hom.pullbackModulesCongr (analytificationRestrictIso_hom_comp X U))

end ComplexAnalytic

end
