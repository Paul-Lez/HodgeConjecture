/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.GeneratingSectionCoefficient
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Pullback of sections of a sheaf of modules along a morphism of schemes

The unit of the adjunction `Scheme.Modules.pullback f ⊣ Scheme.Modules.pushforward f` turns a
section of `M : Y.Modules` over an open `U` into a section of `f^* M` over `f ⁻¹ᵁ U`.  This file
records that operation and its two structural properties — compatibility with restriction and
semilinearity over the pullback of regular functions — and deduces that **algebraic transition
identities transport verbatim through inverse image**:

```
u • a|_W = b|_W   ⟹   f^*u • (f^*a)|_{f⁻¹W} = (f^*b)|_{f⁻¹W}
```

This is the scheme analogue of `Other/AlgebraicGeometry/AnalyticSectionOfAlgebraic.lean`, where
the same statements are proved for the analytification morphism of ringed sites.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Restriction of a regular function to a smaller open. -/
abbrev resRing {S : Scheme.{u}} {U V : S.Opens} (h : V ≤ U) (r : Γ(S, U)) : Γ(S, V) :=
  S.presheaf.map (homOfLE h).op r

@[simp]
lemma resRing_rfl {S : Scheme.{u}} {U : S.Opens} (r : Γ(S, U)) : resRing le_rfl r = r := by
  change S.presheaf.map (𝟙 (op U)) r = r
  rw [S.presheaf.map_id]
  rfl

lemma resRing_resRing {S : Scheme.{u}} {U V W : S.Opens} (hVU : V ≤ U) (hWV : W ≤ V)
    (r : Γ(S, U)) : resRing hWV (resRing hVU r) = resRing (hWV.trans hVU) r := by
  change (S.presheaf.map (homOfLE hVU).op ≫ S.presheaf.map (homOfLE hWV).op) r = _
  rw [← S.presheaf.map_comp]
  rfl

lemma resRing_one {S : Scheme.{u}} {U V : S.Opens} (h : V ≤ U) :
    resRing h (1 : Γ(S, U)) = 1 :=
  map_one (S.presheaf.map (homOfLE h).op).hom

lemma resRing_mul {S : Scheme.{u}} {U V : S.Opens} (h : V ≤ U) (r r' : Γ(S, U)) :
    resRing h (r * r') = resRing h r * resRing h r' :=
  map_mul (S.presheaf.map (homOfLE h).op).hom r r'

lemma resRing_add {S : Scheme.{u}} {U V : S.Opens} (h : V ≤ U) (r r' : Γ(S, U)) :
    resRing h (r + r') = resRing h r + resRing h r' :=
  map_add (S.presheaf.map (homOfLE h).op).hom r r'

/-- Preimages of opens are monotone. -/
lemma preimage_mono (f : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U :=
  fun _ hz ↦ h hz

/-- The pullback of a regular function along a morphism of schemes. -/
def pullbackFunction (f : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U)) : Γ(X, f ⁻¹ᵁ U) := f.app U r

/-- The pullback of a section of a sheaf of modules, through the unit of the
inverse-image adjunction. -/
def pullbackSection (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) (g : Γ(M, U)) :
    Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U g

@[simp]
lemma pullbackFunction_one (f : X ⟶ Y) (U : Y.Opens) :
    pullbackFunction f U (1 : Γ(Y, U)) = 1 := map_one (f.app U).hom

lemma pullbackFunction_mul (f : X ⟶ Y) (U : Y.Opens) (r r' : Γ(Y, U)) :
    pullbackFunction f U (r * r') = pullbackFunction f U r * pullbackFunction f U r' :=
  map_mul (f.app U).hom r r'

lemma pullbackFunction_add (f : X ⟶ Y) (U : Y.Opens) (r r' : Γ(Y, U)) :
    pullbackFunction f U (r + r') = pullbackFunction f U r + pullbackFunction f U r' :=
  map_add (f.app U).hom r r'

lemma pullbackFunction_pow (f : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U)) (m : ℕ) :
    pullbackFunction f U (r ^ m) = pullbackFunction f U r ^ m :=
  map_pow (f.app U).hom r m

/-- The pullback of a unit is a unit. -/
lemma isUnit_pullbackFunction (f : X ⟶ Y) {U : Y.Opens} {r : Γ(Y, U)} (hr : IsUnit r) :
    IsUnit (pullbackFunction f U r) := hr.map (f.app U).hom

/-- Pullback of regular functions commutes with restriction. -/
lemma pullbackFunction_res (f : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) (r : Γ(Y, U)) :
    pullbackFunction f V (resRing h r) = resRing (preimage_mono f h) (pullbackFunction f U r) := by
  exact congrArg (fun φ : Γ(Y, U) ⟶ Γ(X, f ⁻¹ᵁ V) ↦ (ConcreteCategory.hom φ) r)
    (f.naturality (homOfLE h).op)

/-- Pullback of sections is semilinear over pullback of regular functions. -/
lemma pullbackSection_smul (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) (r : Γ(Y, U))
    (g : Γ(M, U)) :
    pullbackSection f M U (r • g) = pullbackFunction f U r • pullbackSection f M U g :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app_smul r g

/-- Pullback of sections commutes with restriction. -/
lemma pullbackSection_res (f : X ⟶ Y) (M : Y.Modules) {U V : Y.Opens} (h : V ≤ U) (g : Γ(M, U)) :
    pullbackSection f M V (resSection M h g) =
      resSection ((Scheme.Modules.pullback f).obj M) (preimage_mono f h)
        (pullbackSection f M U g) :=
  PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val (homOfLE h).op g

/-- **Transport of transition identities through inverse image.** -/
theorem pullbackSection_smul_res (f : X ⟶ Y) (M : Y.Modules) {U V W : Y.Opens}
    (hWU : W ≤ U) (hWV : W ≤ V) (u : Γ(Y, W)) (a : Γ(M, U)) (b : Γ(M, V))
    (h : u • resSection M hWU a = resSection M hWV b) :
    pullbackFunction f W u •
        resSection ((Scheme.Modules.pullback f).obj M) (preimage_mono f hWU)
          (pullbackSection f M U a) =
      resSection ((Scheme.Modules.pullback f).obj M) (preimage_mono f hWV)
        (pullbackSection f M V b) := by
  have hcong := congrArg (pullbackSection f M W) h
  rwa [pullbackSection_smul, pullbackSection_res, pullbackSection_res] at hcong

end AlgebraicGeometry.Scheme.Modules
