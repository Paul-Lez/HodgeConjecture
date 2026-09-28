/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveSpectrumTwistFrames

/-!
# Multiplication by a homogeneous element as a map of negative twists

`HomogeneousShift.multiply` multiplies a local fraction of degree `−k` by a homogeneous element
of degree `k`, landing in `𝒪(0)`.  The same formula multiplies a fraction of degree `−(b + k)`
into degree `−b`, and this is a morphism of sheaves of modules `𝒪(−(b+k)) ⟶ 𝒪(−b)`.  On the
standard frames of `ProjectiveSpectrumTwistFrames.lean` it acts by

```
q · (1 / q₁) = (q / q₂) · (1 / q₃)      whenever   q₁ = q₂ * q₃,
```

which is the algebraic source of the chart multiplier of a reconstructed twist morphism.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open scoped DirectSum Pointwise
open DirectSum SetLike Localization TopCat TopologicalSpace CategoryTheory Opposite

universe u v

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace ProjectiveSpectrum.NegativeTwist

set_option backward.isDefEq.respectTransparency.types false in
/-- Multiplication by a homogeneous element of degree `k` sends `𝒪(-(b+k))` to `𝒪(-b)`. -/
def multiplyShift {k : ℕ} (q : 𝒜 k) (b : ℕ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (f : (sheafInType 𝒜 (b + k)).1.obj U) :
    (sheafInType 𝒜 b).1.obj U :=
  ⟨fun x => Localization.mk (q : A) 1 * f.1 x, fun x => by
    rcases f.2 x with ⟨V, hxV, i, hzero | ⟨d, r, s, hs, h⟩⟩
    · refine ⟨V, hxV, i, Or.inl ?_⟩
      funext y
      change Localization.mk (q : A) 1 * f.1 (i y) = 0
      have hy := congrFun hzero y
      change f.1 (i y) = 0 at hy
      rw [hy, mul_zero]
    · let e := k + d
      let r' : 𝒜 e := ⟨q * r, by
        simpa only [e] using SetLike.mul_mem_graded q.2 r.2⟩
      let s' : 𝒜 (e + b) := ⟨s, by
        have hdeg : d + (b + k) = e + b := by simp only [e]; omega
        simpa only [hdeg] using s.2⟩
      refine ⟨V, hxV, i, Or.inr ⟨e, r', s', ?_, ?_⟩⟩
      · intro y
        exact hs y
      · intro y
        change Localization.mk (q : A) 1 * f.1 (i y) = _
        have hy := h y
        change f.1 (i y) = _ at hy
        rw [hy, Localization.mk_mul]
        simp [r', s', ProjectiveSpectrum.ambientDenominator]⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem multiplyShift_apply {k : ℕ} (q : 𝒜 k) (b : ℕ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (f : (sheafInType 𝒜 (b + k)).1.obj U)
    (x : U.unop) :
    (multiplyShift 𝒜 q b U f).1 x = Localization.mk (q : A) 1 * f.1 x := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Multiplication by a homogeneous element, as a linear map on sections. -/
def multiplyShiftLinear {k : ℕ} (q : 𝒜 k) (b : ℕ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    sectionModule 𝒜 (b + k) U →ₗ[(ringSheaf 𝒜).obj.obj U] sectionModule 𝒜 b U where
  toFun := multiplyShift 𝒜 q b U
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact mul_add _ _ _
  map_smul' a f := by
    apply Subtype.ext
    funext x
    change Localization.mk (q : A) 1 * ((a.1 x).val * f.1 x) =
      (a.1 x).val * (Localization.mk (q : A) 1 * f.1 x)
    ring

set_option backward.isDefEq.respectTransparency.types false in
/-- Multiplication by a homogeneous element, as a morphism of presheaves of modules. -/
def multiplyShiftPresheafHom {k : ℕ} (q : 𝒜 k) (b : ℕ) :
    presheafOfModules 𝒜 (b + k) ⟶ presheafOfModules 𝒜 b where
  app U := ModuleCat.ofHom (multiplyShiftLinear 𝒜 q b U)
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    rfl

/-- **Multiplication by a homogeneous element of degree `k`,** as a morphism of sheaves of
modules `𝒪(-(b+k)) ⟶ 𝒪(-b)`. -/
def multiplyShiftHom {k : ℕ} (q : 𝒜 k) (b : ℕ) :
    sheafOfModules 𝒜 (b + k) ⟶ sheafOfModules 𝒜 b :=
  ⟨multiplyShiftPresheafHom 𝒜 q b⟩

/-- The scheme-level form of multiplication by a homogeneous element. -/
def schemeMultiplyShiftHom {k : ℕ} (q : 𝒜 k) (b : ℕ) :
    schemeSheafOfModules 𝒜 (b + k) ⟶ schemeSheafOfModules 𝒜 b :=
  multiplyShiftHom 𝒜 q b

set_option backward.isDefEq.respectTransparency.types false in
theorem schemeMultiplyShiftHom_app {k : ℕ} (q : 𝒜 k) (b : ℕ) (U : («Proj» 𝒜).Opens)
    (f : Γ(schemeSheafOfModules 𝒜 (b + k), U)) (x : U) :
    ((schemeMultiplyShiftHom 𝒜 q b).app U f).1 x = Localization.mk (q : A) 1 * f.1 x := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **Multiplication on the standard frames.**  If `q₁ = q₂ * q₃` then multiplication by `q`
sends the frame `1 / q₁` of `𝒪(−(b+k))` to `(q / q₂) • (1 / q₃)`. -/
theorem multiplyShiftHom_projFrame {k b : ℕ} (q q₂ : 𝒜 k) (q₃ : 𝒜 b) (q₁ : 𝒜 (b + k))
    (hq : (q₁ : A) = (q₂ : A) * (q₃ : A)) (W : («Proj» 𝒜).Opens)
    (h1 : W ≤ (ProjectiveSpectrum.basicOpen 𝒜 (q₁ : A) : («Proj» 𝒜).Opens))
    (h3 : W ≤ (ProjectiveSpectrum.basicOpen 𝒜 (q₃ : A) : («Proj» 𝒜).Opens))
    (h2 : ∀ x : W, (q₂ : A) ∉ x.1.asHomogeneousIdeal) :
    (schemeMultiplyShiftHom 𝒜 q b).app W
        (Scheme.Modules.resSection (schemeSheafOfModules 𝒜 (b + k)) h1 (projFrame 𝒜 q₁)) =
      projRatio 𝒜 q q₂ W h2 •
        Scheme.Modules.resSection (schemeSheafOfModules 𝒜 b) h3 (projFrame 𝒜 q₃) := by
  apply Subtype.ext
  funext x
  show Localization.mk (q : A) 1 * ((basicOpenFrame 𝒜 q₁).1 ⟨x.1, h1 x.2⟩) =
    ((homogeneousRatio 𝒜 q q₂ W h2).1 x).val * ((basicOpenFrame 𝒜 q₃).1 ⟨x.1, h3 x.2⟩)
  rw [basicOpenFrame_apply, basicOpenFrame_apply, homogeneousRatio_val,
    Localization.mk_mul, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  show (1 : A) * (((q₂ : A) * (q₃ : A)) * ((q : A) * 1)) =
    1 * (((1 : A) * (q₁ : A)) * ((q : A) * 1))
  rw [hq]
  ring

end ProjectiveSpectrum.NegativeTwist

end AlgebraicGeometry
