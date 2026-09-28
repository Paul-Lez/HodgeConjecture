/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveSpectrumTwistMultiply

/-!
# Division by a nowhere-vanishing homogeneous element

If a homogeneous element `q` of degree `k` lies outside every relevant homogeneous prime — that
is, `D₊(q) = ⊤` — then division by `q` is a morphism of sheaves of modules
`𝒪(−b) ⟶ 𝒪(−(b+k))` on `Proj 𝒜`.  On the standard frames it sends `1/q₃` to `1/(q·q₃)`.

This is what makes all twists isomorphic on `ℙ⁰`, where `D₊(X₀) = ⊤`.
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
/-- Division by a nowhere-vanishing homogeneous element of degree `k` sends `𝒪(-b)` to
`𝒪(-(b+k))`. -/
def divideShift {k : ℕ} (q : 𝒜 k) (b : ℕ)
    (hq : ∀ x : ProjectiveSpectrum.top 𝒜, (q : A) ∉ x.asHomogeneousIdeal)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (f : (sheafInType 𝒜 b).1.obj U) :
    (sheafInType 𝒜 (b + k)).1.obj U :=
  ⟨fun x => Localization.mk (1 : A)
      (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q (hq x.1)) * f.1 x, fun x => by
    rcases f.2 x with ⟨V, hxV, i, hzero | ⟨d, r, s, hs, h⟩⟩
    · refine ⟨V, hxV, i, Or.inl ?_⟩
      funext y
      change Localization.mk (1 : A)
        (ProjectiveSpectrum.ambientDenominator 𝒜 y.1 q (hq y.1)) * f.1 (i y) = 0
      have hy := congrFun hzero y
      change f.1 (i y) = 0 at hy
      rw [hy, mul_zero]
    · let s' : 𝒜 (d + (b + k)) := ⟨q * s, by
        have hdeg : k + (d + b) = d + (b + k) := by omega
        simpa only [hdeg] using SetLike.mul_mem_graded q.2 s.2⟩
      refine ⟨V, hxV, i, Or.inr ⟨d, r, s', ?_, ?_⟩⟩
      · intro y
        exact y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hq y.1) (hs y)
      · intro y
        change Localization.mk (1 : A)
          (ProjectiveSpectrum.ambientDenominator 𝒜 y.1 q (hq y.1)) * f.1 (i y) = _
        have hy := h y
        change f.1 (i y) = _ at hy
        rw [hy, Localization.mk_mul]
        simp [s', ProjectiveSpectrum.ambientDenominator]
        congr 1⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Division by a nowhere-vanishing homogeneous element, as a linear map on sections. -/
def divideShiftLinear {k : ℕ} (q : 𝒜 k) (b : ℕ)
    (hq : ∀ x : ProjectiveSpectrum.top 𝒜, (q : A) ∉ x.asHomogeneousIdeal)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    sectionModule 𝒜 b U →ₗ[(ringSheaf 𝒜).obj.obj U] sectionModule 𝒜 (b + k) U where
  toFun := divideShift 𝒜 q b hq U
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact mul_add _ _ _
  map_smul' a f := by
    apply Subtype.ext
    funext x
    change Localization.mk (1 : A)
        (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q (hq x.1)) * ((a.1 x).val * f.1 x) =
      (a.1 x).val * (Localization.mk (1 : A)
        (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q (hq x.1)) * f.1 x)
    ring

set_option backward.isDefEq.respectTransparency.types false in
/-- Division by a nowhere-vanishing homogeneous element, as a morphism of presheaves. -/
def divideShiftPresheafHom {k : ℕ} (q : 𝒜 k) (b : ℕ)
    (hq : ∀ x : ProjectiveSpectrum.top 𝒜, (q : A) ∉ x.asHomogeneousIdeal) :
    presheafOfModules 𝒜 b ⟶ presheafOfModules 𝒜 (b + k) where
  app U := ModuleCat.ofHom (divideShiftLinear 𝒜 q b hq U)
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    rfl

/-- **Division by a nowhere-vanishing homogeneous element of degree `k`.** -/
def divideShiftHom {k : ℕ} (q : 𝒜 k) (b : ℕ)
    (hq : ∀ x : ProjectiveSpectrum.top 𝒜, (q : A) ∉ x.asHomogeneousIdeal) :
    sheafOfModules 𝒜 b ⟶ sheafOfModules 𝒜 (b + k) :=
  ⟨divideShiftPresheafHom 𝒜 q b hq⟩

/-- The scheme-level form of division. -/
def schemeDivideShiftHom {k : ℕ} (q : 𝒜 k) (b : ℕ)
    (hq : ∀ x : ProjectiveSpectrum.top 𝒜, (q : A) ∉ x.asHomogeneousIdeal) :
    schemeSheafOfModules 𝒜 b ⟶ schemeSheafOfModules 𝒜 (b + k) :=
  divideShiftHom 𝒜 q b hq

set_option backward.isDefEq.respectTransparency.types false in
/-- **Division on the standard frames.**  If `q₁ = q * q₃` then division by `q` sends the frame
`1 / q₃` of `𝒪(−b)` to the frame `1 / q₁` of `𝒪(−(b+k))`. -/
theorem divideShiftHom_projFrame {k b : ℕ} (q : 𝒜 k) (q₃ : 𝒜 b) (q₁ : 𝒜 (b + k))
    (hq : ∀ x : ProjectiveSpectrum.top 𝒜, (q : A) ∉ x.asHomogeneousIdeal)
    (hq1 : (q₁ : A) = (q : A) * (q₃ : A)) (W : («Proj» 𝒜).Opens)
    (h3 : W ≤ (ProjectiveSpectrum.basicOpen 𝒜 (q₃ : A) : («Proj» 𝒜).Opens))
    (h1 : W ≤ (ProjectiveSpectrum.basicOpen 𝒜 (q₁ : A) : («Proj» 𝒜).Opens)) :
    (schemeDivideShiftHom 𝒜 q b hq).app W
        (Scheme.Modules.resSection (schemeSheafOfModules 𝒜 b) h3 (projFrame 𝒜 q₃)) =
      Scheme.Modules.resSection (schemeSheafOfModules 𝒜 (b + k)) h1 (projFrame 𝒜 q₁) := by
  apply Subtype.ext
  funext x
  show Localization.mk (1 : A)
      (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q (hq x.1)) *
      ((basicOpenFrame 𝒜 q₃).1 ⟨x.1, h3 x.2⟩) = (basicOpenFrame 𝒜 q₁).1 ⟨x.1, h1 x.2⟩
  rw [basicOpenFrame_apply, basicOpenFrame_apply, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  show (1 : A) * ((q₁ : A) * ((1 : A) * 1)) = 1 * (((q : A) * (q₃ : A)) * (1 : A))
  rw [hq1]
  ring

end ProjectiveSpectrum.NegativeTwist

end AlgebraicGeometry
