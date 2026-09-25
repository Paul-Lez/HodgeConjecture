/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveSpectrumNegativeTwist
public import Other.AlgebraicGeometry.InvertibleSheafRationalSection

/-!
# The standard frames of `𝒪(-n)` on `Proj 𝒜` and their transition units

`ProjectiveSpectrum.NegativeTwist.HomogeneousShift.basicOpenUnitIso` trivialises `𝒪(-n)` on the
basic open `D₊(q)` of a homogeneous element `q` of degree `n`.  This file computes the
corresponding generating section explicitly — it is the fraction `1 / q` — and deduces the
**explicit transition unit** between two such frames:

```
(q₂ / q₁) • (1 / q₂)|_W = (1 / q₁)|_W    on   W = D₊(q₁) ⊓ D₊(q₂).
```

This is the algebraic input for the chart cocycle of the analytified twists on `ℙᴺ`.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open scoped DirectSum Pointwise
open DirectSum SetLike Localization TopCat TopologicalSpace CategoryTheory Opposite

universe u v

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace ProjectiveSpectrum.NegativeTwist

local notation3 "loc[" x "]" => ProjectiveSpectrum.ambientLocalization 𝒜 x

set_option backward.isDefEq.respectTransparency.types false in
/-- The regular function `num / den` on an open set where the degree-`n` element `den` does not
vanish. -/
def homogeneousRatio {n : ℕ} (num den : 𝒜 n) (U : Opens (ProjectiveSpectrum.top 𝒜))
    (h : ∀ x : U, (den : A) ∉ x.1.asHomogeneousIdeal) :
    (ringSheaf 𝒜).obj.obj (op U) :=
  ⟨fun x => HomogeneousLocalization.mk ⟨n, num, den, h x⟩,
    fun x => ⟨U, x.2, 𝟙 _, ⟨n, num, den, h, fun _ => rfl⟩⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem homogeneousRatio_val {n : ℕ} (num den : 𝒜 n) (U : Opens (ProjectiveSpectrum.top 𝒜))
    (h : ∀ x : U, (den : A) ∉ x.1.asHomogeneousIdeal) (x : U) :
    ((homogeneousRatio 𝒜 num den U h).1 x).val =
      Localization.mk (num : A) (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 den (h x)) := by
  rw [show (homogeneousRatio 𝒜 num den U h).1 x =
    HomogeneousLocalization.mk ⟨n, num, den, h x⟩ from rfl, HomogeneousLocalization.val_mk]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The explicit generating section `1 / q` of `𝒪(-n)` on `D₊(q)`. -/
def basicOpenFrame {n : ℕ} (q : 𝒜 n) :
    (sheafInType 𝒜 n).1.obj (op (ProjectiveSpectrum.basicOpen 𝒜 (q : A))) :=
  HomogeneousShift.divide 𝒜 q (op (ProjectiveSpectrum.basicOpen 𝒜 (q : A)))
    (fun x => x.2) (DegreeZero.ofRegular 𝒜 _ 1)

set_option backward.isDefEq.respectTransparency.types false in
theorem basicOpenFrame_apply {n : ℕ} (q : 𝒜 n)
    (x : (ProjectiveSpectrum.basicOpen 𝒜 (q : A) : Opens (ProjectiveSpectrum.top 𝒜))) :
    (basicOpenFrame 𝒜 q).1 x =
      Localization.mk (1 : A) (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q x.2) := by
  refine Eq.trans (congrArg
    (fun t => Localization.mk (1 : A)
      (ProjectiveSpectrum.ambientDenominator 𝒜 x.1 q x.2) * t) ?_) (mul_one _)
  exact HomogeneousLocalization.val_one

/-- The frame `1 / q`, as a section of the scheme-level twist. -/
def projFrame {n : ℕ} (q : 𝒜 n) :
    Γ(schemeSheafOfModules 𝒜 n,
      (ProjectiveSpectrum.basicOpen 𝒜 (q : A) : («Proj» 𝒜).Opens)) :=
  basicOpenFrame 𝒜 q

/-- The regular function `num / den`, as a section of the structure sheaf of the scheme
`Proj 𝒜`. -/
def projRatio {n : ℕ} (num den : 𝒜 n) (U : («Proj» 𝒜).Opens)
    (h : ∀ x : U, (den : A) ∉ x.1.asHomogeneousIdeal) : Γ(«Proj» 𝒜, U) :=
  homogeneousRatio 𝒜 num den U h

set_option backward.isDefEq.respectTransparency false in
/-- The frame `1 / q` is the section attached to `basicOpenUnitIso`, hence it generates. -/
theorem generates_projFrame {n : ℕ} (q : 𝒜 n) :
    Scheme.Modules.Generates (projFrame 𝒜 q) := by
  have h := Scheme.Modules.generates_unitIsoSection
    (L := schemeSheafOfModules 𝒜 n)
    (U := (ProjectiveSpectrum.basicOpen 𝒜 (q : A) : («Proj» 𝒜).Opens))
    (HomogeneousShift.basicOpenUnitIso 𝒜 q)
  exact h

set_option backward.isDefEq.respectTransparency.types false in
/-- **The explicit transition unit of the standard frames.**  On any open set contained in two
basic opens of degree-`n` elements, the frame `1 / q₁` is `q₂ / q₁` times the frame `1 / q₂`. -/
theorem projRatio_smul_projFrame {n : ℕ} (q₁ q₂ : 𝒜 n) (W : («Proj» 𝒜).Opens)
    (h₁ : W ≤ (ProjectiveSpectrum.basicOpen 𝒜 (q₁ : A) : («Proj» 𝒜).Opens))
    (h₂ : W ≤ (ProjectiveSpectrum.basicOpen 𝒜 (q₂ : A) : («Proj» 𝒜).Opens))
    (hden : ∀ x : W, (q₁ : A) ∉ x.1.asHomogeneousIdeal) :
    projRatio 𝒜 q₂ q₁ W hden •
        Scheme.Modules.resSection (schemeSheafOfModules 𝒜 n) h₂ (projFrame 𝒜 q₂) =
      Scheme.Modules.resSection (schemeSheafOfModules 𝒜 n) h₁ (projFrame 𝒜 q₁) := by
  apply Subtype.ext
  funext x
  show ((homogeneousRatio 𝒜 q₂ q₁ W hden).1 x).val *
    ((basicOpenFrame 𝒜 q₂).1 ⟨x.1, h₂ x.2⟩) = (basicOpenFrame 𝒜 q₁).1 ⟨x.1, h₁ x.2⟩
  rw [homogeneousRatio_val, basicOpenFrame_apply, basicOpenFrame_apply, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  show (1 : A) * ((q₁ : A) * ((q₂ : A) * 1)) = 1 * (((q₁ : A) * (q₂ : A)) * 1)
  ring

end ProjectiveSpectrum.NegativeTwist

end AlgebraicGeometry
