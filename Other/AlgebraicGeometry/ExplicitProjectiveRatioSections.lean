/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitProjectiveCoordinates

/-!
# Regular coordinate ratios on projective charts

Coordinate ratios are actual sections of the structure sheaf. Their transition identities are
proved in homogeneous localization, and they remain valid after pullback to any scheme.
-/

@[expose] public noncomputable section

open MvPolynomial HomogeneousLocalization CategoryTheory

namespace AlgebraicGeometry.ProjectiveRatioSections

universe u
variable (R : Type u) [CommRing R] {σ : Type u}

attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The fraction identity expressing change of a projective coordinate pivot. -/
theorem awayMap_ratio_transition (i k a : σ) :
    awayMap (homogeneousSubmodule σ R) (isHomogeneous_X R k) rfl
      (ProjectiveSpaceChart.ratio R i a) =
    awayMap (homogeneousSubmodule σ R) (isHomogeneous_X R i)
        (mul_comm (X i) (X k)) (ProjectiveSpaceChart.ratio R k a) *
      awayMap (homogeneousSubmodule σ R) (isHomogeneous_X R k) rfl
        (ProjectiveSpaceChart.ratio R i k) := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul]
  simp only [ProjectiveSpaceChart.ratio, awayMap_mk, Away.val_mk, pow_one,
    Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  rw [Localization.r_iff_exists]
  use 1
  simp only [Submonoid.coe_one, Submonoid.mk_mul_mk, one_mul]
  ring

/-- The regular function represented by `Xₐ / Xᵢ`. -/
def ratio (i a : σ) :
    Γ(Proj (homogeneousSubmodule σ R), Proj.basicOpen (homogeneousSubmodule σ R) (X i)) :=
  Proj.awayToSection (homogeneousSubmodule σ R) (X i) (ProjectiveSpaceChart.ratio R i a)

@[simp] theorem ratio_self (i : σ) : ratio R i i = 1 := by
  simp [ratio]

/-- The nonvanishing locus of a regular coordinate ratio is the intersection of the two
corresponding projective coordinate charts. -/
theorem basicOpen_ratio (i a : σ) :
    (Proj (homogeneousSubmodule σ R)).basicOpen (ratio R i a) =
      Proj.basicOpen (homogeneousSubmodule σ R) (X i) ⊓
        Proj.basicOpen (homogeneousSubmodule σ R) (X a) := by
  let A := homogeneousSubmodule σ R
  let U := Proj.basicOpen A (X i)
  let E := Proj.basicOpenIsoSpec A (X i) (isHomogeneous_X R i) zero_lt_one
  have hleft : Proj.awayι A (X i) (isHomogeneous_X R i) zero_lt_one ⁻¹ᵁ
      (Proj A).basicOpen (ratio R i a) =
        PrimeSpectrum.basicOpen (ProjectiveSpaceChart.ratio R i a) := by
    change E.inv ⁻¹ᵁ (U.ι ⁻¹ᵁ (Proj A).basicOpen (ratio R i a)) = _
    rw [← Scheme.Opens.toSpecΓ_preimage_basicOpen]
    change E.inv ⁻¹ᵁ (U.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen
      ((Proj.awayToSection A (X i)) (ProjectiveSpaceChart.ratio R i a))) = _
    rw [← SpecMap_preimage_basicOpen, ← Scheme.Hom.comp_preimage]
    change E.inv ⁻¹ᵁ (E.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (ProjectiveSpaceChart.ratio R i a)) = _
    rw [← Scheme.Hom.comp_preimage, Iso.inv_hom_id, Scheme.Hom.id_preimage]
  have hright : Proj.awayι A (X i) (isHomogeneous_X R i) zero_lt_one ⁻¹ᵁ
      Proj.basicOpen A (X a) = PrimeSpectrum.basicOpen (ProjectiveSpaceChart.ratio R i a) := by
    simpa only [HomogeneousLocalization.Away.isLocalizationElem, pow_one,
      ProjectiveSpaceChart.ratio] using
      Proj.awayι_preimage_basicOpen A (isHomogeneous_X R i) zero_lt_one
        (isHomogeneous_X R a) zero_lt_one
  have h := congrArg (fun V ↦ (Proj.awayι A (X i) (isHomogeneous_X R i) zero_lt_one) ''ᵁ V)
    (hleft.trans hright.symm)
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Proj.opensRange_awayι] at h
  rwa [inf_eq_right.mpr ((Proj A).basicOpen_le (ratio R i a))] at h

variable {Y : Scheme.{u}} (f : Y ⟶ Proj (homogeneousSubmodule σ R))

/-- A coordinate ratio pulled back as an actual regular section on an open subscheme. -/
def pullRatio (U : Y.Opens) (i : σ)
    (hi : U ≤ f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) (X i)) (a : σ) : Γ(Y, U) :=
  f.appLE _ U hi (ratio R i a)

@[simp] theorem pullRatio_self (U : Y.Opens) (i : σ)
    (hi : U ≤ f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) (X i)) :
    pullRatio R f U i hi i = 1 := by
  simp [pullRatio]

/-- Pullback coordinate ratios commute with restriction to a smaller open subscheme. -/
theorem restrict_pullRatio {U V : Y.Opens} (h : U ≤ V) (i : σ)
    (hi : V ≤ f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) (X i)) (a : σ) :
    (Y.presheaf.map (homOfLE h).op) (pullRatio R f V i hi a) =
      pullRatio R f U i (h.trans hi) a := by
  change (f.appLE _ V hi ≫ Y.presheaf.map (homOfLE h).op) (ratio R i a) = _
  rw [Scheme.Hom.appLE_map]
  rfl

/-- Restriction of the chart's homogeneous localization map to an overlap. -/
theorem awayToSection_appLE (U : Y.Opens) (i k : σ)
    (hi : U ≤ f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) (X i))
    (hk : U ≤ f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) (X k)) :
    CommRingCat.ofHom (awayMap (homogeneousSubmodule σ R) (isHomogeneous_X R k) rfl) ≫
        Proj.awayToSection (homogeneousSubmodule σ R) (X i * X k) ≫
        f.appLE (Proj.basicOpen (homogeneousSubmodule σ R) (X i * X k)) U
          (by simpa only [Proj.basicOpen_mul, Scheme.Hom.preimage_inf] using le_inf hi hk) =
      Proj.awayToSection (homogeneousSubmodule σ R) (X i) ≫
        f.appLE (Proj.basicOpen (homogeneousSubmodule σ R) (X i)) U hi := by
  rw [Proj.awayMap_awayToSection_assoc, Scheme.Hom.map_appLE]

/-- Coordinate transition identities hold as equalities of actual pulled-back regular sections. -/
theorem pullRatio_transition (U : Y.Opens) (i k a : σ)
    (hi : U ≤ f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) (X i))
    (hk : U ≤ f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) (X k)) :
    pullRatio R f U i hi a = pullRatio R f U k hk a * pullRatio R f U i hi k := by
  let hU : U ≤ f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) (X i * X k) :=
    by simpa only [Proj.basicOpen_mul, Scheme.Hom.preimage_inf] using le_inf hi hk
  let θ := Proj.awayToSection (homogeneousSubmodule σ R) (X i * X k) ≫
    f.appLE _ U hU
  have hi' := awayToSection_appLE R f U i k hi hk
  have hk' : CommRingCat.ofHom (awayMap (homogeneousSubmodule σ R) (isHomogeneous_X R i)
        (mul_comm (X i) (X k))) ≫ θ =
      Proj.awayToSection (homogeneousSubmodule σ R) (X k) ≫
        f.appLE (Proj.basicOpen (homogeneousSubmodule σ R) (X k)) U hk := by
    dsimp only [θ]
    rw [Proj.awayMap_awayToSection_assoc, Scheme.Hom.map_appLE]
  have ha := congrArg θ (awayMap_ratio_transition R i k a)
  rw [map_mul] at ha
  change (CommRingCat.ofHom (awayMap (homogeneousSubmodule σ R) (isHomogeneous_X R k) rfl) ≫ θ)
      (ProjectiveSpaceChart.ratio R i a) =
    (CommRingCat.ofHom (awayMap (homogeneousSubmodule σ R) (isHomogeneous_X R i)
      (mul_comm (X i) (X k))) ≫ θ) (ProjectiveSpaceChart.ratio R k a) *
    (CommRingCat.ofHom (awayMap (homogeneousSubmodule σ R) (isHomogeneous_X R k) rfl) ≫ θ)
      (ProjectiveSpaceChart.ratio R i k) at ha
  rw [show CommRingCat.ofHom (awayMap (homogeneousSubmodule σ R) (isHomogeneous_X R k) rfl) ≫ θ =
    Proj.awayToSection (homogeneousSubmodule σ R) (X i) ≫
      f.appLE (Proj.basicOpen (homogeneousSubmodule σ R) (X i)) U hi from hi', hk'] at ha
  exact ha

/-- The nonvanishing locus of a pulled-back coordinate ratio is the expected coordinate locus. -/
theorem basicOpen_pullRatio (U : Y.Opens) (i a : σ)
    (hi : U ≤ f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) (X i)) :
    Y.basicOpen (pullRatio R f U i hi a) =
      U ⊓ f ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) (X a) := by
  rw [pullRatio, Scheme.basicOpen_appLE, basicOpen_ratio, Scheme.Hom.preimage_inf,
    ← inf_assoc, inf_eq_left.mpr hi]

end AlgebraicGeometry.ProjectiveRatioSections
