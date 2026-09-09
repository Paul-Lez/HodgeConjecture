/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitProjectiveSpaceChart

/-!
# Projective maps from coordinate functions

Coordinate functions with one invertible coordinate determine an actual morphism to projective
space. These maps are independent of the chosen invertible coordinate. This is the chart
compatibility needed to glue the Segre morphism.
-/

@[expose] public noncomputable section

open MvPolynomial HomogeneousLocalization CategoryTheory

namespace AlgebraicGeometry.ProjectiveCoordinates

universe u
variable {R S σ : Type u} [CommRing R] [CommRing S]
  (φ : R →+* S) (x : σ → S)

attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Evaluation of a degree-zero homogeneous fraction whenever its denominator is a unit. -/
def evaluate (f : MvPolynomial σ R) (hf : IsUnit (eval₂Hom φ x f)) :
    HomogeneousLocalization.Away (homogeneousSubmodule σ R) f →+* S :=
  (Localization.awayLift (eval₂Hom φ x) f hf).comp
    (algebraMap _ (Localization.Away f))

/-- Evaluation commutes with restriction from one projective basic open to a smaller one. -/
theorem evaluate_comp_awayMap (f g : MvPolynomial σ R) {d : ℕ}
    (hg : g.IsHomogeneous d) (hf : IsUnit (eval₂Hom φ x f))
    (hg' : IsUnit (eval₂Hom φ x g)) :
    (evaluate φ x (f * g) (by simpa using hf.mul hg')).comp
        (HomogeneousLocalization.awayMap (homogeneousSubmodule σ R) hg rfl) =
      evaluate φ x f hf := by
  have h : (Localization.awayLift (eval₂Hom φ x) (f * g)
        (by simpa using hf.mul hg')).comp
      (Localization.awayLift (algebraMap (MvPolynomial σ R) (Localization.Away (f * g))) f
        (isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right f g))
          (IsLocalization.Away.algebraMap_isUnit (f * g)))) =
      Localization.awayLift (eval₂Hom φ x) f hf := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers f)
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, Localization.awayLift, IsLocalization.Away.lift_eq]
  apply RingHom.ext
  intro a
  change Localization.awayLift (eval₂Hom φ x) (f * g) (by simpa using hf.mul hg')
      (HomogeneousLocalization.awayMap (homogeneousSubmodule σ R) hg rfl a).val = _
  rw [HomogeneousLocalization.val_awayMap]
  exact DFunLike.congr_fun h a.val

/-- Evaluation also commutes with restriction when the product denominator is given by an
explicit equality. -/
theorem evaluate_comp_awayMap_of_eq (f g q : MvPolynomial σ R) {d : ℕ}
    (hg : g.IsHomogeneous d) (hq : q = f * g) (hf : IsUnit (eval₂Hom φ x f))
    (hg' : IsUnit (eval₂Hom φ x g)) :
    (evaluate φ x q (by simpa [hq] using hf.mul hg')).comp
        (HomogeneousLocalization.awayMap (homogeneousSubmodule σ R) hg hq) =
      evaluate φ x f hf := by
  subst q
  exact evaluate_comp_awayMap φ x f g hg hf hg'

/-- A coordinate family determines a morphism on any chart whose coordinate is a unit. -/
def toProjective (i : σ) (hi : IsUnit (x i)) :
    Spec (CommRingCat.of S) ⟶ Proj (homogeneousSubmodule σ R) :=
  Spec.map (CommRingCat.ofHom (evaluate φ x (X i) (by simpa using hi))) ≫
    Proj.awayι (homogeneousSubmodule σ R) (X i) (isHomogeneous_X R i) zero_lt_one

/-- Changing the invertible pivot leaves the actual projective morphism unchanged. -/
theorem toProjective_eq (i k : σ) (hi : IsUnit (x i)) (hk : IsUnit (x k)) :
    toProjective φ x i hi = toProjective φ x k hk := by
  let E := evaluate φ x (X i * X k) (by simpa using hi.mul hk)
  have hi' : toProjective φ x i hi = Spec.map (CommRingCat.ofHom E) ≫
      Proj.awayι (homogeneousSubmodule σ R) (X i * X k)
        ((isHomogeneous_X R i).mul (isHomogeneous_X R k)) (by decide) := by
    rw [toProjective, ← evaluate_comp_awayMap φ x (X i) (X k)
      (isHomogeneous_X R k) (by simpa using hi) (by simpa using hk)]
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      Proj.SpecMap_awayMap_awayι]
  have hk' : toProjective φ x k hk = Spec.map (CommRingCat.ofHom E) ≫
      Proj.awayι (homogeneousSubmodule σ R) (X i * X k)
        ((isHomogeneous_X R i).mul (isHomogeneous_X R k)) (by decide) := by
    rw [toProjective, ← evaluate_comp_awayMap_of_eq φ x (X k) (X i) (X i * X k)
      (isHomogeneous_X R i) (mul_comm _ _) (by simpa using hk) (by simpa using hi)]
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      Proj.SpecMap_awayMap_awayι]

  exact hi'.trans hk'.symm

/-- Evaluation on the affine chart sends a coordinate ratio to the corresponding quotient. -/
theorem evaluate_ratio (i a : σ) (hi : IsUnit (x i)) (v : S)
    (hv : x i * v = 1) :
    evaluate φ x (X i) (by simpa using hi) (ProjectiveSpaceChart.ratio R i a) = x a * v := by
  change Localization.awayLift (eval₂Hom φ x) (X i) (by simpa using hi)
    (Localization.mk (X a) ⟨X i ^ 1, ⟨1, rfl⟩⟩) = _
  rw [Localization.awayLift_mk (v := v) (hv := by simpa using hv)]
  simp

/-- Evaluation on a projective chart preserves constants. -/
theorem evaluate_coefficient (i : σ) (hi : IsUnit (x i)) (r : R) :
    evaluate φ x (X i) (by simpa using hi) (ProjectiveSpaceChart.coefficient R i r) = φ r := by
  change Localization.awayLift (eval₂Hom φ x) (X i) (by simpa using hi)
    (Localization.mk (C r) ⟨X i ^ 0, ⟨0, rfl⟩⟩) = _
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hi
  rw [Localization.awayLift_mk (v := v) (hv := by simpa using hv)]
  simp

variable [DecidableEq σ] [Fintype σ]

/-- Multiplying every projective coordinate by the same unit does not change the map. -/
theorem toProjective_eq_of_proportional (y : σ → S) (i k : σ)
    (hi : x i = 1) (hk : y k = 1) (h : ∀ a, x a = x k * y a) :
    toProjective φ x i (by simp [hi]) = toProjective φ y k (by simp [hk]) := by
  have hxk : x k * y i = 1 := (h i).symm.trans hi
  have hu : IsUnit (x k) := isUnit_iff_exists_inv.mpr ⟨y i, hxk⟩
  rw [toProjective_eq φ x i k (by simp [hi]) hu]
  unfold toProjective
  congr 2
  apply CommRingCat.hom_ext
  change evaluate φ x (X k) (by simpa using hu) =
    evaluate φ y (X k) (by simp [hk])
  apply ProjectiveSpaceChart.ringHom_ext
  · intro r
    exact (evaluate_coefficient φ x k hu r).trans
      (evaluate_coefficient φ y k (by simp [hk]) r).symm
  · intro a
    rw [evaluate_ratio φ x k a hu (y i) hxk,
      evaluate_ratio φ y k a (by simp [hk]) 1 (by simp [hk])]
    rw [h a]
    calc x k * y a * y i = x k * y i * y a := by ring
         _ = y a * 1 := by rw [hxk]; simp

/-- Evaluation of projective coordinates commutes with a homomorphism on their values. -/
theorem map_comp_evaluate {T : Type u} [CommRing T] (ψ : S →+* T)
    (i : σ) (hi : IsUnit (x i)) :
    ψ.comp (evaluate φ x (X i) (by simpa using hi)) =
      evaluate (ψ.comp φ) (ψ ∘ x) (X i) (by simpa using hi.map ψ) := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hi
  apply ProjectiveSpaceChart.ringHom_ext
  · intro r
    change ψ (evaluate φ x (X i) _ (ProjectiveSpaceChart.coefficient R i r)) = _
    rw [evaluate_coefficient φ x i hi r,
      evaluate_coefficient (ψ.comp φ) (ψ ∘ x) i (hi.map ψ) r]
    rfl
  · intro a
    change ψ (evaluate φ x (X i) _ (ProjectiveSpaceChart.ratio R i a)) = _
    rw [evaluate_ratio φ x i a hi v hv,
      evaluate_ratio (ψ.comp φ) (ψ ∘ x) i a (hi.map ψ) (ψ v)
        (by simpa only [Function.comp_apply, ← map_mul, map_one] using congrArg ψ hv)]
    exact ψ.map_mul _ _

/-- The projective coordinate map is natural in the source affine scheme. -/
@[reassoc] theorem SpecMap_toProjective {T : Type u} [CommRing T] (ψ : S →+* T)
    (i : σ) (hi : IsUnit (x i)) :
    Spec.map (CommRingCat.ofHom ψ) ≫ toProjective φ x i hi =
      toProjective (ψ.comp φ) (ψ ∘ x) i (hi.map ψ) := by
  simp only [toProjective, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [map_comp_evaluate φ x ψ i hi]

/-- Coordinate sections on an arbitrary open subscheme determine a projective map. -/
def fromSections {X : Scheme.{u}} (U : X.Opens) (φ : R →+* Γ(X, U))
    (x : σ → Γ(X, U)) (i : σ) (hi : IsUnit (x i)) :
    U.toScheme ⟶ Proj (homogeneousSubmodule σ R) :=
  U.toSpecΓ ≫ toProjective φ x i hi

/-- Projective maps from coordinate sections are compatible with restriction of sections. -/
theorem homOfLE_fromSections {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V)
    (φ : R →+* Γ(X, V)) (x : σ → Γ(X, V)) (i : σ) (hi : IsUnit (x i)) :
    X.homOfLE h ≫ fromSections V φ x i hi =
      fromSections U ((X.presheaf.map (homOfLE h).op).hom.comp φ)
        ((X.presheaf.map (homOfLE h).op).hom ∘ x) i
        (hi.map (X.presheaf.map (homOfLE h).op).hom) := by
  rw [fromSections, ← Category.assoc,
    ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map, Category.assoc]
  exact congrArg (fun f ↦ U.toSpecΓ ≫ f)
    (SpecMap_toProjective φ x (X.presheaf.map (homOfLE h).op).hom i hi)

omit [DecidableEq σ] [Fintype σ] in
/-- With the pivot normalized to one, a projective coordinate basic open pulls back to the
basic open of that coordinate function. -/
theorem toProjective_preimage_coordinate (i a : σ) (hi : x i = 1) :
    toProjective φ x i (by simp [hi]) ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule σ R) (MvPolynomial.X a) =
        PrimeSpectrum.basicOpen (x a) := by
  rw [toProjective, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen (homogeneousSubmodule σ R)
      (isHomogeneous_X R i) zero_lt_one (isHomogeneous_X R a) zero_lt_one,
    SpecMap_preimage_basicOpen]
  simp only [HomogeneousLocalization.Away.isLocalizationElem, pow_one, CommRingCat.hom_ofHom]
  change PrimeSpectrum.basicOpen
    (evaluate φ x (MvPolynomial.X i) (by simp [hi]) (ProjectiveSpaceChart.ratio R i a)) = _
  rw [evaluate_ratio φ x i a (by simp [hi]) 1 (by simp [hi]), mul_one]

omit [DecidableEq σ] [Fintype σ] in
/-- The same nonvanishing formula holds for coordinate sections on any open subscheme. -/
theorem fromSections_preimage_coordinate {Y : Scheme.{u}} (U : Y.Opens)
    (φ : R →+* Γ(Y, U)) (x : σ → Γ(Y, U)) (i a : σ) (hi : x i = 1) :
    fromSections U φ x i (by simp [hi]) ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule σ R) (MvPolynomial.X a) =
        U.ι ⁻¹ᵁ Y.basicOpen (x a) := by
  rw [fromSections, Scheme.Hom.comp_preimage, toProjective_preimage_coordinate φ x i a hi,
    Scheme.Opens.toSpecΓ_preimage_basicOpen]

end AlgebraicGeometry.ProjectiveCoordinates
