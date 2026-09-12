/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ProjectiveAnalytification

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Points of the integral `Proj` model from homogeneous coordinates

Nonzero homogeneous coordinates define a morphism `Spec ℂ ⟶ Proj` of the universal graded ring,
and rescaling them does not move the resulting point, so the construction descends to linear
projectivization. The basic opens met by such a point are computed by evaluating homogeneous
polynomials at the coordinates; in particular the coordinate chart it meets is the one where that
coordinate is nonzero.

The comparison of projectivization with the complex points of scheme-theoretic projective space
in `ProjectiveAnalytification.lean` is built from the standard affine charts instead, through
`chartIntegralProj`, so nothing here is needed to state the conjecture.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped LinearAlgebra.Projectivization

namespace AlgebraicGeometry

namespace ComplexProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Nonzero homogeneous coordinates define a morphism from `Spec ℂ` to the integral `Proj`
model. -/
noncomputable def toIntegralProj {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0) :
    Spec ↧ℂ ⟶ Proj (UniversalGrading n) :=
  Proj.fromOfGlobalSections (UniversalGrading n) (coordinateGlobalSectionsHom v)
    (coordinate_irrelevant_map_eq_top v hv)

/-- The inverse image of a positive-degree basic open under the point constructed from
coordinates is determined by whether the homogeneous polynomial vanishes at those coordinates. -/
lemma toIntegralProj_preimage_basicOpen {n d : ℕ}
    (v : CoordinateSpace n) (hv : v ≠ 0)
    (r : UniversalRing n) (hd : 0 < d) (hr : r ∈ UniversalGrading n d) :
    toIntegralProj v hv ⁻¹ᵁ Proj.basicOpen (UniversalGrading n) r =
      if (Scheme.ΓSpecIso ↧ℂ).hom (coordinateGlobalSectionsHom v r) = 0
        then ⊥ else ⊤ := by
  rw [toIntegralProj,
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hd hr]
  rw [basicOpen_eq_of_affine']
  let a : ℂ := (Scheme.ΓSpecIso ↧ℂ).hom (coordinateGlobalSectionsHom v r)
  change PrimeSpectrum.basicOpen a = if a = 0 then ⊥ else ⊤
  split_ifs with h
  · rw [h]
    exact PrimeSpectrum.basicOpen_zero
  · apply top_unique
    intro x hx
    rw [PrimeSpectrum.mem_basicOpen, Subsingleton.elim x (⊥ : PrimeSpectrum ℂ)]
    simpa using h

/-- The coordinate chart met by the point constructed from a vector is exactly the chart on
which that coordinate is nonzero. -/
lemma toIntegralProj_preimage_coordinateBasicOpen {n : ℕ}
    (v : CoordinateSpace n) (hv : v ≠ 0) (i : Fin (n + 1)) :
    toIntegralProj v hv ⁻¹ᵁ
      Proj.basicOpen (UniversalGrading n) (MvPolynomial.X i) =
        if v i = 0 then ⊥ else ⊤ := by
  rw [toIntegralProj,
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ zero_lt_one
      (MvPolynomial.isHomogeneous_X _ i)]
  rw [coordinateGlobalSectionsHom_X, basicOpen_eq_of_affine']
  let a : ℂ := (Scheme.ΓSpecIso ↧ℂ).hom
    ((Scheme.ΓSpecIso ↧ℂ).inv (v i))
  have ha : a = v i := Iso.hom_inv_id_apply _ _
  change PrimeSpectrum.basicOpen a = _
  rw [ha]
  split_ifs with h
  · rw [h]
    exact PrimeSpectrum.basicOpen_zero
  · apply top_unique
    intro x hx
    rw [PrimeSpectrum.mem_basicOpen, Subsingleton.elim x (⊥ : PrimeSpectrum ℂ)]
    simpa using h

/-- Rescaling nonzero homogeneous coordinates does not change the underlying point of the
integral `Proj` model. -/
lemma toIntegralProj_apply_smul {n : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (x : Spec ↧ℂ) :
    toIntegralProj (c • v) (smul_ne_zero hc hv) x = toIntegralProj v hv x := by
  classical
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero v hv
  apply ProjectiveSpectrum.ext
  ext r
  rw [(toIntegralProj (c • v) (smul_ne_zero hc hv) x).asHomogeneousIdeal.isHomogeneous.mem_iff,
    (toIntegralProj v hv x).asHomogeneousIdeal.isHomogeneous.mem_iff]
  apply forall_congr'
  intro d
  let s : UniversalRing n :=
    GradedRing.proj (UniversalGrading n) d r
  have hs : s ∈ UniversalGrading n d := SetLike.coe_mem _
  let t : UniversalRing n := s * MvPolynomial.X i
  have ht : t ∈ UniversalGrading n (d + 1) :=
    SetLike.mul_mem_graded hs (MvPolynomial.isHomogeneous_X _ i)
  have hXi_v : MvPolynomial.X i ∉
      (toIntegralProj v hv x).asHomogeneousIdeal := by
    rw [← Proj.mem_basicOpen]
    change x ∈ toIntegralProj v hv ⁻¹ᵁ
      Proj.basicOpen (UniversalGrading n) (MvPolynomial.X i)
    rw [toIntegralProj_preimage_basicOpen v hv (MvPolynomial.X i) zero_lt_one
      (MvPolynomial.isHomogeneous_X _ i), coordinateGlobalSectionsHom_X]
    simp [hi]
  have hXi_cv : MvPolynomial.X i ∉
      (toIntegralProj (c • v) (smul_ne_zero hc hv) x).asHomogeneousIdeal := by
    rw [← Proj.mem_basicOpen]
    change x ∈ toIntegralProj (c • v) (smul_ne_zero hc hv) ⁻¹ᵁ
      Proj.basicOpen (UniversalGrading n) (MvPolynomial.X i)
    rw [toIntegralProj_preimage_basicOpen (c • v) (smul_ne_zero hc hv)
      (MvPolynomial.X i) zero_lt_one (MvPolynomial.isHomogeneous_X _ i),
      coordinateGlobalSectionsHom_X]
    simp [hi, hc]
  have htmem (w : CoordinateSpace n) (hw : w ≠ 0) :
      t ∈ (toIntegralProj w hw x).asHomogeneousIdeal ↔
        (Scheme.ΓSpecIso ↧ℂ).hom (coordinateGlobalSectionsHom w t) = 0 := by
    rw [← not_iff_not, ← Proj.mem_basicOpen]
    change x ∈ toIntegralProj w hw ⁻¹ᵁ
      Proj.basicOpen (UniversalGrading n) t ↔ _
    rw [toIntegralProj_preimage_basicOpen w hw t (Nat.zero_lt_succ d) ht]
    split_ifs with h <;> simp [h]
  change s ∈ (toIntegralProj (c • v) (smul_ne_zero hc hv) x).asHomogeneousIdeal ↔
    s ∈ (toIntegralProj v hv x).asHomogeneousIdeal
  have hmul_cv : t ∈
      (toIntegralProj (c • v) (smul_ne_zero hc hv) x).asHomogeneousIdeal ↔
        s ∈ (toIntegralProj (c • v) (smul_ne_zero hc hv) x).asHomogeneousIdeal :=
    ⟨fun h ↦ ((toIntegralProj (c • v) (smul_ne_zero hc hv) x).isPrime.mem_or_mem
      h).resolve_right hXi_cv, fun h ↦ Ideal.mul_mem_right _ _ h⟩
  have hmul_v : t ∈ (toIntegralProj v hv x).asHomogeneousIdeal ↔
      s ∈ (toIntegralProj v hv x).asHomogeneousIdeal :=
    ⟨fun h ↦ ((toIntegralProj v hv x).isPrime.mem_or_mem h).resolve_right hXi_v,
      fun h ↦ Ideal.mul_mem_right _ _ h⟩
  rw [← hmul_cv, ← hmul_v, htmem, htmem, coordinateGlobalSectionsHom_smul t ht c v]
  simp [hc]

/-- Homogeneous coordinates give a scale-independent map to the underlying projective spectrum.
This is the point-level part of the comparison with scheme-theoretic projective space. -/
noncomputable def projectivizationToIntegralProjPointAt {n : ℕ} (x : Spec ↧ℂ) :
    Projectivization ℂ (CoordinateSpace n) → Proj (UniversalGrading n) :=
  Projectivization.lift
    (fun v ↦ toIntegralProj v.1 v.2 x)
    (fun a b c h ↦ by
      have hc : c ≠ 0 := by
        intro hc
        apply a.2
        rw [h, hc, zero_smul]
      simpa only [h] using toIntegralProj_apply_smul b.1 b.2 c hc x)

@[simp]
lemma projectivizationToIntegralProjPointAt_mk {n : ℕ} (x : Spec ↧ℂ)
    (v : CoordinateSpace n) (hv : v ≠ 0) :
    projectivizationToIntegralProjPointAt x (Projectivization.mk ℂ v hv) =
      toIntegralProj v hv x :=
  rfl

end ComplexProjectiveSpace

end AlgebraicGeometry
