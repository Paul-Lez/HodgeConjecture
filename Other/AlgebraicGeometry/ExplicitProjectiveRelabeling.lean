/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ExplicitProjectiveSpaceChart
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Relabeling projective homogeneous coordinates
-/

@[expose] public noncomputable section

open MvPolynomial CategoryTheory

namespace AlgebraicGeometry.ProjectiveRelabeling

universe u
variable (R : Type u) [CommRing R] {σ τ ρ : Type u}

attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Renaming homogeneous coordinates preserves the standard grading. -/
def gradedRename (e : σ ≃ τ) : homogeneousSubmodule σ R →+*ᵍ homogeneousSubmodule τ R where
  __ := rename e
  map_mem h := h.rename_isHomogeneous

/-- A coordinate relabeling preserves the irrelevant ideal. -/
theorem irrelevant_le_map (e : σ ≃ τ) :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule τ R) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ R)).map (gradedRename R e) := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
  intro p hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨d, hd, hp⟩ := hp
  have hm := HomogeneousIdeal.mem_irrelevant_of_mem (homogeneousSubmodule σ R) hd
    (hp.rename_isHomogeneous (f := e.symm))
  have := Ideal.mem_map_of_mem (gradedRename R e) hm
  simpa [gradedRename, rename_rename] using this

@[simp] theorem gradedRename_refl : gradedRename R (Equiv.refl σ) =
    GradedRingHom.id (homogeneousSubmodule σ R) := by
  ext p
  simp [gradedRename]

@[simp] theorem gradedRename_comp (e : σ ≃ τ) (d : τ ≃ ρ) :
    (gradedRename R d).comp (gradedRename R e) = gradedRename R (e.trans d) := by
  ext p
  simp [gradedRename, rename_rename]

/-- Relabeling gives an isomorphism of the actual projective spectra. -/
def iso (e : σ ≃ τ) : Proj (homogeneousSubmodule σ R) ≅
    Proj (homogeneousSubmodule τ R) where
  hom := Proj.map (gradedRename R e.symm) (irrelevant_le_map R e.symm)
  inv := Proj.map (gradedRename R e) (irrelevant_le_map R e)
  hom_inv_id := by
    rw [← Proj.map_comp]
    simp only [gradedRename_comp, Equiv.self_trans_symm, gradedRename_refl, Proj.map_id]
  inv_hom_id := by
    rw [← Proj.map_comp]
    simp only [gradedRename_comp, Equiv.symm_trans_self, gradedRename_refl, Proj.map_id]

/-- The relabeling sends each coordinate basic open to the corresponding coordinate basic open. -/
theorem iso_hom_preimage_basicOpen (e : σ ≃ τ) (a : τ) :
    (iso R e).hom ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule τ R) (X a) =
      Proj.basicOpen (homogeneousSubmodule σ R) (X (e.symm a)) := by
  rw [iso, Proj.map_preimage_basicOpen]
  simp [gradedRename]

end AlgebraicGeometry.ProjectiveRelabeling
