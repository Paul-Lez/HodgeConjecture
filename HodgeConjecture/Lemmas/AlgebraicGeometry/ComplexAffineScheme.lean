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

public import HodgeConjecture.Mathlib.Algebra.Category.Ring.Basic
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexAffineSpace

/-!
# Complex points of affine schemes

The complex points of `Spec R` are canonically homeomorphic to the space of complex algebra
homomorphisms from `R` to `ℂ`, equipped with the topology of pointwise convergence. The proof of
continuity in the reverse direction uses the localization description of regular functions on
principal opens.
-/

@[expose] public section

open CategoryTheory Topology

namespace AlgebraicGeometry.ComplexPoint

noncomputable section

variable (R : Type) [CommRing R] [Algebra ℂ R]

/-- The topology of pointwise convergence on complex algebra homomorphisms. -/
noncomputable instance affineAlgebraHomTopology : TopologicalSpace (R →ₐ[ℂ] ℂ) :=
  TopologicalSpace.induced (fun φ : R →ₐ[ℂ] ℂ ↦ (φ : R → ℂ)) inferInstance

/-- The structure morphism of an affine complex scheme. -/
abbrev affineSpecStructureMap : Spec ↧R ⟶ Spec ↧ℂ :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ R))

noncomputable local instance :
    TopologicalSpace (ComplexPoint (Spec ↧R) (affineSpecStructureMap R)) :=
  analyticTopology

/-- Complex points of `Spec R` correspond to complex algebra homomorphisms from `R` to `ℂ`. -/
def affineSpecEquiv :
    ComplexPoint (Spec ↧R) (affineSpecStructureMap R) ≃ (R →ₐ[ℂ] ℂ) where
  toFun z :=
    { toRingHom := (Spec.homEquiv z.1).hom
      commutes' c := by
        have hz := congrArg Spec.preimage z.2
        have hr : CommRingCat.ofHom (algebraMap ℂ R) ≫ Spec.preimage z.1 =
            𝟙 (CommRingCat.of ℂ) := by
          simpa [affineSpecStructureMap, Spec.preimage_comp] using hz
        exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hr) c }
  invFun φ := ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), by
    rw [← Spec.map_comp]
    rw [← Spec.map_id]
    congr 1
    ext c
    exact φ.commutes c⟩
  left_inv z := by
    apply Subtype.ext
    exact Spec.map_preimage z.1
  right_inv φ := by
    ext r
    simp [Spec.homEquiv_apply]

lemma affineSpecEquiv_apply
    (z : ComplexPoint (Spec ↧R) (affineSpecStructureMap R)) (r : R) :
    affineSpecEquiv R z r =
      evaluate ⊤ ((Scheme.ΓSpecIso ↧R).inv r) z := by
  rw [evaluate_top_eq_appTop]
  change (Spec.preimage z.1).hom r =
    (Scheme.ΓSpecIso ↧ℂ).hom (z.1.appTop ((Scheme.ΓSpecIso ↧R).inv r))
  have h := Scheme.ΓSpecIso_naturality (Spec.preimage z.1)
  rw [Spec.map_preimage] at h
  have h' := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h)
    ((Scheme.ΓSpecIso ↧R).inv r)
  simpa using h'.symm

lemma evaluate_affineSpecEquiv_symm_top (s : Γ(Spec ↧R, ⊤)) (φ : R →ₐ[ℂ] ℂ) :
    evaluate ⊤ s ((affineSpecEquiv R).symm φ) =
      φ ((Scheme.ΓSpecIso ↧R).hom s) := by
  calc
    evaluate ⊤ s ((affineSpecEquiv R).symm φ) =
        evaluate ⊤ ((Scheme.ΓSpecIso ↧R).inv
          ((Scheme.ΓSpecIso ↧R).hom s)) ((affineSpecEquiv R).symm φ) := by simp
    _ = affineSpecEquiv R ((affineSpecEquiv R).symm φ)
          ((Scheme.ΓSpecIso ↧R).hom s) :=
      (affineSpecEquiv_apply R _ _).symm
    _ = φ ((Scheme.ΓSpecIso ↧R).hom s) := by simp

lemma continuous_affineAlgebraHom_apply (r : R) :
    Continuous (fun φ : R →ₐ[ℂ] ℂ ↦ φ r) := by
  exact (continuous_apply r).comp continuous_induced_dom

lemma continuous_affineSpecEquiv :
    @Continuous
      (ComplexPoint (Spec ↧R) (affineSpecStructureMap R))
      (R →ₐ[ℂ] ℂ) analyticTopology (affineAlgebraHomTopology R)
      (affineSpecEquiv R) := by
  rw [continuous_induced_rng]
  exact continuous_pi fun r ↦ by
    simpa only [Function.comp_apply, affineSpecEquiv_apply] using
      continuous_evaluate_top ((Scheme.ΓSpecIso ↧R).inv r)

lemma isOpen_affineSpecEquiv_symm_preimage_overOpen_basicOpen
    (s : Γ(Spec ↧R, ⊤)) :
    IsOpen ((affineSpecEquiv R).symm ⁻¹'
      overOpen ((Spec ↧R).basicOpen s)) := by
  rw [show (affineSpecEquiv R).symm ⁻¹'
      overOpen ((Spec ↧R).basicOpen s) =
      {φ | φ ((Scheme.ΓSpecIso ↧R).hom s) ≠ 0} by
    ext φ
    rw [Set.mem_preimage, mem_overOpen_basicOpen_iff_evaluate_ne_zero,
      evaluate_affineSpecEquiv_symm_top]
    rfl]
  exact isOpen_ne_fun
    (continuous_affineAlgebraHom_apply R ((Scheme.ΓSpecIso ↧R).hom s))
    continuous_const

/-- On an affine scheme, evaluation of a section on a principal open is locally a quotient of
evaluations of global sections. -/
lemma exists_evaluate_affine_basicOpen_eq_div {X : Scheme} [IsAffine X]
    {structureMap : X ⟶ Spec ↧ℂ} (f : Γ(X, ⊤)) (t : Γ(X, X.basicOpen f)) :
    ∃ (k : ℕ) (a : Γ(X, ⊤)),
      ∀ z : ComplexPoint X structureMap, z ∈ overOpen (X.basicOpen f) →
        evaluate (X.basicOpen f) t z = evaluate ⊤ a z / evaluate ⊤ f z ^ k := by
  let _ := AlgebraicGeometry.isLocalization_away_of_isAffine f
  obtain ⟨k, a, hta⟩ := IsLocalization.Away.surj f t
  refine ⟨k, a, ?_⟩
  intro z hz
  have hden : evaluate ⊤ f z ≠ 0 :=
    (mem_overOpen_basicOpen_iff_evaluate_ne_zero f z).mp hz
  apply (eq_div_iff (pow_ne_zero k hden)).2
  let ψ : Γ(X, X.basicOpen f) →+* ℂ :=
    z.residueData.2.hom.comp
      (X.evaluation (X.basicOpen f) z.residueData.1 hz).hom
  have hmap := congrArg ψ hta
  have hf := evaluate_res (X.basicOpen_le f) f z hz
  have ha := evaluate_res (X.basicOpen_le f) a z hz
  have hz' : z.residueData.1 ∈ X.basicOpen f := hz
  rw [hf, ha]
  simp only [evaluate, dif_pos hz']
  change ψ t * ψ (algebraMap _ _ f) ^ k = ψ (algebraMap _ _ a)
  simpa using hmap

lemma exists_evaluate_affineSpec_basicOpen_eq_div
    (f : Γ(Spec ↧R, ⊤))
    (t : Γ(Spec ↧R, (Spec ↧R).basicOpen f)) :
    ∃ (k : ℕ) (a : Γ(Spec ↧R, ⊤)),
      ∀ z : ComplexPoint (Spec ↧R) (affineSpecStructureMap R),
        z ∈ overOpen ((Spec ↧R).basicOpen f) →
          evaluate ((Spec ↧R).basicOpen f) t z =
            evaluate ⊤ a z / evaluate ⊤ f z ^ k :=
  exists_evaluate_affine_basicOpen_eq_div f t

lemma continuousOn_evaluate_affineSpec_basicOpen_equiv_symm
    (f : Γ(Spec ↧R, ⊤))
    (t : Γ(Spec ↧R, (Spec ↧R).basicOpen f)) :
    ContinuousOn
      (fun φ : R →ₐ[ℂ] ℂ ↦ evaluate ((Spec ↧R).basicOpen f) t
        ((affineSpecEquiv R).symm φ))
      ((affineSpecEquiv R).symm ⁻¹'
        overOpen ((Spec ↧R).basicOpen f)) := by
  obtain ⟨k, a, h⟩ := exists_evaluate_affineSpec_basicOpen_eq_div R f t
  have ha : Continuous (fun φ : R →ₐ[ℂ] ℂ ↦
      evaluate ⊤ a ((affineSpecEquiv R).symm φ)) := by
    simpa only [evaluate_affineSpecEquiv_symm_top] using
      continuous_affineAlgebraHom_apply R ((Scheme.ΓSpecIso ↧R).hom a)
  have hf : Continuous (fun φ : R →ₐ[ℂ] ℂ ↦
      evaluate ⊤ f ((affineSpecEquiv R).symm φ)) := by
    simpa only [evaluate_affineSpecEquiv_symm_top] using
      continuous_affineAlgebraHom_apply R ((Scheme.ΓSpecIso ↧R).hom f)
  have hrat : ContinuousOn
      (fun φ : R →ₐ[ℂ] ℂ ↦ evaluate ⊤ a ((affineSpecEquiv R).symm φ) /
        evaluate ⊤ f ((affineSpecEquiv R).symm φ) ^ k)
      ((affineSpecEquiv R).symm ⁻¹'
        overOpen ((Spec ↧R).basicOpen f)) :=
    ha.continuousOn.div (hf.pow k).continuousOn fun φ hφ ↦
      pow_ne_zero k ((mem_overOpen_basicOpen_iff_evaluate_ne_zero f _).mp hφ)
  exact hrat.congr fun φ hφ ↦ h _ hφ

lemma continuous_affineSpecEquiv_symm :
    @Continuous (R →ₐ[ℂ] ℂ)
      (ComplexPoint (Spec ↧R) (affineSpecStructureMap R))
      (affineAlgebraHomTopology R) analyticTopology (affineSpecEquiv R).symm := by
  rw [continuous_generateFrom_iff]
  rintro W ⟨U, s, V, hV, rfl⟩
  rw [Set.preimage_inter, Set.preimage_preimage]
  apply isOpen_iff_forall_mem_open.mpr
  rintro φ ⟨hφU, hφV⟩
  obtain ⟨f, hfU, hφf⟩ :=
    (isAffineOpen_top (Spec ↧R)).exists_basicOpen_le
      ⟨((affineSpecEquiv R).symm φ).underlying, hφU⟩ trivial
  let t := (Spec ↧R).presheaf.map (homOfLE hfU).op s
  let N := (affineSpecEquiv R).symm ⁻¹'
      overOpen ((Spec ↧R).basicOpen f) ∩
    (fun ψ : R →ₐ[ℂ] ℂ ↦ evaluate ((Spec ↧R).basicOpen f) t
      ((affineSpecEquiv R).symm ψ)) ⁻¹' V
  have hNopen : IsOpen N :=
    (continuousOn_evaluate_affineSpec_basicOpen_equiv_symm R f t).isOpen_inter_preimage
      (isOpen_affineSpecEquiv_symm_preimage_overOpen_basicOpen R f) hV
  refine ⟨N, ?_, hNopen, ?_⟩
  · rintro ψ ⟨hψf, hψV⟩
    have hψU : (affineSpecEquiv R).symm ψ ∈ overOpen U := hfU hψf
    refine ⟨hψU, ?_⟩
    change evaluate U s ((affineSpecEquiv R).symm ψ) ∈ V
    rw [evaluate_res hfU s _ hψf]
    exact hψV
  · refine ⟨hφf, ?_⟩
    change evaluate ((Spec ↧R).basicOpen f) t
      ((affineSpecEquiv R).symm φ) ∈ V
    rw [← evaluate_res hfU s _ hφf]
    exact hφV

/-- The complex points of `Spec R` are homeomorphic to the complex algebra homomorphisms
from `R` to `ℂ`, with their topology of pointwise convergence. -/
def affineSpecHomeomorph :
    @Homeomorph
      (ComplexPoint (Spec ↧R) (affineSpecStructureMap R))
      (R →ₐ[ℂ] ℂ) analyticTopology (affineAlgebraHomTopology R) where
  toEquiv := affineSpecEquiv R
  continuous_toFun := continuous_affineSpecEquiv R
  continuous_invFun := continuous_affineSpecEquiv_symm R

variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

/-- The affine scheme morphism contravariantly associated to a complex algebra homomorphism. -/
abbrev affineSpecMap (g : A →ₐ[ℂ] B) : Spec ↧B ⟶ Spec ↧A :=
  Spec.map (CommRingCat.ofHom g.toRingHom)

lemma affineSpecMap_over (g : A →ₐ[ℂ] B) :
    affineSpecMap g ≫ affineSpecStructureMap A = affineSpecStructureMap B := by
  rw [← Spec.map_comp]
  congr 1
  ext c
  exact g.commutes c

/-- The map on complex points contravariantly associated to a complex algebra homomorphism. -/
def affineSpecComplexPointMap (g : A →ₐ[ℂ] B) :
    ComplexPoint (Spec ↧B) (affineSpecStructureMap B) →
      ComplexPoint (Spec ↧A) (affineSpecStructureMap A) :=
  map (affineSpecMap g) (affineSpecMap_over g)

/-- Under the affine-point equivalence, an affine scheme map acts by precomposition of algebra
homomorphisms. -/
lemma affineSpecEquiv_affineSpecComplexPointMap (g : A →ₐ[ℂ] B)
    (z : ComplexPoint (Spec ↧B) (affineSpecStructureMap B)) :
    affineSpecEquiv A (affineSpecComplexPointMap g z) =
      (affineSpecEquiv B z).comp g := by
  apply AlgHom.coe_ringHom_injective
  apply DFunLike.ext _ _
  intro a
  simp [affineSpecComplexPointMap, map, affineSpecEquiv, affineSpecMap,
    Spec.preimage_comp]

end

end AlgebraicGeometry.ComplexPoint
