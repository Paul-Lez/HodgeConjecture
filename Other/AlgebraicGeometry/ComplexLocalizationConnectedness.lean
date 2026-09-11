/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Other.AlgebraicGeometry.ComplexIteratedLocalization
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexLocalization
public import Other.AlgebraicGeometry.SmoothLocalNonvanishing

@[expose] public section

open scoped Polynomial Topology

namespace AlgebraicGeometry.ComplexAlgHom

open CategoryTheory Polynomial Set

noncomputable section

/-- A nonzero function on a smooth integral affine complex algebra has dense nonvanishing locus
in its complex algebra-hom space. -/
lemma dense_eval_ne_zero_of_smooth
    (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.Smooth ℂ B]
    (y : B) (hy : y ≠ 0) :
    Dense {u : B →ₐ[ℂ] ℂ | u y ≠ 0} := by
  let X := Over.mk (ComplexPoint.affineSpecStructureMap B)
  let t : Γ(X.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of B)).inv y
  have ht : t ≠ 0 := by
    intro h
    apply hy
    simpa [t] using congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).hom h
  let hschemeSmooth : Smooth X.hom := by
    change Smooth (ComplexPoint.affineSpecStructureMap B)
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).2
    change (algebraMap ℂ B).Smooth
    exact RingHom.smooth_algebraMap.mpr inferInstance
  let _ : Smooth X.hom := hschemeSmooth
  let _ : IsIntegral X.left := by
    change IsIntegral (Spec (CommRingCat.of B))
    infer_instance
  let _ : QuasiSeparatedSpace X.left := by
    change QuasiSeparatedSpace (Spec (CommRingCat.of B))
    infer_instance
  have hdense := ComplexPoint.dense_evaluate_ne_zero X t ht
  rw [show {z : ComplexPoint X | Point.evaluate ⊤ t z ≠ 0} =
      (ComplexPoint.affineSpecHomeomorph B) ⁻¹'
        {u : B →ₐ[ℂ] ℂ | u y ≠ 0} by
    ext z
    change Point.evaluate ⊤ t z ≠ 0 ↔ ComplexPoint.affineSpecEquiv B z y ≠ 0
    rw [ComplexPoint.affineSpecEquiv_apply]] at hdense
  exact (ComplexPoint.affineSpecHomeomorph B).isOpenQuotientMap.dense_preimage_iff.mp hdense

/-- The derivative times a nonzero base polynomial remains nonzero in the monogenic quotient.
Irreducibility of `p` is not needed for this degree argument. -/
lemma derivativeAdjoinRootElement_ne_zero {n : ℕ}
    (p : Polynomial (complexPolynomialRing n)) (hp : p.Monic)
    (hdeg : 0 < p.natDegree) (ρ : complexPolynomialRing n) (hρ : ρ ≠ 0) :
    derivativeAdjoinRootElement p ρ ≠ 0 := by
  apply AdjoinRoot.mk_ne_zero_of_natDegree_lt hp
  · apply mul_ne_zero
    · exact Polynomial.derivative_ne_zero.mpr (Nat.ne_of_gt hdeg)
    · exact Polynomial.C_ne_zero.mpr hρ
  · rw [Polynomial.natDegree_mul_C hρ]
    simpa using Polynomial.natDegree_derivative_lt (Nat.ne_of_gt hdeg)

/-- In the irreducible case the derivative element remains nonzero after the first localization
at a nonzero base polynomial. -/
lemma algebraMap_derivativeAdjoinRootElement_ne_zero {n : ℕ}
    (p : Polynomial (complexPolynomialRing n)) (hp : p.Monic)
    (hirr : Irreducible p) (hdeg : 0 < p.natDegree)
    (r ρ : complexPolynomialRing n) (hr : r ≠ 0) (hρ : ρ ≠ 0) :
    algebraMap (AdjoinRoot p)
      (Localization.Away (algebraMap (complexPolynomialRing n) (AdjoinRoot p) r))
      (derivativeAdjoinRootElement p ρ) ≠ 0 := by
  let _ : IsDomain (AdjoinRoot p) := AdjoinRoot.isDomain_of_prime hirr.prime
  have hpdeg : p.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero]
    exact_mod_cast (Nat.ne_of_gt hdeg)
  have hrAR : algebraMap (complexPolynomialRing n) (AdjoinRoot p) r ≠ 0 := by
    rw [AdjoinRoot.algebraMap_eq]
    simpa only [map_zero] using (AdjoinRoot.of.injective_of_degree_ne_zero hpdeg).ne hr
  simpa only [map_zero] using (IsLocalization.injective
    (Localization.Away (algebraMap (complexPolynomialRing n) (AdjoinRoot p) r))
    (powers_le_nonZeroDivisors_of_noZeroDivisors hrAR)).ne
      (derivativeAdjoinRootElement_ne_zero p hp hdeg ρ hρ)

/-- The element pulled back for the second localization is nonzero for any first-stage
normalization equivalence. -/
lemma symm_algebraMap_derivativeAdjoinRootElement_ne_zero {n : ℕ}
    {B : Type*} [CommRing B] [Algebra (complexPolynomialRing n) B]
    (p : Polynomial (complexPolynomialRing n)) (hp : p.Monic)
    (hirr : Irreducible p) (hdeg : 0 < p.natDegree)
    (r ρ : complexPolynomialRing n) (hr : r ≠ 0) (hρ : ρ ≠ 0)
    (e : B ≃ₐ[complexPolynomialRing n]
      Localization.Away (algebraMap (complexPolynomialRing n) (AdjoinRoot p) r)) :
    e.symm (algebraMap (AdjoinRoot p)
      (Localization.Away (algebraMap (complexPolynomialRing n) (AdjoinRoot p) r))
      (derivativeAdjoinRootElement p ρ)) ≠ 0 :=
  iteratedAwayAlgEquivOfAlgEquiv_symm_ne_zero e
    (algebraMap_derivativeAdjoinRootElement_ne_zero p hp hirr hdeg r ρ hr hρ)

/-- A dense nonvanishing locus is connected when the complex points of its localization are
connected. Therefore the whole affine complex point space is connected. -/
lemma isConnected_affineAlgHom_of_dense_nonvanishing_of_localization
    (B : Type) [CommRing B] [Algebra ℂ B] (y : B)
    (hdense : Dense {u : B →ₐ[ℂ] ℂ | u y ≠ 0})
    (hlocal : IsConnected
      (Set.univ : Set (Localization.Away y →ₐ[ℂ] ℂ))) :
    IsConnected (Set.univ : Set (B →ₐ[ℂ] ℂ)) := by
  let e := localizationAwayAlgHomHomeomorph B y
  have hopen : IsConnected (Set.univ : Set (nonvanishingAlgHom B y)) := by
    have h := (e.isConnected_image (s := Set.univ)).2 hlocal
    simpa only [image_univ, EquivLike.range_eq_univ] using h
  have hnonvanishing : IsConnected {u : B →ₐ[ℂ] ℂ | u y ≠ 0} := by
    have h := hopen.image ((↑) : nonvanishingAlgHom B y → (B →ₐ[ℂ] ℂ))
      continuous_subtype_val.continuousOn
    simpa only [image_univ, Subtype.range_coe_subtype] using h
  have hclosure := hnonvanishing.closure
  simpa only [hdense.closure_eq] using hclosure

/-- Connectedness of complex points descends from a localization whose nonvanishing locus is
dense. -/
lemma connectedSpace_affineAlgHom_of_dense_nonvanishing_of_localization
    (B : Type) [CommRing B] [Algebra ℂ B] (y : B)
    (hdense : Dense {u : B →ₐ[ℂ] ℂ | u y ≠ 0})
    [ConnectedSpace (Localization.Away y →ₐ[ℂ] ℂ)] :
    ConnectedSpace (B →ₐ[ℂ] ℂ) := by
  rw [connectedSpace_iff_univ]
  exact isConnected_affineAlgHom_of_dense_nonvanishing_of_localization B y hdense
    isConnected_univ

/-- Connectedness descends successively through two localizations when both nonvanishing loci
are dense. -/
lemma connectedSpace_affineAlgHom_of_two_dense_localizations
    (B : Type) [CommRing B] [Algebra ℂ B] (y : B)
    (z : Localization.Away y)
    (hdense₁ : Dense {u : B →ₐ[ℂ] ℂ | u y ≠ 0})
    (hdense₂ : Dense
      {u : Localization.Away y →ₐ[ℂ] ℂ | u z ≠ 0})
    [ConnectedSpace (Localization.Away z →ₐ[ℂ] ℂ)] :
    ConnectedSpace (B →ₐ[ℂ] ℂ) := by
  let _ : ConnectedSpace (Localization.Away y →ₐ[ℂ] ℂ) :=
    connectedSpace_affineAlgHom_of_dense_nonvanishing_of_localization
      (Localization.Away y) z hdense₂
  exact connectedSpace_affineAlgHom_of_dense_nonvanishing_of_localization B y hdense₁

/-- For a smooth integral affine algebra, connectedness descends through two localizations at
nonzero elements. Smoothness of the first localization follows from smoothness of the original
algebra and stability under localization. -/
lemma connectedSpace_affineAlgHom_of_two_smooth_localizations
    (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.Smooth ℂ B]
    (y : B) (hy : y ≠ 0) (z : Localization.Away y) (hz : z ≠ 0)
    [ConnectedSpace (Localization.Away z →ₐ[ℂ] ℂ)] :
    ConnectedSpace (B →ₐ[ℂ] ℂ) := by
  let _ : IsDomain (Localization.Away y) :=
    IsLocalization.Away.isDomain (S := Localization.Away y) hy
  let _ : Algebra.Smooth B (Localization.Away y) :=
    Algebra.Smooth.of_isLocalization_Away y
  let _ : Algebra.Smooth ℂ (Localization.Away y) :=
    Algebra.Smooth.comp ℂ B (Localization.Away y)
  exact connectedSpace_affineAlgHom_of_two_dense_localizations B y z
    (dense_eval_ne_zero_of_smooth B y hy)
    (dense_eval_ne_zero_of_smooth (Localization.Away y) z hz)

end

end AlgebraicGeometry.ComplexAlgHom
