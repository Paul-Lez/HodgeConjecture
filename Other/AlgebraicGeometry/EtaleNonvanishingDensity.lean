/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexEtale
public import HodgeConjecture.Lemmas.Analysis.PolynomialComplement
public import Other.RingTheory.StandardEtaleAlgebraic
public import Other.RingTheory.AlgebraicNonvanishingObstruction

/-!
# Analytic density on étale complex algebras

The nonvanishing locus of a nonzero element in an étale domain over a complex polynomial ring is dense in its complex points.
-/

@[expose] public section

open scoped Topology

open Set
open Polynomial

namespace AlgebraicGeometry.ComplexAlgHom

noncomputable section

variable {n : ℕ} (T : Type) [CommRing T] [Algebra ℂ T]
  [Algebra (complexPolynomialRing n) T]
  [IsScalarTower ℂ (complexPolynomialRing n) T]
  [Algebra.Etale (complexPolynomialRing n) T]

variable [IsDomain T]

/-- The nonzero locus of a nonzero element of a pointed étale domain is dense in its complex
algebra-homomorphism space. -/
theorem dense_eval_ne_zero (n : ℕ) [Algebra (complexPolynomialRing n) T]
    [IsScalarTower ℂ (complexPolynomialRing n) T]
    [Algebra.Etale (complexPolynomialRing n) T]
    (b : T) (hb : b ≠ 0) :
    Dense {v : T →ₐ[ℂ] ℂ | v b ≠ 0} := by
  rw [dense_iff_inter_open]
  intro O hO hOne
  obtain ⟨u, huO⟩ := hOne
  let D := etaleStandardNeighborhood (n := n) T u
  let e := etaleAlgHomProjectionChart (n := n) T u
  have hu : u ∈ e.source := mem_etaleAlgHomProjectionChart_source (n := n) T u
  have helement : D.element ≠ 0 := by
    intro h
    exact D.nonzero (by rw [h, map_zero])
  have hlocal : Function.Injective (algebraMap T (Localization.Away D.element)) := by
    apply IsLocalization.injective (M := Submonoid.powers D.element) _
    rintro x ⟨m, rfl⟩
    exact pow_mem (mem_nonZeroDivisors_of_ne_zero helement) m
  have hbS : algebraMap T (Localization.Away D.element) b ≠ 0 := by
    intro h
    apply hb
    exact hlocal (by simpa using h)
  let _ : Algebra.IsStandardEtale (complexPolynomialRing n)
      (Localization.Away D.element) := D.isStandard
  have hbSalg : IsAlgebraic (complexPolynomialRing n)
      (algebraMap T (Localization.Away D.element) b) :=
    (Algebra.IsStandardEtale.isAlgebraic _ _).isAlgebraic _
  obtain ⟨p, hp0, hpS⟩ := hbSalg.exists_nonzero_coeff_and_aeval_eq_zero
    (mem_nonZeroDivisors_of_ne_zero hbS)
  have hpT : aeval b p = 0 := by
    apply hlocal
    rw [map_zero]
    change (IsScalarTower.toAlgHom (complexPolynomialRing n) T
      (Localization.Away D.element)) (aeval b p) = 0
    rw [← aeval_algHom_apply]
    simpa only [IsScalarTower.toAlgHom_apply] using hpS
  let W := e.target ∩ e.symm ⁻¹' O
  have hWopen : IsOpen W := e.isOpen_inter_preimage_symm hO
  have hutarget : e u ∈ e.target := e.map_source hu
  have heuW : e u ∈ W := by
    refine ⟨hutarget, ?_⟩
    change e.symm (e u) ∈ O
    rw [e.left_inv hu]
    exact huO
  obtain ⟨w, hwW, hpw⟩ :=
    (MvPolynomial.dense_complex_nonzero (p.coeff 0) hp0).inter_open_nonempty
      W hWopen ⟨e u, heuW⟩
  let v : T →ₐ[ℂ] ℂ := e.symm w
  have hwtarget : w ∈ e.target := hwW.1
  have hvsource : v ∈ e.source := e.map_target hwtarget
  have hev : e v = w := e.right_inv hwtarget
  have hchart := etaleAlgHomProjectionChart_apply_of_mem (n := n) T u v hvsource
  have hcoordinates :
      mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom (n := n) T v) = w := by
    rw [← hchart]
    exact hev
  refine ⟨v, hwW.2, ?_⟩
  intro hvb
  have hkill := Polynomial.map_coeff_zero_eq_zero_of_map_eq_zero hpT
    (etaleBaseAlgHom (n := n) T v).toRingHom v.toRingHom (by rfl) hvb
  have hbase_eq :
      MvPolynomial.aeval
          (mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom (n := n) T v)) =
        etaleBaseAlgHom (n := n) T v :=
    (mvPolynomialAlgHomHomeomorph n).symm_apply_apply _
  have heval := congrFun (congrArg DFunLike.coe hbase_eq.symm) (p.coeff 0) ▸ hkill
  rw [hcoordinates] at heval
  exact hpw heval
end

end AlgebraicGeometry.ComplexAlgHom

namespace AlgebraicGeometry.ComplexPoint

open Point

open CategoryTheory
noncomputable section

variable (T : Type) [CommRing T] [Algebra ℂ T] (n : ℕ)
  [Algebra (ComplexAlgHom.complexPolynomialRing n) T]
  [IsScalarTower ℂ (ComplexAlgHom.complexPolynomialRing n) T]
  [Algebra.Etale (ComplexAlgHom.complexPolynomialRing n) T]
  [IsDomain T]

/-- A nonzero global function on an affine pointed étale domain has analytically dense principal
open subset. -/
theorem dense_overOpen_basicOpen_of_etale (n : ℕ)
    [Algebra (ComplexAlgHom.complexPolynomialRing n) T]
    [IsScalarTower ℂ (ComplexAlgHom.complexPolynomialRing n) T]
    [Algebra.Etale (ComplexAlgHom.complexPolynomialRing n) T] (b : T) (hb : b ≠ 0) :
    Dense (overOpen ((Spec (CommRingCat.of T)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of T)).inv b)) :
      Set (ComplexPoint (Over.mk (affineSpecStructureMap T)))) := by
  rw [show (overOpen ((Spec (CommRingCat.of T)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of T)).inv b)) :
      Set (ComplexPoint (Over.mk (affineSpecStructureMap T)))) =
      (affineSpecEquiv T) ⁻¹' {φ : T →ₐ[ℂ] ℂ | φ b ≠ 0} by
    ext z
    change z ∈ overOpen ((Over.mk (affineSpecStructureMap T)).left.basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of T)).inv b)) ↔ affineSpecEquiv T z b ≠ 0
    rw [mem_overOpen_basicOpen_iff_evaluate_ne_zero
      (X := Over.mk (affineSpecStructureMap T)) (U := ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of T)).inv b) z trivial]
    rw [affineSpecEquiv_apply]]
  exact (affineSpecHomeomorph T).isOpenQuotientMap.dense_preimage_iff.2
    (ComplexAlgHom.dense_eval_ne_zero T n b hb)
