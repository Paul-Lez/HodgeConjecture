/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexEtale
import HodgeConjecture.Lemmas.Analysis.PolynomialComplement

/-!
# Injectivity of pointed étale coordinate maps

An étale algebra over a complex polynomial ring which has a complex point is faithful over its
polynomial base. This follows directly from an analytic projection chart at that point and the
density of the nonzero locus of a nonzero complex polynomial.
-/

open scoped Topology

open Set

namespace AlgebraicGeometry.ComplexAlgHom

noncomputable section

variable {n : ℕ} (T : Type) [CommRing T] [Algebra ℂ T]
  [Algebra (complexPolynomialRing n) T]
  [IsScalarTower ℂ (complexPolynomialRing n) T]
  [Algebra.Etale (complexPolynomialRing n) T]

/-- An étale algebra over a complex polynomial ring with a complex point has an injective
coordinate-ring map. -/
theorem injective_algebraMap_of_etale_of_point (u : T →ₐ[ℂ] ℂ) :
    Function.Injective (algebraMap (complexPolynomialRing n) T) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  let e := etaleAlgHomProjectionChart (n := n) T u
  have hu : u ∈ e.source := mem_etaleAlgHomProjectionChart_source (n := n) T u
  have hetarget : e.target.Nonempty := ⟨e u, e.map_source hu⟩
  obtain ⟨w, hw, hwp⟩ :=
    (MvPolynomial.dense_complex_nonzero p hp0).inter_open_nonempty
      e.target e.open_target hetarget
  let v : T →ₐ[ℂ] ℂ := e.symm w
  have hv : v ∈ e.source := e.map_target hw
  have hev : e v = w := e.right_inv hw
  have hchart := etaleAlgHomProjectionChart_apply_of_mem (n := n) T u v hv
  have hcoordinates :
      mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom (n := n) T v) = w := by
    rw [← hchart]
    exact hev
  have hvp : v (algebraMap (complexPolynomialRing n) T p) = 0 := by
    rw [hp, map_zero]
  have hbase : etaleBaseAlgHom (n := n) T v p = 0 := by
    exact hvp
  have hbase_eq :
      MvPolynomial.aeval
          (mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom (n := n) T v)) =
        etaleBaseAlgHom (n := n) T v :=
    (mvPolynomialAlgHomHomeomorph n).symm_apply_apply _
  have heval := congrFun (congrArg DFunLike.coe hbase_eq.symm) p ▸ hbase
  rw [hcoordinates] at heval
  exact hwp heval

end

end AlgebraicGeometry.ComplexAlgHom
