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

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.Complex.Basic

import HodgeConjecture.Mathlib.AlgebraicGeometry.PointClosure
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Support
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula
import HodgeConjecture.Mathlib.AlgebraicGeometry.GenericPoint
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib.RingTheory.Unramified.LocalStructure
import HodgeConjecture.Mathlib.Topology.KrullDimension

/-!
# Pointwise dimension of smooth complex schemes

This file proves the pointwise dimension formula at the generic and closed points of an integral
smooth complex scheme.  It also proves the formula at every point in relative dimensions zero,
one, or two.  The proofs pass through affine standard-smooth neighborhoods and maximal ideals
under étale coordinates.

Above relative dimension two, the remaining commutative-algebra statement is the arbitrary-prime
dimension formula for a polynomial ring over a field.  Mathlib currently proves the height of
maximal polynomial ideals and the global Krull dimension, but not this arbitrary-prime catenary
formula.  No higher-dimensional pointwise equality is assumed here.
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace

namespace RingHom

/-- Every maximal ideal of a standard-smooth complex algebra of relative dimension `d` has
height `d`. -/
lemma IsStandardSmoothOfRelativeDimension.height_eq_of_isMaximal
    {S : Type*} [CommRing S] {f : ℂ →+* S} {d : ℕ}
    (hf : f.IsStandardSmoothOfRelativeDimension d) (P : Ideal S) [P.IsMaximal] :
    P.height = d := by
  obtain ⟨g, _, hg⟩ := hf.exists_etale_mvPolynomial
  let : Algebra (MvPolynomial (Fin d) ℂ) S := g.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin d) ℂ) S :=
    RingHom.etale_algebraMap.mp hg
  have hfiniteType : (algebraMap (MvPolynomial (Fin d) ℂ) S).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  have hunder : (P.under (MvPolynomial (Fin d) ℂ)).IsMaximal :=
    hfiniteType.isMaximal_comap_of_isJacobsonRing P
  rw [Algebra.QuasiFinite.height_eq_height_under (R := MvPolynomial (Fin d) ℂ)]
  exact MvPolynomial.height_eq_fin_of_isMaximal ℂ d
    (P.under (MvPolynomial (Fin d) ℂ))

end RingHom

namespace AlgebraicGeometry

/-- Under an affine presentation, the height of the corresponding prime ideal is the coheight of
the scheme point. -/
lemma IsAffineOpen.primeIdealOf_height_eq_coheight {X : Scheme} {U : X.Opens}
    (hU : IsAffineOpen U) (x : U.toScheme) :
    (hU.primeIdealOf x).asIdeal.height = Order.coheight x := by
  calc
    (hU.isoSpec.hom x : Spec ↧Γ(X, U)).asIdeal.height =
        Order.coheight (hU.isoSpec.hom x) :=
      idealHeight_eq_coheight ↧Γ(X, U) (hU.isoSpec.hom x)
    _ = Order.coheight x := coheight_eq_of_isOpenImmersion hU.isoSpec.hom

variable {X : Scheme} {f : X ⟶ Spec ↧ℂ} {d : ℕ}

/-- A nonempty integral smooth complex scheme of relative dimension `d` has global order Krull
dimension exactly `d`. -/
lemma SmoothOfRelativeDimension.orderKrullDim_eq_complex [IsIntegral X]
    [SmoothOfRelativeDimension d f] : Order.krullDim X = d := by
  apply le_antisymm
    (SmoothOfRelativeDimension.orderKrullDim_le_complex (f := f) (d := d))
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨U, hU, hxU, hsmooth⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension
      (d := d) f x
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hUdim : Order.krullDim U = d := by
    rw [orderKrullDim_affineOpen_eq_ringKrullDim U hU]
    exact (algebraMap_isStandardSmoothOfRelativeDimension
      (d := d) (Over.mk f) hsmooth).ringKrullDim_eq_complex
  rw [← hUdim, ← topologicalKrullDim_eq_krullDim U.toScheme,
    ← topologicalKrullDim_eq_krullDim X]
  exact U.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le

/-- The pointwise dimension formula holds at every closed point of an integral smooth complex
scheme. -/
lemma SmoothOfRelativeDimension.height_add_coheight_eq_of_isClosed [IsIntegral X]
    [SmoothOfRelativeDimension d f] (x : X) (hx : IsClosed {x}) :
    Order.height x + Order.coheight x = d := by
  have hmin : IsMin x := by
    intro y hy
    have hy' : y ∈ closure {x} := by
      rwa [← specializes_iff_mem_closure, ← Scheme.le_iff_specializes]
    rw [hx.closure_eq] at hy'
    exact (Set.mem_singleton_iff.mp hy').ge
  have hheight : Order.height x = 0 := Order.IsMin.height_eq_zero hmin
  obtain ⟨U, hU, hxU, hsmooth⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension
      (d := d) f x
  let y : U.toScheme := ⟨x, hxU⟩
  let P : Ideal Γ(X, U) := (hU.primeIdealOf y).asIdeal
  let : P.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed y hx
  have hP : P.height = d :=
    (algebraMap_isStandardSmoothOfRelativeDimension
      (d := d) (Over.mk f) hsmooth).height_eq_of_isMaximal P
  have hcoheight : Order.coheight x = d := by
    calc
      Order.coheight x = Order.coheight y := coheight_eq_of_isOpenImmersion (x := y) U.ι
      _ = P.height := (hU.primeIdealOf_height_eq_coheight y).symm
      _ = d := hP
  rw [hheight, hcoheight, zero_add]

end AlgebraicGeometry
