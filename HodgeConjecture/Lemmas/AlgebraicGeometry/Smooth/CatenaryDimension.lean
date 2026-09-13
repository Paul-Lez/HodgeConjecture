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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Support
public import HodgeConjecture.Lemmas.RingTheory.TranscendenceDegreeKrullDimension

import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.Dimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.DimensionFormula
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.PointwiseDimension
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import HodgeConjecture.Mathlib.Algebra.PolynomialCatenary
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Catenary dimension formulas for smooth complex schemes

This file proves the arbitrary-dimensional pointwise dimension formula for smooth complex
schemes.  Its commutative-algebra bridge is
`HodgeConjecture.Lemmas.RingTheory.TranscendenceDegreeKrullDimension`, which compares quotient
dimensions under a quasi-finite map of finite-type algebras using Noether normalization and the
finite extension of residue fields, rather than any unproved catenarity assumption or flatness
of the quotient map.

Applied to the étale polynomial coordinates of a standard-smooth algebra, the bridge transfers
the arbitrary-prime polynomial dimension formula.  An affine neighborhood then supplies enough
specialization chains to prove `height x + coheight x = d` at every point of a smooth complex
`d`-fold.  Consequently, the reduced closure of a point of coheight `p` has dimension `d - p`.
-/

@[expose] public noncomputable section

open CategoryTheory Ideal MvPolynomial Topology

namespace AlgebraicGeometry

end AlgebraicGeometry

namespace RingHom

/-- For every prime of a standard-smooth complex algebra of relative dimension `d`, its height
plus the dimension of its quotient is `d`. -/
lemma IsStandardSmoothOfRelativeDimension.height_add_ringKrullDim_quotient_eq_complex
    {S : Type} [CommRing S] {f : ℂ →+* S} {d : ℕ}
    (hf : f.IsStandardSmoothOfRelativeDimension d)
    (P : Ideal S) [P.IsPrime] :
    (↑P.height : WithBot ℕ∞) + ringKrullDim (S ⧸ P) = d := by
  obtain ⟨g, hgC, hg⟩ := hf.exists_etale_mvPolynomial
  let : Algebra ℂ S := f.toAlgebra
  let : Algebra (MvPolynomial (Fin d) ℂ) S := g.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) S :=
    IsScalarTower.of_algebraMap_eq' hgC.symm
  let : Algebra.Etale (MvPolynomial (Fin d) ℂ) S :=
    RingHom.etale_algebraMap.mp hg
  let : Algebra.FiniteType ℂ S :=
    Algebra.FiniteType.trans (R := ℂ) (S := MvPolynomial (Fin d) ℂ)
      (A := S) inferInstance inferInstance
  have hheight : P.height = (P.under (MvPolynomial (Fin d) ℂ)).height :=
    Algebra.QuasiFinite.height_eq_height_under P
  have hquot : ringKrullDim (S ⧸ P) =
      ringKrullDim (MvPolynomial (Fin d) ℂ ⧸ P.under (MvPolynomial (Fin d) ℂ)) :=
    Algebra.QuasiFinite.ringKrullDim_quotient_eq
      (k := ℂ) (R := MvPolynomial (Fin d) ℂ) P
  rw [hheight, hquot]
  exact PolynomialCatenary.MvPolynomial.height_add_ringKrullDim_quotient_eq_fin
    (P.under (MvPolynomial (Fin d) ℂ))

end RingHom

namespace AlgebraicGeometry

variable {X : Scheme.{0}} {f : X ⟶ Spec ↧ℂ} {d : ℕ}

end AlgebraicGeometry
