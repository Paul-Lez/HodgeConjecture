/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Localization.Integral

/-!
# Standard étale algebras are algebraic over a domain

A standard étale algebra is a localization of a monogenic finite algebra. It need not be finite as
a module, but every one of its elements remains algebraic over the base field.
-/

open Polynomial

noncomputable section

namespace Algebra

variable (K S : Type*) [CommRing K] [IsDomain K] [CommRing S] [Algebra K S]

/-- Every standard étale algebra over a domain is algebraic over that domain. -/
theorem IsStandardEtale.isAlgebraic [IsStandardEtale K S] : Algebra.IsAlgebraic K S := by
  let P : StandardEtalePresentation K S :=
    IsStandardEtale.nonempty_standardEtalePresentation.some
  have hx : IsIntegral K P.x := ⟨P.f, P.monic_f, P.hasMap.1⟩
  have heval (q : K[X]) : IsIntegral K (aeval P.x q) := by
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
        simpa using hp.add hq
    | monomial n a =>
        simpa using (isIntegral_algebraMap : IsIntegral K (algebraMap K S a)).mul (hx.pow n)
  constructor
  intro z
  obtain ⟨p, n, hz⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x z
  let _ : Invertible (aeval P.x P.g) := P.hasMap.2.invertible
  have hg : IsAlgebraic K (aeval P.x P.g) := (heval P.g).isAlgebraic
  have hginv : IsAlgebraic K (⅟(aeval P.x P.g)) := hg.invOf
  have hz_eq : z = aeval P.x p * ⅟(aeval P.x P.g) ^ n := by
    calc
      z = (z * aeval P.x P.g ^ n) * ⅟(aeval P.x P.g) ^ n := by
        rw [mul_assoc, ← mul_pow, mul_invOf_self, one_pow, mul_one]
      _ = aeval P.x p * ⅟(aeval P.x P.g) ^ n := by rw [hz]
  rw [hz_eq]
  exact (heval p).isAlgebraic.mul (hginv.pow n)

end Algebra

namespace Algebra

variable {R S K L : Type*} [CommRing R] [IsDomain R] [CommRing S]
  [Field K] [Field L] [Algebra R S] [Algebra R K] [IsFractionRing R K]
  [Algebra R L] [Algebra S L] [IsFractionRing S L] [Algebra K L]
  [IsScalarTower R S L] [IsScalarTower R K L]

/-- The fraction field of a standard étale domain is algebraic over the fraction field of its
base domain. -/
theorem IsStandardEtale.isAlgebraic_fractionRing [IsStandardEtale R S] :
    Algebra.IsAlgebraic K L := by
  let _ : Algebra.IsAlgebraic R S := IsStandardEtale.isAlgebraic R S
  have hRL : Algebra.IsAlgebraic R L := by
    constructor
    intro z
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective S z
    have hx : IsAlgebraic R (algebraMap S L x) :=
      (Algebra.IsAlgebraic.isAlgebraic x).algHom (IsScalarTower.toAlgHom R S L)
    have hyalg : IsAlgebraic R (algebraMap S L y) :=
      (Algebra.IsAlgebraic.isAlgebraic y).algHom (IsScalarTower.toAlgHom R S L)
    rw [← hxy, div_eq_mul_inv]
    exact hx.mul hyalg.inv
  exact (IsFractionRing.comap_isAlgebraic_iff (A := R) (K := K) (C := L)).1 hRL

end Algebra
