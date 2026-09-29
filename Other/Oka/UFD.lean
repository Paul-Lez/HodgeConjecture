/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Other.Oka.Noetherian

/-!
# The germ ring is a unique factorisation domain

The ring `LocalOkaRing ι` of germs at the origin of holomorphic functions in finitely many
complex variables is a unique factorisation domain. This is the second classical algebraic
consequence of the Weierstrass theorems, after the Rückert basis theorem of `Other/Oka/Noetherian.lean`,
and it is what makes the local theory of analytic hypersurfaces work.

Being a domain is inherited from `MvPowerSeries ι ℂ`. Factoriality is proved by induction on the
number of variables. Since the germ ring is Noetherian it is a `WfDvdMonoid`, so only
`Irreducible → Prime` has to be established, and the whole argument is the transfer of
factorisations across `LocalOkaRing.fromPolynomial`.

Write `R := LocalOkaRing (Fin n)` and `S := LocalOkaRing (Fin (n + 1))`. Given an irreducible
`f : S`, a linear change of coordinates (`LocalOkaRing.exists_congr_localweierstrass_preparation`)
makes `f` a unit times the germ of a Weierstrass polynomial `w ∈ R[X]`. The two transfers are:

* **units.** A factor `p` of `w` whose germ is a unit is itself a unit. Evaluating coefficients
  at the origin sends `w` to `X ^ d` in `ℂ[X]`, and a divisor of `X ^ d` with nonvanishing
  constant term is a nonzero constant; the leading coefficient of `p` is a unit because `w` is
  monic, so this degree computation survives back in `R[X]`. Hence `w` is irreducible, and
  therefore prime, `R[X]` being a unique factorisation domain by Gauss's lemma.
* **divisibility.** Conversely, the germ of `w` divides the germ of `p` only if `w` divides `p`,
  by the uniqueness half of Weierstrass division. Applied to the remainders of a product, this
  turns primality of `w` in `R[X]` into primality of its germ in `S`.

## Main results

- `LocalOkaRing.instIsDomain`: the germ ring is an integral domain.
- `LocalOkaRing.map_constantCoeff_eq_X_pow`: a Weierstrass polynomial of degree `d` becomes
  `X ^ d` when its coefficients are evaluated at the origin.
- `LocalOkaRing.isUnit_of_isUnit_fromPolynomial`: a factor of a Weierstrass polynomial whose
  germ is a unit is a unit.
- `LocalOkaRing.dvd_of_fromPolynomial_dvd`: divisibility by a Weierstrass polynomial may be
  tested on germs.
- `LocalOkaRing.prime_fromPolynomial`: a prime Weierstrass polynomial has prime germ.
- `LocalOkaRing.uniqueFactorizationMonoid_fin` and
  `LocalOkaRing.instUniqueFactorizationMonoid`: the germ ring is a unique factorisation domain.

## References

- [Hans Grauert and Reinhold Remmert, *Analytische Stellenalgebren*][grauert-remmert1971], §I
- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

@[expose] public section

open Polynomial

namespace LocalOkaRing

variable {ι : Type*} [Finite ι]

/-- The ring of germs at the origin is an integral domain, being a subring of the ring of
formal power series. -/
instance instIsDomain {ι : Type*} : IsDomain (LocalOkaRing ι) := NoZeroDivisors.to_isDomain _

section Weierstrass

variable {n : ℕ}

/-- The constant term of the germ attached to a polynomial is the constant term of its
constant coefficient. -/
lemma constantCoeff_fromPolynomial (p : (LocalOkaRing (Fin n))[X]) :
    constantCoeff (LocalOkaRing.fromPolynomial p) = constantCoeff (p.coeff 0) := by
  have h := MvPowerSeries.coeff_fromPolynomial'
    (p.map (Subring.subtype (localOkaSubring (Fin n)).toSubring)) 0 0
  simp only [Finsupp.mapDomain_zero, Finsupp.single_zero, add_zero] at h
  rw [constantCoeff_apply, LocalOkaRing.coe_fromPolynomial,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  rw [Polynomial.coeff_map, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  rfl

/-- A Weierstrass polynomial is monic. -/
lemma monic_of_isLocalWeierstrass {w : (LocalOkaRing (Fin n))[X]}
    (hw : IsLocalWeierstrassPolynomial
      (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) w)) :
    w.Monic :=
  Polynomial.monic_of_injective Subtype.val_injective hw.monic

/-- Evaluating the coefficients of a Weierstrass polynomial of degree `d` at the origin gives
`X ^ d`. This is the precise sense in which a Weierstrass polynomial is a deformation of a pure
power of the last variable. -/
lemma map_constantCoeff_eq_X_pow {w : (LocalOkaRing (Fin n))[X]}
    (hw : IsLocalWeierstrassPolynomial
      (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) w)) :
    w.map (constantCoeff : LocalOkaRing (Fin n) →+* ℂ) = X ^ w.natDegree := by
  have hm : w.Monic := monic_of_isLocalWeierstrass hw
  have hdeg : w.degree = (w.natDegree : WithBot ℕ) := Polynomial.degree_eq_natDegree hm.ne_zero
  ext i
  rw [Polynomial.coeff_map, Polynomial.coeff_X_pow]
  rcases lt_trichotomy i w.natDegree with hi | rfl | hi
  · have hi' : (i : WithBot ℕ) <
        (Polynomial.map (Subring.subtype (localOkaSubring (Fin n)).toSubring) w).degree := by
      rw [Polynomial.degree_map_eq_of_injective Subtype.val_injective, hdeg]
      exact_mod_cast hi
    have h0 := hw.apply_zero i hi'
    rw [Polynomial.coeff_map] at h0
    rw [if_neg hi.ne, constantCoeff_apply]
    exact h0
  · rw [if_pos rfl, ← Polynomial.leadingCoeff, hm.leadingCoeff, map_one]
  · rw [if_neg hi.ne', Polynomial.coeff_eq_zero_of_natDegree_lt hi, map_zero]

/-- A factor of a Weierstrass polynomial whose germ is a unit is itself a unit.

This is the half of the correspondence between factorisations that needs the Weierstrass
condition: a monic polynomial of positive degree over the germ ring has all its lower
coefficients vanishing at the origin, so its germ has vanishing constant term and cannot be a
unit. -/
lemma isUnit_of_isUnit_fromPolynomial {w p q : (LocalOkaRing (Fin n))[X]}
    (hw : IsLocalWeierstrassPolynomial
      (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) w))
    (hpq : w = p * q) (hu : IsUnit (LocalOkaRing.fromPolynomial p)) : IsUnit p := by
  have hm : w.Monic := monic_of_isLocalWeierstrass hw
  -- the leading coefficient of `p` divides that of `w`, hence is a unit
  have hlc : p.leadingCoeff * q.leadingCoeff = 1 := by
    rw [← Polynomial.leadingCoeff_mul, ← hpq]; exact hm
  have hlcu : IsUnit p.leadingCoeff := IsUnit.of_mul_eq_one _ hlc
  have hφlc : (constantCoeff : LocalOkaRing (Fin n) →+* ℂ) p.leadingCoeff ≠ 0 :=
    (hlcu.map (constantCoeff : LocalOkaRing (Fin n) →+* ℂ)).ne_zero
  -- so evaluating the coefficients at the origin does not drop the degree
  have hdegmap : (p.map (constantCoeff : LocalOkaRing (Fin n) →+* ℂ)).natDegree = p.natDegree :=
    Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hφlc
  -- the image of `p` divides `X ^ d` in `ℂ[X]`
  have hdvd : p.map (constantCoeff : LocalOkaRing (Fin n) →+* ℂ) ∣ X ^ w.natDegree := by
    rw [← map_constantCoeff_eq_X_pow hw, hpq, Polynomial.map_mul]
    exact Dvd.intro _ rfl
  -- but its constant coefficient does not vanish, since the germ of `p` is a unit
  have hc0 : (p.map (constantCoeff : LocalOkaRing (Fin n) →+* ℂ)).coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_map, ← constantCoeff_fromPolynomial]
    exact isUnit_iff.mp hu
  -- hence the image of `p` is a nonzero constant, and `p` has degree zero
  obtain ⟨i, -, hassoc⟩ := (dvd_prime_pow Polynomial.prime_X w.natDegree).mp hdvd
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · have hunit : IsUnit (p.map (constantCoeff : LocalOkaRing (Fin n) →+* ℂ)) :=
      associated_one_iff_isUnit.mp (by simpa using hassoc)
    have hd0 : p.natDegree = 0 := by
      rw [← hdegmap]; exact Polynomial.natDegree_eq_zero_of_isUnit hunit
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd0]
    refine Polynomial.isUnit_C.mpr ?_
    rwa [Polynomial.leadingCoeff, hd0] at hlcu
  · exact absurd (Polynomial.X_dvd_iff.mp
      ((dvd_pow_self X hipos.ne').trans hassoc.symm.dvd)) hc0

/-- Divisibility by a Weierstrass polynomial may be tested on germs: if the germ of `w` divides
the germ of `p`, then `w` divides `p` as a polynomial.

This is the uniqueness half of Weierstrass division: the quotient and remainder of `p` by `w`
computed in the germ ring must be the polynomial ones. -/
lemma dvd_of_fromPolynomial_dvd {w p : (LocalOkaRing (Fin n))[X]}
    (hw : IsLocalWeierstrassPolynomial
      (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) w))
    (h : LocalOkaRing.fromPolynomial w ∣ LocalOkaRing.fromPolynomial p) : w ∣ p := by
  have hm : w.Monic := monic_of_isLocalWeierstrass hw
  obtain ⟨a, ha⟩ := h
  have hb : (0 : (LocalOkaRing (Fin n))[X]).degree < w.degree := by
    rw [Polynomial.degree_zero, bot_lt_iff_ne_bot, ne_eq, Polynomial.degree_eq_bot]
    exact hm.ne_zero
  have heq : LocalOkaRing.fromPolynomial p =
      a * LocalOkaRing.fromPolynomial w + LocalOkaRing.fromPolynomial 0 := by
    rw [map_zero, add_zero, ha, mul_comm]
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hm).mp
    (fromPolynomial_eq_divByMonic hw p hb heq).2.symm

/-- A Weierstrass polynomial which is prime in `R[X]` has prime germ.

Weierstrass division reduces a divisibility question in the germ ring to one between the
remainders, which are polynomials of bounded degree, and `dvd_of_fromPolynomial_dvd` transports
the answer back. -/
lemma prime_fromPolynomial {w : (LocalOkaRing (Fin n))[X]}
    (hw : IsLocalWeierstrassPolynomial
      (Polynomial.map (Subring.subtype (localOkaSubring _).toSubring) w))
    (hp : Prime w) : Prime (LocalOkaRing.fromPolynomial w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    exact hp.1 (LocalOkaRing.fromPolynomial_injective (by rw [hz, map_zero]))
  · intro hu
    exact hp.2.1 (isUnit_of_isUnit_fromPolynomial hw (mul_one w).symm hu)
  · intro g h hdvd
    obtain ⟨a, bg, -, hgeq⟩ := localweierstrass_division w hw g
    obtain ⟨a', bh, -, hheq⟩ := localweierstrass_division w hw h
    -- the germ of `w` divides the product of the two remainders
    have hprod : LocalOkaRing.fromPolynomial w ∣ LocalOkaRing.fromPolynomial (bg * bh) := by
      have hrw : LocalOkaRing.fromPolynomial (bg * bh) = g * h -
          (a * a' * LocalOkaRing.fromPolynomial w + a * LocalOkaRing.fromPolynomial bh +
            a' * LocalOkaRing.fromPolynomial bg) * LocalOkaRing.fromPolynomial w := by
        rw [map_mul, hgeq, hheq]
        ring
      rw [hrw]
      exact dvd_sub hdvd (dvd_mul_left _ _)
    rcases hp.2.2 bg bh (dvd_of_fromPolynomial_dvd hw hprod) with hbg | hbh
    · exact Or.inl (hgeq ▸ dvd_add (dvd_mul_left _ _)
        (map_dvd LocalOkaRing.fromPolynomial hbg))
    · exact Or.inr (hheq ▸ dvd_add (dvd_mul_left _ _)
        (map_dvd LocalOkaRing.fromPolynomial hbh))

end Weierstrass

/-! ### Factoriality -/

section Factorial

variable {n : ℕ}

/-- The inductive step: if the germs in `n` variables form a unique factorisation domain, then
every irreducible germ in `n + 1` variables is prime.

After a linear change of coordinates the germ is, up to a unit, the germ of a Weierstrass
polynomial `w`; irreducibility transfers to `w` by `isUnit_of_isUnit_fromPolynomial`, `w` is
then prime in `R[X]` because `R[X]` is a unique factorisation domain by Gauss's lemma, and
primality transfers back by `prime_fromPolynomial`. -/
theorem prime_of_irreducible_succ [UniqueFactorizationMonoid (LocalOkaRing (Fin n))]
    {f : LocalOkaRing (Fin (n + 1))} (hf : Irreducible f) : Prime f := by
  obtain ⟨φ, u, hu, w, hw, hfeq⟩ := exists_congr_localweierstrass_preparation hf.ne_zero
  set E : LocalOkaRing (Fin (n + 1)) ≃* LocalOkaRing (Fin (n + 1)) :=
    (LocalOkaRing.congr φ).toRingEquiv.toMulEquiv
  have hFirr : Irreducible (LocalOkaRing.congr φ f) := (MulEquiv.irreducible_iff E).mpr hf
  -- the germ of `w` is associated to the transported germ, hence irreducible
  have hass : Associated (LocalOkaRing.fromPolynomial w) (LocalOkaRing.congr φ f) :=
    ⟨hu.unit, by rw [IsUnit.unit_spec]; exact hfeq.symm⟩
  have hWirr : Irreducible (LocalOkaRing.fromPolynomial w) := hass.symm.irreducible hFirr
  -- so `w` is irreducible, hence prime, in the polynomial ring
  have hwirr : Irreducible w := by
    refine ⟨fun hu' ↦ hWirr.not_isUnit (hu'.map LocalOkaRing.fromPolynomial), fun p q hpq ↦ ?_⟩
    rcases hWirr.isUnit_or_isUnit (by rw [hpq, map_mul]) with h | h
    · exact Or.inl (isUnit_of_isUnit_fromPolynomial hw hpq h)
    · exact Or.inr (isUnit_of_isUnit_fromPolynomial hw (by rw [hpq]; ring) h)
  have hwp : Prime w := UniqueFactorizationMonoid.irreducible_iff_prime.mp hwirr
  -- and primality transports back through the germ and the change of coordinates
  exact (MulEquiv.prime_iff E).mp (hass.prime (prime_fromPolynomial hw hwp))

end Factorial

/-- **The Rückert factorisation theorem** for the standard variables: the ring of germs at the
origin of holomorphic functions in `n` complex variables is a unique factorisation domain.

See `LocalOkaRing.instUniqueFactorizationMonoid` for the version with an arbitrary finite set of
variables, which is the one registered as an instance. -/
theorem uniqueFactorizationMonoid_fin :
    ∀ n : ℕ, UniqueFactorizationMonoid (LocalOkaRing (Fin n))
  | 0 =>
    { irreducible_iff_prime := fun {a} ↦
        ⟨fun ha ↦ absurd (isUnit_iff_ne_zero.mpr ha.ne_zero) ha.not_isUnit, Prime.irreducible⟩ }
  | (n + 1) => by
    haveI := uniqueFactorizationMonoid_fin n
    exact { irreducible_iff_prime := fun {_} ↦
      ⟨prime_of_irreducible_succ, Prime.irreducible⟩ }

/-- **The Rückert factorisation theorem**: the ring of germs at the origin of holomorphic
functions in finitely many complex variables is a unique factorisation domain. -/
instance instUniqueFactorizationMonoid : UniqueFactorizationMonoid (LocalOkaRing ι) := by
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  haveI := uniqueFactorizationMonoid_fin n
  refine { irreducible_iff_prime := fun {a} ↦ ?_ }
  rw [← MulEquiv.irreducible_iff (congrEquiv e).toRingEquiv.toMulEquiv,
    ← MulEquiv.prime_iff (congrEquiv e).toRingEquiv.toMulEquiv]
  exact UniqueFactorizationMonoid.irreducible_iff_prime

end LocalOkaRing

end
