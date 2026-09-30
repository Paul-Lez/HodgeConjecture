/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Localising at a maximal ideal does not change the quotients by its powers

Material for `Mathlib/RingTheory/Localization/AtPrime/Basic.lean`; see `README.md` on the mirror
tree. Upstreaming it adds nothing: that file's transitive closure is **1227** Mathlib modules,
the import above is the target itself, and the cost is **0**, measured with
`python3 scripts/import_cost.py Other/Oka/RingTheory/Localization/AtPrime/Basic.lean`.

**This file was `Other/Oka/RingTheory/Localization/Ideal.lean` until taxis #935**, proposing
`Mathlib/RingTheory/Localization/Ideal.lean` at **113** on a closure of 1114 ; the price of
`Mathlib.RingTheory.Localization.AtPrime.Basic`, which accounted for all 113 on its own, with
`Mathlib.RingTheory.Ideal.Quotient.Nilpotent`'s 91 contained in it as a set. Everything below is
*about* `Localization.AtPrime p`, which is defined in `AtPrime/Basic.lean` and is not in
`Localization/Ideal.lean`'s closure, so the old path had to buy the new one in order to state
anything at all ; while the new path already imports both of the old file's imports.
**A mirror path that cannot state its own declarations is the sharpest case of `README.md`'s
test that the path has to survive the imports its results need.**

For a **maximal** ideal `p` of `R`, the canonical map

```
R ⧸ p ^ k  ⟶  R_p ⧸ (p R_p) ^ k
```

is an isomorphism: everything outside `p` is already invertible modulo `p ^ k`, so there is
nothing left for the localisation to invert. This is the statement that makes the `p`-adic
completion of `R` and the completion of the local ring `R_p` the same thing, and it is the reason
one may compute with either.

Both halves are already in Mathlib and neither is stated in terms of the other:
`Ideal.Quotient.isUnit_mk_pow_of_notMem` says an element outside a maximal ideal is a unit modulo
its `k`-th power, and the instance in `Mathlib/RingTheory/Localization/Ideal.lean` says a quotient
of a localisation is a localisation of the quotient. `IsLocalization.atUnits` ; a localisation at
a submonoid of units is the ring itself ; turns the first into the hypothesis the second needs.

## Main definitions

- `IsLocalization.quotientPowAtPrimeEquiv`: **`R ⧸ p ^ k ≃ R_p ⧸ (p R_p) ^ k`** for `p` maximal,
  as an algebra isomorphism over any base ring `A` under `R`.
-/

@[expose] public section

noncomputable section

namespace IsLocalization

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
  (p : Ideal R) [p.IsMaximal] (k : ℕ)

/-- Modulo `p ^ k`, the elements outside a maximal ideal `p` are units ; so the submonoid the
localisation at `p` inverts is already invertible there. -/
theorem algebraMapSubmonoid_primeCompl_le_isUnit :
    Algebra.algebraMapSubmonoid (R ⧸ p ^ k) p.primeCompl ≤ IsUnit.submonoid (R ⧸ p ^ k) := by
  rintro _ ⟨x, hx, rfl⟩
  exact Ideal.Quotient.isUnit_mk_pow_of_notMem p hx

/-- `R ⧸ p ^ k ≃ R_p ⧸ (p R_p) ^ k`, over `R ⧸ p ^ k` itself. See
`IsLocalization.quotientPowAtPrimeEquiv` for the version over an arbitrary base. -/
def quotientPowAtPrimeEquivSelf :
    (R ⧸ p ^ k) ≃ₐ[R ⧸ p ^ k]
      (Localization.AtPrime p ⧸ Ideal.map (algebraMap R (Localization.AtPrime p)) (p ^ k)) :=
  IsLocalization.atUnits (R ⧸ p ^ k) (Algebra.algebraMapSubmonoid (R ⧸ p ^ k) p.primeCompl)
    (algebraMapSubmonoid_primeCompl_le_isUnit p k)

theorem quotientPowAtPrimeEquivSelf_mk (x : R) :
    quotientPowAtPrimeEquivSelf p k (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime p) x) := rfl

/-- **Localising at a maximal ideal does not change the quotients by its powers**:
`R ⧸ p ^ k ≃ R_p ⧸ (p R_p) ^ k`, as an algebra isomorphism over any base ring under `R`. -/
def quotientPowAtPrimeEquiv :
    (R ⧸ p ^ k) ≃ₐ[A]
      (Localization.AtPrime p ⧸ Ideal.map (algebraMap R (Localization.AtPrime p)) (p ^ k)) where
  __ := (quotientPowAtPrimeEquivSelf p k).toRingEquiv
  commutes' a := by
    change quotientPowAtPrimeEquivSelf p k (Ideal.Quotient.mk _ (algebraMap A R a)) = _
    rw [quotientPowAtPrimeEquivSelf_mk, ← IsScalarTower.algebraMap_apply]
    rfl

@[simp]
theorem quotientPowAtPrimeEquiv_mk (x : R) :
    quotientPowAtPrimeEquiv (A := A) p k (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime p) x) := rfl

end IsLocalization

end
