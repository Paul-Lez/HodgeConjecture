/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.RingHom.Flat
public import Other.Oka.MaximalIdeal
public import Other.Oka.RingTheory.AdicCompletion.Algebra
public import Other.Oka.RingTheory.Localization.AtPrime.Basic
public import Other.Oka.RingTheory.MvPolynomial.Ideal
public import Other.Oka.Weierstrass

/-!
# The local ring of affine space at the origin, and its completion

Write `𝒪_{𝔸^ι, 0} = ℂ[x]_{(x)}` for the polynomials localised at the ideal of variables ; the
local ring of `𝔸^ι_ℂ` at the origin. This file identifies its completion:

```
ComplexAnalytic.polyLocalAdicCompletionEquiv :
  AdicCompletion 𝔪 (ComplexAnalytic.polyLocal ι) ≃ₐ[ℂ] MvPowerSeries ι ℂ
```

and deduces that **the formal power series are flat over it**
(`ComplexAnalytic.flat_polyLocalToMvPowerSeries`), the algebraic half of the flatness statement
that underwrites GAGA.

## Why the algebraic side is not harder than the analytic one

`Other/Oka/Completion.lean` did the same for the *analytic* local ring: the completion of the germ ring
`ℂ{x}` is `ℂ⟦x⟧`. Here the ring is `ℂ[x]_{(x)}` and the answer is the same ring, so the two local
rings have **the same completion** ; which is the whole reason flatness of `ℂ[x]_{(x)} → ℂ{x}` is
a reasonable thing to hope for.

The passage to the limit is `AdicCompletion.equivOfQuotientEquiv` in the mirror tree, so all that
is needed here is a compatible family of isomorphisms

```
ℂ⟦x⟧ ⧸ (x) ^ k  ≃  ℂ[x] ⧸ (x) ^ k  ≃  ℂ[x]_{(x)} ⧸ 𝔪 ^ k
```

The first is truncation, and is Mathlib's `MvPowerSeries.truncTotal` read as a map to the
quotient: surjective because a truncation is a polynomial, injective because a power series all
of whose coefficients in degree `< k` vanish is in `(x) ^ k`. **The second is where one expects
to work and does not**: localising at a maximal ideal does not change the quotients by its
powers, because everything outside the ideal is a unit modulo `p ^ k` already
(`IsLocalization.quotientPowAtPrimeEquiv`, mirror tree, twenty-five lines out of two Mathlib
lemmas).

## Flatness, and what it is not

`ComplexAnalytic.flat_polyLocalToMvPowerSeries` says `ℂ[x]_{(x)} → ℂ⟦x⟧` is flat: the completion
of a Noetherian local ring is flat over it (`AdicCompletion.flat_of_isNoetherian`, with the
Hilbert basis theorem supplying Noetherianness), and that completion is `ℂ⟦x⟧`.

**Everything here is at the origin.** For `p = ker (eval z)` the same statements hold, by the
automorphism of `ℂ[x]` sending `xᵢ` to `xᵢ + zᵢ`, which carries `p` to the ideal of variables;
that translation is **not done here**, and it is not needed here either, because what consumes
these results ; `Other/Oka/Analytification/FlatnessAtAPoint.lean` ; translates the *conclusion* rather
than re-running the argument. It does so with `MvPolynomial.taylorEquiv`; note that a translation
is affine and not linear, so `Other/Oka/ChangeOfCoordinates.lean`, which handles linear changes of
coordinate, is not what does it.

**This is not itself the flatness of `𝒪_{𝔸^ι, 0} → 𝒪_{ℂ^ι, 0}`** ; the map to the *germ* ring,
which is what a GAGA argument consumes. That is one descent step further on and is
`Other/Oka/Analytification/Flatness.lean`: `ℂ{x} → ℂ⟦x⟧` is faithfully flat
(`LocalOkaRing.instFaithfullyFlat`, `Other/Oka/Completion.lean`) and `ℂ[x]_{(x)} → ℂ⟦x⟧` is flat, so
`ℂ[x]_{(x)} → ℂ{x}` is flat by cancellation on the right of the tower. That file also had to
build the algebra map `ℂ[x]_{(x)} → ℂ{x}`, which did not exist when this one was written.

## Main definitions

- `ComplexAnalytic.polyLocal`: the local ring of `𝔸^ι_ℂ` at the origin.
- `ComplexAnalytic.polyLocalToMvPowerSeries`: its embedding in the formal power series, the
  Taylor expansion of a rational function regular at the origin.
- `ComplexAnalytic.polyLocalAdicCompletionEquiv`: **its completion is `MvPowerSeries ι ℂ`.**

## Main results

- `ComplexAnalytic.polyLocalAdicCompletionEquiv_of_algebraMap`: **the isomorphism is the one
  induced by the inclusion of polynomials** ; a polynomial goes to itself.
- `ComplexAnalytic.flat_polyLocalToMvPowerSeries`: **`ℂ⟦x⟧` is flat over `ℂ[x]_{(x)}`.**

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

@[expose] public section

open MvPowerSeries IsLocalRing

universe u

noncomputable section

namespace ComplexAnalytic

variable {ι : Type u} [Finite ι]

/-- The powers of the ideal of variables in the formal power series ring. -/
theorem _root_.MvPowerSeries.mem_span_range_X_pow_iff {k : ℕ} {F : MvPowerSeries ι ℂ} :
    F ∈ (Ideal.span (Set.range (X : ι → MvPowerSeries ι ℂ))) ^ k ↔
      ∀ d : ι →₀ ℕ, d.degree < k → coeff d F = 0 := by
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  letI : LinearOrder ι := LinearOrder.lift' e e.injective
  rw [← MvPowerSeries.maximalIdeal_eq_span_X]
  simp only [Finsupp.degree_eq_sum]
  exact MvPowerSeries.mem_maximalIdeal_pow_iff

/-- Truncation to order `k`, as a `ℂ`-algebra map to `ℂ[x] ⧸ 𝔪₀ ^ k`. -/
def truncPolyHom (k : ℕ) :
    MvPowerSeries ι ℂ →ₐ[ℂ] MvPolynomial ι ℂ ⧸ (MvPolynomial.idealOfVars ι ℂ) ^ k :=
  (MvPowerSeries.truncTotalAlgHom ι ℂ k).restrictScalars ℂ

theorem truncPolyHom_apply (k : ℕ) (F : MvPowerSeries ι ℂ) :
    truncPolyHom k F = Ideal.Quotient.mk _ (MvPowerSeries.truncTotal k F) := rfl

theorem truncPolyHom_surjective (k : ℕ) : Function.Surjective (truncPolyHom (ι := ι) k) := by
  intro y
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨(q : MvPowerSeries ι ℂ), ?_⟩
  rw [truncPolyHom_apply, Ideal.Quotient.eq]
  refine (MvPolynomial.mem_pow_idealOfVars_iff' _ _).mpr fun d hd ↦ ?_
  rw [MvPolynomial.coeff_sub, MvPowerSeries.coeff_truncTotal _ hd, MvPolynomial.coeff_coe,
    sub_self]

theorem ker_truncPolyHom (k : ℕ) :
    RingHom.ker (truncPolyHom (ι := ι) k).toRingHom =
      (Ideal.span (Set.range (X : ι → MvPowerSeries ι ℂ))) ^ k := by
  ext F
  rw [RingHom.mem_ker]
  change truncPolyHom k F = 0 ↔ _
  rw [truncPolyHom_apply, Ideal.Quotient.eq_zero_iff_mem,
    MvPolynomial.mem_pow_idealOfVars_iff', MvPowerSeries.mem_span_range_X_pow_iff]
  exact forall_congr' fun d ↦ forall_congr' fun hd ↦ by
    rw [MvPowerSeries.coeff_truncTotal _ hd]

/-- **The formal power series and the polynomials have the same truncations**:
`ℂ⟦x⟧ ⧸ 𝔪 ^ k ≃ ℂ[x] ⧸ 𝔪₀ ^ k`. -/
def truncQuotEquiv (k : ℕ) :
    (MvPowerSeries ι ℂ ⧸ (Ideal.span (Set.range (X : ι → MvPowerSeries ι ℂ))) ^ k) ≃ₐ[ℂ]
      (MvPolynomial ι ℂ ⧸ (MvPolynomial.idealOfVars ι ℂ) ^ k) :=
  (Ideal.quotientEquivAlgOfEq ℂ (ker_truncPolyHom k).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (truncPolyHom_surjective k))

theorem truncQuotEquiv_mk (k : ℕ) (F : MvPowerSeries ι ℂ) :
    truncQuotEquiv k (Ideal.Quotient.mk _ F) =
      Ideal.Quotient.mk _ (MvPowerSeries.truncTotal k F) := rfl

theorem factorₐ_truncQuotEquiv {j k : ℕ} (hjk : j ≤ k)
    (x : MvPowerSeries ι ℂ ⧸ (Ideal.span (Set.range (X : ι → MvPowerSeries ι ℂ))) ^ k) :
    Ideal.Quotient.factorₐ ℂ (Ideal.pow_le_pow_right hjk) (truncQuotEquiv k x) =
      truncQuotEquiv j (Ideal.Quotient.factorₐ ℂ (Ideal.pow_le_pow_right hjk) x) := by
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [truncQuotEquiv_mk, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factorₐ_apply,
    Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, truncQuotEquiv_mk, Ideal.Quotient.eq]
  exact MvPowerSeries.truncTotal_sub_truncTotal_mem_pow_idealOfVars hjk le_rfl F

section Localization

/-- The local ring of `𝔸^ι_ℂ` at the origin: the polynomials localised at the ideal of
variables. -/
abbrev polyLocal (ι : Type u) : Type u :=
  Localization.AtPrime (MvPolynomial.idealOfVars ι ℂ)

omit [Finite ι] in
/-- The powers of the maximal ideal of the local ring are the extensions of the powers of the
ideal of variables. -/
theorem maximalIdeal_polyLocal_pow (k : ℕ) :
    maximalIdeal (polyLocal ι) ^ k =
      Ideal.map (algebraMap (MvPolynomial ι ℂ) (polyLocal ι))
        ((MvPolynomial.idealOfVars ι ℂ) ^ k) := by
  rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal]

/-- The `k`-th truncation of the local ring at the origin is that of the formal power series. -/
def localQuotEquiv (k : ℕ) :
    (MvPowerSeries ι ℂ ⧸ (Ideal.span (Set.range (X : ι → MvPowerSeries ι ℂ))) ^ k) ≃ₐ[ℂ]
      (polyLocal ι ⧸ maximalIdeal (polyLocal ι) ^ k) :=
  (truncQuotEquiv k).trans
    ((IsLocalization.quotientPowAtPrimeEquiv (MvPolynomial.idealOfVars ι ℂ) k).trans
      (Ideal.quotientEquivAlgOfEq ℂ (maximalIdeal_polyLocal_pow k).symm))

theorem localQuotEquiv_mk (k : ℕ) (F : MvPowerSeries ι ℂ) :
    localQuotEquiv k (Ideal.Quotient.mk _ F) =
      Ideal.Quotient.mk _ (algebraMap (MvPolynomial ι ℂ) (polyLocal ι)
        (MvPowerSeries.truncTotal k F)) := rfl

end Localization

section Assembly

theorem factorₐ_localQuotEquiv {j k : ℕ} (hjk : j ≤ k)
    (x : MvPowerSeries ι ℂ ⧸ (Ideal.span (Set.range (X : ι → MvPowerSeries ι ℂ))) ^ k) :
    Ideal.Quotient.factorₐ ℂ (Ideal.pow_le_pow_right hjk) (localQuotEquiv k x) =
      localQuotEquiv j (Ideal.Quotient.factorₐ ℂ (Ideal.pow_le_pow_right hjk) x) := by
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [localQuotEquiv_mk, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factorₐ_apply,
    Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, localQuotEquiv_mk, Ideal.Quotient.eq,
    ← map_sub, maximalIdeal_polyLocal_pow]
  exact Ideal.mem_map_of_mem _
    (MvPowerSeries.truncTotal_sub_truncTotal_mem_pow_idealOfVars hjk le_rfl F)

/-- The compatibility of `localQuotEquiv` with the reductions, in the form
`AdicCompletion.equivOfQuotientEquiv` consumes. -/
theorem localQuotEquiv_symm_compat {j k : ℕ} (hjk : j ≤ k) :
    (Ideal.Quotient.factorₐ ℂ (Ideal.pow_le_pow_right hjk)).comp
        ((localQuotEquiv (ι := ι) k).symm).toAlgHom =
      ((localQuotEquiv (ι := ι) j).symm).toAlgHom.comp
        (Ideal.Quotient.factorₐ ℂ (Ideal.pow_le_pow_right hjk)) :=
  AdicCompletion.compat_of_symm (IsLocalRing.maximalIdeal (polyLocal ι))
    (Ideal.span (Set.range (X : ι → MvPowerSeries ι ℂ))) (fun n ↦ (localQuotEquiv n).symm)
    (fun hmn x ↦ factorₐ_localQuotEquiv hmn x) hjk

/-- **The completion of the local ring of `𝔸^ι` at the origin is the formal power series
ring.** -/
def polyLocalAdicCompletionEquiv :
    AdicCompletion (maximalIdeal (polyLocal ι)) (polyLocal ι) ≃ₐ[ℂ] MvPowerSeries ι ℂ :=
  AdicCompletion.equivOfQuotientEquiv (maximalIdeal (polyLocal ι))
    (Ideal.span (Set.range (X : ι → MvPowerSeries ι ℂ))) (fun n ↦ (localQuotEquiv n).symm)
    (fun hjk ↦ localQuotEquiv_symm_compat hjk)

theorem mk_polyLocalAdicCompletionEquiv (n : ℕ)
    (x : AdicCompletion (maximalIdeal (polyLocal ι)) (polyLocal ι)) :
    Ideal.Quotient.mk ((Ideal.span (Set.range (X : ι → MvPowerSeries ι ℂ))) ^ n)
        (polyLocalAdicCompletionEquiv x) =
      (localQuotEquiv (ι := ι) n).symm (AdicCompletion.evalₐ _ n x) :=
  AdicCompletion.mk_equivOfQuotientEquiv (maximalIdeal (polyLocal ι))
    (Ideal.span (Set.range (X : ι → MvPowerSeries ι ℂ))) (fun n ↦ (localQuotEquiv n).symm)
    (fun hjk ↦ localQuotEquiv_symm_compat hjk) n x

end Assembly

theorem _root_.MvPowerSeries.ext_of_mk_eq {F G : MvPowerSeries ι ℂ}
    (h : ∀ n : ℕ, Ideal.Quotient.mk
      ((Ideal.span (Set.range (X : ι → MvPowerSeries ι ℂ))) ^ n) F = Ideal.Quotient.mk _ G) :
    F = G := by
  refine MvPowerSeries.ext fun d ↦ ?_
  have hmem := Ideal.Quotient.eq.mp (h (d.degree + 1))
  have := (MvPowerSeries.mem_span_range_X_pow_iff.mp hmem) d (by omega)
  rw [map_sub, sub_eq_zero] at this
  exact this

theorem polyLocalAdicCompletionEquiv_of_algebraMap (q : MvPolynomial ι ℂ) :
    polyLocalAdicCompletionEquiv
        (AdicCompletion.of _ _ (algebraMap (MvPolynomial ι ℂ) (polyLocal ι) q)) =
      (q : MvPowerSeries ι ℂ) := by
  refine MvPowerSeries.ext_of_mk_eq fun n ↦ ?_
  rw [mk_polyLocalAdicCompletionEquiv n, AdicCompletion.evalₐ_of]
  refine (localQuotEquiv (ι := ι) n).symm_apply_eq.2 ?_
  rw [localQuotEquiv_mk, Ideal.Quotient.eq, ← map_sub, maximalIdeal_polyLocal_pow]
  refine Ideal.mem_map_of_mem _ ((MvPolynomial.mem_pow_idealOfVars_iff' _ _).mpr fun d hd ↦ ?_)
  rw [MvPolynomial.coeff_sub, MvPowerSeries.coeff_truncTotal _ hd, MvPolynomial.coeff_coe,
    sub_self]

omit [Finite ι] in
/-- A polynomial not vanishing at the origin is invertible as a formal power series. -/
theorem isUnit_coe_of_notMem_idealOfVars {q : MvPolynomial ι ℂ}
    (hq : q ∉ MvPolynomial.idealOfVars ι ℂ) : IsUnit (q : MvPowerSeries ι ℂ) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  intro hc
  refine hq ?_
  rw [← pow_one (MvPolynomial.idealOfVars ι ℂ), MvPolynomial.mem_pow_idealOfVars_iff']
  intro d hd
  have hd0 : d = 0 := by rw [← Finsupp.degree_eq_zero_iff]; omega
  subst hd0
  rw [← MvPolynomial.coeff_coe, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact hc

/-- **The local ring of `𝔸^ι` at the origin sits inside the formal power series.** -/
def polyLocalToMvPowerSeries : polyLocal ι →ₐ[ℂ] MvPowerSeries ι ℂ :=
  IsLocalization.liftAlgHom (M := (MvPolynomial.idealOfVars ι ℂ).primeCompl)
    (f := (MvPolynomial.coeToMvPowerSeries.algHom ℂ))
    fun y ↦ isUnit_coe_of_notMem_idealOfVars y.2

omit [Finite ι] in
/-- On polynomials, the embedding of the local ring in the formal power series is the
inclusion. -/
theorem polyLocalToMvPowerSeries_algebraMap (q : MvPolynomial ι ℂ) :
    polyLocalToMvPowerSeries (algebraMap (MvPolynomial ι ℂ) (polyLocal ι) q) =
      (q : MvPowerSeries ι ℂ) :=
  IsLocalization.lift_eq _ q

section Flatness

theorem algHom_comp_algebraMap_eq :
    (polyLocalAdicCompletionEquiv (ι := ι)).toAlgHom.toRingHom.comp
        (algebraMap (polyLocal ι)
          (AdicCompletion (maximalIdeal (polyLocal ι)) (polyLocal ι))) =
      (polyLocalToMvPowerSeries (ι := ι)).toRingHom := by
  refine IsLocalization.ringHom_ext (MvPolynomial.idealOfVars ι ℂ).primeCompl ?_
  refine RingHom.ext fun q ↦ ?_
  change polyLocalAdicCompletionEquiv (algebraMap (polyLocal ι) _
    (algebraMap (MvPolynomial ι ℂ) (polyLocal ι) q)) = _
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply,
    polyLocalAdicCompletionEquiv_of_algebraMap]
  exact (polyLocalToMvPowerSeries_algebraMap q).symm

theorem polyLocalAdicCompletionEquiv_algebraMap (a : polyLocal ι) :
    polyLocalAdicCompletionEquiv (algebraMap (polyLocal ι) _ a) = polyLocalToMvPowerSeries a :=
  RingHom.congr_fun algHom_comp_algebraMap_eq a

instance : IsNoetherianRing (polyLocal ι) := by
  haveI : Fintype ι := Fintype.ofFinite ι
  infer_instance

/-- **The formal power series are flat over the local ring of `𝔸^ι` at the origin.** -/
theorem flat_polyLocalToMvPowerSeries :
    (polyLocalToMvPowerSeries (ι := ι)).toRingHom.Flat := by
  rw [← algHom_comp_algebraMap_eq]
  exact RingHom.Flat.comp
    (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian _))
    (RingHom.Flat.of_bijective (polyLocalAdicCompletionEquiv (ι := ι)).bijective)

end Flatness

end ComplexAnalytic

end
