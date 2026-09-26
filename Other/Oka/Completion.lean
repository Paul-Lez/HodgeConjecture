/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Other.Oka.MaximalIdeal
public import Other.Oka.Noetherian
public import Other.Oka.RingTheory.AdicCompletion.Algebra
public import Other.Oka.Weierstrass

/-!
# The completion of the germ ring is the formal power series ring

The germ ring `LocalOkaRing ι` of convergent power series sits inside `MvPowerSeries ι ℂ` by
construction. This file shows that the larger ring is exactly its **completion** at the maximal
ideal `𝔪` of germs vanishing at the origin:

```
LocalOkaRing.adicCompletionEquiv : MvPowerSeries ι ℂ ≃ₐ[ℂ] AdicCompletion 𝔪 (LocalOkaRing ι)
```

and that the inclusion of the germs is the canonical map into the completion
(`LocalOkaRing.toAdicCompletion_coe`) ; without which the isomorphism would be a statement about
two abstract `ℂ`-algebras rather than about convergent and formal power series.

Since the completion of a Noetherian local ring is faithfully flat over it, the corollary is that

```
LocalOkaRing.instFaithfullyFlat : Module.FaithfullyFlat (LocalOkaRing ι) (MvPowerSeries ι ℂ)
```

**formal power series are faithfully flat over convergent ones** ; the classical statement that
makes formal computations with germs conclusive. `LocalOkaRing.coe_mem_map_iff` is one reading of
it: a germ that lies **formally** in an ideal of germs ; that is, in the ideal it generates in
`ℂ⟦x⟧` ; lies in that ideal of germs already.

## The analytic content is elsewhere, and this file is the limit of it

Nothing here is analysis. The one analytic fact is that the germ ring and the formal power series
have the **same truncations**, `LocalOkaRing.truncQuotientEquiv` in `Other/Oka/MaximalIdeal.lean`:
surjectivity because a truncated power series is a polynomial, hence convergent, and injectivity
because a germ vanishing to order `k` is a formal power series vanishing to order `k`. That is
"convergent series are dense in formal ones", and it is the whole of the mathematics. What this
file adds is the passage to the limit, which is bookkeeping over Mathlib's
`AdicCompletion.liftAlgHom` and the completeness of `MvPowerSeries` already registered in
`Other/Oka/Weierstrass.lean`.

The two directions of the bijection use the two halves of that completeness. Injectivity is
separation ; a formal power series lying in every `𝔪̂ ^ k` is zero, which is
`MvPowerSeries.mem_maximalIdeal_pow_iff` coefficientwise. Surjectivity is precompleteness: an
element of the completion is a compatible family of truncations, which lifts to a Cauchy sequence
of formal power series, which converges.

## What is *not* here

**This is not the flatness of `𝒪_{𝔸^ι, z} → 𝒪_{ℂ^ι, z}`**, the analytic input to GAGA (taxis
#600). Two things stand between this file and that statement, neither of them attempted here:

* that the completion of `Localization.AtPrime (MvPolynomial ι ℂ) (ker (eval z))` at its maximal
  ideal is again `MvPowerSeries ι ℂ` ; Mathlib has
  `MvPowerSeries.toAdicCompletionAlgEquiv` for the polynomial ring at the ideal of variables, and
  what is missing is the comparison with the localisation;
* the local criterion ; that a local homomorphism of Noetherian local rings is flat as soon as
  the induced map of completions is. This was searched for in Mathlib and not found; that is a
  negative claim about Mathlib and should be re-checked rather than believed.

**That statement is missing from this file and from this route, and not from the repository.**
`ComplexAnalytic.faithfullyFlat_stalkMap_complexSpaceToSpec` in
`Other/Oka/Analytification/FlatnessAtAPoint.lean` is exactly it, at every point of `ℂ^ι` and in the
spelling a GAGA argument consumes, proved through the germ ring rather than through completions.
So the two items above are gaps in *this* route and not obstacles to the theorem, and nothing
below discharges either of them.

This paragraph used to say instead that `Other/Oka/Analytification/AffineSpace.lean` *names flatness as
an outstanding item and still should*. That file now records it as no longer missing, so the
sentence described a stance that had moved. **A cross-reference that quotes another file's stance
goes stale every time that stance moves; one that names a declaration does not** ; which is the
same rule, read for stances rather than for numbers, as the one that a figure in a docstring
should either carry the command that reproduces it or not be there.

## Main definitions

- `LocalOkaRing.truncHom`: truncation of a formal power series to order `k`, landing in
  `𝒪 ⧸ 𝔪 ^ k`.
- `LocalOkaRing.toAdicCompletion`: a formal power series read as an element of the `𝔪`-adic
  completion of the germ ring, namely the compatible family of its truncations.
- `LocalOkaRing.adicCompletionEquiv`: **the `𝔪`-adic completion of the germ ring is the formal
  power series ring.**

## Main results

- `LocalOkaRing.toAdicCompletion_coe`: **the isomorphism is the one induced by the inclusion** ;
  a convergent power series goes to its own image in the completion.
- `LocalOkaRing.instFaithfullyFlat`: **`MvPowerSeries ι ℂ` is faithfully flat over
  `LocalOkaRing ι`.**
- `LocalOkaRing.coe_mem_map_iff`: a germ lies in an ideal of germs as soon as it lies in the
  ideal it generates formally.

## References

- [Hans Grauert and Reinhold Remmert, *Analytische Stellenalgebren*][grauert-remmert1971], §I
-/

@[expose] public section

open IsLocalRing MvPowerSeries

universe u

noncomputable section

namespace LocalOkaRing

variable {ι : Type u} [Fintype ι]

/-! ### The truncations of a formal power series as an element of the completion -/

/-- The isomorphism `𝒪 ⧸ 𝔪 ^ k ≃ ℂ⟦X⟧ ⧸ 𝔪̂ ^ k` of `LocalOkaRing.truncQuotientEquiv` is the one
induced by the inclusion of the germs into the formal power series. -/
theorem truncQuotientEquiv_mk (k : ℕ) (P : LocalOkaRing ι) :
    truncQuotientEquiv k (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (P : MvPowerSeries ι ℂ) := rfl

/-- `LocalOkaRing.truncQuotientEquiv` is natural in `k`: it commutes with the reductions
`_ ⧸ 𝔪 ^ k → _ ⧸ 𝔪 ^ j`. Both sides send the class of a germ to the class of the same germ, so
this is `LocalOkaRing.truncQuotientEquiv_mk` and surjectivity of `Ideal.Quotient.mk`. -/
theorem factorPow_truncQuotientEquiv {j k : ℕ} (hjk : j ≤ k)
    (x : LocalOkaRing ι ⧸ maximalIdeal (LocalOkaRing ι) ^ k) :
    truncQuotientEquiv j (Ideal.Quotient.factorPow _ hjk x) =
      Ideal.Quotient.factorPow _ hjk (truncQuotientEquiv k x) := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [truncQuotientEquiv_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
    truncQuotientEquiv_mk]

/-- **Truncation of a formal power series to order `k`**, as a `ℂ`-algebra map to `𝒪 ⧸ 𝔪 ^ k`.

This is the reduction `ℂ⟦X⟧ → ℂ⟦X⟧ ⧸ 𝔪̂ ^ k` read through `LocalOkaRing.truncQuotientEquiv`; the
germ it produces is the truncated polynomial, and `LocalOkaRing.trunc` is a representative of
it. -/
def truncHom (k : ℕ) :
    MvPowerSeries ι ℂ →ₐ[ℂ] LocalOkaRing ι ⧸ maximalIdeal (LocalOkaRing ι) ^ k :=
  (truncQuotientEquiv (ι := ι) k).symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ _)

theorem truncHom_apply (k : ℕ) (F : MvPowerSeries ι ℂ) :
    truncHom k F = (truncQuotientEquiv (ι := ι) k).symm (Ideal.Quotient.mk _ F) := rfl

/-- The truncations of a formal power series are a compatible family, which is what makes
`LocalOkaRing.toAdicCompletion` well defined. -/
theorem factorₐ_comp_truncHom {j k : ℕ} (hjk : j ≤ k) :
    (Ideal.Quotient.factorₐ ℂ (Ideal.pow_le_pow_right hjk)).comp (truncHom (ι := ι) k) =
      truncHom j := by
  ext F
  refine (truncQuotientEquiv (ι := ι) j).injective ?_
  rw [AlgHom.comp_apply, Ideal.Quotient.factorₐ_apply, truncHom_apply, truncHom_apply,
    factorPow_truncQuotientEquiv hjk, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
    Ideal.Quotient.factor_mk]

/-- **A formal power series as an element of the `𝔪`-adic completion of the germ ring**: the
compatible family of its truncations. -/
def toAdicCompletion :
    MvPowerSeries ι ℂ →ₐ[ℂ] AdicCompletion (maximalIdeal (LocalOkaRing ι)) (LocalOkaRing ι) :=
  AdicCompletion.liftAlgHom (maximalIdeal (LocalOkaRing ι)) truncHom
    fun hle ↦ factorₐ_comp_truncHom hle

@[simp]
theorem evalₐ_toAdicCompletion (k : ℕ) (F : MvPowerSeries ι ℂ) :
    AdicCompletion.evalₐ (maximalIdeal (LocalOkaRing ι)) k (toAdicCompletion F) =
      (truncQuotientEquiv k).symm (Ideal.Quotient.mk _ F) :=
  AdicCompletion.evalₐ_liftAlgHom (maximalIdeal (LocalOkaRing ι)) truncHom
    (fun hle ↦ factorₐ_comp_truncHom hle) k F

/-! ### The completion of the germ ring is the formal power series ring -/

/-- Two formal power series with the same truncations to every order are equal: this is
separation of the `𝔪̂`-adic topology on `ℂ⟦X⟧`, in the concrete form
`MvPowerSeries.mem_maximalIdeal_pow_iff`. -/
theorem toAdicCompletion_injective :
    Function.Injective (toAdicCompletion (ι := ι)) := by
  intro F G hFG
  have key : ∀ k : ℕ, (Ideal.Quotient.mk (maximalIdeal (MvPowerSeries ι ℂ) ^ k)) F =
      Ideal.Quotient.mk _ G := fun k ↦ by
    refine (truncQuotientEquiv (ι := ι) k).symm.injective ?_
    rw [← evalₐ_toAdicCompletion, ← evalₐ_toAdicCompletion, hFG]
  refine MvPowerSeries.ext fun d ↦ ?_
  have hmem : F - G ∈ maximalIdeal (MvPowerSeries ι ℂ) ^ ((∑ i, d i) + 1) :=
    Ideal.Quotient.eq.mp (key _)
  have h := (MvPowerSeries.mem_maximalIdeal_pow_iff.mp hmem) d (by omega)
  rw [map_sub, sub_eq_zero] at h
  exact h

/-- Every element of the completion of the germ ring comes from a formal power series.

An element of the completion is a compatible family of classes in `𝒪 ⧸ 𝔪 ^ k`; reading them
through `LocalOkaRing.truncQuotientEquiv` and choosing representatives gives a Cauchy sequence of
formal power series, and `ℂ⟦X⟧` is `𝔪̂`-adically complete
(`instIsAdicCompleteMaximalIdealMvPowerSeries`), so it converges. -/
theorem toAdicCompletion_surjective :
    Function.Surjective (toAdicCompletion (ι := ι)) := by
  intro x
  have hpow : ∀ k : ℕ,
      (maximalIdeal (MvPowerSeries ι ℂ) ^ k • ⊤ : Ideal (MvPowerSeries ι ℂ)) =
        maximalIdeal (MvPowerSeries ι ℂ) ^ k := fun k ↦ by ext y; simp
  choose F hF using fun k : ℕ ↦ Ideal.Quotient.mk_surjective
    (I := maximalIdeal (MvPowerSeries ι ℂ) ^ k)
    (truncQuotientEquiv k (AdicCompletion.evalₐ _ k x))
  have hcompat : ∀ {j k : ℕ}, j ≤ k →
      F j ≡ F k [SMOD (maximalIdeal (MvPowerSeries ι ℂ) ^ j • ⊤ : Ideal (MvPowerSeries ι ℂ))] := by
    intro j k hjk
    rw [SModEq.sub_mem, hpow, ← Ideal.Quotient.eq, hF j,
      ← Ideal.Quotient.factor_mk (Ideal.pow_le_pow_right hjk) (F k), hF k,
      ← factorPow_truncQuotientEquiv hjk, AdicCompletion.factorPow_evalₐ _ hjk]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := maximalIdeal (MvPowerSeries ι ℂ)) inferInstance
    hcompat
  refine ⟨L, AdicCompletion.ext_evalₐ fun k ↦ ?_⟩
  rw [evalₐ_toAdicCompletion]
  refine (truncQuotientEquiv (ι := ι) k).injective ?_
  rw [AlgEquiv.apply_symm_apply, ← hF k]
  have h := hL k
  rw [SModEq.sub_mem, hpow, ← Ideal.Quotient.eq] at h
  exact h.symm

/-- **The `𝔪`-adic completion of the germ ring is the ring of formal power series.**

Read the other way round ; `adicCompletionEquiv.symm` ; this says that the completion of the
convergent power series in `ι` variables is the formal ones, which is the statement the
literature makes.

It is the isomorphism *induced by the inclusion*: see `LocalOkaRing.toAdicCompletion_coe`,
without which this would be a statement about two abstract `ℂ`-algebras. -/
def adicCompletionEquiv :
    MvPowerSeries ι ℂ ≃ₐ[ℂ] AdicCompletion (maximalIdeal (LocalOkaRing ι)) (LocalOkaRing ι) :=
  AlgEquiv.ofBijective toAdicCompletion ⟨toAdicCompletion_injective, toAdicCompletion_surjective⟩

@[simp]
theorem adicCompletionEquiv_apply (F : MvPowerSeries ι ℂ) :
    adicCompletionEquiv F = toAdicCompletion F := rfl

@[simp]
theorem symm_adicCompletionEquiv_toAdicCompletion (F : MvPowerSeries ι ℂ) :
    (adicCompletionEquiv (ι := ι)).symm (toAdicCompletion F) = F :=
  (adicCompletionEquiv (ι := ι)).symm_apply_apply F

@[simp]
theorem toAdicCompletion_symm_adicCompletionEquiv
    (x : AdicCompletion (maximalIdeal (LocalOkaRing ι)) (LocalOkaRing ι)) :
    toAdicCompletion ((adicCompletionEquiv (ι := ι)).symm x) = x :=
  (adicCompletionEquiv (ι := ι)).apply_symm_apply x

/-- **A convergent power series goes to its own image in the completion.**

This is what makes `LocalOkaRing.adicCompletionEquiv` a statement about the inclusion of the
germs into the formal power series rather than about two abstract `ℂ`-algebras that happen to be
isomorphic, and it is what promotes that isomorphism to one of `LocalOkaRing ι`-modules in
`LocalOkaRing.adicCompletionLinearEquiv`. -/
@[simp]
theorem toAdicCompletion_coe (P : LocalOkaRing ι) :
    toAdicCompletion (P : MvPowerSeries ι ℂ) =
      AdicCompletion.of (maximalIdeal (LocalOkaRing ι)) (LocalOkaRing ι) P :=
  AdicCompletion.ext_evalₐ fun k ↦ by
    rw [evalₐ_toAdicCompletion, AdicCompletion.evalₐ_of]
    exact (truncQuotientEquiv (ι := ι) k).symm_apply_eq.2 (truncQuotientEquiv_mk k P).symm

theorem symm_adicCompletionEquiv_of (P : LocalOkaRing ι) :
    (adicCompletionEquiv (ι := ι)).symm
        (AdicCompletion.of (maximalIdeal (LocalOkaRing ι)) (LocalOkaRing ι) P) =
      (P : MvPowerSeries ι ℂ) :=
  (adicCompletionEquiv (ι := ι)).symm_apply_eq.2 (toAdicCompletion_coe P).symm

/-! ### Faithful flatness -/

theorem toAdicCompletion_smul (P : LocalOkaRing ι) (F : MvPowerSeries ι ℂ) :
    toAdicCompletion (P • F) = P • toAdicCompletion F := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, AdicCompletion.algebraMap_apply,
    Algebra.algebraMap_self_apply]
  exact congrArg (· * toAdicCompletion F) (toAdicCompletion_coe P)

/-- `LocalOkaRing.adicCompletionEquiv` as an isomorphism of `LocalOkaRing ι`-modules, which is
what transports flatness. It is `LocalOkaRing.toAdicCompletion_coe` that makes it one. -/
def adicCompletionLinearEquiv :
    MvPowerSeries ι ℂ ≃ₗ[LocalOkaRing ι]
      AdicCompletion (maximalIdeal (LocalOkaRing ι)) (LocalOkaRing ι) where
  __ := adicCompletionEquiv (ι := ι)
  map_smul' := toAdicCompletion_smul

/-- **The formal power series are faithfully flat over the convergent ones.**

The germ ring is Noetherian (the Rückert basis theorem, `LocalOkaRing.instIsNoetherianRing`) and
local, so its completion is faithfully flat over it ; `AdicCompletion.flat_of_isNoetherian`
upgraded by `Module.FaithfullyFlat.of_flat_of_isLocalHom` ; and that completion is
`MvPowerSeries ι ℂ`.

So the Rückert basis theorem, proved here for entirely different reasons, is what makes this
free. -/
instance instFaithfullyFlat {ι : Type u} [Finite ι] :
    Module.FaithfullyFlat (LocalOkaRing ι) (MvPowerSeries ι ℂ) := by
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Module.FaithfullyFlat (LocalOkaRing ι)
      (AdicCompletion (maximalIdeal (LocalOkaRing ι)) (LocalOkaRing ι)) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Module.FaithfullyFlat.of_linearEquiv _ _ adicCompletionLinearEquiv

/-- **A germ that lies *formally* in an ideal of germs lies in it already**: membership of the
ideal generated by germs in `ℂ⟦X⟧` is no weaker than membership in `𝒪`. The direction with
content is the forward one; the converse is `Ideal.mem_map_of_mem`.

This is faithful flatness read as `Ideal.comap_map_eq_self_of_faithfullyFlat`, and it is the
concrete form in which the flatness of `ℂ⟦X⟧` over `ℂ{X}` is usually used. -/
theorem coe_mem_map_iff {ι : Type u} [Finite ι] (I : Ideal (LocalOkaRing ι))
    {P : LocalOkaRing ι} :
    (P : MvPowerSeries ι ℂ) ∈ I.map (algebraMap (LocalOkaRing ι) (MvPowerSeries ι ℂ)) ↔ P ∈ I := by
  refine ⟨fun hP ↦ ?_, fun hP ↦ Ideal.mem_map_of_mem _ hP⟩
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := MvPowerSeries ι ℂ) I]
  exact hP

end LocalOkaRing

end
