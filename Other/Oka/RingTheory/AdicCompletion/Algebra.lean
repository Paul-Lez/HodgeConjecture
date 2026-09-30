/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.RingHom

/-!
# The projections of an adic completion are compatible with each other

Material for `Mathlib/RingTheory/AdicCompletion/Algebra.lean`; see `README.md` on the mirror
tree. Upstreaming it adds `Mathlib.RingTheory.AdicCompletion.RingHom` to a target whose closure is
**1305** Mathlib modules ; **one** new one, measured with `scripts/import_cost.py`.

`AdicCompletion.evalₐ I n : AdicCompletion I R →ₐ[R] R ⧸ I ^ n` is the `n`-th projection of the
`I`-adic completion of a ring. That these projections are compatible ; that `R ⧸ I ^ k → R ⧸ I ^ j`
carries the `k`-th to the `j`-th ; is the defining property of the completion, and Mathlib states
it for the module-level projection `AdicCompletion.eval`
(`AdicCompletion.transitionMap_comp_eval_apply`) but not for `evalₐ`, whose target is the honest
ideal quotient `R ⧸ I ^ n` rather than `R ⧸ (I ^ n • ⊤)`.

Everything needed is already there ; `AdicCompletion.mk_surjective`, `AdicCompletion.evalₐ_mk`
and `AdicCompletion.Ideal.mk_eq_mk` ; so this is three lines; it is here because a consumer that
has to rediscover it pays more than that.

## A ring with the right quotients *is* the completion

`AdicCompletion.equivOfQuotientEquiv` is the recognition principle this file exists for: a ring
`S` which is `J`-adically complete and whose quotients `S ⧸ J ^ n` are compatibly isomorphic to
the `R ⧸ I ^ n` **is** the `I`-adic completion of `R`. Both directions are Mathlib lifts ;
`AdicCompletion.liftAlgHom` into a completion, `IsAdicComplete.liftAlgHom` into a complete ring ;
and the two composites are identified by the extensionality principles that come with them, so
nothing here is more than assembly. It is stated because the alternative is that every consumer
assembles it again, which has already happened once in this repository (`Other/Oka/Completion.lean`,
where the target is `MvPowerSeries ι ℂ` and the completeness is Mathlib's).

## Main results

- `AdicCompletion.factorPow_evalₐ`: the projections of `AdicCompletion I R` to the quotients
  `R ⧸ I ^ n` form a compatible family.
- `AdicCompletion.equivOfQuotientEquiv`: **a `J`-adically complete ring with compatibly
  isomorphic quotients is the `I`-adic completion**, with `AdicCompletion.mk_equivOfQuotientEquiv`
  computing it and `AdicCompletion.compat_of_symm` supplying the compatibility hypothesis from
  the inverse family.
-/

@[expose] public section

noncomputable section

namespace AdicCompletion

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- **The projections of an adic completion to `R ⧸ I ^ n` are a compatible family**: reducing
the `k`-th projection modulo `I ^ j` gives the `j`-th, for `j ≤ k`.

This is `AdicCompletion.transitionMap_comp_eval_apply` for `AdicCompletion.evalₐ` in place of
`AdicCompletion.eval`, i.e. with the quotients taken as ideal quotients rather than as
`R ⧸ (I ^ n • ⊤)`. -/
theorem factorPow_evalₐ {j k : ℕ} (hjk : j ≤ k) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I hjk (AdicCompletion.evalₐ I k x) = AdicCompletion.evalₐ I j x := by
  obtain ⟨r, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk,
    AdicCompletion.Ideal.mk_eq_mk I hjk]

section QuotientEquiv

variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
  (I : Ideal R) (J : Ideal S) [IsAdicComplete J S]
  (e : ∀ n : ℕ, (R ⧸ I ^ n) ≃ₐ[A] (S ⧸ J ^ n))
  (he : ∀ {m n : ℕ} (h : m ≤ n),
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right h)).comp (e n).toAlgHom =
      (e m).toAlgHom.comp (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right h)))

omit [IsAdicComplete J S] in
include he in
/-- The family `e n ∘ evalₐ I n` out of the completion is compatible with the reductions: the
hypothesis `AdicCompletion.toComplete` needs. -/
theorem compat_fwd {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right h)).comp
        ((e n).toAlgHom.comp ((AdicCompletion.evalₐ I n).restrictScalars A)) =
      (e m).toAlgHom.comp ((AdicCompletion.evalₐ I m).restrictScalars A) := by
  ext x
  have h1 := congrArg (fun f : (R ⧸ I ^ n) →ₐ[A] (S ⧸ J ^ m) ↦ f (AdicCompletion.evalₐ I n x))
    (he h)
  simpa [AdicCompletion.factorPow_evalₐ I h x] using h1

omit [IsAdicComplete J S] in
include he in
/-- The family `(e n).symm ∘ mk` out of `S` is compatible with the reductions: the hypothesis
`AdicCompletion.ofComplete` needs. -/
theorem compat_bwd {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right h)).comp
        ((e n).symm.toAlgHom.comp (Ideal.Quotient.mkₐ A (J ^ n))) =
      (e m).symm.toAlgHom.comp (Ideal.Quotient.mkₐ A (J ^ m)) := by
  ext x
  refine (e m).injective ?_
  have h1 := congrArg (fun f : (R ⧸ I ^ n) →ₐ[A] (S ⧸ J ^ m) ↦
    f ((e n).symm (Ideal.Quotient.mk (J ^ n) x))) (he h)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply,
    Ideal.Quotient.mkₐ_eq_mk] at h1 ⊢
  rw [← h1, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk]

/-- The map from the `I`-adic completion of `R` to `S`, read off level by level through the
isomorphisms `e`. It is an isomorphism: see `AdicCompletion.equivOfQuotientEquiv`. -/
def toComplete : AdicCompletion I R →ₐ[A] S :=
  IsAdicComplete.liftAlgHom J
    (fun n ↦ (e n).toAlgHom.comp ((AdicCompletion.evalₐ I n).restrictScalars A))
    (fun h ↦ compat_fwd I J e he h)

/-- The map from `S` to the `I`-adic completion of `R`, inverse to
`AdicCompletion.toComplete`. -/
def ofComplete : S →ₐ[A] AdicCompletion I R :=
  AdicCompletion.liftAlgHom I
    (fun n ↦ (e n).symm.toAlgHom.comp (Ideal.Quotient.mkₐ A (J ^ n)))
    (fun h ↦ compat_bwd I J e he h)

/-- One half of `AdicCompletion.equivOfQuotientEquiv`. -/
theorem toComplete_comp_ofComplete :
    (toComplete I J e he).comp (ofComplete I J e he) = AlgHom.id A S := by
  refine IsAdicComplete.algHom_ext J fun n ↦ ?_
  ext x
  change Ideal.Quotient.mk (J ^ n) (toComplete I J e he (ofComplete I J e he x)) = _
  rw [toComplete, IsAdicComplete.mk_liftAlgHom J
    (fun n ↦ (e n).toAlgHom.comp ((AdicCompletion.evalₐ I n).restrictScalars A))
    (fun h ↦ compat_fwd I J e he h) n]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_restrictScalars']
  rw [ofComplete, AdicCompletion.evalₐ_liftAlgHom I
    (fun n ↦ (e n).symm.toAlgHom.comp (Ideal.Quotient.mkₐ A (J ^ n)))
    (fun h ↦ compat_bwd I J e he h)]
  simp

/-- The other half of `AdicCompletion.equivOfQuotientEquiv`. -/
theorem ofComplete_comp_toComplete :
    (ofComplete I J e he).comp (toComplete I J e he) = AlgHom.id A (AdicCompletion I R) := by
  refine AlgHom.ext fun x ↦ AdicCompletion.ext_evalₐ (I := I) fun n ↦ ?_
  change AdicCompletion.evalₐ I n (ofComplete I J e he (toComplete I J e he x)) = _
  rw [ofComplete, AdicCompletion.evalₐ_liftAlgHom I
    (fun n ↦ (e n).symm.toAlgHom.comp (Ideal.Quotient.mkₐ A (J ^ n)))
    (fun h ↦ compat_bwd I J e he h)]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk]
  rw [show Ideal.Quotient.mk (J ^ n) (toComplete I J e he x) =
      (e n) (AdicCompletion.evalₐ I n x) from
    IsAdicComplete.mk_liftAlgHom J
      (fun n ↦ (e n).toAlgHom.comp ((AdicCompletion.evalₐ I n).restrictScalars A))
      (fun h ↦ compat_fwd I J e he h) n x]
  simp

/-- **A ring with a compatible family of isomorphisms `R ⧸ I ^ n ≃ S ⧸ J ^ n` which is
`J`-adically complete is the `I`-adic completion of `R`.** -/
def equivOfQuotientEquiv : AdicCompletion I R ≃ₐ[A] S :=
  AlgEquiv.ofAlgHom (toComplete I J e he) (ofComplete I J e he)
    (toComplete_comp_ofComplete I J e he) (ofComplete_comp_toComplete I J e he)

/-- The computation rule for `AdicCompletion.equivOfQuotientEquiv`: modulo `J ^ n` it is the
`n`-th isomorphism applied to the `n`-th projection. -/
theorem mk_equivOfQuotientEquiv (n : ℕ) (x : AdicCompletion I R) :
    Ideal.Quotient.mk (J ^ n) (equivOfQuotientEquiv I J e he x) =
      e n (AdicCompletion.evalₐ I n x) :=
  IsAdicComplete.mk_liftAlgHom J
    (fun n ↦ (e n).toAlgHom.comp ((AdicCompletion.evalₐ I n).restrictScalars A))
    (fun h ↦ compat_fwd I J e he h) n x

omit [IsAdicComplete J S] in
/-- The compatibility `AdicCompletion.equivOfQuotientEquiv` requires, obtained from the
compatibility of the *inverse* family ; which is the direction a family built out of maps into
the quotients comes with. -/
theorem compat_of_symm
    (h : ∀ {m n : ℕ} (hmn : m ≤ n) (x : S ⧸ J ^ n),
      Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn) ((e n).symm x) =
        (e m).symm (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn) x))
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp (e n).toAlgHom =
      (e m).toAlgHom.comp (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)) := by
  ext x
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  refine (e m).symm.injective ?_
  rw [AlgEquiv.symm_apply_apply, ← h hmn ((e n) x), AlgEquiv.symm_apply_apply]

end QuotientEquiv

end AdicCompletion

end

end
