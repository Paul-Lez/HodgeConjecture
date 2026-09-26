/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.LocalOkaRing

/-!
# The analytic Nullstellensatz: the vanishing ideal, and the easy inclusion

For an ideal `I` of the germ ring `LocalOkaRing ι`, write `V(I)` for the common zero locus of
`I` near the origin and `I(V(I))` for the ideal of germs vanishing on it. The **Rückert
Nullstellensatz** states

```
I(V(I)) = √I.
```

Only the inclusion `√I ≤ I(V(I))` is proved in this file. The hard half, for the zero locus of a
finite generating family, is `LocalOkaRing.mem_radical_span_of_eventually` in
`Other/Oka/Nullstellensatz/Germ.lean`.

The easy inclusion is elementary: if `f ^ n ∈ I` then `f` vanishes wherever every element of `I`
does, because `ℂ` has no nilpotents.

## Implementation notes

There is no notion of a germ of a *subset* of `ℂ^ι` here, and none is introduced. Instead only
the composite operator `I ↦ I(V(I))` is defined, directly, as `LocalOkaRing.vanishingIdeal`.
That is all the Nullstellensatz statement needs, it avoids a quotient construction, and it makes
the easy inclusion nearly immediate.

Membership is an eventuality in `𝓝 0`, not a condition on a fixed neighbourhood: a germ has no
canonical domain, so any formulation over a fixed neighbourhood would depend on a choice of
representative. For the same reason the evaluation of a germ is only a ring homomorphism
*eventually*, which is what `LocalOkaRing.eventually_eval_add`, `eventually_eval_mul` and
`eventually_eval_pow` record; they are what make `vanishingIdeal` an ideal.

## Main definitions

- `LocalOkaRing.VanishesOn I f`: near the origin, `f` vanishes wherever every element of `I`
  does.
- `LocalOkaRing.vanishingIdeal I`: the germs vanishing on the zero locus of `I`.

## Main results

- `LocalOkaRing.eq_zero_of_eventually_eval_eq_zero`: a germ whose evaluation vanishes near the
  origin is zero ; the identity theorem, in the form used here.
- `LocalOkaRing.le_vanishingIdeal` and `LocalOkaRing.isRadical_vanishingIdeal`.
- `LocalOkaRing.radical_le_vanishingIdeal`: **the easy half of the Nullstellensatz**.
- `LocalOkaRing.vanishingIdeal_bot` and `LocalOkaRing.vanishingIdeal_top`: the two degenerate
  cases, computed. These are the check that the definition is not vacuous ; `vanishingIdeal ⊥`
  is `⊥`, not `⊤`, and it is the identity theorem that makes it so.

## References

- [Hans Grauert and Reinhold Remmert, *Analytische Stellenalgebren*][grauert-remmert1971], §I
- [Robert C. Gunning and Hugo Rossi, *Analytic functions of several complex
  variables*][gunning-rossi1965], Chapter III
-/

@[expose] public section

open Filter Topology MvPowerSeries

universe u

namespace LocalOkaRing

variable {ι : Type u}

/-! ### Evaluation is a ring homomorphism near the origin -/

/-- Near the origin, evaluation of germs is additive. It is only *near* the origin: a germ is a
power series that need not converge at a given point. -/
lemma eventually_eval_add (P Q : LocalOkaRing ι) :
    ∀ᶠ z in 𝓝 (0 : ι → ℂ), ((P + Q : LocalOkaRing ι) : MvPowerSeries ι ℂ).eval z =
      (P : MvPowerSeries ι ℂ).eval z + (Q : MvPowerSeries ι ℂ).eval z := by
  filter_upwards [(P + Q).2.represents_eval,
    Represents.add P.2.represents_eval Q.2.represents_eval] with z h1 h2
  exact h1.unique (by rwa [AddMemClass.coe_add])

/-- Near the origin, evaluation of germs is multiplicative. -/
lemma eventually_eval_mul (P Q : LocalOkaRing ι) :
    ∀ᶠ z in 𝓝 (0 : ι → ℂ), ((P * Q : LocalOkaRing ι) : MvPowerSeries ι ℂ).eval z =
      (P : MvPowerSeries ι ℂ).eval z * (Q : MvPowerSeries ι ℂ).eval z := by
  filter_upwards [(P * Q).2.represents_eval,
    Represents.mul P.2 Q.2 P.2.represents_eval Q.2.represents_eval] with z h1 h2
  exact h1.unique (by rwa [MulMemClass.coe_mul])

/-- Near the origin, evaluation of germs respects powers. -/
lemma eventually_eval_pow (P : LocalOkaRing ι) (n : ℕ) :
    ∀ᶠ z in 𝓝 (0 : ι → ℂ), ((P ^ n : LocalOkaRing ι) : MvPowerSeries ι ℂ).eval z =
      ((P : MvPowerSeries ι ℂ).eval z) ^ n := by
  induction n with
  | zero =>
    filter_upwards [(1 : LocalOkaRing ι).2.represents_eval, represents_one (ι := ι)] with z h1 h2
    rw [pow_zero, pow_zero]
    exact h1.unique (by rwa [OneMemClass.coe_one])
  | succ n ih =>
    filter_upwards [ih, eventually_eval_mul (P ^ n) P] with z hz hmul
    rw [pow_succ, hmul, hz, pow_succ]

/-! ### The vanishing ideal of the zero locus of an ideal -/

variable (I : Ideal (LocalOkaRing ι))

/-- A germ `f` **vanishes on the zero locus of `I`** if, near the origin, `f` vanishes at every
point at which every element of `I` vanishes.

"Near the origin" is an eventuality in `𝓝 0`, not a condition on any fixed neighbourhood: germs
have no canonical domain, so this is the only formulation that does not depend on a choice of
representative. -/
def VanishesOn (I : Ideal (LocalOkaRing ι)) (f : LocalOkaRing ι) : Prop :=
  ∀ᶠ z in 𝓝 (0 : ι → ℂ),
    (∀ g ∈ I, (g : MvPowerSeries ι ℂ).eval z = 0) → (f : MvPowerSeries ι ℂ).eval z = 0

/-- The **vanishing ideal** of the zero locus of `I`: the germs vanishing, near the origin, at
every point at which every element of `I` vanishes.

The Rückert Nullstellensatz states that this equals `I.radical`. Only the inclusion
`I.radical ≤ vanishingIdeal I` is proved here; see the module docstring. -/
def vanishingIdeal (I : Ideal (LocalOkaRing ι)) : Ideal (LocalOkaRing ι) where
  carrier := {f | VanishesOn I f}
  zero_mem' := by
    filter_upwards [(0 : LocalOkaRing ι).2.represents_eval, represents_zero (ι := ι)]
      with z h1 h2 _
    exact h1.unique (by rwa [ZeroMemClass.coe_zero])
  add_mem' {a b} ha hb := by
    filter_upwards [ha, hb, eventually_eval_add a b] with z hza hzb hadd h
    rw [hadd, hza h, hzb h, add_zero]
  smul_mem' c a ha := by
    filter_upwards [ha, eventually_eval_mul c a] with z hza hmul h
    rw [smul_eq_mul, hmul, hza h, mul_zero]

lemma mem_vanishingIdeal_iff {f : LocalOkaRing ι} : f ∈ vanishingIdeal I ↔ VanishesOn I f :=
  Iff.rfl

/-- Every element of `I` vanishes on the zero locus of `I`, tautologically. -/
theorem le_vanishingIdeal : I ≤ vanishingIdeal I :=
  fun _ hf ↦ Filter.Eventually.of_forall fun _ h ↦ h _ hf

omit I in
theorem vanishingIdeal_mono {I J : Ideal (LocalOkaRing ι)} (h : I ≤ J) :
    vanishingIdeal I ≤ vanishingIdeal J :=
  fun _ hf ↦ hf.mono fun _ hz hJ ↦ hz fun g hg ↦ hJ g (h hg)

/-- The vanishing ideal is a radical ideal: `ℂ` has no nilpotents, so if a power of `f`
vanishes on the zero locus then so does `f`. -/
theorem isRadical_vanishingIdeal : (vanishingIdeal I).IsRadical := by
  rintro f ⟨n, hfn⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `f ^ 0 = 1 ∈ vanishingIdeal I` forces the whole ring, so in particular `f` is a member
    rw [pow_zero] at hfn
    simpa using (vanishingIdeal I).mul_mem_left f hfn
  · filter_upwards [hfn, eventually_eval_pow f n] with z hz hpow h
    exact pow_eq_zero_iff hn.ne' |>.mp (hpow ▸ hz h)

/-- **The easy half of the Rückert Nullstellensatz**: the radical of `I` vanishes on the zero
locus of `I`. For the hard half see `LocalOkaRing.mem_radical_span_of_eventually`. -/
theorem radical_le_vanishingIdeal : I.radical ≤ vanishingIdeal I :=
  (Ideal.radical_mono (le_vanishingIdeal I)).trans (isRadical_vanishingIdeal I)

/-- The zero locus of the unit ideal is empty near the origin, since `1` does not vanish there,
so every germ vanishes on it vacuously. -/
@[simp]
theorem vanishingIdeal_top : vanishingIdeal (⊤ : Ideal (LocalOkaRing ι)) = ⊤ := by
  refine le_antisymm le_top (fun f _ ↦ ?_)
  filter_upwards [(1 : LocalOkaRing ι).2.represents_eval, represents_one (ι := ι)] with z h1 h2 h
  exact absurd (h 1 Submodule.mem_top)
    (by rw [h1.unique (by rwa [OneMemClass.coe_one])]; exact one_ne_zero)

variable [Finite ι]

/-- A germ whose evaluation vanishes near the origin is zero: the identity theorem. -/
theorem eq_zero_of_eventually_eval_eq_zero {P : LocalOkaRing ι}
    (h : ∀ᶠ z in 𝓝 (0 : ι → ℂ), (P : MvPowerSeries ι ℂ).eval z = 0) : P = 0 :=
  LocalOkaRing.ext (eq_zero_of_represents_zero (P.2.represents_eval.congr h))

/-- The zero locus of the zero ideal is the whole neighbourhood of the origin, so only the zero
germ vanishes on it. This is the identity theorem, and it is the sanity check that
`vanishingIdeal` is not degenerate. -/
@[simp]
theorem vanishingIdeal_bot : vanishingIdeal (⊥ : Ideal (LocalOkaRing ι)) = ⊥ := by
  refine le_antisymm (fun f hf ↦ ?_) ?_
  · refine Ideal.mem_bot.mpr (eq_zero_of_eventually_eval_eq_zero ?_)
    filter_upwards [hf, (0 : LocalOkaRing ι).2.represents_eval, represents_zero (ι := ι)]
      with z hz h1 h2
    refine hz fun g hg ↦ ?_
    rw [Ideal.mem_bot.mp hg]
    exact h1.unique (by rwa [ZeroMemClass.coe_zero])
  · simp

end LocalOkaRing

end
