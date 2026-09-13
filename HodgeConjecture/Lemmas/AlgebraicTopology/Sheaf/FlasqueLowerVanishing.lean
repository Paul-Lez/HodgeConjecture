/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.FlasqueBoundedBelow
/-!
# Global lower-degree vanishing for flasque coefficient complexes

If a bounded-below termwise-flasque sheaf complex is exact through degree `M`,
its global section complex is exact through the same degree. Only the stated
initial range is used; exactness in higher degrees is not assumed.

The proof inductively establishes flasqueness of the cycle sheaves in that
range and then applies the actual short exact cycles sequence. This is the
globalization step for supported semipurity, without assuming a spectral
sequence or an exact global-sections functor.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace HomologicalComplex

universe u

namespace TopCat.Sheaf.IsFlasque.BoundedBelowComplex

variable {X : TopCat.{u}} (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ)

/-- Cycle sheaves are flasque in the initial exact range. -/
lemma cycles_isFlasque_add_nat_of_exact_le (N M : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ i, i ≤ M → K.ExactAt i) (hflasque : ∀ i, (K.X i).IsFlasque)
    (m : ℕ) (hm : N + (m : ℤ) ≤ M) :
    (K.cycles (N + (m : ℤ))).IsFlasque := by
  induction m with
  | zero =>
      let S := cyclesShortComplex K (N - 1)
      have hS : S.ShortExact := by
        apply cyclesShortComplex_shortExact
        simpa only [sub_add_cancel] using hK N (by simpa using hm)
      have hsource : IsZero S.X₂ := K.isZero_of_isStrictlyGE N (N - 1) (by omega)
      let : Epi S.g := hS.epi_g
      have hzero : IsZero (K.cycles N) := by
        simpa only [S, cyclesShortComplex, sub_add_cancel] using IsZero.of_epi S.g hsource
      simpa using of_isZero (K.cycles N) hzero
  | succ m ih =>
      let i : ℤ := N + (m : ℤ)
      let S := cyclesShortComplex K i
      have hS : S.ShortExact :=
        cyclesShortComplex_shortExact K i (hK (i + 1) (by dsimp [i]; omega))
      let : S.X₁.IsFlasque := ih (by omega)
      let : S.X₂.IsFlasque := hflasque i
      have htarget : S.X₃.IsFlasque := of_shortExact_of_isFlasque₁₂ hS
      simpa only [Nat.cast_succ, i, S, cyclesShortComplex, add_assoc] using htarget

/-- All cycle sheaves through the specified exactness bound are flasque,
including those below the strict starting degree, which are zero. -/
lemma cycles_isFlasque_of_exact_le (N M : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ i, i ≤ M → K.ExactAt i) (hflasque : ∀ i, (K.X i).IsFlasque)
    (i : ℤ) (hi : i ≤ M) : (K.cycles i).IsFlasque := by
  by_cases hiN : i < N
  · exact of_isZero _ (IsZero.of_mono (K.iCycles i) (K.isZero_of_isStrictlyGE N i hiN))
  · let m := (i - N).toNat
    have hm : i = N + (m : ℤ) := by
      dsimp [m]
      omega
    rw [hm]
    exact cycles_isFlasque_add_nat_of_exact_le K N M hK hflasque m (by omega)

end TopCat.Sheaf.IsFlasque.BoundedBelowComplex
