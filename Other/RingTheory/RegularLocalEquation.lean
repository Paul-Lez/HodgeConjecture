/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.RingTheory.RegularLocalQuotientKernel
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# First-order local equation
-/

@[expose] public noncomputable section

open IsLocalRing

namespace Ideal

variable {R : Type*} [CommRing R] [IsRegularLocalRing R]

/-- A principal equation cutting a regular local hypersurface has nonzero cotangent class. -/
theorem generator_not_mem_square_of_regular_quotient (a : R)
    (hquot : IsRegularLocalRing (R ⧸ Ideal.span ({a} : Set R)))
    (hdim : ringKrullDim (R ⧸ Ideal.span ({a} : Set R)) + 1 = ringKrullDim R) :
    a ∉ (maximalIdeal R) ^ 2 := by
  intro ha2
  let I : Ideal R := Ideal.span ({a} : Set R)
  let Q := R ⧸ I
  let _ : IsRegularLocalRing Q := hquot
  let q : R →+* Q := Ideal.Quotient.mk I
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  let J : Ideal Q := maximalIdeal Q
  let m : Ideal R := maximalIdeal R
  have hJfg : J.FG := IsNoetherian.noetherian J
  have hlocal : IsLocalHom q := IsLocalHom.of_surjective q hq
  let _ : IsLocalHom q := hlocal
  let s : Set R := Function.surjInv hq '' J.generators
  let N : Ideal R := Ideal.span s
  have hs : s.Finite := (Submodule.FG.finite_generators hJfg).image _
  have hqs : q '' s = J.generators := by
    change q '' (Function.surjInv hq '' J.generators) = J.generators
    rw [← Set.image_comp]
    rw [Function.comp_surjInv hq, Set.image_id]
  have hmap : Ideal.map q N = J := by
    change Ideal.map q (Ideal.span s) = J
    rw [Ideal.map_span, hqs]
    exact J.span_generators
  have hNrank : N.spanFinrank ≤ J.spanFinrank := by
    calc
      N.spanFinrank ≤ s.ncard :=
        Submodule.spanFinrank_span_le_ncard_of_finite hs
      _ ≤ J.generators.ncard := Set.ncard_image_le (Submodule.FG.finite_generators hJfg)
      _ = J.spanFinrank := Submodule.FG.generators_ncard hJfg
  have hmq : Ideal.map q m ≤ J := IsLocalRing.map_maximalIdeal_le q
  have hI_square : I ≤ m ^ 2 := by
    change Ideal.span ({a} : Set R) ≤ m ^ 2
    exact Ideal.span_le.2 fun z hz => by
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ha2
  have hmn : m ≤ N ⊔ m ^ 2 := by
    intro x hx
    have hqx : q x ∈ J := hmq (Ideal.mem_map_of_mem q hx)
    obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective q hq).mp (hmap ▸ hqx)
    have hdiff : x - y ∈ m ^ 2 := by
      apply hI_square
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change q (x - y) = 0
      rw [map_sub, hxy]
      simp
    have hy' : y ∈ N ⊔ m ^ 2 := (show N ≤ N ⊔ m ^ 2 from le_sup_left) hy
    have hd' : x - y ∈ N ⊔ m ^ 2 := (show m ^ 2 ≤ N ⊔ m ^ 2 from le_sup_right) hdiff
    rw [← sub_add_cancel x y]
    exact add_mem hd' hy'
  have hmN : m ≤ N := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian m)
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · simpa [smul_eq_mul, pow_two] using hmn
  have hNm : N ≤ m := by
    apply Ideal.span_le.2
    rintro z ⟨g, hg, rfl⟩
    have hzg : q (Function.surjInv hq g) = g := congrFun (Function.comp_surjInv hq) g
    change Function.surjInv hq g ∈ maximalIdeal R
    rw [← IsLocalRing.maximalIdeal_comap q]
    change q (Function.surjInv hq g) ∈ J
    rw [hzg]
    exact (Submodule.FG.generators_mem J) hg
  have hNeq : N = m := le_antisymm hNm hmN
  have hdimle : ringKrullDim R ≤ ringKrullDim Q := by
    calc
      ringKrullDim R = m.spanFinrank :=
        (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
      _ = N.spanFinrank := by rw [hNeq]
      _ ≤ J.spanFinrank := by exact_mod_cast hNrank
      _ = ringKrullDim Q := IsRegularLocalRing.spanFinrank_maximalIdeal (R := Q)
  have hlt : ringKrullDim Q < ringKrullDim R := by
    rw [← hdim, ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := Q)]
    simp [ENat.WithBot.lt_add_one_iff]
  exact (not_lt_of_ge hdimle) hlt

end Ideal
