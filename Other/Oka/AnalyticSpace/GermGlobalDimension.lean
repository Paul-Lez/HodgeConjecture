/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Regular
public import Other.Oka.RenameIndex
public import Other.Oka.RingTheory.Regular.ChangeOfRings

/-!
# Finitely generated modules over the germ ring have projective dimension `≤ n`

Every finitely generated module over the ring `LocalOkaRing (ULift (Fin n))` of germs of
holomorphic functions in `n` variables has projective dimension at most `n`
(`LocalOkaRing.hasFGGlobalDimensionLE`). This is the analytic form of Hilbert's syzygy theorem.

The proof is an induction on `n`: the last coordinate is a nonzerodivisor in the maximal ideal,
and the quotient by it is the germ ring in `n` variables (`LocalOkaRing.quotientLastVarEquiv`,
which is Weierstrass division), so `ModuleCat.HasFGGlobalDimensionLE.of_quotient` applies. In
`0` variables the germ ring is a field. The coordinates are indexed by `ULift (Fin n)` so that the
ring, and the modules over it, live in an arbitrary universe; this is the indexing of
`complexAffineSpace`.
-/

@[expose] public section

universe u

open IsLocalRing ModuleCat

namespace LocalOkaRing

/-- The germ ring in `0` variables is a field. -/
theorem isField_fin_zero : IsField (LocalOkaRing (Fin 0)) := by
  rw [isField_iff_maximalIdeal_eq, maximalIdeal_eq_span_coord]
  simp

/-- The last coordinate, transported to the `ULift`-indexed germ ring. -/
noncomputable abbrev uliftLastVar (n : ℕ) : LocalOkaRing (ULift.{u} (Fin (n + 1))) :=
  (uliftEquiv (Fin (n + 1))).symm lastVar

/-- The last coordinate is nonzero. -/
lemma uliftLastVar_ne_zero (n : ℕ) : uliftLastVar.{u} n ≠ 0 := by
  intro h
  have := congrArg (uliftEquiv.{u} (Fin (n + 1))) h
  rw [AlgEquiv.apply_symm_apply, map_zero, lastVar_eq_coord] at this
  exact coord_ne_zero _ this

/-- The last coordinate vanishes at the origin. -/
lemma uliftLastVar_mem_maximalIdeal (n : ℕ) :
    uliftLastVar.{u} n ∈ maximalIdeal (LocalOkaRing (ULift.{u} (Fin (n + 1)))) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro h
  have := h.map (uliftEquiv.{u} (Fin (n + 1)))
  rw [AlgEquiv.apply_symm_apply] at this
  have hmem : (lastVar : LocalOkaRing (Fin (n + 1))) ∈ maximalIdeal _ :=
    mem_maximalIdeal_iff.2 (by rw [lastVar_eq_coord]; exact constantCoeff_coord _)
  exact hmem this

/-- Quotienting the `ULift`-indexed germ ring in `n + 1` variables by the last coordinate returns
the germ ring in `n` variables. -/
noncomputable def uliftQuotientLastVarEquiv (n : ℕ) :
    LocalOkaRing (ULift.{u} (Fin (n + 1))) ⧸ Ideal.span {uliftLastVar.{u} n} ≃+*
      LocalOkaRing (ULift.{u} (Fin n)) :=
  (Ideal.quotientEquiv _ (Ideal.span {(lastVar : LocalOkaRing (Fin (n + 1)))})
      (uliftEquiv.{u} (Fin (n + 1))).toRingEquiv (by
        rw [Ideal.map_span, Set.image_singleton]
        simp)).trans
    (quotientLastVarEquiv.symm.trans (uliftEquiv.{u} (Fin n)).toRingEquiv.symm)

/-- **Every finitely generated module over the germ ring in `n` variables has projective
dimension at most `n`.** -/
theorem hasFGGlobalDimensionLE (n : ℕ) :
    HasFGGlobalDimensionLE (LocalOkaRing (ULift.{u} (Fin n))) n := by
  induction n with
  | zero =>
    exact hasFGGlobalDimensionLE_zero_of_isField
      (MulEquiv.isField isField_fin_zero (uliftEquiv.{u} (Fin 0)).toMulEquiv)
  | succ n ih =>
    refine HasFGGlobalDimensionLE.of_quotient (x := uliftLastVar.{u} n) ?_
      (uliftLastVar_mem_maximalIdeal n)
      (ih.of_ringEquiv (uliftQuotientLastVarEquiv.{u} n).symm)
    exact IsSMulRegular.of_ne_zero (uliftLastVar_ne_zero n)

end LocalOkaRing

end
