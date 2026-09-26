/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.RingTheory.MvPolynomial.Localization

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

/-!
# Adjoining an inverse to a quotient of a polynomial ring, in one more variable

Material for `Mathlib/RingTheory/MvPolynomial/Localization.lean`; see `README.md` on the mirror
tree.

For an ideal `I` of `R[xᵢ]` and `f : R[xᵢ]`, the classical presentation of the localisation of
`R[xᵢ] ⧸ I` away from the image of `f` adjoins **one** variable and **one** equation:

  `(R[xᵢ] ⧸ I)_f = R[xᵢ, t] ⧸ (I, t·f - 1)`.

`MvPolynomial.awayIdeal I f` is the ideal on the right, in `R[Option σ]` with `none` the new
variable, and `MvPolynomial.isLocalization_away_quotient_awayIdeal` says the quotient by it
**is** that localisation ; not merely isomorphic to it, but an `IsLocalization.Away` for the
image of `f`, so that the universal property is available at the presented algebra directly and
a consumer does not have to transport along an isomorphism to use it.

## What Mathlib already has, and what this adds

`IsLocalization.Away.mvPolynomialQuotientEquiv` is the same statement in **one** variable over an
arbitrary base: `A[t] ⧸ (r·t - 1) ≃ₐ[A] S` for `[IsLocalization.Away r S]`. It is not directly
usable for a quotient of a polynomial ring, because the base one wants there is `R[xᵢ] ⧸ I` while
the ring one has in hand is `R[xᵢ, t] ⧸ (I, t·f - 1)`: the two differ by the transport that
commutes a quotient past a polynomial ring, and it is that transport, not the localisation, that
is the work. This file goes round it instead of through it, by exhibiting the two maps and
checking both composites on generators, which is shorter and leaves no `Option σ ≃ Unit ⊕ σ`
bookkeeping in the statement.

## Main definitions

- `MvPolynomial.awayIdeal`: the ideal `(I, t·f - 1)` of `R[Option σ]`.
- `MvPolynomial.awayBaseHom`: the map `R[xᵢ] ⧸ I ⟶ R[xᵢ, t] ⧸ (I, t·f - 1)`, which is the
  `Algebra` structure the localisation statement is about.
- `MvPolynomial.awayQuotientEquiv`: the resulting isomorphism with `Localization.Away`.

## Main results

- `MvPolynomial.isLocalization_away_quotient_awayIdeal`: **the quotient is the localisation.**
  This is the statement to use. Mind the direction of the file, which is the opposite of the
  direction of the mathematics: the two maps are built by hand, `MvPolynomial.awayQuotientEquiv`
  is assembled from them, and the instance is transported along it.

## What is not here

**No claim that `MvPolynomial.awayIdeal` is a *presentation* in Mathlib's structured sense.**
`Mathlib/RingTheory/Extension/Presentation/Basic.lean` has a `localizationAway` presentation at
`:225` and composes it with a presentation of the base, and its `relation_comp_localizationAway_inl`
at `:460` computes the composed relation to be `rename Sum.inr (P.σ g) * X (Sum.inl ()) - 1` ;
the same equation as here, up to a reindexing of `Option σ` as `Unit ⊕ σ`. Nothing here is stated
in those terms, and a consumer wanting the structured presentation should build it from that
route. Note before taking it that the Mathlib lemma carries two hypotheses on the chosen
set-theoretic section, `P.σ (-1) = -1` and `P.σ 0 = 0`, which have no analogue here; that file is
not imported, which is why its declarations are named above by path and line rather than in
backticks.
-/

noncomputable section

namespace MvPolynomial

variable {R : Type*} [CommRing R] {σ : Type*} (I : Ideal (MvPolynomial σ R))
  (f : MvPolynomial σ R)

/-- **The ideal `(I, t·f - 1)` of `R[xᵢ, t]`**, with `none : Option σ` the new variable `t`.

The quotient by it is the localisation of `R[xᵢ] ⧸ I` away from the image of `f`
(`MvPolynomial.isLocalization_away_quotient_awayIdeal`). -/
def awayIdeal : Ideal (MvPolynomial (Option σ) R) :=
  I.map (rename some) ⊔ Ideal.span {X none * rename some f - 1}

/-- **The map to the localisation, before passing to the quotient**: the old variables go to
their own images, and the new one to `1/f`. -/
def awayAeval : MvPolynomial (Option σ) R →ₐ[R]
    Localization.Away (Ideal.Quotient.mk I f) :=
  aeval fun o ↦ o.elim (IsLocalization.Away.invSelf (Ideal.Quotient.mk I f))
    fun i ↦ algebraMap _ _ (Ideal.Quotient.mk I (X i))

/-- On the old variables `MvPolynomial.awayAeval` is the structure map of the localisation, which
is what makes it kill `I` and is the only property of it used below. -/
theorem awayAeval_comp_rename :
    (awayAeval I f).comp (rename (R := R) (some (α := σ))) =
      (IsScalarTower.toAlgHom R (MvPolynomial σ R ⧸ I) _).comp (Ideal.Quotient.mkₐ R I) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [awayAeval]

/-- Both generators of `MvPolynomial.awayIdeal` are killed: the first because `I` dies in the
quotient, the second because `1/f` is inverse to the image of `f`. -/
theorem awayIdeal_le_ker : awayIdeal I f ≤ RingHom.ker (awayAeval I f) := by
  refine sup_le ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    have h := congrArg (fun φ : MvPolynomial σ R →ₐ[R] _ ↦ φ p) (awayAeval_comp_rename I f)
    simp only [AlgHom.coe_comp, Function.comp_apply] at h
    rw [h]
    simp [Ideal.Quotient.eq_zero_iff_mem.2 hp]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, map_one]
    have h1 : awayAeval I f (X none) =
        IsLocalization.Away.invSelf (Ideal.Quotient.mk I f) := by simp [awayAeval]
    have h2 : awayAeval I f (rename some f) =
        algebraMap (MvPolynomial σ R ⧸ I) _ (Ideal.Quotient.mk I f) := by
      have h := congrArg (fun φ : MvPolynomial σ R →ₐ[R] _ ↦ φ f) (awayAeval_comp_rename I f)
      simpa using h
    rw [h1, h2, mul_comm, IsLocalization.Away.mul_invSelf, sub_self]

/-- **`MvPolynomial.awayAeval` on the quotient.** -/
def awayLift : (MvPolynomial (Option σ) R ⧸ awayIdeal I f) →ₐ[R]
    Localization.Away (Ideal.Quotient.mk I f) :=
  Ideal.Quotient.liftₐ _ (awayAeval I f) fun _ ha ↦ awayIdeal_le_ker I f ha

/-- **The map from the base**, `R[xᵢ] ⧸ I ⟶ R[xᵢ, t] ⧸ (I, t·f - 1)`: rename the variables and
project. This is the `Algebra` structure the localisation statement is about. -/
def awayBaseHom : (MvPolynomial σ R ⧸ I) →ₐ[R]
    (MvPolynomial (Option σ) R ⧸ awayIdeal I f) :=
  Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ R (awayIdeal I f)).comp (rename some))
    fun _ ha ↦ by
      simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)

instance : Algebra (MvPolynomial σ R ⧸ I) (MvPolynomial (Option σ) R ⧸ awayIdeal I f) :=
  (awayBaseHom I f).toRingHom.toAlgebra

instance : IsScalarTower R (MvPolynomial σ R ⧸ I)
    (MvPolynomial (Option σ) R ⧸ awayIdeal I f) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ ((awayBaseHom I f).commutes r).symm

/-- **The new variable is the inverse of the image of `f`** ; the equation `t·f = 1`, read in the
quotient. Everything about invertibility below comes from this one line. -/
theorem awayBaseHom_mul_mk_X_none :
    awayBaseHom I f (Ideal.Quotient.mk I f) *
      Ideal.Quotient.mk (awayIdeal I f) (X none) = 1 := by
  have hmem : X (R := R) none * rename some f - 1 ∈ awayIdeal I f :=
    Ideal.mem_sup_right (Ideal.subset_span rfl)
  have h : Ideal.Quotient.mk (awayIdeal I f) (X none * rename some f - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 hmem
  simp only [map_sub, map_mul, map_one, sub_eq_zero] at h
  simp only [awayBaseHom, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rw [mul_comm]
  exact h

theorem awayBaseHom_isUnit : IsUnit (awayBaseHom I f (Ideal.Quotient.mk I f)) :=
  IsUnit.of_mul_eq_one _ (awayBaseHom_mul_mk_X_none I f)

/-- **The map back from the localisation**, by its universal property. -/
def awayInv : Localization.Away (Ideal.Quotient.mk I f) →ₐ[R]
    (MvPolynomial (Option σ) R ⧸ awayIdeal I f) :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (Ideal.Quotient.mk I f))
    (f := awayBaseHom I f) (by
      rintro ⟨y, n, rfl⟩
      simpa only [map_pow] using (awayBaseHom_isUnit I f).pow n)

theorem awayInv_algebraMap (a : MvPolynomial σ R ⧸ I) :
    awayInv I f (algebraMap _ _ a) = awayBaseHom I f a := by
  rw [awayInv, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  rfl

/-- `1/f` goes back to the new variable. Proved by cancelling the image of `f`, which is a unit
on both sides, rather than by unfolding `IsLocalization.lift` at an `IsLocalization.mk'`. -/
theorem awayInv_invSelf :
    awayInv I f (IsLocalization.Away.invSelf (Ideal.Quotient.mk I f)) =
      Ideal.Quotient.mk (awayIdeal I f) (X none) := by
  have h1 : awayBaseHom I f (Ideal.Quotient.mk I f) *
      awayInv I f (IsLocalization.Away.invSelf (Ideal.Quotient.mk I f)) = 1 := by
    rw [← awayInv_algebraMap I f, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  calc awayInv I f (IsLocalization.Away.invSelf (Ideal.Quotient.mk I f))
      = awayInv I f (IsLocalization.Away.invSelf (Ideal.Quotient.mk I f)) *
          (awayBaseHom I f (Ideal.Quotient.mk I f) *
            Ideal.Quotient.mk (awayIdeal I f) (X none)) := by
        rw [awayBaseHom_mul_mk_X_none, mul_one]
    _ = Ideal.Quotient.mk (awayIdeal I f) (X none) := by
        rw [← mul_assoc, mul_comm _ (awayBaseHom I f _), h1, one_mul]

theorem awayLift_awayBaseHom (a : MvPolynomial σ R ⧸ I) :
    awayLift I f (awayBaseHom I f a) = algebraMap _ _ a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h := congrArg (fun φ : MvPolynomial σ R →ₐ[R] _ ↦ φ p) (awayAeval_comp_rename I f)
  simp only [AlgHom.coe_comp, Function.comp_apply] at h
  simpa [awayLift, awayBaseHom] using h

theorem awayLift_comp_awayInv : (awayLift I f).comp (awayInv I f) = AlgHom.id R _ := by
  ext a
  change awayLift I f (awayInv I f (algebraMap _ _ a)) = algebraMap _ _ a
  rw [awayInv_algebraMap, awayLift_awayBaseHom]

theorem awayInv_comp_awayLift : (awayInv I f).comp (awayLift I f) = AlgHom.id R _ := by
  ext x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  revert p
  suffices h : ((awayInv I f).comp (awayLift I f)).comp
      (Ideal.Quotient.mkₐ R (awayIdeal I f)) = Ideal.Quotient.mkₐ R (awayIdeal I f) by
    intro p
    exact congrFun (congrArg DFunLike.coe h) p
  apply MvPolynomial.algHom_ext
  rintro (_ | i)
  · simp [awayLift, awayAeval, awayInv_invSelf]
  · simp [awayLift, awayAeval, awayInv_algebraMap, awayBaseHom]

/-- **The isomorphism with `Localization.Away`**, over `R`. This is the shape a consumer that
renames variables wants; `MvPolynomial.isLocalization_away_quotient_awayIdeal` is the shape a
consumer that maps out of the quotient wants, and it is the stronger of the two. -/
def awayQuotientEquiv :
    (MvPolynomial (Option σ) R ⧸ awayIdeal I f) ≃ₐ[R]
      Localization.Away (Ideal.Quotient.mk I f) :=
  AlgEquiv.ofAlgHom (awayLift I f) (awayInv I f) (awayLift_comp_awayInv I f)
    (awayInv_comp_awayLift I f)

@[simp]
theorem awayQuotientEquiv_apply (x : MvPolynomial (Option σ) R ⧸ awayIdeal I f) :
    awayQuotientEquiv I f x = awayLift I f x :=
  rfl

/-- `MvPolynomial.awayQuotientEquiv` read as an isomorphism of algebras over `R[xᵢ] ⧸ I`, which
is the form `IsLocalization.isLocalization_of_algEquiv` consumes. -/
def awayQuotientAlgEquiv :
    Localization.Away (Ideal.Quotient.mk I f) ≃ₐ[MvPolynomial σ R ⧸ I]
      (MvPolynomial (Option σ) R ⧸ awayIdeal I f) :=
  AlgEquiv.ofRingEquiv (f := (awayQuotientEquiv I f).symm.toRingEquiv) (awayInv_algebraMap I f)

/-- **`R[xᵢ, t] ⧸ (I, t·f - 1)` is the localisation of `R[xᵢ] ⧸ I` away from the image of `f`.**

An instance rather than only an isomorphism, because what a consumer wants is the universal
property *at this ring*: a map out of it is a map out of `R[xᵢ] ⧸ I` inverting `f`, and with only
an isomorphism in hand every such construction becomes a transport. -/
instance isLocalization_away_quotient_awayIdeal :
    IsLocalization.Away (Ideal.Quotient.mk I f)
      (MvPolynomial (Option σ) R ⧸ awayIdeal I f) :=
  IsLocalization.isLocalization_of_algEquiv _ (awayQuotientAlgEquiv I f)

end MvPolynomial

end

end
