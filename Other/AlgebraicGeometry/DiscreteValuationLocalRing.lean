/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SmoothRegularLocal
public import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
public import HodgeConjecture.Lemmas.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Stalks at codimension-one points of smooth schemes are discrete valuation rings

This file is the commutative-algebra half of sub-obligation (2) of §4.3 step 4 of
`docs/DIVISOR_HANDOFF.md`: the algebraic local form of a Cartier local equation.

* `isDiscreteValuationRing_of_ringKrullDim_eq_one`: a regular local domain of Krull dimension
  one is a discrete valuation ring. This is the implication `regular of dimension one ⇒ DVR` of
  `IsDiscreteValuationRing.TFAE`, read off from the cotangent-space characterisation of
  regularity.
* `isDiscreteValuationRing_stalk_of_coheight_eq_one`: the stalk of a smooth complex scheme at a
  point of codimension one is a discrete valuation ring. The regularity of the stalk is
  `Smooth.isRegularLocalRing_stalk_complex` and its dimension is `ringKrullDim_stalk_eq_coheight`.
* `Scheme.ord_algebraMap_eq_one_of_irreducible`: the order of vanishing of (the image in the
  function field of) a uniformiser is one.
* `Scheme.exists_unit_mul_zpow_eq`: a nonzero rational function is, in the function field,
  a unit of the stalk times the `ord`-th power of a uniformiser.

Nothing here uses projectivity, and only `isDiscreteValuationRing_stalk_of_coheight_eq_one`
uses the complex numbers (through the repository's regularity theorem for smooth stalks).
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry

/-- A regular local domain whose Krull dimension is one is a discrete valuation ring. -/
theorem isDiscreteValuationRing_of_ringKrullDim_eq_one (R : Type*) [CommRing R] [IsDomain R]
    [IsRegularLocalRing R] (h : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  rw [← IsLocalRing.finrank_CotangentSpace_eq_one_iff]
  have hfin := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp ‹_›
  rw [h] at hfin
  exact_mod_cast hfin

variable {X : Scheme.{0}}

/-- The stalk of a smooth complex scheme at a point of codimension one is a discrete valuation
ring: it is a regular local ring by `Smooth.isRegularLocalRing_stalk_complex`, a domain because
the scheme is integral, and of dimension one by `ringKrullDim_stalk_eq_coheight`. -/
theorem isDiscreteValuationRing_stalk_of_coheight_eq_one (f : X ⟶ Spec ↧ℂ) [Smooth f]
    [IsIntegral X] {x : X} (hx : coheight x = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  have : IsRegularLocalRing (X.presheaf.stalk x) :=
    Smooth.isRegularLocalRing_stalk_complex (f := f) x
  refine isDiscreteValuationRing_of_ringKrullDim_eq_one _ ?_
  rw [ringKrullDim_stalk_eq_coheight, hx]
  rfl

variable [IsIntegral X] [IsLocallyNoetherian X] {x : X}
  [IsDiscreteValuationRing (X.presheaf.stalk x)]

/-- The order-of-vanishing homomorphism of a scheme at a codimension-one point is the
order-of-vanishing homomorphism of its stalk. -/
theorem Scheme.ordHom_eq_ordFrac (hx : coheight x = 1) :
    X.ordHom x hx = Ring.ordFrac (X.presheaf.stalk x) (K := X.functionField) := rfl

/-- In the function field, the image of a uniformiser of the stalk at a codimension-one point has
order of vanishing one. -/
theorem Scheme.ord_algebraMap_eq_one_of_irreducible (hx : coheight x = 1)
    {p : X.presheaf.stalk x} (hp : Irreducible p) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField p) x = 1 := by
  have hp0 : algebraMap (X.presheaf.stalk x) X.functionField p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (X.presheaf.stalk x)
      X.functionField)).mpr hp.ne_zero
  rw [Scheme.ord_eq_iff hx hp0, Scheme.ordHom_eq_ordFrac hx, Ring.ordFrac_irreducible hp,
    WithZero.exp_eq_coe_ofAdd]

/-- A regular germ which is not a unit at a codimension-one point with discrete valuation stalk
has nonzero order of vanishing there. -/
theorem Scheme.ord_ne_zero_of_not_isUnit (hx : coheight x = 1) {a : X.presheaf.stalk x}
    (ha : a ≠ 0) (hu : ¬ IsUnit a) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x ≠ 0 := by
  intro hzero
  refine hu ?_
  have ha0 : algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)).mpr ha
  rw [Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing (K := X.functionField),
    ← Scheme.ordHom_eq_ordFrac hx, (Scheme.ord_eq_iff hx ha0).mp hzero]
  simp

/-- **The local form of a rational function at a codimension-one point.** A nonzero rational
function is, in the function field, the product of a unit of the stalk and the `ord`-th power of
a uniformiser of the stalk. -/
theorem Scheme.exists_unit_mul_zpow_eq (hx : coheight x = 1)
    {g : X.functionField} (hg : g ≠ 0) :
    ∃ (p : X.presheaf.stalk x) (u : (X.presheaf.stalk x)ˣ), Irreducible p ∧
      X.ord (algebraMap (X.presheaf.stalk x) X.functionField p) x = 1 ∧
      g = algebraMap (X.presheaf.stalk x) X.functionField (u : X.presheaf.stalk x) *
        (algebraMap (X.presheaf.stalk x) X.functionField p) ^ (X.ord g x) := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  have hp0 : algebraMap (X.presheaf.stalk x) X.functionField p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (X.presheaf.stalk x)
      X.functionField)).mpr hp.ne_zero
  have hordp := X.ord_algebraMap_eq_one_of_irreducible hx hp
  have hord : Ring.ordFrac (X.presheaf.stalk x) (K := X.functionField)
      ((algebraMap (X.presheaf.stalk x) X.functionField p) ^ (X.ord g x)) =
      Ring.ordFrac (X.presheaf.stalk x) (K := X.functionField) g := by
    rw [map_zpow₀, ← Scheme.ordHom_eq_ordFrac hx,
      (Scheme.ord_eq_iff hx hg).mp rfl, (Scheme.ord_eq_iff hx hp0).mp hordp,
      ← WithZero.coe_zpow, ← ofAdd_zsmul]
    simp
  obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq
    (R := X.presheaf.stalk x) (K := X.functionField) _ _ hord
  rw [Units.smul_def, Algebra.smul_def] at hu
  exact ⟨p, u, hp, hordp, hu.symm⟩

end AlgebraicGeometry
