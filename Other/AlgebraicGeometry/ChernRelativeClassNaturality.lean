/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernRelativeClass
public import Other.AlgebraicGeometry.ChernLocalModelWinding
public import Other.AlgebraicGeometry.ClosedSupportCoheightDimension

/-!
# The relative first Chern class as the witness of the winding naturality obligation

This file connects the canonical relative first Chern class of
`Other/AlgebraicGeometry/ChernRelativeClass.lean` with the obligation
`HasChernWindingNaturality` of `Other/AlgebraicGeometry/ChernLocalModelWinding.lean`, which is
the last remaining piece of §4.3 step 4 of `docs/DIVISOR_HANDOFF.md`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open CategoryTheory.Localization

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernRelativeNaturalityTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

/-! ### Transport along an equality of supports -/

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Transport of supported rational cohomology along an equality of supports. -/
def supportedClassTransport {Z Z' : Set (ComplexPoint X)} (h : Z = Z') (n : ℤ) :
    RationalCohomologyWithSupport X Z n ≃ RationalCohomologyWithSupport X Z' n := by
  subst h; exact Equiv.refl _

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
@[simp] lemma forgetSupportHypercohomology_supportedClassTransport
    {Z Z' : Set (ComplexPoint X)} (h : Z = Z') (n : ℤ)
    (β : RationalCohomologyWithSupport X Z n) :
    forgetSupportHypercohomology X Z' n (supportedClassTransport X h n β) =
      forgetSupportHypercohomology X Z n β := by
  subst h; rfl

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
@[simp] lemma forgetSupport_supportedClassTransport {Z Z' : Set (ComplexPoint X)} (h : Z = Z')
    (n : ℕ) (β : RationalCohomologyWithSupport X Z n) :
    coneForgetSupport X Z' n (supportedClassTransport X h (n : ℤ) β) = coneForgetSupport X Z n β := by
  subst h; rfl

/-! ### The splitting datum off the support of the divisor -/

/-- **The frame off the divisor.** For Cartier data `c` representing `L`, the analytification of
the corresponding rational section frames the line bundle on `X^an ∖ |D|^an`; equivalently, the
extension `E` acquires a lift `ℓ` of the constant integer section `1` over that open set.

This is the splitting datum `ℓ` that §4.3 step 3 of `docs/DIVISOR_HANDOFF.md` has always been
missing, and it is the *only* geometric input the canonical relative first Chern class needs. -/
def HasComplementFrame : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∀ c : Scheme.CartierData X.left, c.Represents L →
      ∃ ℓ : E.middle.obj.obj (op ((cycleAnalyticClosedSupport X c.divisor).compl)),
        E.projection.hom.app (op ((cycleAnalyticClosedSupport X c.divisor).compl)) ℓ =
          (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top :
              (cycleAnalyticClosedSupport X c.divisor).compl ≤ ⊤)).op
            HolomorphicUnitExtension.integerOneSection

/-! ### The relative first Chern class in the supported injective model -/

variable {X}

/-- The complement of the analytic support of the divisor, as an analytic open. -/
abbrev divisorComplementOpen (c : Scheme.CartierData X.left) :
    Opens (TopCat.of (ComplexPoint X)) :=
  (cycleAnalyticClosedSupport X c.divisor).compl

lemma divisorComplementOpen_compl (c : Scheme.CartierData X.left) :
    ((divisorComplementOpen c : Opens (TopCat.of (ComplexPoint X))) :
        Set (ComplexPoint X))ᶜ =
      ((cycleAnalyticClosedSupport X c.divisor : Closeds (ComplexPoint X)) :
        Set (ComplexPoint X)) :=
  compl_compl _

set_option maxHeartbeats 1000000 in
/-- The relative first Chern class, with its support written as the analytic support of the
divisor rather than as the complement of the complement. -/
def relativeChernClassOnSupport (c : Scheme.CartierData X.left)
    (E : HolomorphicUnitExtension X (dim X.left))
    (ℓ : E.middle.obj.obj (op (divisorComplementOpen c)))
    (hℓ : E.projection.hom.app (op (divisorComplementOpen c)) ℓ =
      (𝓒(↧(ComplexPoint X); ℤ)).obj.map
        (homOfLE (le_top : divisorComplementOpen c ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection)
    (cmp : RelativeChernComparison X (dim X.left) (divisorComplementOpen c)) :
    RationalCohomologyWithSupport X
      ((cycleAnalyticClosedSupport X c.divisor : Closeds (ComplexPoint X)) :
        Set (ComplexPoint X)) 2 :=
  supportedClassTransport X (divisorComplementOpen_compl c) 2
    (E.relativeChernClass (divisorComplementOpen c) ℓ hℓ cmp)

set_option maxHeartbeats 1000000 in
/-- **The relative first Chern class of `(L, s)` in the supported injective model.**

This is the witness required by `HasChernLocalModel` and `HasChernWindingNaturality`: not an
arbitrary lift of the first Chern class, but the canonical one cut out by the frame of the bundle
off `|D|^an`. -/
def relativeChernSupportedClass (c : Scheme.CartierData X.left)
    (E : HolomorphicUnitExtension X (dim X.left))
    (ℓ : E.middle.obj.obj (op (divisorComplementOpen c)))
    (hℓ : E.projection.hom.app (op (divisorComplementOpen c)) ℓ =
      (𝓒(↧(ComplexPoint X); ℤ)).obj.map
        (homOfLE (le_top : divisorComplementOpen c ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection)
    (cmp : RelativeChernComparison X (dim X.left) (divisorComplementOpen c)) :
    SupportedInjectiveHomology X (cycleAnalyticClosedSupport X c.divisor) (2 : ℤ) :=
  coneSupportAddEquivSupportedInjectiveHomology X
    ((cycleAnalyticClosedSupport X c.divisor : Closeds (ComplexPoint X)) :
      Set (ComplexPoint X))
    (cycleAnalyticClosedSupport X c.divisor).isClosed (2 : ℤ)
    (relativeChernClassOnSupport c E ℓ hℓ cmp)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The relative first Chern class is a lift of the rational first Chern class.** This is the
first clause of `HasChernLocalModel` / `HasChernWindingNaturality`, for the canonical witness. -/
theorem supportedInjectiveToAmbient_relativeChernSupportedClass
    (c : Scheme.CartierData X.left) (E : HolomorphicUnitExtension X (dim X.left))
    (ℓ : E.middle.obj.obj (op (divisorComplementOpen c)))
    (hℓ : E.projection.hom.app (op (divisorComplementOpen c)) ℓ =
      (𝓒(↧(ComplexPoint X); ℤ)).obj.map
        (homOfLE (le_top : divisorComplementOpen c ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection)
    (cmp : RelativeChernComparison X (dim X.left) (divisorComplementOpen c)) :
    supportedInjectiveToAmbient X (cycleAnalyticClosedSupport X c.divisor) (2 : ℤ)
        (relativeChernSupportedClass c E ℓ hℓ cmp) =
      rationalCohomologyAddEquivAmbientInjectiveHomology X 2
        (integralToRationalCohomology X 2 E.firstChernClass) := by
  have h := coneSupportAddEquivSupportedInjectiveHomology_forgetSupport X
    ((cycleAnalyticClosedSupport X c.divisor : Closeds (ComplexPoint X)) :
      Set (ComplexPoint X))
    (cycleAnalyticClosedSupport X c.divisor).isClosed 2
    (relativeChernClassOnSupport c E ℓ hℓ cmp)
  refine h.symm.trans (congrArg _ ?_)
  rw [relativeChernClassOnSupport, forgetSupportHypercohomology_supportedClassTransport]
  have hc := congrArg (hypercohomologyAddEquivConstantCohomology ℚ X 2).symm
    (E.forgetSupport_relativeChernClass _ ℓ hℓ cmp)
  dsimp only [coneForgetSupport, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at hc
  simpa only [Nat.cast_ofNat, AddEquiv.symm_apply_apply, AddEquiv.toEquiv_eq_coe,
    AddEquiv.coe_toEquiv] using hc

end AlgebraicGeometry.ComplexPoint
