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
@[simp] lemma forgetSupport_supportedClassTransport {Z Z' : Set (ComplexPoint X)} (h : Z = Z')
    (n : ℤ) (β : RationalCohomologyWithSupport X Z n) :
    forgetSupport X Z' n (supportedClassTransport X h n β) = forgetSupport X Z n β := by
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
          (constantIntegerSheaf X).obj.map (homOfLE (le_top :
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
      (constantIntegerSheaf X).obj.map
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
      (constantIntegerSheaf X).obj.map
        (homOfLE (le_top : divisorComplementOpen c ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection)
    (cmp : RelativeChernComparison X (dim X.left) (divisorComplementOpen c)) :
    SupportedInjectiveHomology X (cycleAnalyticClosedSupport X c.divisor) (2 * ((1 : ℕ) : ℤ)) :=
  rationalSupportAddEquivSupportedInjectiveHomology X
    ((cycleAnalyticClosedSupport X c.divisor : Closeds (ComplexPoint X)) :
      Set (ComplexPoint X))
    (cycleAnalyticClosedSupport X c.divisor).isClosed (2 * ((1 : ℕ) : ℤ))
    (relativeChernClassOnSupport c E ℓ hℓ cmp)

set_option maxHeartbeats 1000000 in
/-- **The relative first Chern class is a lift of the rational first Chern class.** This is the
first clause of `HasChernLocalModel` / `HasChernWindingNaturality`, for the canonical witness. -/
theorem supportedInjectiveToAmbient_relativeChernSupportedClass
    (c : Scheme.CartierData X.left) (E : HolomorphicUnitExtension X (dim X.left))
    (ℓ : E.middle.obj.obj (op (divisorComplementOpen c)))
    (hℓ : E.projection.hom.app (op (divisorComplementOpen c)) ℓ =
      (constantIntegerSheaf X).obj.map
        (homOfLE (le_top : divisorComplementOpen c ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection)
    (cmp : RelativeChernComparison X (dim X.left) (divisorComplementOpen c)) :
    supportedInjectiveToAmbient X (cycleAnalyticClosedSupport X c.divisor) (2 * ((1 : ℕ) : ℤ))
        (relativeChernSupportedClass c E ℓ hℓ cmp) =
      rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * ((1 : ℕ) : ℤ))
        (integralToRationalCohomology X 2 E.firstChernClass) := by
  have h := rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport X
    ((cycleAnalyticClosedSupport X c.divisor : Closeds (ComplexPoint X)) :
      Set (ComplexPoint X))
    (cycleAnalyticClosedSupport X c.divisor).isClosed 2
    (relativeChernClassOnSupport c E ℓ hℓ cmp)
  refine h.symm.trans (congrArg _ ?_)
  rw [relativeChernClassOnSupport, forgetSupport_supportedClassTransport]
  exact E.forgetSupport_relativeChernClass _ ℓ hℓ cmp

/-! ### The remaining obligation, and the reduction -/

variable (X)

/-- **Obligation: the chart formula for the relative first Chern class.**

On every normalised winding chart, the component piece of the *canonical* relative first Chern
class is the winding class of the local equation of the bundle. This is `(a)` of
`Other/AlgebraicGeometry/ChernLocalModelWinding.lean` with the existential lift `β` replaced by
the explicit witness `relativeChernSupportedClass`: no quantifier over lifts remains, so the
statement is not vacuous and not refutable by the `ℙ¹` example. -/
def HasRelativeChernChartFormula : Prop :=
  ∀ (c : Scheme.CartierData X.left) (E : HolomorphicUnitExtension X (dim X.left))
    (ℓ : E.middle.obj.obj (op (divisorComplementOpen c)))
    (hℓ : E.projection.hom.app (op (divisorComplementOpen c)) ℓ =
      (constantIntegerSheaf X).obj.map
        (homOfLE (le_top : divisorComplementOpen c ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection)
    (cmp : RelativeChernComparison X (dim X.left) (divisorComplementOpen c))
    (γ : ∀ x : X.left, SupportedInjectiveHomology X
      (cycleComponentAnalyticClosedSupport X x) (2 * ((1 : ℕ) : ℤ))),
    relativeChernSupportedClass c E ℓ hℓ cmp =
        ∑ x ∈ cycleComponents X c.divisor,
          componentContribution X (cycleComponents X c.divisor) x (2 * ((1 : ℕ) : ℤ)) (γ x) →
      ∀ x ∈ cycleComponents X c.divisor, ∀ hx : coheight x = ((1 : ℕ) : ℕ∞),
      ∀ (q : ComplexPoint X) (ch : ChernWindingChart X c x (dim X.left) 1 q),
        ch.HasTrivialUnitWinding → ch.NormalizesCoclass hx →
        ch.ComputesClass (c.divisor x)
          ((cycleComponentSupportedClassNormalizationIso X x (d := dim X.left) hx).hom (γ x))

set_option maxHeartbeats 1000000 in
/-- **The reduction.** The frame off the divisor together with the chart formula for the
canonical relative first Chern class give the naturality obligation
`HasChernWindingNaturality X`, hence — with `hasChernLocalModel_of_winding` and
`hasDivisorClassOfSomeCartierData_of_supportedChernLift_of_localModel` — the remaining obligation
of `docs/DIVISOR_HANDOFF.md` §3.

The point is that the *existential* quantifier over the supported lift in
`HasChernWindingNaturality` is discharged here, by the canonical relative class: what is left is a
statement about one explicitly constructed class. -/
theorem hasChernWindingNaturality_of_relativeChernChartFormula
    (hframe : HasComplementFrame X) (hchart : HasRelativeChernChartFormula X) :
    HasChernWindingNaturality X := by
  intro E L hL iso c hc
  obtain ⟨ℓ, hℓ⟩ := hframe E L hL iso c hc
  obtain ⟨cmp⟩ := nonempty_relativeChernComparison X (dim X.left) (divisorComplementOpen c)
  exact ⟨relativeChernSupportedClass c E ℓ hℓ cmp,
    supportedInjectiveToAmbient_relativeChernSupportedClass c E ℓ hℓ cmp,
    fun γ hγ x hxs hx q ch hb hcn => hchart c E ℓ hℓ cmp γ hγ x hxs hx q ch hb hcn⟩

set_option maxHeartbeats 1000000 in
/-- **Step 4 of `docs/DIVISOR_HANDOFF.md` §4.3, in terms of the relative first Chern class.**
The frame off the divisor, normalised winding charts, and the chart formula for the canonical
relative class together give the remaining obligation `HasDivisorClassOfSomeCartierData X`. -/
theorem hasDivisorClassOfSomeCartierData_of_relativeChernChartFormula
    (hframe : HasComplementFrame X) (hcharts : HasNormalizedWindingCharts X)
    (hchart : HasRelativeChernChartFormula X) :
    HasDivisorClassOfSomeCartierData X :=
  hasDivisorClassOfSomeCartierData_of_supportedChernLift_of_localModel X
    (hasChernLocalModel_of_winding X hcharts
      (hasChernWindingNaturality_of_relativeChernChartFormula X hframe hchart))

end AlgebraicGeometry.ComplexPoint
