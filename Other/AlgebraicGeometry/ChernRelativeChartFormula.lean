/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernRelativeClassGeneric

/-!
# The chart formula: the correct quantifiers

`HasRelativeChernChartFormulaGeneric` of
[`ChernRelativeClassGeneric.lean`](ChernRelativeClassGeneric.lean) quantifies **universally** over
the closed set `Z'`, the frame `ℓ` over its analytic complement, and the comparison datum `cmp`.
As stated it is **false**, for the same reason as the `ℙ¹` counterexample that forced
`HasChernLocalModel` to be existential in its lift.

* *The frame is not unique.* Two lifts `ℓ₁, ℓ₂` of the constant integer section `1` over
  `Ω' := X^an ∖ (Z')^an` differ by a unit `w ∈ 𝒪ˣ(Ω')`, and the two relative first Chern classes
  differ by the image of the class of `w` under the connecting maps. Concretely, for `X = ℙ¹`,
  `L = 𝒪`, the rational section `s = z` and `D = [0] − [∞]`, one has `Ω' = ℙ¹ ∖ {0, ∞}` and
  `w = z ∈ 𝒪ˣ(Ω')` has winding number `1` around `0`; replacing `ℓ` by `ℓ + ι(w)` changes the
  local multiplicities from `(1, −1)` to `(2, −2)`. Since `w` does *not* extend to a unit across
  `0`, the extra unit `u` allowed by `ChernWindingChart.ComputesClass` cannot absorb the change.
  So the conclusion fails for one of the two frames.

* *The comparison datum is not unique.* `RelativeChernComparison` is produced by the axiom TR3,
  which determines its filler only up to the image of
  `Hom_{D(X)}(cone(η), Rj_*ℚ_{Ω'}[1])`; concretely, two data `cmp₁, cmp₂` give relative Chern
  classes differing by a class in the image of `H²(Ω', ℚ) → H²_{(Z')^an}(X^an, ℚ)`, which is not
  zero in general (in the `ℙ¹` example that image is exactly the ambiguity `(1, −1)ℚ`).

This file therefore restates the obligation with `Z'`, `ℓ` and `cmp` quantified **existentially**
— `HasRelativeChernChartFormulaExists` — and re-proves the two reductions. Nothing is lost: the
existential form is implied by the universal one
(`hasRelativeChernChartFormulaExists_of_generic`), and it is what the reduction actually consumes,
because `hasChernWindingNaturality_of_generic` chooses `Z'`, `ℓ` (from
`hasComplementFrameOffCodimTwo`) and `cmp` (from `nonempty_relativeChernComparison`) itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open CategoryTheory.Localization

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernRelativeChartFormulaTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

/-- The analytic support of the divisor is contained in the analytic support of any Zariski-closed
set containing the Zariski support of its components. -/
theorem cycleAnalyticClosedSupport_le_of_componentsZariskiSupport_le
    (c : Scheme.CartierData X.left) (Z' : Closeds X.left)
    (h : componentsZariskiSupport X (cycleComponents X c.divisor) ≤ Z') :
    cycleAnalyticClosedSupport X c.divisor ≤ analyticClosedSupport X Z' := by
  rw [show cycleAnalyticClosedSupport X c.divisor =
      analyticClosedSupport X (componentsZariskiSupport X (cycleComponents X c.divisor)) from
    (analyticClosedSupport_componentsZariskiSupport X _).symm]
  exact analyticClosedSupport_le_of_le X h

/-- **Obligation: the chart formula for the canonical relative first Chern class, with the
correct quantifiers.**

There *exist* a closed set `Z'` containing the divisor with all further points of codimension at
least two, a frame `ℓ` of the bundle over `X^an ∖ (Z')^an`, and a comparison datum `cmp`, such
that the relative first Chern class they cut out computes the divisor multiplicities on every
normalised winding chart.

The existential quantifiers on `ℓ` and `cmp` are **forced**: see the file docstring for the `ℙ¹`
counterexample to the universally quantified form. They cost nothing, because the reduction below
chooses `Z'`, `ℓ` and `cmp` itself. -/
def HasRelativeChernChartFormulaExists : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∀ c : Scheme.CartierData X.left, c.Represents L →
      ∃ (Z' : Closeds X.left)
        (_ : componentsZariskiSupport X (cycleComponents X c.divisor) ≤ Z')
        (_ : ∀ z ∈ Z', z ∉ componentsZariskiSupport X (cycleComponents X c.divisor) →
          (2 : ℕ∞) ≤ coheight z)
        (hle : cycleAnalyticClosedSupport X c.divisor ≤ analyticClosedSupport X Z')
        (ℓ : E.middle.obj.obj (op ((analyticClosedSupport X Z').compl)))
        (hℓ : E.projection.hom.app (op ((analyticClosedSupport X Z').compl)) ℓ =
          (constantIntegerSheaf X).obj.map
            (homOfLE (le_top : (analyticClosedSupport X Z').compl ≤ ⊤)).op
            HolomorphicUnitExtension.integerOneSection)
        (cmp : RelativeChernComparison X (dim X.left) (analyticClosedSupport X Z').compl),
        ∀ β : SupportedInjectiveHomology X (cycleAnalyticClosedSupport X c.divisor)
            (2 * ((1 : ℕ) : ℤ)),
          enlargeSupportedInjectiveHomology X hle (2 * ((1 : ℕ) : ℤ)) β =
              relativeChernSupportedClassOnClosed (analyticClosedSupport X Z') E ℓ hℓ cmp →
            ∀ γ : ∀ x : X.left, SupportedInjectiveHomology X
              (cycleComponentAnalyticClosedSupport X x) (2 * ((1 : ℕ) : ℤ)),
            β = ∑ x ∈ cycleComponents X c.divisor,
                componentContribution X (cycleComponents X c.divisor) x (2 * ((1 : ℕ) : ℤ)) (γ x) →
            ∀ x ∈ cycleComponents X c.divisor, ∀ hx : coheight x = ((1 : ℕ) : ℕ∞),
            ∀ (q : ComplexPoint X) (ch : ChernWindingChart X c x (dim X.left) 1 q),
              ch.HasTrivialUnitWinding → ch.NormalizesCoclass hx →
              ch.ComputesClass (c.divisor x)
                ((cycleComponentSupportedClassNormalizationIso X x (d := dim X.left) hx).hom (γ x))

set_option maxHeartbeats 1000000 in
/-- The existential form is implied by the universal one, so restating the obligation this way
loses nothing: the frame is supplied by `hasComplementFrameOffCodimTwo` and the comparison datum
by `nonempty_relativeChernComparison`. -/
theorem hasRelativeChernChartFormulaExists_of_generic
    (h : HasRelativeChernChartFormulaGeneric X) : HasRelativeChernChartFormulaExists X := by
  intro E L hL iso c hc
  obtain ⟨Z', hcontain, hcodZ, ℓ, hℓ⟩ := hasComplementFrameOffCodimTwo X E L hL iso c hc
  have hZle : componentsZariskiSupport X (cycleComponents X c.divisor) ≤ Z' := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := (mem_componentsZariskiSupport X).mp hz
    exact hcontain y ((mem_cycleComponents_iff X c.divisor y).mp hy) hzy
  have hcod : ∀ z ∈ Z', z ∉ componentsZariskiSupport X (cycleComponents X c.divisor) →
      (2 : ℕ∞) ≤ coheight z := by
    intro z hz hnot
    refine hcodZ z hz fun y hy hzy => hnot ?_
    exact (mem_componentsZariskiSupport X).mpr
      ⟨y, (mem_cycleComponents_iff X c.divisor y).mpr hy, hzy⟩
  obtain ⟨cmp⟩ := nonempty_relativeChernComparison X (dim X.left)
    (analyticClosedSupport X Z').compl
  exact ⟨Z', hZle, hcod,
    cycleAnalyticClosedSupport_le_of_componentsZariskiSupport_le X c Z' hZle, ℓ, hℓ, cmp,
    fun β hβ γ hγ x hxs hx q ch hb hcn =>
      h c E Z' _ ℓ hℓ cmp β hβ γ hγ x hxs hx q ch hb hcn⟩

set_option maxHeartbeats 1000000 in
/-- **The reduction, with the corrected quantifiers.** -/
theorem hasChernWindingNaturality_of_chartFormulaExists
    (h : HasRelativeChernChartFormulaExists X) : HasChernWindingNaturality X := by
  intro E L hL iso c hc
  obtain ⟨Z', hZle, hcod, hle, ℓ, hℓ, cmp, hform⟩ := h E L hL iso c hc
  obtain ⟨β, hβ⟩ := exists_enlarge_of_analyticClosedSupport_eq X (enlargeSurjectiveCodimTwo X)
    (componentsZariskiSupport X (cycleComponents X c.divisor)) Z' hZle hcod
    (cycleAnalyticClosedSupport X c.divisor) (analyticClosedSupport X Z')
    (analyticClosedSupport_componentsZariskiSupport X (cycleComponents X c.divisor)) rfl hle
    (relativeChernSupportedClassOnClosed (analyticClosedSupport X Z') E ℓ hℓ cmp)
  refine ⟨β, ?_, ?_⟩
  · rw [← supportedInjectiveToAmbient_enlarge X hle (2 * ((1 : ℕ) : ℤ)) β, hβ]
    exact supportedInjectiveToAmbient_relativeChernSupportedClassOnClosed
      (analyticClosedSupport X Z') E ℓ hℓ cmp
  · intro γ hγ x hxs hx q ch hb hcn
    exact hform β hβ γ hγ x hxs hx q ch hb hcn

set_option maxHeartbeats 1000000 in
/-- **Step 4 of `docs/DIVISOR_HANDOFF.md` §4.3, with the corrected quantifiers.** -/
theorem hasDivisorClassOfSomeCartierData_of_chartFormulaExists
    (hcharts : HasNormalizedWindingCharts X) (h : HasRelativeChernChartFormulaExists X) :
    HasDivisorClassOfSomeCartierData X :=
  hasDivisorClassOfSomeCartierData_of_supportedChernLift_of_localModel X
    (hasChernLocalModel_of_winding X hcharts
      (hasChernWindingNaturality_of_chartFormulaExists X h))

end AlgebraicGeometry.ComplexPoint
