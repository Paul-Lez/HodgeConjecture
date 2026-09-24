/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CartierFrameLift
public import Other.AlgebraicGeometry.ChernRelativeClassGeneric

/-!
# The compatible lift over the bad-locus complement
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open CategoryTheory.Localization

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernRelativeCanonicalLiftTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable {X}

omit [Smooth X.hom] in
theorem componentsZariskiSupport_le_badLocus (c : Scheme.CartierData X.left) :
    componentsZariskiSupport X (cycleComponents X c.divisor) ≤ badLocus c := by
  intro z hz
  obtain ⟨y, hy, hzy⟩ := (mem_componentsZariskiSupport X).mp hz
  exact closure_subset_badLocus c y ((mem_cycleComponents_iff X c.divisor y).mp hy) hzy

theorem badLocus_codimension_two_off_components (c : Scheme.CartierData X.left) :
    ∀ z ∈ badLocus c,
      z ∉ componentsZariskiSupport X (cycleComponents X c.divisor) →
        (2 : ℕ∞) ≤ coheight z := by
  intro z hz hnot
  refine two_le_coheight_of_mem_badLocus c z hz ?_
  intro y hy hzy
  apply hnot
  exact (mem_componentsZariskiSupport X).mpr
    ⟨y, (mem_cycleComponents_iff X c.divisor y).mpr hy, hzy⟩

theorem cycleAnalyticClosedSupport_le_badLocus (c : Scheme.CartierData X.left) :
    cycleAnalyticClosedSupport X c.divisor ≤ analyticClosedSupport X (badLocus c) :=
  cycleAnalyticClosedSupport_le_analyticClosedSupport X c (badLocus c) fun y hy =>
    closure_subset_badLocus c y hy

set_option maxHeartbeats 1000000 in
/-- The good-locus lift and its supported class, with compatibility retained. -/
theorem exists_compatible_global_lift_and_supported_class
    (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules)
    (e : (moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules)
    (c : Scheme.CartierData X.left) (hc : c.Represents L) :
    ∃ (g : ∀ i : c.ι, Γ(L, c.opens i))
      (hg : ∀ i, Scheme.Modules.Generates (g i))
      (_hrep : c.RepresentsWith L g),
      ∃ (ℓ : E.middle.obj.obj
          (op ((analyticClosedSupport X (badLocus c)).compl)))
        (hℓ : E.projection.hom.app
          (op ((analyticClosedSupport X (badLocus c)).compl)) ℓ =
          (𝓒(↧(ComplexPoint X); ℤ)).obj.map
            (homOfLE (le_top : (analyticClosedSupport X (badLocus c)).compl ≤ ⊤)).op
            HolomorphicUnitExtension.integerOneSection),
        IsCartierComplementLift g E e hg
          ((analyticClosedSupport X (badLocus c)).compl) ℓ ∧
        ∃ (cmp : RelativeChernComparison X (dim X.left)
            ((analyticClosedSupport X (badLocus c)).compl))
          (β : SupportedInjectiveHomology X
            (cycleAnalyticClosedSupport X c.divisor) (2 : ℤ)),
          enlargeSupportedInjectiveHomology X
              (cycleAnalyticClosedSupport_le_badLocus (X := X) c) (2 : ℤ) β =
              relativeChernSupportedClassOnClosed
                (analyticClosedSupport X (badLocus c)) E ℓ hℓ cmp ∧
            supportedInjectiveToAmbient X
                (cycleAnalyticClosedSupport X c.divisor) (2 : ℤ) β =
              rationalCohomologyAddEquivAmbientInjectiveHomology X 2
                (integralToRationalCohomology X 2 E.firstChernClass) := by
  obtain ⟨g, hg, hrep⟩ := hc
  let Ω : Opens (TopCat.of (ComplexPoint X)) :=
    (analyticClosedSupport X (badLocus c)).compl
  have hΩ : ∀ z ∈ Ω, Point.underlying z ∈ goodLocus c := by
    intro z hz
    exact not_not.mp hz
  have hΩc : Ω ≤ divisorComplementOpen c := by
    intro z hz hdiv
    exact hz (cycleAnalyticClosedSupport_le_badLocus (X := X) c hdiv)
  obtain ⟨ℓ, hℓ', hcompat⟩ := exists_lift_of_goodLocus_with_localFormula
    g E e hg hrep Ω hΩ hΩc
  have hℓ : E.projection.hom.app (op Ω) ℓ =
      (𝓒(↧(ComplexPoint X); ℤ)).obj.map
        (homOfLE (le_top : Ω ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection := by
    exact hℓ'
  obtain ⟨cmp⟩ := nonempty_relativeChernComparison X (dim X.left) Ω
  have hZle : componentsZariskiSupport X (cycleComponents X c.divisor) ≤ badLocus c :=
    componentsZariskiSupport_le_badLocus (X := X) c
  have hcod := badLocus_codimension_two_off_components (X := X) c
  have hSeq : analyticClosedSupport X
      (componentsZariskiSupport X (cycleComponents X c.divisor)) =
      cycleAnalyticClosedSupport X c.divisor :=
    analyticClosedSupport_componentsZariskiSupport X (cycleComponents X c.divisor)
  obtain ⟨β, hβ⟩ := exists_enlarge_of_analyticClosedSupport_eq X
    (enlargeSurjectiveCodimTwo X)
    (componentsZariskiSupport X (cycleComponents X c.divisor)) (badLocus c) hZle hcod
    (cycleAnalyticClosedSupport X c.divisor) (analyticClosedSupport X (badLocus c))
    hSeq rfl (cycleAnalyticClosedSupport_le_badLocus (X := X) c)
    (relativeChernSupportedClassOnClosed (analyticClosedSupport X (badLocus c)) E ℓ hℓ cmp)
  refine ⟨g, hg, hrep, ℓ, ?_, hcompat, cmp, β, hβ, ?_⟩
  · simpa only [Ω] using hℓ
  · rw [← supportedInjectiveToAmbient_enlarge X
      (cycleAnalyticClosedSupport_le_badLocus (X := X) c) (2 : ℤ) β, hβ]
    exact supportedInjectiveToAmbient_relativeChernSupportedClassOnClosed
      (analyticClosedSupport X (badLocus c)) E ℓ hℓ cmp

end AlgebraicGeometry.ComplexPoint
