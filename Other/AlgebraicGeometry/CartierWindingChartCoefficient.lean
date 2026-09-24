/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CartierWindingChartFrame

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open AlgebraicTopology.Singular

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace AlgebraicGeometry.ComplexPoint

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
local instance coefficientTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology
attribute [local instance] isNoetherian_of_isProjective

variable {c : Scheme.CartierData X.left} {x : X.left} {q : ComplexPoint X}
  {d : ℕ} [SmoothOfRelativeDimension d X.hom]
  (ch : ChernWindingChart X c x d 1 q)

/-- The local and global support pairs agree after restricting to the chart. -/
lemma ChernWindingChart.puncturedSupportPair_eq :
    ChernWinding.supportPair (ch.carrier : Set (ComplexPoint X))
        (((ch.punctured : Opens (ComplexPoint X)) : Set (ComplexPoint X))ᶜ) =
      ChernWinding.supportPair (ch.carrier : Set (ComplexPoint X))
        (cycleComponentSupport X x) := by
  change TopPair.ofSubset (X := TopCat.of (ch.carrier : Set (ComplexPoint X)))
      {w : (ch.carrier : Set (ComplexPoint X)) |
        (w : ComplexPoint X) ∉ (((ch.punctured : Opens (ComplexPoint X)) : Set
          (ComplexPoint X))ᶜ)} =
    TopPair.ofSubset (X := TopCat.of (ch.carrier : Set (ComplexPoint X)))
      {w : (ch.carrier : Set (ComplexPoint X)) |
        (w : ComplexPoint X) ∉ cycleComponentSupport X x}
  congr 1
  ext w
  simp [ChernWindingChart.punctured, cycleComponentAnalyticClosedSupport]

/-- The chart puncture lies in the complement of the Cartier bad locus. -/
lemma ChernWindingChart.punctured_le_goodComplement :
    ch.punctured ≤ (analyticClosedSupport X (badLocus c)).compl := by
  intro y hy
  change ¬ ¬ Nonempty (c.UnitDatum (Point.underlying y))
  exact not_not_intro ⟨ch.localForm.toUnitDatum _ (ch.punctured_le_basicOpen hy)⟩

/-- On a nonzero component, the good complement and the chart puncture agree. -/
lemma ChernWindingChart.inf_goodComplement_eq_punctured (hx : c.divisor x ≠ 0) :
    ch.carrier ⊓ (analyticClosedSupport X (badLocus c)).compl = ch.punctured := by
  apply le_antisymm
  · intro y hy
    refine ⟨hy.1, ?_⟩
    intro hyS
    exact hy.2 (closure_subset_badLocus c x hx hyS)
  · exact le_inf ch.punctured_le ch.punctured_le_goodComplement

lemma ChernWindingChart.cartierUnit_winding_eq_divisor_smul_coclass
    (hx : coheight x = ((1 : ℕ) : ℕ∞))
    (hb : ch.HasTrivialUnitWinding)
    (hc : ch.NormalizesCoclass hx) :
    ch.winding ch.cartierUnit =
      (c.divisor x) •
        (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
          (cycleComponentSupport X x) (2 * 1 : ℕ)).obj.map (homOfLE ch.le).op
          (cycleComponentSmoothSupportCoclassSection X x hx) := by
  rw [ch.winding_cartierUnit hb, hc]

end AlgebraicGeometry.ComplexPoint
