/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.SmoothPair.CoclassSection

/-!
# The global exactly normalized smooth-support coclass section

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.SmoothPair.CoclassSection`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular
open TopCat.Presheaf

namespace AlgebraicGeometry.ComplexPoint

variable {X Y : Over (Spec ↧ℂ)}
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

/-- The descended section restricts to the normalized section on each chart. -/
@[simp]
theorem smoothClosedSupportCoclassSection_restrict_chart (z : ComplexPoint Y) :
    (smoothClosedSupportCoclassSheaf i m d).obj.map
      (homOfLE (show smoothClosedSupportChartOpen i m d z ≤ ⊤ from le_top)).op
      (smoothClosedSupportCoclassSection i m d) =
        smoothClosedSupportChartSheafSection i m d z :=
  (existsUnique_smoothClosedSupportCoclassSection i m d).choose_spec.1.1 z

/-- The descended section restricts to zero off the support. -/
@[simp]
theorem smoothClosedSupportCoclassSection_restrict_compl :
    (smoothClosedSupportCoclassSheaf i m d).obj.map
      (homOfLE (show
        (⟨(Set.range (Point.map i))ᶜ,
          (isClosed_range_map_of_closedImmersion i).isOpen_compl⟩ :
            Opens (ComplexPoint X)) ≤ ⊤ from le_top)).op
      (smoothClosedSupportCoclassSection i m d) = 0 :=
  (existsUnique_smoothClosedSupportCoclassSection i m d).choose_spec.1.2

/-- On a chart, the global germ is the germ of its normalized chart section. -/
theorem smoothClosedSupportCoclassSection_germ_eq_chart
    (z : ComplexPoint Y) (x : ComplexPoint X)
    (hx : x ∈ smoothClosedSupportChartOpen i m d z) :
    (smoothClosedSupportCoclassSheaf i m d).presheaf.Γgerm x
      (smoothClosedSupportCoclassSection i m d) =
        (smoothClosedSupportCoclassSheaf i m d).presheaf.germ
          (smoothClosedSupportChartOpen i m d z) x hx
          (smoothClosedSupportChartSheafSection i m d z) := by
  rw [← (smoothClosedSupportCoclassSheaf i m d).presheaf.Γgerm_res_apply
    (i := homOfLE (show smoothClosedSupportChartOpen i m d z ≤ ⊤ from le_top)) x hx,
    smoothClosedSupportCoclassSection_restrict_chart]

/-- Outside the support, the descended section has zero germ. -/
theorem smoothClosedSupportCoclassSection_germ_eq_zero
    (x : ComplexPoint X) (hxS : x ∉ Set.range (Point.map i)) :
    (smoothClosedSupportCoclassSheaf i m d).presheaf.Γgerm x
      (smoothClosedSupportCoclassSection i m d) = 0 := by
  let U : Opens (ComplexPoint X) :=
    ⟨(Set.range (Point.map i))ᶜ, (isClosed_range_map_of_closedImmersion i).isOpen_compl⟩
  rw [← (smoothClosedSupportCoclassSheaf i m d).presheaf.Γgerm_res_apply
    (i := homOfLE (show U ≤ ⊤ from le_top)) x hxS,
    smoothClosedSupportCoclassSection_restrict_compl, map_zero]

end AlgebraicGeometry.ComplexPoint
