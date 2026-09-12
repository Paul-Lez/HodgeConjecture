/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SmoothSupportCoclassSection

open CategoryTheory Limits TopologicalSpace Topology Opposite
open AlgebraicTopology.Singular

@[expose] public noncomputable section

namespace AlgebraicGeometry.ComplexPoint

section GeneralOpenTransport

variable (X Y : Over (Spec (.of ℂ)))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]
  {M : TopCat.{0}} (f : TopCat.of (ComplexPoint X) ⟶ M)
  (hf : IsOpenEmbedding f) (S : Set M)
  (hS : f ⁻¹' S = Set.range (Point.map i))

def smoothClosedSupportOpenImageCoclassSection :
  (supportRelativeCohomologySheaf M S (2 * (d - m))).obj.obj (op (hf.functor.obj ⊤)) :=
  supportRelativeCohomologySectionOpenImage f hf S (Set.range (Point.map i)) hS
    (2 * (d - m)) (smoothClosedSupportCoclassSection X Y i m d)


theorem smoothClosedSupportOpenImageCoclassSection_restrict_chart
    (z : ComplexPoint Y) :
    (supportRelativeCohomologySheaf M S (2 * (d - m))).obj.map
      (hf.functor.map (homOfLE (show
        smoothClosedSupportChartOpen X Y i m d z ≤ ⊤ from le_top))).op
      (smoothClosedSupportOpenImageCoclassSection X Y i m d f hf S hS) =
    (supportRelativeCohomologyToSheaf M S (2 * (d - m))).app
      (op (hf.functor.obj (smoothClosedSupportChartOpen X Y i m d z)))
      ((supportRelativeCohomologyPresheafOpenIso f hf S (Set.range (Point.map i)) hS
          (2 * (d - m))).inv.app (op (smoothClosedSupportChartOpen X Y i m d z))
        (smoothClosedSupportChartCoclass X Y i m d z
          (smoothClosedSupportChartOpen X Y i m d z) (le_refl _))) := by
  rw [smoothClosedSupportOpenImageCoclassSection,
    supportRelativeCohomologySectionOpenImage_restrict,
    smoothClosedSupportCoclassSection_restrict_chart]
  exact supportRelativeCohomologySheafOpenIso_unit_apply f hf S (Set.range (Point.map i))
    hS (2 * (d - m)) (smoothClosedSupportChartOpen X Y i m d z) _


end GeneralOpenTransport

end AlgebraicGeometry.ComplexPoint
