import Other.AlgebraicGeometry.AnalyticIteratedTransitionTwo

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec (CommRingCat.of ℂ)))

example (U : Opens (TopCat.of (ComplexPoint X))) :
    analyticOpenFreeAbelianMap X (𝟙 U) = 𝟙 _ := by
  unfold analyticOpenFreeAbelianMap
  simp
  change (presheafToSheaf (Opens.grothendieckTopology
      (TopCat.of (ComplexPoint X))) AddCommGrpCat).map (𝟙 _) =
    𝟙 ((presheafToSheaf (Opens.grothendieckTopology
      (TopCat.of (ComplexPoint X))) AddCommGrpCat).obj _)
  exact (presheafToSheaf (Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))) AddCommGrpCat).map_id _

example (U V : Opens (TopCat.of (ComplexPoint X)))
    (hcover : U ⊔ V = ⊤) :
    analyticRelativeCoverMayerVietorisSquare X U V ⊤ le_top le_top hcover =
      analyticCoverMayerVietorisSquare X U V hcover := by
  rfl

end AlgebraicGeometry.ComplexPoint
