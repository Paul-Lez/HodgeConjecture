/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernRelativeSupportUnit

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open HomologicalComplex
open AlgebraicTopology.Singular
open AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
local instance closedSupportUnitTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology
attribute [local instance] isNoetherian_of_isProjective
variable {X d}

set_option maxHeartbeats 1000000 in
/-- Transport normalized unit winding across the double-complement support equality. -/
lemma normalizedWindingUnit_supportMap_doubleComplement
    [SmoothOfRelativeDimension d X.hom]
    (S : Closeds (ComplexPoint X))
    (W : Opens (TopCat.of (ComplexPoint X)))
    (u : (holomorphicUnitSheaf X d).obj.obj (op (W ⊓ S.compl))) :
    let S₀ : Closeds (ComplexPoint X) :=
      ⟨((S.compl : Set (ComplexPoint X))ᶜ), S.compl.isOpen.isClosed_compl⟩
    let hS : S₀ = S := by
      apply Closeds.ext
      change ((S.compl : Set (ComplexPoint X))ᶜ) = (S : Set (ComplexPoint X))
      exact compl_compl _
    let h₀ : S₀.compl ≤ S.compl := by
      intro y hy hyS
      exact hy (hS.ge hyS)
    let u₀ := (holomorphicUnitSheaf X d).obj.map
      (homOfLE (inf_le_inf_left W h₀)).op u
    (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hS.le) (2 : ℤ)).hom.app
        (op W)
        ((complexSupportInjectiveCohomologySheafIsoRelative X S₀ 2).inv.hom.app (op W)
          (windingSheafHom (hasWindingPeriods X d W S₀) u₀)) =
      (complexSupportInjectiveCohomologySheafIsoRelative X S 2).inv.hom.app (op W)
        (windingSheafHom (hasWindingPeriods X d W S) u) := by
  dsimp only
  let S₀ : Closeds (ComplexPoint X) :=
    ⟨((S.compl : Set (ComplexPoint X))ᶜ), S.compl.isOpen.isClosed_compl⟩
  let hS : S₀ = S := by
    apply Closeds.ext
    change ((S.compl : Set (ComplexPoint X))ᶜ) = (S : Set (ComplexPoint X))
    exact compl_compl _
  let h₀ : S₀.compl ≤ S.compl := by
    intro y hy hyS
    exact hy (hS.ge hyS)
  let h₁ : S.compl ≤ S₀.compl := by
    intro y hy hy₀
    exact hy (hS.le hy₀)
  let u₀ := (holomorphicUnitSheaf X d).obj.map
    (homOfLE (inf_le_inf_left W h₀)).op u
  apply normalizedWindingUnit_supportMap (X := X) hS.le W u₀ u
  change u = (holomorphicUnitSheaf X d).obj.map
      (homOfLE (inf_le_inf_left W h₁)).op
      ((holomorphicUnitSheaf X d).obj.map
        (homOfLE (inf_le_inf_left W h₀)).op u)
  rw [← ConcreteCategory.comp_apply]
  rw [← (holomorphicUnitSheaf X d).obj.map_comp]
  have hmap :
      (homOfLE (inf_le_inf_left W h₀)).op ≫
          (homOfLE (inf_le_inf_left W h₁)).op = 𝟙 _ := by
    apply Subsingleton.elim
  rw [hmap]
  simp

end AlgebraicGeometry.ComplexPoint
