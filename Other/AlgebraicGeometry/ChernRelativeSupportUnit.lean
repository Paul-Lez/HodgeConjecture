/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernRelativeSupportNormalized
public import Other.AlgebraicGeometry.ChernWindingUnitClass
public import Other.AlgebraicGeometry.ChernWindingChartPeriods

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
local instance unitTopology : TopologicalSpace (ComplexPoint X) := Point.analyticTopology
attribute [local instance] isNoetherian_of_isProjective
variable {X d}

set_option maxHeartbeats 1000000 in
lemma normalizedWindingUnit_supportMap
    [SmoothOfRelativeDimension d X.hom]
    {S T : Closeds (ComplexPoint X)} (hST : S ≤ T)
    (W : Opens (TopCat.of (ComplexPoint X)))
    (uS : (holomorphicUnitSheaf X d).obj.obj
      (op (W ⊓ S.compl)))
    (uT : (holomorphicUnitSheaf X d).obj.obj
      (op (W ⊓ T.compl)))
    (huT : uT = (holomorphicUnitSheaf X d).obj.map
      (homOfLE (inf_le_inf_left W (show T.compl ≤ S.compl from
        fun _ hs ht => hs (hST ht)))).op uS) :
    (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hST) (2 : ℤ)).hom.app
        (op W)
        ((complexSupportInjectiveCohomologySheafIsoRelative X S 2).inv.hom.app (op W)
          (windingSheafHom (hasWindingPeriods X d W S) uS)) =
      (complexSupportInjectiveCohomologySheafIsoRelative X T 2).inv.hom.app (op W)
        (windingSheafHom (hasWindingPeriods X d W T) uT) := by
  have hcomp :
      (windingUnitFunction X d W S uS).comp
          (ChernWinding.topMap (TopPair.Hom.snd
            (neighborhoodSupportSupportInclusionPairMap X hST W))) =
        windingUnitFunction X d W T uT := by
    subst uT
    ext y
    rfl
  rw [windingSheafHom_apply, windingSheafHom_apply]
  exact normalizedWinding_supportMap_of_raw (X := X) hST W
    (windingUnitFunction X d W S uS)
    (windingUnitFunction_ne_zero X d W S uS)
    (hasWindingPeriods X d W S uS)
    (windingUnitFunction X d W T uT)
    (windingUnitFunction_ne_zero X d W T uT)
    (hasWindingPeriods X d W T uT) hcomp

end AlgebraicGeometry.ComplexPoint
