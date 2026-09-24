/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicGeometry.Cohomology.SupportSheafConeBoundaryOnOpen

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (Z : Set (ComplexPoint X)) (hZ : IsClosed Z)
  (U V : Opens (TopCat.of (ComplexPoint X))) (j : U ⟶ V)

local instance restrictionNaturalityTopology (X : Over (Spec ↧ℂ)) :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology
local instance restrictionNaturalityDerived (Y : TopCat.{0}) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat Y) := HasDerivedCategory.standard _

/-- The fixed signed inverse and shift commute with restriction to an open subset. -/
lemma supportSheafSection_shift_restrict_naturality
    (t : ((CochainComplex.mappingCone
      (ambientRationalInjectiveRestriction X Z hZ)).homology 1).obj.obj (op V)) :
    let Y := TopCat.of (ComplexPoint X)
    let S := TopCat.Sheaf.supportRestrictionComplexShortComplex Y
      ⟨Zᶜ, hZ.isOpen_compl⟩ (ambientRationalInjectiveComplex X)
    let K := S.X₁
    let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
    let m := supportSheafToAmbientInjectiveCone X Z hZ
    let M := HomologicalComplex.homologyMap m 1
    let L := TopCat.Sheaf.sectionCohomologySheafShiftMap Y K 1 1 2 (by omega)
    let : IsIso M := by
      exact (quasiIsoAt_iff_isIso_homologyMap m 1).mp inferInstance
    (K.homology 2).obj.map j.op
        (-L.hom.app (op V) (inv (M.hom.app (op V)) t)) =
      -L.hom.app (op U)
        (inv (M.hom.app (op U)) ((C.homology 1).obj.map j.op t)) := by
  dsimp only
  let Y := TopCat.of (ComplexPoint X)
  let S := TopCat.Sheaf.supportRestrictionComplexShortComplex Y
    ⟨Zᶜ, hZ.isOpen_compl⟩ (ambientRationalInjectiveComplex X)
  let K := S.X₁
  let C := CochainComplex.mappingCone (ambientRationalInjectiveRestriction X Z hZ)
  let m := supportSheafToAmbientInjectiveCone X Z hZ
  let M := HomologicalComplex.homologyMap m 1
  let L := TopCat.Sheaf.sectionCohomologySheafShiftMap Y K 1 1 2 (by omega)
  let : IsIso M := by
    exact (quasiIsoAt_iff_isIso_homologyMap m 1).mp inferInstance
  let : IsIso (M.hom.app (op U)) := by infer_instance
  let : IsIso (M.hom.app (op V)) := by infer_instance
  let P := inv M.hom ≫ L.hom
  have hP := P.naturality j.op
  have hPt := ConcreteCategory.congr_hom hP t
  simp only [ConcreteCategory.comp_apply] at hPt
  have hPappU := NatIso.isIso_inv_app M.hom (op U)
  have hPappV := NatIso.isIso_inv_app M.hom (op V)
  dsimp only [P] at hPt
  simp only [NatTrans.comp_app] at hPt
  rw [hPappU, hPappV] at hPt
  simp only [ConcreteCategory.comp_apply] at hPt
  simpa only [map_neg] using congrArg Neg.neg hPt.symm

end AlgebraicGeometry.ComplexPoint
