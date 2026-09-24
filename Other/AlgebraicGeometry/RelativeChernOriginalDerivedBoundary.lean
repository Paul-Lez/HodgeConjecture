/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.RelativeChernOriginalBoundary
public import Other.AlgebraicGeometry.RelativeChernFrameLocalVanishing

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CochainComplex.HomComplex

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (E : HolomorphicUnitExtension X d)
variable (U : Opens (TopCat.of (ComplexPoint X)))
  (ℓU : E.middle.obj.obj (op U))
  (hℓU : E.projection.hom.app (op U) ℓU =
    (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : U ≤ ⊤)).op
      HolomorphicUnitExtension.integerOneSection)
local instance localAmbient : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _
local instance localOpen : HasDerivedCategory
    (TopCat.Sheaf AddCommGrpCat (TopCat.of U)) := HasDerivedCategory.standard _

include hℓU in
lemma restrict_coneToInteger_inv_comp_factors_eq_restrictedConeSection :
    (restrictToOpen X U).mapDerivedCategory.map
        (Localization.isoOfHom DerivedCategory.Q (analyticQuasiIsomorphisms X)
          E.coneToInteger (by change QuasiIso _; exact E.quasiIso_coneToInteger)).inv ≫
      (restrictToOpen X U).mapDerivedCategoryFactors.hom.app E.inclusionCone =
      (restrictToOpen X U).mapDerivedCategoryFactors.hom.app
        ((analyticSingleFunctor X).obj (𝓒(↧(ComplexPoint X); ℤ))) ≫
      DerivedCategory.Q.map (restrictedConeSection X d E U ℓU) := by
  let F := restrictToOpen X U
  let H := F.mapHomologicalComplex (.up ℤ)
  let S := restrictedConeSection X d E U ℓU
  let C := E.coneToInteger
  let e := Localization.isoOfHom DerivedCategory.Q (analyticQuasiIsomorphisms X)
    C (by change QuasiIso _; exact E.quasiIso_coneToInteger)
  have hs := restrictedConeSection_comp_coneToInteger X d E U ℓU hℓU
  have hq := congrArg DerivedCategory.Q.map hs
  have hn := F.mapDerivedCategoryFactors_hom_naturality C
  have hC : DerivedCategory.Q.map (H.map C) =
      F.mapDerivedCategoryFactors.inv.app E.inclusionCone ≫
      F.mapDerivedCategory.map (DerivedCategory.Q.map C) ≫
        F.mapDerivedCategoryFactors.hom.app ((analyticSingleFunctor X).obj
          (𝓒(↧(ComplexPoint X); ℤ))) := by
    change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map C) = _
    apply (cancel_epi
      (F.mapDerivedCategoryFactors.hom.app E.inclusionCone)).1
    rw [← Category.assoc, F.mapDerivedCategoryFactors.hom_inv_id_app,
      Category.id_comp]
    exact hn.symm
  have : IsIso (DerivedCategory.Q.map C) := by
    exact Localization.inverts DerivedCategory.Q (analyticQuasiIsomorphisms X) C
      (by change QuasiIso C; exact E.quasiIso_coneToInteger)
  have : IsIso (F.mapDerivedCategory.map (DerivedCategory.Q.map C)) := by
    infer_instance
  let : IsIso (DerivedCategory.Q.map (H.map C)) := by
    rw [hC]
    infer_instance
  apply (cancel_mono (DerivedCategory.Q.map (H.map C))).1
  simp only [Category.assoc]
  change F.mapDerivedCategory.map e.inv ≫
      F.mapDerivedCategoryFactors.hom.app E.inclusionCone ≫
      DerivedCategory.Q.map (H.map C) = _
  rw [← hn]
  rw [← Category.assoc, ← F.mapDerivedCategory.map_comp]
  have he : e.inv ≫ DerivedCategory.Q.map C = 𝟙 _ := by
    exact e.inv_hom_id
  rw [he, F.mapDerivedCategory.map_id, Category.id_comp]
  rw [← CategoryTheory.Functor.map_comp, hq]
  rw [CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

end AlgebraicGeometry.ComplexPoint
