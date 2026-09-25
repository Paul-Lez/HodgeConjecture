/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernComponentLocalIsolation
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.OpenRestriction

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

@[expose] public noncomputable section

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
local instance chernComponentSheafIsolationTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology
attribute [local instance] isNoetherian_of_isProjective
variable {X}

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Support enlargement is an isomorphism after restriction where the supports agree. -/
theorem supportedInjectiveComplexMap_restrict_isIso
    {S T : Closeds (ComplexPoint X)} (hST : S ≤ T)
    (W : Opens (TopCat.of (ComplexPoint X)))
    (hW : W ⊓ S.compl ≤ T.compl) :
    IsIso (((W.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
      (supportedInjectiveComplexMap X hST)) := by
  let R := W.isOpenEmbedding.sheafPullback AddCommGrpCat
  let m := (R.mapHomologicalComplex (.up ℤ)).map (supportedInjectiveComplexMap X hST)
  let : ∀ n, IsIso (m.f n) := by
    intro j
    have hnat : IsIso ((TopCat.Sheaf.forget AddCommGrpCat (TopCat.of W)).map (m.f j)) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro V
      have hV : W.isOpenEmbedding.functor.obj V.unop ≤ W := by
        rintro z ⟨z', hz', rfl⟩
        exact z'.property
      have hWV : W.isOpenEmbedding.functor.obj V.unop ⊓ S.compl ≤ T.compl := by
        intro z hz
        exact hW ⟨hV hz.1, hz.2⟩
      change IsIso (((supportedInjectiveComplexMap X hST).f j).hom.app
        (op (W.isOpenEmbedding.functor.obj V.unop)))
      have hcomp : T.compl ≤ S.compl := by
        intro z hzS hzT
        exact hzS (hST hzT)
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      exact TopCat.Sheaf.supportedOutsideMap_app_bijective hcomp hWV
        ((ambientRationalInjectiveComplex X).X j)
    let := hnat
    exact isIso_of_fully_faithful (TopCat.Sheaf.forget AddCommGrpCat (TopCat.of W)) (m.f j)
  exact HomologicalComplex.Hom.isIso_of_components m

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Exact restriction carries the support-enlargement homology map to an isomorphism. -/
theorem supportedInjectiveHomologySheafMap_restrict_isIso
    {S T : Closeds (ComplexPoint X)} (hST : S ≤ T)
    (W : Opens (TopCat.of (ComplexPoint X)))
    (hW : W ⊓ S.compl ≤ T.compl) (n : ℤ) :
    IsIso ((W.isOpenEmbedding.sheafPullback AddCommGrpCat).map
      (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hST) n)) := by
  let R := W.isOpenEmbedding.sheafPullback AddCommGrpCat
  let m := (R.mapHomologicalComplex (.up ℤ)).map (supportedInjectiveComplexMap X hST)
  let : IsIso m := supportedInjectiveComplexMap_restrict_isIso (X := X) hST W hW
  let : IsIso (HomologicalComplex.homologyMap m n) := by
    infer_instance
  let φ := (HomologicalComplex.shortComplexFunctor (ι := ℤ)
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) (.up ℤ) n).map
      (supportedInjectiveComplexMap X hST)
  have hn := ShortComplex.mapHomologyIso_hom_naturality φ R
  let e := ((HomologicalComplex.shortComplexFunctor (ι := ℤ)
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) (.up ℤ) n).obj
      (complexSupportInjectiveComplex X T)).mapHomologyIso R
  let eS := ((HomologicalComplex.shortComplexFunctor (ι := ℤ)
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint X))) (.up ℤ) n).obj
      (complexSupportInjectiveComplex X S)).mapHomologyIso R
  change HomologicalComplex.homologyMap m n ≫ e.hom =
    eS.hom ≫
      R.map (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hST) n) at hn
  let : IsIso eS.hom := eS.isIso_hom
  have hcomp : IsIso (HomologicalComplex.homologyMap m n ≫ e.hom) := by
    exact (asIso (HomologicalComplex.homologyMap m n) ≪≫ e).isIso_hom
  have hmap : IsIso (R.map (HomologicalComplex.homologyMap
      (supportedInjectiveComplexMap X hST) n)) :=
    IsIso.of_isIso_fac_left (f := eS.hom)
      (g := R.map (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hST) n))
      (h := HomologicalComplex.homologyMap m n ≫ e.hom) (hh := hcomp) hn.symm
  let := hmap
  exact inferInstance

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- The support-enlargement map is an isomorphism on local cohomology-sheaf sections. -/
theorem supportedInjectiveHomologySheafMap_app_isIso
    {S T : Closeds (ComplexPoint X)} (hST : S ≤ T)
    (W : Opens (TopCat.of (ComplexPoint X)))
    (hW : W ⊓ S.compl ≤ T.compl) (n : ℤ) :
    IsIso ((HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hST) n).hom.app
      (op W)) := by
  have : IsIso ((W.isOpenEmbedding.sheafPullback AddCommGrpCat).map
      (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hST) n)) :=
    supportedInjectiveHomologySheafMap_restrict_isIso (X := X) hST W hW n
  have hf : IsIso ((TopCat.Sheaf.forget AddCommGrpCat
      (TopCat.of W)).map ((W.isOpenEmbedding.sheafPullback AddCommGrpCat).map
        (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hST) n))) := by
    let eR := asIso ((W.isOpenEmbedding.sheafPullback AddCommGrpCat).map
      (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hST) n))
    exact ((TopCat.Sheaf.forget AddCommGrpCat (TopCat.of W)).mapIso eR).isIso_hom
  rw [NatTrans.isIso_iff_isIso_app] at hf
  have ht := hf (op (⊤ : Opens (TopCat.of W)))
  change IsIso ((HomologicalComplex.homologyMap
    (supportedInjectiveComplexMap X hST) n).hom.app
      (op (W.isOpenEmbedding.functor.obj ⊤))) at ht
  rw [Opens.isOpenEmbedding_obj_top] at ht
  exact ht

end
end AlgebraicGeometry.ComplexPoint
