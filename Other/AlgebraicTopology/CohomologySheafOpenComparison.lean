/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.OpenSheafification
public import Other.AlgebraicTopology.CohomologySheafSectionNaturality
public import Other.AlgebraicTopology.OpenRestrictedLowestCohomology

/-! # The canonical local cohomology-sheaf map under actual open restriction -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace CategoryTheory.ShortComplex

variable {C D E A : Type*} [Category* C] [Category* D] [Category* E] [Category* A]
  [Abelian C] [Abelian D] [Abelian E] [Abelian A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Homology comparisons around an actual square of exact functors. -/
@[reassoc]
lemma mapHomologyIso_exactSquare (S : ShortComplex C)
    (F : C ⥤ D) (P : D ⥤ A) (G : C ⥤ E) (Q : E ⥤ A)
    [F.Additive] [P.Additive] [G.Additive] [Q.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (τ : F ⋙ P ⟶ G ⋙ Q) :
    P.map (S.mapHomologyIso F).hom ≫ τ.app S.homology ≫ Q.map (S.mapHomologyIso G).inv =
      ((S.map F).mapHomologyIso P).inv ≫ homologyMap (S.mapNatTrans τ) ≫
        ((S.map G).mapHomologyIso Q).hom := by
  rw [← cancel_epi ((S.map F).mapHomologyIso P).hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← mapHomologyIso_comp_hom_assoc, NatTrans.app_homology]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [mapHomologyIso_comp_hom]
  simp only [Category.assoc, ← Q.map_comp, Iso.hom_inv_id, Q.map_id, Category.comp_id]

end CategoryTheory.ShortComplex

namespace TopCat.Sheaf

variable (X : TopCat.{u}) (U : Opens X)

/-- Actual restriction of additive presheaves to the open subspace. -/
def cohomologyOpenPresheafRestriction :
    ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ ((Opens (TopCat.of U))ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (Functor.whiskeringLeft (Opens (TopCat.of U))ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
    U.isOpenEmbedding.functor.op

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance cohomologyOpenPresheafRestriction_additive :
    (cohomologyOpenPresheafRestriction X U).Additive := by
  dsimp [cohomologyOpenPresheafRestriction]
  infer_instance

instance cohomologyOpenPresheafRestriction_preservesZeroMorphisms :
    (cohomologyOpenPresheafRestriction X U).PreservesZeroMorphisms where
  map_zero := by intros; rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance cohomologyOpenPresheafRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (cohomologyOpenPresheafRestriction X U) := by
  dsimp [cohomologyOpenPresheafRestriction]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance cohomologyOpenPresheafRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (cohomologyOpenPresheafRestriction X U) := by
  dsimp [cohomologyOpenPresheafRestriction]
  infer_instance

/-- The previously normalized open sheafification comparisons form a natural isomorphism. -/
def cohomologyOpenSheafificationIso :
    cohomologyOpenPresheafRestriction X U ⋙
      presheafToSheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u} ≅
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u} :=
  NatIso.ofComponents (openRestrictionSheafificationIso X U)
    (fun f => openRestrictionSheafificationIso_naturality X U f)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Open restriction of the actual sheafification counit is its actual subspace counit. -/
@[reassoc]
lemma openRestrictionSheafificationIso_counit (F : Sheaf AddCommGrpCat.{u} X) :
    (openRestrictionSheafificationIso X U F.obj).hom ≫
      (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).map
        ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit.app F) =
    (sheafificationAdjunction (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}).counit.app
      ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj F) := by
  apply (sheafToPresheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}).map_injective
  apply sheafify_hom_ext
    (Opens.grothendieckTopology (TopCat.of U)) _ _
    ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj F).property
  change toSheafify _ _ ≫ ((openRestrictionSheafificationIso X U F.obj).hom.hom ≫ _) = _
  rw [← Category.assoc, toSheafify_openRestrictionSheafificationIso]
  have hX := (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_triangle_components F
  have hU := (sheafificationAdjunction (Opens.grothendieckTopology (TopCat.of U))
    AddCommGrpCat.{u}).right_triangle_components
      ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj F)
  change Functor.whiskerLeft U.isOpenEmbedding.functor.op
      (toSheafify (Opens.grothendieckTopology X) F.obj) ≫
    Functor.whiskerLeft U.isOpenEmbedding.functor.op
      ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit.app F).hom = _
  change toSheafify (Opens.grothendieckTopology X) F.obj ≫
    ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit.app F).hom =
      𝟙 F.obj at hX
  rw [← Functor.whiskerLeft_comp, hX]
  exact hU.symm

variable (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- Exact presheaf restriction commutes with the presheaf of local cohomology. -/
def openRestrictionSectionCohomologyPresheafIso (n : ℤ) :
    sectionCohomologyPresheaf (TopCat.of U)
      (((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).obj K) n ≅
    (cohomologyOpenPresheafRestriction X U).obj (sectionCohomologyPresheaf X K n) := by
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    (((forget AddCommGrpCat.{u} X).mapHomologicalComplex (.up ℤ)).obj K).sc n
  exact S.mapHomologyIso (cohomologyOpenPresheafRestriction X U)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- The exact sheafification/counit comparison respects open restriction. -/
@[reassoc]
lemma openRestrictionSectionCohomologySheafificationIso (n : ℤ) :
    (presheafToSheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}).map
        (openRestrictionSectionCohomologyPresheafIso X U K n).hom ≫
      (openRestrictionSheafificationIso X U (sectionCohomologyPresheaf X K n)).hom ≫
      (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).map
        (sectionCohomologyPresheafSheafificationIso X K n).hom =
    (sectionCohomologyPresheafSheafificationIso (TopCat.of U)
      (((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex (.up ℤ)).obj K) n).hom ≫
      ((K.sc n).mapHomologyIso (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u})).hom := by
  let A := cohomologyOpenPresheafRestriction X U
  let R : Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} (TopCat.of U) :=
    U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}
  let P : ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ Sheaf AddCommGrpCat.{u} X :=
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let Q : ((Opens (TopCat.of U))ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ Sheaf AddCommGrpCat.{u} (TopCat.of U) :=
    presheafToSheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}
  let : P.PreservesZeroMorphisms := inferInstanceAs
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).PreservesZeroMorphisms
  let : Q.PreservesZeroMorphisms := inferInstanceAs
    (presheafToSheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}).PreservesZeroMorphisms
  let : R.PreservesZeroMorphisms := inferInstanceAs
    (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).PreservesZeroMorphisms
  let : P.Additive := inferInstanceAs
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive
  let : Q.Additive := inferInstanceAs
    (presheafToSheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}).Additive
  let : R.Additive := openSheafRestriction_additive X U
  let : PreservesFiniteLimits P := inferInstanceAs
    (PreservesFiniteLimits (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
  let : PreservesFiniteColimits P := inferInstanceAs
    (PreservesFiniteColimits (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
  let : PreservesFiniteLimits Q := inferInstanceAs
    (PreservesFiniteLimits (presheafToSheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}))
  let : PreservesFiniteColimits Q := inferInstanceAs
    (PreservesFiniteColimits (presheafToSheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}))
  let : PreservesFiniteLimits R := openSheafRestriction_preservesFiniteLimits X U
  let : PreservesFiniteColimits R := openSheafRestriction_preservesFiniteColimits X U
  let L : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ :=
    ((forget AddCommGrpCat.{u} X).mapHomologicalComplex (.up ℤ)).obj K
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) := L.sc n
  let β : A ⋙ Q ≅ P ⋙ R := cohomologyOpenSheafificationIso X U
  let b := (β.hom.mapHomologicalComplex (.up ℤ)).app L
  let eX : (P.mapHomologicalComplex (.up ℤ)).obj L ≅ K := (NatIso.mapHomologicalComplex
    (asIso (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit)
    (.up ℤ)).app K
  let eU : (Q.mapHomologicalComplex (.up ℤ)).obj ((A.mapHomologicalComplex (.up ℤ)).obj L) ≅
      (R.mapHomologicalComplex (.up ℤ)).obj K := (NatIso.mapHomologicalComplex
    (asIso (sheafificationAdjunction (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}).counit)
    (.up ℤ)).app ((R.mapHomologicalComplex (.up ℤ)).obj K)
  let H := homologyFunctor (Sheaf AddCommGrpCat.{u} (TopCat.of U)) (.up ℤ) n
  have hb : b ≫ (R.mapHomologicalComplex (.up ℤ)).map eX.hom = eU.hom := by
    apply HomologicalComplex.Hom.ext
    funext j
    exact openRestrictionSheafificationIso_counit X U (K.X j)
  have hs := ShortComplex.mapHomologyIso_exactSquare S A Q P R β.hom
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor (Sheaf AddCommGrpCat.{u} X) (.up ℤ) n).map eX.hom) R
  change H.map ((R.mapHomologicalComplex (.up ℤ)).map eX.hom) ≫
      ((K.sc n).mapHomologyIso R).hom =
    ((S.map P).mapHomologyIso R).hom ≫ R.map (homologyMap eX.hom n) at hn
  change Q.map (S.mapHomologyIso A).hom ≫ β.hom.app S.homology ≫
      R.map ((S.mapHomologyIso P).inv ≫ homologyMap eX.hom n) =
    (((S.map A).mapHomologyIso Q).inv ≫ H.map eU.hom) ≫ ((K.sc n).mapHomologyIso R).hom
  rw [R.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc _ (R.map (S.mapHomologyIso P).inv), ← Category.assoc, hs]
  simp only [Category.assoc]
  rw [← hn]
  change ((S.map A).mapHomologyIso Q).inv ≫
      H.map b ≫ H.map ((R.mapHomologicalComplex (.up ℤ)).map eX.hom) ≫
        ((K.sc n).mapHomologyIso R).hom = _
  rw [← H.map_comp_assoc, hb]

end TopCat.Sheaf
