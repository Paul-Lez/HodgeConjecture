/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.CohomologySheafSection

/-! # Coefficient-map naturality of the canonical local cohomology-sheaf class -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u}) {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ}
  (f : K ⟶ L) (n : ℤ)

/-- The actual map on the presheaves of local section-complex cohomology. -/
def sectionCohomologyPresheafMap :
    sectionCohomologyPresheaf X K n ⟶ sectionCohomologyPresheaf X L n :=
  homologyMap (((forget AddCommGrpCat.{u} X).mapHomologicalComplex (.up ℤ)).map f) n

/-- The actual evaluation/homology comparison is natural in coefficient maps. -/
@[reassoc]
lemma sectionCohomologyPresheafOnOpenIso_naturality (U : Opens X) :
    homologyMap (((supportEvaluation X U).mapHomologicalComplex (.up ℤ)).map f) n ≫
      (sectionCohomologyPresheafOnOpenIso X L n U).hom =
    (sectionCohomologyPresheafOnOpenIso X K n U).hom ≫
      (sectionCohomologyPresheafMap X f n).app (op U) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (.up ℤ) n).map
      (((forget AddCommGrpCat.{u} X).mapHomologicalComplex (.up ℤ)).map f))
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
/-- Exact sheafification and its counit give a coefficient-natural cohomology isomorphism. -/
@[reassoc]
lemma sectionCohomologyPresheafSheafificationIso_naturality :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      (sectionCohomologyPresheafMap X f n) ≫
        (sectionCohomologyPresheafSheafificationIso X L n).hom =
    (sectionCohomologyPresheafSheafificationIso X K n).hom ≫ homologyMap f n := by
  let F : Sheaf AddCommGrpCat.{u} X ⥤ ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    forget AddCommGrpCat.{u} X
  let P : ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ Sheaf AddCommGrpCat.{u} X :=
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}
  let : F.PreservesZeroMorphisms :=
    inferInstanceAs (forget AddCommGrpCat.{u} X).PreservesZeroMorphisms
  let : P.PreservesZeroMorphisms :=
    inferInstanceAs (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).PreservesZeroMorphisms
  let : P.PreservesHomology :=
    inferInstanceAs (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).PreservesHomology
  let g := (F.mapHomologicalComplex (.up ℤ)).map f
  let e : (F ⋙ P).mapHomologicalComplex (.up ℤ) ≅
      (𝟭 (Sheaf AddCommGrpCat.{u} X)).mapHomologicalComplex (.up ℤ) := NatIso.mapHomologicalComplex
    (asIso (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit)
    (.up ℤ)
  let H := homologyFunctor (Sheaf AddCommGrpCat.{u} X) (.up ℤ) n
  change P.map (homologyMap g n) ≫
      (((((F.mapHomologicalComplex (.up ℤ)).obj L).sc n).mapHomologyIso P).inv ≫
        H.map (e.app L).hom) =
    (((((F.mapHomologicalComplex (.up ℤ)).obj K).sc n).mapHomologyIso P).inv ≫
        H.map (e.app K).hom) ≫ H.map f
  calc
    _ = (((((F.mapHomologicalComplex (.up ℤ)).obj K).sc n).mapHomologyIso P).inv ≫
        H.map ((P.mapHomologicalComplex (.up ℤ)).map g)) ≫ H.map (e.app L).hom :=
      congrArg (fun t => t ≫ H.map (e.app L).hom)
        (ShortComplex.mapHomologyIso_inv_naturality
          ((shortComplexFunctor _ (.up ℤ) n).map g) P)
    _ = _ := by
      simp only [Category.assoc]
      congr 1
      rw [← H.map_comp, ← H.map_comp]
      exact congrArg H.map (e.hom.naturality f)

/-- The canonical presheaf-to-cohomology-sheaf map is natural in coefficient complexes. -/
@[reassoc]
lemma sectionCohomologyPresheafToSheaf_naturality :
    sectionCohomologyPresheafMap X f n ≫ sectionCohomologyPresheafToSheaf X L n =
    sectionCohomologyPresheafToSheaf X K n ≫ (homologyMap f n).hom := by
  dsimp only [sectionCohomologyPresheafToSheaf]
  rw [← Category.assoc, toSheafify_naturality, Category.assoc, Category.assoc]
  congr 1
  exact congrArg (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    (sectionCohomologyPresheafSheafificationIso_naturality X f n)

/-- The actual map from cohomology of local sections to cohomology-sheaf sections
commutes with every actual coefficient-complex map. -/
@[reassoc]
lemma sectionCohomologyToSheafSection_naturality (U : Opens X) :
    homologyMap (((supportEvaluation X U).mapHomologicalComplex (.up ℤ)).map f) n ≫
      sectionCohomologyToSheafSection X L n U =
    sectionCohomologyToSheafSection X K n U ≫ (homologyMap f n).hom.app (op U) := by
  dsimp only [sectionCohomologyToSheafSection]
  rw [sectionCohomologyPresheafOnOpenIso_naturality_assoc]
  simp only [Category.assoc]
  congr 1
  exact congrArg (fun α => α.app (op U))
    (sectionCohomologyPresheafToSheaf_naturality X f n)

end TopCat.Sheaf
