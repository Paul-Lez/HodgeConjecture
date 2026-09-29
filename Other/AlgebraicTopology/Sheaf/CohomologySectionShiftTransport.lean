/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import Other.AlgebraicTopology.Sheaf.CohomologySectionNaturality
public import Other.Algebra.Homology.MapHomologyShift

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace TopCat.Sheaf

universe u

variable (Y : TopCat.{u}) (K : CochainComplex (Sheaf AddCommGrpCat Y) ℤ)
  (s n n' : ℤ) (h : s + n = n')

noncomputable def sectionCohomologyPresheafShiftShortComplex :
    (((forget AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ).obj (K⟦s⟧)).sc n ⟶
      (((forget AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ).obj K).sc n' :=
  (shortComplexFunctor ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat) ℤᵘᵖ n).map
      ((Functor.commShiftIso ((forget AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ) s).hom.app K) ≫
    (CochainComplex.shiftShortComplexFunctorIso
      ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat) s n n' h).hom.app
      (((forget AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ).obj K)

noncomputable def sectionCohomologyPresheafShiftMapViaShortComplex :
    sectionCohomologyPresheaf Y (K⟦s⟧) n ⟶ sectionCohomologyPresheaf Y K n' :=
  ShortComplex.homologyMap (sectionCohomologyPresheafShiftShortComplex Y K s n n' h)

/-- The canonical map on the presheaf of local section cohomology induced by a shift.
It displays the actual shifted three-term homology map, including its sign. -/
noncomputable def sectionCohomologyPresheafShiftMap :
    sectionCohomologyPresheaf Y (K⟦s⟧) n ⟶ sectionCohomologyPresheaf Y K n' :=
  HomologicalComplex.homologyMap
      ((Functor.commShiftIso ((forget AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ) s).hom.app K) n ≫
    ((HomologicalComplex.homologyFunctor ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat) ℤᵘᵖ 0).shiftIso
      s n n' h).hom.app (((forget AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ).obj K)

/-- The sheaf map transported through the actual sheafification/cohomology isomorphisms.
This is the canonical target map for section normalization, so its compatibility is
proved directly from the defining normalization maps. -/
noncomputable def sectionCohomologySheafShiftMap :
    (K⟦s⟧).homology n ⟶ K.homology n' :=
  (sectionCohomologyPresheafSheafificationIso Y (K⟦s⟧) n).inv ≫
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
      (sectionCohomologyPresheafShiftMap Y K s n n' h) ≫
    (sectionCohomologyPresheafSheafificationIso Y K n').hom

@[reassoc]
lemma sectionCohomologyPresheafShiftMap_toSheaf :
    sectionCohomologyPresheafShiftMap Y K s n n' h ≫
        sectionCohomologyPresheafToSheaf Y K n' =
      sectionCohomologyPresheafToSheaf Y (K⟦s⟧) n ≫
        (sectionCohomologySheafShiftMap Y K s n n' h).hom := by
  dsimp [sectionCohomologyPresheafToSheaf,
    sectionCohomologySheafShiftMap]
  rw [← Category.assoc, toSheafify_naturality]
  simp only [Category.assoc]
  change _ = _ ≫
    ((sectionCohomologyPresheafSheafificationIso Y (K⟦s⟧) n).hom ≫
      (sectionCohomologyPresheafSheafificationIso Y (K⟦s⟧) n).inv ≫
      (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
        (sectionCohomologyPresheafShiftMap Y K s n n' h) ≫
      (sectionCohomologyPresheafSheafificationIso Y K n').hom).hom
  rw [Iso.hom_inv_id_assoc]
  rfl

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency.types false in
lemma sectionCohomologyPresheafShiftMapViaShortComplex_onOpen
    (U : Opens Y) :
    (sectionCohomologyPresheafOnOpenIso Y (K⟦s⟧) n U).hom ≫
        (sectionCohomologyPresheafShiftMapViaShortComplex Y K s n n' h).app (op U) =
      ShortComplex.homologyMap
          (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (op U)).mapShortComplex.map
            (sectionCohomologyPresheafShiftShortComplex Y K s n n' h)) ≫
        (sectionCohomologyPresheafOnOpenIso Y K n' U).hom := by
  let F := (forget AddCommGrpCat Y)
  let φP :
      (((F.mapHomologicalComplex ℤᵘᵖ).obj (K⟦s⟧)).sc n) ⟶
        (((F.mapHomologicalComplex ℤᵘᵖ).obj K).sc n') :=
    sectionCohomologyPresheafShiftShortComplex Y K s n n' h
  change
    (sectionCohomologyPresheafOnOpenIso Y (K⟦s⟧) n U).hom ≫
        (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (op U)).map
          (ShortComplex.homologyMap φP)) =
      ShortComplex.homologyMap
          (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (op U)).mapShortComplex.map φP) ≫
        (sectionCohomologyPresheafOnOpenIso Y K n' U).hom
  have hh := (ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat) ℤᵘᵖ n).map
      ((Functor.commShiftIso ((forget AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ) s).hom.app K) ≫
      (CochainComplex.shiftShortComplexFunctorIso
        ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat) s n n' h).hom.app
        (((forget AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ).obj K))
    ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (op U))).symm
  convert hh using 1 <;> rfl

set_option maxHeartbeats 1000000 in
lemma sectionCohomologyPresheafShiftMap_eq_viaShortComplex :
    sectionCohomologyPresheafShiftMap Y K s n n' h =
      sectionCohomologyPresheafShiftMapViaShortComplex Y K s n n' h := by
  dsimp [sectionCohomologyPresheafShiftMapViaShortComplex,
    sectionCohomologyPresheafShiftShortComplex,
    sectionCohomologyPresheafShiftMap]
  rw [ShortComplex.homologyMap_comp]
  exact congrArg (fun f => HomologicalComplex.homologyMap
      ((Functor.commShiftIso ((forget AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ) s).hom.app K) n ≫ f)
    (CochainComplex.ShiftSequence.shiftIso_hom_app s n n' h
      (((forget AddCommGrpCat Y).mapHomologicalComplex ℤᵘᵖ).obj K)).symm

set_option maxHeartbeats 1000000 in
lemma sectionCohomologyToSheafSection_shift_naturality (U : Opens Y) :
    ShortComplex.homologyMap
          (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat).obj (op U)).mapShortComplex.map
            (sectionCohomologyPresheafShiftShortComplex Y K s n n' h)) ≫
        sectionCohomologyToSheafSection Y K n' U =
      sectionCohomologyToSheafSection Y (K⟦s⟧) n U ≫
        (sectionCohomologySheafShiftMap Y K s n n' h).hom.app (op U) := by
  dsimp only [sectionCohomologyToSheafSection]
  rw [← Category.assoc,
    ← sectionCohomologyPresheafShiftMapViaShortComplex_onOpen Y K s n n' h U,
    ← sectionCohomologyPresheafShiftMap_eq_viaShortComplex]
  simp only [Category.assoc]
  congr 1
  exact congrArg (fun f => f.app (op U))
    (sectionCohomologyPresheafShiftMap_toSheaf Y K s n n' h)

end TopCat.Sheaf
