/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Singular.Sheaf.CochainOpenSections

/-!
# Singular cochains compute sheafified cochains on an arbitrary open

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Singular.Sheaf.CochainOpenSections`.
-/

/-! ### Constructions used only in proofs -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicTopology.Singular

variable (R : Type) [Field R] (X : TopCat.{0})

/-- The image of the top open of a subspace is that ambient open itself. -/
def openSubspaceImageTopIso (V : Opens X) : V.isOpenEmbedding.functor.obj ⊤ ≅ V :=
  eqToIso (Opens.isOpenEmbedding_obj_top V)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Ambient raw cochains on `V` identified with top-open raw cochains of
the space `V`, through the actual image homeomorphism. -/
def openRawSingularCochainComplexIsoGlobal (V : Opens X) :
    openRawSingularCochainComplex R X V ≅ globalRawSingularCochainComplex R (TopCat.of V) :=
  (NatIso.mapHomologicalComplex
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).mapIso (openSubspaceImageTopIso X V).op)
      (.up ℕ)).app (singularCochainPresheafComplex R X) ≪≫
    (((evaluation (Opens (TopCat.of V))ᵒᵖ AddCommGrpCat).obj (.op ⊤)).mapHomologicalComplex
      (.up ℕ)).mapIso (singularCochainPresheafComplexOpenRestrictionIso R X V)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Sections of the ambient singular sheaf on `V` identified with global
sections of its intrinsic singular sheaf, using the normalized open restriction. -/
def openSingularCochainSheafComplexIsoGlobal (V : Opens X) :
    openSingularCochainSheafComplex R X V ≅
      globalSingularCochainSheafComplex R (TopCat.of V) := by
  let : (TopCat.Sheaf.forget AddCommGrpCat X ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (.op V)).PreservesZeroMorphisms :=
    inferInstanceAs ((TopCat.Sheaf.supportEvaluation X V).PreservesZeroMorphisms)
  let : (TopCat.Sheaf.forget AddCommGrpCat X ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj
        (.op (V.isOpenEmbedding.functor.obj ⊤))).PreservesZeroMorphisms :=
    inferInstanceAs ((TopCat.Sheaf.supportEvaluation X
      (V.isOpenEmbedding.functor.obj ⊤)).PreservesZeroMorphisms)
  exact
  (NatIso.mapHomologicalComplex
    (Functor.isoWhiskerLeft (TopCat.Sheaf.forget AddCommGrpCat X)
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).mapIso (openSubspaceImageTopIso X V).op))
      (.up ℕ)).app (singularCochainSheafComplex R X) ≪≫
    ((TopCat.Sheaf.supportEvaluation (TopCat.of V) ⊤).mapHomologicalComplex (.up ℕ)).mapIso
      (singularCochainSheafComplexOpenRestrictionIso R X V)

end AlgebraicTopology.Singular

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicTopology.Singular

variable (R : Type) [Field R] (X : TopCat.{0})

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic/global comparison retains the actual sheafification unit. -/
@[reassoc]
lemma openRawToSingularCochainSheafComplex_global (V : Opens X) :
    openRawToSingularCochainSheafComplex R X V ≫
      (openSingularCochainSheafComplexIsoGlobal R X V).hom =
    (openRawSingularCochainComplexIsoGlobal R X V).hom ≫
      topOpenToGlobalSingularCochainSheafComplex R (TopCat.of V) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (toSheafify (Opens.grothendieckTopology X) (singularCochainPresheaf R X n)).app
      (.op V) ≫
      ((singularCochainSheaf R X n).obj.map (openSubspaceImageTopIso X V).hom.op ≫
        (singularCochainSheafOpenRestrictionIso R X V n).hom.hom.app (.op ⊤)) =
    ((singularCochainPresheaf R X n).map (openSubspaceImageTopIso X V).hom.op ≫
      (singularCochainPresheafOpenRestrictionIso R X V n).hom.app (.op ⊤)) ≫ _
  calc
    _ = (singularCochainPresheaf R X n).map (openSubspaceImageTopIso X V).hom.op ≫
        (toSheafify (Opens.grothendieckTopology X)
          (singularCochainPresheaf R X n)).app
            (.op (V.isOpenEmbedding.functor.obj ⊤)) ≫
        (singularCochainSheafOpenRestrictionIso R X V n).hom.hom.app (.op ⊤) :=
      ((toSheafify (Opens.grothendieckTopology X)
        (singularCochainPresheaf R X n)).naturality_assoc
          (openSubspaceImageTopIso X V).hom.op _).symm
    _ = _ := by
      rw [Category.assoc, topOpenToGlobalSingularCochainSheafComplex_f]
      exact congrArg
        (fun f => (singularCochainPresheaf R X n).map
          (openSubspaceImageTopIso X V).hom.op ≫ f.app (.op ⊤))
        (toSheafify_singularCochainSheafOpenRestrictionIso R X V n)

/-- On any paracompact Hausdorff ambient open, raw rational singular
cochains map quasi-isomorphically to sections of the actual singular sheaf.
No separation or paracompactness assumption is made on the rest of `X`. -/
theorem openRawToSingularCochainSheafComplex_quasiIso (V : Opens X)
    [ParacompactSpace V] [T2Space V] :
    QuasiIso (openRawToSingularCochainSheafComplex ℚ X V) := by
  have := topOpenToGlobalSingularCochainSheafComplex_quasiIso (Y := TopCat.of V)
  have : QuasiIso
      ((openRawSingularCochainComplexIsoGlobal ℚ X V).hom ≫
        topOpenToGlobalSingularCochainSheafComplex ℚ (TopCat.of V)) := inferInstance
  rw [← openRawToSingularCochainSheafComplex_global] at this
  exact (quasiIso_iff_comp_right _ _).mp this

/-- The open-section comparisons commute with the literal restriction maps.
In particular this applies to `W = V ⊓ U`. -/
@[reassoc]
lemma openSingularSheafRestriction_naturality {V W : Opens X} (i : W ⟶ V) :
    openRawToSingularCochainSheafComplex R X V ≫ openSingularSheafRestriction R X i =
      openRawSingularRestriction R X i ≫ openRawToSingularCochainSheafComplex R X W := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact ((toSheafify (Opens.grothendieckTopology X)
    (singularCochainPresheaf R X n)).naturality i.op).symm

end AlgebraicTopology.Singular
