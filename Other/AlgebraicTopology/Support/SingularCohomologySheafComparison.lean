/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularCohomologySheafComparison

/-!
# The actual supported singular cohomology sheaf and local relative cohomology

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularCohomologySheafComparison`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace AlgebraicTopology.Singular

open TopCat.Sheaf

variable (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
  (S : Set X) (hS : IsClosed S) (n : ℕ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The sheaf comparison preserves the actual sheafification unit. -/
@[reassoc]
lemma supportedSingularCohomologySheafIsoRelative_unit :
    sectionCohomologyPresheafToSheaf X
      (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) (n : ℤ) ≫
        (supportedSingularCohomologySheafIsoRelative X S hS n).hom.hom =
    (supportedSingularCohomologyPresheafIsoRelative X S hS n).hom ≫
      supportRelativeCohomologyToSheaf X S n := by
  dsimp only [sectionCohomologyPresheafToSheaf, supportedSingularCohomologySheafIsoRelative,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, supportRelativeCohomologyToSheaf]
  let e := sectionCohomologyPresheafSheafificationIso X
    (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) (n : ℤ)
  let m := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
    (supportedSingularCohomologyPresheafIsoRelative X S hS n).hom
  have he : e.hom.hom ≫ (e.inv ≫ m).hom = m.hom :=
    congrArg (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
      (Iso.hom_inv_id_assoc e m)
  rw [Category.assoc, he]
  exact (toSheafify_naturality (Opens.grothendieckTopology X)
    (supportedSingularCohomologyPresheafIsoRelative X S hS n).hom).symm

/-- An actual local section-complex class maps to its actual relative class
followed by the relative sheafification unit. This fixes the local normalization. -/
@[reassoc]
lemma supportedSingularCohomologySheafIsoRelative_section (V : Opens X) :
    sectionCohomologyToSheafSection X
      (supportedRationalSingularCochainComplex X ⟨Sᶜ, hS.isOpen_compl⟩) (n : ℤ) V ≫
        (supportedSingularCohomologySheafIsoRelative X S hS n).hom.hom.app (op V) =
    (supportedRationalSingularSectionCohomologyEquivSupportComplement X S hS V n).toAddCommGrpIso.hom ≫
      (supportRelativeCohomologyToSheaf X S n).app (op V) := by
  dsimp only [sectionCohomologyToSheafSection]
  rw [Category.assoc, ← NatTrans.comp_app, supportedSingularCohomologySheafIsoRelative_unit,
    NatTrans.comp_app, ← Category.assoc]
  dsimp only [supportedSingularCohomologyPresheafIsoRelative, NatIso.ofComponents_hom_app,
    Iso.trans_hom, Iso.symm_hom]
  rw [Iso.hom_inv_id_assoc]

end AlgebraicTopology.Singular
