/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.CycleComponentSheafClass
public import Other.AlgebraicTopology.CohomologySheafSectionNaturality

/-! # Exact local normalization of the actual supported injective cohomology sheaf -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open AlgebraicTopology.Singular TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance complexSupportCohomologySheafNormalizationTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

local instance complexSupportCohomologySheafNormalizationParacompact :
    ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X

/-- The injective-sheaf comparison inverts exactly the actual singular-resolution map. -/
@[reassoc]
lemma complexSupportInjectiveCohomologySheafIsoRelative_comp
    (S : Closeds (ComplexPoint X)) (n : ℕ) :
    homologyMap (complexSupportedSingularToAmbientInjective X S.compl) (n : ℤ) ≫
      (complexSupportInjectiveCohomologySheafIsoRelative X S n).hom =
    (supportedSingularCohomologySheafIsoRelative
      (TopCat.of (ComplexPoint X)) S S.isClosed n).hom := by
  let : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X
  change (asIso (homologyMap (complexSupportedSingularToAmbientInjective X S.compl) (n : ℤ))).hom ≫
    ((asIso (homologyMap (complexSupportedSingularToAmbientInjective X S.compl) (n : ℤ))).inv ≫ _) = _
  rw [Iso.hom_inv_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual supported injective cohomology-sheaf comparison takes the
canonical original-ambient section to the prescribed relative sheafification unit. -/
@[reassoc]
lemma complexSupportInjectiveCohomologySheafIsoRelative_section
    (S : Closeds (ComplexPoint X)) (n : ℕ) (V : Opens (ComplexPoint X)) :
    sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
      (complexSupportInjectiveComplex X S) (n : ℤ) V ≫
        (complexSupportInjectiveCohomologySheafIsoRelative X S n).hom.hom.app (op V) =
    (complexSupportInjectiveSectionCohomologyEquiv X S V n).toAddCommGrpIso.hom ≫
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) S n).app (op V) := by
  let : ∀ W : Opens (ComplexPoint X), ParacompactSpace W := openParacompactSpace X
  let Y := TopCat.of (ComplexPoint X)
  let K := supportedRationalSingularCochainComplex Y S.compl
  let e := complexSupportedSingularInjectiveHomologyIso X S.compl V (n : ℤ)
  have hn : e.hom ≫ sectionCohomologyToSheafSection Y (complexSupportInjectiveComplex X S) (n : ℤ) V =
      sectionCohomologyToSheafSection Y K (n : ℤ) V ≫
        (homologyMap (complexSupportedSingularToAmbientInjective X S.compl) (n : ℤ)).hom.app (op V) :=
    sectionCohomologyToSheafSection_naturality Y
      (complexSupportedSingularToAmbientInjective X S.compl) (n : ℤ) V
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, hn, Category.assoc]
  have hc := congrArg (fun f => f.hom.app (op V))
    (complexSupportInjectiveCohomologySheafIsoRelative_comp X S n)
  change (homologyMap (complexSupportedSingularToAmbientInjective X S.compl) (n : ℤ)).hom.app (op V) ≫
      (complexSupportInjectiveCohomologySheafIsoRelative X S n).hom.hom.app (op V) =
    (supportedSingularCohomologySheafIsoRelative Y S S.isClosed n).hom.hom.app (op V) at hc
  rw [hc]
  refine (supportedSingularCohomologySheafIsoRelative_section Y S S.isClosed n V).trans ?_
  apply ConcreteCategory.hom_ext
  intro z
  change (supportRelativeCohomologyToSheaf Y S n).app (op V)
      (supportedRationalSingularSectionCohomologyEquivSupportComplement Y S S.isClosed V n z) =
    (supportRelativeCohomologyToSheaf Y S n).app (op V)
      (supportedRationalSingularSectionCohomologyEquivSupportComplement Y S S.isClosed V n
        (e.inv (e.hom z)))
  exact congrArg (fun z => (supportRelativeCohomologyToSheaf Y S n).app (op V)
    (supportedRationalSingularSectionCohomologyEquivSupportComplement Y S S.isClosed V n z))
      (e.addCommGroupIsoToAddEquiv.symm_apply_apply z).symm

/-- The normalization equation on an actual local injective-model cohomology class. -/
lemma complexSupportInjectiveCohomologySheafIsoRelative_section_apply
    (S : Closeds (ComplexPoint X)) (n : ℕ) (V : Opens (ComplexPoint X))
    (z : ((((supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X S))).homology (n : ℤ)) :
    (complexSupportInjectiveCohomologySheafIsoRelative X S n).hom.hom.app (op V)
      (sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X S) (n : ℤ) V z) =
    (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) S n).app (op V)
      (complexSupportInjectiveSectionCohomologyEquiv X S V n z) :=
  ConcreteCategory.congr_hom (complexSupportInjectiveCohomologySheafIsoRelative_section X S n V) z

end AlgebraicGeometry.ComplexPoint
