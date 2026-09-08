/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicGeometry.CycleComponentSheafClass
public import HodgeConjecture.Other.AlgebraicTopology.CohomologySheafSectionNaturality

/-! # Exact local normalization of the actual supported injective cohomology sheaf -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open AlgebraicTopology.Singular TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme} (s : X ⟶ Spec (.of ℂ))
  [IsIntegral X] [Smooth s] [IsProjective s]

local instance complexSupportCohomologySheafNormalizationTopology :
    TopologicalSpace (ComplexPoint X s) := Point.analyticTopology

local instance complexSupportCohomologySheafNormalizationParacompact :
    ∀ V : Opens (ComplexPoint X s), ParacompactSpace V := openParacompactSpace s

/-- The injective-sheaf comparison inverts exactly the actual singular-resolution map. -/
@[reassoc]
lemma complexSupportInjectiveCohomologySheafIsoRelative_comp
    (S : Closeds (ComplexPoint X s)) (n : ℕ) :
    homologyMap (complexSupportedSingularToAmbientInjective s S.compl) (n : ℤ) ≫
      (complexSupportInjectiveCohomologySheafIsoRelative s S n).hom =
    (supportedSingularCohomologySheafIsoRelative
      (TopCat.of (ComplexPoint X s)) S S.isClosed n).hom := by
  let : ∀ V : Opens (ComplexPoint X s), ParacompactSpace V := openParacompactSpace s
  change (asIso (homologyMap (complexSupportedSingularToAmbientInjective s S.compl) (n : ℤ))).hom ≫
    ((asIso (homologyMap (complexSupportedSingularToAmbientInjective s S.compl) (n : ℤ))).inv ≫ _) = _
  rw [Iso.hom_inv_id_assoc]

/-- The actual supported injective cohomology-sheaf comparison takes the
canonical original-ambient section to the prescribed relative sheafification unit. -/
@[reassoc]
lemma complexSupportInjectiveCohomologySheafIsoRelative_section
    (S : Closeds (ComplexPoint X s)) (n : ℕ) (V : Opens (ComplexPoint X s)) :
    sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X s))
      (complexSupportInjectiveComplex s S) (n : ℤ) V ≫
        (complexSupportInjectiveCohomologySheafIsoRelative s S n).hom.hom.app (op V) =
    (complexSupportInjectiveSectionCohomologyEquiv s S V n).toAddCommGrpIso.hom ≫
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X s)) S n).app (op V) := by
  let : ∀ W : Opens (ComplexPoint X s), ParacompactSpace W := openParacompactSpace s
  let Y := TopCat.of (ComplexPoint X s)
  let K := supportedRationalSingularCochainComplex Y S.compl
  let e := complexSupportedSingularInjectiveHomologyIso s S.compl V (n : ℤ)
  have hn : e.hom ≫ sectionCohomologyToSheafSection Y (complexSupportInjectiveComplex s S) (n : ℤ) V =
      sectionCohomologyToSheafSection Y K (n : ℤ) V ≫
        (homologyMap (complexSupportedSingularToAmbientInjective s S.compl) (n : ℤ)).hom.app (op V) :=
    sectionCohomologyToSheafSection_naturality Y
      (complexSupportedSingularToAmbientInjective s S.compl) (n : ℤ) V
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, hn, Category.assoc]
  have hc := congrArg (fun f => f.hom.app (op V))
    (complexSupportInjectiveCohomologySheafIsoRelative_comp s S n)
  change (homologyMap (complexSupportedSingularToAmbientInjective s S.compl) (n : ℤ)).hom.app (op V) ≫
      (complexSupportInjectiveCohomologySheafIsoRelative s S n).hom.hom.app (op V) =
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
    (S : Closeds (ComplexPoint X s)) (n : ℕ) (V : Opens (ComplexPoint X s))
    (z : ((((supportEvaluation (TopCat.of (ComplexPoint X s)) V).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex s S))).homology (n : ℤ)) :
    (complexSupportInjectiveCohomologySheafIsoRelative s S n).hom.hom.app (op V)
      (sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X s))
        (complexSupportInjectiveComplex s S) (n : ℤ) V z) =
    (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X s)) S n).app (op V)
      (complexSupportInjectiveSectionCohomologyEquiv s S V n z) :=
  ConcreteCategory.congr_hom (complexSupportInjectiveCohomologySheafIsoRelative_section s S n V) z

end AlgebraicGeometry.ComplexPoint
