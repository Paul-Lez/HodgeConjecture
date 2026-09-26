/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import Other.AlgebraicGeometry.Cycle.FundamentalClass
public import Other.AlgebraicTopology.Sheaf.CohomologySectionNaturality
public import Other.AlgebraicTopology.Support.SingularCohomologySheafComparison

/-! # Exact local normalization of the actual supported injective cohomology sheaf -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open AlgebraicTopology.Singular TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

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
      ℤᵘᵖ).obj (complexSupportInjectiveComplex X S))).homology (n : ℤ)) :
    (complexSupportInjectiveCohomologySheafIsoRelative X S n).hom.hom.app (op V)
      (sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X S) (n : ℤ) V z) =
    (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) S n).app (op V)
      (complexSupportInjectiveSectionCohomologyEquiv X S V n z) :=
  ConcreteCategory.congr_hom (complexSupportInjectiveCohomologySheafIsoRelative_section X S n V) z

variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- Restriction of the supported injective complex to the smooth ambient open. -/
def cycleComponentSupportSectionRestriction :
    ((supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex ℤᵘᵖ).obj
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)) ⟶
      ((supportEvaluation (TopCat.of (ComplexPoint X))
        (cycleComponentSmoothSupportAmbientOpen X x)).mapHomologicalComplex ℤᵘᵖ).obj
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)) :=
  sectionComplexRestriction (TopCat.of (ComplexPoint X)) ℤᵘᵖ
    (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)) (homOfLE le_top)

set_option maxHeartbeats 800000 in
/-- The normalization is the supported Ext class restricted to the smooth ambient open. -/
theorem cycleComponentSupportedClassNormalizationIso_apply
    (a : CycleComponentSupportedCohomology X x p) :
    (cycleComponentSupportedClassNormalizationIso X x hx).toAddMonoidHom a =
      (complexSupportInjectiveCohomologySheafIsoRelative X
          (cycleComponentAnalyticClosedSupport X x) (2 * p)).hom.hom.app
        (op (cycleComponentSmoothSupportAmbientOpen X x))
        ((cycleComponentSmoothSupportLowestSectionCohomologyComplexIso X x hx).hom
          (HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x)
            (2 * (p : ℤ))
            ((rationalSupportAddEquivSupportedInjectiveHomology X
              (cycleComponentAnalyticClosedSupport X x) (2 * p)) a))) := by
  let T := TopCat.of (ComplexPoint X)
  let Z := cycleComponentAnalyticClosedSupport X x
  let U := cycleComponentSmoothSupportAmbientOpen X x
  let hW : U ⊓ Z.compl = Z.compl := inf_eq_right.mpr
    (cycleComponentSupportComplement_le_smoothAmbientOpen X x)
  let f : Z.compl ⟶ U := homOfLE (by
    intro y hy hyS
    obtain ⟨w, _, hw⟩ := hyS
    apply hy
    change y.underlying ∈ closure ({x} : Set X.left)
    rw [← range_cycleComponentι X.left x]
    exact ⟨w, hw⟩)
  let g : U ⟶ ⊤ := homOfLE le_top
  let F := (TopCat.Sheaf.constantFunctor T).obj (AddCommGrpCat.of ℚ)
  let n : ℕ := 2 * p
  have hcycle (y : H_[Z]^n(X; ℚ)) :
      cycleComponentSupportExtensionIso X x hx y =
        CategoryTheory.Sheaf.relH.restrict F (homOfLE (show Z.compl ≤ ⊤ from le_top))
          f (homOfLE (show Z.compl ≤ Z.compl from le_rfl)) g
          (by apply Subsingleton.elim) n y := by
    rfl
  change cycleComponentSmoothSupportLowestSectionCohomologyEquiv X x hx
    (cycleComponentSupportExtensionIso X x hx a) = _
  have hcycle' : cycleComponentSupportExtensionIso X x hx a =
      CategoryTheory.Sheaf.relH.restrict F (homOfLE (show Z.compl ≤ ⊤ from le_top))
        (homOfLE (show Z.compl ≤ U from
          (cycleComponentSupportComplement_le_smoothAmbientOpen X x)))
        (homOfLE (show Z.compl ≤ Z.compl from le_rfl)) (homOfLE (show U ≤ ⊤ from le_top))
          (by apply Subsingleton.elim) n a := by
    rw [hcycle]
  rw [hcycle']
  change (rationalSupportAddEquivSupportedInjectiveSheafSection X Z U Z.compl hW n
    (cycleComponentSmoothSupportLowestSectionCohomologyComplexIso X x hx))
      ((CategoryTheory.Sheaf.relH.restrict F (homOfLE (show Z.compl ≤ ⊤ from le_top))
        (homOfLE (show Z.compl ≤ U from
          (cycleComponentSupportComplement_le_smoothAmbientOpen X x)))
        (homOfLE (show Z.compl ≤ Z.compl from le_rfl))
        (homOfLE (show U ≤ ⊤ from le_top)) (by apply Subsingleton.elim) n) a) = _
  rw [rationalSupportAddEquivSupportedInjectiveSheafSection_apply]
  have hbridge :=
    @relHAddEquivSupportedSectionsHomology_restrict T Z.compl
      (⊤ : Opens T) Z.compl Z.compl U Z.compl (top_inf_eq _) hW le_rfl le_top le_rfl
      (analyticHasExt X) F (ambientRationalInjectiveComplex X)
      (ambientRationalInjectiveComplex_isKInjective X)
      (ambientRationalInjectiveSingleAugmentation X)
      (ambientRationalInjectiveSingleAugmentation_quasiIso X) n a
  erw [hbridge]
  have hsupport :
        supportedSectionsRestriction T
            (show Z.compl ≤ Z.compl from le_rfl)
            (show U ≤ (⊤ : Opens T) from le_top)
            (ambientRationalInjectiveComplex X) =
          cycleComponentSupportSectionRestriction X x := by
    rw [supportedSectionsRestriction_refl]
    rfl
  rw [hsupport]
  dsimp [cycleComponentSupportSectionRestriction, cycleComponentSmoothRestrictedInjectiveComplex,
    complexSupportInjectiveComplex, rationalSupportAddEquivSupportedInjectiveHomology]
  simp [supportEvaluation, T, Z, U, n]
  rfl

end AlgebraicGeometry.ComplexPoint
