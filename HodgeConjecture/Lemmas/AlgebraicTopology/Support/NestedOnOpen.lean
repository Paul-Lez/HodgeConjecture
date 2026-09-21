/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.NestedLocalization
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.FlasqueSections
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SectionRestrictionCone
/-!
# The open-set model of the last localization term

For `V ≤ U`, global sections of the sheaf of sections on `U` vanishing on `V` are
canonically sections on `U` of the sheaf of ambient sections vanishing on `V`, both sides
being the kernel of restriction `F(U) → F(V)`. The comparison is functorial in the
coefficient sheaf, so it identifies the last complex in nested-support localization with
the supported-section complex on the complement of the smaller closed support.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable (X : TopCat.{u})

theorem openRestrictionImage_top (U : Opens X) :
    openRestrictionImage X U ⊤ = U := by simp

theorem openRestrictionImage_eq_of_le {U V : Opens X} (h : V ≤ U) :
    openRestrictionImage X V U = V := by simp_all

/-- Let `X` be a topological space and `U ⊆ X` open, with inclusion `j`. This natural isomorphism
identifies `Γ(X, j_*(F|_U))` with `F(U)` for every sheaf of abelian groups `F`. -/
def openRestrictionPushforwardTopEvaluationIso (U : Opens X) :
    openRestrictionPushforward X U ⋙ supportEvaluation X ⊤ ≅ supportEvaluation X U :=
  NatIso.ofComponents (fun F =>
    F.obj.mapIso (eqToIso (congrArg op (openRestrictionImage_top X U))))
    (fun f => (f.hom.naturality _).symm)

/-- Let `V ⊆ U` be open subsets of a topological space `X`, and let `F` be a sheaf of abelian
groups. This includes the kernel sheaf of `j_{U*}(F|_U) → j_{V*}(F|_V)` into `j_{U*}(F|_U)`. On
an open `W` it includes sections over `W ∩ U` vanishing on `W ∩ V` into all sections over `W ∩
U`. -/
def sheafSectionsBetweenOpensInclusion {U V : Opens X} (h : V ≤ U) :
    sheafSectionsBetweenOpens X h ⟶ openRestrictionPushforward X U where
  app F := kernel.ι ((openRestrictionPushforwardMap X h).app F)
  naturality F G f := by simp [sheafSectionsBetweenOpens]

variable {U V : Opens X} (h : V ≤ U)

/-- Let `V ⊆ U` be open subsets of a topological space `X`, and let `F` be a sheaf of abelian
groups. This identifies global sections of `j_{V*}(F|_V)` with its sections over `U`: both
groups are `F(V)` because `V ⊆ U`. -/
def nestedSupportRestrictionTargetIso (F : Sheaf AddCommGrpCat.{u} X) :
    ((openRestrictionPushforward X V).obj F).obj.obj (op ⊤) ≅
      ((openRestrictionPushforward X V).obj F).obj.obj (op U) :=
  F.obj.mapIso (eqToIso (congrArg op
    ((openRestrictionImage_top X V).trans (openRestrictionImage_eq_of_le X h).symm)))

/-- The comparison of the two restriction arrows is the presheaf restriction square. -/
@[reassoc]
theorem nestedSupportRestrictionTargetIso_square (F : Sheaf AddCommGrpCat.{u} X) :
    (((openRestrictionPushforwardMap X h).app F).hom.app (op ⊤)) ≫
        (nestedSupportRestrictionTargetIso X h F).hom =
      (openRestrictionPushforwardTopEvaluationIso X U).hom.app F ≫
        (((toOpenRestrictionPushforward X V).app F).hom.app (op U)) := by
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
  rw [← F.obj.map_comp, ← F.obj.map_comp]
  congr 1

/-- Let `V ⊆ U` be open subsets of a topological space `X`, and let `F` be a sheaf of abelian
groups. This identifies global sections of `ker(j_{U*}(F|_U) → j_{V*}(F|_V))` with sections over
`U` of the subsheaf of `F` supported in `X \ V`. Both are the kernel of `F(U) → F(V)`. -/
def sheafSectionsBetweenOpensGlobalIso (F : Sheaf AddCommGrpCat.{u} X) :
    ((sheafSectionsBetweenOpens X h).obj F).obj.obj (op ⊤) ≅
      ((sheafSectionsSupportedOutside X V).obj F).obj.obj (op U) :=
  sheafSectionsBetweenOpensOnOpenIso X h ⊤ F ≪≫
    kernel.mapIso _ _ ((openRestrictionPushforwardTopEvaluationIso X U).app F)
      (nestedSupportRestrictionTargetIso X h F)
      (nestedSupportRestrictionTargetIso_square X h F) ≪≫
    (sheafSectionsSupportedOutsideOnOpenIso X V U F).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The comparison preserves the inclusion into sections on `U`. -/
@[reassoc (attr := simp)]
theorem sheafSectionsBetweenOpensGlobalIso_hom_inclusion
    (F : Sheaf AddCommGrpCat.{u} X) :
    (sheafSectionsBetweenOpensGlobalIso X h F).hom ≫
        ((sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op U) =
      ((sheafSectionsBetweenOpensInclusion X h).app F).hom.app (op ⊤) ≫
        (openRestrictionPushforwardTopEvaluationIso X U).hom.app F := by
  rw [← sheafSectionsSupportedOutsideOnOpenIso_hom_ι X V U F]
  simp only [sheafSectionsBetweenOpensGlobalIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, kernel.mapIso_hom, kernel.map,
    kernel.lift_ι]
  rw [sheafSectionsBetweenOpensOnOpenIso_hom_ι_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality in the coefficient sheaf. -/
@[reassoc]
theorem sheafSectionsBetweenOpensGlobalIso_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    (((sheafSectionsBetweenOpens X h).map f).hom.app (op ⊤)) ≫
        (sheafSectionsBetweenOpensGlobalIso X h G).hom =
      (sheafSectionsBetweenOpensGlobalIso X h F).hom ≫
        (((sheafSectionsSupportedOutside X V).map f).hom.app (op U)) := by
  have : Mono (((sheafSectionsSupportedOutsideInclusion X V).app G).hom.app (op U)) := by
    rw [← sheafSectionsSupportedOutsideOnOpenIso_hom_ι X V U G]
    infer_instance
  apply (cancel_mono (((sheafSectionsSupportedOutsideInclusion X V).app G).hom.app (op U))).1
  rw [Category.assoc, sheafSectionsBetweenOpensGlobalIso_hom_inclusion]
  have h₁ := congrArg (fun q => q.hom.app (op ⊤))
    ((sheafSectionsBetweenOpensInclusion X h).naturality f)
  have h₂ := congrArg (fun q => q.hom.app (op U))
    ((sheafSectionsSupportedOutsideInclusion X V).naturality f)
  change (((sheafSectionsSupportedOutside X V).map f).hom.app (op U)) ≫
      ((sheafSectionsSupportedOutsideInclusion X V).app G).hom.app (op U) =
    ((sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op U) ≫
      f.hom.app (op U) at h₂
  change (((sheafSectionsBetweenOpens X h).map f).hom.app (op ⊤)) ≫
      ((sheafSectionsBetweenOpensInclusion X h).app G).hom.app (op ⊤) =
    ((sheafSectionsBetweenOpensInclusion X h).app F).hom.app (op ⊤) ≫
      (((openRestrictionPushforward X U).map f).hom.app (op ⊤)) at h₁
  rw [Category.assoc, h₂, sheafSectionsBetweenOpensGlobalIso_hom_inclusion_assoc]
  rw [← Category.assoc, h₁, Category.assoc]
  exact congrArg (fun q =>
    ((sheafSectionsBetweenOpensInclusion X h).app F).hom.app (op ⊤) ≫ q)
      ((openRestrictionPushforwardTopEvaluationIso X U).hom.naturality f)

/-- Let `V ⊆ U` be open subsets of a topological space `X`. For each sheaf `F` of abelian groups,
global sections of the kernel sheaf of restriction from `U` to `V` equal sections of `F` over
`U` vanishing on `V`. This is that identification as a natural isomorphism in `F`. -/
def sheafSectionsBetweenOpensGlobalNatIso :
    sheafSectionsBetweenOpens X h ⋙ supportEvaluation X ⊤ ≅
      sheafSectionsSupportedOutside X V ⋙ supportEvaluation X U :=
  NatIso.ofComponents (sheafSectionsBetweenOpensGlobalIso X h)
    (fun f => sheafSectionsBetweenOpensGlobalIso_naturality X h f)

/-- Let `V ⊆ U` be open subsets of a topological space `X` and `K` an integer-indexed sheaf complex.
This identifies the last complex in the global sequence for supports `X \ U ⊆ X \ V` with
sections on `U` of `K` vanishing on `V`. In each degree both are the kernel of `K^q(U) →
K^q(V)`. -/
def nestedSupportRestrictionLastComplexIso
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    (nestedSupportRestrictionSectionsComplexShortComplex X h ⊤ K).X₃ ≅
      ((supportEvaluation X U).mapHomologicalComplex ℤᵘᵖ).obj
        (((sheafSectionsSupportedOutside X V).mapHomologicalComplex ℤᵘᵖ).obj K) :=
  (NatIso.mapHomologicalComplex (sheafSectionsBetweenOpensGlobalNatIso X h) ℤᵘᵖ).app K

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The last localization map, under the kernel comparison, is
restriction of the supported section to `U`. -/
@[reassoc]
theorem toSheafSectionsBetweenOpens_global_comparison
    (F : Sheaf AddCommGrpCat.{u} X) :
    ((toSheafSectionsBetweenOpens X h).app F).hom.app (op ⊤) ≫
        (sheafSectionsBetweenOpensGlobalIso X h F).hom =
      ((sheafSectionsSupportedOutside X V).obj F).obj.map (homOfLE (le_top : U ≤ ⊤)).op := by
  have : Mono (((sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op U)) := by
    rw [← sheafSectionsSupportedOutsideOnOpenIso_hom_ι X V U F]
    infer_instance
  apply (cancel_mono (((sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op U))).1
  rw [Category.assoc, sheafSectionsBetweenOpensGlobalIso_hom_inclusion]
  have hι := ((sheafSectionsSupportedOutsideInclusion X V).app F).hom.naturality
    (homOfLE (le_top : U ≤ ⊤)).op
  rw [hι, ← Category.assoc]
  have hg : ((toSheafSectionsBetweenOpens X h).app F).hom.app (op ⊤) ≫
      ((sheafSectionsBetweenOpensInclusion X h).app F).hom.app (op ⊤) =
    ((sheafSectionsSupportedOutsideInclusion X V).app F).hom.app (op ⊤) ≫
      ((toOpenRestrictionPushforward X U).app F).hom.app (op ⊤) := by
    change (((toSheafSectionsBetweenOpens X h).app F) ≫
      ((sheafSectionsBetweenOpensInclusion X h).app F)).hom.app (op ⊤) = _
    simp only [toSheafSectionsBetweenOpens, sheafSectionsBetweenOpensInclusion,
      kernel.map, kernel.lift_ι]
    rfl
  rw [hg, Category.assoc]
  congr 1
  change F.obj.map _ ≫ F.obj.map _ = F.obj.map _
  rw [← F.obj.map_comp]
  congr 1

/-- The last-complex identification retains the restriction map,
before passage to homology. -/
@[reassoc]
theorem nestedSupportRestrictionLastComplexIso_g
    (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ) :
    (nestedSupportRestrictionSectionsComplexShortComplex X h ⊤ K).g ≫
        (nestedSupportRestrictionLastComplexIso X h K).hom =
      sectionComplexRestriction X ℤᵘᵖ
        (((sheafSectionsSupportedOutside X V).mapHomologicalComplex ℤᵘᵖ).obj K)
        (homOfLE (le_top : U ≤ ⊤)) := by
  ext n : 1
  exact toSheafSectionsBetweenOpens_global_comparison X h (K.X n)

end TopCat.Sheaf
