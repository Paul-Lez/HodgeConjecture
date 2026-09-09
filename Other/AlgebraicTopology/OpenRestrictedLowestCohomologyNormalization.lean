/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.OpenRestrictedLowestCohomology
public import Other.AlgebraicTopology.CohomologySheafOpenRestriction

/-!
# Exact normalization of the lowest-degree comparison on an ambient open

The actual top-open equality transport is compatible with the canonical
cohomology-sheaf section map. No identification of cohomology groups is
supplied as data: all equality transports are those of the underlying opens.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace TopCat.Sheaf

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{u})

/-- Evaluation on equal opens, using the actual presheaf equality map. -/
def supportEvaluationEqIso {V W : Opens X} (h : V = W) :
    supportEvaluation X V ≅ supportEvaluation X W :=
  NatIso.ofComponents (fun F => F.obj.mapIso (eqToIso (congrArg op h)))
    (fun f => (f.hom.naturality _).symm)

variable (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- The same literal equality transport on the actual section complexes. -/
def sectionComplexEqIso {V W : Opens X} (h : V = W) :
    ((supportEvaluation X V).mapHomologicalComplex (.up ℤ)).obj K ≅
      ((supportEvaluation X W).mapHomologicalComplex (.up ℤ)).obj K :=
  (NatIso.mapHomologicalComplex (supportEvaluationEqIso X h) (.up ℤ)).app K

@[simp]
theorem sectionComplexEqIso_hom_refl (V : Opens X) :
    (sectionComplexEqIso X K (rfl : V = V)).hom = 𝟙 _ := by
  ext n : 1
  simp [sectionComplexEqIso, supportEvaluationEqIso]
  rfl

/-- The canonical section map respects equality of the underlying opens. -/
@[reassoc]
theorem sectionComplexEqIso_homology_section {V W : Opens X} (h : V = W) (n : ℤ) :
    homologyMap (sectionComplexEqIso X K h).hom n ≫
      sectionCohomologyToSheafSection X K n W =
    sectionCohomologyToSheafSection X K n V ≫
      (supportEvaluationEqIso X h).hom.app (K.homology n) := by
  subst W
  rw [sectionComplexEqIso_hom_refl, homologyMap_id]
  simp [supportEvaluationEqIso]

/-- In particular the actual top-open identification used by open restriction
preserves the original ambient cohomology-sheaf section map exactly. -/
@[reassoc]
theorem openRestrictionTopSectionComplexIso_homology_section (U : Opens X) (n : ℤ) :
    homologyMap (openRestrictionTopSectionComplexIso X U K).hom n ≫
      sectionCohomologyToSheafSection X K n U =
    sectionCohomologyToSheafSection X K n (U.isOpenEmbedding.functor.obj ⊤) ≫
      (openRestrictionTopSectionsIso X U).hom.app (K.homology n) :=
  sectionComplexEqIso_homology_section X K (openRestrictionTopOpen_eq X U) n

/-- The constructed lowest-degree isomorphism on an ambient open has
EXACTLY the original ambient canonical section map as its forward map.
The open restriction and its top-open transport introduce no normalization. -/
@[simp]
theorem openRestrictedLowestSectionCohomologyIso_hom (U : Opens X) (N n : ℤ)
    [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero
      ((((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℤ)).obj K).homology j))
    (hflasque : ∀ j, (K.X j).IsFlasque) :
    (openRestrictedLowestSectionCohomologyIso X U K N n hK hflasque).hom =
      sectionCohomologyToSheafSection X K n U := by
  simp only [openRestrictedLowestSectionCohomologyIso, openRestrictionHomologyTopSectionsIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    lowestSectionCohomologyIso_hom]
  change homologyMap (openRestrictionTopSectionComplexIso X U K).inv n ≫
    (sectionCohomologyToSheafSection (TopCat.of U)
      (((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).mapHomologicalComplex
        (.up ℤ)).obj K) n ⊤ ≫
      ((K.sc n).mapHomologyIso (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u})).hom.hom.app
        (op (⊤ : Opens (TopCat.of U))) ≫
      (openRestrictionTopSectionsIso X U).hom.app (K.homology n)) = _
  rw [sectionCohomologyToSheafSection_openRestriction_assoc,
    ← openRestrictionTopSectionComplexIso_homology_section]
  rw [← Category.assoc, ← homologyMap_comp, Iso.inv_hom_id,
    homologyMap_id, Category.id_comp]

end TopCat.Sheaf
