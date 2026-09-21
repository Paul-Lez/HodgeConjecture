/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import HodgeConjecture.Definitions.AlgebraicTopology.Support.Cohomology
public import HodgeConjecture.Definitions.AlgebraicTopology.Support.DerivedSectionsLocalization
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.FlasqueSections
public import HodgeConjecture.Mathlib.Algebra.Homology.DerivedCategory.KInjectiveHom
public import HodgeConjecture.Mathlib.Algebra.Homology.HomComplexSingle
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

/-!
# Cohomology with support computed by an injective resolution

For opens `W = V ⊓ U ≤ V`, morphisms `ℤ[V, W] → G` are the sections of `G` over `V` that vanish
on `W`, that is `Γ_{X ∖ U}(V, G)`. For a K-injective resolution `F → I` this identifies the
cohomology of the pair `H^n(V, W; F)` with `H^n(Γ_{X ∖ U}(V, I))`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Abelian Opposite TopologicalSpace

namespace TopCat.Sheaf

variable (X : TopCat.{0})

/-- `Γ_{X ∖ U}(V, G) ≅ ker(G(V) → G(W))` when `W = V ⊓ U`. -/
def supportedSectionsIsoKer (U V W : Opens X) (hW : V ⊓ U = W)
    (G : Sheaf AddCommGrpCat X) :
    ((sheafSectionsSupportedOutside X U).obj G).obj.obj (op V) ≅
      AddCommGrpCat.of (G.obj.map (homOfLE (hW ▸ inf_le_left : W ≤ V)).op).hom.ker := by
  subst hW
  exact sheafSectionsSupportedOutsideOnOpenIso X U V G ≪≫
    (kernelCompMono _ (supportedOutsideIntersectionIso X U V G).hom).symm ≪≫
    kernelIsoOfEq (toOpenRestrictionPushforward_intersection X U V G) ≪≫
    AddCommGrpCat.kernelIsoKer _

lemma supportedSectionsIsoKer_hom_subtype (U V W : Opens X) (hW : V ⊓ U = W)
    (G : Sheaf AddCommGrpCat X) :
    (supportedSectionsIsoKer X U V W hW G).hom ≫ AddCommGrpCat.ofHom (AddSubgroup.subtype _) =
      ((sheafSectionsSupportedOutsideInclusion X U).app G).hom.app (op V) := by
  subst hW
  simp [supportedSectionsIsoKer, kernelCompMono]


set_option linter.auxLemma false
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

variable (U V W : Opens X) (hW : V ⊓ U = W)

/-- The pair sheaf `ℤ[V, W]` for `W = V ⊓ U`, as an object of the site category. -/
abbrev pairSheaf' : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat :=
  CategoryTheory.Sheaf.pairSheaf (homOfLE (hW ▸ inf_le_left : W ≤ V))

/-- Evaluation of a morphism `ℤ[V, W] ⟶ G` at the generator, as a section of `G` over `V`. -/
def pairSheafHomEvaluation (G : Sheaf AddCommGrpCat X) :
    (preadditiveCoyoneda.obj (op (pairSheaf' X U V W hW))).obj G ⟶ G.obj.obj (op V) :=
  AddCommGrpCat.ofHom
    ((CategoryTheory.Sheaf.freeAbelianSheafHomAddEquiv V G).toAddMonoidHom.comp
      (preadditiveCoyoneda.map (cokernel.π _).op |>.app G).hom)

lemma pairSheafHomEvaluation_naturality {G G' : Sheaf AddCommGrpCat X} (g : G ⟶ G') :
    pairSheafHomEvaluation X U V W hW G ≫ g.hom.app (op V) =
      (preadditiveCoyoneda.obj (op (pairSheaf' X U V W hW))).map g ≫
        pairSheafHomEvaluation X U V W hW G' := rfl

/-- `Hom(ℤ[V, W], G) ≅ Γ_{X ∖ U}(V, G)`. -/
def pairSheafHomIsoSupportedSections (G : Sheaf AddCommGrpCat X) :
    (preadditiveCoyoneda.obj (op (pairSheaf' X U V W hW))).obj G ≅
      ((sheafSectionsSupportedOutside X U).obj G).obj.obj (op V) :=
  (CategoryTheory.Sheaf.pairSheafHomAddEquiv _ G).toAddCommGrpIso ≪≫
    (supportedSectionsIsoKer X U V W hW G).symm

lemma pairSheafHomIsoSupportedSections_hom_inclusion (G : Sheaf AddCommGrpCat X) :
    (pairSheafHomIsoSupportedSections X U V W hW G).hom ≫
      ((sheafSectionsSupportedOutsideInclusion X U).app G).hom.app (op V) =
      pairSheafHomEvaluation X U V W hW G := by
  rw [← supportedSectionsIsoKer_hom_subtype X U V W hW G, pairSheafHomIsoSupportedSections,
    Iso.trans_hom,
    Category.assoc, Iso.symm_hom, Iso.inv_hom_id_assoc]
  rfl

instance (G : Sheaf AddCommGrpCat X) :
    Mono (((sheafSectionsSupportedOutsideInclusion X U).app G).hom.app (op V)) := by
  rw [← sheafSectionsSupportedOutsideOnOpenIso_hom_ι]
  infer_instance

lemma pairSheafHomIsoSupportedSections_naturality {G G' : Sheaf AddCommGrpCat X} (g : G ⟶ G') :
    (pairSheafHomIsoSupportedSections X U V W hW G).hom ≫
        ((sheafSectionsSupportedOutside X U).map g).hom.app (op V) =
      (preadditiveCoyoneda.obj (op (pairSheaf' X U V W hW))).map g ≫
        (pairSheafHomIsoSupportedSections X U V W hW G').hom := by
  apply (cancel_mono (((sheafSectionsSupportedOutsideInclusion X U).app G').hom.app (op V))).1
  rw [Category.assoc, Category.assoc, pairSheafHomIsoSupportedSections_hom_inclusion,
    ← pairSheafHomEvaluation_naturality, ← pairSheafHomIsoSupportedSections_hom_inclusion,
    Category.assoc]
  congr 1
  exact (congrArg (fun h => h.hom.app (op V))
    ((sheafSectionsSupportedOutsideInclusion X U).naturality g))

/-- `Hom^•(ℤ[V, W][0], K) ≅ Γ_{X ∖ U}(V, K)` for a complex of sheaves `K`. -/
def homComplexPairSheafIsoSupportedSections
    (K : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ) :
    CochainComplex.HomComplex
        ((CochainComplex.singleFunctor _ 0).obj (pairSheaf' X U V W hW)) K ≅
      ((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
        (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj K) :=
  CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda _ K ≪≫
    HomologicalComplex.Hom.isoOfComponents
      (fun n => pairSheafHomIsoSupportedSections X U V W hW (K.X n))
      (fun i j _ => pairSheafHomIsoSupportedSections_naturality X U V W hW (K.d i j))

variable [HasExt.{1} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)]

local instance :
    HasDerivedCategory (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) :=
  HasDerivedCategory.standard _

/-- `H^n(V, W; F) ≃ H^n(Γ_{X ∖ U}(V, I))` for a K-injective resolution `F[0] → I` of `F`. -/
def relHAddEquivSupportedSectionsHomology (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (I : CochainComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) ℤ) [I.IsKInjective]
    (ι : (CochainComplex.singleFunctor _ 0).obj F ⟶ I) [QuasiIso ι] (n : ℕ) :
    CategoryTheory.Sheaf.relH F n (homOfLE (hW ▸ inf_le_left : W ≤ V)) ≃+
      (((supportEvaluation X V).mapHomologicalComplex ℤᵘᵖ).obj
        (((sheafSectionsSupportedOutside X U).mapHomologicalComplex ℤᵘᵖ).obj
          I)).homology n :=
  haveI : IsIso (DerivedCategory.Q.map ι) := (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := ι)).2
    inferInstance
  Ext.homAddEquiv.trans <|
    (show ShiftedHom (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor _ 0).obj (pairSheaf' X U V W hW)))
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj F)) (n : ℤ) ≃+
      ShiftedHom (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor _ 0).obj (pairSheaf' X U V W hW)))
        (DerivedCategory.Q.obj I) (n : ℤ) from
      isoHomCongrAddEquiv (Iso.refl _)
        ((shiftFunctor _ (n : ℤ)).mapIso (asIso (DerivedCategory.Q.map ι)))).trans <|
    (CochainComplex.kInjectiveDerivedHomAddEquivCohomologyClass _ I n).trans <|
    (CochainComplex.HomComplex.homologyAddEquiv _ I n).symm.trans
      (HomologicalComplex.homologyMapIso
        (homComplexPairSheafIsoSupportedSections X U V W hW I) n).addCommGroupIsoToAddEquiv

end TopCat.Sheaf

end
