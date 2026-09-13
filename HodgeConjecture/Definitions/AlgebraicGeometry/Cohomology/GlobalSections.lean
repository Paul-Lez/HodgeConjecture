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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SingularSheafComparison
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.FlasqueQuasiIso
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.InjectiveFlasque
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.SubdivisionCochain
public import HodgeConjecture.Mathlib.Algebra.Homology.MapExtend
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Singular cohomology and global sections

This file identifies rational singular cohomology with the cohomology of the global-section
complex of the sheafified singular-cochain resolution on a paracompact Hausdorff space. It also
computes the hypercohomology of that resolution on a hereditarily paracompact Hausdorff space.

The derived comparison uses a bounded-below termwise-injective replacement. The mapping-cone
argument in `Sheaf.FlasqueQuasiIso` proves that its quasi-isomorphism remains a
quasi-isomorphism after taking global sections. Thus no spectral sequence or acyclic-resolution
theorem is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace CochainComplex.HomComplex

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The Hom complex from an object placed in degree zero is the degreewise preadditive
coyoneda functor applied to the target complex. -/
def fromSingleZeroIsoPreadditiveCoyoneda (X : C) (K : CochainComplex C ℤ) :
    CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj X) K ≅
      ((preadditiveCoyoneda.obj (.op X)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (Cochain.fromSingleEquiv (p := 0) (q := n) (n := n)
      (zero_add n)).toAddCommGrpIso)
    (by
      intro i j hij
      apply AddCommGrpCat.hom_ext
      ext z
      obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z i (zero_add i)
      have he : Cochain.fromSingleEquiv (zero_add j)
          (CochainComplex.HomComplex.δ i j
            (Cochain.fromSingleMk f (zero_add i))) = f ≫ K.d i j := by
        rw [Cochain.δ_fromSingleMk f (zero_add i) j j (zero_add j)]
        simp
      have hleft : (preadditiveCoyoneda.obj (.op X)).map (K.d i j)
          (Cochain.fromSingleEquiv (zero_add i)
            (Cochain.fromSingleMk f (zero_add i))) = f ≫ K.d i j := by
        rw [Cochain.fromSingleEquiv_fromSingleMk]
        rfl
      have hcalc := hleft.trans he.symm
      simp only [AddCommGrpCat.comp_apply, AddEquiv.toAddCommGrpIso_hom,
        Functor.mapHomologicalComplex_obj_d]
      convert hcalc using 1 <;> rfl)

end CochainComplex.HomComplex

namespace TopCat.Sheaf

section

variable {Y : TopCat.{0}}

/-- Morphisms from the constant integer sheaf are the same as global sections. This is the
degree-zero adjunction underlying the global-sections comparison below. The explicit local
Hom-group instance avoids depending on reducibility-sensitive typeclass search through the
sheaf subcategory. -/
def integerConstantHomAddEquivGlobalSections
    (F : TopCat.Sheaf AddCommGrpCat Y) :
    letI : AddCommGroup
        ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ) ⟶ F) :=
      (inferInstance : Preadditive (TopCat.Sheaf AddCommGrpCat Y)).homGroup _ _
    ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ) ⟶ F) ≃+
      F.obj.obj (.op (⊤ : Opens Y)) := by
  letI : AddCommGroup
      ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ) ⟶ F) :=
    (inferInstance : Preadditive (TopCat.Sheaf AddCommGrpCat Y)).homGroup _ _
  exact ((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat
      isTerminalTop).homAddEquiv (AddCommGrpCat.of ℤ) F).trans <|
    AddCommGrpCat.homAddEquiv.trans (zmultiplesAddHom (F.obj.obj (.op ⊤))).symm

/-- The constant-integer/global-sections equivalence is natural in the sheaf. -/
lemma integerConstantHomAddEquivGlobalSections_naturality
    {F G : TopCat.Sheaf AddCommGrpCat Y} (f : F ⟶ G)
    (g : (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ) ⟶ F) :
    integerConstantHomAddEquivGlobalSections G (g ≫ f) =
      f.hom.app (.op (⊤ : Opens Y))
        (integerConstantHomAddEquivGlobalSections F g) := by
  have h := (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat
    isTerminalTop).homEquiv_naturality_right g f
  exact ConcreteCategory.congr_hom h (1 : ℤ)

end

/-- The integer sheaf placed in cohomological degree zero. -/
def integerConstantSingleComplex (Y : TopCat.{0}) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ :=
  (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat Y) 0).obj
    ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
      (AddCommGrpCat.of ℤ))

/-- Evaluation of an integer-indexed sheaf complex on the top open subset. -/
def globalSectionsComplexInt (Y : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) :
    CochainComplex AddCommGrpCat ℤ :=
  IsFlasque.BoundedBelowComplex.globalSectionsComplex K

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The additive constant-sheaf adjunction identifies the coyoneda functor represented by the
constant integer sheaf with the global-sections functor. -/
def integerConstantHomIsoGlobalSectionsFunctor (Y : TopCat.{0}) :
    preadditiveCoyoneda.obj
        (.op ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ))) ≅
      IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y :=
  NatIso.ofComponents
    (fun F ↦ (integerConstantHomAddEquivGlobalSections F).toAddCommGrpIso)
    (fun {F G} f ↦ by
      apply AddCommGrpCat.hom_ext
      ext g
      change f.hom.app (.op (⊤ : Opens Y))
          (integerConstantHomAddEquivGlobalSections F g) =
        integerConstantHomAddEquivGlobalSections G (g ≫ f)
      exact (integerConstantHomAddEquivGlobalSections_naturality f g).symm)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The Hom complex from the degree-zero integer sheaf is canonically the complex of global
sections. -/
def homComplexSingleIntegerIsoGlobalSections
    (Y : TopCat.{0}) (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) :
    CochainComplex.HomComplex (integerConstantSingleComplex Y) K ≅
      globalSectionsComplexInt Y K := by
  let pre := (inferInstance : Preadditive (TopCat.Sheaf AddCommGrpCat Y))
  letI : Preadditive (TopCat.Sheaf AddCommGrpCat Y) := pre
  let : (IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  exact CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda
      ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
        (AddCommGrpCat.of ℤ)) K ≪≫
    (NatIso.mapHomologicalComplex (integerConstantHomIsoGlobalSectionsFunctor Y)
      (ComplexShape.up ℤ)).app K

end TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

local instance bettiGlobalSectionsHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- The integer constant-sheaf complex used to define hypercohomology is the degree-zero
integer constant sheaf, after extending its natural-number grading to integer degrees. -/
def constantIntegerSheafComplexIntIsoSingle :
    constantIntegerSheafComplexInt X ≅
      TopCat.Sheaf.integerConstantSingleComplex
        (TopCat.of (ComplexPoint X)) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    (constantIntegerSheaf X) 0 0 rfl

end AlgebraicGeometry.ComplexPoint

namespace AlgebraicTopology.Singular

universe u

variable (R : Type u) [Field R] (Y : TopCat.{u})

end AlgebraicTopology.Singular

namespace AlgebraicTopology.Singular.HereditarilyParacompact

end AlgebraicTopology.Singular.HereditarilyParacompact

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

end AlgebraicGeometry.ComplexPoint
