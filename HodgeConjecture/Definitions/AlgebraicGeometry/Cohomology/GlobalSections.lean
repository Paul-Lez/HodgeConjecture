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

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Definitions.AlgebraicTopology.Sheaf.Constant
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SingularSheafComparison
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.FlasqueQuasiIso
public import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.InjectiveFlasque
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.SubdivisionCochain
public import HodgeConjecture.Mathlib.Algebra.Homology.MapExtend
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Singular cohomology and global sections

This file identifies rational singular cohomology with the cohomology of the global-section
complex of the sheafified singular-cochain resolution on a paracompact Hausdorff space. It also
computes the hypercohomology of that resolution on a hereditarily paracompact Hausdorff space.

The derived comparison uses a bounded-below termwise-injective replacement. The mapping-cone
argument in `Sheaf.FlasqueQuasiIso` proves that its quasi-isomorphism remains a
quasi-isomorphism after taking global sections.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace CochainComplex.HomComplex

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let `C` be a preadditive category with a zero object, `X` an object, and `K` an integer-indexed
cochain complex in `C`. This identifies the Hom complex from `X[0]` to `K` with the complex of
abelian groups `n ↦ Hom_C(X, K^n)`, whose differential is postcomposition with the differential
of `K`. -/
def fromSingleZeroIsoPreadditiveCoyoneda (X : C) (K : CochainComplex C ℤ) :
    CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj X) K ≅
      ((preadditiveCoyoneda.obj (.op X)).mapHomologicalComplex
        ℤᵘᵖ).obj K :=
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

/-- Let `Y` be a topological space and `F` a sheaf of abelian groups on `Y`. This additive
equivalence `Hom(ℤ_Y, F) ≃ Γ(Y, F)` evaluates a sheaf morphism at the constant global section
`1`. Its inverse sends a section `s` to the morphism taking each locally constant integer to the
corresponding multiple of `s`. -/
def integerConstantHomAddEquivGlobalSections
    (F : TopCat.Sheaf AddCommGrpCat Y) :
    letI : AddCommGroup ((constantFunctor Y).obj (AddCommGrpCat.of ℤ) ⟶ F) :=
      (inferInstance : Preadditive (TopCat.Sheaf AddCommGrpCat Y)).homGroup _ _
    ((constantFunctor Y).obj (AddCommGrpCat.of ℤ) ⟶ F) ≃+ F.presheaf.obj (.op (⊤ : Opens Y)) := by
  letI : AddCommGroup ((constantFunctor Y).obj (AddCommGrpCat.of ℤ) ⟶ F) :=
    (inferInstance : Preadditive (TopCat.Sheaf AddCommGrpCat Y)).homGroup _ _
  exact ((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat
      isTerminalTop).homAddEquiv (AddCommGrpCat.of ℤ) F).trans <|
    AddCommGrpCat.homAddEquiv.trans (zmultiplesAddHom (F.presheaf.obj (.op ⊤))).symm

/-- The constant-integer/global-sections equivalence is natural in the sheaf. -/
lemma integerConstantHomAddEquivGlobalSections_naturality
    {F G : TopCat.Sheaf AddCommGrpCat Y} (f : F ⟶ G)
    (g : (constantFunctor Y).obj (AddCommGrpCat.of ℤ) ⟶ F) :
    integerConstantHomAddEquivGlobalSections G (g ≫ f) =
      f.hom.app (.op (⊤ : Opens Y))
        (integerConstantHomAddEquivGlobalSections F g) := rfl

end

/-- Let `Y` be a topological space. This integer-indexed complex of sheaves of abelian groups on `Y`
has the constant integer sheaf `ℤ_Y` in degree zero, zero sheaves in every other degree, and
zero differentials. -/
def integerConstantSingleComplex (Y : TopCat.{0}) :
    CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ :=
  (CochainComplex.singleFunctor (TopCat.Sheaf AddCommGrpCat Y) 0).obj
    ((constantFunctor Y).obj (AddCommGrpCat.of ℤ))

/-- Let `Y` be a topological space and `K` an integer-indexed complex of sheaves of abelian groups
on `Y`. The complex `Γ(Y, K)` has `Γ(Y, K^n)` in degree `n`; its differentials are the maps on
global sections induced by those of `K`. -/
def globalSectionsComplexInt (Y : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) :
    -- `Γ(Y, K^•)`.
    CochainComplex AddCommGrpCat ℤ :=
  IsFlasque.BoundedBelowComplex.globalSectionsComplex K

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Let `Y` be a topological space. This natural isomorphism identifies the functors `F ↦ Hom(ℤ_Y,
F)` and `F ↦ Γ(Y, F)` on sheaves of abelian groups, by evaluating each morphism at the constant
section `1`. -/
def integerConstantHomIsoGlobalSectionsFunctor (Y : TopCat.{0}) :
    preadditiveCoyoneda.obj (.op ((constantFunctor Y).obj (AddCommGrpCat.of ℤ))) ≅
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
/-- Let `Y` be a topological space and `K` an integer-indexed complex of sheaves of abelian groups.
Evaluation at `1` gives this isomorphism of complexes `Hom^•(ℤ_Y[0], K) ≅ Γ(Y, K)`. -/
def homComplexSingleIntegerIsoGlobalSections
    (Y : TopCat.{0}) (K : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ) :
    CochainComplex.HomComplex (integerConstantSingleComplex Y) K ≅
      globalSectionsComplexInt Y K :=
  let pre := (inferInstance : Preadditive (TopCat.Sheaf AddCommGrpCat Y))
  letI : Preadditive (TopCat.Sheaf AddCommGrpCat Y) := pre
  letI : (IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda
      ((constantFunctor Y).obj (AddCommGrpCat.of ℤ)) K ≪≫
    (NatIso.mapHomologicalComplex (integerConstantHomIsoGlobalSectionsFunctor Y)
      ℤᵘᵖ).app K

end TopCat.Sheaf

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

local instance bettiGlobalSectionsHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- Let `X` be a scheme over `ℂ`. This identifies two complexes on its analytic space: the constant
integer sheaf in degree zero first indexed by natural numbers and then extended by zero, and the
same sheaf placed directly in degree zero of an integer-indexed complex. -/
def constantIntegerSheafComplexIntIsoSingle :
    constantIntegerSheafComplexInt X ≅
      TopCat.Sheaf.integerConstantSingleComplex
        (TopCat.of (ComplexPoint X)) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
    𝓒(↧(ComplexPoint X); ℤ) 0 0 rfl

end AlgebraicGeometry.ComplexPoint
