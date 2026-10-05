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

public import Other.Algebra.FieldToComplex
public import HodgeConjecture.Definitions.AlgebraicGeometry.Hodge.Filtration
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.GlobalSections
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.Filtration
public import Other.AlgebraicGeometry.Hodge.HolomorphicDeRham
public import Other.LinearAlgebra.HodgeStructure

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Filtration, the part the statement does not need

Separated out of
`HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.Filtration`:
nothing in the statement's dependency chain uses these results, only material in
`Other` does.
-/

@[expose] public noncomputable section
open CategoryTheory Limits TopologicalSpace
open scoped TensorProduct TopCat.Sheaf
namespace AlgebraicGeometry.ComplexPoint
open Point
variable (K : Type) [Field K] [Algebra K ℂ]
variable (X : Over (Spec ↧ℂ))
attribute [local instance] analyticHasDerivedCategory
local instance : HasDerivedCategory AddCommGrpCat := HasDerivedCategory.standard _
local instance : HasDerivedCategory (ModuleCat K) := HasDerivedCategory.standard _
local instance : HasDerivedCategory
    (TopCat.Sheaf (ModuleCat K) (TopCat.of (ComplexPoint X))) := HasDerivedCategory.standard _
local instance : HasDerivedCategory (ModuleCat ℂ) := HasDerivedCategory.standard _
local instance : HasDerivedCategory
    (TopCat.Sheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X))) := HasDerivedCategory.standard _

/-- The chosen rational-linear retraction, applied to the complex constant sheaf. -/
def complexToFieldConstantSheaf :
    𝓒(↧(ComplexPoint X); ℂ) ⟶ 𝓒(↧(ComplexPoint X); K) :=
  (TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
    (AddCommGrpCat.ofHom (complexToFieldLinear K).toAddMonoidHom)

/-- The chosen retraction from the complex constant sheaf complex to the rational one. -/
def complexToFieldConstantSheafComplexInt :
    constantComplexSheafComplexIntPlus X ⟶ constantFieldSheafComplexIntPlus K X :=
  (CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)).map
    (complexToFieldConstantSheaf K X)

omit [Algebra K ℂ] in
/-- The unit in degree-zero field-valued cohomology, via the derived global-sections unit. -/
def fieldCohomologyUnit : H^0(X; K) :=
  letI Y := TopCat.of (ComplexPoint X)
  letI A := constantModuleSheaf X K
  letI s := (constantSheafAdj (Opens.grothendieckTopology Y) (ModuleCat K)
      isTerminalTop).homEquiv (ModuleCat.of K K) A
      (eqToHom (show
        (constantSheaf (Opens.grothendieckTopology Y) (ModuleCat K)).obj
            (ModuleCat.of K K) = A from rfl))
  letI t : ↥((CochainComplex.Plus.ι
      (TopCat.Sheaf (ModuleCat K) Y) ⋙
      (TopCat.Sheaf.globalSections (ModuleCat K) Y).mapHomologicalComplex ℤᵘᵖ ⋙
      HomologicalComplex.homologyFunctor (ModuleCat K) ℤᵘᵖ 0).obj
        (constantModuleSheafComplexIntPlus X K)) :=
    (TopCat.Sheaf.globalSectionsSingle₀HomologyIso (ModuleCat K) Y A).inv (s.hom 1)
  ((TopCat.Sheaf.toHypercohomology (ModuleCat K) Y 0).app
    (constantModuleSheafComplexIntPlus X K)).hom t

omit [Algebra K ℂ] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local implicit_reducible] TopCat.Sheaf in
private lemma constantModuleSheafForgetIso_unit :
    letI Y := TopCat.of (ComplexPoint X)
    letI J := Opens.grothendieckTopology Y
    (forget₂ (ModuleCat K) AddCommGrpCat).map
        ((constantSheafAdj J (ModuleCat K) isTerminalTop).unit.app (ModuleCat.of K K)) ≫
      (TopCat.Sheaf.globalSections AddCommGrpCat Y).map
        (constantModuleSheafForgetIso X K).hom =
    (constantSheafAdj J AddCommGrpCat isTerminalTop).unit.app (AddCommGrpCat.of K) := by
  let Y := TopCat.of (ComplexPoint X)
  let J := Opens.grothendieckTopology Y
  let U := forget₂ (ModuleCat K) AddCommGrpCat
  let P := (Functor.const (Opens Y)ᵒᵖ).obj (ModuleCat.of K K)
  have h := sheafComposeIso_inv_fac J U P
  have h' := toSheafify_naturality J (Functor.constComp (Opens Y)ᵒᵖ (ModuleCat.of K K) U).hom
  have hh :
      Functor.whiskerRight (toSheafify J P) U ≫
          (constantModuleSheafForgetIso X K).hom.hom =
        toSheafify J ((Functor.const (Opens Y)ᵒᵖ).obj (AddCommGrpCat.of K)) := by
    have he : (constantModuleSheafForgetIso X K).hom.hom =
        (sheafifyComposeIso J U P).inv ≫
          sheafifyMap J (Functor.constComp (Opens Y)ᵒᵖ (ModuleCat.of K K) U).hom :=
      constantCommuteCompose_hom_app_hom J U (ModuleCat.of K K)
    rw [he, ← Category.assoc, h, ← h']
    rfl
  simpa [constantSheafAdj, Adjunction.comp_unit_app, constantPresheafAdj_unit_app,
    Y, J, U, P, TopCat.Sheaf.globalSections] using
    congrArg (fun t => t.app (.op (⊤ : Opens Y))) hh

omit [Algebra K ℂ] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local implicit_reducible] TopCat.Sheaf in
private lemma constantModuleSheafForgetIso_unit_section :
    letI Y := TopCat.of (ComplexPoint X)
    letI A := constantModuleSheaf X K
    letI s := (constantSheafAdj (Opens.grothendieckTopology Y) (ModuleCat K)
      isTerminalTop).homEquiv (ModuleCat.of K K) A
      (eqToHom (show (constantSheaf (Opens.grothendieckTopology Y) (ModuleCat K)).obj
        (ModuleCat.of K K) = A from rfl))
    (constantModuleSheafForgetIso X K).hom.hom.app (.op (⊤ : Opens Y)) (s.hom 1) =
      TopCat.Sheaf.integerConstantHomAddEquivGlobalSections 𝓒(Y; K)
        ((TopCat.Sheaf.constantFunctor Y).map
          (AddCommGrpCat.ofHom (zmultiplesAddHom K 1))) := by
  dsimp only [constantModuleSheaf]
  simp only [Adjunction.homEquiv_unit, eqToHom_refl]
  have h := ConcreteCategory.congr_hom (constantModuleSheafForgetIso_unit K X) (1 : K)
  have hA := (constantSheafAdj (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
    AddCommGrpCat isTerminalTop).homEquiv_naturality_left
      (AddCommGrpCat.ofHom (zmultiplesAddHom K 1))
      (𝟙 ((constantSheaf (Opens.grothendieckTopology (TopCat.of (ComplexPoint X)))
        AddCommGrpCat).obj (AddCommGrpCat.of K)))
  simp only [Category.comp_id, Adjunction.homEquiv_id] at hA
  change _ = (((constantSheafAdj
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X))) AddCommGrpCat
      isTerminalTop).homEquiv (AddCommGrpCat.of ℤ) 𝓒(TopCat.of (ComplexPoint X); K))
    ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).map
      (AddCommGrpCat.ofHom (zmultiplesAddHom K 1)))).hom 1
  rw [hA]
  simpa [TopCat.Sheaf.globalSections] using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local implicit_reducible] TopCat.Sheaf in
/-- Forgetting coefficients sends the degree-zero unit to the class of the constant section `1`. -/
theorem constantModuleCohomologyToAdditiveEquiv_unit :
    constantModuleCohomologyToAdditiveEquiv K X 0 (fieldCohomologyUnit K X) =
      ((TopCat.Sheaf.toHypercohomology AddCommGrpCat (TopCat.of (ComplexPoint X)) 0).app
        (constantFieldSheafComplexIntPlus K X)).hom
        ((TopCat.Sheaf.globalSectionsSingle₀HomologyIso AddCommGrpCat
          (TopCat.of (ComplexPoint X)) 𝓒(↧(ComplexPoint X); K)).inv
          (TopCat.Sheaf.integerConstantHomAddEquivGlobalSections 𝓒(↧(ComplexPoint X); K)
            ((TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)).map
              (AddCommGrpCat.ofHom (zmultiplesAddHom K 1))))) := by
  let Y := TopCat.of (ComplexPoint X)
  let J := Opens.grothendieckTopology Y
  let F := forget₂ (ModuleCat K) AddCommGrpCat
  let P : TopCat.Sheaf (ModuleCat K) Y ⥤ TopCat.Sheaf AddCommGrpCat Y :=
    CategoryTheory.sheafCompose J F
  let : CharZero K := (RingHom.charZero_iff (algebraMap K ℂ).injective).2 inferInstance
  let : PreservesFiniteColimits (CategoryTheory.sheafCompose J F) := by
    exact CategoryTheory.Sheaf.moduleForget_preservesFiniteColimits J
      (ModuleCatSheafification.integerForget_sheafCompose_preservesFiniteColimits J)
  let : (CategoryTheory.sheafCompose J F).PreservesInjectiveObjects :=
    CategoryTheory.Sheaf.moduleForget_preservesInjectiveObjects_of_flat J
      (CategoryTheory.Sheaf.intAlgebraMap_flat K)
  let : P.Additive := inferInstanceAs (CategoryTheory.sheafCompose J F).Additive
  let : PreservesFiniteLimits P := inferInstanceAs
    (PreservesFiniteLimits (CategoryTheory.sheafCompose J F))
  let : PreservesFiniteColimits P := inferInstanceAs
    (PreservesFiniteColimits (CategoryTheory.sheafCompose J F))
  let : P.PreservesInjectiveObjects := inferInstanceAs
    (CategoryTheory.sheafCompose J F).PreservesInjectiveObjects
  let A := constantModuleSheaf X K
  let B := (TopCat.Sheaf.constantFunctor Y).obj (AddCommGrpCat.of K)
  let S := CochainComplex.Plus.single₀ (TopCat.Sheaf AddCommGrpCat Y)
  let Γ := TopCat.Sheaf.globalSections AddCommGrpCat Y
  let G := CochainComplex.Plus.ι (TopCat.Sheaf AddCommGrpCat Y) ⋙
    Γ.mapHomologicalComplex ℤᵘᵖ ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat ℤᵘᵖ 0
  let H := TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat Y 0
  let η := TopCat.Sheaf.toHypercohomology AddCommGrpCat Y 0
  let i := constantModuleSheafForgetIso X K
  let eM := TopCat.Sheaf.globalSectionsSingle₀HomologyIso (ModuleCat K) Y A
  let eP := TopCat.Sheaf.globalSectionsSingle₀HomologyIso AddCommGrpCat Y (P.obj A)
  let eA := TopCat.Sheaf.globalSectionsSingle₀HomologyIso AddCommGrpCat Y B
  let c := TopCat.Sheaf.hypercohomologyForget₂Iso
    (K := K) Y 0
  let AM := constantModuleSheafComplexIntPlus X K
  have hn : eP.inv ≫ G.map (S.map i.hom) = Γ.map i.hom ≫ eA.inv := by
    apply (Iso.cancel_iso_hom_right _ _ eA).1
    rw [Category.assoc]
    rw [show G.map (S.map i.hom) ≫ eA.hom = eP.hom ≫ Γ.map i.hom from
      TopCat.Sheaf.globalSectionsSingle₀HomologyIso_hom_naturality AddCommGrpCat Y i.hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have h₀ := TopCat.Sheaf.globalSectionsSingle₀_toHypercohomology_changeOfFunctor
    (X := Y) F A
  have h : F.map eM.inv ≫
      F.map ((TopCat.Sheaf.toHypercohomology (ModuleCat K) Y 0).app AM) ≫
      c.hom.app AM ≫ H.map (constantModuleSheafForgetComplexIso X K).hom =
      Γ.map i.hom ≫ eA.inv ≫ η.app (S.obj B) := by
    change F.map eM.inv ≫
      F.map ((TopCat.Sheaf.toHypercohomology (ModuleCat K) Y 0).app AM) ≫
      c.hom.app AM ≫ H.map
        ((CochainComplex.Plus.mapSingle₀Iso P A).hom ≫ S.map i.hom) = _
    rw [Functor.map_comp]
    change F.map eM.inv ≫
      F.map ((TopCat.Sheaf.toHypercohomology (ModuleCat K) Y 0).app AM) ≫
      c.hom.app AM ≫ H.map (CochainComplex.Plus.mapSingle₀Iso P A).hom =
        eP.inv ≫ η.app (S.obj (P.obj A)) at h₀
    rw [reassoc_of% h₀, ← η.naturality (S.map i.hom),
      ← Category.assoc, hn, Category.assoc]
  let s := (constantSheafAdj J (ModuleCat K) isTerminalTop).homEquiv
    (ModuleCat.of K K) A (eqToHom (show
      (constantSheaf J (ModuleCat K)).obj (ModuleCat.of K K) = A from rfl))
  have hs := ConcreteCategory.congr_hom h (s.hom 1)
  simp only [ConcreteCategory.comp_apply] at hs
  have hunit : Γ.map i.hom (s.hom 1) =
      TopCat.Sheaf.integerConstantHomAddEquivGlobalSections B
        ((TopCat.Sheaf.constantFunctor Y).map
          (AddCommGrpCat.ofHom (zmultiplesAddHom K 1))) :=
    constantModuleSheafForgetIso_unit_section K X
  have hs' := hs.trans (congrArg (fun t => η.app (S.obj B) (eA.inv t)) hunit)
  dsimp only [constantModuleCohomologyToAdditiveEquiv, fieldCohomologyUnit,
    Iso.addCommGroupIsoToAddEquiv, AddMonoidHom.toAddEquiv, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
  exact hs'

omit [Algebra K ℂ] in
/-- The degree-zero constant class associated to a field element. -/
def fieldCohomologyClass (q : K) : H^0(X; K) :=
  q • fieldCohomologyUnit K X

omit [Algebra K ℂ] in
@[simp] lemma fieldCohomologyClass_zero :
    fieldCohomologyClass K X 0 = 0 := by
  simp [fieldCohomologyClass]

omit [Algebra K ℂ] in
@[simp] lemma fieldCohomologyClass_add (a b : K) :
    fieldCohomologyClass K X (a + b) =
      fieldCohomologyClass K X a + fieldCohomologyClass K X b := by
  simpa only [fieldCohomologyClass] using
    add_smul a b (fieldCohomologyUnit K X)

/-- Extension of coefficients from rational to complex constant-sheaf cohomology. -/
def fieldToComplexCohomology (n : ℤ) :
    H^n(X; K) →+
      ↥((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
        (TopCat.of (ComplexPoint X)) n).obj (constantComplexModuleSheafIntPlus X)) :=
  (fieldToComplexCohomologyLinear K X n).toAddMonoidHom

/-- The cohomological retraction induced by the chosen rational-linear retraction `ℂ → K`. -/
def complexToFieldCohomology (n : ℤ) :
    ↥((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
      (TopCat.of (ComplexPoint X)) n).obj (constantComplexModuleSheafIntPlus X)) →+
      H^n(X; K) :=
  (constantModuleCohomologyToAdditiveEquiv K X n).symm.toAddMonoidHom.comp
    (((TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
      (TopCat.of (ComplexPoint X)) n).map
        (complexToFieldConstantSheafComplexInt K X)).hom.comp
      (constantComplexModuleCohomologyToAdditiveEquiv X n).toAddMonoidHom)

omit [Algebra K ℂ] in
/-- Constant degree-zero cohomology classes respect rational scalar multiplication. -/
lemma fieldCohomologyClass_mul (q r : K) :
    fieldCohomologyClass K X (q * r) =
      q • fieldCohomologyClass K X r := by
  simp [fieldCohomologyClass, mul_smul]

omit [Algebra K ℂ] in
/-- Rational constants map rational-linearly to degree-zero rational cohomology. -/
def fieldCohomologyClassLinear : K →ₗ[K] H^0(X; K) where
  toFun := fieldCohomologyClass K X
  map_add' := fieldCohomologyClass_add K X
  map_smul' q r := fieldCohomologyClass_mul K X q r

end AlgebraicGeometry.ComplexPoint
end

@[expose] public noncomputable section
open CategoryTheory Limits TopologicalSpace
open scoped TensorProduct TopCat.Sheaf
namespace AlgebraicGeometry.ComplexPoint
open Point
variable (K : Type) [Field K] [Algebra K ℂ]
variable (X : Over (Spec ↧ℂ))
attribute [local instance] analyticHasDerivedCategory
local instance : HasDerivedCategory AddCommGrpCat := HasDerivedCategory.standard _
local instance : HasDerivedCategory (ModuleCat K) := HasDerivedCategory.standard _
local instance : HasDerivedCategory
    (TopCat.Sheaf (ModuleCat K) (TopCat.of (ComplexPoint X))) := HasDerivedCategory.standard _
local instance : HasDerivedCategory (ModuleCat ℂ) := HasDerivedCategory.standard _
local instance : HasDerivedCategory
    (TopCat.Sheaf (ModuleCat ℂ) (TopCat.of (ComplexPoint X))) := HasDerivedCategory.standard _

/-- The rational constant sheaf is a retract of the complex constant sheaf. -/
lemma fieldToComplexConstantSheaf_comp_complexToFieldConstantSheaf :
    fieldToComplexConstantSheaf K X ≫
      complexToFieldConstantSheaf K X = 𝟙 _ := by
  let F := TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)
  change F.map (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom) ≫
    F.map (AddCommGrpCat.ofHom (complexToFieldLinear K).toAddMonoidHom) = 𝟙 _
  rw [← Functor.map_comp]
  have h : AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom ≫
      AddCommGrpCat.ofHom (complexToFieldLinear K).toAddMonoidHom =
      𝟙 (AddCommGrpCat.of K) := by
    ext q
    exact complexToFieldLinear_algebraMap K q
  rw [h]
  exact F.map_id (AddCommGrpCat.of K)

/-- The rational constant sheaf complex is a retract of the complex constant sheaf complex. -/
lemma fieldToComplexConstantSheafComplexInt_comp_complexToField :
    fieldToComplexConstantSheafComplexInt K X ≫
      complexToFieldConstantSheafComplexInt K X = 𝟙 _ := by
  rw [fieldToComplexConstantSheafComplexInt, complexToFieldConstantSheafComplexInt,
    ← Functor.map_comp, fieldToComplexConstantSheaf_comp_complexToFieldConstantSheaf]
  exact (CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)).map_id _

lemma complexConstantCohomologyDeRhamAddEquiv_apply
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : ↥((TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
      (TopCat.of (ComplexPoint X)) n).obj (constantComplexModuleSheafIntPlus X))) :
    complexConstantCohomologyDeRhamAddEquiv X n α =
      (TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
        (TopCat.of (ComplexPoint X)) n).map
        (⟨constantsToHolomorphicDeRhamModuleComplexInt X⟩ :
          constantComplexModuleSheafIntPlus X ⟶ holomorphicDeRhamModuleComplexPlus X) α :=
  rfl

set_option maxHeartbeats 2000000 in
/-- The rational-to-complex cohomology map has the displayed cohomological left inverse. -/
lemma complexToFieldCohomology_leftInverse (n : ℤ) :
    Function.LeftInverse (complexToFieldCohomology K X n)
      (fieldToComplexCohomology K X n) := by
  intro α
  dsimp only [complexToFieldCohomology, fieldToComplexCohomology,
    fieldToComplexCohomologyLinear]
  let eK := constantModuleCohomologyToAdditiveEquiv K X n
  let eC := constantComplexModuleCohomologyToAdditiveEquiv X n
  let F := TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
    (TopCat.of (ComplexPoint X)) n
  let f := fieldToComplexConstantSheafComplexInt K X
  let g := complexToFieldConstantSheafComplexInt K X
  change eK.symm (F.map g (eC (eC.symm (F.map f (eK α))))) = α
  rw [eC.apply_symm_apply, ← Functor.map_comp_apply]
  have h : f ≫ g = 𝟙 _ := fieldToComplexConstantSheafComplexInt_comp_complexToField K X
  rw [h]
  simp [eK]

/-- Extension from rational to complex constant-sheaf cohomology is injective in every degree. -/
lemma fieldToComplexCohomology_injective (n : ℤ) :
    Function.Injective (fieldToComplexCohomology K X n) :=
  (complexToFieldCohomology_leftInverse K X n).injective

/-- The rational-to-de Rham map factors through extension from rational to complex constants. -/
lemma fieldToDeRhamCohomology_factor
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : H^n(X; K)) :
    fieldToDeRhamCohomology K X n α =
      (TopCat.Sheaf.hypercohomologyFunctor (ModuleCat ℂ)
        (TopCat.of (ComplexPoint X)) n).map
        (⟨constantsToHolomorphicDeRhamModuleComplexInt X⟩ :
          constantComplexModuleSheafIntPlus X ⟶ holomorphicDeRhamModuleComplexPlus X)
        (fieldToComplexCohomology K X n α) := by
  rfl

/-- The rational-to-de Rham comparison is injective. The holomorphic Poincaré lemma supplies
the analytic quasi-isomorphism, while the explicit splitting of `K → ℂ` proves that extending
scalars is injective; no finite-dimensionality assumption is needed. -/
lemma fieldToDeRhamCohomology_injective
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Function.Injective (fieldToDeRhamCohomology K X n) := by
  exact (complexConstantCohomologyDeRhamAddEquiv X n).injective.comp
    (fieldToComplexCohomology_injective K X n)

/-- The part of the holomorphic de Rham complex in form degrees at least `p` is zero when `p`
is above the complex dimension. -/
lemma hodgeFilteredDeRhamComplex_isZero_of_lt
    [IsIntegral X.left] [Smooth X.hom] {p : ℤ} (hp : (dim X.left : ℤ) < p) :
    IsZero (hodgeFilteredDeRhamComplex X p) := by
  rw [hodgeFilteredDeRhamComplex,
    HomologicalComplex.isZero_stupidTrunc_iff]
  refine ⟨fun n => ?_⟩
  exact (holomorphicDeRhamModuleComplexInt X).isZero_of_isStrictlyLE
    (dim X.left) (p + n) (by lia)

/-- Above the complex dimension the filtered-to-full inclusion has zero source and hence is the
zero morphism. -/
lemma hodgeFilteredDeRhamInclusion_eq_zero_of_lt
    [IsIntegral X.left] [Smooth X.hom] {p : ℤ} (hp : (dim X.left : ℤ) < p) :
    hodgeFilteredDeRhamInclusion X p = 0 :=
  (hodgeFilteredDeRhamComplex_isZero_of_lt X hp).eq_of_src _ _

/-- The Hodge filtration is zero above the complex dimension. -/
lemma hodgeFiltration_eq_bot_of_lt [IsIntegral X.left] [Smooth X.hom]
    {p : ℤ} (hp : (dim X.left : ℤ) < p) (n : ℤ) :
    hodgeFiltration X p n = ⊥ := by
  change LinearMap.range (filteredToDeRhamCohomology X p n) = ⊥
  have h : (⟨hodgeFilteredDeRhamInclusion X p⟩ :
      hodgeFilteredDeRhamComplexPlus X p ⟶ holomorphicDeRhamModuleComplexPlus X) =
        (0 : hodgeFilteredDeRhamComplexPlus X p ⟶ holomorphicDeRhamModuleComplexPlus X) := by
    apply ObjectProperty.hom_ext
    exact hodgeFilteredDeRhamInclusion_eq_zero_of_lt X hp
  rw [filteredToDeRhamCohomology, h, Functor.map_zero]
  simp

set_option maxHeartbeats 800000 in
/-- Complex conjugation on constant-sheaf hypercohomology is an involution. -/
lemma complexConjugationSemilinear_involutive (n : ℤ) :
    Function.Involutive (complexConjugationSemilinear X n) := by
  intro x
  let e := constantComplexModuleCohomologyToAdditiveEquiv X n
  let F := TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
    (TopCat.of (ComplexPoint X)) n
  let j : constantComplexSheafComplexIntPlus X ⟶ constantComplexSheafComplexIntPlus X :=
    ⟨conjConstantComplexSheafComplexInt X⟩
  have hj : j ≫ j = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    exact conjConstantComplexSheafComplexInt_comp_self X
  apply e.injective
  change e (e.symm (F.map j (e (e.symm (F.map j (e x)))))) = e x
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  change F.map j (F.map j (e x)) = e x
  rw [← Functor.map_comp_apply, hj, F.map_id]
  rfl

/-- Conjugation on de Rham hypercohomology is an involution. -/
lemma deRhamConj_involutive [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    Function.Involutive (deRhamConjSemilinear X n) := by
  intro α
  let e := complexConstantCohomologyDeRhamLinearEquiv X n
  simpa [deRhamConjSemilinear, LinearMap.comp_apply] using
    congrArg e (complexConjugationSemilinear_involutive X n (e.symm α))

/-- If conjugation fixes the image of `K` in `ℂ`, it fixes the constant `K`-sheaf sitting inside
the constant `ℂ`-sheaf. -/
lemma fieldToComplexConstantSheaf_comp_conj
    (hK : ∀ q : K, starRingEnd ℂ (algebraMap K ℂ q) = algebraMap K ℂ q) :
    fieldToComplexConstantSheaf K X ≫ conjConstantComplexSheaf X =
      fieldToComplexConstantSheaf K X := by
  let F := TopCat.Sheaf.constantFunctor ↧(ComplexPoint X)
  change F.map (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom) ≫
    F.map (AddCommGrpCat.ofHom (starRingEnd ℂ).toAddMonoidHom) =
    F.map (AddCommGrpCat.ofHom (algebraMap K ℂ).toAddMonoidHom)
  rw [← Functor.map_comp]
  congr 1
  ext q
  exact hK q

/-- The same statement for the integer-indexed constant complexes. -/
lemma fieldToComplexConstantSheafComplexInt_comp_conj
    (hK : ∀ q : K, starRingEnd ℂ (algebraMap K ℂ q) = algebraMap K ℂ q) :
    fieldToComplexConstantSheafComplexInt K X ≫
        (⟨conjConstantComplexSheafComplexInt X⟩ :
          constantComplexSheafComplexIntPlus X ⟶ constantComplexSheafComplexIntPlus X) =
      fieldToComplexConstantSheafComplexInt K X := by
  change (CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)).map
        (fieldToComplexConstantSheaf K X) ≫
      (CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)).map
        (conjConstantComplexSheaf X) =
    (CochainComplex.Plus.single₀ (AnalyticAdditiveSheaf X)).map
      (fieldToComplexConstantSheaf K X)
  rw [← Functor.map_comp,
    fieldToComplexConstantSheaf_comp_conj K X hK]

set_option maxHeartbeats 2000000 in
/-- Such classes are their own conjugates in complex constant-sheaf cohomology. -/
lemma conj_fieldToComplexCohomology
    (hK : ∀ q : K, starRingEnd ℂ (algebraMap K ℂ q) = algebraMap K ℂ q)
    (n : ℤ) (α : H^n(X; K)) :
    complexConjugationSemilinear X n (fieldToComplexCohomology K X n α) =
      fieldToComplexCohomology K X n α := by
  let eK := constantModuleCohomologyToAdditiveEquiv K X n
  let eC := constantComplexModuleCohomologyToAdditiveEquiv X n
  let F := TopCat.Sheaf.hypercohomologyFunctor AddCommGrpCat
    (TopCat.of (ComplexPoint X)) n
  let f := fieldToComplexConstantSheafComplexInt K X
  let g : constantComplexSheafComplexIntPlus X ⟶ constantComplexSheafComplexIntPlus X :=
    ⟨conjConstantComplexSheafComplexInt X⟩
  change eC.symm (F.map g (eC (eC.symm (F.map f (eK α))))) =
    eC.symm (F.map f (eK α))
  rw [eC.apply_symm_apply]
  apply congrArg eC.symm
  change F.map g (F.map f (eK α)) = F.map f (eK α)
  rw [← Functor.map_comp_apply]
  have h : f ≫ g = f := fieldToComplexConstantSheafComplexInt_comp_conj K X hK
  rw [h]

/-- Such classes are their own conjugates in de Rham hypercohomology. This is the step that
makes `F^p` alone the right condition over `ℚ`. -/
lemma deRhamConj_fieldToDeRhamCohomology [IsIntegral X.left] [Smooth X.hom]
    (hK : ∀ q : K, starRingEnd ℂ (algebraMap K ℂ q) = algebraMap K ℂ q)
    (n : ℤ) (α : H^n(X; K)) :
    deRhamConjSemilinear X n (fieldToDeRhamCohomology K X n α) =
      fieldToDeRhamCohomology K X n α := by
  have he : fieldToDeRhamCohomology K X n α =
      complexConstantCohomologyDeRhamLinearEquiv X n
        (fieldToComplexCohomology K X n α) :=
    fieldToDeRhamCohomology_factor K X n α
  rw [he]
  let e := complexConstantCohomologyDeRhamLinearEquiv X n
  simpa [deRhamConjSemilinear, LinearMap.comp_apply] using
    congrArg e (conj_fieldToComplexCohomology K X hK n α)

lemma mem_hodgePiece_iff [IsIntegral X.left] [Smooth X.hom] (p q n : ℤ)
    (α : DeRhamHypercohomology X n) :
    α ∈ hodgePiece X p q n ↔
      α ∈ hodgeFiltration X p n ∧ deRhamConjSemilinear X n α ∈ hodgeFiltration X q n :=
  Iff.rfl

/-- Above the complex dimension the Hodge pieces vanish, because `F^p` already does. -/
lemma hodgePiece_eq_bot_of_lt [IsIntegral X.left] [Smooth X.hom]
    {p : ℤ} (hp : (dim X.left : ℤ) < p) (q n : ℤ) :
    hodgePiece X p q n = ⊥ := by
  refine le_antisymm (fun α hα ↦ ?_) bot_le
  have h : α ∈ hodgeFiltration X p n := hα.1
  rw [hodgeFiltration_eq_bot_of_lt X hp n, Submodule.mem_bot] at h
  exact h

/-- When conjugation fixes `K`, a `K`-class is its own conjugate, so `F^p` already implies
`(p,p)` and the Hodge filtration alone cuts out the Hodge classes. -/
lemma hodgeClasses_eq_comap_hodgeFiltration [IsIntegral X.left] [Smooth X.hom]
    (hK : ∀ q : K, starRingEnd ℂ (algebraMap K ℂ q) = algebraMap K ℂ q) (p : ℕ) :
    Hdg^p(X; K) =
      ((hodgeFiltration X p (2 * p)).restrictScalars K).comap
        (fieldToDeRhamCohomology K X (2 * p)) := by
  refine SetLike.ext fun α ↦ ?_
  show fieldToDeRhamCohomology K X (2 * (p : ℤ)) α ∈
      hodgePiece X (p : ℤ) (p : ℤ) (2 * (p : ℤ)) ↔
    fieldToDeRhamCohomology K X (2 * (p : ℤ)) α ∈
      hodgeFiltration X (p : ℤ) (2 * (p : ℤ))
  rw [mem_hodgePiece_iff, deRhamConj_fieldToDeRhamCohomology K X hK]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h⟩⟩

/-- Over `ℚ`, the coefficient field the Hodge conjecture is stated for, the `(p,p)` and `F^p`
definitions agree. -/
lemma hodgeClasses_rat_eq_comap_hodgeFiltration [IsIntegral X.left]
    [Smooth X.hom] (p : ℕ) :
    Hdg^p(X; ℚ) =
      ((hodgeFiltration X p (2 * p)).restrictScalars ℚ).comap
        (fieldToDeRhamCohomology ℚ X (2 * p)) :=
  hodgeClasses_eq_comap_hodgeFiltration ℚ X (fun q ↦ by simp) p

/-- Above the complex dimension, the rational Hodge subgroup is exactly the kernel of the
rational-to-de Rham comparison. In particular, showing that comparison injective makes the
out-of-range Hodge subgroup vanish. -/
lemma hodgeClasses_eq_ker_of_lt [IsIntegral X.left] [Smooth X.hom] {p : ℕ} (hp : dim X.left < p) :
    Hdg^p(X; K) =
      LinearMap.ker (fieldToDeRhamCohomology K X (2 * p)) := by
  rw [hodgeClasses,
    hodgePiece_eq_bot_of_lt X (by exact_mod_cast hp : (dim X.left : ℤ) < (p : ℤ)),
    Submodule.restrictScalars_bot, Submodule.comap_bot]

/-- Rational Hodge classes vanish above the complex dimension. -/
lemma hodgeClasses_eq_bot_of_lt
    [IsIntegral X.left] [Smooth X.hom]
    {p : ℕ} (hp : dim X.left < p) :
    Hdg^p(X; K) = ⊥ := by
  rw [hodgeClasses_eq_ker_of_lt K X hp]
  exact LinearMap.ker_eq_bot.mpr (fieldToDeRhamCohomology_injective K X (2 * p))

end AlgebraicGeometry.ComplexPoint
end
