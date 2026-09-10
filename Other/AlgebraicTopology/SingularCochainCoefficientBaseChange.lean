/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularCoefficientBaseChange
public import Other.AlgebraicTopology.SingularCochainSheaf

/-!
# Cochain-level rational-to-complex coefficient extension

The chain-level base-change equivalence from rational to complex singular chains dualizes
degreewise to a map from rational singular cochains to complex singular cochains.  This file
packages that map naturally on open subsets, then sheafifies it.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open AlgebraicTopology
open scoped Simplicial

universe u

namespace AlgebraicTopology.Singular

section FieldExtension

variable (K L : Type) [Field K] [Field L] [Algebra K L]

local instance fieldExtensionChainsModule (X : TopCat) (n : ℕ) :
    Module K (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of L L)).X n) :=
  Module.compHom _ (algebraMap K L)

local instance fieldExtensionChainsScalarTower (X : TopCat) (n : ℕ) :
    IsScalarTower K L (((TopCat.toSSet.obj X).chainComplex
      (ModuleCat.of L L)).X n) :=
  IsScalarTower.of_compHom K L _

/-- Extend coefficients in a singular chain group along an arbitrary field extension. -/
def fieldToFieldChainGroup (X : TopCat) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of K K)).X n →ₗ[K]
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of L L)).X n :=
  ((chainGroupFinsuppIso L X n).symm.toLinearEquiv.restrictScalars K).toLinearMap.comp
    ((Finsupp.mapRange.linearMap (Algebra.linearMap K L)).comp
      (chainGroupFinsuppIso K X n).toLinearEquiv.toLinearMap)

@[simp]
lemma fieldToFieldChainGroup_iota (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) (q : K) :
    fieldToFieldChainGroup K L X n
        ((SSet.ιChainComplex (C := ModuleCat K) (R := ModuleCat.of K K)
          (TopCat.toSSet.obj X) x).hom q) =
      (SSet.ιChainComplex (C := ModuleCat L) (R := ModuleCat.of L L)
        (TopCat.toSSet.obj X) x).hom (algebraMap K L q) := by
  change (chainGroupFinsuppIso L X n).symm.toLinearEquiv
      ((Finsupp.mapRange.linearMap (Algebra.linearMap K L))
        ((chainGroupFinsuppIso K X n).toLinearEquiv
          ((SSet.ιChainComplex (C := ModuleCat K) (R := ModuleCat.of K K)
            (TopCat.toSSet.obj X) x).hom q))) = _
  apply (chainGroupFinsuppIso L X n).toLinearEquiv.injective
  rw [← Iso.toLinearEquiv_symm, LinearEquiv.apply_symm_apply,
    chainGroupFinsuppIso_iota, chainGroupFinsuppIso_iota]
  simp

/-- Singular chains over the larger field are the scalar extension of chains over the smaller
field. -/
lemma fieldToFieldChainGroup_isBaseChange (X : TopCat) (n : ℕ) :
    IsBaseChange L (fieldToFieldChainGroup K L X n) := by
  apply (IsBaseChange.iff_of_equiv_comm
    (chainGroupFinsuppIso K X n).toLinearEquiv
    (chainGroupFinsuppIso L X n).toLinearEquiv ?_).mpr
  · exact IsBaseChange.finsuppPow _ (IsBaseChange.linearMap K L)
  · ext z
    simp [fieldToFieldChainGroup]

/-- Generic coefficient extension commutes with a continuous map. -/
lemma fieldToFieldChainGroup_naturality {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    ModuleCat.ofHom (fieldToFieldChainGroup K L X n) ≫
        (ModuleCat.restrictScalars (algebraMap K L)).map
          ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of L L)).f n) =
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of K K)).f n ≫
        ModuleCat.ofHom (fieldToFieldChainGroup K L Y n) := by
  apply SSet.chainComplex_hom_ext
  intro x
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  change ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of L L)).f n).hom
      (fieldToFieldChainGroup K L X n
        ((SSet.ιChainComplex (C := ModuleCat K) (R := ModuleCat.of K K)
          (TopCat.toSSet.obj X) x).hom q)) =
    fieldToFieldChainGroup K L Y n
      (((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of K K)).f n).hom
        ((SSet.ιChainComplex (C := ModuleCat K) (R := ModuleCat.of K K)
          (TopCat.toSSet.obj X) x).hom q))
  rw [fieldToFieldChainGroup_iota]
  have hK := SSet.ι_chainComplexMap_f
    (X := TopCat.toSSet.obj X) (Y := TopCat.toSSet.obj Y)
    (f := TopCat.toSSet.map f) (R := ModuleCat.of K K) x
  have hL := SSet.ι_chainComplexMap_f
    (X := TopCat.toSSet.obj X) (Y := TopCat.toSSet.obj Y)
    (f := TopCat.toSSet.map f) (R := ModuleCat.of L L) x
  have hKq := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hK) q
  have hLq := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hL)
    (algebraMap K L q)
  simp only [ConcreteCategory.comp_apply] at hKq hLq
  rw [hKq, hLq, fieldToFieldChainGroup_iota]

end FieldExtension

section OpenFieldExtension

variable (K L : Type) [Field K] [Field L] [Algebra K L]

local instance openFieldExtensionChainsModule (X : TopCat) (U : (Opens X)ᵒᵖ)
    (n : ℕ) : Module K (OpenChains L X U n) :=
  Module.compHom _ (algebraMap K L)

local instance openFieldExtensionChainsScalarTower (X : TopCat)
    (U : (Opens X)ᵒᵖ) (n : ℕ) :
    IsScalarTower K L (OpenChains L X U n) :=
  IsScalarTower.of_compHom K L _

local instance openFieldExtensionDirectChainsModule (X : TopCat)
    (U : (Opens X)ᵒᵖ) (n : ℕ) :
    Module K (((TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)).chainComplex
      (ModuleCat.of L L)).X n) :=
  Module.compHom _ (algebraMap K L)

local instance openFieldExtensionDirectChainsScalarTower (X : TopCat)
    (U : (Opens X)ᵒᵖ) (n : ℕ) :
    IsScalarTower K L
      (((TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)).chainComplex
        (ModuleCat.of L L)).X n) :=
  IsScalarTower.of_compHom K L _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coefficient extension on the chain group of an open subset, with its type expressed through
the open-chain functor used by the singular-cochain presheaf. -/
def fieldToFieldOpenChainGroup (X : TopCat) (U : (Opens X)ᵒᵖ) (n : ℕ) :
    OpenChains K X U n →ₗ[K] OpenChains L X U n := by
  change ((TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)).chainComplex
      (ModuleCat.of K K)).X n →ₗ[K]
    ((TopCat.toSSet.obj ((Opens.toTopCat X).obj U.unop)).chainComplex
      (ModuleCat.of L L)).X n
  exact fieldToFieldChainGroup K L ((Opens.toTopCat X).obj U.unop) n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma fieldToFieldOpenChainGroup_isBaseChange
    (X : TopCat) (U : (Opens X)ᵒᵖ) (n : ℕ) :
    IsBaseChange L (fieldToFieldOpenChainGroup K L X U n) := by
  change IsBaseChange L
    (fieldToFieldChainGroup K L ((Opens.toTopCat X).obj U.unop) n)
  exact fieldToFieldChainGroup_isBaseChange K L
    ((Opens.toTopCat X).obj U.unop) n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Open-chain restriction commutes with extension of coefficients. -/
lemma fieldToFieldOpenChainGroup_naturality (X : TopCat)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (n : ℕ) :
    ModuleCat.ofHom (fieldToFieldOpenChainGroup K L X V n) ≫
      (ModuleCat.restrictScalars (algebraMap K L)).map
        (((openSingularChainComplexFunctor L X).map i.unop).f n) =
    ((openSingularChainComplexFunctor K X).map i.unop).f n ≫
      ModuleCat.ofHom (fieldToFieldOpenChainGroup K L X U n) := by
  change ModuleCat.ofHom
        (fieldToFieldChainGroup K L ((Opens.toTopCat X).obj V.unop) n) ≫
      (ModuleCat.restrictScalars (algebraMap K L)).map
        ((SSet.chainComplexMap
          (TopCat.toSSet.map ((Opens.toTopCat X).map i.unop))
          (ModuleCat.of L L)).f n) =
    (SSet.chainComplexMap
        (TopCat.toSSet.map ((Opens.toTopCat X).map i.unop))
        (ModuleCat.of K K)).f n ≫
      ModuleCat.ofHom
        (fieldToFieldChainGroup K L ((Opens.toTopCat X).obj U.unop) n)
  exact fieldToFieldChainGroup_naturality K L
    ((Opens.toTopCat X).map i.unop) n

end OpenFieldExtension

local instance cChainsRatModule (X : TopCat) (n : ℕ) : Module ℚ ((CChains X).X n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance cChainsRatScalarTower (X : TopCat) (n : ℕ) :
    IsScalarTower ℚ ℂ ((CChains X).X n) :=
  IsScalarTower.of_compHom ℚ ℂ _

local instance openCChainsRatModule (X : TopCat) (U : (Opens X)ᵒᵖ)
    (n : ℕ) : Module ℚ (OpenChains ℂ X U n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance openCChainsRatScalarTower (X : TopCat) (U : (Opens X)ᵒᵖ)
    (n : ℕ) : IsScalarTower ℚ ℂ (OpenChains ℂ X U n) :=
  IsScalarTower.of_compHom ℚ ℂ _

/-- The generic field-extension chain map specializes definitionally to the original rational to
complex chain map. -/
lemma fieldToFieldChainGroup_rat_complex_eq (X : TopCat) (n : ℕ) :
    fieldToFieldChainGroup ℚ ℂ X n = qToCChainGroup X n :=
  rfl

/-- Extension of singular-chain coefficients commutes with a continuous map. -/
lemma qToCChainGroup_naturality {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    ModuleCat.ofHom (qToCChainGroup X n) ≫
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map
          ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℂ ℂ)).f n) =
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f n ≫
        ModuleCat.ofHom (qToCChainGroup Y n) := by
  apply SSet.chainComplex_hom_ext
  intro x
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  change ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℂ ℂ)).f n).hom
      (qToCChainGroup X n
        ((SSet.ιChainComplex (C := ModuleCat ℚ) (R := ModuleCat.of ℚ ℚ)
          (TopCat.toSSet.obj X) x).hom q)) =
    qToCChainGroup Y n
      (((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f n).hom
        ((SSet.ιChainComplex (C := ModuleCat ℚ) (R := ModuleCat.of ℚ ℚ)
          (TopCat.toSSet.obj X) x).hom q))
  rw [qToCChainGroup_iota]
  have hQ := SSet.ι_chainComplexMap_f
    (X := TopCat.toSSet.obj X) (Y := TopCat.toSSet.obj Y)
    (f := TopCat.toSSet.map f) (R := ModuleCat.of ℚ ℚ) x
  have hC := SSet.ι_chainComplexMap_f
    (X := TopCat.toSSet.obj X) (Y := TopCat.toSSet.obj Y)
    (f := TopCat.toSSet.map f) (R := ModuleCat.of ℂ ℂ) x
  have hQq := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hQ) q
  have hCq := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hC)
    (algebraMap ℚ ℂ q)
  simp only [ConcreteCategory.comp_apply] at hQq hCq
  rw [hQq, hCq, qToCChainGroup_iota]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The preceding naturality square specialized to an inclusion of open subsets. -/
lemma qToCOpenChainGroup_naturality (X : TopCat) {U V : (Opens X)ᵒᵖ}
    (i : U ⟶ V) (n : ℕ) :
    ModuleCat.ofHom
        (fieldToFieldOpenChainGroup ℚ ℂ X V n) ≫
      (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map
        (((openSingularChainComplexFunctor ℂ X).map i.unop).f n) =
    ((openSingularChainComplexFunctor ℚ X).map i.unop).f n ≫
      ModuleCat.ofHom
        (fieldToFieldOpenChainGroup ℚ ℂ X U n) :=
  fieldToFieldOpenChainGroup_naturality ℚ ℂ X i n

/-- Extend a rational singular cochain to the unique complex-linear cochain with the same values
on rational chains. -/
def qToCOpenCochains (X : TopCat) (U : (Opens X)ᵒᵖ) (n : ℕ) :
    OpenCochains ℚ X U n →ₗ[ℚ] OpenCochains ℂ X U n :=
  fieldToFieldOpenChainGroup_isBaseChange ℚ ℂ X U n |>.toDual

@[simp]
lemma qToCOpenCochains_apply_qToCChain
    (X : TopCat) (U : (Opens X)ᵒᵖ) (n : ℕ)
    (φ : OpenCochains ℚ X U n) (c : OpenChains ℚ X U n) :
    qToCOpenCochains X U n φ
        (fieldToFieldOpenChainGroup ℚ ℂ X U n c) =
      algebraMap ℚ ℂ (φ c) :=
  IsBaseChange.toDual_comp_apply
    (fieldToFieldOpenChainGroup_isBaseChange ℚ ℂ X U n) φ c

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Extension of coefficients commutes with the singular boundary on every open subset. -/
lemma qToCOpenChainGroup_boundary
    (X : TopCat) (U : (Opens X)ᵒᵖ) (n : ℕ) (c : OpenChains ℚ X U (n + 1)) :
    (((openSingularChainComplexFunctor ℂ X).obj U.unop).d (n + 1) n).hom
        (fieldToFieldOpenChainGroup ℚ ℂ X U (n + 1) c) =
      fieldToFieldOpenChainGroup ℚ ℂ X U n
        ((((openSingularChainComplexFunctor ℚ X).obj U.unop).d (n + 1) n).hom c) := by
  change ((CChains ((Opens.toTopCat X).obj U.unop)).d (n + 1) n).hom
      (qToCChainGroup ((Opens.toTopCat X).obj U.unop) (n + 1) c) =
    qToCChainGroup ((Opens.toTopCat X).obj U.unop) n
      (((QChains ((Opens.toTopCat X).obj U.unop)).d (n + 1) n).hom c)
  have h := (qToCChainMap ((Opens.toTopCat X).obj U.unop)).comm (n + 1) n
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) c

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rational-to-complex coefficient extension as a natural map of singular-cochain presheaves in
a fixed degree. -/
def qToCSingularCochainPresheaf (X : TopCat) (n : ℕ) :
    singularCochainPresheaf ℚ X n ⟶ singularCochainPresheaf ℂ X n where
  app U := AddCommGrpCat.ofHom (qToCOpenCochains X U n).toAddMonoidHom
  naturality {U V} i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    change OpenCochains ℚ X U n at φ
    apply (fieldToFieldOpenChainGroup_isBaseChange ℚ ℂ X V n).algHom_ext
    intro c
    have hsquare := qToCOpenChainGroup_naturality X i n
    have hsquare_c := DFunLike.congr_fun
      (congrArg ModuleCat.Hom.hom hsquare) c
    change qToCOpenCochains X V n
        (((((openSingularChainComplexFunctor ℚ X).map i.unop).f n).hom.dualMap) φ)
        (fieldToFieldOpenChainGroup ℚ ℂ X V n c) =
      (((((openSingularChainComplexFunctor ℂ X).map i.unop).f n).hom.dualMap)
        (qToCOpenCochains X U n φ))
        (fieldToFieldOpenChainGroup ℚ ℂ X V n c)
    rw [qToCOpenCochains_apply_qToCChain]
    change algebraMap ℚ ℂ
        (φ (((openSingularChainComplexFunctor ℚ X).map i.unop).f n |>.hom c)) =
      qToCOpenCochains X U n φ
        (((openSingularChainComplexFunctor ℂ X).map i.unop).f n |>.hom
          (fieldToFieldOpenChainGroup ℚ ℂ X V n c))
    rw [show (((openSingularChainComplexFunctor ℂ X).map i.unop).f n).hom
          (fieldToFieldOpenChainGroup ℚ ℂ X V n c) =
        fieldToFieldOpenChainGroup ℚ ℂ X U n
          (((openSingularChainComplexFunctor ℚ X).map i.unop).f n |>.hom c) by
      change (((openSingularChainComplexFunctor ℂ X).map i.unop).f n).hom
          (fieldToFieldOpenChainGroup ℚ ℂ X V n c) =
        fieldToFieldOpenChainGroup ℚ ℂ X U n
          (((openSingularChainComplexFunctor ℚ X).map i.unop).f n |>.hom c)
        at hsquare_c
      exact hsquare_c,
      qToCOpenCochains_apply_qToCChain]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coefficient extension intertwines the rational and complex singular coboundaries. -/
lemma qToCSingularCochainPresheaf_coboundary (X : TopCat) (n : ℕ) :
    qToCSingularCochainPresheaf X n ≫ singularCochainCoboundary ℂ X n =
      singularCochainCoboundary ℚ X n ≫ qToCSingularCochainPresheaf X (n + 1) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  change OpenCochains ℚ X U n at φ
  apply (fieldToFieldOpenChainGroup_isBaseChange ℚ ℂ X U (n + 1)).algHom_ext
  intro c
  change qToCOpenCochains X U n φ
        ((((openSingularChainComplexFunctor ℂ X).obj U.unop).d (n + 1) n).hom
          (fieldToFieldOpenChainGroup ℚ ℂ X U (n + 1) c)) =
    qToCOpenCochains X U (n + 1)
        (((((openSingularChainComplexFunctor ℚ X).obj U.unop).d
          (n + 1) n).hom.dualMap) φ)
        (fieldToFieldOpenChainGroup ℚ ℂ X U (n + 1) c)
  rw [qToCOpenChainGroup_boundary, qToCOpenCochains_apply_qToCChain,
    qToCOpenCochains_apply_qToCChain]
  rfl

/-- Rational-to-complex coefficient extension as a morphism of singular-cochain presheaf
complexes. -/
def qToCSingularCochainPresheafComplex (X : TopCat) :
    singularCochainPresheafComplex ℚ X ⟶
      singularCochainPresheafComplex ℂ X where
  f n := qToCSingularCochainPresheaf X n
  comm' i j hij := by
    rw [ComplexShape.up_Rel] at hij
    obtain rfl : j = i + 1 := hij.symm
    rw [singularCochainPresheafComplex_d,
      singularCochainPresheafComplex_d]
    exact qToCSingularCochainPresheaf_coboundary X i

/-- Rational-to-complex coefficient extension on the sheafified singular-cochain complexes. -/
def qToCSingularCochainSheafComplex (X : TopCat) :
    singularCochainSheafComplex ℚ X ⟶ singularCochainSheafComplex ℂ X :=
  let J := Opens.grothendieckTopology X
  ((presheafToSheaf J AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.up ℕ)).map (qToCSingularCochainPresheafComplex X)

@[simp]
lemma qToCSingularCochainSheafComplex_f (X : TopCat) (n : ℕ) :
    (qToCSingularCochainSheafComplex X).f n =
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
        (qToCSingularCochainPresheaf X n) :=
  rfl

end AlgebraicTopology.Singular
