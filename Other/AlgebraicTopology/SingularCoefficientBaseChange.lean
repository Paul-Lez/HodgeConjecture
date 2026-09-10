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

public import HodgeConjecture.Definitions.AlgebraicTopology.SingularCohomology
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Dual.BaseChange

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Flat.IsBaseChange
import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact

/-!
# Base change for rational and complex singular cohomology

This file constructs the coefficient-extension map from rational singular chains to complex
singular chains. It proves that the induced map on homology is a base-change map. Dualizing gives
the usual rational-to-complex cohomology comparison when rational homology in the given degree is
finite-dimensional.

The finite-dimensionality hypothesis is explicit. No compactness, manifold, or projectivity
hypothesis is used to infer it.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open AlgebraicTopology
open scoped Simplicial TensorProduct

namespace AlgebraicTopology.Singular

/-- The singular chain complex with rational coefficients. -/
abbrev QChains (X : TopCat) :=
  (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)

/-- The singular chain complex with complex coefficients. -/
abbrev CChains (X : TopCat) :=
  (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℂ ℂ)

local instance (X : TopCat) (n : ℕ) : Module ℚ ((CChains X).X n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (X : TopCat) (n : ℕ) : IsScalarTower ℚ ℂ ((CChains X).X n) :=
  IsScalarTower.of_compHom ℚ ℂ _

/-- A singular chain group identified with finitely supported functions on singular simplices. -/
def chainGroupFinsuppIso (R : Type) [Field R] (X : TopCat) (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n ≅
      ModuleCat.of R (((TopCat.toSSet.obj X).obj
        (Opposite.op (SimplexCategory.mk n))) →₀ R) :=
  (SSet.isColimitChainComplexXCofan (C := ModuleCat R) (TopCat.toSSet.obj X)
      (ModuleCat.of R R) n).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit R R ((TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))))

@[simp]
lemma chainGroupFinsuppIso_iota (R : Type) [Field R] (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) (r : R) :
    (chainGroupFinsuppIso R X n).toLinearEquiv
        ((SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
          (TopCat.toSSet.obj X) x).hom r) = Finsupp.single x r := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (SSet.isColimitChainComplexXCofan (C := ModuleCat R) (TopCat.toSSet.obj X)
      (ModuleCat.of R R) n)
    (ModuleCat.finsuppCoconeIsColimit R R ((TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n)))) (Discrete.mk x)
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) r

/-- Extend the coefficients of a rational singular chain to `ℂ`. -/
def qToCChainGroup (X : TopCat) (n : ℕ) :
    (QChains X).X n →ₗ[ℚ] (CChains X).X n :=
  ((chainGroupFinsuppIso ℂ X n).symm.toLinearEquiv.restrictScalars ℚ).toLinearMap.comp
    ((Finsupp.mapRange.linearMap (Algebra.linearMap ℚ ℂ)).comp
      (chainGroupFinsuppIso ℚ X n).toLinearEquiv.toLinearMap)

@[simp]
lemma qToCChainGroup_iota (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) (q : ℚ) :
    qToCChainGroup X n
        ((SSet.ιChainComplex (C := ModuleCat ℚ) (R := ModuleCat.of ℚ ℚ)
          (TopCat.toSSet.obj X) x).hom q) =
      (SSet.ιChainComplex (C := ModuleCat ℂ) (R := ModuleCat.of ℂ ℂ)
        (TopCat.toSSet.obj X) x).hom (algebraMap ℚ ℂ q) := by
  change (chainGroupFinsuppIso ℂ X n).symm.toLinearEquiv
      ((Finsupp.mapRange.linearMap (Algebra.linearMap ℚ ℂ))
        ((chainGroupFinsuppIso ℚ X n).toLinearEquiv
          ((SSet.ιChainComplex (C := ModuleCat ℚ) (R := ModuleCat.of ℚ ℚ)
            (TopCat.toSSet.obj X) x).hom q))) = _
  apply (chainGroupFinsuppIso ℂ X n).toLinearEquiv.injective
  rw [← Iso.toLinearEquiv_symm, LinearEquiv.apply_symm_apply,
    chainGroupFinsuppIso_iota, chainGroupFinsuppIso_iota]
  simp

/-- Complex singular chains are obtained from rational singular chains by base change. -/
lemma qToCChainGroup_isBaseChange (X : TopCat) (n : ℕ) :
    IsBaseChange ℂ (qToCChainGroup X n) := by
  apply (IsBaseChange.iff_of_equiv_comm
    (chainGroupFinsuppIso ℚ X n).toLinearEquiv
    (chainGroupFinsuppIso ℂ X n).toLinearEquiv ?_).mpr
  · exact IsBaseChange.finsuppPow _ (IsBaseChange.linearMap ℚ ℂ)
  · ext z
    simp [qToCChainGroup]

/-- Complex singular chains, regarded as a chain complex of rational modules. -/
abbrev RestrictedCChains (X : TopCat) : ChainComplex (ModuleCat ℚ) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (CChains X)

/-- Coefficient extension as a morphism of singular chain complexes. -/
def qToCChainMap (X : TopCat) : QChains X ⟶ RestrictedCChains X where
  f n := ModuleCat.ofHom (qToCChainGroup X n)
  comm' i j hij := by
    rw [ComplexShape.down_Rel] at hij
    obtain rfl : i = j + 1 := hij.symm
    apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X)
    intro x
    ext
    change ((CChains X).d (j + 1) j).hom
        (qToCChainGroup X (j + 1)
          ((SSet.ιChainComplex (C := ModuleCat ℚ) (R := ModuleCat.of ℚ ℚ)
            (TopCat.toSSet.obj X) x).hom 1)) =
      qToCChainGroup X j
        (((QChains X).d (j + 1) j).hom
          ((SSet.ιChainComplex (C := ModuleCat ℚ) (R := ModuleCat.of ℚ ℚ)
            (TopCat.toSSet.obj X) x).hom 1))
    rw [qToCChainGroup_iota, map_one]
    change ((SSet.ιChainComplex (C := ModuleCat ℂ) (R := ModuleCat.of ℂ ℂ)
        (TopCat.toSSet.obj X) x ≫ (CChains X).d (j + 1) j).hom 1) = _
    rw [SSet.ιChainComplex_d]
    change _ = qToCChainGroup X j
      ((SSet.ιChainComplex (C := ModuleCat ℚ) (R := ModuleCat.of ℚ ℚ)
        (TopCat.toSSet.obj X) x ≫ (QChains X).d (j + 1) j).hom 1)
    rw [SSet.ιChainComplex_d]
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.coe_sum,
      Finset.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    change ((-1 : ℤ) ^ k.val) •
        ((SSet.ιChainComplex (C := ModuleCat ℂ) (R := ModuleCat.of ℂ ℂ)
          (TopCat.toSSet.obj X) ((SimplicialObject.δ (TopCat.toSSet.obj X) k) x)).hom 1) =
      qToCChainGroup X j (((-1 : ℤ) ^ k.val) •
        ((SSet.ιChainComplex (C := ModuleCat ℚ) (R := ModuleCat.of ℚ ℚ)
          (TopCat.toSSet.obj X) ((SimplicialObject.δ (TopCat.toSSet.obj X) k) x)).hom 1))
    rw [map_zsmul]
    refine congrArg (fun z : (CChains X).X j ↦ ((-1 : ℤ) ^ k.val) • z) ?_
    symm
    simpa using (qToCChainGroup_iota X j
      ((SimplicialObject.δ (TopCat.toSSet.obj X) k) x) 1)

/-- A canonical cycle object from the homology data of the complex chain complex. -/
abbrev CCyclesModel (X : TopCat) (n : ℕ) :=
  ((CChains X).sc n).homologyData.left.K

local instance (X : TopCat) (n : ℕ) : Module ℚ (CCyclesModel X n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (X : TopCat) (n : ℕ) : IsScalarTower ℚ ℂ (CCyclesModel X n) :=
  IsScalarTower.of_compHom ℚ ℂ _

local instance (X : TopCat) (n : ℕ) : Module ℚ ((CChains X).homology n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (X : TopCat) (n : ℕ) : IsScalarTower ℚ ℂ ((CChains X).homology n) :=
  IsScalarTower.of_compHom ℚ ℂ _

/-- Restriction of scalars commutes with the selected complex cycle object. -/
def restrictedCChainsCyclesIso (X : TopCat) (n : ℕ) :
    (RestrictedCChains X).cycles n ≅
      (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj (CCyclesModel X n) :=
  (((CChains X).sc n).homologyData.left.map
    (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).cyclesIso

/-- Restriction of scalars commutes with the selected complex homology object. -/
def restrictedCChainsHomologyIso (X : TopCat) (n : ℕ) :
    (RestrictedCChains X).homology n ≅
      (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj ((CChains X).homology n) :=
  (((CChains X).sc n).homologyData.left.map
    (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).homologyIso

/-- The coefficient-extension map on cycles. -/
def qToCCycles (X : TopCat) (n : ℕ) :
    (QChains X).cycles n →ₗ[ℚ] CCyclesModel X n :=
  (restrictedCChainsCyclesIso X n).hom.hom.comp
    (HomologicalComplex.cyclesMap (qToCChainMap X) n).hom

/-- The coefficient-extension map on singular homology. -/
def qToCHomology (X : TopCat) (n : ℕ) :
    (QChains X).homology n →ₗ[ℚ] (CChains X).homology n :=
  (HomologicalComplex.homologyMap (qToCChainMap X) n ≫
    (restrictedCChainsHomologyIso X n).hom).hom

lemma iCycles_comp_qToCChainGroup (X : TopCat) (n : ℕ) :
    (qToCChainGroup X n).comp ((QChains X).iCycles n).hom =
      (((CChains X).sc n).homologyData.left.map
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).i.hom.comp
        (qToCCycles X n) := by
  ext z
  have h₁ := DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom
      (HomologicalComplex.cyclesMap_i (qToCChainMap X) n).symm) z
  have h₂ := DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom
      (((CChains X).sc n).homologyData.left.map
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).cyclesIso_hom_comp_i)
    ((HomologicalComplex.cyclesMap (qToCChainMap X) n).hom z)
  exact h₁.trans h₂.symm

lemma restrictedCChains_homologyπ_iso (X : TopCat) (n : ℕ) :
    (RestrictedCChains X).homologyπ n ≫
        (restrictedCChainsHomologyIso X n).hom =
      (restrictedCChainsCyclesIso X n).hom ≫
        (((CChains X).sc n).homologyData.left.map
          (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).π :=
  (((CChains X).sc n).homologyData.left.map
    (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).homologyπ_comp_homologyIso_hom

lemma homologyπ_comp_qToCHomology (X : TopCat) (n : ℕ) :
    (QChains X).homologyπ n ≫ ModuleCat.ofHom (qToCHomology X n) =
      ModuleCat.ofHom (qToCCycles X n) ≫
        (((CChains X).sc n).homologyData.left.map
          (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).π := by
  change (QChains X).homologyπ n ≫
      (HomologicalComplex.homologyMap (qToCChainMap X) n ≫
        (restrictedCChainsHomologyIso X n).hom) =
    (HomologicalComplex.cyclesMap (qToCChainMap X) n ≫
      (restrictedCChainsCyclesIso X n).hom) ≫
        (((CChains X).sc n).homologyData.left.map
          (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).π
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  simp only [restrictedCChains_homologyπ_iso]
  rfl

/-- Coefficient extension from rational cycles to complex cycles is a base-change map. -/
lemma qToCCycles_isBaseChange (X : TopCat) (n : ℕ) :
    IsBaseChange ℂ (qToCCycles X n) := by
  have ht₁ : IsScalarTower ℚ ℂ (CCyclesModel X n) :=
    IsScalarTower.of_compHom ℚ ℂ _
  have ht₂ : IsScalarTower ℚ ℂ ((CChains X).X n) :=
    IsScalarTower.of_compHom ℚ ℂ _
  have ht₃ : IsScalarTower ℚ ℂ
      ((CChains X).X ((ComplexShape.down ℕ).next n)) :=
    IsScalarTower.of_compHom ℚ ℂ _
  let hQ := (QChains X).sc n |>.leftHomologyData
  let hC := (CChains X).sc n |>.homologyData.left
  refine @IsBaseChange.of_left_exact
    ℚ _ ℂ _ _
    ((QChains X).cycles n) ((QChains X).X n)
    ((QChains X).X ((ComplexShape.down ℕ).next n))
    (CCyclesModel X n) ((CChains X).X n)
    ((CChains X).X ((ComplexShape.down ℕ).next n))
    _ _ _ _ _ _
    _ _ _ _ _ _
    _ _ _ ht₁ ht₂ ht₃
    (qToCCycles X n) (qToCChainGroup X n)
    (qToCChainGroup X ((ComplexShape.down ℕ).next n))
    hQ.i.hom ((QChains X).d n ((ComplexShape.down ℕ).next n)).hom
    hC.i.hom ((CChains X).d n ((ComplexShape.down ℕ).next n)).hom
    ?_ ?_ _ (qToCChainGroup_isBaseChange X n)
    (qToCChainGroup_isBaseChange X ((ComplexShape.down ℕ).next n)) ?_ ?_ ?_ ?_
  · ext z
    exact DFunLike.congr_fun (iCycles_comp_qToCChainGroup X n) z
  · ext z
    have h := (qToCChainMap X).comm n ((ComplexShape.down ℕ).next n)
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h.symm) z
  · let T := ShortComplex.mk hQ.i ((QChains X).sc n).g hQ.wi
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp
      (T.exact_of_f_is_kernel hQ.hi)
  · exact (ModuleCat.mono_iff_injective hQ.i).mp
      (Limits.mono_of_isLimit_fork hQ.hi)
  · let T := ShortComplex.mk hC.i ((CChains X).sc n).g hC.wi
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp
      (T.exact_of_f_is_kernel hC.hi)
  · exact (ModuleCat.mono_iff_injective hC.i).mp
      (Limits.mono_of_isLimit_fork hC.hi)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma restrictedCChains_toCycles_iso (X : TopCat) (n : ℕ) :
    ((RestrictedCChains X).sc n).toCycles ≫
        (restrictedCChainsCyclesIso X n).hom =
      (((CChains X).sc n).homologyData.left.map
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).f' := by
  rw [← cancel_mono (((CChains X).sc n).homologyData.left.map
    (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).i, Category.assoc,
    show (restrictedCChainsCyclesIso X n).hom ≫
      (((CChains X).sc n).homologyData.left.map
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).i =
      ((RestrictedCChains X).sc n).iCycles from
      (((CChains X).sc n).homologyData.left.map
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).cyclesIso_hom_comp_i,
    ShortComplex.toCycles_i]
  simp only [ShortComplex.LeftHomologyData.map_f',
    ShortComplex.LeftHomologyData.map_i, ← Functor.map_comp,
    ShortComplex.LeftHomologyData.f'_i]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma toCycles_comp_qToCCycles (X : TopCat) (n : ℕ) :
    (qToCCycles X n).comp (((QChains X).sc n).toCycles.hom) =
      (((CChains X).sc n).homologyData.left.map
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).f'.hom.comp
        (qToCChainGroup X ((ComplexShape.down ℕ).prev n)) := by
  ext z
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ)
    (ComplexShape.down ℕ) n).map (qToCChainMap X)
  have h : (((QChains X).sc n).toCycles ≫
      ShortComplex.cyclesMap φ) ≫ (restrictedCChainsCyclesIso X n).hom =
      φ.τ₁ ≫ (((CChains X).sc n).homologyData.left.map
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ))).f' := by
    rw [ShortComplex.toCycles_naturality, Category.assoc, restrictedCChains_toCycles_iso]
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) z

/-- Singular homology with complex coefficients is obtained from rational singular homology by
base change. No finite-dimensionality hypothesis is needed. -/
lemma qToCHomology_isBaseChange (X : TopCat) (n : ℕ) :
    IsBaseChange ℂ (qToCHomology X n) := by
  have ht₁ : IsScalarTower ℚ ℂ
      ((CChains X).X ((ComplexShape.down ℕ).prev n)) :=
    IsScalarTower.of_compHom ℚ ℂ _
  have ht₂ : IsScalarTower ℚ ℂ (CCyclesModel X n) :=
    IsScalarTower.of_compHom ℚ ℂ _
  have ht₃ : IsScalarTower ℚ ℂ ((CChains X).homology n) :=
    IsScalarTower.of_compHom ℚ ℂ _
  let hC := (CChains X).sc n |>.homologyData.left
  refine @IsBaseChange.of_right_exact
    ℚ _ ℂ _ _
    ((QChains X).X ((ComplexShape.down ℕ).prev n)) ((QChains X).cycles n)
    ((QChains X).homology n)
    ((CChains X).X ((ComplexShape.down ℕ).prev n)) (CCyclesModel X n)
    ((CChains X).homology n)
    _ _ _ _ _ _
    _ _ _ _ _ _
    _ _ _ ht₁ ht₂ ht₃
    (qToCChainGroup X ((ComplexShape.down ℕ).prev n))
    (qToCCycles X n) (qToCHomology X n)
    ((QChains X).sc n).toCycles.hom ((QChains X).homologyπ n).hom
    hC.f'.hom hC.π.hom
    ?_ ?_ (qToCChainGroup_isBaseChange X ((ComplexShape.down ℕ).prev n))
    (qToCCycles_isBaseChange X n) ?_ ?_ ?_ ?_
  · ext z
    have hz := DFunLike.congr_fun (toCycles_comp_qToCCycles X n) z
    change qToCCycles X n (((QChains X).sc n).toCycles.hom z) =
      hC.f'.hom (qToCChainGroup X ((ComplexShape.down ℕ).prev n) z)
    rw [ShortComplex.LeftHomologyData.map_f'] at hz
    exact hz
  · ext z
    have h := homologyπ_comp_qToCHomology X n
    have hz := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom h) z
    change qToCHomology X n (((QChains X).homologyπ n).hom z) =
      hC.π.hom (qToCCycles X n z)
    rw [ShortComplex.LeftHomologyData.map_π] at hz
    exact hz
  · let T := ShortComplex.mk ((QChains X).sc n).toCycles
      ((QChains X).homologyπ n) ((QChains X).sc n).toCycles_comp_homologyπ
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp
      (T.exact_of_g_is_cokernel ((QChains X).sc n).homologyIsCokernel)
  · exact (ModuleCat.epi_iff_surjective ((QChains X).homologyπ n)).mp inferInstance
  · let T := ShortComplex.mk hC.f' hC.π hC.wπ
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp
      (T.exact_of_g_is_cokernel hC.hπ)
  · exact (ModuleCat.epi_iff_surjective hC.π).mp
      (Limits.epi_of_isColimit_cofork hC.hπ)

/-- The rational-to-complex comparison map on singular cohomology. -/
def rationalToComplexCohomologyMap (X : TopCat) (n : ℕ) :
    Cohomology ℚ X n →ₗ[ℚ] Cohomology ℂ X n :=
  (qToCHomology_isBaseChange X n).toDual

/-- If rational singular homology in degree `n` is finite-dimensional, extending rational
singular cohomology coefficients to `ℂ` gives complex singular cohomology. -/
def rationalToComplexCohomologyBaseChange (X : TopCat) (n : ℕ)
    [Module.Finite ℚ (Homology ℚ X n)] :
    ℂ ⊗[ℚ] Cohomology ℚ X n ≃ₗ[ℂ] Cohomology ℂ X n := by
  letI : Module.Finite ℚ ((QChains X).homology n) := by
    change Module.Finite ℚ (Homology ℚ X n)
    infer_instance
  exact (qToCHomology_isBaseChange X n).toDualBaseChange

end AlgebraicTopology.Singular
