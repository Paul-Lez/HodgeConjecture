/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# Connecting morphisms and extension by zero

This file proves that extending a short exact sequence of nonnegative cochain
complexes by zero to integer degrees preserves its connecting morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace HomologicalComplex

variable (R : Type u) [Field R]

private def elementHom (M : ModuleCat.{u} R) (x : M) :
    ModuleCat.of R R ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)

@[simp]
private lemma elementHom_apply_one (M : ModuleCat.{u} R) (x : M) :
    (elementHom (R := R) M x).hom 1 = x := by
  simp [elementHom]

@[reassoc (attr := simp)]
private lemma elementHom_comp {M N : ModuleCat.{u} R} (x : M) (f : M ⟶ N) :
    elementHom (R := R) M x ≫ f = elementHom (R := R) N (f.hom x) := by
  ext
  simp [elementHom]

@[simp]
private lemma elementHom_zero (M : ModuleCat.{u} R) :
    elementHom (R := R) M 0 = 0 := by
  ext
  simp [elementHom]

set_option backward.isDefEq.respectTransparency false in
private lemma liftCycles_elementHom_apply_one
    {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{u} R) c)
    (i j : ι) (h : c.next i = j)
    (x : LinearMap.ker (K.sc i).g.hom)
    (hx : elementHom (R := R) (K.X i) x.1 ≫ K.d i j = 0) :
    (K.liftCycles (elementHom (R := R) (K.X i) x.1) j h hx).hom 1 =
      (K.sc i).moduleCatCyclesIso.inv x := by
  apply (ModuleCat.mono_iff_injective (K.sc i).iCycles).mp inferInstance
  have hl := ConcreteCategory.congr_hom
    (K.liftCycles_i (elementHom (R := R) (K.X i) x.1) j h hx) 1
  rw [ShortComplex.moduleCatCyclesIso_inv_iCycles_apply]
  change ((K.sc i).iCycles).hom
      ((K.liftCycles (elementHom (R := R) (K.X i) x.1) j h hx).hom 1) = x.1
  change ((K.sc i).iCycles).hom
      ((K.liftCycles (elementHom (R := R) (K.X i) x.1) j h hx).hom 1) =
    (elementHom (R := R) (K.X i) x.1).hom 1 at hl
  rw [elementHom_apply_one] at hl
  exact hl

set_option backward.isDefEq.respectTransparency false in
private lemma extendCyclesIso_hom_moduleCatCyclesIso_inv
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (x : LinearMap.ker (K.sc n).g.hom)
    (xe : LinearMap.ker (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).g).hom)
    (hxe : xe.1 = (K.extendXIso ComplexShape.embeddingUpNat
      (i := n) (i' := (n : ℤ)) rfl).inv.hom x.1) :
    (K.extendCyclesIso ComplexShape.embeddingUpNat
        (j := n) (j' := (n : ℤ)) rfl).hom.hom
        (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).moduleCatCyclesIso.inv xe) =
      (K.sc n).moduleCatCyclesIso.inv x := by
  apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
  let h₀ : ComplexShape.embeddingUpNat.f n = (n : ℤ) := rfl
  have hcycles := ConcreteCategory.congr_hom
    (K.extendCyclesIso_hom_iCycles ComplexShape.embeddingUpNat
      (j := n) (j' := (n : ℤ)) h₀)
    (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).moduleCatCyclesIso.inv xe)
  have hext := ConcreteCategory.congr_hom
    (ShortComplex.moduleCatCyclesIso_inv_iCycles
      ((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ))) xe
  have hnat := ConcreteCategory.congr_hom
    (ShortComplex.moduleCatCyclesIso_inv_iCycles (K.sc n)) x
  change (K.iCycles n).hom
      ((K.extendCyclesIso ComplexShape.embeddingUpNat
        (j := n) (j' := (n : ℤ)) h₀).hom.hom
          (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).moduleCatCyclesIso.inv xe)) =
    (K.iCycles n).hom ((K.sc n).moduleCatCyclesIso.inv x)
  change (K.iCycles n).hom
      ((K.extendCyclesIso ComplexShape.embeddingUpNat
        (j := n) (j' := (n : ℤ)) h₀).hom.hom
          (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).moduleCatCyclesIso.inv xe)) =
    (K.extendXIso ComplexShape.embeddingUpNat h₀).hom.hom
      ((K.extend ComplexShape.embeddingUpNat).iCycles (n : ℤ) |>.hom
        (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).moduleCatCyclesIso.inv xe))
      at hcycles
  change ((K.extend ComplexShape.embeddingUpNat).iCycles (n : ℤ)).hom
      (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).moduleCatCyclesIso.inv xe) = xe.1
      at hext
  change (K.iCycles n).hom ((K.sc n).moduleCatCyclesIso.inv x) = x.1 at hnat
  rw [hcycles, hext, hxe, hnat]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma extendHomologyIso_hom_moduleCatHomologyClass
    (K : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (x : LinearMap.ker (K.sc n).g.hom)
    (xe : LinearMap.ker (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).g).hom)
    (hxe : xe.1 = (K.extendXIso ComplexShape.embeddingUpNat
      (i := n) (i' := (n : ℤ)) rfl).inv.hom x.1) :
    (K.extendHomologyIso ComplexShape.embeddingUpNat
        (j := n) (j' := (n : ℤ)) rfl).hom.hom
        (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).moduleCatHomologyClass xe) =
      (K.sc n).moduleCatHomologyClass x := by
  let h₀ : ComplexShape.embeddingUpNat.f n = (n : ℤ) := rfl
  change (K.extendHomologyIso ComplexShape.embeddingUpNat h₀).hom.hom
      (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).moduleCatHomologyClass xe) =
    (K.sc n).moduleCatHomologyClass x
  change (K.extendHomologyIso ComplexShape.embeddingUpNat h₀).hom.hom
      (((K.extend ComplexShape.embeddingUpNat).homologyπ (n : ℤ)).hom
        (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).moduleCatCyclesIso.inv xe)) =
    (K.homologyπ n).hom ((K.sc n).moduleCatCyclesIso.inv x)
  have hπ := ConcreteCategory.congr_hom
    (K.homologyπ_extendHomologyIso_hom ComplexShape.embeddingUpNat
      (j := n) (j' := (n : ℤ)) h₀)
    (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).moduleCatCyclesIso.inv xe)
  change (K.extendHomologyIso ComplexShape.embeddingUpNat h₀).hom.hom
      (((K.extend ComplexShape.embeddingUpNat).homologyπ (n : ℤ)).hom
        (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).moduleCatCyclesIso.inv xe)) =
    (K.homologyπ n).hom
      ((K.extendCyclesIso ComplexShape.embeddingUpNat h₀).hom.hom
        (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).moduleCatCyclesIso.inv xe))
      at hπ
  calc
    _ = (K.homologyπ n).hom
        ((K.extendCyclesIso ComplexShape.embeddingUpNat h₀).hom.hom
          (((K.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).moduleCatCyclesIso.inv xe)) := by
      simpa only using hπ
    _ = (K.homologyπ n).hom ((K.sc n).moduleCatCyclesIso.inv x) :=
      congrArg (K.homologyπ n).hom
        (extendCyclesIso_hom_moduleCatCyclesIso_inv (R := R) K n x xe hxe)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Extension by zero from nonnegative to integer degrees preserves the
connecting morphism under the canonical homology isomorphisms. -/
theorem extendShortComplex_connecting
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact)
    (hE : (S.map (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat R))).ShortExact)
    (n : ℕ) :
    hE.δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (ComplexShape.up_mk _ _ (by omega)) ≫
        (S.X₁.extendHomologyIso ComplexShape.embeddingUpNat
          (j := n + 1) (j' := ((n + 1 : ℕ) : ℤ)) rfl).hom =
      (S.X₃.extendHomologyIso ComplexShape.embeddingUpNat
          (j := n) (j' := (n : ℤ)) rfl).hom ≫
        hS.δ n (n + 1) (ComplexShape.up_mk _ _ (by omega)) := by
  let E := S.map (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat R))
  let e₁ := S.X₁.extendHomologyIso ComplexShape.embeddingUpNat
    (j := n + 1) (j' := ((n + 1 : ℕ) : ℤ)) rfl
  let e₃ := S.X₃.extendHomologyIso ComplexShape.embeddingUpNat
    (j := n) (j' := (n : ℤ)) rfl
  ext a
  obtain ⟨b, rfl⟩ := e₃.toLinearEquiv.symm.surjective a
  obtain ⟨φ, rfl⟩ := (S.X₃.sc n).moduleCatHomologyClass_surjective b
  have hSn := ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS) n
  obtain ⟨φ₂, hφ₂⟩ := (ModuleCat.epi_iff_surjective
    ((S.map (HomologicalComplex.eval (ModuleCat R) (.up ℕ) n)).g)).mp
      hSn.epi_g φ.1
  change S.X₂.X n at φ₂
  change (S.g.f n).hom φ₂ = φ.1 at hφ₂
  have hφclosed : ((S.X₃.sc n).g).hom φ.1 = 0 := LinearMap.mem_ker.mp φ.2
  change (S.X₃.d n ((ComplexShape.up ℕ).next n)).hom φ.1 = 0 at hφclosed
  rw [show (ComplexShape.up ℕ).next n = n + 1 by simp] at hφclosed
  have hφker : (S.g.f (n + 1)).hom ((S.X₂.d n (n + 1)).hom φ₂) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← S.g.comm]
    change (S.X₃.d n (n + 1)).hom ((S.g.f n).hom φ₂) = 0
    rw [hφ₂]
    exact hφclosed
  have hSnext :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS) (n + 1)
  have hSexact := hSnext.exact.moduleCat_range_eq_ker
  change LinearMap.range (S.f.f (n + 1)).hom =
    LinearMap.ker (S.g.f (n + 1)).hom at hSexact
  have hφrange : (S.X₂.d n (n + 1)).hom φ₂ ∈
      LinearMap.range (S.f.f (n + 1)).hom := by
    rw [hSexact]
    exact hφker
  obtain ⟨φ₁, hφ₁⟩ := hφrange
  have hφ₁closed : (S.X₁.d (n + 1) (n + 2)).hom φ₁ = 0 := by
    have hmono := ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS)
      (n + 2) |>.mono_f
    apply (ModuleCat.mono_iff_injective (S.f.f (n + 2))).mp hmono
    rw [map_zero, ← ConcreteCategory.comp_apply, ← S.f.comm]
    change (S.X₂.d (n + 1) (n + 2)).hom ((S.f.f (n + 1)).hom φ₁) = 0
    rw [hφ₁]
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]
    rfl
  let φ₁c : LinearMap.ker ((S.X₁.sc (n + 1)).g).hom := ⟨φ₁, by
    apply LinearMap.mem_ker.mpr
    change (S.X₁.d (n + 1) ((ComplexShape.up ℕ).next (n + 1))).hom φ₁ = 0
    rw [show (ComplexShape.up ℕ).next (n + 1) = n + 2 by simp]
    exact hφ₁closed⟩
  have hδS := hS.δ_eq n (n + 1) (ComplexShape.up_mk _ _ (by simp))
    (elementHom (R := R) (S.X₃.X n) φ.1) (by
      rw [elementHom_comp, hφclosed, elementHom_zero])
    (elementHom (R := R) (S.X₂.X n) φ₂) (by
      rw [elementHom_comp, hφ₂])
    (elementHom (R := R) (S.X₁.X (n + 1)) φ₁) (by
      rw [elementHom_comp, elementHom_comp, hφ₁])
    (n + 2) (by simp)
  have hδSclass :
      (hS.δ n (n + 1) (ComplexShape.up_mk _ _ (by simp))).hom
          ((S.X₃.sc n).moduleCatHomologyClass φ) =
        (S.X₁.sc (n + 1)).moduleCatHomologyClass φ₁c := by
    change (hS.δ n (n + 1) (ComplexShape.up_mk _ _ (by simp))).hom
        ((S.X₃.homologyπ n).hom ((S.X₃.sc n).moduleCatCyclesIso.inv φ)) =
      (S.X₁.homologyπ (n + 1)).hom
        ((S.X₁.sc (n + 1)).moduleCatCyclesIso.inv φ₁c)
    rw [← liftCycles_elementHom_apply_one (R := R) S.X₃ n (n + 1) (by simp) φ,
      ← liftCycles_elementHom_apply_one (R := R) S.X₁ (n + 1) (n + 2) (by simp) φ₁c]
    exact ConcreteCategory.congr_hom hδS 1

  let x₃e : E.X₃.X (n : ℤ) :=
    (S.X₃.extendXIso ComplexShape.embeddingUpNat
      (i := n) (i' := (n : ℤ))
      (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)).inv.hom φ.1
  have hx₃e : (E.X₃.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x₃e = 0 := by
    change ((S.X₃.extend ComplexShape.embeddingUpNat).d
      (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom _ = 0
    dsimp only [x₃e]
    rw [S.X₃.extend_d_eq ComplexShape.embeddingUpNat
      (i := n) (j := n + 1)
      (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)
      (show ComplexShape.embeddingUpNat.f (n + 1) = ((n + 1 : ℕ) : ℤ) from rfl)]
    simp [hφclosed]
  have hnext₀ : (ComplexShape.up ℤ).next (n : ℤ) = ((n + 1 : ℕ) : ℤ) := by
    apply (ComplexShape.up ℤ).next_eq'
    apply ComplexShape.up_mk
    push_cast
    omega
  let φe : LinearMap.ker ((E.X₃.sc (n : ℤ)).g).hom := ⟨x₃e, by
    apply LinearMap.mem_ker.mpr
    change (E.X₃.d (n : ℤ) ((ComplexShape.up ℤ).next (n : ℤ))).hom x₃e = 0
    rw [hnext₀]
    exact hx₃e⟩
  let x₂e : E.X₂.X (n : ℤ) :=
    (S.X₂.extendXIso ComplexShape.embeddingUpNat
      (i := n) (i' := (n : ℤ))
      (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)).inv.hom φ₂
  have hx₂e : (E.g.f (n : ℤ)).hom x₂e = x₃e := by
    change ((HomologicalComplex.extendMap S.g ComplexShape.embeddingUpNat).f (n : ℤ)).hom
      x₂e = x₃e
    dsimp only [x₂e, x₃e]
    rw [HomologicalComplex.extendMap_f S.g ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)]
    simp [hφ₂]
  let x₁e : E.X₁.X ((n + 1 : ℕ) : ℤ) :=
    (S.X₁.extendXIso ComplexShape.embeddingUpNat
      (i := n + 1) (i' := ((n + 1 : ℕ) : ℤ))
      (show ComplexShape.embeddingUpNat.f (n + 1) = ((n + 1 : ℕ) : ℤ)
        from rfl)).inv.hom φ₁
  have hx₁e : (E.f.f ((n + 1 : ℕ) : ℤ)).hom x₁e =
      (E.X₂.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x₂e := by
    change ((HomologicalComplex.extendMap S.f ComplexShape.embeddingUpNat).f
        ((n + 1 : ℕ) : ℤ)).hom x₁e =
      ((S.X₂.extend ComplexShape.embeddingUpNat).d
        (n : ℤ) ((n + 1 : ℕ) : ℤ)).hom x₂e
    dsimp only [x₁e, x₂e]
    rw [HomologicalComplex.extendMap_f S.f ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f (n + 1) = ((n + 1 : ℕ) : ℤ)
          from rfl),
      S.X₂.extend_d_eq ComplexShape.embeddingUpNat
        (i := n) (j := n + 1)
        (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)
        (show ComplexShape.embeddingUpNat.f (n + 1) = ((n + 1 : ℕ) : ℤ)
          from rfl)]
    simp [hφ₁]
  have hx₁eclosed :
      (E.X₁.d ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)).hom x₁e = 0 := by
    change ((S.X₁.extend ComplexShape.embeddingUpNat).d
      ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)).hom x₁e = 0
    dsimp only [x₁e]
    rw [S.X₁.extend_d_eq ComplexShape.embeddingUpNat
      (i := n + 1) (j := n + 2)
      (show ComplexShape.embeddingUpNat.f (n + 1) = ((n + 1 : ℕ) : ℤ) from rfl)
      (show ComplexShape.embeddingUpNat.f (n + 2) = ((n + 2 : ℕ) : ℤ) from rfl)]
    simp [hφ₁closed]
  have hnext₁ : (ComplexShape.up ℤ).next ((n + 1 : ℕ) : ℤ) =
      ((n + 2 : ℕ) : ℤ) := by
    apply (ComplexShape.up ℤ).next_eq'
    apply ComplexShape.up_mk
    push_cast
    omega
  let φ₁e : LinearMap.ker ((E.X₁.sc ((n + 1 : ℕ) : ℤ)).g).hom := ⟨x₁e, by
    apply LinearMap.mem_ker.mpr
    change (E.X₁.d ((n + 1 : ℕ) : ℤ)
      ((ComplexShape.up ℤ).next ((n + 1 : ℕ) : ℤ))).hom x₁e = 0
    rw [hnext₁]
    exact hx₁eclosed⟩
  have hδE := hE.δ_eq (n : ℤ) ((n + 1 : ℕ) : ℤ)
    (ComplexShape.up_mk _ _ (by simp))
    (elementHom (R := R) (E.X₃.X (n : ℤ)) x₃e) (by
      rw [elementHom_comp, hx₃e, elementHom_zero])
    (elementHom (R := R) (E.X₂.X (n : ℤ)) x₂e) (by
      rw [elementHom_comp, hx₂e])
    (elementHom (R := R) (E.X₁.X ((n + 1 : ℕ) : ℤ)) x₁e) (by
      rw [elementHom_comp, elementHom_comp, hx₁e])
    ((n + 2 : ℕ) : ℤ) hnext₁
  have hδEclass :
      (hE.δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (ComplexShape.up_mk _ _ (by simp))).hom
          ((E.X₃.sc (n : ℤ)).moduleCatHomologyClass φe) =
        (E.X₁.sc ((n + 1 : ℕ) : ℤ)).moduleCatHomologyClass φ₁e := by
    change (hE.δ (n : ℤ) ((n + 1 : ℕ) : ℤ)
        (ComplexShape.up_mk _ _ (by simp))).hom
        ((E.X₃.homologyπ (n : ℤ)).hom
          ((E.X₃.sc (n : ℤ)).moduleCatCyclesIso.inv φe)) =
      (E.X₁.homologyπ ((n + 1 : ℕ) : ℤ)).hom
        ((E.X₁.sc ((n + 1 : ℕ) : ℤ)).moduleCatCyclesIso.inv φ₁e)
    rw [← liftCycles_elementHom_apply_one (R := R) E.X₃ (n : ℤ)
        ((n + 1 : ℕ) : ℤ) hnext₀ φe,
      ← liftCycles_elementHom_apply_one (R := R) E.X₁ ((n + 1 : ℕ) : ℤ)
        ((n + 2 : ℕ) : ℤ) hnext₁ φ₁e]
    exact ConcreteCategory.congr_hom hδE 1
  change
    (hE.δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (ComplexShape.up_mk _ _ (by simp))).hom
        (((S.X₃.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).moduleCatHomologyClass φe) =
      (((S.X₁.extend ComplexShape.embeddingUpNat).sc
        ((n + 1 : ℕ) : ℤ)).moduleCatHomologyClass φ₁e)
    at hδEclass

  have hclass₃ := extendHomologyIso_hom_moduleCatHomologyClass
    (R := R) S.X₃ n φ φe (by rfl)
  have hclass₁ := extendHomologyIso_hom_moduleCatHomologyClass
    (R := R) S.X₁ (n + 1) φ₁c φ₁e (by rfl)
  have hclass₃inv :
      (S.X₃.extendHomologyIso ComplexShape.embeddingUpNat
        (j := n) (j' := (n : ℤ)) rfl).inv.hom
          ((S.X₃.sc n).moduleCatHomologyClass φ) =
        (((S.X₃.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).moduleCatHomologyClass φe) := by
    calc
      _ = (S.X₃.extendHomologyIso ComplexShape.embeddingUpNat
          (j := n) (j' := (n : ℤ)) rfl).inv.hom
          ((S.X₃.extendHomologyIso ComplexShape.embeddingUpNat
            (j := n) (j' := (n : ℤ)) rfl).hom.hom
            (((S.X₃.extend ComplexShape.embeddingUpNat).sc (n : ℤ)).moduleCatHomologyClass φe)) := by
        rw [hclass₃]
      _ = _ := by simp
  have hclass₃inv' :
      e₃.inv.hom ((S.X₃.sc n).moduleCatHomologyClass φ) =
        (((S.X₃.extend ComplexShape.embeddingUpNat).sc
          (n : ℤ)).moduleCatHomologyClass φe) := by
    change (S.X₃.extendHomologyIso ComplexShape.embeddingUpNat
        (j := n) (j' := (n : ℤ)) rfl).inv.hom
          ((S.X₃.sc n).moduleCatHomologyClass φ) = _
    exact hclass₃inv
  have hclass₁' :
      e₁.hom.hom
          (((S.X₁.extend ComplexShape.embeddingUpNat).sc
            ((n + 1 : ℕ) : ℤ)).moduleCatHomologyClass φ₁e) =
        (S.X₁.sc (n + 1)).moduleCatHomologyClass φ₁c := by
    change (S.X₁.extendHomologyIso ComplexShape.embeddingUpNat
        (j := n + 1) (j' := ((n + 1 : ℕ) : ℤ)) rfl).hom.hom _ = _
    exact hclass₁
  have hcancel₃ :
      e₃.hom.hom (e₃.inv.hom ((S.X₃.sc n).moduleCatHomologyClass φ)) =
        (S.X₃.sc n).moduleCatHomologyClass φ := by
    exact e₃.toLinearEquiv.apply_symm_apply _
  simp only [ConcreteCategory.comp_apply]
  change e₁.hom.hom
      ((hE.δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (ComplexShape.up_mk _ _ (by simp))).hom
        (e₃.inv.hom ((S.X₃.sc n).moduleCatHomologyClass φ))) =
    (hS.δ n (n + 1) (ComplexShape.up_mk _ _ (by simp))).hom
      (e₃.hom.hom (e₃.inv.hom ((S.X₃.sc n).moduleCatHomologyClass φ)))
  rw [hcancel₃, hclass₃inv', hδEclass, hclass₁', hδSclass]

end HomologicalComplex
