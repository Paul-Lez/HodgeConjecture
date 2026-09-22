/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicTopology.LinearDualHomologyNaturality
public import HodgeConjecture.Mathlib.Algebra.Homology.DualExact
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Dual connecting morphisms

The algebraic dual of a short exact sequence of chain complexes has a cohomological
connecting morphism.  This file proves, at the level of concrete cycles, that it is paired
with the ordinary homological connecting morphism with positive sign.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace HomologicalComplex

variable {R : Type u} [Field R]

/-- Applying algebraic duals degreewise reverses a short complex of nonnegative
chain complexes. -/
def linearDualShortComplex
    (S : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ)) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (linearDualMap S.g) (linearDualMap S.f) (by
    rw [← linearDualMap_comp, S.zero]
    ext n φ
    apply LinearMap.ext
    intro x
    simp [linearDualMap])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Universal coefficients evaluates the class of an explicit cochain cocycle on the class of
an explicit chain cycle. The displayed cycle map is the canonical grading identification between
the degreewise dual complex and the reversed dual short complex. -/
lemma linearDualHomologyEquiv_moduleCatHomologyClass_apply
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (φ : LinearMap.ker (K.linearDualCochainComplex.sc n).g.hom)
    (x : LinearMap.ker (K.sc n).g.hom) :
    K.linearDualHomologyEquiv n
        ((K.linearDualCochainComplex.sc n).moduleCatHomologyClass φ)
        ((K.sc n).moduleCatHomologyClass x) =
      (show Module.Dual R ((K.sc n).X₂) from
        (ShortComplex.moduleCatCycleMap
          (linearDualCochainComplexScIso K n).hom φ).1) x.1 := by
  change (K.sc n).linearDualHomologyEquiv
    (ShortComplex.homologyMap (linearDualCochainComplexScIso K n).hom
      ((K.linearDualCochainComplex.sc n).moduleCatHomologyClass φ))
    ((K.sc n).moduleCatHomologyClass x) = _
  rw [ShortComplex.moduleCatHomologyClass_naturality]
  rw [ShortComplex.linearDualHomologyEquiv_class_apply_class]

/-- Reversing and dualizing a short exact sequence of chain complexes
produces a short exact sequence of cochain complexes. -/
lemma linearDualShortComplex_shortExact
    (S : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact) :
    (linearDualShortComplex S).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  let T := S.map
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
  have hT : T.ShortExact :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS) n
  apply ModuleCat.shortComplex_shortExact
  · dsimp [linearDualShortComplex, T, linearDualMap]
    exact LinearMap.exact_iff.mpr
      ((LinearMap.range_dualMap_eq_ker_dualMap_of_range_eq_ker
        T.f.hom T.g.hom hT.exact.moduleCat_range_eq_ker).symm)
  · dsimp [linearDualShortComplex, T, linearDualMap]
    change Function.Injective T.g.hom.dualMap
    exact LinearMap.dualMap_injective_of_surjective
      ((ModuleCat.epi_iff_surjective T.g).mp hT.epi_g)
  · dsimp [linearDualShortComplex, T, linearDualMap]
    change Function.Surjective T.f.hom.dualMap
    exact LinearMap.dualMap_surjective_of_injective
      ((ModuleCat.mono_iff_injective T.f).mp hT.mono_f)

private def moduleCatElementHom (M : ModuleCat.{u} R) (x : M) :
    ModuleCat.of R R ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)

@[simp]
private lemma moduleCatElementHom_apply_one (M : ModuleCat.{u} R) (x : M) :
    (moduleCatElementHom M x).hom 1 = x := by
  simp [moduleCatElementHom]

@[reassoc (attr := simp)]
private lemma moduleCatElementHom_comp {M N : ModuleCat.{u} R} (x : M) (f : M ⟶ N) :
    moduleCatElementHom M x ≫ f = moduleCatElementHom N (f.hom x) := by
  ext
  simp [moduleCatElementHom]

@[simp]
private lemma moduleCatElementHom_zero (M : ModuleCat.{u} R) :
    moduleCatElementHom M 0 = 0 := by
  ext
  simp [moduleCatElementHom]

set_option backward.isDefEq.respectTransparency false in
private lemma liftCycles_moduleCatElementHom_apply_one
    {c : ComplexShape ℕ} (K : HomologicalComplex (ModuleCat.{u} R) c)
    (i j : ℕ) (h : c.next i = j)
    (x : LinearMap.ker (K.sc i).g.hom)
    (hx : moduleCatElementHom (K.X i) x.1 ≫ K.d i j = 0) :
    (K.liftCycles (moduleCatElementHom (K.X i) x.1) j h hx).hom 1 =
      (K.sc i).moduleCatCyclesIso.inv x := by
  apply (ModuleCat.mono_iff_injective (K.sc i).iCycles).mp inferInstance
  have hl := ConcreteCategory.congr_hom
    (K.liftCycles_i (moduleCatElementHom (K.X i) x.1) j h hx) 1
  rw [ShortComplex.moduleCatCyclesIso_inv_iCycles_apply]
  change ((K.sc i).iCycles).hom
      ((K.liftCycles (moduleCatElementHom (K.X i) x.1) j h hx).hom 1) = x.1
  change ((K.sc i).iCycles).hom
      ((K.liftCycles (moduleCatElementHom (K.X i) x.1) j h hx).hom 1) =
    (moduleCatElementHom (K.X i) x.1).hom 1 at hl
  rw [moduleCatElementHom_apply_one] at hl
  exact hl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cohomological connecting morphism of a degreewise dual short exact
sequence is paired with the homological connecting morphism with positive
sign. No finite-dimensionality hypothesis is needed. -/
theorem linearDualShortComplex_connecting_pairing
    (S : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact)
    (n : ℕ)
    (a : (linearDualShortComplex S).X₃.homology n)
    (z : S.X₃.homology (n + 1)) :
    S.X₃.linearDualHomologyEquiv (n + 1)
        (((linearDualShortComplex_shortExact S hS).δ n (n + 1)
          (ComplexShape.up_mk n (n + 1) (by simp))).hom a) z =
      S.X₁.linearDualHomologyEquiv n a
        (((hS.δ (n + 1) n
          (ComplexShape.down_mk (n + 1) n (by simp))).hom z)) := by
  let D := linearDualShortComplex S
  let hD := linearDualShortComplex_shortExact S hS
  obtain ⟨φ, rfl⟩ := (D.X₃.sc n).moduleCatHomologyClass_surjective a
  obtain ⟨x, rfl⟩ := (S.X₃.sc (n + 1)).moduleCatHomologyClass_surjective z
  have hDn := ((HomologicalComplex.shortExact_iff_degreewise_shortExact D).mp hD) n
  obtain ⟨φ₂, hφ₂⟩ := (ModuleCat.epi_iff_surjective
    ((D.map (HomologicalComplex.eval (ModuleCat R) (.up ℕ) n)).g)).mp
      hDn.epi_g φ.1
  change D.X₂.X n at φ₂
  change (D.g.f n).hom φ₂ = φ.1 at hφ₂
  have hφclosed : ((D.X₃.sc n).g).hom φ.1 = 0 :=
    LinearMap.mem_ker.mp φ.2
  change (D.X₃.d n ((ComplexShape.up ℕ).next n)).hom φ.1 = 0 at hφclosed
  rw [show (ComplexShape.up ℕ).next n = n + 1 by simp] at hφclosed
  have hφker :
      (D.g.f (n + 1)).hom ((D.X₂.d n (n + 1)).hom φ₂) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← D.g.comm]
    change (D.X₃.d n (n + 1)).hom ((D.g.f n).hom φ₂) = 0
    rw [hφ₂]
    exact hφclosed
  have hDnext :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact D).mp hD) (n + 1)
  have hDexact := hDnext.exact.moduleCat_range_eq_ker
  change LinearMap.range (D.f.f (n + 1)).hom =
    LinearMap.ker (D.g.f (n + 1)).hom at hDexact
  have hφrange : (D.X₂.d n (n + 1)).hom φ₂ ∈
      LinearMap.range (D.f.f (n + 1)).hom := by
    rw [hDexact]
    exact hφker
  obtain ⟨φ₁, hφ₁⟩ := hφrange
  have hSn1 :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS) (n + 1)
  obtain ⟨x₂, hx₂⟩ := (ModuleCat.epi_iff_surjective
    ((S.map (HomologicalComplex.eval (ModuleCat R) (.down ℕ) (n + 1))).g)).mp
      hSn1.epi_g x.1
  change S.X₂.X (n + 1) at x₂
  change (S.g.f (n + 1)).hom x₂ = x.1 at hx₂
  have hxclosed : ((S.X₃.sc (n + 1)).g).hom x.1 = 0 :=
    LinearMap.mem_ker.mp x.2
  change (S.X₃.d (n + 1) ((ComplexShape.down ℕ).next (n + 1))).hom x.1 = 0
    at hxclosed
  rw [show (ComplexShape.down ℕ).next (n + 1) = n by simp] at hxclosed
  have hxker :
      (S.g.f n).hom ((S.X₂.d (n + 1) n).hom x₂) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← S.g.comm]
    change (S.X₃.d (n + 1) n).hom ((S.g.f (n + 1)).hom x₂) = 0
    rw [hx₂]
    exact hxclosed
  have hSn := ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS) n
  have hSexact := hSn.exact.moduleCat_range_eq_ker
  change LinearMap.range (S.f.f n).hom = LinearMap.ker (S.g.f n).hom at hSexact
  have hxrange : (S.X₂.d (n + 1) n).hom x₂ ∈
      LinearMap.range (S.f.f n).hom := by
    rw [hSexact]
    exact hxker
  obtain ⟨x₁, hx₁⟩ := hxrange
  have hφ₁closed :
      (D.X₁.d (n + 1) (n + 2)).hom φ₁ = 0 := by
    have hmono := ((HomologicalComplex.shortExact_iff_degreewise_shortExact D).mp hD)
      (n + 2) |>.mono_f
    apply (ModuleCat.mono_iff_injective (D.f.f (n + 2))).mp hmono
    rw [← ConcreteCategory.comp_apply, ← D.f.comm]
    change (D.X₂.d (n + 1) (n + 2)).hom ((D.f.f (n + 1)).hom φ₁) = 0
    rw [hφ₁]
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]
    rfl
  have hx₁closed : ((S.X₁.sc n).g).hom x₁ = 0 := by
    change (S.X₁.d n ((ComplexShape.down ℕ).next n)).hom x₁ = 0
    have hmono := ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS)
      ((ComplexShape.down ℕ).next n) |>.mono_f
    apply (ModuleCat.mono_iff_injective (S.f.f ((ComplexShape.down ℕ).next n))).mp hmono
    rw [map_zero, ← ConcreteCategory.comp_apply, ← S.f.comm]
    change (S.X₂.d n ((ComplexShape.down ℕ).next n)).hom
      ((S.f.f n).hom x₁) = 0
    rw [hx₁]
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]
    rfl
  let φ₁c : LinearMap.ker ((D.X₁.sc (n + 1)).g).hom := ⟨φ₁, by
    apply LinearMap.mem_ker.mpr
    change (D.X₁.d (n + 1) ((ComplexShape.up ℕ).next (n + 1))).hom φ₁ = 0
    rw [show (ComplexShape.up ℕ).next (n + 1) = n + 2 by simp]
    exact hφ₁closed⟩
  let x₁c : LinearMap.ker ((S.X₁.sc n).g).hom :=
    ⟨x₁, LinearMap.mem_ker.mpr hx₁closed⟩
  have hδDmap := hD.δ_eq n (n + 1)
    (ComplexShape.up_mk n (n + 1) (by simp))
    (moduleCatElementHom (D.X₃.X n) φ.1) (by
      rw [moduleCatElementHom_comp, hφclosed, moduleCatElementHom_zero])
    (moduleCatElementHom (D.X₂.X n) φ₂) (by
      rw [moduleCatElementHom_comp, hφ₂])
    (moduleCatElementHom (D.X₁.X (n + 1)) φ₁) (by
      rw [moduleCatElementHom_comp, moduleCatElementHom_comp, hφ₁])
    ((ComplexShape.up ℕ).next (n + 1)) rfl
  have hδSmap := hS.δ_eq (n + 1) n
    (ComplexShape.down_mk (n + 1) n (by simp))
    (moduleCatElementHom (S.X₃.X (n + 1)) x.1) (by
      rw [moduleCatElementHom_comp, hxclosed, moduleCatElementHom_zero])
    (moduleCatElementHom (S.X₂.X (n + 1)) x₂) (by
      rw [moduleCatElementHom_comp, hx₂])
    (moduleCatElementHom (S.X₁.X n) x₁) (by
      rw [moduleCatElementHom_comp, moduleCatElementHom_comp, hx₁])
    ((ComplexShape.down ℕ).next n) rfl
  have hδDclass :
      hD.δ n (n + 1) (ComplexShape.up_mk n (n + 1) (by simp))
          ((D.X₃.sc n).moduleCatHomologyClass φ) =
        (D.X₁.sc (n + 1)).moduleCatHomologyClass φ₁c := by
    change (hD.δ n (n + 1) (ComplexShape.up_mk n (n + 1) (by simp))).hom
        ((D.X₃.homologyπ n).hom ((D.X₃.sc n).moduleCatCyclesIso.inv φ)) =
      (D.X₁.homologyπ (n + 1)).hom
        ((D.X₁.sc (n + 1)).moduleCatCyclesIso.inv φ₁c)
    rw [← liftCycles_moduleCatElementHom_apply_one D.X₃ n (n + 1) (by simp) φ,
      ← liftCycles_moduleCatElementHom_apply_one D.X₁ (n + 1)
        ((ComplexShape.up ℕ).next (n + 1)) rfl φ₁c]
    exact ConcreteCategory.congr_hom hδDmap 1
  have hδSclass :
      hS.δ (n + 1) n (ComplexShape.down_mk (n + 1) n (by simp))
          ((S.X₃.sc (n + 1)).moduleCatHomologyClass x) =
        (S.X₁.sc n).moduleCatHomologyClass x₁c := by
    change (hS.δ (n + 1) n (ComplexShape.down_mk (n + 1) n (by simp))).hom
        ((S.X₃.homologyπ (n + 1)).hom ((S.X₃.sc (n + 1)).moduleCatCyclesIso.inv x)) =
      (S.X₁.homologyπ n).hom ((S.X₁.sc n).moduleCatCyclesIso.inv x₁c)
    rw [← liftCycles_moduleCatElementHom_apply_one S.X₃ (n + 1) n (by simp) x,
      ← liftCycles_moduleCatElementHom_apply_one S.X₁ n
        ((ComplexShape.down ℕ).next n) rfl x₁c]
    exact ConcreteCategory.congr_hom hδSmap 1
  rw [hδDclass, hδSclass]
  dsimp only [D, linearDualShortComplex] at φ φ₁c ⊢
  rw [linearDualHomologyEquiv_moduleCatHomologyClass_apply,
    linearDualHomologyEquiv_moduleCatHomologyClass_apply]
  change Module.Dual R (S.X₃.X (n + 1)) at φ₁
  change Module.Dual R (S.X₂.X n) at φ₂
  let φ₀ : Module.Dual R (S.X₁.X n) := φ.1
  change φ₁.comp (S.g.f (n + 1)).hom =
    φ₂.comp (S.X₂.d (n + 1) n).hom at hφ₁
  change φ₂.comp (S.f.f n).hom = φ₀ at hφ₂
  change φ₁ x.1 = φ₀ x₁
  calc
    φ₁ x.1 = φ₁ ((S.g.f (n + 1)).hom x₂) := congrArg φ₁ hx₂.symm
    _ = (φ₁.comp (S.g.f (n + 1)).hom) x₂ := rfl
    _ = (φ₂.comp (S.X₂.d (n + 1) n).hom) x₂ :=
      congrArg (fun q => q x₂) hφ₁
    _ = φ₂ ((S.X₂.d (n + 1) n).hom x₂) := rfl
    _ = φ₂ ((S.f.f n).hom x₁) := congrArg φ₂ hx₁.symm
    _ = (φ₂.comp (S.f.f n).hom) x₁ := rfl
    _ = φ₀ x₁ := congrArg (fun q => q x₁) hφ₂


end HomologicalComplex
