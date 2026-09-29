/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality
public import Other.Algebra.Homology.DualExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Evaluation pairing and connecting maps

Algebraic duality over a field reverses a short exact sequence of chain complexes.
Its cohomological connecting map is dual to the original homological connecting map,
with a positive sign. The proof evaluates cocycles on cycles and uses the concrete
lifting formula for both connecting maps. No finite-dimensionality is required.
-/

open CategoryTheory CategoryTheory.Limits
universe u
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Field R]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Universal coefficients is the literal evaluation of an actual dual
cycle on an actual cycle. -/
lemma linearDualHomologyEquiv_homologyπ_apply (S : ShortComplex (ModuleCat.{u} R))
    (φ : S.linearDual.cycles) (z : S.cycles) :
    S.linearDualHomologyEquiv (S.linearDual.homologyπ φ) (S.homologyπ z) =
      (show Module.Dual R S.X₂ from S.linearDual.iCycles φ) (S.iCycles z) := by
  change S.dualHomologyComparisonExplicit
    (S.linearDual.moduleCatHomologyIso.hom (S.linearDual.homologyπ φ))
    (S.moduleCatHomologyIso.hom (S.homologyπ z)) = _
  have hφ := ConcreteCategory.congr_hom (π_moduleCatCyclesIso_hom S.linearDual) φ
  have hz := ConcreteCategory.congr_hom (π_moduleCatCyclesIso_hom S) z
  change S.linearDual.moduleCatHomologyIso.hom (S.linearDual.homologyπ φ) =
    Submodule.Quotient.mk (S.linearDual.moduleCatCyclesIso.hom φ) at hφ
  change S.moduleCatHomologyIso.hom (S.homologyπ z) =
    Submodule.Quotient.mk (S.moduleCatCyclesIso.hom z) at hz
  rw [hφ, hz]
  change (show Module.Dual R S.X₂ from (S.linearDual.moduleCatCyclesIso.hom φ).val)
    (S.moduleCatCyclesIso.hom z).val = _
  have hφ' := ConcreteCategory.congr_hom (moduleCatCyclesIso_hom_i S.linearDual) φ
  have hz' := ConcreteCategory.congr_hom (moduleCatCyclesIso_hom_i S) z
  change (S.linearDual.moduleCatCyclesIso.hom φ).val = S.linearDual.iCycles φ at hφ'
  change (S.moduleCatCyclesIso.hom z).val = S.iCycles z at hz'
  rw [hφ', hz']

end CategoryTheory.ShortComplex


namespace HomologicalComplex
variable {R : Type u} [Field R]

/-- The cochain universal-coefficient map evaluates a cocycle on a cycle. -/
lemma linearDualHomologyEquiv_homologyπ_apply
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (φ : K.linearDualCochainComplex.cycles n) (z : K.cycles n) :
    linearDualHomologyEquiv K n (K.linearDualCochainComplex.homologyπ n φ)
      (K.homologyπ n z) =
      (show Module.Dual R (K.X n) from K.linearDualCochainComplex.iCycles n φ)
        (K.iCycles n z) := by
  let e := linearDualCochainComplexScIso K n
  have hπ := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality e.hom) φ
  change ShortComplex.homologyMap e.hom
      (K.linearDualCochainComplex.homologyπ n φ) =
    (K.sc n).linearDual.homologyπ (ShortComplex.cyclesMap e.hom φ) at hπ
  change (K.sc n).linearDualHomologyEquiv
    (ShortComplex.homologyMap e.hom (K.linearDualCochainComplex.homologyπ n φ))
      (K.homologyπ n z) = _
  rw [hπ]
  erw [ShortComplex.linearDualHomologyEquiv_homologyπ_apply]
  have hi := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i e.hom) φ
  change (K.sc n).linearDual.iCycles (ShortComplex.cyclesMap e.hom φ) =
    e.hom.τ₂ (K.linearDualCochainComplex.iCycles n φ) at hi
  rw [hi]
  rfl
end HomologicalComplex

namespace CategoryTheory.ShortComplex
variable {R : Type u} [Field R]

/-- Reversed degreewise algebraic dual of a short complex of chain complexes. -/
def linearDualChain (S : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ)) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (HomologicalComplex.linearDualMap S.g)
    (HomologicalComplex.linearDualMap S.f) (by
      ext n φ
      change Module.Dual R (S.X₃.X n) at φ
      apply LinearMap.ext
      intro x
      change φ (((S.f ≫ S.g).f n).hom x) = 0
      rw [S.zero]
      exact map_zero φ)

lemma linearDualChain_shortExact
    (S : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact) :
    S.linearDualChain.ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  let T := S.map (HomologicalComplex.eval (ModuleCat.{u} R) (.down ℕ) n)
  have hT : T.ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
  apply ModuleCat.shortComplex_shortExact
  · dsimp [linearDualChain, T]
    rw [LinearMap.exact_iff]
    exact (LinearMap.range_dualMap_eq_ker_dualMap_of_range_eq_ker
      T.f.hom T.g.hom hT.exact.moduleCat_range_eq_ker).symm
  · exact LinearMap.dualMap_injective_of_surjective hT.moduleCat_surjective_g
  · exact LinearMap.dualMap_surjective_of_injective hT.moduleCat_injective_f


open HomologicalComplex in
/-- The dual cohomological connecting map pairs with the homological connecting map
with a positive sign. -/
lemma linearDualChain_connecting_pairing
    (S : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact)
    (n : ℕ) (a : S.X₁.linearDualCochainComplex.homology n)
    (z : S.X₃.homology (n + 1)) :
    HomologicalComplex.linearDualHomologyEquiv S.X₃ (n + 1)
        ((linearDualChain_shortExact S hS).δ n (n + 1) rfl a) z =
      HomologicalComplex.linearDualHomologyEquiv S.X₁ n a
        (hS.δ (n + 1) n (by simp) z) := by
  obtain ⟨φ, rfl⟩ := (ModuleCat.epi_iff_surjective
    (S.X₁.linearDualCochainComplex.homologyπ n)).mp inferInstance a
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective
    (S.X₃.homologyπ (n + 1))).mp inferInstance z
  let D := S.linearDualChain
  have hD : D.ShortExact := linearDualChain_shortExact S hS
  have hSn (k : ℕ) :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS k
  have hDn (k : ℕ) :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact D).mp hD k
  let α := S.X₁.linearDualCochainComplex.iCycles n φ
  let x := S.X₃.iCycles (n + 1) w
  have hα : D.X₃.d n (n + 1) α = 0 :=
    ConcreteCategory.congr_hom (D.X₃.iCycles_d n (n + 1)) φ
  have hx : S.X₃.d (n + 1) n x = 0 :=
    ConcreteCategory.congr_hom (S.X₃.iCycles_d (n + 1) n) w
  obtain ⟨β, hβ⟩ := (hDn n).moduleCat_surjective_g α
  obtain ⟨v, hv⟩ := (hSn (n + 1)).moduleCat_surjective_g x
  have hdβ : D.g.f (n + 1) (D.X₂.d n (n + 1) β) = 0 := by
    have hc := ConcreteCategory.congr_hom (D.g.comm n (n + 1)).symm β
    change D.g.f (n + 1) (D.X₂.d n (n + 1) β) =
      D.X₃.d n (n + 1) (D.g.f n β) at hc
    change D.g.f n β = α at hβ
    rw [hc, hβ, hα]
  obtain ⟨γ, hγ⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (hDn (n + 1)).exact _ hdβ
  have hdv : S.g.f n (S.X₂.d (n + 1) n v) = 0 := by
    have hc := ConcreteCategory.congr_hom (S.g.comm (n + 1) n).symm v
    change S.g.f n (S.X₂.d (n + 1) n v) =
      S.X₃.d (n + 1) n (S.g.f (n + 1) v) at hc
    change S.g.f (n + 1) v = x at hv
    rw [hc, hv, hx]
  obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hSn n).exact _ hdv
  have hδD := hD.δ_apply n (n + 1) rfl α hα β hβ γ hγ (n + 2) (by simp)
  have hδS := hS.δ_apply (n + 1) n (by simp) x hx v hv t ht
    ((ComplexShape.down ℕ).next n) rfl
  have hφ : D.X₃.cyclesMk α (n + 1) (by simp) hα = φ := by
    apply (ModuleCat.mono_iff_injective (D.X₃.iCycles n)).mp inferInstance
    exact D.X₃.i_cyclesMk α (n + 1) (by simp) hα
  have hw : S.X₃.cyclesMk x n (by simp) hx = w := by
    apply (ModuleCat.mono_iff_injective (S.X₃.iCycles (n + 1))).mp inferInstance
    exact S.X₃.i_cyclesMk x n (by simp) hx
  rw [hφ] at hδD
  rw [hw] at hδS
  change (hD.δ n (n + 1) rfl) (D.X₃.homologyπ n φ) = _ at hδD
  change (hS.δ (n + 1) n (by simp)) (S.X₃.homologyπ (n + 1) w) = _ at hδS
  erw [hδD, hδS]
  erw [HomologicalComplex.linearDualHomologyEquiv_homologyπ_apply,
    HomologicalComplex.linearDualHomologyEquiv_homologyπ_apply]
  have hγcycles := D.X₁.i_cyclesMk γ (n + 2) (by simp)
    (hD.d_eq_zero_of_f_eq_d_apply n (n + 1) β γ hγ (n + 2))
  have htcycles := S.X₁.i_cyclesMk t ((ComplexShape.down ℕ).next n) rfl
    (hS.d_eq_zero_of_f_eq_d_apply (n + 1) n v t ht _)
  change D.X₁.iCycles (n + 1) _ = γ at hγcycles
  change S.X₁.iCycles n _ = t at htcycles
  erw [hγcycles, htcycles]
  change (show Module.Dual R (S.X₃.X (n + 1)) from γ) x =
    (show Module.Dual R (S.X₁.X n) from α) t
  change (S.g.f (n + 1)).hom.dualMap γ =
    S.X₂.linearDualCochainComplex.d n (n + 1) β at hγ
  rw [linearDualCochainComplex_d_succ] at hγ
  have he := LinearMap.congr_fun hγ v
  change S.g.f (n + 1) v = x at hv
  change S.f.f n t = S.X₂.d (n + 1) n v at ht
  change (S.f.f n).hom.dualMap β = α at hβ
  change (show Module.Dual R (S.X₃.X (n + 1)) from γ) (S.g.f (n + 1) v) =
    (show Module.Dual R (S.X₂.X n) from β) (S.X₂.d (n + 1) n v) at he
  erw [hv, ← ht] at he
  exact he.trans (LinearMap.congr_fun hβ t)

end CategoryTheory.ShortComplex
