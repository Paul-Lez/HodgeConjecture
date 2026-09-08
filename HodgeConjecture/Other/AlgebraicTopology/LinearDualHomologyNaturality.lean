/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Other.AlgebraicTopology.SingularCochainCohomology
public import HodgeConjecture.Other.AlgebraicTopology.SingularSubdivisionCochainSheaf

/-! # Naturality of the actual universal-coefficient pairing -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Field R] {S T : ShortComplex (ModuleCat.{u} R)}

/-- Reverse algebraic dual of a short-complex map. -/
def linearDualMap (f : S ⟶ T) : T.linearDual ⟶ S.linearDual where
  τ₁ := ModuleCat.ofHom f.τ₃.hom.dualMap
  τ₂ := ModuleCat.ofHom f.τ₂.hom.dualMap
  τ₃ := ModuleCat.ofHom f.τ₁.hom.dualMap
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change Module.Dual R T.X₃ at φ
    apply LinearMap.ext
    intro x
    exact congrArg φ (ConcreteCategory.congr_hom f.comm₂₃ x).symm
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change Module.Dual R T.X₂ at φ
    apply LinearMap.ext
    intro x
    exact congrArg φ (ConcreteCategory.congr_hom f.comm₁₂ x).symm

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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality of universal coefficients under actual short-complex maps. -/
lemma linearDualHomologyEquiv_naturality (f : S ⟶ T)
    (a : T.linearDual.homology) (z : S.homology) :
    S.linearDualHomologyEquiv (homologyMap (linearDualMap f) a) z =
      T.linearDualHomologyEquiv a (homologyMap f z) := by
  obtain ⟨φ, rfl⟩ := (ModuleCat.epi_iff_surjective T.linearDual.homologyπ).mp inferInstance a
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance z
  have hφ := ConcreteCategory.congr_hom (homologyπ_naturality (linearDualMap f)) φ
  have hc := ConcreteCategory.congr_hom (homologyπ_naturality f) c
  change homologyMap (linearDualMap f) (T.linearDual.homologyπ φ) =
    S.linearDual.homologyπ (cyclesMap (linearDualMap f) φ) at hφ
  change homologyMap f (S.homologyπ c) = T.homologyπ (cyclesMap f c) at hc
  rw [hφ, hc, linearDualHomologyEquiv_homologyπ_apply,
    linearDualHomologyEquiv_homologyπ_apply]
  have hφ' := ConcreteCategory.congr_hom (cyclesMap_i (linearDualMap f)) φ
  have hc' := ConcreteCategory.congr_hom (cyclesMap_i f) c
  change S.linearDual.iCycles (cyclesMap (linearDualMap f) φ) =
    (linearDualMap f).τ₂ (T.linearDual.iCycles φ) at hφ'
  change T.iCycles (cyclesMap f c) = f.τ₂ (S.iCycles c) at hc'
  rw [hφ', hc']
  rfl

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {R : Type u} [Field R]
  {K L : ChainComplex (ModuleCat.{u} R) ℕ}

/-- The actual cochain-complex universal-coefficient identification. -/
def linearDualHomologyEquiv (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    K.linearDualCochainComplex.homology n ≃ₗ[R] Module.Dual R (K.homology n) :=
  (ShortComplex.homologyMapIso (linearDualCochainComplexScIso K n)).toLinearEquiv.trans
    (K.sc n).linearDualHomologyEquiv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The degreewise short-complex dual identification preserves actual maps. -/
lemma linearDualCochainComplexScIso_naturality (f : K ⟶ L) (n : ℕ) :
    (shortComplexFunctor (ModuleCat R) (.up ℕ) n).map (linearDualMap f) ≫
      (linearDualCochainComplexScIso K n).hom =
    (linearDualCochainComplexScIso L n).hom ≫
      ShortComplex.linearDualMap ((shortComplexFunctor (ModuleCat R) (.down ℕ) n).map f) := by
  ext <;> cases n <;>
    simp [linearDualCochainComplexScIso, isoSc', linearDualMap,
      ShortComplex.linearDualMap]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The universal-coefficient identification intertwines the actual dual
cochain map with the dual of the actual homology map. -/
lemma linearDualHomologyEquiv_naturality (f : K ⟶ L) (n : ℕ)
    (a : L.linearDualCochainComplex.homology n) (z : K.homology n) :
    linearDualHomologyEquiv K n (homologyMap (linearDualMap f) n a) z =
      linearDualHomologyEquiv L n a (homologyMap f n z) := by
  have h := congrArg (ShortComplex.homologyFunctor (ModuleCat R)).map
    (linearDualCochainComplexScIso_naturality f n)
  rw [Functor.map_comp, Functor.map_comp] at h
  have ha := ConcreteCategory.congr_hom h a
  change (K.sc n).linearDualHomologyEquiv
    (ShortComplex.homologyMap (linearDualCochainComplexScIso K n).hom
      (homologyMap (linearDualMap f) n a)) z = _
  rw [show ShortComplex.homologyMap (linearDualCochainComplexScIso K n).hom
      (homologyMap (linearDualMap f) n a) =
    ShortComplex.homologyMap
      (ShortComplex.linearDualMap ((shortComplexFunctor (ModuleCat R) (.down ℕ) n).map f))
      (ShortComplex.homologyMap (linearDualCochainComplexScIso L n).hom a) from ha]
  exact ShortComplex.linearDualHomologyEquiv_naturality _ _ _

end HomologicalComplex
