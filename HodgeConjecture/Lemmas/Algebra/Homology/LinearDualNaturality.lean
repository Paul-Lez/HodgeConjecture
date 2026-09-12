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

public import HodgeConjecture.Definitions.Algebra.Homology.LinearDual

/-!
# Naturality of linear duality on homology

Concrete cycle representatives and the canonical universal-coefficient equivalence are
compatible with actual morphisms of short complexes. These identities are used to descend
geometric cap-product identities in the cohomology variable.

The same holds one level up: the universal-coefficient equivalence
`HomologicalComplex.linearDualHomologyEquiv` between the cohomology of the linear-dual cochain
complex and the dual of homology intertwines the dualised cochain map with the dual of the
homology map.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Field R]

/-- The canonical class of an explicit cycle in a short complex of vector spaces. -/
def moduleCatHomologyClass (S : ShortComplex (ModuleCat.{u} R)) :
    LinearMap.ker S.g.hom →ₗ[R] S.homology :=
  S.moduleCatHomologyIso.inv.hom.comp (LinearMap.range S.moduleCatToCycles).mkQ

/-- Every homology class has an explicit cycle representative. -/
lemma moduleCatHomologyClass_surjective (S : ShortComplex (ModuleCat.{u} R)) :
    Function.Surjective S.moduleCatHomologyClass :=
  S.moduleCatHomologyIso.toLinearEquiv.symm.surjective.comp
    (Submodule.mkQ_surjective _)

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of short complexes sends cycles to cycles. -/
def moduleCatCycleMap {S T : ShortComplex (ModuleCat.{u} R)} (f : S ⟶ T) :
    LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
  f.τ₂.hom.restrict (fun x hx ↦ by
    change T.g.hom (f.τ₂.hom x) = 0
    have h := ConcreteCategory.congr_hom f.comm₂₃ x
    change T.g.hom (f.τ₂.hom x) = f.τ₃.hom (S.g.hom x) at h
    rwa [show S.g.hom x = 0 from hx, map_zero] at h)

set_option backward.isDefEq.respectTransparency false in
lemma moduleCatCyclesIso_inv_cycleMap {S T : ShortComplex (ModuleCat.{u} R)}
    (f : S ⟶ T) :
    S.moduleCatCyclesIso.inv ≫ cyclesMap f =
      ModuleCat.ofHom (moduleCatCycleMap f) ≫ T.moduleCatCyclesIso.inv := by
  rw [← cancel_mono T.iCycles]
  simp only [Category.assoc, cyclesMap_i, moduleCatCyclesIso_inv_iCycles_assoc,
    moduleCatCyclesIso_inv_iCycles]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Taking the class of a cycle commutes with the induced homology map. -/
lemma moduleCatHomologyClass_naturality {S T : ShortComplex (ModuleCat.{u} R)}
    (f : S ⟶ T) (x : LinearMap.ker S.g.hom) :
    (homologyMap f).hom (S.moduleCatHomologyClass x) =
      T.moduleCatHomologyClass (moduleCatCycleMap f x) := by
  have h :
      S.moduleCatCyclesIso.inv ≫ S.homologyπ ≫ homologyMap f =
        ModuleCat.ofHom (moduleCatCycleMap f) ≫ T.moduleCatCyclesIso.inv ≫ T.homologyπ := by
    rw [homologyπ_naturality, ← Category.assoc, moduleCatCyclesIso_inv_cycleMap,
      Category.assoc]
  rw [← Category.assoc, moduleCatCyclesIso_inv_π,
    moduleCatCyclesIso_inv_π] at h
  exact ConcreteCategory.congr_hom h x

set_option backward.isDefEq.respectTransparency false in
/-- Reversed linear-dual short complexes are contravariantly functorial. -/
def linearDualMap {S T : ShortComplex (ModuleCat.{u} R)} (f : S ⟶ T) :
    T.linearDual ⟶ S.linearDual where
  τ₁ := ModuleCat.ofHom f.τ₃.hom.dualMap
  τ₂ := ModuleCat.ofHom f.τ₂.hom.dualMap
  τ₃ := ModuleCat.ofHom f.τ₁.hom.dualMap
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change Module.Dual R T.X₃ at phi
    apply LinearMap.ext
    intro x
    exact congrArg phi (ConcreteCategory.congr_hom f.comm₂₃ x).symm
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro phi
    change Module.Dual R T.X₂ at phi
    apply LinearMap.ext
    intro x
    exact congrArg phi (ConcreteCategory.congr_hom f.comm₁₂ x).symm

set_option backward.isDefEq.respectTransparency false in
/-- Universal coefficients evaluate a dual cycle on an ordinary cycle without any
choice of generators or representatives in the resulting pairing. -/
lemma linearDualHomologyEquiv_class_apply_class (S : ShortComplex (ModuleCat.{u} R))
    (phi : LinearMap.ker S.f.hom.dualMap) (x : LinearMap.ker S.g.hom) :
    S.linearDualHomologyEquiv (S.linearDual.moduleCatHomologyClass phi)
        (S.moduleCatHomologyClass x) = (phi.1 : Module.Dual R S.X₂) x.1 := by
  change S.dualHomologyComparisonExplicit
      (S.linearDual.moduleCatHomologyIso.hom.hom
        (S.linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi)))
      (S.moduleCatHomologyIso.hom.hom
        (S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk x))) =
      (phi.1 : Module.Dual R S.X₂) x.1
  have hphi := ConcreteCategory.congr_hom
    S.linearDual.moduleCatHomologyIso.inv_hom_id (Submodule.Quotient.mk phi)
  have hx := ConcreteCategory.congr_hom
    S.moduleCatHomologyIso.inv_hom_id (Submodule.Quotient.mk x)
  change S.linearDual.moduleCatHomologyIso.hom.hom
    (S.linearDual.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk phi)) =
      Submodule.Quotient.mk phi at hphi
  change S.moduleCatHomologyIso.hom.hom
    (S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk x at hx
  rw [hphi, hx]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The constructed universal-coefficient equivalence is natural, not merely an
abstract isomorphism between vector spaces of the same dimension. -/
theorem linearDualHomologyEquiv_naturality
    {S T : ShortComplex (ModuleCat.{u} R)} (f : S ⟶ T)
    (alpha : T.linearDual.homology) :
    S.linearDualHomologyEquiv ((homologyMap (linearDualMap f)).hom alpha) =
      (homologyMap f).hom.dualMap (T.linearDualHomologyEquiv alpha) := by
  obtain ⟨phi, rfl⟩ := T.linearDual.moduleCatHomologyClass_surjective alpha
  apply LinearMap.ext
  intro c
  obtain ⟨x, rfl⟩ := S.moduleCatHomologyClass_surjective c
  change S.linearDualHomologyEquiv
      ((homologyMap (linearDualMap f)).hom (T.linearDual.moduleCatHomologyClass phi))
      (S.moduleCatHomologyClass x) =
    T.linearDualHomologyEquiv (T.linearDual.moduleCatHomologyClass phi)
      ((homologyMap f).hom (S.moduleCatHomologyClass x))
  rw [moduleCatHomologyClass_naturality, moduleCatHomologyClass_naturality,
    linearDualHomologyEquiv_class_apply_class, linearDualHomologyEquiv_class_apply_class]
  rfl

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
  {K L : ChainComplex (ModuleCat.{u} R) ℕ}

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
  exact congrArg (fun α => α z) (ShortComplex.linearDualHomologyEquiv_naturality _ _)

end HomologicalComplex
