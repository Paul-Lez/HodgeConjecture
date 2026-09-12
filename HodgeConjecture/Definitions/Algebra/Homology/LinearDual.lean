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

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import HodgeConjecture.Mathlib.LinearAlgebra.Quotient.Basic
public import HodgeConjecture.Mathlib.LinearAlgebra.Dual.Defs

import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The linear dual of a complex of vector spaces

This file dualises complexes of vector spaces. The reversed algebraic-dual short complex of a
short complex has homology canonically linearly equivalent to the dual of the original homology:
this is the universal-coefficient identification, and no finite-dimensionality hypothesis is
needed.

Applying the dual degreewise turns a nonnegatively graded chain complex into a cochain complex,
whose degree-`n` short complex is the reversed dual of the original one. A chain-homotopy
equivalence therefore induces, contravariantly, a linear equivalence on dual homology.

Duality is contravariantly functorial for maps, isomorphisms, chain homotopies and
chain-homotopy equivalences, so all of these transport to the dual cochain complex.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Field R]

attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData

/-- The reversed algebraic-dual short complex. -/
abbrev linearDual (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk S.g.hom.dualMap S.f.hom.dualMap (by ext; simp)

@[simps]
def dualCycleToHomologyFunctional (S : ShortComplex (ModuleCat.{u} R)) :
    LinearMap.ker S.f.hom.dualMap →ₗ[R]
      Module.Dual R S.moduleCatLeftHomologyData.H where
  toFun φ := (LinearMap.range S.moduleCatToCycles).liftQ
    (φ.1.comp (LinearMap.ker S.g.hom).subtype) (by
      rintro _ ⟨x, rfl⟩
      have := LinearMap.congr_fun (LinearMap.mem_ker.1 φ.2) x
      simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at this
      simpa [moduleCatToCycles, S.f.hom.codRestrict_apply S.g.hom.ker (h := moduleCat_zero_apply S)])
  map_add' φ ψ := by
    generalize_proofs
    simp [LinearMap.add_comp, Submodule.liftQ_add S.moduleCatToCycles.range, *]
  map_smul' a φ := by
    generalize_proofs
    simp [LinearMap.smul_comp, Submodule.liftQ_smul S.moduleCatToCycles.range, *]

lemma dualCycleToHomologyFunctional_vanishes_on_boundaries
    (S : ShortComplex (ModuleCat.{u} R)) :
    LinearMap.range (S.linearDual.moduleCatToCycles) ≤
      LinearMap.ker S.dualCycleToHomologyFunctional := by
  rintro _ ⟨(ψ : Module.Dual R S.X₃), rfl⟩
  simp [dualCycleToHomologyFunctional]
  ext z
  induction z using Submodule.Quotient.induction_on with
  | H z => simp [moduleCatToCycles, S.g.hom.dualMap_apply]

/-- The canonical pairing from the explicit homology of the dual complex to the dual of the
explicit homology of the original complex. -/
def dualHomologyComparisonExplicit (S : ShortComplex (ModuleCat.{u} R)) :
    S.linearDual.moduleCatLeftHomologyData.H →ₗ[R]
      Module.Dual R S.moduleCatLeftHomologyData.H :=
  (LinearMap.range S.linearDual.moduleCatToCycles).liftQ
    S.dualCycleToHomologyFunctional
    S.dualCycleToHomologyFunctional_vanishes_on_boundaries

@[simp]
lemma dualHomologyComparisonExplicit_mk_apply_mk
    (S : ShortComplex (ModuleCat.{u} R))
    (φ : LinearMap.ker S.f.hom.dualMap) (z : LinearMap.ker S.g.hom) :
    S.dualHomologyComparisonExplicit (Submodule.Quotient.mk φ)
        (Submodule.Quotient.mk z) = φ.1 z.1 :=
  rfl

lemma dualHomologyComparisonExplicit_surjective
    (S : ShortComplex (ModuleCat.{u} R)) :
    Function.Surjective S.dualHomologyComparisonExplicit := by
  intro α
  let φ : Module.Dual R S.X₂ :=
    Subspace.dualLift (LinearMap.ker S.g.hom) <| α.comp (LinearMap.range S.moduleCatToCycles).mkQ
  have hφ : φ ∈ LinearMap.ker S.f.hom.dualMap := LinearMap.mem_ker.2 <| LinearMap.ext fun x ↦ by
    simpa [φ, Subspace.dualLift_of_mem (LinearMap.mem_ker.2 <| S.moduleCat_zero_apply x)] using!
      congr(α $((Submodule.Quotient.mk_eq_zero _).2 <| S.moduleCatToCycles.mem_range_self x))
  refine ⟨Submodule.Quotient.mk ⟨φ, hφ⟩, ?_⟩
  ext z
  induction z using Submodule.Quotient.induction_on with
  | _ z => simp +zetaDelta [Submodule.mkQ_apply _]

lemma dualHomologyComparisonExplicit_injective
    (S : ShortComplex (ModuleCat.{u} R)) :
    Function.Injective S.dualHomologyComparisonExplicit := by
  intro a b hab
  induction a using Submodule.Quotient.induction_on with
  | _ φ =>
    induction b using Submodule.Quotient.induction_on with
    | _ ψ =>
      rw [Submodule.Quotient.eq]
      have hzero : S.dualCycleToHomologyFunctional (φ - ψ) = 0 :=
        (S.dualCycleToHomologyFunctional.map_sub φ ψ).trans (sub_eq_zero.2 hab)
      have hv : (φ - ψ).1 ∈ (LinearMap.ker S.g.hom).dualAnnihilator := by
        rw [Submodule.mem_dualAnnihilator]
        intro z hz
        exact LinearMap.congr_fun hzero (Submodule.Quotient.mk ⟨z, hz⟩)
      rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hv
      obtain ⟨η, hη⟩ := hv
      exact ⟨η, Subtype.ext hη⟩

/-- Universal coefficients for a short complex of vector spaces: the homology of its reversed
dual is canonically linearly equivalent to the dual of its homology. -/
def linearDualHomologyEquiv (S : ShortComplex (ModuleCat.{u} R)) :
    S.linearDual.homology ≃ₗ[R] Module.Dual R S.homology :=
  S.linearDual.moduleCatHomologyIso.toLinearEquiv.trans <|
    (LinearEquiv.ofBijective S.dualHomologyComparisonExplicit
      ⟨S.dualHomologyComparisonExplicit_injective,
        S.dualHomologyComparisonExplicit_surjective⟩).trans <|
      S.moduleCatHomologyIso.toLinearEquiv.dualMap

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {R : Type u} [Field R]

/-- The algebraic-dual cochain complex of a nonnegatively graded chain complex of vector
spaces. -/
@[implicit_reducible, simps -isSimp X d]
def linearDualCochainComplex (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ where
  X n := ModuleCat.of R (Module.Dual R (K.X n))
  d i j := ModuleCat.ofHom (K.d j i).hom.dualMap
  shape i j := by simp +contextual
  d_comp_d' i j k h1 h2 := by
    simp [← ModuleCat.ofHom_comp, LinearMap.dualMap_comp_dualMap, ← ModuleCat.hom_comp]

attribute [simp] HomologicalComplex.linearDualCochainComplex_X

@[simp]
lemma linearDualCochainComplex_d_succ (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (K.linearDualCochainComplex).d n (n + 1) =
      ModuleCat.ofHom (K.d (n + 1) n).hom.dualMap := rfl

/-- The degree-`n` short complex of a linear-dual cochain complex is the reversed dual of the
degree-`n` short complex of the original chain complex. -/
@[implicit_reducible]
def linearDualCochainComplexScIso (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    K.linearDualCochainComplex.sc n ≅ (K.sc n).linearDual :=
  have hprev : (ComplexShape.up ℕ).prev n = (ComplexShape.down ℕ).next n := by cases n <;> simp
  have hnext : (ComplexShape.up ℕ).next n = (ComplexShape.down ℕ).prev n := by simp
  K.linearDualCochainComplex.isoSc' (c := ComplexShape.up ℕ) _ _ _ hprev hnext

variable {K L M : ChainComplex (ModuleCat.{u} R) ℕ}

/-- Algebraic duality sends a map of nonnegative chain complexes contravariantly to a map of
cochain complexes. -/
@[implicit_reducible, simps f]
def linearDualMap (f : K ⟶ L) :
    L.linearDualCochainComplex ⟶ K.linearDualCochainComplex where
  f n := ModuleCat.ofHom (f.f n).hom.dualMap
  comm' _ _ _ := by
    rw [linearDualCochainComplex_d, linearDualCochainComplex_d, ← ModuleCat.ofHom_comp,
      LinearMap.dualMap_comp_dualMap, ← ModuleCat.hom_comp, ← ModuleCat.ofHom_comp,
      LinearMap.dualMap_comp_dualMap, ← ModuleCat.hom_comp, f.comm]

@[simp]
lemma linearDualMap_id (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    linearDualMap (𝟙 K) = 𝟙 K.linearDualCochainComplex :=
  rfl

@[simp]
lemma linearDualMap_comp (f : K ⟶ L) (g : L ⟶ M) :
    linearDualMap (f ≫ g) = linearDualMap g ≫ linearDualMap f :=
  rfl

/-- Algebraic duality sends an isomorphism of chain complexes to an isomorphism of cochain
complexes, reversing its direction. -/
@[implicit_reducible]
def linearDualIso (e : K ≅ L) :
    L.linearDualCochainComplex ≅ K.linearDualCochainComplex where
  hom := linearDualMap e.hom
  inv := linearDualMap e.inv
  hom_inv_id := by rw [← linearDualMap_comp, e.inv_hom_id, linearDualMap_id]
  inv_hom_id := by rw [← linearDualMap_comp, e.hom_inv_id, linearDualMap_id]

lemma ModuleCat.ofHom_sub.{v} {R : Type*} [Ring R] {M N : Type v} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (f g : M →ₗ[R] N) :
    ModuleCat.ofHom (f - g) = ModuleCat.ofHom f - ModuleCat.ofHom g := rfl

open Homotopy in
/-- Algebraic duality sends a chain homotopy contravariantly to a cochain homotopy. -/
def linearDualHomotopy {f g : K ⟶ L} (h : Homotopy f g) :
    Homotopy (linearDualMap f) (linearDualMap g) where
  hom i j := ModuleCat.ofHom (h.hom j i).hom.dualMap
  zero i j hij := by simp [h.zero j i hij]
  comm i := by
    cases i with
    | zero =>
      rw [dNext_cochainComplex, prevD_zero_cochainComplex, linearDualCochainComplex_d_succ]
      have h' : f.f 0 - g.f 0 = h.hom 0 1 ≫ L.d 1 0 := by
        simpa [dNext_zero_chainComplex _, prevD_chainComplex _, ← sub_eq_iff_eq_add] using h.comm 0
      simp [← ModuleCat.ofHom_comp, LinearMap.dualMap_comp_dualMap, ← ModuleCat.hom_comp, ← h',
        LinearMap.dualMap_sub, ModuleCat.ofHom_sub]
    | succ n =>
        rw [Homotopy.dNext_cochainComplex, Homotopy.prevD_succ_cochainComplex]
        have h': f.f (n + 1) - g.f (n + 1) = h.hom (n + 1) (n + 1 + 1) ≫
            L.d (n + 1 + 1) (n + 1) + K.d (n + 1) n ≫ h.hom n (n + 1) := by
          simpa [dNext_succ_chainComplex _, prevD_chainComplex _, ← sub_eq_iff_eq_add,
            add_comm (K.d _ _ ≫ _)] using h.comm (n + 1)
        simp [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_add, LinearMap.dualMap_comp_dualMap,
          ← ModuleCat.hom_comp, ← LinearMap.dualMap_add, ← ModuleCat.hom_add, ← h']

/-- Algebraic duality sends a chain-homotopy equivalence contravariantly to a cochain-homotopy
equivalence. -/
def linearDualHomotopyEquiv (e : HomotopyEquiv K L) :
    HomotopyEquiv L.linearDualCochainComplex K.linearDualCochainComplex where
  hom := linearDualMap e.hom
  inv := linearDualMap e.inv
  homotopyHomInvId :=
    (Homotopy.ofEq (linearDualMap_comp e.inv e.hom).symm).trans <|
      (linearDualHomotopy e.homotopyInvHomId).trans <|
        Homotopy.ofEq (linearDualMap_id L)
  homotopyInvHomId :=
    (Homotopy.ofEq (linearDualMap_comp e.hom e.inv).symm).trans <|
      (linearDualHomotopy e.homotopyHomInvId).trans <|
        Homotopy.ofEq (linearDualMap_id K)

end HomologicalComplex

namespace HomologicalComplex.HomotopyEquiv

variable {R : Type u} [Field R]
variable {K L : ChainComplex (ModuleCat.{u} R) ℕ}

/-- A chain-homotopy equivalence induces, contravariantly, a linear equivalence on the
cohomology of the algebraic-dual short complexes. -/
def linearDualCohomologyEquiv (h : HomotopyEquiv K L) (n : ℕ) :
    (L.sc n).linearDual.homology ≃ₗ[R] (K.sc n).linearDual.homology :=
  (L.sc n).linearDualHomologyEquiv |>.trans <|
    h.toHomologyIso n |>.toLinearEquiv.dualMap |>.trans <|
      (K.sc n).linearDualHomologyEquiv.symm

end HomologicalComplex.HomotopyEquiv
