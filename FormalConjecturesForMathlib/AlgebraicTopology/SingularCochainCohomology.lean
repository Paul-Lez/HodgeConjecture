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

public import FormalConjecturesForMathlib.Algebra.Homology.DualExact
public import FormalConjecturesForMathlib.AlgebraicTopology.SingularCohomology

/-!
# Cohomology of singular cochains

This file proves the universal-coefficient identification for a short complex of vector spaces.
The homology of the reversed algebraic-dual complex is linearly equivalent to the algebraic dual
of the original homology. No finite-dimensionality hypothesis is needed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Field R]

/-- The reversed algebraic-dual short complex. -/
def linearDual (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk S.g.hom.dualMap S.f.hom.dualMap (by
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    change φ (S.g.hom (S.f.hom x)) = 0
    rw [S.moduleCat_zero_apply, map_zero])

/-- A dual cycle evaluates on a cycle of the original short complex and descends to its
homology. -/
def dualCycleToHomologyFunctional (S : ShortComplex (ModuleCat.{u} R)) :
    LinearMap.ker S.f.hom.dualMap →ₗ[R]
      Module.Dual R S.moduleCatLeftHomologyData.H where
  toFun φ := (LinearMap.range S.moduleCatToCycles).liftQ
    (φ.1.comp (LinearMap.ker S.g.hom).subtype) (by
      rintro _ ⟨x, rfl⟩
      exact LinearMap.congr_fun φ.2 x)
  map_add' φ ψ := by
    ext z
    induction z using Submodule.Quotient.induction_on with
    | _ z => rfl
  map_smul' a φ := by
    ext z
    induction z using Submodule.Quotient.induction_on with
    | _ z => rfl

lemma dualCycleToHomologyFunctional_vanishes_on_boundaries
    (S : ShortComplex (ModuleCat.{u} R)) :
    LinearMap.range (S.linearDual.moduleCatToCycles) ≤
      LinearMap.ker S.dualCycleToHomologyFunctional := by
  rintro _ ⟨ψ, rfl⟩
  change Module.Dual R S.X₃ at ψ
  ext z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
      change (ψ : Module.Dual R S.X₃) (S.g.hom z.1) = 0
      rw [z.2, map_zero]

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
  change Module.Dual R
    (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) at α
  let αcycles : Module.Dual R (LinearMap.ker S.g.hom) :=
    α.comp (LinearMap.range S.moduleCatToCycles).mkQ
  let φ : Module.Dual R S.X₂ :=
    Subspace.dualLift (LinearMap.ker S.g.hom) αcycles
  have hφ : φ ∈ LinearMap.ker S.f.hom.dualMap := by
    rw [LinearMap.mem_ker]
    ext x
    change φ (S.f.hom x) = 0
    rw [Subspace.dualLift_of_mem (S.moduleCat_zero_apply x)]
    change α (Submodule.Quotient.mk
      (S.moduleCatToCycles x)) = 0
    simpa using congrArg α
      ((Submodule.Quotient.mk_eq_zero _).mpr
        (LinearMap.mem_range_self S.moduleCatToCycles x))
  refine ⟨Submodule.Quotient.mk ⟨φ, hφ⟩, ?_⟩
  ext z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
      change φ z.1 = α (Submodule.Quotient.mk z)
      rw [Subspace.dualLift_of_subtype]
      rfl

lemma dualHomologyComparisonExplicit_injective
    (S : ShortComplex (ModuleCat.{u} R)) :
    Function.Injective S.dualHomologyComparisonExplicit := by
  intro a b hab
  induction a using Submodule.Quotient.induction_on with
  | _ φ =>
    induction b using Submodule.Quotient.induction_on with
    | _ ψ =>
      change LinearMap.ker S.f.hom.dualMap at φ ψ
      apply (Submodule.Quotient.eq _).mpr
      have hzero : S.dualCycleToHomologyFunctional (φ - ψ) = 0 := by
        change S.dualCycleToHomologyFunctional φ =
          S.dualCycleToHomologyFunctional ψ at hab
        exact (S.dualCycleToHomologyFunctional.map_sub φ ψ).trans
          (sub_eq_zero.mpr hab)
      have hv : (φ - ψ).1 ∈ (LinearMap.ker S.g.hom).dualAnnihilator := by
        rw [Submodule.mem_dualAnnihilator]
        intro z hz
        have := LinearMap.congr_fun hzero
          (Submodule.Quotient.mk ⟨z, hz⟩)
        exact this
      rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hv
      obtain ⟨η, hη⟩ := hv
      refine ⟨η, Subtype.ext ?_⟩
      exact hη

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
def linearDualCochainComplex (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of R (Module.Dual R (K.X n)))
    (fun n ↦ ModuleCat.ofHom (K.d (n + 1) n).hom.dualMap)
    (fun n ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro c
      change φ ((K.d (n + 1) n).hom ((K.d (n + 2) (n + 1)).hom c)) = 0
      have h := K.d_comp_d (n + 2) (n + 1) n
      rw [show (K.d (n + 1) n).hom ((K.d (n + 2) (n + 1)).hom c) = 0 by
        exact ConcreteCategory.congr_hom h c, map_zero])

@[simp]
lemma linearDualCochainComplex_d (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (K.linearDualCochainComplex).d n (n + 1) =
      ModuleCat.ofHom (K.d (n + 1) n).hom.dualMap := by
  simp [linearDualCochainComplex]

set_option backward.isDefEq.respectTransparency false in
/-- The degree-`n` short complex of a linear-dual cochain complex is the reversed dual of the
degree-`n` short complex of the original chain complex. -/
def linearDualCochainComplexScIso (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    K.linearDualCochainComplex.sc n ≅ (K.sc n).linearDual := by
  let D := K.linearDualCochainComplex
  have hprev : (ComplexShape.up ℕ).prev n = (ComplexShape.down ℕ).next n := by
    cases n <;> simp
  have hnext : (ComplexShape.up ℕ).next n = (ComplexShape.down ℕ).prev n := by simp
  refine D.isoSc' ((ComplexShape.down ℕ).next n) n
      ((ComplexShape.down ℕ).prev n) hprev hnext ≪≫
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · cases n with
    | zero =>
        simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
          HomologicalComplex.shortComplexFunctor'_obj_f]
        dsimp only [ShortComplex.linearDual, ShortComplex.moduleCatMk, HomologicalComplex.sc,
          HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor']
        rw [ChainComplex.next_nat_zero]
        change ModuleCat.ofHom (K.d 0 0).hom.dualMap = D.d 0 0
        rw [K.shape 0 0 (by simp), D.shape 0 0 (by simp)]
        ext φ x
        exact map_zero φ
    | succ n =>
        simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
          HomologicalComplex.shortComplexFunctor'_obj_f]
        dsimp only [ShortComplex.linearDual, ShortComplex.moduleCatMk, HomologicalComplex.sc,
          HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor']
        rw [ChainComplex.next_nat_succ]
        exact (linearDualCochainComplex_d K n).symm
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
      HomologicalComplex.shortComplexFunctor'_obj_g]
    dsimp only [ShortComplex.linearDual, ShortComplex.moduleCatMk, HomologicalComplex.sc,
      HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor']
    rw [ChainComplex.prev]
    exact (linearDualCochainComplex_d K n).symm

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

namespace AlgebraicTopology.Singular

variable (R : Type u) [Field R] (X : TopCat.{u})

/-- Ordinary singular cochain cohomology in degree `n`, expressed as the homology of the
algebraic-dual short complex centered on the singular chain group in degree `n`. -/
abbrev CochainCohomology (n : ℕ) : ModuleCat.{u} R :=
  let K :=
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj X
  (K.sc n).linearDual.homology

/-- The universal-coefficient equivalence from ordinary singular cochain cohomology to the
linear dual of singular homology. -/
def cochainCohomologyEquiv (n : ℕ) :
    CochainCohomology R X n ≃ₗ[R] Cohomology R X n :=
  let K :=
    ((singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)).obj X
  (K.sc n).linearDualHomologyEquiv

end AlgebraicTopology.Singular
