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

public import HodgeConjecture.Definitions.AlgebraicGeometry.AlgebraicCycleSupport
public import HodgeConjecture.Definitions.AlgebraicGeometry.CycleClassImage
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Chow-group compatibility for intrinsic cycle classes

This module extends maps on cycles to Chow groups when rational equivalences map to zero. It
constructs the codimension-zero cycle-class map and proves that its image is the unit line used
by the intrinsic definition in `CycleClassImage`.

A positive-codimension Chow-group map additionally requires Gysin compatibility and vanishing
on rational equivalences. The conjecture statement only imports `CycleClassImage` and does not
choose such a map.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- On a compact scheme, regard a locally finite integral algebraic cycle as a finitely supported
function. -/
def compactCycleToFinsupp {X : Scheme.{u}} [CompactSpace X] :
    AlgebraicCycle X ℤ →+ X →₀ ℤ where
  toFun c := Finsupp.ofSupportFinite c
    (by
      have h := c.locallyFiniteSupport.finite_inter_support_of_isCompact
        (W := Set.univ) isCompact_univ
      simpa using h)
  map_zero' := by
    ext
    rfl
  map_add' _ _ := by
    ext
    rfl

@[simp] lemma compactCycleToFinsupp_apply {X : Scheme.{u}} [CompactSpace X]
    (c : AlgebraicCycle X ℤ) (x : X) : compactCycleToFinsupp c x = c x :=
  rfl

/-- Extend prescribed classes of irreducible codimension-`p` components additively to integral
codimension-`p` cycles. Values away from codimension `p` are set to zero; the support condition on
a `CodimensionCycle` ensures that this branch is never used by a nonzero coefficient. -/
def cycleClassOnCyclesOfComponents {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (componentClass : ∀ (x : X), coheight x = p → M) :
    CodimensionCycle X p →+ M := by
  classical
  let componentValue : X → M := fun x ↦
    if hx : coheight x = p then componentClass x hx else 0
  exact (Finsupp.linearCombination ℤ componentValue).toAddMonoidHom.comp
    ((compactCycleToFinsupp (X := X)).comp (codimensionCycleInclusion X p))

/-- The additive extension sends a one-component cycle to its coefficient times the prescribed
component class. -/
@[simp] lemma cycleClassOnCyclesOfComponents_single
    {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (componentClass : ∀ (x : X), coheight x = p → M)
    (x : X) (hx : coheight x = p) (n : ℤ) :
    cycleClassOnCyclesOfComponents componentClass
        (CodimensionCycle.single x hx n) =
      n • componentClass x hx := by
  classical
  change (Finsupp.linearCombination ℤ (fun y ↦
      if hy : coheight y = p then componentClass y hy else 0))
    (compactCycleToFinsupp ((codimensionCycleInclusion X p)
      (CodimensionCycle.single x hx n))) = n • componentClass x hx
  have hsingle : compactCycleToFinsupp
      ((codimensionCycleInclusion X p) (CodimensionCycle.single x hx n)) =
      Finsupp.single x n := by
    ext y
    change CodimensionCycle.single x hx n y = Finsupp.single x n y
    rw [CodimensionCycle.single_apply, Finsupp.single_apply]
    by_cases h : y = x
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hsingle, Finsupp.linearCombination_single]
  simp only [dif_pos hx]

namespace ChowGroup

/-- An additive map on codimension cycles that vanishes on rational equivalences descends to the
Chow group. -/
def liftCycleClass {X : Scheme.{u}} {p : ℕ} {M : Type*} [AddCommGroup M]
    (f : CodimensionCycle X p →+ M)
    (h : rationalEquivalenceSubgroup X p ≤ f.ker) : ChowGroup X p →+ M :=
  QuotientAddGroup.lift (rationalEquivalenceSubgroup X p) f h

/-- Evaluation of a descended additive map on a represented Chow class. -/
@[simp] lemma liftCycleClass_mk {X : Scheme.{u}} {p : ℕ} {M : Type*} [AddCommGroup M]
    (f : CodimensionCycle X p →+ M)
    (h : rationalEquivalenceSubgroup X p ≤ f.ker) (z : CodimensionCycle X p) :
    liftCycleClass f h (mk z) = f z :=
  QuotientAddGroup.lift_mk' _ h z

/-- The bilinear map used to extend an integral Chow-group map over rational coefficients. -/
def rationalExtensionBilinear {X : Scheme.{u}} {p : ℕ} {M : Type*}
    [AddCommGroup M] [Module ℚ M] (f : ChowGroup X p →+ M) :
    ℚ →ₗ[ℚ] ChowGroup X p →ₗ[ℤ] M where
  toFun q := q • f.toIntLinearMap
  map_add' _ _ := by
    ext
    simp [add_smul]
  map_smul' _ _ := by
    ext
    simp [mul_smul]

/-- Extend an additive map on the integral Chow group over rational coefficients. -/
def rationalExtension {X : Scheme.{u}} {p : ℕ} {M : Type*}
    [AddCommGroup M] [Module ℚ M] (f : ChowGroup X p →+ M) :
    RationalChowGroup X p →ₗ[ℚ] M :=
  TensorProduct.AlgebraTensorModule.lift (rationalExtensionBilinear f)

@[simp] lemma rationalExtension_tmul {X : Scheme.{u}} {p : ℕ} {M : Type*}
    [AddCommGroup M] [Module ℚ M] (f : ChowGroup X p →+ M)
    (q : ℚ) (z : ChowGroup X p) :
    rationalExtension f (q ⊗ₜ[ℤ] z) = q • f z :=
  rfl

end ChowGroup

end AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ))

/-- The rational Chow class represented by an irreducible codimension-`p` component with
coefficient one. -/
def rationalComponentChowClass
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (p : ℕ)
    (x : X) (hx : coheight x = p) : RationalChowGroup X p :=
  ChowGroup.toRational (ChowGroup.mk (CodimensionCycle.single x hx 1))

/-! ### The genuine codimension-zero cycle class -/

/-- A codimension-zero cycle maps to the constant cohomology class given by the coefficient of
the generic component. -/
def codimensionZeroCycleClassOnCycles
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] :
    CodimensionCycle X 0 →+ RationalCohomology structureMap 0 :=
  (rationalCohomologyClassAddHom structureMap).comp
    ((Int.castAddHom ℚ).comp CodimensionCycle.integralEquiv.toAddMonoidHom)

/-- Codimension-zero rational equivalences map to zero. Here this is a theorem rather than part
of the data of the cycle-class map: the rational-equivalence subgroup is trivial in codimension
zero. -/
lemma rationalEquivalenceSubgroup_le_codimensionZeroCycleClassOnCycles_ker
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] :
    rationalEquivalenceSubgroup X 0 ≤
      (codimensionZeroCycleClassOnCycles structureMap).ker := by
  rw [rationalEquivalenceSubgroup_zero]
  exact bot_le

/-- The genuine integral codimension-zero cycle-class map on the Chow group. -/
def codimensionZeroChowCycleClass
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] :
    ChowGroup X 0 →+ RationalCohomology structureMap 0 :=
  ChowGroup.liftCycleClass (codimensionZeroCycleClassOnCycles structureMap)
    (rationalEquivalenceSubgroup_le_codimensionZeroCycleClassOnCycles_ker structureMap)

/-- Evaluation of the integral codimension-zero class map on a represented cycle. -/
@[simp] lemma codimensionZeroChowCycleClass_mk
    [IsIntegral X] [Smooth structureMap]
    [ProjectiveSpace.IsProjective structureMap] (z : CodimensionCycle X 0) :
    codimensionZeroChowCycleClass structureMap (ChowGroup.mk z) =
      codimensionZeroCycleClassOnCycles structureMap z := by
  exact ChowGroup.liftCycleClass_mk _ _ _

/-- The rational codimension-zero Chow group of an integral variety maps to degree-zero
cohomology by rational extension of the integral class map. -/
def codimensionZeroCycleClass
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] :
    RationalChowGroup X 0 →ₗ[ℚ] RationalCohomology structureMap 0 :=
  ChowGroup.rationalExtension (codimensionZeroChowCycleClass structureMap)

/-- The generic component with coefficient one maps to the unit in degree-zero cohomology. -/
@[simp] lemma codimensionZeroCycleClass_genericPoint
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] :
    codimensionZeroCycleClass structureMap
        (ChowGroup.toRational
          (ChowGroup.mk (CodimensionCycle.single (genericPoint X)
            (Order.IsMax.coheight_eq_zero isMax_top) 1))) =
      rationalCohomologyUnit structureMap := by
  unfold codimensionZeroCycleClass
  rw [ChowGroup.toRational_apply, ChowGroup.rationalExtension_tmul, one_smul,
    codimensionZeroChowCycleClass_mk]
  let z : CodimensionCycle X 0 :=
    CodimensionCycle.single (genericPoint X)
      (Order.IsMax.coheight_eq_zero isMax_top) 1
  have hz : CodimensionCycle.integralEquiv z = 1 := by
    change z (genericPoint X) = 1
    dsimp [z]
    exact CodimensionCycle.single_same (p := 0) (genericPoint X) _ 1
  change rationalCohomologyClass structureMap
      ((CodimensionCycle.integralEquiv z : ℤ) : ℚ) =
    rationalCohomologyClass structureMap 1
  rw [hz]
  norm_num

/-- The actual codimension-zero algebraic cycle-class span. -/
def codimensionZeroCycleClassSpan
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] :
    Submodule ℚ (RationalCohomology structureMap 0) :=
  LinearMap.range (codimensionZeroCycleClass structureMap)

/-- In codimension zero the actual cycle-class span is the line generated by the cohomological
unit. This statement does not assert that the unit spans all of `H⁰`; that further conclusion
requires connectedness of the analytic space. -/
lemma codimensionZeroCycleClassSpan_eq_span_unit
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] :
    codimensionZeroCycleClassSpan structureMap =
      Submodule.span ℚ {rationalCohomologyUnit structureMap} := by
  apply le_antisymm
  · rintro α ⟨z, rfl⟩
    rw [ChowGroup.rational_eq_smul_genericPoint X z, map_smul,
      codimensionZeroCycleClass_genericPoint]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro α hα
    rw [Set.mem_singleton_iff.mp hα]
    exact ⟨ChowGroup.toRational
      (ChowGroup.mk (CodimensionCycle.single (genericPoint X)
        (Order.IsMax.coheight_eq_zero isMax_top) 1)),
      codimensionZeroCycleClass_genericPoint structureMap⟩

/-- The intrinsic codimension-zero span is the image of the Chow-group cycle-class map. -/
lemma algebraicCycleClassSpan_zero
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] :
    algebraicCycleClassSpan structureMap 0 = codimensionZeroCycleClassSpan structureMap := by
  rw [algebraicCycleClassSpan_zero_eq_span_unit, codimensionZeroCycleClassSpan_eq_span_unit]

/-- The intrinsic definition agrees with the formulation using a Chow-group image in
codimension zero and component-image generators in positive codimension. -/
lemma algebraicCycleClassSpan_eq_chow_zero_or_component_span
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (p : ℕ) :
    algebraicCycleClassSpan structureMap p =
      if hp : p = 0 then hp ▸ codimensionZeroCycleClassSpan structureMap
      else ⨆ (x : X) (_ : coheight x = p), rationalComponentCycleClassLine structureMap p x := by
  by_cases hp : p = 0
  · subst p
    rw [dif_pos rfl]
    exact algebraicCycleClassSpan_zero structureMap
  · simpa only [dif_neg hp] using algebraicCycleClassSpan_of_ne_zero structureMap p hp

/-- If the codimension-zero unit spans degree-zero cohomology and positive-codimension purity has
been proved for every relevant component, the algebraic cycle-class span agrees with the
coniveau subspace. The separate degree-zero hypothesis records the connectedness calculation
needed to identify `H⁰` with the line generated by the unit. -/
lemma algebraicCycleClassSpan_eq_rationalConiveauSubspace_of_purity
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (p : ℕ)
    (hzero : p = 0 → codimensionZeroCycleClassSpan structureMap = ⊤)
    (h : ∀ (x : X), coheight x = p →
      RationalComponentCycleClassPurity structureMap p x) :
    algebraicCycleClassSpan structureMap p = rationalConiveauSubspace structureMap p := by
  by_cases hp : p = 0
  · subst p
    rw [algebraicCycleClassSpan_zero, hzero rfl,
      rationalConiveauSubspace_zero_eq_top]
  · rw [algebraicCycleClassSpan_of_ne_zero structureMap p hp]
    apply le_antisymm
    · refine iSup_le fun x ↦ iSup_le fun hx ↦ ?_
      apply (rationalComponentCycleClassLine_le_supportedOn structureMap p x).trans
      apply le_iSup_of_le x
      apply le_iSup_of_le hx
      rfl
    · refine iSup_le fun x ↦ iSup_le fun hx ↦ ?_
      rw [← rationalComponentCycleClassLine_eq_supportedOn_of_purity
        structureMap p x (h x hx)]
      apply le_iSup_of_le x
      apply le_iSup_of_le hx
      rfl

end AlgebraicGeometry.ComplexPoint
