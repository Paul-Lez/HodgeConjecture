/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.Cycle.ChowGroup
public import Other.AlgebraicGeometry.Cycle.ClassOnCycles

/-!
# Maps out of Chow groups

An additive map on codimension cycles descends to the Chow group once it vanishes on rational
equivalences. This file records that formal quotient step and rational scalar extension.
-/

@[expose] public noncomputable section

open Order TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- Extend codimension-`p` component classes to all algebraic cycles, using zero in every other
codimension. -/
def cycleClassOnAlgebraicCyclesOfComponents {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (componentClass : ∀ (x : X), coheight x = p → M) :
    AlgebraicCycle X ℤ →+ M :=
  let componentValue : X → M := fun x ↦
    if hx : coheight x = p then componentClass x hx else 0
  (Finsupp.linearCombination ℤ componentValue).toAddMonoidHom.comp
    (compactCycleToFinsupp (X := X))

/-- The full-cycle extension restricts to the existing map on pure codimension cycles. -/
lemma cycleClassOnAlgebraicCyclesOfComponents_comp_codimensionCycleInclusion
    {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (componentClass : ∀ (x : X), coheight x = p → M) :
    (cycleClassOnAlgebraicCyclesOfComponents componentClass).comp
        (codimensionCycleInclusion X p) =
      cycleClassOnCyclesOfComponents componentClass :=
  rfl

/-- A componentwise cycle-class map kills rational equivalences if it kills every pushed-forward
principal-divisor generator. -/
theorem rationalEquivalenceSubgroup_le_cycleClassOnCyclesOfComponents_ker
    {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (componentClass : ∀ (x : X), coheight x = p → M)
    (hprincipal : ∀ D : PrincipalDivisor X p,
      cycleClassOnAlgebraicCyclesOfComponents componentClass D.pushforwardCycle = 0) :
    rationalEquivalenceSubgroup X p ≤
      (cycleClassOnCyclesOfComponents componentClass).ker := by
  intro z hz
  change z.1 ∈ principalDivisorSubgroup X p at hz
  change cycleClassOnAlgebraicCyclesOfComponents componentClass z.1 = 0
  apply (show principalDivisorSubgroup X p ≤
    (cycleClassOnAlgebraicCyclesOfComponents componentClass).ker from ?_) hz
  rw [principalDivisorSubgroup, AddSubgroup.closure_le]
  rintro _ ⟨D, rfl⟩
  exact hprincipal D

end AlgebraicGeometry

namespace AlgebraicGeometry.ChowGroup

universe u

/-- Descend an additive map on codimension cycles through rational equivalence. -/
def lift {X : Scheme.{u}} {p : ℕ} {M : Type*} [AddCommGroup M]
    (f : codimensionCycleSubgroup X p →+ M)
    (h : rationalEquivalenceSubgroup X p ≤ f.ker) :
    ChowGroup X p →+ M :=
  QuotientAddGroup.lift (rationalEquivalenceSubgroup X p) f h

/-- Evaluation of a descended map on a represented cycle. -/
@[simp]
lemma lift_mk {X : Scheme.{u}} {p : ℕ} {M : Type*} [AddCommGroup M]
    (f : codimensionCycleSubgroup X p →+ M)
    (h : rationalEquivalenceSubgroup X p ≤ f.ker)
    (z : codimensionCycleSubgroup X p) :
    lift f h (mk z) = f z :=
  QuotientAddGroup.lift_mk' _ h z

/-- Extend an integral Chow-group map to rational coefficients. -/
def rationalExtension {X : Scheme.{u}} {p : ℕ} {M : Type*}
    [AddCommGroup M] [Module ℚ M] (f : ChowGroup X p →+ M) :
    RationalChowGroup X p →ₗ[ℚ] M :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun q ↦ q • f.toIntLinearMap
      map_add' := by
        intro q r
        ext z
        simp [add_smul]
      map_smul' := by
        intro q r
        ext z
        simp [mul_smul] }

@[simp]
lemma rationalExtension_tmul {X : Scheme.{u}} {p : ℕ} {M : Type*}
    [AddCommGroup M] [Module ℚ M] (f : ChowGroup X p →+ M)
    (q : ℚ) (z : ChowGroup X p) :
    rationalExtension f (q ⊗ₜ[ℤ] z) = q • f z :=
  rfl

end AlgebraicGeometry.ChowGroup
