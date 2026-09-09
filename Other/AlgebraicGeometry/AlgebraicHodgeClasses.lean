/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SheafCycleClass
public import Other.AlgebraicGeometry.CycleClassDimension

import HodgeConjecture.Lemmas.AlgebraicGeometry.SmoothPointwiseDimension

/-!
# Algebraic classes and the Hodge filtration

The span of the constructed component classes is exactly the image of the constructed rational
cycle-class map. To prove that this image consists of Hodge classes, it suffices to lift the
de Rham image of each component class to filtered de Rham hypercohomology. We prove this reduction
for the actual classes used in `HodgeConjecture`, including rational combinations and a map with
values in the Hodge subspace once those lifts are supplied.

The existence of these filtered lifts in positive codimension is still a geometric prerequisite,
not a theorem of this file. Topological purity alone does not supply a filtered de Rham lift.
Unconditionally, we prove the inclusion in codimension zero, above the dimension, and hence in
every codimension on a zero-dimensional variety.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.ComplexPoint

/-- The classical assertion that every rational algebraic cycle class on a smooth projective
integral complex variety is a Hodge class. This records the statement; a proof in arbitrary
codimension still requires the filtered comparison isolated below. -/
def AlgebraicClassesAreHodge : Prop :=
  ∀ {X : Scheme} [IsIntegral X] (s : X ⟶ Spec ↧ℂ) [Smooth s] [IsProjective s] (p : ℕ),
    algebraicCycleClassSpan s p ≤ Hdg^p(ℚ; s)

variable (V : DimensionedSmoothProjectiveComplexVariety)

/-- The dimension in the auxiliary wrapper agrees with the intrinsic dimension of its scheme. -/
theorem DimensionedSmoothProjectiveComplexVariety.dimension_eq_dim :
    V.dimension = dim V.scheme := by
  rw [TopologicalSpace.dim_eq_krullDim,
    SmoothOfRelativeDimension.orderKrullDim_eq_complex
      (f := V.structureMap) (d := V.dimension)]
  simp

/-- Every integral cycle class is in the span of the constructed component classes. -/
theorem sheafCycleClassOnCycles_mem_algebraicCycleClassSpan (p : ℕ)
    (c : CodimensionCycle V.scheme p) :
    sheafCycleClassOnCycles V p c ∈ algebraicCycleClassSpan V.structureMap p := by
  classical
  have hd := V.dimension_eq_dim
  rw [sheafCycleClassOnCycles_apply]
  apply Submodule.sum_mem
  intro x _
  apply Submodule.smul_of_tower_mem
  split_ifs with hx
  · simpa only [hd] using
      cycleComponentSheafClass_mem_algebraicCycleClassSpan V.structureMap p x hx
  · exact Submodule.zero_mem _

/-- Every rational cycle class is in the algebraic cycle-class span. -/
theorem rationalSheafCycleClassOnCycles_mem_algebraicCycleClassSpan (p : ℕ)
    (c : ℚ ⊗[ℤ] CodimensionCycle V.scheme p) :
    rationalSheafCycleClassOnCycles V p c ∈ algebraicCycleClassSpan V.structureMap p := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul q c =>
      rw [rationalSheafCycleClassOnCycles_tmul]
      exact Submodule.smul_mem _ q
        (sheafCycleClassOnCycles_mem_algebraicCycleClassSpan V p c)
  | add a b ha hb =>
      rw [map_add]
      exact Submodule.add_mem _ ha hb

/-- The algebraic subspace in the Hodge-conjecture statement is precisely the image of the
constructed map on rational cycles. No descent through rational equivalence is needed. -/
theorem range_rationalSheafCycleClassOnCycles (p : ℕ) :
    LinearMap.range (rationalSheafCycleClassOnCycles V p) =
      algebraicCycleClassSpan V.structureMap p := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    exact rationalSheafCycleClassOnCycles_mem_algebraicCycleClassSpan V p c
  · refine iSup₂_le fun x hx => Submodule.span_le.mpr ?_
    rintro a (rfl : a = _)
    refine ⟨1 ⊗ₜ[ℤ] CodimensionCycle.single x hx 1, ?_⟩
    have hd := V.dimension_eq_dim
    simp only [rationalSheafCycleClassOnCycles_tmul_single, one_smul, hd]

variable {X : Scheme} [IsIntegral X]
  (s : X ⟶ Spec ↧ℂ) [Smooth s] [IsProjective s] (p : ℕ)

/-- All algebraic classes are Hodge if and only if each constructed component class is Hodge.
This isolates the geometric assertion from closure under rational linear combinations. -/
theorem algebraicCycleClassSpan_le_hodgeClasses_iff :
    algebraicCycleClassSpan s p ≤ Hdg^p(ℚ; s) ↔
      ∀ (x : X) (hx : coheight x = p),
        IsHodgeClass ℚ s p (cycleComponentSheafClass s x (d := dim X) hx) := by
  constructor
  · intro h x hx
    exact h (cycleComponentSheafClass_mem_algebraicCycleClassSpan s p x hx)
  · intro h
    refine iSup₂_le fun x hx => Submodule.span_le.mpr ?_
    rintro a (rfl : a = _)
    exact h x hx

/-- The precise remaining geometric assertion: each constructed component class has a lift to
the `p`-th filtered de Rham hypercohomology group. This equivalence does not assume or assert that
such lifts have been constructed. -/
theorem algebraicCycleClassSpan_le_hodgeClasses_iff_filtered_lifts :
    algebraicCycleClassSpan s p ≤ Hdg^p(ℚ; s) ↔
      ∀ (x : X) (hx : coheight x = p),
        ∃ β : FilteredDeRhamHypercohomology s p (2 * (p : ℤ)),
          filteredToDeRhamCohomology s p (2 * (p : ℤ)) β =
            fieldToDeRhamCohomology ℚ s (2 * (p : ℤ))
              (cycleComponentSheafClass s x (d := dim X) hx) := by
  rw [algebraicCycleClassSpan_le_hodgeClasses_iff]
  rfl

/-- Filtered de Rham lifts of component classes imply the Hodge property for their entire
rational span. The lift existence assumption is explicit. -/
theorem algebraicCycleClassSpan_le_hodgeClasses_of_filtered_lifts
    (hlift : ∀ (x : X) (hx : coheight x = p),
      ∃ β : FilteredDeRhamHypercohomology s p (2 * (p : ℤ)),
        filteredToDeRhamCohomology s p (2 * (p : ℤ)) β =
          fieldToDeRhamCohomology ℚ s (2 * (p : ℤ))
            (cycleComponentSheafClass s x (d := dim X) hx)) :
    algebraicCycleClassSpan s p ≤ Hdg^p(ℚ; s) :=
  (algebraicCycleClassSpan_le_hodgeClasses_iff_filtered_lifts s p).2 hlift

/-- Algebraic degree-zero classes are Hodge, without any comparison between the component
construction and the separately defined codimension-zero Chow map. -/
theorem algebraicCycleClassSpan_zero_le_hodgeClasses :
    algebraicCycleClassSpan s 0 ≤ Hdg^0(ℚ; s) := by
  rw [hodgeClasses_zero_eq_top]
  exact le_top

/-- Above the dimension there are no nonzero algebraic classes, so every algebraic class is
Hodge. -/
theorem algebraicCycleClassSpan_le_hodgeClasses_of_lt (hp : dim X < p) :
    algebraicCycleClassSpan s p ≤ Hdg^p(ℚ; s) := by
  rw [algebraicCycleClassSpan_eq_bot_of_lt s (dim X) p hp]
  exact bot_le

/-- On a zero-dimensional smooth projective integral complex variety, every algebraic class is
Hodge in every codimension. -/
theorem algebraicCycleClassSpan_le_hodgeClasses_of_dimension_eq_zero
    (hd : dim X = 0) : algebraicCycleClassSpan s p ≤ Hdg^p(ℚ; s) := by
  obtain rfl | hp := Nat.eq_zero_or_pos p
  · exact algebraicCycleClassSpan_zero_le_hodgeClasses s
  · exact algebraicCycleClassSpan_le_hodgeClasses_of_lt s p (by simpa [hd] using hp)

/-- The constructed rational cycle-class map with values in Hodge classes, provided the Hodge
property of the constructed component classes is proved. -/
def rationalSheafCycleClassToHodgeClasses
    (h : ∀ (x : V.scheme) (hx : coheight x = p),
      IsHodgeClass ℚ V.structureMap p
        (cycleComponentSheafClass V.structureMap x (d := dim V.scheme) hx)) :
    (ℚ ⊗[ℤ] CodimensionCycle V.scheme p) →ₗ[ℚ] Hdg^p(ℚ; V.structureMap) :=
  (rationalSheafCycleClassOnCycles V p).codRestrict _ fun c =>
    (algebraicCycleClassSpan_le_hodgeClasses_iff V.structureMap p).2 h
      (rationalSheafCycleClassOnCycles_mem_algebraicCycleClassSpan V p c)

/-- Forgetting Hodge membership recovers the actual rational cycle class. -/
@[simp]
theorem rationalSheafCycleClassToHodgeClasses_coe
    (h : ∀ (x : V.scheme) (hx : coheight x = p),
      IsHodgeClass ℚ V.structureMap p
        (cycleComponentSheafClass V.structureMap x (d := dim V.scheme) hx))
    (c : ℚ ⊗[ℤ] CodimensionCycle V.scheme p) :
    (rationalSheafCycleClassToHodgeClasses V p h c :
      FieldCohomology ℚ V.structureMap (2 * (p : ℤ))) =
        rationalSheafCycleClassOnCycles V p c := rfl

end AlgebraicGeometry.ComplexPoint
