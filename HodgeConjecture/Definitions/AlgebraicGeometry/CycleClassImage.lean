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

public import HodgeConjecture.Definitions.AlgebraicGeometry.CycleComponentSupport
public import HodgeConjecture.Definitions.AlgebraicGeometry.CohomologyWithSupport
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Intrinsic cycle-class images and coniveau

The support-forgetting map sends cohomology supported on an irreducible algebraic subset into
ordinary rational cohomology. A component contributes the span of the generators of this image.
This is an intrinsic condition: no generator, normalization, or map from a Chow group is chosen.

The generator span equals the image exactly when the image has rank at most one. A geometric
purity theorem can identify it with the usual fundamental-class line in the critical degree.
The sum of the entire supported images is separately named the coniveau subspace.

In codimension zero, the algebraic-class span is the unit line. The Chow-group compatibility
module `CycleClass` proves that this is the image of its codimension-zero cycle-class map.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ))

/-! ### The coniveau subspace -/

/-- Rational constant-sheaf cohomology supported on a closed subset of an analytification. -/
abbrev RationalConstantSheafCohomologyWithSupport
    [IsIntegral X] [Smooth structureMap]
    [ProjectiveSpace.IsProjective structureMap] (Z : Set (ComplexPoint X structureMap)) (n : ℤ) :=
  RationalCohomologyWithSupport structureMap Z n

/-- The rational span in ordinary cohomology of classes supported on `Z`. -/
def rationalCohomologySupportedOn
    [IsIntegral X] [Smooth structureMap]
    [ProjectiveSpace.IsProjective structureMap] (Z : Set (ComplexPoint X structureMap)) (n : ℤ) :
    Submodule ℚ (RationalCohomology structureMap n) :=
  Submodule.span ℚ (Set.range (forgetSupport structureMap Z n))

/-- A generator of the degree-`2p` supported image of the closure of `x`.
For `coheight x = p`, purity identifies this image with the component's fundamental-class line.
A generator is nonzero when the supported image is nonzero; zero generates the zero image. -/
def IsRationalComponentCycleClass
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap]
    (p : ℕ) (x : X) (α : RationalCohomology structureMap (2 * (p : ℤ))) : Prop :=
  Submodule.span ℚ {α} =
    rationalCohomologySupportedOn structureMap
      (cycleComponentSupport structureMap x) (2 * (p : ℤ))

/-- A generator belongs to the supported image it generates. -/
lemma IsRationalComponentCycleClass.mem_supportedOn
    {structureMap : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap]
    {p : ℕ} {x : X} {α : RationalCohomology structureMap (2 * (p : ℤ))}
    (hα : IsRationalComponentCycleClass structureMap p x α) :
    α ∈ rationalCohomologySupportedOn structureMap
      (cycleComponentSupport structureMap x) (2 * (p : ℤ)) := by
  rw [← hα]
  exact Submodule.subset_span (Set.mem_singleton α)

/-- Explicit membership is redundant in the component-generator criterion. -/
lemma isRationalComponentCycleClass_iff_mem_and_span
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap]
    (p : ℕ) (x : X) (α : RationalCohomology structureMap (2 * (p : ℤ))) :
    IsRationalComponentCycleClass structureMap p x α ↔
      α ∈ rationalCohomologySupportedOn structureMap
          (cycleComponentSupport structureMap x) (2 * (p : ℤ)) ∧
        Submodule.span ℚ {α} = rationalCohomologySupportedOn structureMap
          (cycleComponentSupport structureMap x) (2 * (p : ℤ)) := by
  exact ⟨fun h ↦ ⟨h.mem_supportedOn, h⟩, fun h ↦ h.2⟩

/-- The span of all generators of the degree-`2p` supported image of the closure of `x`.
The final cycle-class span restricts to points of coheight `p`. This construction is the whole
supported image when that image has rank at most one, and zero otherwise. -/
def rationalComponentCycleClassLine
    [IsIntegral X] [Smooth structureMap]
    [ProjectiveSpace.IsProjective structureMap] (p : ℕ) (x : X) :
    Submodule ℚ (RationalCohomology structureMap (2 * (p : ℤ))) :=
  Submodule.span ℚ {α | IsRationalComponentCycleClass structureMap p x α}

/-- Any generator of the supported image computes the same intrinsic component line. -/
lemma rationalComponentCycleClassLine_eq_span
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (p : ℕ) (x : X)
    (α : RationalCohomology structureMap (2 * (p : ℤ)))
    (hα : IsRationalComponentCycleClass structureMap p x α) :
    rationalComponentCycleClassLine structureMap p x = Submodule.span ℚ {α} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro β hβ
    have hβ' := hβ.mem_supportedOn
    rw [← hα] at hβ'
    exact hβ'
  · apply Submodule.span_mono
    intro β hβ
    rw [Set.mem_singleton_iff] at hβ
    subst β
    exact hα

/-- The component line is its whole supported image. This condition is equivalent to the image
having rank at most one, including the zero image. It does not assert nonvanishing or cyclicity
of the supported cohomology group. The geometric purity interpretation uses `coheight x = p`. -/
def RationalComponentCycleClassPurity
    [IsIntegral X] [Smooth structureMap]
    [ProjectiveSpace.IsProjective structureMap] (p : ℕ) (x : X) : Prop :=
  rationalComponentCycleClassLine structureMap p x =
    rationalCohomologySupportedOn structureMap (cycleComponentSupport structureMap x) (2 * (p : ℤ))

/-- Component purity asks precisely for a principal supported image. -/
lemma rationalComponentCycleClassPurity_iff_isPrincipal
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap]
    (p : ℕ) (x : X) :
    RationalComponentCycleClassPurity structureMap p x ↔
      (rationalCohomologySupportedOn structureMap
        (cycleComponentSupport structureMap x) (2 * (p : ℤ))).IsPrincipal := by
  classical
  let I := rationalCohomologySupportedOn structureMap
    (cycleComponentSupport structureMap x) (2 * (p : ℤ))
  change rationalComponentCycleClassLine structureMap p x = I ↔ I.IsPrincipal
  rw [Submodule.isPrincipal_iff]
  constructor
  · intro heq
    by_contra h
    have hempty : {α | IsRationalComponentCycleClass structureMap p x α} = ∅ := by
      ext α
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hα
      exact h ⟨α, hα.symm⟩
    have hI : I = ⊥ := by
      rw [← heq, rationalComponentCycleClassLine, hempty, Submodule.span_empty]
    exact h ⟨0, by simp [hI]⟩
  · rintro ⟨α, hα⟩
    exact (rationalComponentCycleClassLine_eq_span structureMap p x α hα.symm).trans hα.symm

/-- The principal-image condition includes both rank zero and rank one. -/
lemma rationalComponentCycleClassPurity_iff_rank_le_one
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap]
    (p : ℕ) (x : X) :
    RationalComponentCycleClassPurity structureMap p x ↔
      Module.rank ℚ (rationalCohomologySupportedOn structureMap
        (cycleComponentSupport structureMap x) (2 * (p : ℤ))) ≤ 1 := by
  rw [rationalComponentCycleClassPurity_iff_isPrincipal,
    Submodule.rank_le_one_iff_isPrincipal]

/-- An image without a single generator contributes no component line. -/
lemma rationalComponentCycleClassLine_eq_bot_of_not_isPrincipal
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap]
    (p : ℕ) (x : X)
    (h : ¬ (rationalCohomologySupportedOn structureMap
      (cycleComponentSupport structureMap x) (2 * (p : ℤ))).IsPrincipal) :
    rationalComponentCycleClassLine structureMap p x = ⊥ := by
  apply bot_unique
  apply Submodule.span_le.mpr
  intro α hα
  exfalso
  apply h
  rw [Submodule.isPrincipal_iff]
  exact ⟨α, hα.symm⟩

lemma rationalComponentCycleClassLine_eq_supportedOn_of_purity
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (p : ℕ) (x : X)
    (h : RationalComponentCycleClassPurity structureMap p x) :
    rationalComponentCycleClassLine structureMap p x =
      rationalCohomologySupportedOn structureMap
        (cycleComponentSupport structureMap x) (2 * (p : ℤ)) := by
  exact h

/-- The component cycle-class line lies in the image of cohomology supported on that component. -/
lemma rationalComponentCycleClassLine_le_supportedOn
    [IsIntegral X] [Smooth structureMap]
    [ProjectiveSpace.IsProjective structureMap] (p : ℕ) (x : X) :
    rationalComponentCycleClassLine structureMap p x ≤
      rationalCohomologySupportedOn structureMap
        (cycleComponentSupport structureMap x) (2 * (p : ℤ)) := by
  apply Submodule.span_le.mpr
  intro α hα
  exact hα.mem_supportedOn

/-- The intrinsic rational span of algebraic cycle classes in codimension `p`.
In codimension zero this is the line generated by the cohomological unit. In positive codimension,
a component contributes through generators of its supported image. Purity identifies this line
with the usual class `cl(Z)`. Compatibility with Chow groups is proved in `CycleClass`. -/
def algebraicCycleClassSpan
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (p : ℕ) :
    Submodule ℚ (RationalCohomology structureMap (2 * (p : ℤ))) :=
  if hp : p = 0 then hp ▸ Submodule.span ℚ {rationalCohomologyUnit structureMap}
  else ⨆ (x : X) (_ : coheight x = p), rationalComponentCycleClassLine structureMap p x

@[simp]
lemma algebraicCycleClassSpan_zero_eq_span_unit
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] :
    algebraicCycleClassSpan structureMap 0 =
      Submodule.span ℚ {rationalCohomologyUnit structureMap} := by
  simp [algebraicCycleClassSpan]

lemma algebraicCycleClassSpan_of_ne_zero
    [IsIntegral X] [Smooth structureMap]
    [ProjectiveSpace.IsProjective structureMap] (p : ℕ) (hp : p ≠ 0) :
    algebraicCycleClassSpan structureMap p =
      ⨆ (x : X) (_ : coheight x = p), rationalComponentCycleClassLine structureMap p x := by
  simp [algebraicCycleClassSpan, hp]

/-- Every ordinary rational cohomology class is represented with support on the whole analytic
space. -/
lemma rationalCohomologySupportedOn_univ_eq_top
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (n : ℤ) :
    rationalCohomologySupportedOn structureMap Set.univ n = ⊤ := by
  apply top_unique
  intro α _
  obtain ⟨β, hβ⟩ := forgetSupport_surjective_univ structureMap n α
  exact Submodule.subset_span ⟨β, hβ⟩

/-- The component belonging to the generic point of an integral variety has the whole analytic
space as its support. -/
lemma cycleComponentSupport_genericPoint_eq_univ
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] :
    cycleComponentSupport structureMap (genericPoint X) = Set.univ := by
  rw [cycleComponentSupport, genericPoint_closure]
  exact Set.preimage_univ

/-- The degree-`2p` rational coniveau subspace obtained from all cohomology classes supported on
irreducible algebraic subvarieties of codimension `p`. This is not the cycle-class span unless a
purity theorem identifying each relevant image with its fundamental-class line is supplied. -/
def rationalConiveauSubspace
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (p : ℕ) :
    Submodule ℚ (RationalCohomology structureMap (2 * (p : ℤ))) :=
  ⨆ (x : X) (_ : coheight x = p),
    rationalCohomologySupportedOn structureMap (cycleComponentSupport structureMap x) (2 * (p : ℤ))

/-- In codimension zero, the degree-zero coniveau subspace is all rational cohomology because
support on the whole space imposes no condition. This is a statement about coniveau, not about
the span of the codimension-zero cycle class. -/
lemma rationalConiveauSubspace_zero_eq_top
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] :
    rationalConiveauSubspace structureMap 0 = ⊤ := by
  apply top_unique
  rw [← rationalCohomologySupportedOn_univ_eq_top structureMap 0,
    ← cycleComponentSupport_genericPoint_eq_univ structureMap]
  apply le_iSup_of_le (genericPoint X)
  apply le_iSup_of_le (Order.IsMax.coheight_eq_zero isMax_top)
  rfl

/-- Forgetting the support of a class on one codimension-`p` component lands in the corresponding
coniveau subspace. -/
lemma forgetSupport_mem_rationalConiveauSubspace
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (p : ℕ)
    (x : X) (hx : coheight x = p)
    (α : RationalConstantSheafCohomologyWithSupport structureMap
      (cycleComponentSupport structureMap x) (2 * (p : ℤ))) :
    forgetSupport structureMap (cycleComponentSupport structureMap x) (2 * (p : ℤ)) α ∈
      rationalConiveauSubspace structureMap p := by
  apply (le_iSup (fun x : X => ⨆ hx : coheight x = p,
    rationalCohomologySupportedOn structureMap
      (cycleComponentSupport structureMap x) (2 * (p : ℤ))) x)
  apply (le_iSup (fun _ : coheight x = p =>
    rationalCohomologySupportedOn structureMap
      (cycleComponentSupport structureMap x) (2 * (p : ℤ))) hx)
  exact Submodule.subset_span ⟨α, rfl⟩

/-- Every algebraic cycle class has coniveau at least its codimension. The reverse inclusion is
the purity statement that arbitrary supported classes in degree `2p` are multiples of the
fundamental class. -/
lemma algebraicCycleClassSpan_le_rationalConiveauSubspace
    [IsIntegral X] [Smooth structureMap] [ProjectiveSpace.IsProjective structureMap] (p : ℕ) :
    algebraicCycleClassSpan structureMap p ≤ rationalConiveauSubspace structureMap p := by
  by_cases hp : p = 0
  · subst p
    rw [rationalConiveauSubspace_zero_eq_top]
    exact le_top
  · rw [algebraicCycleClassSpan_of_ne_zero structureMap p hp]
    refine iSup_le fun x ↦ iSup_le fun hx ↦ ?_
    apply (rationalComponentCycleClassLine_le_supportedOn structureMap p x).trans
    apply le_iSup_of_le x
    apply le_iSup_of_le hx
    rfl

end AlgebraicGeometry.ComplexPoint
