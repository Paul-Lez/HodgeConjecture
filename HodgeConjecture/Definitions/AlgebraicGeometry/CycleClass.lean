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
public import HodgeConjecture.Definitions.AlgebraicGeometry.CohomologyWithSupport

/-!
# Cycle classes and coniveau

For a projective complex variety, a class supported on a closed set `Z` belongs to the homotopy
fiber of `RΓ(X, ℚ) → RΓ(X ∖ Z, ℚ)`, and its image in ordinary cohomology is the canonical
connecting map. The sum of these images over codimension-`p` algebraic subsets is a coniveau
subspace. It is only an upper bound for the span of cycle classes until cohomological purity has
been proved: arbitrary supported cohomology classes are not, by definition, fundamental classes.

This file therefore keeps the coniveau construction explicitly named as such. It constructs the
genuine Chow-group cycle-class map in codimension zero. In every codimension it also defines the
intrinsic component class line as the span of those classes which generate the component's entire
supported image. This generator condition is a proposition, not an assumed purity theorem. It
removes choices of sign and rational scaling, while a later purity theorem can prove that the
condition is inhabited and agrees with the usual locally normalized fundamental class.

A positive-codimension map on Chow groups additionally requires Gysin compatibility and
vanishing on rational equivalences; neither fact is postulated here. The Hodge conjecture itself
only needs the span of classes of irreducible subvarieties, so it does not require choosing such a
Chow-group map.

The elementary constructions at the start of the file record how an independently constructed
map on cycles descends to Chow groups once vanishing on rational equivalences has been proved.
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

open Point

variable {X : Scheme} (structureMap : X ⟶ Spec ↧ℂ)

/-- The rational Chow class represented by an irreducible codimension-`p` component with
coefficient one. -/
def rationalComponentChowClass
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (p : ℕ)
    (x : X) (hx : coheight x = p) : RationalChowGroup X p :=
  ChowGroup.toRational (ChowGroup.mk (CodimensionCycle.single x hx 1))

/-! ### The genuine codimension-zero cycle class -/

/-- A codimension-zero cycle maps to the constant cohomology class given by the coefficient of
the generic component. -/
def codimensionZeroCycleClassOnCycles
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] :
    CodimensionCycle X 0 →+ FieldCohomology ℚ structureMap 0 :=
  (fieldCohomologyClassAddHom ℚ structureMap).comp
    ((Int.castAddHom ℚ).comp CodimensionCycle.integralEquiv.toAddMonoidHom)

/-- Codimension-zero rational equivalences map to zero. Here this is a theorem rather than part
of the data of the cycle-class map: the rational-equivalence subgroup is trivial in codimension
zero. -/
lemma rationalEquivalenceSubgroup_le_codimensionZeroCycleClassOnCycles_ker
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] :
    rationalEquivalenceSubgroup X 0 ≤
      (codimensionZeroCycleClassOnCycles structureMap).ker := by
  rw [rationalEquivalenceSubgroup_zero]
  exact bot_le

/-- The genuine integral codimension-zero cycle-class map on the Chow group. -/
def codimensionZeroChowCycleClass
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] :
    ChowGroup X 0 →+ FieldCohomology ℚ structureMap 0 :=
  ChowGroup.liftCycleClass (codimensionZeroCycleClassOnCycles structureMap)
    (rationalEquivalenceSubgroup_le_codimensionZeroCycleClassOnCycles_ker structureMap)

/-- Evaluation of the integral codimension-zero class map on a represented cycle. -/
@[simp] lemma codimensionZeroChowCycleClass_mk
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (z : CodimensionCycle X 0) :
    codimensionZeroChowCycleClass structureMap (ChowGroup.mk z) =
      codimensionZeroCycleClassOnCycles structureMap z := by
  exact ChowGroup.liftCycleClass_mk _ _ _

/-- The rational codimension-zero Chow group of an integral variety maps to degree-zero
cohomology by rational extension of the integral class map. -/
def codimensionZeroCycleClass
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] :
    RationalChowGroup X 0 →ₗ[ℚ] FieldCohomology ℚ structureMap 0 :=
  ChowGroup.rationalExtension (codimensionZeroChowCycleClass structureMap)

/-- The generic component with coefficient one maps to the unit in degree-zero cohomology. -/
@[simp] lemma codimensionZeroCycleClass_genericPoint
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] :
    codimensionZeroCycleClass structureMap
        (ChowGroup.toRational
          (ChowGroup.mk (CodimensionCycle.single (genericPoint X)
            (Order.IsMax.coheight_eq_zero isMax_top) 1))) =
      fieldCohomologyUnit ℚ structureMap := by
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
  change fieldCohomologyClass ℚ structureMap
      ((CodimensionCycle.integralEquiv z : ℤ) : ℚ) =
    fieldCohomologyClass ℚ structureMap 1
  rw [hz]
  norm_num

/-- The actual codimension-zero algebraic cycle-class span. -/
def codimensionZeroCycleClassSpan
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] :
    Submodule ℚ (FieldCohomology ℚ structureMap 0) :=
  LinearMap.range (codimensionZeroCycleClass structureMap)

/-- In codimension zero the actual cycle-class span is the line generated by the cohomological
unit. This statement does not assert that the unit spans all of `H⁰`; that further conclusion
requires connectedness of the analytic space. -/
lemma codimensionZeroCycleClassSpan_eq_span_unit
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] :
    codimensionZeroCycleClassSpan structureMap =
      Submodule.span ℚ {fieldCohomologyUnit ℚ structureMap} := by
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

/-! ### The coniveau subspace -/

/-- Rational constant-sheaf cohomology supported on a closed subset of an analytification. -/
abbrev RationalConstantSheafCohomologyWithSupport
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (Z : Set (ComplexPoint (Over.mk structureMap))) (n : ℤ) :=
  RationalCohomologyWithSupport structureMap Z n

/-- The rational span in ordinary cohomology of classes supported on `Z`. -/
def rationalCohomologySupportedOn
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (Z : Set (ComplexPoint (Over.mk structureMap))) (n : ℤ) :
    Submodule ℚ (FieldCohomology ℚ structureMap n) :=
  Submodule.span ℚ (Set.range (forgetSupport structureMap Z n))

/-- A class which generates the whole degree-`2p` image of cohomology supported on one
irreducible component. This is a property inside ordinary rational cohomology; it does not assume
that the supported image is one-dimensional. Cohomological purity proves that such a generator
is precisely a nonzero rational multiple of the component's fundamental class. -/
def IsRationalComponentCycleClass
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap]
    (p : ℕ) (x : X) (α : FieldCohomology ℚ structureMap (2 * (p : ℤ))) : Prop :=
  α ∈ rationalCohomologySupportedOn structureMap
      (cycleComponentSupport structureMap x) (2 * (p : ℤ)) ∧
    Submodule.span ℚ {α} =
      rationalCohomologySupportedOn structureMap
        (cycleComponentSupport structureMap x) (2 * (p : ℤ))

/-- The intrinsic cycle-class line of an irreducible codimension-`p` component. Taking the span
of all generators removes the arbitrary choice of generator and its rational scaling. -/
def rationalComponentCycleClassLine
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (p : ℕ) (x : X) :
    Submodule ℚ (FieldCohomology ℚ structureMap (2 * (p : ℤ))) :=
  Submodule.span ℚ {α | IsRationalComponentCycleClass structureMap p x α}

/-- Any generator of the supported image computes the same intrinsic component line. -/
lemma rationalComponentCycleClassLine_eq_span
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (p : ℕ) (x : X)
    (α : FieldCohomology ℚ structureMap (2 * (p : ℤ)))
    (hα : IsRationalComponentCycleClass structureMap p x α) :
    rationalComponentCycleClassLine structureMap p x = Submodule.span ℚ {α} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro β hβ
    have hβ' := hβ.1
    rw [← hα.2] at hβ'
    exact hβ'
  · apply Submodule.span_mono
    intro β hβ
    rw [Set.mem_singleton_iff] at hβ
    subst β
    exact hα

/-- Cohomological purity for a component, stated independently of the construction of any
particular supported class: its fundamental-class line is the whole supported image in the
critical degree. -/
def RationalComponentCycleClassPurity
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (p : ℕ) (x : X) : Prop :=
  rationalComponentCycleClassLine structureMap p x =
    rationalCohomologySupportedOn structureMap (cycleComponentSupport structureMap x) (2 * (p : ℤ))

lemma rationalComponentCycleClassLine_eq_supportedOn_of_purity
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (p : ℕ) (x : X)
    (h : RationalComponentCycleClassPurity structureMap p x) :
    rationalComponentCycleClassLine structureMap p x =
      rationalCohomologySupportedOn structureMap
        (cycleComponentSupport structureMap x) (2 * (p : ℤ)) := by
  exact h

/-- The component cycle-class line lies in the image of cohomology supported on that component. -/
lemma rationalComponentCycleClassLine_le_supportedOn
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (p : ℕ) (x : X) :
    rationalComponentCycleClassLine structureMap p x ≤
      rationalCohomologySupportedOn structureMap
        (cycleComponentSupport structureMap x) (2 * (p : ℤ)) := by
  apply Submodule.span_le.mpr
  intro α hα
  exact hα.1

/-- The rational span of algebraic cycle classes in codimension `p`. In codimension zero this is
the range of the genuine Chow-group cycle-class map constructed above. In positive codimension,
a component contributes only through a generator of its supported image; cohomological purity
identifies this line with the usual class `cl(Z)`. -/
def algebraicCycleClassSpan
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (p : ℕ) :
    Submodule ℚ (FieldCohomology ℚ structureMap (2 * (p : ℤ))) :=
  if hp : p = 0 then hp ▸ codimensionZeroCycleClassSpan structureMap
  else ⨆ (x : X) (_ : coheight x = p), rationalComponentCycleClassLine structureMap p x

@[simp]
lemma algebraicCycleClassSpan_zero
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] :
    algebraicCycleClassSpan structureMap 0 = codimensionZeroCycleClassSpan structureMap := by
  simp [algebraicCycleClassSpan]

lemma algebraicCycleClassSpan_of_ne_zero
    [IsIntegral X] [Smooth structureMap]
    [IsProjective structureMap] (p : ℕ) (hp : p ≠ 0) :
    algebraicCycleClassSpan structureMap p =
      ⨆ (x : X) (_ : coheight x = p), rationalComponentCycleClassLine structureMap p x := by
  simp [algebraicCycleClassSpan, hp]

/-- Every ordinary rational cohomology class is represented with support on the whole analytic
space. -/
lemma rationalCohomologySupportedOn_univ_eq_top
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (n : ℤ) :
    rationalCohomologySupportedOn structureMap Set.univ n = ⊤ := by
  apply top_unique
  intro α _
  obtain ⟨β, hβ⟩ := forgetSupport_surjective_univ structureMap n α
  exact Submodule.subset_span ⟨β, hβ⟩

/-- The component belonging to the generic point of an integral variety has the whole analytic
space as its support. -/
lemma cycleComponentSupport_genericPoint_eq_univ
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] :
    cycleComponentSupport structureMap (genericPoint X) = Set.univ := by
  rw [cycleComponentSupport]
  change (@Point.underlying ℂ _ _ (Over.mk structureMap)) ⁻¹'
    (closure {genericPoint X} : Set X) = Set.univ
  rw [genericPoint_closure (α := X)]
  exact Set.preimage_univ

/-- The degree-`2p` rational coniveau subspace obtained from all cohomology classes supported on
irreducible algebraic subvarieties of codimension `p`. This is not the cycle-class span unless a
purity theorem identifying each relevant image with its fundamental-class line is supplied. -/
def rationalConiveauSubspace
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (p : ℕ) :
    Submodule ℚ (FieldCohomology ℚ structureMap (2 * (p : ℤ))) :=
  ⨆ (x : X) (_ : coheight x = p),
    rationalCohomologySupportedOn structureMap (cycleComponentSupport structureMap x) (2 * (p : ℤ))

/-- In codimension zero, the degree-zero coniveau subspace is all rational cohomology because
support on the whole space imposes no condition. This is a statement about coniveau, not about
the span of the codimension-zero cycle class. -/
lemma rationalConiveauSubspace_zero_eq_top
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] :
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
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (p : ℕ)
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
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (p : ℕ) :
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

/-- If the codimension-zero unit spans degree-zero cohomology and positive-codimension purity has
been proved for every relevant component, the algebraic cycle-class span agrees with the
coniveau subspace. The separate degree-zero hypothesis records the connectedness calculation
needed to identify `H⁰` with the line generated by the unit. -/
lemma algebraicCycleClassSpan_eq_rationalConiveauSubspace_of_purity
    [IsIntegral X] [Smooth structureMap] [IsProjective structureMap] (p : ℕ)
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
