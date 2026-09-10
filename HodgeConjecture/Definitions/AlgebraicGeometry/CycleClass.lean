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
public import HodgeConjecture.Definitions.AlgebraicGeometry.CycleComponentSheafClass

/-!
# Cycle classes and coniveau

For a projective complex variety, a class supported on a closed set `Z` belongs to the homotopy
fiber of `RΓ(X, ℚ) → RΓ(X ∖ Z, ℚ)`, and its image in ordinary cohomology is the canonical
connecting map. The sum of these images over codimension-`p` algebraic subsets is a coniveau
subspace. It is only an upper bound for the span of cycle classes until cohomological purity has
been proved: arbitrary supported cohomology classes are not, by definition, fundamental classes.

This file therefore keeps the coniveau construction explicitly named as such. It constructs the
genuine Chow-group cycle-class map in codimension zero. It also retains an intrinsic component
line, defined using generators of the entire supported image, for stating comparison theorems.
The algebraic cycle-class span itself is instead defined from the actual normalized component
classes constructed in `CycleComponentSheafClass`.

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
      simpa using c.locallyFiniteSupport.finite_inter_support_of_isCompact
        (W := Set.univ) isCompact_univ)
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
a `codimensionCycleSubgroup` ensures that this branch is never used by a nonzero coefficient. -/
def cycleClassOnCyclesOfComponents {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (componentClass : ∀ (x : X), coheight x = p → M) :
    codimensionCycleSubgroup X p →+ M := by
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
        (codimensionCycleSubgroup.single x hx n) =
      n • componentClass x hx := by
  classical
  change (Finsupp.linearCombination ℤ (fun y ↦
      if hy : coheight y = p then componentClass y hy else 0))
    (compactCycleToFinsupp ((codimensionCycleInclusion X p)
      (codimensionCycleSubgroup.single x hx n))) = n • componentClass x hx
  have hsingle : compactCycleToFinsupp
      ((codimensionCycleInclusion X p) (codimensionCycleSubgroup.single x hx n)) =
      Finsupp.single x n := by
    ext y
    change codimensionCycleSubgroup.single x hx n y = Finsupp.single x n y
    rw [codimensionCycleSubgroup.single_apply, Finsupp.single_apply]
    by_cases h : y = x
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hsingle, Finsupp.linearCombination_single, dif_pos hx]

namespace ChowGroup

/-- An additive map on codimension cycles that vanishes on rational equivalences descends to the
Chow group. -/
def liftCycleClass {X : Scheme.{u}} {p : ℕ} {M : Type*} [AddCommGroup M]
    (f : codimensionCycleSubgroup X p →+ M)
    (h : rationalEquivalenceSubgroup X p ≤ f.ker) : ChowGroup X p →+ M :=
  QuotientAddGroup.lift (rationalEquivalenceSubgroup X p) f h

/-- Evaluation of a descended additive map on a represented Chow class. -/
@[simp] lemma liftCycleClass_mk {X : Scheme.{u}} {p : ℕ} {M : Type*} [AddCommGroup M]
    (f : codimensionCycleSubgroup X p →+ M)
    (h : rationalEquivalenceSubgroup X p ≤ f.ker) (z : codimensionCycleSubgroup X p) :
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

variable (X : Over (Spec ↧ℂ))

/-- The rational Chow class represented by an irreducible codimension-`p` component with
coefficient one. -/
def rationalComponentChowClass
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ)
    (x : X.left) (hx : coheight x = p) : RationalChowGroup X.left p :=
  ChowGroup.toRational (ChowGroup.mk (codimensionCycleSubgroup.single x hx 1))

/-! ### The genuine codimension-zero cycle class -/

/-- A codimension-zero cycle maps to the constant cohomology class given by the coefficient of
the generic component. -/
def codimensionZeroCycleClassOnCycles
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    codimensionCycleSubgroup X.left 0 →+ FieldCohomology ℚ X 0 :=
  (fieldCohomologyClassAddHom ℚ X).comp
    ((Int.castAddHom ℚ).comp codimensionCycleSubgroup.integralEquiv.toAddMonoidHom)

/-- Codimension-zero rational equivalences map to zero. Here this is a theorem rather than part
of the data of the cycle-class map: the rational-equivalence subgroup is trivial in codimension
zero. -/
lemma rationalEquivalenceSubgroup_le_codimensionZeroCycleClassOnCycles_ker
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    rationalEquivalenceSubgroup X.left 0 ≤
      (codimensionZeroCycleClassOnCycles X).ker := by
  rw [rationalEquivalenceSubgroup_zero]
  exact bot_le

/-- The genuine integral codimension-zero cycle-class map on the Chow group. -/
def codimensionZeroChowCycleClass
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ChowGroup X.left 0 →+ FieldCohomology ℚ X 0 :=
  ChowGroup.liftCycleClass (codimensionZeroCycleClassOnCycles X)
    (rationalEquivalenceSubgroup_le_codimensionZeroCycleClassOnCycles_ker X)

/-- Evaluation of the integral codimension-zero class map on a represented cycle. -/
@[simp] lemma codimensionZeroChowCycleClass_mk
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (z : codimensionCycleSubgroup X.left 0) :
    codimensionZeroChowCycleClass X (ChowGroup.mk z) =
      codimensionZeroCycleClassOnCycles X z :=
  ChowGroup.liftCycleClass_mk _ _ _

/-- The rational codimension-zero Chow group of an integral variety maps to degree-zero
cohomology by rational extension of the integral class map. -/
def codimensionZeroCycleClass
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    RationalChowGroup X.left 0 →ₗ[ℚ] FieldCohomology ℚ X 0 :=
  ChowGroup.rationalExtension (codimensionZeroChowCycleClass X)

/-- The generic component with coefficient one maps to the unit in degree-zero cohomology. -/
@[simp] lemma codimensionZeroCycleClass_genericPoint
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    codimensionZeroCycleClass X
        (ChowGroup.toRational
          (ChowGroup.mk (codimensionCycleSubgroup.single (genericPoint X.left)
            (Order.IsMax.coheight_eq_zero isMax_top) 1))) =
      fieldCohomologyUnit ℚ X := by
  unfold codimensionZeroCycleClass
  rw [ChowGroup.toRational_apply, ChowGroup.rationalExtension_tmul, one_smul,
    codimensionZeroChowCycleClass_mk]
  let z : codimensionCycleSubgroup X.left 0 :=
    codimensionCycleSubgroup.single (genericPoint X.left)
      (Order.IsMax.coheight_eq_zero isMax_top) 1
  have hz : codimensionCycleSubgroup.integralEquiv z = 1 := by
    change z (genericPoint X.left) = 1
    dsimp [z]
    exact codimensionCycleSubgroup.single_same (p := 0) (genericPoint X.left) _ 1
  change fieldCohomologyClass ℚ X
      ((codimensionCycleSubgroup.integralEquiv z : ℤ) : ℚ) =
    fieldCohomologyClass ℚ X 1
  rw [hz]
  norm_num

/-- The actual codimension-zero algebraic cycle-class span. -/
def codimensionZeroCycleClassSpan
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    Submodule ℚ (FieldCohomology ℚ X 0) :=
  LinearMap.range (codimensionZeroCycleClass X)

/-- In codimension zero the actual cycle-class span is the line generated by the cohomological
unit. This statement does not assert that the unit spans all of `H⁰`; that further conclusion
requires connectedness of the analytic space. -/
lemma codimensionZeroCycleClassSpan_eq_span_unit
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    codimensionZeroCycleClassSpan X =
      Submodule.span ℚ {fieldCohomologyUnit ℚ X} := by
  apply le_antisymm
  · rintro α ⟨z, rfl⟩
    rw [ChowGroup.rational_eq_smul_genericPoint X.left z, map_smul,
      codimensionZeroCycleClass_genericPoint]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      ⟨ChowGroup.toRational
        (ChowGroup.mk (codimensionCycleSubgroup.single (genericPoint X.left)
          (Order.IsMax.coheight_eq_zero isMax_top) 1)),
        codimensionZeroCycleClass_genericPoint X⟩)

/-! ### The coniveau subspace -/

/-- Rational constant-sheaf cohomology supported on a closed subset of an analytification. -/
abbrev RationalConstantSheafCohomologyWithSupport
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (Z : Set (ComplexPoint X)) (n : ℤ) :=
  RationalCohomologyWithSupport X Z n

/-- The rational span in ordinary cohomology of classes supported on `Z`. -/
def rationalCohomologySupportedOn
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (Z : Set (ComplexPoint X)) (n : ℤ) :
    Submodule ℚ (FieldCohomology ℚ X n) :=
  Submodule.span ℚ (Set.range (forgetSupport X Z n))

/-- A class which generates the whole degree-`2p` image of cohomology supported on one
irreducible component. This is a property inside ordinary rational cohomology; it does not assume
that the supported image is one-dimensional. Cohomological purity proves that such a generator
is precisely a nonzero rational multiple of the component's fundamental class. -/
def IsRationalComponentCycleClass
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (p : ℕ) (x : X.left) (α : FieldCohomology ℚ X (2 * (p : ℤ))) : Prop :=
  α ∈ rationalCohomologySupportedOn X
      (cycleComponentSupport X x) (2 * (p : ℤ)) ∧
    Submodule.span ℚ {α} =
      rationalCohomologySupportedOn X
        (cycleComponentSupport X x) (2 * (p : ℤ))

/-- The intrinsic cycle-class line of an irreducible codimension-`p` component. Taking the span
of all generators removes the arbitrary choice of generator and its rational scaling. -/
def rationalComponentCycleClassLine
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ) (x : X.left) :
    Submodule ℚ (FieldCohomology ℚ X (2 * (p : ℤ))) :=
  Submodule.span ℚ {α | IsRationalComponentCycleClass X p x α}

/-- Any generator of the supported image computes the same intrinsic component line. -/
lemma rationalComponentCycleClassLine_eq_span
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ) (x : X.left)
    (α : FieldCohomology ℚ X (2 * (p : ℤ)))
    (hα : IsRationalComponentCycleClass X p x α) :
    rationalComponentCycleClassLine X p x = Submodule.span ℚ {α} :=
  le_antisymm (Submodule.span_le.mpr fun _ hβ ↦ hα.2.ge hβ.1)
    (Submodule.span_mono (Set.singleton_subset_iff.mpr hα))

/-- Cohomological purity for a component, stated independently of the construction of any
particular supported class: its fundamental-class line is the whole supported image in the
critical degree. -/
def RationalComponentCycleClassPurity
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ) (x : X.left) : Prop :=
  rationalComponentCycleClassLine X p x =
    rationalCohomologySupportedOn X (cycleComponentSupport X x) (2 * (p : ℤ))

lemma rationalComponentCycleClassLine_eq_supportedOn_of_purity
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ) (x : X.left)
    (h : RationalComponentCycleClassPurity X p x) :
    rationalComponentCycleClassLine X p x =
      rationalCohomologySupportedOn X
        (cycleComponentSupport X x) (2 * (p : ℤ)) :=
  h

/-- The component cycle-class line lies in the image of cohomology supported on that component. -/
lemma rationalComponentCycleClassLine_le_supportedOn
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ) (x : X.left) :
    rationalComponentCycleClassLine X p x ≤
      rationalCohomologySupportedOn X
        (cycleComponentSupport X x) (2 * (p : ℤ)) :=
  Submodule.span_le.mpr fun _ hα ↦ hα.1

/-- The rational span of the actually constructed codimension-`p` component classes.

The relative dimension is the canonical `dim X`, whose certificate is proved from smoothness and
integrality. This definition spans explicit class terms; it does not quantify over hypothetical
generators and does not assume descent to the Chow group. -/
def algebraicCycleClassSpan
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ) :
    Submodule ℚ (FieldCohomology ℚ X (2 * (p : ℤ))) :=
  ⨆ (x : X.left) (hx : coheight x = p),
    Submodule.span ℚ {cycleComponentSheafClass X x (d := dim X.left) hx}

@[simp]
lemma algebraicCycleClassSpan_zero
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    algebraicCycleClassSpan X 0 =
      ⨆ (x : X.left) (hx : coheight x = 0),
        Submodule.span ℚ {cycleComponentSheafClass X x (d := dim X.left) hx} :=
  rfl

lemma algebraicCycleClassSpan_of_ne_zero
    [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (p : ℕ) (_hp : p ≠ 0) :
    algebraicCycleClassSpan X p =
      ⨆ (x : X.left) (hx : coheight x = p),
        Submodule.span ℚ {cycleComponentSheafClass X x (d := dim X.left) hx} :=
  rfl

/-- Every ordinary rational cohomology class is represented with support on the whole analytic
space. -/
lemma rationalCohomologySupportedOn_univ_eq_top
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℤ) :
    rationalCohomologySupportedOn X Set.univ n = ⊤ := by
  apply top_unique
  intro α _
  obtain ⟨β, hβ⟩ := forgetSupport_surjective_univ X n α
  exact Submodule.subset_span ⟨β, hβ⟩

/-- The component belonging to the generic point of an integral variety has the whole analytic
space as its support. -/
lemma cycleComponentSupport_genericPoint_eq_univ
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    cycleComponentSupport X (genericPoint X.left) = Set.univ := by
  rw [cycleComponentSupport]
  change (@Point.underlying ℂ _ _ X) ⁻¹'
    (closure {genericPoint X.left} : Set X.left) = Set.univ
  rw [genericPoint_closure (α := X.left)]
  exact Set.preimage_univ

/-- The degree-`2p` rational coniveau subspace obtained from all cohomology classes supported on
irreducible algebraic subvarieties of codimension `p`. This is not the cycle-class span unless a
purity theorem identifying each relevant image with its fundamental-class line is supplied. -/
def rationalConiveauSubspace
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ) :
    Submodule ℚ (FieldCohomology ℚ X (2 * (p : ℤ))) :=
  ⨆ (x : X.left) (_ : coheight x = p),
    rationalCohomologySupportedOn X (cycleComponentSupport X x) (2 * (p : ℤ))

/-- In codimension zero, the degree-zero coniveau subspace is all rational cohomology because
support on the whole space imposes no condition. This is a statement about coniveau, not about
the span of the codimension-zero cycle class. -/
lemma rationalConiveauSubspace_zero_eq_top
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    rationalConiveauSubspace X 0 = ⊤ := by
  apply top_unique
  rw [← rationalCohomologySupportedOn_univ_eq_top X 0,
    ← cycleComponentSupport_genericPoint_eq_univ X]
  apply le_iSup_of_le (genericPoint X.left)
  apply le_iSup_of_le (Order.IsMax.coheight_eq_zero isMax_top)
  rfl

/-- Forgetting the support of a class on one codimension-`p` component lands in the corresponding
coniveau subspace. -/
lemma forgetSupport_mem_rationalConiveauSubspace
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ)
    (x : X.left) (hx : coheight x = p)
    (α : RationalConstantSheafCohomologyWithSupport X
      (cycleComponentSupport X x) (2 * (p : ℤ))) :
    forgetSupport X (cycleComponentSupport X x) (2 * (p : ℤ)) α ∈
      rationalConiveauSubspace X p := by
  apply (le_iSup (fun x : X.left => ⨆ hx : coheight x = p,
    rationalCohomologySupportedOn X
      (cycleComponentSupport X x) (2 * (p : ℤ))) x)
  apply (le_iSup (fun _ : coheight x = p =>
    rationalCohomologySupportedOn X
      (cycleComponentSupport X x) (2 * (p : ℤ))) hx)
  exact Submodule.subset_span ⟨α, rfl⟩

/-- Every constructed algebraic cycle class has coniveau at least its codimension. -/
lemma algebraicCycleClassSpan_le_rationalConiveauSubspace
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ) :
    algebraicCycleClassSpan X p ≤ rationalConiveauSubspace X p := by
  refine iSup_le fun x ↦ iSup_le fun hx ↦ ?_
  apply Submodule.span_le.mpr
  intro α hα
  rw [Set.mem_singleton_iff] at hα
  subst α
  apply (le_iSup (fun x : X.left => ⨆ hx : coheight x = p,
    rationalCohomologySupportedOn X
      (cycleComponentSupport X x) (2 * (p : ℤ))) x)
  apply (le_iSup (fun _ : coheight x = p =>
    rationalCohomologySupportedOn X
      (cycleComponentSupport X x) (2 * (p : ℤ))) hx)
  rw [cycleComponentSheafClass_eq_forgetSupport]
  exact Submodule.subset_span ⟨cycleComponentSheafSupportedClass
    X x (d := dim X.left) hx, rfl⟩

/-- If every constructed component class spans its entire supported image, the algebraic
cycle-class span agrees with the coniveau subspace. The equality for each component is an
explicit hypothesis; it is not built into either construction. -/
lemma algebraicCycleClassSpan_eq_rationalConiveauSubspace_of_purity
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ)
    (h : ∀ (x : X.left) (hx : coheight x = p),
      Submodule.span ℚ {cycleComponentSheafClass X x (d := dim X.left) hx} =
        rationalCohomologySupportedOn X
          (cycleComponentSupport X x) (2 * (p : ℤ))) :
    algebraicCycleClassSpan X p = rationalConiveauSubspace X p := by
  refine le_antisymm (algebraicCycleClassSpan_le_rationalConiveauSubspace X p)
    (iSup_le fun x ↦ iSup_le fun hx ↦ ?_)
  rw [← h x hx]
  exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)
end AlgebraicGeometry.ComplexPoint
