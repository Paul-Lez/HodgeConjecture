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

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.Filtration
public import Other.Mathlib.Topology.Category.TopCat.Basic
public import Other.Algebra.Homology.ShiftedExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation

/-!
# Rational cohomology with support

The definitions in this file, and the lemmas about them, are reached from the statement of the
conjecture only through proofs, so the statement never inspects them: by proof irrelevance
nothing about how they were built can change what it asserts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

local instance analyticSupportHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- Let `X` be a scheme over `ℂ` and `Z ⊆ X(ℂ)`. This is the continuous inclusion `X(ℂ) \ Z → X(ℂ)`,
where complex points have the analytic topology and the complement has the subspace topology. -/
def analyticComplementInclusion (Z : Set (ComplexPoint X)) :
    TopCat.of ↥Zᶜ ⟶
      TopCat.of (ComplexPoint X) :=
  TopCat.subtypeInclusion (TopCat.of (ComplexPoint X)) Zᶜ

/-- Let `X` be a scheme over `ℂ` and `Z ⊆ X(ℂ)`. This is the category of sheaves of abelian groups
on the subspace `X(ℂ) \ Z` of the analytic space of complex points. -/
abbrev AnalyticComplementAdditiveSheaf (Z : Set (ComplexPoint X)) :=
  TopCat.Sheaf AddCommGrpCat (TopCat.of ↥Zᶜ)

/-- Let `X` be a scheme over `ℂ`, `Z ⊆ X(ℂ)`, and `j : X(ℂ) \ Z → X(ℂ)` the inclusion. This is
`j_*ℚ`, the sheaf whose sections on an analytic open `V` are locally constant rational-valued
functions on `V \ Z`. -/
def pushforwardComplementConstantRationalSheaf
    (Z : Set (ComplexPoint X)) : AnalyticAdditiveSheaf X :=
  (TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticComplementInclusion X Z)).obj
      𝓒(↧↥Zᶜ; ℚ)

/-- Let `X` be a scheme over `ℂ` and `Z ⊆ X(ℂ)`. This map sends a rational number on each analytic
open `V` to the constant function with that value on `V \ Z`. Its source is the constant
presheaf and its target is the direct image of the constant sheaf on the complement. -/
def rationalRestrictionPresheaf (Z : Set (ComplexPoint X)) :
    𝓒ᵖ(↧(ComplexPoint X); ℚ) ⟶
      (pushforwardComplementConstantRationalSheaf X Z).obj :=
  let U := TopCat.of ↥Zᶜ
  let J := Opens.grothendieckTopology U
  Functor.whiskerLeft (Opens.map (analyticComplementInclusion X Z)).op
    ((sheafificationAdjunction J AddCommGrpCat).unit.app
      𝓒ᵖ(U; ℚ))

/-- Let `X` be a scheme over `ℂ`, `Z ⊆ X(ℂ)`, and `j : X(ℂ) \ Z → X(ℂ)` the inclusion. This is the
sheaf morphism `ℚ → j_*ℚ` that restricts locally constant rational-valued functions from `V` to
`V \ Z` on every analytic open `V`. -/
def rationalRestrictionSheaf (Z : Set (ComplexPoint X)) :
    𝓒(↧(ComplexPoint X); ℚ) ⟶
      pushforwardComplementConstantRationalSheaf X Z :=
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))
  ⟨sheafifyLift J (rationalRestrictionPresheaf X Z)
    (pushforwardComplementConstantRationalSheaf X Z).property⟩

/-- Let `X` be a scheme over `ℂ` and `Z ⊆ X(ℂ)`. Choose an injective resolution `ℚ → I^•` of the
constant rational sheaf on the analytic subspace `X(ℂ) \ Z`. The complex is indexed by
nonnegative integers and is exact after the augmentation. -/
def complementConstantRationalInjectiveResolution
    (Z : Set (ComplexPoint X)) :
    InjectiveResolution 𝓒(↧↥Zᶜ; ℚ) :=
  injectiveResolution 𝓒(↧↥Zᶜ; ℚ)

/-- Let `X` be a scheme over `ℂ`, `Z ⊆ X(ℂ)`, and `j : X(ℂ) \ Z → X(ℂ)` the inclusion. Resolve the
constant rational sheaf on the complement by injective sheaves `I^•` and apply `j_*` in each
degree. The resulting complex `j_*I^•`, indexed by nonnegative integers, represents `Rj_*ℚ`. -/
def derivedPushforwardComplementConstantRationalComplexNat
    (Z : Set (ComplexPoint X)) :
    CochainComplex (AnalyticAdditiveSheaf X) ℕ :=
  ((TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticComplementInclusion X Z)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
    (complementConstantRationalInjectiveResolution X Z).cocomplex

/-- Every additive sheaf on the empty complement is a zero object. -/
private lemma isZero_sheaf_on_complement_univ
    (F : TopCat.Sheaf AddCommGrpCat.{0}
      (TopCat.of ↥((Set.univ : Set (ComplexPoint X))ᶜ))) :
    IsZero F :=
  (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero
    (C := AddCommGrpCat.{0})
    (X := TopCat.of ↥((Set.univ : Set (ComplexPoint X))ᶜ)) F).2
    fun x ↦ (show False by simpa using x.property).elim

/-- Every term of the derived pushforward from the empty complement is zero. -/
private lemma isZero_derivedPushforwardComplement_univ_X (n : ℕ) :
    IsZero ((derivedPushforwardComplementConstantRationalComplexNat X
      (Set.univ : Set (ComplexPoint X))).X n) :=
  (TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticComplementInclusion X
      (Set.univ : Set (ComplexPoint X)))).map_isZero
        (isZero_sheaf_on_complement_univ X _)

/-- The complex representing derived pushforward from the empty complement is a zero object. -/
private lemma isZero_derivedPushforwardComplement_univ :
    IsZero (derivedPushforwardComplementConstantRationalComplexNat X
      (Set.univ : Set (ComplexPoint X))) := by
  constructor
  · exact fun K ↦ ⟨⟨⟨0⟩, fun f ↦ HomologicalComplex.hom_ext _ _ fun n ↦
      (isZero_derivedPushforwardComplement_univ_X X n).eq_zero_of_src _⟩⟩
  · exact fun K ↦ ⟨⟨⟨0⟩, fun f ↦ HomologicalComplex.hom_ext _ _ fun n ↦
      (isZero_derivedPushforwardComplement_univ_X X n).eq_zero_of_tgt _⟩⟩

/-- Let `X` be a scheme over `ℂ`, `Z ⊆ X(ℂ)`, and `j : X(ℂ) \ Z → X(ℂ)` the inclusion. This
integer-indexed complex represents `Rj_*ℚ`: it is `j_*I^q` for `q ≥ 0`, using an injective
resolution `ℚ → I^•` on the complement, and zero for `q < 0`. -/
def derivedPushforwardComplementConstantRationalComplexInt
    (Z : Set (ComplexPoint X)) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  (derivedPushforwardComplementConstantRationalComplexNat X Z).extend
    ComplexShape.embeddingUpNat

instance (Z : Set (ComplexPoint X)) :
    (derivedPushforwardComplementConstantRationalComplexInt X Z).IsStrictlyGE 0 := by
  unfold derivedPushforwardComplementConstantRationalComplexInt
  infer_instance

/-- Extending the zero derived pushforward from the empty complement to integer degrees remains a
zero complex. -/
lemma isZero_derivedPushforwardComplement_univ_int :
    IsZero (derivedPushforwardComplementConstantRationalComplexInt X
      (Set.univ : Set (ComplexPoint X))) :=
  (ComplexShape.embeddingUpNat.extendFunctor
    (AnalyticAdditiveSheaf X)).map_isZero
      (isZero_derivedPushforwardComplement_univ X)

/-- Let `X` be a scheme over `ℂ`, `Z ⊆ X(ℂ)`, and `j : X(ℂ) \ Z → X(ℂ)` the inclusion. For the
chosen injective resolution `ℚ → I^•` on the complement, this is its direct image `j_*ℚ[0] →
j_*I^•`, as a map of complexes indexed by nonnegative integers. -/
def pushforwardComplementResolutionMap
    (Z : Set (ComplexPoint X)) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticComplementInclusion X Z)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
      ((CochainComplex.single₀
        (AnalyticComplementAdditiveSheaf X Z)).obj
          𝓒(↧↥Zᶜ; ℚ)) ⟶
    derivedPushforwardComplementConstantRationalComplexNat X Z :=
  ((TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticComplementInclusion X Z)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
    (complementConstantRationalInjectiveResolution X Z).ι

/-- Let `X` be a scheme over `ℂ`, `Z ⊆ X(ℂ)`, and `j : X(ℂ) \ Z → X(ℂ)` the inclusion. This map of
complexes `ℚ[0] → j_*I^•` restricts locally constant functions to the complement and then
applies the augmentation of its chosen injective resolution `ℚ → I^•`. Degrees are nonnegative
integers. -/
def rationalRestrictionComplexNat
    (Z : Set (ComplexPoint X)) :
    (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).obj
        𝓒(↧(ComplexPoint X); ℚ) ⟶
      derivedPushforwardComplementConstantRationalComplexNat X Z :=
  (CochainComplex.single₀ (AnalyticAdditiveSheaf X)).map
      (rationalRestrictionSheaf X Z) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticComplementInclusion X Z)) (ComplexShape.up ℕ) 0).inv.app
          𝓒(↧↥Zᶜ; ℚ) ≫
    pushforwardComplementResolutionMap X Z

/-- Let `X` be a scheme over `ℂ` and `Z ⊆ X(ℂ)`. This is the integer-indexed map `ℚ[0] → j_*I^•`
representing restriction to `X(ℂ) \ Z`, where `j` is the inclusion and `ℚ → I^•` is an injective
resolution on the complement. Both complexes are zero in negative degrees. -/
def rationalRestrictionComplexInt (Z : Set (ComplexPoint X)) :
    constantFieldSheafComplexInt ℚ X ⟶
      derivedPushforwardComplementConstantRationalComplexInt X Z :=
  HomologicalComplex.extendMap (rationalRestrictionComplexNat X Z)
    ComplexShape.embeddingUpNat

/-- For support equal to the whole space, the third morphism of the restriction mapping-cone
triangle is an isomorphism in the homotopy category. This is the precise categorical form of the
fact that cohomology supported on the whole space is ordinary cohomology. -/
noncomputable instance isIso_mappingConeTriangleh_mor₃_univ :
    IsIso ((CochainComplex.mappingCone.triangleh
      (rationalRestrictionComplexInt X
        (Set.univ : Set (ComplexPoint X)))).mor₃) := by
  let f := rationalRestrictionComplexInt X
    (Set.univ : Set (ComplexPoint X))
  have hdist : CochainComplex.mappingCone.triangleh f ∈
      HomotopyCategory.Pretriangulated.distinguishedTriangles
        (AnalyticAdditiveSheaf X) :=
    ⟨_, _, f, ⟨Iso.refl _⟩⟩
  exact (Pretriangulated.Triangle.isZero₂_iff_isIso₃ _ hdist).1
    ((HomotopyCategory.quotient (AnalyticAdditiveSheaf X) ℤᵘᵖ).map_isZero
      (isZero_derivedPushforwardComplement_univ_int X))

/-- The same whole-support connecting morphism is an isomorphism in the derived category used by
hypercohomology. -/
noncomputable instance isIso_derivedMappingConeTriangle_mor₃_univ :
    IsIso ((DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCone.triangle
        (rationalRestrictionComplexInt X
          (Set.univ : Set (ComplexPoint X))))).mor₃) := by
  let f := rationalRestrictionComplexInt X
    (Set.univ : Set (ComplexPoint X))
  exact (Pretriangulated.Triangle.isZero₂_iff_isIso₃ _
    (DerivedCategory.mappingCone_triangle_distinguished f)).1
    (DerivedCategory.Q.map_isZero (isZero_derivedPushforwardComplement_univ_int X))

/-- Let `X` be a scheme over `ℂ`, let `Z ⊆ X(ℂ)`, and write `j : X(ℂ) \ Z → X(ℂ)` for the inclusion.
This is the mapping cone of the restriction `ℚ[0] → j_*I^•`, where `ℚ → I^•` is an injective
resolution on the complement. For closed `Z`, the cone shifted by `-1` represents the sheaf
complex of derived sections with support in `Z`. -/
abbrev rationalCohomologyWithSupportComplex
    (Z : Set (ComplexPoint X)) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  CochainComplex.mappingCone (rationalRestrictionComplexInt X Z)

/-- Let `X` be a scheme over `ℂ`, `Z ⊆ Y = X(ℂ)` any subset, and `j : Y \ Z → Y` the inclusion. This
defines `H_Z^n(Y;ℚ)` as `ℍ^{n-1}(Y,Cone(ℚ_Y → Rj_*ℚ_{Y \ Z}))`, using constant rational sheaves.
For closed `Z`, it can also be computed from global sections vanishing off `Z` in an injective
resolution of `ℚ_Y`. -/
abbrev RationalCohomologyWithSupport
    (Z : Set (ComplexPoint X)) (n : ℤ) : Type 1 :=
  Hypercohomology X (rationalCohomologyWithSupportComplex X Z) (n - 1)


/-- Let `X` be a scheme over `ℂ` and `Z ⊆ X(ℂ)`. For the cone of rational restriction `ℚ → Rj_*ℚ`,
with `j` the complement inclusion, this is the connecting morphism `Cone(ℚ → Rj_*ℚ) → ℚ[1]` in
the derived category. Its action on hypercohomology defines the map that forgets support. -/
def forgetSupportShiftedHom (Z : Set (ComplexPoint X)) :
    Localization.SmallShiftedHom (analyticQuasiIsomorphisms X)
      (rationalCohomologyWithSupportComplex X Z)
      (constantFieldSheafComplexInt ℚ X) (1 : ℤ) :=
  Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
    (CochainComplex.mappingCone.triangle
      (rationalRestrictionComplexInt X Z)).mor₃

/-- Forget support, using the connecting morphism of the mapping-cone triangle, in the
hypercohomology presentation of rational cohomology. -/
def forgetSupportHypercohomology (Z : Set (ComplexPoint X)) (n : ℤ) :
    RationalCohomologyWithSupport X Z n →+
      Hypercohomology X (constantFieldSheafComplexInt ℚ X) n where
  toFun α := α.comp (forgetSupportShiftedHom X Z) (by lia)
  map_zero' := by
    apply (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    simp only [Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_zero, ShiftedHom.zero_comp]
  map_add' α β := by
    apply (Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    simp only [Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_add, ShiftedHom.add_comp]

/-- Forget support: the map `H^n_Z(X(ℂ); ℚ) → H^n(X(ℂ); ℚ)`. -/
def coneForgetSupport (Z : Set (ComplexPoint X)) (n : ℕ) :
    RationalCohomologyWithSupport X Z n →+ H^n(X; ℚ) :=
  (hypercohomologyAddEquivConstantCohomology ℚ X n).toAddMonoidHom.comp
    (forgetSupportHypercohomology X Z n)

section

/-- After passage to the derived category, the morphism which forgets whole-space support is an
isomorphism. -/
instance isIso_forgetSupportShiftedHom_univ_map :
    IsIso ((Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q)
        (forgetSupportShiftedHom X
          (Set.univ : Set (ComplexPoint X)))) := by
  unfold forgetSupportShiftedHom
  erw [Localization.SmallShiftedHom.equiv_mk]
  exact isIso_derivedMappingConeTriangle_mor₃_univ X

end

/-- For support equal to the whole space, forgetting support is a canonical equivalence with
ordinary rational cohomology in its hypercohomology presentation. Its forward map is
definitionally the support-forgetting map. -/
noncomputable def forgetSupportHypercohomologyEquivUniv (n : ℤ) :
    RationalCohomologyWithSupport X
        (Set.univ : Set (ComplexPoint X)) n ≃
      Hypercohomology X (constantFieldSheafComplexInt ℚ X) n :=
  let eSource : RationalCohomologyWithSupport X
        (Set.univ : Set (ComplexPoint X)) n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (rationalCohomologyWithSupportComplex X Set.univ))
        (n - 1) :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  let eTarget : Hypercohomology X (constantFieldSheafComplexInt ℚ X) n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (constantFieldSheafComplexInt ℚ X)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms X) DerivedCategory.Q
  let g := (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms X) DerivedCategory.Q)
      (forgetSupportShiftedHom X
        (Set.univ : Set (ComplexPoint X)))
  let eComp : ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (rationalCohomologyWithSupportComplex X Set.univ))
        (n - 1) ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X))
        (DerivedCategory.Q.obj (constantFieldSheafComplexInt ℚ X)) n :=
    ShiftedHom.postcompEquivOfIsIso
      (X := DerivedCategory.Q.obj (constantIntegerSheafComplexInt X)) g
      (show (1 : ℤ) + (n - 1) = n by lia)
  have hcomp (α : RationalCohomologyWithSupport X
      (Set.univ : Set (ComplexPoint X)) n) :
      eTarget (forgetSupportHypercohomology X Set.univ n α) = eComp (eSource α) := by
    change eTarget
      (α.comp (forgetSupportShiftedHom X Set.univ) (by lia)) = _
    rw [Localization.SmallShiftedHom.equiv_comp]
    exact (ShiftedHom.postcompEquivOfIsIso_apply g
      (show (1 : ℤ) + (n - 1) = n by lia) (eSource α)).symm
  { toFun := forgetSupportHypercohomology X Set.univ n
    invFun := fun α => eSource.symm (eComp.symm (eTarget α))
    left_inv := fun α ↦ eSource.injective (by
      rw [eSource.apply_symm_apply, hcomp, eComp.symm_apply_apply])
    right_inv := fun α ↦ eTarget.injective (by
      rw [hcomp, eSource.apply_symm_apply, eComp.apply_symm_apply]) }

end AlgebraicGeometry.ComplexPoint

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

attribute [local instance] analyticSupportHasDerivedCategory

@[simp] lemma forgetSupportHypercohomologyEquivUniv_apply (n : ℤ)
    (α : RationalCohomologyWithSupport X
      (Set.univ : Set (ComplexPoint X)) n) :
    forgetSupportHypercohomologyEquivUniv X n α =
      forgetSupportHypercohomology X Set.univ n α := rfl

/-- For support equal to the whole space, forgetting support is a canonical equivalence with
ordinary rational cohomology. -/
noncomputable def forgetSupportEquivUniv (n : ℕ) :
    RationalCohomologyWithSupport X (Set.univ : Set (ComplexPoint X)) n ≃ H^n(X; ℚ) :=
  (forgetSupportHypercohomologyEquivUniv X n).trans
    (hypercohomologyAddEquivConstantCohomology ℚ X n).toEquiv

@[simp] lemma forgetSupportEquivUniv_apply (n : ℕ)
    (α : RationalCohomologyWithSupport X (Set.univ : Set (ComplexPoint X)) n) :
    forgetSupportEquivUniv X n α = coneForgetSupport X Set.univ n α := rfl

end AlgebraicGeometry.ComplexPoint
