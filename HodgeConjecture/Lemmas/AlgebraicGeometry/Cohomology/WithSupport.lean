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

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Hodge.Filtration
public import HodgeConjecture.Mathlib.Topology.Category.TopCat.Basic
public import HodgeConjecture.Lemmas.Algebra.Homology.ShiftedExact
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

local instance analyticSupportAddCommGrpHasDerivedCategory :
    HasDerivedCategory AddCommGrpCat := HasDerivedCategory.standard _

/-- The inclusion of the complement of a subset into the complex-point space. -/
def analyticComplementInclusion (Z : Set (ComplexPoint X)) :
    TopCat.of ↥Zᶜ ⟶
      TopCat.of (ComplexPoint X) :=
  TopCat.subtypeInclusion (TopCat.of (ComplexPoint X)) Zᶜ

/-- Sheaves of additive groups on the complement of a subset. -/
abbrev AnalyticComplementAdditiveSheaf (Z : Set (ComplexPoint X)) :=
  TopCat.Sheaf AddCommGrpCat (TopCat.of ↥Zᶜ)

/-- The rational constant sheaf on the complement, pushed forward to the ambient space. -/
def pushforwardComplementConstantRationalSheaf
    (Z : Set (ComplexPoint X)) : AnalyticAdditiveSheaf X :=
  (TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticComplementInclusion X Z)).obj
      𝓒(↧↥Zᶜ; ℚ)

/-- Constant rational sections restrict canonically to locally constant sections on the
complement. This is the presheaf morphism before sheafifying the source. -/
def rationalRestrictionPresheaf (Z : Set (ComplexPoint X)) :
    (Functor.const (Opens (TopCat.of (ComplexPoint X)))ᵒᵖ).obj
        (AddCommGrpCat.of ℚ) ⟶
      (pushforwardComplementConstantRationalSheaf X Z).obj :=
  let U := TopCat.of ↥Zᶜ
  let J := Opens.grothendieckTopology U
  Functor.whiskerLeft (Opens.map (analyticComplementInclusion X Z)).op
    ((sheafificationAdjunction J AddCommGrpCat).unit.app
      ((Functor.const (Opens U)ᵒᵖ).obj (AddCommGrpCat.of ℚ)))

/-- The canonical restriction of the rational constant sheaf to the complement. -/
def rationalRestrictionSheaf (Z : Set (ComplexPoint X)) :
    𝓒(↧(ComplexPoint X); ℚ) ⟶
      pushforwardComplementConstantRationalSheaf X Z :=
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X))
  ⟨sheafifyLift J (rationalRestrictionPresheaf X Z)
    (pushforwardComplementConstantRationalSheaf X Z).property⟩

/-- A fixed injective resolution used to compute the derived pushforward from the complement. -/
def complementConstantRationalInjectiveResolution
    (Z : Set (ComplexPoint X)) :
    InjectiveResolution 𝓒(↧↥Zᶜ; ℚ) :=
  injectiveResolution 𝓒(↧↥Zᶜ; ℚ)

/-- A complex representing the derived pushforward of the rational constant sheaf on the
complement. -/
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

/-- The complex representing derived pushforward from the empty complement is itself a zero
object, not merely acyclic. -/
private lemma isZero_derivedPushforwardComplement_univ :
    IsZero (derivedPushforwardComplementConstantRationalComplexNat X
      (Set.univ : Set (ComplexPoint X))) := by
  constructor
  · exact fun K ↦ ⟨⟨⟨0⟩, fun f ↦ HomologicalComplex.hom_ext _ _ fun n ↦
      (isZero_derivedPushforwardComplement_univ_X X n).eq_zero_of_src _⟩⟩
  · exact fun K ↦ ⟨⟨⟨0⟩, fun f ↦ HomologicalComplex.hom_ext _ _ fun n ↦
      (isZero_derivedPushforwardComplement_univ_X X n).eq_zero_of_tgt _⟩⟩

/-- The derived pushforward complex, extended by zero to integer degrees. -/
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

/-- The pushed-forward resolution map from the underived constant sheaf on the complement. -/
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

/-- Restriction from ambient rational constants to a complex representing the derived
pushforward from the complement. -/
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

/-- Restriction from the ambient rational constant complex to the derived pushforward from the
complement. -/
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
    ((HomotopyCategory.quotient (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ)).map_isZero
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

/-- The mapping-cone model for the homotopy fiber defining rational cohomology with support. -/
abbrev rationalCohomologyWithSupportComplex
    (Z : Set (ComplexPoint X)) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  CochainComplex.mappingCone (rationalRestrictionComplexInt X Z)

/-- Rational constant-sheaf cohomology with support in `Z`. The degree shift realizes the
homotopy fiber of restriction as the mapping cone shifted by `-1`. -/
abbrev rationalCohomologyWithSupportComplexPlus
    (Z : Set (ComplexPoint X)) : CochainComplex.Plus (AnalyticAdditiveSheaf X) :=
  ⟨(shiftFunctor _ (-1 : ℤ)).obj (rationalCohomologyWithSupportComplex X Z),
    ⟨0, by
      let _ : (rationalCohomologyWithSupportComplex X Z).IsStrictlyGE (-1) :=
        CochainComplex.isStrictlyGE_mappingCone _ 0 0 (-1)
      exact CochainComplex.isStrictlyGE_shift _ (-1) (-1) 0 (by norm_num)⟩⟩

/-- Rational constant-sheaf cohomology with support in `Z`. -/
abbrev RationalCohomologyWithSupport
    (Z : Set (ComplexPoint X)) (n : ℤ) :=
  ↥((analyticHypercohomologyFunctor X n).obj
    (rationalCohomologyWithSupportComplexPlus X Z))

/-- The shifted mapping-cone morphism which forgets support. -/
def forgetSupportComplex (Z : Set (ComplexPoint X)) :
    (rationalCohomologyWithSupportComplexPlus X Z).obj ⟶
      constantFieldSheafComplexInt ℚ X :=
  ((CochainComplex.mappingCone.triangle
      (rationalRestrictionComplexInt X Z)).mor₃)⟦(-1 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by simp)).hom.app _

/-- Forget support, using the connecting morphism of the mapping-cone triangle. -/
def forgetSupport (Z : Set (ComplexPoint X)) (n : ℤ) :
    RationalCohomologyWithSupport X Z n →+
      H^n(X; ℚ) :=
  ((analyticHypercohomologyFunctor X n).map
    (⟨forgetSupportComplex X Z⟩ : rationalCohomologyWithSupportComplexPlus X Z ⟶
      constantFieldSheafComplexIntPlus ℚ X)).hom

section

/-- After passage to the derived category, the morphism which forgets whole-space support is an
isomorphism. -/
instance forgetSupportComplex_univ_quasiIso :
    QuasiIso (forgetSupportComplex X (Set.univ : Set (ComplexPoint X))) := by
  let t := CochainComplex.mappingCone.triangle
      (rationalRestrictionComplexInt X (Set.univ : Set (ComplexPoint X)))
  have ht : QuasiIso t.mor₃ :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (C := AnalyticAdditiveSheaf X) t.mor₃).1 (by
      let c := (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app t.obj₁
      let _ : IsIso (DerivedCategory.Q.map t.mor₃ ≫ c) := by
        change IsIso ((DerivedCategory.Q.mapTriangle.obj t).mor₃)
        infer_instance
      exact IsIso.of_isIso_comp_right (DerivedCategory.Q.map t.mor₃) c)
  have hs : QuasiIso (t.mor₃⟦(-1 : ℤ)⟧') :=
    (CochainComplex.quasiIso_shift_iff t.mor₃ (-1)).2 ht
  let c := (shiftFunctorCompIsoId (CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    (1 : ℤ) (-1) (by simp)).hom.app t.obj₁
  have hc : QuasiIso c := inferInstance
  dsimp only [forgetSupportComplex]
  let e := shiftFunctorCompIsoId (CochainComplex (AnalyticAdditiveSheaf X) ℤ)
    (1 : ℤ) (-1) (by simp)
  change QuasiIso (t.mor₃⟦(-1 : ℤ)⟧' ≫ e.hom.app t.obj₁)
  let _ : QuasiIso (t.mor₃⟦(-1 : ℤ)⟧') := hs
  let _ : QuasiIso (e.hom.app t.obj₁) := by infer_instance
  infer_instance

end

/-- For support equal to the whole space, forgetting support is a canonical equivalence with
ordinary rational cohomology. Its forward map is definitionally the support-forgetting map. -/
noncomputable def forgetSupportEquivUniv (n : ℤ) :
    RationalCohomologyWithSupport X
        (Set.univ : Set (ComplexPoint X)) n ≃
      H^n(X; ℚ) :=
  let f : rationalCohomologyWithSupportComplexPlus X Set.univ ⟶
      constantFieldSheafComplexIntPlus ℚ X :=
    ⟨forgetSupportComplex X Set.univ⟩
  letI : QuasiIso f.hom := forgetSupportComplex_univ_quasiIso X
  letI : IsIso (DerivedCategory.Plus.Q.map f) := inferInstance
  letI : IsIso ((analyticHypercohomologyFunctor X n).map f) :=
    by
      dsimp only [analyticHypercohomologyFunctor, Functor.comp_map]
      infer_instance
  (asIso ((analyticHypercohomologyFunctor X n).map f)).addCommGroupIsoToAddEquiv.toEquiv

end AlgebraicGeometry.ComplexPoint

end

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

open Point

variable (X : Over (Spec ↧ℂ))

attribute [local instance] analyticSupportHasDerivedCategory

@[simp] lemma forgetSupportEquivUniv_apply (n : ℤ)
    (α : RationalCohomologyWithSupport X
      (Set.univ : Set (ComplexPoint X)) n) :
    forgetSupportEquivUniv X n α =
      forgetSupport X Set.univ n α := rfl

end AlgebraicGeometry.ComplexPoint
