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

public import HodgeConjecture.Definitions.AlgebraicGeometry.HodgeFiltration
public import HodgeConjecture.Lemmas.Algebra.Homology.ShiftedExact
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Topology.Sheaves.Functors

/-!
# Rational cohomology with support

For a subset `Z` of the analytic complex-point space, this file resolves the rational constant
sheaf on the complement injectively and pushes the resolution to the ambient space. This computes
the derived pushforward from the complement. The homotopy fiber of the canonical restriction to
that derived pushforward is represented by the mapping cone shifted by `-1`. Its hypercohomology
is rational constant-sheaf cohomology with support in `Z`.

The connecting morphism of the mapping-cone triangle gives the canonical map that forgets
support. Thus supported and ordinary rational cohomology use exactly the same derived
constant-sheaf model as the Hodge filtration.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (structureMap : X ⟶ Spec (.of ℂ))

local instance cohomologyWithSupportTopology :
    TopologicalSpace (ComplexPoint X structureMap) := analyticTopology

local instance analyticSupportHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf structureMap) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf structureMap)

/-- The analytic complement of a subset of the complex-point space. -/
abbrev AnalyticComplement (Z : Set (ComplexPoint X structureMap)) :=
  Zᶜ

/-- The inclusion of the analytic complement into the complex-point space. -/
def analyticComplementInclusion (Z : Set (ComplexPoint X structureMap)) :
    TopCat.of (AnalyticComplement structureMap Z) ⟶
      TopCat.of (ComplexPoint X structureMap) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Sheaves of additive groups on the analytic complement. -/
abbrev AnalyticComplementAdditiveSheaf (Z : Set (ComplexPoint X structureMap)) :=
  TopCat.Sheaf AddCommGrpCat (TopCat.of (AnalyticComplement structureMap Z))

/-- The rational constant sheaf on the analytic complement. -/
def complementConstantRationalSheaf (Z : Set (ComplexPoint X structureMap)) :
    AnalyticComplementAdditiveSheaf structureMap Z :=
  let J := Opens.grothendieckTopology
    (TopCat.of (AnalyticComplement structureMap Z))
  (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of ℚ)

/-- The rational constant sheaf on the complement, pushed forward to the ambient space. -/
def pushforwardComplementConstantRationalSheaf
    (Z : Set (ComplexPoint X structureMap)) : AnalyticAdditiveSheaf structureMap :=
  (TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticComplementInclusion structureMap Z)).obj
      (complementConstantRationalSheaf structureMap Z)

/-- Constant rational sections restrict canonically to locally constant sections on the
complement. This is the presheaf morphism before sheafifying the source. -/
def rationalRestrictionPresheaf (Z : Set (ComplexPoint X structureMap)) :
    (Functor.const (Opens (TopCat.of (ComplexPoint X structureMap)))ᵒᵖ).obj
        (AddCommGrpCat.of ℚ) ⟶
      (pushforwardComplementConstantRationalSheaf structureMap Z).obj :=
  let U := TopCat.of (AnalyticComplement structureMap Z)
  let J := Opens.grothendieckTopology U
  Functor.whiskerLeft (Opens.map (analyticComplementInclusion structureMap Z)).op
    ((sheafificationAdjunction J AddCommGrpCat).unit.app
      ((Functor.const (Opens U)ᵒᵖ).obj (AddCommGrpCat.of ℚ)))

/-- The canonical restriction of the rational constant sheaf to the complement. -/
def rationalRestrictionSheaf (Z : Set (ComplexPoint X structureMap)) :
    constantRationalSheaf structureMap ⟶
      pushforwardComplementConstantRationalSheaf structureMap Z :=
  let J := Opens.grothendieckTopology
    (TopCat.of (ComplexPoint X structureMap))
  ⟨sheafifyLift J (rationalRestrictionPresheaf structureMap Z)
    (pushforwardComplementConstantRationalSheaf structureMap Z).property⟩

/-- A fixed injective resolution used to compute the derived pushforward from the complement. -/
def complementConstantRationalInjectiveResolution
    (Z : Set (ComplexPoint X structureMap)) :
    InjectiveResolution (complementConstantRationalSheaf structureMap Z) :=
  injectiveResolution (complementConstantRationalSheaf structureMap Z)

/-- A complex representing the derived pushforward of the rational constant sheaf on the
complement. -/
def derivedPushforwardComplementConstantRationalComplexNat
    (Z : Set (ComplexPoint X structureMap)) :
    CochainComplex (AnalyticAdditiveSheaf structureMap) ℕ :=
  ((TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticComplementInclusion structureMap Z)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
    (complementConstantRationalInjectiveResolution structureMap Z).cocomplex

/-- Every additive sheaf on the empty analytic complement is a zero object. -/
lemma isZero_sheaf_on_complement_univ
    (F : TopCat.Sheaf AddCommGrpCat.{0}
      (TopCat.of (AnalyticComplement structureMap
        (Set.univ : Set (ComplexPoint X structureMap))))) :
    IsZero F := by
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero
    (C := AddCommGrpCat.{0})
    (X := TopCat.of (AnalyticComplement structureMap
      (Set.univ : Set (ComplexPoint X structureMap)))) F).2
  intro x
  have hx : False := by
    simpa [AnalyticComplement] using x.property
  exact hx.elim

/-- Every term of the derived pushforward from the empty complement is zero. -/
lemma isZero_derivedPushforwardComplement_univ_X (n : ℕ) :
    IsZero ((derivedPushforwardComplementConstantRationalComplexNat structureMap
      (Set.univ : Set (ComplexPoint X structureMap))).X n) := by
  change IsZero ((TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticComplementInclusion structureMap
      (Set.univ : Set (ComplexPoint X structureMap)))).obj
        ((complementConstantRationalInjectiveResolution structureMap
          (Set.univ : Set (ComplexPoint X structureMap))).cocomplex.X n))
  exact (TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticComplementInclusion structureMap
      (Set.univ : Set (ComplexPoint X structureMap)))).map_isZero
        (isZero_sheaf_on_complement_univ structureMap _)

/-- The complex representing derived pushforward from the empty complement is itself a zero
object, not merely acyclic. -/
lemma isZero_derivedPushforwardComplement_univ :
    IsZero (derivedPushforwardComplementConstantRationalComplexNat structureMap
      (Set.univ : Set (ComplexPoint X structureMap))) := by
  constructor
  · intro K
    refine ⟨⟨⟨0⟩, fun f => ?_⟩⟩
    apply HomologicalComplex.hom_ext
    intro n
    exact (isZero_derivedPushforwardComplement_univ_X structureMap n).eq_zero_of_src _
  · intro K
    refine ⟨⟨⟨0⟩, fun f => ?_⟩⟩
    apply HomologicalComplex.hom_ext
    intro n
    exact (isZero_derivedPushforwardComplement_univ_X structureMap n).eq_zero_of_tgt _

/-- The derived pushforward complex, extended by zero to integer degrees. -/
def derivedPushforwardComplementConstantRationalComplexInt
    (Z : Set (ComplexPoint X structureMap)) :
    CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ :=
  (derivedPushforwardComplementConstantRationalComplexNat structureMap Z).extend
    ComplexShape.embeddingUpNat

/-- Extending the zero derived pushforward from the empty complement to integer degrees remains a
zero complex. -/
lemma isZero_derivedPushforwardComplement_univ_int :
    IsZero (derivedPushforwardComplementConstantRationalComplexInt structureMap
      (Set.univ : Set (ComplexPoint X structureMap))) := by
  change IsZero ((ComplexShape.embeddingUpNat.extendFunctor
    (AnalyticAdditiveSheaf structureMap)).obj
      (derivedPushforwardComplementConstantRationalComplexNat structureMap
        (Set.univ : Set (ComplexPoint X structureMap))))
  exact (ComplexShape.embeddingUpNat.extendFunctor
    (AnalyticAdditiveSheaf structureMap)).map_isZero
      (isZero_derivedPushforwardComplement_univ structureMap)

/-- The pushed-forward resolution map from the underived constant sheaf on the complement. -/
def pushforwardComplementResolutionMap
    (Z : Set (ComplexPoint X structureMap)) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat
      (analyticComplementInclusion structureMap Z)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
      ((CochainComplex.single₀
        (AnalyticComplementAdditiveSheaf structureMap Z)).obj
          (complementConstantRationalSheaf structureMap Z)) ⟶
    derivedPushforwardComplementConstantRationalComplexNat structureMap Z :=
  ((TopCat.Sheaf.pushforward AddCommGrpCat
    (analyticComplementInclusion structureMap Z)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
    (complementConstantRationalInjectiveResolution structureMap Z).ι

/-- Restriction from ambient rational constants to a complex representing the derived
pushforward from the complement. -/
def rationalRestrictionComplexNat
    (Z : Set (ComplexPoint X structureMap)) :
    (CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).obj
        (constantRationalSheaf structureMap) ⟶
      derivedPushforwardComplementConstantRationalComplexNat structureMap Z :=
  (CochainComplex.single₀ (AnalyticAdditiveSheaf structureMap)).map
      (rationalRestrictionSheaf structureMap Z) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticComplementInclusion structureMap Z)) (ComplexShape.up ℕ) 0).inv.app
          (complementConstantRationalSheaf structureMap Z) ≫
    pushforwardComplementResolutionMap structureMap Z

/-- Restriction from the ambient rational constant complex to the derived pushforward from the
complement. -/
def rationalRestrictionComplexInt (Z : Set (ComplexPoint X structureMap)) :
    constantRationalSheafComplexInt structureMap ⟶
      derivedPushforwardComplementConstantRationalComplexInt structureMap Z :=
  HomologicalComplex.extendMap (rationalRestrictionComplexNat structureMap Z)
    ComplexShape.embeddingUpNat

/-- For support equal to the whole space, the third morphism of the restriction mapping-cone
triangle is an isomorphism in the homotopy category. This is the precise categorical form of the
fact that cohomology supported on the whole space is ordinary cohomology. -/
noncomputable instance isIso_mappingConeTriangleh_mor₃_univ :
    IsIso ((CochainComplex.mappingCone.triangleh
      (rationalRestrictionComplexInt structureMap
        (Set.univ : Set (ComplexPoint X structureMap)))).mor₃) := by
  let f := rationalRestrictionComplexInt structureMap
    (Set.univ : Set (ComplexPoint X structureMap))
  have hdist : CochainComplex.mappingCone.triangleh f ∈
      HomotopyCategory.Pretriangulated.distinguishedTriangles
        (AnalyticAdditiveSheaf structureMap) :=
    ⟨_, _, f, ⟨Iso.refl _⟩⟩
  apply (Pretriangulated.Triangle.isZero₂_iff_isIso₃ _ hdist).1
  exact (HomotopyCategory.quotient
    (AnalyticAdditiveSheaf structureMap) (ComplexShape.up ℤ)).map_isZero
      (isZero_derivedPushforwardComplement_univ_int structureMap)

/-- The same whole-support connecting morphism is an isomorphism in the derived category used by
hypercohomology. -/
noncomputable instance isIso_derivedMappingConeTriangle_mor₃_univ :
    IsIso ((DerivedCategory.Q.mapTriangle.obj
      (CochainComplex.mappingCone.triangle
        (rationalRestrictionComplexInt structureMap
          (Set.univ : Set (ComplexPoint X structureMap))))).mor₃) := by
  let f := rationalRestrictionComplexInt structureMap
    (Set.univ : Set (ComplexPoint X structureMap))
  apply (Pretriangulated.Triangle.isZero₂_iff_isIso₃ _
    (DerivedCategory.mappingCone_triangle_distinguished f)).1
  exact DerivedCategory.Q.map_isZero
    (isZero_derivedPushforwardComplement_univ_int structureMap)

/-- The mapping-cone model for the homotopy fiber defining rational cohomology with support. -/
abbrev rationalCohomologyWithSupportComplex
    (Z : Set (ComplexPoint X structureMap)) :
    CochainComplex (AnalyticAdditiveSheaf structureMap) ℤ :=
  CochainComplex.mappingCone (rationalRestrictionComplexInt structureMap Z)

/-- Rational constant-sheaf cohomology with support in `Z`. The degree shift realizes the
homotopy fiber of restriction as the mapping cone shifted by `-1`. -/
abbrev RationalCohomologyWithSupport
    (Z : Set (ComplexPoint X structureMap)) (n : ℤ) : Type 1 :=
  Hypercohomology structureMap (rationalCohomologyWithSupportComplex structureMap Z) (n - 1)

/-- The degree-one connecting morphism from the mapping cone to the ambient rational constant
complex. -/
def forgetSupportShiftedHom (Z : Set (ComplexPoint X structureMap)) :
    Localization.SmallShiftedHom (analyticQuasiIsomorphisms structureMap)
      (rationalCohomologyWithSupportComplex structureMap Z)
      (constantRationalSheafComplexInt structureMap) (1 : ℤ) :=
  Localization.SmallShiftedHom.mk (analyticQuasiIsomorphisms structureMap)
    (CochainComplex.mappingCone.triangle
      (rationalRestrictionComplexInt structureMap Z)).mor₃

/-- Forget support, using the connecting morphism of the mapping-cone triangle. -/
def forgetSupport (Z : Set (ComplexPoint X structureMap)) (n : ℤ) :
    RationalCohomologyWithSupport structureMap Z n →+
      RationalCohomology structureMap n where
  toFun α := α.comp (forgetSupportShiftedHom structureMap Z) (by omega)
  map_zero' := by
    let e : RationalCohomology structureMap n ≃
        ShiftedHom
          (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
          (DerivedCategory.Q.obj (constantRationalSheafComplexInt structureMap)) n :=
      Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
    apply e.injective
    rw [Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_zero structureMap
        (rationalCohomologyWithSupportComplex structureMap Z) (n - 1),
      hypercohomologyEquiv_zero structureMap
        (constantRationalSheafComplexInt structureMap) n]
    simp
  map_add' α β := by
    let eSource : RationalCohomologyWithSupport structureMap Z n ≃
        ShiftedHom
          (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
          (DerivedCategory.Q.obj
            (rationalCohomologyWithSupportComplex structureMap Z)) (n - 1) :=
      Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
    let eTarget : RationalCohomology structureMap n ≃
        ShiftedHom
          (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
          (DerivedCategory.Q.obj (constantRationalSheafComplexInt structureMap)) n :=
      Localization.SmallShiftedHom.equiv
        (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
    apply eTarget.injective
    rw [Localization.SmallShiftedHom.equiv_comp,
      hypercohomologyEquiv_add structureMap
        (rationalCohomologyWithSupportComplex structureMap Z) (n - 1),
      hypercohomologyEquiv_add structureMap
        (constantRationalSheafComplexInt structureMap) n,
      Localization.SmallShiftedHom.equiv_comp,
      Localization.SmallShiftedHom.equiv_comp]
    simp

section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- After passage to the derived category, the morphism which forgets whole-space support is an
isomorphism. -/
instance isIso_forgetSupportShiftedHom_univ_map :
    IsIso ((Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q)
        (forgetSupportShiftedHom structureMap
          (Set.univ : Set (ComplexPoint X structureMap)))) := by
  unfold forgetSupportShiftedHom
  erw [Localization.SmallShiftedHom.equiv_mk]
  exact isIso_derivedMappingConeTriangle_mor₃_univ structureMap

end

/-- For support equal to the whole space, forgetting support is a canonical equivalence with
ordinary rational cohomology. Its forward map is definitionally the support-forgetting map. -/
noncomputable def forgetSupportEquivUniv (n : ℤ) :
    RationalCohomologyWithSupport structureMap
        (Set.univ : Set (ComplexPoint X structureMap)) n ≃
      RationalCohomology structureMap n := by
  let eSource : RationalCohomologyWithSupport structureMap
        (Set.univ : Set (ComplexPoint X structureMap)) n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (rationalCohomologyWithSupportComplex structureMap Set.univ))
        (n - 1) :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  let eTarget : RationalCohomology structureMap n ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (constantRationalSheafComplexInt structureMap)) n :=
    Localization.SmallShiftedHom.equiv
      (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q
  let g := (Localization.SmallShiftedHom.equiv
    (analyticQuasiIsomorphisms structureMap) DerivedCategory.Q)
      (forgetSupportShiftedHom structureMap
        (Set.univ : Set (ComplexPoint X structureMap)))
  let eComp : ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (rationalCohomologyWithSupportComplex structureMap Set.univ))
        (n - 1) ≃
      ShiftedHom
        (DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap))
        (DerivedCategory.Q.obj (constantRationalSheafComplexInt structureMap)) n :=
    ShiftedHom.postcompEquivOfIsIso
      (X := DerivedCategory.Q.obj (constantIntegerSheafComplexInt structureMap)) g
      (show (1 : ℤ) + (n - 1) = n by omega)
  have hcomp (α : RationalCohomologyWithSupport structureMap
      (Set.univ : Set (ComplexPoint X structureMap)) n) :
      eTarget (forgetSupport structureMap Set.univ n α) = eComp (eSource α) := by
    change eTarget
      (α.comp (forgetSupportShiftedHom structureMap Set.univ) (by omega)) = _
    rw [Localization.SmallShiftedHom.equiv_comp]
    exact (ShiftedHom.postcompEquivOfIsIso_apply g
      (show (1 : ℤ) + (n - 1) = n by omega) (eSource α)).symm
  refine
    { toFun := forgetSupport structureMap Set.univ n
      invFun := fun α => eSource.symm (eComp.symm (eTarget α))
      left_inv := ?_
      right_inv := ?_ }
  · intro α
    apply eSource.injective
    rw [eSource.apply_symm_apply, hcomp, eComp.symm_apply_apply]
  · intro α
    apply eTarget.injective
    rw [hcomp, eSource.apply_symm_apply, eComp.apply_symm_apply]

@[simp] lemma forgetSupportEquivUniv_apply (n : ℤ)
    (α : RationalCohomologyWithSupport structureMap
      (Set.univ : Set (ComplexPoint X structureMap)) n) :
    forgetSupportEquivUniv structureMap n α =
      forgetSupport structureMap Set.univ n α := by
  rfl

/-- Forgetting whole-space support is surjective. -/
lemma forgetSupport_surjective_univ (n : ℤ) :
    Function.Surjective
      (forgetSupport structureMap (Set.univ : Set (ComplexPoint X structureMap)) n) := by
  intro α
  obtain ⟨β, hβ⟩ := (forgetSupportEquivUniv structureMap n).surjective α
  exact ⟨β, (forgetSupportEquivUniv_apply structureMap n β).symm.trans hβ⟩

end AlgebraicGeometry.ComplexPoint
