/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernClassRestrictionVanishing

/-!
# The canonical relative class of a unit-sheaf extension split on an open set

This is the first half of **Route A** of §4.3 step 4 of `docs/DIVISOR_HANDOFF.md`: the
construction of the *canonical* supported lift of the first Chern class out of the splitting
datum, rather than the bare existence supplied by exactness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace Opposite
open CategoryTheory.Localization

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance chernRelativeClassTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

local instance chernRelativeClassHasDerivedCategory :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- The single-complex functor on analytic sheaves. -/
abbrev analyticSingleFunctor :
    AnalyticAdditiveSheaf X ⥤ CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  CochainComplex.singleFunctor (AnalyticAdditiveSheaf X) 0

/-- The mapping cone of the canonical restriction morphism `𝒪ˣ ⟶ j_*(𝒪ˣ|_Ω)` of the unit sheaf
to an open set `Ω`. Its shift by `-1` is the *relative unit sheaf* of the pair `(X, Ω)`; a class in
`Hom_{D(X)}(ℤ_X, relativeUnitCone)` is an extension class together with a trivialisation over
`Ω`. -/
abbrev relativeUnitCone (Ω : Opens (TopCat.of (ComplexPoint X))) :
    CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  CochainComplex.mappingCone
    ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d)))

/-- The connecting morphism of the cone of the restriction morphism: it forgets the
trivialisation over `Ω`. -/
abbrev relativeUnitConeδ (Ω : Opens (TopCat.of (ComplexPoint X))) :
    ShiftedHom (relativeUnitCone X d Ω)
      ((analyticSingleFunctor X).obj (holomorphicUnitSheaf X d)) ((1 : ℕ) : ℤ) :=
  (CochainComplex.mappingCone.triangle
    ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d)))).mor₃

/-- The rational first Chern class of a unit class, as a *single* derived morphism out of the
unit sheaf: the connecting class of the exponential sequence followed by the rationalisation of
the constant integer complex. Composing an extension class with it gives the rational first Chern
class of the extension (`cohomologyClass_comp_rationalChernShiftedHom`). -/
def rationalChernShiftedHom :
    SmallShiftedHom.{1} (analyticQuasiIsomorphisms X)
      ((analyticSingleFunctor X).obj (holomorphicUnitSheaf X d))
      (constantFieldSheafComplexInt ℚ X) ((1 : ℕ) : ℤ) :=
  SmallShiftedHom.comp (holomorphicExponentialSequence_shortExact X d).extClass
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
      ((analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).inv ≫
        integerToFieldConstantSheafComplexInt ℚ X 1)) (zero_add ((1 : ℕ) : ℤ))

variable {X d}

/-! ### The comparison datum, and the relative first Chern class -/

/-- **The comparison datum of Route A.**

A derived morphism from the cone of the restriction morphism of the unit sheaf to the supported
rational complex, compatible with the connecting maps: composing it with `forgetSupport` is
composing the connecting morphism of the relative unit cone with the rational exponential Chern
class.

Such a datum exists by the axiom TR3 of triangulated categories applied to the commutative square
formed by the exponential class and the factorisation `ζ` of
`exists_comp_restrictionUnit_eq` (`hasRestrictedChernFactorization`); it is *data* rather than a
construction because TR3 produces the filler only existentially. Everything downstream of this
structure is canonical in the datum. -/
structure RelativeChernComparison (Y : Over (Spec ↧ℂ)) (e : ℕ)
    [SmoothOfRelativeDimension e Y.hom] (V : Opens (TopCat.of (ComplexPoint Y))) where
  /-- the comparison morphism -/
  hom : SmallShiftedHom.{1} (analyticQuasiIsomorphisms Y) (relativeUnitCone Y e V)
    (rationalCohomologyWithSupportComplex Y ((V : Set (ComplexPoint Y))ᶜ)) ((1 : ℕ) : ℤ)
  /-- it is a morphism of triangles in the third component -/
  comm : SmallShiftedHom.comp hom
      (forgetSupportShiftedHom Y ((V : Set (ComplexPoint Y))ᶜ))
      (show (1 : ℤ) + ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by lia) =
    SmallShiftedHom.comp
      (SmallShiftedHom.mk (analyticQuasiIsomorphisms Y) (relativeUnitConeδ Y e V))
      (rationalChernShiftedHom Y e)
      (show ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by lia)

namespace HolomorphicUnitExtension

variable (E : HolomorphicUnitExtension X d)

/-- The image of the defining short exact sequence under the single-complex functor. -/
abbrev singleShortComplex : ShortComplex (CochainComplex (AnalyticAdditiveSheaf X) ℤ) :=
  E.shortComplex.map (analyticSingleFunctor X)

lemma singleShortComplex_shortExact : E.singleShortComplex.ShortExact :=
  E.shortExact.map_of_exact (HomologicalComplex.single _ _ _)

/-- The mapping cone of the inclusion of the unit sheaf, as a complex. -/
abbrev inclusionCone : CochainComplex (AnalyticAdditiveSheaf X) ℤ :=
  CochainComplex.mappingCone E.singleShortComplex.f

/-- The canonical quasi-isomorphism from the mapping cone of the inclusion to the quotient. -/
abbrev coneToInteger :
    E.inclusionCone ⟶ (analyticSingleFunctor X).obj (constantIntegerSheaf X) :=
  CochainComplex.mappingCone.descShortComplex E.singleShortComplex

lemma quasiIso_coneToInteger : QuasiIso E.coneToInteger :=
  CochainComplex.mappingCone.quasiIso_descShortComplex E.singleShortComplex_shortExact

set_option backward.isDefEq.respectTransparency false in
/-- The extension class, precomposed with the canonical quasi-isomorphism out of the mapping
cone of the inclusion, is the connecting morphism of the mapping-cone triangle. -/
theorem mk₀_coneToInteger_comp_cohomologyClass :
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl E.coneToInteger).comp
        E.cohomologyClass (add_zero ((1 : ℕ) : ℤ)) =
      SmallShiftedHom.mk (analyticQuasiIsomorphisms X)
        (CochainComplex.mappingCone.triangle E.singleShortComplex.f).mor₃ := by
  apply (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
  rw [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀, SmallShiftedHom.equiv_mk,
    ShiftedHom.mk₀_comp,
    show (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q)
        E.cohomologyClass = E.shortExact.extClass.hom from rfl,
    ShortComplex.ShortExact.extClass_hom]
  simp [ShortComplex.ShortExact.singleδ, DerivedCategory.triangleOfSESδ, ShiftedHom.map,
    SingleFunctors.evaluation, -DerivedCategory.Q_obj_single_obj,
    DerivedCategory.singleFunctorsPostcompQIso_hom_hom,
    DerivedCategory.singleFunctorsPostcompQIso_inv_hom, CochainComplex.singleFunctors,
    ShortComplex.map, CochainComplex.singleFunctor, analyticSingleFunctor,
    HolomorphicUnitExtension.coneToInteger, HolomorphicUnitExtension.singleShortComplex,
    HolomorphicUnitExtension.shortComplex, Category.comp_id, SingleFunctors.postcomp]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The rational first Chern class of an extension is the composition of its extension class with
`rationalChernShiftedHom`, read through the comparison of the two presentations of the source
complex. -/
theorem cohomologyClass_comp_rationalChernShiftedHom :
    SmallShiftedHom.comp E.cohomologyClass (rationalChernShiftedHom X d)
        (show ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by lia) =
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
          (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).inv).comp
        (integralToRationalCohomology X 2 E.firstChernClass) (add_zero ((2 : ℕ) : ℤ)) := by
  have hα : analyticSheafCohomologyEquivExt X (constantIntegerSheaf X) 2 E.firstChernClass =
      holomorphicFirstChernClass X d E.cohomologyClass :=
    (analyticSheafCohomologyEquivExt X (constantIntegerSheaf X) 2).apply_symm_apply _
  have h1 := analyticSheafCohomologyEquivExt_comp X (constantIntegerSheaf X) 2 E.firstChernClass
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
      ((analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).inv ≫
        integerToFieldConstantSheafComplexInt ℚ X 1)) (zero_add ((2 : ℕ) : ℤ))
  rw [hα, SmallShiftedHom.mk₀_comp_mk₀' (M := ℤ),
    show (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).hom ≫
      (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).inv ≫
        integerToFieldConstantSheafComplexInt ℚ X 1 =
      integerToFieldConstantSheafComplexInt ℚ X 1 by
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]] at h1
  refine Eq.trans ?_ h1
  exact (SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X) E.cohomologyClass
    (holomorphicExponentialSequence_shortExact X d).extClass
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
      ((analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).inv ≫
        integerToFieldConstantSheafComplexInt ℚ X 1))
    (show ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by lia) (zero_add ((1 : ℕ) : ℤ))
    (by lia)).symm

/-! ### The canonical relative class of a splitting -/

variable (Ω : Opens (TopCat.of (ComplexPoint X))) (ℓ : E.middle.obj.obj (op Ω))
  (hℓ : E.projection.hom.app (op Ω) ℓ =
    (constantIntegerSheaf X).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op integerOneSection)

set_option backward.isDefEq.respectTransparency false in
/-- The commutative square expressing that the restriction morphism of the unit sheaf factors
through the inclusion of the unit sheaf into the middle term of the extension. -/
lemma singleShortComplex_f_comp_restrictionFactorisation :
    E.singleShortComplex.f ≫
        (analyticSingleFunctor X).map (E.restrictionFactorisation Ω ℓ hℓ) =
      𝟙 _ ≫ (analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d)) := by
  rw [Category.id_comp]
  exact ((analyticSingleFunctor X).map_comp E.inclusion
    (E.restrictionFactorisation Ω ℓ hℓ)).symm.trans
    (congrArg (analyticSingleFunctor X).map (E.inclusion_comp_restrictionFactorisation Ω ℓ hℓ))

/-- The canonical morphism of mapping cones induced by the splitting: it compares the cone of the
inclusion of the unit sheaf (a model of `ℤ_X`) with the cone of the restriction morphism. -/
def relativeConeMap : E.inclusionCone ⟶ relativeUnitCone X d Ω :=
  CochainComplex.mappingCone.map _ _ (𝟙 _)
    ((analyticSingleFunctor X).map (E.restrictionFactorisation Ω ℓ hℓ))
    (E.singleShortComplex_f_comp_restrictionFactorisation Ω ℓ hℓ)

/-- **The canonical relative cohomology class of a splitting.**

This is a genuine definition, involving no choice: the mapping cone of a morphism of complexes is
functorial for honest commutative squares, and the square is the factorisation
`E.inclusion ≫ restrictionFactorisation = restrictionUnit` produced by the splitting datum `ℓ`. -/
def relativeCohomologyClass :
    SmallShiftedHom.{1} (analyticQuasiIsomorphisms X)
      ((analyticSingleFunctor X).obj (constantIntegerSheaf X)) (relativeUnitCone X d Ω)
      (0 : ℤ) :=
  (SmallShiftedHom.precompEquiv E.coneToInteger
    (by change QuasiIso _; exact E.quasiIso_coneToInteger) (a := (0 : ℤ))).symm
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl (E.relativeConeMap Ω ℓ hℓ))

lemma mk₀_coneToInteger_comp_relativeCohomologyClass :
    (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl E.coneToInteger).comp
        (E.relativeCohomologyClass Ω ℓ hℓ) (add_zero (0 : ℤ)) =
      SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl (E.relativeConeMap Ω ℓ hℓ) :=
  (SmallShiftedHom.precompEquiv E.coneToInteger
    (by change QuasiIso _; exact E.quasiIso_coneToInteger) (a := (0 : ℤ))).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
/-- **The canonical relative class lifts the extension class.** Forgetting the trivialisation over
`Ω` — that is, composing with the connecting morphism of the cone of the restriction morphism —
recovers `E.cohomologyClass`. -/
theorem relativeCohomologyClass_comp_relativeUnitConeδ :
    (E.relativeCohomologyClass Ω ℓ hℓ).comp
        (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) (relativeUnitConeδ X d Ω))
        (add_zero ((1 : ℕ) : ℤ)) = E.cohomologyClass := by
  apply (SmallShiftedHom.precompEquiv E.coneToInteger
    (by change QuasiIso _; exact E.quasiIso_coneToInteger) (a := ((1 : ℕ) : ℤ))).injective
  show (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl E.coneToInteger).comp
      ((E.relativeCohomologyClass Ω ℓ hℓ).comp
        (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) (relativeUnitConeδ X d Ω))
        (add_zero ((1 : ℕ) : ℤ))) (add_zero ((1 : ℕ) : ℤ)) =
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl E.coneToInteger).comp
        E.cohomologyClass (add_zero ((1 : ℕ) : ℤ))
  rw [← SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X)
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl E.coneToInteger)
      (E.relativeCohomologyClass Ω ℓ hℓ)
      (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) (relativeUnitConeδ X d Ω))
      (add_zero (0 : ℤ)) (add_zero ((1 : ℕ) : ℤ)) (by lia),
    mk₀_coneToInteger_comp_relativeCohomologyClass,
    SmallShiftedHom.mk₀_comp_mk (analyticQuasiIsomorphisms X),
    E.mk₀_coneToInteger_comp_cohomologyClass]
  congr 1
  have hcomm := (CochainComplex.mappingCone.triangleMap E.singleShortComplex.f
    ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d)))
    (𝟙 _) ((analyticSingleFunctor X).map (E.restrictionFactorisation Ω ℓ hℓ))
    (E.singleShortComplex_f_comp_restrictionFactorisation Ω ℓ hℓ)).comm₃
  simp only [CochainComplex.mappingCone.triangleMap_hom₁,
    CochainComplex.mappingCone.triangleMap_hom₃] at hcomm
  exact hcomm.symm

/-- The canonical relative cohomology class, with the integral constant *complex* as source, so
that it can be composed into the hypercohomology presentation used by
`RationalCohomologyWithSupport`. -/
def relativeCohomologyClass' :
    SmallShiftedHom.{1} (analyticQuasiIsomorphisms X) (constantIntegerSheafComplexInt X)
      (relativeUnitCone X d Ω) (0 : ℤ) :=
  (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
      (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).hom).comp
    (E.relativeCohomologyClass Ω ℓ hℓ) (add_zero (0 : ℤ))

set_option backward.isDefEq.respectTransparency false in
lemma relativeCohomologyClass'_comp_relativeUnitConeδ :
    SmallShiftedHom.comp (E.relativeCohomologyClass' Ω ℓ hℓ)
        (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) (relativeUnitConeδ X d Ω))
        (add_zero ((1 : ℕ) : ℤ)) =
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
          (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).hom).comp
        E.cohomologyClass (add_zero ((1 : ℕ) : ℤ)) := by
  rw [relativeCohomologyClass',
    SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X)
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).hom)
      (E.relativeCohomologyClass Ω ℓ hℓ)
      (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) (relativeUnitConeδ X d Ω))
      (add_zero (0 : ℤ)) (add_zero ((1 : ℕ) : ℤ)) (by lia),
    E.relativeCohomologyClass_comp_relativeUnitConeδ Ω ℓ hℓ]

set_option backward.isDefEq.respectTransparency false in
/-- The rational first Chern class, as a composition out of the integral constant complex. -/
theorem mk₀_comp_cohomologyClass_comp_rationalChernShiftedHom :
    SmallShiftedHom.comp
        ((SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
            (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).hom).comp
          E.cohomologyClass (add_zero ((1 : ℕ) : ℤ)))
        (rationalChernShiftedHom X d)
        (show ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by lia) =
      integralToRationalCohomology X 2 E.firstChernClass := by
  rw [SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X)
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).hom)
      E.cohomologyClass (rationalChernShiftedHom X d)
      (add_zero ((1 : ℕ) : ℤ)) (show ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by lia)
      (by lia),
    E.cohomologyClass_comp_rationalChernShiftedHom,
    ← SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X)
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).hom)
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        (analyticSheafComplexIntIsoSingle X (constantIntegerSheaf X)).inv)
      (integralToRationalCohomology X 2 E.firstChernClass)
      (add_zero (0 : ℤ)) (add_zero ((2 : ℕ) : ℤ)) (by lia),
    SmallShiftedHom.mk₀_comp_mk₀' (M := ℤ), Iso.hom_inv_id,
    SmallShiftedHom.mk₀_id_comp]


/-- **The relative first Chern class** `c₁(E, ℓ)` of an extension together with a splitting over
the open set `Ω`, as a class in rational cohomology with support in `Ωᶜ`.

This is a genuine definition, not a choice: given the comparison datum, it is the canonical
relative class of the splitting composed with the comparison. -/
def relativeChernClass (cmp : RelativeChernComparison X d Ω) :
    RationalCohomologyWithSupport X ((Ω : Set (ComplexPoint X))ᶜ) 2 :=
  SmallShiftedHom.comp (E.relativeCohomologyClass' Ω ℓ hℓ) cmp.hom
    (show ((1 : ℕ) : ℤ) + (0 : ℤ) = (2 : ℤ) - 1 by lia)

set_option backward.isDefEq.respectTransparency false in
/-- **The relative first Chern class lifts the rational first Chern class.** -/
theorem forgetSupport_relativeChernClass (cmp : RelativeChernComparison X d Ω) :
    forgetSupport X ((Ω : Set (ComplexPoint X))ᶜ) 2 (E.relativeChernClass Ω ℓ hℓ cmp) =
      integralToRationalCohomology X 2 E.firstChernClass := by
  show SmallShiftedHom.comp
      (SmallShiftedHom.comp (E.relativeCohomologyClass' Ω ℓ hℓ) cmp.hom
        (show ((1 : ℕ) : ℤ) + (0 : ℤ) = (2 : ℤ) - 1 by lia))
      (forgetSupportShiftedHom X ((Ω : Set (ComplexPoint X))ᶜ))
      (show (1 : ℤ) + ((2 : ℤ) - 1) = ((2 : ℕ) : ℤ) by lia) = _
  rw [SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X)
      (E.relativeCohomologyClass' Ω ℓ hℓ) cmp.hom
      (forgetSupportShiftedHom X ((Ω : Set (ComplexPoint X))ᶜ))
      (show ((1 : ℕ) : ℤ) + (0 : ℤ) = (2 : ℤ) - 1 by lia)
      (show (1 : ℤ) + ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by lia) (by lia),
    cmp.comm,
    ← SmallShiftedHom.comp_assoc (analyticQuasiIsomorphisms X)
      (E.relativeCohomologyClass' Ω ℓ hℓ)
      (SmallShiftedHom.mk (analyticQuasiIsomorphisms X) (relativeUnitConeδ X d Ω))
      (rationalChernShiftedHom X d) (add_zero ((1 : ℕ) : ℤ))
      (show ((1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = ((2 : ℕ) : ℤ) by lia) (by lia),
    E.relativeCohomologyClass'_comp_relativeUnitConeδ Ω ℓ hℓ,
    E.mk₀_comp_cohomologyClass_comp_rationalChernShiftedHom]

end HolomorphicUnitExtension

/-! ### Existence of the comparison datum -/

variable (X d)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The comparison datum exists.** This is the axiom TR3 of triangulated categories applied to
the square formed by the rational exponential Chern class and the factorisation of the restricted
class through `η` (`exists_comp_restrictionUnit_eq`). -/
theorem nonempty_relativeChernComparison (Ω : Opens (TopCat.of (ComplexPoint X))) :
    Nonempty (RelativeChernComparison X d Ω) := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_comp_restrictionUnit_eq X Ω ((Ω : Set (ComplexPoint X))ᶜ)
    Ω.isOpen.isClosed_compl (compl_compl _).symm (holomorphicUnitSheaf X d) ((1 : ℕ) : ℤ)
    (SmallShiftedHom.comp (rationalChernShiftedHom X d)
      (SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl
        (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ))) (zero_add ((1 : ℕ) : ℤ)))
  -- the two derived morphisms forming the square
  set ζ₀D := (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q)
    (rationalChernShiftedHom X d) with hζ₀D
  set ζD := (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q) ζ with hζD
  have hsq : DerivedCategory.Q.map ((analyticSingleFunctor X).map
        (restrictionUnit Ω (holomorphicUnitSheaf X d))) ≫ ζD =
      ζ₀D ≫ (DerivedCategory.Q.map
        (rationalRestrictionComplexInt X ((Ω : Set (ComplexPoint X))ᶜ)))⟦(1 : ℤ)⟧' := by
    have h := congrArg (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q) hζ
    rw [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀,
      SmallShiftedHom.equiv_mk₀, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at h
    exact h.symm
  obtain ⟨c, -, hc₃⟩ := complete_distinguished_triangle_morphism
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
      ((analyticSingleFunctor X).map (restrictionUnit Ω (holomorphicUnitSheaf X d)))))
    ((CategoryTheory.shiftFunctor (Triangle (DerivedCategory (AnalyticAdditiveSheaf X)))
      (1 : ℤ)).obj (restrictionDerivedTriangle X ((Ω : Set (ComplexPoint X))ᶜ)))
    (DerivedCategory.mappingCone_triangle_distinguished _)
    (Triangle.shift_distinguished (restrictionDerivedTriangle X ((Ω : Set (ComplexPoint X))ᶜ))
      (restrictionDerivedTriangle_distinguished X ((Ω : Set (ComplexPoint X))ᶜ)) 1)
    (-ζ₀D) ζD (by
      dsimp [Triangle.shiftFunctor, CategoryTheory.Functor.mapTriangle, Triangle.mk,
        CochainComplex.mappingCone.triangle]
      rw [hsq]
      simp
      rfl)
  · dsimp [Triangle.shiftFunctor] at hc₃
    rw [shiftFunctorComm_eq_refl] at hc₃
    simp only [Triangle.mk_mor₃, Iso.refl_hom, NatTrans.id_app,
      CategoryTheory.Functor.map_neg, Preadditive.comp_neg,
      Units.neg_smul, one_smul, neg_inj] at hc₃
    simp only [CategoryTheory.Functor.comp_obj, Category.comp_id] at hc₃
    refine ⟨⟨(SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).symm c, ?_⟩⟩
    apply (SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q).injective
    rw [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_comp, Equiv.apply_symm_apply,
      equiv_forgetSupportShiftedHom, SmallShiftedHom.equiv_mk]
    have hc₃' : (DerivedCategory.Q.map (relativeUnitConeδ X d Ω) ≫
          (DerivedCategory.Q.commShiftIso ((1 : ℕ) : ℤ)).hom.app
            ((analyticSingleFunctor X).obj (holomorphicUnitSheaf X d))) ≫
          (shiftFunctor (DerivedCategory (AnalyticAdditiveSheaf X)) ((1 : ℕ) : ℤ)).map ζ₀D =
        c ≫ (shiftFunctor (DerivedCategory (AnalyticAdditiveSheaf X)) ((1 : ℕ) : ℤ)).map
          (restrictionDerivedTriangle X ((Ω : Set (ComplexPoint X))ᶜ)).mor₃ := hc₃
    dsimp only [ShiftedHom.comp, ShiftedHom.map]
    simp only [← Category.assoc]
    rw [hc₃']
    rfl

/-- **Unconditional form of step 3 with a canonical witness.** The rational first Chern class of
an extension splitting over `Ω` is the image, under `forgetSupport`, of the relative first Chern
class attached to the splitting. Compare
`exists_forgetSupport_eq_integralToRational_firstChernClass`, which produces a lift by bare
exactness; here the lift is `E.relativeChernClass Ω ℓ hℓ cmp`, built from the splitting. -/
theorem exists_relativeChernClass (Ω : Opens (TopCat.of (ComplexPoint X)))
    (E : HolomorphicUnitExtension X d) (ℓ : E.middle.obj.obj (op Ω))
    (hℓ : E.projection.hom.app (op Ω) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection) :
    ∃ β : RationalCohomologyWithSupport X ((Ω : Set (ComplexPoint X))ᶜ) 2,
      forgetSupport X ((Ω : Set (ComplexPoint X))ᶜ) 2 β =
        integralToRationalCohomology X 2 E.firstChernClass :=
  (nonempty_relativeChernComparison X d Ω).elim fun cmp =>
    ⟨E.relativeChernClass Ω ℓ hℓ cmp, E.forgetSupport_relativeChernClass Ω ℓ hℓ cmp⟩

end AlgebraicGeometry.ComplexPoint
