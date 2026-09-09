/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SmoothClosedSupportedCycleMorphism
public import Other.AlgebraicTopology.ClosedEmbeddingConstantSectionClass
public import Other.AlgebraicGeometry.IntrinsicComplexBorelMoore

/-!
# Actual ordinary classes of smooth closed complex subvarieties

For a smooth closed immersion of an `e`-dimensional smooth complex scheme into a
`d`-dimensional smooth complex scheme, the literal constant-one section on the source
is sent through the normalized source orientation and the actual singular-chain sheaf
pushforward. Actual derived whole-space sections give a Borel–Moore class with whole
ambient support; the constructed ambient orientation gives an ordinary cohomology class
in degree `2d - 2e`. Whole-space supported cohomology is used as the derived presentation
of ordinary cohomology here.

All coefficients are additive, and the specialization to codimension `p` proves the
degree arithmetic. Neither an orientation nor a comparison is an input. These are
smooth closed-component classes, not classes for singular components or a Chow map.
Relating this global construction to the group-valued class supported on the exact
closed image is a further compatibility theorem for the two derived support operations.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

namespace AlgebraicGeometry.ComplexPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable local instance smoothClosedClassAnalyticTopology
    (Y : Over (Spec (.of ℂ))) : TopologicalSpace (ComplexPoint Y) :=
  Point.analyticTopology

local instance smoothClosedClassSheafDerivedCategory
    (Y : Over (Spec (.of ℂ))) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint Y))) :=
  HasDerivedCategory.standard _

local instance smoothClosedClassGroupsDerivedCategory : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

variable (Z X : Over (Spec (.of ℂ)))
  (i : Z ⟶ X) [IsClosedImmersion i.left]
  (e d : ℕ) [SmoothOfRelativeDimension e Z.hom] [SmoothOfRelativeDimension d X.hom]
  [T2Space (ComplexPoint Z)] [T2Space (ComplexPoint X)]

/-- The actual normalized smooth closed-component Borel–Moore class with whole ambient
support, additive in the coefficient multiplying the literal source section. -/
def smoothClosedWholeSupportBorelMooreClassMap :
    AddCommGrpCat.of ℚ ⟶
      ComplexAmbientSheafBorelMooreHomology X d ⊤ (2 * (e : ℤ)) :=
  TopCat.Sheaf.closedEmbeddingConstantShiftedSectionClassMap
    (closedCycleAnalyticMap Z X i) ℚ
    (closedCycleAnalyticMap_isClosedEmbedding Z X i) (2 * (e : ℤ)) ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat (-(2 * (e : ℤ)))).map
        ((TopCat.Sheaf.derivedClosedSupportSections (TopCat.of (ComplexPoint X)) ⊤).map
          (smoothClosedCycleMorphism Z X i e d))

/-- The fundamental class uses exactly `1` in the source constant rational sheaf. -/
def smoothClosedWholeSupportBorelMooreClass :
    ComplexAmbientSheafBorelMooreHomology X d ⊤ (2 * (e : ℤ)) :=
  smoothClosedWholeSupportBorelMooreClassMap Z X i e d 1

/-- The constructed smooth closed-component class in intrinsic chain-sheaf
Borel–Moore homology of the ambient analytic space. The comparison used here is
constructed from complex orientation; it is not an additional input. -/
def smoothClosedIntrinsicBorelMooreClass :
    IntrinsicSheafBorelMooreHomology X (2 * (e : ℤ)) :=
  (intrinsicComplexBorelMooreAddEquivAmbientTop X d (2 * (e : ℤ))).symm
    (smoothClosedWholeSupportBorelMooreClass Z X i e d)

/-- The intrinsic class recovers the existing normalized whole-support class. -/
@[simp]
lemma smoothClosedIntrinsicBorelMooreClass_comparison :
    intrinsicComplexBorelMooreAddEquivAmbientTop X d (2 * (e : ℤ))
      (smoothClosedIntrinsicBorelMooreClass Z X i e d) =
      smoothClosedWholeSupportBorelMooreClass Z X i e d :=
  (intrinsicComplexBorelMooreAddEquivAmbientTop X d (2 * (e : ℤ))).apply_symm_apply _

/-- Actual ordinary cohomology classes of smooth closed subvarieties, with no comparison
input; the displayed ambient orientation supplies the degree shift. -/
def smoothClosedCohomologyClassMap :
    AddCommGrpCat.of ℚ ⟶
      ComplexDerivedSupportedCohomology X ⊤ (2 * (d : ℤ) - 2 * (e : ℤ)) :=
  smoothClosedWholeSupportBorelMooreClassMap Z X i e d ≫
    (complexAmbientSheafBorelMooreHomologyIso X d ⊤ (2 * (e : ℤ))).hom

/-- The normalized ordinary class of a smooth closed immersion. -/
def smoothClosedCohomologyClass :
    ComplexDerivedSupportedCohomology X ⊤ (2 * (d : ℤ) - 2 * (e : ℤ)) :=
  smoothClosedCohomologyClassMap Z X i e d 1

/-- Ordinary duality sends the actually constructed fundamental class to the actual
ordinary class; this is a normalization theorem for the displayed construction. -/
@[simp]
lemma smoothClosedCohomologyClass_eq_orientation :
    smoothClosedCohomologyClass Z X i e d =
      (complexAmbientSheafBorelMooreHomologyIso X d ⊤ (2 * (e : ℤ))).hom
        (smoothClosedWholeSupportBorelMooreClass Z X i e d) := rfl

/-- Coefficients add through the actual class construction. -/
@[simp]
lemma smoothClosedCohomologyClassMap_add (q r : ℚ) :
    smoothClosedCohomologyClassMap Z X i e d (q + r) =
      smoothClosedCohomologyClassMap Z X i e d q +
        smoothClosedCohomologyClassMap Z X i e d r :=
  map_add _ _ _

/-- Integer multiplicity has its usual meaning for the normalized fundamental class. -/
@[simp]
lemma smoothClosedCohomologyClassMap_int (m : ℤ) :
    smoothClosedCohomologyClassMap Z X i e d (m : ℚ) =
      m • smoothClosedCohomologyClass Z X i e d := by
  simpa [smoothClosedCohomologyClass] using
    map_zsmul (smoothClosedCohomologyClassMap Z X i e d).hom m (1 : ℚ)

/-- A finite linear combination of coefficients is evaluated term by term. -/
lemma smoothClosedCohomologyClassMap_sum {ι : Type*} (s : Finset ι) (q : ι → ℚ) :
    smoothClosedCohomologyClassMap Z X i e d (∑ j ∈ s, q j) =
      ∑ j ∈ s, smoothClosedCohomologyClassMap Z X i e d (q j) :=
  map_sum _ _ _

/-- The codimension specialization proves the arithmetic from the actual dimension equality. -/
def smoothClosedCohomologyClassInCodimension (p : ℕ) (hdim : e + p = d) :
    ComplexDerivedSupportedCohomology X ⊤ (2 * (p : ℤ)) :=
  (eqToIso (congrArg (ComplexDerivedSupportedCohomology X ⊤)
    (show 2 * (d : ℤ) - 2 * (e : ℤ) = 2 * (p : ℤ) by omega))).hom
      (smoothClosedCohomologyClass Z X i e d)

end AlgebraicGeometry.ComplexPoint
