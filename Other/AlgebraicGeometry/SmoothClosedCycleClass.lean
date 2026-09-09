/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SmoothClosedSupportedCycleMorphism
public import Other.AlgebraicTopology.ClosedEmbeddingConstantSectionClass

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
    (Y : Scheme) (sY : Y ⟶ Spec (.of ℂ)) : TopologicalSpace (ComplexPoint Y sY) :=
  Point.analyticTopology

local instance smoothClosedClassSheafDerivedCategory
    (Y : Scheme) (sY : Y ⟶ Spec (.of ℂ)) :
    HasDerivedCategory (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint Y sY))) :=
  HasDerivedCategory.standard _

local instance smoothClosedClassGroupsDerivedCategory : HasDerivedCategory AddCommGrpCat :=
  HasDerivedCategory.standard _

variable {Z X : Scheme} (sZ : Z ⟶ Spec (.of ℂ)) (sX : X ⟶ Spec (.of ℂ))
  (i : Z ⟶ X) (hi : i ≫ sX = sZ) [IsClosedImmersion i]
  (e d : ℕ) [SmoothOfRelativeDimension e sZ] [SmoothOfRelativeDimension d sX]
  [T2Space (ComplexPoint Z sZ)] [T2Space (ComplexPoint X sX)]

/-- The actual normalized smooth closed-component Borel–Moore class with whole ambient
support, additive in the coefficient multiplying the literal source section. -/
def smoothClosedWholeSupportBorelMooreClassMap :
    AddCommGrpCat.of ℚ ⟶
      ComplexAmbientSheafBorelMooreHomology sX d ⊤ (2 * (e : ℤ)) :=
  TopCat.Sheaf.closedEmbeddingConstantShiftedSectionClassMap
    (closedCycleAnalyticMap sZ sX i hi) ℚ
    (closedCycleAnalyticMap_isClosedEmbedding sZ sX i hi) (2 * (e : ℤ)) ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat (-(2 * (e : ℤ)))).map
        ((TopCat.Sheaf.derivedClosedSupportSections (TopCat.of (ComplexPoint X sX)) ⊤).map
          (smoothClosedCycleMorphism sZ sX i hi e d))

/-- The fundamental class uses exactly `1` in the source constant rational sheaf. -/
def smoothClosedWholeSupportBorelMooreClass :
    ComplexAmbientSheafBorelMooreHomology sX d ⊤ (2 * (e : ℤ)) :=
  smoothClosedWholeSupportBorelMooreClassMap sZ sX i hi e d 1

/-- Actual ordinary cohomology classes of smooth closed subvarieties, with no comparison
input; the displayed ambient orientation supplies the degree shift. -/
def smoothClosedCohomologyClassMap :
    AddCommGrpCat.of ℚ ⟶
      ComplexDerivedSupportedCohomology sX ⊤ (2 * (d : ℤ) - 2 * (e : ℤ)) :=
  smoothClosedWholeSupportBorelMooreClassMap sZ sX i hi e d ≫
    (complexAmbientSheafBorelMooreHomologyIso sX d ⊤ (2 * (e : ℤ))).hom

/-- The normalized ordinary class of a smooth closed immersion. -/
def smoothClosedCohomologyClass :
    ComplexDerivedSupportedCohomology sX ⊤ (2 * (d : ℤ) - 2 * (e : ℤ)) :=
  smoothClosedCohomologyClassMap sZ sX i hi e d 1

/-- Ordinary duality sends the actually constructed fundamental class to the actual
ordinary class; this is a normalization theorem for the displayed construction. -/
@[simp]
lemma smoothClosedCohomologyClass_eq_orientation :
    smoothClosedCohomologyClass sZ sX i hi e d =
      (complexAmbientSheafBorelMooreHomologyIso sX d ⊤ (2 * (e : ℤ))).hom
        (smoothClosedWholeSupportBorelMooreClass sZ sX i hi e d) := rfl

/-- Coefficients add through the actual class construction. -/
@[simp]
lemma smoothClosedCohomologyClassMap_add (q r : ℚ) :
    smoothClosedCohomologyClassMap sZ sX i hi e d (q + r) =
      smoothClosedCohomologyClassMap sZ sX i hi e d q +
        smoothClosedCohomologyClassMap sZ sX i hi e d r :=
  map_add _ _ _

/-- Integer multiplicity has its usual meaning for the normalized fundamental class. -/
@[simp]
lemma smoothClosedCohomologyClassMap_int (m : ℤ) :
    smoothClosedCohomologyClassMap sZ sX i hi e d (m : ℚ) =
      m • smoothClosedCohomologyClass sZ sX i hi e d := by
  simpa [smoothClosedCohomologyClass] using
    map_zsmul (smoothClosedCohomologyClassMap sZ sX i hi e d).hom m (1 : ℚ)

/-- A finite linear combination of coefficients is evaluated term by term. -/
lemma smoothClosedCohomologyClassMap_sum {ι : Type*} (s : Finset ι) (q : ι → ℚ) :
    smoothClosedCohomologyClassMap sZ sX i hi e d (∑ j ∈ s, q j) =
      ∑ j ∈ s, smoothClosedCohomologyClassMap sZ sX i hi e d (q j) :=
  map_sum _ _ _

/-- The codimension specialization proves the arithmetic from the actual dimension equality. -/
def smoothClosedCohomologyClassInCodimension (p : ℕ) (hdim : e + p = d) :
    ComplexDerivedSupportedCohomology sX ⊤ (2 * (p : ℤ)) :=
  (eqToIso (congrArg (ComplexDerivedSupportedCohomology sX ⊤)
    (show 2 * (d : ℤ) - 2 * (e : ℤ) = 2 * (p : ℤ) by omega))).hom
      (smoothClosedCohomologyClass sZ sX i hi e d)

end AlgebraicGeometry.ComplexPoint
