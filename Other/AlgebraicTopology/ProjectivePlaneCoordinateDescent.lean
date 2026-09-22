/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.TwoOpenCechCochain
public import Other.AlgebraicTopology.WindingRelativeUnitBoundary

/-!
# The literal Čech winding cocycle for the coordinate hyperplane in `ℙ²`

This is the analytic coordinate calculation behind the zero locus `X₀ = 0`.  On the two
standard affine charts meeting that hyperplane we use

* `[z : 1 : w]`, whose normal coordinate is `z`, and
* `[z' : w' : 1]`, whose normal coordinate is `z'`.

Their overlap is `w ≠ 0`, and the literal transition identity is
`z' = z * w⁻¹`.  The cochain below is therefore an actual element of the two-open
Čech--singular mapping-cone total complex: two displayed winding cochains plus the displayed
degree-zero correction on the overlap.
-/

@[expose] public noncomputable section

open CategoryTheory Topology AlgebraicTopology.Singular

namespace ChernWinding.ProjectivePlaneCoordinateDescent

/-- One affine coordinate chart, written as pairs `(z,w) ∈ ℂ²`. -/
abbrev chartAmbient : TopCat := TopCat.of (ℂ × ℂ)

/-- The complement of the coordinate hyperplane in one affine chart. -/
def normalComplement : Set (ℂ × ℂ) := {x | x.1 ≠ 0}

/-- An affine chart together with the complement of `X₀ = 0`. -/
abbrev chartPair : TopPair := TopPair.ofSubset (X := chartAmbient) normalComplement

/-- The normal coordinate `z` in either affine chart. -/
def chartNormal : C(chartPair.snd, ℂ) :=
  ⟨fun x => x.1.1, continuous_fst.comp continuous_subtype_val⟩

lemma chartNormal_ne_zero (x : chartPair.snd) : chartNormal x ≠ 0 := by
  exact x.2

/-- The overlap of the two affine coordinate charts, written in the first chart. -/
def chartOverlap : Set (ℂ × ℂ) := {x | x.2 ≠ 0}

/-- The overlap as a topological space. -/
abbrev overlapAmbient : TopCat := TopCat.of chartOverlap

/-- The complement of the hyperplane inside the overlap. -/
def overlapComplement : Set chartOverlap := {x | x.1.1 ≠ 0}

/-- The overlap pair. -/
abbrev overlapPair : TopPair := TopPair.ofSubset (X := overlapAmbient) overlapComplement

/-- The inclusion of the overlap in the first affine chart, as a map of pairs. -/
def overlapToFirstChart : overlapPair ⟶ chartPair :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun x => x.1, continuous_subtype_val⟩)
    (TopCat.ofHom ⟨fun x => ⟨x.1.1, x.2⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩)
    (by ext x; rfl)

/-- The coordinate change from `[z : 1 : w]` to `[z/w : 1/w : 1]`. -/
def chartTransition (x : chartOverlap) : ℂ × ℂ :=
  (x.1.1 * (x.1.2)⁻¹, (x.1.2)⁻¹)

lemma continuous_chartTransition : Continuous chartTransition := by
  exact ((continuous_fst.comp continuous_subtype_val).mul
    ((continuous_snd.comp continuous_subtype_val).inv₀ fun x => x.2)).prodMk
      ((continuous_snd.comp continuous_subtype_val).inv₀ fun x => x.2)

lemma chartTransition_normal_ne_zero (x : overlapPair.snd) :
    (chartTransition x.1).1 ≠ 0 := by
  change x.1.1.1 * (x.1.1.2)⁻¹ ≠ 0
  exact mul_ne_zero x.2 (inv_ne_zero x.1.2)

/-- The inclusion of the overlap in the second affine chart, expressed by the coordinate
change. -/
def overlapToSecondChart : overlapPair ⟶ chartPair :=
  TopPair.ofHom
    (TopCat.ofHom ⟨chartTransition, continuous_chartTransition⟩)
    (TopCat.ofHom ⟨fun x => ⟨chartTransition x.1, chartTransition_normal_ne_zero x⟩,
      (continuous_chartTransition.comp continuous_subtype_val).subtype_mk _⟩)
    (by ext x; rfl)

/-- The first chart's normal coordinate, restricted to the overlap pair. -/
def overlapFirstNormal : C(overlapPair.snd, ℂ) :=
  chartNormal.comp (topMap (TopPair.Hom.snd overlapToFirstChart))

lemma overlapFirstNormal_ne_zero (x : overlapPair.snd) : overlapFirstNormal x ≠ 0 :=
  chartNormal_ne_zero (TopPair.Hom.snd overlapToFirstChart x)

/-- The second chart's normal coordinate, restricted to the overlap pair. -/
def overlapSecondNormal : C(overlapPair.snd, ℂ) :=
  chartNormal.comp (topMap (TopPair.Hom.snd overlapToSecondChart))

lemma overlapSecondNormal_ne_zero (x : overlapPair.snd) : overlapSecondNormal x ≠ 0 :=
  chartNormal_ne_zero (TopPair.Hom.snd overlapToSecondChart x)

/-- The nowhere-zero transition unit `w⁻¹` on the overlap. -/
def overlapUnit : C(overlapPair.fst, ℂ) :=
  ⟨fun x => (x.1.2)⁻¹,
    (continuous_snd.comp continuous_subtype_val).inv₀ fun x => x.2⟩

lemma overlapUnit_ne_zero (x : overlapPair.fst) : overlapUnit x ≠ 0 := by
  exact inv_ne_zero x.2

/-- The coordinate-transition formula `z' = z w⁻¹` on the overlap. -/
lemma overlap_normal_transition (x : overlapPair.snd) :
    overlapSecondNormal x = overlapFirstNormal x *
      (overlapUnit.comp (topMap overlapPair.map)) x := by
  change x.1.1.1 * (x.1.1.2)⁻¹ = x.1.1.1 * (x.1.1.2)⁻¹
  rfl

/-- The raw normal winding cochain on the first affine chart. -/
def firstChartWindingCochain :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ chartPair)).X 1 :=
  rawRelativeWindingCochain (X := chartPair) chartNormal chartNormal_ne_zero

/-- The raw normal winding cochain on the second affine chart. -/
def secondChartWindingCochain :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ chartPair)).X 1 :=
  rawRelativeWindingCochain (X := chartPair) chartNormal chartNormal_ne_zero

/-- Restriction from the first chart to the overlap in the literal relative-cone model. -/
def firstChartRestriction :
    CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ chartPair) ⟶
      CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ overlapPair) :=
  relativeCochainConeMap ℚ overlapToFirstChart

/-- Restriction from the second chart to the overlap in the literal relative-cone model. -/
def secondChartRestriction :
    CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ chartPair) ⟶
      CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ overlapPair) :=
  relativeCochainConeMap ℚ overlapToSecondChart

/-- The first local cochain restricts to the literal winding cochain of `z`. -/
lemma firstChartRestriction_winding :
    firstChartRestriction.f 1 firstChartWindingCochain =
      rawRelativeWindingCochain (X := overlapPair)
        overlapFirstNormal overlapFirstNormal_ne_zero := by
  change rawRelativeWindingCochainPullback
      overlapToFirstChart chartNormal chartNormal_ne_zero = _
  exact rawRelativeWindingCochainPullback_eq_rawRelativeWindingCochain
    overlapToFirstChart chartNormal chartNormal_ne_zero

/-- The second local cochain restricts to the literal winding cochain of `z/w`. -/
lemma secondChartRestriction_winding :
    secondChartRestriction.f 1 secondChartWindingCochain =
      rawRelativeWindingCochain (X := overlapPair)
        overlapSecondNormal overlapSecondNormal_ne_zero := by
  change rawRelativeWindingCochainPullback
      overlapToSecondChart chartNormal chartNormal_ne_zero = _
  exact rawRelativeWindingCochainPullback_eq_rawRelativeWindingCochain
    overlapToSecondChart chartNormal chartNormal_ne_zero

/-- The completely explicit degree-zero overlap correction: the ambient winding cochain of
`w⁻¹`, minus the principal-log branch jump. -/
def overlapTransitionPrimitive :
    (CochainComplex.mappingCone (relativeCochainRestrictionInt ℚ overlapPair)).X 0 :=
  rawRelativeWindingCoordinateTransitionPrimitive
    overlapFirstNormal overlapUnit overlapSecondNormal
    overlapFirstNormal_ne_zero overlapUnit_ne_zero overlapSecondNormal_ne_zero
    overlap_normal_transition

/-- The concrete compatibility equation for the two affine normal winding cochains. -/
lemma chartWindingCochainCompatibility :
    firstChartRestriction.f 1 firstChartWindingCochain -
      secondChartRestriction.f 1 secondChartWindingCochain =
        -(CochainComplex.mappingCone
          (relativeCochainRestrictionInt ℚ overlapPair)).d 0 1
          overlapTransitionPrimitive := by
  rw [firstChartRestriction_winding, secondChartRestriction_winding]
  change rawRelativeWindingCochain (X := overlapPair)
      overlapFirstNormal overlapFirstNormal_ne_zero -
      rawRelativeWindingCochain (X := overlapPair)
        overlapSecondNormal overlapSecondNormal_ne_zero =
      -(CochainComplex.mappingCone
        (relativeCochainRestrictionInt ℚ overlapPair)).d
          (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1)
        (rawRelativeWindingCoordinateTransitionPrimitive
          overlapFirstNormal overlapUnit overlapSecondNormal
          overlapFirstNormal_ne_zero overlapUnit_ne_zero overlapSecondNormal_ne_zero
          overlap_normal_transition)
  have htransition := rawRelativeWindingCochain_coordinateTransition
    overlapFirstNormal overlapUnit overlapSecondNormal
    overlapFirstNormal_ne_zero overlapUnit_ne_zero overlapSecondNormal_ne_zero
    overlap_normal_transition
  rw [htransition]
  abel

/-- The literal Čech--singular cochain for the coordinate hyperplane.  It has the three
promised visible components: winding on `[z:1:w]`, winding on `[z':w':1]`, and the explicit
branch-corrected overlap primitive. -/
def coordinateHyperplaneCechCochain :
    (twoOpenCechTotal firstChartRestriction secondChartRestriction).X 0 :=
  twoOpenCechCochain firstChartRestriction secondChartRestriction 1
    firstChartWindingCochain secondChartWindingCochain overlapTransitionPrimitive

/-- The displayed coordinate-hyperplane Čech cochain is closed, before taking any quotient by
coboundaries or choosing any representative. -/
lemma coordinateHyperplaneCechCochain_closed :
    (twoOpenCechTotal firstChartRestriction secondChartRestriction).d 0 1
      coordinateHyperplaneCechCochain = 0 := by
  exact twoOpenCechCochain_closed firstChartRestriction secondChartRestriction 1
    firstChartWindingCochain secondChartWindingCochain overlapTransitionPrimitive
    (rawRelativeWindingCochain_closed chartNormal chartNormal_ne_zero)
    (rawRelativeWindingCochain_closed chartNormal chartNormal_ne_zero)
    chartWindingCochainCompatibility

/-- The displayed cochain packaged as a cycle of the Čech--singular total complex. -/
def coordinateHyperplaneCechCocycle :
    ModuleCat.of ℚ ℚ ⟶
      (twoOpenCechTotal firstChartRestriction secondChartRestriction).cycles 0 :=
  (twoOpenCechTotal firstChartRestriction secondChartRestriction).liftCycles
    (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ coordinateHyperplaneCechCochain)) 1
    (by norm_num) (by
      ext
      change (twoOpenCechTotal firstChartRestriction secondChartRestriction).d 0 1
        (LinearMap.toSpanSingleton ℚ _ coordinateHyperplaneCechCochain 1) = 0
      rw [LinearMap.toSpanSingleton_apply]
      simpa using coordinateHyperplaneCechCochain_closed)

/-- The cohomology class of the literal Čech--singular cocycle. -/
def coordinateHyperplaneCechClass :
    (twoOpenCechTotal firstChartRestriction secondChartRestriction).homology 0 :=
  (coordinateHyperplaneCechCocycle ≫
    (twoOpenCechTotal firstChartRestriction secondChartRestriction).homologyπ 0).hom 1

end ChernWinding.ProjectivePlaneCoordinateDescent
