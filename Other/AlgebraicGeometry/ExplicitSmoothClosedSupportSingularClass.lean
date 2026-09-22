/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import Other.AlgebraicGeometry.SmoothClosedSupportLowestCohomology
public import HodgeConjecture.Definitions.AlgebraicGeometry.CycleComponentSheafClass
public import Other.AlgebraicTopology.TopOpenRelativeCochainNormalization
public import Other.AlgebraicGeometry.ExplicitSingularToHypercohomology
public import Other.AlgebraicGeometry.ExplicitSupportedPositiveKernel
public import Other.AlgebraicGeometry.ComplexSupportCohomologySheafNormalization

/-!
# A supported singular class from the normalized local normal coclass

For a smooth closed immersion, the existing normalized support section is characterized by its
local normal-coclass germs.  Lowest-degree support cohomology turns that section into a global
supported class, and the literal top-open pair isomorphism then puts it in singular cohomology
with support.  The separate chart-level winding cochains are proved closed in the projective-plane
file, but their chain-level map into this global section is not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (Y : Over (Spec (.of ℂ))) (i : Y ⟶ X)
  (m d : ℕ) [SmoothOfRelativeDimension m Y.hom]
  [SmoothOfRelativeDimension d X.hom] [IsClosedImmersion i.left]

local instance explicitSmoothClosedSupportAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

local instance explicitSmoothClosedSupportOpenParacompact :
    ∀ U : Opens (ComplexPoint X), ParacompactSpace U := openParacompactSpace X

/-- The global supported-injective class whose local normalization is the already constructed
normal-coclass section. -/
def smoothClosedSupportInjectiveClass :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      ℤᵘᵖ).obj (complexSupportInjectiveComplex X
        (smoothClosedAnalyticSupport X Y i)))).homology
      (2 * ((d - m : ℕ) : ℤ)) := by
  let S := smoothClosedAnalyticSupport X Y i
  let e := complexSupportInjectiveCohomologySheafIsoRelative X S (2 * (d - m))
  let l := smoothClosedSupportLowestSectionCohomologyIso X Y i m d ⊤
  have hdegree : ((2 * (d - m : ℕ) : ℕ) : ℤ) = 2 * ((d - m : ℕ) : ℤ) := by
    omega
  exact hdegree ▸ l.inv
    (e.inv.hom.app (op ⊤) (smoothClosedSupportCoclassSection X Y i m d))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The globally supported injective class has exactly the prescribed smooth normal-coclass
section under the two canonical normalization isomorphisms used in its definition. -/
@[simp]
theorem smoothClosedSupportInjectiveClass_normalization :
    (complexSupportInjectiveCohomologySheafIsoRelative X
        (smoothClosedAnalyticSupport X Y i) (2 * (d - m))).hom.hom.app (op ⊤)
      ((smoothClosedSupportLowestSectionCohomologyIso X Y i m d ⊤).hom
        (smoothClosedSupportInjectiveClass X Y i m d)) =
      smoothClosedSupportCoclassSection X Y i m d := by
  let S := smoothClosedAnalyticSupport X Y i
  let e := complexSupportInjectiveCohomologySheafIsoRelative X S (2 * (d - m))
  let l := smoothClosedSupportLowestSectionCohomologyIso X Y i m d ⊤
  change e.hom.hom.app (op ⊤)
      (l.hom (l.inv (e.inv.hom.app (op ⊤)
        (smoothClosedSupportCoclassSection X Y i m d)))) = _
  rw [Iso.inv_hom_id_apply]
  have he := congrArg (fun f ↦ f.hom.app (op ⊤)) e.inv_hom_id
  exact ConcreteCategory.congr_hom he _

/-- The resulting class in the literal singular cohomology of the global pair
`(X(ℂ), X(ℂ) \ i(Y(ℂ)))`.  Its construction uses the normalized normal-coclass section and then
the proved support comparisons. -/
def smoothClosedSupportSingularClass :
    CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X))
      (Set.range (Point.map i)) (2 * (d - m)) := by
  let S := smoothClosedAnalyticSupport X Y i
  let b := complexSupportInjectiveSectionCohomologyEquiv X S ⊤ (2 * (d - m))
    (smoothClosedSupportInjectiveClass X Y i m d)
  exact relativeCohomologyMap ℚ (2 * (d - m))
    (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X)) S).inv b

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Returning the normalized supported singular class to the top-open relative-cohomology
sheaf gives exactly the globally normalized normal-coclass section.  In particular, the
passage through the supported injective resolution and the literal top-open pair introduces
neither a choice nor an additional sign. -/
theorem smoothClosedSupportSingularClass_normalization :
    (supportRelativeCohomologyToSheaf
        (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))).app (op ⊤)
      (relativeCohomologyMap ℚ (2 * (d - m))
        (topOpenNeighborhoodSupportPairIso
          (TopCat.of (ComplexPoint X)) (smoothClosedAnalyticSupport X Y i)).hom
        (smoothClosedSupportSingularClass X Y i m d)) =
      smoothClosedSupportCoclassSection X Y i m d := by
  let S := smoothClosedAnalyticSupport X Y i
  let z := smoothClosedSupportInjectiveClass X Y i m d
  have hpair :
      relativeCohomologyMap ℚ (2 * (d - m))
          (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X)) S).hom
          (smoothClosedSupportSingularClass X Y i m d) =
        complexSupportInjectiveSectionCohomologyEquiv X S ⊤ (2 * (d - m)) z := by
    dsimp [smoothClosedSupportSingularClass, S, z]
    change ((relativeCohomologyMap ℚ (2 * (d - m))
        (topOpenNeighborhoodSupportPairIso
          (TopCat.of (ComplexPoint X)) (smoothClosedAnalyticSupport X Y i)).hom).comp
      (relativeCohomologyMap ℚ (2 * (d - m))
        (topOpenNeighborhoodSupportPairIso
          (TopCat.of (ComplexPoint X)) (smoothClosedAnalyticSupport X Y i)).inv)) _ = _
    rw [← relativeCohomologyMap_comp]
    simp
  rw [hpair]
  change (supportRelativeCohomologyToSheaf
      (TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X)) (2 * (d - m))).app (op ⊤)
        (complexSupportInjectiveSectionCohomologyEquiv X S ⊤ (2 * (d - m)) z) = _
  rw [← complexSupportInjectiveCohomologySheafIsoRelative_section_apply
    X S (2 * (d - m)) ⊤ z]
  dsimp only [S, z]
  change (complexSupportInjectiveCohomologySheafIsoRelative X
      (smoothClosedAnalyticSupport X Y i) (2 * (d - m))).hom.hom.app (op ⊤)
        (TopCat.Sheaf.sectionCohomologyToSheafSection
          (TopCat.of (ComplexPoint X))
          (complexSupportInjectiveComplex X (smoothClosedAnalyticSupport X Y i))
          (2 * ((d - m : ℕ) : ℤ)) ⊤
          (smoothClosedSupportInjectiveClass X Y i m d)) = _
  simpa only [smoothClosedSupportLowestSectionCohomologyIso_hom] using
    (smoothClosedSupportInjectiveClass_normalization X Y i m d)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In the lowest supported degree, the top-open singular class is determined by the
corresponding support-cohomology sheaf section. -/
theorem smoothClosedSupportSingularNormalization_injective :
    Function.Injective (fun a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X))
        (Set.range (Point.map i)) (2 * (d - m)) ↦
      (supportRelativeCohomologyToSheaf
        (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))).app (op ⊤)
        (relativeCohomologyMap ℚ (2 * (d - m))
          (topOpenNeighborhoodSupportPairIso
            (TopCat.of (ComplexPoint X)) (smoothClosedAnalyticSupport X Y i)).hom a)) := by
  intro a b hab
  let S := smoothClosedAnalyticSupport X Y i
  let q : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X))
      (Set.range (Point.map i)) (2 * (d - m)) →
      RelativeCohomology ℚ
        (neighborhoodSupportComplementPair ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X)) S)
        (2 * (d - m)) :=
    fun c ↦ relativeCohomologyMap ℚ (2 * (d - m))
      (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X)) S).hom c
  let e := complexSupportInjectiveSectionCohomologyEquiv X S ⊤ (2 * (d - m))
  let za := e.symm (q a)
  let zb := e.symm (q b)
  have hsection :
      (TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X S) (2 * ((d - m : ℕ) : ℤ)) ⊤ za) =
      (TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X S) (2 * ((d - m : ℕ) : ℤ)) ⊤ zb) := by
    have ha := complexSupportInjectiveCohomologySheafIsoRelative_section_apply
      X S (2 * (d - m)) ⊤ za
    have hb := complexSupportInjectiveCohomologySheafIsoRelative_section_apply
      X S (2 * (d - m)) ⊤ zb
    have habS :
        (supportRelativeCohomologyToSheaf
          (TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X)) (2 * (d - m))).app
            (op ⊤) (q a) =
          (supportRelativeCohomologyToSheaf
          (TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X)) (2 * (d - m))).app
            (op ⊤) (q b) := by
      dsimp only [q, S]
      exact hab
    have hqa : q a = e za := (e.apply_symm_apply _).symm
    have hqb : q b = e zb := (e.apply_symm_apply _).symm
    have hab' := congrArg
      ((complexSupportInjectiveCohomologySheafIsoRelative X S (2 * (d - m))).inv.hom.app (op ⊤)) habS
    rw [hqa, hqb, ← ha, ← hb] at hab'
    have hid := congrArg (fun f ↦ f.hom.app (op ⊤))
      (complexSupportInjectiveCohomologySheafIsoRelative X S (2 * (d - m))).hom_inv_id
    have ha' := ConcreteCategory.congr_hom hid
      ((TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X S) (2 * ((d - m : ℕ) : ℤ)) ⊤) za)
    have hb' := ConcreteCategory.congr_hom hid
      ((TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X S) (2 * ((d - m : ℕ) : ℤ)) ⊤) zb)
    calc
      _ = (ConcreteCategory.hom
        ((complexSupportInjectiveCohomologySheafIsoRelative X S (2 * (d - m))).inv.hom.app
          (op ⊤)))
          ((ConcreteCategory.hom
            ((complexSupportInjectiveCohomologySheafIsoRelative X S (2 * (d - m))).hom.hom.app
              (op ⊤)))
            ((ConcreteCategory.hom
              (TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
                (complexSupportInjectiveComplex X S) (2 * ((d - m : ℕ) : ℤ)) ⊤)) za)) := ha'.symm
      _ = _ := hab'
      _ = _ := hb'
  have hza : za = zb := by
    apply (smoothClosedSupportLowestSectionCohomologyIso X Y i m d ⊤).addCommGroupIsoToAddEquiv.injective
    change (smoothClosedSupportLowestSectionCohomologyIso X Y i m d ⊤).hom za =
      (smoothClosedSupportLowestSectionCohomologyIso X Y i m d ⊤).hom zb
    simpa only [smoothClosedSupportLowestSectionCohomologyIso_hom] using hsection
  have hq : q a = q b := by
    calc
      q a = e (e.symm (q a)) := (e.apply_symm_apply _).symm
      _ = e (e.symm (q b)) := congrArg e hza
      _ = q b := e.apply_symm_apply _
  have hback := congrArg
    (relativeCohomologyMap ℚ (2 * (d - m))
      (topOpenNeighborhoodSupportPairIso
        (TopCat.of (ComplexPoint X)) (smoothClosedAnalyticSupport X Y i)).inv) hq
  dsimp only [q, S] at hback
  change ((relativeCohomologyMap ℚ (2 * (d - m))
      (topOpenNeighborhoodSupportPairIso
        (TopCat.of (ComplexPoint X)) (smoothClosedAnalyticSupport X Y i)).inv).comp
    (relativeCohomologyMap ℚ (2 * (d - m))
      (topOpenNeighborhoodSupportPairIso
        (TopCat.of (ComplexPoint X)) (smoothClosedAnalyticSupport X Y i)).hom)) a =
    ((relativeCohomologyMap ℚ (2 * (d - m))
      (topOpenNeighborhoodSupportPairIso
        (TopCat.of (ComplexPoint X)) (smoothClosedAnalyticSupport X Y i)).inv).comp
    (relativeCohomologyMap ℚ (2 * (d - m))
      (topOpenNeighborhoodSupportPairIso
        (TopCat.of (ComplexPoint X)) (smoothClosedAnalyticSupport X Y i)).hom)) b at hback
  rw [← relativeCohomologyMap_comp] at hback
  simpa using hback

/-- Once a supported singular class has the same top-open normal-coclass section as the
normalized smooth-closed construction, the two supported classes are equal.  This is the
interface used by an explicit two-chart calculation: the chart calculation need only establish
the displayed section equality, not a separate global cohomological uniqueness assumption. -/
theorem smoothClosedSupportSingularClass_eq_of_normalization
    (a : CohomologyWithSupport ℚ (TopCat.of (ComplexPoint X))
      (Set.range (Point.map i)) (2 * (d - m)))
    (ha :
      (supportRelativeCohomologyToSheaf
        (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))).app (op ⊤)
        (relativeCohomologyMap ℚ (2 * (d - m))
          (topOpenNeighborhoodSupportPairIso
            (TopCat.of (ComplexPoint X)) (smoothClosedAnalyticSupport X Y i)).hom a) =
        smoothClosedSupportCoclassSection X Y i m d) :
    a = smoothClosedSupportSingularClass X Y i m d := by
  apply smoothClosedSupportSingularNormalization_injective X Y i m d
  change (supportRelativeCohomologyToSheaf
      (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))).app (op ⊤)
      (relativeCohomologyMap ℚ (2 * (d - m))
        (topOpenNeighborhoodSupportPairIso
          (TopCat.of (ComplexPoint X)) (smoothClosedAnalyticSupport X Y i)).hom a) =
    (supportRelativeCohomologyToSheaf
      (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))).app (op ⊤)
      (relativeCohomologyMap ℚ (2 * (d - m))
        (topOpenNeighborhoodSupportPairIso
          (TopCat.of (ComplexPoint X)) (smoothClosedAnalyticSupport X Y i)).hom
        (smoothClosedSupportSingularClass X Y i m d))
  rw [ha, smoothClosedSupportSingularClass_normalization]

/-- A literal global raw singular cochain representing the ordinary class of the smooth closed
support.  It is selected from the resulting supported class; it is not definitionally one of the
chart winding cochains. -/
noncomputable def smoothClosedOrdinaryRawCochain :
    (globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))).X (2 * (d - m)) :=
  globalRawCochainOfSupportedSingularClass X (Set.range (Point.map i)) (2 * (d - m))
    (smoothClosedSupportSingularClass X Y i m d)

/-- The literal global raw cochain representing the smooth closed support is closed. -/
lemma smoothClosedOrdinaryRawCochain_closed :
    ((globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))).d
      (2 * (d - m)) (2 * (d - m) + 1)).hom
      (smoothClosedOrdinaryRawCochain X Y i m d) = 0 :=
  globalRawCochainOfSupportedSingularClass_closed X (Set.range (Point.map i)) (2 * (d - m))
    (smoothClosedSupportSingularClass X Y i m d)

/-- The cycle underlying the literal global raw cochain gives the class induced by the supported
normal-winding construction. -/
lemma smoothClosedOrdinaryRawCochain_class :
    ((globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))).homologyπ
      (2 * (d - m))).hom
      (HomologicalComplex.cochainCycleRepresentative
        (globalRawSingularCochainComplex ℚ (TopCat.of (ComplexPoint X))) (2 * (d - m))
        (globalRawClassOfSupportedSingularClass X (Set.range (Point.map i)) (2 * (d - m))
          (smoothClosedSupportSingularClass X Y i m d))) =
      globalRawClassOfSupportedSingularClass X (Set.range (Point.map i)) (2 * (d - m))
        (smoothClosedSupportSingularClass X Y i m d) :=
  globalRawCochainOfSupportedSingularClass_class X (Set.range (Point.map i)) (2 * (d - m))
    (smoothClosedSupportSingularClass X Y i m d)

/-- The ordinary singular class read from the literal global raw cochain. -/
noncomputable def smoothClosedOrdinarySingularClassOfRawCochain :
    Cohomology ℚ (TopCat.of (ComplexPoint X)) (2 * (d - m)) :=
  singularClassOfDisplayedGlobalRawCochain X (Set.range (Point.map i)) (2 * (d - m))
    (smoothClosedSupportSingularClass X Y i m d)

/-- Forget the support of the globally glued singular class, still on the singular side. -/
def smoothClosedOrdinarySingularClass :
    Cohomology ℚ (TopCat.of (ComplexPoint X)) (2 * (d - m)) :=
  singularClassOfSupportedSingularClass X (Set.range (Point.map i)) (2 * (d - m))
    (smoothClosedSupportSingularClass X Y i m d)

/-- The literal global raw cochain represents the ordinary singular class used for the Betti
comparison. -/
lemma smoothClosedOrdinarySingularClassOfRawCochain_eq :
    smoothClosedOrdinarySingularClassOfRawCochain X Y i m d =
      smoothClosedOrdinarySingularClass X Y i m d :=
  singularClassOfDisplayedGlobalRawCochain_eq_singularClassOfSupportedSingularClass
    X (Set.range (Point.map i)) (2 * (d - m))
    (smoothClosedSupportSingularClass X Y i m d)

/-- Finally transport the explicitly globalised singular class through the proved rational Betti
comparison to constant-sheaf hypercohomology. -/
def smoothClosedHypercohomologyClass : H^(2 * ((d - m : ℕ) : ℤ))(X; ℚ) :=
  hypercohomologyClassOfSupportedSingularClass X (Set.range (Point.map i)) (2 * (d - m))
    (smoothClosedSupportSingularClass X Y i m d)

@[simp]
lemma rationalCohomologyLinearEquivSingularCohomology_smoothClosedHypercohomologyClass :
    rationalCohomologyLinearEquivSingularCohomology X (2 * (d - m))
      (smoothClosedHypercohomologyClass X Y i m d) =
        smoothClosedOrdinarySingularClass X Y i m d := by
  exact rationalCohomologyLinearEquivSingularCohomology_hypercohomologyClassOfSupportedSingularClass
    X (Set.range (Point.map i)) (2 * (d - m))
      (smoothClosedSupportSingularClass X Y i m d)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
set_option backward.isDefEq.respectTransparency false in
/- The normalized smooth-support class is the positive-kernel image of its supported
injective class.  This is the bridge used by the canonical cycle-component comparison. -/
theorem smoothClosedHypercohomologyClass_eq_positiveKernel :
    ((show ((2 * (d - m) : ℕ) : ℤ) = 2 * ((d - m : ℕ) : ℤ) by omega).symm ▸
      smoothClosedHypercohomologyClass X Y i m d) =
      (rationalCohomologyAddEquivAmbientInjectiveHomology X
        ((2 * (d - m) : ℕ) : ℤ)).symm
        (HomologicalComplex.homologyMap
          (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex
            (TopCat.of (ComplexPoint X))
            (smoothClosedAnalyticSupport X Y i).compl ⊤
          (ambientRationalInjectiveComplex X)).f
          ((2 * (d - m) : ℕ) : ℤ)
          (smoothClosedSupportInjectiveClass X Y i m d)) := by
  have h := hypercohomologyClassOfSupportedSingularClass_eq_positiveKernel
    X (smoothClosedAnalyticSupport X Y i) (2 * (d - m))
    (smoothClosedSupportInjectiveClass X Y i m d)
  change hypercohomologyClassOfSupportedSingularClass X
    (smoothClosedAnalyticSupport X Y i : Set (ComplexPoint X)) (2 * (d - m))
    (relativeCohomologyMap ℚ (2 * (d - m))
      (topOpenNeighborhoodSupportPairIso (TopCat.of (ComplexPoint X))
        (smoothClosedAnalyticSupport X Y i)).inv
      (complexSupportInjectiveSectionCohomologyEquiv X
        (smoothClosedAnalyticSupport X Y i) ⊤ (2 * (d - m))
        (smoothClosedSupportInjectiveClass X Y i m d))) = _
  exact h

end AlgebraicGeometry.ComplexPoint
