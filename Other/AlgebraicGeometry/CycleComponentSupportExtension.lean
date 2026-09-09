/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SingularFiltrationLocalSupportVanishing
public import Other.AlgebraicGeometry.CycleComponentSmoothSupportPurity
public import Other.AlgebraicTopology.FiniteSheafSupportVanishing

/-!
# Actual unique extension across a cycle component's singular boundary

The canonical finite smooth filtration and its proved layerwise vanishing
show that the singular boundary has zero supported cohomology below
`2(p+1)`. In particular the two degrees `2p` and `2p+1` vanish. The actual
nested-support localization sequence then makes restriction from the full
component support to its smooth-locus ambient open an isomorphism in degree
`2p`. The inverse is therefore an actual unique extension operation, not
an existence or duality assumption.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable {X : Scheme} (s : X ⟶ Spec (.of ℂ))
  [IsIntegral X] [Smooth s] [IsProjective s] (x : X)
  {d p : ℕ} [SmoothOfRelativeDimension d s] (hx : Order.coheight x = p)

local instance cycleComponentSupportExtensionAnalyticTopology :
    TopologicalSpace (ComplexPoint X s) := Point.analyticTopology

include d hx in
/-- Every actual closed remainder in the finite singular filtration has
vanishing supported section-complex cohomology below `2(p+1)`. -/
theorem cycleComponentSingularFiltrationSectionCohomology_isZero_of_lt
    (k : ℕ) (hk : k ≤ cycleComponentSingularFiltrationLength s x)
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex s
        (cycleComponentSingularAnalyticClosedFiltration s x k))).homology n) := by
  let O (j : ℕ) := (cycleComponentSingularAnalyticClosedFiltration s x j).compl
  have hO : Monotone O := by
    intro a b hab y hy hyb
    exact hy (cycleComponentSingularAnalyticClosedFiltration_antitone s x hab hyb)
  have hN : O (cycleComponentSingularFiltrationLength s x) = ⊤ := by
    dsimp only [O]
    rw [cycleComponentSingularAnalyticClosedFiltration_length]
    ext y
    change (y ∉ (∅ : Set (ComplexPoint X s))) ↔ y ∈ Set.univ
    simp
  exact TopCat.Sheaf.finiteNestedSupport_homology_isZero
    (TopCat.of (ComplexPoint X s)) O hO (cycleComponentSingularFiltrationLength s x) hN
    (ambientRationalInjectiveComplex s)
    (fun j => TopCat.Sheaf.injective_isFlasque _ _) n
    (fun j _ => cycleComponentSingularLayerSectionCohomology_isZero_of_lt
      s x (d := d) hx j n hn) k hk

include d hx in
/-- The actual singular boundary has the required lower supported
cohomological bound. All geometric and finite-filtration inputs are proved. -/
theorem cycleComponentSingularBoundarySectionCohomology_isZero_of_lt
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex s
        (cycleComponentSingularAnalyticClosedFiltration s x 0))).homology n) :=
  cycleComponentSingularFiltrationSectionCohomology_isZero_of_lt s x (d := d) hx
    0 (Nat.zero_le _) n hn

include d hx in
theorem cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex s
        (cycleComponentSingularAnalyticClosedFiltration s x 0))).homology (2 * (p : ℤ))) :=
  cycleComponentSingularBoundarySectionCohomology_isZero_of_lt s x (d := d) hx _ (by omega)

include d hx in
theorem cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree_succ :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex s
        (cycleComponentSingularAnalyticClosedFiltration s x 0))).homology (2 * (p : ℤ) + 1)) :=
  cycleComponentSingularBoundarySectionCohomology_isZero_of_lt s x (d := d) hx _ (by omega)

/-- Every point of the singular boundary belongs to the full component support. -/
theorem cycleComponentSingularBoundary_le_support :
    cycleComponentSingularAnalyticClosedFiltration s x 0 ≤ cycleComponentAnalyticClosedSupport s x := by
  intro y hy
  obtain ⟨z, _, hz⟩ := hy
  change y.underlying ∈ closure ({x} : Set X)
  rw [← range_cycleComponentι X x]
  exact ⟨z, hz⟩

/-- The actual complement inclusion determining the localization sequence. -/
theorem cycleComponentSupportComplement_le_smoothAmbientOpen :
    (cycleComponentAnalyticClosedSupport s x).compl ≤ cycleComponentSmoothSupportAmbientOpen s x := by
  intro y hy hyS
  exact hy (cycleComponentSingularBoundary_le_support s x hyS)

/-- Restriction of the original supported injective section complex to the
actual smooth-locus ambient open. -/
def cycleComponentSupportSectionRestriction :
    ((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex s (cycleComponentAnalyticClosedSupport s x)) ⟶
    ((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s))
      (cycleComponentSmoothSupportAmbientOpen s x)).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex s (cycleComponentAnalyticClosedSupport s x)) :=
  TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X s)) (.up ℤ)
    (complexSupportInjectiveComplex s (cycleComponentAnalyticClosedSupport s x)) (homOfLE le_top)

include d hx in
/-- The actual restriction map is an isomorphism in cycle degree, by the
two proved boundary vanishings and the actual localization sequence. -/
theorem cycleComponentSupportSectionRestriction_homology_isIso :
    IsIso (HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction s x) (2 * (p : ℤ))) := by
  let T := TopCat.of (ComplexPoint X s)
  let h := cycleComponentSupportComplement_le_smoothAmbientOpen s x
  let K := ambientRationalInjectiveComplex s
  let S := TopCat.Sheaf.nestedSupportRestrictionSectionsComplexShortComplex T h ⊤ K
  let := TopCat.Sheaf.nestedSupportRestriction_homologyMap_isIso_of_vanishing T h ⊤ K
    (2 * (p : ℤ))
    (cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree s x (d := d) hx)
    (cycleComponentSingularBoundarySectionCohomology_isZero_cycleDegree_succ s x (d := d) hx)
  have he : HomologicalComplex.homologyMap S.g (2 * (p : ℤ)) ≫
      HomologicalComplex.homologyMap
        (TopCat.Sheaf.nestedSupportRestrictionLastComplexIso T h K).hom (2 * (p : ℤ)) =
    HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction s x) (2 * (p : ℤ)) := by
    rw [← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun f => HomologicalComplex.homologyMap f (2 * (p : ℤ)))
      (TopCat.Sheaf.nestedSupportRestrictionLastComplexIso_g T h K)
  rw [← he]
  infer_instance

/-- The extension equivalence is the actual restriction map with its proved
inverse. It has no boundary-vanishing or fundamental-class input. -/
def cycleComponentSupportExtensionIso :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex s
        (cycleComponentAnalyticClosedSupport s x))).homology (2 * (p : ℤ))) ≅
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X s))
      (cycleComponentSmoothSupportAmbientOpen s x)).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex s (cycleComponentAnalyticClosedSupport s x))).homology
          (2 * (p : ℤ))) := by
  let := cycleComponentSupportSectionRestriction_homology_isIso s x (d := d) hx
  exact asIso (HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction s x) (2 * (p : ℤ)))

@[simp]
theorem cycleComponentSupportExtensionIso_hom :
    (cycleComponentSupportExtensionIso s x (d := d) hx).hom =
      HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction s x) (2 * (p : ℤ)) := rfl

end AlgebraicGeometry.ComplexPoint
