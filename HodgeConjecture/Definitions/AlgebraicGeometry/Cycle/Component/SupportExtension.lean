/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.LocalSupportVanishing
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.FiniteFiltrationVanishing
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.NestedOnOpen

/-!
# Unique extension across a cycle component's singular boundary

The finite smooth filtration gives vanishing below `2(p+1)` on the singular boundary.
The localization sequence then makes restriction to the smooth-locus ambient open an
isomorphism in degree `2p`. Its inverse is the unique extension operation.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

include hx in
/-- Every actual closed remainder in the finite singular filtration has
vanishing supported section-complex cohomology below `2(p+1)`. -/
private theorem cycleComponentSingularFiltrationSectionCohomology_isZero_of_lt
    (k : ℕ) (hk : k ≤ cycleComponentSingularFiltrationLength X x)
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentSingularAnalyticClosedFiltration X x k))).homology n) := by
  let O (j : ℕ) := (cycleComponentSingularAnalyticClosedFiltration X x j).compl
  have hO : Monotone O := fun _ _ hab _ hy hyb ↦
    hy (cycleComponentSingularAnalyticClosedFiltration_antitone X x hab hyb)
  have hN : O (cycleComponentSingularFiltrationLength X x) = ⊤ := by
    ext y
    simp [O, cycleComponentSingularAnalyticClosedFiltration_length]
  exact TopCat.Sheaf.finiteNestedSupport_homology_isZero
    (TopCat.of (ComplexPoint X)) O hO (cycleComponentSingularFiltrationLength X x) hN
    (ambientRationalInjectiveComplex X)
    (fun j => TopCat.Sheaf.injective_isFlasque _ _) n
    (fun j _ => cycleComponentSingularLayerSectionCohomology_isZero_of_lt
      X x hx j n hn) k hk

include hx in
/-- Supported cohomology of the singular boundary vanishes below `2(p+1)`. -/
theorem cycleComponentSingularBoundarySectionCohomology_isZero_of_lt
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentSingularAnalyticClosedFiltration X x 0))).homology n) :=
  cycleComponentSingularFiltrationSectionCohomology_isZero_of_lt X x hx
    0 (Nat.zero_le _) n hn

/-- Restriction of the original supported injective section complex to the
actual smooth-locus ambient open. -/
def cycleComponentSupportSectionRestriction :
    ((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)) ⟶
    ((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (cycleComponentSmoothSupportAmbientOpen X x)).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)) :=
  TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) (.up ℤ)
    (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x)) (homOfLE le_top)

/-- The extension equivalence is the actual restriction map with its proved
inverse. It has no boundary-vanishing or fundamental-class input. -/
def cycleComponentSupportExtensionIso :
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      (.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentAnalyticClosedSupport X x))).homology (2 * (p : ℤ))) ≅
    ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (cycleComponentSmoothSupportAmbientOpen X x)).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))).homology
          (2 * (p : ℤ))) :=
  TopCat.Sheaf.nestedSupportSectionRestrictionHomologyIsoOfVanishing
    (TopCat.of (ComplexPoint X))
    (U := cycleComponentSmoothSupportAmbientOpen X x)
    (V := (cycleComponentAnalyticClosedSupport X x).compl)
    (fun y hy hyS => hy (by
      obtain ⟨z, _, hz⟩ := hyS
      change y.underlying ∈ closure ({x} : Set X.left)
      rw [← range_cycleComponentι X.left x]
      exact ⟨z, hz⟩))
    (ambientRationalInjectiveComplex X) (2 * (p : ℤ))
    (cycleComponentSingularBoundarySectionCohomology_isZero_of_lt X x hx _ (by omega))
    (cycleComponentSingularBoundarySectionCohomology_isZero_of_lt X x hx _ (by omega))

@[simp]
theorem cycleComponentSupportExtensionIso_hom :
    (cycleComponentSupportExtensionIso X x hx).hom =
      HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x)
        (2 * (p : ℤ)) := by
  apply TopCat.Sheaf.nestedSupportSectionRestrictionHomologyIsoOfVanishing_hom

end AlgebraicGeometry.ComplexPoint
