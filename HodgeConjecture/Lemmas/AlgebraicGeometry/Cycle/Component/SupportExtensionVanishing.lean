/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HodgeConjecture.Mathlib.Algebra.Homology.Notation

public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.SupportedInjectiveModel
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SmoothSupportPurity
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Stratification.LocalSupportVanishing
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.FiniteFiltrationVanishing

/-!
# Vanishing on a cycle component's singular boundary

The finite smooth filtration of the singular boundary gives the supported Ext vanishing needed by
the localization sequence for the cycle component.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Abelian TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

include hx in
private theorem cycleComponentSingularFiltrationSectionCohomology_isZero_of_lt
    (k : ℕ) (hk : k ≤ cycleComponentSingularFiltrationLength X x)
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X))
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      (complexSupportInjectiveComplex X
        (cycleComponentSingularAnalyticClosedFiltration X x k))).homology n) := by
  let O (j : ℕ) := (cycleComponentSingularAnalyticClosedFiltration X x j).compl
  have hO : Monotone O := fun _ _ hab _ hy hyb ↦
    hy (cycleComponentSingularAnalyticClosedFiltration_antitone X x hab hyb)
  have hN : O (cycleComponentSingularFiltrationLength X x) = ⊤ := by
    dsimp only [O]
    rw [cycleComponentSingularAnalyticClosedFiltration_length]
    ext y
    change (y ∉ (∅ : Set (ComplexPoint X))) ↔ y ∈ Set.univ
    simp
  exact TopCat.Sheaf.finiteNestedSupport_homology_isZero
    (TopCat.of (ComplexPoint X)) O hO (cycleComponentSingularFiltrationLength X x) hN
    (ambientRationalInjectiveComplex X)
    (fun j => TopCat.Sheaf.injective_isFlasque _ _) n
    (fun j _ => cycleComponentSingularLayerSectionCohomology_isZero_of_lt
      X x hx j n hn) k hk

include hx in
private theorem cycleComponentSingularBoundarySectionCohomology_isZero_of_lt
    (n : ℤ) (hn : n < 2 * ((p : ℤ) + 1)) :
    IsZero ((((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X))
      ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      (complexSupportInjectiveComplex X
        (cycleComponentSingularAnalyticClosedFiltration X x 0))).homology n) :=
  cycleComponentSingularFiltrationSectionCohomology_isZero_of_lt X x hx
    0 (Nat.zero_le _) n hn

include hx in
/-- The singular-boundary supported Ext groups vanish below degree `2(p + 1)`. -/
theorem cycleComponentSingularBoundaryRelH_isZero_of_lt (n : ℕ)
    (hn : (n : ℤ) < 2 * ((p : ℤ) + 1)) :
    IsZero (AddCommGrpCat.of
      (CategoryTheory.Sheaf.relH
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
        n
        (homOfLE (show cycleComponentSmoothSupportAmbientOpen X x ≤
          (⊤ : Opens (TopCat.of (ComplexPoint X))) from le_top)))) := by
  let T := TopCat.of (ComplexPoint X)
  let Z := cycleComponentSingularAnalyticClosedFiltration X x 0
  let e := rationalSupportAddEquivSupportedInjectiveHomology X Z n
  let hcomplex : IsZero ((((TopCat.Sheaf.supportEvaluation T ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      (complexSupportInjectiveComplex X Z)).homology (n : ℤ)) := by
    simpa [Z] using cycleComponentSingularBoundarySectionCohomology_isZero_of_lt
      X x hx (n : ℤ) hn
  let : Subsingleton ((((TopCat.Sheaf.supportEvaluation T ⊤).mapHomologicalComplex ℤᵘᵖ).obj
      (complexSupportInjectiveComplex X Z)).homology (n : ℤ)) :=
    AddCommGrpCat.subsingleton_of_isZero hcomplex
  let : Subsingleton (TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X))
      (cycleComponentSingularAnalyticClosedFiltration X x 0)
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ)) n) :=
    e.injective.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

end AlgebraicGeometry.ComplexPoint
