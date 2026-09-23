/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticLineBundleFiniteAtlas
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# The analytic Serre-generation interface

This file packages the precise hard analytic input needed by the finite-presentation route to
line-bundle GAGA.  Relative to a projective presentation, an analytic module is Serre-generated
if it is a quotient of a finite coproduct of one negative twist.  The property is stable under
quotients, and analytification identifies the algebraic and analytic finite twist sums.

The assertion that every finitely presented analytic module is Serre-generated is recorded as
`AnalyticSerreGeneration`; proving it is the remaining analytic theorem, not a consequence of
the categorical constructions in this file.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint.ProjectiveTwist

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/-- A finite algebraic sum of one presentation-induced negative twist. -/
def algebraicSum (P : ProjectiveSpace.Presentation X.hom) (n r : ℕ) : X.left.Modules :=
  ∐ fun _ : Fin r ↦ algebraic X P n

/-- The corresponding finite analytic sum of the analytified negative twist. -/
def analyticSum (P : ProjectiveSpace.Presentation X.hom) (n r : ℕ) :
    SheafOfModules (holomorphicRingSheaf X d) :=
  ∐ fun _ : Fin r ↦ analytic X d P n

/-- Analytification commutes with a finite sum of presentation-induced twists. -/
def sumAnalytificationIso (P : ProjectiveSpace.Presentation X.hom) (n r : ℕ) :
    (moduleAnalytification X d).obj (algebraicSum X P n r) ≅ analyticSum X d P n r :=
  PreservesCoproduct.iso (moduleAnalytification X d) (fun _ : Fin r ↦ algebraic X P n)

/-- An analytic module is generated in a Serre degree if it is an epimorphic image of a finite
sum of one presentation-induced negative twist. -/
def IsSerreGenerated (P : ProjectiveSpace.Presentation X.hom)
    (F : SheafOfModules (holomorphicRingSheaf X d)) : Prop :=
  ∃ (n r : ℕ), ∃ p : analyticSum X d P n r ⟶ F, Epi p

/-- A finite sum of a twist is Serre-generated, using its identity map. -/
theorem isSerreGenerated_analyticSum (P : ProjectiveSpace.Presentation X.hom) (n r : ℕ) :
    IsSerreGenerated X d P (analyticSum X d P n r) := by
  exact ⟨n, r, 𝟙 _, inferInstance⟩

/-- Serre generation is invariant under isomorphism. -/
theorem IsSerreGenerated.of_iso (P : ProjectiveSpace.Presentation X.hom)
    {F G : SheafOfModules (holomorphicRingSheaf X d)}
    (hF : IsSerreGenerated X d P F) (e : F ≅ G) : IsSerreGenerated X d P G := by
  obtain ⟨n, r, p, hp⟩ := hF
  let _ : Epi p := hp
  exact ⟨n, r, p ≫ e.hom, inferInstance⟩

/-- A quotient of a Serre-generated module is Serre-generated. -/
theorem IsSerreGenerated.of_epi (P : ProjectiveSpace.Presentation X.hom)
    {F G : SheafOfModules (holomorphicRingSheaf X d)}
    (hF : IsSerreGenerated X d P F) (q : F ⟶ G) [Epi q] :
    IsSerreGenerated X d P G := by
  obtain ⟨n, r, p, hp⟩ := hF
  let _ : Epi p := hp
  exact ⟨n, r, p ≫ q, inferInstance⟩

/-- Analytic Serre global generation for the chosen projective presentation: every finitely
presented analytic module is a quotient of finitely many copies of a sufficiently negative
twist.  This is the exact hard analytic input required twice in a two-term GAGA presentation. -/
def AnalyticSerreGeneration (P : ProjectiveSpace.Presentation X.hom) : Prop :=
  ∀ (F : SheafOfModules.{0} (holomorphicRingSheaf X d)),
    F.IsFinitePresentation → IsSerreGenerated X d P F

/-- Unpacked form of analytic Serre generation. -/
theorem exists_epi_finiteCoproduct_projectiveTwist
    (P : ProjectiveSpace.Presentation X.hom) (h : AnalyticSerreGeneration X d P)
    (F : SheafOfModules.{0} (holomorphicRingSheaf X d))
    (hF : F.IsFinitePresentation) :
    ∃ (n r : ℕ), ∃ p : (∐ fun _ : Fin r ↦ analytic X d P n) ⟶ F, Epi p :=
  h F hF

end AlgebraicGeometry.ComplexPoint.ProjectiveTwist
