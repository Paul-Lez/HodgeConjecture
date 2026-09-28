/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveChartFormComparison
public import Other.AlgebraicGeometry.GAGASerreReduction
public import Other.AlgebraicGeometry.AnalytificationGenerates

/-!
# The Serre-presentation obligations, specialised to `ℙᴺ`

Projective space now carries the repository's analytic structure
(`Other.ProjectiveChart.smoothOfRelativeDimension_projectiveSpaceToBase`) and is projective over
its base (`ComplexProjectiveSpace.isProjective_projectiveSpace`), so the four Serre-presentation
obligations of `GAGASerreReduction.lean` can be *stated* on `ℙᴺ` itself, with the tautological
presentation.  This file records them, together with the conditional theorem they feed, and the
one further obligation ((G2)) that the present development reduces the relation obligation to.

None of these is asserted; they are `def … : Prop` so that progress on each can be checked
independently.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint

namespace Other.ProjectiveChart

/-- Projective `N`-space as an object over `Spec ℂ`. -/
abbrev projectiveSpaceOver (N : ℕ) : Over (Spec ↧ℂ) :=
  Over.mk (ProjectiveSpace.toBase (Fin (N + 1)) (Spec ↧ℂ))

/-- The tautological projective presentation of `ℙᴺ`. -/
abbrev projPresentation (N : ℕ) :
    ProjectiveSpace.Presentation (projectiveSpaceOver N).hom :=
  ComplexProjectiveSpace.selfPresentation N

/-! ### The four obligations on `ℙᴺ` -/

/-- Analytic Serre generation on `ℙᴺ`: every finitely presented analytic module is a quotient of
a finite sum of one negative twist.  This is Cartan's Theorem A together with ampleness. -/
def SerreGenerationProj (N : ℕ) : Prop :=
  ProjectiveTwist.AnalyticSerreGeneration (projectiveSpaceOver N) N (projPresentation N)

/-- Coherence of the first relation kernel on `ℙᴺ` (Oka). -/
def TwistKernelsFiniteProj (N : ℕ) : Prop :=
  ProjectiveTwist.AnalyticTwistPresentationKernelsFinite
    (projectiveSpaceOver N) N (projPresentation N)

/-- Algebraization of relations between finite twist sums on `ℙᴺ`.  This is the `H⁰` comparison
for all twists of `𝒪_{ℙᴺ}`; the analytic and algebraic halves are now available
(`existsUnique_isHomogeneous_of_chart_growth`), and what remains is the chart dictionary
`TwistChartFramesProj` below. -/
def TwistRelationsAlgebraizeProj (N : ℕ) : Prop :=
  ProjectiveTwist.AnalyticTwistRelationsAlgebraize
    (projectiveSpaceOver N) N (projPresentation N)

/-- Reflection of invertibility for the algebraic cokernel on `ℙᴺ` (faithful flatness). -/
def TwistCokernelsReflectInvertibilityProj (N : ℕ) : Prop :=
  ProjectiveTwist.AlgebraicTwistCokernelsReflectInvertibility
    (projectiveSpaceOver N) N (projPresentation N)

/-- **(G2).** The algebraic negative twist `𝒪(−n)` on `ℙᴺ` has a generating section on each
standard homogeneous chart, and those charts are exactly the analytic chart sets of
`ProjectiveAnalytificationCharts.lean`.  Via `analytificationGenerates`, this produces analytic
frames for `𝒪(−n)^an` on the sets `complexPointChartSet i`, which is what the chart dictionary
for (G3) needs.  The algebraic half exists in
`ProjectiveSpectrumNegativeTwist.HomogeneousShift.basicOpenUnitIso`; what is missing is its
transport through the two pullbacks defining `ProjectiveTwist.algebraic`. -/
def TwistChartFramesProj (N n : ℕ) : Prop :=
  ∀ i : Fin (N + 1), ∃ (U : (projectiveSpaceOver N).left.Opens)
    (g : Γ(ProjectiveTwist.algebraic (projectiveSpaceOver N) (projPresentation N) n, U)),
    Scheme.Modules.Generates g ∧
    ((ComplexPoint.analyticOpen (projectiveSpaceOver N) U :
        Set (ComplexPoint (projectiveSpaceOver N))) =
      ComplexProjectiveSpace.complexPointChartSet i)

/-- The four obligations give line-bundle GAGA on `ℙᴺ`: every invertible analytic module on
`ℙᴺ(ℂ)^an` is the analytification of an invertible algebraic one. -/
theorem algebraizes_of_serreData_proj (N : ℕ)
    (hgenerate : SerreGenerationProj N) (hkernels : TwistKernelsFiniteProj N)
    (hrelations : TwistRelationsAlgebraizeProj N)
    (hreflect : TwistCokernelsReflectInvertibilityProj N)
    (M : SheafOfModules.{0} (holomorphicRingSheaf (projectiveSpaceOver N) N))
    (hM : TauCeti.SheafOfModules.IsInvertible M) :
    ∃ L : (projectiveSpaceOver N).left.Modules,
      TauCeti.SheafOfModules.IsInvertible L ∧
      Nonempty ((moduleAnalytification (projectiveSpaceOver N) N).obj L ≅ M) :=
  ProjectiveTwist.algebraizes_of_serreData (projectiveSpaceOver N) N (projPresentation N)
    hgenerate hkernels hrelations hreflect M hM

end Other.ProjectiveChart
