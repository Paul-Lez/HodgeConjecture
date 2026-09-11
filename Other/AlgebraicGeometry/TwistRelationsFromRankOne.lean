/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.FiniteSumHomSurjective
public import Other.AlgebraicGeometry.GAGASerreReduction

/-!
# The relation obligation reduces to rank one

`AnalyticTwistRelationsAlgebraize` asks that every morphism between finite sums of analytified
negative twists be the analytification of an algebraic one.  Because analytification is additive
and preserves the finite coproducts involved, a morphism of finite sums is a matrix of morphisms
between single twists (`Other/AlgebraicGeometry/FiniteSumHomSurjective.lean`), so the obligation
follows from its **rank-one** case.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint.ProjectiveTwist

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  (P : ProjectiveSpace.Presentation X.hom)

/-- **The rank-one relation obligation.**  Every morphism `𝒪(−a)^an ⟶ 𝒪(−b)^an` between single
analytified twists is the analytification of an algebraic morphism `𝒪(−a) ⟶ 𝒪(−b)`. -/
def AnalyticTwistRelationsAlgebraizeRankOne : Prop :=
  ∀ (a b : ℕ) (φ : analytic X d P a ⟶ analytic X d P b),
    ∃ g : algebraic X P a ⟶ algebraic X P b, (moduleAnalytification X d).map g = φ

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

local instance moduleAnalytification_additive :
    (moduleAnalytification X d).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

/-- **Rank one suffices.**  The relation obligation follows from its rank-one case. -/
theorem analyticTwistRelationsAlgebraize_of_rankOne
    (h : AnalyticTwistRelationsAlgebraizeRankOne X d P) :
    AnalyticTwistRelationsAlgebraize X d P := by
  classical
  intro relationDegree relationRank generatorDegree generatorRank f
  obtain ⟨g, hg⟩ := CategoryTheory.Limits.exists_sumMatrix_of_hom_surjective
    (moduleAnalytification X d)
    (A := algebraic X P relationDegree) (B := algebraic X P generatorDegree)
    (ι := Fin relationRank) (κ := Fin generatorRank)
    (fun φ => h relationDegree generatorDegree φ) f
  exact ⟨g, hg⟩

end AlgebraicGeometry.ComplexPoint.ProjectiveTwist
