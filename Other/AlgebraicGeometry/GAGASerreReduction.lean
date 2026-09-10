/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.GAGATwistPresentation
public import Other.AlgebraicGeometry.GAGALineBundles
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Reduction of line-bundle GAGA to the three Serre-presentation inputs

This file completes the formal categorical reduction suggested by the classical proof of GAGA.
Once finite analytic Serre generation, coherence of the first relation kernel, algebraization of
maps between finite twist sums, and reflection of rank one are available, an arbitrary analytic
line bundle acquires a two-term algebraic twist presentation.  Its algebraic model is the
cokernel of the algebraic relation.

The propositions below deliberately expose the remaining mathematical inputs; none is asserted
as an axiom.  In particular, the final theorem is conditional and does not by itself prove the
unconditional GAGA target.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint.ProjectiveTwist

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  (P : ProjectiveSpace.Presentation X.hom)

/-- Coherence in precisely the form needed after choosing the first Serre presentation: the
kernel of its epimorphism is again finitely presented. -/
def AnalyticTwistPresentationKernelsFinite : Prop :=
  ∀ (M : SheafOfModules.{0} (holomorphicRingSheaf X d)) (n r : ℕ)
    (p : analyticSum X d P n r ⟶ M), Epi p → M.IsFinitePresentation →
      (kernel p).IsFinitePresentation

/-- Fullness of analytification on the finite negative-twist sums used for generators and
relations. -/
def AnalyticTwistRelationsAlgebraize : Prop :=
  ∀ (relationDegree relationRank generatorDegree generatorRank : ℕ)
    (f : analyticSum X d P relationDegree relationRank ⟶
      analyticSum X d P generatorDegree generatorRank),
    ∃ g : algebraicSum X P relationDegree relationRank ⟶
        algebraicSum X P generatorDegree generatorRank,
      analyticRelation X d P g = f

/-- Reflection of rank one for the algebraic cokernels produced by a two-term twist
presentation.  A stalkwise proof would follow from the missing faithfully-flat comparison
between algebraic and holomorphic local rings. -/
def AlgebraicTwistCokernelsReflectInvertibility : Prop :=
  ∀ (M : SheafOfModules.{0} (holomorphicRingSheaf X d)),
    TauCeti.SheafOfModules.IsInvertible M →
      ∀ Q : AlgebraicTwistPresentation X d P M,
        TauCeti.SheafOfModules.IsInvertible Q.algebraicModel

/-- The first presentation epimorphism is a cokernel of any epimorphic set of generators for
its kernel. -/
def epiIsCokernelOfKernelGenerators
    {M : SheafOfModules.{0} (holomorphicRingSheaf X d)}
    {generatorDegree generatorRank relationDegree relationRank : ℕ}
    (p : analyticSum X d P generatorDegree generatorRank ⟶ M) [Epi p]
    (q : analyticSum X d P relationDegree relationRank ⟶ kernel p) [Epi q] :
    IsColimit (CokernelCofork.ofπ p (by simp) :
      CokernelCofork (q ≫ kernel.ι p)) :=
  isCokernelEpiComp
    (Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι p) (kernel.condition p))
      (kernelIsKernel p)) q rfl

/-- The four genuine Serre-presentation inputs construct an algebraic two-term presentation of
any invertible analytic module. -/
theorem exists_algebraicTwistPresentationOfSerreData
    (hgenerate : AnalyticSerreGeneration X d P)
    (hkernels : AnalyticTwistPresentationKernelsFinite X d P)
    (hrelations : AnalyticTwistRelationsAlgebraize X d P)
    (M : SheafOfModules.{0} (holomorphicRingSheaf X d))
    (hM : TauCeti.SheafOfModules.IsInvertible M) :
    Nonempty (AlgebraicTwistPresentation X d P M) := by
  have hMfinite : M.IsFinitePresentation := by
    let : TauCeti.SheafOfModules.IsInvertible M := hM
    infer_instance
  obtain ⟨generatorDegree, generatorRank, p, hp⟩ := hgenerate M hMfinite
  let _ : Epi p := hp
  have hKfinite : (kernel p).IsFinitePresentation :=
    hkernels M generatorDegree generatorRank p hp hMfinite
  obtain ⟨relationDegree, relationRank, q, hq⟩ := hgenerate (kernel p) hKfinite
  let _ : Epi q := hq
  obtain ⟨relation, hrelation⟩ :=
    hrelations relationDegree relationRank generatorDegree generatorRank (q ≫ kernel.ι p)
  exact ⟨
    { relationDegree := relationDegree
      relationRank := relationRank
      generatorDegree := generatorDegree
      generatorRank := generatorRank
      relation := relation
      projection := p
      zero := by rw [hrelation]; simp
      isCokernel := by
        apply CokernelCofork.isColimitOfIsColimitOfIff'
          (epiIsCokernelOfKernelGenerators X d P p q)
        intro W φ
        rw [hrelation] }⟩

/-- Conditional line-bundle GAGA in a fixed relative dimension. -/
theorem algebraizes_of_serreData
    (hgenerate : AnalyticSerreGeneration X d P)
    (hkernels : AnalyticTwistPresentationKernelsFinite X d P)
    (hrelations : AnalyticTwistRelationsAlgebraize X d P)
    (hreflect : AlgebraicTwistCokernelsReflectInvertibility X d P)
    (M : SheafOfModules.{0} (holomorphicRingSheaf X d))
    (hM : TauCeti.SheafOfModules.IsInvertible M) :
    ∃ L : X.left.Modules, TauCeti.SheafOfModules.IsInvertible L ∧
      Nonempty ((moduleAnalytification X d).obj L ≅ M) := by
  obtain ⟨Q⟩ :=
    exists_algebraicTwistPresentationOfSerreData X d P hgenerate hkernels hrelations M hM
  exact Q.algebraizes (hreflect M hM Q)

end AlgebraicGeometry.ComplexPoint.ProjectiveTwist

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The exact GAGA target follows once the four remaining Serre-presentation inputs have been
proved for one projective presentation. -/
theorem analyticLineBundlesAlgebraize_of_serreData
    (P : ProjectiveSpace.Presentation X.hom)
    (hgenerate : ProjectiveTwist.AnalyticSerreGeneration X (dim X.left) P)
    (hkernels : ProjectiveTwist.AnalyticTwistPresentationKernelsFinite X (dim X.left) P)
    (hrelations : ProjectiveTwist.AnalyticTwistRelationsAlgebraize X (dim X.left) P)
    (hreflect : ProjectiveTwist.AlgebraicTwistCokernelsReflectInvertibility
      X (dim X.left) P) :
    AnalyticLineBundlesAlgebraize X := by
  intro M hM
  exact ProjectiveTwist.algebraizes_of_serreData X (dim X.left) P hgenerate hkernels
    hrelations hreflect M hM

end AlgebraicGeometry.ComplexPoint
