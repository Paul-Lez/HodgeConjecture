/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveSpectrumTwistMultiply
public import Other.AlgebraicGeometry.ProjectiveChartMultiplierGrowth
public import Other.AlgebraicGeometry.PullbackSectionNaturality

/-!
# Multiplication morphisms of twists on `ℙᴺ`, and their chart multipliers

Inverse image along `toUniversalProj` and the (identity) immersion carries multiplication by a
homogeneous element `G` of degree `k` to a morphism `𝒪(−(b+k)) ⟶ 𝒪(−b)` on `ℙᴺ`.  Because the
frames of `ProjectiveTwistCanonicalFrames.lean` are canonical inverse images, the frame identity
of `multiplyShiftHom_projFrame` transports verbatim, and analytification turns it into the
statement that the chart multiplier of the analytified morphism is the evaluation of `G / Xᵢᵏ`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ProjectiveSpectrum.NegativeTwist

namespace AlgebraicGeometry.ComplexProjectiveSpace

open ComplexPoint Other.ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (N b k : ℕ) (G : UniversalGrading N k) (i : Fin (N + 1))

set_option backward.isDefEq.respectTransparency false in
/-- **Multiplication on the universal frames over `D₊(Xᵢ)`.** -/
theorem multiplyShiftHom_universalChartFrame :
    (schemeMultiplyShiftHom (UniversalGrading N) G b).app
        (ProjectiveSpectrum.basicOpen (UniversalGrading N) (MvPolynomial.X i) :
          (Proj (UniversalGrading N)).Opens)
        (Scheme.Modules.resSection (schemeSheafOfModules (UniversalGrading N) (b + k))
          (basicOpen_le_pow N (b + k) (MvPolynomial.X i)) (universalChartFrame N (b + k) i)) =
      universalRatioBig N k G i •
        Scheme.Modules.resSection (schemeSheafOfModules (UniversalGrading N) b)
          (basicOpen_le_pow N b (MvPolynomial.X i)) (universalChartFrame N b i) := by
  refine multiplyShiftHom_projFrame (UniversalGrading N) G (coordPower N k i) (coordPower N b i)
    (coordPower N (b + k) i) ?_ _ _ _ _
  show (MvPolynomial.X i : UniversalRing N) ^ (b + k) =
    (MvPolynomial.X i : UniversalRing N) ^ k * (MvPolynomial.X i : UniversalRing N) ^ b
  rw [← pow_add]
  congr 1
  omega

/-- **Multiplication by a homogeneous element, transported to `ℙᴺ`.** -/
def algMulHom :
    ComplexPoint.ProjectiveTwist.algebraic (projectiveSpaceOver N) (projPresentation N) (b + k) ⟶
      ComplexPoint.ProjectiveTwist.algebraic (projectiveSpaceOver N) (projPresentation N) b :=
  (Scheme.Modules.pullback (projPresentation N).immersion).map
    ((Scheme.Modules.pullback (toUniversalProj N)).map
      (schemeMultiplyShiftHom (UniversalGrading N) G b))

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The algebraic frame identity on `ℙᴺ`.** -/
theorem algMulHom_algChartFrame :
    (algMulHom N b k G).app (projectiveSpaceBasicOpen N (MvPolynomial.X i))
        (algChartFrame N (b + k) i) =
      spaceRatioBig N k G i • algChartFrame N b i := by
  have h1 := congrArg
    (Scheme.Modules.pullbackSection (toUniversalProj N) (schemeSheafOfModules (UniversalGrading N) b)
      (ProjectiveSpectrum.basicOpen (UniversalGrading N) (MvPolynomial.X i) :
        (Proj (UniversalGrading N)).Opens))
    (multiplyShiftHom_universalChartFrame N b k G i)
  rw [Scheme.Modules.pullbackSection_map, Scheme.Modules.pullbackSection_smul,
    Scheme.Modules.pullbackSection_res, Scheme.Modules.pullbackSection_res] at h1
  have h2 := congrArg
    (Scheme.Modules.pullbackSection (projPresentation N).immersion
      ((Scheme.Modules.pullback (toUniversalProj N)).obj
        (schemeSheafOfModules (UniversalGrading N) b))
      (toUniversalProj N ⁻¹ᵁ (ProjectiveSpectrum.basicOpen (UniversalGrading N) (MvPolynomial.X i) :
        (Proj (UniversalGrading N)).Opens)))
    h1
  rw [Scheme.Modules.pullbackSection_map, Scheme.Modules.pullbackSection_smul,
    Scheme.Modules.pullbackSection_res, Scheme.Modules.pullbackSection_res] at h2
  exact h2

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The analytic chart multiplier of a multiplication morphism.** -/
theorem analytified_algMulHom_anChartFrame :
    ((moduleAnalytification (projectiveSpaceOver N) N).map (algMulHom N b k G)).val.app
        (op (chartOpen N i)) (anChartFrame N (b + k) i) =
      ComplexPoint.analyticFunction (projectiveSpaceOver N) N
          (projectiveSpaceBasicOpen N (MvPolynomial.X i)) (spaceRatioBig N k G i) •
        anChartFrame N b i := by
  have h := congrArg
    (ComplexPoint.analyticSection (projectiveSpaceOver N) N
      (ComplexPoint.ProjectiveTwist.algebraic (projectiveSpaceOver N) (projPresentation N) b)
      (projectiveSpaceBasicOpen N (MvPolynomial.X i)))
    (algMulHom_algChartFrame N b k G i)
  rw [ComplexPoint.analyticSection_map, ComplexPoint.analyticSection_smul] at h
  exact h

end AlgebraicGeometry.ComplexProjectiveSpace
