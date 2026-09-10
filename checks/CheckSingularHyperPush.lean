import Other.AlgebraicGeometry.HypercohomologyGlobalSectionsCoherence
import Other.AlgebraicGeometry.ComplexSingularCohomologyMapNaturality

open CategoryTheory Limits TopologicalSpace Topology
namespace AlgebraicGeometry.ComplexPoint
open AlgebraicTopology
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (X : Over (Spec (.of ℂ)))
local instance : HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard _
local instance singularGE : CochainComplex.IsStrictlyGE
    (singularCochainSheafComplexInt X ℂ) 0 := by
  dsimp [singularCochainSheafComplexInt]
  infer_instance
example [IsIntegral X.left] [Smooth X.hom]
    [T2Space (ComplexPoint X)]
    [∀ U : Opens (ComplexPoint X), ParacompactSpace U]
    (f : X ⟶ X) [IsIso (analyticMapTopCat X X f)]
    (n : ℕ)
    (a : Hypercohomology X
      (((TopCat.Sheaf.pushforward AddCommGrpCat
        (analyticMapTopCat X X f)).mapHomologicalComplex
          (.up ℤ)).obj
        (singularCochainSheafComplexInt X ℂ)) (n : ℤ)) :
    pushforwardComplexSingularHypercohomologyEquivCohomology X f n a =
      complexSingularCochainHypercohomologyEquivCohomology X n
        (hypercohomologyPushforwardAddEquivOfIso X
          (asIso (analyticMapTopCat X X f))
          (singularCochainSheafComplexInt X ℂ) (n : ℤ) a) := by
  let Y := TopCat.of (ComplexPoint X)
  let K := AlgebraicTopology.Singular.globalSingularCochainSheafComplex ℂ Y
  letI : ParacompactSpace (ComplexPoint X) :=
    (Homeomorph.Set.univ (ComplexPoint X)).paracompactSpace_iff.mp
      (inferInstance : ParacompactSpace (⊤ : Opens (ComplexPoint X)))
  letI : QuasiIso
      (AlgebraicTopology.Singular.topOpenToGlobalSingularCochainSheafComplex
        ℂ Y) :=
    AlgebraicTopology.Singular.HereditarilyParacompact.topOpenToGlobalSingularCochainSheafComplex_quasiIso_complex
  rw [← normalizedComplexSingularCochainHypercohomologyEquivCohomology_eq_standard
    X n (hypercohomologyPushforwardAddEquivOfIso X
      (asIso (analyticMapTopCat X X f))
      (singularCochainSheafComplexInt X ℂ) (n : ℤ) a)]
  apply (AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
    ℂ Y n).injective
  simp only [pushforwardComplexSingularHypercohomologyEquivCohomology,
    normalizedComplexSingularCochainHypercohomologyEquivCohomology,
    Equiv.trans_apply]
  let b := pushforwardComplexSingularHypercohomologyEquivGlobalSections X f n a
  let c := normalizedComplexSingularCochainHypercohomologyEquivGlobalSections X n
    (hypercohomologyPushforwardAddEquivOfIso X
      (asIso (analyticMapTopCat X X f))
      (singularCochainSheafComplexInt X ℂ) (n : ℤ) a)
  have hb :
      (AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
        ℂ Y n)
        ((AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
          ℂ Y n).symm.toEquiv b) = b := by
    change (AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
      ℂ Y n).toEquiv
      ((AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
        ℂ Y n).toEquiv.symm b) = b
    exact (AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
      ℂ Y n).toEquiv.apply_symm_apply b
  have hc :
      (AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
        ℂ Y n)
        ((AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
          ℂ Y n).symm.toEquiv c) = c := by
    exact (AlgebraicTopology.Singular.singularCohomologyEquivGlobalSections
      ℂ Y n).toEquiv.apply_symm_apply c
  rw [hb, hc]
  dsimp [pushforwardComplexSingularHypercohomologyEquivGlobalSections,
    normalizedComplexSingularCochainHypercohomologyEquivGlobalSections, b, c]
  rw [hypercohomologyPushforwardAddEquivOfIso_globalSections_plain]
