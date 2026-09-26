/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.GAGACoherentReduction
public import Other.AlgebraicGeometry.HolomorphicAnalytificationLocalIso
public import Other.Oka.Analytification.GAGA.Proper.Equivalence
public import Other.Oka.Analytification.GAGA.SheafAnalytification
public import Other.Oka.AnalyticSpace.PullbackCoherent

/-! Proper GAGA and the rational Lefschetz `(1, 1)` theorem. -/

open CategoryTheory AlgebraicGeometry

universe u

@[expose] public noncomputable section

namespace ComplexAnalytic

open AnalyticSpace

/-- Coherent-sheaf algebraization transports from the canonical analytification to any
analytification of the same scheme. -/
theorem coherent_algebraizes_of_isAnalytification
    (X : SchemeLFTℂ.{u})
    {W : AnalyticSpace.{u}}
    {π : AnalyticSpace.toOverSpec.obj W ⟶ schemeToOverSpec.obj X.obj}
    (hπ : IsAnalytification π)
    (hGAGA :
      ∀ N : SheafOfModules.{u}
          (analytification.obj X).toLocallyRingedSpace.ringSheaf,
        N.IsCoherent →
          ∃ F : SheafOfModules.{u}
              X.obj.left.toLocallyRingedSpace.ringSheaf,
            F.IsCoherent ∧
              Nonempty ((analytificationModules X).obj F ≅ N))
    (M : SheafOfModules.{u} W.toLocallyRingedSpace.ringSheaf)
    (hM : M.IsCoherent) :
    ∃ F : SheafOfModules.{u}
        X.obj.left.toLocallyRingedSpace.ringSheaf,
      F.IsCoherent ∧ Nonempty (π.left.pullbackModules.obj F ≅ M) := by
  let hcan := isAnalytification_analytificationπ X
  let I := hπ.isoOfIsAnalytification hcan
  let IL := AnalyticSpace.forgetToLocallyRingedSpace.mapIso I
  let N := IL.inv.pullbackModules.obj M
  have hN : N.IsCoherent := by
    exact @isCoherent_pullbackModules_of_isCoherent _ _ IL.inv M hM
  obtain ⟨F, hF, ⟨eF⟩⟩ := hGAGA N hN
  refine ⟨F, hF, ⟨?_⟩⟩
  have hI : IL.hom ≫ analytificationπLRS X = π.left := by
    have hI' := congrArg CommaMorphism.left
      (IsAnalytification.isoOfIsAnalytification_hom_comp hπ hcan)
    exact hI'
  let eπ : π.left.pullbackModules.obj F ≅
      IL.hom.pullbackModules.obj ((analytificationModules X).obj F) :=
    (LocallyRingedSpace.Hom.pullbackModulesCongr hI.symm).app F ≪≫
      ((LocallyRingedSpace.Hom.pullbackModulesComp
        IL.hom (analytificationπLRS X)).app F).symm
  let eI : IL.hom.pullbackModules.obj
      (IL.inv.pullbackModules.obj M) ≅ M :=
    (LocallyRingedSpace.Hom.pullbackModulesComp IL.hom IL.inv).app M ≪≫
      (LocallyRingedSpace.Hom.pullbackModulesCongr IL.hom_inv_id).app M ≪≫
      (SheafOfModules.pullbackId W.toLocallyRingedSpace.ringSheaf).app M
  exact eπ ≪≫ IL.hom.pullbackModules.mapIso eF ≪≫ eI

end ComplexAnalytic

namespace AlgebraicGeometry.ComplexPoint

open TopologicalSpace

/-- Proper GAGA algebraizes coherent sheaves on the project-specific holomorphic model. -/
theorem analyticCoherentSheavesAlgebraize
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    AnalyticCoherentSheavesAlgebraize X := by
  intro M hM
  refine ComplexAnalytic.coherent_algebraizes_of_isAnalytification
    (toSchemeLFTℂ X (dim X.left))
    (holomorphicAnalytificationπ_isAnalytification X (dim X.left))
    ?_ M hM
  intro N hN
  exact @ComplexAnalytic.gaga₃_proper
    (toSchemeLFTℂ X (dim X.left))
    (toSchemeLFTℂ_isProper X (dim X.left)) N hN

/-- Proper GAGA algebraizes holomorphic line bundles on smooth projective complex varieties. -/
theorem analyticLineBundlesAlgebraize
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    AnalyticLineBundlesAlgebraize X :=
  analyticLineBundlesAlgebraize_of_coherent X
    (analyticCoherentSheavesAlgebraize X) fun z ↦
      faithfullyFlat_stalkMap_holomorphicAnalytificationπ X (dim X.left) z

/-- The rational Lefschetz `(1, 1)` theorem. -/
theorem _root_.rationalLefschetzOneOne : RationalLefschetzOneOne := by
  exact RationalLefschetzOneOne.of_analyticLineBundlesAlgebraize fun X ↦
    analyticLineBundlesAlgebraize X

/-- The Lefschetz `(1, 1)` theorem in the repository's named formulation. -/
theorem _root_.lefschetzOneOne : LefschetzOneOne :=
  rationalLefschetzOneOne.to_lefschetzOneOne

end AlgebraicGeometry.ComplexPoint

end
