/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalytificationReflectsInvertible
public import Other.AlgebraicGeometry.GAGACoherentStatement
public import Other.AlgebraicGeometry.GAGAtoLefschetz
public import Other.AlgebraicGeometry.HolomorphicAnalyticSpace
public import Other.AlgebraicGeometry.InvertibleSheafCoherent

/-!
# Reduction of line-bundle GAGA to coherent GAGA

Coherent-sheaf algebraization gives line-bundle algebraization once the holomorphic structure
sheaf is coherent and analytification is faithfully flat on stalks.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

omit [IsProjective X.hom] in
/-- Coherent GAGA and faithfully flat stalk comparison imply line-bundle GAGA. -/
theorem analyticLineBundlesAlgebraize_of_coherent
    (hGAGA : AnalyticCoherentSheavesAlgebraize X)
    (hff : ∀ z : ComplexPoint X,
      ((analytificationToPresheafedSpace X (dim X.left)).stalkMap z).hom.FaithfullyFlat) :
    AnalyticLineBundlesAlgebraize X := by
  intro M hM
  let Y := holomorphicLocallyRingedSpace X (dim X.left)
  have hOY : (SheafOfModules.unit Y.ringSheaf).IsCoherent :=
    holomorphicLocallyRingedSpace_isCoherentStructureSheaf X (dim X.left)
  have hMY : TauCeti.SheafOfModules.IsInvertible
      (show SheafOfModules.{0} Y.ringSheaf from M) := hM
  have hMcoherent : M.IsCoherent :=
    @AlgebraicGeometry.LocallyRingedSpace.isCoherent_of_isInvertible
      Y (show SheafOfModules.{0} Y.ringSheaf from M) hOY hMY
  obtain ⟨F, hF, ⟨eFM⟩⟩ := hGAGA M hMcoherent
  let : F.IsCoherent := hF
  exact ⟨F, algebraic_isInvertible_of_analytificationIso
    X (dim X.left) F M hff eFM hM, ⟨eFM⟩⟩

/-- The rational Lefschetz `(1, 1)` theorem follows from coherent GAGA and faithfully flat
analytification maps on stalks. -/
theorem _root_.RationalLefschetzOneOne.of_coherentGAGA
    (hGAGA : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
      [IsProjective X.hom], AnalyticCoherentSheavesAlgebraize X)
    (hff : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
      [IsProjective X.hom] (z : ComplexPoint X),
      ((analytificationToPresheafedSpace X (dim X.left)).stalkMap z).hom.FaithfullyFlat) :
    RationalLefschetzOneOne :=
  RationalLefschetzOneOne.of_analyticLineBundlesAlgebraize fun X ↦
    analyticLineBundlesAlgebraize_of_coherent X (hGAGA X) (hff X)

end AlgebraicGeometry.ComplexPoint
