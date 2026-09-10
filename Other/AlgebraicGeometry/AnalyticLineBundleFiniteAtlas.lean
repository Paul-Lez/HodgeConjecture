/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectivePresentationTwist
public import Other.TauCeti.SheafOfModules.FiniteLocalTriviality

/-!
# Finite analytic line-bundle atlases on projective complex schemes

The complex points of a projective complex scheme are compact.  Consequently every analytic
line bundle has a finite trivializing atlas.  This is the first analytic finiteness input for the
projective GAGA argument: it turns the local rank-one data supplied by invertibility into finite
Čech data.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  [IsProjective X.hom]

local instance finiteAtlasOverHasSheafify (V : Opens (ComplexPoint X)) :
    HasSheafify ((Opens.grothendieckTopology (ComplexPoint X)).over V) AddCommGrpCat.{0} :=
  opensOverHasSheafify V

local instance finiteAtlasOverHasWeakSheafify (V : Opens (ComplexPoint X)) :
    HasWeakSheafify ((Opens.grothendieckTopology (ComplexPoint X)).over V) AddCommGrpCat.{0} :=
  HasSheafify.isRightAdjoint

local instance finiteAtlasOverWEqualsLocallyBijective (V : Opens (ComplexPoint X)) :
    ((Opens.grothendieckTopology (ComplexPoint X)).over V).WEqualsLocallyBijective
      AddCommGrpCat.{0} := by
  infer_instance

/-- A finite local trivialization atlas for an analytic line bundle on a projective complex
scheme.  Its indexing type is definitionally a subtype of a finite set chosen from an arbitrary
invertibility atlas. -/
def analyticLineBundleFiniteTrivializations
    (M : SheafOfModules.{0} (holomorphicRingSheaf X d))
    (hM : TauCeti.SheafOfModules.IsInvertible M) :
    TauCeti.SheafOfModules.LocalTrivializations M := by
  let _ : TauCeti.SheafOfModules.IsInvertible M := hM
  exact (TauCeti.SheafOfModules.LocalTrivializations.ofIsInvertible M).finiteOfCompact

/-- The chosen analytic line-bundle atlas has finitely many members. -/
instance analyticLineBundleFiniteTrivializations_finite
    (M : SheafOfModules.{0} (holomorphicRingSheaf X d))
    (hM : TauCeti.SheafOfModules.IsInvertible M) :
    Finite (analyticLineBundleFiniteTrivializations X d M hM).I := by
  dsimp [analyticLineBundleFiniteTrivializations]
  infer_instance

/-- The finitely many opens in the chosen analytic line-bundle atlas cover all complex points. -/
theorem analyticLineBundleFiniteTrivializations_coversTop
    (M : SheafOfModules.{0} (holomorphicRingSheaf X d))
    (hM : TauCeti.SheafOfModules.IsInvertible M) :
    (Opens.grothendieckTopology (ComplexPoint X)).CoversTop
      (analyticLineBundleFiniteTrivializations X d M hM).X :=
  (analyticLineBundleFiniteTrivializations X d M hM).coversTop

end AlgebraicGeometry.ComplexPoint
