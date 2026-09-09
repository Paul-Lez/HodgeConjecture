/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicLineBundleCoordinates
public import Other.TauCeti.SheafOfModules.Free
public import Other.TauCeti.SheafOfModules.LocalTriviality

/-!
# Invertibility of the holomorphic section sheaf

Local bundle coordinates give isomorphisms from the structure sheaf to the section sheaf
over each trivializing neighborhood. This proves invertibility in Tau Ceti's rank-one
local-generator formulation, and hence local freeness in Mathlib's formulation.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint.HolomorphicUnitExtension

variable {X : Scheme} {s : X ⟶ Spec ↧ℂ} {d : ℕ} [SmoothOfRelativeDimension d s]

local instance holomorphicLineBundleInvertibleTopology : TopologicalSpace (ComplexPoint X s) :=
  Point.analyticTopology

variable (E : HolomorphicUnitExtension s d) (i : ComplexPoint X s)

set_option backward.isDefEq.respectTransparency false in
/-- The coordinate isomorphism on every object of the site over a trivializing neighborhood. -/
def localSectionModuleIso (V : (Over (E.localLifts.opens i))ᵒᵖ) :
    ((E.sectionSheafOfModules).over (E.localLifts.opens i)).val.obj V ≅
      (SheafOfModules.unit ((holomorphicRingSheaf s d).over (E.localLifts.opens i))).val.obj V :=
  (E.localCoordinateEquiv i (unop V).left (leOfHom (unop V).hom)).toModuleIso

set_option backward.isDefEq.respectTransparency false in
/-- The section sheaf is trivial over every chosen bundle neighborhood. -/
def localSectionSheafIso : (E.sectionSheafOfModules).over (E.localLifts.opens i) ≅
    SheafOfModules.unit ((holomorphicRingSheaf s d).over (E.localLifts.opens i)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (E.localSectionModuleIso i) (by
      intro V W f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      apply Subtype.ext
      funext x
      rfl))

/-- The section sheaf is locally the free sheaf on one generator. -/
def localFreeSheafIso :
    SheafOfModules.free (R := (holomorphicRingSheaf s d).over (E.localLifts.opens i)) PUnit ≅
      (E.sectionSheafOfModules).over (E.localLifts.opens i) :=
  TauCeti.SheafOfModules.freePUnitIsoUnit _ ≪≫ (E.localSectionSheafIso i).symm

/-- The local lifting neighborhoods cover the analytic space. -/
theorem localLifts_coversTop :
    (Opens.grothendieckTopology (TopCat.of (ComplexPoint X s))).CoversTop E.localLifts.opens := by
  intro U x hx
  refine ⟨U ⊓ E.localLifts.opens x, homOfLE inf_le_left, ?_, hx, E.localLifts.mem_opens x⟩
  exact ⟨x, ⟨homOfLE inf_le_right⟩⟩

/-- The explicit rank-one trivializations of the holomorphic section sheaf. -/
def sectionLocalTrivializations :
    TauCeti.SheafOfModules.LocalTrivializations E.sectionSheafOfModules where
  I := ComplexPoint X s
  X := E.localLifts.opens
  coversTop := E.localLifts_coversTop
  iso := E.localFreeSheafIso

/-- The holomorphic section sheaf of the constructed line bundle is invertible. -/
instance sectionSheafOfModules_isInvertible :
    TauCeti.SheafOfModules.IsInvertible E.sectionSheafOfModules :=
  E.sectionLocalTrivializations.isInvertible

end AlgebraicGeometry.ComplexPoint.HolomorphicUnitExtension
