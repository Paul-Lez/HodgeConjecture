/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.Cohomology
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.RestrictModulesOver
public import Other.Oka.Topology.Sheaves.Cohomology.Restrict

/-!
# Cohomology of the restriction of a sheaf of modules to an open subspace

For a locally ringed space `Y`, an open `W ⊆ Y` and a sheaf of `𝒪_Y`-modules `M`, the underlying
abelian sheaf of the restriction `M|_W = (Y.restrictModules W).obj M` (a sheaf of modules on the
open subspace `Y|_W`) is the restriction `(TopCat.Sheaf.restrictOpen W).obj M.toAb` of the
underlying abelian sheaf of `M` (`AlgebraicGeometry.LocallyRingedSpace.restrictModulesToAbIso`).
Hence `Hᵠ(Y|_W, M|_W)` is the cohomology `Hᵠ(W, M|_W)` of the restricted abelian sheaf
(`AlgebraicGeometry.LocallyRingedSpace.restrictModulesHAddEquiv`).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace

variable (Y : LocallyRingedSpace.{u}) (W : Opens Y.toPresheafedSpace)

/-- The underlying abelian sheaf of the restriction of a sheaf of modules to an open subspace is
the restriction of its underlying abelian sheaf. -/
noncomputable def restrictModulesToAbIso (M : SheafOfModules.{u} Y.ringSheaf) :
    ((Y.restrictModules W).obj M).toAb ≅ (TopCat.Sheaf.restrictOpen W).obj M.toAb :=
  (modulesToAb _).mapIso (restrictModulesObjIso Y W M)

/-- The cohomology of the restriction of a sheaf of modules to an open subspace `W` is the
cohomology on `W` of the restriction of its underlying abelian sheaf. -/
noncomputable def restrictModulesHAddEquiv (M : SheafOfModules.{u} Y.ringSheaf) (q : ℕ) :
    H ((Y.restrictModules W).obj M) q ≃+
      TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen W).obj M.toAb) q :=
  TopCat.Sheaf.H.addEquivOfIso (restrictModulesToAbIso Y W M) q

end AlgebraicGeometry.LocallyRingedSpace

end
