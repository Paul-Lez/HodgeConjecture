/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Topology.Sheaves.Abelian
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Colimits

/-!
# Exactness on stalks for sheaves of modules

This transfers Mathlib's stalkwise exactness criterion for sheaves of abelian groups to sheaves
of modules.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace TopCat

universe u

variable {X : TopCat.{u}} {R : CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) RingCat.{u}}

/-- The stalk functor on sheaves of abelian groups. -/
abbrev TopCat.Sheaf.stalkFunctor (X : TopCat.{u}) (x : X) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

instance (x : X) : (TopCat.Sheaf.stalkFunctor X x).Additive :=
  inferInstanceAs ((TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive)

instance (x : X) : PreservesFiniteLimits (TopCat.Sheaf.stalkFunctor X x) :=
  inferInstanceAs (PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x))

/-- Exactness of sheaves of abelian groups is detected on stalks. -/
theorem TopCat.Sheaf.exact_iff_stalk_exact
    (S : ShortComplex (CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u})) :
    S.Exact ↔ ∀ x : X, (S.map (TopCat.Sheaf.stalkFunctor X x)).Exact :=
  TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S

/-- The stalk functor on sheaves of modules, valued in abelian groups. -/
abbrev SheafOfModules.stalkFunctorAddCommGrp (x : X) :
    SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf R ⋙ TopCat.Sheaf.stalkFunctor X x

instance (x : X) :
    PreservesFiniteLimits (SheafOfModules.stalkFunctorAddCommGrp (R := R) x) :=
  comp_preservesFiniteLimits _ _

/-- A short complex of sheaves of modules is exact if it is exact on every stalk. -/
theorem SheafOfModules.exact_of_stalk_exact (S : ShortComplex (SheafOfModules.{u} R))
    (h : ∀ x : X, (S.map (SheafOfModules.stalkFunctorAddCommGrp x)).Exact) : S.Exact :=
  Functor.reflects_exact_of_faithful (SheafOfModules.toSheaf R) S
    ((TopCat.Sheaf.exact_iff_stalk_exact (S.map (SheafOfModules.toSheaf R))).mpr h)

/-- Exactness of a short complex of sheaves of modules implies exactness on every stalk. -/
theorem SheafOfModules.stalk_exact_of_exact (S : ShortComplex (SheafOfModules.{u} R))
    (h : S.Exact) (x : X) : (S.map (SheafOfModules.stalkFunctorAddCommGrp x)).Exact :=
  (TopCat.Sheaf.exact_iff_stalk_exact _).mp (h.map (SheafOfModules.toSheaf R)) x

/-- Exactness of sheaves of modules is equivalent to exactness on every stalk. -/
theorem SheafOfModules.exact_iff_stalk_exact (S : ShortComplex (SheafOfModules.{u} R)) :
    S.Exact ↔ ∀ x : X, (S.map (SheafOfModules.stalkFunctorAddCommGrp x)).Exact :=
  ⟨fun h x ↦ SheafOfModules.stalk_exact_of_exact S h x,
    SheafOfModules.exact_of_stalk_exact S⟩
