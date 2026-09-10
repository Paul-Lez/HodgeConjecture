/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SheafExtensionCocycle

/-!
# Transition sections from local lifts in an extension

Choose local lifts of a global section of the quotient sheaf. Differences of the lifts
give sections of the kernel sheaf on overlaps, satisfying the cocycle identity.
We allow any common open subset of the chosen neighborhoods as the domain of a transition.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {Y : TopCat.{0}} (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} Y))

/-- A covering family of local lifts of a global section in a sheaf extension. -/
structure ExtensionLocalLifts (t : S.X₃.obj.obj (op (⊤ : Opens Y))) where
  /-- One lifting neighborhood for each point. -/
  opens : Y → Opens Y
  /-- The chosen neighborhoods cover the space. -/
  mem_opens (x : Y) : x ∈ opens x
  /-- A lift on each chosen neighborhood. -/
  lift (x : Y) : S.X₂.obj.obj (op (opens x))
  /-- Each local lift maps to the restricted global section. -/
  map_lift (x : Y) : S.g.hom.app (op (opens x)) (lift x) =
    S.X₃.obj.map (homOfLE le_top).op t

namespace ExtensionLocalLifts

/-- Local surjectivity of a sheaf epimorphism supplies the lifting data. -/
def choose (hS : S.ShortExact) (t : S.X₃.obj.obj (op (⊤ : Opens Y))) :
    ExtensionLocalLifts S t where
  opens x := (exists_local_lift S hS t x).choose
  mem_opens x := (exists_local_lift S hS t x).choose_spec.1
  lift x := (exists_local_lift S hS t x).choose_spec.2.choose
  map_lift x := (exists_local_lift S hS t x).choose_spec.2.choose_spec

variable {S} {t : S.X₃.obj.obj (op (⊤ : Opens Y))} (l : ExtensionLocalLifts S t)

/-- A chosen lift restricted to a smaller open set. -/
def restrictLift (x : Y) (V : Opens Y) (hV : V ≤ l.opens x) : S.X₂.obj.obj (op V) :=
  S.X₂.obj.map (homOfLE hV).op (l.lift x)

/-- Every restricted lift still maps to the restriction of the same global section. -/
theorem map_restrictLift (x : Y) (V : Opens Y) (hV : V ≤ l.opens x) :
    S.g.hom.app (op V) (l.restrictLift x V hV) =
      S.X₃.obj.map (homOfLE le_top).op t := by
  calc
    _ = S.X₃.obj.map (homOfLE hV).op
        (S.g.hom.app (op (l.opens x)) (l.lift x)) :=
      ConcreteCategory.congr_hom (S.g.hom.naturality (homOfLE hV).op) _
    _ = _ := by
      rw [l.map_lift, ← AddCommGrpCat.comp_apply, ← Functor.map_comp]
      rfl

/-- Restricting a chosen lift twice agrees with direct restriction. -/
theorem restrictLift_restrict (x : Y) {U V : Opens Y}
    (hU : U ≤ l.opens x) (hVU : V ≤ U) :
    S.X₂.obj.map (homOfLE hVU).op (l.restrictLift x U hU) =
      l.restrictLift x V (hVU.trans hU) := by
  unfold restrictLift
  rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Differences of restricted lifts give a transition section of the kernel sheaf. -/
def transition (hS : S.ShortExact) (x y : Y) (V : Opens Y)
    (hx : V ≤ l.opens x) (hy : V ≤ l.opens y) : S.X₁.obj.obj (op V) :=
  liftDifference S hS V (l.restrictLift x V hx) (l.restrictLift y V hy)
    ((l.map_restrictLift x V hx).trans (l.map_restrictLift y V hy).symm)

/-- The defining equation for a transition section. -/
theorem transition_spec (hS : S.ShortExact) (x y : Y) (V : Opens Y)
    (hx : V ≤ l.opens x) (hy : V ≤ l.opens y) :
    S.f.hom.app (op V) (l.transition hS x y V hx hy) =
      l.restrictLift x V hx - l.restrictLift y V hy :=
  liftDifference_spec ..

/-- The transition from a local lift to itself is zero. -/
@[simp]
theorem transition_self (hS : S.ShortExact) (x : Y) (V : Opens Y)
    (hx : V ≤ l.opens x) : l.transition hS x x V hx hx = 0 :=
  liftDifference_self ..

/-- Transition sections satisfy the cocycle identity on every triple overlap. -/
theorem transition_add (hS : S.ShortExact) (x y z : Y) (V : Opens Y)
    (hx : V ≤ l.opens x) (hy : V ≤ l.opens y) (hz : V ≤ l.opens z) :
    l.transition hS x y V hx hy + l.transition hS y z V hy hz =
      l.transition hS x z V hx hz :=
  liftDifference_add ..

/-- Transition sections commute with restriction of their domain. -/
theorem transition_restrict (hS : S.ShortExact) (x y : Y) {U V : Opens Y}
    (hx : U ≤ l.opens x) (hy : U ≤ l.opens y) (hVU : V ≤ U) :
    S.X₁.obj.map (homOfLE hVU).op (l.transition hS x y U hx hy) =
      l.transition hS x y V (hVU.trans hx) (hVU.trans hy) := by
  apply sections_injective S hS V
  calc
    _ = S.X₂.obj.map (homOfLE hVU).op
        (S.f.hom.app (op U) (l.transition hS x y U hx hy)) :=
      ConcreteCategory.congr_hom (S.f.hom.naturality (homOfLE hVU).op) _
    _ = _ := by
      rw [l.transition_spec, map_sub, l.restrictLift_restrict, l.restrictLift_restrict,
        l.transition_spec]

end ExtensionLocalLifts

end TopCat.Sheaf
