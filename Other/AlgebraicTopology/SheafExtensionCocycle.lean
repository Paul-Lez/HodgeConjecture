/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Differences of local lifts in a sheaf extension

The kernel in a short exact sequence of abelian sheaves is already a kernel on sections.
Consequently two lifts of the same section differ by a unique section of the kernel sheaf.
These differences commute with restriction and satisfy the additive cocycle identity.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {Y : TopCat.{0}} (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} Y))
  (hS : S.ShortExact)

/-- Evaluation of abelian sheaves on an open set. -/
abbrev sectionsFunctor (U : Opens Y) : TopCat.Sheaf AddCommGrpCat.{0} Y ⥤ AddCommGrpCat.{0} :=
  TopCat.Sheaf.forget AddCommGrpCat.{0} Y ⋙
    (evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{0}).obj (op U)

instance sectionsFunctor_additive (U : Opens Y) : (sectionsFunctor U).Additive := by
  constructor
  intro A B f g
  change ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{0}).obj (op U)).map
    ((TopCat.Sheaf.forget AddCommGrpCat.{0} Y).map (f + g)) = _
  rw [Functor.map_add, Functor.map_add]
  rfl

instance sectionsFunctor_preservesFiniteLimits (U : Opens Y) :
    PreservesFiniteLimits (sectionsFunctor U) := by
  let : PreservesFiniteLimits ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{0}).obj (op U)) :=
    inferInstance
  exact comp_preservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{0} Y)
    ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{0}).obj (op U))

include hS

/-- Sections preserve exactness at the middle term when the first map is a kernel. -/
theorem sections_exact (U : Opens Y) :
    ∀ t : S.X₂.obj.obj (op U), S.g.hom.app (op U) t = 0 →
      ∃ a : S.X₁.obj.obj (op U), S.f.hom.app (op U) a = t := by
  have h := hS.exact.map_of_mono_of_preservesKernel (sectionsFunctor U)
    hS.mono_f inferInstance
  exact (ShortComplex.ab_exact_iff _).mp h

/-- The inclusion of the kernel sheaf is injective on sections. -/
theorem sections_injective (U : Opens Y) :
    Function.Injective (S.f.hom.app (op U)) := by
  have := hS.mono_f
  have : Mono ((sectionsFunctor U).map S.f) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).mp this

/-- The unique kernel section measuring the difference of two lifts of the same section. -/
def liftDifference (U : Opens Y) (a b : S.X₂.obj.obj (op U))
    (h : S.g.hom.app (op U) a = S.g.hom.app (op U) b) : S.X₁.obj.obj (op U) :=
  Classical.choose (sections_exact S hS U (a - b) (by rw [map_sub, h, sub_self]))

/-- Applying the kernel inclusion to the difference recovers the difference of lifts. -/
theorem liftDifference_spec (U : Opens Y) (a b : S.X₂.obj.obj (op U))
    (h : S.g.hom.app (op U) a = S.g.hom.app (op U) b) :
    S.f.hom.app (op U) (liftDifference S hS U a b h) = a - b :=
  Classical.choose_spec (sections_exact S hS U (a - b) (by rw [map_sub, h, sub_self]))

/-- Differences of three lifts satisfy the cocycle identity. -/
theorem liftDifference_add (U : Opens Y) (a b c : S.X₂.obj.obj (op U))
    (hab : S.g.hom.app (op U) a = S.g.hom.app (op U) b)
    (hbc : S.g.hom.app (op U) b = S.g.hom.app (op U) c) :
    liftDifference S hS U a b hab + liftDifference S hS U b c hbc =
      liftDifference S hS U a c (hab.trans hbc) := by
  apply sections_injective S hS U
  rw [map_add, liftDifference_spec, liftDifference_spec, liftDifference_spec]
  abel

/-- The difference of a lift with itself is zero. -/
@[simp]
theorem liftDifference_self (U : Opens Y) (a : S.X₂.obj.obj (op U)) :
    liftDifference S hS U a a rfl = 0 := by
  apply sections_injective S hS U
  rw [liftDifference_spec, map_zero, sub_self]

/-- Taking the difference of lifts commutes with restriction to a smaller open set. -/
theorem liftDifference_restrict {U V : Opens Y} (hVU : V ≤ U)
    (a b : S.X₂.obj.obj (op U))
    (h : S.g.hom.app (op U) a = S.g.hom.app (op U) b)
    (h' : S.g.hom.app (op V) (S.X₂.obj.map (homOfLE hVU).op a) =
      S.g.hom.app (op V) (S.X₂.obj.map (homOfLE hVU).op b)) :
    S.X₁.obj.map (homOfLE hVU).op (liftDifference S hS U a b h) =
      liftDifference S hS V (S.X₂.obj.map (homOfLE hVU).op a)
        (S.X₂.obj.map (homOfLE hVU).op b) h' := by
  apply sections_injective S hS V
  calc
    _ = S.X₂.obj.map (homOfLE hVU).op
        (S.f.hom.app (op U) (liftDifference S hS U a b h)) :=
      ConcreteCategory.congr_hom (S.f.hom.naturality (homOfLE hVU).op) _
    _ = _ := by rw [liftDifference_spec, map_sub, liftDifference_spec]

/-- A global section of the quotient sheaf lifts on a neighborhood of each point. -/
theorem exists_local_lift (t : S.X₃.obj.obj (op (⊤ : Opens Y))) (x : Y) :
    ∃ (U : Opens Y), x ∈ U ∧ ∃ a : S.X₂.obj.obj (op U),
      S.g.hom.app (op U) a = S.X₃.obj.map (homOfLE le_top).op t := by
  have hloc := (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mpr hS.epi_g
  obtain ⟨U, hU, ⟨a, ha⟩, hx⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).mp hloc ⊤ t x (by trivial)
  exact ⟨U, hx, a, ha⟩

end TopCat.Sheaf
