/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.AnalyticSectionOfAlgebraic

/-!
# The extension class of a unit-sheaf extension is determined by its line bundle

The remaining obligation `HasDivisorClassOfSomeCartierData` is stated for an arbitrary
unit-sheaf extension `E` together with an isomorphism between the analytification of an
algebraic invertible sheaf and `E.sectionSheafOfModules`. To compute `E.firstChernClass` from
the algebraic data one must know that the assignment `E ↦ E.cohomologyClass` factors through
the isomorphism class of `E.sectionSheafOfModules` — that is, that

  `H¹(X^an, 𝒪ˣ) → Pic(X^an)`

is injective. This file isolates that statement, `SectionSheafDeterminesClass`, and derives the
consequence used downstream.

This is the first half of step 2 of `docs/DIVISOR_HANDOFF.md` §4.3. It is not a Čech-to-derived
comparison: it only asks that two extensions with isomorphic line bundles have the same class,
which the local-lift machinery of `Other/AlgebraicTopology/SheafExtensionLocalLifts.lean`
reduces to gluing an isomorphism of short exact sequences from a frame change.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

/--
**Obligation.** The line bundle of a unit-sheaf extension determines its class: two extensions of
the constant integer sheaf by the sheaf of holomorphic units whose sheaves of sections are
isomorphic have the same class in `Ext¹(ℤ, 𝒪ˣ)`.

This is injectivity of `H¹(X^an, 𝒪ˣ) → Pic(X^an)`. Its proof does not need any comparison of
cohomology theories: from an isomorphism of the section sheaves one obtains, on a common
refinement of the two trivializing covers, unit frame changes
(`HolomorphicTrivializingCover.exists_isUnit_frameChange`); correcting the local lifts of the
integer section `1` by those units makes the two cocycles of
`Other/AlgebraicTopology/SheafExtensionCocycle.lean` equal, and the resulting local isomorphisms
of the two extensions glue, so the two short exact sequences are isomorphic and have the same
`ShortComplex.ShortExact.extClass`.
-/
def SectionSheafDeterminesClass : Prop :=
  ∀ E E' : HolomorphicUnitExtension X d,
    Nonempty (E.sectionSheafOfModules ≅ E'.sectionSheafOfModules) →
      E.cohomologyClass = E'.cohomologyClass

variable {X d}

/-- Extensions with isomorphic line bundles have the same integral first Chern class. -/
theorem firstChernClass_eq_of_sectionSheafOfModules_iso
    (h : SectionSheafDeterminesClass X d) (E E' : HolomorphicUnitExtension X d)
    (e : E.sectionSheafOfModules ≅ E'.sectionSheafOfModules) :
    E.firstChernClass = E'.firstChernClass := by
  unfold HolomorphicUnitExtension.firstChernClass
  rw [h E E' ⟨e⟩]

end AlgebraicGeometry.ComplexPoint
