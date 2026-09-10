/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.UnitExtensionCorrectedLiftsOfIso

/-!
# Injectivity of `H¹(X^an, 𝒪ˣ) → Pic(X^an)` on unit-sheaf extensions

`SectionSheafDeterminesClass` from
`Other/AlgebraicGeometry/UnitExtensionClassObligations.lean` is proved here: two extensions of
the constant integer sheaf by the sheaf of holomorphic units whose sheaves of holomorphic
sections are isomorphic have the same class in `Ext¹(ℤ, 𝒪ˣ)`.

The proof runs through the local-lift machinery. On the common lifting neighbourhoods the two
line bundles carry the canonical frames of
`Other/AlgebraicGeometry/HolomorphicLineBundleFrame.lean`, whose frame changes turn the
isomorphism of section sheaves into a `0`-cochain of holomorphic units trivializing the
difference of the two transition cocycles
(`AlgebraicGeometry.ComplexPoint.correctionCochain_spec`). Correcting the local lifts of the
integer section `1` in the second extension by that cochain gives a `CorrectedLifts` datum, and
`CorrectedLifts.cohomologyClass_eq` glues from it a morphism of the two extensions which is the
identity on both ends; `ShortComplex.ShortExact.extClass_eq_of_middleHom` then equates the two
classes.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

/-- **Injectivity of `H¹(𝒪ˣ) → Pic` on unit-sheaf extensions.** Two extensions of the constant
integer sheaf by the sheaf of holomorphic units with isomorphic sheaves of sections have the
same degree-one class. -/
theorem sectionSheafDeterminesClass (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] : SectionSheafDeterminesClass X d := by
  intro E E' he
  obtain ⟨e⟩ := he
  obtain ⟨c⟩ := nonempty_correctedLifts E E' e
  exact c.cohomologyClass_eq

/-- Extensions with isomorphic line bundles have the same integral first Chern class. -/
theorem HolomorphicUnitExtension.firstChernClass_eq_of_sectionSheafOfModules_iso'
    {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]
    (E E' : HolomorphicUnitExtension X d)
    (e : E.sectionSheafOfModules ≅ E'.sectionSheafOfModules) :
    E.firstChernClass = E'.firstChernClass :=
  firstChernClass_eq_of_sectionSheafOfModules_iso (sectionSheafDeterminesClass X d) E E' e

end AlgebraicGeometry.ComplexPoint
