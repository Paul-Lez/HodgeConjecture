import Mathlib.Util.AssertNoSorry
import Other.AlgebraicGeometry.LefschetzOneOneProof

/-!
# Lefschetz `(1, 1)` axiom boundary

This file fails to build if either exported Lefschetz theorem starts depending on an axiom other
than Lean's standard quotient, choice, or propositional-extensionality axioms.
-/

open Lean Elab Command

private def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

elab "assert_standard_axioms " declaration:ident : command => do
  let declarationName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo declaration
  let axioms ← Lean.collectAxioms declarationName
  let unexpected := axioms.filter fun axiomName => !allowedAxioms.contains axiomName
  unless unexpected.isEmpty do
    throwErrorAt declaration
      m!"'{declarationName}' depends on disallowed axioms: {unexpected.toList}"

assert_standard_axioms rationalLefschetzOneOne
assert_standard_axioms lefschetzOneOne
