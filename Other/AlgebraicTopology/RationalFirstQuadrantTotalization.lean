/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.FirstQuadrantRowwiseTotalization
public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Rational first-quadrant totalization

This is the rational-coefficient specialization of the coefficient-generic finite-filtration
argument.  It is the input needed to totalize the rational Čech--singular chain bicomplex of a
finite open cover before dualizing to the literal winding cochain.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology

/-- Rowwise quasi-isomorphisms of first-quadrant bicomplexes of rational vector spaces remain
quasi-isomorphisms after direct-sum totalization. -/
public theorem rationalFirstQuadrantRowwiseTotalization :
    FirstQuadrantRowwiseTotalization (C := ModuleCat ℚ) :=
  firstQuadrantRowwiseTotalization (C := ModuleCat ℚ)

end AlgebraicTopology
