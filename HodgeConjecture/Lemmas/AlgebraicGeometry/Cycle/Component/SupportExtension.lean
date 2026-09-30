/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SupportExtension
public import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.WithSupport
public import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Component.SupportExtensionVanishing

/-!
# Unique extension across a cycle component's singular boundary

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Component.SupportExtension`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

set_option maxHeartbeats 800000 in
include hx in
/-- Vanishing on the singular boundary identifies `H_[Z]^(2p)(X;ℚ)` with the relative group
`H^(2p)(U, U \ Z;ℚ)` on the smooth ambient open `U`. -/
def cycleComponentSupportExtensionIso :
    H_[cycleComponentAnalyticClosedSupport X x]^(2 * p)(X; ℚ) ≃+
      CategoryTheory.Sheaf.relH
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
        (2 * p)
        (homOfLE (cycleComponentSupportComplement_le_smoothAmbientOpen X x)) :=
  let T := TopCat.of (ComplexPoint X)
  let Z := cycleComponentAnalyticClosedSupport X x
  let U := cycleComponentSmoothSupportAmbientOpen X x
  let f : Z.compl ⟶ U := homOfLE (cycleComponentSupportComplement_le_smoothAmbientOpen X x)
  let g : U ⟶ ⊤ := homOfLE le_top
  let F := (TopCat.Sheaf.constantFunctor T).obj (AddCommGrpCat.of ℚ)
  let n : ℕ := 2 * p
  let e := CategoryTheory.Sheaf.relH.restrictEquivOfIsZero F f g n
    (cycleComponentSingularBoundaryRelH_isZero_of_lt X x hx n (by omega))
    (cycleComponentSingularBoundaryRelH_isZero_of_lt X x hx (n + 1) (by omega))
  e

end AlgebraicGeometry.ComplexPoint
