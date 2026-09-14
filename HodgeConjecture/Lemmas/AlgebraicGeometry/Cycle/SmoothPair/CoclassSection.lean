/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.SmoothPair.CoclassSection

/-!
# The global exactly normalized smooth-support coclass section

Lemmas about the definitions in
`HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.SmoothPair.CoclassSection`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular
open TopCat.Presheaf

namespace AlgebraicGeometry.ComplexPoint

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left]

@[simp] theorem smoothClosedSupportCoclassSection_germ (x : Point ℂ X) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm x
      (smoothClosedSupportCoclassSection X Y i m d) =
        smoothClosedSupportCoclassStalk X Y i m d x :=
  TopCat.Sheaf.sectionOfLocallyRepresentable_germ
    (smoothClosedSupportCoclassSheaf X Y i m d)
    (smoothClosedSupportCoclassStalk X Y i m d)
    (smoothClosedSupportCoclassStalk_locallyRepresentable X Y i m d) x

end AlgebraicGeometry.ComplexPoint
