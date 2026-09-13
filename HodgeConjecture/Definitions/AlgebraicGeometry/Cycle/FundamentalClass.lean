/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HodgeConjecture.Definitions.AlgebraicGeometry.Cycle.Transport.InjectiveModel
/-!
# The class of an integral cycle component

The three steps of the construction, and nothing else.

1. The exactly normalized normal-chart coclass on the component's smooth locus, a section
   of the relative-cohomology sheaf over `X ∖ Z_sing`. This is
   `cycleComponentSmoothSupportCoclassSection`, built in `Cycle/Component/`.
2. That section extends uniquely to a class with support in the whole component:
   `cycleComponentSheafSupportedClass`, in `H^{2p}` with support, in the mapping-cone model.
3. Forgetting the support gives `cycleComponentSheafClass`, the class in ordinary rational
   cohomology that the statement of the conjecture uses.

Every group named here is one the statement could name. The injective resolution that
proves step 2 is confined to `Cycle/Transport/InjectiveModel.lean`, and reaches this file
only through `cycleComponentSupportedClassEquiv`.

No fundamental-class, orientation, duality, or vanishing datum is an argument. This does
not assert intrinsic compactification independence or rational-equivalence invariance.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ)))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

attribute [local instance] cycleComponentSheafClassAnalyticTopology

variable (x : X.left) {p : ℕ} (hx : Order.coheight x = p)

/-- **Step 2.** Extend a smooth-locus coclass across the singular boundary, uniquely.

The singular locus has codimension at least `p + 1`, so restriction to `X ∖ Z_sing` is an
isomorphism in degree `2p`; this is its inverse. Purity and boundary vanishing are proved
in the injective model, but the map itself lands in cohomology with support. -/
def cycleComponentExtendSmoothCoclass :
    CycleComponentSmoothCoclassSections X x p →+
      RationalCohomologyWithSupport X (cycleComponentSupport X x) (2 * (p : ℤ)) :=
  (cycleComponentSupportedClassEquiv X x hx).symm.toAddMonoidHom

/-- The class of the component in degree-`2p` rational cohomology with support in it,
obtained by extending the normalized smooth-locus coclass. -/
def cycleComponentSheafSupportedClass :
    RationalCohomologyWithSupport X (cycleComponentSupport X x) (2 * (p : ℤ)) :=
  cycleComponentExtendSmoothCoclass X x hx
    (cycleComponentSmoothSupportCoclassSection X x hx)

/-- **Step 3.** The unconditional ordinary class of an arbitrary integral component: the
supported class of step 2, with its support forgotten.

This is the composite of the three steps, not a second route into ordinary cohomology; the
agreement with `forgetSupport` is therefore definitional rather than a theorem. -/
def cycleComponentSheafClass : H^(2 * (p : ℤ))(X; ℚ) :=
  forgetSupport X (cycleComponentSupport X x) (2 * (p : ℤ))
    (cycleComponentSheafSupportedClass X x hx)

end AlgebraicGeometry.ComplexPoint
