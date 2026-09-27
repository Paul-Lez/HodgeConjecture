/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ComplementFrameGeneric
public import Other.AlgebraicGeometry.SupportEnlargementCodimTwo

/-!
# The relative first Chern class for a frame defined only off a codimension-two set

`Other/AlgebraicGeometry/ChernRelativeClassNaturality.lean` builds the canonical relative first
Chern class out of a frame of the line bundle on the complement of the analytic support of the
divisor, `HasComplementFrame`. That hypothesis is *not* provable with the algebra currently in
Mathlib: the local equation `c.fn i` of the rational section is only known to be a unit at the
codimension-one points off the divisor, and upgrading this to "unit on the whole complement" is
algebraic Hartogs (a regular local ring is normal), which Mathlib does not have.

This file therefore redoes the construction for a frame defined on the complement of a *larger*
Zariski-closed set `Z'`, which contains the support of the divisor and whose extra points have
codimension at least two. The construction of the relative class works verbatim for the
complement of an arbitrary closed analytic set (nothing in
`ChernRelativeClass.lean` refers to the divisor), so the only work here is the bookkeeping, and
the passage back from the support `Z'` to the support of the divisor, which is the surjectivity
of the support-enlargement map in codimension two.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open CategoryTheory.Localization

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernRelativeGenericTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

/-! ### The relative first Chern class for an arbitrary closed support -/

variable {X}

/-- The relative first Chern class of a splitting over the complement of a closed analytic set
`S`, with its support written as `S` rather than as the complement of the complement. -/
def relativeChernClassOnClosed (S : Closeds (ComplexPoint X))
    (E : HolomorphicUnitExtension X (dim X.left))
    (ℓ : E.middle.obj.obj (op (S.compl)))
    (hℓ : E.projection.hom.app (op (S.compl)) ℓ =
      (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : S.compl ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection)
    (cmp : RelativeChernComparison X (dim X.left) S.compl) :
    RationalCohomologyWithSupport X ((S : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) 2 :=
  supportedClassTransport X
    (show (S.compl : Set (ComplexPoint X))ᶜ = (S : Set (ComplexPoint X)) from
      compl_compl (S : Set (ComplexPoint X))) 2
    (E.relativeChernClass S.compl ℓ hℓ cmp)

set_option maxHeartbeats 1000000 in
/-- **The relative first Chern class in the supported injective model, for an arbitrary closed
analytic support.** For `S = |D|^an` this is `relativeChernSupportedClass`. -/
def relativeChernSupportedClassOnClosed (S : Closeds (ComplexPoint X))
    (E : HolomorphicUnitExtension X (dim X.left))
    (ℓ : E.middle.obj.obj (op (S.compl)))
    (hℓ : E.projection.hom.app (op (S.compl)) ℓ =
      (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : S.compl ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection)
    (cmp : RelativeChernComparison X (dim X.left) S.compl) :
    SupportedInjectiveHomology X S (2 : ℤ) :=
  coneSupportAddEquivSupportedInjectiveHomology X
    ((S : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) S.isClosed (2 : ℤ)
    (relativeChernClassOnClosed S E ℓ hℓ cmp)

omit [IsProjective X.hom] in
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The relative first Chern class is a lift of the rational first Chern class**, for an
arbitrary closed analytic support. -/
theorem supportedInjectiveToAmbient_relativeChernSupportedClassOnClosed
    (S : Closeds (ComplexPoint X)) (E : HolomorphicUnitExtension X (dim X.left))
    (ℓ : E.middle.obj.obj (op (S.compl)))
    (hℓ : E.projection.hom.app (op (S.compl)) ℓ =
      (𝓒(↧(ComplexPoint X); ℤ)).obj.map (homOfLE (le_top : S.compl ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection)
    (cmp : RelativeChernComparison X (dim X.left) S.compl) :
    supportedInjectiveToAmbient X S (2 : ℤ)
        (relativeChernSupportedClassOnClosed S E ℓ hℓ cmp) =
      rationalCohomologyAddEquivAmbientInjectiveHomology X 2
        (integralToRationalCohomology X 2 E.firstChernClass) := by
  have h := coneSupportAddEquivSupportedInjectiveHomology_forgetSupport X
    ((S : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) S.isClosed 2
    (relativeChernClassOnClosed S E ℓ hℓ cmp)
  refine h.symm.trans (congrArg _ ?_)
  rw [relativeChernClassOnClosed, forgetSupportHypercohomology_supportedClassTransport]
  have hc := congrArg (hypercohomologyAddEquivConstantCohomology ℚ X 2).symm
    (E.forgetSupport_relativeChernClass _ ℓ hℓ cmp)
  dsimp only [coneForgetSupport, AddMonoidHom.comp_apply,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at hc
  simpa only [Nat.cast_ofNat, AddEquiv.symm_apply_apply, AddEquiv.toEquiv_eq_coe,
    AddEquiv.coe_toEquiv] using hc

/-! ### Codimension-two support enlargement -/

variable (X)

/-- **Excision in codimension two.** For Zariski-closed `Z ≤ Z'` all of whose points in
`Z' ∖ Z` have codimension at least two, every degree-two class supported on `(Z')^an` is the
enlargement of a class supported on `Z^an`.

Mathematically this is the vanishing of `H²` and `H³` with support in `Z' ∖ Z` — the same
codimension-two vanishing that already proves `hasComponentSupportDecomposition_unconditional`
(`HasCodimensionTwoSupportedVanishing`) — fed through the nested-support localisation sequence.
No compatibility with `supportedInjectiveToAmbient` has to be assumed: it is
`supportedInjectiveToAmbient_enlarge`. -/
def EnlargeSurjectiveCodimTwo : Prop :=
  ∀ (Z Z' : Closeds X.left) (hZZ' : Z ≤ Z'),
    (∀ z ∈ Z', z ∉ Z → (2 : ℕ∞) ≤ coheight z) →
    ∀ β' : SupportedInjectiveHomology X (analyticClosedSupport X Z') (2 : ℤ),
      ∃ β : SupportedInjectiveHomology X (analyticClosedSupport X Z) (2 : ℤ),
        enlargeSupportedInjectiveHomology X (analyticClosedSupport_le_of_le X hZZ')
          (2 : ℤ) β = β'

/-- The form of `EnlargeSurjectiveCodimTwo` used below: the two analytic supports are supplied as
closed analytic sets together with equalities, so that no transport is needed at the point of
use. -/
theorem exists_enlarge_of_analyticClosedSupport_eq (h : EnlargeSurjectiveCodimTwo X)
    (Z Z' : Closeds X.left) (hZZ' : Z ≤ Z')
    (hcod : ∀ z ∈ Z', z ∉ Z → (2 : ℕ∞) ≤ coheight z)
    (S T : Closeds (ComplexPoint X)) (hS : analyticClosedSupport X Z = S)
    (hT : analyticClosedSupport X Z' = T) (hST : S ≤ T)
    (β' : SupportedInjectiveHomology X T (2 : ℤ)) :
    ∃ β : SupportedInjectiveHomology X S (2 : ℤ),
      enlargeSupportedInjectiveHomology X hST (2 : ℤ) β = β' := by
  subst hS
  subst hT
  exact h Z Z' hZZ' hcod β'

/-- Codimension-two support enlargement is surjective. -/
theorem enlargeSurjectiveCodimTwo : EnlargeSurjectiveCodimTwo X := by
  intro Z Z' hZZ' hcod β'
  obtain ⟨β, hβ, -⟩ := exists_enlarge_eq_of_codimTwo X Z Z' hZZ' hcod β'
  exact ⟨β, hβ⟩

end AlgebraicGeometry.ComplexPoint
