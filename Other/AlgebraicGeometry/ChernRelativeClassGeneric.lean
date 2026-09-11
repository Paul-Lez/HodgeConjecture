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
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : S.compl ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection)
    (cmp : RelativeChernComparison X (dim X.left) S.compl) :
    RationalCohomologyWithSupport X ((S : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) 2 :=
  supportedClassTransport X
    (compl_compl ((S : Closeds (ComplexPoint X)) : Set (ComplexPoint X))) 2
    (E.relativeChernClass S.compl ℓ hℓ cmp)

set_option maxHeartbeats 1000000 in
/-- **The relative first Chern class in the supported injective model, for an arbitrary closed
analytic support.** For `S = |D|^an` this is `relativeChernSupportedClass`. -/
def relativeChernSupportedClassOnClosed (S : Closeds (ComplexPoint X))
    (E : HolomorphicUnitExtension X (dim X.left))
    (ℓ : E.middle.obj.obj (op (S.compl)))
    (hℓ : E.projection.hom.app (op (S.compl)) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : S.compl ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection)
    (cmp : RelativeChernComparison X (dim X.left) S.compl) :
    SupportedInjectiveHomology X S (2 * ((1 : ℕ) : ℤ)) :=
  rationalSupportAddEquivSupportedInjectiveHomology X
    ((S : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) S.isClosed (2 * ((1 : ℕ) : ℤ))
    (relativeChernClassOnClosed S E ℓ hℓ cmp)

omit [IsProjective X.hom] in
set_option maxHeartbeats 1000000 in
/-- **The relative first Chern class is a lift of the rational first Chern class**, for an
arbitrary closed analytic support. -/
theorem supportedInjectiveToAmbient_relativeChernSupportedClassOnClosed
    (S : Closeds (ComplexPoint X)) (E : HolomorphicUnitExtension X (dim X.left))
    (ℓ : E.middle.obj.obj (op (S.compl)))
    (hℓ : E.projection.hom.app (op (S.compl)) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top : S.compl ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection)
    (cmp : RelativeChernComparison X (dim X.left) S.compl) :
    supportedInjectiveToAmbient X S (2 * ((1 : ℕ) : ℤ))
        (relativeChernSupportedClassOnClosed S E ℓ hℓ cmp) =
      rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * ((1 : ℕ) : ℤ))
        (integralToRationalCohomology X 2 E.firstChernClass) := by
  have h := rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport X
    ((S : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) S.isClosed 2
    (relativeChernClassOnClosed S E ℓ hℓ cmp)
  refine h.symm.trans (congrArg _ ?_)
  exact (forgetSupport_supportedClassTransport X
      (compl_compl ((S : Closeds (ComplexPoint X)) : Set (ComplexPoint X))) 2
      (E.relativeChernClass S.compl ℓ hℓ cmp)).trans
    (E.forgetSupport_relativeChernClass _ ℓ hℓ cmp)

/-! ### The two inputs -/

variable (X)

-- Input 1 is `AlgebraicGeometry.ComplexPoint.HasComplementFrameOffCodimTwo` of
-- `Other/AlgebraicGeometry/ComplementFrameGeneric.lean`, where it is **proved unconditionally**
-- (`hasComplementFrameOffCodimTwo`).

/-- **Input 2 (excision in codimension two).** For Zariski-closed `Z ≤ Z'` all of whose points in
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
    ∀ β' : SupportedInjectiveHomology X (analyticClosedSupport X Z') (2 * ((1 : ℕ) : ℤ)),
      ∃ β : SupportedInjectiveHomology X (analyticClosedSupport X Z) (2 * ((1 : ℕ) : ℤ)),
        enlargeSupportedInjectiveHomology X (analyticClosedSupport_le_of_le X hZZ')
          (2 * ((1 : ℕ) : ℤ)) β = β'

/-- The form of `EnlargeSurjectiveCodimTwo` used below: the two analytic supports are supplied as
closed analytic sets together with equalities, so that no transport is needed at the point of
use. -/
theorem exists_enlarge_of_analyticClosedSupport_eq (h : EnlargeSurjectiveCodimTwo X)
    (Z Z' : Closeds X.left) (hZZ' : Z ≤ Z')
    (hcod : ∀ z ∈ Z', z ∉ Z → (2 : ℕ∞) ≤ coheight z)
    (S T : Closeds (ComplexPoint X)) (hS : analyticClosedSupport X Z = S)
    (hT : analyticClosedSupport X Z' = T) (hST : S ≤ T)
    (β' : SupportedInjectiveHomology X T (2 * ((1 : ℕ) : ℤ))) :
    ∃ β : SupportedInjectiveHomology X S (2 * ((1 : ℕ) : ℤ)),
      enlargeSupportedInjectiveHomology X hST (2 * ((1 : ℕ) : ℤ)) β = β' := by
  subst hS
  subst hT
  exact h Z Z' hZZ' hcod β'

/-! ### The remaining obligation, and the reduction -/

/-- **Obligation: the chart formula for the relative first Chern class, generic form.**

Same shape as `HasRelativeChernChartFormula`, with the frame defined only off the larger closed
set `Z'`: the class `β` supported on `|D|^an` is now pinned by the requirement that its
enlargement to `(Z')^an` be the relative first Chern class of the frame, and the conclusion is
unchanged. -/
def HasRelativeChernChartFormulaGeneric : Prop :=
  ∀ (c : Scheme.CartierData X.left) (E : HolomorphicUnitExtension X (dim X.left))
    (Z' : Closeds X.left)
    (hle : cycleAnalyticClosedSupport X c.divisor ≤ analyticClosedSupport X Z')
    (ℓ : E.middle.obj.obj (op ((analyticClosedSupport X Z').compl)))
    (hℓ : E.projection.hom.app (op ((analyticClosedSupport X Z').compl)) ℓ =
      (constantIntegerSheaf X).obj.map
        (homOfLE (le_top : (analyticClosedSupport X Z').compl ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection)
    (cmp : RelativeChernComparison X (dim X.left) (analyticClosedSupport X Z').compl)
    (β : SupportedInjectiveHomology X (cycleAnalyticClosedSupport X c.divisor)
      (2 * ((1 : ℕ) : ℤ))),
    enlargeSupportedInjectiveHomology X hle (2 * ((1 : ℕ) : ℤ)) β =
        relativeChernSupportedClassOnClosed (analyticClosedSupport X Z') E ℓ hℓ cmp →
      ∀ γ : ∀ x : X.left, SupportedInjectiveHomology X
        (cycleComponentAnalyticClosedSupport X x) (2 * ((1 : ℕ) : ℤ)),
      β = ∑ x ∈ cycleComponents X c.divisor,
          componentContribution X (cycleComponents X c.divisor) x (2 * ((1 : ℕ) : ℤ)) (γ x) →
      ∀ x ∈ cycleComponents X c.divisor, ∀ hx : coheight x = ((1 : ℕ) : ℕ∞),
      ∀ (q : ComplexPoint X) (ch : ChernWindingChart X c x (dim X.left) 1 q),
        ch.HasTrivialUnitWinding → ch.NormalizesCoclass hx →
        ch.ComputesClass (c.divisor x)
          ((cycleComponentSupportedClassNormalizationIso X x (d := dim X.left) hx).hom (γ x))

set_option maxHeartbeats 1000000 in
/-- **The reduction.** The frame off a codimension-two enlargement of the divisor, excision in
codimension two, and the chart formula for the resulting relative first Chern class give the
naturality obligation `HasChernWindingNaturality X`.

The witness `β` is obtained by pushing the relative first Chern class of the frame — which is
supported on `(Z')^an` — back to the support `|D|^an` along the enlargement map; the first clause
is then `supportedInjectiveToAmbient_enlarge` together with
`supportedInjectiveToAmbient_relativeChernSupportedClassOnClosed`. -/
theorem hasChernWindingNaturality_of_generic
    (hframe : HasComplementFrameOffCodimTwo X) (henl : EnlargeSurjectiveCodimTwo X)
    (hchart : HasRelativeChernChartFormulaGeneric X) :
    HasChernWindingNaturality X := by
  intro E L hL iso c hc
  obtain ⟨Z', hcontain, hcodZ, ℓ, hℓ⟩ := hframe E L hL iso c hc
  have hZle : componentsZariskiSupport X (cycleComponents X c.divisor) ≤ Z' := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := (mem_componentsZariskiSupport X).mp hz
    exact hcontain y ((mem_cycleComponents_iff X c.divisor y).mp hy) hzy
  have hcod : ∀ z ∈ Z', z ∉ componentsZariskiSupport X (cycleComponents X c.divisor) →
      (2 : ℕ∞) ≤ coheight z := by
    intro z hz hnot
    refine hcodZ z hz fun y hy hzy => hnot ?_
    exact (mem_componentsZariskiSupport X).mpr
      ⟨y, (mem_cycleComponents_iff X c.divisor y).mpr hy, hzy⟩
  obtain ⟨cmp⟩ := nonempty_relativeChernComparison X (dim X.left)
    (analyticClosedSupport X Z').compl
  have hSeq : analyticClosedSupport X (componentsZariskiSupport X (cycleComponents X c.divisor)) =
      cycleAnalyticClosedSupport X c.divisor :=
    analyticClosedSupport_componentsZariskiSupport X (cycleComponents X c.divisor)
  have hle : cycleAnalyticClosedSupport X c.divisor ≤ analyticClosedSupport X Z' :=
    cycleAnalyticClosedSupport_le_analyticClosedSupport X c Z' hcontain
  obtain ⟨β, hβ⟩ := exists_enlarge_of_analyticClosedSupport_eq X henl
    (componentsZariskiSupport X (cycleComponents X c.divisor)) Z' hZle hcod
    (cycleAnalyticClosedSupport X c.divisor) (analyticClosedSupport X Z') hSeq rfl hle
    (relativeChernSupportedClassOnClosed (analyticClosedSupport X Z') E ℓ hℓ cmp)
  refine ⟨β, ?_, ?_⟩
  · rw [← supportedInjectiveToAmbient_enlarge X hle (2 * ((1 : ℕ) : ℤ)) β, hβ]
    exact supportedInjectiveToAmbient_relativeChernSupportedClassOnClosed
      (analyticClosedSupport X Z') E ℓ hℓ cmp
  · intro γ hγ x hxs hx q ch hb hcn
    exact hchart c E Z' hle ℓ hℓ cmp β hβ γ hγ x hxs hx q ch hb hcn

set_option maxHeartbeats 1000000 in
/-- **Step 4 of `docs/DIVISOR_HANDOFF.md` §4.3, with the frame available only off a
codimension-two set.** -/
theorem hasDivisorClassOfSomeCartierData_of_generic
    (hframe : HasComplementFrameOffCodimTwo X) (henl : EnlargeSurjectiveCodimTwo X)
    (hcharts : HasNormalizedWindingCharts X) (hchart : HasRelativeChernChartFormulaGeneric X) :
    HasDivisorClassOfSomeCartierData X :=
  hasDivisorClassOfSomeCartierData_of_supportedChernLift_of_localModel X
    (hasChernLocalModel_of_winding X hcharts
      (hasChernWindingNaturality_of_generic X hframe henl hchart))

/-! ### Discharging the frame input -/

set_option maxHeartbeats 1000000 in
/-- The frame input is **unconditional** (`hasComplementFrameOffCodimTwo` of
`Other/AlgebraicGeometry/ComplementFrameGeneric.lean`), so the naturality obligation follows from
excision in codimension two together with the chart formula alone. -/
theorem hasChernWindingNaturality_of_enlargeSurjective
    (henl : EnlargeSurjectiveCodimTwo X) (hchart : HasRelativeChernChartFormulaGeneric X) :
    HasChernWindingNaturality X :=
  hasChernWindingNaturality_of_generic X (hasComplementFrameOffCodimTwo X) henl hchart

set_option maxHeartbeats 1000000 in
/-- **Step 4 of `docs/DIVISOR_HANDOFF.md` §4.3, with the frame input discharged.** What is left is
excision in codimension two, normalised winding charts, and the chart formula for the canonical
relative first Chern class. -/
theorem hasDivisorClassOfSomeCartierData_of_enlargeSurjective
    (henl : EnlargeSurjectiveCodimTwo X) (hcharts : HasNormalizedWindingCharts X)
    (hchart : HasRelativeChernChartFormulaGeneric X) :
    HasDivisorClassOfSomeCartierData X :=
  hasDivisorClassOfSomeCartierData_of_generic X (hasComplementFrameOffCodimTwo X) henl hcharts
    hchart

/-! ### Discharging excision in codimension two -/

/-- **Input 2 is unconditional**: it is `exists_enlarge_eq_of_codimTwo` of
`Other/AlgebraicGeometry/SupportEnlargementCodimTwo.lean`. -/
theorem enlargeSurjectiveCodimTwo : EnlargeSurjectiveCodimTwo X := by
  intro Z Z' hZZ' hcod β'
  obtain ⟨β, hβ, -⟩ := exists_enlarge_eq_of_codimTwo X Z Z' hZZ' hcod β'
  exact ⟨β, hβ⟩

set_option maxHeartbeats 1000000 in
/-- **The naturality obligation, with both inputs discharged.** Only the chart formula for the
canonical relative first Chern class is left. -/
theorem hasChernWindingNaturality_of_relativeChernChartFormulaGeneric
    (hchart : HasRelativeChernChartFormulaGeneric X) : HasChernWindingNaturality X :=
  hasChernWindingNaturality_of_enlargeSurjective X (enlargeSurjectiveCodimTwo X) hchart

set_option maxHeartbeats 1000000 in
/-- **Step 4 of `docs/DIVISOR_HANDOFF.md` §4.3, with the frame and the excision inputs
discharged.** What is left is normalised winding charts and the chart formula for the canonical
relative first Chern class. -/
theorem hasDivisorClassOfSomeCartierData_of_relativeChernChartFormulaGeneric
    (hcharts : HasNormalizedWindingCharts X) (hchart : HasRelativeChernChartFormulaGeneric X) :
    HasDivisorClassOfSomeCartierData X :=
  hasDivisorClassOfSomeCartierData_of_enlargeSurjective X (enlargeSurjectiveCodimTwo X) hcharts
    hchart

end AlgebraicGeometry.ComplexPoint
