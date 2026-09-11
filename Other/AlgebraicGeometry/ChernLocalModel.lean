/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.DivisorClassComparisonSupport

/-!
# The local model of the first Chern class along a divisor, and the final assembly

This file carries out step 4 of §4.3 of `docs/DIVISOR_HANDOFF.md`: it states, *correctly*, what
remains of `HasDivisorClassOfSomeCartierData X` after the supported lift of the first Chern class
has been produced, and it proves the assembly.

## The correction to the drafted statement

The draft of `HasChernLocalModel` in the handoff quantified over a class
`β : RationalCohomologyWithSupport X (cycleComponentSupport X x) 2` supported on a **single**
component with `forgetSupport β = c₁`. When the divisor has more than one component no such `β`
exists, so the drafted proposition was vacuous. What step 3 actually produces is a class supported
on the analytic support `|D|^an` of the *whole* divisor, and the comparison target
`sheafCycleClassOnCycles … 1 c.divisor` is the *sum*
`∑ₓ nₓ • cycleComponentSheafClass X x` over the components. The statement is therefore split into
two propositions:

* `HasComponentSupportDecomposition X` — **excision in codimension one**: a degree-two class
  supported on a finite union of codimension-one component supports is a sum of classes supported
  on the individual components. Mathematically this is the vanishing of `H²` and `H³` with support
  in the pairwise intersections `Z_x ∩ Z_y`, which have complex codimension at least two, i.e.
  real codimension at least four; the repository already proves exactly this shape of vanishing
  for the singular boundary of a single component
  (`cycleComponentSingularBoundarySectionCohomology_isZero_of_lt`, via
  `FiniteSheafSupportVanishing` and `ReducedSmoothClosedFiltration`), and the
  nested-support localization sequence
  (`TopCat.Sheaf.nestedSupportRestriction_homologyMap_isIso_of_vanishing`) is the tool that turns
  such a vanishing into a decomposition. It is stated here for a general finite set of
  codimension-one points, since nothing about the Chern class is involved.

* `HasChernLocalModel X` — **the one-variable Lelong–Poincaré computation**: there *exists* a
  supported lift `β` of the first Chern class such that in any decomposition of it, the piece
  supported on the component of `x` restricts, on the smooth locus of that component, to
  `c.divisor x` times the normalised normal-chart coclass
  `cycleComponentSmoothSupportCoclassSection`. This is the only genuinely analytic input, and it
  is what fixes the sign.

## A second correction: the quantifier over the lift must be existential

A previous form of `HasChernLocalModel` quantified *universally* over every `β` lifting the first
Chern class. That is false, and made the whole assembly rest on an unprovable hypothesis. The lift
is not unique: by the exactness of the support sequence two lifts differ by the image of
`H¹(X^an ∖ |D|^an, ℚ)`, and such a difference does change the local multiplicities. Concretely,
for `X = ℙ¹`, `L = 𝒪` and the rational section `s = z`, the divisor is `D = [0] − [∞]` and
`c₁(L) = 0`, while `H²_{\{0,∞\}}(ℙ¹, ℚ) ≅ ℚ²` with `forgetSupport` the sum map; both `(1, −1)`
and `(2, −2)` lift `c₁ = 0`, and only the first is the divisor. The statement is therefore
existential in `β`, and the witness is the **relative first Chern class** `c₁(L, s)` cut out by
the splitting of `E` over `X^an ∖ |D|^an`.

As a consequence, `HasSupportedChernLift X` — the bare existence of a lift, which is what step 3
produces — is **no longer a hypothesis of the assembly**: it is implied by, and strictly weaker
than, `HasChernLocalModel X`. It is kept below because it records the conclusion of step 3 and its
bridge `exists_supportedChernLift_of_splitting`, which is where the splitting datum that should
produce the canonical lift enters.

## What is proved here

`hasDivisorClassOfSomeCartierData_of_localModel`: the three propositions above imply
`HasDivisorClassOfSomeCartierData X`, hence (`hasDivisorOfAlgebraicModel_of_divisorClass`)
`HasDivisorOfAlgebraicModel X`. All the support bookkeeping — that enlarging the support does not
change the ordinary class, that the constructed cycle class is the explicit finite sum, and that
the normalisation isomorphism is injective — is proved, in
`Other/AlgebraicGeometry/DivisorClassComparisonSupport.lean` and here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernLocalModelAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

/-! ### The three propositions -/

/-- **Hypothesis (step 3).** The rational first Chern class of a unit-sheaf extension whose
section sheaf is the analytification of `L` lifts to a class supported on the analytic support of
the divisor of any Cartier datum representing `L`.

This is the conclusion of `exists_forgetSupport_eq_integralToRational_firstChernClass` for the
open set `Ω := (cycleAnalyticClosedSupport X c.divisor).compl`: the rational section frames the
bundle off the support of its divisor, so the extension splits there.

**This is weaker than what the assembly needs**, and is no longer one of its hypotheses: it
produces *some* lift, by exactness, whereas `HasChernLocalModel` requires the *canonical*,
normalised one (see its docstring for the `ℙ¹` counterexample showing that an arbitrary lift has
the wrong local multiplicities). It is retained because it is the exact output of step 3 and
because its proof `exists_supportedChernLift_of_splitting` is where the splitting datum — the
frame of the bundle off `|D|^an`, which is what should cut out the canonical lift — enters. -/
def HasSupportedChernLift : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∀ c : Scheme.CartierData X.left, c.Represents L →
      ∃ β : RationalCohomologyWithSupport X
          ((cycleAnalyticClosedSupport X c.divisor : Closeds (ComplexPoint X)) :
            Set (ComplexPoint X)) (2 * ((1 : ℕ) : ℤ)),
        forgetSupport X
            ((cycleAnalyticClosedSupport X c.divisor : Closeds (ComplexPoint X)) :
              Set (ComplexPoint X)) (2 * ((1 : ℕ) : ℤ)) β =
          integralToRationalCohomology X 2 E.firstChernClass

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Transport of a supported lift along an equality of supports. This is the bookkeeping that
turns the conclusion of step 3, which is stated for the complement of an open set `Ω`, into
`HasSupportedChernLift`, whose support is the closed set `|D|^an` itself. -/
theorem exists_forgetSupport_of_support_eq {Z Z' : Set (ComplexPoint X)} (hZ : Z = Z') (n : ℤ)
    (α : FieldCohomology ℚ X n)
    (h : ∃ β : RationalCohomologyWithSupport X Z n, forgetSupport X Z n β = α) :
    ∃ β : RationalCohomologyWithSupport X Z' n, forgetSupport X Z' n β = α := by
  subst hZ
  exact h

/-- The supported lift required by `HasSupportedChernLift` is produced by step 3 applied to the
open complement of `|D|^an`: given the obligation `RestrictedChernClassVanishes` for that open set
and a global lift `ℓ` over it of the constant integer section `1` — equivalently, a frame of the
line bundle off the support of the divisor, which the rational section provides — the class
exists. The only bookkeeping is `compl_compl`. -/
theorem exists_supportedChernLift_of_splitting
    (E : HolomorphicUnitExtension X (dim X.left)) (c : Scheme.CartierData X.left)
    (hvan : RestrictedChernClassVanishes X (dim X.left)
      (cycleAnalyticClosedSupport X c.divisor).compl)
    (ℓ : E.middle.obj.obj (op ((cycleAnalyticClosedSupport X c.divisor).compl)))
    (hℓ : E.projection.hom.app (op ((cycleAnalyticClosedSupport X c.divisor).compl)) ℓ =
      (constantIntegerSheaf X).obj.map (homOfLE (le_top :
          (cycleAnalyticClosedSupport X c.divisor).compl ≤ ⊤)).op
        HolomorphicUnitExtension.integerOneSection) :
    ∃ β : RationalCohomologyWithSupport X
        ((cycleAnalyticClosedSupport X c.divisor : Closeds (ComplexPoint X)) :
          Set (ComplexPoint X)) (2 * ((1 : ℕ) : ℤ)),
      forgetSupport X
          ((cycleAnalyticClosedSupport X c.divisor : Closeds (ComplexPoint X)) :
            Set (ComplexPoint X)) (2 * ((1 : ℕ) : ℤ)) β =
        integralToRationalCohomology X 2 E.firstChernClass :=
  exists_forgetSupport_of_support_eq X
    (compl_compl (cycleAnalyticClosedSupport X c.divisor : Set (ComplexPoint X)))
    (2 * ((1 : ℕ) : ℤ)) _
    (exists_forgetSupport_eq_integralToRational_firstChernClass hvan E ℓ hℓ)

/-- **Obligation: excision in codimension one.** A degree-two rational class supported on a finite
union of codimension-one component supports is a sum of classes supported on the individual
components.

Mathematically this is the excision/Mayer–Vietoris statement that the enlargement maps
`H²_{Z_x} → H²_{⋃ Z_y}` are jointly surjective, which follows from the vanishing of `H²` and `H³`
with support in the pairwise intersections `Z_x ∩ Z_y` — closed algebraic subsets of complex
codimension at least two, hence real codimension at least four. Nothing about a Chern class is
involved. -/
def HasComponentSupportDecomposition : Prop :=
  ∀ (s : Finset X.left), (∀ x ∈ s, coheight x = ((1 : ℕ) : ℕ∞)) →
    ∀ β : SupportedInjectiveHomology X (componentsAnalyticClosedSupport X s)
        (2 * ((1 : ℕ) : ℤ)),
      ∃ γ : ∀ x : X.left,
          SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X x)
            (2 * ((1 : ℕ) : ℤ)),
        β = ∑ x ∈ s, componentContribution X s x (2 * ((1 : ℕ) : ℤ)) (γ x)

/-- **Obligation: the local model of the first Chern class along a divisor.**

Let `c` be Cartier data representing `L`. Then there **exists** a class `β` supported on the
analytic support of `c.divisor` whose ordinary class is the rational first Chern class of `E`, and
which is *normalised*: in any decomposition `γ` of `β` into classes supported on the individual
components, the piece `γ x` is, on the smooth locus of the component of a codimension-one point
`x` of the divisor, exactly the multiplicity `c.divisor x` times the normalised normal-chart
coclass.

**Why the quantifier over `β` is existential.** An earlier form of this statement quantified
universally over every `β` lifting the first Chern class. That is *false*. The lift is not unique:
by the exactness of the support sequence, two lifts differ by the image of
`H¹(X^an ∖ |D|^an, ℚ)` under the connecting map, and such a difference does change the local
multiplicities. Take `X = ℙ¹`, `L = 𝒪`, the rational section `s = z`, so `D = [0] − [∞]` and
`c₁(L) = 0`. Then `H²_{\{0, ∞\}}(ℙ¹, ℚ) ≅ ℚ²` by the two local coclasses, `forgetSupport` is the
sum map `ℚ² → ℚ`, and *both* `β = (1, −1)` and `β = (2, −2)` lift `c₁ = 0`; only the first has the
local multiplicities `(1, −1)` of `D`. So a universally quantified statement is refutable, and any
theorem resting on it rests on an unprovable hypothesis.

The witness `β` is the **relative first Chern class** `c₁(L, s) ∈ H²_{|D|^an}(X^an, ℚ)` of the
pair (line bundle, rational section): the frame of `L^an` on `X^an ∖ |D|^an` supplied by `s`
splits the extension `E` there, and that *splitting*, not merely the vanishing of the restricted
class, determines a canonical lift. Step 3 of §4.3 of `docs/DIVISOR_HANDOFF.md`
(`exists_forgetSupport_eq_integralToRational_firstChernClass`, packaged here as
`HasSupportedChernLift`) only produces *some* lift, by exactness; it is therefore **not** enough
to prove this obligation, and the construction of the canonical lift out of the splitting datum is
part of what is left.

Mathematically the normalisation is the one-variable Lelong–Poincaré computation: in a normal
chart at a smooth point of the component the divisor is `{z₁ = 0}`, the transition cocycle of the
line bundle is that of `z₁^{c.divisor x}` (the local equation of the rational section, by
`Represents` and `extensionFramesOfAlgebraic_transitionUnit`), and `(1/2πi) d log z₁` generates
the first cohomology of the punctured disc. It is where the sign of
`Scheme.CartierData.Represents` is fixed. The reduction of this obligation to the winding
homomorphism of a chart is `Other/AlgebraicGeometry/ChernLocalModelWinding.lean`. -/
def HasChernLocalModel : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∀ c : Scheme.CartierData X.left, c.Represents L →
      ∃ β : SupportedInjectiveHomology X (cycleAnalyticClosedSupport X c.divisor)
          (2 * ((1 : ℕ) : ℤ)),
        supportedInjectiveToAmbient X (cycleAnalyticClosedSupport X c.divisor)
            (2 * ((1 : ℕ) : ℤ)) β =
          rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * ((1 : ℕ) : ℤ))
            (integralToRationalCohomology X 2 E.firstChernClass) ∧
        ∀ γ : ∀ x : X.left,
            SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X x)
              (2 * ((1 : ℕ) : ℤ)),
          β = ∑ x ∈ cycleComponents X c.divisor,
              componentContribution X (cycleComponents X c.divisor) x (2 * ((1 : ℕ) : ℤ)) (γ x) →
          ∀ x ∈ cycleComponents X c.divisor, ∀ hx : coheight x = ((1 : ℕ) : ℕ∞),
            (cycleComponentSupportedClassNormalizationIso X x (d := dim X.left) hx).hom (γ x) =
              (c.divisor x) • cycleComponentSmoothSupportCoclassSection X x (d := dim X.left) hx

/-! ### The assembly -/

variable {X}

/-- A component piece whose smooth-locus normalisation is `n` times the normal-chart coclass is
`n` times the constructed supported component class. This is
`cycleComponentSupportedInjectiveClass_unique` in additive form. -/
theorem eq_zsmul_cycleComponentSupportedInjectiveClass {x : X.left}
    (hx : coheight x = ((1 : ℕ) : ℕ∞)) (n : ℤ)
    (a : SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X x)
      (2 * ((1 : ℕ) : ℤ)))
    (ha : (cycleComponentSupportedClassNormalizationIso X x (d := dim X.left) hx).hom a =
      n • cycleComponentSmoothSupportCoclassSection X x (d := dim X.left) hx) :
    a = n • cycleComponentSupportedInjectiveClass X x (d := dim X.left) hx := by
  refine (cycleComponentSupportedClassNormalizationIso X x
    (d := dim X.left) hx).addCommGroupIsoToAddEquiv.injective ?_
  rw [map_zsmul]
  exact ha.trans (congrArg (fun t => n • t)
    (cycleComponentSupportedInjectiveClass_normalization X x (d := dim X.left) hx).symm)

variable (X)

set_option maxHeartbeats 1000000 in
/-- **The assembly.** The codimension-one excision statement and the local model together prove
the remaining obligation `HasDivisorClassOfSomeCartierData X` of `docs/DIVISOR_HANDOFF.md` §3.

Note that `HasSupportedChernLift` is *not* a hypothesis: the existence of a supported lift is part
of `HasChernLocalModel`, which asks for a *normalised* one. The bare existence supplied by step 3
would not suffice, because the lift is not unique (see the docstring of `HasChernLocalModel`). -/
theorem hasDivisorClassOfSomeCartierData_of_localModel
    (hdec : HasComponentSupportDecomposition X)
    (hloc : HasChernLocalModel X) :
    HasDivisorClassOfSomeCartierData X := by
  intro E L hL iso
  obtain ⟨c, hc⟩ := exists_cartierData_represents X L hL
  refine ⟨c, hc, ?_⟩
  obtain ⟨b, hb, hlocal⟩ := hloc E L hL iso c hc
  obtain ⟨γ, hγ⟩ := hdec (cycleComponents X c.divisor)
    (fun x hx => coheight_of_mem_cycleComponents X hx) b
  have hnorm := hlocal γ hγ
  have key : ∀ x ∈ cycleComponents X c.divisor,
      supportedInjectiveToAmbient X (componentsAnalyticClosedSupport X
          (cycleComponents X c.divisor)) (2 * ((1 : ℕ) : ℤ))
        (componentContribution X (cycleComponents X c.divisor) x (2 * ((1 : ℕ) : ℤ)) (γ x)) =
      c.divisor x • rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * ((1 : ℕ) : ℤ))
        (if hx : coheight x = ((1 : ℕ) : ℕ∞) then
            cycleComponentSheafClass X x (d := dim X.left) hx else 0) := by
    intro x hxs
    have hx1 : coheight x = ((1 : ℕ) : ℕ∞) := coheight_of_mem_cycleComponents X hxs
    have hγx : γ x = c.divisor x • cycleComponentSupportedInjectiveClass X x
        (d := dim X.left) hx1 :=
      eq_zsmul_cycleComponentSupportedInjectiveClass hx1 _ (γ x) (hnorm x hxs hx1)
    rw [supportedInjectiveToAmbient_componentContribution X hxs, hγx, map_zsmul, dif_pos hx1]
    congr 1
    exact (AddEquiv.apply_symm_apply
      (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * ((1 : ℕ) : ℤ))) _).symm
  apply (rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * ((1 : ℕ) : ℤ))).injective
  rw [sheafCycleClassOnCycles_eq_sum X c.divisor, map_sum, ← hb, hγ, map_sum]
  refine Finset.sum_congr rfl fun x hxs => ?_
  rw [key x hxs, map_zsmul]

end AlgebraicGeometry.ComplexPoint
