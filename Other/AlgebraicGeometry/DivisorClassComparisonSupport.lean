/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.SheafCycleClass
public import Other.AlgebraicGeometry.DivisorObligations
public import Other.AlgebraicGeometry.ChernClassRestrictionVanishing

/-!
# Support bookkeeping for the divisor/first-Chern-class comparison

Step 3 of `docs/DIVISOR_HANDOFF.md` §4.3 produces a rational class *supported on the whole
analytic support `|D|^an` of the divisor*, while the constructed cycle class
`sheafCycleClassOnCycles` is a finite sum of classes each supported on the analytic support of a
*single* component. This file provides the bookkeeping that connects the two, entirely inside the
concrete "supported injective sections" model in which both the constructed component classes
(`cycleComponentSupportedInjectiveClass`) and `forgetSupport`
(`rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport`) are already expressed.

* `SupportedInjectiveHomology X S n` — the supported group itself, abbreviating the homology of
  the global sections of the `S`-supported part of the ambient rational injective resolution.
* `enlargeSupportedInjectiveHomology X (h : S ≤ T) n` — the support-enlargement map, from the
  coefficient-level `TopCat.Sheaf.sheafSectionsWithClosedSupportMap`.
* `supportedInjectiveToAmbient X S n` — the map to ordinary cohomology used by
  `cycleComponentSheafClass`, and `supportedInjectiveToAmbient_enlarge`: **enlarging the support
  does not change the ordinary class**. This is the only fact about supports that the final
  assembly needs, and it is proved, not assumed.
* `componentsAnalyticClosedSupport X s` — the analytic support `|D|^an` of a finite set `s` of
  codimension-one points, as a `Closeds`, together with `componentContribution`, the
  enlargement of a class supported on one component into it.
* `cycleComponents D` — the finite set of components of a codimension-one cycle, and
  `sheafCycleClassOnCycles_eq_sum`, the explicit finite-sum formula for its constructed class.

Nothing here is an obligation: every declaration is proved.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance divisorClassComparisonAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

/-! ### The supported injective model and its support functoriality -/

/-- Rational cohomology with support in a closed analytic set `S`, in the concrete model used by
`cycleComponentSupportedInjectiveClass`: the homology of the global sections of the `S`-supported
part of the ambient rational injective resolution. -/
abbrev SupportedInjectiveHomology (S : Closeds (ComplexPoint X)) (n : ℤ) :=
  ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
    (.up ℤ)).obj (complexSupportInjectiveComplex X S)).homology n)

/-- Enlarging the support, at the level of the supported injective coefficient complexes. -/
def supportedInjectiveComplexMap {S T : Closeds (ComplexPoint X)} (h : S ≤ T) :
    complexSupportInjectiveComplex X S ⟶ complexSupportInjectiveComplex X T :=
  (NatTrans.mapHomologicalComplex
      (TopCat.Sheaf.sheafSectionsWithClosedSupportMap (TopCat.of (ComplexPoint X)) h)
      (ComplexShape.up ℤ)).app (ambientRationalInjectiveComplex X)

/-- Enlarging the support, on supported cohomology. -/
def enlargeSupportedInjectiveHomology {S T : Closeds (ComplexPoint X)} (h : S ≤ T) (n : ℤ) :
    SupportedInjectiveHomology X S n ⟶ SupportedInjectiveHomology X T n :=
  HomologicalComplex.homologyMap
    (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
        (.up ℤ)).map (supportedInjectiveComplexMap X h)) n

/-- Forgetting the support, in the concrete model. This is the map already used by
`cycleComponentSheafClass` and by
`rationalSupportAddEquivSupportedInjectiveHomology_forgetSupport`. -/
def supportedInjectiveToAmbient (S : Closeds (ComplexPoint X)) (n : ℤ) :
    SupportedInjectiveHomology X S n ⟶
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex (TopCat.of (ComplexPoint X))
        S.compl ⊤ (ambientRationalInjectiveComplex X)).X₂.homology n :=
  HomologicalComplex.homologyMap
    (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex (TopCat.of (ComplexPoint X))
      S.compl ⊤ (ambientRationalInjectiveComplex X)).f n

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Support enlargement is compatible with the inclusion into the ambient coefficient complex.
This is the coefficient-level statement `sheafSectionsSupportedOutsideMap_inclusion`. -/
theorem supportedInjectiveComplexMap_comp_f {S T : Closeds (ComplexPoint X)} (h : S ≤ T) :
    supportedInjectiveComplexMap X h ≫
        (TopCat.Sheaf.supportRestrictionComplexShortComplex (TopCat.of (ComplexPoint X))
          T.compl (ambientRationalInjectiveComplex X)).f =
      (TopCat.Sheaf.supportRestrictionComplexShortComplex (TopCat.of (ComplexPoint X))
        S.compl (ambientRationalInjectiveComplex X)).f := by
  ext n
  exact NatTrans.congr_app
    (TopCat.Sheaf.sheafSectionsSupportedOutsideMap_inclusion (TopCat.of (ComplexPoint X))
      (show T.compl ≤ S.compl from fun _ hy hz => hy (h hz)))
    ((ambientRationalInjectiveComplex X).X n)

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
set_option backward.isDefEq.respectTransparency false in
/-- The same statement after taking global sections. -/
theorem supportedInjectiveSectionsMap_comp_f {S T : Closeds (ComplexPoint X)} (h : S ≤ T) :
    ((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
        (.up ℤ)).map (supportedInjectiveComplexMap X h) ≫
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex (TopCat.of (ComplexPoint X))
        T.compl ⊤ (ambientRationalInjectiveComplex X)).f =
      (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex (TopCat.of (ComplexPoint X))
        S.compl ⊤ (ambientRationalInjectiveComplex X)).f := by
  rw [show (TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex (TopCat.of (ComplexPoint X))
        T.compl ⊤ (ambientRationalInjectiveComplex X)).f =
      ((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
        (.up ℤ)).map (TopCat.Sheaf.supportRestrictionComplexShortComplex
          (TopCat.of (ComplexPoint X)) T.compl (ambientRationalInjectiveComplex X)).f from rfl,
    ← Functor.map_comp, supportedInjectiveComplexMap_comp_f]
  rfl

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
set_option backward.isDefEq.respectTransparency false in
/-- Enlarging the support does not change the ordinary class. -/
theorem enlargeSupportedInjectiveHomology_comp_toAmbient
    {S T : Closeds (ComplexPoint X)} (h : S ≤ T) (n : ℤ) :
    enlargeSupportedInjectiveHomology X h n ≫ supportedInjectiveToAmbient X T n =
      supportedInjectiveToAmbient X S n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (fun f => HomologicalComplex.homologyMap f n)
      (supportedInjectiveSectionsMap_comp_f X h))

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Enlarging the support does not change the ordinary class, on elements. -/
theorem supportedInjectiveToAmbient_enlarge {S T : Closeds (ComplexPoint X)} (h : S ≤ T) (n : ℤ)
    (a : SupportedInjectiveHomology X S n) :
    supportedInjectiveToAmbient X T n (enlargeSupportedInjectiveHomology X h n a) =
      supportedInjectiveToAmbient X S n a := by
  rw [← ConcreteCategory.comp_apply, enlargeSupportedInjectiveHomology_comp_toAmbient]
  rfl

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Enlarging the support along the identity is the identity. -/
@[simp]
theorem enlargeSupportedInjectiveHomology_refl (S : Closeds (ComplexPoint X)) (n : ℤ) :
    enlargeSupportedInjectiveHomology X (le_refl S) n = 𝟙 _ := by
  have h : supportedInjectiveComplexMap X (le_refl S) = 𝟙 _ := by
    rw [supportedInjectiveComplexMap,
      show TopCat.Sheaf.sheafSectionsWithClosedSupportMap (TopCat.of (ComplexPoint X))
          (le_refl S) =
        𝟙 (TopCat.Sheaf.sheafSectionsWithClosedSupport (TopCat.of (ComplexPoint X)) S) from
        TopCat.Sheaf.sheafSectionsSupportedOutsideMap_refl (TopCat.of (ComplexPoint X)) S.compl]
    rfl
  rw [enlargeSupportedInjectiveHomology, h, CategoryTheory.Functor.map_id]
  exact HomologicalComplex.homologyMap_id _ n

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Support enlargement along an equality of supports is surjective. -/
theorem exists_enlargeSupportedInjectiveHomology_eq {S T : Closeds (ComplexPoint X)}
    (h : S ≤ T) (he : S = T) (n : ℤ) (b : SupportedInjectiveHomology X T n) :
    ∃ a : SupportedInjectiveHomology X S n,
      enlargeSupportedInjectiveHomology X h n a = b := by
  subst he
  exact ⟨b, by rw [enlargeSupportedInjectiveHomology_refl]; rfl⟩

/-! ### The analytic support of a finite family of components -/

/-- The analytic support `|D|^an` of a finite family of points of `X.left`: the union of the
analytic supports of the corresponding irreducible closed subsets. -/
def componentsAnalyticClosedSupport (s : Finset X.left) : Closeds (ComplexPoint X) :=
  s.sup fun x => cycleComponentAnalyticClosedSupport X x

theorem cycleComponentAnalyticClosedSupport_le_componentsAnalyticClosedSupport
    {s : Finset X.left} {x : X.left} (hx : x ∈ s) :
    cycleComponentAnalyticClosedSupport X x ≤ componentsAnalyticClosedSupport X s :=
  Finset.le_sup (f := fun y => cycleComponentAnalyticClosedSupport X y) hx

open scoped Classical in
/-- The contribution of one component to a class supported on the whole family: the
support-enlargement map when `x` belongs to the family, and zero otherwise. -/
def componentContribution (s : Finset X.left) (x : X.left) (n : ℤ)
    (a : SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X x) n) :
    SupportedInjectiveHomology X (componentsAnalyticClosedSupport X s) n :=
  if hx : x ∈ s then
    enlargeSupportedInjectiveHomology X
      (cycleComponentAnalyticClosedSupport_le_componentsAnalyticClosedSupport X hx) n a
  else 0

theorem componentContribution_of_mem {s : Finset X.left} {x : X.left} (hx : x ∈ s) (n : ℤ)
    (a : SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X x) n) :
    componentContribution X s x n a =
      enlargeSupportedInjectiveHomology X
        (cycleComponentAnalyticClosedSupport_le_componentsAnalyticClosedSupport X hx) n a := by
  classical
  rw [componentContribution, dif_pos hx]

/-- The ordinary class of a component contribution is the ordinary class of the component. -/
theorem supportedInjectiveToAmbient_componentContribution
    {s : Finset X.left} {x : X.left} (hx : x ∈ s) (n : ℤ)
    (a : SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X x) n) :
    supportedInjectiveToAmbient X (componentsAnalyticClosedSupport X s) n
        (componentContribution X s x n a) =
      supportedInjectiveToAmbient X (cycleComponentAnalyticClosedSupport X x) n a := by
  rw [componentContribution_of_mem X hx, supportedInjectiveToAmbient_enlarge]

/-- The analytic support of a one-element family is the support of that component. -/
@[simp]
theorem componentsAnalyticClosedSupport_singleton (x : X.left) :
    componentsAnalyticClosedSupport X {x} = cycleComponentAnalyticClosedSupport X x := by
  rw [componentsAnalyticClosedSupport, Finset.sup_singleton]

/-- **Non-vacuity of the decomposition obligation.** For a one-element family the required
decomposition exists: the enlargement map is the identity. -/
theorem exists_componentContribution_sum_singleton (x : X.left) (n : ℤ)
    (β : SupportedInjectiveHomology X (componentsAnalyticClosedSupport X {x}) n) :
    ∃ γ : ∀ y : X.left,
        SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X y) n,
      β = ∑ y ∈ ({x} : Finset X.left), componentContribution X {x} y n (γ y) := by
  classical
  obtain ⟨a, ha⟩ := exists_enlargeSupportedInjectiveHomology_eq X
    (cycleComponentAnalyticClosedSupport_le_componentsAnalyticClosedSupport X
      (Finset.mem_singleton_self x))
    (componentsAnalyticClosedSupport_singleton X x).symm n β
  refine ⟨fun y => if hy : y = x then hy ▸ a else 0, ?_⟩
  rw [Finset.sum_singleton, componentContribution_of_mem X (Finset.mem_singleton_self x)]
  simp only
  rw [dif_pos trivial]
  exact ha.symm

/-! ### Components of a codimension-one cycle -/

/-- The finite set of components of a codimension-one cycle on the projective variety `X.left`. -/
def cycleComponents (D : CodimensionCycle X.left 1) : Finset X.left :=
  (compactCycleToFinsupp D.1).support

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Membership in the component set is nonvanishing of the multiplicity. -/
theorem mem_cycleComponents_iff (D : CodimensionCycle X.left 1) (x : X.left) :
    x ∈ cycleComponents X D ↔ D.1 x ≠ 0 := by
  rw [cycleComponents, Finsupp.mem_support_iff]
  exact Iff.rfl

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Every component of a codimension-one cycle has coheight one. -/
theorem coheight_of_mem_cycleComponents {D : CodimensionCycle X.left 1} {x : X.left}
    (hx : x ∈ cycleComponents X D) : coheight x = ((1 : ℕ) : ℕ∞) :=
  D.2 x ((mem_cycleComponents_iff X D x).mp hx)

/-- The analytic support `|D|^an` of a codimension-one cycle. -/
abbrev cycleAnalyticClosedSupport (D : CodimensionCycle X.left 1) : Closeds (ComplexPoint X) :=
  componentsAnalyticClosedSupport X (cycleComponents X D)

/-- The constructed cycle class of a codimension-one cycle is the explicit finite sum of its
component classes with their exact integer multiplicities. -/
theorem sheafCycleClassOnCycles_eq_sum (D : CodimensionCycle X.left 1) :
    sheafCycleClassOnCycles (DimensionedSmoothProjectiveComplexVariety.ofOver X) 1 D =
      ∑ x ∈ cycleComponents X D, D.1 x •
        (if hx : coheight x = ((1 : ℕ) : ℕ∞) then
            cycleComponentSheafClass X x (d := dim X.left) hx
          else 0) := by
  rw [show sheafCycleClassOnCycles (DimensionedSmoothProjectiveComplexVariety.ofOver X) 1 D =
      (compactCycleToFinsupp D.1).sum fun x n ↦
        n • if hx : coheight x = ((1 : ℕ) : ℕ∞) then
            cycleComponentSheafClass X x (d := dim X.left) hx else 0 from rfl]
  rfl

end AlgebraicGeometry.ComplexPoint
