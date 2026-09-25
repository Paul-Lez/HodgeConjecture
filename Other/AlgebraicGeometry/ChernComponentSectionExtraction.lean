/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernComponentLocalIsolation
public import Other.AlgebraicGeometry.SupportedInjectiveSectionNaturality
public import Other.AlgebraicGeometry.ChernWindingLocalFormObstruction
public import Other.AlgebraicGeometry.Cycle.Component.PointClassNormalization
public import Other.AlgebraicTopology.Sheaf.CohomologySectionNaturality
public import HodgeConjecture.Lemmas.AlgebraicTopology.Support.SectionRestrictionCone

/-! Restriction and component isolation for supported local sections. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open AlgebraicTopology.Singular
open AlgebraicGeometry

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernComponentSectionExtractionTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable {X}

/-- The section of the cohomology sheaf over `W` obtained by restricting a global supported
class. -/
def supportedInjectiveLocalSection {S : Closeds (ComplexPoint X)}
    (W : Opens (TopCat.of (ComplexPoint X))) (n : ℤ)
    (a : SupportedInjectiveHomology X S n) :
    ((complexSupportInjectiveComplex X S).homology n).presheaf.obj (op W) :=
  TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
      (complexSupportInjectiveComplex X S) n W
    (HomologicalComplex.homologyMap
      (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) (.up ℤ)
        (complexSupportInjectiveComplex X S)
        (homOfLE (le_top : W ≤ ⊤))) n a)

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem supportedInjectiveLocalSection_eq_zero_of_le_compl
    {S : Closeds (ComplexPoint X)} (W : Opens (TopCat.of (ComplexPoint X)))
    (hWS : W ≤ S.compl) (a : SupportedInjectiveHomology X S (2 : ℤ)) :
    supportedInjectiveLocalSection W (2 : ℤ) a = 0 := by
  have hzero : IsZero ((((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex X S)).homology (2 : ℤ)) := by
    apply ShortComplex.isZero_homology_of_isZero_X₂
    exact TopCat.Sheaf.supportedOutsideSections_isZero_of_le
      (TopCat.of (ComplexPoint X)) S.compl W
      ((ambientRationalInjectiveComplex X).X (2 : ℤ)) hWS
  let h := HomologicalComplex.homologyMap
    (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) (.up ℤ)
      (complexSupportInjectiveComplex X S) (homOfLE (le_top : W ≤ ⊤))) (2 : ℤ)
  let hsub : Subsingleton ((((TopCat.Sheaf.supportEvaluation
      (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex (.up ℤ)).obj
        (complexSupportInjectiveComplex X S)).homology (2 : ℤ)) :=
    AddCommGrpCat.subsingleton_of_isZero hzero
  have ha : (ConcreteCategory.hom h) a = 0 := @Subsingleton.elim _ hsub _ _
  change (ConcreteCategory.hom
    (TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
      (complexSupportInjectiveComplex X S) (2 : ℤ) W))
      ((ConcreteCategory.hom h) a) = 0
  rw [ha, map_zero]

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem supportedInjectiveLocalSection_enlarge
    {S T : Closeds (ComplexPoint X)} (hST : S ≤ T)
    (W : Opens (TopCat.of (ComplexPoint X))) (n : ℤ)
    (a : SupportedInjectiveHomology X S n) :
    supportedInjectiveLocalSection W n
        (enlargeSupportedInjectiveHomology X hST n a) =
      (HomologicalComplex.homologyMap (supportedInjectiveComplexMap X hST) n).hom.app
      (op W) (supportedInjectiveLocalSection W n a) := by
  dsimp only [supportedInjectiveLocalSection, enlargeSupportedInjectiveHomology]
  have hcomp :
      HomologicalComplex.homologyMap
          (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) (.up ℤ)
            (complexSupportInjectiveComplex X T) (homOfLE (le_top : W ≤ ⊤))) n
        ((HomologicalComplex.homologyMap
          (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
            (.up ℤ)).map (supportedInjectiveComplexMap X hST)) n) a) =
      HomologicalComplex.homologyMap
          (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) W).mapHomologicalComplex
            (.up ℤ)).map (supportedInjectiveComplexMap X hST)) n
        (HomologicalComplex.homologyMap
          (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) (.up ℤ)
            (complexSupportInjectiveComplex X S) (homOfLE (le_top : W ≤ ⊤))) n a) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      sectionComplexRestriction_comp_supportedInjectiveComplexMap]
  rw [hcomp]
  exact supportedInjectiveComplexMap_section_apply hST n W _

theorem componentContribution_localSection_eq_zero_of_le_compl
    {s : Finset X.left} {y : X.left}
    (W : Opens (TopCat.of (ComplexPoint X)))
    (hWY : W ≤ (cycleComponentAnalyticClosedSupport X y).compl)
    (a : SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X y) (2 : ℤ)) :
    supportedInjectiveLocalSection W (2 : ℤ)
        (componentContribution X s y (2 : ℤ) a) = 0 := by
  classical
  by_cases hy : y ∈ s
  · rw [componentContribution_of_mem X hy]
    rw [supportedInjectiveLocalSection_enlarge,
      supportedInjectiveLocalSection_eq_zero_of_le_compl W hWY, map_zero]
  · simp [componentContribution, hy, supportedInjectiveLocalSection]

namespace ChernWindingChart

variable {c : Scheme.CartierData X.left} {x : X.left} {d p : ℕ}
  [SmoothOfRelativeDimension d X.hom] {q : ComplexPoint X}

theorem carrier_le_component_compl_of_divisor_ne_zero
    (ch : ChernWindingChart X c x d p q) (hx : coheight x = ((1 : ℕ) : ℕ∞))
    {y : X.left} (hy : coheight y = ((1 : ℕ) : ℕ∞)) (hyx : y ≠ x)
    (hyd : c.divisor y ≠ 0) :
    ch.carrier ≤ (cycleComponentAnalyticClosedSupport X y).compl := by
  intro z hz hzY
  change Point.underlying z ∈ closure ({y} : Set X.left) at hzY
  have hzOpen : Point.underlying z ∈ ch.localForm.opens := by
    exact ch.le_analytic hz
  obtain ⟨z', hz', hzEq⟩ := mem_closure_iff.mp hzY _ ch.localForm.opens.isOpen hzOpen
  have hyOpen : y ∈ ch.localForm.opens := by
    simpa [Set.mem_singleton_iff.mp hzEq] using hz'
  exact ch.localForm.notMem_of_divisor_ne_zero hx hy hyx hyd hyOpen

end ChernWindingChart

theorem normalizedComponentSection_restrict_eq_zero_of_le_compl
    {x : X.left} (hx : coheight x = ((1 : ℕ) : ℕ∞))
    (a : SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X x) (2 : ℤ))
    (W : Opens (TopCat.of (ComplexPoint X)))
    (hWU : W ≤ cycleComponentSmoothSupportAmbientOpen X x)
    (hWS : W ≤ (cycleComponentAnalyticClosedSupport X x).compl) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * 1)).obj.map (homOfLE hWU).op
      ((cycleComponentSupportedClassNormalizationIso X x hx).hom a) = 0 := by
  apply AlgebraicTopology.Singular.supportRelativeCohomologySheaf_section_eq_zero
    (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x) (2 * 1)
    (cycleComponentAnalyticClosedSupport X x).isClosed W
  intro z hz
  exact hWS hz

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem supportedInjectiveLocalSection_sum {ι : Type*}
    {S : Closeds (ComplexPoint X)} (W : Opens (TopCat.of (ComplexPoint X))) (n : ℤ)
    (s : Finset ι) (a : ι → SupportedInjectiveHomology X S n) :
    supportedInjectiveLocalSection W n (∑ i ∈ s, a i) =
      ∑ i ∈ s, supportedInjectiveLocalSection W n (a i) := by
  dsimp only [supportedInjectiveLocalSection]
  let f := TopCat.Sheaf.sectionCohomologyToSheafSection
    (TopCat.of (ComplexPoint X)) (complexSupportInjectiveComplex X S) n W
  let h := HomologicalComplex.homologyMap
    (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) (.up ℤ)
      (complexSupportInjectiveComplex X S) (homOfLE (le_top : W ≤ ⊤))) n
  rw [map_sum (ConcreteCategory.hom h) a s]
  exact map_sum (ConcreteCategory.hom f) _ s

theorem supportedInjectiveLocalSection_sum_of_componentContribution
    {s : Finset X.left}
    (b : SupportedInjectiveHomology X (componentsAnalyticClosedSupport X s) (2 : ℤ))
    (γ : ∀ y : X.left,
      SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X y) (2 : ℤ))
    (hγ : b = ∑ y ∈ s, componentContribution X s y (2 : ℤ) (γ y))
    (W : Opens (TopCat.of (ComplexPoint X))) :
    supportedInjectiveLocalSection W (2 : ℤ) b =
      ∑ y ∈ s, supportedInjectiveLocalSection W (2 : ℤ)
        (componentContribution X s y (2 : ℤ) (γ y)) := by
  rw [hγ]
  rw [supportedInjectiveLocalSection_sum]

theorem supportedInjectiveLocalSection_eq_component_of_componentContribution_sum
    {s : Finset X.left} {x : X.left} (hx : x ∈ s)
    (b : SupportedInjectiveHomology X (componentsAnalyticClosedSupport X s) (2 : ℤ))
    (γ : ∀ y : X.left,
      SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X y) (2 : ℤ))
    (hγ : b = ∑ y ∈ s, componentContribution X s y (2 : ℤ) (γ y))
    (W : Opens (TopCat.of (ComplexPoint X)))
    (hW : ∀ y ∈ s, y ≠ x →
      W ≤ (cycleComponentAnalyticClosedSupport X y).compl) :
    supportedInjectiveLocalSection W (2 : ℤ) b =
      (HomologicalComplex.homologyMap
        (supportedInjectiveComplexMap X
          (cycleComponentAnalyticClosedSupport_le_componentsAnalyticClosedSupport X hx))
        (2 : ℤ)).hom.app (op W)
        (supportedInjectiveLocalSection W (2 : ℤ) (γ x)) := by
  rw [supportedInjectiveLocalSection_sum_of_componentContribution b γ hγ W]
  rw [Finset.sum_eq_single x]
  · rw [componentContribution_of_mem X hx]
    exact supportedInjectiveLocalSection_enlarge _ W _ _
  · intro y hy hne
    exact componentContribution_localSection_eq_zero_of_le_compl W
      (hW y hy hne) (γ y)
  · intro hnot
    exact (hnot hx).elim

namespace ChernWindingChart

variable {c : Scheme.CartierData X.left} {x : X.left} {d p : ℕ}
  [SmoothOfRelativeDimension d X.hom] {q : ComplexPoint X}

theorem carrier_localSection_eq_component_of_componentContribution_sum
    (ch : ChernWindingChart X c x d p q)
    (hx : coheight x = ((1 : ℕ) : ℕ∞))
    {s : Finset X.left} (hxS : x ∈ s)
    (hco : ∀ y ∈ s, coheight y = ((1 : ℕ) : ℕ∞))
    (hdiv : ∀ y ∈ s, c.divisor y ≠ 0)
    (b : SupportedInjectiveHomology X (componentsAnalyticClosedSupport X s) (2 : ℤ))
    (γ : ∀ y : X.left,
      SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X y) (2 : ℤ))
    (hγ : b = ∑ y ∈ s, componentContribution X s y (2 : ℤ) (γ y)) :
    supportedInjectiveLocalSection ch.carrier (2 : ℤ) b =
      (HomologicalComplex.homologyMap
        (supportedInjectiveComplexMap X
          (cycleComponentAnalyticClosedSupport_le_componentsAnalyticClosedSupport X hxS))
        (2 : ℤ)).hom.app (op ch.carrier)
        (supportedInjectiveLocalSection ch.carrier (2 : ℤ) (γ x)) := by
  apply supportedInjectiveLocalSection_eq_component_of_componentContribution_sum
    hxS b γ hγ ch.carrier
  intro y hy hyx
  exact ch.carrier_le_component_compl_of_divisor_ne_zero hx (hco y hy) hyx (hdiv y hy)

end ChernWindingChart

end AlgebraicGeometry.ComplexPoint
