/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernRelativeChartFormula
public import Other.AlgebraicGeometry.ChernLocalModelWinding

/-!
# Generic-local interface for the Chern chart formula

The cohomological formula is only needed on compatible winding charts covering the smooth locus
away from a proper closed subset of each component.  This file keeps the constructed supported
class and its ambient comparison while making that local quantifier explicit.  It is a reduction
interface; the actual frame and support comparison is proved separately.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open CategoryTheory.Localization
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance genericLocalChartFormulaTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

def HasRelativeChernChartFormulaGenericLocal : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∀ c : Scheme.CartierData X.left, c.Represents L →
      ∃ β : SupportedInjectiveHomology X (cycleAnalyticClosedSupport X c.divisor) (2 : ℤ),
        supportedInjectiveToAmbient X (cycleAnalyticClosedSupport X c.divisor) (2 : ℤ) β =
          rationalCohomologyAddEquivAmbientInjectiveHomology X 2
            (integralToRationalCohomology X 2 E.firstChernClass) ∧
        ∀ γ : ∀ x : X.left, SupportedInjectiveHomology
            X (cycleComponentAnalyticClosedSupport X x) (2 : ℤ),
          β = ∑ x ∈ cycleComponents X c.divisor,
              componentContribution X (cycleComponents X c.divisor) x (2 : ℤ) (γ x) →
          ∀ x ∈ cycleComponents X c.divisor, ∀ hx : coheight x = ((1 : ℕ) : ℕ∞),
            ∃ B : Closeds X.left,
              (B : Set X.left) ⊆ closure ({x} : Set X.left) ∧ x ∉ B ∧
              ∀ q ∈ cycleComponentSmoothSupportAmbientOpen X x,
                q ∈ cycleComponentSupport X x → Point.underlying q ∉ B →
                ∀ ch : ChernWindingChart X c x (dim X.left) 1 q,
                  ch.HasTrivialUnitWinding → ch.NormalizesCoclass hx →
                  ch.ComputesClass (c.divisor x)
                    ((cycleComponentSupportedClassNormalizationIso X x hx).hom (γ x))

set_option maxHeartbeats 1000000 in
/-- The generic-local formula is sufficient for the full local model: taking the union of its
exceptional closed set with the chart exceptional set (equivalently, intersecting the good opens)
preserves injectivity of restriction. -/
theorem hasChernLocalModel_of_chartFormulaGenericLocal
    (hcharts : HasNormalizedWindingCharts X)
    (hformula : HasRelativeChernChartFormulaGenericLocal X) :
    HasChernLocalModel X := by
  intro E L hL iso c hc
  obtain ⟨β, hβ, hnat⟩ := hformula E L hL iso c hc
  refine ⟨β, hβ, ?_⟩
  intro γ hγ x hxs hx
  obtain ⟨B₁, hB₁, hxB₁, hch⟩ := hcharts c x hx
  obtain ⟨B₂, hB₂, hxB₂, hformula'⟩ := hnat γ hγ x hxs hx
  choose ch hunit hnorm using
    fun q : {q : ComplexPoint X // q ∈ cycleComponentSmoothSupportAmbientOpen X x ∧
        q ∈ cycleComponentSupport X x ∧ Point.underlying q ∉ B₁} =>
      hch q.1 q.2.1 q.2.2.1 q.2.2.2
  let B : Closeds X.left := B₁ ⊔ B₂
  have hB : (B : Set X.left) ⊆ closure ({x} : Set X.left) := by
    intro z hz
    rcases hz with hz | hz
    · exact hB₁ hz
    · exact hB₂ hz
  have hxB : x ∉ B := by
    intro hxB
    rcases hxB with hxB | hxB
    · exact hxB₁ hxB
    · exact hxB₂ hxB
  refine cycleComponentSmoothSupport_restriction_injective X x (d := dim X.left) hx B hB hxB ?_
  refine TopCat.Sheaf.eq_of_locally_eq'
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * 1))
    (fun q : Option {q : ComplexPoint X // q ∈ cycleComponentSmoothSupportAmbientOpen X x ∧
        q ∈ cycleComponentSupport X x ∧ Point.underlying q ∉ B} =>
      q.elim ((cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl) ⊓
        (cycleComponentAnalyticClosedSupport X x).compl)
        (fun q => (ch ⟨q, q.2.1, q.2.2.1, fun h => q.2.2.2 (Or.inl h)⟩).carrier ⊓
          (cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl)))
    (cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl)
    (fun q => match q with
      | none => homOfLE inf_le_left
      | some _ => homOfLE inf_le_right) ?_ _ _ ?_
  · intro y hy
    rw [Opens.mem_iSup]
    by_cases hyS : y ∈ cycleComponentSupport X x
    · let y₁ : {q : ComplexPoint X // q ∈ cycleComponentSmoothSupportAmbientOpen X x ∧
          q ∈ cycleComponentSupport X x ∧ Point.underlying q ∉ B₁} :=
        ⟨y, hy.1, hyS, fun h => hy.2 (Or.inl h)⟩
      exact ⟨some ⟨y, hy.1, hyS, hy.2⟩, (ch y₁).mem, hy⟩
    · exact ⟨none, hy, hyS⟩
  · rintro (_ | q)
    · have hVS : ∀ y ∈ ((cycleComponentSmoothSupportAmbientOpen X x ⊓
          (analyticClosedSupport X B).compl) ⊓
          (cycleComponentAnalyticClosedSupport X x).compl :
            Opens (TopCat.of (ComplexPoint X))), y ∉ cycleComponentSupport X x :=
        fun _ hy => hy.2
      exact (supportRelativeCohomologySheaf_section_eq_zero
          (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x) (2 * 1)
          (cycleComponentAnalyticClosedSupport X x).isClosed _ hVS _).trans
        (supportRelativeCohomologySheaf_section_eq_zero
          (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x) (2 * 1)
          (cycleComponentAnalyticClosedSupport X x).isClosed _ hVS _).symm
    · have hqB₁ : Point.underlying q.1 ∉ B₁ := by
        intro hq
        exact q.2.2.2 (Or.inl hq)
      have hqB₂ : Point.underlying q.1 ∉ B₂ := by
        intro hq
        exact q.2.2.2 (Or.inr hq)
      let q₁ : {q : ComplexPoint X // q ∈ cycleComponentSmoothSupportAmbientOpen X x ∧
          q ∈ cycleComponentSupport X x ∧ Point.underlying q ∉ B₁} :=
        ⟨q.1, q.2.1, q.2.2.1, hqB₁⟩
      let q₂ : {q : ComplexPoint X // q ∈ cycleComponentSmoothSupportAmbientOpen X x ∧
          q ∈ cycleComponentSupport X x ∧ Point.underlying q ∉ B₂} :=
        ⟨q.1, q.2.1, q.2.2.1, hqB₂⟩
      let chq := ch q₁
      have hcomp := hformula' q₂.1 q₂.2.1 q₂.2.2.1 q₂.2.2.2 chq (hunit q₁) (hnorm q₁)
      have key := chq.restrict_eq_zsmul_coclass hx (c.divisor x) _ hcomp (hunit q₁) (hnorm q₁)
      let F := supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * 1)
      let U' : Opens (ComplexPoint X) :=
        cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl
      let i : chq.carrier ⊓ U' ⟶ U' := homOfLE inf_le_right
      let j : U' ⟶ cycleComponentSmoothSupportAmbientOpen X x := homOfLE inf_le_left
      let k : chq.carrier ⊓ U' ⟶ chq.carrier := homOfLE inf_le_left
      let l : chq.carrier ⟶ cycleComponentSmoothSupportAmbientOpen X x :=
        homOfLE chq.le
      let m : chq.carrier ⊓ U' ⟶ cycleComponentSmoothSupportAmbientOpen X x :=
        homOfLE (le_trans inf_le_left chq.le)
      have hcomp' := congrArg (F.obj.map k.op) key
      exact (sheaf_map_map_eq F i j m _).trans
        ((sheaf_map_map_eq F k l m _).symm.trans (hcomp'.trans
          ((sheaf_map_map_eq F k l m _).trans (sheaf_map_map_eq F i j m _).symm)))

end AlgebraicGeometry.ComplexPoint
