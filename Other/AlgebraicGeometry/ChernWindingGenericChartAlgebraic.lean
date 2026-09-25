/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the LICENSE file.
-/
module

public import Other.AlgebraicGeometry.ChernWindingGenericChartCanonical
public import Other.AlgebraicGeometry.ChernWindingGenericChartExistence
public import Other.AlgebraicGeometry.CartierLocalDerivativePointJet

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace Opposite Order
open AlgebraicTopology.Singular
open scoped Manifold ContDiff

namespace AlgebraicGeometry.ComplexPoint

open AlgebraicGeometry.ComplexPoint.Affine

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

attribute [local instance] isNoetherian_of_isProjective

set_option maxHeartbeats 1000000 in
/-- The algebraic local-form shrink supplies the input needed by the canonical chart constructor.
The returned carrier can be forced below any analytic neighbourhood `N` of the point. -/
theorem exists_genericWindingChartData_of_component_algebraic
    (c : Scheme.CartierData X.left) (x : X.left)
    (hx : coheight x = ((1 : ℕ) : ℕ∞))
    (i : c.ι) (f : c.LocalForm i x)
    (s : Γ(X.left, f.opens))
    (hs : s ∉ (f.isAffineOpen.primeIdealOf ⟨x, f.mem⟩).asIdeal)
    (hEq :
      (f.isAffineOpen.primeIdealOf ⟨x, f.mem⟩).asIdeal.map
          (algebraMap (Γ(X.left, f.opens)) (Localization.Away s)) =
        (Ideal.span {f.equation}).map
          (algebraMap (Γ(X.left, f.opens)) (Localization.Away s)))
    (z : ComplexPoint (cycleComponentSmoothLocusOver X x))
    (q : ComplexPoint X)
    (hq : q = Point.map (ComplexPoint.openInclusion X
      (cycleComponentSmoothLocusAmbientOpen X x))
        (Point.map (cycleComponentSmoothLocusClosedLiftOver X x) z))
    (N : Opens (ComplexPoint X)) (hqN : q ∈ N)
    (hN : N ≤ analyticOpen X f.opens)
    (hys : q ∈ analyticOpen X (X.left.basicOpen s)) :
    ∃ G : GenericWindingChartData X c x (dim X.left) q,
      G.toChart.carrier ≤ N := by
  subst q
  let M := cycleComponentSmoothLocusAmbientOpenOver X x
  let r := ComplexPoint.openInclusion X (cycleComponentSmoothLocusAmbientOpen X x)
  let j := cycleComponentSmoothLocusClosedLiftOver X x
  let D := dim X.left
  have hqOpen : Point.map r (Point.map j z) ∈ analyticOpen X f.opens := hN hqN
  have hqBasic : Point.map r (Point.map j z) ∈ analyticOpen X (X.left.basicOpen s) := hys
  have hambient :
      let M := cycleComponentSmoothLocusAmbientOpenOver X x
      let r := ComplexPoint.openInclusion X (cycleComponentSmoothLocusAmbientOpen X x)
      let j := cycleComponentSmoothLocusClosedLiftOver X x
      fderiv ℂ (fun w ↦ Point.evaluate (r.left ⁻¹ᵁ f.opens)
          (r.left.app f.opens f.equation)
          ((localChart M D (Point.map j z)).symm w))
        (localChart M D (Point.map j z) (Point.map j z)) ≠ 0 := by
    dsimp only
    change fderiv ℂ (fun w ↦ Point.evaluate
        ((cycleComponentSmoothLocusAmbientOpen X x).ι ⁻¹ᵁ f.opens)
        ((cycleComponentSmoothLocusAmbientOpen X x).ι.app f.opens f.equation)
        ((localChart (cycleComponentSmoothLocusAmbientOpenOver X x) D
          (Point.map (cycleComponentSmoothLocusClosedLiftOver X x) z)).symm w))
      (localChart (cycleComponentSmoothLocusAmbientOpenOver X x) D
        (Point.map (cycleComponentSmoothLocusClosedLiftOver X x) z)
        (Point.map (cycleComponentSmoothLocusClosedLiftOver X x) z)) ≠ 0
    exact fderiv_ne_zero_of_smooth_locus_component_equation_of_ambient_membership
      X c x D f (by exact_mod_cast hx) s hs hEq z hqOpen hqBasic
  exact exists_genericWindingChartData_of_component_canonical X c x hx i f z
    (Point.map r (Point.map j z)) rfl N hqN hN hambient

set_option maxHeartbeats 1000000 in
/-- The principal local-form shrink gives generic charts inside every analytic neighbourhood. -/
theorem exists_genericWindingChartData_off_component_exceptional
    (c : Scheme.CartierData X.left) (x : X.left)
    (hx : coheight x = ((1 : ℕ) : ℕ∞)) :
    ∃ B : Closeds X.left,
      (B : Set X.left) ⊆ closure ({x} : Set X.left) ∧ x ∉ B ∧
      ∀ q ∈ cycleComponentSmoothSupportAmbientOpen X x,
        q ∈ cycleComponentSupport X x → Point.underlying q ∉ B →
        ∀ N : Opens (ComplexPoint X), q ∈ N →
          ∃ G : GenericWindingChartData X c x (dim X.left) q,
            G.toChart.carrier ≤ N := by
  let i := c.index x
  have hxi : x ∈ c.opens i := c.mem_opens_index x
  obtain ⟨f⟩ := Scheme.CartierData.exists_localForm X c i x hx hxi
  let _ : IsDiscreteValuationRing (X.left.presheaf.stalk x) :=
    isDiscreteValuationRing_stalk_of_coheight_eq_one X.hom (by exact_mod_cast hx)
  obtain ⟨s, hs, hEq, hclosed, hxB, hBsub⟩ :=
    Scheme.CartierData.LocalForm.exists_away_eq_component_with_exceptional f
      (by exact_mod_cast hx)
  let B : Closeds X.left := ⟨f.exceptionalSet s, hclosed⟩
  refine ⟨B, ?_, ?_, ?_⟩
  · exact hBsub
  · exact hxB
  · intro q hqOpen hqS hqB N hqN0
    have hqN0_orig : q ∈ N := hqN0
    have hclosure : q.underlying ∈ closure ({x} : Set X.left) := hqS
    have hbasic : q.underlying ∈ X.left.basicOpen s := by
      by_contra hnot
      exact hqB ⟨hclosure, hnot⟩
    have hopen : q.underlying ∈ f.opens := X.left.basicOpen_le s hbasic
    have hq' : q ∈
        (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).functor.obj ⊤ := by
      rw [cycleComponentSmoothClosedLiftAmbientMap_imageOpen]
      exact hqOpen
    obtain ⟨qM, -, rfl⟩ := hq'
    have hqMS : qM ∈ Set.range (Point.map
        (cycleComponentSmoothLocusClosedLiftOver X x)) := by
      rw [← cycleComponentSmoothClosedLiftAmbientMap_support]
      exact hqS
    obtain ⟨z, rfl⟩ := hqMS
    let q0 := Point.map (ComplexPoint.openInclusion X
      (cycleComponentSmoothLocusAmbientOpen X x))
      (Point.map (cycleComponentSmoothLocusClosedLiftOver X x) z)
    let N' := N ⊓ analyticOpen X f.opens ⊓ analyticOpen X (X.left.basicOpen s)
    have hqN : q0 ∈ N' := by
      have hqN0' : q0 ∈ N := by
        exact hqN0_orig
      have hq0open : q0 ∈ analyticOpen X f.opens := by
        exact hopen
      have hq0basic : q0 ∈ analyticOpen X (X.left.basicOpen s) := by
        exact hbasic
      exact ⟨⟨hqN0', hq0open⟩, hq0basic⟩
    have hN' : N' ≤ analyticOpen X f.opens := by
      exact (inf_le_left.trans inf_le_right)
    obtain ⟨G, hG⟩ := exists_genericWindingChartData_of_component_algebraic X c x hx i f s hs hEq
      z q0 rfl N' hqN hN' (by exact hbasic)
    have hq0eq : q0 = (cycleComponentSmoothClosedLiftAmbientMap X x)
        (Point.map (cycleComponentSmoothLocusClosedLiftOver X x) z) := by rfl
    rw [← hq0eq]
    exact ⟨G, hG.trans (inf_le_left.trans inf_le_left)⟩

set_option maxHeartbeats 1000000 in
/-- The exceptional closed set supplied by the principal local-form shrink gives the generic chart
cover. -/
theorem hasGenericFlatteningCharts_of_component_algebraic :
    AlgebraicGeometry.ComplexPoint.HasGenericFlatteningCharts (X := X) := by
  intro c x hx
  obtain ⟨B, hBsub, hxB, hcover⟩ :=
    exists_genericWindingChartData_off_component_exceptional X c x hx
  refine ⟨B, hBsub, hxB, ?_⟩
  intro q hqOpen hqS hqB
  obtain ⟨G, -⟩ := hcover q hqOpen hqS hqB ⊤ trivial
  exact ⟨G⟩

theorem hasNormalizedWindingCharts_of_component_algebraic :
    HasNormalizedWindingCharts X :=
  hasNormalizedWindingCharts_of_genericFlatteningCharts
    (hasGenericFlatteningCharts_of_component_algebraic X)

end AlgebraicGeometry.ComplexPoint
