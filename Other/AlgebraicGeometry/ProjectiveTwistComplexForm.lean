/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveTwistFormTools
public import Other.AlgebraicGeometry.ProjectiveHolomorphicFunctions

/-!
# Algebraic twist morphisms from forms with complex coefficients

`algMulHom` realises multiplication by a homogeneous element of `ℤ[X₀,…,X_N]`.  Composing with
multiplication by a constant global regular function (`globalSmulHom`) and summing over the
monomials of a complex form `Q` realises *every* degree-`k` form with complex coefficients, and
the chart multiplier of the analytified morphism has chart expression
`z ↦ MvPolynomial.eval z (deh ℂ i Q)`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ProjectiveSpectrum.NegativeTwist

namespace AlgebraicGeometry.ComplexProjectiveSpace

open ComplexPoint Other.ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts

local instance projFormModuleAnalytification_additive (N : ℕ) :
    (moduleAnalytification (projectiveSpaceOver N) N).Additive :=
  CategoryTheory.Functor.additive_of_preservesBinaryBiproducts _

variable (N b k : ℕ) (i : Fin (N + 1))

/-- The monomial `Xᵅ`, as a homogeneous element of degree `k` of the universal grading. -/
def monomialGrading (α : Fin (N + 1) →₀ ℕ) (hα : α.degree = k) : UniversalGrading N k :=
  ⟨MvPolynomial.monomial α 1, MvPolynomial.isHomogeneous_monomial _ hα⟩

@[simp]
theorem coe_monomialGrading (α : Fin (N + 1) →₀ ℕ) (hα : α.degree = k) :
    ((monomialGrading N k α hα : UniversalGrading N k) : UniversalRing N) =
      MvPolynomial.monomial α 1 := rfl

/-- The exponents of a homogeneous form have the expected degree. -/
theorem degree_of_mem_support {Q : MvPolynomial (Fin (N + 1)) ℂ} (hQ : Q.IsHomogeneous k)
    {α : Fin (N + 1) →₀ ℕ} (hα : α ∈ Q.support) : α.degree = k := by
  rw [Finsupp.degree_eq_weight_one]
  exact hQ (MvPolynomial.mem_support_iff.mp hα)

/-- Multiplication by the constant `c`, as an endomorphism of `𝒪(−b)` on `ℙᴺ`. -/
def constMulHom (c : ℂ) :
    ComplexPoint.ProjectiveTwist.algebraic (projectiveSpaceOver N) (projPresentation N) b ⟶
      ComplexPoint.ProjectiveTwist.algebraic (projectiveSpaceOver N) (projPresentation N) b :=
  Scheme.Modules.globalSmulHom _
    (ComplexPoint.constantRegularSection (projectiveSpaceOver N) c)

/-- **The algebraic morphism attached to a complex form.** -/
def algMulC (Q : MvPolynomial (Fin (N + 1)) ℂ) (hQ : Q.IsHomogeneous k) :
    ComplexPoint.ProjectiveTwist.algebraic (projectiveSpaceOver N) (projPresentation N) (b + k) ⟶
      ComplexPoint.ProjectiveTwist.algebraic (projectiveSpaceOver N) (projPresentation N) b :=
  ∑ α ∈ Q.support.attach,
    algMulHom N b k (monomialGrading N k α.1 (degree_of_mem_support N k hQ α.2)) ≫
      constMulHom N b (MvPolynomial.coeff α.1 Q)

/-! ### The chart multiplier of `algMulC` -/

/-- A regular function on the `i`-th standard chart, read as a holomorphic function there. -/
def chartAnalyticFun (r : Γ((projectiveSpaceOver N).left,
    projectiveSpaceBasicOpen N (MvPolynomial.X i))) :
    (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj (op (chartOpen N i)) :=
  ComplexPoint.analyticFunction (projectiveSpaceOver N) N
    (projectiveSpaceBasicOpen N (MvPolynomial.X i)) r

/-- The evaluation of the constant `c`, as a holomorphic function on the `i`-th chart. -/
def constAnalyticFun (c : ℂ) :
    (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj (op (chartOpen N i)) :=
  chartAnalyticFun N i
    ((projectiveSpaceOver N).left.ringCatSheaf.obj.map
      (homOfLE (le_top : projectiveSpaceBasicOpen N (MvPolynomial.X i) ≤ ⊤)).op
      (ComplexPoint.constantRegularSection (projectiveSpaceOver N) c))

set_option backward.isDefEq.respectTransparency false in
/-- The chart multiplier of multiplication by a constant. -/
theorem analytified_constMulHom_anChartFrame (c : ℂ) :
    ((moduleAnalytification (projectiveSpaceOver N) N).map (constMulHom N b c)).val.app
        (op (chartOpen N i)) (anChartFrame N b i) =
      constAnalyticFun N i c • anChartFrame N b i := by
  have h := congrArg (ComplexPoint.analyticSection (projectiveSpaceOver N) N
      (ComplexPoint.ProjectiveTwist.algebraic (projectiveSpaceOver N) (projPresentation N) b)
      (projectiveSpaceBasicOpen N (MvPolynomial.X i)))
    (Scheme.Modules.globalSmulHom_app
      (ComplexPoint.ProjectiveTwist.algebraic (projectiveSpaceOver N) (projPresentation N) b)
      (ComplexPoint.constantRegularSection (projectiveSpaceOver N) c)
      (projectiveSpaceBasicOpen N (MvPolynomial.X i)) (algChartFrame N b i))
  rw [ComplexPoint.analyticSection_map, ComplexPoint.analyticSection_smul] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The chart multiplier of `algMulHom`, in the `chartAnalyticFun` normal form. -/
theorem analytified_algMulHom_anChartFrame' (G : UniversalGrading N k) :
    ((moduleAnalytification (projectiveSpaceOver N) N).map (algMulHom N b k G)).val.app
        (op (chartOpen N i)) (anChartFrame N (b + k) i) =
      chartAnalyticFun N i (spaceRatioBig N k G i) • anChartFrame N b i :=
  analytified_algMulHom_anChartFrame N b k G i

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The chart multiplier of a monomial multiplication followed by a constant. -/
theorem analytified_monomialStep (G : UniversalGrading N k) (c : ℂ) :
    ((moduleAnalytification (projectiveSpaceOver N) N).map
          (algMulHom N b k G ≫ constMulHom N b c)).val.app
        (op (chartOpen N i)) (anChartFrame N (b + k) i) =
      (chartAnalyticFun N i (spaceRatioBig N k G i) * constAnalyticFun N i c) •
        anChartFrame N b i := by
  rw [(moduleAnalytification (projectiveSpaceOver N) N).map_comp]
  show ((moduleAnalytification (projectiveSpaceOver N) N).map (constMulHom N b c)).val.app
      (op (chartOpen N i))
      (((moduleAnalytification (projectiveSpaceOver N) N).map (algMulHom N b k G)).val.app
        (op (chartOpen N i)) (anChartFrame N (b + k) i)) = _
  rw [analytified_algMulHom_anChartFrame' N b k i G,
    ((moduleAnalytification (projectiveSpaceOver N) N).map
      (constMulHom N b c)).val.app (op (chartOpen N i)) |>.hom.map_smul,
    analytified_constMulHom_anChartFrame, smul_smul]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The chart multiplier of a finite sum of morphisms is the sum of the chart multipliers. -/
theorem analytified_sum_anChartFrame {ι : Type} (s : Finset ι)
    (g : ι →
      (ComplexPoint.ProjectiveTwist.algebraic (projectiveSpaceOver N) (projPresentation N)
          (b + k) ⟶
        ComplexPoint.ProjectiveTwist.algebraic (projectiveSpaceOver N) (projPresentation N) b))
    (m : ι → (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj (op (chartOpen N i)))
    (hm : ∀ t ∈ s, ((moduleAnalytification (projectiveSpaceOver N) N).map (g t)).val.app
        (op (chartOpen N i)) (anChartFrame N (b + k) i) = m t • anChartFrame N b i) :
    ((moduleAnalytification (projectiveSpaceOver N) N).map (∑ t ∈ s, g t)).val.app
        (op (chartOpen N i)) (anChartFrame N (b + k) i) =
      (∑ t ∈ s, m t) • anChartFrame N b i := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, CategoryTheory.Functor.map_zero, zero_smul]
    rfl
  | insert t s ht ih =>
    rw [Finset.sum_insert ht, Finset.sum_insert ht,
      CategoryTheory.Functor.map_add, add_smul]
    show ((moduleAnalytification (projectiveSpaceOver N) N).map (g t)).val.app
        (op (chartOpen N i)) (anChartFrame N (b + k) i) +
      ((moduleAnalytification (projectiveSpaceOver N) N).map (∑ x ∈ s, g x)).val.app
        (op (chartOpen N i)) (anChartFrame N (b + k) i) = _
    rw [hm t (Finset.mem_insert_self t s), ih fun x hx => hm x (Finset.mem_insert_of_mem hx)]

/-- The analytic chart multiplier attached to a complex form. -/
def formMultiplier (Q : MvPolynomial (Fin (N + 1)) ℂ) (hQ : Q.IsHomogeneous k) :
    (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj (op (chartOpen N i)) :=
  ∑ α ∈ Q.support.attach,
    chartAnalyticFun N i
        (spaceRatioBig N k (monomialGrading N k α.1 (degree_of_mem_support N k hQ α.2)) i) *
      constAnalyticFun N i (MvPolynomial.coeff α.1 Q)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The chart multiplier of `algMulC`.** -/
theorem analytified_algMulC_anChartFrame (Q : MvPolynomial (Fin (N + 1)) ℂ)
    (hQ : Q.IsHomogeneous k) :
    ((moduleAnalytification (projectiveSpaceOver N) N).map (algMulC N b k Q hQ)).val.app
        (op (chartOpen N i)) (anChartFrame N (b + k) i) =
      formMultiplier N k i Q hQ • anChartFrame N b i :=
  analytified_sum_anChartFrame N b k i _ _ _ fun _ _ =>
    analytified_monomialStep N b k i _ _

/-! ### The chart expression of the form multiplier -/

theorem holSectionFun_sum {V : Opens (TopCat.of (ComplexPoint (projectiveSpaceOver N)))}
    {ι : Type} (s : Finset ι)
    (f : ι → (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj (op V)) (x : V) :
    holSectionFun (∑ t ∈ s, f t) x = ∑ t ∈ s, holSectionFun (f t) x := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert t s ht ih =>
    rw [Finset.sum_insert ht, Finset.sum_insert ht, ← ih]
    rfl

/-- Evaluation of the universal coordinate ring is `eval₂` at the coordinate vector. -/
theorem coordinateEvaluationHom_eq (v : CoordinateSpace N) :
    coordinateEvaluationHom v =
      MvPolynomial.eval₂Hom ((algebraMap ℤ ℂ).comp ULift.ringEquiv.toRingHom) v := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [coordinateEvaluationHom, coordinateGlobalSectionsHom]
  · intro j
    simp [coordinateEvaluationHom, coordinateGlobalSectionsHom]

theorem coordinateEvaluationHom_monomial (v : CoordinateSpace N) (α : Fin (N + 1) →₀ ℕ) :
    coordinateEvaluationHom v (MvPolynomial.monomial α (1 : ULift ℤ)) = ∏ l, v l ^ α l := by
  rw [coordinateEvaluationHom_eq, MvPolynomial.eval₂Hom_monomial]
  simp only [map_one, one_mul]
  exact (Finsupp.prod_fintype α (fun l e => v l ^ e) (fun _ => pow_zero _))

set_option maxHeartbeats 1000000 in
/-- The chart expression of `chartAnalyticFun` of a homogeneous ratio. -/
theorem chartFun_chartAnalyticFun_spaceRatioBig (G : UniversalGrading N k) (z : Fin N → ℂ) :
    chartFun N i (chartAnalyticFun N i (spaceRatioBig N k G i)) z =
      coordinateEvaluationHom (i.insertNth (1 : ℂ) z) (G : UniversalRing N) := by
  have hvi : ((i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) i) = 1 := Fin.insertNth_apply_same _ _ _
  have h := homogeneousRatioEvaluation N k G i (i.insertNth (1 : ℂ) z)
    (insertNth_one_ne_zero i z) (by rw [hvi]; exact one_ne_zero)
  rw [hvi, one_pow, div_one] at h
  exact h

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The chart expression of the constant multiplier. -/
theorem chartFun_constAnalyticFun (c : ℂ) (z : Fin N → ℂ) :
    chartFun N i (constAnalyticFun N i c) z = c := by
  show Point.evaluate (projectiveSpaceBasicOpen N (MvPolynomial.X i))
      ((projectiveSpaceOver N).left.presheaf.map
        (homOfLE (le_top : projectiveSpaceBasicOpen N (MvPolynomial.X i) ≤ ⊤)).op
        (ComplexPoint.constantRegularSection (projectiveSpaceOver N) c))
      (projectivizationToComplexPoint (chartPoint i z)) = c
  rw [← Point.evaluate_res (le_top : projectiveSpaceBasicOpen N (MvPolynomial.X i) ≤ ⊤)
    (ComplexPoint.constantRegularSection (projectiveSpaceOver N) c) _
    (chartPoint_mem_overOpen_self N i z)]
  exact ComplexPoint.evaluate_constantRegularSection (projectiveSpaceOver N) c _

set_option maxHeartbeats 1000000 in
/-- **The chart expression of the form multiplier is the dehomogenised form.** -/
theorem chartFun_formMultiplier (Q : MvPolynomial (Fin (N + 1)) ℂ) (hQ : Q.IsHomogeneous k)
    (z : Fin N → ℂ) :
    chartFun N i (formMultiplier N k i Q hQ) z = MvPolynomial.eval z (deh ℂ i Q) := by
  classical
  rw [Other.ProjectiveChart.eval_deh i z Q, MvPolynomial.eval_eq']
  show holSectionFun (formMultiplier N k i Q hQ) (chartPointIn N i z) = _
  rw [formMultiplier, holSectionFun_sum]
  rw [← Finset.sum_attach Q.support
    (fun α => MvPolynomial.coeff α Q * ∏ l, (i.insertNth (1 : ℂ) z : Fin (N + 1) → ℂ) l ^ α l)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [holSectionFun_mul]
  show chartFun N i _ z * chartFun N i _ z = _
  rw [chartFun_chartAnalyticFun_spaceRatioBig, chartFun_constAnalyticFun,
    coe_monomialGrading, coordinateEvaluationHom_monomial]
  ring

end AlgebraicGeometry.ComplexProjectiveSpace
