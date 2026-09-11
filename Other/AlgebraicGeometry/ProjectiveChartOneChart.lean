/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ProjectiveChartLocality
public import Other.AlgebraicGeometry.ProjectiveTwistNegativeVanishing
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# One chart determines a morphism of analytic twists

The transition units `analyticSpaceRatio N n i j` are *units* of the holomorphic structure sheaf
on chart overlaps, because `Xⱼⁿ/Xᵢⁿ` and `Xᵢⁿ/Xⱼⁿ` are mutually inverse regular functions there.
Hence if one chart multiplier of a morphism `𝒪(−a)^an ⟶ 𝒪(−b)^an` vanishes, all the others
vanish on the corresponding overlaps; those overlaps are complements of hyperplanes in the chart
coordinates, so the identity principle propagates the vanishing to the whole chart, and
`hom_eq_zero_of_anChartFrame` finishes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ProjectiveSpectrum.NegativeTwist

namespace AlgebraicGeometry

universe u v

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace ProjectiveSpectrum.NegativeTwist

set_option backward.isDefEq.respectTransparency.types false in
/-- The two homogeneous ratios of a pair of nonvanishing elements are mutually inverse. -/
theorem homogeneousRatio_mul_swap {k : ℕ} (num den : 𝒜 k)
    (U : Opens (ProjectiveSpectrum.top 𝒜))
    (hnum : ∀ x : U, (num : A) ∉ x.1.asHomogeneousIdeal)
    (hden : ∀ x : U, (den : A) ∉ x.1.asHomogeneousIdeal) :
    homogeneousRatio 𝒜 num den U hden * homogeneousRatio 𝒜 den num U hnum = 1 := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  show ((homogeneousRatio 𝒜 num den U hden).1 x * (homogeneousRatio 𝒜 den num U hnum).1 x).val =
    ((1 : (ringSheaf 𝒜).obj.obj (op U)).1 x).val
  have h1 : ((1 : (ringSheaf 𝒜).obj.obj (op U)).1 x).val =
      (1 : ProjectiveSpectrum.ambientLocalization 𝒜 x.1) := HomogeneousLocalization.val_one
  rw [HomogeneousLocalization.val_mul, homogeneousRatio_val, homogeneousRatio_val,
    Localization.mk_mul, h1,
    show (1 : ProjectiveSpectrum.ambientLocalization 𝒜 x.1) = Localization.mk 1 1 from
      (Localization.mk_one).symm,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  show (1 : A) * ((1 : A) * ((num : A) * (den : A))) =
    1 * (((den : A) * (num : A)) * (1 : A))
  ring

end ProjectiveSpectrum.NegativeTwist

namespace ComplexProjectiveSpace

open ComplexPoint Other.ProjectiveChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (N n : ℕ) (i j : Fin (N + 1))

/-- The universal transition unit is a unit. -/
theorem isUnit_universalRatio : IsUnit (universalRatio N n i j) := by
  refine ⟨⟨universalRatio N n i j,
    projRatio (UniversalGrading N) (coordPower N n i) (coordPower N n j)
      (universalOverlap N i j) (fun x => universalOverlap_le_coordPower' N n i j x.2), ?_, ?_⟩,
    rfl⟩
  · exact homogeneousRatio_mul_swap (UniversalGrading N) (coordPower N n j) (coordPower N n i)
      (universalOverlap N i j) (fun x => universalOverlap_le_coordPower' N n i j x.2)
      (fun x => universalOverlap_le_coordPower N n i j x.2)
  · exact homogeneousRatio_mul_swap (UniversalGrading N) (coordPower N n i) (coordPower N n j)
      (universalOverlap N i j) (fun x => universalOverlap_le_coordPower N n i j x.2)
      (fun x => universalOverlap_le_coordPower' N n i j x.2)

set_option backward.isDefEq.respectTransparency false in
/-- The transition unit on `ℙᴺ` is a unit. -/
theorem isUnit_spaceRatio : IsUnit (spaceRatio N n i j) :=
  Scheme.Modules.isUnit_pullbackFunction _
    (Scheme.Modules.isUnit_pullbackFunction _ (isUnit_universalRatio N n i j))

set_option backward.isDefEq.respectTransparency false in
/-- The analytic transition unit is a unit. -/
theorem isUnit_analyticSpaceRatio : IsUnit (analyticSpaceRatio N n i j) :=
  ComplexPoint.isUnit_analyticFunction (isUnit_spaceRatio N n i j)

set_option maxHeartbeats 1000000 in
/-- **One chart suffices.**  A morphism of analytic twists on `ℙᴺ` whose chart multiplier on one
chart vanishes is zero. -/
theorem hom_eq_zero_of_one_chart {N a b : ℕ} (φ : analyticTwist N a ⟶ analyticTwist N b)
    (i₀ : Fin (N + 1))
    (v : ∀ i : Fin (N + 1), (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj
      (op (chartOpen N i)))
    (hv : ∀ i, φ.val.app (op (chartOpen N i)) (anChartFrame N a i) = v i • anChartFrame N b i)
    (h0 : ∀ z : Fin N → ℂ, chartFun N i₀ (v i₀) z = 0) : φ = 0 := by
  have hvi0 : v i₀ = 0 := holSection_ext i₀ fun z => by rw [h0 z]; rfl
  refine hom_eq_zero_of_anChartFrame φ fun i => ?_
  have hco := canonicalChartMultiplier_transition N a b i₀ i φ (hv i₀) (hv i)
  rw [hvi0] at hco
  have hzero : analyticSpaceRatio N a i₀ i *
      ComplexPoint.holRingRes (inf_le_right : chartOpen N i₀ ⊓ chartOpen N i ≤ chartOpen N i)
        (v i) = 0 := by
    rw [← hco]
    have h1 : ComplexPoint.holRingRes
        (inf_le_left : chartOpen N i₀ ⊓ chartOpen N i ≤ chartOpen N i₀)
        (0 : (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj (op (chartOpen N i₀))) = 0 :=
      map_zero ((holomorphicRingSheaf (projectiveSpaceOver N) N).obj.map
        (homOfLE (inf_le_left : chartOpen N i₀ ⊓ chartOpen N i ≤ chartOpen N i₀)).op).hom
    rw [h1, zero_mul]
  have hres : ComplexPoint.holRingRes
      (inf_le_right : chartOpen N i₀ ⊓ chartOpen N i ≤ chartOpen N i) (v i) = 0 :=
    ((isUnit_analyticSpaceRatio N a i₀ i).mul_right_eq_zero).mp hzero
  have hoverlap : ∀ y : Fin N → ℂ,
      ((i.insertNth (1 : ℂ) y : Fin (N + 1) → ℂ) i₀) ≠ 0 → chartFun N i (v i) y = 0 := by
    intro y hy
    have hmem : (chartPointIn N i y : ComplexPoint (projectiveSpaceOver N)) ∈
        chartOpen N i₀ ⊓ chartOpen N i :=
      ⟨chartPoint_mem_overOpen_of_ne_zero N i i₀ y hy, chartPoint_mem_overOpen_self N i y⟩
    have hval := congrArg
      (fun t : (holomorphicRingSheaf (projectiveSpaceOver N) N).obj.obj
          (op (chartOpen N i₀ ⊓ chartOpen N i)) =>
        holSectionFun t ⟨(chartPointIn N i y : ComplexPoint (projectiveSpaceOver N)), hmem⟩) hres
    rw [holSectionFun_holRingRes] at hval
    exact hval
  have hall : ∀ y : Fin N → ℂ, chartFun N i (v i) y = 0 := by
    rcases eq_or_ne i₀ i with rfl | hne
    · intro y
      refine hoverlap y ?_
      rw [Fin.insertNth_apply_same]
      exact one_ne_zero
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hne
      have hopen : IsOpen {y : Fin N → ℂ | y l ≠ 0} :=
        isOpen_ne.preimage (continuous_apply l)
      have hf : Set.EqOn (chartFun N i (v i)) 0 {y : Fin N → ℂ | y l ≠ 0} := by
        intro y hy
        refine hoverlap y ?_
        rwa [Fin.insertNth_apply_succAbove]
      have hy0 : (fun _ : Fin N => (1 : ℂ)) ∈ {y : Fin N → ℂ | y l ≠ 0} := one_ne_zero
      have hev : chartFun N i (v i) =ᶠ[nhds (fun _ : Fin N => (1 : ℂ))] 0 :=
        Filter.eventuallyEq_of_mem (hopen.mem_nhds hy0) hf
      have hzeroOn := (analyticOnNhd_chartFun i (v i)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ _) hev
      exact fun y => hzeroOn (Set.mem_univ y)
  have hvi : v i = 0 := holSection_ext i fun y => by rw [hall y]; rfl
  rw [hv i, hvi, zero_smul]

end ComplexProjectiveSpace

end AlgebraicGeometry
