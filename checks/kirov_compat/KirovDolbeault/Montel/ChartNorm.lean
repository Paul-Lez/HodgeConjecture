import KirovDolbeault.Montel.Cover
import KirovDolbeault.Montel.LocalRep

/-!
# Montel path — bounded chart-local sup-norm `chartNormK`

For each chart center `x₀ ∈ chartCover`, `chartNormK α x₀` is the `sSup` of
`‖localRep α x₀ y‖` over `y ∈ shrunkChart x₀`. Because `shrunkChart x₀`
is compact and `localRep α x₀` is continuous on the containing
chart source, the image is compact in ℝ, hence bounded — the sSup is
finite.

This replaces the naive `⨆ y : X, ‖localRep α x₀ y‖` which is unbounded
in general (the "unit tangent" blows up near the chart boundary) and
thus collapses to 0 via `Real.iSup_of_not_bddAbove` — destroying the
triangle inequality.

Contents:
- `chartNormK` definition.
- `chartNormK_nonneg`, `chartNormK_bddAbove`, `norm_localRep_le_chartNormK`.
- `chartNormK_zero` (the zero section has chartNormK = 0).
- Triangle + full homogeneity: `chartNormK_add_le`, `chartNormK_smul_le`,
  `chartNormK_smul`. -/

namespace Jacobians.Montel

open scoped Manifold ContDiff
open Bundle

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `chartNormK` and boundedness -/

/-- Bounded chart-local sup-norm: sup over the compact `shrunkChart x₀`. -/
noncomputable def HolomorphicOneForms.chartNormK
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) : ℝ :=
  sSup ((fun y : X => ‖localRep α x₀ y‖) '' shrunkChart (X := X) x₀)

omit [ConnectedSpace X] [Nonempty X] in
/-- The image of `‖localRep α x₀ ·‖` over `shrunkChart x₀` is bounded above. -/
theorem HolomorphicOneForms.chartNormK_bddAbove
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    BddAbove ((fun y : X => ‖localRep α x₀ y‖) '' shrunkChart (X := X) x₀) := by
  by_cases hx : x₀ ∈ (chartCover : Finset X)
  · have hsub : shrunkChart (X := X) x₀ ⊆
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact shrunkChart_subset_source x₀ hx
    have hcompact := shrunkChart_isCompact (X := X) x₀
    have hcont : ContinuousOn (fun y : X => ‖localRep α x₀ y‖)
        (shrunkChart (X := X) x₀) :=
      ((localRep_continuousOn α x₀).mono hsub).norm
    exact (hcompact.image_of_continuousOn hcont).bddAbove
  · rw [shrunkChart_eq_empty x₀ hx]
    simp [BddAbove, Set.image_empty]

omit [ConnectedSpace X] [Nonempty X] in
/-- `chartNormK` is non-negative. -/
theorem HolomorphicOneForms.chartNormK_nonneg
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) : 0 ≤ HolomorphicOneForms.chartNormK α x₀ := by
  unfold HolomorphicOneForms.chartNormK
  by_cases hne : (shrunkChart (X := X) x₀).Nonempty
  · obtain ⟨y, hy⟩ := hne
    apply le_csSup_of_le (HolomorphicOneForms.chartNormK_bddAbove α x₀)
      ⟨y, hy, rfl⟩
    exact norm_nonneg _
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne]

omit [ConnectedSpace X] [Nonempty X] in
/-- Pointwise bound: `‖localRep α x₀ y‖ ≤ chartNormK α x₀` for y ∈ shrunkChart. -/
theorem HolomorphicOneForms.norm_localRep_le_chartNormK
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) {y : X} (hy : y ∈ shrunkChart (X := X) x₀) :
    ‖localRep α x₀ y‖ ≤ HolomorphicOneForms.chartNormK α x₀ :=
  le_csSup (HolomorphicOneForms.chartNormK_bddAbove α x₀) ⟨y, hy, rfl⟩

omit [ConnectedSpace X] [Nonempty X] in
/-- `chartNormK` of the zero section is zero. -/
theorem HolomorphicOneForms.chartNormK_zero (x₀ : X) :
    HolomorphicOneForms.chartNormK
      (0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
        (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
      x₀ = 0 := by
  unfold HolomorphicOneForms.chartNormK localRep
  have himg : (fun y : X => ‖(0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
        (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)).toFun y
      ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1)‖) ''
        shrunkChart (X := X) x₀ ⊆ {0} := by
    intro r hr
    obtain ⟨y, _, rfl⟩ := hr
    change ‖(0 : TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ) _‖ ∈ ({0} : Set ℝ)
    simp
  by_cases hne : (shrunkChart (X := X) x₀).Nonempty
  · obtain ⟨y, hy⟩ := hne
    have hmem : (0 : ℝ) ∈ (fun y : X => ‖(0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
        (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)).toFun y
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1)‖) ''
          shrunkChart x₀ := by
      refine ⟨y, hy, ?_⟩
      change ‖(0 : TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ) _‖ = 0
      simp
    have : (fun y : X => ‖(0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
        (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)).toFun y
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1)‖) ''
          shrunkChart x₀ = {0} :=
      Set.eq_singleton_iff_unique_mem.mpr ⟨hmem, fun b hb => himg hb⟩
    rw [this]
    exact csSup_singleton 0
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne]

/-! ### Triangle inequality and homogeneity -/

omit [ConnectedSpace X] [Nonempty X] in
/-- Triangle inequality for `chartNormK`. -/
theorem HolomorphicOneForms.chartNormK_add_le
    (α β : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    HolomorphicOneForms.chartNormK (α + β) x₀ ≤
      HolomorphicOneForms.chartNormK α x₀ + HolomorphicOneForms.chartNormK β x₀ := by
  unfold HolomorphicOneForms.chartNormK
  by_cases hne : (shrunkChart (X := X) x₀).Nonempty
  · apply csSup_le (Set.Nonempty.image _ hne)
    rintro r ⟨y, hy, rfl⟩
    show ‖localRep (α + β) x₀ y‖ ≤ _
    rw [localRep_add]
    calc ‖localRep α x₀ y + localRep β x₀ y‖
        ≤ ‖localRep α x₀ y‖ + ‖localRep β x₀ y‖ := norm_add_le _ _
      _ ≤ sSup ((fun z : X => ‖localRep α x₀ z‖) '' shrunkChart (X := X) x₀) +
          sSup ((fun z : X => ‖localRep β x₀ z‖) '' shrunkChart (X := X) x₀) := by
        apply add_le_add
        · exact le_csSup
            (HolomorphicOneForms.chartNormK_bddAbove α x₀) ⟨y, hy, rfl⟩
        · exact le_csSup
            (HolomorphicOneForms.chartNormK_bddAbove β x₀) ⟨y, hy, rfl⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hα : sSup ((fun y : X => ‖localRep α x₀ y‖) '' shrunkChart (X := X) x₀) = 0 := by
      simp [hne, Real.sSup_empty]
    have hβ : sSup ((fun y : X => ‖localRep β x₀ y‖) '' shrunkChart (X := X) x₀) = 0 := by
      simp [hne, Real.sSup_empty]
    have hαβ : sSup ((fun y : X => ‖localRep (α + β) x₀ y‖) '' shrunkChart (X := X) x₀) = 0 := by
      simp [hne, Real.sSup_empty]
    rw [hα, hβ, hαβ]; ring_nf; rfl

omit [ConnectedSpace X] [Nonempty X] in
/-- Sub-homogeneity: `chartNormK (c • α) ≤ ‖c‖ * chartNormK α`. -/
theorem HolomorphicOneForms.chartNormK_smul_le (c : ℂ)
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    HolomorphicOneForms.chartNormK (c • α) x₀ ≤
      ‖c‖ * HolomorphicOneForms.chartNormK α x₀ := by
  unfold HolomorphicOneForms.chartNormK
  by_cases hne : (shrunkChart (X := X) x₀).Nonempty
  · apply csSup_le (Set.Nonempty.image _ hne)
    rintro r ⟨y, hy, rfl⟩
    show ‖localRep (c • α) x₀ y‖ ≤ _
    rw [localRep_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left
      (le_csSup (HolomorphicOneForms.chartNormK_bddAbove α x₀) ⟨y, hy, rfl⟩)
      (norm_nonneg _)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have h1 : sSup ((fun y : X => ‖localRep (c • α) x₀ y‖) '' shrunkChart (X := X) x₀) = 0 := by
      simp [hne, Real.sSup_empty]
    have h2 : sSup ((fun y : X => ‖localRep α x₀ y‖) '' shrunkChart (X := X) x₀) = 0 := by
      simp [hne, Real.sSup_empty]
    rw [h1, h2, mul_zero]

omit [ConnectedSpace X] [Nonempty X] in
/-- Full homogeneity: `chartNormK (c • α) = ‖c‖ * chartNormK α`. -/
theorem HolomorphicOneForms.chartNormK_smul (c : ℂ)
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    HolomorphicOneForms.chartNormK (c • α) x₀ =
      ‖c‖ * HolomorphicOneForms.chartNormK α x₀ := by
  refine le_antisymm (HolomorphicOneForms.chartNormK_smul_le c α x₀) ?_
  by_cases hc : c = 0
  · subst hc
    simp
    exact HolomorphicOneForms.chartNormK_nonneg _ _
  · have hc' : c⁻¹ • (c • α) = α := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hsub := HolomorphicOneForms.chartNormK_smul_le c⁻¹ (c • α) x₀
    rw [hc'] at hsub
    rw [norm_inv] at hsub
    have hcpos : 0 < ‖c‖ := by
      rw [norm_pos_iff]; exact hc
    calc ‖c‖ * HolomorphicOneForms.chartNormK α x₀
        ≤ ‖c‖ * (‖c‖⁻¹ * HolomorphicOneForms.chartNormK (c • α) x₀) :=
          mul_le_mul_of_nonneg_left hsub (norm_nonneg _)
      _ = HolomorphicOneForms.chartNormK (c • α) x₀ := by
          rw [← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]

end Jacobians.Montel
