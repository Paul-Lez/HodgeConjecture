import KirovDolbeault.Montel.ChartNorm

/-!
# Montel path — assembled sup-norm `supNormK`

`supNormK α` is the `Finset.sup'` over the `chartCover` of the per-chart
`chartNormK α x₀`. This is the canonical norm candidate on
`HolomorphicOneForms X`.

Contents:
- `supNormK` definition + basic properties (nonneg, zero, chart-bound,
  pointwise-bound, triangle, homogeneity, neg-invariance).
- Positive-definiteness (`eq_zero_of_supNormK_eq_zero`): this is the
  only piece that genuinely uses the manifold's 1-dim ℂ-structure,
  via `T_y X ≃L[ℂ] ℂ` (`Trivialization.continuousLinearEquivAt`). -/

namespace Jacobians.Montel

open scoped Manifold ContDiff
open Bundle

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `supNormK` definition + basic properties -/

/-- The assembled sup-norm on `HolomorphicOneForms X`: sup over `chartCover` of
per-chart `chartNormK`. -/
noncomputable def HolomorphicOneForms.supNormK
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) : ℝ :=
  (chartCover : Finset X).sup' (chartCover_nonempty)
    (fun x₀ => HolomorphicOneForms.chartNormK α x₀)

omit [ConnectedSpace X] in
/-- `supNormK` is non-negative. -/
theorem HolomorphicOneForms.supNormK_nonneg
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) :
    0 ≤ HolomorphicOneForms.supNormK α := by
  unfold HolomorphicOneForms.supNormK
  obtain ⟨x₀, hx₀⟩ := chartCover_nonempty (X := X)
  exact le_trans (HolomorphicOneForms.chartNormK_nonneg α x₀)
    (Finset.le_sup' _ hx₀)

omit [ConnectedSpace X] in
/-- Chart-local bound via supNormK. -/
theorem HolomorphicOneForms.chartNormK_le_supNormK
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    HolomorphicOneForms.chartNormK α x₀ ≤ HolomorphicOneForms.supNormK α := by
  unfold HolomorphicOneForms.supNormK
  exact Finset.le_sup' _ hx₀

omit [ConnectedSpace X] in
/-- Pointwise bound via `supNormK`. -/
theorem HolomorphicOneForms.norm_localRep_le_supNormK
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    {y : X} (hy : y ∈ shrunkChart (X := X) x₀) :
    ‖localRep α x₀ y‖ ≤ HolomorphicOneForms.supNormK α :=
  le_trans (HolomorphicOneForms.norm_localRep_le_chartNormK α x₀ hy)
    (HolomorphicOneForms.chartNormK_le_supNormK α hx₀)

omit [ConnectedSpace X] in
/-- `supNormK` of zero is zero. -/
theorem HolomorphicOneForms.supNormK_zero :
    HolomorphicOneForms.supNormK (0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) = 0 := by
  unfold HolomorphicOneForms.supNormK
  simp [HolomorphicOneForms.chartNormK_zero]

omit [ConnectedSpace X] in
/-- Triangle inequality for `supNormK`. -/
theorem HolomorphicOneForms.supNormK_add_le
    (α β : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) :
    HolomorphicOneForms.supNormK (α + β) ≤
      HolomorphicOneForms.supNormK α + HolomorphicOneForms.supNormK β := by
  unfold HolomorphicOneForms.supNormK
  rw [Finset.sup'_le_iff]
  intro x₀ hx₀
  calc HolomorphicOneForms.chartNormK (α + β) x₀
      ≤ HolomorphicOneForms.chartNormK α x₀ +
        HolomorphicOneForms.chartNormK β x₀ :=
        HolomorphicOneForms.chartNormK_add_le α β x₀
    _ ≤ (chartCover : Finset X).sup' chartCover_nonempty
          (fun y => HolomorphicOneForms.chartNormK α y) +
        (chartCover : Finset X).sup' chartCover_nonempty
          (fun y => HolomorphicOneForms.chartNormK β y) :=
        add_le_add (Finset.le_sup' _ hx₀) (Finset.le_sup' _ hx₀)

omit [ConnectedSpace X] in
/-- Homogeneity of `supNormK`. -/
theorem HolomorphicOneForms.supNormK_smul (c : ℂ)
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) :
    HolomorphicOneForms.supNormK (c • α) = ‖c‖ * HolomorphicOneForms.supNormK α := by
  unfold HolomorphicOneForms.supNormK
  have hrw : (fun x₀ : X => HolomorphicOneForms.chartNormK (c • α) x₀) =
      fun x₀ => ‖c‖ * HolomorphicOneForms.chartNormK α x₀ := by
    funext x₀; exact HolomorphicOneForms.chartNormK_smul c α x₀
  rw [hrw, ← Finset.mul₀_sup' (norm_nonneg c) _ _ chartCover_nonempty]

omit [ConnectedSpace X] in
/-- Negation invariance: `supNormK (-α) = supNormK α`. -/
theorem HolomorphicOneForms.supNormK_neg
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) :
    HolomorphicOneForms.supNormK (-α) = HolomorphicOneForms.supNormK α := by
  have h : -α = (-1 : ℂ) • α := (neg_one_smul ℂ α).symm
  rw [h, HolomorphicOneForms.supNormK_smul]
  simp

/-! ### Vanishing consequences of `supNormK α = 0` -/

omit [ConnectedSpace X] [Nonempty X] in
/-- If `chartNormK α x₀ = 0` then `localRep α x₀ y = 0` for y ∈ shrunkChart x₀. -/
theorem HolomorphicOneForms.localRep_eq_zero_of_chartNormK_eq_zero
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) (h : HolomorphicOneForms.chartNormK α x₀ = 0)
    (y : X) (hy : y ∈ shrunkChart (X := X) x₀) :
    localRep α x₀ y = 0 := by
  have hbd := HolomorphicOneForms.chartNormK_bddAbove α x₀
  have hle : ‖localRep α x₀ y‖ ≤ HolomorphicOneForms.chartNormK α x₀ := by
    unfold HolomorphicOneForms.chartNormK
    exact le_csSup hbd ⟨y, hy, rfl⟩
  rw [h] at hle
  have : ‖localRep α x₀ y‖ = 0 := le_antisymm hle (norm_nonneg _)
  exact norm_eq_zero.mp this

omit [ConnectedSpace X] in
/-- If `supNormK α = 0` then `chartNormK α x = 0` for every `x ∈ chartCover`. -/
theorem HolomorphicOneForms.chartNormK_eq_zero_of_supNormK_eq_zero
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h : HolomorphicOneForms.supNormK α = 0)
    (x : X) (hx : x ∈ (chartCover : Finset X)) :
    HolomorphicOneForms.chartNormK α x = 0 := by
  have hle : HolomorphicOneForms.chartNormK α x ≤ HolomorphicOneForms.supNormK α := by
    unfold HolomorphicOneForms.supNormK
    exact Finset.le_sup' _ hx
  rw [h] at hle
  exact le_antisymm hle (HolomorphicOneForms.chartNormK_nonneg α x)

omit [ConnectedSpace X] in
/-- `supNormK α = 0` forces `localRep α x₀ y = 0` for every
`x₀ ∈ chartCover` and `y ∈ shrunkChart x₀`. -/
theorem HolomorphicOneForms.localRep_eq_zero_of_supNormK_eq_zero
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h : HolomorphicOneForms.supNormK α = 0)
    (x₀ : X) (hx₀ : x₀ ∈ (chartCover : Finset X))
    (y : X) (hy : y ∈ shrunkChart (X := X) x₀) :
    localRep α x₀ y = 0 :=
  HolomorphicOneForms.localRep_eq_zero_of_chartNormK_eq_zero α x₀
    (HolomorphicOneForms.chartNormK_eq_zero_of_supNormK_eq_zero α h x₀ hx₀) y hy

/-! ### The key geometric content: localRep = 0 on a base-set point forces α.toFun = 0 -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- If the local representative of α vanishes at y ∈ baseSet of the trivialization
at x₀, then `α.toFun y = 0` as a continuous linear map.

This uses that `T_y X ≃L[ℂ] ℂ` on the trivialization base set (X is charted
over ℂ, so tangent spaces are 1-dim over ℂ), and that the image of `1` under
`(φ.symm)` is a nonzero vector — a CLM vanishing on a spanning vector is 0. -/
theorem alpha_toFun_eq_zero_of_localRep_eq_zero
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ y : X)
    (hy : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet)
    (h : localRep α x₀ y = 0) :
    α.toFun y = 0 := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀ with he_def
  set φ := e.continuousLinearEquivAt ℂ y hy with hφ_def
  have hφsymm : (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) = e.symmL ℂ y :=
    Trivialization.symm_continuousLinearEquivAt_eq' e hy
  have hcomp : (α.toFun y : TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ).comp
      (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) = 0 := by
    apply ContinuousLinearMap.ext_ring
    show α.toFun y ((φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) 1) = 0
    rw [hφsymm]
    exact h
  have hext : (α.toFun y : TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ) =
      ((α.toFun y).comp (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y)).comp
        (φ : TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ) := by
    apply ContinuousLinearMap.ext
    intro w
    change α.toFun y w = α.toFun y (φ.symm (φ w))
    rw [φ.symm_apply_apply]
  rw [hext, hcomp, ContinuousLinearMap.zero_comp]

/-! ### Positive-definiteness -/

omit [ConnectedSpace X] in
/-- Positive-definiteness: `supNormK α = 0 → α = 0`. -/
theorem HolomorphicOneForms.eq_zero_of_supNormK_eq_zero
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h : HolomorphicOneForms.supNormK α = 0) :
    α = 0 := by
  apply ContMDiffSection.ext
  intro y
  have hmem : y ∈ (Set.univ : Set X) := Set.mem_univ _
  rw [← iUnion_shrunkChart_chartCover_eq (X := X)] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨x₀, hx₀mem, hyx₀⟩ := hmem
  have hlocal := HolomorphicOneForms.localRep_eq_zero_of_supNormK_eq_zero α h x₀ hx₀mem y hyx₀
  have hy_baseSet :
      y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact shrunkChart_subset_source x₀ hx₀mem hyx₀
  have htofun := alpha_toFun_eq_zero_of_localRep_eq_zero α x₀ y hy_baseSet hlocal
  change α.toFun y = (0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
    (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)).toFun y
  rw [htofun]
  have : (⇑(0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))) = 0 :=
    ContMDiffSection.coe_zero
  exact (congrFun this y).symm

end Jacobians.Montel
