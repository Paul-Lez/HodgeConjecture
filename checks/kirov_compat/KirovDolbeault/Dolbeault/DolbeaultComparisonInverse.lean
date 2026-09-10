/-
  Dolbeault's comparison theorem — **inverse direction** (`Čech → Dolbeault`), the CONSTRUCTION.

  This file builds the inverse map `cech_to_dolbeault : H¹(X, 𝒪) → H^{0,1}(X)` from the
  partition-of-unity backbone, the `∂̄ρ_k` gluing data, the ℂ-scaling toolkit, and the glued-form
  operator `cechToDolbeaultForm` (Bott–Tu double-sum). It deliberately imports only the *light*
  dependencies (`DolbeaultComparison`, `CechH0`, `ChartDiskCover`, partitions of unity) and NOT the
  heavy forward file `DolbeaultComparisonProof` — the construction uses no forward symbol, so keeping
  this file off that import makes it fast to elaborate. The final assembly into the `ℝ`-linear
  equivalence (which needs the forward map `dolbeault_to_cech`) lives in `DolbeaultComparisonEquiv`.
-/
import KirovDolbeault.Dolbeault.DolbeaultComparison
import KirovDolbeault.Dolbeault.CechH0
import KirovDolbeault.Dolbeault.HoloRep
import KirovDolbeault.Dolbeault.ChartDiskCover
import KirovDolbeault.MeromorphicNFRepair
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.BumpFunction

open scoped Manifold ContDiff Bundle Topology
open TopologicalSpace (Opens)
open Filter

-- Same permissive transparency as `RealForms` (the section hom-bundle instances, and any
-- `Finset.sum` / ℂ-scaling over `SmoothCOneForms`, need it).
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable (𝔘 : FiniteCover X)


/-! ### Sorry-free backbone of the Čech → Dolbeault map: the partition of unity

The Čech → Dolbeault globalization needs a smooth partition of unity `{ρ_i}` subordinate to the
cover. We provide it **completely** from Mathlib (`SmoothPartitionOfUnity.exists_isSubordinate`,
available because a compact `T2` `ℂ`-manifold is a `σ`-compact finite-dimensional real manifold via
`RealManifold`). This `ρ` is the actual analytic input `h_i := ∑_k ρ_k · f_ik` is built from. -/

/-- **(Čech → Dolbeault backbone, complete.)** The partition-of-unity *telescoping identity* — the
algebraic heart of the Čech → Dolbeault coboundary construction. For any additive Čech `1`-cocycle
`f` (`f_jk − f_ik + f_ij = 0`, the `cechDelta1 = 0` relation) and any weights `ρ` summing to `1`, the
globalized functions `h_i := ∑_k ρ_k • f_ki` satisfy `h_j − h_i = f_ij` — i.e. the cocycle becomes a
coboundary of the smooth (partition-of-unity-glued) `0`-cochain. Pure module algebra (it is what
"`∂̄h_i` glue to a global form" rests on); proven here abstractly over any `ℂ`-module. -/
theorem cechCoboundary_telescoping {ι : Type*} [Fintype ι] {M : Type*} [AddCommGroup M] [Module ℂ M]
    (f : ι → ι → M) (hcoc : ∀ a b c, f b c - f a c + f a b = 0)
    (ρ : ι → ℂ) (hρ : ∑ k, ρ k = 1) (i j : ι) :
    (∑ k, ρ k • f k j) - (∑ k, ρ k • f k i) = f i j := by
  rw [← Finset.sum_sub_distrib]
  have hpt : ∀ k, ρ k • f k j - ρ k • f k i = ρ k • f i j := fun k => by
    rw [← smul_sub]; congr 1; linear_combination (norm := module) -hcoc k i j
  simp_rw [hpt, ← Finset.sum_smul, hρ, one_smul]

/-- **(Čech → Dolbeault backbone, complete.)** A smooth partition of unity subordinate to the
finite cover `𝔘`, over the real-manifold structure `𝓘(ℝ, ℂ)`. The input for the globalization
`h_i := ∑_k ρ_k · f_ik`. -/
theorem exists_smoothPartitionOfUnity_subordinate :
    ∃ ρ : SmoothPartitionOfUnity 𝔘.ι 𝓘(ℝ, ℂ) X (Set.univ : Set X),
      ρ.IsSubordinate (fun i => (𝔘.U i : Set X)) := by
  have hcov : (Set.univ : Set X) ⊆ ⋃ i, (𝔘.U i : Set X) := by
    rw [Set.univ_subset_iff, ← TopologicalSpace.Opens.coe_iSup, 𝔘.covers]; rfl
  exact SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ
    (fun i => (𝔘.U i : Set X)) (fun i => (𝔘.U i).isOpen) hcov


/-- `ℝ → ℂ` as a smooth map, for coercing the real-valued PoU functions to `SmoothCFunctions`. -/
noncomputable def ofRealCM : ContMDiffMap (𝓘(ℝ)) (𝓘(ℝ, ℂ)) ℝ ℂ (⊤ : ℕ∞) :=
  ⟨Complex.ofReal, Complex.ofRealCLM.contMDiff⟩

/-- A fixed smooth partition of unity subordinate to the cover (`exists_smoothPartitionOfUnity_
subordinate`) — the globalization input for the inverse map. -/
noncomputable def cechPoU (𝔇 : ChartDiskCover X) :
    SmoothPartitionOfUnity 𝔇.toFiniteCover.ι 𝓘(ℝ, ℂ) X (Set.univ : Set X) :=
  (exists_smoothPartitionOfUnity_subordinate 𝔇.toFiniteCover).choose

theorem cechPoU_subordinate (𝔇 : ChartDiskCover X) :
    (cechPoU 𝔇).IsSubordinate (fun i => (𝔇.U i : Set X)) :=
  (exists_smoothPartitionOfUnity_subordinate 𝔇.toFiniteCover).choose_spec

/-- The `k`-th PoU function as a complex `SmoothCFunctions` (`ρ̃_k = ofReal ∘ ρ_k`). -/
noncomputable def rhoC (𝔇 : ChartDiskCover X) (k : 𝔇.toFiniteCover.ι) : SmoothCFunctions X :=
  ofRealCM.comp (cechPoU 𝔇 k)

/-- `∂̄ρ_k` as a global `(0,1)`-form. -/
noncomputable def dbarRho (𝔇 : ChartDiskCover X) (k : 𝔇.toFiniteCover.ι) : SmoothCOneForms X :=
  dbarL (rhoC 𝔇 k)

/-- The PoU functions sum to the constant `1` (finite cover ⇒ plain `Finset.sum`). -/
theorem sum_rhoC (𝔇 : ChartDiskCover X) : ∑ k, rhoC 𝔇 k = 1 := by
  refine ContMDiffMap.ext fun x => ?_
  have h1 : (⇑(∑ k, rhoC 𝔇 k) : X → ℂ) = ∑ k, ⇑(rhoC 𝔇 k) :=
    map_sum ContMDiffMap.coeFnAddMonoidHom _ _
  rw [show (∑ k, rhoC 𝔇 k) x = (⇑(∑ k, rhoC 𝔇 k) : X → ℂ) x from rfl, h1, Finset.sum_apply,
    ContMDiffMap.coe_one, Pi.one_apply]
  show ∑ k, ((cechPoU 𝔇 k x : ℝ) : ℂ) = 1
  rw [← Complex.ofReal_sum, ← finsum_eq_sum_of_fintype,
    (cechPoU 𝔇).sum_eq_one (Set.mem_univ x), Complex.ofReal_one]

/-- **The gluing relation** `∑_k ∂̄ρ_k = 0` (`∂̄` of `∑ρ_k = 1` is `∂̄1 = 0`). This is what makes the
local `∂̄η_i` agree on overlaps. -/
theorem dbarL_one_eq_zero : dbarL (1 : SmoothCFunctions X) = 0 := by
  rw [dbarL_eq_proj01L_differential]
  have hd : differential (1 : SmoothCFunctions X) = 0 := by
    refine ContMDiffSection.ext fun x => ?_
    show mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun _ : X => (1 : ℂ)) x = 0
    exact mfderiv_const
  rw [hd]; exact proj01L.map_zero

/-- **The gluing relation** `∑_k ∂̄ρ_k = 0` — `∂̄` of `∑_k ρ_k = 1` is `∂̄1 = 0`. This is what makes
the local primitives `∂̄η_i` agree on overlaps (so they glue to a global `(0,1)`-form). The summand
forms are `dbarRho 𝔇 k = dbarL (rhoC 𝔇 k)`; `dbarL` is `ℝ`-linear, so the sum commutes through it
(`map_sum`) onto `∑_k ρ_k = 1` (`sum_rhoC`).

Historical note: summing `SmoothCOneForms` (`Finset.sum`) was once thought to be blocked by the
`Module ℝ` section-instance diamond (`reference_module_real_diamond`). It is not: with the file-level
`set_option backward.isDefEq.respectTransparency false` already in force (for the hom-bundle section
instances), `AddCommMonoid (SmoothCOneForms X)` synthesises and the form-sum elaborates normally. -/
theorem sum_dbarRho_eq_zero (𝔇 : ChartDiskCover X) :
    ∑ k, dbarRho 𝔇 k = 0 := by
  have h : ∑ k, dbarRho 𝔇 k = dbarL (∑ k, rhoC 𝔇 k) := (map_sum dbarL _ _).symm
  rw [h, sum_rhoC, dbarL_one_eq_zero]

/-- Value form of `sum_rhoC`: `∑_k ρ_k x = 1` pointwise. -/
theorem sum_rhoC_apply (𝔇 : ChartDiskCover X) (x : X) : ∑ k, (rhoC 𝔇 k x) = 1 := by
  have h1 : (⇑(∑ k, rhoC 𝔇 k) : X → ℂ) = ∑ k, ⇑(rhoC 𝔇 k) :=
    map_sum ContMDiffMap.coeFnAddMonoidHom _ _
  have h2 : (∑ k, rhoC 𝔇 k) x = ∑ k, (rhoC 𝔇 k x) := by
    rw [show ((∑ k, rhoC 𝔇 k) x : ℂ) = (⇑(∑ k, rhoC 𝔇 k) : X → ℂ) x from rfl, h1, Finset.sum_apply]
  rw [← h2, sum_rhoC, ContMDiffMap.coe_one, Pi.one_apply]

/-- Value form of `sum_dbarRho_eq_zero`: `∑_k ∂̄ρ_k x = 0` pointwise. -/
theorem sum_dbarRho_apply (𝔇 : ChartDiskCover X) (x : X) :
    ∑ k, ((dbarRho 𝔇 k) x) = 0 := by
  have h1 : (⇑(∑ k, dbarRho 𝔇 k)) = ∑ k, ⇑(dbarRho 𝔇 k) :=
    map_sum (ContMDiffSection.coeAddHom _ _ _ _) _ _
  have h2 : (∑ k, dbarRho 𝔇 k) x = ∑ k, ((dbarRho 𝔇 k) x) := by
    rw [show ((∑ k, dbarRho 𝔇 k) x) = (⇑(∑ k, dbarRho 𝔇 k)) x from rfl, h1, Finset.sum_apply]
  rw [← h2, sum_dbarRho_eq_zero, ContMDiffSection.coe_zero, Pi.zero_apply]

/-! ### ℂ-valued function scaling of `(0,1)`-forms (the double-sum term builder)

Each Bott–Tu double-sum term is `(ρ_j·F_jk) • ∂̄ρ_k` — a `(0,1)`-form `∂̄ρ_k` scaled by a ℂ-valued
smooth function. The base manifold model `𝓘(ℝ,ℂ)` is an `ℝ`-model, so Mathlib's `smul_section` only
covers `ℝ`-scaling; ℂ-scaling is recovered by writing `z • β = (mul ℝ ℂ z).comp β` (post-compose
mult-by-`z`) and using `clm_comp`. The result stays `(0,1)` because `proj01` commutes with the
ℂ-scale (`proj01_smul`). -/

/-- **(`ContMDiffAt` form, the workhorse.)** Scaling a smooth `(0,1)`-valued section by a ℂ-valued
function, fiberwise, is smooth at `x₀` when both are. The ℂ-smul is post-composition on the trivial
codomain (`z • β = (mul ℝ ℂ z).comp β`), so it slides through the tangent `symmL`, reducing to
`clm_comp` of the smooth `x ↦ mul ℝ ℂ (F x)` and the smooth in-coordinates of `s`. -/
theorem contMDiffAt_cSmul_section {F : X → ℂ}
    {s : ∀ x : X, TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x} {x₀ : X}
    (hF : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) F x₀)
    (hs : ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ)) (⊤ : ℕ∞)
      (fun x => (⟨x, s x⟩ : Bundle.TotalSpace (ℂ →L[ℝ] ℂ)
        (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x))) x₀) :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ)) (⊤ : ℕ∞)
      (fun x => (⟨x, (F x) • (s x)⟩ : Bundle.TotalSpace (ℂ →L[ℝ] ℂ)
        (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x))) x₀ := by
  rw [contMDiffAt_hom_bundle] at hs ⊢
  refine ⟨contMDiffAt_id, ?_⟩
  simp only [ContinuousLinearMap.inCoordinates,
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    Bundle.Trivial.fiberBundle_trivializationAt', ContinuousLinearMap.id_comp] at hs ⊢
  have hM : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ) (⊤ : ℕ∞)
      (fun x => ContinuousLinearMap.mul ℝ ℂ (F x)) x₀ :=
    ContMDiffAt.clm_apply contMDiffAt_const hF
  refine (hM.clm_comp hs.2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Global form of `contMDiffAt_cSmul_section` for a `SmoothCFunctions` scalar and a smooth form. -/
theorem contMDiff_cSmul_section (c : SmoothCFunctions X) (g : SmoothCOneForms X) :
    ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ)) (⊤ : ℕ∞)
      (fun x => (⟨x, (c x) • (g x)⟩ : Bundle.TotalSpace (ℂ →L[ℝ] ℂ)
        (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x))) :=
  fun x₀ => contMDiffAt_cSmul_section (c.contMDiff x₀) (g.contMDiff_toFun x₀)

/-- **ℂ-valued smooth-function scaling of a `(0,1)`-valued smooth form** (the double-sum term builder):
`(c • g) x = c x • g x`, a smooth `(0,1)`-valued form. -/
noncomputable def cSmulForm (c : SmoothCFunctions X) (g : SmoothCOneForms X) : SmoothCOneForms X where
  toFun := fun x => (c x) • (g x)
  contMDiff_toFun := contMDiff_cSmul_section c g

@[simp] theorem cSmulForm_apply (c : SmoothCFunctions X) (g : SmoothCOneForms X) (x : X) :
    cSmulForm c g x = (c x) • (g x) := rfl

/-- The `(0,1)`-projection commutes with ℂ-scaling of the codomain: `proj01 (z • α) = z • proj01 α`
(`z` factors out of the Wirtinger average). -/
theorem proj01_smul (z : ℂ) (α : ℂ →L[ℝ] ℂ) : proj01 (z • α) = z • proj01 α := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [proj01_apply, proj01_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, mulI, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.real_smul]
  ring

/-- ℂ-scaling preserves the `(0,1)`-forms: `c • g ∈ A^{0,1}` whenever `g ∈ A^{0,1}`. (Witness
`c • h` where `g = proj01L h`; `proj01` commutes with the ℂ-scale, `proj01_smul`.) -/
theorem cSmulForm_mem_zeroOne (c : SmoothCFunctions X) {g : SmoothCOneForms X}
    (hg : g ∈ OneFormsZeroOne X) : cSmulForm c g ∈ OneFormsZeroOne X := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨cSmulForm c h, ?_⟩
  refine ContMDiffSection.ext fun x => ?_
  simp only [proj01L_apply, proj01Section_apply, cSmulForm_apply]
  exact proj01_smul (c x) (h x)

/-- `ℂ`-multiplication is real-`C^∞` (it is `ℝ`-bilinear) — the instance Mathlib provides only over the
*complex* model `𝓘(ℂ)`, supplied here over the real model `𝓘(ℝ,ℂ)` so that `SmoothCFunctions X` is a
ring (needed for the `∂̄` Leibniz rule). -/
instance contMDiffMul_real_complex : ContMDiffMul 𝓘(ℝ, ℂ) (⊤ : ℕ∞) ℂ :=
  { (inferInstance : IsManifold 𝓘(ℝ, ℂ) (⊤ : ℕ∞) ℂ) with
    contMDiff_mul := by
      rw [contMDiff_iff]
      refine ⟨continuous_mul, fun x y => ?_⟩
      simp only [mfld_simps]
      rw [contDiffOn_univ]
      exact contDiff_mul }

/-- **The `∂̄` Leibniz rule** `∂̄(g₁·g₂) = g₂·∂̄g₁ + g₁·∂̄g₂` (`∂̄ = proj01 ∘ mfderiv`; `mfderiv` has the
product rule `HasMFDerivAt.mul`, `proj01` commutes with the ℂ-scale `proj01_smul`). -/
theorem dbarL_mul (g₁ g₂ : SmoothCFunctions X) :
    dbarL (g₁ * g₂) = cSmulForm g₂ (dbarL g₁) + cSmulForm g₁ (dbarL g₂) := by
  refine ContMDiffSection.ext fun x => ?_
  have h1 : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑g₁) x (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑g₁) x) :=
    (g₁.contMDiff.mdifferentiable (by simp) x).hasMFDerivAt
  have h2 : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑g₂) x (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑g₂) x) :=
    (g₂.contMDiff.mdifferentiable (by simp) x).hasMFDerivAt
  show proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑(g₁ * g₂)) x)
    = g₂ x • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑g₁) x)
      + g₁ x • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑g₂) x)
  rw [show (⇑(g₁ * g₂) : X → ℂ) = ⇑g₁ * ⇑g₂ from rfl, (h1.mul h2).mfderiv, map_add,
    proj01_smul, proj01_smul, add_comm]

/-! ### Support of the gluing forms `∂̄ρ_k`

Each double-sum term `ρ_j·F_jk·∂̄ρ_k` is globally smooth because `∂̄ρ_k` is supported in `U_k`
(and `ρ_j` in `U_j`), confining the product to the overlap `U_j ∩ U_k` where `F_jk` lives. -/

/-- `∂̄` shrinks support: `∂̄u x = 0` wherever `u` is locally constant (`x ∉ tsupport u`). (Stated
pointwise — section coes are dependently typed, so `tsupport` of a section is not available.) -/
theorem dbarL_eq_zero_of_notMem_tsupport (u : SmoothCFunctions X) {x : X}
    (hx : x ∉ tsupport (⇑u : X → ℂ)) : (dbarL u) x = 0 := by
  have h0 : (⇑u : X → ℂ) =ᶠ[nhds x] 0 := by
    filter_upwards [(isClosed_tsupport (⇑u : X → ℂ)).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [dbarL_apply]
  show proj01 ((differential u).toFun x) = 0
  have hmf : (differential u).toFun x = 0 := by
    show mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x = 0
    rw [h0.mfderiv_eq]; exact mfderiv_const
  rw [hmf, map_zero]

/-- `∂̄ρ_k x = 0` for `x ∉ tsupport ρ_k` — so `∂̄ρ_k` is supported in `U_k` (`ρ_k` subordinate). -/
theorem dbarRho_eq_zero_of_notMem (𝔇 : ChartDiskCover X) (k : 𝔇.toFiniteCover.ι) {x : X}
    (hx : x ∉ tsupport (cechPoU 𝔇 k)) : (dbarRho 𝔇 k) x = 0 := by
  refine dbarL_eq_zero_of_notMem_tsupport (rhoC 𝔇 k) (fun hc => hx ?_)
  refine closure_mono (fun y hy => ?_) hc
  simp only [Function.mem_support, ne_eq] at hy ⊢
  exact fun h0 => hy (by simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM, h0]; rfl)

/-- The punctured neighborhood of any point of a `ℂ`-manifold is `NeBot` (no isolated points). -/
theorem nhdsNE_neBot_of_chart (x : X) : (𝓝[≠] x).NeBot := by
  have hsrc : x ∈ (chartAt (H := ℂ) x).source := mem_chart_source ℂ x
  exact ((chartAt (H := ℂ) x).symm.tendsto_nhdsNE (x := (chartAt (H := ℂ) x) x)
    (by simp [(chartAt (H := ℂ) x).map_source hsrc])).neBot.mono
    (by simp only [(chartAt (H := ℂ) x).left_inv hsrc]; exact le_rfl)

/-- `Gext` is additive (extension by `0`). -/
theorem Gext_add {U : Opens X} (f g : U → ℂ) : Gext (f + g) = Gext f + Gext g := by
  funext x
  simp only [Gext, Pi.add_apply]
  split <;> simp

/-- `Gext` is homogeneous (extension by `0`). -/
theorem Gext_smul {U : Opens X} (c : ℂ) (g : U → ℂ) : Gext (c • g) = c • Gext g := by
  funext x
  simp only [Gext, Pi.smul_apply]
  split <;> simp

/-- `Gext` respects subtraction (extension by `0`). -/
theorem Gext_sub {U : Opens X} (f g : U → ℂ) : Gext (f - g) = Gext f - Gext g := by
  funext x
  simp only [Gext, Pi.sub_apply]
  split <;> simp

/-- For a holomorphic (`OmegaDGerm 0`) class, the analytic representative `Gext(holoRep)` has a genuine
limit along `𝓝[≠] x` at every `x ∈ V` (order `≥ 0` ⟹ the limit exists; this is `holoFn x`). -/
theorem holoFn_tendsto {V : Opens X} {g : MGerm V} (hg : g ∈ OmegaDGerm (0 : Divisor X) V) {x : X}
    (hx : x ∈ V) : ∃ c, Tendsto (Gext (holoRep hg)) (𝓝[≠] x) (𝓝 c) := by
  set φ := chartAt (H := ℂ) x with hφ
  have hmero : MeromorphicAt (Gext (holoRep hg) ∘ φ.symm) (φ x) :=
    Gext_meromorphicAt (holoRep_mem hg).1 hx
  have hord : 0 ≤ meromorphicOrderAt (Gext (holoRep hg) ∘ φ.symm) (φ x) := by
    rw [← ordU_eq_orderAt_Gext (holoRep hg) hx]; simpa using (mem_OmegaD.1 (holoRep_mem hg)).2 ⟨x, hx⟩
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hmero hord
  refine ⟨c, (hc.comp (φ.tendsto_nhdsNE (mem_chart_source ℂ x))).congr' ?_⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds (φ.open_source.mem_nhds (mem_chart_source ℂ x))] with z hz
  simp [Function.comp, φ.left_inv hz]

/-! ### The holomorphic representative function and the double-sum terms -/

/-- **`holoFn` is additive** at every `x ∈ V` (the choice in `holoRep` washes out: the limit-repair
`limUnder` is insensitive to codiscrete junk, so it depends only on the germ class, and the limit is
additive). -/
theorem holoFn_add {V : Opens X} {g₁ g₂ : MGerm V} (hg₁ : g₁ ∈ OmegaDGerm (0 : Divisor X) V)
    (hg₂ : g₂ ∈ OmegaDGerm (0 : Divisor X) V) (hg : g₁ + g₂ ∈ OmegaDGerm (0 : Divisor X) V)
    {x : X} (hx : x ∈ V) : holoFn hg x = holoFn hg₁ x + holoFn hg₂ x := by
  haveI := nhdsNE_neBot_of_chart x
  obtain ⟨c₁, hc₁⟩ := holoFn_tendsto hg₁ hx
  obtain ⟨c₂, hc₂⟩ := holoFn_tendsto hg₂ hx
  have hgerm : toGerm V (holoRep hg₁ + holoRep hg₂) = toGerm V (holoRep hg) := by
    rw [map_add, toGerm_holoRep hg₁, toGerm_holoRep hg₂, toGerm_holoRep hg]
  have heq : Gext (holoRep hg) =ᶠ[𝓝[≠] x] Gext (holoRep hg₁) + Gext (holoRep hg₂) := by
    have hmatch : rawRestrictG (inf_le_right : V ⊓ V ≤ V) (toGerm V (holoRep hg₁ + holoRep hg₂))
        = rawRestrictG (inf_le_left : V ⊓ V ≤ V) (toGerm V (holoRep hg)) := by rw [hgerm]
    have h := Gext_overlap_eventuallyEq (holoRep hg) (holoRep hg₁ + holoRep hg₂) hmatch hx hx
    rwa [Gext_add] at h
  show limUnder (𝓝[≠] x) (Gext (holoRep hg)) = holoFn hg₁ x + holoFn hg₂ x
  rw [show holoFn hg₁ x = c₁ from hc₁.limUnder_eq, show holoFn hg₂ x = c₂ from hc₂.limUnder_eq]
  exact ((hc₁.add hc₂).congr' heq.symm).limUnder_eq

/-- **`holoFn` is homogeneous** at every `x ∈ V` (same washout as `holoFn_add`). -/
theorem holoFn_smul {V : Opens X} (c : ℂ) {g : MGerm V} (hg : g ∈ OmegaDGerm (0 : Divisor X) V)
    (hcg : c • g ∈ OmegaDGerm (0 : Divisor X) V) {x : X} (hx : x ∈ V) :
    holoFn hcg x = c • holoFn hg x := by
  haveI := nhdsNE_neBot_of_chart x
  obtain ⟨c₀, hc₀⟩ := holoFn_tendsto hg hx
  have hgerm : toGerm V (c • holoRep hg) = toGerm V (holoRep hcg) := by
    rw [map_smul, toGerm_holoRep hg, toGerm_holoRep hcg]
  have heq : Gext (holoRep hcg) =ᶠ[𝓝[≠] x] c • Gext (holoRep hg) := by
    have hmatch : rawRestrictG (inf_le_right : V ⊓ V ≤ V) (toGerm V (c • holoRep hg))
        = rawRestrictG (inf_le_left : V ⊓ V ≤ V) (toGerm V (holoRep hcg)) := by rw [hgerm]
    have h := Gext_overlap_eventuallyEq (holoRep hcg) (c • holoRep hg) hmatch hx hx
    rwa [Gext_smul] at h
  show limUnder (𝓝[≠] x) (Gext (holoRep hcg)) = c • holoFn hg x
  rw [show holoFn hg x = c₀ from hc₀.limUnder_eq]
  exact ((hc₀.const_smul c).congr' heq.symm).limUnder_eq

/-- **`holoFn` respects subtraction** at `x ∈ V` (same washout as `holoFn_add`). -/
theorem holoFn_sub {V : Opens X} {g₁ g₂ : MGerm V} (hg₁ : g₁ ∈ OmegaDGerm (0 : Divisor X) V)
    (hg₂ : g₂ ∈ OmegaDGerm (0 : Divisor X) V) (hg : g₁ - g₂ ∈ OmegaDGerm (0 : Divisor X) V)
    {x : X} (hx : x ∈ V) : holoFn hg x = holoFn hg₁ x - holoFn hg₂ x := by
  haveI := nhdsNE_neBot_of_chart x
  obtain ⟨c₁, hc₁⟩ := holoFn_tendsto hg₁ hx
  obtain ⟨c₂, hc₂⟩ := holoFn_tendsto hg₂ hx
  have hgerm : toGerm V (holoRep hg₁ - holoRep hg₂) = toGerm V (holoRep hg) := by
    rw [map_sub, toGerm_holoRep hg₁, toGerm_holoRep hg₂, toGerm_holoRep hg]
  have heq : Gext (holoRep hg) =ᶠ[𝓝[≠] x] Gext (holoRep hg₁) - Gext (holoRep hg₂) := by
    have hmatch : rawRestrictG (inf_le_right : V ⊓ V ≤ V) (toGerm V (holoRep hg₁ - holoRep hg₂))
        = rawRestrictG (inf_le_left : V ⊓ V ≤ V) (toGerm V (holoRep hg)) := by rw [hgerm]
    have h := Gext_overlap_eventuallyEq (holoRep hg) (holoRep hg₁ - holoRep hg₂) hmatch hx hx
    rwa [Gext_sub] at h
  show limUnder (𝓝[≠] x) (Gext (holoRep hg)) = holoFn hg₁ x - holoFn hg₂ x
  rw [show holoFn hg₁ x = c₁ from hc₁.limUnder_eq, show holoFn hg₂ x = c₂ from hc₂.limUnder_eq]
  exact ((hc₁.sub hc₂).congr' heq.symm).limUnder_eq

/-- **`holoFn` depends only on the germ class.** Two memberships of equal germs give the same `holoFn`
at points of `V` (the `holoRep` choice washes out). -/
theorem holoFn_congr {V : Opens X} {g g' : MGerm V} (hg : g ∈ OmegaDGerm (0 : Divisor X) V)
    (hg' : g' ∈ OmegaDGerm (0 : Divisor X) V) (hgg : g = g') {x : X} (hx : x ∈ V) :
    holoFn hg x = holoFn hg' x := by
  haveI := nhdsNE_neBot_of_chart x
  have heq : Gext (holoRep hg) =ᶠ[𝓝[≠] x] Gext (holoRep hg') := by
    have hgerm : toGerm V (holoRep hg') = toGerm V (holoRep hg) := by
      rw [toGerm_holoRep, toGerm_holoRep, hgg]
    have hmatch : rawRestrictG (inf_le_right : V ⊓ V ≤ V) (toGerm V (holoRep hg'))
        = rawRestrictG (inf_le_left : V ⊓ V ≤ V) (toGerm V (holoRep hg)) := by rw [hgerm]
    exact Gext_overlap_eventuallyEq (holoRep hg) (holoRep hg') hmatch hx hx
  exact congrArg Filter.lim (Filter.map_congr heq)


/-- The `(j,k)` component of a Čech `1`-cocycle is a holomorphic (`OmegaDGerm 0`) germ-class on the
overlap `U_j ⊓ U_k` (the `sections1` part of `cocycles1`). -/
theorem cocycle_mem (𝔇 : ChartDiskCover X) (f : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X)))
    (j k : 𝔇.toFiniteCover.ι) :
    (f : 𝔇.toFiniteCover.Cochain1) (j, k) ∈ OmegaDGerm (0 : Divisor X) (𝔇.U j ⊓ 𝔇.U k) :=
  (Submodule.mem_inf.1 f.2).2 (j, k)

/-- The `(j,k)` **double-sum term** `T_jk = (ρ_j · F_jk) • ∂̄ρ_k`, a global smooth `(0,1)`-valued form
(`F_jk = holoFn` = the analytic representative). Globally smooth by a 3-case `ContMDiffAt` argument:
on the overlap `U_j ⊓ U_k` everything is smooth (`F_jk` via `holoFn_contMDiffAt`); off `tsupport ρ_j`
the factor `ρ_j` vanishes; off `tsupport ρ_k` the factor `∂̄ρ_k` vanishes — and these three opens cover
`X` (a point in neither support-complement lies in `tsupport ρ_j ∩ tsupport ρ_k ⊆ U_j ⊓ U_k`). -/
noncomputable def cechTerm (𝔇 : ChartDiskCover X)
    (f : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X))) (j k : 𝔇.toFiniteCover.ι) :
    SmoothCOneForms X where
  toFun := fun x => (rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 f j k) x) • (dbarRho 𝔇 k x)
  contMDiff_toFun := by
    intro x₀
    by_cases hbj : x₀ ∈ tsupport (cechPoU 𝔇 j)
    · by_cases hbk : x₀ ∈ tsupport (cechPoU 𝔇 k)
      · -- (a) x₀ ∈ U_j ⊓ U_k: the genuine smooth case.
        have hxV : x₀ ∈ ((𝔇.U j ⊓ 𝔇.U k : Opens X) : Set X) :=
          ⟨cechPoU_subordinate 𝔇 j hbj, cechPoU_subordinate 𝔇 k hbk⟩
        have hmulrho : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ) (⊤ : ℕ∞)
            (fun x => ContinuousLinearMap.mul ℝ ℂ (rhoC 𝔇 j x)) x₀ :=
          ContMDiffAt.clm_apply contMDiffAt_const ((rhoC 𝔇 j).contMDiff x₀)
        have hG : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
            (fun x => rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 f j k) x) x₀ :=
          (hmulrho.clm_apply (holoFn_contMDiffAt (cocycle_mem 𝔇 f j k) hxV)).congr_of_eventuallyEq
            (Filter.Eventually.of_forall fun x => by simp [ContinuousLinearMap.mul_apply'])
        exact contMDiffAt_cSmul_section hG ((dbarRho 𝔇 k).contMDiff_toFun x₀)
      · -- (c) x₀ ∉ tsupport ρ_k: `∂̄ρ_k = 0` on a neighborhood, so the term is `0`.
        refine ContMDiffAt.congr_of_eventuallyEq (Bundle.contMDiffAt_zeroSection ℝ
        (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x)) ?_
        filter_upwards [(isClosed_tsupport (cechPoU 𝔇 k)).isOpen_compl.mem_nhds hbk] with x hx
        have hV : (rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 f j k) x) • (dbarRho 𝔇 k x) = 0 := by
          rw [dbarRho_eq_zero_of_notMem 𝔇 k hx]; module
        exact congrArg (Bundle.TotalSpace.mk x) hV
    · -- (b) x₀ ∉ tsupport ρ_j: `ρ_j = 0` on a neighborhood, so the term is `0`.
      refine ContMDiffAt.congr_of_eventuallyEq (Bundle.contMDiffAt_zeroSection ℝ
        (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x)) ?_
      filter_upwards [(isClosed_tsupport (cechPoU 𝔇 j)).isOpen_compl.mem_nhds hbj] with x hx
      have hr : rhoC 𝔇 j x = 0 := by
        simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM,
          image_eq_zero_of_notMem_tsupport hx]; rfl
      have hV : (rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 f j k) x) • (dbarRho 𝔇 k x) = 0 := by
        rw [hr, zero_mul]; module
      exact congrArg (Bundle.TotalSpace.mk x) hV

/-- `proj01 α` at a vector, written out: `proj01 α v = ½(α v + i·α(i·v))` (the Wirtinger average). -/
theorem proj01_apply_val (α : ℂ →L[ℝ] ℂ) (v : ℂ) :
    proj01 α v = (2 : ℂ)⁻¹ * (α v + Complex.I * α (Complex.I * v)) := by
  rw [proj01_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, mulI, ContinuousLinearMap.mul_apply',
    Complex.real_smul]
  push_cast; ring

/-- The `(0,1)`-projection is idempotent (`proj01²= proj01`). -/
theorem proj01_idempotent (α : ℂ →L[ℝ] ℂ) : proj01 (proj01 α) = proj01 α := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [proj01_apply_val (proj01 α) v, proj01_apply_val α v, proj01_apply_val α (Complex.I * v)]
  have hI : Complex.I * (Complex.I * v) = -v := by rw [← mul_assoc, Complex.I_mul_I]; ring
  rw [hI, map_neg]
  linear_combination (-(1 / 4 : ℂ) * α v) * Complex.I_sq

/-- **`holoFn` is restriction-compatible.** For `V ≤ U` and `x ∈ V`, the analytic rep of the restricted
germ agrees with the original at `x` (`limUnder` depends only on the germ, which restriction preserves
at `x`). -/
theorem holoFn_restrict {U V : Opens X} (h : V ≤ U) {g : MGerm U}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) U) {x : X} (hx : x ∈ V) :
    holoFn (rawRestrictG_omegaDGerm h hg) x = holoFn hg x := by
  haveI := nhdsNE_neBot_of_chart x
  have heq : Gext (holoRep hg) =ᶠ[𝓝[≠] x] Gext (holoRep (rawRestrictG_omegaDGerm h hg)) := by
    have hmatch : rawRestrictG (inf_le_right : U ⊓ V ≤ V)
          (toGerm V (holoRep (rawRestrictG_omegaDGerm h hg)))
        = rawRestrictG (inf_le_left : U ⊓ V ≤ U) (toGerm U (holoRep hg)) := by
      rw [toGerm_holoRep, toGerm_holoRep, FiniteFamily.rawRestrictG_comp_apply]
    exact Gext_overlap_eventuallyEq (holoRep hg) (holoRep (rawRestrictG_omegaDGerm h hg)) hmatch
      (h hx) hx
  show limUnder (𝓝[≠] x) (Gext (holoRep (rawRestrictG_omegaDGerm h hg)))
    = limUnder (𝓝[≠] x) (Gext (holoRep hg))
  exact congrArg Filter.lim (Filter.map_congr heq.symm)

/-- **The Čech cocycle relation, at the `holoFn` value level.** For a `1`-cocycle `f` (so `δ¹f = 0`)
and `y ∈ U_i ⊓ U_j ⊓ U_k`, the holomorphic representatives satisfy `holoFn(f_ik) = holoFn(f_ij) +
holoFn(f_jk)`. From `δ¹f = 0` the germs obey `f_ik = f_jk + f_ij` on the triple overlap; `holoFn` is
additive (`holoFn_add`) and restriction-compatible (`holoFn_restrict`). The gateway to round-trip 2. -/
theorem holoFn_cocycle_add (𝔇 : ChartDiskCover X)
    (f : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X))) (i j k : 𝔇.toFiniteCover.ι) {y : X}
    (hy : y ∈ (𝔇.U i ⊓ 𝔇.U j ⊓ 𝔇.U k : Opens X)) :
    holoFn (cocycle_mem 𝔇 f i k) y
      = holoFn (cocycle_mem 𝔇 f i j) y + holoFn (cocycle_mem 𝔇 f j k) y := by
  have hjk : (𝔇.U i ⊓ 𝔇.U j ⊓ 𝔇.U k : Opens X) ≤ 𝔇.U j ⊓ 𝔇.U k :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hik : (𝔇.U i ⊓ 𝔇.U j ⊓ 𝔇.U k : Opens X) ≤ 𝔇.U i ⊓ 𝔇.U k :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hij : (𝔇.U i ⊓ 𝔇.U j ⊓ 𝔇.U k : Opens X) ≤ 𝔇.U i ⊓ 𝔇.U j := inf_le_left
  have hk0 : 𝔇.toFiniteCover.cechDelta1 (f : 𝔇.toFiniteCover.Cochain1) = 0 :=
    LinearMap.mem_ker.1 (Submodule.mem_inf.1 f.2).1
  have h0 : rawRestrictG hjk ((f : 𝔇.toFiniteCover.Cochain1) (j, k))
      - rawRestrictG hik ((f : 𝔇.toFiniteCover.Cochain1) (i, k))
      + rawRestrictG hij ((f : 𝔇.toFiniteCover.Cochain1) (i, j)) = 0 := by
    have hev := congrFun hk0 (i, j, k)
    simpa only [FiniteFamily.cechDelta1, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.comp_apply, LinearMap.proj_apply, Pi.zero_apply] using hev
  have hrel : rawRestrictG hik ((f : 𝔇.toFiniteCover.Cochain1) (i, k))
      = rawRestrictG hjk ((f : 𝔇.toFiniteCover.Cochain1) (j, k))
        + rawRestrictG hij ((f : 𝔇.toFiniteCover.Cochain1) (i, j)) := by
    have h1 : rawRestrictG hjk ((f : 𝔇.toFiniteCover.Cochain1) (j, k))
        + rawRestrictG hij ((f : 𝔇.toFiniteCover.Cochain1) (i, j))
        - rawRestrictG hik ((f : 𝔇.toFiniteCover.Cochain1) (i, k)) = 0 := by rw [← h0]; abel
    exact (sub_eq_zero.1 h1).symm
  rw [← holoFn_restrict hik (cocycle_mem 𝔇 f i k) hy,
    holoFn_congr (rawRestrictG_omegaDGerm hik (cocycle_mem 𝔇 f i k))
      (add_mem (rawRestrictG_omegaDGerm hjk (cocycle_mem 𝔇 f j k))
        (rawRestrictG_omegaDGerm hij (cocycle_mem 𝔇 f i j))) hrel hy,
    holoFn_add (rawRestrictG_omegaDGerm hjk (cocycle_mem 𝔇 f j k))
      (rawRestrictG_omegaDGerm hij (cocycle_mem 𝔇 f i j)) _ hy,
    holoFn_restrict hjk (cocycle_mem 𝔇 f j k) hy,
    holoFn_restrict hij (cocycle_mem 𝔇 f i j) hy]
  abel

/-- The **global primitive summand** `ρ_k · holoFn(s_k)` as a `SmoothCFunctions` (globally smooth: on
`U_k` both factors are smooth, off `tsupport ρ_k` it vanishes). The `∂̄` of `h = ∑_k primFn` is the
coboundary's image, since each `holoFn(s_k)` is holomorphic (`holoFn_dbar_eq_zero`). -/
noncomputable def primFn (𝔇 : ChartDiskCover X) (k : 𝔇.toFiniteCover.ι) {g : MGerm (𝔇.U k)}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) (𝔇.U k)) : SmoothCFunctions X :=
  ⟨fun x => rhoC 𝔇 k x * holoFn hg x, by
    intro x₀
    by_cases hb : x₀ ∈ tsupport (cechPoU 𝔇 k)
    · exact ((rhoC 𝔇 k).contMDiff x₀).mul (holoFn_contMDiffAt hg (cechPoU_subordinate 𝔇 k hb))
    · refine (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport (cechPoU 𝔇 k)).isOpen_compl.mem_nhds hb] with x hx
      have hr : rhoC 𝔇 k x = 0 := by
        simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM, image_eq_zero_of_notMem_tsupport hx]; rfl
      simp only [hr, zero_mul]⟩

@[simp] theorem primFn_apply (𝔇 : ChartDiskCover X) (k : 𝔇.toFiniteCover.ι) {g : MGerm (𝔇.U k)}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) (𝔇.U k)) (x : X) :
    primFn 𝔇 k hg x = rhoC 𝔇 k x * holoFn hg x := rfl

/-- **`∂̄(ρ_k·holoFn(s_k)) = holoFn(s_k)·∂̄ρ_k`** (the Leibniz identity, with the `holoFn` term killed
since `holoFn(s_k)` is holomorphic, `holoFn_dbar_eq_zero`). Pointwise, 2-case (on `tsupport ρ_k ⊆ U_k`
the product rule; off it both sides vanish). -/
theorem dbarL_primFn_apply (𝔇 : ChartDiskCover X) (k : 𝔇.toFiniteCover.ι) {g : MGerm (𝔇.U k)}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) (𝔇.U k)) (x : X) :
    (dbarL (primFn 𝔇 k hg)) x = holoFn hg x • (dbarRho 𝔇 k x) := by
  by_cases hb : x ∈ tsupport (cechPoU 𝔇 k)
  · have hxU : x ∈ 𝔇.U k := cechPoU_subordinate 𝔇 k hb
    have hr : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑(rhoC 𝔇 k)) x
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑(rhoC 𝔇 k)) x) :=
      ((rhoC 𝔇 k).contMDiff.mdifferentiable (by simp) x).hasMFDerivAt
    have hh : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (holoFn hg) x
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (holoFn hg) x) :=
      ((holoFn_contMDiffAt hg hxU).mdifferentiableAt (by simp)).hasMFDerivAt
    show proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑(primFn 𝔇 k hg)) x)
      = holoFn hg x • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑(rhoC 𝔇 k)) x)
    rw [show (⇑(primFn 𝔇 k hg) : X → ℂ) = ⇑(rhoC 𝔇 k) * holoFn hg from rfl, (hr.mul hh).mfderiv,
      map_add, proj01_smul, proj01_smul, holoFn_dbar_eq_zero hg hxU]
    module
  · have hr0 : (dbarL (primFn 𝔇 k hg)) x = 0 := by
      refine dbarL_eq_zero_of_notMem_tsupport (primFn 𝔇 k hg) (fun hc => hb ?_)
      refine closure_mono (fun y hy => ?_) hc
      simp only [Function.mem_support, ne_eq, primFn_apply, mul_eq_zero, not_or] at hy
      simp only [Function.mem_support, ne_eq]
      exact fun h0 => hy.1 (by simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM, h0]; rfl)
    rw [hr0, dbarRho_eq_zero_of_notMem 𝔇 k hb]
    module

/-- Each double-sum term `T_jk` is a `(0,1)`-form: its fiber value `c • (∂̄ρ_k x)` lies in the range
of `proj01` because `∂̄ρ_k x` does (`dbarL_mem_zeroOne`/idempotence) and `proj01` commutes with the
ℂ-scale (`proj01_smul`). -/
theorem cechTerm_mem_zeroOne (𝔇 : ChartDiskCover X)
    (f : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X))) (j k : 𝔇.toFiniteCover.ι) :
    cechTerm 𝔇 f j k ∈ OneFormsZeroOne X := by
  refine ⟨cechTerm 𝔇 f j k, ?_⟩
  refine ContMDiffSection.ext fun x => ?_
  show proj01 (cechTerm 𝔇 f j k x) = cechTerm 𝔇 f j k x
  show proj01 ((rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 f j k) x) • (dbarRho 𝔇 k x))
    = (rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 f j k) x) • (dbarRho 𝔇 k x)
  rw [proj01_smul]
  have hfix : proj01 ((dbarRho 𝔇 k) x) = (dbarRho 𝔇 k) x := by
    show proj01 (dbarL (rhoC 𝔇 k) x) = dbarL (rhoC 𝔇 k) x
    rw [dbarL_eq_proj01L_differential]
    show proj01 (proj01 ((differential (rhoC 𝔇 k)) x)) = proj01 ((differential (rhoC 𝔇 k)) x)
    exact proj01_idempotent _
  rw [hfix]

/-- The double-sum term is additive in the cocycle (`holoFn_add` washout on the overlap; off it both
sides vanish). -/
theorem cechTerm_add (𝔇 : ChartDiskCover X)
    (f₁ f₂ : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X))) (j k : 𝔇.toFiniteCover.ι) :
    cechTerm 𝔇 (f₁ + f₂) j k = cechTerm 𝔇 f₁ j k + cechTerm 𝔇 f₂ j k := by
  refine ContMDiffSection.ext fun x => ?_
  show (rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 (f₁ + f₂) j k) x) • (dbarRho 𝔇 k x)
    = (rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 f₁ j k) x) • (dbarRho 𝔇 k x)
    + (rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 f₂ j k) x) • (dbarRho 𝔇 k x)
  by_cases hxk : x ∈ tsupport (cechPoU 𝔇 k)
  · by_cases hxj : x ∈ tsupport (cechPoU 𝔇 j)
    · have hxV : x ∈ ((𝔇.U j ⊓ 𝔇.U k : Opens X) : Set X) :=
        ⟨cechPoU_subordinate 𝔇 j hxj, cechPoU_subordinate 𝔇 k hxk⟩
      rw [holoFn_add (cocycle_mem 𝔇 f₁ j k) (cocycle_mem 𝔇 f₂ j k) (cocycle_mem 𝔇 (f₁ + f₂) j k) hxV,
        mul_add]
      module
    · have hr : rhoC 𝔇 j x = 0 := by
        simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM, image_eq_zero_of_notMem_tsupport hxj]; rfl
      rw [hr]; module
  · rw [dbarRho_eq_zero_of_notMem 𝔇 k hxk]; module

/-- The double-sum term is `ℝ`-homogeneous in the cocycle (`holoFn_smul` washout; the `ℝ`-action on the
`ℂ`-module is `↑r`-scaling). -/
theorem cechTerm_smul (𝔇 : ChartDiskCover X) (r : ℝ)
    (f : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X))) (j k : 𝔇.toFiniteCover.ι) :
    cechTerm 𝔇 (r • f) j k = r • cechTerm 𝔇 f j k := by
  refine ContMDiffSection.ext fun x => ?_
  show (rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 (r • f) j k) x) • (dbarRho 𝔇 k x)
    = r • ((rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 f j k) x) • (dbarRho 𝔇 k x))
  by_cases hxk : x ∈ tsupport (cechPoU 𝔇 k)
  · by_cases hxj : x ∈ tsupport (cechPoU 𝔇 j)
    · have hxV : x ∈ ((𝔇.U j ⊓ 𝔇.U k : Opens X) : Set X) :=
        ⟨cechPoU_subordinate 𝔇 j hxj, cechPoU_subordinate 𝔇 k hxk⟩
      rw [holoFn_smul (↑r) (cocycle_mem 𝔇 f j k) (cocycle_mem 𝔇 (r • f) j k) hxV, smul_eq_mul,
        ← smul_assoc, Complex.real_smul]
      congr 1
      ring
    · have hr : rhoC 𝔇 j x = 0 := by
        simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM, image_eq_zero_of_notMem_tsupport hxj]; rfl
      rw [hr]; module
  · rw [dbarRho_eq_zero_of_notMem 𝔇 k hxk]; module

/-- **(Analytic sub-kernel — the Čech → Dolbeault glued-form operator.)** The `ℝ`-linear map sending
a holomorphic Čech `1`-cocycle `f = {f_ij}` to the global `(0,1)`-form `ω` with `ω = ∂̄η_i` on `U_i`,
`η_i := ∑_k ρ_k·f_ik` (partition-of-unity globalization). The genuine analytic content of the inverse:
lift the germ-class cocycle to holomorphic reps, the PoU smooth globalization
(`SmoothPartitionOfUnity.IsSubordinate.contMDiff_finsum_smul`), and glue the local `∂̄η_i` (which agree
on overlaps, `cechCoboundary_telescoping`) into a global section (gluedFun-for-forms). Plan:
-/
noncomputable def cechToDolbeaultForm (𝔇 : ChartDiskCover X) :
    ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X)) →ₗ[ℝ] ↥(OneFormsZeroOne X) where
  toFun f := ∑ p : 𝔇.toFiniteCover.ι × 𝔇.toFiniteCover.ι,
    ⟨cechTerm 𝔇 f p.1 p.2, cechTerm_mem_zeroOne 𝔇 f p.1 p.2⟩
  map_add' f₁ f₂ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    exact Subtype.ext (cechTerm_add 𝔇 f₁ f₂ p.1 p.2)
  map_smul' r f := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    exact Subtype.ext (cechTerm_smul 𝔇 r f p.1 p.2)

/-- `cechToDolbeaultForm 𝔇 f` is (the section underlying) the finite sum `∑_{(j,k)} T_jk`. Isolates the
single subtype-coercion-through-a-`Finset.sum` step (the only place the transparency-option `isDefEq`
cost on `cechTerm` bodies appears), so downstream uses go through `section_finset_sum_apply` cheaply. -/
theorem cechToDolbeaultForm_val (𝔇 : ChartDiskCover X)
    (f : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X))) :
    ((cechToDolbeaultForm 𝔇 f : ↥(OneFormsZeroOne X)) : SmoothCOneForms X)
      = ∑ p : 𝔇.toFiniteCover.ι × 𝔇.toFiniteCover.ι, cechTerm 𝔇 f p.1 p.2 := by
  show ((∑ p : 𝔇.toFiniteCover.ι × 𝔇.toFiniteCover.ι,
      (⟨cechTerm 𝔇 f p.1 p.2, cechTerm_mem_zeroOne 𝔇 f p.1 p.2⟩ : ↥(OneFormsZeroOne X)) :
      ↥(OneFormsZeroOne X)) : SmoothCOneForms X) = _
  rw [AddSubmonoidClass.coe_finsetSum]

/-- Section-eval commutes with finite sums of `(0,1)`-forms (generic; applied by unification, so it
never whnfs the heavy `cechTerm` body — avoiding the transparency-option `isDefEq` blowup). -/
theorem section_finset_sum_apply {ι : Type*} (s : ι → SmoothCOneForms X) (t : Finset ι) (x : X) :
    (∑ i ∈ t, s i) x = ∑ i ∈ t, (s i) x := by
  have h1 : (⇑(∑ i ∈ t, s i)) = ∑ i ∈ t, ⇑(s i) := map_sum (ContMDiffSection.coeAddHom _ _ _ _) _ _
  rw [show ((∑ i ∈ t, s i) x) = (⇑(∑ i ∈ t, s i)) x from rfl, h1, Finset.sum_apply]

/-- The **double-sum telescoping** `∑_{j,k} ρ_j·(H_k − H_j) • D_k = ∑_k H_k • D_k` when `∑_j ρ_j = 1`
and `∑_k D_k = 0` — pure module algebra over any `ℂ`-module `M`, extracted so it elaborates without the
manifold-instance / transparency cost of the section setting. -/
theorem telescope_sum {ι : Type*} [Fintype ι] {M : Type*} [AddCommGroup M] [Module ℂ M]
    (R H : ι → ℂ) (D : ι → M) (hR : ∑ j, R j = 1) (hD : ∑ k, D k = 0) :
    (∑ p : ι × ι, (R p.1 * (H p.2 - H p.1)) • D p.2) = ∑ k, H k • D k := by
  rw [Fintype.sum_prod_type]
  simp_rw [mul_sub, sub_smul, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  have h2 : (∑ j, ∑ _k : ι, (R j * H j) • D _k) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [← Finset.smul_sum, hD, smul_zero]
  rw [h2, sub_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul, ← Finset.sum_mul, hR, one_mul]

set_option maxHeartbeats 1000000 in
/-- **(Analytic sub-kernel — well-definedness of Čech → Dolbeault.)** A Čech **coboundary** cocycle
maps to a `∂̄`-image (its glued form `ω` is `∂̄` of the global primitive that the coboundary's
holomorphic `0`-cochain supplies), hence to `0` in `H^{0,1} = A^{0,1}/im ∂̄`. This is the kernel
inclusion that makes the lift to `cechH1 = Z¹/B¹` well-defined. -/
theorem cechToDolbeaultForm_coboundary_le (𝔇 : ChartDiskCover X) :
    ((𝔇.toFiniteCover.coboundaries1 (0 : Divisor X)).submoduleOf
        (𝔇.toFiniteCover.cocycles1 (0 : Divisor X))).restrictScalars ℝ
      ≤ LinearMap.ker ((Submodule.mkQ (dbarImageInZeroOne X)) ∘ₗ cechToDolbeaultForm 𝔇) := by
  intro f hf
  simp only [Submodule.restrictScalars_mem, Submodule.submoduleOf, Submodule.mem_comap,
    Submodule.subtype_apply] at hf
  obtain ⟨s, hs, hseq⟩ := hf
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    dbarImageInZeroOne, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    LinearMap.mem_range]
  -- The global primitive `h = ∑_k ρ_k·holoFn(s_k)`; `∂̄h = ω(f)`.
  refine ⟨∑ k, primFn 𝔇 k (hs k), ?_⟩
  -- Per-(j,k) `holoFn` decomposition on the overlap (`f_jk = s_k − s_j`).
  have hHol : ∀ (j k : 𝔇.toFiniteCover.ι) {y : X}, y ∈ (𝔇.U j ⊓ 𝔇.U k : Opens X) →
      holoFn (cocycle_mem 𝔇 f j k) y = holoFn (hs k) y - holoFn (hs j) y := by
    intro j k y hyV
    have hgeq : (f : 𝔇.toFiniteCover.Cochain1) (j, k)
        = rawRestrictG inf_le_right (s k) - rawRestrictG inf_le_left (s j) := by rw [← hseq]; rfl
    rw [holoFn_congr (cocycle_mem 𝔇 f j k)
        (sub_mem (rawRestrictG_omegaDGerm inf_le_right (hs k))
          (rawRestrictG_omegaDGerm inf_le_left (hs j))) hgeq hyV,
      holoFn_sub (rawRestrictG_omegaDGerm inf_le_right (hs k))
        (rawRestrictG_omegaDGerm inf_le_left (hs j)) _ hyV,
      holoFn_restrict inf_le_right (hs k) hyV, holoFn_restrict inf_le_left (hs j) hyV]
  -- Per-(j,k) term identity, valid for all `x` (off the overlap both sides vanish).
  have hTerm : ∀ (j k : 𝔇.toFiniteCover.ι) (x : X),
      (cechTerm 𝔇 f j k) x
        = (rhoC 𝔇 j x * (holoFn (hs k) x - holoFn (hs j) x)) • (dbarRho 𝔇 k x) := by
    intro j k x
    show (rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 f j k) x) • (dbarRho 𝔇 k x)
      = (rhoC 𝔇 j x * (holoFn (hs k) x - holoFn (hs j) x)) • (dbarRho 𝔇 k x)
    by_cases hxV : x ∈ (𝔇.U j ⊓ 𝔇.U k : Opens X)
    · rw [hHol j k hxV]
    · rcases not_and_or.1 hxV with hj | hk
      · have hr : rhoC 𝔇 j x = 0 := by
          have : x ∉ tsupport (cechPoU 𝔇 j) := fun hc => hj (cechPoU_subordinate 𝔇 j hc)
          simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM, image_eq_zero_of_notMem_tsupport this]
          rfl
        rw [hr, zero_mul, zero_mul]
      · have hd : dbarRho 𝔇 k x = 0 :=
          dbarRho_eq_zero_of_notMem 𝔇 k (fun hc => hk (cechPoU_subordinate 𝔇 k hc))
        rw [hd]
        module
  -- Assemble: `∂̄(∑ primFn) = ∑ cechTerm`, pointwise via the telescoping `∑ρ=1`, `∑∂̄ρ=0`.
  rw [map_sum]
  refine ContMDiffSection.ext fun x => ?_
  have hLHS : (∑ k, dbarL (primFn 𝔇 k (hs k))) x = ∑ k, holoFn (hs k) x • (dbarRho 𝔇 k x) := by
    rw [section_finset_sum_apply]
    exact Finset.sum_congr rfl fun k _ => dbarL_primFn_apply 𝔇 k (hs k) x
  have hRHS : ((cechToDolbeaultForm 𝔇 f : ↥(OneFormsZeroOne X)) : SmoothCOneForms X) x
      = ∑ p : 𝔇.toFiniteCover.ι × 𝔇.toFiniteCover.ι,
          (rhoC 𝔇 p.1 x * (holoFn (hs p.2) x - holoFn (hs p.1) x)) • (dbarRho 𝔇 p.2 x) := by
    rw [cechToDolbeaultForm_val, section_finset_sum_apply]
    exact Finset.sum_congr rfl fun p _ => hTerm p.1 p.2 x
  rw [hLHS, hRHS]
  exact (telescope_sum (fun j => rhoC 𝔇 j x) (fun k => holoFn (hs k) x)
    (fun k => dbarRho 𝔇 k x) (sum_rhoC_apply 𝔇 x) (sum_dbarRho_apply 𝔇 x)).symm

/-- **Čech → Dolbeault.** The `ℝ`-linear inverse `H¹(X, 𝒪) → H^{0,1}(X)`. Assembled **completely** from
the analytic glued-form operator `cechToDolbeaultForm` and its well-definedness
`cechToDolbeaultForm_coboundary_le` via `Submodule.liftQ` through the Čech quotient `Z¹/B¹` (scalar
`ℂ → ℝ`). The overall **minus sign** is the boundary-map sign convention (`(δc)(i,j) = c_j − c_i` in
`cechDelta0`): without it the round-trips would be `−id`. All genuine content lives in the two named
sub-kernels above. -/
noncomputable def cech_to_dolbeault (𝔇 : ChartDiskCover X) :
    𝔇.toFiniteCover.cechH1 0 →ₗ[ℝ] DolbeaultH01 X :=
  -Submodule.liftQ (((𝔇.toFiniteCover.coboundaries1 (0 : Divisor X)).submoduleOf
      (𝔇.toFiniteCover.cocycles1 (0 : Divisor X))).restrictScalars ℝ)
    ((Submodule.mkQ (dbarImageInZeroOne X)) ∘ₗ cechToDolbeaultForm 𝔇)
    (cechToDolbeaultForm_coboundary_le 𝔇)

/-- `cech_to_dolbeault` on a cocycle representative: `−[ω]` for `ω = cechToDolbeaultForm f`. -/
theorem cech_to_dolbeault_mk (𝔇 : ChartDiskCover X)
    (f : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X))) :
    cech_to_dolbeault 𝔇 (Submodule.Quotient.mk f)
      = -(Submodule.Quotient.mk (cechToDolbeaultForm 𝔇 f)) := rfl

end Jacobians.Dolbeault
