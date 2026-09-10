/-
  The abstract Forster-14.9 reduction: Čech `H¹` is finite-dimensional once the cochain restriction
  to a shrinking is compact (Montel) and the Leray-combined map is surjective. Cochain Banach spaces
  appear here as abstract Banach spaces — NO manifold/Čech dependency — so this is the clean logical
  core of the finiteness node, built directly on the Schwartz lemma (Forster 14.8).

  The two remaining manifold-side inputs it consumes —
  `ρ` compact (Montel; from `CechFiniteness.isCompact_closure_restrict_bddHolo` + `BddHol`) and the
  Leray surjectivity (`H¹(disk,𝒪)=0`, from the proven G1 `DbarDisk`) — are all that stands between
  this and `DolbeaultLadder.finiteDimensional_cechH1`.
-/
import KirovDolbeault.Dolbeault.SchwartzFiniteness

open Jacobians.SchwartzFiniteness ContinuousLinearMap

namespace Jacobians.Dolbeault.CechFiniteness

/-- **Abstract finiteness reduction (Forster 14.9 core).** Let `δ : C0 →L Z1V` (the coboundary
`C⁰(𝔙) → Z¹(𝔙)`) and `ρ : Z1U →L Z1V` (the restriction `Z¹(𝔘) → Z¹(𝔙)`) be maps of Banach spaces
such that the combined map `(η,ξ) ↦ δη + ρξ` is surjective (the **Leray** condition — restriction is
onto on `H¹`) and `ρ` is a **compact** operator (**Montel**). Then `Z1V ⧸ range δ` (i.e. `H¹(𝔙)`) is
finite-dimensional.

Proof: with `A := δ⊕ρ` (surjective) and `K := 0⊕(−ρ)` (compact), `A + K = δ⊕0` so
`range (A+K) = range δ = B¹`; the Schwartz lemma gives `Z1V ⧸ range δ` finite-dimensional. -/
theorem finiteDimensional_h1_of_leray_compact
    {C0 Z1U Z1V : Type*}
    [NormedAddCommGroup C0] [NormedSpace ℂ C0] [CompleteSpace C0]
    [NormedAddCommGroup Z1U] [NormedSpace ℂ Z1U] [CompleteSpace Z1U]
    [NormedAddCommGroup Z1V] [NormedSpace ℂ Z1V] [CompleteSpace Z1V]
    (δ : C0 →L[ℂ] Z1V) (ρ : Z1U →L[ℂ] Z1V)
    (hsurj : Function.Surjective (fun p : C0 × Z1U => δ p.1 + ρ p.2))
    (hρ : IsCompactOperator ρ) :
    FiniteDimensional ℂ (Z1V ⧸ LinearMap.range δ.toLinearMap) := by
  set A : (C0 × Z1U) →L[ℂ] Z1V := δ.comp (fst ℂ C0 Z1U) + ρ.comp (snd ℂ C0 Z1U) with hA
  set K : (C0 × Z1U) →L[ℂ] Z1V := -(ρ.comp (snd ℂ C0 Z1U)) with hK
  have hAsurj : Function.Surjective A := hsurj
  have hKcompact : IsCompactOperator K := (hρ.comp_clm (snd ℂ C0 Z1U)).neg
  have hfd := finiteDimensional_quotient_range_add_compact A hAsurj K hKcompact
  have hAK : A + K = δ.comp (fst ℂ C0 Z1U) := by rw [hA, hK]; abel
  rw [hAK] at hfd
  have hrange : LinearMap.range (δ.comp (fst ℂ C0 Z1U)).toLinearMap
      = LinearMap.range δ.toLinearMap := by
    rw [ContinuousLinearMap.coe_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.2 (Prod.fst_surjective (β := Z1U)), Submodule.map_top]
  rwa [hrange] at hfd

/-- **Finite product of compact operators is compact.** For a finite index `ι`, the product map
`Πᵢ Kᵢ : (∀ i, E i) →L (∀ i, F i)` of compact operators `Kᵢ` is compact (it is the finite sum
`∑ᵢ single_i ∘ Kᵢ ∘ proj_i`). This makes the cochain restriction `C^q(𝔘) → C^q(𝔙)` (componentwise
over the finite pair-index of the cover) a compact operator from the per-overlap
`BddHol.isCompactOperator_restrictCLM` — the bridge from STEP 1 to STEP 3's `ρ` input. -/
theorem isCompactOperator_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {E F : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
    (K : ∀ i, E i →L[ℂ] F i) (hK : ∀ i, IsCompactOperator (K i)) :
    IsCompactOperator (pi (fun i => (K i).comp (proj i)) : (∀ i, E i) →L[ℂ] (∀ i, F i)) := by
  have hsum : (pi (fun i => (K i).comp (proj i)) : (∀ i, E i) →L[ℂ] (∀ i, F i))
      = ∑ i : ι, (single ℂ F i).comp ((K i).comp (proj i)) := by
    ext x j
    simp [ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.single_apply, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.coe_sum']
  refine Finset.sum_induction _ IsCompactOperator (fun _ _ ha hb => ha.add hb)
    isCompactOperator_zero (fun i _ => ?_)
  exact ((hK i).comp_clm (proj i)).clm_comp (single ℂ F i)

/-- **A compact operator into a closed subspace is compact.** If `g : E →L p` (into a *closed*
submodule `p ≤ F`) becomes compact after including into `F` (`p.subtypeL ∘ g` compact), then `g` is
compact. Needed so the cochain restriction `ρ`, viewed as landing in the closed cocycle subspace
`Z¹(𝔙)`, is a compact operator (the `ρ` input of `finiteDimensional_h1_of_leray_compact`). -/
theorem isCompactOperator_of_subtypeL_comp {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {p : Submodule ℂ F} (hp : IsClosed (p : Set F)) (g : E →L[ℂ] p)
    (h : IsCompactOperator (p.subtypeL.comp g)) : IsCompactOperator g := by
  rw [isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image] at h ⊢
  obtain ⟨V, hV, hcpt⟩ := h
  refine ⟨V, hV, ?_⟩
  have hind : Topology.IsInducing (Subtype.val : p → F) :=
    Topology.IsEmbedding.subtypeVal.isInducing
  have hrange : IsClosed (Set.range (Subtype.val : p → F)) := by
    rw [Subtype.range_coe_subtype]; exact hp
  have key : (⇑(p.subtypeL.comp g)) '' V = Subtype.val '' (g '' V) := by
    simp only [ContinuousLinearMap.coe_comp', Submodule.coe_subtypeL, Submodule.coe_subtype,
      Set.image_comp]
  have hcpt' : IsCompact ((Subtype.val : p → F) ⁻¹' closure (Subtype.val '' (g '' V))) := by
    rw [← key]; exact hind.isCompact_preimage hrange hcpt
  apply hcpt'.of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_closure.preimage continuous_subtype_val)
  intro y hy
  exact subset_closure ⟨y, hy, rfl⟩

end Jacobians.Dolbeault.CechFiniteness
