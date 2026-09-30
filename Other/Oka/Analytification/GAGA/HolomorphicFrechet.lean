/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.CousinCoordinate
public import Other.Oka.Analytification.GAGA.Montel
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.ContinuousMap.LocallyConvex
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# The Fréchet space of holomorphic functions

We equip `OkaRing U`, the holomorphic functions on an open `U ⊆ ℂ^ι`, with the topology of
uniform convergence on compact subsets of `U`, as the uniform structure induced from `C(U, ℂ)`
(compact convergence). With it `OkaRing U` is a **Fréchet space**: a complete, metrizable (the
uniformity is countably generated, since `U` is σ-compact and locally compact), locally convex,
Hausdorff topological vector space over `ℂ`, and even a topological ring. Completeness is
Weierstrass' theorem: the image of `OkaRing U` in `C(U, ℂ)` is closed.

## Main definitions

- `OkaRing.toContinuousMap U : OkaRing U →ₐ[ℂ] C(U, ℂ)`, a closed uniform embedding.
- `OkaRing.toUniformOnFun U`: the same map into `U →ᵤ[{K | IsCompact K}] ℂ`.
- `OkaRing.restrictCLM h : OkaRing U →L[ℂ] OkaRing V`: restriction along `h : V ≤ U`.

## Main results

- Instances: `UniformSpace`, `IsUniformAddGroup`, `IsTopologicalRing`, `ContinuousSMul ℂ`,
  `T2Space`, `(𝓤 (OkaRing U)).IsCountablyGenerated` (hence `MetrizableSpace`),
  `LocallyConvexSpace ℝ`, `CompleteSpace`; they pass to `Fin p → OkaRing U`.
- `OkaRing.tendsto_iff_tendstoLocallyUniformlyOn`: convergence is locally uniform convergence.
- `OkaRing.isClosed_range_toContinuousMap`: locally uniform limits of holomorphic functions are
  holomorphic.
- `OkaRing.continuous_evalHom_pt`: evaluation at a point is continuous.
- `OkaRing.isCompact_closure_of_forall_isCompact`: **Montel's theorem**: a set of holomorphic
  functions uniformly bounded on compact subsets of `U` is relatively compact.
- `OkaRing.isCompactOperator_restrictCLM`: for `V` with compact closure inside `U`, restriction
  `𝒪(U) → 𝒪(V)` is a compact operator.
-/

@[expose] public section

open Filter Set Topology TopologicalSpace
open scoped UniformConvergence

universe u
variable {ι : Type u} [Fintype ι] {U : Opens (ι → ℂ)}

namespace OkaRing

/-- A holomorphic function is continuous on its domain. -/
lemma continuous_toFun (f : OkaRing U) : Continuous (f.toFun U) := by
  have h := f.continuousOn_toGlobalFun
  rw [continuousOn_iff_continuous_restrict] at h
  exact h.congr fun x ↦ f.toGlobalFun_apply x.2

variable (U) in
/-- A holomorphic function on `U` as a continuous function on `U`. -/
def toContinuousMap : OkaRing U →ₐ[ℂ] C(U, ℂ) where
  toFun f := ⟨f.toFun U, f.continuous_toFun⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
lemma toContinuousMap_apply (f : OkaRing U) (x : U) : toContinuousMap U f x = f.toFun U x :=
  rfl

/-- A holomorphic function is determined by its values. -/
lemma toContinuousMap_injective : Function.Injective (toContinuousMap U) := fun _ _ h ↦
  OkaRing.ext (congrArg DFunLike.coe h)

/-- The uniform structure of compact convergence on `OkaRing U`. -/
noncomputable instance : UniformSpace (OkaRing U) := .comap (toContinuousMap U) inferInstance

/-- `OkaRing U` carries the uniform structure induced from `C(U, ℂ)`. -/
lemma isUniformEmbedding_toContinuousMap : IsUniformEmbedding (toContinuousMap U) :=
  ⟨⟨rfl⟩, toContinuousMap_injective⟩

/-- `OkaRing U` carries the topology induced from `C(U, ℂ)`. -/
lemma isEmbedding_toContinuousMap : Topology.IsEmbedding (toContinuousMap U) :=
  isUniformEmbedding_toContinuousMap.isEmbedding

/-- The inclusion into `C(U, ℂ)` is continuous. -/
lemma continuous_toContinuousMap : Continuous (toContinuousMap U) :=
  isEmbedding_toContinuousMap.continuous

variable (U) in
/-- A holomorphic function on `U` as a function with the topology of uniform convergence on
compact subsets of `U`, as an additive homomorphism. -/
noncomputable def toUniformOnFun : OkaRing U →+ (U →ᵤ[{K | IsCompact K}] ℂ) where
  toFun f := UniformOnFun.ofFun _ (f.toFun U)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The uniform structure is that of uniform convergence on compact subsets of `U`. -/
lemma isUniformInducing_toUniformOnFun : IsUniformInducing (toUniformOnFun U) :=
  ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isUniformInducing.comp
    isUniformEmbedding_toContinuousMap.isUniformInducing

instance : IsUniformAddGroup (OkaRing U) :=
  isUniformInducing_toUniformOnFun.isUniformAddGroup (toUniformOnFun U)

instance : IsTopologicalRing (OkaRing U) where
  continuous_mul := by
    haveI := U.isOpen.locallyCompactSpace
    refine isEmbedding_toContinuousMap.continuous_iff.2 ?_
    simp_rw [Function.comp_def, map_mul]
    exact (continuous_toContinuousMap.comp continuous_fst).mul
      (continuous_toContinuousMap.comp continuous_snd)

instance : ContinuousSMul ℂ (OkaRing U) := by
  refine ⟨isEmbedding_toContinuousMap.continuous_iff.2 ?_⟩
  simp_rw [Function.comp_def, map_smul]
  exact continuous_fst.smul (continuous_toContinuousMap.comp continuous_snd)

instance : T2Space (OkaRing U) := isEmbedding_toContinuousMap.t2Space

instance : (uniformity (OkaRing U)).IsCountablyGenerated := by
  haveI := U.isOpen.locallyCompactSpace
  exact Filter.comap.isCountablyGenerated _ _

instance : LocallyConvexSpace ℝ (OkaRing U) := by
  let L : OkaRing U →ₗ[ℝ] C(U, ℂ) :=
    { toFun := toContinuousMap U
      map_add' := map_add _
      map_smul' := fun r f ↦ by ext x; simp [Complex.real_smul]; rfl }
  exact LocallyConvexSpace.induced L

end OkaRing

namespace OkaRing

/-- The extension by zero restricts back to the function on `U`. -/
lemma toGlobalFun_comp_val (f : OkaRing U) : f.toGlobalFun U ∘ Subtype.val = f.toFun U :=
  funext fun x ↦ f.toGlobalFun_apply x.2

/-- Convergence in `OkaRing U` is locally uniform convergence on `U`. -/
theorem tendsto_iff_tendstoLocallyUniformlyOn {α : Type*} {l : Filter α} {f : α → OkaRing U}
    {g : OkaRing U} :
    Tendsto f l (𝓝 g) ↔
      TendstoLocallyUniformlyOn (fun a ↦ (f a).toGlobalFun U) (g.toGlobalFun U) l U := by
  haveI := U.isOpen.locallyCompactSpace
  rw [isEmbedding_toContinuousMap.tendsto_nhds_iff, Function.comp_def,
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly,
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simp only [Function.comp_def, toGlobalFun_apply _ (Subtype.prop _)]
  rfl

/-- **Weierstrass' theorem**: holomorphic functions form a closed subset of `C(U, ℂ)`. -/
lemma isClosed_range_toContinuousMap : IsClosed (range (toContinuousMap U)) := by
  haveI := U.isOpen.locallyCompactSpace
  refine isClosed_of_closure_subset fun g hg ↦ ?_
  obtain ⟨f, hf, hlim⟩ := mem_closure_iff_seq_limit.1 hg
  choose F hF using hf
  have hG : TendstoLocallyUniformlyOn (fun n ↦ (F n).toGlobalFun U)
      (Function.extend Subtype.val g 0) atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly] at hlim
    have h1 : (fun n (x : (U : Set (ι → ℂ))) ↦ (F n).toGlobalFun U x) = fun n x ↦ f n x := by
      funext n x
      rw [← hF n, toGlobalFun_apply _ x.2]
      rfl
    have h2 : Function.extend Subtype.val g 0 ∘ (Subtype.val : ↥(U : Set (ι → ℂ)) → ι → ℂ) = g :=
      funext fun x ↦ Subtype.val_injective.extend_apply (f := (Subtype.val : U → ι → ℂ)) _ _ x
    rw [h1, h2]
    exact hlim
  have hd := differentiableOn_of_tendstoLocallyUniformlyOn U.isOpen
    (fun n ↦ (F n).differentiableOn_toGlobalFun) hG
  refine ⟨ofDifferentiableOn _ hd, ContinuousMap.ext fun x ↦ ?_⟩
  simp only [toContinuousMap_apply, ofDifferentiableOn_toFun]
  exact Subtype.val_injective.extend_apply (f := (Subtype.val : U → ι → ℂ)) _ _ x

instance : CompleteSpace (OkaRing U) := by
  haveI := U.isOpen.locallyCompactSpace
  rw [completeSpace_iff_isComplete_range isUniformEmbedding_toContinuousMap.isUniformInducing]
  exact isClosed_range_toContinuousMap.isComplete

end OkaRing

namespace OkaRing

/-- Evaluation at a point is continuous for the topology of compact convergence. -/
lemma continuous_evalHom_pt {x : ι → ℂ} (hx : x ∈ U) : Continuous (evalHom (U := U) hx) :=
  (continuous_eval_const (⟨x, hx⟩ : U)).comp continuous_toContinuousMap

/-- Restriction of holomorphic functions along `V ≤ U`, as a continuous `ℂ`-linear map. -/
noncomputable def restrictCLM {V : Opens (ι → ℂ)} (h : V ≤ U) : OkaRing U →L[ℂ] OkaRing V where
  toLinearMap := (OkaRing.restrict h).toLinearMap
  cont := by
    refine isEmbedding_toContinuousMap.continuous_iff.2 ?_
    exact (ContinuousMap.continuous_precomp ⟨Opens.inclusion h, continuous_inclusion h⟩).comp
      continuous_toContinuousMap

@[simp]
lemma restrictCLM_apply {V : Opens (ι → ℂ)} (h : V ≤ U) (f : OkaRing U) :
    restrictCLM h f = OkaRing.restrict h f :=
  rfl

end OkaRing

namespace OkaRing

/-- The inclusion into `C(U, ℂ)` is a closed embedding. -/
lemma isClosedEmbedding_toContinuousMap : IsClosedEmbedding (toContinuousMap U) :=
  ⟨isEmbedding_toContinuousMap, isClosed_range_toContinuousMap⟩

/-- **Montel's theorem** for `OkaRing U`: a set of holomorphic functions which is uniformly
bounded on every compact subset of `U` is relatively compact. -/
theorem isCompact_closure_of_forall_isCompact {S : Set (OkaRing U)}
    (hS : ∀ K ⊆ (U : Set (ι → ℂ)), IsCompact K →
      ∃ C, ∀ f ∈ S, ∀ x ∈ K, ‖f.toGlobalFun U x‖ ≤ C) :
    IsCompact (closure S) := by
  have h := isCompact_closure_of_differentiableOn U.isOpen
    (fun f : S ↦ (f : OkaRing U).differentiableOn_toGlobalFun)
    (fun K hKU hK ↦ (hS K hKU hK).imp fun C hC f ↦ hC f f.2)
  have hrange : (range fun f : S ↦ (f : OkaRing U).differentiableOn_toGlobalFun.continuousOn
      |>.toContinuousMapOn) = toContinuousMap U '' S := by
    ext g
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f, f.2, ContinuousMap.ext fun x ↦ (toGlobalFun_apply _ x.2).symm⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, ContinuousMap.ext fun x ↦ toGlobalFun_apply _ x.2⟩
  rw [hrange, isClosedEmbedding_toContinuousMap.closure_image_eq] at h
  simpa [Set.preimage_image_eq _ toContinuousMap_injective] using
    isClosedEmbedding_toContinuousMap.isCompact_preimage h

/-- **Montel's theorem**, compact operator form: if `V` has compact closure contained in `U`,
restriction `𝒪(U) → 𝒪(V)` is a compact operator. -/
theorem isCompactOperator_restrictCLM {V : Opens (ι → ℂ)}
    (hV : IsCompact (closure (V : Set (ι → ℂ)))) (hVU : closure (V : Set (ι → ℂ)) ⊆ U) :
    IsCompactOperator (restrictCLM (U := U) (V := V) (fun _ hx ↦ hVU (subset_closure hx))) := by
  set K : Set U := Subtype.val ⁻¹' closure (V : Set (ι → ℂ))
  have hK : IsCompact K := by
    have : Subtype.val '' K = closure (V : Set (ι → ℂ)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · exact fun hx ↦ ⟨⟨x, hVU hx⟩, hx, rfl⟩
    rw [Subtype.isCompact_iff, this]
    exact hV
  set N : Set (OkaRing U) := toContinuousMap U ⁻¹' {g | MapsTo g K (Metric.ball 0 1)}
  have hN : N ∈ 𝓝 0 := by
    refine continuous_toContinuousMap.continuousAt.preimage_mem_nhds
      ((ContinuousMap.isOpen_setOf_mapsTo hK Metric.isOpen_ball).mem_nhds ?_)
    intro x _
    simp
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  refine ⟨N, hN, _, isCompact_closure_of_forall_isCompact fun L hL _ ↦ ⟨1, ?_⟩, subset_closure⟩
  rintro _ ⟨f, hf, rfl⟩ x hx
  have hxU : x ∈ U := hVU (subset_closure (hL hx))
  have := hf (show (⟨x, hxU⟩ : U) ∈ K from subset_closure (hL hx))
  rw [toGlobalFun_apply _ (hL hx)]
  rw [mem_ball_zero_iff] at this
  exact this.le

end OkaRing

end
