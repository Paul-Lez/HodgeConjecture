/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Topology.IsLocalHomeomorph

/-!
# A level set projects to the remaining coordinates by a local homeomorphism

Let `f : (ι → 𝕜) → 𝕜` be strictly differentiable at a point of the level set `{z | f z = c}`,
and let `j : ι` be a coordinate at which the derivative does not vanish ; `f' (Pi.single j 1) ≠ 0`.
Forgetting the `j`-th coordinate then maps a neighbourhood of that point *inside the level set*
homeomorphically onto an open set. That is the topological half of the implicit function theorem:
the level set is locally a graph over the remaining coordinates, and here only the *local
homeomorphism* is extracted, not the graph.

`e : κ ↪ ι` is the enumeration of the remaining coordinates, asked for as an embedding whose
range is exactly the complement of `j` (`he` and `hj` below). Forgetting the `j`-th coordinate is
then `fun z ↦ z ∘ e`.

## What this is built from

`Mathlib.Analysis.Calculus.Implicit` already has the whole analytic content, in the form of
`ImplicitFunctionData`: a pair of maps whose derivatives are surjective with complementary
kernels is packaged by `ImplicitFunctionData.toOpenPartialHomeomorph` into a partial
homeomorphism `z ↦ (leftFun z, rightFun z)`. Everything below is a matter of supplying that datum
in coordinates and of reading off what it says about one fibre of the first component:

* `ImplicitFunctionData.ofCoordProj` is the datum with `leftFun = f` and
  `rightFun = fun z ↦ z ∘ e`. Its three conditions are all elementary ; `f'` is onto `𝕜` because
  `f' (Pi.single j 1) ≠ 0`, restriction of coordinates is onto because `e` is injective
  (`Function.Injective.extend_apply`), and the two kernels are complementary because
  `ker (fun z ↦ z ∘ e)` is the line spanned by `Pi.single j 1`, on which `f'` is nonzero.
* `ImplicitFunctionData.injOn_rightFun_levelSet` and
  `ImplicitFunctionData.isOpen_image_rightFun_levelSet` are the two halves of "an open embedding",
  for a general datum: on the level set through `pt`, the pair `(leftFun, rightFun)` has a
  constant first component, so `rightFun` inherits injectivity from the partial homeomorphism, and
  the image of an open set is the slice of an open set at that constant.

**No completeness or invertibility is proved here and none is assumed beyond Mathlib's own.**
`ImplicitFunctionData` asks for `CompleteSpace` on all three spaces; `ι` and `κ` are finite and
`𝕜` is complete, which is where `[CompleteSpace 𝕜]` and the two `Finite` instances go.

## Main definitions

- `ImplicitFunctionData.ofCoordProj`

## Main results

- `ImplicitFunctionData.injOn_rightFun_levelSet`
- `ImplicitFunctionData.isOpen_image_rightFun_levelSet`
- `isLocalHomeomorph_coordProj_comp_of_isEmbedding`: **forgetting the `j`-th coordinate is a local
  homeomorphism on the level set**, stated for an arbitrary topological space embedded onto that
  level set, which is the form a subspace of `ι → 𝕜` carrying extra structure needs.
- `isLocalHomeomorph_coordProj_comp_of_isEmbedding_inter`: **the same on the part of the level set
  lying in an open set**, with the two analytic hypotheses asked only there. This is the form a
  restriction of the embedded space needs. **It is a corollary of the statement above**, and its
  docstring says by what replacement ; and why that replacement is unavailable to a caller whose
  cutting function is constrained to be continuous, holomorphic, or a section of a sheaf.
- `isLocalHomeomorph_coordProj_levelSet`: the same for the level set itself, as a subtype.

## What is not here

* **No implicit function.** `ImplicitFunctionData.implicitFunction` is the map whose graph the
  level set locally is, and nothing below names it: the statements are about the *projection*
  being a local homeomorphism and say nothing about a section of it, let alone a differentiable
  one. A caller that needs the graph should use Mathlib's `implicitFunction` directly.
* **No smoothness of the local inverse**, for the same reason.
* **Nothing about the level set as a manifold or as an analytic space.** The conclusion is a
  statement about topological spaces.
* **Nothing for a piece of the level set that is not relatively open.** The `Ω` of
  `isLocalHomeomorph_coordProj_comp_of_isEmbedding_inter` is an *open* subset of `ι → 𝕜`, and its
  openness is used ; but **not** by the implicit function theorem, which never sees `Ω` at all.
  It enters at `IsOpen.mem_nhds`, as what makes the replacement function of that proof agree with
  `f` on a neighbourhood of each point of `Ω`, so that the derivative hypothesis transports with
  the same `f'`. Replacing `Ω` by an arbitrary `S` gives a false statement and not merely an
  unproved one ; for `ι` with at least two elements take `f` the `j`-th coordinate, `c = 0`, `S` a
  single point of the level set and `T` a one-point space embedded at it: both hypotheses hold on
  `S`, and the image of the map is one point of `κ → 𝕜`, which is not open. **That counterexample
  is an argument here and is compiled nowhere.**
* **No converse.** Nothing says that a level set on which the projection is a local homeomorphism
  has a nonvanishing derivative, and the hypothesis is not necessary: `f` could be constant in a
  different set of coordinates.
* **`e` is asked to enumerate the complement of `j` exactly.** With `Set.range e` smaller the
  projection forgets more than one coordinate and the conclusion is false; with `j ∈ Set.range e`
  the two kernels are not complementary. Both are hypotheses `he` and `hj` and neither is derived.
-/

@[expose] public section

open Set Filter Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ImplicitFunctionData

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section Levels

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  (φ : ImplicitFunctionData 𝕜 E F G)

/-- **On the level set of `leftFun` through `pt`, `rightFun` is injective** where the partial
homeomorphism of the implicit function theorem is defined.

Two points of the source with the same `rightFun` and the same `leftFun` have the same image
under `z ↦ (leftFun z, rightFun z)`, which is injective on its source. -/
theorem injOn_rightFun_levelSet :
    Set.InjOn φ.rightFun
      (φ.toOpenPartialHomeomorph.source ∩ {z | φ.leftFun z = φ.leftFun φ.pt}) := by
  rintro x ⟨hxs, hxl⟩ y ⟨hys, hyl⟩ hxy
  refine φ.toOpenPartialHomeomorph.injOn hxs hys ?_
  rw [φ.toOpenPartialHomeomorph_apply, φ.toOpenPartialHomeomorph_apply, hxl, hyl, hxy]

/-- **On that level set, `rightFun` takes open sets to open sets.**

The image of `s ∩ {leftFun = leftFun pt}` is the slice of the open set
`toOpenPartialHomeomorph '' s` at the first coordinate `leftFun pt`, and slicing is taking a
preimage under a continuous map. -/
theorem isOpen_image_rightFun_levelSet {s : Set E} (hs : IsOpen s)
    (hsub : s ⊆ φ.toOpenPartialHomeomorph.source) :
    IsOpen (φ.rightFun '' (s ∩ {z | φ.leftFun z = φ.leftFun φ.pt})) := by
  have himg : φ.rightFun '' (s ∩ {z | φ.leftFun z = φ.leftFun φ.pt}) =
      (fun y ↦ (φ.leftFun φ.pt, y)) ⁻¹' (φ.toOpenPartialHomeomorph '' s) := by
    ext y
    constructor
    · rintro ⟨z, ⟨hzs, hzl⟩, rfl⟩
      exact ⟨z, hzs, by rw [φ.toOpenPartialHomeomorph_apply, hzl]⟩
    · rintro ⟨z, hzs, hz⟩
      rw [φ.toOpenPartialHomeomorph_apply] at hz
      exact ⟨z, ⟨hzs, (congrArg Prod.fst hz : _)⟩, congrArg Prod.snd hz⟩
  rw [himg]
  exact (φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hs hsub).preimage (by fun_prop)

end Levels

section Coord

variable [CompleteSpace 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  {e : κ ↪ ι} {j : ι} {f : (ι → 𝕜) → 𝕜} {f' : (ι → 𝕜) →L[𝕜] 𝕜} {a : ι → 𝕜}

/-- **The implicit-function datum of `f` against the coordinates outside `j`.**

`leftFun` is `f` and `rightFun` forgets the `j`-th coordinate. The hypotheses say that `e`
enumerates exactly the coordinates other than `j` (`he`, `hj`) and that the derivative of `f` in
the `j`-th direction does not vanish (`hf'`); `Mathlib.Analysis.Calculus.Implicit` turns the datum
into a partial homeomorphism `z ↦ (f z, z ∘ e)`. -/
noncomputable def ofCoordProj (he : ∀ i, i ≠ j → i ∈ Set.range e) (hj : j ∉ Set.range e)
    (hf : HasStrictFDerivAt f f' a) (hf' : f' (Pi.single j 1) ≠ 0) :
    ImplicitFunctionData 𝕜 (ι → 𝕜) 𝕜 (κ → 𝕜) where
  leftFun := f
  leftDeriv := f'
  rightFun := fun z ↦ z ∘ e
  rightDeriv := ContinuousLinearMap.pi fun k ↦ ContinuousLinearMap.proj (e k)
  pt := a
  hasStrictFDerivAt_leftFun := hf
  hasStrictFDerivAt_rightFun :=
    (ContinuousLinearMap.pi fun k ↦ ContinuousLinearMap.proj (e k) :
      (ι → 𝕜) →L[𝕜] (κ → 𝕜)).hasStrictFDerivAt
  range_leftDeriv := by
    rw [eq_top_iff]
    intro y _
    exact ⟨(y / f' (Pi.single j 1)) • Pi.single j 1, by
      simp only [ContinuousLinearMap.coe_coe, map_smul, smul_eq_mul]
      exact div_mul_cancel₀ _ hf'⟩
  range_rightDeriv := LinearMap.range_eq_top.2 fun w ↦
    ⟨Function.extend e w 0, funext fun k ↦ e.injective.extend_apply w 0 k⟩
  isCompl_ker := by
    have hsingle : ∀ k, (Pi.single j 1 : ι → 𝕜) (e k) = 0 := by
      intro k
      have hne : e k ≠ j := fun h ↦ hj ⟨k, h⟩
      simp [hne]
    have hker : ∀ v : ι → 𝕜, (∀ k, v (e k) = 0) → v = v j • Pi.single j 1 := by
      intro v hv
      funext i
      rcases eq_or_ne i j with rfl | hij
      · simp
      · obtain ⟨k, rfl⟩ := he i hij
        simp [hv k, hij]
    constructor
    · rw [Submodule.disjoint_def]
      intro v hv1 hv2
      have hsm := hker v fun k ↦ congrFun (LinearMap.mem_ker.1 hv2) k
      have hzero : v j * f' (Pi.single j 1) = 0 := by
        have hv1' := LinearMap.mem_ker.1 hv1
        rw [hsm] at hv1'
        simpa [smul_eq_mul] using hv1'
      rcases mul_eq_zero.1 hzero with h | h
      · rw [hsm, h, zero_smul]
      · exact absurd h hf'
    · rw [codisjoint_iff, eq_top_iff]
      intro w _
      refine Submodule.mem_sup.2 ⟨w - (f' w / f' (Pi.single j 1)) • Pi.single j 1, ?_,
        (f' w / f' (Pi.single j 1)) • Pi.single j 1, ?_, by ring⟩
      · simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, map_smul, smul_eq_mul]
        rw [div_mul_cancel₀ _ hf', sub_self]
      · simp only [LinearMap.mem_ker]
        funext k
        simp [hsingle k]

@[simp]
theorem ofCoordProj_leftFun (he : ∀ i, i ≠ j → i ∈ Set.range e) (hj : j ∉ Set.range e)
    (hf : HasStrictFDerivAt f f' a) (hf' : f' (Pi.single j 1) ≠ 0) :
    (ofCoordProj he hj hf hf').leftFun = f := rfl

@[simp]
theorem ofCoordProj_rightFun (he : ∀ i, i ≠ j → i ∈ Set.range e) (hj : j ∉ Set.range e)
    (hf : HasStrictFDerivAt f f' a) (hf' : f' (Pi.single j 1) ≠ 0) :
    (ofCoordProj he hj hf hf').rightFun = fun z ↦ z ∘ e := rfl

@[simp]
theorem ofCoordProj_pt (he : ∀ i, i ≠ j → i ∈ Set.range e) (hj : j ∉ Set.range e)
    (hf : HasStrictFDerivAt f f' a) (hf' : f' (Pi.single j 1) ≠ 0) :
    (ofCoordProj he hj hf hf').pt = a := rfl

end Coord

end ImplicitFunctionData

section LevelSet

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {ι κ : Type*} [Finite ι] [DecidableEq ι] [Finite κ] {e : κ ↪ ι} {j : ι}
  {f : (ι → 𝕜) → 𝕜} {f' : (ι → 𝕜) → ((ι → 𝕜) →L[𝕜] 𝕜)} {c : 𝕜}

/-- **Forgetting the `j`-th coordinate is a local homeomorphism on a level set of `f`**, at every
point of which the derivative of `f` in the `j`-th direction is nonzero.

The level set is not taken as a subtype but presented by a topological embedding `g` of an
arbitrary space onto it, which is what a subspace carrying its own structure ; a complex analytic
space cut out by `f`, say ; supplies.

The proof is the implicit function theorem at each point and nothing else: `g x` lies in the
source of the partial homeomorphism `z ↦ (f z, z ∘ e)` of
`ImplicitFunctionData.ofCoordProj`, its `g`-preimage is the required neighbourhood, and the two
halves of `IsOpenEmbedding` on it are
`ImplicitFunctionData.injOn_rightFun_levelSet` and
`ImplicitFunctionData.isOpen_image_rightFun_levelSet`. Openness of the image needs that an open
subset of the domain is `g ⁻¹' W` for some open `W`, which is `Topology.IsInducing.isOpen_iff`. -/
theorem isLocalHomeomorph_coordProj_comp_of_isEmbedding
    {T : Type*} [TopologicalSpace T] {g : T → (ι → 𝕜)} (hg : Topology.IsEmbedding g)
    (he : ∀ i, i ≠ j → i ∈ Set.range e) (hj : j ∉ Set.range e)
    (hrange : Set.range g = {z | f z = c})
    (hf : ∀ z, f z = c → HasStrictFDerivAt f (f' z) z)
    (hne : ∀ z, f z = c → f' z (Pi.single j 1) ≠ 0) :
    IsLocalHomeomorph fun x ↦ g x ∘ e := by
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Fintype κ := Fintype.ofFinite κ
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro x
  have hmem : ∀ y : T, f (g y) = c := fun y ↦ by
    have hy : g y ∈ {z | f z = c} := hrange ▸ Set.mem_range_self y
    exact hy
  set φ := ImplicitFunctionData.ofCoordProj he hj (hf _ (hmem x)) (hne _ (hmem x)) with hφ
  have hlevel : {z | φ.leftFun z = φ.leftFun φ.pt} = {z | f z = c} := by
    ext z; simp [hφ, hmem x]
  set U : Set T := g ⁻¹' φ.toOpenPartialHomeomorph.source with hU
  have hUopen : IsOpen U := φ.toOpenPartialHomeomorph.open_source.preimage hg.continuous
  have hxU : x ∈ U := φ.pt_mem_toOpenPartialHomeomorph_source
  have hsub : ∀ y ∈ U, g y ∈ φ.toOpenPartialHomeomorph.source ∩
      {z | φ.leftFun z = φ.leftFun φ.pt} := fun y hy ↦ ⟨hy, by rw [hlevel]; exact hmem y⟩
  refine ⟨U, hUopen.mem_nhds hxU, ?_⟩
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    ((continuous_pi fun k ↦ (continuous_apply (e k)).comp hg.continuous).comp
      continuous_subtype_val) ?_ ?_
  · intro y y' hyy'
    exact Subtype.ext (hg.injective
      (φ.injOn_rightFun_levelSet (hsub y y.2) (hsub y' y'.2) hyy'))
  · intro W hW
    obtain ⟨W', hW'open, rfl⟩ := isOpen_induced_iff.1 hW
    have himg : U.domRestrict (fun t ↦ g t ∘ e) '' (Subtype.val ⁻¹' W') =
        (fun t ↦ g t ∘ e) '' (U ∩ W') := by
      rw [Set.domRestrict_eq, Set.image_comp, Subtype.image_preimage_coe]
    rw [himg]
    obtain ⟨W₀, hW₀open, hW₀⟩ := hg.isInducing.isOpen_iff.1 (hUopen.inter hW'open)
    have hgV : g '' (U ∩ W') = W₀ ∩ Set.range g := by
      rw [← hW₀, Set.image_preimage_eq_inter_range]
    have hgVsub : g '' (U ∩ W') ⊆ φ.toOpenPartialHomeomorph.source := by
      rintro _ ⟨y, hy, rfl⟩; exact (hsub y hy.1).1
    have hset : (W₀ ∩ φ.toOpenPartialHomeomorph.source) ∩
        {z | φ.leftFun z = φ.leftFun φ.pt} = g '' (U ∩ W') := by
      rw [hgV, hlevel, hrange]
      ext z
      constructor
      · rintro ⟨⟨hzW, _⟩, hzl⟩; exact ⟨hzW, hzl⟩
      · rintro ⟨hzW, hzl⟩
        exact ⟨⟨hzW, hgVsub (by rw [hgV, hrange]; exact ⟨hzW, hzl⟩)⟩, hzl⟩
    have himg2 : (fun t ↦ g t ∘ e) '' (U ∩ W') = φ.rightFun '' (g '' (U ∩ W')) := by
      rw [← Set.image_comp]; rfl
    rw [himg2, ← hset]
    exact φ.isOpen_image_rightFun_levelSet
      (hW₀open.inter φ.toOpenPartialHomeomorph.open_source) Set.inter_subset_right

/-- **Forgetting the `j`-th coordinate is a local homeomorphism on the part of a level set of `f`
lying in an open set**, at every point of which the derivative of `f` in the `j`-th direction is
nonzero ; the two analytic hypotheses being asked only there.

This is the form a *restriction of the source* needs: an embedding onto the whole level set
followed by the inclusion of an open subspace of `T` is an embedding onto such a piece.

**It is a corollary of the theorem above and the reason is that `f` is arbitrary.** No regularity
is asked of `f` anywhere off the level set, so the level set can be moved by moving `f`:
`{z | f z = c} ∩ Ω` is exactly the level set of `fun z ↦ if z ∈ Ω then f z else c + 1`, which
takes the value `c + 1 ≠ c` off `Ω`. Openness of `Ω` is what makes that replacement invisible to
the derivative ; the two functions agree on a neighbourhood of each point of `Ω`, so
`HasStrictFDerivAt.congr_of_eventuallyEq` transports the hypothesis with the *same* `f'` ; and it
is essential for that reason and not for a reason internal to the implicit function theorem.
The auxiliary function is discontinuous across `frontier Ω` and nothing minds: the theorem above
never looks there.

**The freedom being spent is that `f` is a bare function**, and it is worth saying so because it
is not available to every consumer of this theorem: a caller whose level set is cut out by a
function it is required to keep ; continuous, holomorphic, a section of a structure sheaf ; has
in general no replacement with level set `{z | f z = c} ∩ Ω`, and for such a caller the restricted
statement is not a corollary of the unrestricted one. -/
theorem isLocalHomeomorph_coordProj_comp_of_isEmbedding_inter
    {T : Type*} [TopologicalSpace T] {g : T → (ι → 𝕜)} {Ω : Set (ι → 𝕜)}
    (hg : Topology.IsEmbedding g) (hΩ : IsOpen Ω)
    (he : ∀ i, i ≠ j → i ∈ Set.range e) (hj : j ∉ Set.range e)
    (hrange : Set.range g = {z | f z = c} ∩ Ω)
    (hf : ∀ z ∈ Ω, f z = c → HasStrictFDerivAt f (f' z) z)
    (hne : ∀ z ∈ Ω, f z = c → f' z (Pi.single j 1) ≠ 0) :
    IsLocalHomeomorph fun x ↦ g x ∘ e := by
  classical
  have hc : c + 1 ≠ c := by simp
  set F : (ι → 𝕜) → 𝕜 := fun z ↦ if z ∈ Ω then f z else c + 1 with hF
  have hFlevel : {z | F z = c} = {z | f z = c} ∩ Ω := by
    ext z
    by_cases hz : z ∈ Ω <;> simp [hF, hz, hc]
  have hFeq : ∀ z ∈ Ω, F =ᶠ[𝓝 z] f := fun z hz ↦
    Filter.eventuallyEq_of_mem (hΩ.mem_nhds hz) fun y hy ↦ by simp [hF, hy]
  refine isLocalHomeomorph_coordProj_comp_of_isEmbedding (f := F) (f' := f') (c := c) hg he hj
    (by rw [hrange, hFlevel]) (fun z hz ↦ ?_) fun z hz ↦ ?_
  · obtain ⟨hzl, hzΩ⟩ : z ∈ {z | f z = c} ∩ Ω := hFlevel ▸ (show z ∈ {z | F z = c} from hz)
    exact (hf z hzΩ hzl).congr_of_eventuallyEq (hFeq z hzΩ).symm
  · obtain ⟨hzl, hzΩ⟩ : z ∈ {z | f z = c} ∩ Ω := hFlevel ▸ (show z ∈ {z | F z = c} from hz)
    exact hne z hzΩ hzl

/-- **The level set itself, as a subtype, is locally homeomorphic to the remaining
coordinates.** `isLocalHomeomorph_coordProj_comp_of_isEmbedding` at the inclusion of the level
set. -/
theorem isLocalHomeomorph_coordProj_levelSet
    (he : ∀ i, i ≠ j → i ∈ Set.range e) (hj : j ∉ Set.range e)
    (hf : ∀ z, f z = c → HasStrictFDerivAt f (f' z) z)
    (hne : ∀ z, f z = c → f' z (Pi.single j 1) ≠ 0) :
    IsLocalHomeomorph fun z : ↥{z : ι → 𝕜 | f z = c} ↦ (z : ι → 𝕜) ∘ e :=
  isLocalHomeomorph_coordProj_comp_of_isEmbedding Topology.IsEmbedding.subtypeVal he hj
    Subtype.range_coe hf hne

end LevelSet

end
