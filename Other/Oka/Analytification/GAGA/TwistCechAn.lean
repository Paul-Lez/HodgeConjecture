/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.Modules.CocycleTwistPullback
public import Other.Oka.Analytification.GAGA.TwistTransition
public import Other.Oka.Analytification.GAGA.CechProjectiveAn
public import Other.Oka.Analytification.GAGA.SheafAnalytification
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.Cohomology
public import Other.Oka.Topology.Sheaves.Cohomology.Leray
public import Other.Oka.Analytification.GAGA.TheoremB

@[expose] public section


/-!
# The Čech complex of `𝒪(k)^an` on `ℙⁿ_an` and its cohomology

Let `𝒪(k)^an` be the analytification of the twisting sheaf `𝒪(k)` on `ℙⁿ_ℂ`
(`ComplexAnalytic.projectiveSpaceAn.twistingSheafAn n k`). By
`Other/Oka/AlgebraicGeometry/Modules/CocycleTwistPullback.lean`, it is the twist `twistAn k` of
`𝒪_{ℙⁿ_an}` by the pulled back transition functions: sections over `W` are families
`tᵢ ∈ Γ(W ∩ π⁻¹ Uᵢ, 𝒪)` with `tᵢ = π^♯(Xⱼ / Xᵢ)ᵏ · tⱼ` (`twistingSheafAnIso`). Since
`π^♯(Xⱼ / Xᵢ)` has value `vⱼ / vᵢ` at `[v]` (`evπ_cocycle_zpow`), such a family is the same as the
function `F(v) = vᵢᵏ tᵢ([v])` on the cone over `W` (`twFun`, independent of `i`), holomorphic and
homogeneous of degree `k`, and every such function arises (`exists_twFun_eq`). For the
intersections `U_σ` of the standard cover `π⁻¹ Uᵢ` the cone is `V (im σ)`, so the sections are the
space `CechProjectiveAn.hol k (im σ)` (`cechSectionsEquivAn`), compatibly with restriction, and the
Čech complex of `𝒪(k)^an` is the analytic Čech complex `CechProjectiveAn.holD`
(`cechCochainEquivAn`, `cechCochainEquivAn_cechD`).

On each chart `𝒪(k)^an` is trivial (`restrictOpenTwistingSheafAnIso`), so by Theorem B for `𝒪` it
has no higher cohomology on the `U_σ` (`subsingleton_H_restrictOpen_cechOpen`). With the
exactness of `holD` and Leray's theorem:

## Main results

- `ComplexAnalytic.projectiveSpaceAn.H_twistingSheafAn_eq_zero`: `Hᵠ(ℙⁿ_an, 𝒪(k)^an) = 0` for
  `q ≥ 1` and `k ≥ -n`.
- `ComplexAnalytic.projectiveSpaceAn.hZeroTwistingSheafAnEquiv`:
  `H⁰(ℙⁿ_an, 𝒪(e)^an) ≃ ℂ[X₀, …, Xₙ]_e` for `e ≥ 0`.
- `ComplexAnalytic.projectiveSpaceAn.H_zero_twistingSheafAn_eq_zero`: `H⁰(ℙⁿ_an, 𝒪(k)^an) = 0` for
  `k < 0`, `n ≥ 1`.
- `ComplexAnalytic.projectiveSpaceAn.exactAt_cechComplex_twistingSheafAn`: exactness of the Čech
  complex in degree `q = p + 1` if `q > n`, `q < n` or `k > -n - 1`.
-/

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Topology
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.LocallyRingedSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic.projectiveSpaceAn

open AnalyticSpace ProjectiveSpace

variable {n : ℕ}

/-- The comparison morphism `ℙⁿ_an ⟶ ℙⁿ`, as a morphism of locally ringed spaces. -/
noncomputable abbrev πL : (projectiveSpaceAn.{u} n).toLocallyRingedSpace ⟶
    ℙₒ(n; ULift.{u} ℂ).toLocallyRingedSpace :=
  analytificationπLRS (projectiveSpace.{u} n)

/-- **`𝒪(k)^an` in explicit form**: sections over `W` are families `tᵢ ∈ Γ(W ∩ π⁻¹ Uᵢ, 𝒪)` with
`tᵢ = π^♯ (Xⱼ / Xᵢ)ᵏ · tⱼ`. -/
noncomputable abbrev twistAn (k : ℤ) : SheafOfModules.{u} (projectiveSpaceAn.{u} n).ringSheaf :=
  pbTwist πL.{u} (cocycle n (ULift.{u} ℂ) ^ k)

lemma pointOfVec_mem_preimOpen_iff (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) (i : Fin (n + 1)) :
    pointOfVec.{u} v hv ∈ preimOpen πL.{u} (U n (ULift.{u} ℂ) i) ↔ v i ≠ 0 := by
  rw [← mem_range_chart_pointOfVec_iff v hv i, range_chart]
  rfl

lemma mem_vecCone_inf_iff {W : (projectiveSpaceAn.{u} n).Opens} (v : Fin (n + 1) → ℂ)
    (i : Fin (n + 1)) :
    v ∈ vecCone.{u} (W ⊓ preimOpen πL.{u} (U n (ULift.{u} ℂ) i)) ↔ v ∈ vecCone.{u} W ∧ v i ≠ 0 := by
  constructor
  · rintro ⟨hv, h1, h2⟩
    exact ⟨⟨hv, h1⟩, (pointOfVec_mem_preimOpen_iff v hv i).1 h2⟩
  · rintro ⟨⟨hv, h1⟩, h2⟩
    exact ⟨hv, h1, (pointOfVec_mem_preimOpen_iff v hv i).2 h2⟩

/-- The value at `[v]` of the pulled-back transition function `(Xⱼ / Xᵢ)ᵏ` is `(vⱼ / vᵢ)ᵏ`. -/
lemma secFun_pbG (k : ℤ) (i j : Fin (n + 1)) {v : Fin (n + 1) → ℂ}
    (hv : v ∈ vecCone.{u} (preimOpen πL.{u} (U n (ULift.{u} ℂ) i) ⊓
      preimOpen πL.{u} (U n (ULift.{u} ℂ) j))) :
    secFun (pbG πL.{u} (cocycle n (ULift.{u} ℂ) ^ k) i j) v = (v j / v i) ^ k := by
  rw [secFun_of_mem _ hv.1 hv.2]
  have hi : v i ≠ 0 := (pointOfVec_mem_preimOpen_iff v hv.1 i).1 hv.2.1
  exact evπ_cocycle_zpow k v hv.1 i j hi hv.2


variable {k : ℤ} {W : (projectiveSpaceAn.{u} n).Opens}

/-- The chart index used to evaluate a section of `𝒪(k)^an` at `v`. -/
noncomputable def coneIdx {v : Fin (n + 1) → ℂ} (h : v ∈ vecCone.{u} W) : Fin (n + 1) :=
  (Function.ne_iff.1 h.1).choose

lemma coneIdx_spec {v : Fin (n + 1) → ℂ} (h : v ∈ vecCone.{u} W) : v (coneIdx h) ≠ 0 :=
  (Function.ne_iff.1 h.1).choose_spec

open scoped Classical in
/-- **A section of `𝒪(k)^an` over `W` as a function on `ℂⁿ⁺¹`**: `v ↦ vᵢᵏ tᵢ([v])` for any `i`
with `vᵢ ≠ 0` (on the cone over `W`; zero off it). -/
noncomputable def twFun (t : (twistAn.{u} (n := n) k).val.obj (op W)) (v : Fin (n + 1) → ℂ) : ℂ :=
  if h : v ∈ vecCone.{u} W then v (coneIdx h) ^ k * secFun (pbComp t (coneIdx h)) v else 0

/-- The value `vᵢᵏ tᵢ([v])` does not depend on the chart `i`. -/
lemma zpow_mul_secFun_pbComp (t : (twistAn.{u} (n := n) k).val.obj (op W))
    {v : Fin (n + 1) → ℂ} (hv : v ∈ vecCone.{u} W) {a b : Fin (n + 1)} (ha : v a ≠ 0)
    (hb : v b ≠ 0) :
    v a ^ k * secFun (pbComp t a) v = v b ^ k * secFun (pbComp t b) v := by
  have hvO : v ∈ vecCone.{u}
      (W ⊓ (preimOpen πL.{u} (U n (ULift.{u} ℂ) a) ⊓ preimOpen πL.{u} (U n (ULift.{u} ℂ) b))) :=
    ⟨hv.1, hv.2, (pointOfVec_mem_preimOpen_iff v hv.1 a).2 ha,
      (pointOfVec_mem_preimOpen_iff v hv.1 b).2 hb⟩
  have hc := congrArg (secFun · v) (pbComp_compat t a b)
  simp only [secFun_mul, secFun_restrictOpen] at hc
  rw [Set.indicator_of_mem hvO, Set.indicator_of_mem hvO, Set.indicator_of_mem hvO] at hc
  rw [hc, secFun_pbG k a b ⟨hv.1, hvO.2.2⟩, ← mul_assoc, div_zpow,
    mul_div_cancel₀ _ (zpow_ne_zero _ ha)]

lemma twFun_eq (t : (twistAn.{u} (n := n) k).val.obj (op W)) {v : Fin (n + 1) → ℂ}
    (hv : v ∈ vecCone.{u} W) (i : Fin (n + 1)) (hi : v i ≠ 0) :
    twFun t v = v i ^ k * secFun (pbComp t i) v := by
  classical
  rw [twFun, dif_pos hv]
  exact zpow_mul_secFun_pbComp t hv (coneIdx_spec hv) hi

lemma twFun_of_notMem (t : (twistAn.{u} (n := n) k).val.obj (op W)) {v : Fin (n + 1) → ℂ}
    (hv : v ∉ vecCone.{u} W) : twFun t v = 0 := by
  classical
  rw [twFun, dif_neg hv]

lemma twFun_add (t t' : (twistAn.{u} (n := n) k).val.obj (op W)) :
    twFun (t + t') = twFun t + twFun t' := by
  funext v
  by_cases hv : v ∈ vecCone.{u} W
  · have hi := coneIdx_spec hv
    rw [Pi.add_apply, twFun_eq _ hv _ hi, twFun_eq _ hv _ hi, twFun_eq _ hv _ hi, pbComp_add,
      secFun_add, mul_add]
  · rw [Pi.add_apply, twFun_of_notMem _ hv, twFun_of_notMem _ hv, twFun_of_notMem _ hv, add_zero]

lemma twFun_zero : twFun (0 : (twistAn.{u} (n := n) k).val.obj (op W)) = 0 := by
  funext v
  by_cases hv : v ∈ vecCone.{u} W
  · rw [twFun_eq _ hv _ (coneIdx_spec hv), pbComp_zero, secFun_zero, mul_zero, Pi.zero_apply]
  · rw [twFun_of_notMem _ hv, Pi.zero_apply]

lemma twFun_modRes (t : (twistAn.{u} (n := n) k).val.obj (op W))
    {W' : (projectiveSpaceAn.{u} n).Opens} (h : W' ≤ W) :
    twFun (modRes t W' h) = (vecCone.{u} W').indicator (twFun t) := by
  funext v
  by_cases hv : v ∈ vecCone.{u} W'
  · have hi := coneIdx_spec hv
    rw [Set.indicator_of_mem hv, twFun_eq _ hv _ hi, twFun_eq _ (vecCone_mono h hv) _ hi,
      pbComp_modRes, secFun_restrictOpen,
      Set.indicator_of_mem ((mem_vecCone_inf_iff v _).2 ⟨hv, hi⟩)]
  · rw [Set.indicator_of_notMem hv, twFun_of_notMem _ hv]

lemma twFun_smul (t : (twistAn.{u} (n := n) k).val.obj (op W)) {v : Fin (n + 1) → ℂ}
    (hv : v ∈ vecCone.{u} W) {c : ℂ} (hc : c ≠ 0) : twFun t (c • v) = c ^ k * twFun t v := by
  have hi := coneIdx_spec hv
  have hci : (c • v) (coneIdx hv) ≠ 0 := by simpa using And.intro hc hi
  rw [twFun_eq _ (smul_mem_vecCone hv hc) _ hci, twFun_eq _ hv _ hi, secFun_smul _ _ hc,
    Pi.smul_apply, smul_eq_mul, mul_zpow, mul_assoc]

lemma differentiableOn_twFun (t : (twistAn.{u} (n := n) k).val.obj (op W)) :
    DifferentiableOn ℂ (twFun t) (vecCone.{u} W) := by
  intro v hv
  have hi := coneIdx_spec hv
  set i := coneIdx hv
  refine DifferentiableAt.differentiableWithinAt ?_
  have hvi : v ∈ vecCone.{u} (W ⊓ preimOpen πL.{u} (U n (ULift.{u} ℂ) i)) :=
    (mem_vecCone_inf_iff v i).2 ⟨hv, hi⟩
  have hN := isOpen_vecCone.mem_nhds hvi
  have heq : (fun w ↦ w i ^ k * secFun (pbComp t i) w) =ᶠ[𝓝 v] twFun t := by
    filter_upwards [hN] with w hw
    have hw' := (mem_vecCone_inf_iff w i).1 hw
    exact (twFun_eq t hw'.1 i hw'.2).symm
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
  exact ((differentiableAt_apply (𝕜 := ℂ) i v).zpow (Or.inl hi)).mul
    ((differentiableOn_secFun _ v hvi).differentiableAt hN)


lemma eq_zero_of_twFun (t : (twistAn.{u} (n := n) k).val.obj (op W)) (h : twFun t = 0) :
    t = 0 := by
  refine pbTwist_ext fun i ↦ ?_
  refine eq_zero_of_secFun _ fun v hv ↦ ?_
  have hv' := (mem_vecCone_inf_iff v i).1 hv
  have := congrFun h v
  rw [twFun_eq t hv'.1 i hv'.2, Pi.zero_apply] at this
  exact (mul_eq_zero.1 this).resolve_left (zpow_ne_zero _ hv'.2)

lemma twFun_injective : Function.Injective (twFun (k := k) (W := W) (n := n)) := by
  intro t t' h
  rw [← sub_eq_zero]
  refine eq_zero_of_twFun _ ?_
  have := twFun_add (t - t') t'
  rw [sub_add_cancel, h] at this
  simpa using this.symm

lemma preimOpen_le_range (i : Fin (n + 1)) :
    ∀ y ∈ W ⊓ preimOpen πL.{u} (U n (ULift.{u} ℂ) i), y ∈ Set.range (chartLRS.{u} i).base :=
  fun y hy ↦ by rw [range_chart]; exact hy.2

/-- **Every holomorphic function on the cone over `W`, homogeneous of degree `k`, comes from a
section of `𝒪(k)^an`.** -/
lemma exists_twFun_eq (F : (Fin (n + 1) → ℂ) → ℂ) (hF : DifferentiableOn ℂ F (vecCone.{u} W))
    (hhom : ∀ v ∈ vecCone.{u} W, ∀ c : ℂ, c ≠ 0 → F (c • v) = c ^ k * F v)
    (h0 : ∀ v ∉ vecCone.{u} W, F v = 0) :
    ∃ t : (twistAn.{u} (n := n) k).val.obj (op W), twFun t = F := by
  have hs (i : Fin (n + 1)) := exists_secFun_eq (W := W ⊓ preimOpen πL.{u} (U n (ULift.{u} ℂ) i))
    i (preimOpen_le_range i) (fun v ↦ F v / v i ^ k)
    (fun v hv ↦ by
      have hv' := (mem_vecCone_inf_iff v i).1 hv
      have h1 : DifferentiableWithinAt ℂ (fun w ↦ F w * (w i ^ k)⁻¹)
          (vecCone.{u} (W ⊓ preimOpen πL.{u} (U n (ULift.{u} ℂ) i))) v :=
        ((hF v hv'.1).mono fun w hw ↦ ((mem_vecCone_inf_iff w i).1 hw).1).mul
          (((differentiableAt_apply (𝕜 := ℂ) i v).zpow (Or.inl hv'.2)).inv
            (zpow_ne_zero _ hv'.2)).differentiableWithinAt
      simpa only [div_eq_mul_inv] using h1)
    (fun v hv c hc ↦ by
      have hv' := (mem_vecCone_inf_iff v i).1 hv
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hhom v hv'.1 c hc, mul_zpow, mul_div_mul_left _ _ (zpow_ne_zero _ hc)])
  choose s hs using hs
  refine ⟨pbMk s fun a b ↦ eq_of_secFun fun v hv ↦ ?_, ?_⟩
  · have hva : v ∈ vecCone.{u} (W ⊓ preimOpen πL.{u} (U n (ULift.{u} ℂ) a)) :=
      vecCone_mono (by order) hv
    have hvb : v ∈ vecCone.{u} (W ⊓ preimOpen πL.{u} (U n (ULift.{u} ℂ) b)) :=
      vecCone_mono (by order) hv
    have ha := ((mem_vecCone_inf_iff v a).1 hva).2
    have hb := ((mem_vecCone_inf_iff v b).1 hvb).2
    rw [secFun_mul, secFun_restrictOpen, secFun_restrictOpen, secFun_restrictOpen,
      Set.indicator_of_mem hv, Set.indicator_of_mem hv, Set.indicator_of_mem hv, hs a v hva,
      hs b v hvb, secFun_pbG k a b (vecCone_mono (by order) hv), div_zpow]
    field_simp
  · funext v
    by_cases hv : v ∈ vecCone.{u} W
    · have hi := coneIdx_spec hv
      rw [twFun_eq _ hv _ hi, pbComp_pbMk, hs _ v ((mem_vecCone_inf_iff v _).2 ⟨hv, hi⟩),
        mul_div_cancel₀ _ (zpow_ne_zero _ hi)]
    · rw [twFun_of_notMem _ hv, h0 v hv]


open CechProjectiveAn in
/-- `twFun` as an additive map to `CechProjectiveAn.hol k I`, when the cone over `W` is `V I`. -/
noncomputable def twHolHom (I : Finset (Fin (n + 1))) (hWI : vecCone.{u} W = V I) :
    (twistAn.{u} (n := n) k).val.obj (op W) →+ hol k I where
  toFun t := ⟨twFun t, hWI ▸ differentiableOn_twFun t,
    fun _ hz _ hc ↦ twFun_smul t (hWI ▸ hz) hc, fun _ hz ↦ twFun_of_notMem t (hWI ▸ hz)⟩
  map_zero' := Subtype.ext twFun_zero
  map_add' t t' := Subtype.ext (twFun_add t t')

open CechProjectiveAn in
/-- **Sections of `𝒪(k)^an` over an open with cone `V I` are the holomorphic functions on `V I`,
homogeneous of degree `k`**: `twFun` as an additive equivalence onto `CechProjectiveAn.hol k I`. -/
noncomputable def twHolEquiv (I : Finset (Fin (n + 1))) (hWI : vecCone.{u} W = V I) :
    (twistAn.{u} (n := n) k).val.obj (op W) ≃+ hol k I :=
  AddEquiv.ofBijective (twHolHom I hWI)
    ⟨fun t t' h ↦ twFun_injective (congrArg Subtype.val h), fun F ↦ by
      obtain ⟨t, ht⟩ := exists_twFun_eq (W := W) (k := k) F.1 (hWI ▸ F.2.1)
        (fun v hv c hc ↦ F.2.2.1 v (hWI ▸ hv) c hc) (fun v hv ↦ F.2.2.2 v (hWI ▸ hv))
      exact ⟨t, Subtype.ext ht⟩⟩

open CechProjectiveAn in
lemma coe_twHolEquiv (I : Finset (Fin (n + 1))) (hWI : vecCone.{u} W = V I)
    (t : (twistAn.{u} (n := n) k).val.obj (op W)) :
    ((twHolEquiv I hWI t : hol k I) : (Fin (n + 1) → ℂ) → ℂ) = twFun t :=
  rfl

open CechProjectiveAn in
/-- `twHolEquiv` is compatible with restriction (`holRes`). -/
lemma twHolEquiv_modRes {I J : Finset (Fin (n + 1))} (hJI : J ⊆ I) (hWI : vecCone.{u} W = V J)
    {W' : (projectiveSpaceAn.{u} n).Opens} (h : W' ≤ W) (hW'I : vecCone.{u} W' = V I)
    (t : (twistAn.{u} (n := n) k).val.obj (op W)) :
    twHolEquiv I hW'I (modRes t W' h) = holRes k hJI (twHolEquiv J hWI t) := by
  apply Subtype.ext
  rw [coe_twHolEquiv, coe_holRes, coe_twHolEquiv, twFun_modRes, hW'I]


/-! ### The Čech complex of `𝒪(k)^an` for the standard cover -/

/-- The standard cover `π⁻¹ Uᵢ` of `ℙⁿ_an`, indexed by `ULift (Fin (n + 1))`. -/
noncomputable def stdCoverAn : ULift.{u} (Fin (n + 1)) →
    Opens (projectiveSpaceAn.{u} n).toPresheafedSpace :=
  fun i ↦ preimOpen πL.{u} (U n (ULift.{u} ℂ) i.down)

lemma iSup_stdCoverAn : ⨆ i, stdCoverAn.{u} (n := n) i = ⊤ := by
  refine eq_top_iff.2 fun y _ ↦ ?_
  have : πL.{u}.base y ∈ (⨆ i, U n (ULift.{u} ℂ) i : ℙₒ(n; ULift.{u} ℂ).Opens) := by
    rw [iSup_U]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 this
  exact Opens.mem_iSup.2 ⟨⟨i⟩, hi⟩

open CechProjectiveAn SimplexCochain in
/-- The cone over the intersection `U_σ` of the standard cover is `V (im σ)`. -/
lemma vecCone_cechOpen {p : ℕ} (σ : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    vecCone.{u} (TopCat.Presheaf.cechOpen stdCoverAn σ) = V (im fun a ↦ (σ a).down) := by
  ext v
  have key : ∀ hv : v ≠ 0, pointOfVec.{u} v hv ∈ TopCat.Presheaf.cechOpen stdCoverAn σ ↔
      ∀ a, v (σ a).down ≠ 0 := fun hv ↦ by
    rw [TopCat.Presheaf.cechOpen, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
    exact forall_congr' fun a ↦ pointOfVec_mem_preimOpen_iff v hv _
  simp only [V, Set.mem_setOf_eq, Finset.mem_image, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]
  refine ⟨fun ⟨hv, h⟩ ↦ (key hv).1 h, fun h ↦ ?_⟩
  have hv : v ≠ 0 := fun h0 ↦ h 0 (by simp [h0])
  exact ⟨hv, (key hv).2 h⟩

variable (n) in
/-- **The analytification `𝒪(k)^an` of the twisting sheaf `𝒪(k)` on `ℙⁿ`.** -/
noncomputable abbrev twistingSheafAn (k : ℤ) :
    SheafOfModules.{u} (projectiveSpaceAn.{u} n).ringSheaf :=
  (analytificationModules (projectiveSpace.{u} n)).obj
    (ProjectiveSpace.twistingSheaf n (ULift.{u} ℂ) k)

variable (n) in
/-- `𝒪(k)^an ≅ twistAn k`: the analytification of `𝒪(k)` is the twist of `𝒪_{ℙⁿ_an}` by the
pulled back transition functions `(Xⱼ / Xᵢ)ᵏ`. -/
noncomputable def twistingSheafAnIso (k : ℤ) : twistingSheafAn.{u} n k ≅ twistAn.{u} (n := n) k :=
  pullbackTwistUnitIso πL.{u} (cocycle n (ULift.{u} ℂ) ^ k) (iSup_U n _)


/-- An isomorphism of sheaves of modules, on sections. -/
noncomputable def isoSectionsEquiv {P Q : SheafOfModules.{u} (projectiveSpaceAn.{u} n).ringSheaf}
    (e : P ≅ Q) (W : (projectiveSpaceAn.{u} n).Opens) : P.val.obj (op W) ≃+ Q.val.obj (op W) where
  toFun x := e.hom.val.app (op W) x
  invFun y := e.inv.val.app (op W) y
  left_inv x := congr($(congrArg (fun φ : P ⟶ P ↦ φ.val.app (op W)) e.hom_inv_id).hom x)
  right_inv y := congr($(congrArg (fun φ : Q ⟶ Q ↦ φ.val.app (op W)) e.inv_hom_id).hom y)
  map_add' x y := map_add _ x y

open CechProjectiveAn SimplexCochain in
/-- Sections of `𝒪(k)^an` over the intersection `U_σ` of the standard cover, as holomorphic
functions on `V (im σ)` homogeneous of degree `k`. -/
noncomputable def cechSectionsEquivAn (k : ℤ) {p : ℕ} (σ : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    (twistingSheafAn.{u} n k).toAb.obj.obj (op (TopCat.Presheaf.cechOpen stdCoverAn σ)) ≃+
      hol k (im fun a ↦ (σ a).down) :=
  (isoSectionsEquiv (twistingSheafAnIso n k) _).trans (twHolEquiv _ (vecCone_cechOpen σ))

open CechProjectiveAn SimplexCochain in
lemma cechSectionsEquivAn_res (k : ℤ) {m p : ℕ} (τ : Fin (p + 1) → ULift.{u} (Fin (n + 1)))
    (θ : Fin (m + 1) → Fin (p + 1))
    (s : (twistingSheafAn.{u} n k).toAb.obj.obj
      (op (TopCat.Presheaf.cechOpen stdCoverAn (τ ∘ θ)))) :
    cechSectionsEquivAn k τ ((twistingSheafAn.{u} n k).toAb.obj.map
      (homOfLE (TopCat.Presheaf.cechOpen_le_comp _ τ θ)).op s) =
      holRes k (im_comp_subset (fun a ↦ (τ a).down) θ) (cechSectionsEquivAn k (τ ∘ θ) s) := by
  change twHolEquiv _ (vecCone_cechOpen τ) ((twistingSheafAnIso n k).hom.val.app _
    (modRes s _ (TopCat.Presheaf.cechOpen_le_comp _ τ θ))) = _
  rw [modHom_modRes]
  exact twHolEquiv_modRes _ (vecCone_cechOpen (τ ∘ θ)) _ _ _


open CechProjectiveAn SimplexCochain in
/-- **The Čech cochains of `𝒪(k)^an`** for the standard cover are the cochains of the analytic
Čech complex `CechProjectiveAn.holD`. -/
noncomputable def cechCochainEquivAn (k : ℤ) (p : ℕ) :
    TopCat.Presheaf.CechCochain stdCoverAn (twistingSheafAn.{u} n k).toAb.obj p ≃+
      HolCochain k n p where
  toFun c i := cechSectionsEquivAn k (fun a ↦ ULift.up (i a)) (c _)
  invFun y σ := (cechSectionsEquivAn k σ).symm (y fun a ↦ (σ a).down)
  left_inv c := funext fun σ ↦ (cechSectionsEquivAn k σ).symm_apply_apply (c σ)
  right_inv _ := funext fun i ↦
    (cechSectionsEquivAn k (fun a ↦ ULift.up (i a))).apply_symm_apply _
  map_add' _ _ := funext fun i ↦ map_add (cechSectionsEquivAn k (fun a ↦ ULift.up (i a))) _ _

open CechProjectiveAn SimplexCochain in
/-- **The Čech differential of `𝒪(k)^an` is `holD`** under `cechCochainEquivAn`. -/
lemma cechCochainEquivAn_cechD (k : ℤ) (p : ℕ)
    (c : TopCat.Presheaf.CechCochain stdCoverAn (twistingSheafAn.{u} n k).toAb.obj p) :
    cechCochainEquivAn k (p + 1) (TopCat.Presheaf.cechD _ _ p c) =
      holD k p (cechCochainEquivAn k p c) := by
  funext i
  apply Subtype.ext
  change ((cechSectionsEquivAn k (fun a ↦ ULift.up (i a)) (TopCat.Presheaf.cechD _ _ p c _) :
    hol k _) : (Fin (n + 1) → ℂ) → ℂ) = _
  rw [TopCat.Presheaf.cechD_apply]
  simp only [map_sum, map_zsmul, holD, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum,
    Submodule.coe_smul_of_tower]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  congr 2
  exact cechSectionsEquivAn_res k (fun a ↦ ULift.up (i a)) l.succAbove _

/-- **Čech cohomology of `𝒪(k)^an`**: the Čech complex for the standard cover of `ℙⁿ_an` is exact
in degree `p + 1` if `p + 1 > n`, or `0 < p + 1 < n`, or `k > -n - 1`. -/
theorem exactAt_cechComplex_twistingSheafAn (k : ℤ) (p : ℕ)
    (hp : n ≤ p ∨ p + 1 < n ∨ -((n : ℤ) + 1) < k) :
    (TopCat.Presheaf.cechComplex stdCoverAn (twistingSheafAn.{u} n k).toAb.obj).ExactAt
      (p + 1) := by
  rw [TopCat.Presheaf.exactAt_cechComplex_succ_iff]
  intro c hc
  have hx : CechProjectiveAn.holD k (p + 1) (cechCochainEquivAn k (p + 1) c) = 0 := by
    rw [← cechCochainEquivAn_cechD, hc, map_zero]
  obtain ⟨y, hy⟩ := (CechProjectiveAn.holD_exact k p hp _).1 hx
  refine ⟨(cechCochainEquivAn k p).symm y, (cechCochainEquivAn k (p + 1)).injective ?_⟩
  rw [cechCochainEquivAn_cechD, AddEquiv.apply_symm_apply, hy]

/-- For `k ≥ -n`, the Čech complex of `𝒪(k)^an` for the standard cover is exact in all positive
degrees. -/
theorem isCechAcyclic_twistingSheafAn (k : ℤ) (hk : -(n : ℤ) ≤ k) :
    TopCat.Presheaf.IsCechAcyclic stdCoverAn (twistingSheafAn.{u} n k).toAb.obj :=
  fun p ↦ exactAt_cechComplex_twistingSheafAn k p (Or.inr (Or.inr (by omega)))


/-- **`𝒪(k)^an` is trivial on the chart `π⁻¹ Uᵢ`**: for `W ≤ π⁻¹ Uᵢ`, the restrictions of
`𝒪(k)^an` and `𝒪` to `W` are isomorphic abelian sheaves (`t ↦ tᵢ`). -/
noncomputable def restrictOpenTwistingSheafAnIso (k : ℤ) (W : (projectiveSpaceAn.{u} n).Opens)
    (i : Fin (n + 1)) (hW : W ≤ preimOpen πL.{u} (U n (ULift.{u} ℂ) i)) :
    (TopCat.Sheaf.restrictOpen W).obj (twistingSheafAn.{u} n k).toAb ≅
      (TopCat.Sheaf.restrictOpen W).obj
        (projectiveSpaceAn.{u} n).toLocallyRingedSpace.structureSheafAb :=
  have hle (V : Opens ((Opens.toTopCat (projectiveSpaceAn.{u} n).toPresheafedSpace).obj W)) :
      W.isOpenEmbedding.isOpenMap.functor.obj V ≤ preimOpen πL.{u} (U n (ULift.{u} ℂ) i) :=
    fun _ ⟨y, _, hy⟩ ↦ hy ▸ hW y.2
  (sheafToPresheaf _ _).preimageIso <| NatIso.ofComponents
    (fun V ↦ AddEquiv.toAddCommGrpIso
      ((isoSectionsEquiv (twistingSheafAnIso n k) _).trans
        (pbTwistSectionsEquiv (cocycle n (ULift.{u} ℂ) ^ k) i (hle V.unop))))
    (by
      intro V V' h
      ext x
      have h' := (W.isOpenEmbedding.isOpenMap.functor.map h.unop).le
      exact (congrArg (pbTwistSectionsEquiv _ i (hle V'.unop))
        (modHom_modRes (twistingSheafAnIso n k).hom h' x)).trans
        (pbTwistSectionsEquiv_modRes i (hle V.unop) h' _))


open SimplexCochain in
/-- The intersection `U_σ` of the standard cover is `π⁻¹ (UI (im σ))`. -/
lemma cechOpen_stdCoverAn {p : ℕ} (σ : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    TopCat.Presheaf.cechOpen stdCoverAn σ = opensUI.{u} (im fun a ↦ (σ a).down) := by
  ext y
  obtain ⟨v, hv, rfl⟩ := pointOfVec_surjective y
  change pointOfVec.{u} v hv ∈ TopCat.Presheaf.cechOpen stdCoverAn σ ↔
    pointOfVec.{u} v hv ∈ (opensUI.{u} (im fun a ↦ (σ a).down) : Set (projectiveSpaceAn.{u} n))
  rw [TopCat.Presheaf.cechOpen, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter, coe_opensUI,
    Set.mem_preimage, ← Set.mem_preimage, preimage_UI]
  simp only [Set.mem_iInter, Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, mem_range_chart_pointOfVec_iff]
  exact forall_congr' fun a ↦ pointOfVec_mem_preimOpen_iff v hv _

/-- **`𝒪(k)^an` is acyclic on the intersections of the standard cover** (from Theorem B for `𝒪`,
since `𝒪(k)^an` is trivial on each chart). -/
lemma subsingleton_H_restrictOpen_cechOpen (k : ℤ) {p : ℕ}
    (σ : Fin (p + 1) → ULift.{u} (Fin (n + 1))) (q : ℕ) (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen
      (TopCat.Presheaf.cechOpen stdCoverAn σ)).obj (twistingSheafAn.{u} n k).toAb) q) := by
  have e := restrictOpenTwistingSheafAnIso k (TopCat.Presheaf.cechOpen stdCoverAn σ) (σ 0).down
    (iInf_le _ 0)
  refine (TopCat.Sheaf.H.addEquivOfIso e q).toEquiv.subsingleton_congr.2 ?_
  rw [cechOpen_stdCoverAn σ]
  exact subsingleton_H_restrictOpen_opensUI (SimplexCochain.im_nonempty _) q hq

/-- **`Hᵠ(ℙⁿ_an, 𝒪(k)^an) = 0` for `q ≥ 1` and `k ≥ -n`.** -/
theorem H_twistingSheafAn_eq_zero (k : ℤ) (hk : -(n : ℤ) ≤ k) (q : ℕ)
    (x : LocallyRingedSpace.H (twistingSheafAn.{u} n k) (q + 1)) : x = 0 :=
  TopCat.Sheaf.H_eq_zero_of_isCechAcyclic stdCoverAn iSup_stdCoverAn _
    (fun _ σ q' _ ↦ (subsingleton_H_restrictOpen_cechOpen k σ (q' + 1) q'.succ_pos).elim _ _)
    (isCechAcyclic_twistingSheafAn k hk) q x


/-! ### Global sections -/

/-- Kernels correspond under additive equivalences intertwining two maps. -/
def kerAddEquivOfComm {A A' B B' : Type*} [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B]
    [AddCommGroup B'] (e₀ : A ≃+ A') (e₁ : B ≃+ B') (f : A →+ B) (g : A' →+ B')
    (h : ∀ x, e₁ (f x) = g (e₀ x)) : f.ker ≃+ g.ker where
  toFun x := ⟨e₀ x.1, by rw [AddMonoidHom.mem_ker, ← h, x.2, map_zero]⟩
  invFun y := ⟨e₀.symm y.1, by
    rw [AddMonoidHom.mem_ker, ← e₁.map_eq_zero_iff, h, AddEquiv.apply_symm_apply]; exact y.2⟩
  left_inv x := Subtype.ext (e₀.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e₀.apply_symm_apply y.1)
  map_add' x y := Subtype.ext (map_add e₀ x.1 y.1)

variable (n) in
/-- The `0`-cocycles of the analytic Čech complex of `𝒪(e)`, `e ≥ 0`, are the homogeneous
polynomials of degree `e`. -/
noncomputable def homogeneousEquivKerHolD (e : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ e ≃+
      (CechProjectiveAn.holD (e : ℤ) (n := n) 0).toAddMonoidHom.ker :=
  AddEquiv.ofBijective
    ({ toFun P := ⟨CechProjectiveAn.holAug n e P, CechProjectiveAn.holD_holAug P⟩
       map_zero' := Subtype.ext (map_zero _)
       map_add' P Q := Subtype.ext (map_add _ P Q) } :
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ e →+
        (CechProjectiveAn.holD (e : ℤ) (n := n) 0).toAddMonoidHom.ker)
    ⟨fun P Q h ↦ CechProjectiveAn.holAug_injective e (congrArg Subtype.val h), fun y ↦ by
      obtain ⟨P, hP⟩ := (CechProjectiveAn.holAug_exact e y.1).1 y.2
      exact ⟨P, Subtype.ext hP⟩⟩

variable (n) in
/-- `H⁰(ℙⁿ_an, 𝒪(k)^an)` is the kernel of the first differential of the analytic Čech
complex. -/
noncomputable def hZeroTwistingSheafAnEquivKer (k : ℤ) :
    LocallyRingedSpace.H (twistingSheafAn.{u} n k) 0 ≃+
      (CechProjectiveAn.holD k (n := n) 0).toAddMonoidHom.ker :=
  (LocallyRingedSpace.H.equiv₀ _).trans
    ((TopCat.Presheaf.cechAugmentAddEquivKer stdCoverAn (fun _ ↦ le_top) _
      iSup_stdCoverAn.ge).trans
      (kerAddEquivOfComm (cechCochainEquivAn k 0) (cechCochainEquivAn k 1) _ _
        (cechCochainEquivAn_cechD k 0)))

variable (n) in
/-- **`H⁰(ℙⁿ_an, 𝒪(e)^an) = ℂ[X₀, …, Xₙ]_e`** for `e ≥ 0`. -/
noncomputable def hZeroTwistingSheafAnEquiv (e : ℕ) :
    LocallyRingedSpace.H (twistingSheafAn.{u} n e) 0 ≃+
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℂ e :=
  (hZeroTwistingSheafAnEquivKer n e).trans (homogeneousEquivKerHolD n e).symm

/-- **`H⁰(ℙⁿ_an, 𝒪(k)^an) = 0` for `k < 0`** (`n ≥ 1`). -/
theorem H_zero_twistingSheafAn_eq_zero (hn : 1 ≤ n) (k : ℤ) (hk : k < 0)
    (x : LocallyRingedSpace.H (twistingSheafAn.{u} n k) 0) : x = 0 := by
  apply (hZeroTwistingSheafAnEquivKer n k).injective
  rw [map_zero]
  apply Subtype.ext
  have hx := (hZeroTwistingSheafAnEquivKer n k x).2
  exact (CechProjectiveAn.holD_zero_injective hk (Or.inl hn)) (hx.trans (map_zero _).symm)

end ComplexAnalytic.projectiveSpaceAn

end
