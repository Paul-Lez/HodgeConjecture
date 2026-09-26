/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.Proper.CechProjectiveBox
public import Other.Oka.Analytification.GAGA.Proper.RelativeProjectiveAnFunctions
public import Other.Oka.Analytification.GAGA.TwistCechAn
public import Other.Oka.Topology.Sheaves.Cohomology.CechLocalization

/-!
# The Čech complex of `𝒪(k)^an` on `U × ℙᴺ` and its cohomology

Let `P = ℙₒ(N; ℂ[y₀, …, y_{m-1}])` and `𝒪(k)^an` the analytification of the twisting sheaf `𝒪(k)`
on `P` (`ComplexAnalytic.relProjectiveSpaceAn.twistingSheafAn m N k`). As for `ℙᴺ_ℂ`
(`Other/Oka/Analytification/GAGA/TwistCechAn.lean`), `𝒪(k)^an` is the twist of `𝒪_{P^an}` by the
pulled back transition functions (`twistingSheafAnIso`), and a section over `W` is the same as
the function `F(v, y) = vᵢᵏ tᵢ([v; y])` on the cone over `W` (`twFun`), holomorphic and
homogeneous of degree `k` in `v`, and every such function arises (`exists_twFun_eq`).

For an open `U ⊆ ℂᵐ`, the opens `tube U ⊓ π⁻¹ Uᵢ` cover `tube U = U × ℙᴺ`
(`stdCoverAn U`), and the cone over their intersection `U_σ` is `V (im σ) × U`. Hence the Čech
complex of `𝒪(k)^an` for this cover is the parametric Čech complex
`CechProjectiveBox.holPD k U` (`cechCochainEquivAn`, `cechCochainEquivAn_cechD`), which is exact in
positive degrees for `k ≥ -N`. On a box `B`, `𝒪(k)^an` has no higher cohomology on the `U_σ`
(it is trivial on each chart, and Theorem B holds on the chart pieces), so Leray's theorem gives:

## Main results

- `ComplexAnalytic.relProjectiveSpaceAn.H_tube_twistingSheafAn_eq_zero`:
  `Hᵠ(B × ℙᴺ, 𝒪(k)^an) = 0` for `q ≥ 1`, `k ≥ -N` and `B` an open box.
- `ComplexAnalytic.relProjectiveSpaceAn.tubeSectionsEquivKer`: `Γ(U × ℙᴺ, 𝒪(k)^an)` is the kernel
  of the first differential of `CechProjectiveBox.holPD k U`, for every open `U`.
- `ComplexAnalytic.relProjectiveSpaceAn.tubeSectionsEquiv`: for `e ≥ 0`, `Γ(U × ℙᴺ, 𝒪(e)^an)` is
  the space of families `(c_s)_s`, indexed by the monomials of degree `e`, of holomorphic
  functions on `U`; the section of `(c_s)_s` is `(v, y) ↦ ∑_s c_s(y) vˢ`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Topology
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.LocallyRingedSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic.relProjectiveSpaceAn

open AnalyticSpace ProjectiveSpace

variable {m N : ℕ}

/-- The comparison morphism `P^an ⟶ P`, as a morphism of locally ringed spaces. -/
noncomputable abbrev πL : (relProjectiveSpaceAn.{u} m N).toLocallyRingedSpace ⟶
    ℙₒ(N; RelBase.{u} m).toLocallyRingedSpace :=
  analytificationπLRS (relProjectiveSpace.{u} m N)

/-- **`𝒪(k)^an` in explicit form**: sections over `W` are families `tᵢ ∈ Γ(W ∩ π⁻¹ Uᵢ, 𝒪)` with
`tᵢ = π^♯ (Xⱼ / Xᵢ)ᵏ · tⱼ`. -/
noncomputable abbrev twistAn (k : ℤ) :
    SheafOfModules.{u} (relProjectiveSpaceAn.{u} m N).ringSheaf :=
  pbTwist πL.{u} (cocycle N (RelBase.{u} m) ^ k)

lemma pointOfVec_mem_preimOpen_iff (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) (y : Fin m → ℂ)
    (i : Fin (N + 1)) :
    pointOfVec.{u} v hv y ∈ preimOpen πL.{u} (U N (RelBase.{u} m) i) ↔ v i ≠ 0 := by
  rw [← mem_range_chart_pointOfVec_iff v hv y i, range_chart]
  rfl

lemma mem_vecCone_inf_iff {W : (relProjectiveSpaceAn.{u} m N).Opens}
    (p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)) (i : Fin (N + 1)) :
    p ∈ vecCone.{u} (W ⊓ preimOpen πL.{u} (U N (RelBase.{u} m) i)) ↔
      p ∈ vecCone.{u} W ∧ p.1 i ≠ 0 := by
  constructor
  · rintro ⟨hv, h1, h2⟩
    exact ⟨⟨hv, h1⟩, (pointOfVec_mem_preimOpen_iff p.1 hv p.2 i).1 h2⟩
  · rintro ⟨⟨hv, h1⟩, h2⟩
    exact ⟨hv, h1, (pointOfVec_mem_preimOpen_iff p.1 hv p.2 i).2 h2⟩

/-- The value at `[v; y]` of the pulled-back transition function `(Xⱼ / Xᵢ)ᵏ` is
`(vⱼ / vᵢ)ᵏ`. -/
lemma secFun_pbG (k : ℤ) (i j : Fin (N + 1)) {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)}
    (hp : p ∈ vecCone.{u} (preimOpen πL.{u} (U N (RelBase.{u} m) i) ⊓
      preimOpen πL.{u} (U N (RelBase.{u} m) j))) :
    secFun (pbG πL.{u} (cocycle N (RelBase.{u} m) ^ k) i j) p = (p.1 j / p.1 i) ^ k := by
  rw [secFun_of_mem _ hp.1 hp.2]
  have hi : p.1 i ≠ 0 := (pointOfVec_mem_preimOpen_iff p.1 hp.1 p.2 i).1 hp.2.1
  exact evπ_cocycle_zpow k p.1 hp.1 p.2 i j hi hp.2

variable {k : ℤ} {W : (relProjectiveSpaceAn.{u} m N).Opens}

/-- The chart index used to evaluate a section of `𝒪(k)^an` at `(v, y)`. -/
noncomputable def coneIdx {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)} (h : p ∈ vecCone.{u} W) :
    Fin (N + 1) :=
  (Function.ne_iff.1 h.1).choose

lemma coneIdx_spec {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)} (h : p ∈ vecCone.{u} W) :
    p.1 (coneIdx h) ≠ 0 :=
  (Function.ne_iff.1 h.1).choose_spec

open scoped Classical in
/-- **A section of `𝒪(k)^an` over `W` as a function on `ℂᴺ⁺¹ × ℂᵐ`**:
`(v, y) ↦ vᵢᵏ tᵢ([v; y])` for any `i` with `vᵢ ≠ 0` (on the cone over `W`; zero off it). -/
noncomputable def twFun (t : (twistAn.{u} (m := m) (N := N) k).val.obj (op W))
    (p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)) : ℂ :=
  if h : p ∈ vecCone.{u} W then p.1 (coneIdx h) ^ k * secFun (pbComp t (coneIdx h)) p else 0

/-- The value `vᵢᵏ tᵢ([v; y])` does not depend on the chart `i`. -/
lemma zpow_mul_secFun_pbComp (t : (twistAn.{u} (m := m) (N := N) k).val.obj (op W))
    {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)} (hp : p ∈ vecCone.{u} W) {a b : Fin (N + 1)}
    (ha : p.1 a ≠ 0) (hb : p.1 b ≠ 0) :
    p.1 a ^ k * secFun (pbComp t a) p = p.1 b ^ k * secFun (pbComp t b) p := by
  have hpO : p ∈ vecCone.{u} (W ⊓ (preimOpen πL.{u} (U N (RelBase.{u} m) a) ⊓
      preimOpen πL.{u} (U N (RelBase.{u} m) b))) :=
    ⟨hp.1, hp.2, (pointOfVec_mem_preimOpen_iff p.1 hp.1 p.2 a).2 ha,
      (pointOfVec_mem_preimOpen_iff p.1 hp.1 p.2 b).2 hb⟩
  have hc := congrArg (secFun · p) (pbComp_compat t a b)
  simp only [secFun_mul, secFun_restrictOpen] at hc
  rw [Set.indicator_of_mem hpO, Set.indicator_of_mem hpO, Set.indicator_of_mem hpO] at hc
  rw [hc, secFun_pbG k a b ⟨hp.1, hpO.2.2⟩, ← mul_assoc, div_zpow,
    mul_div_cancel₀ _ (zpow_ne_zero _ ha)]

lemma twFun_eq (t : (twistAn.{u} (m := m) (N := N) k).val.obj (op W))
    {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)} (hp : p ∈ vecCone.{u} W) (i : Fin (N + 1))
    (hi : p.1 i ≠ 0) : twFun t p = p.1 i ^ k * secFun (pbComp t i) p := by
  classical
  rw [twFun, dif_pos hp]
  exact zpow_mul_secFun_pbComp t hp (coneIdx_spec hp) hi

lemma twFun_of_notMem (t : (twistAn.{u} (m := m) (N := N) k).val.obj (op W))
    {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)} (hp : p ∉ vecCone.{u} W) : twFun t p = 0 := by
  classical
  rw [twFun, dif_neg hp]

lemma twFun_add (t t' : (twistAn.{u} (m := m) (N := N) k).val.obj (op W)) :
    twFun (t + t') = twFun t + twFun t' := by
  funext p
  by_cases hp : p ∈ vecCone.{u} W
  · have hi := coneIdx_spec hp
    rw [Pi.add_apply, twFun_eq _ hp _ hi, twFun_eq _ hp _ hi, twFun_eq _ hp _ hi, pbComp_add,
      secFun_add, mul_add]
  · rw [Pi.add_apply, twFun_of_notMem _ hp, twFun_of_notMem _ hp, twFun_of_notMem _ hp,
      add_zero]

lemma twFun_zero : twFun (0 : (twistAn.{u} (m := m) (N := N) k).val.obj (op W)) = 0 := by
  funext p
  by_cases hp : p ∈ vecCone.{u} W
  · rw [twFun_eq _ hp _ (coneIdx_spec hp), pbComp_zero, secFun_zero, mul_zero, Pi.zero_apply]
  · rw [twFun_of_notMem _ hp, Pi.zero_apply]

lemma twFun_modRes (t : (twistAn.{u} (m := m) (N := N) k).val.obj (op W))
    {W' : (relProjectiveSpaceAn.{u} m N).Opens} (h : W' ≤ W) :
    twFun (modRes t W' h) = (vecCone.{u} W').indicator (twFun t) := by
  funext p
  by_cases hp : p ∈ vecCone.{u} W'
  · have hi := coneIdx_spec hp
    rw [Set.indicator_of_mem hp, twFun_eq _ hp _ hi, twFun_eq _ (vecCone_mono h hp) _ hi,
      pbComp_modRes, secFun_restrictOpen,
      Set.indicator_of_mem ((mem_vecCone_inf_iff p _).2 ⟨hp, hi⟩)]
  · rw [Set.indicator_of_notMem hp, twFun_of_notMem _ hp]

lemma twFun_smul (t : (twistAn.{u} (m := m) (N := N) k).val.obj (op W))
    {v : Fin (N + 1) → ℂ} {y : Fin m → ℂ} (hp : (v, y) ∈ vecCone.{u} W) {c : ℂ} (hc : c ≠ 0) :
    twFun t (c • v, y) = c ^ k * twFun t (v, y) := by
  have hi := coneIdx_spec hp
  have hci : (c • v, y).1 (coneIdx hp) ≠ 0 := by simpa using And.intro hc hi
  rw [twFun_eq _ (smul_mem_vecCone hp hc) _ hci, twFun_eq _ hp _ hi, secFun_smul _ _ _ hc]
  simp only [Pi.smul_apply, smul_eq_mul, mul_zpow, mul_assoc]

lemma differentiableOn_twFun (t : (twistAn.{u} (m := m) (N := N) k).val.obj (op W)) :
    DifferentiableOn ℂ (twFun t) (vecCone.{u} W) := by
  intro p hp
  have hi := coneIdx_spec hp
  set i := coneIdx hp
  refine DifferentiableAt.differentiableWithinAt ?_
  have hpi : p ∈ vecCone.{u} (W ⊓ preimOpen πL.{u} (U N (RelBase.{u} m) i)) :=
    (mem_vecCone_inf_iff p i).2 ⟨hp, hi⟩
  have hN := isOpen_vecCone.mem_nhds hpi
  have heq : (fun q : (Fin (N + 1) → ℂ) × (Fin m → ℂ) ↦ q.1 i ^ k * secFun (pbComp t i) q)
      =ᶠ[𝓝 p] twFun t := by
    filter_upwards [hN] with q hq
    have hq' := (mem_vecCone_inf_iff q i).1 hq
    exact (twFun_eq t hq'.1 i hq'.2).symm
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq.symm
  have h1 : DifferentiableAt ℂ (fun q : (Fin (N + 1) → ℂ) × (Fin m → ℂ) ↦ q.1 i) p := by
    fun_prop
  exact (h1.zpow (Or.inl hi)).mul ((differentiableOn_secFun _ p hpi).differentiableAt hN)

lemma eq_zero_of_twFun (t : (twistAn.{u} (m := m) (N := N) k).val.obj (op W))
    (h : twFun t = 0) : t = 0 := by
  refine pbTwist_ext fun i ↦ ?_
  refine eq_zero_of_secFun _ fun p hp ↦ ?_
  have hp' := (mem_vecCone_inf_iff p i).1 hp
  have := congrFun h p
  rw [twFun_eq t hp'.1 i hp'.2, Pi.zero_apply] at this
  exact (mul_eq_zero.1 this).resolve_left (zpow_ne_zero _ hp'.2)

lemma twFun_injective :
    Function.Injective (twFun (k := k) (W := W) (m := m) (N := N)) := by
  intro t t' h
  rw [← sub_eq_zero]
  refine eq_zero_of_twFun _ ?_
  have := twFun_add (t - t') t'
  rw [sub_add_cancel, h] at this
  simpa using this.symm

lemma preimOpen_le_range (i : Fin (N + 1)) :
    ∀ x ∈ W ⊓ preimOpen πL.{u} (U N (RelBase.{u} m) i), x ∈ Set.range (chartLRS.{u} i).base :=
  fun x hx ↦ by rw [range_chart]; exact hx.2

/-- **Every holomorphic function on the cone over `W`, homogeneous of degree `k` in `v`, comes
from a section of `𝒪(k)^an`.** -/
lemma exists_twFun_eq (F : (Fin (N + 1) → ℂ) × (Fin m → ℂ) → ℂ)
    (hF : DifferentiableOn ℂ F (vecCone.{u} W))
    (hhom : ∀ p ∈ vecCone.{u} W, ∀ c : ℂ, c ≠ 0 → F (c • p.1, p.2) = c ^ k * F p)
    (h0 : ∀ p ∉ vecCone.{u} W, F p = 0) :
    ∃ t : (twistAn.{u} (m := m) (N := N) k).val.obj (op W), twFun t = F := by
  have hs (i : Fin (N + 1)) := exists_secFun_eq
    (W := W ⊓ preimOpen πL.{u} (U N (RelBase.{u} m) i)) i (preimOpen_le_range i)
    (fun p ↦ F p / p.1 i ^ k)
    (fun p hp ↦ by
      have hp' := (mem_vecCone_inf_iff p i).1 hp
      have h2 : DifferentiableAt ℂ (fun q : (Fin (N + 1) → ℂ) × (Fin m → ℂ) ↦ q.1 i) p := by
        fun_prop
      have h1 : DifferentiableWithinAt ℂ (fun q ↦ F q * (q.1 i ^ k)⁻¹)
          (vecCone.{u} (W ⊓ preimOpen πL.{u} (U N (RelBase.{u} m) i))) p :=
        ((hF p hp'.1).mono fun q hq ↦ ((mem_vecCone_inf_iff q i).1 hq).1).mul
          ((h2.zpow (Or.inl hp'.2)).inv (zpow_ne_zero _ hp'.2)).differentiableWithinAt
      simpa only [div_eq_mul_inv] using h1)
    (fun p hp c hc ↦ by
      have hp' := (mem_vecCone_inf_iff p i).1 hp
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hhom p hp'.1 c hc, mul_zpow, mul_div_mul_left _ _ (zpow_ne_zero _ hc)])
  choose s hs using hs
  refine ⟨pbMk s fun a b ↦ eq_of_secFun fun p hp ↦ ?_, ?_⟩
  · have hpa : p ∈ vecCone.{u} (W ⊓ preimOpen πL.{u} (U N (RelBase.{u} m) a)) :=
      vecCone_mono (by order) hp
    have hpb : p ∈ vecCone.{u} (W ⊓ preimOpen πL.{u} (U N (RelBase.{u} m) b)) :=
      vecCone_mono (by order) hp
    have ha := ((mem_vecCone_inf_iff p a).1 hpa).2
    have hb := ((mem_vecCone_inf_iff p b).1 hpb).2
    rw [secFun_mul, secFun_restrictOpen, secFun_restrictOpen, secFun_restrictOpen,
      Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp, hs a p hpa,
      hs b p hpb, secFun_pbG k a b (vecCone_mono (by order) hp), div_zpow]
    field_simp
  · funext p
    by_cases hp : p ∈ vecCone.{u} W
    · have hi := coneIdx_spec hp
      rw [twFun_eq _ hp _ hi, pbComp_pbMk, hs _ p ((mem_vecCone_inf_iff p _).2 ⟨hp, hi⟩),
        mul_div_cancel₀ _ (zpow_ne_zero _ hi)]
    · rw [twFun_of_notMem _ hp, h0 p hp]

/-! ### Sections over opens whose cone is a product -/

open CechProjectiveAn CechProjectiveBox

/-- `twFun` as an additive map to `CechProjectiveBox.holP k D I`, when the cone over `W` is
`V I × D`. -/
noncomputable def twHolHom (D : Opens (Fin m → ℂ)) (I : Finset (Fin (N + 1)))
    (hWI : vecCone.{u} W = V I ×ˢ (D : Set (Fin m → ℂ))) :
    (twistAn.{u} (m := m) (N := N) k).val.obj (op W) →+ holP k D I where
  toFun t := ⟨twFun t, hWI ▸ differentiableOn_twFun t,
    fun z hz y hy c hc ↦ twFun_smul t (by rw [hWI]; exact ⟨hz, hy⟩) hc,
    fun p hp ↦ twFun_of_notMem t (by rw [hWI]; exact hp)⟩
  map_zero' := Subtype.ext twFun_zero
  map_add' t t' := Subtype.ext (twFun_add t t')

/-- **Sections of `𝒪(k)^an` over an open with cone `V I × D` are the holomorphic functions on
`V I × D`, homogeneous of degree `k` in the first variable**: `twFun` as an additive equivalence
onto `CechProjectiveBox.holP k D I`. -/
noncomputable def twHolEquiv (D : Opens (Fin m → ℂ)) (I : Finset (Fin (N + 1)))
    (hWI : vecCone.{u} W = V I ×ˢ (D : Set (Fin m → ℂ))) :
    (twistAn.{u} (m := m) (N := N) k).val.obj (op W) ≃+ holP k D I :=
  AddEquiv.ofBijective (twHolHom D I hWI)
    ⟨fun t t' h ↦ twFun_injective (congrArg Subtype.val h), fun F ↦ by
      obtain ⟨t, ht⟩ := exists_twFun_eq (W := W) (k := k) F.1 (hWI ▸ F.2.1)
        (fun p hp c hc ↦ by
          rw [hWI] at hp
          exact F.2.2.1 p.1 hp.1 p.2 hp.2 c hc)
        (fun p hp ↦ F.2.2.2 p (by rwa [hWI] at hp))
      exact ⟨t, Subtype.ext ht⟩⟩

lemma coe_twHolEquiv (D : Opens (Fin m → ℂ)) (I : Finset (Fin (N + 1)))
    (hWI : vecCone.{u} W = V I ×ˢ (D : Set (Fin m → ℂ)))
    (t : (twistAn.{u} (m := m) (N := N) k).val.obj (op W)) :
    ((twHolEquiv D I hWI t : holP k D I) : (Fin (N + 1) → ℂ) × (Fin m → ℂ) → ℂ) = twFun t :=
  rfl

/-- `twHolEquiv` is compatible with restriction (`CechProjectiveBox.holPRes`). -/
lemma twHolEquiv_modRes (D : Opens (Fin m → ℂ)) {I J : Finset (Fin (N + 1))} (hJI : J ⊆ I)
    (hWI : vecCone.{u} W = V J ×ˢ (D : Set (Fin m → ℂ)))
    {W' : (relProjectiveSpaceAn.{u} m N).Opens} (h : W' ≤ W)
    (hW'I : vecCone.{u} W' = V I ×ˢ (D : Set (Fin m → ℂ)))
    (t : (twistAn.{u} (m := m) (N := N) k).val.obj (op W)) :
    twHolEquiv D I hW'I (modRes t W' h) = holPRes k D hJI (twHolEquiv D J hWI t) := by
  apply Subtype.ext
  rw [coe_twHolEquiv, coe_holPRes, coe_twHolEquiv, twFun_modRes, hW'I]

/-! ### The Čech complex of `𝒪(k)^an` for the standard cover of `D × ℙᴺ` -/

/-- The standard cover `tube D ⊓ π⁻¹ Uᵢ` of `tube D = D × ℙᴺ`, indexed by
`ULift (Fin (N + 1))`. -/
noncomputable def stdCoverAn (D : Opens (Fin m → ℂ)) :
    ULift.{u} (Fin (N + 1)) → (relProjectiveSpaceAn.{u} m N).Opens :=
  fun i ↦ tube D ⊓ preimOpen πL.{u} (U N (RelBase.{u} m) i.down)

lemma iSup_stdCoverAn (D : Opens (Fin m → ℂ)) :
    ⨆ i, stdCoverAn.{u} (m := m) (N := N) D i = tube D := by
  refine le_antisymm (iSup_le fun i ↦ inf_le_left) fun x hx ↦ ?_
  have : πL.{u}.base x ∈ (⨆ i, U N (RelBase.{u} m) i : ℙₒ(N; RelBase.{u} m).Opens) := by
    rw [iSup_U]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 this
  exact Opens.mem_iSup.2 ⟨⟨i⟩, hx, hi⟩

lemma stdCoverAn_le (D : Opens (Fin m → ℂ)) (i : ULift.{u} (Fin (N + 1))) :
    stdCoverAn.{u} (m := m) (N := N) D i ≤ tube D :=
  inf_le_left

lemma mem_cechOpen_stdCoverAn_iff (D : Opens (Fin m → ℂ)) {p : ℕ}
    (σ : Fin (p + 1) → ULift.{u} (Fin (N + 1))) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0)
    (y : Fin m → ℂ) :
    pointOfVec.{u} v hv y ∈ TopCat.Presheaf.cechOpen (stdCoverAn D) σ ↔
      y ∈ D ∧ ∀ a, v (σ a).down ≠ 0 := by
  rw [TopCat.Presheaf.cechOpen, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  simp only [stdCoverAn, Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, mem_tube,
    baseY_pointOfVec, pointOfVec_mem_preimOpen_iff]
  exact ⟨fun h ↦ ⟨(h 0).1, fun a ↦ (h a).2⟩, fun h a ↦ ⟨h.1, h.2 a⟩⟩

open SimplexCochain in
/-- The cone over the intersection `U_σ` of the standard cover is `V (im σ) × D`. -/
lemma vecCone_cechOpen (D : Opens (Fin m → ℂ)) {p : ℕ}
    (σ : Fin (p + 1) → ULift.{u} (Fin (N + 1))) :
    vecCone.{u} (TopCat.Presheaf.cechOpen (stdCoverAn D) σ) =
      V (im fun a ↦ (σ a).down) ×ˢ (D : Set (Fin m → ℂ)) := by
  ext q
  simp only [V, Set.mem_prod, Set.mem_setOf_eq, Finset.mem_image, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff, SetLike.mem_coe]
  refine ⟨fun ⟨hv, h⟩ ↦ ?_, fun ⟨h1, h2⟩ ↦ ?_⟩
  · obtain ⟨hD, hσ⟩ := (mem_cechOpen_stdCoverAn_iff D σ q.1 hv q.2).1 h
    exact ⟨hσ, hD⟩
  · have hv : q.1 ≠ 0 := fun h0 ↦ h1 0 (by simp [h0])
    exact ⟨hv, (mem_cechOpen_stdCoverAn_iff D σ q.1 hv q.2).2 ⟨h2, h1⟩⟩

variable (m N) in
/-- **The analytification `𝒪(k)^an` of the twisting sheaf `𝒪(k)` on `P`.** -/
noncomputable abbrev twistingSheafAn (k : ℤ) :
    SheafOfModules.{u} (relProjectiveSpaceAn.{u} m N).ringSheaf :=
  (analytificationModules (relProjectiveSpace.{u} m N)).obj
    (ProjectiveSpace.twistingSheaf N (RelBase.{u} m) k)

variable (m N) in
/-- `𝒪(k)^an ≅ twistAn k`: the analytification of `𝒪(k)` is the twist of `𝒪_{P^an}` by the
pulled back transition functions `(Xⱼ / Xᵢ)ᵏ`. -/
noncomputable def twistingSheafAnIso (k : ℤ) :
    twistingSheafAn.{u} m N k ≅ twistAn.{u} (m := m) (N := N) k :=
  pullbackTwistUnitIso πL.{u} (cocycle N (RelBase.{u} m) ^ k) (iSup_U N _)

/-- An isomorphism of sheaves of modules, on sections. -/
noncomputable def isoSectionsEquiv
    {P Q : SheafOfModules.{u} (relProjectiveSpaceAn.{u} m N).ringSheaf}
    (e : P ≅ Q) (W : (relProjectiveSpaceAn.{u} m N).Opens) :
    P.val.obj (op W) ≃+ Q.val.obj (op W) where
  toFun x := e.hom.val.app (op W) x
  invFun y := e.inv.val.app (op W) y
  left_inv x := congr($(congrArg (fun φ : P ⟶ P ↦ φ.val.app (op W)) e.hom_inv_id).hom x)
  right_inv y := congr($(congrArg (fun φ : Q ⟶ Q ↦ φ.val.app (op W)) e.inv_hom_id).hom y)
  map_add' x y := map_add _ x y

open SimplexCochain in
/-- Sections of `𝒪(k)^an` over the intersection `U_σ` of the standard cover of `D × ℙᴺ`, as
holomorphic functions on `V (im σ) × D` homogeneous of degree `k` in the first variable. -/
noncomputable def cechSectionsEquivAn (D : Opens (Fin m → ℂ)) (k : ℤ) {p : ℕ}
    (σ : Fin (p + 1) → ULift.{u} (Fin (N + 1))) :
    (twistingSheafAn.{u} m N k).toAb.obj.obj (op (TopCat.Presheaf.cechOpen (stdCoverAn D) σ)) ≃+
      holP k D (im fun a ↦ (σ a).down) :=
  (isoSectionsEquiv (twistingSheafAnIso m N k) _).trans (twHolEquiv D _ (vecCone_cechOpen D σ))

open SimplexCochain in
lemma cechSectionsEquivAn_res (D : Opens (Fin m → ℂ)) (k : ℤ) {l p : ℕ}
    (τ : Fin (p + 1) → ULift.{u} (Fin (N + 1))) (θ : Fin (l + 1) → Fin (p + 1))
    (s : (twistingSheafAn.{u} m N k).toAb.obj.obj
      (op (TopCat.Presheaf.cechOpen (stdCoverAn D) (τ ∘ θ)))) :
    cechSectionsEquivAn D k τ ((twistingSheafAn.{u} m N k).toAb.obj.map
      (homOfLE (TopCat.Presheaf.cechOpen_le_comp _ τ θ)).op s) =
      holPRes k D (im_comp_subset (fun a ↦ (τ a).down) θ) (cechSectionsEquivAn D k (τ ∘ θ) s) := by
  change twHolEquiv D _ (vecCone_cechOpen D τ) ((twistingSheafAnIso m N k).hom.val.app _
    (modRes s _ (TopCat.Presheaf.cechOpen_le_comp _ τ θ))) = _
  rw [modHom_modRes]
  exact twHolEquiv_modRes D _ (vecCone_cechOpen D (τ ∘ θ)) _ _ _

open SimplexCochain in
/-- **The Čech cochains of `𝒪(k)^an`** for the standard cover of `D × ℙᴺ` are the cochains of
the parametric Čech complex `CechProjectiveBox.holPD k D`. -/
noncomputable def cechCochainEquivAn (D : Opens (Fin m → ℂ)) (k : ℤ) (p : ℕ) :
    TopCat.Presheaf.CechCochain (stdCoverAn D) (twistingSheafAn.{u} m N k).toAb.obj p ≃+
      PCochain N k D p where
  toFun c i := cechSectionsEquivAn D k (fun a ↦ ULift.up (i a)) (c _)
  invFun y σ := (cechSectionsEquivAn D k σ).symm (y fun a ↦ (σ a).down)
  left_inv c := funext fun σ ↦ (cechSectionsEquivAn D k σ).symm_apply_apply (c σ)
  right_inv _ := funext fun i ↦
    (cechSectionsEquivAn D k (fun a ↦ ULift.up (i a))).apply_symm_apply _
  map_add' _ _ := funext fun i ↦
    map_add (cechSectionsEquivAn D k (fun a ↦ ULift.up (i a))) _ _

open SimplexCochain in
/-- **The Čech differential of `𝒪(k)^an` is `CechProjectiveBox.holPD`** under
`cechCochainEquivAn`. -/
lemma cechCochainEquivAn_cechD (D : Opens (Fin m → ℂ)) (k : ℤ) (p : ℕ)
    (c : TopCat.Presheaf.CechCochain (stdCoverAn D) (twistingSheafAn.{u} m N k).toAb.obj p) :
    cechCochainEquivAn D k (p + 1) (TopCat.Presheaf.cechD _ _ p c) =
      holPD k D p (cechCochainEquivAn D k p c) := by
  funext i
  apply Subtype.ext
  change ((cechSectionsEquivAn D k (fun a ↦ ULift.up (i a)) (TopCat.Presheaf.cechD _ _ p c _) :
    holP k D _) : (Fin (N + 1) → ℂ) × (Fin m → ℂ) → ℂ) = _
  rw [TopCat.Presheaf.cechD_apply]
  simp only [map_sum, map_zsmul, holPD, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum,
    Submodule.coe_smul_of_tower]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  congr 2
  exact cechSectionsEquivAn_res D k (fun a ↦ ULift.up (i a)) l.succAbove _

/-- **Čech cohomology of `𝒪(k)^an` on `D × ℙᴺ`**: the Čech complex for the standard cover is
exact in degree `p + 1` if `p + 1 > N`, or `0 < p + 1 < N`, or `k > -N - 1`. -/
theorem exactAt_cechComplex_twistingSheafAn (D : Opens (Fin m → ℂ)) (k : ℤ) (p : ℕ)
    (hp : N ≤ p ∨ p + 1 < N ∨ -((N : ℤ) + 1) < k) :
    (TopCat.Presheaf.cechComplex (stdCoverAn D) (twistingSheafAn.{u} m N k).toAb.obj).ExactAt
      (p + 1) := by
  rw [TopCat.Presheaf.exactAt_cechComplex_succ_iff]
  intro c hc
  have hx : holPD k D (p + 1) (cechCochainEquivAn D k (p + 1) c) = 0 := by
    rw [← cechCochainEquivAn_cechD, hc, map_zero]
  obtain ⟨y, hy⟩ := (holPD_exact k D p hp _).1 hx
  refine ⟨(cechCochainEquivAn D k p).symm y, (cechCochainEquivAn D k (p + 1)).injective ?_⟩
  rw [cechCochainEquivAn_cechD, AddEquiv.apply_symm_apply, hy]

/-- For `k ≥ -N`, the Čech complex of `𝒪(k)^an` for the standard cover of `D × ℙᴺ` is exact in
all positive degrees. -/
theorem isCechAcyclic_twistingSheafAn (D : Opens (Fin m → ℂ)) (k : ℤ) (hk : -(N : ℤ) ≤ k) :
    TopCat.Presheaf.IsCechAcyclic (stdCoverAn D) (twistingSheafAn.{u} m N k).toAb.obj :=
  fun p ↦ exactAt_cechComplex_twistingSheafAn D k p (Or.inr (Or.inr (by omega)))

/-! ### Vanishing on boxes -/

/-- **`𝒪(k)^an` is trivial on the chart `π⁻¹ Uᵢ`**: for `W ≤ π⁻¹ Uᵢ`, the restrictions of
`𝒪(k)^an` and `𝒪` to `W` are isomorphic abelian sheaves (`t ↦ tᵢ`). -/
noncomputable def restrictOpenTwistingSheafAnIso (k : ℤ) (W : (relProjectiveSpaceAn.{u} m N).Opens)
    (i : Fin (N + 1)) (hW : W ≤ preimOpen πL.{u} (U N (RelBase.{u} m) i)) :
    (TopCat.Sheaf.restrictOpen W).obj (twistingSheafAn.{u} m N k).toAb ≅
      (TopCat.Sheaf.restrictOpen W).obj
        (relProjectiveSpaceAn.{u} m N).toLocallyRingedSpace.structureSheafAb :=
  have hle (V : Opens ((Opens.toTopCat (relProjectiveSpaceAn.{u} m N).toPresheafedSpace).obj W)) :
      W.isOpenEmbedding.isOpenMap.functor.obj V ≤ preimOpen πL.{u} (U N (RelBase.{u} m) i) :=
    fun _ ⟨y, _, hy⟩ ↦ hy ▸ hW y.2
  (sheafToPresheaf _ _).preimageIso <| NatIso.ofComponents
    (fun V ↦ AddEquiv.toAddCommGrpIso
      ((isoSectionsEquiv (twistingSheafAnIso m N k) _).trans
        (pbTwistSectionsEquiv (cocycle N (RelBase.{u} m) ^ k) i (hle V.unop))))
    (by
      intro V V' h
      ext x
      have h' := (W.isOpenEmbedding.isOpenMap.functor.map h.unop).le
      exact (congrArg (pbTwistSectionsEquiv _ i (hle V'.unop))
        (modHom_modRes (twistingSheafAnIso m N k).hom h' x)).trans
        (pbTwistSectionsEquiv_modRes i (hle V.unop) h' _))

open SimplexCochain in
/-- The intersection `U_σ` of the standard cover of `D × ℙᴺ` is `tube D ⊓ π⁻¹ (UI (im σ))`. -/
lemma cechOpen_stdCoverAn (D : Opens (Fin m → ℂ)) {p : ℕ}
    (σ : Fin (p + 1) → ULift.{u} (Fin (N + 1))) :
    TopCat.Presheaf.cechOpen (stdCoverAn D) σ = tube D ⊓ opensUI (im fun a ↦ (σ a).down) := by
  ext x
  obtain ⟨v, hv, y, rfl⟩ := pointOfVec_surjective x
  rw [SetLike.mem_coe, mem_cechOpen_stdCoverAn_iff, SetLike.mem_coe, Opens.mem_inf, mem_tube,
    baseY_pointOfVec, mem_opensUI_iff]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, mem_range_chart_pointOfVec_iff]

/-- **`𝒪(k)^an` is acyclic on the intersections of the standard cover of `B × ℙᴺ`**, `B` an open
box (from Theorem B for `𝒪`, since `𝒪(k)^an` is trivial on each chart). -/
lemma subsingleton_H_restrictOpen_cechOpen (a b : Fin m → ℂ) {B : Opens (Fin m → ℂ)}
    (hB : (B : Set (Fin m → ℂ)) = Complex.openBox a b) (k : ℤ) {p : ℕ}
    (σ : Fin (p + 1) → ULift.{u} (Fin (N + 1))) (q : ℕ) (hq : 0 < q) :
    Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen
      (TopCat.Presheaf.cechOpen (stdCoverAn B) σ)).obj (twistingSheafAn.{u} m N k).toAb) q) := by
  have e := restrictOpenTwistingSheafAnIso k (TopCat.Presheaf.cechOpen (stdCoverAn B) σ)
    (σ 0).down ((iInf_le _ 0).trans inf_le_right)
  refine (TopCat.Sheaf.H.addEquivOfIso e q).toEquiv.subsingleton_congr.2 ?_
  rw [cechOpen_stdCoverAn B σ]
  exact subsingleton_H_tube_inf_opensUI a b hB (SimplexCochain.im_nonempty _) q hq

/-- **`Hᵠ(B × ℙᴺ, 𝒪(k)^an) = 0` for `q ≥ 1` and `k ≥ -N`**, `B` an open box. -/
theorem H_tube_twistingSheafAn_eq_zero (a b : Fin m → ℂ) {B : Opens (Fin m → ℂ)}
    (hB : (B : Set (Fin m → ℂ)) = Complex.openBox a b) (k : ℤ) (hk : -(N : ℤ) ≤ k) (q : ℕ)
    (x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (tube.{u} (N := N) B)).obj
      (twistingSheafAn.{u} m N k).toAb) (q + 1)) : x = 0 :=
  TopCat.Sheaf.H_restrictOpen_eq_zero_of_isCechAcyclic (stdCoverAn B) (iSup_stdCoverAn B) _
    (fun _ σ q' _ ↦ (subsingleton_H_restrictOpen_cechOpen a b hB k σ (q' + 1)
      q'.succ_pos).elim _ _)
    (isCechAcyclic_twistingSheafAn B k hk) q x

/-! ### Sections over `D × ℙᴺ` -/

/-- `Γ(D × ℙᴺ, 𝒪(k)^an)` is the kernel of the first differential of the parametric Čech
complex `CechProjectiveBox.holPD k D`. -/
noncomputable def tubeSectionsEquivKer (D : Opens (Fin m → ℂ)) (k : ℤ) :
    (twistingSheafAn.{u} m N k).toAb.obj.obj (op (tube D)) ≃+
      (holPD k D (n := N) 0).toAddMonoidHom.ker :=
  (TopCat.Presheaf.cechAugmentAddEquivKer (stdCoverAn D) (stdCoverAn_le D) _
      (iSup_stdCoverAn D).ge).trans
    (projectiveSpaceAn.kerAddEquivOfComm (cechCochainEquivAn D k 0) (cechCochainEquivAn D k 1)
      _ _ (cechCochainEquivAn_cechD D k 0))

/-- The `0`-cocycles of the parametric Čech complex of `𝒪(e)`, `e ≥ 0`, are the families,
indexed by the monomials of degree `e`, of holomorphic functions on `D`. -/
noncomputable def monoExpEquivKer (D : Opens (Fin m → ℂ)) (e : ℕ) :
    (MonoExp N e → OkaRing D) ≃+ (holPD (e : ℤ) D (n := N) 0).toAddMonoidHom.ker :=
  AddEquiv.ofBijective
    ({ toFun c := ⟨holPAug N D e c, holPD_holPAug c⟩
       map_zero' := Subtype.ext (map_zero _)
       map_add' c c' := Subtype.ext (map_add _ c c') } :
      (MonoExp N e → OkaRing D) →+ (holPD (e : ℤ) D (n := N) 0).toAddMonoidHom.ker)
    ⟨fun c c' h ↦ holPAug_injective e (congrArg Subtype.val h), fun x ↦ by
      obtain ⟨c, hc⟩ := (holPAug_exact e x.1).1 x.2
      exact ⟨c, Subtype.ext hc⟩⟩

/-- **`Γ(D × ℙᴺ, 𝒪(e)^an)` for `e ≥ 0`**: the sections are the functions
`(v, y) ↦ ∑_{|s| = e} c_s(y) vˢ` with `c_s` holomorphic on `D`. -/
noncomputable def tubeSectionsEquiv (D : Opens (Fin m → ℂ)) (e : ℕ) :
    (twistingSheafAn.{u} m N e).toAb.obj.obj (op (tube D)) ≃+ (MonoExp N e → OkaRing D) :=
  (tubeSectionsEquivKer D e).trans (monoExpEquivKer D e).symm

end ComplexAnalytic.relProjectiveSpaceAn

end
