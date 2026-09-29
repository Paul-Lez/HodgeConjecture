/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.Tactic.LinearCombination
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Exactness of the Čech complex of a module for a unit-ideal family

Material for `Mathlib/RingTheory/LocalProperties/Exactness.lean`; see `README.md` on the mirror
tree. Nothing here is complex-analytic.

Let `M` be a module over a commutative ring `R` and `f : ι → R` a family. The Čech complex of `M`
for `f` (the Čech complex of `M~` on `Spec R` for the cover by the `D(f i)`) has degree-`n` term
`cechObj M f n = ∏_{i : Fin (n + 1) → ι} M_{f (i 0) ⋯ f (i n)}`, where
`M_a = LocalizedModule (Submonoid.powers a) M`, and differential
`(cechD M f n x) i = ∑ₖ (-1) ^ k • x (i ∘ Fin.succAbove k)`, the restriction maps being
`awayMap M : M_a → M_b` for `a ∣ b ^ m`. The augmentation is `cechAug M f : M → cechObj M f 0`.

If `Ideal.span (Set.range f) = ⊤` and `ι` is finite, the augmented complex
`0 → M → cechObj M f 0 → cechObj M f 1 → ⋯` is exact. Exactness is checked after inverting each
`f j` (`exact_of_isLocalized_span`); inverting `f j` in the Čech complex of `f` gives the Čech
complex of `fun i ↦ f j * f i` (`isLocalizedModule_cechMap`), which is contracted by the homotopy
`x ↦ (i ↦ x (Fin.cons j i))` (`cechD_cechHtpy_add`).

## Main definitions

- `LocalizedModule.awayMap`: the restriction `M_a → M_b` when `a ∣ b ^ n`.
- `LocalizedModule.cechObj`, `LocalizedModule.cechD`, `LocalizedModule.cechAug`: the terms, the
  differential and the augmentation of the Čech complex.
- `LocalizedModule.cechCosimplicial`: the Čech cochains as a cosimplicial `R`-module;
  `LocalizedModule.cechComplex` its alternating coface map complex, with `d = cechD`.

## Main results

- `LocalizedModule.cechD_cechD`: `d ∘ d = 0`.
- `LocalizedModule.cechD_exact`: `Function.Exact (cechD M f n) (cechD M f (n + 1))`.
- `LocalizedModule.cechAug_injective`, `LocalizedModule.cechAug_exact`,
  `LocalizedModule.cechAugEquivKer`: `M ≅ ker (cechD M f 0)`.
- `LocalizedModule.cechComplex_exactAt`: `cechComplex M f` is exact in positive degrees.
-/

@[expose] public section

open CategoryTheory Submonoid Simplicial

namespace LocalizedModule

universe u v w

variable {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

lemma isUnit_algebraMap_of_dvd {N : Type*} [AddCommGroup N] [Module R N] {a b : R} (h : a ∣ b)
    (hb : IsUnit (algebraMap R (Module.End R N) b)) :
    IsUnit (algebraMap R (Module.End R N) a) := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul] at hb
  exact ((Commute.all a c).map (algebraMap R (Module.End R N)) |>.isUnit_mul_iff.mp hb).1

lemma isUnit_algebraMap_of_dvd_pow {a b : R} (h : ∃ n, a ∣ b ^ n) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule (powers b) M)) a) := by
  obtain ⟨n, hn⟩ := h
  refine isUnit_algebraMap_of_dvd hn ?_
  rw [map_pow]
  exact (IsLocalizedModule.Away.isUnit_algebraMap (mkLinearMap (powers b) M) b).pow n

lemma isUnit_algebraMap_of_mem_powers {a b : R} (h : ∃ n, a ∣ b ^ n) (s : powers a) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule (powers b) M)) s) := by
  obtain ⟨_, k, rfl⟩ := s
  rw [map_pow]
  exact (isUnit_algebraMap_of_dvd_pow M h).pow k

lemma exists_dvd_pow_trans {a b c : R} (h : ∃ n, a ∣ b ^ n) (h' : ∃ n, b ∣ c ^ n) :
    ∃ n, a ∣ c ^ n := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, hm⟩ := h'
  exact ⟨m * n, hn.trans (by rw [pow_mul]; exact pow_dvd_pow_of_dvd hm n)⟩

/-- The restriction map `M_a → M_b` between localisations away from `a` and `b`, defined whenever
`a` divides a power of `b` (i.e. `D(b) ⊆ D(a)`). -/
noncomputable def awayMap {a b : R} (h : ∃ n, a ∣ b ^ n) :
    LocalizedModule (powers a) M →ₗ[R] LocalizedModule (powers b) M :=
  lift (powers a) (mkLinearMap (powers b) M) (isUnit_algebraMap_of_mem_powers M h)

@[simp]
lemma awayMap_comp_mkLinearMap {a b : R} (h : ∃ n, a ∣ b ^ n) :
    awayMap M h ∘ₗ mkLinearMap (powers a) M = mkLinearMap (powers b) M :=
  lift_comp _ _ _

@[simp]
lemma awayMap_mk_one {a b : R} (h : ∃ n, a ∣ b ^ n) (m : M) :
    awayMap M h (mk m 1) = mk m 1 :=
  lift_mk_one _ _ _ m

lemma awayMap_mk {a b : R} (h : ∃ n, a ∣ b ^ n) (m : M) (s : powers a) (t : powers b) (e : R)
    (he : (t : R) = s * e) : awayMap M h (mk m s) = mk (e • m) t := by
  apply ((Module.End.isUnit_iff _).mp (isUnit_algebraMap_of_mem_powers M h s)).1
  simp only [Module.algebraMap_end_apply]
  rw [← map_smul, smul'_mk, smul'_mk, ← Submonoid.smul_def, mk_cancel, awayMap_mk_one, smul_smul,
    ← he, ← Submonoid.smul_def, mk_cancel]

@[simp]
lemma awayMap_awayMap {a b c : R} (h : ∃ n, a ∣ b ^ n) (h' : ∃ n, b ∣ c ^ n) (x) :
    awayMap M h' (awayMap M h x) = awayMap M (exists_dvd_pow_trans h h') x := by
  have : awayMap M h' ∘ₗ awayMap M h = awayMap M (exists_dvd_pow_trans h h') :=
    IsLocalizedModule.ext (powers a) (mkLinearMap (powers a) M)
      (isUnit_algebraMap_of_mem_powers M (exists_dvd_pow_trans h h'))
      (by rw [LinearMap.comp_assoc]; simp)
  exact LinearMap.congr_fun this x

@[simp]
lemma awayMap_self {a : R} (h : ∃ n, a ∣ a ^ n) (x) : awayMap M h x = x := by
  have : awayMap M h = LinearMap.id :=
    IsLocalizedModule.ext (powers a) (mkLinearMap (powers a) M)
      (isUnit_algebraMap_of_mem_powers M h) (by simp)
  exact LinearMap.congr_fun this x

/-- Transport of a restriction along an equality of indices. -/
lemma awayMap_congr {κ : Type*} {w : κ → R} (x : ∀ k, LocalizedModule (powers (w k)) M)
    {k k' : κ} (e : k = k') {b : R} (h : ∃ n, w k ∣ b ^ n) :
    awayMap M h (x k) = awayMap M (e ▸ h) (x k') := by
  subst e; rfl

/-- If `D(b) = D(c) ∩ D(a)`, then `M_a → M_b` is the localisation away from `c`. -/
lemma isLocalizedModule_awayMap {a b c : R} (h : ∃ n, a ∣ b ^ n) (hc : ∃ n, c ∣ b ^ n)
    (hb : ∃ n, b ∣ (c * a) ^ n) : IsLocalizedModule (powers c) (awayMap M h) := by
  obtain ⟨n₀, hn₀⟩ := h
  obtain ⟨N, hN⟩ := hb
  refine IsLocalizedModule.Away.mk_of_addCommGroup
    (isUnit_algebraMap_of_dvd_pow M hc) (fun y ↦ ?_) (fun x hx ↦ ?_)
  · induction y using LocalizedModule.induction_on with | h m s => ?_
    obtain ⟨_, t, rfl⟩ := s
    obtain ⟨d, hd⟩ := pow_dvd_pow_of_dvd hN t
    obtain ⟨e, he⟩ := pow_dvd_pow_of_dvd hn₀ (N * t)
    refine ⟨N * t, mk (d • m) ⟨a ^ (N * t), N * t, rfl⟩, ?_⟩
    rw [awayMap_mk M ⟨n₀, hn₀⟩ _ _ ⟨_, n₀ * (N * t), rfl⟩ e (by simpa [pow_mul] using he),
      smul'_mk, mk_eq]
    refine ⟨1, ?_⟩
    simp only [Submonoid.smul_def, one_smul, smul_smul]
    congr 1
    simp only [← pow_mul] at he hd ⊢
    linear_combination c ^ (N * t) * he + e * hd
  · induction x using LocalizedModule.induction_on with | h m s => ?_
    obtain ⟨_, t, rfl⟩ := s
    obtain ⟨e, he⟩ := pow_dvd_pow_of_dvd hn₀ t
    rw [awayMap_mk M ⟨n₀, hn₀⟩ _ _ ⟨_, n₀ * t, rfl⟩ e (by simpa [pow_mul] using he),
      ← zero_mk 1, mk_eq] at hx
    obtain ⟨⟨_, v, rfl⟩, hv⟩ := hx
    simp only [Submonoid.smul_def, one_smul, smul_zero] at hv
    obtain ⟨d, hd⟩ := pow_dvd_pow_of_dvd hN (v + n₀ * t)
    refine ⟨N * (v + n₀ * t), ?_⟩
    rw [smul'_mk, ← zero_mk (⟨a ^ t, t, rfl⟩ : powers a), mk_eq]
    refine ⟨⟨a ^ (N * (v + n₀ * t)), _, rfl⟩, ?_⟩
    simp only [Submonoid.smul_def, smul_zero, smul_smul] at hv ⊢
    have key : a ^ (N * (v + n₀ * t)) * (a ^ t * c ^ (N * (v + n₀ * t))) =
        a ^ t * d * a ^ t * (b ^ v * e) := by
      simp only [← pow_mul] at he hd
      linear_combination a ^ t * hd + a ^ t * d * b ^ v * he
    rw [key, ← smul_smul, hv, smul_zero]

/-! ### The Čech complex -/

variable {ι : Type w} (f : ι → R)

/-- The degree-`n` term of the Čech complex of `M` for the family `f`:
`∏_{i : Fin (n + 1) → ι} M_{f (i 0) ⋯ f (i n)}`. -/
abbrev cechObj (n : ℕ) : Type _ :=
  ∀ i : Fin (n + 1) → ι, LocalizedModule (powers (∏ a, f (i a))) M

lemma exists_prod_comp_dvd_pow {m n : ℕ} (i : Fin n → ι) (θ : Fin m → Fin n) :
    ∃ k, ∏ a, f (i (θ a)) ∣ (∏ a, f (i a)) ^ k := by
  refine ⟨m, ?_⟩
  have : (∏ a, f (i a)) ^ m = ∏ _b : Fin m, ∏ a, f (i a) := by simp
  rw [this]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun a _ ↦ Finset.dvd_prod_of_mem _ (Finset.mem_univ _)

variable {M} in
/-- The restriction of a Čech cochain along a map `θ : Fin (m + 1) → Fin (n + 1)`:
`(cechRestrict f θ x) i = x (i ∘ θ)` restricted to `D(f_i)`. -/
noncomputable def cechRestrict {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) :
    cechObj M f m →ₗ[R] cechObj M f n :=
  LinearMap.pi fun i ↦ awayMap M (exists_prod_comp_dvd_pow f i θ) ∘ₗ LinearMap.proj fun a ↦ i (θ a)

@[simp]
lemma cechRestrict_apply {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) (x : cechObj M f m)
    (i : Fin (n + 1) → ι) :
    cechRestrict f θ x i = awayMap M (exists_prod_comp_dvd_pow f i θ) (x fun a ↦ i (θ a)) :=
  rfl

/-- The Čech differential `cechObj M f n → cechObj M f (n + 1)`,
`(d x) i = ∑ₖ (-1) ^ k • x (i ∘ δₖ)` where `δₖ = Fin.succAbove k` skips `k`. -/
noncomputable def cechD (n : ℕ) : cechObj M f n →ₗ[R] cechObj M f (n + 1) :=
  ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) • cechRestrict f k.succAbove

@[simp]
lemma cechD_apply (n : ℕ) (x : cechObj M f n) (i : Fin (n + 2) → ι) :
    cechD M f n x i = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
      awayMap M (exists_prod_comp_dvd_pow f i k.succAbove) (x fun a ↦ i (k.succAbove a)) := by
  simp only [cechD, LinearMap.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ ↦ rfl

@[simp]
lemma cechRestrict_id (n : ℕ) (x : cechObj M f n) : cechRestrict f id x = x := by
  ext i
  exact awayMap_self M (exists_prod_comp_dvd_pow f i id) _

@[simp]
lemma cechRestrict_cechRestrict {l m n : ℕ} (θ : Fin (l + 1) → Fin (m + 1))
    (θ' : Fin (m + 1) → Fin (n + 1)) (x : cechObj M f l) :
    cechRestrict f θ' (cechRestrict f θ x) = cechRestrict f (fun a ↦ θ' (θ a)) x := by
  ext i
  exact awayMap_awayMap M (exists_prod_comp_dvd_pow f (fun a ↦ i (θ' a)) θ)
    (exists_prod_comp_dvd_pow f i θ') _

/-- The Čech cochains as a cosimplicial module: `⦋n⦌ ↦ cechObj M f n`, with a monotone map
`θ : ⦋m⦌ ⟶ ⦋n⦌` acting by `cechRestrict f θ`. -/
@[simps]
noncomputable def cechCosimplicial : CosimplicialObject (ModuleCat.{max u v w} R) where
  obj Δ := ModuleCat.of R (cechObj M f Δ.len)
  map θ := ModuleCat.ofHom (cechRestrict f θ.toOrderHom)
  map_id Δ := by ext x : 2; exact cechRestrict_id M f _ x
  map_comp θ θ' := by
    ext x : 2
    exact (cechRestrict_cechRestrict M f θ.toOrderHom θ'.toOrderHom x).symm

lemma cechCosimplicial_δ (n : ℕ) (k : Fin (n + 2)) :
    (cechCosimplicial M f).δ k = ModuleCat.ofHom (cechRestrict f k.succAbove) :=
  rfl

/-- `cechD` is the differential of the alternating coface map complex of `cechCosimplicial`. -/
lemma cechD_eq_objD (n : ℕ) : cechD M f n =
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cechCosimplicial M f) n).hom := by
  simp only [cechD, AlgebraicTopology.AlternatingCofaceMapComplex.objD, cechCosimplicial_δ,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul]
  rfl

@[simp]
lemma cechD_cechD (n : ℕ) (x : cechObj M f n) : cechD M f (n + 1) (cechD M f n x) = 0 := by
  have h := congrArg
    (fun φ : (cechCosimplicial M f).obj ⦋n⦌ ⟶ (cechCosimplicial M f).obj ⦋n + 2⦌ ↦ φ.hom x)
    (AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (cechCosimplicial M f) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at h
  rw [cechD_eq_objD, cechD_eq_objD]
  exact h

/-! ### The augmentation -/

/-- The augmentation `M → cechObj M f 0`, `m ↦ (i ↦ m / 1)`. -/
noncomputable def cechAug : M →ₗ[R] cechObj M f 0 :=
  LinearMap.pi fun _ ↦ mkLinearMap _ M

@[simp]
lemma cechAug_apply (m : M) (i : Fin 1 → ι) : cechAug M f m i = mk m 1 :=
  rfl

@[simp]
lemma cechD_cechAug (m : M) : cechD M f 0 (cechAug M f m) = 0 := by
  ext i
  simp [cechD_apply, Fin.sum_univ_succ]

lemma exists_dvd_pow_prod_fin_one {c : R} (hc : ∀ i, ∃ n, c ∣ f i ^ n) (i : Fin 1 → ι) :
    ∃ n, c ∣ (∏ a, f (i a)) ^ n := by
  simpa using hc (i 0)

variable {M f} in
/-- The augmentation `M_c → cechObj M f 0` out of a localisation `M_c` with `D(f i) ⊆ D(c)` for
all `i`. -/
noncomputable def cechAugAway {c : R} (hc : ∀ i, ∃ n, c ∣ f i ^ n) :
    LocalizedModule (powers c) M →ₗ[R] cechObj M f 0 :=
  LinearMap.pi fun i ↦ awayMap M (exists_dvd_pow_prod_fin_one f hc i)

@[simp]
lemma cechAugAway_apply {c : R} (hc : ∀ i, ∃ n, c ∣ f i ^ n) (x : LocalizedModule (powers c) M)
    (i : Fin 1 → ι) : cechAugAway hc x i = awayMap M (exists_dvd_pow_prod_fin_one f hc i) x :=
  rfl

@[simp]
lemma cechD_cechAugAway {c : R} (hc : ∀ i, ∃ n, c ∣ f i ^ n) (x : LocalizedModule (powers c) M) :
    cechD M f 0 (cechAugAway hc x) = 0 := by
  ext i
  simp [cechD_apply, Fin.sum_univ_succ]

/-! ### Changing the family -/

variable {f} in
lemma exists_prod_dvd_prod_pow {g : ι → R} (h : ∀ i, f i ∣ g i) {n : ℕ} (i : Fin n → ι) :
    ∃ k, ∏ a, f (i a) ∣ (∏ a, g (i a)) ^ k :=
  ⟨1, by rw [pow_one]; exact Finset.prod_dvd_prod_of_dvd _ _ fun a _ ↦ h (i a)⟩

variable {f} in
/-- The componentwise restriction `cechObj M f n → cechObj M g n` when `f i ∣ g i` for all `i`. -/
noncomputable def cechMap {g : ι → R} (h : ∀ i, f i ∣ g i) (n : ℕ) :
    cechObj M f n →ₗ[R] cechObj M g n :=
  LinearMap.pi fun i ↦ awayMap M (exists_prod_dvd_prod_pow h i) ∘ₗ LinearMap.proj i

@[simp]
lemma cechMap_apply {g : ι → R} (h : ∀ i, f i ∣ g i) (n : ℕ) (x : cechObj M f n)
    (i : Fin (n + 1) → ι) : cechMap M h n x i = awayMap M (exists_prod_dvd_prod_pow h i) (x i) :=
  rfl

@[simp]
lemma cechMap_cechD {g : ι → R} (h : ∀ i, f i ∣ g i) (n : ℕ) (x : cechObj M f n) :
    cechMap M h (n + 1) (cechD M f n x) = cechD M g n (cechMap M h n x) := by
  ext i
  simp [cechD_apply, map_sum, map_zsmul]

@[simp]
lemma cechMap_cechAug {g : ι → R} (h : ∀ i, f i ∣ g i) (m : M) :
    cechMap M h 0 (cechAug M f m) = cechAug M g m := by
  ext i
  simp

/-- Restricting from `f` to `c • f` localises the Čech cochains away from `c`. -/
instance isLocalizedModule_cechMap [Finite ι] (c : R) (n : ℕ) :
    IsLocalizedModule (powers c) (cechMap M (fun i ↦ dvd_mul_left (f i) c) n) := by
  have (i : Fin (n + 1) → ι) : IsLocalizedModule (powers c)
      (awayMap M (exists_prod_dvd_prod_pow (fun i ↦ dvd_mul_left (f i) c) i)) := by
    have hprod : ∏ a, c * f (i a) = c ^ (n + 1) * ∏ a, f (i a) := by
      simp [Finset.prod_mul_distrib]
    refine isLocalizedModule_awayMap M _ ⟨1, ?_⟩ ⟨n + 1, ?_⟩
    · rw [pow_one, hprod]
      exact dvd_mul_of_dvd_left (dvd_pow_self c n.succ_ne_zero) _
    · rw [hprod, mul_pow]
      exact mul_dvd_mul_left _ (dvd_pow_self _ n.succ_ne_zero)
  exact IsLocalizedModule.pi (S := powers c)
    (fun i ↦ awayMap M (exists_prod_dvd_prod_pow (fun i ↦ dvd_mul_left (f i) c) i))

/-! ### The contracting homotopy when some `D(f j)` contains all `D(f i)` -/

section Homotopy

variable {f} {j : ι} (hj : ∀ i, ∃ m, f j ∣ f i ^ m)
include hj

lemma exists_prod_cons_dvd_pow {n : ℕ} (i : Fin (n + 1) → ι) :
    ∃ m, ∏ a, f ((Fin.cons j i : Fin (n + 2) → ι) a) ∣ (∏ a, f (i a)) ^ m := by
  obtain ⟨m, hm⟩ := hj (i 0)
  refine ⟨m + 1, ?_⟩
  rw [Fin.prod_univ_succ, pow_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  exact mul_dvd_mul (hm.trans (pow_dvd_pow_of_dvd
    (Finset.dvd_prod_of_mem (fun a ↦ f (i a)) (Finset.mem_univ 0)) m)) dvd_rfl

/-- The contracting homotopy `(h x) i = x (j, i₀, …, iₙ)` of the Čech complex, for a family in
which `D(f j) ⊇ D(f i)` for all `i`. -/
noncomputable def cechHtpy (n : ℕ) : cechObj M f (n + 1) →ₗ[R] cechObj M f n :=
  LinearMap.pi fun i ↦
    awayMap M (exists_prod_cons_dvd_pow hj i) ∘ₗ LinearMap.proj (Fin.cons j i : Fin (n + 2) → ι)

@[simp]
lemma cechHtpy_apply (n : ℕ) (x : cechObj M f (n + 1)) (i : Fin (n + 1) → ι) :
    cechHtpy M hj n x i =
      awayMap M (exists_prod_cons_dvd_pow hj i) (x (Fin.cons j i : Fin (n + 2) → ι)) :=
  rfl

omit hj in
lemma exists_prod_const_dvd_pow {c : R} (hjc : ∃ k, f j ∣ c ^ k) :
    ∃ k, ∏ _a : Fin 1, f j ∣ c ^ k := by
  simpa using hjc

omit hj in
/-- The contracting homotopy in degree `0`, `x ↦ x (j)`, with values in a localisation `M_c` with
`D(c) ⊆ D(f j)`. -/
noncomputable def cechHtpy₀ {c : R} (hjc : ∃ k, f j ∣ c ^ k) :
    cechObj M f 0 →ₗ[R] LocalizedModule (powers c) M :=
  awayMap M (exists_prod_const_dvd_pow hjc) ∘ₗ LinearMap.proj fun _ ↦ j

omit hj in
@[simp]
lemma cechHtpy₀_apply {c : R} (hjc : ∃ k, f j ∣ c ^ k) (x : cechObj M f 0) :
    cechHtpy₀ M hjc x = awayMap M (exists_prod_const_dvd_pow hjc) (x fun _ ↦ j) :=
  rfl

lemma cechD_cechHtpy_add (n : ℕ) (x : cechObj M f (n + 1)) :
    cechD M f n (cechHtpy M hj n x) + cechHtpy M hj (n + 1) (cechD M f (n + 1) x) = x := by
  ext i
  simp only [Pi.add_apply, cechD_apply, cechHtpy_apply, map_sum, map_zsmul, awayMap_awayMap]
  rw [Fin.sum_univ_succ (n := n + 2)]
  have e0 : (fun a ↦ (Fin.cons j i : Fin (n + 3) → ι) ((0 : Fin (n + 3)).succAbove a)) = i := by
    ext a; simp
  have e1 (k : Fin (n + 2)) : (fun a ↦ (Fin.cons j i : Fin (n + 3) → ι) (k.succ.succAbove a)) =
      (Fin.cons j (fun a ↦ i (k.succAbove a)) : Fin (n + 2) → ι) := by
    ext a
    cases a using Fin.cases <;> simp
  rw [awayMap_congr M x e0, awayMap_self]
  have hs : ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k.succ : ℕ)) • awayMap M
      (exists_dvd_pow_trans
        (exists_prod_comp_dvd_pow f (Fin.cons j i : Fin (n + 3) → ι) k.succ.succAbove)
        (exists_prod_cons_dvd_pow hj i))
      (x fun a ↦ (Fin.cons j i : Fin (n + 3) → ι) (k.succ.succAbove a)) =
      -∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) • awayMap M
        (exists_dvd_pow_trans (exists_prod_cons_dvd_pow hj fun a ↦ i (k.succAbove a))
          (exists_prod_comp_dvd_pow f i k.succAbove))
        (x (Fin.cons j (fun a ↦ i (k.succAbove a)) : Fin (n + 2) → ι)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [awayMap_congr M x (e1 k), Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
  rw [hs, Fin.val_zero, pow_zero, one_smul]
  abel

variable {c : R} (hjc : ∃ k, f j ∣ c ^ k) (hc : ∀ i, ∃ n, c ∣ f i ^ n)
include hjc

omit hj in
lemma cechHtpy₀_cechAugAway (y : LocalizedModule (powers c) M) :
    cechHtpy₀ M hjc (cechAugAway hc y) = y := by
  simp

lemma cechAugAway_cechHtpy₀_add (x : cechObj M f 0) :
    cechAugAway hc (cechHtpy₀ M hjc x) + cechHtpy M hj 0 (cechD M f 0 x) = x := by
  ext i
  simp only [Pi.add_apply, cechAugAway_apply, cechHtpy₀_apply, cechD_apply, cechHtpy_apply,
    map_zsmul, awayMap_awayMap, Fin.sum_univ_succ, Fin.sum_univ_zero, map_add, map_zero]
  have e0 : (fun a ↦ (Fin.cons j i : Fin 2 → ι) ((0 : Fin 2).succAbove a)) = i := by
    ext a; simp
  have e1 : (fun a ↦ (Fin.cons j i : Fin 2 → ι) ((0 : Fin 1).succ.succAbove a)) = fun _ ↦ j := by
    ext a; simp [Fin.fin_one_eq_zero a]
  rw [awayMap_congr M x e0, awayMap_self, awayMap_congr M x e1]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, zero_add, pow_one, neg_smul,
    add_zero]
  abel

omit hjc in
/-- A Čech complex with a contracting homotopy is exact. -/
lemma cechD_exact_of_dvd (n : ℕ) : Function.Exact (cechD M f n) (cechD M f (n + 1)) := by
  intro y
  refine ⟨fun hy ↦ ⟨cechHtpy M hj n y, ?_⟩, ?_⟩
  · simpa [hy] using cechD_cechHtpy_add M hj n y
  · rintro ⟨x, rfl⟩
    exact cechD_cechD M f n x

omit hj in
lemma cechAugAway_injective : Function.Injective (cechAugAway (M := M) hc) :=
  Function.LeftInverse.injective (cechHtpy₀_cechAugAway M hjc hc)

lemma cechAugAway_exact : Function.Exact (cechAugAway (M := M) hc) (cechD M f 0) := by
  intro y
  refine ⟨fun hy ↦ ⟨cechHtpy₀ M hjc y, ?_⟩, ?_⟩
  · simpa [hy] using cechAugAway_cechHtpy₀_add M hj hjc hc y
  · rintro ⟨x, rfl⟩
    exact cechD_cechAugAway M f hc x

end Homotopy

/-! ### Exactness -/

section Exactness

variable [Finite ι]

lemma map_cechD (c : R) (n : ℕ) :
    IsLocalizedModule.map (powers c) (cechMap M (fun i ↦ dvd_mul_left (f i) c) n)
      (cechMap M (fun i ↦ dvd_mul_left (f i) c) (n + 1)) (cechD M f n) =
      cechD M (fun i ↦ c * f i) n := by
  refine IsLocalizedModule.ext (powers c) (cechMap M (fun i ↦ dvd_mul_left (f i) c) n)
    (IsLocalizedModule.map_units (cechMap M (fun i ↦ dvd_mul_left (f i) c) (n + 1))) ?_
  rw [IsLocalizedModule.map_comp]
  ext x : 1
  simp

omit [Finite ι] in
lemma exists_dvd_pow_mul_left (c : R) (i : ι) : ∃ n, c ∣ (c * f i) ^ n :=
  ⟨1, by rw [pow_one]; exact dvd_mul_right c (f i)⟩

lemma map_cechAug (c : R) :
    IsLocalizedModule.map (powers c) (mkLinearMap (powers c) M)
      (cechMap M (fun i ↦ dvd_mul_left (f i) c) 0) (cechAug M f) =
      cechAugAway (exists_dvd_pow_mul_left f c) := by
  refine IsLocalizedModule.ext (powers c) (mkLinearMap (powers c) M)
    (IsLocalizedModule.map_units (cechMap M (fun i ↦ dvd_mul_left (f i) c) 0)) ?_
  rw [IsLocalizedModule.map_comp]
  ext x i
  simp

omit [Finite ι] in
private lemma dvd_pow_mul_self (j i : ι) : ∃ m, f j * f j ∣ (f j * f i) ^ m :=
  ⟨2, Dvd.intro (f i ^ 2) (by ring)⟩

omit [Finite ι] in
private lemma dvd_pow_mul_self' (j : ι) : ∃ m, f j * f j ∣ f j ^ m :=
  ⟨2, by rw [sq]⟩

/-- **Exactness of the Čech complex**: if the `f i` generate the unit ideal, then the Čech complex
`∏ M_{f i} → ∏ M_{f i f j} → ⋯` is exact at `cechObj M f (n + 1)`. -/
theorem cechD_exact (hf : Ideal.span (Set.range f) = ⊤) (n : ℕ) :
    Function.Exact (cechD M f n) (cechD M f (n + 1)) := by
  refine exact_of_isLocalized_span (Set.range f) hf
    (fun r ↦ cechObj M (fun i ↦ r.1 * f i) n)
    (fun r ↦ cechMap M (fun i ↦ dvd_mul_left (f i) r.1) n)
    (fun r ↦ cechObj M (fun i ↦ r.1 * f i) (n + 1))
    (fun r ↦ cechMap M (fun i ↦ dvd_mul_left (f i) r.1) (n + 1))
    (fun r ↦ cechObj M (fun i ↦ r.1 * f i) (n + 2))
    (fun r ↦ cechMap M (fun i ↦ dvd_mul_left (f i) r.1) (n + 2)) _ _ fun r ↦ ?_
  obtain ⟨_, j, rfl⟩ := r
  rw [map_cechD, map_cechD]
  exact cechD_exact_of_dvd M (j := j) (dvd_pow_mul_self f j) n

/-- The augmentation `M → ∏ M_{f i}` is injective if the `f i` generate the unit ideal. -/
theorem cechAug_injective (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Injective (cechAug M f) := by
  refine injective_of_isLocalized_span (Set.range f) hf
    (fun r ↦ LocalizedModule (powers r.1) M) (fun r ↦ mkLinearMap (powers r.1) M)
    (fun r ↦ cechObj M (fun i ↦ r.1 * f i) 0)
    (fun r ↦ cechMap M (fun i ↦ dvd_mul_left (f i) r.1) 0) _ fun r ↦ ?_
  obtain ⟨_, j, rfl⟩ := r
  rw [map_cechAug]
  exact cechAugAway_injective M (f := fun i ↦ f j * f i) (j := j) (dvd_pow_mul_self' f j) _

/-- The augmented Čech complex is exact at `∏ M_{f i}`: a compatible family of sections over the
`D(f i)` comes from a unique element of `M` (see also `cechAug_injective`). -/
theorem cechAug_exact (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Exact (cechAug M f) (cechD M f 0) := by
  refine exact_of_isLocalized_span (Set.range f) hf
    (fun r ↦ LocalizedModule (powers r.1) M) (fun r ↦ mkLinearMap (powers r.1) M)
    (fun r ↦ cechObj M (fun i ↦ r.1 * f i) 0)
    (fun r ↦ cechMap M (fun i ↦ dvd_mul_left (f i) r.1) 0)
    (fun r ↦ cechObj M (fun i ↦ r.1 * f i) 1)
    (fun r ↦ cechMap M (fun i ↦ dvd_mul_left (f i) r.1) 1) _ _ fun r ↦ ?_
  obtain ⟨_, j, rfl⟩ := r
  rw [map_cechAug, map_cechD]
  exact cechAugAway_exact M (dvd_pow_mul_self f j) (dvd_pow_mul_self' f j) _

/-- If the `f i` generate the unit ideal, `M` is the kernel of the first Čech differential:
`M ≃ ker (∏ M_{f i} → ∏ M_{f i f j})`. -/
noncomputable def cechAugEquivKer (hf : Ideal.span (Set.range f) = ⊤) :
    M ≃ₗ[R] LinearMap.ker (cechD M f 0) :=
  LinearEquiv.ofBijective ((cechAug M f).codRestrict _ fun m ↦ cechD_cechAug M f m)
    ⟨fun _ _ h ↦ cechAug_injective M f hf (congrArg Subtype.val h),
      fun ⟨y, hy⟩ ↦ by
        obtain ⟨m, rfl⟩ := (cechAug_exact M f hf y).mp hy
        exact ⟨m, rfl⟩⟩

@[simp]
lemma cechAugEquivKer_apply_coe (hf : Ideal.span (Set.range f) = ⊤) (m : M) :
    (cechAugEquivKer M f hf m : cechObj M f 0) = cechAug M f m :=
  rfl

end Exactness

/-! ### The Čech complex as a cochain complex -/

/-- The Čech complex of `M` for the family `f`, as the alternating coface map complex of
`cechCosimplicial M f`. Its degree-`n` term is `cechObj M f n` and its differential is
`cechD M f n` (`cechComplex_X`, `cechComplex_d`). -/
noncomputable def cechComplex : CochainComplex (ModuleCat.{max u v w} R) ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj (cechCosimplicial M f)

lemma cechComplex_X (n : ℕ) : (cechComplex M f).X n = ModuleCat.of R (cechObj M f n) :=
  rfl

@[simp]
lemma cechComplex_d (n : ℕ) :
    (cechComplex M f).d n (n + 1) = ModuleCat.ofHom (cechD M f n) := by
  rw [cechD_eq_objD]
  exact CochainComplex.of_d (fun n ↦ (cechCosimplicial M f).obj ⦋n⦌)
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cechCosimplicial M f)) n

/-- The Čech complex is exact in every positive degree if the `f i` generate the unit ideal. -/
theorem cechComplex_exactAt [Finite ι] (hf : Ideal.span (Set.range f) = ⊤) (n : ℕ) :
    (cechComplex M f).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro y hy
  change ((cechComplex M f).d (n + 1) (n + 1 + 1)).hom y = 0 at hy
  change ∃ x, ((cechComplex M f).d n (n + 1)).hom x = y
  simp only [cechComplex_d] at hy ⊢
  exact (cechD_exact M f hf n y).mp hy

end LocalizedModule

end
