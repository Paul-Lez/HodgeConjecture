/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.SerreVanishing
public import Other.Oka.Analytification.GAGA.CohomologyComparison
public import Other.Oka.Analytification.GAGA.Proper.RelativeProjectiveVanishing
public import Other.Oka.Analytification.GAGA.Proper.RelativeTwistCechAn
public import Other.Oka.Topology.Sheaves.Cohomology.PushforwardAcyclic

/-!
# Relative analytic Serre vanishing over boxes

Let `P = ℙₒ(N; ℂ[y₀, …, y_{m-1}])` and `G` a coherent sheaf on `P`. We show that there is `n₀`,
depending only on `G`, such that `Hᵠ(B × ℙᴺ, G(n)^an) = 0` for all `q ≥ 1`, `n ≥ n₀` and all
open boxes `B ⊆ ℂᵐ` (`ComplexAnalytic.relProjectiveSpaceAn.exists_H_tube_twist_eq_zero`), where
`B × ℙᴺ = tube B` is the preimage of `B` in `P^an`.

The proof is Serre's descending induction on `q`, with algebraic input: for `q > N` the
cohomology of every analytified coherent sheaf vanishes on `tube B`
(`ComplexAnalytic.relProjectiveSpaceAn.subsingleton_H_tube_analytificationModules`). For smaller
`q ≥ 1`, Theorem A on `P` gives `0 → K → ⊕ 𝒪(-m₁) → G → 0` with `K` coherent; twisting by `n`,
analytifying and restricting to `tube B` are exact, `Hᵠ(tube B, 𝒪(n - m₁)^an) = 0` for `q ≥ 1`
once `n - m₁ ≥ -N` (`ComplexAnalytic.relProjectiveSpaceAn.H_tube_twistingSheafAn_eq_zero`), and
`Hᵠ⁺¹(tube B, K(n)^an) = 0` for `n ≫ 0` by induction. All bounds come from the algebraic
presentations, so they do not depend on `B`.

Since the open boxes form a neighbourhood basis of `ℂᵐ` (`exists_openBox_subset`), `G(n)^an` is
then acyclic for the analytification of `P ⟶ 𝔸ᵐ`, i.e. its higher direct images vanish
(`ComplexAnalytic.relProjectiveSpaceAn.exists_isPushforwardAcyclic_twist`).
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry.ProjectiveSpace

universe u

namespace ComplexAnalytic.relProjectiveSpaceAn

open ProjectiveSpace

variable {m N : ℕ}

/-- Cohomology of the image of a finite coproduct under an additive functor to abelian sheaves
vanishes in degree `q` if it vanishes on the images of all summands. -/
lemma H_map_sigma_eq_zero {C : Type*} [Category C] [Preadditive C] {Y : TopCat.{u}}
    (T : C ⥤ TopCat.AbSheaf Y) [T.Additive] {I : Type u} [Finite I] (G : I → C)
    [HasCoproduct G] (q : ℕ) (h : ∀ i (x : TopCat.Sheaf.H (T.obj (G i)) q), x = 0)
    (x : TopCat.Sheaf.H (T.obj (∐ G)) q) : x = 0 := by
  have := Fintype.ofFinite I
  have := HasBiproduct.of_hasCoproduct G
  let e := T.mapIso (biproduct.isoCoproduct G)
  suffices hy : ∀ y : TopCat.Sheaf.H (T.obj (⨁ G)) q, y = 0 by
    have hx : x = TopCat.Sheaf.H.map e.hom q (TopCat.Sheaf.H.map e.inv q x) := by
      rw [← TopCat.Sheaf.H.map_comp_apply, e.inv_hom_id, TopCat.Sheaf.H.map_id_apply]
    rw [hx, hy (TopCat.Sheaf.H.map e.inv q x)]
    exact map_zero _
  intro y
  have htot : ∑ i, biproduct.π G i ≫ biproduct.ι G i = 𝟙 (⨁ G) :=
    IsBilimit.total (biproduct.isBilimit G)
  have hsum : ∀ (s : Finset I) (φ : I → (⨁ G ⟶ ⨁ G)),
      TopCat.Sheaf.H.map (T.map (∑ i ∈ s, φ i)) q y =
        ∑ i ∈ s, TopCat.Sheaf.H.map (T.map (φ i)) q y := by
    classical
    intro s φ
    induction s using Finset.induction_on with
    | empty => simp [TopCat.Sheaf.H.map_zero_apply]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, T.map_add,
        TopCat.Sheaf.H.map_add_apply, ih]
  rw [← TopCat.Sheaf.H.map_id_apply y, ← T.map_id, ← htot, hsum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [T.map_comp, TopCat.Sheaf.H.map_comp_apply, h i (TopCat.Sheaf.H.map _ q y), map_zero]

variable (m N) in
/-- `G ↦ G^an|_{tube D}`: analytification, followed by the underlying abelian sheaf, restricted
to `tube D = D × ℙᴺ`. -/
noncomputable abbrev tubeAb (D : Opens (Fin m → ℂ)) :
    ℙₒ(N; RelBase.{u} m).Modules ⥤
      TopCat.AbSheaf ((Opens.toTopCat (relProjectiveSpaceAn.{u} m N).toPresheafedSpace).obj
        (tube.{u} (N := N) D)) :=
  analytificationModules (relProjectiveSpace.{u} m N) ⋙
    LocallyRingedSpace.modulesToAb _ ⋙ TopCat.Sheaf.restrictOpen (tube.{u} (N := N) D)

instance (D : Opens (Fin m → ℂ)) : (tubeAb.{u} m N D).Additive := by
  haveI : (analytificationModules (relProjectiveSpace.{u} m N)).Additive :=
    Functor.additive_of_preserves_binary_products _
  exact (inferInstance : (analytificationModules (relProjectiveSpace.{u} m N) ⋙
    LocallyRingedSpace.modulesToAb _ ⋙ TopCat.Sheaf.restrictOpen (tube.{u} (N := N) D)).Additive)

lemma shortExact_map_tubeAb (D : Opens (Fin m → ℂ))
    {S : ShortComplex ℙₒ(N; RelBase.{u} m).Modules} (hS : S.ShortExact) :
    (S.map (tubeAb.{u} m N D)).ShortExact :=
  ((shortExact_map_analytificationModules (X := relProjectiveSpace.{u} m N) hS).map_of_exact
    (LocallyRingedSpace.modulesToAb _)).map_of_exact (TopCat.Sheaf.restrictOpen _)

/-- `Hᵠ(B × ℙᴺ, 𝒪^I(k)^an) = 0` for `q ≥ 1`, `I` finite, `k ≥ -N` and `B` an open box. -/
lemma H_tube_twist_free_eq_zero (a b : Fin m → ℂ) {B : Opens (Fin m → ℂ)}
    (hB : (B : Set (Fin m → ℂ)) = Complex.openBox a b) {I : Type u} [Finite I] (k : ℤ)
    (hk : -(N : ℤ) ≤ k) (q : ℕ)
    (x : TopCat.Sheaf.H ((tubeAb.{u} m N B).obj
      (twist (SheafOfModules.free I : ℙₒ(N; RelBase.{u} m).Modules) k)) (q + 1)) : x = 0 := by
  let e := (tubeAb.{u} m N B).mapIso (twistFreeIso (n := N) (R := RelBase.{u} m) I k)
  have hx : x = TopCat.Sheaf.H.map e.inv (q + 1) (TopCat.Sheaf.H.map e.hom (q + 1) x) := by
    rw [← TopCat.Sheaf.H.map_comp_apply, e.hom_inv_id, TopCat.Sheaf.H.map_id_apply]
  have h0 : TopCat.Sheaf.H.map e.hom (q + 1) x = 0 :=
    H_map_sigma_eq_zero (tubeAb.{u} m N B) _ (q + 1)
      (fun _ y ↦ H_tube_twistingSheafAn_eq_zero a b hB k hk q y) _
  rw [hx, h0]
  exact map_zero _

/-- The descending induction behind relative analytic Serre vanishing: for every coherent `G`
there is `n₀` with `Hᵠ⁺¹(B × ℙᴺ, G(n)^an) = 0` whenever `n ≥ n₀`, `N + 1 ≤ q + 1 + k` and `B`
is an open box. -/
theorem exists_H_tube_twist_eq_zero_aux (k : ℕ) :
    ∀ (G : ℙₒ(N; RelBase.{u} m).Modules) [G.IsCoherent], ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
      ∀ q : ℕ, N + 1 ≤ q + 1 + k → ∀ (a b : Fin m → ℂ) (B : Opens (Fin m → ℂ)),
        (B : Set (Fin m → ℂ)) = Complex.openBox a b →
        ∀ x : TopCat.Sheaf.H ((tubeAb.{u} m N B).obj (twist G n)) (q + 1), x = 0 := by
  induction k with
  | zero =>
    intro G _
    refine ⟨0, fun n _ q hq a b B hB x ↦ ?_⟩
    exact (@subsingleton_H_tube_analytificationModules _ _ a b B hB (twist G n)
      (isCoherent_twist G n) (q + 1) (by omega)).elim _ _
  | succ k ih =>
    intro G _
    obtain ⟨m₁, hm₁⟩ := exists_epi_twist_free_isCoherent_kernel G
    obtain ⟨I, _, π, _, -, hK⟩ := hm₁ m₁ le_rfl
    obtain ⟨m₂, hm₂⟩ := ih (kernel π)
    refine ⟨max m₂ ((m₁ : ℤ) - N), fun n hn q hq a b B hB x ↦ ?_⟩
    let S : ShortComplex ℙₒ(N; RelBase.{u} m).Modules :=
      ShortComplex.mk (kernel.ι π) π (kernel.condition π)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π))
        inferInstance inferInstance
    have hS' := shortExact_map_tubeAb B (hS.map_of_exact (twistFunctor N (RelBase.{u} m) n))
    have hδ : TopCat.Sheaf.H.δ hS' (q + 1) (q + 2) rfl x = 0 :=
      hm₂ n (le_of_max_le_left hn) (q + 1) (by omega) a b B hB _
    obtain ⟨y, hyx⟩ := (TopCat.Sheaf.H.exact₃ hS' (q + 1) (q + 2) rfl x).1 hδ
    let e := (tubeAb.{u} m N B).mapIso
      (twistTwistIso (SheafOfModules.free I : ℙₒ(N; RelBase.{u} m).Modules) (-(m₁ : ℤ)) n)
    have hy : ∀ z : TopCat.Sheaf.H ((tubeAb.{u} m N B).obj
        (twist (twist (SheafOfModules.free I) (-(m₁ : ℤ))) n)) (q + 1), z = 0 := by
      intro z
      have hz : z = TopCat.Sheaf.H.map e.inv (q + 1) (TopCat.Sheaf.H.map e.hom (q + 1) z) := by
        rw [← TopCat.Sheaf.H.map_comp_apply, e.hom_inv_id, TopCat.Sheaf.H.map_id_apply]
      have h0 : TopCat.Sheaf.H.map e.hom (q + 1) z = 0 :=
        H_tube_twist_free_eq_zero a b hB (-(m₁ : ℤ) + n) (by omega) q _
      rw [hz, h0]
      exact map_zero _
    rw [← hyx, hy y]
    exact map_zero _

/-- **Relative analytic Serre vanishing, uniform in the box**: for a coherent sheaf `G` on
`P = ℙₒ(N; ℂ[y₀, …, y_{m-1}])` there is `n₀` such that `Hᵠ(B × ℙᴺ, G(n)^an) = 0` for all
`q ≥ 1`, `n ≥ n₀` and all open boxes `B ⊆ ℂᵐ`. -/
theorem exists_H_tube_twist_eq_zero (G : ℙₒ(N; RelBase.{u} m).Modules) [G.IsCoherent] :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ∀ (a b : Fin m → ℂ) (B : Opens (Fin m → ℂ)),
      (B : Set (Fin m → ℂ)) = Complex.openBox a b → ∀ q : ℕ,
        ∀ x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (tube.{u} (N := N) B)).obj
          ((analytificationModules (relProjectiveSpace.{u} m N)).obj (twist G n)).toAb)
          (q + 1), x = 0 := by
  obtain ⟨n₀, h⟩ := exists_H_tube_twist_eq_zero_aux (m := m) N G
  exact ⟨n₀, fun n hn a b B hB q ↦ h n hn q (by omega) a b B hB⟩

/-! ### Acyclicity for `P^an ⟶ (𝔸ᵐ)^an` -/

/-- The open boxes containing a point form a neighbourhood basis. -/
lemma exists_openBox_subset {U : Set (Fin m → ℂ)} (hU : IsOpen U) {z : Fin m → ℂ} (hz : z ∈ U) :
    ∃ a b : Fin m → ℂ, z ∈ Complex.openBox a b ∧ Complex.openBox a b ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z hz
  set δ : ℝ := ε / 4
  have hδ : 0 < δ := by positivity
  refine ⟨fun j ↦ z j - (δ + δ * Complex.I), fun j ↦ z j + (δ + δ * Complex.I), ?_, ?_⟩
  · intro j _
    simp only [Complex.mem_reProdIm, Set.mem_Ioo, Complex.sub_re, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      Complex.sub_im, Complex.add_im, Complex.mul_im]
    constructor <;> constructor <;> linarith
  · intro w hw
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro j
    have hj := hw j (Set.mem_univ j)
    simp only [Complex.mem_reProdIm, Set.mem_Ioo, Complex.sub_re, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      Complex.sub_im, Complex.add_im, Complex.mul_im] at hj
    rw [dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
    simp only [Complex.sub_re, Complex.sub_im]
    have h1 : |(w j).re - (z j).re| < 2 * δ := abs_lt.2 ⟨by linarith, by linarith⟩
    have h2 : |(w j).im - (z j).im| < 2 * δ := abs_lt.2 ⟨by linarith, by linarith⟩
    have hδε : δ = ε / 4 := rfl
    linarith

/-- **`G(n)^an` is acyclic for `P^an ⟶ (𝔸ᵐ)^an`, `n ≫ 0`**: for a coherent sheaf `G` on
`P = ℙₒ(N; ℂ[y₀, …, y_{m-1}])` there is `n₀` such that `G(n)^an` is acyclic for the analytification
of `P ⟶ 𝔸ᵐ` for all `n ≥ n₀`, i.e. its higher direct images vanish. -/
theorem exists_isPushforwardAcyclic_twist (G : ℙₒ(N; RelBase.{u} m).Modules) [G.IsCoherent] :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → TopCat.Sheaf.IsPushforwardAcyclic
      (analytification.map (relProjectiveSpaceToAffine.{u} m N)).toLRSHom.base
      ((analytificationModules (relProjectiveSpace.{u} m N)).obj (twist G n)).toAb := by
  obtain ⟨n₀, h⟩ := exists_H_tube_twist_eq_zero G
  refine ⟨n₀, fun n hn q V c x hx ↦ ?_⟩
  set ψ := (analytificationAffineSpaceIso.{u} m).hom.toLRSHom.base
  set φ := (analytificationAffineSpaceIso.{u} m).inv.toLRSHom.base
  have hφψ : ∀ x', φ (ψ x') = x' := fun x' ↦
    congr(($((AnalyticSpace.forgetToLocallyRingedSpace.mapIso
      (analytificationAffineSpaceIso.{u} m)).hom_inv_id).base x'))
  have hVo : IsOpen {w : Fin m → ℂ | φ (projectiveSpaceAn.ofFin.{u} w) ∈ V} :=
    V.isOpen.preimage (φ.hom.continuous.comp (continuous_pi fun k ↦ continuous_apply k.down))
  obtain ⟨a, b, hxB, hBV⟩ := exists_openBox_subset hVo
    (z := projectiveSpaceAn.toFin (ψ x)) (by simpa [hφψ] using hx)
  let B : Opens (Fin m → ℂ) := boxOpens a b
  let V' : Opens (analytification.obj (affineSpace.{u} m)).toPresheafedSpace :=
    ⟨ψ ⁻¹' (projectiveSpaceAn.toFin ⁻¹' (B : Set (Fin m → ℂ))),
      (B.isOpen.preimage (continuous_pi fun k ↦ continuous_apply (ULift.up k))).preimage
        ψ.hom.continuous⟩
  have hV' : V' ≤ V := fun x' hx' ↦ by
    have := hBV hx'
    simpa [hφψ] using this
  refine ⟨V', hV', hxB, ?_⟩
  have hsub : Subsingleton (CategoryTheory.Sheaf.H'.{u}
      ((analytificationModules (relProjectiveSpace.{u} m N)).obj (twist G n)).toAb (q + 1)
      ((Opens.map (analytification.map (relProjectiveSpaceToAffine.{u} m N)).toLRSHom.base).obj
        V')) := by
    haveI : Subsingleton (TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (tube.{u} (N := N) B)).obj
        ((analytificationModules (relProjectiveSpace.{u} m N)).obj (twist G n)).toAb) (q + 1)) :=
      ⟨fun c₁ c₂ ↦ (h n hn a b B rfl q c₁).trans (h n hn a b B rfl q c₂).symm⟩
    exact (TopCat.Sheaf.H'AddEquiv (tube.{u} (N := N) B) _ (q + 1)).toEquiv.subsingleton
  exact Subsingleton.elim _ _

end ComplexAnalytic.relProjectiveSpaceAn

end
