/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Topology.Sheaves.Cohomology.CechLocalization
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.SerreVanishing

/-!
# Relative Serre vanishing on projective space

Let `R` be a noetherian ring, `p : ℙⁿ = ℙₒ(n; R) ⟶ Spec R` and `F` a coherent sheaf on `ℙⁿ`. We
show that there is `m₀` such that for all `m ≥ m₀` and every global function `φ` on `ℙⁿ`,
`Hᵠ(ℙⁿ_φ, F(m)) = 0` for `q ≥ 1`, where `ℙⁿ_φ` is the basic open of `φ`
(`ProjectiveSpace.exists_H_basicOpen_twist_eq_zero`). Taking `φ = p^♯ r` gives
`Hᵠ(p⁻¹ D(r), F(m)) = 0` for all `r ∈ R`, so `F(m)` is `p`-acyclic
(`ProjectiveSpace.exists_isPushforwardAcyclic_twist`, via the criterion
`AlgebraicGeometry.isPushforwardAcyclic_of_basicOpen`): the higher direct images `Rᵠ p_* F(m)`
vanish.

The point is that `m₀` does not depend on `φ`. The proof is Serre's descending induction, as in
`ProjectiveSpace.exists_H_twist_eq_zero`, run on `ℙⁿ_φ`; it needs
* `Hᵠ(ℙⁿ_φ, O(k)) = 0` for `q ≥ 1` and `k ≥ -n`
  (`ProjectiveSpace.H_basicOpen_twistingSheafAb_eq_zero`):
  the Čech complex of `O(k)` for the cover `Uᵢ ∩ ℙⁿ_φ` is the localisation of the one for the
  standard cover (`Scheme.Modules.exactAt_cechComplex_inf_basicOpen`), which is exact, and Leray's
  theorem applies since the `Uᵢ ∩ ℙⁿ_φ` and their intersections are affine;
* `Hᵠ(ℙⁿ_φ, F) = 0` for `q ≥ n + 1` and quasi-coherent `F`
  (`ProjectiveSpace.H_basicOpen_eq_zero_of_le_of_isQuasicoherent`).
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry.ProjectiveSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- Multiplication by a global function `φ`, as an endomorphism of the underlying abelian
presheaf of an `𝒪_X`-module. -/
noncomputable def smulAb (φ : Γ(X, ⊤)) :
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj ⟶
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj where
  app V := AddCommGrpCat.ofHom (DistribSMul.toAddMonoidHom Γ(F, V.unop) (φ |ₒ V.unop))
  naturality V W h := by
    ext s
    change (φ |ₒ W.unop) • TopCat.Presheaf.restrictOpen (F := F.presheaf)
        (show Γ(F, V.unop) from s) W.unop (leOfHom h.unop) =
      TopCat.Presheaf.restrictOpen (F := F.presheaf)
        ((φ |ₒ V.unop) • (show Γ(F, V.unop) from s)) W.unop (leOfHom h.unop)
    rw [mres_smul, ores_res]

variable {F} in
lemma iterate_smulAb_app (φ : Γ(X, ⊤)) (V : X.Opens) (k : ℕ) (s : Γ(F, V)) :
    ((smulAb F φ).app (op V))^[k] s = (φ |ₒ V) ^ k • s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul]
    rfl


lemma bijective_smulAb_app (φ : Γ(X, ⊤)) {V : X.Opens} (hV : V ≤ X.basicOpen φ) :
    Function.Bijective ((smulAb F φ).app (op V)) := by
  have hu : IsUnit (φ |ₒ V) := by
    have h : IsUnit ((φ |ₒ X.basicOpen φ) |ₒ V) :=
      (X.toRingedSpace.isUnit_res_basicOpen φ).map (X.presheaf.map (homOfLE hV).op).hom
    rwa [ores_res] at h
  obtain ⟨u, hu⟩ := hu
  refine ⟨fun s t hst ↦ ?_, fun s ↦ ⟨(show Γ(F, V) from (↑u⁻¹ : Γ(X, V)) • (show Γ(F, V) from s)),
    ?_⟩⟩
  · change (φ |ₒ V) • (show Γ(F, V) from s) = (φ |ₒ V) • (show Γ(F, V) from t) at hst
    have h := congrArg ((↑u⁻¹ : Γ(X, V)) • ·) hst
    simp only at h
    rwa [← hu, smul_smul, smul_smul, Units.inv_mul, one_smul, one_smul] at h
  · change (φ |ₒ V) • (↑u⁻¹ : Γ(X, V)) • (show Γ(F, V) from s) = s
    rw [← hu, smul_smul, Units.mul_inv, one_smul]

variable {ι : Type u} (U : ι → X.Opens) (φ : Γ(X, ⊤))

lemma cechOpen_inf_basicOpen {n : ℕ} (σ : Fin (n + 1) → ι) :
    TopCat.Presheaf.cechOpen (fun i ↦ U i ⊓ X.basicOpen φ) σ =
      X.basicOpen (φ |ₒ TopCat.Presheaf.cechOpen U σ) := by
  rw [Scheme.basicOpen_restrictOpen]
  exact (iInf_inf (f := fun a ↦ U (σ a))).symm

variable [Finite ι] [F.IsQuasicoherent]

set_option backward.isDefEq.respectTransparency false in
/-- **Čech complexes of quasi-coherent sheaves localise.** If all finite intersections `U_σ` are
affine and the Čech complex of `F` for `U` is exact in degree `n + 1`, then so is the Čech complex
for the family `Uᵢ ∩ X_φ`, for every global function `φ`. -/
theorem exactAt_cechComplex_inf_basicOpen
    (hA : ∀ (m : ℕ) (σ : Fin (m + 1) → ι), IsAffineOpen (TopCat.Presheaf.cechOpen U σ)) (n : ℕ)
    (h : (TopCat.Presheaf.cechComplex U
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj).ExactAt (n + 1)) :
    (TopCat.Presheaf.cechComplex (fun i ↦ U i ⊓ X.basicOpen φ)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F).obj).ExactAt (n + 1) := by
  have hUU' : ∀ i, U i ⊓ X.basicOpen φ ≤ U i := fun i ↦ inf_le_left
  refine TopCat.Presheaf.exactAt_cechComplex_of_localization hUU' (smulAb F φ) n
    (fun σ s ↦ ?_) (fun σ t ht ↦ ?_)
    (fun m σ ↦ bijective_smulAb_app F φ ((iInf_le _ 0).trans inf_le_right)) h
  · have he := cechOpen_inf_basicOpen U φ σ
    obtain ⟨k, t, ht⟩ := (hA _ σ).exists_restrictOpen_eq_pow_smul F
      (φ |ₒ TopCat.Presheaf.cechOpen U σ)
      (TopCat.Presheaf.restrictOpen (F := F.presheaf) s _ he.ge)
    refine ⟨k, t, ?_⟩
    have ht' := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen (F := F.presheaf) x _ he.le) ht
    simp only [mres_res, mres_smul, ores_pow, ores_res, mres_self] at ht'
    rw [iterate_smulAb_app]
    exact ht'
  · have he := cechOpen_inf_basicOpen U φ σ
    change TopCat.Presheaf.restrictOpen (F := F.presheaf) t _
      (TopCat.Presheaf.cechOpen_mono hUU' σ) = 0 at ht
    obtain ⟨k, hk⟩ := (hA _ σ).exists_pow_smul_eq_zero F
      (φ |ₒ TopCat.Presheaf.cechOpen U σ) t (by
        have ht' := congrArg (fun x ↦ TopCat.Presheaf.restrictOpen (F := F.presheaf) x _ he.ge)
          ht
        simp only [mres_res, mres_zero] at ht'
        exact ht')
    refine ⟨k, ?_⟩
    rw [iterate_smulAb_app]
    exact hk

end AlgebraicGeometry.Scheme.Modules


namespace AlgebraicGeometry

/-- **A criterion for acyclicity of a morphism of schemes.** Let `p : X ⟶ S` and let `G` be an
abelian sheaf on `X`. If every point of `S` lies in an affine open `U` such that
`Hᵠ(p⁻¹ D(g), G) = 0` for all `q ≥ 1` and `g ∈ Γ(S, U)`, then `G` is `p`-acyclic. -/
lemma isPushforwardAcyclic_of_basicOpen {X S : Scheme.{u}} (p : X ⟶ S) (G : TopCat.AbSheaf X)
    (h : ∀ s : S, ∃ U : S.Opens, IsAffineOpen U ∧ s ∈ U ∧ ∀ (g : Γ(S, U)) (q : ℕ)
      (c : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (p ⁻¹ᵁ S.basicOpen g)).obj G) (q + 1)),
        c = 0) :
    TopCat.Sheaf.IsPushforwardAcyclic p.base G := by
  refine TopCat.Sheaf.isPushforwardAcyclic_of_forall_exists G fun V s hs ↦ ?_
  obtain ⟨U, hU, hsU, h0⟩ := h s
  obtain ⟨g, hgV, hsg⟩ := hU.exists_basicOpen_le ⟨s, hs⟩ hsU
  exact ⟨S.basicOpen g, hgV, hsg, h0 g⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace

open SimplexCochain

variable {n : ℕ} {R : Type u} [CommRing R]

/-- Cohomology of `T(∐ G)` vanishes in degree `q` if it vanishes for every `T(G i)`, for an
additive functor `T` to abelian sheaves and a finite coproduct. -/
lemma H_map_sigma_eq_zero {X : Scheme.{u}} {Y : TopCat.{u}} (T : X.Modules ⥤ TopCat.AbSheaf Y)
    [T.Additive] {I : Type u} [Finite I] (G : I → X.Modules) (q : ℕ)
    (h : ∀ i (x : TopCat.Sheaf.H (T.obj (G i)) q), x = 0)
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

lemma isAffineOpen_cechOpen_stdCover {p : ℕ} (σ : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    IsAffineOpen (TopCat.Presheaf.cechOpen (stdCover n R) σ) := by
  rw [cechOpen_stdCover]
  obtain ⟨i, hi⟩ := im_nonempty fun a ↦ (σ a).down
  exact isAffineOpen_UI hi

lemma isAffineOpen_cechOpen_stdCover_inf_basicOpen (φ : Γ(ℙₒ(n; R), ⊤)) {p : ℕ}
    (σ : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    IsAffineOpen (TopCat.Presheaf.cechOpen
      (fun i ↦ stdCover n R i ⊓ ℙₒ(n; R).basicOpen φ) σ) := by
  rw [cechOpen_inf_basicOpen]
  exact (isAffineOpen_cechOpen_stdCover σ).basicOpen _

lemma iSup_stdCover_inf_basicOpen (φ : Γ(ℙₒ(n; R), ⊤)) :
    ⨆ i, stdCover n R i ⊓ ℙₒ(n; R).basicOpen φ = ℙₒ(n; R).basicOpen φ := by
  rw [← iSup_inf_eq, iSup_stdCover, top_inf_eq]

/-- **`Hᵠ(ℙⁿ_φ, O(k)) = 0` for `q ≥ 1` and `k ≥ -n`**, for every global function `φ`. -/
theorem H_basicOpen_twistingSheafAb_eq_zero (k : ℤ) (hk : -(n : ℤ) ≤ k) (φ : Γ(ℙₒ(n; R), ⊤))
    (q : ℕ) (x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (ℙₒ(n; R).basicOpen φ)).obj
      (twistingSheafAb n R k)) (q + 1)) : x = 0 :=
  TopCat.Sheaf.H_restrictOpen_eq_zero_of_isCechAcyclic _ (iSup_stdCover_inf_basicOpen φ) _
    (fun _ σ q y ↦ H_restrictOpen_eq_zero_of_isAffineOpen (twistingSheaf n R k)
      (isAffineOpen_cechOpen_stdCover_inf_basicOpen φ σ) q y)
    (fun p ↦ exactAt_cechComplex_inf_basicOpen (twistingSheaf n R k) (stdCover n R) φ
      (fun _ σ ↦ isAffineOpen_cechOpen_stdCover σ) p (isCechAcyclic_twistingSheafAb k hk p)) q x

/-- **Cohomological dimension of `ℙⁿ_φ`**: `Hᵠ(ℙⁿ_φ, F) = 0` for every quasi-coherent `F`,
every global function `φ` and `q ≥ n + 1`. -/
theorem H_basicOpen_eq_zero_of_le_of_isQuasicoherent (F : ℙₒ(n; R).Modules) [F.IsQuasicoherent]
    (φ : Γ(ℙₒ(n; R), ⊤)) (q : ℕ) (hq : n + 1 ≤ q)
    (x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (ℙₒ(n; R).basicOpen φ)).obj
      ((SheafOfModules.toSheaf ℙₒ(n; R).ringCatSheaf).obj F)) q) : x = 0 := by
  refine (TopCat.Sheaf.subsingleton_H_restrictOpen_of_iSup_eq _
    (fun i ↦ stdCover n R i ⊓ ℙₒ(n; R).basicOpen φ) (iSup_stdCover_inf_basicOpen φ)
    (fun I hI q hq ↦ ?_) q (by simpa using hq)).elim x 0
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hq.ne'
  have he : ⨅ i ∈ I, (stdCover n R i ⊓ ℙₒ(n; R).basicOpen φ) =
      ℙₒ(n; R).basicOpen (φ |ₒ ⨅ i ∈ I, stdCover n R i) := by
    rw [Scheme.basicOpen_restrictOpen]
    obtain ⟨j, hj⟩ := hI
    refine le_antisymm (le_inf (iInf₂_mono fun _ _ ↦ inf_le_left)
      ((iInf₂_le j hj).trans inf_le_right)) (le_iInf₂ fun i hi ↦ inf_le_inf_right _ ?_)
    exact iInf₂_le i hi
  rw [he]
  exact subsingleton_H_restrictOpen_of_isAffineOpen F
    ((isAffineOpen_iInf_stdCover I hI).basicOpen _) q

/-- `Hᵠ(ℙⁿ_φ, 𝒪^I(k)) = 0` for `q ≥ 1`, `I` finite, `k ≥ -n` and every global function `φ`. -/
lemma H_basicOpen_twist_free_eq_zero {I : Type u} [Finite I] (k : ℤ) (hk : -(n : ℤ) ≤ k)
    (φ : Γ(ℙₒ(n; R), ⊤)) (q : ℕ)
    (x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (ℙₒ(n; R).basicOpen φ)).obj
      ((SheafOfModules.toSheaf ℙₒ(n; R).ringCatSheaf).obj
        (twist (SheafOfModules.free I) k))) (q + 1)) : x = 0 := by
  let T := Scheme.Modules.toAbFunctor ℙₒ(n; R) ⋙ TopCat.Sheaf.restrictOpen (ℙₒ(n; R).basicOpen φ)
  let e := T.mapIso (twistFreeIso (n := n) (R := R) I k)
  have hx : x = TopCat.Sheaf.H.map e.inv (q + 1) (TopCat.Sheaf.H.map e.hom (q + 1) x) := by
    rw [← TopCat.Sheaf.H.map_comp_apply, e.hom_inv_id, TopCat.Sheaf.H.map_id_apply]
  have h0 : TopCat.Sheaf.H.map e.hom (q + 1) x = 0 :=
    H_map_sigma_eq_zero T _ (q + 1)
      (fun _ y ↦ H_basicOpen_twistingSheafAb_eq_zero k hk φ q y) _
  rw [hx, h0]
  exact map_zero _

/-- The descending induction behind relative Serre vanishing: for every coherent `F` there is
`m₀` with `Hᵠ⁺¹(ℙⁿ_φ, F(m)) = 0` whenever `m ≥ m₀` and `n + 1 ≤ q + 1 + k`, for every global
function `φ`. -/
theorem exists_H_basicOpen_twist_eq_zero_aux [IsNoetherianRing R] (k : ℕ) :
    ∀ (F : ℙₒ(n; R).Modules) [F.IsCoherent], ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m →
      ∀ (φ : Γ(ℙₒ(n; R), ⊤)) (q : ℕ), n + 1 ≤ q + 1 + k →
        ∀ x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (ℙₒ(n; R).basicOpen φ)).obj
          ((SheafOfModules.toSheaf ℙₒ(n; R).ringCatSheaf).obj (twist F m))) (q + 1), x = 0 := by
  induction k with
  | zero =>
    intro F _
    haveI := SheafOfModules.IsCoherent.isQuasicoherent F
    exact ⟨0, fun m _ φ q hq x ↦ H_basicOpen_eq_zero_of_le_of_isQuasicoherent (twist F m) φ
      (q + 1) (by omega) x⟩
  | succ k ih =>
    intro F _
    obtain ⟨m₁, hm₁⟩ := exists_epi_twist_free_isCoherent_kernel F
    obtain ⟨I, _, π, _, -, hK⟩ := hm₁ m₁ le_rfl
    obtain ⟨m₂, hm₂⟩ := ih (kernel π)
    refine ⟨max m₂ ((m₁ : ℤ) - n), fun m hm φ q hq x ↦ ?_⟩
    let S : ShortComplex ℙₒ(n; R).Modules := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π))
        inferInstance inferInstance
    have hS' := ((hS.map_of_exact (twistFunctor n R m)).map_of_exact
      (Scheme.Modules.toAbFunctor ℙₒ(n; R))).map_of_exact
        (TopCat.Sheaf.restrictOpen (ℙₒ(n; R).basicOpen φ))
    have hδ : TopCat.Sheaf.H.δ hS' (q + 1) (q + 2) rfl x = 0 :=
      hm₂ m (le_of_max_le_left hm) φ (q + 1) (by omega) _
    obtain ⟨y, hyx⟩ := (TopCat.Sheaf.H.exact₃ hS' (q + 1) (q + 2) rfl x).1 hδ
    have e := twistTwistIso (SheafOfModules.free I : ℙₒ(n; R).Modules) (-(m₁ : ℤ)) m
    let T := Scheme.Modules.toAbFunctor ℙₒ(n; R) ⋙
      TopCat.Sheaf.restrictOpen (ℙₒ(n; R).basicOpen φ)
    let e' := T.mapIso e
    have hy : ∀ z : TopCat.Sheaf.H (T.obj (twist (twist (SheafOfModules.free I) (-(m₁ : ℤ))) m))
        (q + 1), z = 0 := by
      intro z
      have hz : z = TopCat.Sheaf.H.map e'.inv (q + 1) (TopCat.Sheaf.H.map e'.hom (q + 1) z) := by
        rw [← TopCat.Sheaf.H.map_comp_apply, e'.hom_inv_id, TopCat.Sheaf.H.map_id_apply]
      have h0 : TopCat.Sheaf.H.map e'.hom (q + 1) z = 0 :=
        H_basicOpen_twist_free_eq_zero (-(m₁ : ℤ) + m) (by omega) φ q _
      rw [hz, h0]
      exact map_zero _
    rw [← hyx, hy y]
    exact map_zero _

/-- **Relative Serre vanishing on `ℙⁿ`**: for a coherent sheaf `F` on `ℙₒ(n; R)` with `R`
noetherian there is `m₀` such that `Hᵠ(ℙⁿ_φ, F(m)) = 0` for all `q ≥ 1`, `m ≥ m₀` and all global
functions `φ`. -/
theorem exists_H_basicOpen_twist_eq_zero [IsNoetherianRing R] (F : ℙₒ(n; R).Modules)
    [F.IsCoherent] : ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → ∀ (φ : Γ(ℙₒ(n; R), ⊤)) (q : ℕ)
      (x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (ℙₒ(n; R).basicOpen φ)).obj
        ((SheafOfModules.toSheaf ℙₒ(n; R).ringCatSheaf).obj (twist F m))) (q + 1)), x = 0 := by
  obtain ⟨m₀, h⟩ := exists_H_basicOpen_twist_eq_zero_aux n F
  exact ⟨m₀, fun m hm φ q ↦ h m hm φ q (by omega)⟩


/-- **Relative Serre vanishing for `ℙⁿ ⟶ Spec R`**: for a coherent sheaf `F` on `ℙₒ(n; R)` with
`R` noetherian there is `m₀` such that `F(m)` is acyclic for `ℙₒ(n; R) ⟶ Spec R` for all
`m ≥ m₀`. -/
theorem exists_isPushforwardAcyclic_twist [IsNoetherianRing R] (F : ℙₒ(n; R).Modules)
    [F.IsCoherent] : ∃ m₀ : ℤ, ∀ m : ℤ, m₀ ≤ m → TopCat.Sheaf.IsPushforwardAcyclic
      (toSpec n R).base ((SheafOfModules.toSheaf ℙₒ(n; R).ringCatSheaf).obj (twist F m)) := by
  obtain ⟨m₀, h⟩ := exists_H_basicOpen_twist_eq_zero F
  refine ⟨m₀, fun m hm ↦ isPushforwardAcyclic_of_basicOpen _ _ fun _ ↦
    ⟨⊤, isAffineOpen_top _, trivial, fun g q ↦ ?_⟩⟩
  have := h m hm ((toSpec n R).appTop g) q
  rwa [← Scheme.preimage_basicOpen_top] at this

end AlgebraicGeometry.ProjectiveSpace

end
