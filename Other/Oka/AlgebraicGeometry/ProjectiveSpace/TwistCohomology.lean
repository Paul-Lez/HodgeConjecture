/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.TwistSections
public import Other.Oka.RingTheory.MvPolynomial.CechProjectiveAway
public import Other.Oka.Topology.Sheaves.Cohomology.Leray
public import Mathlib.Data.Complex.Basic

/-!
# Cohomology of the twisting sheaves on projective space

Let `A = R[X₀, …, Xₙ]` and let `O(k)` be the twisting sheaf on `ℙₒ(n; R)`, regarded as an abelian
sheaf (`ProjectiveSpace.twistingSheafAb n R k`). For the standard cover `Uᵢ = D₊(Xᵢ)`
(`ProjectiveSpace.stdCover`, indexed by `ULift (Fin (n + 1))`), the finite intersections are the
`UI I = D₊(X_I)` (`cechOpen_stdCover`), and the sections of `O(k)` over them are the degree-`k`
parts of `A[1 / X_I]` (`sectionsUIEquiv`). Hence the Čech complex `Č•(U, O(k))` is isomorphic,
degreewise and compatibly with the differentials, to the Laurent-model complex
`MvPolynomial.degCechD` (`cechCochainEquiv`, `cechCochainEquiv_cechD`), so it is exact in degree
`q ≥ 1` unless `q = n` and `k ≤ -n - 1` (`exactAt_cechComplex_twistingSheafAb`).

By Leray's theorem, if `O(k)` has no higher cohomology on the affine opens `UI I` (Serre's affine
vanishing), then `Hᵠ(ℙₒ(n; R), O(k)) = 0` for `q ≥ 1` and `k ≥ -n`
(`H_twistingSheafAb_eq_zero`). In degree zero, `H⁰(ℙₒ(n; R), O(d)) ≅ A_d` for `d ≥ 0`
(`hZeroTwistingSheafAbEquiv`) and `H⁰(ℙₒ(n; R), O(k)) = 0` for `k < 0`
(`H_zero_twistingSheafAb_eq_zero`), for `n ≥ 1`.

## Main definitions and results

- `ProjectiveSpace.twistingSheafAb n R k`: the underlying abelian sheaf of `O(k)`.
- `ProjectiveSpace.stdCover n R`: the standard cover, indexed by `ULift (Fin (n + 1))`.
- `ProjectiveSpace.cechCochainEquiv k p : Čᵖ(U, O(k)) ≃+ DegCechObj (Fin (n + 1)) R k p`, with
  `cechCochainEquiv_cechD` (compatibility with the differentials).
- `ProjectiveSpace.exactAt_cechComplex_twistingSheafAb`,
  `ProjectiveSpace.isCechAcyclic_twistingSheafAb`.
- `ProjectiveSpace.H_twistingSheafAb_eq_zero` (conditional on acyclicity on the `UI I`).
- `ProjectiveSpace.hZeroTwistingSheafAbEquiv`, `ProjectiveSpace.H_zero_twistingSheafAb_eq_zero`.
- The specialisations to `R = ULift ℂ`.
-/

@[expose] public section

open CategoryTheory MvPolynomial TopologicalSpace Opposite SimplexCochain
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry.ProjectiveSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.ProjectiveSpace

variable {n : ℕ} {R : Type u} [CommRing R]

local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) R

variable (n R) in
/-- The underlying abelian sheaf of the twisting sheaf `O(k)` on `ℙₒ(n; R)`. -/
noncomputable abbrev twistingSheafAb (k : ℤ) : TopCat.AbSheaf ℙₒ(n; R) :=
  (SheafOfModules.toSheaf _).obj (twistingSheaf n R k)

variable (n R) in
/-- The standard cover `Uᵢ = D₊(Xᵢ)` of `ℙₒ(n; R)`, indexed by `ULift (Fin (n + 1))` (the index
type of a cover has to live in the universe of the space). -/
noncomputable def stdCover : ULift.{u} (Fin (n + 1)) → ℙₒ(n; R).Opens := fun i ↦ U n R i.down

variable (n R) in
lemma iSup_stdCover : ⨆ i, stdCover n R i = ⊤ :=
  le_antisymm le_top <| (iSup_U n R).ge.trans <| iSup_le fun i ↦ le_iSup (stdCover n R) ⟨i⟩

/-- The finite intersections of the standard cover are the opens `UI I`. -/
lemma cechOpen_stdCover {p : ℕ} (σ : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    TopCat.Presheaf.cechOpen (stdCover n R) σ = UI n R (im fun a ↦ (σ a).down) := by
  rw [UI_eq_iInf]
  apply le_antisymm
  · refine le_iInf₂ fun j hj ↦ ?_
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hj
    exact iInf_le _ a
  · exact le_iInf fun a ↦ iInf₂_le _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))

/-- Restriction along an equality of opens, as an additive equivalence of sections. -/
noncomputable def resEquiv (M : ℙₒ(n; R).Modules) {V W : ℙₒ(n; R).Opens} (h : V = W) :
    Γ(M, V) ≃+ Γ(M, W) where
  toFun s := TopCat.Presheaf.restrictOpen s W h.ge
  invFun t := TopCat.Presheaf.restrictOpen t V h.le
  left_inv s := by simp only [mres_res, mres_self]
  right_inv t := by simp only [mres_res, mres_self]
  map_add' s t := mres_add M _ s t

lemma resEquiv_apply (M : ℙₒ(n; R).Modules) {V W : ℙₒ(n; R).Opens} (h : V = W) (s : Γ(M, V)) :
    resEquiv M h s = TopCat.Presheaf.restrictOpen s W h.ge :=
  rfl

/-- Sections of `O(k)` over the intersection `U_σ` of the standard cover, as degree-`k` elements
of `A[1 / X_{im σ}]`. -/
noncomputable def cechSectionsEquiv (k : ℤ) {p : ℕ} (σ : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    (twistingSheafAb n R k).obj.obj (op (TopCat.Presheaf.cechOpen (stdCover n R) σ)) ≃+
      awayDegree R (im fun a ↦ (σ a).down) k :=
  (resEquiv (twistingSheaf n R k) (cechOpen_stdCover σ)).trans
    (sectionsUIEquiv _ k (im_nonempty _))

/-- Under `cechSectionsEquiv`, the restriction `U_{τ ∘ θ} ⊇ U_τ` is the localisation map
`A[1 / X_{im (τ ∘ θ)}] → A[1 / X_{im τ}]`. -/
lemma cechSectionsEquiv_res (k : ℤ) {m p : ℕ} (τ : Fin (p + 1) → ULift.{u} (Fin (n + 1)))
    (θ : Fin (m + 1) → Fin (p + 1))
    (s : (twistingSheafAb n R k).obj.obj (op (TopCat.Presheaf.cechOpen (stdCover n R) (τ ∘ θ)))) :
    (cechSectionsEquiv k τ ((twistingSheafAb n R k).obj.map
      (homOfLE (TopCat.Presheaf.cechOpen_le_comp _ τ θ)).op s)).1 =
      awayRestr R (im_comp_subset (fun a ↦ (τ a).down) θ) (cechSectionsEquiv k (τ ∘ θ) s).1 := by
  have hIJ : (im fun a ↦ (τ (θ a)).down) ⊆ im fun a ↦ (τ a).down :=
    im_comp_subset (fun a ↦ (τ a).down) θ
  change (sectionsUIEquiv (im fun a ↦ (τ a).down) k (im_nonempty _) (TopCat.Presheaf.restrictOpen
      (TopCat.Presheaf.restrictOpen (F := (twistingSheaf n R k).presheaf) s _ _) _ _)).1 =
      awayRestr R hIJ (sectionsUIEquiv (im fun a ↦ (τ (θ a)).down) k (im_nonempty _)
        (TopCat.Presheaf.restrictOpen (F := (twistingSheaf n R k).presheaf) s _ _)).1
  rw [mres_res, ← sectionsUIEquiv_res k hIJ (im_nonempty _), mres_res]

/-- **The Čech cochains of `O(k)`** for the standard cover are the cochains of the Laurent-model
complex `MvPolynomial.degCechD`. -/
noncomputable def cechCochainEquiv (k : ℤ) (p : ℕ) :
    TopCat.Presheaf.CechCochain (stdCover n R) (twistingSheafAb n R k).obj p ≃+
      DegCechObj (Fin (n + 1)) R k p where
  toFun c i := cechSectionsEquiv k (fun a ↦ ULift.up (i a)) (c _)
  invFun y σ := (cechSectionsEquiv k σ).symm (y fun a ↦ (σ a).down)
  left_inv c := funext fun σ ↦ (cechSectionsEquiv k σ).symm_apply_apply (c σ)
  right_inv _ := funext fun i ↦ (cechSectionsEquiv k (fun a ↦ ULift.up (i a))).apply_symm_apply _
  map_add' _ _ := funext fun i ↦ map_add (cechSectionsEquiv k (fun a ↦ ULift.up (i a))) _ _

lemma cechCochainEquiv_apply (k : ℤ) (p : ℕ)
    (c : TopCat.Presheaf.CechCochain (stdCover n R) (twistingSheafAb n R k).obj p)
    (i : Fin (p + 1) → Fin (n + 1)) :
    cechCochainEquiv k p c i = cechSectionsEquiv k (fun a ↦ ULift.up (i a)) (c _) :=
  rfl

/-- **The Čech differential of `O(k)` is `degCechD`** under `cechCochainEquiv`. -/
lemma cechCochainEquiv_cechD (k : ℤ) (p : ℕ)
    (c : TopCat.Presheaf.CechCochain (stdCover n R) (twistingSheafAb n R k).obj p) :
    cechCochainEquiv k (p + 1) (TopCat.Presheaf.cechD _ _ p c) =
      degCechD (Fin (n + 1)) R k p (cechCochainEquiv k p c) := by
  funext i
  apply Subtype.ext
  rw [cechCochainEquiv_apply, TopCat.Presheaf.cechD_apply]
  simp only [map_sum, map_zsmul, AddSubgroup.val_finsetSum, AddSubgroup.coe_zsmul, degCechD,
    AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  congr 1
  exact cechSectionsEquiv_res k (fun a ↦ ULift.up (i a)) l.succAbove _

/-- **Čech cohomology of `O(k)`**: the Čech complex of `O(k)` for the standard cover of
`ℙₒ(n; R)` is exact in degree `p + 1` unless `p + 1 = n` and `k < -n`. -/
theorem exactAt_cechComplex_twistingSheafAb (k : ℤ) (p : ℕ) (hp : p + 1 ≠ n ∨ -(n : ℤ) ≤ k) :
    (TopCat.Presheaf.cechComplex (stdCover n R) (twistingSheafAb n R k).obj).ExactAt (p + 1) := by
  rw [TopCat.Presheaf.exactAt_cechComplex_succ_iff]
  intro c hc
  have hp' : p + 2 ≠ Fintype.card (Fin (n + 1)) ∨ -(Fintype.card (Fin (n + 1)) : ℤ) < k := by
    rw [Fintype.card_fin]
    omega
  have hx : degCechD (Fin (n + 1)) R k (p + 1) (cechCochainEquiv k (p + 1) c) = 0 := by
    rw [← cechCochainEquiv_cechD, hc, map_zero]
  obtain ⟨y, hy⟩ := (degCech_exact (R := R) k p hp' _).1 hx
  refine ⟨(cechCochainEquiv k p).symm y, (cechCochainEquiv k (p + 1)).injective ?_⟩
  rw [cechCochainEquiv_cechD, AddEquiv.apply_symm_apply, hy]

/-- For `k ≥ -n`, the Čech complex of `O(k)` for the standard cover is exact in all positive
degrees. -/
theorem isCechAcyclic_twistingSheafAb (k : ℤ) (hk : -(n : ℤ) ≤ k) :
    TopCat.Presheaf.IsCechAcyclic (stdCover n R) (twistingSheafAb n R k).obj :=
  fun p ↦ exactAt_cechComplex_twistingSheafAb k p (Or.inr hk)

/-- **Vanishing of `Hᵠ(ℙⁿ, O(k))`** for `q ≥ 1` and `k ≥ -n` (in particular for `O = O(0)`),
assuming that `O(k)` has no higher cohomology on the affine opens `UI I` (which is Serre's
affine vanishing theorem for the quasi-coherent sheaf `O(k)`). -/
theorem H_twistingSheafAb_eq_zero (k : ℤ) (hk : -(n : ℤ) ≤ k)
    (hacyc : ∀ I : Finset (Fin (n + 1)), I.Nonempty → ∀ (q : ℕ)
      (x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (UI n R I)).obj (twistingSheafAb n R k))
        (q + 1)), x = 0)
    (q : ℕ) (x : TopCat.Sheaf.H (twistingSheafAb n R k) (q + 1)) : x = 0 := by
  have key : ∀ V : ℙₒ(n; R).Opens, (∃ I : Finset (Fin (n + 1)), I.Nonempty ∧ V = UI n R I) →
      ∀ (q : ℕ) (x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen V).obj (twistingSheafAb n R k))
        (q + 1)), x = 0 := by
    rintro V ⟨I, hI, rfl⟩
    exact hacyc I hI
  exact TopCat.Sheaf.H_eq_zero_of_isCechAcyclic (stdCover n R) (iSup_stdCover n R) _
    (fun _ σ ↦ key _ ⟨_, im_nonempty _, cechOpen_stdCover σ⟩)
    (isCechAcyclic_twistingSheafAb k hk) q x

/-- **`H⁰(ℙⁿ, O(d)) = A_d`**: for `n ≥ 1` and `d ≥ 0`, the global sections of `O(d)` are the
homogeneous polynomials of degree `d`. -/
noncomputable def hZeroTwistingSheafAbEquiv (hn : 1 ≤ n) (d : ℕ) :
    TopCat.Sheaf.H (twistingSheafAb n R d) 0 ≃+ 𝒜 d :=
  (TopCat.Sheaf.H.equiv₀ _).trans (globalSectionsEquiv hn d)

/-- **`H⁰(ℙⁿ, O(k)) = 0` for `k < 0`** (`n ≥ 1`). -/
lemma H_zero_twistingSheafAb_eq_zero (hn : 1 ≤ n) (k : ℤ) (hk : k < 0)
    (x : TopCat.Sheaf.H (twistingSheafAb n R k) 0) : x = 0 :=
  (TopCat.Sheaf.H.equiv₀ _).injective <| by
    rw [map_zero]
    exact globalSections_eq_zero k hn hk _

section Complex

/-- `Hᵠ(ℙⁿ_ℂ, O(k)) = 0` for `q ≥ 1` and `k ≥ -n`, assuming acyclicity of `O(k)` on the `UI I`. -/
theorem H_twistingSheafAb_complex_eq_zero (k : ℤ) (hk : -(n : ℤ) ≤ k)
    (hacyc : ∀ I : Finset (Fin (n + 1)), I.Nonempty → ∀ (q : ℕ)
      (x : TopCat.Sheaf.H ((TopCat.Sheaf.restrictOpen (UI n (ULift.{u} ℂ) I)).obj
        (twistingSheafAb n (ULift.{u} ℂ) k)) (q + 1)), x = 0)
    (q : ℕ) (x : TopCat.Sheaf.H (twistingSheafAb n (ULift.{u} ℂ) k) (q + 1)) : x = 0 :=
  H_twistingSheafAb_eq_zero k hk hacyc q x

/-- `H⁰(ℙⁿ_ℂ, O(d)) = ℂ[X₀, …, Xₙ]_d` for `n ≥ 1`, `d ≥ 0`. -/
noncomputable def hZeroTwistingSheafAbComplexEquiv (hn : 1 ≤ n) (d : ℕ) :
    TopCat.Sheaf.H (twistingSheafAb n (ULift.{u} ℂ) d) 0 ≃+
      homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℂ) d :=
  hZeroTwistingSheafAbEquiv hn d

end Complex

end AlgebraicGeometry.ProjectiveSpace

end
