/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.Proper.RelativeBaseChangeAn

/-!
# The canonical map for the twisting sheaves over `D × ℙᴺ`

Let `P = ℙₒ(N; A)`, `A = ℂ[y₀, …, y_{m-1}]`, `N ≥ 1`, and `D ⊆ ℂᵐ` open. A global section of
`𝒪(e)` on `P` is a homogeneous polynomial `p ∈ A[X₀, …, X_N]` of degree `e`
(`AlgebraicGeometry.ProjectiveSpace.globalSectionsEquiv`), and its analytification, read as a
function of homogeneous and base coordinates, is `(v, y) ↦ p(v)` with coefficients evaluated at
`y` (`ComplexAnalytic.relProjectiveSpaceAn.anTwFun_algSec`). Sections of `𝒪(e)^an` over
`D × ℙᴺ` are the functions `∑_{|s| = e} c_s(y) vˢ` with `c_s ∈ 𝒪(D)`
(`ComplexAnalytic.relProjectiveSpaceAn.tubeSectionsEquiv`). Hence the canonical map
`𝒪(D) ⊗_A Γ(P, 𝒪(e)) → Γ(D × ℙᴺ, 𝒪(e)^an)` sends `∑_s c_s ⊗ Xˢ` to the section with
coefficients `c`, and it is bijective
(`ComplexAnalytic.relProjectiveSpaceAn.bijective_canMap_twistingSheaf`), since `Γ(P, 𝒪(e))` is
spanned over `A` by the monomials (`eq_sum_smul_monoSec`).

With `Other/Oka/Analytification/GAGA/Proper/RelativeBaseChangeAn.lean` this gives **relative base change
for sections over boxes** (`ComplexAnalytic.relProjectiveSpaceAn.exists_bijective_canMap`): for
coherent `G` on `P` there is `n₀` such that `𝒪(B) ⊗_A Γ(P, G(n)) → Γ(B × ℙᴺ, G(n)^an)` is
bijective for all `n ≥ n₀` and all open boxes `B`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Topology MvPolynomial
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.LocallyRingedSpace
open scoped TensorProduct

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic.relProjectiveSpaceAn

open AnalyticSpace ProjectiveSpace HomogeneousLocalization

variable {m N : ℕ}

set_option hygiene false in
set_option quotPrecheck false in
local notation "𝒜" => homogeneousSubmodule (Fin (N + 1)) (RelBase.{u} m)

/-! ### Values of pulled back sections over `D₊(Xᵢ)` -/

lemma eval₂_prodX_singleton_ne_zero (v : Fin (N + 1) → ℂ) (y : Fin m → ℂ) (i : Fin (N + 1))
    (hi : v i ≠ 0) : eval₂ (evalBase.{u} y) v (prodX (RelBase.{u} m) {i}) ≠ 0 := by
  simpa [prodX] using hi

/-- **Values of pulled back sections over `UI {i}`**: the value at `[v; y]` of `π^♯ u` is the
evaluation of `u ∈ A_(Xᵢ)` at `v`, over `A → ℂ` at `y`. -/
lemma evπ_UI_singleton (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) (y : Fin m → ℂ) (i : Fin (N + 1))
    (hi : v i ≠ 0) (u : Γ(ℙₒ(N; RelBase.{u} m), UI N (RelBase.{u} m) {i}))
    (hW : π m N (pointOfVec.{u} v hv y) ∈ UI N (RelBase.{u} m) {i}) :
    evπ.{u} v hv y hW u = awayEval (φ := evalBase.{u} y) v (prodX _ {i})
      (eval₂_prodX_singleton_ne_zero v y i hi)
      (sectionsUIRingEquiv {i} (Finset.singleton_nonempty i) u) := by
  have hUi : U N (RelBase.{u} m) i ≤ UI N (RelBase.{u} m) {i} := (UI_singleton i).ge
  rw [← evπ_restrictOpen hUi v hv y (π_pointOfVec_mem_U v hv y i hi) u]
  set b := (Proj.basicOpenIsoAway 𝒜 (X i) (X_mem_homogeneousSubmodule_one i) Nat.one_pos).inv
    (TopCat.Presheaf.restrictOpen u (U N (RelBase.{u} m) i) hUi)
  have hb : Proj.awayToSection 𝒜 (X i) b =
      TopCat.Presheaf.restrictOpen u (U N (RelBase.{u} m) i) hUi :=
    (Proj.basicOpenIsoAway 𝒜 (X i) (X_mem_homogeneousSubmodule_one i) Nat.one_pos).inv_hom_id_apply
      _
  have hx := prodX_eq (R := RelBase.{u} m) (Finset.mem_singleton_self i)
  have hg := prod_X_mem_homogeneousSubmodule (R := RelBase.{u} m)
    (({i} : Finset (Fin (N + 1))).erase i)
  have hab : awayMap 𝒜 hg hx b = sectionsUIRingEquiv {i} (Finset.singleton_nonempty i) u := by
    apply (sectionsUIRingEquiv {i} (Finset.singleton_nonempty i)).symm.injective
    rw [RingEquiv.symm_apply_apply, sectionsUIRingEquiv_symm_apply]
    have := congr($(Proj.awayMap_awayToSection 𝒜 hg hx) b)
    refine this.trans ?_
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [hb]
    exact (ores_res _ _ u).trans (ores_self u)
  rw [← hb]
  refine (eval_π_awayToSection v hv y i hi b).trans ?_
  rw [← hab]
  exact (congrArg (fun F ↦ F b) (awayEval_comp_awayMap (φ := evalBase.{u} y) v hg hx
    (by rwa [eval₂_evalBase_X]) (eval₂_prodX_singleton_ne_zero v y i hi))).symm

/-! ### Sections of `𝒪(k)^an` over `D × ℙᴺ` as functions -/

/-- A section of `𝒪(k)^an` over `D × ℙᴺ` as a function of homogeneous and base coordinates
(`twFun`). -/
noncomputable def anTwFun {D : Opens (Fin m → ℂ)} {k : ℤ}
    (x : AnSec D (twistingSheaf N (RelBase.{u} m) k)) : (Fin (N + 1) → ℂ) × (Fin m → ℂ) → ℂ :=
  twFun (isoSectionsEquiv (twistingSheafAnIso m N k) (tube D) x)

variable {D : Opens (Fin m → ℂ)} {k : ℤ}

lemma anTwFun_injective :
    Function.Injective (anTwFun (D := D) (k := k) (N := N) (m := m)) :=
  fun _ _ h ↦ (isoSectionsEquiv (twistingSheafAnIso m N k) (tube D)).injective
    (twFun_injective h)

lemma anTwFun_add (x x' : AnSec D (twistingSheaf N (RelBase.{u} m) k)) :
    anTwFun (x + x') = anTwFun x + anTwFun x' :=
  (congrArg twFun (map_add (isoSectionsEquiv (twistingSheafAnIso m N k) (tube D)) x x')).trans
    (twFun_add _ _)

lemma anTwFun_zero : anTwFun (0 : AnSec D (twistingSheaf N (RelBase.{u} m) k)) = 0 :=
  (congrArg twFun (map_zero (isoSectionsEquiv (twistingSheafAnIso m N k) (tube D)))).trans
    twFun_zero

lemma anTwFun_of_notMem (x : AnSec D (twistingSheaf N (RelBase.{u} m) k))
    {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)} (hp : p ∉ vecCone.{u} (tube.{u} (N := N) D)) :
    anTwFun x p = 0 :=
  twFun_of_notMem _ hp

lemma twFun_smul_left {W : (relProjectiveSpaceAn.{u} m N).Opens}
    (r : (relProjectiveSpaceAn.{u} m N).presheaf.obj (op W))
    (t : (twistAn.{u} (m := m) (N := N) k).val.obj (op W)) {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)}
    (hp : p ∈ vecCone.{u} W) : twFun (r • t) p = secFun r p * twFun t p := by
  have hi := coneIdx_spec hp
  rw [twFun_eq _ hp _ hi, twFun_eq _ hp _ hi, pbComp_smul, secFun_mul, secFun_restrictOpen,
    Set.indicator_of_mem ((mem_vecCone_inf_iff p _).2 ⟨hp, hi⟩)]
  ring

lemma anTwFun_smul (f : OkaRing D) (x : AnSec D (twistingSheaf N (RelBase.{u} m) k))
    {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)} (hp : p ∈ vecCone.{u} (tube.{u} (N := N) D)) :
    anTwFun (f • x) p = f.toGlobalFun _ p.2 * anTwFun x p := by
  have h := modHom_smul (twistingSheafAnIso m N k).hom (baseRingHom.{u} N D f) x
  refine (congrArg (twFun · p) h).trans ?_
  rw [twFun_smul_left _ _ hp, secFun_baseRingHom D f hp]
  rfl

/-- **The analytification of a global section of `𝒪(e)` is its polynomial**: at `(v, y)`,
`v ≠ 0`, `y ∈ D`, the section `s^an|_{D × ℙᴺ}` has value `p(v)`, `p = globalSectionsEquiv s`,
with coefficients evaluated at `y`. -/
theorem anTwFun_algSec (hN : 1 ≤ N) (e : ℕ) (s : AlgSec (twistingSheaf N (RelBase.{u} m) e))
    {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)} (hp : p ∈ vecCone.{u} (tube.{u} (N := N) D)) :
    anTwFun (algSec D _ s) p = eval₂ (evalBase.{u} p.2) p.1
      (globalSectionsEquiv hN e s : MvPolynomial (Fin (N + 1)) _) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hp.1
  have hp' : p ∈ vecCone.{u} (⊤ : (relProjectiveSpaceAn.{u} m N).Opens) := ⟨hp.1, trivial⟩
  -- the section over `D × ℙᴺ` is the restriction of the section over `P^an`
  have h1 : anTwFun (algSec D _ s) p =
      twFun ((twistingSheafAnIso m N e).hom.val.app (op ⊤) (unitSec _ s)) p := by
    have h := modHom_modRes (twistingSheafAnIso m N e).hom (le_top : tube.{u} (N := N) D ≤ ⊤)
      (unitSec _ s)
    refine (congrArg (twFun · p) h).trans ?_
    rw [twFun_modRes, Set.indicator_of_mem hp]
  -- the section over `P^an` has components `π^♯ sᵢ`
  have h2 := pullbackToPbTwist_pfSec (f := πL.{u} (m := m) (N := N))
    (c := cocycle N (RelBase.{u} m) ^ (e : ℤ)) (V := ⊤) s
  rw [h1]
  refine (congrArg (twFun · p) h2).trans ?_
  refine (twFun_eq _ hp' i hi).trans ?_
  change p.1 i ^ (e : ℤ) * secFun (pbSec πL.{u} (unitComp s i)) p = _
  have hW : π m N (pointOfVec.{u} p.1 hp.1 p.2) ∈ (⊤ ⊓ U N (RelBase.{u} m) i) :=
    ⟨trivial, π_pointOfVec_mem_U p.1 hp.1 p.2 i hi⟩
  have hUI : UI N (RelBase.{u} m) {i} ≤ ⊤ ⊓ U N (RelBase.{u} m) i :=
    le_inf le_top (UI_singleton i).le
  have hWI : π m N (pointOfVec.{u} p.1 hp.1 p.2) ∈ UI N (RelBase.{u} m) {i} := by
    rw [UI_singleton]; exact hW.2
  rw [secFun_of_mem _ hp.1 hW]
  change p.1 i ^ (e : ℤ) * evπ.{u} p.1 hp.1 p.2 hW (unitComp s i) = _
  rw [← evπ_restrictOpen hUI p.1 hp.1 p.2 hWI, evπ_UI_singleton p.1 hp.1 p.2 i hi]
  -- the component over `UI {i}` is `p / Xᵢᵉ`
  set t := TopCat.Presheaf.restrictOpen (unitComp s i) (UI N (RelBase.{u} m) {i}) hUI
  have ht : unitSectionsEquiv _ _ (twistSectionsEquiv (cocycle N (RelBase.{u} m) ^ (e : ℤ)) i
      (UI_le_U (Finset.mem_singleton_self i))
      (TopCat.Presheaf.restrictOpen s (UI N (RelBase.{u} m) {i}) le_top)) = t :=
    ores_res (X := ℙₒ(N; RelBase.{u} m)) (V := ⊤ ⊓ U N (RelBase.{u} m) i)
      (W := UI N (RelBase.{u} m) {i} ⊓ U N (RelBase.{u} m) i) (inf_le_inf_right _ le_top)
      (le_inf le_rfl (UI_singleton i).le) (unitComp s i)
  have hs := sectionsUIEquiv_apply (R := RelBase.{u} m) (k := e) (Finset.singleton_nonempty i)
    (Finset.mem_singleton_self i) (TopCat.Presheaf.restrictOpen s (UI N _ {i}) le_top)
  rw [ht] at hs
  have hsp := sectionsUIEquiv_globalSectionsEquiv_symm (R := RelBase.{u} m) hN e
    (globalSectionsEquiv hN e s) i
  rw [AddEquiv.symm_apply_apply] at hsp
  rw [hsp] at hs
  -- evaluate
  set L := Localization.awayLift (eval₂Hom (evalBase.{u} p.2) p.1) (prodX (RelBase.{u} m) {i})
    (by simpa using (eval₂_prodX_singleton_ne_zero.{u} p.1 p.2 i hi).isUnit)
  have hL := congrArg L hs
  have hLX : L (algebraMap (MvPolynomial (Fin (N + 1)) (RelBase.{u} m)) _ (X i)) = p.1 i := by
    rw [IsLocalization.Away.lift_eq]
    simp
  have hLp : L (algebraMap _ _ (globalSectionsEquiv hN e s :
      MvPolynomial (Fin (N + 1)) (RelBase.{u} m))) = eval₂ (evalBase.{u} p.2) p.1
        (globalSectionsEquiv hN e s : MvPolynomial (Fin (N + 1)) (RelBase.{u} m)) :=
    IsLocalization.Away.lift_eq _ _ _
  rw [hLp, map_mul, zpow_natCast, Units.val_pow_eq_pow_val, map_pow, val_xUnit, hLX] at hL
  refine Eq.trans ?_ hL.symm
  rw [zpow_natCast]
  rfl

open CechProjectiveAn CechProjectiveBox in
/-- **The section of `𝒪(e)^an` over `D × ℙᴺ` with coefficients `c`** is
`(v, y) ↦ ∑_{|s| = e} c_s(y) vˢ`. -/
theorem anTwFun_tubeSectionsEquiv_symm (e : ℕ) (c : MonoExp N e → OkaRing D)
    {p : (Fin (N + 1) → ℂ) × (Fin m → ℂ)} (hp : p ∈ vecCone.{u} (tube.{u} (N := N) D)) :
    anTwFun ((tubeSectionsEquiv.{u} D e).symm c) p =
      ∑ s : MonoExp N e, (c s).toGlobalFun _ p.2 * ∏ j, p.1 j ^ s.1 j := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hp.1
  set t := (tubeSectionsEquiv.{u} D e).symm c
  have ht : tubeSectionsEquivKer D e t = monoExpEquivKer D e c := by
    have h := (tubeSectionsEquiv.{u} D e).apply_symm_apply c
    change (monoExpEquivKer D e).symm (tubeSectionsEquivKer D e t) = c at h
    rw [← h, AddEquiv.apply_symm_apply]
  have hval := congrArg (fun z ↦ (((z.1 : PCochain N (e : ℤ) D 0) fun _ ↦ i :
    holP (e : ℤ) D _) : (Fin (N + 1) → ℂ) × (Fin m → ℂ) → ℂ) p) ht
  have hpi : p ∈ vecCone.{u} (TopCat.Presheaf.cechOpen (stdCoverAn D)
      (fun _ : Fin 1 ↦ (ULift.up i : ULift.{u} (Fin (N + 1))))) := by
    rw [vecCone_cechOpen]
    refine ⟨fun j hj ↦ ?_, baseY_mem_of_mem_vecCone hp⟩
    simp only [SimplexCochain.im, Finset.mem_image, Finset.mem_univ, true_and] at hj
    obtain ⟨_, rfl⟩ := hj
    exact hi
  have hl : (((tubeSectionsEquivKer D e t).1 : PCochain N (e : ℤ) D 0) fun _ ↦ i :
      (Fin (N + 1) → ℂ) × (Fin m → ℂ) → ℂ) p = anTwFun t p := by
    change twFun ((twistingSheafAnIso m N e).hom.val.app _ (modRes t _ _)) p = _
    rw [modHom_modRes, twFun_modRes, Set.indicator_of_mem hpi]
    rfl
  rw [← hl, hval]
  change (holPAug N D e c (fun _ ↦ i) : (Fin (N + 1) → ℂ) × (Fin m → ℂ) → ℂ) (p.1, p.2) = _
  refine (holPAug_apply c _ ?_ (baseY_mem_of_mem_vecCone hp)).trans ?_
  · intro j hj
    simp only [SimplexCochain.im, Finset.mem_image, Finset.mem_univ, true_and] at hj
    obtain ⟨_, rfl⟩ := hj
    exact hi
  · rfl

/-! ### Global sections of `𝒪(e)` over `A` -/

open CechProjectiveBox

/-- The exponent `s ∈ ℕᴺ⁺¹`, `|s| = e`, as a finitely supported function. -/
noncomputable abbrev monoExpFinsupp {e : ℕ} (s : MonoExp N e) : Fin (N + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm s.1

lemma degree_monoExpFinsupp {e : ℕ} (s : MonoExp N e) : (monoExpFinsupp s).degree = e := by
  rw [Finsupp.degree_eq_sum]
  exact Finset.Nat.mem_antidiagonalTuple.1 s.2

/-- The monomial `Xˢ`, `|s| = e`, as a homogeneous polynomial of degree `e`. -/
noncomputable def monoPoly {e : ℕ} (s : MonoExp N e) : 𝒜 e :=
  ⟨monomial (monoExpFinsupp s) 1,
    (mem_homogeneousSubmodule _ _).2 (isHomogeneous_monomial _ (degree_monoExpFinsupp s))⟩

/-- The global section `Xˢ` of `𝒪(e)`, `|s| = e`. -/
noncomputable def monoSec (hN : 1 ≤ N) {e : ℕ} (s : MonoExp N e) :
    AlgSec (twistingSheaf N (RelBase.{u} m) e) :=
  (globalSectionsEquiv hN e).symm (monoPoly s)

lemma eval₂_monoPoly {e : ℕ} (s : MonoExp N e) (y : Fin m → ℂ) (v : Fin (N + 1) → ℂ) :
    eval₂ (evalBase.{u} y) v (monoPoly.{u} (m := m) s : MvPolynomial (Fin (N + 1)) _) =
      ∏ j, v j ^ s.1 j := by
  simp only [monoPoly, eval₂_monomial, map_one, one_mul]
  rw [Finsupp.prod_fintype _ _ (fun j ↦ pow_zero _)]
  rfl

/-- **A homogeneous polynomial is the sum of its monomials.** -/
lemma eq_sum_monoPoly {e : ℕ} (p : 𝒜 e) :
    (p : MvPolynomial (Fin (N + 1)) (RelBase.{u} m)) =
      ∑ s : MonoExp N e, C (coeff (monoExpFinsupp s) (p : MvPolynomial _ _)) *
        (monoPoly.{u} (m := m) s : MvPolynomial (Fin (N + 1)) (RelBase.{u} m)) := by
  refine MvPolynomial.ext _ _ fun d ↦ ?_
  simp only [monoPoly, coeff_sum, coeff_C_mul, coeff_monomial]
  by_cases hd : d.degree = e
  · have hmem : (d : Fin (N + 1) → ℕ) ∈ Finset.Nat.antidiagonalTuple (N + 1) e := by
      rw [Finset.Nat.mem_antidiagonalTuple, ← hd, Finsupp.degree_eq_sum]
    rw [Finset.sum_eq_single ⟨_, hmem⟩]
    · simp [monoExpFinsupp]
    · intro t _ ht
      rw [if_neg, mul_zero]
      intro h
      apply ht
      apply Subtype.ext
      subst h
      rfl
    · simp
  · rw [Finset.sum_eq_zero]
    · by_contra hc
      exact hd ((congrFun (congrArg DFunLike.coe Finsupp.degree_eq_weight_one) d).trans
        ((mem_homogeneousSubmodule _ _).1 p.2 hc))
    · intro t _
      rw [if_neg, mul_zero]
      rintro rfl
      exact hd (degree_monoExpFinsupp t)

/-- **The action of the constants on global sections of `𝒪(e)`** is multiplication of
polynomials. -/
lemma globalSectionsEquiv_smul (hN : 1 ≤ N) (e : ℕ) (a : RelBase.{u} m)
    (s : AlgSec (twistingSheaf N (RelBase.{u} m) e)) :
    (globalSectionsEquiv hN e (a • s) : MvPolynomial (Fin (N + 1)) (RelBase.{u} m)) =
      C a * (globalSectionsEquiv hN e s : MvPolynomial (Fin (N + 1)) (RelBase.{u} m)) := by
  set p := globalSectionsEquiv hN e s
  have hq : C a * (p : MvPolynomial (Fin (N + 1)) (RelBase.{u} m)) ∈ 𝒜 e := by
    rw [mem_homogeneousSubmodule]
    simpa using (isHomogeneous_C (Fin (N + 1)) a).mul ((mem_homogeneousSubmodule _ _).1 p.2)
  suffices h : a • s = (globalSectionsEquiv hN e).symm ⟨_, hq⟩ by
    rw [h, AddEquiv.apply_symm_apply]
  apply globalCoeff_injective (e : ℤ) 0
  have h0 : ((0 : Fin (N + 1)) ∈ ({0} : Finset (Fin (N + 1)))) := Finset.mem_singleton_self 0
  change awayCoeff _ {0} _ = awayCoeff _ {0} _
  congr 1
  rw [sectionsUIEquiv_globalSectionsEquiv_symm]
  have hres : TopCat.Presheaf.restrictOpen (a • s : AlgSec (twistingSheaf N (RelBase.{u} m) e))
      (UI N (RelBase.{u} m) {0}) le_top =
      TopCat.Presheaf.restrictOpen (constRingHom.{u} N a) (UI N (RelBase.{u} m) {0}) le_top •
        TopCat.Presheaf.restrictOpen s (UI N (RelBase.{u} m) {0}) le_top :=
    Scheme.Modules.map_smul _ _ _ _
  rw [hres, sectionsUIEquiv_smul]
  have hc : TopCat.Presheaf.restrictOpen (constRingHom.{u} N a) (UI N (RelBase.{u} m) {0})
      le_top = Proj.awayToSection 𝒜 _ (awayConst _ a) :=
    restrict_toSpec_appTop (prod_X_mem_homogeneousSubmodule _) (card_pos_of_mem h0) a
  rw [hc, toAway_awayToSection]
  have hs := sectionsUIEquiv_globalSectionsEquiv_symm (R := RelBase.{u} m) hN e p 0
  rw [AddEquiv.symm_apply_apply] at hs
  rw [hs, map_mul]
  rfl

/-- **`Γ(P, 𝒪(e))` is spanned by the monomials over `A`**: `s = ∑_{|t| = e} p_t • Xᵗ` for
`p = globalSectionsEquiv s`. -/
lemma eq_sum_smul_monoSec (hN : 1 ≤ N) (e : ℕ)
    (s : AlgSec (twistingSheaf N (RelBase.{u} m) e)) :
    s = ∑ t : MonoExp N e, coeff (monoExpFinsupp t)
      (globalSectionsEquiv hN e s : MvPolynomial (Fin (N + 1)) (RelBase.{u} m)) • monoSec hN t := by
  apply (globalSectionsEquiv (R := RelBase.{u} m) hN e).injective
  apply Subtype.ext
  have h1 := map_sum (globalSectionsEquiv (R := RelBase.{u} m) hN e)
    (fun t ↦ coeff (monoExpFinsupp t)
      (globalSectionsEquiv hN e s : MvPolynomial (Fin (N + 1)) (RelBase.{u} m)) • monoSec hN t)
    Finset.univ
  refine Eq.trans ?_ (congrArg Subtype.val h1).symm
  rw [Submodule.coe_sum]
  refine (eq_sum_monoPoly _).trans (Finset.sum_congr rfl fun t _ ↦ ?_)
  refine Eq.trans ?_ (globalSectionsEquiv_smul hN e _ (monoSec hN t)).symm
  rw [monoSec, AddEquiv.apply_symm_apply]

/-! ### The canonical map for `𝒪(e)` -/

variable (hN : 1 ≤ N)

lemma anTwFun_sum {ι : Type*} (s : Finset ι)
    (x : ι → AnSec D (twistingSheaf N (RelBase.{u} m) k)) :
    anTwFun (∑ i ∈ s, x i) = ∑ i ∈ s, anTwFun (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [anTwFun_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, anTwFun_add, ih, Finset.sum_insert ha]

variable (D) in
/-- The element `∑_s c_s ⊗ Xˢ` of `𝒪(D) ⊗_A Γ(P, 𝒪(e))`. -/
noncomputable def monoTensor (e : ℕ) (c : MonoExp N e → OkaRing D) :
    OkaRing D ⊗[RelBase.{u} m] AlgSec (twistingSheaf N (RelBase.{u} m) e) :=
  ∑ s, c s ⊗ₜ monoSec hN s

include hN in
lemma canMap_monoTensor (e : ℕ) (c : MonoExp N e → OkaRing D) :
    canMap D _ (monoTensor D hN e c) = (tubeSectionsEquiv.{u} D e).symm c := by
  apply anTwFun_injective
  funext p
  simp only [monoTensor, map_sum, canMap_tmul]
  rw [anTwFun_sum, Finset.sum_apply]
  by_cases hp : p ∈ vecCone.{u} (tube.{u} (N := N) D)
  · rw [anTwFun_tubeSectionsEquiv_symm e c hp]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [anTwFun_smul _ _ hp, anTwFun_algSec hN e _ hp, monoSec, AddEquiv.apply_symm_apply,
      eval₂_monoPoly]
  · rw [anTwFun_of_notMem _ hp]
    exact Finset.sum_eq_zero fun s _ ↦ anTwFun_of_notMem _ hp

include hN in
lemma surjective_monoTensor (e : ℕ) : Function.Surjective (monoTensor.{u} D hN e) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp [monoTensor]⟩
  | tmul f s =>
    refine ⟨fun t ↦ polyToOka.{u} D (coeff (monoExpFinsupp t)
      (globalSectionsEquiv hN e s : MvPolynomial (Fin (N + 1)) (RelBase.{u} m))) * f, ?_⟩
    conv_rhs => rw [eq_sum_smul_monoSec hN e s]
    rw [TensorProduct.tmul_sum, monoTensor]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
    rfl
  | add x y hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨c', rfl⟩ := hy
    exact ⟨c + c', by simp [monoTensor, TensorProduct.add_tmul, Finset.sum_add_distrib]⟩

include hN in
/-- **The canonical map `𝒪(D) ⊗_A Γ(P, 𝒪(e)) → Γ(D × ℙᴺ, 𝒪(e)^an)` is bijective** for
`e ≥ 0`, `N ≥ 1` and every open `D ⊆ ℂᵐ`. -/
theorem bijective_canMap_twistingSheaf (e : ℕ) (D : Opens (Fin m → ℂ)) :
    Function.Bijective (canMap D (twistingSheaf N (RelBase.{u} m) e)) := by
  refine ⟨fun x x' h ↦ ?_, fun y ↦ ⟨monoTensor D hN e (tubeSectionsEquiv D e y), by
    rw [canMap_monoTensor, AddEquiv.symm_apply_apply]⟩⟩
  obtain ⟨c, rfl⟩ := surjective_monoTensor hN e x
  obtain ⟨c', rfl⟩ := surjective_monoTensor hN e x'
  rw [canMap_monoTensor, canMap_monoTensor] at h
  rw [(tubeSectionsEquiv D e).symm.injective h]

include hN in
/-- **Relative base change for sections over boxes**: for a coherent sheaf `G` on
`P = ℙₒ(N; ℂ[y₀, …, y_{m-1}])`, `N ≥ 1`, there is `n₀`, depending only on `G`, such that the
canonical map `𝒪(B) ⊗_A Γ(P, G(n)) → Γ(B × ℙᴺ, G(n)^an)` is bijective for all `n ≥ n₀` and all
open boxes `B ⊆ ℂᵐ`. -/
theorem exists_bijective_canMap (G : ℙₒ(N; RelBase.{u} m).Modules) [G.IsCoherent] :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ∀ (a b : Fin m → ℂ) (B : Opens (Fin m → ℂ)),
      (B : Set (Fin m → ℂ)) = Complex.openBox a b →
        Function.Bijective (canMap B (twist G n)) :=
  exists_bijective_canMap_of_twistingSheaf (fun e D ↦ bijective_canMap_twistingSheaf hN e D) G

end ComplexAnalytic.relProjectiveSpaceAn

end
