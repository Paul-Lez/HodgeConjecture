/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Algebra.Field.ULift
public import Other.Oka.Analytification.GAGA.FiveLemma
public import Other.Oka.Analytification.GAGA.ClosedImmersionCohomology
public import Other.Oka.Analytification.GAGA.ClosedImmersionPushforward
public import Other.Oka.Analytification.GAGA.ProjectiveSpaceGlobalSections
public import Other.Oka.Analytification.GAGA.TwistCechAn
public import Other.Oka.Analytification.GAGA.TwistTransition
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.GermChart
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.HyperplaneSequence
public import Other.Oka.AlgebraicGeometry.ProjectiveSpace.Vanishing

/-!
# GAGA for the twisting sheaves `O(k)` on `ℙⁿ`

The GAGA comparison map `Hᵠ(ℙⁿ, O(k)) → Hᵠ(ℙⁿ_an, O(k)^an)` is bijective for all `n, q ≥ 0`
and `k ∈ ℤ` (`ComplexAnalytic.bijective_gagaMap_twistingSheaf`).

The proof is Serre's:
1. `k = 0`: in degree `0` the comparison map is `π^♯ : Γ(ℙⁿ, 𝒪) → Γ(ℙⁿ_an, 𝒪)` up to the
   isomorphism `𝒪^an ≅ 𝒪`; it is surjective since global analytic functions on `ℙⁿ_an` are
   constant, and injective since the stalk maps of `π` are faithfully flat and the charts of `ℙⁿ`
   are integral. In degrees `q ≥ 1` both sides vanish
   (`AlgebraicGeometry.ProjectiveSpace.locallyRingedSpaceH_twistingSheaf_eq_zero`,
   `ComplexAnalytic.projectiveSpaceAn.H_twistingSheafAn_eq_zero`).
2. On `ℙ⁰` every `O(k)` is isomorphic to `𝒪`
   (`AlgebraicGeometry.ProjectiveSpace.twistingSheafZeroIsoUnit`).
3. On `ℙⁿ⁺¹` the hyperplane sequence `0 → O(k) → O(k + 1) → ι_* O(k + 1) → 0`, the five lemma
   and the compatibility of the comparison map with pushforward along the closed immersion
   `ι : ℙⁿ → ℙⁿ⁺¹` (together with GAGA on `ℙⁿ`) give GAGA for `O(k + 1)` from GAGA for `O(k)`
   and conversely.

## Main definitions and results

- `ComplexAnalytic.projectiveSpaceHyperplane n : projectiveSpace n ⟶ projectiveSpace (n + 1)`,
  the hyperplane `{Xₙ₊₁ = 0}` as a morphism of schemes locally of finite type over `ℂ`.
- `ComplexAnalytic.bijective_gagaMap_unit_zero`: GAGA for `𝒪` on `ℙⁿ` in degree `0`;
  `ComplexAnalytic.bijective_gagaMap_unit`: GAGA for `𝒪` on `ℙⁿ`.
- `ComplexAnalytic.bijective_gagaMap_twistingSheaf_succ`: GAGA for all `O(k)` on `ℙⁿ` implies
  GAGA for all `O(k)` on `ℙⁿ⁺¹`.
- `ComplexAnalytic.bijective_gagaMap_twistingSheaf`: GAGA for `O(k)` on `ℙⁿ`.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic

open AnalyticSpace

/-! ### The hyperplane as a morphism of schemes locally of finite type over `ℂ` -/

/-- The hyperplane `ℙⁿ ⟶ ℙⁿ⁺¹`, `{Xₙ₊₁ = 0}`, as a morphism over `ℂ`. -/
def projectiveSpaceHyperplane (n : ℕ) : projectiveSpace.{u} n ⟶ projectiveSpace.{u} (n + 1) :=
  ObjectProperty.homMk
    (Over.homMk (ProjectiveSpace.hyperplane n _) ProjectiveSpace.hyperplane_toSpec)

@[simp]
lemma projectiveSpaceHyperplane_hom_left (n : ℕ) :
    (projectiveSpaceHyperplane.{u} n).hom.left = ProjectiveSpace.hyperplane n (ULift.{u} ℂ) :=
  rfl

instance (n : ℕ) : IsClosedImmersion (projectiveSpaceHyperplane.{u} n).hom.left :=
  inferInstanceAs (IsClosedImmersion (ProjectiveSpace.hyperplane n _))

instance (n : ℕ)
    (G : SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf) :
    IsIso (analytificationPushforwardBaseChange (projectiveSpaceHyperplane.{u} n) G) :=
  isIso_analytificationPushforwardBaseChange _ G

/-! ### Degree zero -/

/-- **`π^♯ : Γ(ℙⁿ, 𝒪) → Γ(ℙⁿ_an, 𝒪)` is bijective.** Surjectivity: analytic global functions on
`ℙⁿ_an` are constant. Injectivity: a section killed by `π^♯` has zero germ at a point `π y`
lying in every chart (faithful flatness of the stalk maps of `π`), hence vanishes on every chart,
since the charts are integral. -/
theorem bijective_analytificationπLRS_c_app_top_projectiveSpace (n : ℕ) :
    Function.Bijective ((analytificationπLRS (projectiveSpace.{u} n)).c.app (op ⊤)).hom := by
  set X := projectiveSpace.{u} n
  set π := analytificationπLRS X
  have hconst (c : ℂ) : π.c.app (op ⊤) (schemeConst X (ULift.up c)) =
      (projectiveSpaceAn.{u} n).algebraMap c :=
    RingHom.congr_fun (comapAlgMap_analytificationπ_schemeConst X) (ULift.up c)
  refine ⟨(injective_iff_map_eq_zero _).2 fun s hs ↦ ?_, fun t ↦ ?_⟩
  · set y := projectiveSpaceAn.basePoint.{u} n
    have hgerm : ℙₒ(n; ULift.{u} ℂ).presheaf.germ ⊤ (π.base y) trivial s = 0 := by
      refine (faithfullyFlat_stalkMap_analytificationπ X y).injective
        (((LocallyRingedSpace.stalkMap_germ_apply π ⊤ y trivial s).trans ?_).trans
          (map_zero _).symm)
      exact (congrArg _ hs).trans (map_zero _)
    have hmem (i : Fin (n + 1)) : π.base y ∈ ProjectiveSpace.UI n (ULift.{u} ℂ) {i} := by
      rw [ProjectiveSpace.UI_singleton]
      have := projectiveSpaceAn.basePoint_mem_range_chart.{u} (n := n) i
      rw [projectiveSpaceAn.range_chart] at this
      exact this
    have hres (i : Fin (n + 1)) :
        TopCat.Presheaf.restrictOpen s (ProjectiveSpace.UI n (ULift.{u} ℂ) {i}) le_top = 0 := by
      refine ProjectiveSpace.germ_UI_injective (Finset.singleton_nonempty i) _ (hmem i) ?_
      refine (ℙₒ(n; ULift.{u} ℂ).presheaf.germ_res_apply (homOfLE le_top) _ (hmem i) s).trans ?_
      exact hgerm.trans (map_zero _).symm
    refine TopCat.Presheaf.section_ext ℙₒ(n; ULift.{u} ℂ).sheaf ⊤ s 0 fun z hz ↦ ?_
    change ℙₒ(n; ULift.{u} ℂ).presheaf.germ ⊤ z hz s = ℙₒ(n; ULift.{u} ℂ).presheaf.germ ⊤ z hz 0
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1
      ((ProjectiveSpace.iSup_UI_singleton (n := n) (R := ULift.{u} ℂ)).ge (Set.mem_univ z))
    rw [← TopCat.Presheaf.germ_res_apply ℙₒ(n; ULift.{u} ℂ).presheaf (homOfLE le_top) z hi,
      ← TopCat.Presheaf.germ_res_apply ℙₒ(n; ULift.{u} ℂ).presheaf (homOfLE le_top) z hi]
    exact congrArg _ ((hres i).trans (map_zero _).symm)
  · obtain ⟨c, rfl⟩ := projectiveSpaceAn.bijective_algebraMap.{u} (n := n).2 t
    exact ⟨_, hconst c⟩

/-- **GAGA for `𝒪` on `ℙⁿ` in degree `0`**: `H⁰(ℙⁿ, 𝒪) → H⁰(ℙⁿ_an, 𝒪^an)` is bijective. -/
theorem bijective_gagaMap_unit_zero (n : ℕ) :
    Function.Bijective (gagaMap (projectiveSpace.{u} n) (SheafOfModules.unit _) 0) := by
  set X := projectiveSpace.{u} n
  set φ := (analytificationπLRS X).toRingSheafHom
  -- the unit of `(-)^an ⊣ π_*` at `𝒪`, followed by `π_*(𝒪^an ≅ 𝒪)`, is `π^♯`
  have key := (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ)
  rw [Adjunction.homEquiv_unit] at key
  set u := ((analytificationModulesAdj X).unit.app (SheafOfModules.unit _)).val.app (op ⊤)
  set e := asIso (analytificationπLRS X).pullbackModulesUnitToUnit
  have he : Function.Bijective (e.hom.val.app (op ⊤)) :=
    (((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op ⊤)).mapIso
      e).toLinearEquiv).bijective
  have hu : Function.Bijective u := by
    refine (Function.Bijective.of_comp_iff' he u).1 ?_
    have hcomp : ⇑(e.hom.val.app (op ⊤)) ∘ ⇑u =
        ⇑((analytificationπLRS X).c.app (op ⊤)).hom :=
      funext fun a ↦ congrArg (fun f ↦ f.val.app (op ⊤) a) key
    rw [hcomp]
    exact bijective_analytificationπLRS_c_app_top_projectiveSpace.{u} n
  have hc : ⇑(gagaMap X (SheafOfModules.unit _) 0) =
      (LocallyRingedSpace.H.equiv₀ _).symm ∘ u ∘ LocallyRingedSpace.H.equiv₀ _ := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, AddEquiv.eq_symm_apply]
    exact equiv₀_gagaMap _ x
  rw [hc]
  exact (EquivLike.comp_bijective _ _).2 ((EquivLike.bijective_comp _ _).2 hu)

/-! ### GAGA for `O(k)` -/

/-- **`Hᵠ(ℙⁿ_an, 𝒪^an) = 0` for `q ≥ 1`**, from the vanishing for `O(0)^an`. -/
theorem H_analytificationModules_unit_eq_zero (n q : ℕ)
    (x : LocallyRingedSpace.H
      ((analytificationModules (projectiveSpace.{u} n)).obj (SheafOfModules.unit _)) (q + 1)) :
    x = 0 := by
  obtain ⟨y, rfl⟩ := (bijective_H_map_hom ((analytificationModules (projectiveSpace.{u} n)).mapIso
    (ProjectiveSpace.twistZeroIso (SheafOfModules.unit _))) (q + 1)).2 x
  exact (congrArg _ (projectiveSpaceAn.H_twistingSheafAn_eq_zero 0 (by omega) q y)).trans
    (map_zero _)

/-- **GAGA for `𝒪` on `ℙⁿ`**: `Hᵠ(ℙⁿ, 𝒪) → Hᵠ(ℙⁿ_an, 𝒪^an)` is bijective for all `q`. -/
theorem bijective_gagaMap_unit (n q : ℕ) :
    Function.Bijective (gagaMap (projectiveSpace.{u} n) (SheafOfModules.unit _) q) := by
  cases q with
  | zero => exact bijective_gagaMap_unit_zero n
  | succ q =>
    have h0 (x : LocallyRingedSpace.H (SheafOfModules.unit
        (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf) (q + 1)) : x = 0 := by
      obtain ⟨y, rfl⟩ := (bijective_H_map_hom
        (ProjectiveSpace.twistZeroIso (SheafOfModules.unit _)) (q + 1)).2 x
      exact (congrArg _ (ProjectiveSpace.locallyRingedSpaceH_twistingSheaf_eq_zero 0
        (by omega) q y)).trans (map_zero _)
    exact ⟨fun a b _ ↦ (h0 a).trans (h0 b).symm,
      fun y ↦ ⟨0, (map_zero _).trans (H_analytificationModules_unit_eq_zero n q y).symm⟩⟩

/-- **GAGA for `O(k)` on `ℙⁿ⁺¹` from GAGA for all `O(k)` on `ℙⁿ`**, by the hyperplane sequence
`0 → O(k) → O(k + 1) → ι_* O(k + 1) → 0` and the five lemma, inductively from `k = 0`. -/
theorem bijective_gagaMap_twistingSheaf_succ (n : ℕ)
    (ih : ∀ (k : ℤ) (q : ℕ), Function.Bijective
      (gagaMap (projectiveSpace.{u} n) (ProjectiveSpace.twistingSheaf n (ULift.{u} ℂ) k) q))
    (k : ℤ) (q : ℕ) :
    Function.Bijective (gagaMap (projectiveSpace.{u} (n + 1))
      (ProjectiveSpace.twistingSheaf (n + 1) (ULift.{u} ℂ) k) q) := by
  have hS (m : ℤ) : (show ShortComplex (SheafOfModules.{u}
      (projectiveSpace.{u} (n + 1)).obj.left.toLocallyRingedSpace.ringSheaf) from
    ProjectiveSpace.hyperplaneSequence n (ULift.{u} ℂ) m).ShortExact :=
    ProjectiveSpace.hyperplaneSequence_shortExact n (ULift.{u} ℂ) m
  have hι (m : ℤ) (q : ℕ) : Function.Bijective (gagaMap (projectiveSpace.{u} (n + 1))
      ((ProjectiveSpace.hyperplaneSequence n (ULift.{u} ℂ) m).X₃) q) :=
    (bijective_gagaMap_pushforward_iff (projectiveSpaceHyperplane.{u} n)
      (ProjectiveSpace.twistingSheaf n (ULift.{u} ℂ) (m + 1)) q).2 (ih (m + 1) q)
  induction k using Int.induction_on generalizing q with
  | zero =>
    exact (gagaMap_bijective_iff_of_iso (ProjectiveSpace.twistZeroIso _) q).2
      (bijective_gagaMap_unit (n + 1) q)
  | succ m ih' =>
    exact gagaMap_bijective_X₂_of_shortExact (hS m) ih' (hι m) q
  | pred m ih' =>
    have ih'' (q : ℕ) : Function.Bijective (gagaMap (projectiveSpace.{u} (n + 1))
        (ProjectiveSpace.twistingSheaf (n + 1) (ULift.{u} ℂ) (-(m : ℤ) - 1 + 1)) q) := by
      rw [show -(m : ℤ) - 1 + 1 = -m by ring]
      exact ih' q
    exact gagaMap_bijective_X₁_of_shortExact (hS (-(m : ℤ) - 1)) ih'' (hι _) q

/-- **GAGA for the twisting sheaves on `ℙⁿ`**: for all `n, q ≥ 0` and `k ∈ ℤ`, the comparison map
`Hᵠ(ℙⁿ, O(k)) → Hᵠ(ℙⁿ_an, O(k)^an)` is bijective. -/
theorem bijective_gagaMap_twistingSheaf (n : ℕ) (k : ℤ) (q : ℕ) :
    Function.Bijective (gagaMap (projectiveSpace.{u} n)
      (ProjectiveSpace.twistingSheaf n (ULift.{u} ℂ) k) q) := by
  induction n generalizing k q with
  | zero =>
    exact (gagaMap_bijective_iff_of_iso (ProjectiveSpace.twistingSheafZeroIsoUnit k) q).2
      (bijective_gagaMap_unit 0 q)
  | succ n ih => exact bijective_gagaMap_twistingSheaf_succ n ih k q

end ComplexAnalytic

end
