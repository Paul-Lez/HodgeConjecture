/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.Modules.CocycleTwist

/-!
# Pulling back sections of twisted structure sheaves

Let `φ : Y ⟶ X` be a morphism of schemes, `U : κ → X.Opens` and `U' : κ' → Y.Opens` families of
opens with an index map `e : κ' → κ` such that `U' j ≤ φ⁻¹(U (e j))`, and `c`, `d` cocycles on
`U`, `U'`. If `d` is the pullback of `c` (`Cocycle.IsPullback`: `φ^♯ c_{e i, e j} = d_{i j}`),
then `φ^♯` induces a morphism of `𝒪_X`-modules

  `𝒪_X ⊗ L_c ⟶ φ_*(𝒪_Y ⊗ L_d)`, `(sᵢ)ᵢ ↦ (φ^♯ s_{e j})ⱼ`,

the adjoint of `φ^* L_c ≅ L_d`. Pullbacks of cocycles are closed under products and inverses, so
`d ^ m` is the pullback of `c ^ m` for every `m : ℤ` (`Cocycle.IsPullback.zpow`).

## Main definitions and results

- `Scheme.Modules.Cocycle.IsPullback`, `Cocycle.IsPullback.zpow`.
- `Scheme.Modules.twistUnitToPushforward`: the morphism `𝒪_X ⊗ L_c ⟶ φ_*(𝒪_Y ⊗ L_d)`.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.Modules

/-- Sections over an open contained in `⊥` form a subsingleton. -/
lemma _root_.AlgebraicGeometry.Scheme.subsingleton_sections_of_le_bot {X : Scheme.{u}}
    {W : X.Opens} (hW : W ≤ ⊥) : Subsingleton Γ(X, W) := by
  obtain rfl := le_bot_iff.mp hW
  infer_instance

section Pushforward

variable {X Y : Scheme.{u}} (φ : Y ⟶ X)

/-- `φ^♯` after restriction of the source section. -/
lemma appLE_res {U U' : X.Opens} (hU : U' ≤ U) {W : Y.Opens} (e : W ≤ φ ⁻¹ᵁ U')
    (x : Γ(X, U)) :
    φ.appLE U' W e (TopCat.Presheaf.restrictOpen x U' hU) =
      φ.appLE U W (e.trans (φ.preimage_mono hU)) x :=
  congr($(φ.map_appLE e (homOfLE hU).op) x)

/-- Restriction after `φ^♯`. -/
lemma res_appLE {U : X.Opens} {W W' : Y.Opens} (e : W ≤ φ ⁻¹ᵁ U) (hW : W' ≤ W) (x : Γ(X, U)) :
    TopCat.Presheaf.restrictOpen (φ.appLE U W e x) W' hW = φ.appLE U W' (hW.trans e) x :=
  congr($(φ.appLE_map e (homOfLE hW).op) x)

/-- `φ.app` followed by restriction is `φ.appLE`. -/
lemma app_res_eq_appLE {U : X.Opens} {W : Y.Opens} (hW : W ≤ φ ⁻¹ᵁ U) (x : Γ(X, U)) :
    TopCat.Presheaf.restrictOpen (φ.app U x) W hW = φ.appLE U W hW x :=
  rfl

/-- Restriction in the unit module is restriction in the structure sheaf. -/
lemma unit_mres {Z : Scheme.{u}} {W W' : Z.Opens} (h : W' ≤ W)
    (x : Γ(SheafOfModules.unit Z.ringCatSheaf, W)) :
    TopCat.Presheaf.restrictOpen x W' h =
      (TopCat.Presheaf.restrictOpen (show Γ(Z, W) from x) W' h : Γ(Z, W')) :=
  rfl

/-- Scalar multiplication in the unit module is multiplication. -/
lemma unit_smul {Z : Scheme.{u}} {W : Z.Opens} (r : Γ(Z, W))
    (x : Γ(SheafOfModules.unit Z.ringCatSheaf, W)) :
    r • x = (r * (show Γ(Z, W) from x) : Γ(Z, W)) :=
  rfl

variable {κ κ' : Type} {U : κ → X.Opens} {U' : κ' → Y.Opens} (e : κ' → κ)
  (hU : ∀ j, U' j ≤ φ ⁻¹ᵁ U (e j))

include hU in
lemma le_preimage_inf_inf {W : Y.Opens} {i j : κ'} (hW : W ≤ U' i ⊓ U' j) :
    W ≤ φ ⁻¹ᵁ (U (e i) ⊓ U (e j)) :=
  le_inf (hW.trans (inf_le_left.trans (hU i))) (hW.trans (inf_le_right.trans (hU j)))

/-- The cocycle `d` on `U'` is the pullback along `φ` of the cocycle `c` on `U`, along the index
map `e` (with `U' j ≤ φ⁻¹(U (e j))`). -/
def Cocycle.IsPullback (c : Cocycle U) (d : Cocycle U') : Prop :=
  ∀ i j (W : Y.Opens) (hW : W ≤ U' i ⊓ U' j),
    φ.appLE (U (e i) ⊓ U (e j)) W (le_preimage_inf_inf φ e hU hW) (c.g (e i) (e j)) = d.g i j |ₒ W

namespace Cocycle.IsPullback

variable {φ e hU}

lemma one : Cocycle.IsPullback φ e hU (1 : Cocycle U) (1 : Cocycle U') := by
  intro i j W hW
  simp only [one_g, ores_one, map_one]

lemma mul {c c' : Cocycle U} {d d' : Cocycle U'} (h : IsPullback φ e hU c d)
    (h' : IsPullback φ e hU c' d') : IsPullback φ e hU (c * c') (d * d') := by
  intro i j W hW
  simp only [mul_g, ores_mul, map_mul, h i j W hW, h' i j W hW]

lemma inv {c : Cocycle U} {d : Cocycle U'} (h : IsPullback φ e hU c d) :
    IsPullback φ e hU c⁻¹ d⁻¹ := by
  intro i j W hW
  simp only [inv_g, ores_res]
  rw [appLE_res, h j i W (by order)]

lemma zpow {c : Cocycle U} {d : Cocycle U'} (h : IsPullback φ e hU c d) (m : ℤ) :
    IsPullback φ e hU (c ^ m) (d ^ m) := by
  induction m using Int.induction_on with
  | zero => simpa using one
  | succ m ih => simpa [zpow_add_one] using ih.mul h
  | pred m ih => simpa [zpow_sub_one] using ih.mul h.inv

end Cocycle.IsPullback

include hU in
lemma preimage_inf_le (V : X.Opens) (j : κ') : φ ⁻¹ᵁ V ⊓ U' j ≤ φ ⁻¹ᵁ (V ⊓ U (e j)) :=
  le_inf inf_le_left (inf_le_right.trans (hU j))

variable {φ e hU} {c : Cocycle U} {d : Cocycle U'}

variable (φ e hU) in
/-- The components of the pullback of a section of `𝒪_X ⊗ L_c`. -/
noncomputable def twistPullbackComp (V : X.Opens)
    (s : Γ(twist (SheafOfModules.unit X.ringCatSheaf) c, V)) (j : κ') :
    Γ(SheafOfModules.unit Y.ringCatSheaf, φ ⁻¹ᵁ V ⊓ U' j) :=
  φ.appLE (V ⊓ U (e j)) (φ ⁻¹ᵁ V ⊓ U' j) (preimage_inf_le φ e hU V j) (twistComp s (e j))

lemma twistPullbackComp_compat (h : Cocycle.IsPullback φ e hU c d) (V : X.Opens)
    (s : Γ(twist (SheafOfModules.unit X.ringCatSheaf) c, V)) (i j : κ') :
    (twistPullbackComp φ e hU V s i |ₒ (φ ⁻¹ᵁ V ⊓ (U' i ⊓ U' j))) =
      (d.g i j |ₒ (φ ⁻¹ᵁ V ⊓ (U' i ⊓ U' j))) •
        (twistPullbackComp φ e hU V s j |ₒ (φ ⁻¹ᵁ V ⊓ (U' i ⊓ U' j))) := by
  simp only [twistPullbackComp, unit_mres, unit_smul, res_appLE]
  have hW : φ ⁻¹ᵁ V ⊓ (U' i ⊓ U' j) ≤ φ ⁻¹ᵁ (V ⊓ (U (e i) ⊓ U (e j))) :=
    le_inf inf_le_left (le_preimage_inf_inf φ e hU inf_le_right)
  rw [← appLE_res φ (by order : V ⊓ (U (e i) ⊓ U (e j)) ≤ V ⊓ U (e i)) hW,
    ← appLE_res φ (by order : V ⊓ (U (e i) ⊓ U (e j)) ≤ V ⊓ U (e j)) hW,
    ]
  have hc := twistComp_compat s (e i) (e j)
  simp only [unit_mres, unit_smul] at hc
  rw [hc, map_mul, appLE_res φ (by order : V ⊓ (U (e i) ⊓ U (e j)) ≤ U (e i) ⊓ U (e j)) hW,
    h i j _ inf_le_right]

lemma twistPullbackComp_smul (V : X.Opens) (r : Γ(X, V))
    (s : Γ(twist (SheafOfModules.unit X.ringCatSheaf) c, V)) (j : κ') :
    twistPullbackComp φ e hU V (r • s) j =
      TopCat.Presheaf.restrictOpen (φ.app V r) (φ ⁻¹ᵁ V ⊓ U' j) inf_le_left •
        twistPullbackComp φ e hU V s j := by
  simp only [twistPullbackComp, twistComp_smul, unit_smul, map_mul]
  rw [appLE_res]
  rfl

lemma twistPullbackComp_res {V W : X.Opens} (hW : W ≤ V)
    (s : Γ(twist (SheafOfModules.unit X.ringCatSheaf) c, V)) (j : κ') :
    twistPullbackComp φ e hU W (TopCat.Presheaf.restrictOpen s W hW) j =
      TopCat.Presheaf.restrictOpen (twistPullbackComp φ e hU V s j) (φ ⁻¹ᵁ W ⊓ U' j)
        (inf_le_inf_right _ (φ.preimage_mono hW)) := by
  simp only [twistPullbackComp, twistComp_res, unit_mres, res_appLE]
  rw [appLE_res]

variable (φ e hU c d) in
/-- **Pullback of sections of a twisted structure sheaf**: if the cocycle `d` on `U'` is the
pullback of `c` along `φ : Y ⟶ X`, then `φ^♯` induces `𝒪_X ⊗ L_c ⟶ φ_*(𝒪_Y ⊗ L_d)`,
`(sᵢ) ↦ (φ^♯ s_{e j})ⱼ`. -/
noncomputable def twistUnitToPushforward (h : Cocycle.IsPullback φ e hU c d) :
    twist (SheafOfModules.unit X.ringCatSheaf) c ⟶
      (pushforward φ).obj (twist (SheafOfModules.unit Y.ringCatSheaf) d) :=
  homMk (fun V ↦
    { toFun s := twistMk (c := d) (twistPullbackComp φ e hU V s) (twistPullbackComp_compat h V s)
      map_zero' := twist_ext (V := φ ⁻¹ᵁ V) fun _ ↦ map_zero _
      map_add' _ _ := twist_ext (V := φ ⁻¹ᵁ V) fun _ ↦ map_add _ _ _ })
    (fun V r s ↦ twist_ext (V := φ ⁻¹ᵁ V) fun j ↦ twistPullbackComp_smul (hU := hU) V r s j)
    (fun _ W hW s ↦ twist_ext (V := φ ⁻¹ᵁ W) fun j ↦ twistPullbackComp_res (hU := hU) hW s j)

lemma twistComp_twistUnitToPushforward_app (h : Cocycle.IsPullback φ e hU c d) (V : X.Opens)
    (s : Γ(twist (SheafOfModules.unit X.ringCatSheaf) c, V)) (j : κ') :
    twistComp (V := φ ⁻¹ᵁ V) ((twistUnitToPushforward φ e hU c d h).app V s) j =
      twistPullbackComp φ e hU V s j :=
  rfl

end Pushforward

end AlgebraicGeometry.Scheme.Modules

end
