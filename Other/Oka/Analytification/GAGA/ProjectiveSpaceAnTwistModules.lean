/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.HyperplaneModules
public import Other.Oka.AlgebraicGeometry.Modules.CocycleTwistPullbackModules
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesStalkNakayama

/-!
# Twisting analytic sheaves of modules on `ℙⁿ_an`

For a sheaf of modules `M` on `ℙⁿ_an` and `m : ℤ`, the **twist** `M(m)`
(`ComplexAnalytic.projectiveSpaceAn.twistMod M m`) is the twist of `M` by the pullback along
`π : ℙⁿ_an ⟶ ℙⁿ` of the `m`-th power of the standard cocycle `(Xⱼ / Xᵢ)` on the preimages
`π⁻¹ Uᵢ` of the standard charts (`LocallyRingedSpace.modTwist`).

## Main definitions and results

- `twistModFunctor n m`, an autoequivalence (`twistModEquivalence`);
- `twistModTwistModIso : M(a)(b) ≅ M(a + b)`, `twistModZeroIso : M(0) ≅ M`,
  `twistModCongr : M(a) ≅ M(b)` for `a = b`;
- `analytificationTwistIso : (F(m))^an ≅ F^an(m)`;
- `isCoherent_twistMod`: twists of coherent sheaves are coherent;
- `mulXMod M m l : M(m) ⟶ M(m + 1)`, multiplication by the variable `X_l` (by `X_l / Xₖ` on
  `π⁻¹ Uₖ`), and `mulXModZero M l : M(-1) ⟶ M`; on `π⁻¹ Uₖ` its range is `(X_l / Xₖ) · M` and
  its kernel is killed by `X_l / Xₖ` (`rangeLESMul_mulXModZero`, `sMulLERange_mulXModZero`,
  `sMulKerEqZero_mulXModZero`).
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.LocallyRingedSpace AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic.projectiveSpaceAn

variable {n : ℕ}

variable (n) in
/-- The preimage `π⁻¹ Uᵢ ⊆ ℙⁿ_an` of the standard chart `Uᵢ = D₊(Xᵢ)`. -/
abbrev stdOpenAn (i : Fin (n + 1)) : Opens (projectiveSpaceAn.{u} n).toPresheafedSpace :=
  preimOpen (πLRS.{u} n) (ProjectiveSpace.U n (ULift.{u} ℂ) i)

lemma iSup_stdOpenAn : ⨆ i, stdOpenAn.{u} n i = ⊤ :=
  iSup_preimOpen (ProjectiveSpace.iSup_U n (ULift.{u} ℂ))

variable (n) in
/-- The cocycle `π^♯ (Xⱼ / Xᵢ)ᵐ` on the `π⁻¹ Uᵢ`. -/
def twistModCocycle (m : ℤ) : ModCocycle (stdOpenAn.{u} n) :=
  cocycleComap (πLRS.{u} n) (ProjectiveSpace.cocycle n (ULift.{u} ℂ) ^ m)

lemma twistModCocycle_add (a b : ℤ) :
    twistModCocycle.{u} n (a + b) = twistModCocycle n a * twistModCocycle n b := by
  rw [twistModCocycle, zpow_add, cocycleComap_mul]
  rfl

lemma twistModCocycle_zero : twistModCocycle.{u} n 0 = 1 := by
  rw [twistModCocycle, zpow_zero, cocycleComap_one]

/-- The twist `M(m)` of a sheaf of modules on `ℙⁿ_an`. -/
abbrev twistMod (M : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf)
    (m : ℤ) : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf :=
  modTwist M (twistModCocycle n m)

variable (n) in
/-- The functor `M ↦ M(m)` on sheaves of modules on `ℙⁿ_an`. -/
abbrev twistModFunctor (m : ℤ) :
    SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf ⥤
      SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf :=
  modTwistFunctor (twistModCocycle n m)

variable (n) in
/-- `M ↦ M(m)` is an autoequivalence. -/
def twistModEquivalence (m : ℤ) :
    SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf ≌
      SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf :=
  modTwistEquivalence (twistModCocycle n m) iSup_stdOpenAn

/-- Twisting is an equivalence. -/
instance (m : ℤ) : (twistModFunctor.{u} n m).IsEquivalence :=
  (twistModEquivalence n m).isEquivalence_functor

/-- Twisting is additive. -/
instance (m : ℤ) : (twistModFunctor.{u} n m).Additive :=
  Functor.additive_of_preserves_binary_products _

variable (M : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf)

/-- `M(a)(b) ≅ M(a + b)`. -/
def twistModTwistModIso (a b : ℤ) : twistMod (twistMod M a) b ≅ twistMod M (a + b) :=
  (modTwistFunctorCompIso (twistModCocycle n a) (twistModCocycle n b)).app M ≪≫
    (modTwistFunctorCongr (twistModCocycle_add a b).symm).app M

/-- `M(0) ≅ M`. -/
def twistModZeroIso : twistMod M 0 ≅ M :=
  (modTwistFunctorCongr twistModCocycle_zero).app M ≪≫ modTwistOneIso M iSup_stdOpenAn

/-- `M(a) ≅ M(b)` for `a = b`. -/
def twistModCongr {a b : ℤ} (h : a = b) : twistMod M a ≅ twistMod M b :=
  (modTwistFunctorCongr (congrArg (twistModCocycle n) h)).app M

/-- **Analytification commutes with twisting**: `(F(m))^an ≅ F^an(m)`. -/
def analytificationTwistIso
    (F : SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf)
    (m : ℤ) :
    (analytificationModules (projectiveSpace.{u} n)).obj (ProjectiveSpace.twist F m) ≅
      twistMod ((analytificationModules (projectiveSpace.{u} n)).obj F) m :=
  (pullbackModulesTwistIso (πLRS.{u} n) (ProjectiveSpace.cocycle n (ULift.{u} ℂ) ^ m)
    (ProjectiveSpace.iSup_U n (ULift.{u} ℂ))).app F

/-- **Twists of coherent sheaves on `ℙⁿ_an` are coherent.** -/
theorem isCoherent_twistMod [M.IsCoherent] (m : ℤ) : (twistMod M m).IsCoherent :=
  isCoherent_modTwist M _ iSup_stdOpenAn

section MulX

variable (n) in
/-- The section `π^♯ (X_l / Xₖ)` over `π⁻¹ Uₖ`. -/
abbrev xDivAn (k l : Fin (n + 1)) :
    (projectiveSpaceAn.{u} n).presheaf.obj (op (stdOpenAn.{u} n k)) :=
  pbSec (πLRS.{u} n) (ProjectiveSpace.xDiv k l)

lemma xDivAn_compat (l i j : Fin (n + 1)) :
    (xDivAn.{u} n i l |ₒ (stdOpenAn n i ⊓ stdOpenAn n j)) =
      (twistModCocycle n 1).g i j * (xDivAn n j l |ₒ (stdOpenAn n i ⊓ stdOpenAn n j)) := by
  have h := congrArg (pbSec (πLRS.{u} n)) (ProjectiveSpace.xDiv_compat (R := ULift.{u} ℂ) l i j)
  rw [pbSec_mul, pbSec_res, pbSec_res] at h
  rw [twistModCocycle, zpow_one]
  exact h

/-- **Multiplication by the variable `X_l`**, `M(m) ⟶ M(m + 1)`: on `π⁻¹ Uₖ` it is
multiplication by `π^♯ (X_l / Xₖ)`. -/
def mulXMod (m : ℤ) (l : Fin (n + 1)) : twistMod M m ⟶ twistMod M (m + 1) :=
  modTwistMulSection M (twistModCocycle n m) (twistModCocycle n 1) (fun k ↦ xDivAn n k l)
    (xDivAn_compat l) ≫ (modTwistFunctorCongr (twistModCocycle_add m 1).symm).hom.app M

@[simp]
lemma modTwistComp_mulXMod_app (m : ℤ) (l : Fin (n + 1)) {W : Opens _}
    (s : (twistMod M m).val.obj (op W)) (k : Fin (n + 1)) :
    modTwistComp ((mulXMod M m l).val.app (op W) s) k =
      (xDivAn n k l |ₒ (W ⊓ stdOpenAn n k)) • modTwistComp s k :=
  rfl

/-- In the chart `k`, multiplication by `X_l` is multiplication by `π^♯ (X_l / Xₖ)`. -/
lemma modTwistSectionsEquiv_mulXMod (m : ℤ) (l k : Fin (n + 1)) {W : Opens _}
    (hW : W ≤ stdOpenAn n k) (s : (twistMod M m).val.obj (op W)) :
    modTwistSectionsEquiv (twistModCocycle n (m + 1)) k hW ((mulXMod M m l).val.app (op W) s) =
      (xDivAn n k l |ₒ W) • modTwistSectionsEquiv (twistModCocycle n m) k hW s := by
  rw [modTwistSectionsEquiv_apply, modTwistSectionsEquiv_apply, modTwistComp_mulXMod_app,
    modRes_smul, yres_res]

/-- Multiplication by `X_l`, `M(-1) ⟶ M`. -/
def mulXModZero (l : Fin (n + 1)) : twistMod M (-1) ⟶ M :=
  mulXMod M (-1) l ≫ (twistModCongr M (neg_add_cancel 1) ≪≫ twistModZeroIso M).hom

lemma rangeLESMul_mulXMod (m : ℤ) (l k : Fin (n + 1)) :
    RangeLESMul (mulXMod M m l) (xDivAn n k l) := by
  intro W hW s
  refine ⟨(modTwistSectionsEquiv (twistModCocycle n (m + 1)) k hW).symm
    (modTwistSectionsEquiv (twistModCocycle n m) k hW s),
    (modTwistSectionsEquiv (twistModCocycle n (m + 1)) k hW).injective ?_⟩
  rw [modTwistSectionsEquiv_mulXMod, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]

lemma sMulLERange_mulXMod (m : ℤ) (l k : Fin (n + 1)) :
    SMulLERange (mulXMod M m l) (xDivAn n k l) := by
  intro W hW q
  refine ⟨(modTwistSectionsEquiv (twistModCocycle n m) k hW).symm
    (modTwistSectionsEquiv (twistModCocycle n (m + 1)) k hW q),
    (modTwistSectionsEquiv (twistModCocycle n (m + 1)) k hW).injective ?_⟩
  rw [modTwistSectionsEquiv_mulXMod, LinearEquiv.apply_symm_apply, LinearEquiv.map_smul]

lemma sMulKerEqZero_mulXMod (m : ℤ) (l k : Fin (n + 1)) :
    SMulKerEqZero (mulXMod M m l) (xDivAn n k l) := by
  intro W hW s hs
  apply (modTwistSectionsEquiv (twistModCocycle n m) k hW).injective
  rw [LinearEquiv.map_smul, ← modTwistSectionsEquiv_mulXMod, hs, map_zero, map_zero]

lemma rangeLESMul_mulXModZero (l k : Fin (n + 1)) :
    RangeLESMul (mulXModZero M l) (xDivAn n k l) :=
  (rangeLESMul_mulXMod M (-1) l k).comp_iso _

lemma sMulLERange_mulXModZero (l k : Fin (n + 1)) :
    SMulLERange (mulXModZero M l) (xDivAn n k l) :=
  (sMulLERange_mulXMod M (-1) l k).comp_iso _

lemma sMulKerEqZero_mulXModZero (l k : Fin (n + 1)) :
    SMulKerEqZero (mulXModZero M l) (xDivAn n k l) :=
  (sMulKerEqZero_mulXMod M (-1) l k).comp_iso _

end MulX

end ComplexAnalytic.projectiveSpaceAn

end
