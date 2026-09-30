/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.Modules.QuasicoherentLocalization
public import Other.Oka.Analytification.GAGA.Proper.BaseChangeLocal
public import Other.Oka.Analytification.GAGA.Proper.RelativeBaseChangeStalk
public import Other.Oka.Analytification.GAGA.TwistTransition

/-!
# The analytic base change isomorphism for `ℙᴺ` over `ℂ[y₀, …, y_{m-1}]`

Let `P = ℙₒ(N; A)`, `A = ℂ[y₀, …, y_{m-1}]`, `p : P ⟶ 𝔸ᵐ` and `G` coherent on `P`. We show that
for `n ≫ 0` the base change morphism `(p_* G(n))^an ⟶ (p^an)_* G(n)^an` is bijective on all
stalks (`ComplexAnalytic.relProjectiveSpaceAn.exists_bijective_bcStalk_twist`).

For an open `D ⊆ ℂᵐ`, `baseAnOpens D` is the corresponding open of `(𝔸ᵐ)^an ≅ ℂᵐ`, holomorphic
functions on `D` are sections of `𝒪_{(𝔸ᵐ)^an}` over it (`baseAnRingHom`), and polynomials in `y`
are the pullbacks of the functions of `𝔸ᵐ` (`restrict_c_app_ΓSpecIso_inv`, by comparing values:
sections of `𝒪_{(𝔸ᵐ)^an}` are determined by their values, `eq_of_eval`). This gives a canonical
map `𝒪(D) ⊗_A Γ(P, G) → Γ(D, (p_* G)^an)`, `f ⊗ s ↦ f · s^an` (`baseMap`), which the base change
morphism sends to the canonical map `𝒪(D) ⊗_A Γ(P, G) → Γ(D × ℙᴺ, G^an)` of
`Other/Oka/Analytification/GAGA/Proper/RelativeBaseChangeAn.lean` (`bc_app_baseMap`).

Every germ of `(p_* G)^an` at `y` is the germ of `baseMap` of an element over a box around `y`
(`exists_germMod_baseMap`): the stalk is `𝒪_{(𝔸ᵐ)^an, y} ⊗ (p_* G)_{p y}`, and every germ of
`p_* G` is a multiple of the germ of a global section, `G` being quasi-coherent
(`exists_germMod_eq_smul`). Hence the germ statements of
`Other/Oka/Analytification/GAGA/Proper/RelativeBaseChangeStalk.lean` give surjectivity
(`exists_surjective_bcStalk_twist`) and injectivity (`exists_injective_bcStalk_twist`) for
`N ≥ 1`. For `N = 0`, `p` is an isomorphism (`isIso_toSpec_zero`), in particular a closed
immersion.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic.relProjectiveSpaceAn

open ProjectiveSpace AnalyticSpace LocallyRingedSpace
open scoped TensorProduct

variable {m N : ℕ}
/-- The open `D ⊆ ℂᵐ`, as an open of `(𝔸ᵐ)^an`. -/
def baseAnOpens (D : Opens (Fin m → ℂ)) : (analytification.obj (affineSpace.{u} m)).Opens :=
  (Opens.map (analytificationAffineSpaceIso.{u} m).hom.toLRSHom.base).obj (baseOpens D)

lemma baseAnOpens_mono {D D' : Opens (Fin m → ℂ)} (h : D' ≤ D) :
    baseAnOpens.{u} D' ≤ baseAnOpens D :=
  fun _ hx ↦ h hx

/-- Holomorphic functions on `D ⊆ ℂᵐ` as sections of `𝒪_{(𝔸ᵐ)^an}`. -/
def baseAnRingHom (D : Opens (Fin m → ℂ)) :
    OkaRing D →+* (analytification.obj (affineSpace.{u} m)).presheaf.obj (op (baseAnOpens D)) :=
  ((analytificationAffineSpaceIso.{u} m).hom.toLRSHom.c.app (op (baseOpens D))).hom.comp
    (okaToFin D)

lemma c_app_baseAnRingHom (D : Opens (Fin m → ℂ)) (f : OkaRing D) :
    (analytification.map (relProjectiveSpaceToAffine.{u} m N)).toLRSHom.c.app (op (baseAnOpens D))
      (baseAnRingHom D f) = baseRingHom N D f :=
  rfl

/-- The value of `baseAnRingHom D f` at `x` is `f` at the coordinates of `x`. -/
lemma eval_baseAnRingHom (D : Opens (Fin m → ℂ)) (f : OkaRing D)
    {x : analytification.obj (affineSpace.{u} m)} (hx : x ∈ baseAnOpens D) :
    (analytification.obj (affineSpace.{u} m)).eval x hx (baseAnRingHom D f) =
      f.toGlobalFun _ (projectiveSpaceAn.toFin
        ((analytificationAffineSpaceIso.{u} m).hom.toLRSHom.base x)) := by
  refine (eval_c_app _ (analytificationAffineSpaceIso.{u} m).hom.isCLinear x hx
    (okaToFin D f)).trans ?_
  rw [eval_complexAffineSpace_of _ hx, OkaRing.evalHom_apply, OkaRing.toGlobalFun_apply _ hx]
  rfl

/-- **Sections of `𝒪_{(𝔸ᵐ)^an}` are determined by their values.** -/
lemma eq_zero_of_eval {W : (analytification.obj (affineSpace.{u} m)).Opens}
    (s : (analytification.obj (affineSpace.{u} m)).presheaf.obj (op W))
    (h : ∀ x (hx : x ∈ W), (analytification.obj (affineSpace.{u} m)).eval x hx s = 0) : s = 0 := by
  let e := analytificationAffineSpaceIso.{u} m
  refine TopCat.Presheaf.section_ext (analytification.obj (affineSpace.{u} m)).sheaf W s 0
    fun x hx ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, e.inv.toLRSHom.base w = x :=
    ⟨e.hom.toLRSHom.base x, congr(($((forgetToLocallyRingedSpace.mapIso e).hom_inv_id)).base x)⟩
  haveI : IsIso e.inv.toLRSHom := (forgetToLocallyRingedSpace.mapIso e).isIso_inv
  have h0 : e.inv.toLRSHom.c.app (op W) s = 0 := by
    refine OkaRing.ext (funext fun w' ↦ ?_)
    change OkaRing.evalHom w'.2 (e.inv.toLRSHom.c.app (op W) s) = OkaRing.evalHom w'.2 0
    rw [map_zero, ← eval_complexAffineSpace_of _ w'.2]
    exact (eval_c_app _ e.inv.isCLinear w'.1 w'.2 s).trans (h _ _)
  apply (ConcreteCategory.bijective_of_isIso (e.inv.toLRSHom.stalkMap w)).1
  change e.inv.toLRSHom.stalkMap w
      ((analytification.obj (affineSpace.{u} m)).presheaf.germ W _ hx s)
    = e.inv.toLRSHom.stalkMap w ((analytification.obj (affineSpace.{u} m)).presheaf.germ W _ hx 0)
  rw [LocallyRingedSpace.stalkMap_germ_apply, LocallyRingedSpace.stalkMap_germ_apply, map_zero,
    h0]

lemma eq_of_eval {W : (analytification.obj (affineSpace.{u} m)).Opens}
    {s t : (analytification.obj (affineSpace.{u} m)).presheaf.obj (op W)}
    (h : ∀ x (hx : x ∈ W), (analytification.obj (affineSpace.{u} m)).eval x hx s =
      (analytification.obj (affineSpace.{u} m)).eval x hx t) : s = t := by
  rw [← sub_eq_zero]
  exact eq_zero_of_eval _ fun x hx ↦ by rw [map_sub, h, sub_self]


/-- The comparison morphism `(𝔸ᵐ)^an ⟶ 𝔸ᵐ` on points, through `(𝔸ᵐ)^an ≅ ℂᵐ`. -/
lemma analytificationπ_affineSpace_base (x : analytification.obj (affineSpace.{u} m)) :
    (analytificationπLRS (affineSpace.{u} m)).base x = (complexAffineSpaceπ.{u} m).left.base
      ((analytificationAffineSpaceIso.{u} m).hom.toLRSHom.base x) :=
  (congrArg (fun f ↦ f.left.base x) (analytificationAffineSpaceIso_hom_comp.{u} m)).symm

lemma schemeConst_affineSpace (c : ULift.{u} ℂ) :
    schemeConst (affineSpace.{u} m) c =
      (Scheme.ΓSpecIso (.of (RelBase.{u} m))).inv (MvPolynomial.C c) := by
  change (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin m) (R := ULift.{u} ℂ)))).appTop
    ((Scheme.ΓSpecIso (.of (ULift.{u} ℂ))).inv c) = _
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- **Polynomials as holomorphic functions on the base**: the pullback to `(𝔸ᵐ)^an` of a
polynomial `c` in the base coordinates, restricted over `D`, is the holomorphic function `c`. -/
lemma restrict_c_app_ΓSpecIso_inv (D : Opens (Fin m → ℂ)) (c : RelBase.{u} m) :
    TopCat.Presheaf.restrictOpen (F := (analytification.obj (affineSpace.{u} m)).presheaf)
      ((analytificationπLRS (affineSpace.{u} m)).c.app (op ⊤)
        ((Scheme.ΓSpecIso (.of (RelBase.{u} m))).inv c)) (baseAnOpens D) le_top =
      baseAnRingHom D (polyToOka.{u} D c) := by
  refine eq_of_eval fun x hx ↦ ?_
  rw [eval_baseAnRingHom _ _ hx, toGlobalFun_polyToOka _ _ hx, AnalyticSpace.eval_restrictOpen]
  refine eval_analytificationπ_eq (V := ⊤) _ x trivial _ ?_
  erw [TopCat.Presheaf.restrict_self]
  rw [schemeConst_affineSpace]
  change ¬IsUnit ((Spec (CommRingCat.of (RelBase.{u} m))).presheaf.germ ⊤
    ((analytificationπLRS (affineSpace.{u} m)).base x) trivial (_ - _))
  rw [← map_sub, ← Scheme.mem_basicOpen,
    basicOpen_eq_of_affine]
  intro hmem
  refine hmem ?_
  erw [analytificationπ_affineSpace_base x]
  rw [complexAffineSpaceπ_base_asIdeal, RingHom.mem_ker, map_sub]
  rw [sub_eq_zero]
  simp [affineEval]
  rfl

lemma baseAnRingHom_restrict {D D' : Opens (Fin m → ℂ)} (h : D' ≤ D) (f : OkaRing D) :
    TopCat.Presheaf.restrictOpen (F := (analytification.obj (affineSpace.{u} m)).presheaf)
      (baseAnRingHom D f) (baseAnOpens D') (baseAnOpens_mono h) =
      baseAnRingHom D' (restrictOka.{u} h f) := by
  refine eq_of_eval fun x hx ↦ ?_
  rw [AnalyticSpace.eval_restrictOpen, eval_baseAnRingHom _ _ hx, eval_baseAnRingHom,
    toGlobalFun_restrictOka h f hx]

lemma analyticAt_ofFin (w : Fin m → ℂ) :
    AnalyticAt ℂ (fun w : Fin m → ℂ ↦ fun k : ULift.{u} (Fin m) ↦ w k.down) w :=
  analyticAt_pi_iff.2 fun k ↦
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m ↦ ℂ) k.down).analyticAt w

lemma okaToFin_surjective (D : Opens (Fin m → ℂ)) : Function.Surjective (okaToFin.{u} D) := by
  intro g
  have key : OkaAnalytic (fun w : D ↦ (g.toGlobalFun _ ∘ projectiveSpaceAn.ofFin.{u}) w.1) :=
    okaAnalytic_restrict fun w hw ↦ ((okaAnalytic_iff _).1 g.2 _ hw).comp (analyticAt_ofFin w)
  refine ⟨OkaRing.mk _ key, OkaRing.ext (funext fun z ↦ ?_)⟩
  change (g.toGlobalFun _ ∘ projectiveSpaceAn.ofFin.{u}) (projectiveSpaceAn.toFin z.1) = _
  exact OkaRing.toGlobalFun_apply g z.2

/-- Boxes around the coordinates of `y` form a neighbourhood basis of `y ∈ (𝔸ᵐ)^an`. -/
lemma exists_baseAnOpens_box_subset {O : (analytification.obj (affineSpace.{u} m)).Opens}
    {y : analytification.obj (affineSpace.{u} m)} (hy : y ∈ O) :
    ∃ a b : Fin m → ℂ, y ∈ baseAnOpens.{u} (boxOpens a b) ∧ baseAnOpens (boxOpens a b) ≤ O := by
  let e := analytificationAffineSpaceIso.{u} m
  have hinv : ∀ x, e.inv.toLRSHom.base (e.hom.toLRSHom.base x) = x := fun x ↦
    congr(($((forgetToLocallyRingedSpace.mapIso e).hom_inv_id)).base x)
  have hO : IsOpen {w : Fin m → ℂ | e.inv.toLRSHom.base (projectiveSpaceAn.ofFin.{u} w) ∈ O} :=
    O.isOpen.preimage (e.inv.toLRSHom.base.hom.continuous.comp
      (continuous_pi fun k ↦ continuous_apply k.down))
  obtain ⟨a, b, hyB, hBO⟩ := exists_openBox_subset hO
    (z := projectiveSpaceAn.toFin (e.hom.toLRSHom.base y)) (by simpa [hinv] using hy)
  refine ⟨a, b, hyB, fun x hx ↦ ?_⟩
  have h2 : e.inv.toLRSHom.base (e.hom.toLRSHom.base x) ∈ O := hBO hx
  rwa [hinv] at h2

/-- **Germs of holomorphic functions on boxes**: every germ of `𝒪_{(𝔸ᵐ)^an}` at `y` is the germ of
`baseAnRingHom B f` for an open box `B` around `y`, inside any given neighbourhood of `y`. -/
lemma exists_germ_baseAnRingHom {O : (analytification.obj (affineSpace.{u} m)).Opens}
    {y : analytification.obj (affineSpace.{u} m)} (hy : y ∈ O)
    (r : (analytification.obj (affineSpace.{u} m)).presheaf.stalk y) :
    ∃ (a b : Fin m → ℂ) (hyB : y ∈ baseAnOpens.{u} (boxOpens a b)),
      baseAnOpens (boxOpens a b) ≤ O ∧ ∃ f : OkaRing (boxOpens a b),
        (analytification.obj (affineSpace.{u} m)).presheaf.germ _ y hyB
          (baseAnRingHom (boxOpens a b) f) = r := by
  let t := (analytificationAffineSpaceIso.{u} m).hom.toLRSHom
  haveI : IsIso t :=
    (forgetToLocallyRingedSpace.mapIso (analytificationAffineSpaceIso.{u} m)).isIso_hom
  obtain ⟨r₀, rfl⟩ := (ConcreteCategory.bijective_of_isIso (t.stalkMap y)).2 r
  obtain ⟨O', hO', σ, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ r₀
  obtain ⟨a, b, hyB, hBO⟩ := exists_baseAnOpens_box_subset (O := O ⊓ (Opens.map t.base).obj O')
    ⟨hy, hO'⟩
  refine ⟨a, b, hyB, hBO.trans inf_le_left, ?_⟩
  have hinv : ∀ w, t.base ((analytificationAffineSpaceIso.{u} m).inv.toLRSHom.base w) = w :=
    fun w ↦ congr(($((forgetToLocallyRingedSpace.mapIso
      (analytificationAffineSpaceIso.{u} m)).inv_hom_id)).base w)
  have hle : baseOpens.{u} (boxOpens a b) ≤ O' := fun w hw ↦ by
    have h2 := (hBO (x := (analytificationAffineSpaceIso.{u} m).inv.toLRSHom.base w)
      (by change projectiveSpaceAn.toFin (t.base _) ∈ boxOpens a b; rw [hinv]; exact hw)).2
    change t.base _ ∈ O' at h2
    rwa [hinv] at h2
  have hle' : baseAnOpens.{u} (boxOpens a b) ≤ (Opens.map t.base).obj O' :=
    hBO.trans inf_le_right
  obtain ⟨f, hf⟩ := okaToFin_surjective (boxOpens a b)
    (TopCat.Presheaf.restrictOpen σ (baseOpens.{u} (boxOpens a b)) hle)
  refine ⟨f, ?_⟩
  rw [LocallyRingedSpace.stalkMap_germ_apply, ← TopCat.Presheaf.germ_res_apply _
    (homOfLE hle') _ hyB]
  congr 1
  change t.c.app _ (okaToFin _ f) = _
  rw [hf]
  exact congr($(t.c.naturality (homOfLE hle).op).hom σ)


/-! ### The canonical sections of `(p_* G)^an` over boxes -/


variable (G : ℙₒ(N; RelBase.{u} m).Modules)

/-- `(p_* G)^an` on `(𝔸ᵐ)^an`, for `p : P ⟶ 𝔸ᵐ`. -/
abbrev pushAn :
    SheafOfModules.{u} (analytification.obj (affineSpace.{u} m)).toLocallyRingedSpace.ringSheaf :=
  (analytificationModules (affineSpace.{u} m)).obj
    ((SheafOfModules.pushforward.{u}
      (relProjectiveSpaceToAffine.{u} m N).hom.left.toLRSHom.toRingSheafHom).obj G)

/-- The pullback to `(𝔸ᵐ)^an` of a global section of `G`, as a global section of `(p_* G)^an`. -/
def unitTop (s : AlgSec G) : (pushAn G).val.obj
    (op ((Opens.map (analytificationπLRS (affineSpace.{u} m)).base).obj ⊤)) :=
  ((analytificationModulesAdj (affineSpace.{u} m)).unit.app
    ((SheafOfModules.pushforward.{u}
      (relProjectiveSpaceToAffine.{u} m N).hom.left.toLRSHom.toRingSheafHom).obj G)).val.app
        (op ⊤) s

lemma baseAnOpens_le_top (D : Opens (Fin m → ℂ)) :
    baseAnOpens.{u} D ≤ (Opens.map (analytificationπLRS (affineSpace.{u} m)).base).obj ⊤ :=
  fun _ _ ↦ trivial

/-- The pullback to `(𝔸ᵐ)^an` of a global section of `G`, as a section of `(p_* G)^an` over `D`. -/
def unitBase (D : Opens (Fin m → ℂ)) (s : AlgSec G) : (pushAn G).val.obj (op (baseAnOpens D)) :=
  modRes (unitTop G s) (baseAnOpens D) (baseAnOpens_le_top D)


variable {G} in
lemma unitBase_add (D : Opens (Fin m → ℂ)) (s t : AlgSec G) :
    unitBase G D (s + t) = unitBase G D s + unitBase G D t := by
  exact (congrArg (fun x ↦ modRes x (baseAnOpens D) (baseAnOpens_le_top D))
    (((analytificationModulesAdj (affineSpace.{u} m)).unit.app
    ((SheafOfModules.pushforward.{u}
      (relProjectiveSpaceToAffine.{u} m N).hom.left.toLRSHom.toRingSheafHom).obj G)).val.app
        (op ⊤) |>.hom.map_add s t)).trans (modRes_add _ _ _)

variable {G} in
lemma unitBase_zero (D : Opens (Fin m → ℂ)) : unitBase G D 0 = 0 := by
  have h := unitBase_add (G := G) D 0 0
  rw [add_zero] at h
  exact left_eq_add.1 h

variable {G} in
lemma unitBase_smul (D : Opens (Fin m → ℂ)) (c : RelBase.{u} m) (s : AlgSec G) :
    unitBase G D (c • s) = baseAnRingHom D (polyToOka.{u} D c) • unitBase G D s := by
  rw [unitBase, unitBase, unitTop, unitTop, ← restrict_c_app_ΓSpecIso_inv]
  refine Eq.trans ?_ (modRes_smul _ _ _)
  congr 1
  exact ((analytificationModulesAdj (affineSpace.{u} m)).unit.app
    ((SheafOfModules.pushforward.{u}
      (relProjectiveSpaceToAffine.{u} m N).hom.left.toLRSHom.toRingSheafHom).obj G)).val.app
        (op ⊤) |>.hom.map_smul ((Scheme.ΓSpecIso (.of (RelBase.{u} m))).inv c) s


/-- **The canonical map `𝒪(D) ⊗_A Γ(P, G) → Γ(D, (p_* G)^an)`**, `f ⊗ s ↦ f · s^an`. -/
def baseMap (D : Opens (Fin m → ℂ)) :
    OkaRing D ⊗[RelBase.{u} m] AlgSec G →+ (pushAn G).val.obj (op (baseAnOpens D)) :=
  TensorProduct.liftAddHom
    { toFun := fun f ↦
        { toFun := fun s ↦ baseAnRingHom D f • unitBase G D s
          map_zero' := by rw [unitBase_zero, smul_zero]
          map_add' := fun s t ↦ by rw [unitBase_add, smul_add] }
      map_zero' := by ext s; simp
      map_add' := fun f g ↦ by ext s; simp [add_smul] }
    fun c f s ↦ by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [unitBase_smul, smul_smul, Algebra.smul_def, algebraMap_okaRing, map_mul, mul_comm]

variable {G} in
lemma baseMap_tmul (D : Opens (Fin m → ℂ)) (f : OkaRing D) (s : AlgSec G) :
    baseMap G D (f ⊗ₜ s) = baseAnRingHom D f • unitBase G D s :=
  rfl


variable {G} in
lemma unitBase_restrict {D D' : Opens (Fin m → ℂ)} (h : D' ≤ D) (s : AlgSec G) :
    modRes (unitBase G D s) (baseAnOpens D') (baseAnOpens_mono h) = unitBase G D' s :=
  modRes_res _ _ _

variable {G} in
lemma baseMap_restrict {D D' : Opens (Fin m → ℂ)} (h : D' ≤ D)
    (x : OkaRing D ⊗[RelBase.{u} m] AlgSec G) :
    modRes (baseMap G D x) (baseAnOpens D') (baseAnOpens_mono h) =
      baseMap G D' ((restrictOka.{u} h).toLinearMap.rTensor (AlgSec G) x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; exact modRes_zero _
  | tmul f s =>
    rw [LinearMap.rTensor_tmul, baseMap_tmul, baseMap_tmul, modRes_smul, unitBase_restrict h]
    exact congrArg (· • unitBase G D' s) (baseAnRingHom_restrict h f)
  | add x y hx hy =>
    rw [map_add, map_add, map_add, ← hx, ← hy]
    exact modRes_add _ _ _


variable {G} in
lemma bc_app_unitBase (D : Opens (Fin m → ℂ)) (s : AlgSec G) :
    (analytificationPushforwardBaseChange (relProjectiveSpaceToAffine.{u} m N) G).val.app
      (op (baseAnOpens D)) (unitBase G D s) = algSec D G s := by
  rw [unitBase, modHom_modRes]
  refine (congrArg (fun x ↦ modRes x (baseAnOpens D) (baseAnOpens_le_top D))
    (pushforwardModulesBaseChange_app_unit
      (analytificationπLRS_naturality (relProjectiveSpaceToAffine.{u} m N)) G ⊤ s)).trans ?_
  exact val_map_map_apply ((analytificationModules (relProjectiveSpace.{u} m N)).obj G) _ _ _ _

variable {G} in
/-- **The base change morphism on the canonical sections**: over `D`, the base change morphism
`(p_* G)^an ⟶ (p^an)_* G^an` sends `f ⊗ s ↦ f · s^an` to the canonical map. -/
lemma bc_app_baseMap (D : Opens (Fin m → ℂ)) (x : OkaRing D ⊗[RelBase.{u} m] AlgSec G) :
    (analytificationPushforwardBaseChange (relProjectiveSpaceToAffine.{u} m N) G).val.app
      (op (baseAnOpens D)) (baseMap G D x) = canMap D G x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | tmul f s =>
    rw [baseMap_tmul, modHom_smul, bc_app_unitBase, canMap_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; rfl

/-- **Germs of direct images are generated by global sections**: for quasi-coherent `G` on
`P = ℙₒ(N; A)`, every germ of `p_* G` at a point of `𝔸ᵐ` is a multiple of the germ of a global
section. -/
lemma exists_germMod_eq_smul (G : ℙₒ(N; RelBase.{u} m).Modules) [G.IsQuasicoherent]
    (y : (affineSpace.{u} m).obj.left)
    (a : ((affineSpace.{u} m).obj.left.toLocallyRingedSpace.stalkFunctor y).obj
      ((SheafOfModules.pushforward.{u}
        (relProjectiveSpaceToAffine.{u} m N).hom.left.toLRSHom.toRingSheafHom).obj G)) :
    ∃ (c : (affineSpace.{u} m).obj.left.presheaf.stalk y) (t : AlgSec G),
      a = c • germMod _ (show y ∈ (⊤ : (affineSpace.{u} m).obj.left.Opens) from trivial) t := by
  obtain ⟨O, -, hO, σ, rfl⟩ := exists_germMod_eq_of_le (O := ⊤) (y := y) trivial a
  haveI : IsAffine (affineSpace.{u} m).obj.left := inferInstanceAs (IsAffine (Spec _))
  obtain ⟨_, ⟨g, rfl⟩, hyg, hgO⟩ :=
    (Opens.isBasis_iff_nbhd.1 (isBasis_basicOpen (affineSpace.{u} m).obj.left)) hO
  have hW : ⨆ i, U N (RelBase.{u} m) i = (ProjectiveSpace.toSpec N (RelBase.{u} m)) ⁻¹ᵁ ⊤ := by
    rw [iSup_U]; rfl
  have hWij : ∀ i j, IsAffineOpen (U N (RelBase.{u} m) i ⊓ U N (RelBase.{u} m) j) := fun i j ↦ by
    have h := isAffineOpen_UI (n := N) (R := RelBase.{u} m) (I := {i, j})
      (Finset.mem_insert_self i {j})
    rwa [UI_eq_iInf, Finset.iInf_insert, Finset.iInf_singleton] at h
  obtain ⟨k, t, ht⟩ := Scheme.Modules.exists_restrictOpen_eq_pow_smul_pushforward
    (ProjectiveSpace.toSpec N (RelBase.{u} m)) G (U N (RelBase.{u} m)) hW
    isAffineOpen_U hWij g (TopCat.Presheaf.restrictOpen σ _ hgO)
  have hu : IsUnit ((affineSpace.{u} m).obj.left.presheaf.germ ⊤ y trivial g) :=
    (Scheme.mem_basicOpen _ g y trivial).1 hyg
  refine ⟨↑(hu.unit⁻¹ ^ k), t, ?_⟩
  let M := (SheafOfModules.pushforward.{u}
      (relProjectiveSpaceToAffine.{u} m N).hom.left.toLRSHom.toRingSheafHom).obj G
  have e1 : germMod ((SheafOfModules.pushforward.{u}
      (relProjectiveSpaceToAffine.{u} m N).hom.left.toLRSHom.toRingSheafHom).obj G)
      (show y ∈ (⊤ : (affineSpace.{u} m).obj.left.Opens) from trivial) t =
        germMod _ hyg (TopCat.Presheaf.restrictOpen t _ le_top) :=
    (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE le_top) y hyg t).symm
  have e2 : germMod M hO σ = germMod M hyg (M.val.presheaf.map (homOfLE hgO).op σ) :=
    (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE hgO) y hyg σ).symm
  have e3 : (affineSpace.{u} m).obj.left.presheaf.germ _ y hyg
      (TopCat.Presheaf.restrictOpen g _ le_top) =
        (affineSpace.{u} m).obj.left.presheaf.germ ⊤ y trivial g :=
    TopCat.Presheaf.germ_res_apply _ (homOfLE le_top) y hyg g
  have e4 := congrArg (germMod M hyg) ht
  have key : germMod M (show y ∈ (⊤ : (affineSpace.{u} m).obj.left.Opens) from trivial) t =
      ↑(hu.unit ^ k) • germMod M hO σ := by
    rw [e1, e2]
    refine e4.trans ((germMod_smul hyg _ _).trans ?_)
    congr 1
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← e3]
    exact map_pow _ _ _
  rw [key, Units.smul_def, smul_smul, ← Units.val_mul, ← mul_pow, inv_mul_cancel, one_pow,
    Units.val_one, one_smul]


lemma le_of_baseAnOpens_le {D D' : Opens (Fin m → ℂ)} (h : baseAnOpens.{u} D' ≤ baseAnOpens D) :
    D' ≤ D := by
  intro w hw
  let e := analytificationAffineSpaceIso.{u} m
  have hinv : e.hom.toLRSHom.base (e.inv.toLRSHom.base (projectiveSpaceAn.ofFin w)) =
      projectiveSpaceAn.ofFin w :=
    congr(($((forgetToLocallyRingedSpace.mapIso e).inv_hom_id)).base (projectiveSpaceAn.ofFin w))
  have h1 : e.inv.toLRSHom.base (projectiveSpaceAn.ofFin w) ∈ baseAnOpens.{u} D' := by
    change projectiveSpaceAn.toFin (e.hom.toLRSHom.base _) ∈ D'
    rw [hinv]
    exact hw
  have h2 := h h1
  change projectiveSpaceAn.toFin (e.hom.toLRSHom.base _) ∈ D at h2
  rwa [hinv] at h2

lemma _root_.AlgebraicGeometry.LocallyRingedSpace.germMod_add {Y : LocallyRingedSpace.{u}}
    (M : SheafOfModules.{u} Y.ringSheaf) {W : Opens Y.toPresheafedSpace} {y : Y} (hy : y ∈ W)
    (s t : M.val.obj (op W)) : germMod M hy (s + t) = germMod M hy s + germMod M hy t :=
  map_add _ _ _

variable {G} in
lemma germMod_baseMap_restrict {D D' : Opens (Fin m → ℂ)} (h : D' ≤ D)
    (x : OkaRing D ⊗[RelBase.{u} m] AlgSec G) {y : analytification.obj (affineSpace.{u} m)}
    (hy : y ∈ baseAnOpens D') :
    germMod (pushAn G) hy (baseMap G D' ((restrictOka.{u} h).toLinearMap.rTensor (AlgSec G) x)) =
      germMod (pushAn G) (baseAnOpens_mono h hy) (baseMap G D x) := by
  rw [← baseMap_restrict h]
  exact TopCat.Presheaf.germ_res_apply _ (homOfLE (baseAnOpens_mono h)) y hy _

/-- **The stalks of `(p_* G)^an` are generated by the canonical sections over boxes.** -/
lemma exists_germMod_baseMap [G.IsQuasicoherent] (y : analytification.obj (affineSpace.{u} m))
    (a : ((analytification.obj (affineSpace.{u} m)).toLocallyRingedSpace.stalkFunctor y).obj
      (pushAn G)) :
    ∃ (a' b' : Fin m → ℂ) (hy : y ∈ baseAnOpens.{u} (boxOpens a' b'))
      (x : OkaRing (boxOpens a' b') ⊗[RelBase.{u} m] AlgSec G),
        germMod (pushAn G) hy (baseMap G _ x) = a := by
  let e : ((analytification.obj (affineSpace.{u} m)).toLocallyRingedSpace.stalkFunctor y).obj
      (pushAn G) ≃ₗ[_] (ModuleCat.extendScalars
        ((analytificationπLRS (affineSpace.{u} m)).stalkMap y).hom).obj
        (((affineSpace.{u} m).obj.left.toLocallyRingedSpace.stalkFunctor
          ((analytificationπLRS (affineSpace.{u} m)).base y)).obj
          ((SheafOfModules.pushforward.{u}
            (relProjectiveSpaceToAffine.{u} m N).hom.left.toLRSHom.toRingSheafHom).obj G)) :=
    (((analytificationπLRS (affineSpace.{u} m)).pullbackModulesStalkIso y).app
      ((SheafOfModules.pushforward.{u}
        (relProjectiveSpaceToAffine.{u} m N).hom.left.toLRSHom.toRingSheafHom).obj G)).toLinearEquiv
  suffices h : ∀ t, ∃ (a' b' : Fin m → ℂ) (hy : y ∈ baseAnOpens.{u} (boxOpens a' b'))
      (x : OkaRing (boxOpens a' b') ⊗[RelBase.{u} m] AlgSec G),
        germMod (pushAn G) hy (baseMap G _ x) = e.symm t by
    obtain ⟨a', b', hy, x, hx⟩ := h (e a)
    exact ⟨a', b', hy, x, hx.trans (e.symm_apply_apply a)⟩
  intro t
  induction t using TensorProduct.induction_on with
  | zero =>
    obtain ⟨a', b', hy, -⟩ := exists_baseAnOpens_box_subset (O := ⊤) (y := y) trivial
    exact ⟨a', b', hy, 0, by erw [map_zero, germMod_zero, map_zero]⟩
  | tmul r n =>
    obtain ⟨c, t, rfl⟩ := exists_germMod_eq_smul G _ n
    obtain ⟨a', b', hy, -, f, hf⟩ := exists_germ_baseAnRingHom (O := ⊤) (y := y) trivial
      (((analytificationπLRS (affineSpace.{u} m)).stalkMap y).hom c *
        (show (analytification.obj (affineSpace.{u} m)).presheaf.stalk y from r))
    refine ⟨a', b', hy, f ⊗ₜ t, ?_⟩
    have h1 := (analytificationπLRS (affineSpace.{u} m)).pullbackModulesStalkIso_hom_app_germ_unit
      ((SheafOfModules.pushforward.{u}
        (relProjectiveSpaceToAffine.{u} m N).hom.left.toLRSHom.toRingSheafHom).obj G) ⊤ y trivial t
    have h2 : germMod (pushAn G) hy (unitBase G _ t) = germMod (pushAn G) (show y ∈
        (Opens.map (analytificationπLRS (affineSpace.{u} m)).base).obj ⊤ from trivial)
          (unitTop G t) :=
      TopCat.Presheaf.germ_res_apply _ (homOfLE (baseAnOpens_le_top _)) y hy _
    rw [baseMap_tmul, germMod_smul, hf, h2]
    apply e.injective
    have h1' : e (germMod (pushAn G) (show y ∈ (Opens.map (analytificationπLRS
        (affineSpace.{u} m)).base).obj ⊤ from trivial) (unitTop G t)) =
        (ModuleCat.extendRestrictScalarsAdj
          ((analytificationπLRS (affineSpace.{u} m)).stalkMap y).hom).unit.app _ (germMod _
          (show (analytificationπLRS (affineSpace.{u} m)).base y ∈
            (⊤ : (affineSpace.{u} m).obj.left.Opens) from trivial) t) := h1
    rw [map_smul, e.apply_symm_apply, h1', ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
    refine (ModuleCat.ExtendScalars.smul_tmul _ _ _ _).trans ?_
    rw [mul_one]
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rfl
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨a₁, b₁, hy₁, x₁, hx₁⟩ := h₁
    obtain ⟨a₂, b₂, hy₂, x₂, hx₂⟩ := h₂
    obtain ⟨a', b', hy, hle⟩ := exists_baseAnOpens_box_subset
      (O := baseAnOpens (boxOpens a₁ b₁) ⊓ baseAnOpens (boxOpens a₂ b₂)) ⟨hy₁, hy₂⟩
    have hle₁ := le_of_baseAnOpens_le (hle.trans inf_le_left)
    have hle₂ := le_of_baseAnOpens_le (hle.trans inf_le_right)
    refine ⟨a', b', hy, (restrictOka.{u} hle₁).toLinearMap.rTensor (AlgSec G) x₁ +
      (restrictOka.{u} hle₂).toLinearMap.rTensor (AlgSec G) x₂, ?_⟩
    erw [map_add, germMod_add, germMod_baseMap_restrict hle₁ x₁ hy,
      germMod_baseMap_restrict hle₂ x₂ hy, hx₁, hx₂]
    exact (map_add e.symm t₁ t₂).symm


/-- The open of `ℂᵐ` of the coordinates of the points of an open `W` of `(𝔸ᵐ)^an`. -/
def coordOpens (W : (analytification.obj (affineSpace.{u} m)).Opens) : Opens (Fin m → ℂ) :=
  ⟨{w | (analytificationAffineSpaceIso.{u} m).inv.toLRSHom.base (projectiveSpaceAn.ofFin w) ∈ W},
    W.isOpen.preimage ((analytificationAffineSpaceIso.{u} m).inv.toLRSHom.base.hom.continuous.comp
      (continuous_pi fun k ↦ continuous_apply k.down))⟩

lemma analytificationAffineSpaceIso_inv_hom_base (x : analytification.obj (affineSpace.{u} m)) :
    (analytificationAffineSpaceIso.{u} m).inv.toLRSHom.base
      ((analytificationAffineSpaceIso.{u} m).hom.toLRSHom.base x) = x :=
  congr(($((forgetToLocallyRingedSpace.mapIso
    (analytificationAffineSpaceIso.{u} m)).hom_inv_id)).base x)

lemma analytificationAffineSpaceIso_hom_inv_base (w : AnalyticSpace.complexAffineSpace.{u} m) :
    (analytificationAffineSpaceIso.{u} m).hom.toLRSHom.base
      ((analytificationAffineSpaceIso.{u} m).inv.toLRSHom.base w) = w :=
  congr(($((forgetToLocallyRingedSpace.mapIso
    (analytificationAffineSpaceIso.{u} m)).inv_hom_id)).base w)

lemma mem_baseAnOpens_coordOpens {W : (analytification.obj (affineSpace.{u} m)).Opens}
    {x : analytification.obj (affineSpace.{u} m)} :
    x ∈ baseAnOpens.{u} (coordOpens W) ↔ x ∈ W := by
  change (analytificationAffineSpaceIso.{u} m).inv.toLRSHom.base
    ((analytificationAffineSpaceIso.{u} m).hom.toLRSHom.base x) ∈ W ↔ _
  rw [analytificationAffineSpaceIso_inv_hom_base]

lemma baseAnOpens_coordOpens (W : (analytification.obj (affineSpace.{u} m)).Opens) :
    baseAnOpens.{u} (coordOpens W) = W :=
  Opens.ext (Set.ext fun _ ↦ mem_baseAnOpens_coordOpens)


/-- `(p^an)_* G^an` on `(𝔸ᵐ)^an`. -/
abbrev pushAnTarget : SheafOfModules.{u}
    (analytification.obj (affineSpace.{u} m)).toLocallyRingedSpace.ringSheaf :=
  (SheafOfModules.pushforward.{u}
    (analytification.map (relProjectiveSpaceToAffine.{u} m N)).toLRSHom.toRingSheafHom).obj
      ((analytificationModules (relProjectiveSpace.{u} m N)).obj G)

section Pos

variable (hN : 1 ≤ N)
include hN

/-- **Surjectivity of the base change morphism on stalks**, for `G(n)`, `n ≫ 0`. -/
theorem exists_surjective_bcStalk_twist [G.IsCoherent] :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ∀ y,
      Function.Surjective (bcStalk (relProjectiveSpaceToAffine.{u} m N) (twist G n) y) := by
  obtain ⟨n₀, h⟩ := exists_canMap_eq_restrict hN G
  refine ⟨n₀, fun n hn y b ↦ ?_⟩
  obtain ⟨W, -, hyW, s, rfl⟩ := exists_germMod_eq_of_le (O := ⊤) (y := y) trivial b
  have hVW : baseAnOpens.{u} (coordOpens W) ≤ W := fun x hx ↦ mem_baseAnOpens_coordOpens.1 hx
  obtain ⟨a, a', B, hBV, -, hyB, x, hx⟩ := h n hn (coordOpens W) _
    (mem_baseAnOpens_coordOpens.2 hyW) (modRes (N := pushAnTarget (twist G n)) s _ hVW)
  refine ⟨germMod (pushAn (twist G n)) (y := y) hyB (baseMap _ B x), ?_⟩
  rw [bcStalk, stalkFunctor_map_germMod, bc_app_baseMap, hx]
  refine (TopCat.Presheaf.germ_res_apply _ (homOfLE (baseAnOpens_mono hBV)) y hyB _).trans ?_
  exact TopCat.Presheaf.germ_res_apply (pushAnTarget (twist G n)).val.presheaf (homOfLE hVW) y _ s


/-- **Injectivity of the base change morphism on stalks**, for `G(n)`, `n ≫ 0`. -/
theorem exists_injective_bcStalk_twist [G.IsCoherent] :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ∀ y,
      Function.Injective (bcStalk (relProjectiveSpaceToAffine.{u} m N) (twist G n) y) := by
  obtain ⟨n₀, h⟩ := exists_rTensor_restrict_eq_zero hN G
  refine ⟨n₀, fun n hn y ↦ ?_⟩
  haveI : G.IsQuasicoherent := SheafOfModules.IsCoherent.isQuasicoherent G
  refine (injective_iff_map_eq_zero _).2 fun a ha ↦ ?_
  obtain ⟨a₁, b₁, hy, x, rfl⟩ := exists_germMod_baseMap (twist G n) y a
  rw [bcStalk, stalkFunctor_map_germMod, bc_app_baseMap] at ha
  obtain ⟨W, hyW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq (pushAnTarget (twist G n)).val.presheaf
    y hy hy _ 0 (ha.trans (map_zero _).symm)
  have hVW : baseAnOpens.{u} (coordOpens W) ≤ W := fun x hx ↦ mem_baseAnOpens_coordOpens.1 hx
  have hVB : coordOpens W ≤ boxOpens a₁ b₁ := le_of_baseAnOpens_le (hVW.trans iU.le)
  have h0 : anSecRestrict hVB (canMap (boxOpens a₁ b₁) (twist G n) x) = 0 := by
    change modRes (N := pushAnTarget (twist G n)) _ _ (baseAnOpens_mono hVB) = 0
    rw [← modRes_res (N := pushAnTarget (twist G n)) iU.le hVW]
    change modRes ((pushAnTarget (twist G n)).val.presheaf.map iU.op _) _ hVW = 0
    rw [hW, map_zero]
    exact modRes_zero _
  obtain ⟨B, hBV, -, hyB, hx0⟩ := h n hn _ _ hVB _ (mem_baseAnOpens_coordOpens.2 hyW) x h0
  rw [← germMod_baseMap_restrict (hBV.trans hVB) x hyB, hx0, map_zero, germMod_zero]


end Pos

/-- `ℙ⁰ ⟶ Spec R` is an isomorphism. -/
instance isIso_toSpec_zero (R : Type u) [CommRing R] : IsIso (ProjectiveSpace.toSpec 0 R) := by
  have hU : U 0 R 0 = ⊤ := by
    rw [← iSup_U 0 R]
    exact le_antisymm (le_iSup (U 0 R) 0) (iSup_le fun i ↦ by rw [Fin.fin_one_eq_zero i])
  haveI : IsIso (chart (R := R) (0 : Fin 1)) := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun x ↦ ?_⟩⟩
    have hx : x ∈ (chart (R := R) (0 : Fin 1)).opensRange := by
      rw [opensRange_chart, hU]; trivial
    exact hx
  haveI : IsIso (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin 0) R))) :=
    inferInstanceAs (IsIso (Scheme.Spec.mapIso
      (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingEquiv.toCommRingCatIso.op).inv)
  have h : toSpec 0 R = inv (chart (R := R) (0 : Fin 1)) ≫
      Spec.map (CommRingCat.ofHom MvPolynomial.C) := by
    rw [← chart_toSpec, IsIso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- **The analytic base change isomorphism for `ℙᴺ` over `ℂ[y₀, …, y_{m-1}]`**: for coherent `G`
on `P = ℙₒ(N; ℂ[y₀, …, y_{m-1}])` and `n ≫ 0`, the base change morphism
`(p_* G(n))^an ⟶ (p^an)_* G(n)^an` for `p : P ⟶ 𝔸ᵐ` is bijective on all stalks. -/
theorem exists_bijective_bcStalk_twist [G.IsCoherent] :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ∀ y,
      Function.Bijective (bcStalk (relProjectiveSpaceToAffine.{u} m N) (twist G n) y) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · haveI : IsClosedImmersion (relProjectiveSpaceToAffine.{u} m 0).hom.left :=
      inferInstanceAs (IsClosedImmersion (ProjectiveSpace.toSpec 0 (RelBase.{u} m)))
    exact ⟨0, fun n _ ↦ (isIso_analytificationPushforwardBaseChange_iff _ _).1
      (isIso_analytificationPushforwardBaseChange _ _)⟩
  · obtain ⟨n₁, h₁⟩ := exists_surjective_bcStalk_twist G hN
    obtain ⟨n₂, h₂⟩ := exists_injective_bcStalk_twist G hN
    exact ⟨max n₁ n₂, fun n hn y ↦ ⟨h₂ n (le_of_max_le_right hn) y,
      h₁ n (le_of_max_le_left hn) y⟩⟩

end ComplexAnalytic.relProjectiveSpaceAn

end
