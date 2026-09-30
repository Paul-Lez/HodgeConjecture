/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.RepresentableOpen
public import Other.Oka.Geometry.RingedSpace.PresheafedSpace.GluingMkCore
public import Other.Oka.AnalyticSpace.Glue

/-!
# Analytifications glue

If `Y` is covered by opens `U i` each of which has an analytification, then `Y` has one: the
analytifications of the `U i` are glued along the preimages of the overlaps, the transition
isomorphisms being the ones the uniqueness of analytifications provides.

## Construction

Let `π i : W i ⟶ Y|U i` be analytifications and `p i : W i ⟶ Y` their composites with the
inclusions. Since `Y|U i ⟶ Y` is a monomorphism, a morphism from an analytic space into `W i`, or
into an open subspace of it, is determined by its composite to `Y`
(`ComplexAnalytic.GlueAnalytification.hom_ext_W`), and a morphism to `Y` landing in `U i` lifts to
`W i` (`ComplexAnalytic.GlueAnalytification.liftW`). With `V i j = p i⁻¹(U j)`, the transitions
`W i|V i j ⟶ W j|V j i` are the lifts of `p i`, and all glueing axioms hold by uniqueness. The
glued space `G` carries an analytic structure (`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear`)
and the `p i` glue to `P : G ⟶ Y`. A morphism `Z ⟶ Y` lifts locally on the cover of `Z` by the
preimages of the `U i`, and the local lifts glue; two lifts agree since `P⁻¹(U i)` is the image of
`W i`.

## Main results

- `ComplexAnalytic.GlueAnalytification.isAnalytification_P`: the glued space is an
  analytification.
- `ComplexAnalytic.rightAdjointObjIsDefined_of_iSup_eq_top`: having an analytification is local on
  the target.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

open AnalyticSpace

/-! ### The glue data -/

namespace GlueAnalytification

variable {Y : Over specℂ} {ι : Type u} {U : ι → Opens Y.left} {W : ι → AnalyticSpace.{u}}
  (π : ∀ i, toOverSpec.obj (W i) ⟶ overRestrict Y (U i))

/-- The composite `W i ⟶ Y|U i ⟶ Y`. -/
noncomputable def p (i : ι) : toOverSpec.obj (W i) ⟶ Y := π i ≫ overRestrictι Y (U i)

/-- `p i` lands in `U i`. -/
lemma p_mem (i : ι) (x : W i) : (p π i).left.base x ∈ U i := ((π i).left.base x).2

/-- The part of `W i` lying over `U j`. -/
noncomputable abbrev V (i j : ι) : (W i).Opens := (Opens.map (p π i).left.base).obj (U j)

/-- `W i` lies entirely over `U i`. -/
lemma V_self (i : ι) : V π i i = ⊤ := by
  ext x
  simp only [Opens.coe_top, Set.mem_univ, iff_true]
  exact p_mem π i x

/-- The map from the open subspace `O` of `W i` to `Y`. -/
noncomputable abbrev r (i : ι) (O : (W i).Opens) : toOverSpec.obj ((W i).restrict O) ⟶ Y :=
  toOverSpec.map ((W i).ofRestrict O) ≫ p π i

variable {π} (hπ : ∀ i, IsAnalytification (π i))
include hπ

/-- A morphism from an analytic space to `W i` is determined by its composite to `Y`. -/
lemma hom_ext_W {Z : AnalyticSpace.{u}} {i : ι} {φ ψ : Z ⟶ W i}
    (e : toOverSpec.map φ ≫ p π i = toOverSpec.map ψ ≫ p π i) : φ = ψ :=
  (hπ i).hom_ext ((cancel_mono (overRestrictι Y (U i))).1 (by simpa [p] using e))

/-- A morphism from an analytic space to an open subspace of `W i` is determined by its
composite to `Y`. -/
lemma hom_ext_V {Z : AnalyticSpace.{u}} {i : ι} {O : (W i).Opens} {φ ψ : Z ⟶ (W i).restrict O}
    (e : toOverSpec.map φ ≫ r π i O = toOverSpec.map ψ ≫ r π i O) : φ = ψ :=
  hom_ext_restrict _ _ _ (hom_ext_W hπ (by simpa using e))

/-- A morphism over `Spec ℂ` from an analytic space to `Y` landing in `U i` lifts to `W i`. -/
noncomputable def liftW {Z : AnalyticSpace.{u}} (i : ι) (f : toOverSpec.obj Z ⟶ Y)
    (hf : ∀ z, f.left.base z ∈ U i) : Z ⟶ W i :=
  (hπ i).lift (Over.homMk (LocallyRingedSpace.liftRestrict f.left (U i) (by
    rintro _ ⟨z, rfl⟩; exact hf z)) (by
    change _ ≫ Y.left.ofRestrict _ ≫ Y.hom = _
    rw [LocallyRingedSpace.liftRestrict_fac_assoc]
    exact Over.w f))

/-- `liftW` is a lift of `f`. -/
@[reassoc (attr := simp)]
lemma liftW_fac {Z : AnalyticSpace.{u}} (i : ι) (f : toOverSpec.obj Z ⟶ Y)
    (hf : ∀ z, f.left.base z ∈ U i) : toOverSpec.map (liftW hπ i f hf) ≫ p π i = f := by
  rw [p, liftW, (hπ i).lift_fac_assoc]
  ext1
  apply LocallyRingedSpace.liftRestrict_fac
  rintro _ ⟨z, rfl⟩; exact hf z

/-- The point of `Y` under the image of `z` by `liftW` is `f z`. -/
lemma liftW_base {Z : AnalyticSpace.{u}} (i : ι) (f : toOverSpec.obj Z ⟶ Y)
    (hf : ∀ z, f.left.base z ∈ U i) (z : Z) :
    (p π i).left.base ((liftW hπ i f hf).toLRSHom.base z) = f.left.base z :=
  congrArg (fun m : toOverSpec.obj Z ⟶ Y ↦ m.left.base z) (liftW_fac hπ i f hf)

/-- A morphism over `Spec ℂ` from an analytic space to `Y` landing in `U i` lifts to an open
subspace `O` of `W i` containing all points over its image. -/
noncomputable def liftV {Z : AnalyticSpace.{u}} (i : ι) (O : (W i).Opens)
    (f : toOverSpec.obj Z ⟶ Y) (hf : ∀ z, f.left.base z ∈ U i)
    (hO : ∀ z, (liftW hπ i f hf).toLRSHom.base z ∈ O) : Z ⟶ (W i).restrict O :=
  liftOpen (liftW hπ i f hf) O (by rintro _ ⟨z, rfl⟩; exact hO z)

/-- `liftV` is a lift of `f`. -/
@[reassoc (attr := simp)]
lemma liftV_fac {Z : AnalyticSpace.{u}} (i : ι) (O : (W i).Opens)
    (f : toOverSpec.obj Z ⟶ Y) (hf : ∀ z, f.left.base z ∈ U i)
    (hO : ∀ z, (liftW hπ i f hf).toLRSHom.base z ∈ O) :
    toOverSpec.map (liftV hπ i O f hf hO) ≫ r π i O = f := by
  rw [r, ← Functor.map_comp_assoc, liftV, liftOpen_fac, liftW_fac]

omit hπ in
/-- The maps of the open subspaces of `W i` to `Y` are compatible with the inclusions. -/
@[reassoc (attr := simp)]
lemma restrictLE_r (i : ι) {O O' : (W i).Opens} (h : O ≤ O') :
    toOverSpec.map ((W i).restrictLE h) ≫ r π i O' = r π i O := by
  rw [r, ← Functor.map_comp_assoc, restrictLE_fac]

omit hπ in
/-- The map of an open subspace of `W i` to `Y` is the restriction of `p i`. -/
@[reassoc (attr := simp)]
lemma ofRestrict_r (i : ι) (O : (W i).Opens) :
    toOverSpec.map ((W i).ofRestrict O) ≫ p π i = r π i O := rfl

/-- The transition morphism `W i|V i j ⟶ W j|V j i`, compatible with the maps to `Y`. -/
noncomputable def t (i j : ι) : (W i).restrict (V π i j) ⟶ (W j).restrict (V π j i) :=
  liftV hπ j (V π j i) (r π i (V π i j)) (fun z ↦ z.2) (fun z ↦ by
    change (p π j).left.base _ ∈ U i
    rw [liftW_base]
    exact p_mem π i z.1)

/-- The transition morphisms are compatible with the maps to `Y`. -/
@[reassoc (attr := simp)]
lemma t_r (i j : ι) : toOverSpec.map (t hπ i j) ≫ r π j (V π j i) = r π i (V π i j) :=
  liftV_fac ..

/-- The transition morphism on triple overlaps. -/
noncomputable def t' (i j k : ι) :
    (W i).restrict (V π i j ⊓ V π i k) ⟶ (W j).restrict (V π j k ⊓ V π j i) :=
  liftV hπ j (V π j k ⊓ V π j i) (r π i (V π i j ⊓ V π i k)) (fun z ↦ z.2.1) (fun z ↦ by
    constructor
    · change (p π j).left.base _ ∈ U k
      rw [liftW_base]
      exact z.2.2
    · change (p π j).left.base _ ∈ U i
      rw [liftW_base]
      exact p_mem π i z.1)

/-- The transition morphisms on triple overlaps are compatible with the maps to `Y`. -/
@[reassoc (attr := simp)]
lemma t'_r (i j k : ι) :
    toOverSpec.map (t' hπ i j k) ≫ r π j (V π j k ⊓ V π j i) = r π i (V π i j ⊓ V π i k) :=
  liftV_fac ..

/-- The transition morphism from `W i` to itself is the identity. -/
lemma t_self (i : ι) : t hπ i i = 𝟙 _ :=
  hom_ext_V hπ (by simp)

/-- The transition morphisms are mutually inverse. -/
lemma t_inv (i j : ι) : t hπ i j ≫ t hπ j i = 𝟙 _ :=
  hom_ext_V hπ (by simp)

/-- The transition morphisms on triple overlaps restrict the transition morphisms. -/
lemma t'_fac (i j k : ι) :
    t' hπ i j k ≫ (W j).restrictLE inf_le_right = (W i).restrictLE inf_le_left ≫ t hπ i j :=
  hom_ext_V hπ (by
    simp only [Functor.map_comp, Category.assoc]
    rw [restrictLE_r, t_r, t'_r, restrictLE_r])

/-- The cocycle condition. -/
lemma cocycle (i j k : ι) : t' hπ i j k ≫ t' hπ j k i ≫ t' hπ k i j = 𝟙 _ :=
  hom_ext_V hπ (by simp)

/-- The gluing datum of the `W i` along the `V i j`. -/
noncomputable def mkCore : LocallyRingedSpace.GlueData.MkCore.{u} where
  J := ι
  U i := (W i).toLocallyRingedSpace
  V := V π
  t i j := (t hπ i j).toLRSHom
  V_id := V_self π
  t_id i := congrArg AnalyticSpace.Hom.toLRSHom (t_self hπ i)
  t' i j k := (t' hπ i j k).toLRSHom
  t'_fac i j k := congrArg AnalyticSpace.Hom.toLRSHom (t'_fac hπ i j k)
  t_inv i j := congrArg AnalyticSpace.Hom.toLRSHom (t_inv hπ i j)
  cocycle i j k := congrArg AnalyticSpace.Hom.toLRSHom (cocycle hπ i j k)

/-- The glue data of locally ringed spaces. -/
noncomputable abbrev D : LocallyRingedSpace.GlueData.{u} := (mkCore hπ).toGlueData

/-- The transitions of the glue data are `ℂ`-linear. -/
lemma glueDataCLinear : GlueDataCLinear (D hπ) (fun i ↦ (W i).algebraMap) :=
  glueDataCLinear_of_isCLinearHom (D hπ) (fun i ↦ (W i).algebraMap)
    (fun ij ↦ ((W ij.1).restrict (V π ij.1 ij.2)).algebraMap)
    (fun i j ↦ ((W i).ofRestrict (V π i j)).isCLinear) (fun i j ↦ (t hπ i j).isCLinear)

/-- The glued analytic space. -/
noncomputable def G : AnalyticSpace.{u} :=
  ofGlueDataCLinear (D hπ) (fun i ↦ (W i).algebraMap) (glueDataCLinear hπ)
    (fun i ↦ (W i).local_model)

/-- The inclusion of `W i` into the glued space. -/
noncomputable def ιG (i : ι) : W i ⟶ G hπ :=
  ιCLinear (D hπ) (fun i ↦ (W i).algebraMap) (glueDataCLinear hπ) (fun i ↦ (W i).local_model) i

/-- The glue condition, for the analytic inclusions. -/
lemma ofRestrict_ιG (i j : ι) :
    (W i).ofRestrict (V π i j) ≫ ιG hπ i = t hπ i j ≫ (W j).ofRestrict (V π j i) ≫ ιG hπ j :=
  forgetToLocallyRingedSpace.map_injective ((D hπ).toGlueData.glue_condition i j).symm

/-- The glued morphism from the glued space to `Y`, as a morphism of locally ringed spaces. -/
noncomputable def PLeft : (G hπ).toLocallyRingedSpace ⟶ Y.left :=
  (D hπ).glueMorphisms (fun j ↦ (p π j).left)
    (fun i j ↦ congrArg CommaMorphism.left (t_r hπ i j).symm)

/-- `P` restricts to `p i` on `W i`, as morphisms of locally ringed spaces. -/
@[reassoc (attr := simp)]
lemma ιG_PLeft (i : ι) : (ιG hπ i).toLRSHom ≫ PLeft hπ = (p π i).left :=
  (D hπ).ι_glueMorphisms _ _ i

/-- The glued morphism from the glued space to `Y`, over `Spec ℂ`. -/
noncomputable def P : toOverSpec.obj (G hπ) ⟶ Y :=
  Over.homMk (PLeft hπ) (by
    refine (D hπ).hom_ext _ _ fun (j : ι) ↦ ?_
    change (ιG hπ j).toLRSHom ≫ PLeft hπ ≫ Y.hom = (ιG hπ j).toLRSHom ≫ (G hπ).toSpecℂ
    rw [ιG_PLeft_assoc]
    exact (Over.w (p π j)).trans (Over.w (toOverSpec.map (ιG hπ j))).symm)

/-- `P` restricts to `p i` on `W i`. -/
@[reassoc (attr := simp)]
lemma ιG_P (i : ι) : toOverSpec.map (ιG hπ i) ≫ P hπ = p π i := by
  ext1
  exact ιG_PLeft hπ i

/-- `P` restricts to `p i` on `W i`, on points. -/
lemma PLeft_base (i : ι) (w : W i) :
    (PLeft hπ).base ((ιG hπ i).toLRSHom.base w) = (p π i).left.base w :=
  congrArg (fun m : (W i).toLocallyRingedSpace ⟶ Y.left ↦ m.base w) (ιG_PLeft hπ i)

/-- A point of the glued space lying over `U i` comes from `W i`. -/
lemma exists_ιG (i : ι) (x : G hπ) (hx : (PLeft hπ).base x ∈ U i) :
    ∃ w, (ιG hπ i).toLRSHom.base w = x := by
  obtain ⟨j, y, rfl⟩ := (D hπ).ι_jointly_surjective x
  have hy : y ∈ V π j i := by
    have hx' : (PLeft hπ).base ((ιG hπ j).toLRSHom.base y) ∈ U i := hx
    rw [PLeft_base] at hx'
    exact hx'
  refine ⟨((t hπ j i).toLRSHom.base ⟨y, hy⟩).1, ?_⟩
  have := congrArg (fun m : (W j).restrict (V π j i) ⟶ G hπ ↦ m.toLRSHom.base ⟨y, hy⟩)
    (ofRestrict_ιG hπ j i)
  exact this.symm

/-- The inclusions of the `W i` into the glued space are open immersions. -/
instance (i : ι) : LocallyRingedSpace.IsOpenImmersion (ιG hπ i).toLRSHom :=
  LocallyRingedSpace.GlueData.ι_isOpenImmersion (D hπ) i

/-- A morphism into the glued space lying over `U i` factors through `W i`, as a morphism of
locally ringed spaces. -/
noncomputable def liftGLRS {Z : AnalyticSpace.{u}} (i : ι) (χ : Z ⟶ G hπ)
    (h : ∀ z, (PLeft hπ).base (χ.toLRSHom.base z) ∈ U i) :
    Z.toLocallyRingedSpace ⟶ (W i).toLocallyRingedSpace :=
  LocallyRingedSpace.IsOpenImmersion.lift (ιG hπ i).toLRSHom χ.toLRSHom (by
      rintro _ ⟨z, rfl⟩; exact exists_ιG hπ i _ (h z))

/-- `liftGLRS` is a factorisation. -/
lemma liftGLRS_fac {Z : AnalyticSpace.{u}} (i : ι) (χ : Z ⟶ G hπ)
    (h : ∀ z, (PLeft hπ).base (χ.toLRSHom.base z) ∈ U i) :
    liftGLRS hπ i χ h ≫ (ιG hπ i).toLRSHom = χ.toLRSHom :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac (ιG hπ i).toLRSHom χ.toLRSHom _

/-- A morphism into the glued space lying over `U i` factors through `W i`. -/
noncomputable def liftG {Z : AnalyticSpace.{u}} (i : ι) (χ : Z ⟶ G hπ)
    (h : ∀ z, (PLeft hπ).base (χ.toLRSHom.base z) ∈ U i) : Z ⟶ W i :=
  ⟨liftGLRS hπ i χ h, IsCLinearHom.of_comp (liftGLRS_fac hπ i χ h) χ.isCLinear (ιG hπ i).isCLinear⟩

/-- `liftG` is a factorisation. -/
@[reassoc (attr := simp)]
lemma liftG_fac {Z : AnalyticSpace.{u}} (i : ι) (χ : Z ⟶ G hπ)
    (h : ∀ z, (PLeft hπ).base (χ.toLRSHom.base z) ∈ U i) : liftG hπ i χ h ≫ ιG hπ i = χ :=
  forgetToLocallyRingedSpace.map_injective (liftGLRS_fac hπ i χ h)

omit hπ in
/-- Two morphisms over `Spec ℂ` out of an analytic space agreeing on an open cover are equal. -/
lemma over_hom_ext_of_opens {Z : AnalyticSpace.{u}} {κ : Type u} (O : κ → Z.Opens)
    (hO : ∀ z, ∃ i, z ∈ O i) {Y' : Over specℂ} {a b : toOverSpec.obj Z ⟶ Y'}
    (h : ∀ i, toOverSpec.map (Z.ofRestrict (O i)) ≫ a = toOverSpec.map (Z.ofRestrict (O i)) ≫ b) :
    a = b := by
  ext1
  exact (LocallyRingedSpace.openCoverOfOpens O hO).hom_ext _ _
    fun i ↦ congrArg CommaMorphism.left (h i)

omit hπ in
/-- The preimages of the `U i` cover the source. -/
lemma exists_mem_of_iSup_eq_top (hU : ⨆ i, U i = ⊤) {Z : AnalyticSpace.{u}}
    (f : toOverSpec.obj Z ⟶ Y) (z : Z) :
    ∃ i, z ∈ (Opens.map f.left.base).obj (U i) := by
  have : f.left.base z ∈ (⊤ : Opens Y.left) := trivial
  rw [← hU] at this
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 this
  exact ⟨i, hi⟩

/-- The composite of `liftG` to `Y`. -/
@[reassoc (attr := simp)]
lemma liftG_p {Z : AnalyticSpace.{u}} (i : ι) (χ : Z ⟶ G hπ)
    (h : ∀ z, (PLeft hπ).base (χ.toLRSHom.base z) ∈ U i) :
    toOverSpec.map (liftG hπ i χ h) ≫ p π i = toOverSpec.map χ ≫ P hπ := by
  rw [← ιG_P, ← Functor.map_comp_assoc, liftG_fac]

/-- A morphism from an analytic space to the glued space is determined by its composite to
`Y`. -/
lemma hom_ext_G (hU : ⨆ i, U i = ⊤) {Z : AnalyticSpace.{u}} {φ ψ : Z ⟶ G hπ}
    (e : toOverSpec.map φ ≫ P hπ = toOverSpec.map ψ ≫ P hπ) : φ = ψ := by
  let O : ι → Z.Opens := fun i ↦ (Opens.map (toOverSpec.map φ ≫ P hπ).left.base).obj (U i)
  refine hom_ext_of_opens O (exists_mem_of_iSup_eq_top hU (toOverSpec.map φ ≫ P hπ)) fun i ↦ ?_
  have h1 : ∀ z, (PLeft hπ).base ((Z.ofRestrict (O i) ≫ φ).toLRSHom.base z) ∈ U i :=
    fun z ↦ z.2
  have h2 : ∀ z, (PLeft hπ).base ((Z.ofRestrict (O i) ≫ ψ).toLRSHom.base z) ∈ U i := fun z ↦ by
    have := congrArg (fun m ↦ m.left.base z.1) e
    exact this ▸ z.2
  have : liftG hπ i _ h1 = liftG hπ i _ h2 := hom_ext_W hπ (by
    rw [liftG_p, liftG_p, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, e])
  rw [← liftG_fac hπ i _ h1, ← liftG_fac hπ i _ h2, this]
section Lift

variable {Z : AnalyticSpace.{u}} (f : toOverSpec.obj Z ⟶ Y)

omit hπ in
variable (U) in
/-- The part of `Z` mapping into `U i`. -/
noncomputable abbrev O (i : ι) : Z.Opens := (Opens.map f.left.base).obj (U i)

/-- The lift of `f` over `U i` to `W i`. -/
noncomputable def lam (i : ι) : Z.restrict (O U f i) ⟶ W i :=
  liftW hπ i (toOverSpec.map (Z.ofRestrict (O U f i)) ≫ f) (fun z ↦ z.2)

/-- `lam` is a lift of the restriction of `f`. -/
@[reassoc (attr := simp)]
lemma lam_p (i : ι) : toOverSpec.map (lam hπ f i) ≫ p π i = toOverSpec.map (Z.ofRestrict _) ≫ f :=
  liftW_fac ..

/-- The local lifts `lam` agree on the overlaps after inclusion into the glued space. -/
lemma lam_compat (i j : ι) :
    Z.restrictLE (inf_le_left : O U f i ⊓ O U f j ≤ O U f i) ≫ lam hπ f i ≫ ιG hπ i =
      Z.restrictLE (inf_le_right : O U f i ⊓ O U f j ≤ O U f j) ≫ lam hπ f j ≫ ιG hπ j := by
  let μ := liftV hπ i (V π i j) (toOverSpec.map (Z.ofRestrict (O U f i ⊓ O U f j)) ≫ f)
    (fun z ↦ z.2.1) (fun z ↦ by
      change (p π i).left.base _ ∈ U j
      rw [liftW_base]
      exact z.2.2)
  have hμ : toOverSpec.map μ ≫ r π i (V π i j) =
      toOverSpec.map (Z.ofRestrict (O U f i ⊓ O U f j)) ≫ f := liftV_fac ..
  have e1 : Z.restrictLE inf_le_left ≫ lam hπ f i = μ ≫ (W i).ofRestrict (V π i j) := by
    refine hom_ext_W hπ ?_
    rw [Functor.map_comp_assoc, lam_p, ← Functor.map_comp_assoc, restrictLE_fac,
      Functor.map_comp_assoc, ofRestrict_r, hμ]
  have e2 : Z.restrictLE inf_le_right ≫ lam hπ f j =
      μ ≫ t hπ i j ≫ (W j).ofRestrict (V π j i) := by
    refine hom_ext_W hπ ?_
    rw [Functor.map_comp_assoc, lam_p, ← Functor.map_comp_assoc, restrictLE_fac,
      Functor.map_comp_assoc, Functor.map_comp_assoc, ofRestrict_r, t_r, hμ]
  rw [reassoc_of% e1, reassoc_of% e2, ofRestrict_ιG]

variable (hU : ⨆ i, U i = ⊤)

/-- The lift of `f` to the glued space. -/
noncomputable def glueLift : Z ⟶ G hπ :=
  glueMorphismsOfOpens (O U f) (exists_mem_of_iSup_eq_top hU f) (fun i ↦ lam hπ f i ≫ ιG hπ i)
    (lam_compat hπ f)

/-- `glueLift` is a lift of `f`. -/
lemma glueLift_fac : toOverSpec.map (glueLift hπ f hU) ≫ P hπ = f := by
  refine over_hom_ext_of_opens (O U f) (exists_mem_of_iSup_eq_top hU f) fun i ↦ ?_
  rw [← Functor.map_comp_assoc, glueLift, ofRestrict_comp_glueMorphismsOfOpens,
    Functor.map_comp_assoc, ιG_P, lam_p]

end Lift

/-- **The glued space is an analytification of `Y`.** -/
theorem isAnalytification_P (hU : ⨆ i, U i = ⊤) : IsAnalytification (P hπ) :=
  fun _ ↦ ⟨fun _ _ e ↦ hom_ext_G hπ hU e, fun f ↦ ⟨glueLift hπ f hU, glueLift_fac hπ f hU⟩⟩

end GlueAnalytification

/-- **Having an analytification is local on `Y`.** -/
theorem rightAdjointObjIsDefined_of_iSup_eq_top (Y : Over specℂ.{u}) {ι : Type u}
    (U : ι → Opens Y.left) (hU : ⨆ i, U i = ⊤)
    (h : ∀ i, toOverSpec.{u}.rightAdjointObjIsDefined (overRestrict Y (U i))) :
    toOverSpec.{u}.rightAdjointObjIsDefined Y := by
  choose W π hπ using fun i ↦ exists_isAnalytification (h i)
  exact (GlueAnalytification.isAnalytification_P hπ hU).rightAdjointObjIsDefined

end ComplexAnalytic

end
