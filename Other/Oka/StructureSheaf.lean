/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Analysis.Analytic.Within
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Other.Oka.OkaRing

/-!
# The structure sheaf of `ℂ^ι`

We assemble the rings `OkaRing U` of holomorphic functions on the opens `U` of `ℂ^ι` into a
sheaf of rings `okaSheaf ι` on the site of opens of `ℂ^ι`.

## Main definitions

- `okaPresheaf`: the presheaf of rings `U ↦ OkaRing U`.
- `okaSheaf`: the structure sheaf of `ℂ^ι`, i.e. `okaPresheaf` together with the sheaf condition.
- `OkaRing.evalHom`: evaluation of a holomorphic function at a point of its domain.
- `OkaRing.congr`: the isomorphism of rings of holomorphic functions induced by a `ℂ`-linear
  change of coordinates `ℂ^ι ≃ ℂ^κ`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

variable {ι : Type u} [Fintype ι]

namespace OkaRing

@[ext]
lemma ext {U : Opens (ι → ℂ)} {f g : OkaRing U} (h : f.toFun = g.toFun) : f = g :=
  Subtype.ext h

@[simp]
lemma restrict_toFun {U V : Opens (ι → ℂ)} (h : U ≤ V) (f : OkaRing V) :
    (OkaRing.restrict h f).toFun = f.toFun ∘ Opens.inclusion h :=
  rfl

@[simp]
lemma restrict_self {U : Opens (ι → ℂ)} (f : OkaRing U) :
    OkaRing.restrict le_rfl f = f :=
  rfl

@[simp]
lemma restrict_restrict {U V W : Opens (ι → ℂ)} (h : U ≤ V) (h' : V ≤ W) (f : OkaRing W) :
    OkaRing.restrict h (OkaRing.restrict h' f) = OkaRing.restrict (h.trans h') f :=
  rfl

/-- Evaluation of a holomorphic function at a point of its domain, as a ring homomorphism. -/
def evalHom {U : Opens (ι → ℂ)} {x : ι → ℂ} (hx : x ∈ U) : OkaRing U →+* ℂ where
  toFun f := f.toFun _ ⟨x, hx⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma evalHom_apply {U : Opens (ι → ℂ)} {x : ι → ℂ} (hx : x ∈ U) (f : OkaRing U) :
    OkaRing.evalHom hx f = f.toFun _ ⟨x, hx⟩ :=
  rfl

@[simp]
lemma evalHom_restrict {U V : Opens (ι → ℂ)} (h : V ≤ U) {x : ι → ℂ} (hx : x ∈ V)
    (f : OkaRing U) :
    OkaRing.evalHom hx (OkaRing.restrict h f) = OkaRing.evalHom (h hx) f :=
  rfl

-- Not `@[simp]`: `evalHom_apply` is `@[simp]` and unfolds `evalHom` to `toFun`, so the
-- left-hand side here is never in normal form. `toFun_algebraMap` below is the form `simp`
-- actually meets.
lemma evalHom_algebraMap {U : Opens (ι → ℂ)} {x : ι → ℂ} (hx : x ∈ U) (c : ℂ) :
    OkaRing.evalHom hx (algebraMap ℂ (OkaRing U) c) = c :=
  rfl

/-- `evalHom_algebraMap` in `simp` normal form: a constant function has that constant as its
value at every point. -/
@[simp]
lemma toFun_algebraMap {U : Opens (ι → ℂ)} (c : ℂ) (p : U) :
    OkaRing.toFun U (algebraMap ℂ (OkaRing U) c) p = c :=
  rfl

end OkaRing

section Analytic

/-- Being holomorphic is a pointwise condition: since `U` is open, `OkaAnalytic f` holds if and
only if the extension of `f` by zero is analytic at every point of `U`. -/
lemma okaAnalytic_iff {U : Opens (ι → ℂ)} (f : U → ℂ) :
    OkaAnalytic f ↔ ∀ x ∈ U, AnalyticAt ℂ (Function.extend Subtype.val f 0) x :=
  U.isOpen.analyticOn_iff_analyticOnNhd

omit [Fintype ι] in
/-- Extending by zero commutes with restriction, up to functions agreeing near a point of the
smaller open set. -/
lemma extend_eventuallyEq_extend {U V : Opens (ι → ℂ)} (h : U ≤ V) (f : V → ℂ)
    {x : ι → ℂ} (hx : x ∈ U) :
    Function.extend Subtype.val (f ∘ Opens.inclusion h) 0 =ᶠ[nhds x]
      Function.extend Subtype.val f 0 := by
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  have h₁ : Function.extend Subtype.val (f ∘ Opens.inclusion h) 0 y = f ⟨y, h hy⟩ :=
    Subtype.val_injective.extend_apply (f := (Subtype.val : U → ι → ℂ)) _ _ ⟨y, hy⟩
  have h₂ : Function.extend Subtype.val f 0 y = f ⟨y, h hy⟩ :=
    Subtype.val_injective.extend_apply (f := (Subtype.val : V → ι → ℂ)) _ _ ⟨y, h hy⟩
  rw [h₁, h₂]

omit [Fintype ι] in
/-- Near a point of `U`, the extension by zero of the restriction of a globally defined
function agrees with the function itself. -/
lemma extend_restrict_eventuallyEq {U : Opens (ι → ℂ)} (g : (ι → ℂ) → ℂ)
    {x : ι → ℂ} (hx : x ∈ U) :
    Function.extend Subtype.val (fun y : U ↦ g y) 0 =ᶠ[nhds x] g := by
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  exact Subtype.val_injective.extend_apply (f := (Subtype.val : U → ι → ℂ)) _ _ ⟨y, hy⟩

/-- A function which is holomorphic at every point of `U` restricts to an element of the ring
of holomorphic functions on `U`. -/
lemma okaAnalytic_restrict {U : Opens (ι → ℂ)} {g : (ι → ℂ) → ℂ}
    (hg : ∀ x ∈ U, AnalyticAt ℂ g x) :
    OkaAnalytic (fun y : U ↦ g y) := by
  rw [okaAnalytic_iff]
  exact fun x hx ↦ (hg x hx).congr (extend_restrict_eventuallyEq g hx).symm

/-- The extension by zero of `f : OkaRing U` agrees with `f` on `U`. -/
lemma OkaRing.toGlobalFun_apply {U : Opens (ι → ℂ)} (f : OkaRing U) {x : ι → ℂ} (hx : x ∈ U) :
    f.toGlobalFun _ x = f.toFun _ ⟨x, hx⟩ :=
  Subtype.val_injective.extend_apply (f := (Subtype.val : U → ι → ℂ)) _ _ ⟨x, hx⟩

/-- **A holomorphic function is continuous on its domain.** -/
lemma OkaRing.continuousOn_toGlobalFun {U : Opens (ι → ℂ)} (f : OkaRing U) :
    ContinuousOn (f.toGlobalFun _) U :=
  fun x hx ↦ ((okaAnalytic_iff _).1 f.2 x hx).continuousAt.continuousWithinAt

/-- **The value of a holomorphic function depends continuously on the point.**

This is `OkaRing.continuousOn_toGlobalFun` read through `OkaRing.evalHom`, and it is the form
in which the value map of a complex analytic space is shown to be continuous. -/
lemma OkaRing.continuous_evalHom {U : Opens (ι → ℂ)} (f : OkaRing U) :
    Continuous fun x : U ↦ OkaRing.evalHom x.2 f := by
  refine (continuousOn_iff_continuous_restrict.1 f.continuousOn_toGlobalFun).congr fun x ↦ ?_
  exact f.toGlobalFun_apply x.2

/-- Holomorphic functions restrict to holomorphic functions. -/
lemma OkaAnalytic.restrict {U V : Opens (ι → ℂ)} (h : U ≤ V) {f : V → ℂ} (hf : OkaAnalytic f) :
    OkaAnalytic (f ∘ Opens.inclusion h) := by
  rw [okaAnalytic_iff] at hf ⊢
  exact fun x hx ↦ (hf x (h hx)).congr (extend_eventuallyEq_extend h f hx).symm

/-- Being holomorphic is a local condition. -/
lemma okaAnalytic_of_locally {U : Opens (ι → ℂ)} (f : U → ℂ)
    (hf : ∀ x : U, ∃ (V : Opens (ι → ℂ)) (_ : x.1 ∈ V) (h : V ≤ U),
      OkaAnalytic (f ∘ Opens.inclusion h)) :
    OkaAnalytic f := by
  rw [okaAnalytic_iff]
  intro x hx
  obtain ⟨V, hxV, h, hV⟩ := hf ⟨x, hx⟩
  rw [okaAnalytic_iff] at hV
  exact (hV x hxV).congr (extend_eventuallyEq_extend h f hxV)

end Analytic

section Reindex

/-- A continuous linear equivalence induces an order isomorphism on open sets. -/
abbrev ContinuousLinearEquiv.opensCongr {R E F : Type*} [Semiring R]
    [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]
    [TopologicalSpace E] [TopologicalSpace F] (φ : E ≃L[R] F) :
    Opens E ≃o Opens F :=
  φ.toHomeomorph.opensCongr

variable {κ : Type*} [Fintype κ] (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ))

/-- Precomposing a holomorphic function on `U` with a continuous linear map mapping `V` into `U`
gives a holomorphic function on `V`. -/
lemma OkaAnalytic.comp_continuousLinearMap {U : Opens (ι → ℂ)} {V : Opens (κ → ℂ)}
    (ψ : (κ → ℂ) →L[ℂ] (ι → ℂ)) (h : ∀ y ∈ V, ψ y ∈ U) {f : U → ℂ} (hf : OkaAnalytic f) :
    OkaAnalytic (fun y : V ↦ f ⟨ψ y, h y y.2⟩) := by
  have key : ∀ y ∈ V, AnalyticAt ℂ (Function.extend Subtype.val f 0 ∘ ψ) y := fun y hy ↦
    ((okaAnalytic_iff f).1 hf _ (h y hy)).comp (ψ.analyticAt y)
  refine (funext fun z ↦ ?_ : (fun y : V ↦ f ⟨ψ y, h y y.2⟩) =
    fun y : V ↦ (Function.extend Subtype.val f 0 ∘ ψ) y) ▸ okaAnalytic_restrict key
  exact (Subtype.val_injective.extend_apply _ _ ⟨ψ z, h z z.2⟩).symm

/-- A `ℂ`-linear change of coordinates `φ : ℂ^ι ≃ ℂ^κ` identifies the holomorphic functions on
`U` with the holomorphic functions on the image of `U`. -/
noncomputable def OkaRing.congr (U : Opens (ι → ℂ)) :
    OkaRing U ≃ₐ[ℂ] OkaRing (φ.opensCongr U) where
  toFun f := OkaRing.mk (fun y ↦ f.toFun _ ⟨φ.symm y, y.2⟩)
    (f.2.comp_continuousLinearMap (φ.symm : (κ → ℂ) →L[ℂ] (ι → ℂ)) fun _ hy ↦ hy)
  invFun g := OkaRing.mk (fun z ↦ g.toFun _ ⟨φ z, by simp [z.2]⟩)
    (g.2.comp_continuousLinearMap (φ : (ι → ℂ) →L[ℂ] (κ → ℂ)) fun _ hz ↦ by simp [hz])
  left_inv f := by
    ext z
    exact congrArg (f.toFun _) (Subtype.ext (φ.symm_apply_apply (z : ι → ℂ)))
  right_inv g := by
    ext z
    exact congrArg (g.toFun _) (Subtype.ext (φ.apply_symm_apply (z : κ → ℂ)))
  map_mul' f g := rfl
  map_add' f g := rfl
  commutes' c := rfl

/-- Changing coordinates commutes with restriction. -/
lemma OkaRing.congr_restrict {U V : Opens (ι → ℂ)} (h : V ≤ U) (f : OkaRing U) :
    OkaRing.congr φ V (OkaRing.restrict h f) =
      OkaRing.restrict (φ.opensCongr.monotone h) (OkaRing.congr φ U f) :=
  rfl

/-- Changing coordinates back commutes with restriction. -/
lemma OkaRing.congr_symm_restrict {U V : Opens (ι → ℂ)}
    (h : φ.opensCongr V ≤ φ.opensCongr U) (g : OkaRing (φ.opensCongr U)) :
    (OkaRing.congr φ V).symm (OkaRing.restrict h g) =
      OkaRing.restrict (φ.opensCongr.le_iff_le.mp h) ((OkaRing.congr φ U).symm g) :=
  rfl

end Reindex

section Translate

/-- **Precomposing a holomorphic function on `U` with a map which is analytic only on `V` and
sends `V` into `U` gives a holomorphic function on `V`.**

`ψ` is a map defined on all of `κ → ℂ`, but analyticity is required only at the points of `V`,
which is all the conclusion can see. That is what makes this usable when `ψ` comes from a
holomorphic function on a *proper* open subset; extended by zero outside it, as
`OkaRing.toGlobalFun` does; where analyticity off `V` is false and irrelevant. -/
lemma OkaAnalytic.comp_analyticOn {κ : Type u} [Fintype κ] {U : Opens (ι → ℂ)}
    {V : Opens (κ → ℂ)} (ψ : (κ → ℂ) → (ι → ℂ)) (hψ : ∀ y ∈ V, AnalyticAt ℂ ψ y)
    (h : ∀ y ∈ V, ψ y ∈ U) {f : U → ℂ} (hf : OkaAnalytic f) :
    OkaAnalytic (fun y : V ↦ f ⟨ψ y, h y y.2⟩) := by
  have key : ∀ y ∈ V, AnalyticAt ℂ (Function.extend Subtype.val f 0 ∘ ψ) y := fun y hy ↦
    ((okaAnalytic_iff f).1 hf _ (h y hy)).comp (hψ y hy)
  refine (funext fun z ↦ ?_ : (fun y : V ↦ f ⟨ψ y, h y y.2⟩) =
    fun y : V ↦ (Function.extend Subtype.val f 0 ∘ ψ) y) ▸ okaAnalytic_restrict key
  exact (Subtype.val_injective.extend_apply _ _ ⟨ψ z, h z z.2⟩).symm

/-- Precomposing a holomorphic function on `U` with an entire map sending `V` into `U` gives a
holomorphic function on `V`. -/
lemma OkaAnalytic.comp_analytic {κ : Type u} [Fintype κ] {U : Opens (ι → ℂ)} {V : Opens (κ → ℂ)}
    (ψ : (κ → ℂ) → (ι → ℂ)) (hψ : ∀ y, AnalyticAt ℂ ψ y) (h : ∀ y ∈ V, ψ y ∈ U)
    {f : U → ℂ} (hf : OkaAnalytic f) :
    OkaAnalytic (fun y : V ↦ f ⟨ψ y, h y y.2⟩) :=
  hf.comp_analyticOn ψ (fun y _ ↦ hψ y) h

namespace TopologicalSpace.Opens

omit [Fintype ι]

variable (U : Opens (ι → ℂ)) (v : ι → ℂ)

/-- The translate of an open set `U` of `ℂ^ι` by `-v`, i.e. the preimage of `U` under the
translation `y ↦ y + v`. Its points are the `y` with `y + v ∈ U`. -/
def shift : Opens (ι → ℂ) :=
  ⟨(fun y ↦ y + v) ⁻¹' U, U.isOpen.preimage (continuous_id.add continuous_const)⟩

@[simp]
lemma mem_shift {y : ι → ℂ} : y ∈ U.shift v ↔ y + v ∈ U :=
  Iff.rfl

@[simp]
lemma shift_zero : U.shift 0 = U := by
  ext y
  simp

variable {U v} in
lemma shift_mono {V : Opens (ι → ℂ)} (h : U ≤ V) : U.shift v ≤ V.shift v :=
  fun _ hy ↦ h hy

lemma shift_shift (w : ι → ℂ) : (U.shift v).shift w = U.shift (v + w) := by
  ext y
  simp [add_comm, add_left_comm]

@[simp]
lemma shift_shift_neg : (U.shift v).shift (-v) = U := by
  rw [shift_shift]
  simp

variable {U v} in
lemma shift_le_shift_iff {V : Opens (ι → ℂ)} : U.shift v ≤ V.shift v ↔ U ≤ V := by
  refine ⟨fun h y hy ↦ ?_, fun h ↦ shift_mono h⟩
  have hy' : y - v ∈ U.shift v := by simpa using hy
  simpa using h hy'

end TopologicalSpace.Opens

variable (U : Opens (ι → ℂ)) (v : ι → ℂ)

/-- Translation by `v` identifies the holomorphic functions on `U` with the holomorphic
functions on the translate `U.shift v` of `U`. -/
noncomputable def OkaRing.shift : OkaRing U ≃ₐ[ℂ] OkaRing (U.shift v) where
  toFun f := OkaRing.mk (fun y ↦ f.toFun _ ⟨(y : ι → ℂ) + v, y.2⟩)
    (f.2.comp_analytic (fun y ↦ y + v) (fun _ ↦ analyticAt_id.add analyticAt_const) fun _ hy ↦ hy)
  invFun g := OkaRing.mk (fun z ↦ g.toFun _ ⟨(z : ι → ℂ) - v, by simp⟩)
    (g.2.comp_analytic (fun z ↦ z - v) (fun _ ↦ analyticAt_id.sub analyticAt_const)
      fun _ hz ↦ by simpa using hz)
  left_inv f := by
    ext z
    exact congrArg (f.toFun _) (Subtype.ext (by simp))
  right_inv g := by
    ext z
    exact congrArg (g.toFun _) (Subtype.ext (by simp))
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable {U v}

/-- Translating commutes with restriction. -/
lemma OkaRing.shift_restrict {V : Opens (ι → ℂ)} (h : V ≤ U) (f : OkaRing U) :
    OkaRing.shift V v (OkaRing.restrict h f) =
      OkaRing.restrict (Opens.shift_mono h) (OkaRing.shift U v f) :=
  rfl

/-- Translating back commutes with restriction. -/
lemma OkaRing.shift_symm_restrict {V : Opens (ι → ℂ)} (h : V.shift v ≤ U.shift v)
    (g : OkaRing (U.shift v)) :
    (OkaRing.shift V v).symm (OkaRing.restrict h g) =
      OkaRing.restrict (Opens.shift_le_shift_iff.mp h) ((OkaRing.shift U v).symm g) :=
  rfl

end Translate

/-- The presheaf of rings of holomorphic functions on `ℂ^ι`. -/
noncomputable def okaPresheaf (ι : Type u) [Fintype ι] : (Opens (ι → ℂ))ᵒᵖ ⥤ RingCat.{u} where
  obj U := RingCat.of (OkaRing U.unop)
  map f := RingCat.ofHom (OkaRing.restrict (leOfHom f.unop)).toRingHom
  map_id U := by ext f; rfl
  map_comp f g := by ext h; rfl

/-- Being holomorphic, as a local predicate on the sheaf of `ℂ`-valued functions. -/
def okaLocalPredicate (ι : Type u) [Fintype ι] :
    TopCat.LocalPredicate (X := TopCat.of (ι → ℂ)) (fun _ ↦ ℂ) where
  pred {_} f := OkaAnalytic f
  res i _ hf := hf.restrict (leOfHom i)
  locality _ hf := okaAnalytic_of_locally _ fun x ↦ by
    obtain ⟨V, hxV, i, hi⟩ := hf x
    exact ⟨V, hxV, leOfHom i, hi⟩

/-- The presheaf of holomorphic functions is, as a presheaf of types, the subpresheaf of the
sheaf of all `ℂ`-valued functions cut out by the local predicate `OkaAnalytic`. -/
noncomputable def okaPresheafIsoSubpresheaf (ι : Type u) [Fintype ι] :
    okaPresheaf ι ⋙ CategoryTheory.forget RingCat.{u} ≅
      TopCat.subpresheafToTypes (okaLocalPredicate ι).toPrelocalPredicate :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The presheaf of holomorphic functions on `ℂ^ι` is a sheaf. -/
theorem okaPresheaf_isSheaf (ι : Type u) [Fintype ι] :
    Presheaf.IsSheaf (Opens.grothendieckTopology (ι → ℂ)) (okaPresheaf ι) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget RingCat.{u}),
    isSheaf_iff_isSheaf_of_type]
  have h := TopCat.subpresheafToTypes.isSheaf (okaLocalPredicate ι)
  rw [TopCat.Presheaf.IsSheaf, isSheaf_iff_isSheaf_of_type] at h
  exact Presieve.isSheaf_iso _ (okaPresheafIsoSubpresheaf ι).symm h

/-- The structure sheaf of `ℂ^ι`: the sheaf of rings of holomorphic functions. -/
noncomputable def okaSheaf (ι : Type u) [Fintype ι] :
    Sheaf (Opens.grothendieckTopology (ι → ℂ)) RingCat.{u} :=
  ⟨okaPresheaf ι, okaPresheaf_isSheaf ι⟩

end
