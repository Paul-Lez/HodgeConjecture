/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.Basic
public import Other.Oka.Data.Fin.Tuple.Basic

/-!
# The ring of holomorphic functions on an open subset of `ℂ^ι`

## Main definitions

- `OkaAnalytic`: a function on an open set `U` of `ℂ^ι` is holomorphic if its extension by zero
  is analytic on `U`.
- `okaSubring` and `OkaRing`: the `ℂ`-algebra of holomorphic functions on `U`.
- `OkaRing.restrict`: restriction of holomorphic functions along an inclusion of opens.
- `TopologicalSpace.Opens.extend'`: the cylinder `U × ℂ` over an open set `U` of `ℂ^n`.

The interpretation `Polynomial.toOkaRing` of a polynomial over `OkaRing U` as a holomorphic
function on the cylinder over `U` is defined in `Other.Oka.Weierstrass`.
-/

@[expose] public section

/-- The `R`-linear form `x ↦ ∑ i, x i • f i` attached to a family `f` of elements of `R`. -/
noncomputable
abbrev linOfFun {R : Type*} [CommRing R]
    {ι : Type*} [Finite ι] (f : ι → R) :
    (ι → R) →ₗ[R] R :=
  Module.Basis.constr (S := R)
    (Pi.basisFun _ _) f

/-- The value of `linOfFun f` at a tuple `a`, as the sum `∑ i, a i * f i`.

Stated over an arbitrary commutative ring and with no consumer in this repository: it came here
with `linOfFun`, whose uses are in the statement of Oka's **bounded degree** lemma
(`Other/Oka/OkaLemma.lean`), plus one inside a proof in `Other/Oka/Statement.lean`. -/
lemma linOfFun_apply {A : Type*} [CommRing A] {n : ℕ} (f : Fin n → A) (a : Fin n → A) :
    linOfFun f a = ∑ i, a i * f i := by
  simp [linOfFun, Module.Basis.constr_apply_fintype, mul_comm]

open TopologicalSpace

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A function on an open set `U` of `ℂ^ι` is holomorphic if its extension by zero is
analytic on `U`. -/
def OkaAnalytic {U : Opens (ι → ℂ)} (f : U → ℂ) :
    Prop :=
  AnalyticOn ℂ (Function.extend Subtype.val f 0) U

omit [Fintype ι] [DecidableEq ι] in
lemma extend_mul_extend {U : Opens (ι → ℂ)} (f g : U → ℂ) :
    Function.extend Subtype.val (f * g) 0 =
      Function.extend Subtype.val f 0 * Function.extend Subtype.val g 0 := by
  funext x
  by_cases hx : ∃ a : U, (a : ι → ℂ) = x
  · obtain ⟨a, rfl⟩ := hx
    simp only [Pi.mul_apply, Subtype.val_injective.extend_apply]
  · simp [Function.extend_apply' _ _ _ hx]

omit [Fintype ι] [DecidableEq ι] in
lemma extend_add_extend {U : Opens (ι → ℂ)} (f g : U → ℂ) :
    Function.extend Subtype.val (f + g) 0 =
      Function.extend Subtype.val f 0 + Function.extend Subtype.val g 0 := by
  funext x
  by_cases hx : ∃ a : U, (a : ι → ℂ) = x
  · obtain ⟨a, rfl⟩ := hx
    simp only [Pi.add_apply, Subtype.val_injective.extend_apply]
  · simp [Function.extend_apply' _ _ _ hx]

omit [Fintype ι] [DecidableEq ι] in
lemma extend_const_eqOn {U : Opens (ι → ℂ)} (c : ℂ) :
    Set.EqOn (Function.extend Subtype.val (Function.const U c) 0)
      (Function.const (ι → ℂ) c) (U : Set (ι → ℂ)) := fun x hx ↦
  Subtype.val_injective.extend_apply (f := (Subtype.val : U → ι → ℂ)) _ _ ⟨x, hx⟩

/-- The `ℂ`-subalgebra of holomorphic functions inside all functions on `U`. -/
def okaSubring (U : Opens (ι → ℂ)) :
    Subalgebra ℂ (U → ℂ) where
  carrier := { f | OkaAnalytic f }
  mul_mem' {f g} hf hg := by
    rw [Set.mem_setOf_eq, OkaAnalytic, extend_mul_extend]
    exact AnalyticOn.mul hf hg
  one_mem' :=
    AnalyticOn.congr analyticOn_const (extend_const_eqOn 1)
  add_mem' {f g} hf hg := by
    rw [Set.mem_setOf_eq, OkaAnalytic, extend_add_extend]
    exact AnalyticOn.add hf hg
  zero_mem' :=
    AnalyticOn.congr analyticOn_const (extend_const_eqOn 0)
  algebraMap_mem' c :=
    AnalyticOn.congr analyticOn_const (extend_const_eqOn c)

/-- The `ℂ`-algebra of holomorphic functions on an open set `U` of `ℂ^ι`. -/
def OkaRing (U : Opens (ι → ℂ)) : Type _ :=
  okaSubring U

variable (U : Opens (ι → ℂ))

variable {U} in
/-- Bundle a holomorphic function on `U` as an element of `OkaRing U`. -/
def OkaRing.mk (f : U → ℂ) (hf : OkaAnalytic f) :
    OkaRing U :=
  ⟨_, hf⟩

-- instance : CoeFun (OkaRing U) U ℂ where

/-- The function underlying an element of `OkaRing U`. -/
def OkaRing.toFun (f : OkaRing U) :
    U → ℂ := f.val

/-- The extension by zero of `f : OkaRing U` to a function on all of `ℂ^ι`. -/
noncomputable
def OkaRing.toGlobalFun (f : OkaRing U) :
    (ι → ℂ) → ℂ :=
  Function.extend Subtype.val f.toFun 0

instance : CommRing (OkaRing U) :=
  inferInstanceAs <| CommRing (okaSubring U)

instance : Algebra ℂ (OkaRing U) :=
  inferInstanceAs <| Algebra ℂ (okaSubring U)

omit [DecidableEq ι] in
/-- The restriction of a holomorphic function along an inclusion of opens is holomorphic. -/
lemma OkaAnalytic.comp_inclusion {U V : Opens (ι → ℂ)} (h : U ≤ V) {f : V → ℂ}
    (hf : OkaAnalytic f) :
    OkaAnalytic (f ∘ U.inclusion h) := by
  refine (hf.mono h).congr fun x hx ↦ ?_
  have h₁ : Function.extend Subtype.val (f ∘ Opens.inclusion h) 0 x = f ⟨x, h hx⟩ :=
    Subtype.val_injective.extend_apply (f := (Subtype.val : U → ι → ℂ)) _ _ ⟨x, hx⟩
  have h₂ : Function.extend Subtype.val f 0 x = f ⟨x, h hx⟩ :=
    Subtype.val_injective.extend_apply (f := (Subtype.val : V → ι → ℂ)) _ _ ⟨x, h hx⟩
  rw [h₁, h₂]

/-- Restriction of holomorphic functions along an inclusion `U ≤ V` of open sets. -/
noncomputable
def OkaRing.restrict {U V : Opens (ι → ℂ)}
    (h : U ≤ V) :
    OkaRing V →ₐ[ℂ] OkaRing U where
  toFun f := .mk (f.toFun ∘ U.inclusion h) (OkaAnalytic.comp_inclusion h f.2)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The product of an open set of `X` and an open set of `Y`, as an open set of `X × Y`. -/
def TopologicalSpace.Opens.prod {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U : Opens X) (V : Opens Y) :
    Opens (X × Y) :=
  ⟨_, U.2.prod V.2⟩

/-- The cylinder `U × ℂ` over an open set `U` of `ℂ^n`, as an open set of `ℂ^{n + 1}`. -/
noncomputable
def TopologicalSpace.Opens.extend' (U : Opens (Fin n → ℂ)) :
    Opens (Fin (n + 1) → ℂ) :=
  let homeo : ((Fin n → ℂ) × ℂ) ≃ₜ (Fin (n + 1) → ℂ) :=
    .trans
      ((.prodCongr (.refl _) (.symm <|
          .piUnique fun _ : Fin 1 ↦ ℂ)))
      (Fin.appendHomeomorph n 1)
  Homeomorph.opensCongr homeo (Opens.prod U ⊤)

/-- A point of `ℂ^{n+1}` lies in the cylinder over `U` if and only if its first `n` coordinates
give a point of `U`. -/
@[simp]
lemma TopologicalSpace.Opens.mem_extend' {U : Opens (Fin n → ℂ)} {x : Fin (n + 1) → ℂ} :
    x ∈ U.extend' ↔ Fin.init x ∈ U :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, trivial⟩⟩

lemma TopologicalSpace.Opens.extend'_mono {U V : Opens (Fin n → ℂ)} (h : U ≤ V) :
    U.extend' ≤ V.extend' := by
  intro x hx
  rw [mem_extend'] at hx ⊢
  exact h hx

-- Not `@[simp]`: `mem_extend'` and `Fin.init_zero` are both `@[simp]` and prove this between
-- them, so the attribute here would only be a duplicate.
lemma TopologicalSpace.Opens.zero_mem_extend' {U : Opens (Fin n → ℂ)} :
    (0 : Fin (n + 1) → ℂ) ∈ U.extend' ↔ (0 : Fin n → ℂ) ∈ U := by
  rw [mem_extend']
  exact Iff.of_eq (congrArg (· ∈ U) (funext fun i ↦ rfl))

end
