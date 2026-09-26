/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
public import Other.Oka.AnalyticSpace.LocalModel
public import Other.Oka.AnalyticSpace.OpenSubspace
public import Other.Oka.MaximalIdeal
public import Other.Oka.RingTheory.LocalRing.ResidueField.Basic

/-!
# The residue fields of a complex analytic space, and the value of a section at a point

A section of the structure sheaf of a scheme has no values in a fixed field: the residue field
varies from point to point. For a complex analytic space it does not ; every residue field is
`ℂ` ; and a section over `U` therefore really is a function on `U`, in the same sense in which a
section of `𝒪_{ℂ^n}` is a holomorphic function. This file constructs that function.

Precisely: for `Z` a complex analytic space and `z : Z`, the stalk `𝒪_{Z,z}` is a local
`ℂ`-algebra in which every element differs from a unique constant by an element of the maximal
ideal (`ComplexAnalytic.AnalyticSpace.existsUnique_sub_stalkAlgMap_mem_maximalIdeal`). That
constant is the value, `ComplexAnalytic.AnalyticSpace.evalStalk`, and composing with the germ
map gives the value of a section over an open neighbourhood,
`ComplexAnalytic.AnalyticSpace.eval`.

## Where the statement lives, and why it is stated for `AnalyticSpace`

The ring-theoretic half is general and lives in the mirror tree, as
`IsLocalRing.IsCoefficientField` in `Other/Oka/RingTheory/LocalRing/ResidueField/Basic.lean`: a
homomorphism from a field into a local ring realising the residue field. Everything about
uniqueness, about the induced `S →+* K`, and about transporting the property along a surjection
is proved there, of an arbitrary field and an arbitrary local ring.

What is *not* general is that the stalks of an analytic space have this property, and that is
what this file proves. It is stated for `ComplexAnalytic.AnalyticSpace` rather than for a
locally ringed space with a `ℂ`-algebra structure because the proof is the existence of a chart:
there is no weaker hypothesis on a locally ringed space under which it is true. The intermediate
results are stated at the level of generality at which they hold ; `LocalOkaRing ι`, then a
stalk of `𝒪_{ℂ^ι}`, then a stalk of an open subspace of `ℂ^n`, then an analytic space ; each
obtained from the previous by `IsLocalRing.IsCoefficientField.of_surjective`.

## The chain of transports

`LocalOkaRing.mem_maximalIdeal_iff` says that a convergent power series is a non-unit exactly
when its constant term vanishes, which is the base case. From there:

* `okaStalkEquiv` (Taylor expansion) carries it to the stalks of `𝒪_{ℂ^ι}`;
* `AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso` carries it to the stalks of an open
  subspace of `ℂ^n`;
* `ComplexAnalytic.IsCutOutBy.surjective_stalkMap` carries it across a chart, this being the one
  step which is a genuine surjection rather than an isomorphism, and
  `ComplexAnalytic.IsCLinearHom.stalkAlgMap` is what makes it compatible with the constants ;
  the `ℂ`-linearity of charts exists for exactly this;
* `restrictStalkIso` again carries it from the chart domain to `Z`.

Each step also carries the *value*, by `IsLocalRing.IsCoefficientField.evalHom_map`, which is
what makes `ComplexAnalytic.AnalyticSpace.eval` computable rather than merely well defined; see
`ComplexAnalytic.eval_ofCutOut` and the node below.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.stalkAlgMap`: the constants, as a map `ℂ →+* 𝒪_{Z,z}`.
- `ComplexAnalytic.AnalyticSpace.evalStalk`: the value at `z` of a germ.
- `ComplexAnalytic.AnalyticSpace.eval`: the value at `z` of a section over an open set
  containing `z`.
- `ComplexAnalytic.AnalyticSpace.residueFieldEquiv`: the residue field at `z`, identified
  with `ℂ`.
- `ComplexAnalytic.nodeCoord`: the coordinate functions of `ℂ²`, restricted to the node.

## Main results

- `ComplexAnalytic.AnalyticSpace.existsUnique_sub_stalkAlgMap_mem_maximalIdeal`: **the residue
  field of a complex analytic space at a point is `ℂ`.**
- `ComplexAnalytic.AnalyticSpace.evalStalk_eq_zero_iff` and
  `ComplexAnalytic.AnalyticSpace.evalStalk_ne_zero_iff_isUnit`: a germ vanishes at the point
  exactly when it lies in the maximal ideal, and is a unit exactly when it does not.
- `ComplexAnalytic.AnalyticSpace.evalStalk_eq_iff`: the value of a germ is `c` exactly when the
  germ differs from the constant `c` by one vanishing at the point. This characterises the value
  without reference to the construction, and is what a computation of a value should go through.
- `ComplexAnalytic.eval_complexAffineSpace`: on `ℂ^n` itself the value of a global section is
  its value as a holomorphic function.
- `ComplexAnalytic.eval_restrict_complexAffineSpace`: the same on an **open** subspace `ℂ^n|V`.
- `ComplexAnalytic.eval_ofCutOut`: on an analytic subspace of `V ⊆ ℂ^n`, the value of the
  restriction of a holomorphic function is the value of that function.
- `ComplexAnalytic.eval_nodeCoord`, `ComplexAnalytic.nodeCoord_mul` and
  `ComplexAnalytic.nodeCoord_ne_zero`: on the node, the coordinate functions take the expected
  values, and their product vanishes while neither does ; so `Γ(node, 𝒪)` has zero divisors.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry IsLocalRing

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic

section LocalOkaRing

variable {ι : Type u} [Finite ι]

/-- **`ℂ` is a coefficient field of the ring of convergent power series**: a germ at the origin
differs from its constant term by a germ vanishing at the origin. -/
theorem isCoefficientField_algebraMap_localOkaRing :
    IsCoefficientField (algebraMap ℂ (LocalOkaRing ι)) := fun P ↦
  ⟨LocalOkaRing.constantCoeff P, by
    rw [LocalOkaRing.mem_maximalIdeal_iff, map_sub, LocalOkaRing.constantCoeff_algebraMap,
      sub_self]⟩

@[simp]
lemma evalHom_isCoefficientField_algebraMap_localOkaRing (P : LocalOkaRing ι) :
    isCoefficientField_algebraMap_localOkaRing.evalHom P = LocalOkaRing.constantCoeff P :=
  ((isCoefficientField_algebraMap_localOkaRing.existsUnique_sub_mem_maximalIdeal P).unique
    (isCoefficientField_algebraMap_localOkaRing.sub_evalHom_mem P)
    (by rw [LocalOkaRing.mem_maximalIdeal_iff, map_sub,
      LocalOkaRing.constantCoeff_algebraMap, sub_self]))

end LocalOkaRing

section ComplexSpace

variable {ι : Type u} [Fintype ι]

/-- **`ℂ` is a coefficient field of every stalk of `𝒪_{ℂ^ι}`**, the constants being the germs of
the constant functions on a neighbourhood `U` of the point.

This is `isCoefficientField_algebraMap_localOkaRing` transported along the Taylor expansion
isomorphism `okaStalkEquiv`. -/
theorem isCoefficientField_germ_algebraMap {U : Opens (ι → ℂ)} {y : ι → ℂ} (hy : y ∈ U) :
    IsCoefficientField
      (((okaCommPresheaf ι).germ U y hy).hom.comp (algebraMap ℂ (OkaRing U))) :=
  isCoefficientField_algebraMap_localOkaRing.of_surjective
    (f := (okaStalkEquiv y).symm.toRingHom) (okaStalkEquiv y).symm.surjective fun c ↦
      (okaStalkEquiv y).symm_apply_eq.2 (okaStalkEquiv_germ_algebraMap hy c).symm

@[simp]
lemma evalHom_isCoefficientField_germ_algebraMap {U : Opens (ι → ℂ)} {y : ι → ℂ} (hy : y ∈ U)
    (g : OkaRing U) :
    (isCoefficientField_germ_algebraMap hy).evalHom ((okaCommPresheaf ι).germ U y hy g) =
      OkaRing.evalHom hy g := by
  have h := isCoefficientField_algebraMap_localOkaRing.evalHom_map
    (f := (okaStalkEquiv y).symm.toRingHom) (okaStalkEquiv y).symm.surjective
    (β := ((okaCommPresheaf ι).germ U y hy).hom.comp (algebraMap ℂ (OkaRing U)))
    (fun c ↦ (okaStalkEquiv y).symm_apply_eq.2 (okaStalkEquiv_germ_algebraMap hy c).symm)
    (okaStalkEquiv y ((okaCommPresheaf ι).germ U y hy g))
  rw [show (okaStalkEquiv y).symm.toRingHom
      (okaStalkEquiv y ((okaCommPresheaf ι).germ U y hy g)) =
        (okaCommPresheaf ι).germ U y hy g from (okaStalkEquiv y).symm_apply_apply _] at h
  rw [h, evalHom_isCoefficientField_algebraMap_localOkaRing,
    constantCoeff_okaStalkEquiv_germ]

end ComplexSpace

section OpenSubspaceOfComplexSpace

variable (n : ℕ) (V : Opens (complexAffineSpace.{u} n))

/-- **`ℂ` is a coefficient field of every stalk of an open subspace of `ℂ^n`**, the constants
being `ComplexAnalytic.constantsAlgMap`.

The stalks of the open subspace are the stalks of `ℂ^n`
(`AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso`), compatibly with the constants. -/
theorem isCoefficientField_stalkAlgMap_constantsAlgMap
    (w : (complexAffineSpace.{u} n).restrict V.isOpenEmbedding) :
    IsCoefficientField
      (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).stalkAlgMap
        (constantsAlgMap n V) w) :=
  (isCoefficientField_germ_algebraMap (U := V.isOpenEmbedding.isOpenMap.functor.obj ⊤)
      (y := w.1) ⟨w, trivial, rfl⟩).of_surjective
    (f := ((complexAffineSpace.{u} n).restrictStalkIso V.isOpenEmbedding w).inv.hom)
    (ConcreteCategory.bijective_of_isIso _).surjective
    fun _ ↦ LocallyRingedSpace.restrictStalkIso_inv_eq_germ_apply _ _ ⊤ w trivial _

@[simp]
lemma evalHom_isCoefficientField_stalkAlgMap_constantsAlgMap
    (w : (complexAffineSpace.{u} n).restrict V.isOpenEmbedding)
    (g : ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤)) :
    (isCoefficientField_stalkAlgMap_constantsAlgMap n V w).evalHom
        (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.Γgerm w g) =
      OkaRing.evalHom (U := V.isOpenEmbedding.isOpenMap.functor.obj ⊤) ⟨w, trivial, rfl⟩ g := by
  have hg : ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.Γgerm w g =
      ((complexAffineSpace.{u} n).restrictStalkIso V.isOpenEmbedding w).inv
        ((complexAffineSpace.{u} n).presheaf.germ
          (V.isOpenEmbedding.isOpenMap.functor.obj ⊤) w.1 ⟨w, trivial, rfl⟩ g) :=
    (LocallyRingedSpace.restrictStalkIso_inv_eq_germ_apply _ V.isOpenEmbedding ⊤ w trivial g).symm
  refine (congrArg (isCoefficientField_stalkAlgMap_constantsAlgMap n V w).evalHom hg).trans ?_
  refine Eq.trans ((isCoefficientField_germ_algebraMap
    (U := V.isOpenEmbedding.isOpenMap.functor.obj ⊤) (y := w.1) ⟨w, trivial, rfl⟩).evalHom_map
    (f := ((complexAffineSpace.{u} n).restrictStalkIso V.isOpenEmbedding w).inv.hom)
    (ConcreteCategory.bijective_of_isIso _).surjective
    (fun _ ↦ LocallyRingedSpace.restrictStalkIso_inv_eq_germ_apply _ _ ⊤ w trivial _) _) ?_
  exact evalHom_isCoefficientField_germ_algebraMap _ g

end OpenSubspaceOfComplexSpace

namespace AnalyticSpace

variable (Z : AnalyticSpace.{u})

/-- The `ℂ`-algebra structure on the stalk of `𝒪_Z` at a point: the germ there of the constant
sections. -/
def stalkAlgMap (z : Z) : ℂ →+* Z.presheaf.stalk z :=
  Z.toLocallyRingedSpace.stalkAlgMap Z.algebraMap z

/-- **The residue field of a complex analytic space at a point is `ℂ`**, in the strong form that
the constants realise it: every germ at `z` differs from a unique constant by a germ vanishing
at `z`.

The proof transports the corresponding statement for `ℂ^n` along a chart. Of the three maps
involved ; the identification of the stalks of `Z` with those of the chart domain, the map on
stalks of the closed immersion cutting the chart out, and the identification of the stalks of an
open subset of `ℂ^n` with those of `ℂ^n` ; the first and last are isomorphisms and the middle
one is surjective by `ComplexAnalytic.IsCutOutBy.surjective_stalkMap`, so all three are covered
by `IsLocalRing.IsCoefficientField.of_surjective`. The compatibility with the constants is
`ComplexAnalytic.IsCLinearHom.stalkAlgMap` for the middle map ; this is what the `ℂ`-linearity
of charts is for ; and
`AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso_hom_stalkAlgMap` for the outer two. -/
theorem isCoefficientField_stalkAlgMap (z : Z) : IsCoefficientField (Z.stalkAlgMap z) := by
  obtain ⟨U, n, k, V, i, f, hcut, hlin⟩ := Z.local_model z
  exact ((isCoefficientField_stalkAlgMap_constantsAlgMap n V (i.base ⟨z, U.2⟩)).of_surjective
    (hcut.surjective_stalkMap ⟨z, U.2⟩) (hlin.stalkAlgMap ⟨z, U.2⟩)).of_surjective
    (f := (Z.toLocallyRingedSpace.restrictStalkIso U.1.isOpenEmbedding ⟨z, U.2⟩).hom.hom)
    (ConcreteCategory.bijective_of_isIso _).surjective
    fun _ ↦ LocallyRingedSpace.restrictStalkIso_hom_stalkAlgMap _ _ _ ⟨z, U.2⟩ _

/-- **The value at `z` of a germ of the structure sheaf**, an element of `ℂ`.

A germ is a unit exactly when its value is nonzero (`AnalyticSpace.evalStalk_eq_zero_iff`), and
the value of a constant is that constant (`AnalyticSpace.evalStalk_stalkAlgMap`); these two
properties determine it. -/
def evalStalk (z : Z) : Z.presheaf.stalk z →+* ℂ :=
  (Z.isCoefficientField_stalkAlgMap z).evalHom

/-- **The value at `z` of a section of `𝒪_Z` over an open neighbourhood `U` of `z`.**

This is what makes a section of the structure sheaf of an analytic space a function on `U`,
though ; as for a scheme ; a nilpotent section is a nonzero section all of whose values
vanish. -/
def eval {U : Opens Z} (z : Z) (hz : z ∈ U) : Z.presheaf.obj (op U) →+* ℂ :=
  (Z.evalStalk z).comp (Z.presheaf.germ U z hz).hom

lemma eval_apply {U : Opens Z} (z : Z) (hz : z ∈ U) (s : Z.presheaf.obj (op U)) :
    Z.eval z hz s = Z.evalStalk z (Z.presheaf.germ U z hz s) :=
  rfl

@[simp]
lemma evalStalk_stalkAlgMap (z : Z) (c : ℂ) : Z.evalStalk z (Z.stalkAlgMap z c) = c :=
  (Z.isCoefficientField_stalkAlgMap z).evalHom_const c

@[simp]
lemma evalStalk_eq_zero_iff {z : Z} {a : Z.presheaf.stalk z} :
    Z.evalStalk z a = 0 ↔ a ∈ maximalIdeal (Z.presheaf.stalk z) :=
  (Z.isCoefficientField_stalkAlgMap z).evalHom_eq_zero_iff

/-- **The value of a germ is characterised by the maximal ideal**: `c` is the value of `a` at
`z` exactly when `a` differs from the constant `c` by a germ vanishing at `z`.

This is the form to use whenever a value has to be *computed*, because it turns an equation
between complex numbers into a membership in `𝔪_z`, and that transports along any local
homomorphism ; in particular along the stalk maps of a chart, which is how
`ComplexAnalytic.evalStalk_chart` computes values without touching the chain of transports that
defines `evalStalk`. -/
lemma evalStalk_eq_iff {z : Z} (a : Z.presheaf.stalk z) (c : ℂ) :
    Z.evalStalk z a = c ↔ a - Z.stalkAlgMap z c ∈ maximalIdeal (Z.presheaf.stalk z) :=
  (Z.isCoefficientField_stalkAlgMap z).evalHom_eq_iff

lemma evalStalk_ne_zero_iff_isUnit {z : Z} {a : Z.presheaf.stalk z} :
    Z.evalStalk z a ≠ 0 ↔ IsUnit a := by
  rw [ne_eq, evalStalk_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, not_not]

lemma sub_stalkAlgMap_evalStalk_mem (z : Z) (a : Z.presheaf.stalk z) :
    a - Z.stalkAlgMap z (Z.evalStalk z a) ∈ maximalIdeal (Z.presheaf.stalk z) :=
  (Z.isCoefficientField_stalkAlgMap z).sub_evalHom_mem a

/-- **Every germ differs from a unique constant by a germ vanishing at the point**, which is the
statement that the residue field of `Z` at `z` is `ℂ`. -/
theorem existsUnique_sub_stalkAlgMap_mem_maximalIdeal (z : Z) (a : Z.presheaf.stalk z) :
    ∃! c : ℂ, a - Z.stalkAlgMap z c ∈ maximalIdeal (Z.presheaf.stalk z) :=
  (Z.isCoefficientField_stalkAlgMap z).existsUnique_sub_mem_maximalIdeal a

@[simp]
lemma eval_eq_zero_iff {U : Opens Z} {z : Z} {hz : z ∈ U} {s : Z.presheaf.obj (op U)} :
    Z.eval z hz s = 0 ↔ Z.presheaf.germ U z hz s ∈ maximalIdeal (Z.presheaf.stalk z) :=
  Z.evalStalk_eq_zero_iff

@[simp]
lemma eval_algebraMap (z : Z) (c : ℂ) :
    Z.eval z (U := ⊤) trivial (Z.algebraMap c) = c :=
  Z.evalStalk_stalkAlgMap z c

/-- **Evaluation is natural in the space**: the value at `z` of the pullback of a germ is the
value of that germ at `i z`.

Stated for a morphism of the underlying locally ringed spaces together with `ℂ`-linearity rather
than for a `ComplexAnalytic.AnalyticSpace.Hom`, because that is the form the development can
currently instantiate ; a closed immersion cutting out a chart is `ℂ`-linear and is a morphism
of locally ringed spaces, but is not packaged as a morphism of analytic spaces.
`ComplexAnalytic.AnalyticSpace.evalStalk_stalkMap_hom` is the corollary for an honest
morphism.

This is *not* an instance of `IsLocalRing.IsCoefficientField.evalHom_map`, which requires the map
to be surjective; `i.stalkMap` is not. Surjectivity is not what makes it work. Write the germ as
a constant plus an element of the maximal ideal
(`ComplexAnalytic.AnalyticSpace.evalStalk_eq_iff`); the constant is carried to the constant by
`ℂ`-linearity (`ComplexAnalytic.IsCLinearHom.stalkAlgMap`), and the rest stays in the maximal
ideal because `i.stalkMap` is a **local** homomorphism, which is part of being a morphism of
locally ringed spaces. Locality does here what surjectivity does there. -/
theorem evalStalk_stalkMap {Z W : AnalyticSpace.{u}}
    (i : Z.toLocallyRingedSpace ⟶ W.toLocallyRingedSpace)
    (hlin : IsCLinearHom i Z.algebraMap W.algebraMap) (z : Z)
    (a : W.presheaf.stalk (i.base z)) :
    Z.evalStalk z ((i.stalkMap z).hom a) = W.evalStalk (i.base z) a := by
  haveI : IsLocalHom (i.stalkMap z).hom := i.prop z
  refine (Z.evalStalk_eq_iff _ _).2 ?_
  have h : a - W.stalkAlgMap (i.base z) (W.evalStalk (i.base z) a) ∈
      maximalIdeal (W.presheaf.stalk (i.base z)) :=
    (W.evalStalk_eq_iff a _).1 rfl
  have hlin' : (i.stalkMap z).hom
      (W.stalkAlgMap (i.base z) (W.evalStalk (i.base z) a)) =
      Z.stalkAlgMap z (W.evalStalk (i.base z) a) :=
    hlin.stalkAlgMap z _
  have hmap := _root_.map_nonunit (i.stalkMap z).hom _ h
  rwa [map_sub, hlin'] at hmap

/-- **The value at `z` of the pullback of a section is the value of that section at `i z`.**

`ComplexAnalytic.AnalyticSpace.evalStalk_stalkMap` at the level of sections. This is what says
that the underlying map of a `ℂ`-linear morphism is determined by the values of the pullbacks:
applied to a coordinate function it computes `i.base z`. -/
theorem eval_c_app {Z W : AnalyticSpace.{u}}
    (i : Z.toLocallyRingedSpace ⟶ W.toLocallyRingedSpace)
    (hlin : IsCLinearHom i Z.algebraMap W.algebraMap) {U : Opens W} (z : Z)
    (hz : i.base z ∈ U) (s : W.presheaf.obj (op U)) :
    Z.eval z (show z ∈ (Opens.map i.base).obj U from hz) (i.c.app (op U) s) =
      W.eval (i.base z) hz s :=
  (congrArg (Z.evalStalk z)
    (LocallyRingedSpace.stalkMap_germ_apply i U z hz s).symm).trans
    (evalStalk_stalkMap i hlin z _)

/-- `ComplexAnalytic.AnalyticSpace.evalStalk_stalkMap` for a morphism of complex analytic
spaces. -/
theorem evalStalk_stalkMap_hom {Z W : AnalyticSpace.{u}} (φ : Z ⟶ W) (z : Z)
    (a : W.presheaf.stalk (φ.toLRSHom.base z)) :
    Z.evalStalk z ((φ.toLRSHom.stalkMap z).hom a) = W.evalStalk (φ.toLRSHom.base z) a :=
  evalStalk_stalkMap φ.toLRSHom φ.isCLinear z a

/-- **The residue field of a complex analytic space at a point, identified with `ℂ`.**

`AlgebraicGeometry.LocallyRingedSpace.residueField` is Mathlib's residue field of the stalk;
`AnalyticSpace.eval` is `AlgebraicGeometry.LocallyRingedSpace.evaluation` read through this
isomorphism (`AnalyticSpace.eval_eq_residueFieldEquiv_evaluation`). -/
def residueFieldEquiv (z : Z) : ResidueField (Z.presheaf.stalk z) ≃+* ℂ :=
  (Z.isCoefficientField_stalkAlgMap z).residueFieldEquiv

lemma eval_eq_residueFieldEquiv_evaluation {U : Opens Z} (z : Z) (hz : z ∈ U)
    (s : Z.presheaf.obj (op U)) :
    Z.eval z hz s =
      Z.residueFieldEquiv z (Z.toLocallyRingedSpace.evaluation ⟨z, hz⟩ s) :=
  rfl

end AnalyticSpace

section ComplexAffineSpace

variable {n : ℕ} (y : AnalyticSpace.complexAffineSpace.{u} n)
  (s : (AnalyticSpace.complexAffineSpace.{u} n).presheaf.obj (op ⊤))

/-- **On `ℂ^n` the value of a global section is its value as a holomorphic function.**

`ComplexAnalytic.AnalyticSpace.evalStalk` is defined through a chart and a chain of transports,
so it is not computed by unfolding. It is computed from its *characterisation*
(`ComplexAnalytic.AnalyticSpace.evalStalk_eq_iff`): the value is `c` exactly when the germ
differs from the constant `c` by a germ vanishing at the point, and on `ℂ^n` a germ vanishes at
the point exactly when the function does (`germ_mem_maximalIdeal_iff`).

The two `rw`s below are the only ones the proof can afford. A point of
`ComplexAnalytic.AnalyticSpace.complexAffineSpace n` and a point of `ULift (Fin n) → ℂ` are the
same thing at default transparency but not at the `instances` transparency `rw` and `simp` use,
so every step that crosses that seam has to be a term. -/
theorem eval_complexAffineSpace :
    (AnalyticSpace.complexAffineSpace.{u} n).eval (U := ⊤) y trivial s =
      OkaRing.evalHom (U := (⊤ : Opens (ULift.{u} (Fin n) → ℂ))) (x := y) trivial s := by
  set c := OkaRing.evalHom (U := (⊤ : Opens (ULift.{u} (Fin n) → ℂ))) (x := y) trivial s with hc
  refine ((AnalyticSpace.complexAffineSpace.{u} n).evalStalk_eq_iff _ _).2 ?_
  rw [AnalyticSpace.stalkAlgMap, LocallyRingedSpace.stalkAlgMap_apply,
    show ((AnalyticSpace.complexAffineSpace.{u} n).presheaf.germ ⊤ y trivial).hom s -
          ((AnalyticSpace.complexAffineSpace.{u} n).presheaf.germ ⊤ y trivial).hom
            ((AnalyticSpace.complexAffineSpace.{u} n).algebraMap c) =
        ((AnalyticSpace.complexAffineSpace.{u} n).presheaf.germ ⊤ y trivial).hom
          (s - (AnalyticSpace.complexAffineSpace.{u} n).algebraMap c) from (map_sub _ _ _).symm]
  exact (germ_mem_maximalIdeal_iff (ι := ULift.{u} (Fin n)) (y := y) (U := ⊤) trivial _).2
    ((map_sub (OkaRing.evalHom (U := (⊤ : Opens (ULift.{u} (Fin n) → ℂ))) (x := y) trivial)
        s _).trans
      (sub_eq_zero.2 (hc.trans (OkaRing.evalHom_algebraMap (U := ⊤) trivial c).symm)))

end ComplexAffineSpace

section Restrict

variable {n : ℕ} (V : Opens (complexAffineSpace.{u} n))

/-- **On an open subspace `ℂ^n|V`, the value of a global section is `OkaRing.evalHom`.**

The third of this file's three computation rules, beside
`ComplexAnalytic.eval_complexAffineSpace` for `ℂ^n` itself and `ComplexAnalytic.eval_ofCutOut`
for a cut-out subspace. It is what makes a base-map computation on `ℂ^n|V` checkable by a route
other than unfolding the construction.

**It is one line, and the reason is worth stating because it is not visible from the
statement.** `(AnalyticSpace.restrict (complexAffineSpace n) V).algebraMap` is *definitionally*
`constantsAlgMap n V` ; `AnalyticSpace.restrict_algebraMap` gives `resAlgMap`, and
`ComplexAnalytic.constantsAlgMap_eq_resAlgMap` is `rfl` ; so the coefficient field
`AnalyticSpace.evalStalk` uses and the one
`ComplexAnalytic.isCoefficientField_stalkAlgMap_constantsAlgMap` provides are the *same* one,
and `IsLocalRing.IsCoefficientField.evalHom` agrees on the nose with no transport.

The point of the section is indexed by `V.isOpenEmbedding.isOpenMap.functor.obj ⊤` rather than
by `V`: those two opens have the same points and are not definitionally equal, which is why the
witness is `⟨w, trivial, rfl⟩` rather than `w.2`. -/
theorem eval_restrict_complexAffineSpace
    (w : ((AnalyticSpace.complexAffineSpace.{u} n).restrict V))
    (g : ((AnalyticSpace.complexAffineSpace.{u} n).restrict V).presheaf.obj (op ⊤)) :
    ((AnalyticSpace.complexAffineSpace.{u} n).restrict V).eval (U := ⊤) w trivial g =
      OkaRing.evalHom (U := V.isOpenEmbedding.isOpenMap.functor.obj ⊤) ⟨w, trivial, rfl⟩ g :=
  evalHom_isCoefficientField_stalkAlgMap_constantsAlgMap n V w g

end Restrict

section OfCutOut

variable {n k : ℕ} {V : Opens (complexAffineSpace.{u} n)} {Z : LocallyRingedSpace.{u}}
  {i : Z ⟶ (complexAffineSpace.{u} n).restrict V.isOpenEmbedding}
  {f : Fin k → ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤)}

/-- **On a space cut out inside an open subset of `ℂ^n`, evaluation is evaluation upstairs.**

The `ℂ`-algebra structure of `ComplexAnalytic.AnalyticSpace.ofCutOut` is by definition the
pullback of the constants, so the closed immersion is tautologically `ℂ`-linear and
`IsLocalRing.IsCoefficientField.evalHom_map` applies. -/
theorem evalStalk_ofCutOut (hcut : IsCutOutBy i f) (z : Z)
    (a : ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.stalk (i.base z)) :
    (AnalyticSpace.ofCutOut hcut).evalStalk z ((i.stalkMap z).hom a) =
      (isCoefficientField_stalkAlgMap_constantsAlgMap n V (i.base z)).evalHom a :=
  (isCoefficientField_stalkAlgMap_constantsAlgMap n V (i.base z)).evalHom_map
    (hcut.surjective_stalkMap z)
    (β := (AnalyticSpace.ofCutOut hcut).stalkAlgMap z)
    (IsCLinearHom.stalkAlgMap (fun _ ↦ rfl) z) a

/-- **The value of the pullback of a holomorphic function is its value upstairs.**

This is what makes the evaluation of `ComplexAnalytic.AnalyticSpace.eval` computable, and the
reason it deserves the name: on the analytic subspace of `V ⊆ ℂ^n` cut out by the `f j`, the
section obtained by restricting a holomorphic function `g` on `V` takes at a point the value
`g` takes there. -/
theorem eval_ofCutOut (hcut : IsCutOutBy i f) (z : Z)
    (g : ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤)) :
    (AnalyticSpace.ofCutOut hcut).eval (U := ⊤) z trivial
        ((LocallyRingedSpace.Γ.map i.op).hom g) =
      OkaRing.evalHom (U := V.isOpenEmbedding.isOpenMap.functor.obj ⊤)
        ⟨i.base z, trivial, rfl⟩ g := by
  have hg : (AnalyticSpace.ofCutOut hcut).presheaf.germ ⊤ z trivial
        ((LocallyRingedSpace.Γ.map i.op).hom g) =
      (i.stalkMap z).hom
        (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.Γgerm (i.base z) g) :=
    (LocallyRingedSpace.stalkMap_germ_apply i ⊤ z trivial g).symm
  refine Eq.trans (congrArg ((AnalyticSpace.ofCutOut hcut).evalStalk z) hg) ?_
  exact (evalStalk_ofCutOut hcut z _).trans
    (evalHom_isCoefficientField_stalkAlgMap_constantsAlgMap n V (i.base z) g)

end OfCutOut

section Node

/-- The `j`-th coordinate function `z_j` of `ℂ²`, restricted to the node: a global section of
the structure sheaf of `ComplexAnalytic.AnalyticSpace.node`. -/
def nodeCoord (j : ULift.{u} (Fin 2)) : (AnalyticSpace.node.{u}).presheaf.obj (op ⊤) :=
  (LocallyRingedSpace.Γ.map (nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u}).op).hom
    (OkaRing.ofMvPolynomial _ (MvPolynomial.X j))

/-- **A coordinate function on the node takes at a point of the node the value of that
coordinate.**

This is the non-vacuity check for `ComplexAnalytic.AnalyticSpace.eval`: on a space which is not
`ℂ^n`, the evaluation map is not merely well defined but computes the expected number. -/
@[simp]
theorem eval_nodeCoord (p : AnalyticSpace.node.{u}) (j : ULift.{u} (Fin 2)) :
    (AnalyticSpace.node.{u}).eval (U := ⊤) p trivial (nodeCoord.{u} j) = p.1.1 j :=
  (eval_ofCutOut (nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}) p _).trans
    (MvPolynomial.eval_X j)

/-- **The two coordinate functions on the node multiply to zero**, since the node is cut out by
`z₀ z₁`. -/
theorem nodeCoord_mul :
    nodeCoord.{u} (ULift.up 0) * nodeCoord.{u} (ULift.up 1) = 0 := by
  refine Eq.trans ?_
    ((nodeAmbient.{u}.isCutOutBy_zeroLocusSubspaceι nodeSection.{u}).c_app_eq_zero 0)
  exact (map_mul (LocallyRingedSpace.Γ.map
    (nodeAmbient.{u}.zeroLocusSubspaceι nodeSection.{u}).op).hom _ _).symm.trans
      (congrArg _ (map_mul (OkaRing.ofMvPolynomial _) _ _).symm)

/-- **Neither coordinate function on the node is zero.**

With `ComplexAnalytic.nodeCoord_mul` this says that the ring of global sections of the node has
zero divisors: the node is reducible, being the union of the two axes. The point exhibited is
the one with `j`-th coordinate `1` and the other coordinate `0`, which lies on the node. -/
theorem nodeCoord_ne_zero (j : ULift.{u} (Fin 2)) : nodeCoord.{u} j ≠ 0 := by
  classical
  have hne : (ULift.up 0 : ULift.{u} (Fin 2)) ≠ ULift.up 1 := fun hcon ↦ by
    simpa using congrArg ULift.down hcon
  obtain ⟨x, hxj, hx0⟩ : ∃ x : ULift.{u} (Fin 2) → ℂ,
      x j = 1 ∧ x (ULift.up 0) * x (ULift.up 1) = 0 := by
    refine ⟨fun l ↦ if l = j then 1 else 0, by simp, ?_⟩
    dsimp only
    rcases eq_or_ne (ULift.up 0 : ULift.{u} (Fin 2)) j with h | h
    · rw [if_neg (fun hcon : (ULift.up 1 : ULift.{u} (Fin 2)) = j ↦ hne (h.trans hcon.symm)),
        mul_zero]
    · rw [if_neg h, zero_mul]
  intro hzero
  have h1 := eval_nodeCoord (⟨⟨x, trivial⟩, (mem_zeroLocus_nodeSection_iff _).2 hx0⟩ :
    AnalyticSpace.node.{u}) j
  rw [hzero, map_zero] at h1
  exact zero_ne_one (h1.trans hxj)

end Node

end ComplexAnalytic

end
