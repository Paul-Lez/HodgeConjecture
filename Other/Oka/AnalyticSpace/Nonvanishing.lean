/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.Evaluation
public import Other.Oka.AnalyticSpace.OpenSubspace
public import Other.Oka.Geometry.RingedSpace.Basic

/-!
# The non-vanishing locus of a section, and mapping into an open subspace

Two halves of one piece of API. `Other/Oka/AnalyticSpace/OpenSubspace.lean` builds the open subspace
`X|U` of a complex analytic space and its inclusion `X|U ⟶ X`; this file adds the two things one
needs in order to *use* `X|U` as a target:

* **where to get the open subset from** ; the locus on which a global section of `𝒪_X` does not
  vanish, `ComplexAnalytic.AnalyticSpace.nonvanishing`, on which that section becomes a unit;
* **how to map into it** ; a morphism `Z ⟶ X` whose image lies in `U` factors uniquely through
  `X|U`, `ComplexAnalytic.AnalyticSpace.liftOpen`.

Together they are the shape in which a localisation `A_f` of a finitely generated `ℂ`-algebra
meets the analytic side: the analytification of `A_f` maps to `X^an` because `f` is invertible
upstairs, and it maps to the *open subspace* `D(f)` because that invertibility is exactly the
statement that the image misses the zeros of `f`.

## Nothing here is a new construction

**The non-vanishing locus is Mathlib's `AlgebraicGeometry.RingedSpace.basicOpen` at `U = ⊤`**, and
`nonvanishing` is a name for it, not a definition of it. Openness, the fact that the section is a
unit after restriction, and the behaviour under products are all Mathlib's; what this file adds is
the translation into the evaluation API of `Other/Oka/AnalyticSpace/Evaluation.lean`, i.e. the statement
that a point lies in it exactly when the *value* of the section there is nonzero. That is the form
every consumer wants, and it is the one form Mathlib cannot state, because the residue field of a
locally ringed space is not `ℂ`.

Likewise `liftOpen` is `AlgebraicGeometry.LocallyRingedSpace.liftRestrict` ; itself Mathlib's
`IsOpenImmersion.lift` at `ofRestrict` ; together with the `ℂ`-linearity of the factorisation, and
that is `ComplexAnalytic.IsCLinearHom.of_comp` applied to the factorisation itself: both algebra
structures are the ambient one restricted, so no transport along anything is needed. This is the
same three-line argument `ComplexAnalytic.AnalyticSpace.restrictLE` is built from.

## Main definitions

- `ComplexAnalytic.AnalyticSpace.nonvanishing`: **the open subset on which a global section of
  `𝒪_X` does not vanish.**
- `ComplexAnalytic.AnalyticSpace.liftOpen`: **the factorisation of a morphism through an open
  subspace containing its image.**

## Main results

- `ComplexAnalytic.AnalyticSpace.mem_nonvanishing_iff`: **a point lies in the non-vanishing locus
  of `a` exactly when the value of `a` there is nonzero.**
- `ComplexAnalytic.AnalyticSpace.nonvanishing_pullbackΓ`: **the non-vanishing locus of a
  pulled-back section is the preimage of the non-vanishing locus** ; the only statement here
  about two spaces, and what lets a distinguished open be pulled back along a morphism.
- `ComplexAnalytic.AnalyticSpace.isUnit_resΓ_of_le_nonvanishing`: **a section is invertible on
  every open subspace contained in its non-vanishing locus.** The hypothesis is `≤` rather than
  equality because a consumer holds an open subset it obtained elsewhere and a proof that the
  section does not vanish on it.
- `ComplexAnalytic.AnalyticSpace.liftOpen_fac` and
  `ComplexAnalytic.AnalyticSpace.hom_ext_restrict`: the factorisation is one, and a morphism into
  an open subspace is determined by its composite with the inclusion.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic

namespace AnalyticSpace

section LiftOpen

variable {Z X : AnalyticSpace.{u}} (φ : Z ⟶ X) (U : X.Opens)
  (h : Set.range φ.toLRSHom.base ⊆ (U : Set X))

/-- **A morphism of complex analytic spaces whose image lies in an open subset factors through
that open subspace.**

The underlying morphism of locally ringed spaces is
`AlgebraicGeometry.LocallyRingedSpace.liftRestrict`. It is `ℂ`-linear because it is a morphism
*over* `X` ; that is what `liftOpen_fac` says ; and both algebra structures in sight are the
ambient one restricted, which is the hypothesis of `ComplexAnalytic.IsCLinearHom.of_comp`; this is
the same argument that makes `ComplexAnalytic.AnalyticSpace.restrictLE` `ℂ`-linear. -/
def liftOpen : Z ⟶ X.restrict U :=
  ⟨LocallyRingedSpace.liftRestrict φ.toLRSHom U h,
    IsCLinearHom.of_comp (LocallyRingedSpace.liftRestrict_fac φ.toLRSHom U h) φ.isCLinear
      (isCLinearHom_ofRestrict X.toLocallyRingedSpace X.algebraMap U)⟩

/-- **`liftOpen` is a factorisation of `φ`.** This, rather than the morphism itself, is what every
use of it consumes. -/
@[reassoc (attr := simp)]
lemma liftOpen_fac : liftOpen φ U h ≫ X.ofRestrict U = φ :=
  forgetToLocallyRingedSpace.map_injective (LocallyRingedSpace.liftRestrict_fac φ.toLRSHom U h)

/-- **The point of `X|U` underneath a point of `Z` is its image under `φ`.** -/
@[simp]
lemma base_liftOpen (z : Z) : ((liftOpen φ U h).toLRSHom.base z).1 = φ.toLRSHom.base z :=
  LocallyRingedSpace.base_ofRestrict_base_liftRestrict φ.toLRSHom U h z

end LiftOpen

/-- **Two morphisms into an open subspace agreeing after inclusion are equal.**

The inclusion of an open subspace is a monomorphism of locally ringed spaces, and
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` is faithful, so no `ℂ`-linearity
bookkeeping is needed. With `liftOpen_fac` this is the uniqueness half of the universal property
of an open subspace. -/
lemma hom_ext_restrict {Z X : AnalyticSpace.{u}} (U : X.Opens) (l₁ l₂ : Z ⟶ X.restrict U)
    (h : l₁ ≫ X.ofRestrict U = l₂ ≫ X.ofRestrict U) : l₁ = l₂ :=
  forgetToLocallyRingedSpace.map_injective
    (LocallyRingedSpace.hom_ext_restrict U _ _ (congrArg forgetToLocallyRingedSpace.map h))

section Nonvanishing

variable (X : AnalyticSpace.{u}) (a b : X.presheaf.obj (op ⊤))

/-- **The open subset of `X` on which the global section `a` of `𝒪_X` does not vanish.**

This **is** `AlgebraicGeometry.RingedSpace.basicOpen` at `U = ⊤`, and is given a name only
because the analytic reading of it ; the set where the *value* of `a` is nonzero, which is
`mem_nonvanishing_iff` ; is what every consumer here wants, and because it is an
`AnalyticSpace.Opens`. Nothing about it is constructed in this file, openness included. -/
def nonvanishing : X.Opens :=
  X.toRingedSpace.basicOpen a

/-- **A point lies in the non-vanishing locus of `a` exactly when the value of `a` there is
nonzero.**

Mathlib's membership criterion is that the germ at the point is a unit; on a complex analytic
space a germ is a unit exactly when its value is nonzero, which is
`ComplexAnalytic.AnalyticSpace.evalStalk_eq_zero_iff`, i.e. the fact that the residue field is
`ℂ`. This is the only statement in this file that is not available for a general locally ringed
space. -/
lemma mem_nonvanishing_iff {z : X} :
    z ∈ X.nonvanishing a ↔ X.eval (U := ⊤) z trivial a ≠ 0 := by
  rw [ne_eq, eval_apply, evalStalk_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not]
  exact RingedSpace.mem_top_basicOpen X.toRingedSpace a z

/-- **The non-vanishing locus of a product is the intersection of the non-vanishing loci.**

Mathlib's `AlgebraicGeometry.RingedSpace.basicOpen_mul`, restated in the spelling of this file.
It is what makes the non-vanishing locus useful on a space with zero divisors: on the node the
two coordinate functions multiply to zero, so their non-vanishing loci are disjoint. -/
lemma nonvanishing_mul : X.nonvanishing (a * b) = X.nonvanishing a ⊓ X.nonvanishing b :=
  RingedSpace.basicOpen_mul X.toRingedSpace a b

/-- **The non-vanishing locus of a pulled-back section is the preimage of the non-vanishing
locus.**

Every other statement in this section is about one space; this one is what a morphism is for. The
proof is `ComplexAnalytic.AnalyticSpace.mem_nonvanishing_iff` at each end and
`ComplexAnalytic.AnalyticSpace.eval_c_app` in between ; the value at `z` of the pullback of `a` is
the value of `a` at the image of `z`, so the two memberships are the same condition. Nothing in it
is particular to either space, and the section is a *global* one at both ends.

The last step is `Iff.rfl` rather than the `rfl` a `rw` attempts on its own:
`ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ` is spelled with `AlgebraicGeometry.
LocallyRingedSpace.Γ` and `ComplexAnalytic.AnalyticSpace.eval_c_app` with `c.app`, which are
definitionally equal and are not equal at the transparency `rw` closes a goal with. -/
theorem nonvanishing_pullbackΓ {Z W : AnalyticSpace.{u}} (φ : Z ⟶ W)
    (a : W.presheaf.obj (op ⊤)) :
    Z.nonvanishing (φ.pullbackΓ a) = (Opens.map φ.toLRSHom.base).obj (W.nonvanishing a) := by
  refine Opens.ext (Set.ext fun z ↦ ?_)
  change z ∈ Z.nonvanishing (φ.pullbackΓ a) ↔ φ.toLRSHom.base z ∈ W.nonvanishing a
  rw [mem_nonvanishing_iff, mem_nonvanishing_iff,
    ← eval_c_app φ.toLRSHom φ.isCLinear (U := ⊤) z trivial a]
  exact Iff.rfl

/-- **A section is invertible on every open subspace contained in its non-vanishing locus.**

The hypothesis is `≤` and not equality because that is the shape a consumer holds: an open subset
obtained elsewhere, together with the knowledge that `a` does not vanish on it.

`X.resΓ U a` lives in `Γ(X, U.functor.obj ⊤)` rather than in `Γ(X, U)` ; the two opens have the
same points and are not definitionally equal ; which is why the equation identifying `resΓ` with
the restriction map is stated as a `have` and rewritten with, rather than rewritten with directly:
`AlgebraicGeometry.LocallyRingedSpace.Γ_map_ofRestrict_apply` does not match the goal under the
transparency `rw` uses, and elaborating its left-hand side against the goal is what crosses the
seam. -/
theorem isUnit_resΓ_of_le_nonvanishing {U : X.Opens} (h : U ≤ X.nonvanishing a) :
    IsUnit (X.resΓ U a) := by
  have e : X.resΓ U a =
      (X.presheaf.map (homOfLE (le_top :
        U.isOpenEmbedding.isOpenMap.functor.obj ⊤ ≤ ⊤)).op).hom a :=
    LocallyRingedSpace.Γ_map_ofRestrict_apply X.toLocallyRingedSpace U a
  rw [e]
  exact RingedSpace.isUnit_res_of_le_basicOpen X.toRingedSpace a le_top
    (le_trans (le_of_eq (TopologicalSpace.Opens.isOpenEmbedding_obj_top U)) h)

/-- **A section is invertible on its own non-vanishing locus**, the case `U = D(a)` of
`ComplexAnalytic.AnalyticSpace.isUnit_resΓ_of_le_nonvanishing`. -/
theorem isUnit_resΓ_nonvanishing : IsUnit (X.resΓ (X.nonvanishing a) a) :=
  X.isUnit_resΓ_of_le_nonvanishing a le_rfl

end Nonvanishing

end AnalyticSpace

end ComplexAnalytic

end

end
