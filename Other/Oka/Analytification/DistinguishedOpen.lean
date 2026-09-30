/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.Nonvanishing
public import Other.Oka.Analytification.UniversalProperty
public import Other.Oka.RingTheory.MvPolynomial.Localization

/-!
# The analytification of a distinguished open is a distinguished open of the analytification

For `A = ℂ[x₁, …, x_n] ⧸ (g₁, …, g_k)` and `f ∈ ℂ[x]`, the localisation `A_f` is presented by
adjoining one variable and one equation,

  `A_f = ℂ[x₁, …, x_n, t] ⧸ (g₁, …, g_k, t·f - 1)`,

and this file proves that the analytification of that presentation **is** the open subspace of
`X^an = A^an` on which `f` does not vanish:

  `ComplexAnalytic.localisationIso : (A_f)^an ≅ X^an|D(f)`,

**over `X^an`** ; `ComplexAnalytic.localisationIso_hom_ofRestrict` and
`ComplexAnalytic.localisationIso_inv_localisationProj` say the isomorphism commutes with the
projection `(A_f)^an ⟶ X^an` and with the inclusion of the open subspace. Without that the
statement would only compare two spaces that happen to be isomorphic, and would say nothing
about the immersion.

This is the input the analytification of a *non-affine* scheme needs, and the reason it is worth
stating on its own. `Other/Oka/AnalyticSpace/Glue.lean` already glues an analytic space out of a glue
data of analytic pieces; what a glue data needs from *this* side is that the transition maps are
open immersions, and a scheme locally of finite type over `ℂ` is covered by affines whose pairwise
intersections are covered by opens distinguished in both. So it is the **distinguished** case
that is needed, and the analytification of a general open immersion is neither needed for it nor
proved here. Assembling the analytification of a non-affine scheme is a further step and is not
taken in this file.

## The route: the universal property, twice

Both maps are `ComplexAnalytic.liftHom`, which is why this is one file rather than a construction
plus a comparison.

* **Forwards.** `ComplexAnalytic.localisationProj` is the universal property of `X^an` applied to
  the first `n` coordinates of `(A_f)^an`; they satisfy the `gⱼ` because the `gⱼ` occur among the
  equations of the larger presentation, renamed along the inclusion of the variables. Its image
  lies in `D(f)` because the last equation says that `f`, pulled back, is invertible in
  `Γ((A_f)^an, 𝒪)`, so its *value* at every point is invertible in `ℂ`, hence nonzero ; this is
  `ComplexAnalytic.AnalyticSpace.mem_nonvanishing_iff`, and it is the only genuinely geometric
  step in the file. `ComplexAnalytic.AnalyticSpace.liftOpen` then factors it through `X^an|D(f)`.

* **Backwards.** `ComplexAnalytic.restrictToLocalisation` is the universal property of
  `(A_f)^an` applied to the tuple which is the restriction of the coordinates of `X^an` on the
  old variables and the **inverse** of the restriction of `f` on the new one. That inverse exists
  by `ComplexAnalytic.AnalyticSpace.isUnit_resΓ_nonvanishing`, which is why that statement has to
  be about a unit rather than about non-vanishing.

* **The round trips** are `ComplexAnalytic.hom_ext_analytification` on one side and
  `ComplexAnalytic.AnalyticSpace.hom_ext_restrict` followed by it on the other: a morphism into
  an open subspace is determined by its composite with the inclusion, and a morphism into an
  analytification by the pullbacks of the coordinates.

## Non-vacuity

An isomorphism of analytifications is weak evidence on its own ;
`ComplexAnalytic.analytificationIsoOfPresentationIdealEq` already produces plenty, and every
statement here is satisfied by `D(f) = ⊤` and the identity. What rules that reading out is
`ComplexAnalytic.localisationOpen_ne_top`: if `f` vanishes at some point of `X^an` then `D(f)` is
a **proper** open subset.

The three existential statements added later, under
`### Every distinguished open upstairs comes from one downstairs`, split the same way and it is
worth saying which is which. `ComplexAnalytic.exists_pow_mul_eq_rename` is an equation in the
polynomial ring with no point in it, so nothing can make it degenerate. The two about opens are
equalities of subsets of `(A_f)^an`, and if that space were empty they would hold of nothing.
A point of such a space can be obtained from `ComplexAnalytic.range_base_localisationProj` rather
than by writing a coordinate down.

## Main definitions

- `ComplexAnalytic.localisationPresentation`: **the presentation of `A_f`** ; the `gⱼ` in one more
  variable, together with `t·f - 1`.
- `ComplexAnalytic.localisationProj`: **the projection `(A_f)^an ⟶ X^an`.**
- `ComplexAnalytic.localisationOpen`: `D(f) ⊆ X^an`, the non-vanishing locus of `f`.
- `ComplexAnalytic.localisationIso`: **the isomorphism `(A_f)^an ≅ X^an|D(f)`.**
- `ComplexAnalytic.localisationPresentedAlgebraEquiv`: **the algebra `A_f` presents really is the
  localisation** `Localization.Away f`.

## Main results

- `ComplexAnalytic.localisationIso_hom_ofRestrict` and
  `ComplexAnalytic.localisationIso_inv_localisationProj`: **the isomorphism is one over `X^an`.**
- `ComplexAnalytic.eval_localisationProj` and `ComplexAnalytic.base_localisationProj`: the
  projection forgets the last coordinate.
- `ComplexAnalytic.mem_localisationOpen_iff`: a point lies in `D(f)` exactly when `f` does not
  vanish there.
- `ComplexAnalytic.localisationOpen_one`: **`D(1)` is the whole space**, which is the extreme
  opposite of the bullet below and is what a refinement with a trivial refining family asks for.
- `ComplexAnalytic.localisationOpen_ne_top`: **`D(f)` is a proper open subset** whenever `f` has a
  zero on `X^an`.
- `ComplexAnalytic.localisationOpen_mul`: **`D(f · f') = D(f) ⊓ D(f')`** ; the triple overlap of
  an affine cover, as one of the opens this file is about rather than an intersection of two.
- `ComplexAnalytic.localisationOpen_eq_of_isUnit_mul`: **associates cut out the same open** ;
  a hypothesis on the classes in `ℂ[x]/I`, since that is the form a caller holds it in. The
  converse is false, and which statement it would be is at the declaration.
- `ComplexAnalytic.localisationOpen_rename`: **the open cut out upstairs by a renamed polynomial
  is the preimage of the one it cuts out downstairs.** Where the lemma above relates two opens of
  one space, this relates opens of two, which is what a refinement of a cover needs in order to
  say where a point of an overlap lies.
- `ComplexAnalytic.image_base_localisationProj_localisationOpen_rename`: **and its image
  downstairs is `D(f) ⊓ D(f')`** ; the same relation read forwards, for a consumer that has a
  subset of `(A_f)^an` and has to say where it lands.
- `ComplexAnalytic.exists_localisationOpen_eq_rename` and
  `ComplexAnalytic.exists_localisationOpen_eq_comap`: **the converse of the lemma above, for all
  distinguished opens at once** ; every distinguished open of `(A_f)^an` is cut out by a renamed
  polynomial of the base, equivalently is the preimage of a distinguished open of `X^an`. The
  first form produces the *polynomial*, which is what a caller obliged to supply one needs; the
  second is the same fact about opens.
- `ComplexAnalytic.exists_pow_mul_eq_rename`: **clearing the denominator**, the algebra underneath
  those two and a statement about the polynomial ring alone ; the equations `gⱼ` are not used and
  no point is mentioned.
- `ComplexAnalytic.eval_rename_localisationIncl_ne_zero`: **`f` vanishes nowhere on `(A_f)^an`**,
  the last equation of the presentation read at a point.
- `ComplexAnalytic.isOpenImmersion_localisationProj`: **the projection is an open immersion of
  locally ringed spaces** ; the `f_open` field of any
  `AlgebraicGeometry.LocallyRingedSpace.GlueData` built out of an affine cover, and the second
  thing such a glue data needs from this file, alongside the isomorphism.
- `ComplexAnalytic.isIso_localisationProj_one`: **at `f = 1` that open immersion is an
  isomorphism**, since `D(1)` is everything and the inclusion of such an open is invertible. It is
  the degenerate end of the range `ComplexAnalytic.localisationOpen_ne_top` exists to keep the
  statements here away from, and it says nothing about the corresponding morphism of
  *presentations*.
- `ComplexAnalytic.range_base_localisationProj`: **the image of the projection is exactly
  `D(f)`** ; the equality, where `ComplexAnalytic.range_base_localisationProj_subset` is the
  containment. The side condition of an open-immersion lift is a containment *in* this range, so
  the equality is what lets a statement about `D(f)` discharge it.
- `ComplexAnalytic.map_presentationIdeal_localisationPresentation`: the reindexing carries the
  ideal of `ComplexAnalytic.localisationPresentation` to `MvPolynomial.awayIdeal`, which is the
  whole content of the identification on this side; the ring theory is in the mirror tree.

## What is not here

**Nothing in the geometry uses that `ℂ[x, t] ⧸ (g, t·f - 1)` is a localisation of `ℂ[x] ⧸ (g)`,
and until 2026-08-24 nothing proved it.** Everything from `ComplexAnalytic.localisationProj` down
is a statement about `ComplexAnalytic.localisationPresentation` as a *tuple of polynomials*, and
neither the statements nor the proofs mention a localisation; the first paragraph's
`A_f = ℂ[x₁, …, x_n, t] ⧸ (g₁, …, g_k, t·f - 1)` was the classical fact and not a formal one.

It is now proved, in the last section of this file, because **a consumer analytifying an actual
scheme needs it** and cannot get it from the geometry: what a scheme hands you at an overlap is an
isomorphism of *localisations*, and what
`Other/Oka/Analytification/AffineCover.lean`'s `glue` field asks for is an isomorphism of the algebras
these presentations present. The two are `ComplexAnalytic.localisationPresentedAlgebraEquiv` apart.
The ring theory in it is general and lives in `Other/Oka/RingTheory/MvPolynomial/Localization.lean`; this
file contributes only the reindexing of `Fin (n + 1)` as `Option (Fin n)` that names the new
variable, which is the one part of it that is about `ComplexAnalytic.localisationPresentation`.

**The geometry is unchanged and still does not assume it.** `ComplexAnalytic.localisationIso`
and both factorisations are statements about `ComplexAnalytic.localisationPresentation` as a
tuple of polynomials, and neither their statements nor their proofs mention a localisation.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ}

/-! ### The presentation of `A_f` -/

/-- The old variables, read inside the polynomial ring with one more variable. -/
def localisationIncl (n : ℕ) : ULift.{u} (Fin n) → ULift.{u} (Fin (n + 1)) :=
  fun i ↦ ULift.up i.down.castSucc

/-- **Adjoining a variable does not identify two old ones**, which is what makes
`MvPolynomial.rename (ComplexAnalytic.localisationIncl n)` injective. -/
theorem localisationIncl_injective (n : ℕ) : Function.Injective (localisationIncl.{u} n) :=
  fun _ _ hab ↦ ULift.ext _ _ (Fin.castSucc_injective _ (congrArg ULift.down hab))

/-- The new variable, the one that becomes `1/f`. -/
def localisationVar (n : ℕ) : ULift.{u} (Fin (n + 1)) := ULift.up (Fin.last n)

/-- **The presentation of `A_f` obtained from a presentation of `A`**: the old equations in one
more variable, together with `t·f - 1`.

Packaged with `Fin.snoc` because `Fin.lastCases` is then the way to check a statement for every
equation, and the two `simp` lemmas below are the whole interface. Any family with the same span
would do ; `ComplexAnalytic.analytificationIsoOfPresentationIdealEq` says the analytification
sees only the ideal ; so nothing below depends on this packaging beyond those two lemmas. -/
def localisationPresentation (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (f : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    Fin (k + 1) → MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ :=
  Fin.snoc (fun j ↦ MvPolynomial.rename (localisationIncl.{u} n) (g j))
    (MvPolynomial.X (localisationVar.{u} n) *
      MvPolynomial.rename (localisationIncl.{u} n) f - 1)

variable (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) (f : MvPolynomial (ULift.{u} (Fin n)) ℂ)

@[simp]
theorem localisationPresentation_castSucc (j : Fin k) :
    localisationPresentation.{u} g f j.castSucc =
      MvPolynomial.rename (localisationIncl.{u} n) (g j) :=
  Fin.snoc_castSucc _ _ j

@[simp]
theorem localisationPresentation_last :
    localisationPresentation.{u} g f (Fin.last k) =
      MvPolynomial.X (localisationVar.{u} n) *
        MvPolynomial.rename (localisationIncl.{u} n) f - 1 :=
  Fin.snoc_last _ _

/-! ### The projection to `X^an` -/

/-- **The coordinates of `(A_f)^an` on the old variables satisfy the old equations.**

`ComplexAnalytic.eval₂_analytificationCoord_eq_zero` at the equation `gⱼ`, moved across
`MvPolynomial.eval₂_rename`: substituting a tuple into a renamed polynomial is substituting the
renamed tuple into the original. -/
theorem eval₂_analytificationCoord_comp_incl_eq_zero (j : Fin k) :
    MvPolynomial.eval₂
        (AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f)).algebraMap
        (analytificationCoord.{u} (localisationPresentation.{u} g f) ∘ localisationIncl.{u} n)
        (g j) = 0 := by
  have h := eval₂_analytificationCoord_eq_zero (localisationPresentation.{u} g f) j.castSucc
  rwa [localisationPresentation_castSucc, MvPolynomial.eval₂_rename] at h

/-- **The projection `(A_f)^an ⟶ X^an`**, the universal property of `X^an` applied to the
coordinates of `(A_f)^an` on the old variables. -/
def localisationProj :
    AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f) ⟶
      AnalyticSpace.analytification.{u} g :=
  liftHom.{u} g _ _ (eval₂_analytificationCoord_comp_incl_eq_zero.{u} g f)

@[simp]
theorem coordPullback_localisationProj_comp (i : ULift.{u} (Fin n)) :
    AnalyticSpace.coordPullback
        (localisationProj.{u} g f ≫ analytificationInclHom.{u} g) i =
      analytificationCoord.{u} (localisationPresentation.{u} g f) (localisationIncl.{u} n i) :=
  coordPullback_liftHom_comp.{u} g _ _ _ i

/-- **The projection carries the `i`-th coordinate of `X^an` to the `i`-th coordinate of
`(A_f)^an`**, which is what the universal property was applied to. -/
@[simp]
theorem pullbackΓ_localisationProj_analytificationCoord (i : ULift.{u} (Fin n)) :
    (localisationProj.{u} g f).pullbackΓ (analytificationCoord.{u} g i) =
      analytificationCoord.{u} (localisationPresentation.{u} g f) (localisationIncl.{u} n i) :=
  (AnalyticSpace.coordPullback_comp (localisationProj.{u} g f)
    (analytificationInclHom.{u} g) i).symm.trans
      (coordPullback_localisationProj_comp.{u} g f i)

/-- **The projection carries a polynomial section to the renamed polynomial section**, the
statement of which the previous lemma is the case `p = xᵢ`. -/
theorem pullbackΓ_localisationProj_polyToGlobal (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    (localisationProj.{u} g f).pullbackΓ (polyToGlobal.{u} g p) =
      MvPolynomial.eval₂
        (AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f)).algebraMap
        (analytificationCoord.{u} (localisationPresentation.{u} g f))
        (MvPolynomial.rename (localisationIncl.{u} n) p) :=
  (congrArg (localisationProj.{u} g f).pullbackΓ
      (RingHom.congr_fun (polyToGlobal_eq_eval₂Hom.{u} g) p)).trans
    ((AnalyticSpace.pullbackΓ_eval₂ (localisationProj.{u} g f) (analytificationCoord.{u} g) p).trans
      ((congrArg (fun a ↦ MvPolynomial.eval₂ _ a p)
          (funext (pullbackΓ_localisationProj_analytificationCoord.{u} g f))).trans
        (MvPolynomial.eval₂_rename _ _ _ p).symm))

/-- **The last equation, read on `(A_f)^an`**: the new coordinate is inverse to the pullback of
`f`. This is the whole content of adjoining the variable, and everything below is a consequence
of it. -/
theorem analytificationCoord_localisationVar_mul :
    analytificationCoord.{u} (localisationPresentation.{u} g f) (localisationVar.{u} n) *
        (localisationProj.{u} g f).pullbackΓ (polyToGlobal.{u} g f) = 1 := by
  have h := eval₂_analytificationCoord_eq_zero (localisationPresentation.{u} g f) (Fin.last k)
  rw [localisationPresentation_last, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_one, sub_eq_zero] at h
  rw [pullbackΓ_localisationProj_polyToGlobal]
  exact h

theorem isUnit_pullbackΓ_localisationProj_polyToGlobal :
    IsUnit ((localisationProj.{u} g f).pullbackΓ (polyToGlobal.{u} g f)) :=
  IsUnit.of_mul_eq_one_right _ (analytificationCoord_localisationVar_mul.{u} g f)

/-! ### The open subspace `D(f)` and the isomorphism -/

/-- **`D(f) ⊆ X^an`**, the locus on which the section attached to `f` does not vanish.

An `abbrev` for `ComplexAnalytic.AnalyticSpace.nonvanishing` at
`ComplexAnalytic.polyToGlobal`, so that every lemma about the non-vanishing locus applies to it
unchanged; it exists because that expression occurs in the statement of almost everything
below. -/
abbrev localisationOpen : (AnalyticSpace.analytification.{u} g).Opens :=
  (AnalyticSpace.analytification.{u} g).nonvanishing (polyToGlobal.{u} g f)

/-- **The image of the projection lies in `D(f)`.**

The pullback of `f` is a unit in `Γ((A_f)^an, 𝒪)`, so its value at any point is a unit in `ℂ`,
hence nonzero; and the value of the pullback at a point is the value of `f` at the image point,
which is `ComplexAnalytic.AnalyticSpace.eval_c_app`. This is the step that turns the algebraic
equation `t·f = 1` into a topological containment. -/
theorem range_base_localisationProj_subset :
    Set.range (localisationProj.{u} g f).toLRSHom.base ⊆
      (localisationOpen.{u} g f : Set (AnalyticSpace.analytification.{u} g)) := by
  rintro _ ⟨z, rfl⟩
  refine (AnalyticSpace.mem_nonvanishing_iff _ _).2 ?_
  rw [← AnalyticSpace.eval_c_app (localisationProj.{u} g f).toLRSHom
    (localisationProj.{u} g f).isCLinear (U := ⊤) z trivial (polyToGlobal.{u} g f)]
  exact ((isUnit_pullbackΓ_localisationProj_polyToGlobal.{u} g f).map
    ((AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f)).eval
      (U := ⊤) z trivial)).ne_zero

/-- **The projection, factored through the open subspace `X^an|D(f)`.** -/
def localisationToRestrict :
    AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f) ⟶
      (AnalyticSpace.analytification.{u} g).restrict (localisationOpen.{u} g f) :=
  AnalyticSpace.liftOpen (localisationProj.{u} g f) _
    (range_base_localisationProj_subset.{u} g f)

@[reassoc (attr := simp)]
theorem localisationToRestrict_fac :
    localisationToRestrict.{u} g f ≫
        (AnalyticSpace.analytification.{u} g).ofRestrict (localisationOpen.{u} g f) =
      localisationProj.{u} g f :=
  AnalyticSpace.liftOpen_fac _ _ _

/-- **The tuple of `n + 1` sections of `𝒪` on `X^an|D(f)` that the inverse map is built from**:
the restrictions of the coordinates of `X^an` on the old variables, and the inverse of the
restriction of `f` on the new one.

The inverse is `ComplexAnalytic.AnalyticSpace.isUnit_resΓ_nonvanishing`, and this is the place
where that statement has to be about a *unit*: a section which merely does not vanish on `D(f)`
would give no element to put here. -/
def localisationSection : ULift.{u} (Fin (n + 1)) →
    ((AnalyticSpace.analytification.{u} g).restrict
      (localisationOpen.{u} g f)).presheaf.obj (op ⊤) :=
  fun i ↦ Fin.lastCases
    (((AnalyticSpace.analytification.{u} g).isUnit_resΓ_nonvanishing
      (polyToGlobal.{u} g f)).unit⁻¹ : _)
    (fun i' ↦ (AnalyticSpace.analytification.{u} g).resΓ (localisationOpen.{u} g f)
      (analytificationCoord.{u} g (ULift.up i')))
    i.down

@[simp]
theorem localisationSection_incl (i : ULift.{u} (Fin n)) :
    localisationSection.{u} g f (localisationIncl.{u} n i) =
      (AnalyticSpace.analytification.{u} g).resΓ (localisationOpen.{u} g f)
        (analytificationCoord.{u} g i) :=
  Fin.lastCases_castSucc i.down

@[simp]
theorem localisationSection_var :
    localisationSection.{u} g f (localisationVar.{u} n) =
      (((AnalyticSpace.analytification.{u} g).isUnit_resΓ_nonvanishing
        (polyToGlobal.{u} g f)).unit⁻¹ : _) :=
  Fin.lastCases_last

/-- **Restricting a polynomial section to `D(f)` substitutes the restricted coordinates.**

`ComplexAnalytic.AnalyticSpace.pullbackΓ_eval₂` at the inclusion of the open subspace: the
`ℂ`-algebra structure on `X^an|D(f)` is the ambient one restricted, so no transport is
involved. -/
theorem resΓ_polyToGlobal (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    (AnalyticSpace.analytification.{u} g).resΓ (localisationOpen.{u} g f)
        (polyToGlobal.{u} g p) =
      MvPolynomial.eval₂ ((AnalyticSpace.analytification.{u} g).restrict
          (localisationOpen.{u} g f)).algebraMap
        (localisationSection.{u} g f ∘ localisationIncl.{u} n) p :=
  (congrArg _ (RingHom.congr_fun (polyToGlobal_eq_eval₂Hom.{u} g) p)).trans
    ((AnalyticSpace.pullbackΓ_eval₂
        ((AnalyticSpace.analytification.{u} g).ofRestrict (localisationOpen.{u} g f))
        (analytificationCoord.{u} g) p).trans
      (congrArg (fun a ↦ MvPolynomial.eval₂ _ a p)
        (funext fun i ↦ (localisationSection_incl.{u} g f i).symm)))

/-- **The tuple on `X^an|D(f)` satisfies the equations of the larger presentation.** The old ones
because restriction is a ring homomorphism compatible with the constants and `gⱼ` is already zero
upstairs; the new one because the last entry was chosen to be an inverse. -/
theorem eval₂_localisationSection_eq_zero (j : Fin (k + 1)) :
    MvPolynomial.eval₂ ((AnalyticSpace.analytification.{u} g).restrict
        (localisationOpen.{u} g f)).algebraMap (localisationSection.{u} g f)
      (localisationPresentation.{u} g f j) = 0 := by
  refine Fin.lastCases ?_ (fun j' ↦ ?_) j
  · rw [localisationPresentation_last, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_X, MvPolynomial.eval₂_one, MvPolynomial.eval₂_rename,
      localisationSection_var, ← resΓ_polyToGlobal, sub_eq_zero]
    exact Units.inv_mul_of_eq (IsUnit.unit_spec _)
  · rw [localisationPresentation_castSucc, MvPolynomial.eval₂_rename, ← resΓ_polyToGlobal,
      polyToGlobal_apply_eq_zero]
    exact map_zero _

/-- **The inverse map `X^an|D(f) ⟶ (A_f)^an`**, the universal property of `(A_f)^an` applied to
`ComplexAnalytic.localisationSection`. -/
def restrictToLocalisation :
    (AnalyticSpace.analytification.{u} g).restrict (localisationOpen.{u} g f) ⟶
      AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f) :=
  liftHom.{u} (localisationPresentation.{u} g f) _ (localisationSection.{u} g f)
    (eval₂_localisationSection_eq_zero.{u} g f)

@[simp]
theorem coordPullback_restrictToLocalisation_comp (i : ULift.{u} (Fin (n + 1))) :
    AnalyticSpace.coordPullback (restrictToLocalisation.{u} g f ≫
        analytificationInclHom.{u} (localisationPresentation.{u} g f)) i =
      localisationSection.{u} g f i :=
  coordPullback_liftHom_comp.{u} (localisationPresentation.{u} g f) _ _ _ i

@[simp]
theorem pullbackΓ_restrictToLocalisation_analytificationCoord (i : ULift.{u} (Fin (n + 1))) :
    (restrictToLocalisation.{u} g f).pullbackΓ
        (analytificationCoord.{u} (localisationPresentation.{u} g f) i) =
      localisationSection.{u} g f i :=
  (AnalyticSpace.coordPullback_comp (restrictToLocalisation.{u} g f)
    (analytificationInclHom.{u} (localisationPresentation.{u} g f)) i).symm.trans
      (coordPullback_restrictToLocalisation_comp.{u} g f i)

/-- **Restricting to `D(f)` and then pulling back along the factored projection is pulling back
along the projection.**

Spelled at the level of locally ringed spaces, and proved from
`AlgebraicGeometry.LocallyRingedSpace.liftRestrict_fac` rather than from
`ComplexAnalytic.localisationToRestrict_fac`, for the reason
`ComplexAnalytic.AnalyticSpace.resΓ_restrictLE` records: a `congrArg` over morphisms of *analytic*
spaces forces the unification of `(f ≫ g).toLRSHom` with `f.toLRSHom ≫ g.toLRSHom` and **exceeds
the default heartbeat budget**.

**Measured here and not inherited**, 2026-08-31, by giving the `congrArg` below a motive over
`AnalyticSpace.analytification (localisationPresentation g f) ⟶ AnalyticSpace.analytification g`
and `ComplexAnalytic.localisationToRestrict_fac` as its argument:
`(deterministic) timeout at whnf, maximum number of heartbeats (200000)`, reached in 23s.
That is the same failure at the same budget as the site above, at a different pair of morphisms,
and 200000 is what `lakefile.toml` leaves in force ; the figure of a million this paragraph gave
until today was a budget nobody set. The unbounded run was **not** made here; at the site this
one cites it was still elaborating after 21m29s. -/
@[simp]
theorem pullbackΓ_localisationToRestrict_resΓ
    (s : (AnalyticSpace.analytification.{u} g).presheaf.obj (op ⊤)) :
    (localisationToRestrict.{u} g f).pullbackΓ
        ((AnalyticSpace.analytification.{u} g).resΓ (localisationOpen.{u} g f) s) =
      (localisationProj.{u} g f).pullbackΓ s :=
  (LocallyRingedSpace.Γ_map_comp_apply (localisationToRestrict.{u} g f).toLRSHom
      ((AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.ofRestrict
        (localisationOpen.{u} g f).isOpenEmbedding) s).symm.trans
    (congrArg (fun m : (AnalyticSpace.analytification.{u}
          (localisationPresentation.{u} g f)).toLocallyRingedSpace ⟶
        (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace ↦
      (LocallyRingedSpace.Γ.map m.op).hom s)
      (LocallyRingedSpace.liftRestrict_fac (localisationProj.{u} g f).toLRSHom
        (localisationOpen.{u} g f) (range_base_localisationProj_subset.{u} g f)))

/-- **The factored projection carries the tuple back to the coordinates of `(A_f)^an`.**

On an old variable this is `ComplexAnalytic.pullbackΓ_localisationProj_analytificationCoord`; on
the new one both the image of the inverse and the new coordinate are inverses of the pullback of
`f`, so they agree by cancellation. This is the half of the round trips that is not
bookkeeping. -/
theorem pullbackΓ_localisationToRestrict_localisationSection (i : ULift.{u} (Fin (n + 1))) :
    (localisationToRestrict.{u} g f).pullbackΓ (localisationSection.{u} g f i) =
      analytificationCoord.{u} (localisationPresentation.{u} g f) i := by
  refine Fin.lastCases (motive := fun d ↦
    (localisationToRestrict.{u} g f).pullbackΓ
        (localisationSection.{u} g f (ULift.up d)) =
      analytificationCoord.{u} (localisationPresentation.{u} g f) (ULift.up d)) ?_ ?_ i.down
  · change (localisationToRestrict.{u} g f).pullbackΓ
        (localisationSection.{u} g f (localisationVar.{u} n)) =
      analytificationCoord.{u} (localisationPresentation.{u} g f) (localisationVar.{u} n)
    rw [localisationSection_var]
    refine ((isUnit_pullbackΓ_localisationProj_polyToGlobal.{u} g f).mul_right_cancel ?_).symm
    rw [analytificationCoord_localisationVar_mul, ← pullbackΓ_localisationToRestrict_resΓ]
    exact ((congrArg (fun s ↦ (localisationToRestrict.{u} g f).pullbackΓ
            (((AnalyticSpace.analytification.{u} g).isUnit_resΓ_nonvanishing
              (polyToGlobal.{u} g f)).unit⁻¹ : _) *
            (localisationToRestrict.{u} g f).pullbackΓ s)
          (IsUnit.unit_spec _).symm).trans
        ((map_mul _ _ _).symm.trans ((congrArg _ (Units.inv_mul _)).trans (map_one _)))).symm
  · intro i'
    change (localisationToRestrict.{u} g f).pullbackΓ
        (localisationSection.{u} g f (localisationIncl.{u} n (ULift.up i'))) =
      analytificationCoord.{u} (localisationPresentation.{u} g f)
        (localisationIncl.{u} n (ULift.up i'))
    rw [localisationSection_incl, pullbackΓ_localisationToRestrict_resΓ,
      pullbackΓ_localisationProj_analytificationCoord]

theorem localisationToRestrict_restrictToLocalisation :
    localisationToRestrict.{u} g f ≫ restrictToLocalisation.{u} g f = 𝟙 _ := by
  refine hom_ext_analytification.{u} (localisationPresentation.{u} g f) _ _ fun i ↦ ?_
  rw [Category.assoc, AnalyticSpace.coordPullback_comp,
    coordPullback_restrictToLocalisation_comp, Category.id_comp]
  exact pullbackΓ_localisationToRestrict_localisationSection.{u} g f i

theorem restrictToLocalisation_localisationToRestrict :
    restrictToLocalisation.{u} g f ≫ localisationToRestrict.{u} g f = 𝟙 _ := by
  refine AnalyticSpace.hom_ext_restrict _ _ _ ?_
  rw [Category.id_comp, Category.assoc, localisationToRestrict_fac]
  refine hom_ext_analytification.{u} g _ _ fun i ↦ ?_
  rw [Category.assoc, AnalyticSpace.coordPullback_comp, coordPullback_localisationProj_comp,
    AnalyticSpace.coordPullback_comp]
  exact (pullbackΓ_restrictToLocalisation_analytificationCoord.{u} g f _).trans
    (localisationSection_incl.{u} g f i)

/-- **The analytification of `A_f` is the non-vanishing locus of `f` in `X^an`.**

The two factorisation lemmas below are what makes this a statement about the open immersion
rather than an accidental isomorphism of spaces. -/
def localisationIso :
    AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f) ≅
      (AnalyticSpace.analytification.{u} g).restrict (localisationOpen.{u} g f) where
  hom := localisationToRestrict.{u} g f
  inv := restrictToLocalisation.{u} g f
  hom_inv_id := localisationToRestrict_restrictToLocalisation.{u} g f
  inv_hom_id := restrictToLocalisation_localisationToRestrict.{u} g f

/-- **The isomorphism is one over `X^an`**: followed by the inclusion of the open subspace it is
the projection. -/
@[simp]
theorem localisationIso_hom_ofRestrict :
    (localisationIso.{u} g f).hom ≫
        (AnalyticSpace.analytification.{u} g).ofRestrict (localisationOpen.{u} g f) =
      localisationProj.{u} g f :=
  localisationToRestrict_fac.{u} g f

/-- **The inverse is a morphism over `X^an` too**: followed by the projection it is the inclusion
of the open subspace. -/
@[simp]
theorem localisationIso_inv_localisationProj :
    (localisationIso.{u} g f).inv ≫ localisationProj.{u} g f =
      (AnalyticSpace.analytification.{u} g).ofRestrict (localisationOpen.{u} g f) :=
  (congrArg (fun m ↦ (localisationIso.{u} g f).inv ≫ m)
      (localisationToRestrict_fac.{u} g f)).symm.trans
    ((localisationIso.{u} g f).inv_hom_id_assoc _)

/-! ### What the projection does on points -/

/-- **The projection forgets the last coordinate**, in the form in which the value of every
polynomial can be read off: the value of `p` at the image of `w` is the value of `p` with its
variables renamed at `w` itself.

At `p = xᵢ` this says the `i`-th coordinate of the image point is the `i`-th coordinate of `w`,
which is the concrete description of the projection; `ComplexAnalytic.eval_polyToGlobal` is what
turns a section into a value at both ends. -/
theorem eval_localisationProj
    (w : AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f))
    (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    MvPolynomial.eval
        (((localisationProj.{u} g f).toLRSHom.base w).1.1 : ULift.{u} (Fin n) → ℂ) p =
      MvPolynomial.eval (w.1.1 : ULift.{u} (Fin (n + 1)) → ℂ)
        (MvPolynomial.rename (localisationIncl.{u} n) p) := by
  rw [← eval_polyToGlobal, ← eval_polyToGlobal,
    ← AnalyticSpace.eval_c_app (localisationProj.{u} g f).toLRSHom
      (localisationProj.{u} g f).isCLinear (U := ⊤) w trivial (polyToGlobal.{u} g p)]
  exact congrArg _ ((pullbackΓ_localisationProj_polyToGlobal.{u} g f p).trans
    (RingHom.congr_fun
      (polyToGlobal_eq_eval₂Hom.{u} (localisationPresentation.{u} g f))
      (MvPolynomial.rename (localisationIncl.{u} n) p)).symm)

/-- **The projection is the first `n` coordinates**, which is the concrete description of it:
`ComplexAnalytic.eval_localisationProj` at `p = xᵢ`. -/
@[simp]
theorem base_localisationProj
    (w : AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f))
    (i : ULift.{u} (Fin n)) :
    (((localisationProj.{u} g f).toLRSHom.base w).1.1 : ULift.{u} (Fin n) → ℂ) i =
      (w.1.1 : ULift.{u} (Fin (n + 1)) → ℂ) (localisationIncl.{u} n i) :=
  (MvPolynomial.eval_X i).symm.trans
    ((eval_localisationProj.{u} g f w (MvPolynomial.X i)).trans
      ((congrArg (MvPolynomial.eval (w.1.1 : ULift.{u} (Fin (n + 1)) → ℂ))
        (MvPolynomial.rename_X (localisationIncl.{u} n) i)).trans
          (MvPolynomial.eval_X (localisationIncl.{u} n i))))

/-- **A point of `X^an` lies in `D(f)` exactly when `f` does not vanish there.**

`ComplexAnalytic.AnalyticSpace.mem_nonvanishing_iff` decides membership by the value of the
*section*; this says that value is the value of the *polynomial*, which is the form in which a
caller holds it. -/
theorem mem_localisationOpen_iff {y : AnalyticSpace.analytification.{u} g} :
    y ∈ localisationOpen.{u} g f ↔
      MvPolynomial.eval (y.1.1 : ULift.{u} (Fin n) → ℂ) f ≠ 0 := by
  rw [AnalyticSpace.mem_nonvanishing_iff, eval_polyToGlobal]

/-- **`D(1)` is the whole space.**

The constant `1` vanishes nowhere, which `ComplexAnalytic.mem_localisationOpen_iff` turns into a
membership. Stated because a *refinement* whose refining family is constantly `1` is the cheapest
witness that the cross-member construction is non-vacuous, and its range law asks for exactly this
open ; see `Other/Oka/Analytification/RefineDatumWitness.lean`. It is the extreme opposite of the
theorem below, which is what stops the statements here from being satisfied by `D(f) = ⊤`. -/
theorem localisationOpen_one : localisationOpen.{u} g 1 = ⊤ := by
  ext y
  simp [mem_localisationOpen_iff]

/-- **`D(f)` is a proper open subset whenever `f` vanishes somewhere on `X^an`.**

This is what stops every statement in this file from being satisfied by `D(f) = ⊤` and the
identity, and it is the reason `ComplexAnalytic.eval_polyToGlobal` is quoted here at all: the
hypothesis is about the polynomial, and the conclusion about the open subset. -/
theorem localisationOpen_ne_top (y : AnalyticSpace.analytification.{u} g)
    (hy : MvPolynomial.eval (y.1.1 : ULift.{u} (Fin n) → ℂ) f = 0) :
    localisationOpen.{u} g f ≠ ⊤ := by
  intro hcon
  refine (mem_localisationOpen_iff.{u} g f).1 ?_ hy
  rw [hcon]
  trivial

/-- **At `f = 1` the projection is an isomorphism**, and not merely the open immersion onto `D(f)`
that `ComplexAnalytic.isOpenImmersion_localisationProj` gives at every `f`.

`ComplexAnalytic.localisationIso` factors the projection through the inclusion of `D(1)`
(`ComplexAnalytic.localisationIso_hom_ofRestrict`), `ComplexAnalytic.localisationOpen_one` says
that open is everything, and `ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ` inverts
the inclusion there. So both factors are isomorphisms and **nothing here is proved about
localisation**: the content is entirely in those three, and this is their composite.

**The hypothesis fed to `isIso_ofRestrict_of_eq_univ` is set-level and the `rfl` after the `rw` is
what supplies it.** That theorem asks for `(U : Set X) = Set.univ` rather than `U = ⊤`, which is
what makes it usable here at all: `ComplexAnalytic.localisationOpen_one` is an equality of
`TopologicalSpace.Opens`, and rewriting with it leaves the coercion, where `rfl` closes it. Stating
it at `U = ⊤` instead would have forced a transport, for the reason
`ComplexAnalytic.AnalyticSpace.liftTop`'s docstring gives.

**This is the degenerate case `ComplexAnalytic.localisationOpen_ne_top` above exists to exclude**,
now exhibited rather than described: that lemma says `D(f)` is proper whenever `f` has a zero, and
what it is guarding against is exactly this ; at `f = 1` there is no zero, `D(1) = ⊤`, and the
projection is an isomorphism, so a statement about a general `f` that were satisfied by `f = 1`
would be saying nothing. Nothing below is stated at `f = 1`.

**It says nothing at the level of presentations, and what is missing between the two runs one
way only.** `ComplexAnalytic.localisationHom` (`Other/Oka/Analytification/LocalisationFunctor.lean`) is
the same map as a morphism of `ComplexAnalytic.Presentation`, and whether *it* is an isomorphism
at `f = 1` ; a statement about presented algebras ; does not follow from this:
`ComplexAnalytic.analytificationFunctor` is not known here to reflect isomorphisms, and nothing in
this repository says it is. **This paragraph also said the presentation-level statement was not
decided anywhere, and that is no longer true**: `ComplexAnalytic.isIso_localisationHom_one`
(`Other/Oka/Analytification/LocalisationIndependence.lean`, two modules downstream of this one) is that
statement, proved out of `IsLocalization.atUnits` rather than out of anything here.

**The other direction is not absent, and this paragraph once said the implication was missing in
both.** A presentation-level isomorphism gives the analytic one by functoriality and nothing else:
`ComplexAnalytic.analytificationFunctor_map_localisationPresHom`
(`Other/Oka/Analytification/LocalisationFunctor.lean`) identifies the projection here with the functor's
value on that morphism, and a functor carries an isomorphism to one. **So what is absent here is
the *reflection* and nothing else** ; the analytic-to-presentation direction named above. -/
theorem isIso_localisationProj_one : IsIso (localisationProj.{u} g 1) := by
  haveI : IsIso ((AnalyticSpace.analytification.{u} g).ofRestrict
      (localisationOpen.{u} g 1)) := by
    refine AnalyticSpace.isIso_ofRestrict_of_eq_univ.{u} _ _ ?_
    rw [localisationOpen_one.{u} g]
    rfl
  rw [← localisationIso_hom_ofRestrict.{u} g 1]
  infer_instance

/-- **`D(f · f') = D(f) ⊓ D(f')`.**

The triple-overlap identity a glue data built from an affine cover needs: in `A_i^an` the overlap
of `D(f_ij)` with `D(f_ik)` is the distinguished open of the product, so it is again one of the
opens this file is about rather than merely an intersection of two.

`ComplexAnalytic.polyToGlobal` is a ring map, so the section of the product is the product of the
sections, and `ComplexAnalytic.AnalyticSpace.nonvanishing_mul` is the statement for sections. -/
theorem localisationOpen_mul (f' : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    localisationOpen.{u} g (f * f') =
      localisationOpen.{u} g f ⊓ localisationOpen.{u} g f' := by
  rw [localisationOpen, map_mul, AnalyticSpace.nonvanishing_mul]

/-- **Associates cut out the same open**: if the class of `p` in `ℂ[x]/I` is a unit multiple of
the class of `p'`, then `D(p) = D(p')`.

The hypothesis is on the *classes* and not on the polynomials, which is the form in which a
caller holds it ; an identity in a presented algebra ; and it is why the proof runs through
`ComplexAnalytic.quotientEval` rather than through `MvPolynomial.eval` directly: evaluation at a
point of `X^an` kills the presentation ideal, so it factors through the quotient, and
`ComplexAnalytic.quotientEval_mk` is the equation saying the two agree on a representative. The
image of a unit under a ring map into `ℂ` is a unit and hence nonzero, so the two values differ by
a nonzero factor and `ComplexAnalytic.mem_localisationOpen_iff` decides both memberships by the
same condition.

**The converse is false and `Other/Oka/Analytification/LocalisationIndependence.lean` says so.** An
equality of non-vanishing loci does not give an associate over a general presented `ℂ`-algebra ;
`ComplexAnalytic.exists_mk_rename_eq`'s docstring calls that implication a Nullstellensatz
statement nothing here proves ; so the two directions are different facts and only this one is a
theorem. That is the whole reason the geometric consumers of an associate condition read it in
this direction: `ComplexAnalytic.RefineDatumCrossFactor` is stated as a unit multiple of classes,
and what a refinement needs of it is an equality of opens. -/
theorem localisationOpen_eq_of_isUnit_mul (p p' : MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (u : (PresentedAlgebra.{u} n k g)ˣ)
    (h : Ideal.Quotient.mk (presentationIdeal.{u} g) p =
      (u : PresentedAlgebra.{u} n k g) * Ideal.Quotient.mk (presentationIdeal.{u} g) p') :
    localisationOpen.{u} g p = localisationOpen.{u} g p' := by
  refine Opens.ext (Set.ext fun y ↦ ?_)
  change y ∈ localisationOpen.{u} g p ↔ y ∈ localisationOpen.{u} g p'
  rw [mem_localisationOpen_iff, mem_localisationOpen_iff]
  have he : MvPolynomial.eval (y.1.1 : ULift.{u} (Fin n) → ℂ) p =
      quotientEval.{u} g y (u : PresentedAlgebra.{u} n k g) *
        MvPolynomial.eval (y.1.1 : ULift.{u} (Fin n) → ℂ) p' := by
    have hq := congrArg (quotientEval.{u} g y) h
    rwa [map_mul, quotientEval_mk, quotientEval_mk] at hq
  have hu : quotientEval.{u} g y (u : PresentedAlgebra.{u} n k g) ≠ 0 :=
    (u.isUnit.map (quotientEval.{u} g y)).ne_zero
  rw [he, mul_ne_zero_iff]
  exact ⟨fun h' ↦ h'.2, fun h' ↦ ⟨hu, h'⟩⟩

/-- **`D(f')` upstairs is the preimage of `D(f')` downstairs**, along the projection.

Read `f'` in the extra variable ; which is `MvPolynomial.rename` along
`ComplexAnalytic.localisationIncl`, the same renaming
`ComplexAnalytic.localisationPresentation` applies to the old equations ; and the open it cuts out
of `(A_f)^an` is exactly what lies over `D(f')`. Nothing here is about `f`: the projection sends
the old coordinates to the old coordinates, and that is the whole content.

**This is not `ComplexAnalytic.localisationOpen_mul` and the two are easy to confuse.** That one
says `D(f · f') = D(f) ⊓ D(f')` **inside a single space** and is how a triple overlap becomes one
of this file's opens. This one relates opens of **two** spaces across the projection, and it is
what a statement about a distinguished open of `X^an` needs in order to say anything about
`(A_f)^an`.

`ComplexAnalytic.eval_localisationProj` is the whole proof: it says evaluating `p` at the image
point is evaluating the renamed `p` at the point, and
`ComplexAnalytic.mem_localisationOpen_iff` turns each membership into such an evaluation. -/
theorem localisationOpen_rename (f' : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    localisationOpen.{u} (localisationPresentation.{u} g f)
        (MvPolynomial.rename (localisationIncl.{u} n) f') =
      (Opens.map (localisationProj.{u} g f).toLRSHom.base).obj
        (localisationOpen.{u} g f') := by
  refine Opens.ext (Set.ext fun w ↦ ?_)
  change w ∈ localisationOpen.{u} (localisationPresentation.{u} g f)
      (MvPolynomial.rename (localisationIncl.{u} n) f') ↔
    (localisationProj.{u} g f).toLRSHom.base w ∈ localisationOpen.{u} g f'
  rw [mem_localisationOpen_iff, mem_localisationOpen_iff, eval_localisationProj]

/-! ### Every distinguished open upstairs comes from one downstairs

`ComplexAnalytic.localisationOpen_rename` above says that a polynomial of the base, read in the
extra variable, cuts out of `(A_f)^an` exactly what lies over what it cuts out of `X^an`. This
section is the **converse**, and it is a statement about all distinguished opens rather than about
one: *every* distinguished open of `(A_f)^an` arises that way. Nothing upstairs is new.

The reason is one line of algebra. A point of `(A_f)^an` is a point `x` of `D(f)` together with the
value `1/f(x)` in the extra coordinate, so a polynomial `q` in `n + 1` variables takes the value
`Σ_d c_d(x) · f(x)^(-d)` there, and multiplying by `f(x)^D` for `D` large clears every denominator
and leaves a polynomial in `x` alone. `ComplexAnalytic.exists_pow_mul_eq_rename` is that
computation, done on polynomials modulo the relation `t·f - 1` rather than on values, and
`ComplexAnalytic.exists_localisationOpen_eq_rename` is the geometric consequence ; the multiplier
is invertible at every point of `(A_f)^an`, so it does not move a non-vanishing locus.

**What this is for.** A refinement of an affine cover that refines *across* members has to cut its
overlaps out of a localisation, and `Other/Oka/Analytification/AffineCover.lean`'s `poly` field asks for
**one polynomial per ordered pair** ; its module docstring says in terms that this arity is a
restriction, because a general scheme's pairwise intersections are only *covered* by opens
distinguished in both. Between two members of a cover **already in that shape** the restriction
costs nothing, and this section is the half of that which was missing: every distinguished open of
a localisation is cut out by a renamed polynomial of the member it sits in.

**The other half is not below and the sentence above does not assert it**, but it is no longer
absent from the repository: that the overlap of two refined members *is* a distinguished open of
the localisation needs a distinguished open to pull back along a `ComplexAnalytic.PresHom` to a
distinguished open, and that is `Other/Oka/Analytification/DistinguishedOpenPullback.lean`, which
imports this file. It is bookkeeping about `ComplexAnalytic.polyToGlobal` and
`ComplexAnalytic.AnalyticSpace.mem_nonvanishing_iff` rather than geometry, as this paragraph
predicted when it was still missing, and it is stated there rather than here because it needs
`Other/Oka/Analytification/ChangeOfVariables.lean`, which this file does not import.

**Nothing there builds a refinement either**, and of the two remaining pieces this paragraph named
one is now here and the other is here in part. Transporting the original cover's own glue
isomorphism through two localisations is `ComplexAnalytic.refineCrossGlue`
(`Other/Oka/Analytification/CrossMemberGlue.lean`), with the coherence triangle
`ComplexAnalytic.refineCrossGlue_hom_comp`. **This sentence read *"only one is still nowhere"* and
*"the two geometric laws across members are still nowhere"*, and the two no longer stand or fall
together**: `ComplexAnalytic.refineDatumTransitionHom_localisationProj_of_ne`
(`Other/Oka/Analytification/RefineDatumTransition.lean`) is `hrange`'s cross-member analogue, the refined
transition lying over the original datum's own `ComplexAnalytic.coverTransitionHom` for want of any
morphism between two members to lie over. **It does not prove `hrange`**: at a triple whose three
members are pairwise different what is left is one containment, in the caller's own `D(q b c)`,
which `ComplexAnalytic.range_refineDatumTransitionHom_subset_iff` states as an *equivalence* and
not as a sufficient condition; and at the mixed triples `ComplexAnalytic.refineDatumGlue` takes its
equal branch, whose triangle is over a *member*, so **that** square has no statement there ; and
the square over an identification of the two members does, which is
`Other/Oka/Analytification/RefineDatumRange.lean` and settles the other four shapes.
`Other/Oka/Analytification/RefineDatumGlueData.lean` joins the five into one law, on two conditions it
adopts and proves necessary. This sentence ended *"the square has no statement there at all"*
until the first of those, and it then said **`hcocycle` is still nowhere**, which is no longer
true either: it is stated as `ComplexAnalytic.RefineDatumCocycle`, which needed the assembled
range law because `ComplexAnalytic.coverTriple` takes a proof of it as an argument, and
`ComplexAnalytic.refineDatumHcocycle` (`Other/Oka/Analytification/RefineDatumCocycle.lean`) proves it
from the original datum's own three laws. The datum they are laws of is built out of its `poly`
field (`ComplexAnalytic.refineDatumPoly`)
and its `glue` (`ComplexAnalytic.refineDatumGlue`, both branches under a case split) ; the latter
a function of a choice of extra factor and unit, which
`ComplexAnalytic.exists_refineDatumCross` (`Other/Oka/Analytification/CrossMemberChoice.lean`) produces
at every ordered pair, algebraically and without saying that the overlap it refines to is the
geometric one ; and it reaches a glue data under the two conditions the file above adopts and no
law at all (`ComplexAnalytic.refineDatumGlueDataOfLaws`). **Nothing says a choice meets either
condition**, in either direction, and taxis #1287 is where that question lives. Nothing here is
about a scheme.
-/

/-- **A variable of the larger polynomial ring is either the new one or an old one.**

`Fin.lastCases` through the `ULift`. It is stated because the induction below cases on a variable,
and `ComplexAnalytic.localisationIncl` is a function rather than a pattern a tactic can see
through. -/
theorem eq_localisationVar_or_exists_localisationIncl (i : ULift.{u} (Fin (n + 1))) :
    i = localisationVar.{u} n ∨ ∃ j, i = localisationIncl.{u} n j := by
  obtain ⟨m⟩ := i
  induction m using Fin.lastCases with
  | last => exact Or.inl rfl
  | cast j => exact Or.inr ⟨ULift.up j, rfl⟩

/-- **Clearing the denominator.** A polynomial `q` in the extra variable, multiplied by a high
enough power of `f`, is a renamed polynomial of the base ; modulo the relation `t·f - 1`, which is
the correction term `r` in the statement.

**The name elides that correction term and the statement carries it.** There is no equation of
polynomials here: `t` is a free variable and `q = t` is already not renamed from anything. What is
true is the equation in `ℂ[x, t] ⧸ (t·f - 1)`, and the third existential is the witness that it
holds there.

The proof is `MvPolynomial.induction_on` and the three cases are the whole content:

* a constant, and an old variable, need no power of `f` at all;
* the **new** variable is where the relation is used, and it is used once ; `t · f = 1` modulo the
  relation, so multiplying by one more `f` turns a trailing `t` into nothing and the exponent goes
  up by one;
* a sum takes the sum of the exponents rather than their maximum, which is what makes the
  bookkeeping `ring` rather than a case split on which of the two is larger.

**`gⱼ` plays no part** ; the statement mentions only `f`, and the equations of the base are never
used. That is the reason it is stated before any point of `(A_f)^an` is mentioned: it is a fact
about the polynomial ring with one variable inverted, not about the analytic space. -/
theorem exists_pow_mul_eq_rename (q : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ) :
    ∃ (D : ℕ) (Q : MvPolynomial (ULift.{u} (Fin n)) ℂ)
      (r : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ),
      MvPolynomial.rename (localisationIncl.{u} n) f ^ D * q =
        MvPolynomial.rename (localisationIncl.{u} n) Q +
          (MvPolynomial.X (localisationVar.{u} n) *
            MvPolynomial.rename (localisationIncl.{u} n) f - 1) * r := by
  induction q using MvPolynomial.induction_on with
  | C c => exact ⟨0, MvPolynomial.C c, 0, by simp⟩
  | add p q hp hq =>
      obtain ⟨D₁, Q₁, r₁, h₁⟩ := hp
      obtain ⟨D₂, Q₂, r₂, h₂⟩ := hq
      refine ⟨D₁ + D₂, f ^ D₂ * Q₁ + f ^ D₁ * Q₂,
        MvPolynomial.rename (localisationIncl.{u} n) f ^ D₂ * r₁ +
          MvPolynomial.rename (localisationIncl.{u} n) f ^ D₁ * r₂, ?_⟩
      have e₁ : MvPolynomial.rename (localisationIncl.{u} n) f ^ (D₁ + D₂) * p =
          MvPolynomial.rename (localisationIncl.{u} n) f ^ D₂ *
            (MvPolynomial.rename (localisationIncl.{u} n) f ^ D₁ * p) := by ring
      have e₂ : MvPolynomial.rename (localisationIncl.{u} n) f ^ (D₁ + D₂) * q =
          MvPolynomial.rename (localisationIncl.{u} n) f ^ D₁ *
            (MvPolynomial.rename (localisationIncl.{u} n) f ^ D₂ * q) := by ring
      rw [mul_add, e₁, e₂, h₁, h₂]
      simp only [map_add, map_mul, map_pow]
      ring
  | mul_X p i hp =>
      obtain ⟨D, Q, r, h⟩ := hp
      rcases eq_localisationVar_or_exists_localisationIncl.{u} i with rfl | ⟨j, rfl⟩
      · refine ⟨D + 1, Q,
          r + MvPolynomial.rename (localisationIncl.{u} n) Q +
            (MvPolynomial.X (localisationVar.{u} n) *
              MvPolynomial.rename (localisationIncl.{u} n) f - 1) * r, ?_⟩
        have e : MvPolynomial.rename (localisationIncl.{u} n) f ^ (D + 1) *
            (p * MvPolynomial.X (localisationVar.{u} n)) =
            (MvPolynomial.rename (localisationIncl.{u} n) f ^ D * p) *
              ((MvPolynomial.X (localisationVar.{u} n) *
                MvPolynomial.rename (localisationIncl.{u} n) f - 1) + 1) := by ring
        rw [e, h]; ring
      · refine ⟨D, Q * MvPolynomial.X j, r * MvPolynomial.X (localisationIncl.{u} n j), ?_⟩
        have e : MvPolynomial.rename (localisationIncl.{u} n) f ^ D *
            (p * MvPolynomial.X (localisationIncl.{u} n j)) =
            (MvPolynomial.rename (localisationIncl.{u} n) f ^ D * p) *
              MvPolynomial.X (localisationIncl.{u} n j) := by ring
        rw [e, h]
        simp only [map_mul, MvPolynomial.rename_X]
        ring

/-- **`f` vanishes nowhere on `(A_f)^an`**, which is what the last equation of
`ComplexAnalytic.localisationPresentation` says at a point.

`ComplexAnalytic.range_base_localisationProj` is the same fact read downstairs ; the image of the
projection is `D(f)` ; and this is it read upstairs, where it is what says the multiplier of
`ComplexAnalytic.exists_pow_mul_eq_rename` cannot be zero. -/
theorem eval_rename_localisationIncl_ne_zero
    (w : AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f)) :
    MvPolynomial.eval (w.1.1 : ULift.{u} (Fin (n + 1)) → ℂ)
      (MvPolynomial.rename (localisationIncl.{u} n) f) ≠ 0 := by
  have hrel := (mem_zeroLocus_polySection_iff.{u} (localisationPresentation.{u} g f) w.1).1 w.2
    (Fin.last k)
  rw [localisationPresentation_last] at hrel
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X, map_one,
    sub_eq_zero] at hrel
  intro hcon
  rw [hcon, mul_zero] at hrel
  exact zero_ne_one hrel

/-- **Every distinguished open of `(A_f)^an` is cut out by a renamed polynomial of the base.**

The converse of `ComplexAnalytic.localisationOpen_rename`, and the sharper of the two forms: it
produces the polynomial rather than an open, so a caller that has to *supply* a polynomial ; the
`poly` field of `Other/Oka/Analytification/AffineCover.lean`'s cover datum ; can take this one.

`ComplexAnalytic.exists_pow_mul_eq_rename` and nothing else. At a point of `(A_f)^an` the relation
kills the correction term and the power of `f` is non-zero by
`ComplexAnalytic.eval_rename_localisationIncl_ne_zero`, so `q` and the renamed `Q` vanish at
exactly the same points. **`D` disappears from the statement** because a non-vanishing locus does
not see a non-vanishing factor; it is the exponent that made the algebra work and it is not part
of the geometry.

**This is the geometric half of what that equation says, and the algebraic half is elsewhere.**
Read modulo the ideal rather than at a point, the same equation says `q` and the renamed `Q` are
*associates* ; `ComplexAnalytic.exists_mk_rename_eq`, in
`Other/Oka/Analytification/LocalisationIndependence.lean`, which keeps the unit this statement drops. A
consumer that needs to identify the two *presentations* rather than the two opens needs that one:
a divisibility does not follow from an equality of non-vanishing loci over a general presented
`ℂ`-algebra. -/
theorem exists_localisationOpen_eq_rename (q : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ) :
    ∃ Q : MvPolynomial (ULift.{u} (Fin n)) ℂ,
      localisationOpen.{u} (localisationPresentation.{u} g f) q =
        localisationOpen.{u} (localisationPresentation.{u} g f)
          (MvPolynomial.rename (localisationIncl.{u} n) Q) := by
  obtain ⟨D, Q, r, h⟩ := exists_pow_mul_eq_rename.{u} f q
  refine ⟨Q, Opens.ext (Set.ext fun w ↦ ?_)⟩
  change w ∈ localisationOpen.{u} (localisationPresentation.{u} g f) q ↔
    w ∈ localisationOpen.{u} (localisationPresentation.{u} g f)
      (MvPolynomial.rename (localisationIncl.{u} n) Q)
  rw [mem_localisationOpen_iff, mem_localisationOpen_iff]
  have hrel := (mem_zeroLocus_polySection_iff.{u} (localisationPresentation.{u} g f) w.1).1 w.2
    (Fin.last k)
  rw [localisationPresentation_last] at hrel
  have hev := congrArg (MvPolynomial.eval (w.1.1 : ULift.{u} (Fin (n + 1)) → ℂ)) h
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_add, hrel, zero_mul,
    add_zero] at hev
  rw [← hev, mul_ne_zero_iff]
  exact ⟨fun hne ↦ ⟨pow_ne_zero D (eval_rename_localisationIncl_ne_zero.{u} g f w), hne⟩, And.right⟩

/-- **Every distinguished open of `(A_f)^an` is the preimage of a distinguished open of `X^an`**,
which is the geometric reading of the lemma above and the exact converse of
`ComplexAnalytic.localisationOpen_rename`.

Together the two say that the distinguished opens of `(A_f)^an` and the distinguished opens of
`X^an` correspond under the projection ; not bijectively, since `D(Q)` and `D(Q · f)` have the same
preimage, but surjectively in this direction, which is the half a construction needs. -/
theorem exists_localisationOpen_eq_comap (q : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ) :
    ∃ Q : MvPolynomial (ULift.{u} (Fin n)) ℂ,
      localisationOpen.{u} (localisationPresentation.{u} g f) q =
        (Opens.map (localisationProj.{u} g f).toLRSHom.base).obj (localisationOpen.{u} g Q) := by
  obtain ⟨Q, hQ⟩ := exists_localisationOpen_eq_rename.{u} g f q
  exact ⟨Q, hQ.trans (localisationOpen_rename.{u} g f Q)⟩

/-! ### The projection is an open immersion -/

/-- **The projection factors as the comparison isomorphism followed by the inclusion of `D(f)`**,
at the locally-ringed-space spelling.

`ComplexAnalytic.localisationIso_hom_ofRestrict` is this equation one level up, between morphisms
of analytic spaces; this is it after `ComplexAnalytic.AnalyticSpace.Hom.toLRSHom`, which is the
form both statements below consume, since `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion`
and `AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict` are about locally ringed spaces. -/
theorem toLRSHom_localisationProj :
    (localisationProj.{u} g f).toLRSHom =
      (localisationIso.{u} g f).hom.toLRSHom ≫
        ((AnalyticSpace.analytification.{u} g).ofRestrict (localisationOpen.{u} g f)).toLRSHom :=
  congrArg AnalyticSpace.Hom.toLRSHom (localisationIso_hom_ofRestrict.{u} g f).symm

/-- **The comparison isomorphism is an isomorphism of locally ringed spaces.** It is carried
across by `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`; stated because both
statements below need it as an instance and instance search does not produce it from the
`Iso`. -/
theorem isIso_toLRSHom_localisationIso_hom :
    IsIso ((localisationIso.{u} g f).hom.toLRSHom) :=
  (AnalyticSpace.forgetToLocallyRingedSpace.{u}.mapIso (localisationIso.{u} g f)).isIso_hom

/-- **The projection `(A_f)^an ⟶ X^an` is an open immersion of locally ringed spaces.**

This is what a glue data wants. `AlgebraicGeometry.LocallyRingedSpace.GlueData` is
`CategoryTheory.GlueData` together with one extra field, `f_open`, asserting that each `f i j` is
an open immersion, and in the glue data an affine cover produces `f i j` **is** this projection.

It is `ComplexAnalytic.localisationIso_hom_ofRestrict` read as a factorisation:
`localisationProj` is an isomorphism followed by the inclusion of an open subspace, and both of
those are open immersions.

Two seams are crossed by hand rather than by instance search, and neither is avoidable:

* `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict` supplies the inclusion's
  instance. Searching for it directly at this spelling **fails** ; see that lemma's docstring for
  the measurement and the reason ; so it is introduced as an ascribed `haveI`, where the term
  crosses the seam even though the search does not.
* `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` carries the isomorphism, which is
  where `IsIso` comes from; `ComplexAnalytic.AnalyticSpace.Hom.toLRSHom` of a composite is a
  composite by `rfl`, since the category instance is defined that way, and no lemma in `Other/Oka/`
  states it. -/
theorem isOpenImmersion_localisationProj :
    LocallyRingedSpace.IsOpenImmersion (localisationProj.{u} g f).toLRSHom := by
  haveI : LocallyRingedSpace.IsOpenImmersion
      ((AnalyticSpace.analytification.{u} g).ofRestrict (localisationOpen.{u} g f)).toLRSHom :=
    LocallyRingedSpace.isOpenImmersion_ofRestrict.{u} _ (localisationOpen.{u} g f)
  haveI := isIso_toLRSHom_localisationIso_hom.{u} g f
  rw [toLRSHom_localisationProj]
  infer_instance

/-- **The image of the projection is exactly `D(f)`.**

`ComplexAnalytic.range_base_localisationProj_subset` is the containment, which is all the
universal property needs; this is the equality, which is what an open-immersion lift needs ; the
side condition of `AlgebraicGeometry.LocallyRingedSpace.liftRestrict` and of Mathlib's
`IsOpenImmersion.lift` is a containment *in* this range, so it has to be rewritten into a
containment in `D(f)` before anything about `D(f)` can discharge it.

The isomorphism half of `ComplexAnalytic.toLRSHom_localisationProj` is surjective on points
(`AlgebraicGeometry.LocallyRingedSpace.homeoOfIso`), so the image is the image of the inclusion,
which is `AlgebraicGeometry.LocallyRingedSpace.range_ofRestrict`.

**The last step is `exact` and not `rw`, and that is not a stylistic choice.** `rw
[LocallyRingedSpace.range_ofRestrict]` here fails with *did not find an occurrence of the
pattern*: the goal is headed by `ComplexAnalytic.AnalyticSpace.Hom.toLRSHom` and the lemma by
`AlgebraicGeometry.LocallyRingedSpace.ofRestrict`, which are `rfl`-equal and are different
discrimination-tree keys ; the same seam
`AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict` records for instance search.
The term crosses it; neither instance search nor `rw`'s pattern match does. -/
theorem range_base_localisationProj :
    Set.range (localisationProj.{u} g f).toLRSHom.base =
      (localisationOpen.{u} g f : Set (AnalyticSpace.analytification.{u} g)) := by
  haveI := isIso_toLRSHom_localisationIso_hom.{u} g f
  have hs : Set.range (localisationIso.{u} g f).hom.toLRSHom.base = Set.univ :=
    Set.range_eq_univ.2
      (LocallyRingedSpace.homeoOfIso (asIso ((localisationIso.{u} g f).hom.toLRSHom))).surjective
  rw [toLRSHom_localisationProj, LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp,
    hs, Set.image_univ]
  exact (AnalyticSpace.analytification.{u} g).toLocallyRingedSpace.range_ofRestrict
    (localisationOpen.{u} g f)

/-- **And its image downstairs is `D(f) ⊓ D(f')`.**

`ComplexAnalytic.localisationOpen_rename` says the open upstairs is a *preimage*; a consumer that
has to say where a subset of `(A_f)^an` lands in `X^an` needs the image, and the image of a
preimage is the set met with the range. So this is that lemma and
`ComplexAnalytic.range_base_localisationProj` ; **the equality and not
`ComplexAnalytic.range_base_localisationProj_subset`**, because the containment gives one
inclusion of the two sets and the other has to produce a point of `(A_f)^an` over a point of
`D(f) ⊓ D(f')`.

Stated as an image of a set rather than as an `Opens`: `Set.image_preimage_eq_inter_range` is what
it is, the two lemmas it composes are already stated at that level, and every consumer on the
refinement line is asking where a *subset* goes. -/
theorem image_base_localisationProj_localisationOpen_rename
    (f' : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    (localisationProj.{u} g f).toLRSHom.base ''
        (localisationOpen.{u} (localisationPresentation.{u} g f)
          (MvPolynomial.rename (localisationIncl.{u} n) f') :
          Set (AnalyticSpace.analytification.{u} (localisationPresentation.{u} g f))) =
      ((localisationOpen.{u} g f ⊓ localisationOpen.{u} g f' : Opens _) :
        Set (AnalyticSpace.analytification.{u} g)) := by
  rw [localisationOpen_rename.{u} g f f']
  change (localisationProj.{u} g f).toLRSHom.base ''
      ((localisationProj.{u} g f).toLRSHom.base ⁻¹'
        (localisationOpen.{u} g f' : Set (AnalyticSpace.analytification.{u} g))) = _
  rw [Set.image_preimage_eq_inter_range, range_base_localisationProj.{u} g f]
  exact Set.inter_comm _ _

/-! ### The presented algebra is the localisation

Everything above is about `ComplexAnalytic.localisationPresentation` as a tuple of polynomials.
This section says what the tuple *presents*: `ℂ[x, t] ⧸ (g, t·f - 1)` is the localisation of
`ℂ[x] ⧸ (g)` away from the image of `f`. The general statement, for any base ring and any ideal,
is `MvPolynomial.isLocalization_away_quotient_awayIdeal` in
`Other/Oka/RingTheory/MvPolynomial/Localization.lean`; it is stated there with the new variable called
`none`, so all that is left here is the reindexing that identifies `Fin (n + 1)` with
`Option (Fin n)` in the way `ComplexAnalytic.localisationIncl` and
`ComplexAnalytic.localisationVar` do.
-/

/-- **The reindexing that names the new variable `none`**: `Fin (n + 1)` as `Option (Fin n)`,
sending `ComplexAnalytic.localisationVar` there and `ComplexAnalytic.localisationIncl` to `some`,
under the `ULift` this development carries on its variable types. -/
def localisationVarEquiv (n : ℕ) : ULift.{u} (Fin (n + 1)) ≃ Option (ULift.{u} (Fin n)) :=
  Equiv.ulift.trans (finSuccEquivLast.trans (Equiv.optionCongr Equiv.ulift.symm))

@[simp]
theorem localisationVarEquiv_localisationVar :
    localisationVarEquiv.{u} n (localisationVar.{u} n) = none := by
  simp [localisationVarEquiv, localisationVar]

@[simp]
theorem localisationVarEquiv_localisationIncl (i : ULift.{u} (Fin n)) :
    localisationVarEquiv.{u} n (localisationIncl.{u} n i) = some i := by
  simp [localisationVarEquiv, localisationIncl, Equiv.optionCongr]

/-- Under the reindexing, the equations of `ComplexAnalytic.localisationPresentation` are the
generators of `MvPolynomial.awayIdeal`: the old ones renamed along `some`, and `t·f - 1`. -/
theorem rename_comp_localisationPresentation :
    MvPolynomial.rename (localisationVarEquiv.{u} n) ∘ localisationPresentation.{u} g f =
      Fin.snoc (MvPolynomial.rename (some (α := ULift.{u} (Fin n))) ∘ g)
        (MvPolynomial.X none * MvPolynomial.rename some f - 1 :
          MvPolynomial (Option (ULift.{u} (Fin n))) ℂ) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp [MvPolynomial.rename_rename, Function.comp_def]
  · intro i
    simp [MvPolynomial.rename_rename, Function.comp_def]

/-- **The reindexing carries the ideal of `ComplexAnalytic.localisationPresentation` to
`MvPolynomial.awayIdeal`.** This is the only thing about the identification that is specific to
this development; everything else is the general statement in the mirror tree. -/
theorem map_presentationIdeal_localisationPresentation :
    (presentationIdeal.{u} (localisationPresentation.{u} g f)).map
        (MvPolynomial.rename (localisationVarEquiv.{u} n)) =
      MvPolynomial.awayIdeal (presentationIdeal.{u} g) f := by
  rw [presentationIdeal, Ideal.map_span, ← Set.range_comp,
    rename_comp_localisationPresentation, Fin.range_snoc, Ideal.span_insert, Set.range_comp,
    MvPolynomial.awayIdeal, presentationIdeal, Ideal.map_span, sup_comm]

/-- The reindexing, as an isomorphism of the two quotients. -/
def localisationRenameEquiv :
    PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f) ≃ₐ[ℂ]
      (MvPolynomial (Option (ULift.{u} (Fin n))) ℂ ⧸
        MvPolynomial.awayIdeal (presentationIdeal.{u} g) f) :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv ℂ (localisationVarEquiv.{u} n))
    (map_presentationIdeal_localisationPresentation.{u} g f).symm

/-- **`ℂ[x, t] ⧸ (g, t·f - 1)` is the localisation of `ℂ[x] ⧸ (g)` away from the image of `f`.**

The identification the file's `## What is not here` used to disclaim. It is what turns an
isomorphism of localisations ; which is what a scheme hands you at an overlap of two affine
members ; into an isomorphism of the algebras two `ComplexAnalytic.localisationPresentation`s
present, which is what `Other/Oka/Analytification/AffineCover.lean`'s `glue` field asks for.

An isomorphism rather than an `IsLocalization.Away` instance on this type, deliberately: the
instance is stated in the mirror tree, on the ring with the new variable called `none`, and
putting a second one here would mean an `Algebra (ComplexAnalytic.PresentedAlgebra n k g)`
instance on `ComplexAnalytic.PresentedAlgebra (n + 1) (k + 1) …` ; an instance keyed on a type
this development uses everywhere, bought for a universal property that
`ComplexAnalytic.localisationRenameEquiv` already reaches in one step. -/
def localisationPresentedAlgebraEquiv :
    PresentedAlgebra.{u} (n + 1) (k + 1) (localisationPresentation.{u} g f) ≃ₐ[ℂ]
      Localization.Away (Ideal.Quotient.mk (presentationIdeal.{u} g) f) :=
  (localisationRenameEquiv.{u} g f).trans (MvPolynomial.awayQuotientEquiv _ _)

end

end ComplexAnalytic

end
