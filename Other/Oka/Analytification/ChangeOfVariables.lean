/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.UniversalProperty

/-!
# Presentation-independence of the analytification

`Other/Oka/Analytification/UniversalProperty.lean` proves that for polynomials `g₁, …, g_k` in `n`
variables, morphisms `Z ⟶ X^an` correspond to tuples of `n` global sections of `𝒪_Z` satisfying
the equations, and deduces that `X^an` depends only on the **ideal** the `gⱼ` generate. That is
independence of the *generators*, inside one fixed polynomial ring.

**This file removes the fixed polynomial ring.** A `ℂ`-algebra map `ℂ[y] ⧸ J → ℂ[x] ⧸ I` induces a
morphism of analytifications the other way (`ComplexAnalytic.analytificationMap`), functorially,
**with no relation assumed between the two numbers of variables or the two numbers of equations**.
So two presentations of the same finitely generated `ℂ`-algebra ; in different numbers of
variables, with different numbers of relations ; have isomorphic analytifications:
`ComplexAnalytic.analytificationIsoOfPresHom`.

Together with the universal property this is presentation-independence of the analytification on
objects: `X^an` depends only on the algebra `ℂ[x] ⧸ I`, not on how it was presented.

## How little there is to it, and why that is the surprise

The route one expects ; compare two subspaces of two different `ℂ^n`, transport along a change of
coordinates ; is not taken and is not needed. **The universal property does all the work**, and
the mechanism is one lemma:

```
ComplexAnalytic.eval₂Hom_transported :
  MvPolynomial.eval₂Hom (analytification g).algebraMap (transported ψ)
    = ((quotientToGlobal g).comp ψ.toRingHom).comp (Ideal.Quotient.mk (presentationIdeal g'))
```

Substituting the *transported* tuple into a polynomial of the target presentation is applying the
`ℂ`-algebra map to its class. Once that is known, `g' j ↦ 0` because `g' j` is in the ideal being
quotiented, so the transported tuple satisfies the target equations and
`ComplexAnalytic.liftHom` produces the morphism. `n` and `n'` never meet.

Both sides of that identity are ring homomorphisms out of `MvPolynomial`, so it is
`MvPolynomial.ringHom_ext` ; the same tool as the substitution formula it rests on. On a constant
it is `ComplexAnalytic.quotientToGlobal_mk_C`; on a variable it is `rfl`.

## Functoriality, and what it buys

`ComplexAnalytic.analytificationMap_id` and `ComplexAnalytic.analytificationMap_comp` are proved
from `ComplexAnalytic.hom_ext_analytification` and the naturality of
`ComplexAnalytic.quotientToGlobal` along the induced morphism
(`ComplexAnalytic.Γ_map_analytificationMap_comp_quotientToGlobal`). They are what turn an
isomorphism of presented algebras into an isomorphism of analytifications, which is the point.

## What is still not here

* **A functor.** `ComplexAnalytic.analytificationMap` is contravariant, identity-preserving and
  composition-preserving, so the data of one exists, but nothing here is stated as a
  `CategoryTheory.Functor` and the assignment on objects still takes a *tuple* rather than a
  finitely presented `ℂ`-algebra. That is `Other/Oka/Analytification/Functor.lean`, which bundles
  `ComplexAnalytic.PresHom` as a category and this file's two functoriality lemmas as
  `ComplexAnalytic.analytificationFunctor`, and then removes the presentation from the source.
  The presentation is not *constructed* there ; the earlier version of this paragraph said it
  would have to be ; but chosen, by the inverse of an equivalence of categories.
* **The comparison with `Spec`.** `ComplexAnalytic.analytificationToSpec` is not shown natural in
  the presentation *here*; it is, in `Other/Oka/Analytification/Comparison.lean`, and the ring-level
  square it is `Spec` of is `ComplexAnalytic.Γ_map_analytificationMap_comp_quotientToGlobal`
  below ; proved for functoriality rather than for that.
* **Anything analytic.** Every proof here is `MvPolynomial.ringHom_ext` and category-theoretic
  bookkeeping; the analytic content is upstream, in the universal property.

## Main definitions

- `ComplexAnalytic.PresHom`: a `ℂ`-algebra map between two presented algebras, spelled as a ring
  map plus the commutation it must satisfy ; **there is no `Algebra ℂ` instance on these
  quotients and none is manufactured.**
- `ComplexAnalytic.PresHom.ofRename`: **a renaming of the variables carrying the target's
  relations into the source's ideal is such a map** ; the family of `PresHom`s an explicit
  change of coordinates arrives in, and the only construction here that produces one with
  content in it.
- `ComplexAnalytic.transported`: the tuple of sections of `𝒪_{X^an}` that a `PresHom` names.
- `ComplexAnalytic.analytificationMap`: **the induced morphism of analytifications.**
- `ComplexAnalytic.analytificationIsoOfPresHom`: **two presentations of one algebra have
  isomorphic analytifications**, with no relation between their numbers of variables.

## Main results

- `ComplexAnalytic.eval₂Hom_transported`: substituting the transported tuple is applying the
  `ℂ`-algebra map.
- `ComplexAnalytic.PresHom.ofRename_comp_ofRename`: two renamings inverse to each other give
  mutually inverse `ℂ`-algebra maps, which is what makes such a pair an isomorphism of
  presentations (`ComplexAnalytic.Presentation.isoOfRename`, in
  `Other/Oka/Analytification/Functor.lean`, where presentations have a category).
- `ComplexAnalytic.rename_mem_presentationIdeal`: a renaming carrying the generators of one
  presentation's ideal into another's carries **every element** of it there.
- `ComplexAnalytic.PresHom.ofRename_comp`: **two renamings compose to the renaming of the
  composite** ; the general law, of which the inverse-pair statement above is not a case.
- `ComplexAnalytic.Γ_map_analytificationMap_comp_quotientToGlobal`: `quotientToGlobal` is natural
  along the induced morphism.
- `ComplexAnalytic.analytificationMap_id` and `ComplexAnalytic.analytificationMap_comp`:
  **functoriality.**

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

noncomputable section

variable {n n' n'' k k' k'' : ℕ}

/-! ### Constants -/

/-- **A constant of `ℂ[x] ⧸ I`, read as a global section of `𝒪_{X^an}`, is that constant.**

`ComplexAnalytic.quotientToGlobal` was built in `Other/Oka/Analytification/Presentation.lean` before
the analytification had a `ℂ`-linear structure map named beside it; this is the compatibility,
and it is `ComplexAnalytic.polyToGlobal_eq_eval₂Hom` at a constant. Both halves of this file need
it. -/
theorem quotientToGlobal_mk_C (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) (c : ℂ) :
    quotientToGlobal.{u} g (Ideal.Quotient.mk (presentationIdeal.{u} g) (MvPolynomial.C c)) =
      (AnalyticSpace.analytification.{u} g).algebraMap c :=
  (RingHom.congr_fun (polyToGlobal_eq_eval₂Hom.{u} g) (MvPolynomial.C c)).trans
    (MvPolynomial.eval₂Hom_C _ _ c)

/-- **A variable of `ℂ[x] ⧸ I`, read as a global section of `𝒪_{X^an}`, is the corresponding
coordinate of `X^an`.** The companion of `ComplexAnalytic.quotientToGlobal_mk_C`. -/
theorem quotientToGlobal_mk_X (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (i : ULift.{u} (Fin n)) :
    quotientToGlobal.{u} g (Ideal.Quotient.mk (presentationIdeal.{u} g) (MvPolynomial.X i)) =
      analytificationCoord.{u} g i :=
  (RingHom.congr_fun (polyToGlobal_eq_eval₂Hom.{u} g) (MvPolynomial.X i)).trans
    (MvPolynomial.eval₂Hom_X' _ _ i)

/-! ### `ℂ`-algebra maps of presented algebras -/

/-- A `ℂ`-algebra map between two presented algebras, spelled as a ring map together with the
commutation it has to satisfy. -/
structure PresHom (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (g' : Fin k' → MvPolynomial (ULift.{u} (Fin n')) ℂ) where
  /-- The underlying ring map, which goes the other way from the induced morphism of spaces. -/
  toRingHom : PresentedAlgebra.{u} n' k' g' →+* PresentedAlgebra.{u} n k g
  /-- It fixes the constants. -/
  commutes : toRingHom.comp (presentedAlgebraMap.{u} g') = presentedAlgebraMap.{u} g

variable {g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ}
  {g' : Fin k' → MvPolynomial (ULift.{u} (Fin n')) ℂ}
  {g'' : Fin k'' → MvPolynomial (ULift.{u} (Fin n'')) ℂ}

/-- Two `ℂ`-algebra maps of presented algebras with the same underlying ring map are equal: the
commutation is a proposition. -/
@[ext]
theorem PresHom.ext {ψ χ : PresHom.{u} g g'} (h : ψ.toRingHom = χ.toRingHom) : ψ = χ := by
  cases ψ; cases χ; simp_all

/-- The identity `ℂ`-algebra map. -/
def PresHom.id (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) : PresHom.{u} g g :=
  ⟨RingHom.id _, RingHom.id_comp _⟩

/-- Composition, in the order the induced morphisms of spaces compose. -/
def PresHom.comp (ψ : PresHom.{u} g g') (χ : PresHom.{u} g' g'') : PresHom.{u} g g'' :=
  ⟨ψ.toRingHom.comp χ.toRingHom, by
    rw [RingHom.comp_assoc, χ.commutes, ψ.commutes]⟩

/-! ### `ℂ`-algebra maps from a renaming of the variables

Nothing above produces a `ComplexAnalytic.PresHom` with any content in it: the two constructions
are the identity and composition. This section produces the standard family, a map of *variables*
sending each relation of the target presentation into the ideal of the source one ; which is what
a change of coordinates is. `ComplexAnalytic.localisationPresHom`, the structure map `A ⟶ A_f`, is
one of these, at `ComplexAnalytic.localisationIncl`. -/

/-- **A renaming of the variables carrying the target's relations into the source's ideal is a
`ℂ`-algebra map of the presented algebras.**

Note the direction, which is the one the rest of the file runs in: the ring map of a
`ComplexAnalytic.PresHom g g'` goes `ℂ[y] ⧸ (g') → ℂ[x] ⧸ (g)`, so `σ` renames the variables of
the *target* presentation `g'` into those of the *source* `g`, and the hypothesis is about
`g' j` and not about `g j`.

The commutation is `MvPolynomial.rename_C`: a renaming fixes the constants, which is exactly
what the field demands. -/
def PresHom.ofRename (σ : ULift.{u} (Fin n') → ULift.{u} (Fin n))
    (h : ∀ j, MvPolynomial.rename σ (g' j) ∈ presentationIdeal.{u} g) :
    PresHom.{u} g g' where
  toRingHom :=
    Ideal.Quotient.lift (presentationIdeal.{u} g')
      ((Ideal.Quotient.mk (presentationIdeal.{u} g)).comp
        (MvPolynomial.rename σ : _ →ₐ[ℂ] _).toRingHom)
      (by
        have hle : presentationIdeal.{u} g' ≤
            RingHom.ker ((Ideal.Quotient.mk (presentationIdeal.{u} g)).comp
              (MvPolynomial.rename σ : _ →ₐ[ℂ] _).toRingHom) := by
          rw [presentationIdeal, Ideal.span_le]
          rintro _ ⟨j, rfl⟩
          simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using h j
        exact fun a ha ↦ hle ha)
  commutes := by
    refine RingHom.ext fun c ↦ ?_
    simp [presentedAlgebraMap]

/-- The value of `ComplexAnalytic.PresHom.ofRename` on the class of a polynomial: `rfl`, stated
as a `simp` lemma so that a call site need not unfold the definition. -/
@[simp]
theorem PresHom.ofRename_toRingHom_mk (σ : ULift.{u} (Fin n') → ULift.{u} (Fin n))
    (h : ∀ j, MvPolynomial.rename σ (g' j) ∈ presentationIdeal.{u} g)
    (p : MvPolynomial (ULift.{u} (Fin n')) ℂ) :
    (PresHom.ofRename.{u} σ h).toRingHom (Ideal.Quotient.mk (presentationIdeal.{u} g') p) =
      Ideal.Quotient.mk (presentationIdeal.{u} g) (MvPolynomial.rename σ p) :=
  rfl

/-- **Two renamings inverse to each other give mutually inverse `ℂ`-algebra maps.**

Only `σ ∘ τ = id` is assumed, and only the composite in that order is computed; applying it
twice, with the two hypotheses swapped, is what an isomorphism needs. Both sides are ring
maps out of a quotient of a polynomial ring, so the proof is `Ideal.Quotient.ringHom_ext`
followed by `MvPolynomial.ringHom_ext`, and the variable case is the hypothesis. -/
theorem PresHom.ofRename_comp_ofRename (σ : ULift.{u} (Fin n') → ULift.{u} (Fin n))
    (h : ∀ j, MvPolynomial.rename σ (g' j) ∈ presentationIdeal.{u} g)
    (τ : ULift.{u} (Fin n) → ULift.{u} (Fin n'))
    (h' : ∀ j, MvPolynomial.rename τ (g j) ∈ presentationIdeal.{u} g')
    (hστ : σ ∘ τ = _root_.id) :
    (PresHom.ofRename.{u} σ h).comp (PresHom.ofRename.{u} τ h') = PresHom.id.{u} g := by
  refine PresHom.ext (Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c ↦ ?_)
    (fun i ↦ ?_)))
  · simp [PresHom.comp, PresHom.id]
  · have hi : σ (τ i) = i := congrFun hστ i
    simp [PresHom.comp, PresHom.id, hi]

/-- **A renaming that carries each relation of `g'` into the ideal of `g` carries the whole ideal
of `g'` into it.**

The hypothesis of `ComplexAnalytic.PresHom.ofRename` is about the generators; this is the same
statement about every element, which is what a *composite* of two such renamings needs ; the
middle presentation's ideal is met at an arbitrary element and not at a generator.

`Ideal.span` induction, with the three closure cases discharged by `map_add`, `map_mul` and the
ideal's own closure properties. It is stated here rather than beside
`ComplexAnalytic.presentationIdeal` in `Other/Oka/Analytification/Presentation.lean` because it mentions
two presentations and a rename between them, and that file has neither. -/
theorem rename_mem_presentationIdeal (σ : ULift.{u} (Fin n') → ULift.{u} (Fin n))
    (h : ∀ j, MvPolynomial.rename σ (g' j) ∈ presentationIdeal.{u} g)
    {p : MvPolynomial (ULift.{u} (Fin n')) ℂ} (hp : p ∈ presentationIdeal.{u} g') :
    MvPolynomial.rename σ p ∈ presentationIdeal.{u} g := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨j, rfl⟩
    exact h j
  · simp
  · intro x y _ _ hx hy
    simpa using Ideal.add_mem _ hx hy
  · intro a x _ hx
    simpa using Ideal.mul_mem_left _ _ hx

/-- **Two renamings compose to the renaming of the composite.**

The general composition law for `ComplexAnalytic.PresHom.ofRename`, which
`ComplexAnalytic.PresHom.ofRename_comp_ofRename` above is *not*: that one assumes `σ ∘ τ = id` and
concludes `ComplexAnalytic.PresHom.id`, so it says nothing about a composite of two renamings that
is not an identity ; a tower of presentations, each adjoining variables to the one below, is
exactly that case.

The third hypothesis is what `ComplexAnalytic.rename_mem_presentationIdeal` above supplies, in one
line, from the first two; it is an argument rather than a proof term in the statement so that the
statement reads as a law about `ofRename` and not about a particular way of proving its side
condition. Which proof is supplied is immaterial ; `h''` occurs only under `ofRename`, whose value
does not depend on it.

Both sides are ring maps out of a quotient, so the proof is `Ideal.Quotient.ringHom_ext` and then
one element; the variable case of the composite is `MvPolynomial.rename_rename`, which is where the
`σ ∘ τ` on the right-hand side comes from. -/
theorem PresHom.ofRename_comp (σ : ULift.{u} (Fin n') → ULift.{u} (Fin n))
    (h : ∀ j, MvPolynomial.rename σ (g' j) ∈ presentationIdeal.{u} g)
    (τ : ULift.{u} (Fin n'') → ULift.{u} (Fin n'))
    (h' : ∀ j, MvPolynomial.rename τ (g'' j) ∈ presentationIdeal.{u} g')
    (h'' : ∀ j, MvPolynomial.rename (σ ∘ τ) (g'' j) ∈ presentationIdeal.{u} g) :
    (PresHom.ofRename.{u} σ h).comp (PresHom.ofRename.{u} τ h') =
      PresHom.ofRename.{u} (σ ∘ τ) h'' := by
  refine PresHom.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun p ↦ ?_))
  simp [PresHom.comp, MvPolynomial.rename_rename]

/-! ### The induced morphism of analytifications -/

/-- The `n'` global sections of `𝒪_{X^an_g}` that a `PresHom` names: the images of the variables
of the target presentation. -/
def transported (ψ : PresHom.{u} g g') :
    ULift.{u} (Fin n') → (AnalyticSpace.analytification.{u} g).presheaf.obj (op ⊤) :=
  fun i ↦ quotientToGlobal.{u} g (ψ.toRingHom
    (Ideal.Quotient.mk (presentationIdeal.{u} g') (MvPolynomial.X i)))

/-- **Substituting the transported tuple into a polynomial of the target presentation is applying
the `ℂ`-algebra map to its class.**

This is the whole mechanism of this file. Both sides are ring homomorphisms out of
`MvPolynomial`, so `MvPolynomial.ringHom_ext` reduces it to constants ; where it is
`ComplexAnalytic.quotientToGlobal_mk_C` fed by the `PresHom`'s commutation ; and variables, where
it is `rfl` by the definition of `ComplexAnalytic.transported`.

Nothing here relates the two numbers of variables, which is why a change of variables costs no
more than a change of generators. -/
theorem eval₂Hom_transported (ψ : PresHom.{u} g g') :
    MvPolynomial.eval₂Hom (AnalyticSpace.analytification.{u} g).algebraMap
        (transported.{u} ψ) =
      ((quotientToGlobal.{u} g).comp ψ.toRingHom).comp
        (Ideal.Quotient.mk (presentationIdeal.{u} g')) := by
  refine (MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)).symm
  · refine Eq.trans ?_ (MvPolynomial.eval₂Hom_C
      (AnalyticSpace.analytification.{u} g).algebraMap (transported.{u} ψ) c).symm
    exact (congrArg (quotientToGlobal.{u} g) (RingHom.congr_fun ψ.commutes c)).trans
      (quotientToGlobal_mk_C.{u} g c)
  · exact Eq.trans rfl (MvPolynomial.eval₂Hom_X'
      (AnalyticSpace.analytification.{u} g).algebraMap (transported.{u} ψ) i).symm

/-- **The transported tuple satisfies the target equations.**

Immediate from `ComplexAnalytic.eval₂Hom_transported`: `g' j` lies in the ideal being quotiented,
so its class is zero and any ring map out of the quotient kills it. This is the hypothesis
`ComplexAnalytic.liftHom` needs, and it is the only thing that had to be checked. -/
theorem eval₂_transported_eq_zero (ψ : PresHom.{u} g g') (j : Fin k') :
    MvPolynomial.eval₂ (AnalyticSpace.analytification.{u} g).algebraMap
      (transported.{u} ψ) (g' j) = 0 :=
  (RingHom.congr_fun (eval₂Hom_transported.{u} ψ) (g' j)).trans
    ((congrArg ((quotientToGlobal.{u} g).comp ψ.toRingHom)
      ((Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span ⟨j, rfl⟩))).trans (map_zero _))

/-- **A `ℂ`-algebra map of presented algebras induces a morphism of analytifications**, in the
opposite direction, with no relation assumed between the two numbers of variables. -/
def analytificationMap (ψ : PresHom.{u} g g') :
    AnalyticSpace.analytification.{u} g ⟶ AnalyticSpace.analytification.{u} g' :=
  liftHom.{u} g' _ (transported.{u} ψ) (eval₂_transported_eq_zero.{u} ψ)

/-- The coordinate pullbacks of the induced morphism are the transported tuple: the defining
property of `ComplexAnalytic.analytificationMap`. -/
theorem coordPullback_analytificationMap_comp (ψ : PresHom.{u} g g') (i : ULift.{u} (Fin n')) :
    AnalyticSpace.coordPullback
        (analytificationMap.{u} ψ ≫ analytificationInclHom.{u} g') i = transported.{u} ψ i :=
  coordPullback_liftHom_comp.{u} g' _ _ _ i

/-! ### Functoriality -/

/-- **Pulling a section of `𝒪_{X^an_{g'}}` back along the induced morphism is applying the
`ℂ`-algebra map**: `quotientToGlobal` is natural. -/
theorem Γ_map_analytificationMap_comp_quotientToGlobal (ψ : PresHom.{u} g g') :
    (LocallyRingedSpace.Γ.map (analytificationMap.{u} ψ).toLRSHom.op).hom.comp
        (quotientToGlobal.{u} g') =
      (quotientToGlobal.{u} g).comp ψ.toRingHom := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_))
  · refine Eq.trans (congrArg (LocallyRingedSpace.Γ.map
      (analytificationMap.{u} ψ).toLRSHom.op).hom (quotientToGlobal_mk_C.{u} g' c)) ?_
    refine Eq.trans ((analytificationMap.{u} ψ).isCLinear c) ?_
    exact (quotientToGlobal_mk_C.{u} g c).symm.trans
      (congrArg (quotientToGlobal.{u} g) (RingHom.congr_fun ψ.commutes c).symm)
  · refine Eq.trans (congrArg (LocallyRingedSpace.Γ.map
      (analytificationMap.{u} ψ).toLRSHom.op).hom (quotientToGlobal_mk_X.{u} g' i)) ?_
    refine Eq.trans (AnalyticSpace.coordPullback_comp (analytificationMap.{u} ψ)
      (analytificationInclHom.{u} g') i).symm ?_
    exact coordPullback_analytificationMap_comp.{u} ψ i

/-- The tuple transported along a composite is the tuple transported along the second map, pulled
back along the morphism induced by the first. This is
`ComplexAnalytic.Γ_map_analytificationMap_comp_quotientToGlobal` at one element, and it is what
makes functoriality an application of `ComplexAnalytic.hom_ext_analytification`. -/
theorem transported_comp (ψ : PresHom.{u} g g') (χ : PresHom.{u} g' g'')
    (i : ULift.{u} (Fin n'')) :
    transported.{u} (ψ.comp χ) i =
      (LocallyRingedSpace.Γ.map (analytificationMap.{u} ψ).toLRSHom.op).hom
        (transported.{u} χ i) :=
  (RingHom.congr_fun (Γ_map_analytificationMap_comp_quotientToGlobal.{u} ψ)
    (χ.toRingHom (Ideal.Quotient.mk (presentationIdeal.{u} g'') (MvPolynomial.X i)))).symm

/-- **The identity `ℂ`-algebra map induces the identity morphism.** -/
@[simp]
theorem analytificationMap_id :
    analytificationMap.{u} (PresHom.id.{u} g) = 𝟙 (AnalyticSpace.analytification.{u} g) :=
  hom_ext_analytification.{u} g _ _ fun i ↦
    (coordPullback_analytificationMap_comp.{u} (PresHom.id.{u} g) i).trans
      ((quotientToGlobal_mk_X.{u} g i).trans
        (congrArg (fun m ↦ AnalyticSpace.coordPullback m i)
          (Category.id_comp (analytificationInclHom.{u} g)).symm))

/-- **The induced morphism of a composite is the composite of the induced morphisms**, in the
opposite order ; the assignment is contravariant. -/
@[simp]
theorem analytificationMap_comp (ψ : PresHom.{u} g g') (χ : PresHom.{u} g' g'') :
    analytificationMap.{u} (ψ.comp χ) =
      analytificationMap.{u} ψ ≫ analytificationMap.{u} χ :=
  hom_ext_analytification.{u} g'' _ _ fun i ↦
    (coordPullback_analytificationMap_comp.{u} (ψ.comp χ) i).trans
      ((transported_comp.{u} ψ χ i).trans
        (((congrArg (LocallyRingedSpace.Γ.map (analytificationMap.{u} ψ).toLRSHom.op).hom
            (coordPullback_analytificationMap_comp.{u} χ i)).symm.trans
          (AnalyticSpace.coordPullback_comp (analytificationMap.{u} ψ)
            (analytificationMap.{u} χ ≫ analytificationInclHom.{u} g'') i).symm).trans
          (congrArg (fun m ↦ AnalyticSpace.coordPullback m i)
            (Category.assoc _ _ _).symm)))

/-- **Two presentations of the same `ℂ`-algebra have isomorphic analytifications**, with no
relation assumed between their numbers of variables or their numbers of equations.

This is presentation-independence: `ComplexAnalytic.analytificationIsoOfPresentationIdealEq`
covers a change of *generators* inside one polynomial ring, and this covers a change of
*variables* as well. -/
def analytificationIsoOfPresHom (ψ : PresHom.{u} g g') (χ : PresHom.{u} g' g)
    (h₁ : ψ.toRingHom.comp χ.toRingHom = RingHom.id (PresentedAlgebra.{u} n k g))
    (h₂ : χ.toRingHom.comp ψ.toRingHom = RingHom.id (PresentedAlgebra.{u} n' k' g')) :
    AnalyticSpace.analytification.{u} g ≅ AnalyticSpace.analytification.{u} g' where
  hom := analytificationMap.{u} ψ
  inv := analytificationMap.{u} χ
  hom_inv_id :=
    (analytificationMap_comp.{u} ψ χ).symm.trans
      ((congrArg analytificationMap.{u} (PresHom.ext.{u} (g := g) (g' := g) h₁)).trans
        analytificationMap_id.{u})
  inv_hom_id :=
    (analytificationMap_comp.{u} χ ψ).symm.trans
      ((congrArg analytificationMap.{u} (PresHom.ext.{u} (g := g') (g' := g') h₂)).trans
        analytificationMap_id.{u})

end

end ComplexAnalytic

end
