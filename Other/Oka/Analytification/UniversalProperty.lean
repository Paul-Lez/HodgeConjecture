/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.Factorisation
public import Other.Oka.AnalyticSpace.HolomorphicMapGeneral
public import Other.Oka.Analytification.Presentation

/-!
# The universal property of the analytification of a presented affine `ℂ`-algebra

Fix polynomials `g₁, …, g_k ∈ ℂ[x₁, …, x_n]`. `Other/Oka/Analytification/Presentation.lean` builds the
complex analytic space `X^an = { z ∈ ℂ^n | g₁ z = ⋯ = g_k z = 0 }` and says, in its own module
docstring, that it provides **no universal property**: what it constructs depends on the tuple
`g` and not visibly on the algebra `ℂ[x]/(g)`. This file supplies the mapping property, and with
it the first instalment of presentation-independence.

For every complex analytic space `Z`, morphisms `Z ⟶ X^an` correspond to tuples of global
sections of `𝒪_Z` satisfying the equations:

```
Hom(Z, X^an)  ≃  { a : ULift (Fin n) → Γ(Z, 𝒪_Z) | ∀ j, gⱼ(a₁, …, a_n) = 0 }
```

the correspondence sending `ψ` to the coordinate pullbacks of `ψ` followed by the inclusion
`X^an ↪ ℂ^n`. That is `ComplexAnalytic.existsUnique_hom_analytification`, stated as an `∃!`
rather than as an `Equiv` because the right-hand side is a subtype and the `∃!` is what every
consumer below actually uses.

## The one genuinely new ingredient

**Substitution.** `ComplexAnalytic.Γ_map_comp_ofMvPolynomial` says that pulling a polynomial back
along a `ℂ`-linear morphism `φ : Z ⟶ ℂ^n` is substituting the coordinate pullbacks of `φ` into
it. Both sides are ring homomorphisms out of `MvPolynomial`, so it is `MvPolynomial.ringHom_ext`:
on a constant it is `φ`'s `ℂ`-linearity, and on `Xⱼ` it is `rfl`, because
`ComplexAnalytic.coord j` **is** `OkaRing.ofMvPolynomial ⊤ (X j)` by definition.

This is what converts the geometric hypothesis of the factorisation theorem ; *the sections
cutting `X^an` out pull back to zero along `φ`* ; into the algebraic equation `gⱼ(a) = 0`, and it
is the reason the mapping property can be *stated* in terms of a tuple of sections rather than in
terms of a morphism to `ℂ^n`. Without it the statement would be a tautology about `IsCutOutBy`.

## The two inputs, and the seam between them that turned out not to exist

* **Surjectivity of `ComplexAnalytic.AnalyticSpace.coordPullback` for an arbitrary `Z`** ;
  `ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_general`. Every tuple of global
  sections of `𝒪_Z` is the tuple of coordinate pullbacks of some `Z ⟶ ℂ^n`.
* **The mapping property of `IsCutOutBy` for analytic spaces** ;
  `ComplexAnalytic.IsCutOutBy.existsUnique_liftHom`. A `ℂ`-linear morphism killing the cutting
  sections factors uniquely through the subspace.

The first produces morphisms into `ComplexAnalytic.AnalyticSpace.complexAffineSpace n`; the
second consumes morphisms into `(complexAffineSpace n).restrict ⊤`, which is a different type.
`ComplexAnalytic.toAmbient` crosses between them along `restrictTopIso`, and the crossing is
free: the sections that have to be carried across are **polynomials**, and a section whose
presentation does not mention the open it lives on crosses definitionally. Both general halves
of the crossing already existed ;
`AlgebraicGeometry.LocallyRingedSpace.Γ_map_inv_hom_apply` collapses the round trip for an
arbitrary isomorphism, and `ComplexAnalytic.isCLinearHom_restrictTopIso_inv_constants` supplies
the `ComplexAnalytic.constantsAlgMap` spelling for every `n`.

`ComplexAnalytic.comp_zeroLocusSubspaceι_iff` is where the seam is confined: it says the two
spellings of *"`ψ` is a factorisation of `φ`"* ; one through `zeroLocusSubspaceι` and mentioning
`restrictTopIso`, the other through `ComplexAnalytic.analytificationInclHom` and mentioning
neither ; are the same condition. Everything downstream is stated in the second spelling.

## What is delivered, and what is not

**Delivered: independence of the chosen generators.** The hypothesis `∀ j, gⱼ(a) = 0` says
exactly that the ideal `(g₁, …, g_k)` is contained in the kernel of `MvPolynomial.eval₂Hom`
(`ComplexAnalytic.eval₂_eq_zero_iff_presentationIdeal_le_ker`), so the functor `X^an` represents
depends on the **ideal** and not on the generating tuple. Two tuples spanning the same ideal ;
of possibly different lengths ; therefore give canonically isomorphic analytifications:
`ComplexAnalytic.analytificationIsoOfPresentationIdealEq`.

**Not delivered, and this file must not be read as providing them.**

* **A change of variables.** Two presentations of the same `ℂ`-algebra may use different numbers
  of variables, and nothing here relates `analytification g` for `g` in `n` variables to
  `analytification g'` for `g'` in `n'` variables. That is the rest of presentation-independence
  and it needs more than this file's `∃!`.
* **Functoriality.** There is no functor from finitely presented `ℂ`-algebras to analytic spaces
  here, and no action on morphisms.
* **The `ℂ`-algebra-hom form of the mapping property.** `AnalyticSpace.algebraMap` is a bare
  `ℂ →+* Γ(Z, 𝒪_Z)` and there is no `Algebra ℂ (Γ(Z, 𝒪_Z))` instance, so the bijection is stated
  against `MvPolynomial.eval₂` throughout rather than against `ℂ`-algebra maps out of `ℂ[x]/I`.
  A Yoneda argument for full presentation-independence would want the latter.

## Main definitions

- `ComplexAnalytic.analytificationInclHom`: **the inclusion `X^an ↪ ℂ^n` as a morphism of
  *analytic* spaces**, as opposed to the morphism of locally ringed spaces
  `ComplexAnalytic.analytificationIncl` that `Other/Oka/Analytification/Presentation.lean` provides.
- `ComplexAnalytic.analytificationCoord`: the `n` coordinate functions of `X^an`, i.e. the
  coordinate pullbacks along that inclusion. `ComplexAnalytic.nodeCoord` is this at the node.
- `ComplexAnalytic.toAmbient`: a morphism to `ℂ^n`, moved into the `restrict ⊤` presentation of
  `ℂ^n` that `ComplexAnalytic.IsCutOutBy` demands.
- `ComplexAnalytic.liftHom`: the morphism `Z ⟶ X^an` the mapping property produces.
- `ComplexAnalytic.analytificationIsoOfPresentationIdealEq`: **the analytification of a tuple
  depends only on the ideal it generates.**

## Main results

- `ComplexAnalytic.Γ_map_comp_ofMvPolynomial` and `ComplexAnalytic.Γ_map_ofMvPolynomial`:
  **pulling a polynomial back along a `ℂ`-linear morphism to `ℂ^n` is substituting the
  coordinate pullbacks into it.**
- `ComplexAnalytic.eval₂_analytificationCoord_eq_zero`: **the coordinates of `X^an` satisfy the
  equations**, which is what makes the mapping property's hypothesis meetable at all.
- `ComplexAnalytic.polyToGlobal_eq_eval₂Hom`: the ring map
  `ComplexAnalytic.polyToGlobal` of `Other/Oka/Analytification/Presentation.lean` **is** substitution
  of the coordinates of `X^an`. Nothing new is being built beside it.
- `ComplexAnalytic.existsUnique_hom_analytification`: **the universal property.**
- `ComplexAnalytic.hom_ext_analytification`: two morphisms into `X^an` agreeing on the
  coordinates are equal ; the uniqueness half, usable without producing the tuple's `∃!`.
- `ComplexAnalytic.isCutOutBy_analytificationInclHom`: **the analytification is cut out of `ℂ^n`
  itself by its defining polynomials** ; the zero-locus statement of
  `Other/Oka/AnalyticSpace/LocalModel.lean` at the *other* presentation of `ℂ^n`, which is the one
  every consumer of a cut-out datum takes. (Named by file rather than by declaration on purpose:
  the declaration's own docstring names it.)

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

noncomputable section

variable {n k : ℕ}

/-! ### Substituting sections into a polynomial -/

section Substitution

variable {Z : AnalyticSpace.{u}} (φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} n)

/-- **Pulling a polynomial back along a `ℂ`-linear morphism `φ : Z ⟶ ℂ^n` is substituting the
coordinate pullbacks of `φ` into it.**

Both sides are ring homomorphisms out of `MvPolynomial`, so `MvPolynomial.ringHom_ext` reduces
this to the constants and the variables. On a constant it is `φ`'s `ℂ`-linearity, transported
across `AlgHom.commutes`; on `Xⱼ` it is `rfl`, because `ComplexAnalytic.coord j` is by definition
`OkaRing.ofMvPolynomial ⊤ (MvPolynomial.X j)` and
`ComplexAnalytic.AnalyticSpace.coordPullback φ j` is by definition its pullback.

This is the only genuinely new ingredient of the universal property below: it is what turns *the
cutting sections pull back to zero* into *the equations hold at the tuple*.

Written in term mode because `show` produces a goal which is not type-correct under the
`instances` transparency level and `rw` is rejected ; the `TopCat.of` seam that
`Other/Oka/Analytification/AffineSpace.lean` documents. -/
theorem Γ_map_comp_ofMvPolynomial :
    (LocallyRingedSpace.Γ.map φ.toLRSHom.op).hom.comp
        (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin n) → ℂ))).toRingHom =
      MvPolynomial.eval₂Hom Z.algebraMap (AnalyticSpace.coordPullback φ) :=
  MvPolynomial.ringHom_ext
    (fun c ↦ (congrArg (LocallyRingedSpace.Γ.map φ.toLRSHom.op).hom
        ((OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin n) → ℂ))).commutes c)).trans
      ((φ.isCLinear c).trans (MvPolynomial.eval₂Hom_C _ _ c).symm))
    (fun j ↦ Eq.trans rfl
      (MvPolynomial.eval₂Hom_X' Z.algebraMap (AnalyticSpace.coordPullback φ) j).symm)

/-- `ComplexAnalytic.Γ_map_comp_ofMvPolynomial` applied to a polynomial, which is the form every
consumer wants. -/
theorem Γ_map_ofMvPolynomial (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    (LocallyRingedSpace.Γ.map φ.toLRSHom.op).hom
        (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin n) → ℂ)) p) =
      MvPolynomial.eval₂ Z.algebraMap (AnalyticSpace.coordPullback φ) p :=
  RingHom.congr_fun (Γ_map_comp_ofMvPolynomial φ) p

/-- **Pulling back a polynomial expression in global sections substitutes the pulled-back
sections.**

For *any* morphism of complex analytic spaces, not only for one into `ℂ^n`: `MvPolynomial.eval₂`
commutes with `ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ` because that is a ring homomorphism
(`MvPolynomial.eval₂_comp_left`) and because it carries the constants of `W` to the constants of
`Z`, which is exactly `φ.isCLinear`. Nothing analytic happens here; it is the reason a
factorisation of a morphism through an open subspace can be checked on polynomials. -/
theorem AnalyticSpace.pullbackΓ_eval₂ {Z W : AnalyticSpace.{u}} (φ : Z ⟶ W) {σ : Type*}
    (a : σ → W.presheaf.obj (op ⊤)) (p : MvPolynomial σ ℂ) :
    φ.pullbackΓ (MvPolynomial.eval₂ W.algebraMap a p) =
      MvPolynomial.eval₂ Z.algebraMap (fun i ↦ φ.pullbackΓ (a i)) p :=
  (MvPolynomial.eval₂_comp_left (LocallyRingedSpace.Γ.map φ.toLRSHom.op).hom W.algebraMap a
      p).trans
    (congrArg (fun r ↦ MvPolynomial.eval₂ r (fun i ↦ φ.pullbackΓ (a i)) p)
      (RingHom.ext φ.isCLinear))

end Substitution

/-! ### The inclusion of the analytification, as a morphism of analytic spaces -/

variable (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)

/-- The closed immersion of the analytification into `ℂ^n|⊤` is `ℂ`-linear, by the very choice
of the `ℂ`-algebra structure on the analytification.

`ComplexAnalytic.isCLinearHom_zeroLocusSubspaceι_nodeSection` is this at the node's tuple, and
has the same proof: `fun _ ↦ rfl`. -/
theorem isCLinearHom_zeroLocusSubspaceι_polySection :
    IsCLinearHom ((complexAffineSpaceTop.{u} n).zeroLocusSubspaceι (polySection.{u} g))
      (AnalyticSpace.analytification.{u} g).algebraMap (constantsAlgMap n ⊤) :=
  fun _ ↦ rfl

/-- **The inclusion of the analytification into `ℂ^n`, as a morphism of complex analytic
spaces.**

`ComplexAnalytic.analytificationIncl` is the same map one category down, as a morphism of locally
ringed spaces; this adds the `ℂ`-linearity, which is what the universal property below has to
quantify over. `ComplexAnalytic.nodeIncl` is this at the node's tuple, definitionally. -/
def analytificationInclHom :
    AnalyticSpace.analytification.{u} g ⟶ AnalyticSpace.complexAffineSpace.{u} n :=
  ⟨analytificationIncl.{u} g, (isCLinearHom_zeroLocusSubspaceι_polySection g).comp
    (isCLinearHom_ofRestrict_complexSpace _)⟩

/-- **The analytification is cut out of `ℂ^n` by its own defining polynomials**, read as
holomorphic functions on `ℂ^n` itself.

`AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι` says this for
`ComplexAnalytic.analytificationι`, whose target is `ℂ^n` **presented as an open subspace of
itself**. Every consumer of a cut-out datum in this development takes a morphism into
`ComplexAnalytic.AnalyticSpace.complexAffineSpace n`, i.e. into `ℂ^n` itself, and
`ComplexAnalytic.analytificationIncl` is the first composed with `ofRestrict`. This crosses that
`ofRestrict`.

**Nothing general had to be proved for it.** `ComplexAnalytic.IsCutOutBy.iso_comp`
(`Other/Oka/AnalyticSpace/Restrict.lean`) is the transport along an isomorphism of the target and has
been in the tree since open subspaces were made analytic spaces;
`AlgebraicGeometry.LocallyRingedSpace.restrictTopIso.hom` **is** that `ofRestrict` by definition,
so all that is left is that the family `iso_comp` produces is the one wanted, and
`AlgebraicGeometry.LocallyRingedSpace.Γ_map_inv_hom_apply` collapses the round trip because
`ComplexAnalytic.polySection g j` *is* the pullback of `OkaRing.ofMvPolynomial ⊤ (g j)` along
`restrictTopIso.hom` ; the same definitional fact `ComplexAnalytic.c_app_toAmbient_polySection`
below rests on. **The `Γ_map_inv_hom_apply` argument has to be written out** rather than left as
`_`: solving it from the expected type would need `ComplexAnalytic.polySection` unfolded, and
unification does not do that, so the hole is reported as a type mismatch between two spellings
of the same term.

**It is the first cut-out datum this repository produces, rather than assumes, for a morphism of
complex analytic spaces**, which is a sentence six files carried.

The sections are written out rather than given as `ComplexAnalytic.polySection g`, which is the
same tuple at the other presentation of `ℂ^n` and is a different type. -/
theorem isCutOutBy_analytificationInclHom :
    IsCutOutBy (analytificationInclHom.{u} g).toLRSHom
      (fun j ↦ (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin n) → ℂ)) (g j) :
        (AnalyticSpace.complexAffineSpace.{u} n).presheaf.obj (op ⊤))) := by
  have hfam : (fun j ↦ (LocallyRingedSpace.Γ.map
      (complexAffineSpace.{u} n).restrictTopIso.inv.op).hom (polySection.{u} g j)) =
      fun j ↦ (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin n) → ℂ)) (g j) :
        (AnalyticSpace.complexAffineSpace.{u} n).presheaf.obj (op ⊤)) :=
    funext fun j ↦ LocallyRingedSpace.Γ_map_inv_hom_apply
      (complexAffineSpace.{u} n).restrictTopIso
      (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin n) → ℂ)) (g j))
  exact hfam ▸ ((complexAffineSpaceTop.{u} n).isCutOutBy_zeroLocusSubspaceι
    (polySection.{u} g)).iso_comp (complexAffineSpace.{u} n).restrictTopIso

/-- **The `n` coordinate functions of the analytification**: the pullbacks of the coordinates of
`ℂ^n` along the inclusion. `ComplexAnalytic.nodeCoord` is this at the node's tuple. -/
def analytificationCoord : ULift.{u} (Fin n) →
    (AnalyticSpace.analytification.{u} g).presheaf.obj (op ⊤) :=
  AnalyticSpace.coordPullback (analytificationInclHom.{u} g)

/-- **Reading a polynomial as a global section of `𝒪_{X^an}` is substituting the coordinates of
`X^an` into it.**

`ComplexAnalytic.polyToGlobal` was defined in `Other/Oka/Analytification/Presentation.lean` before
`ComplexAnalytic.analytificationCoord` existed, and this says the two descriptions agree ; so
the machinery here is not a second copy of that one. It is
`ComplexAnalytic.Γ_map_comp_ofMvPolynomial` at the inclusion and nothing else, which is possible
only because a polynomial section crosses `restrictTopIso` definitionally. -/
theorem polyToGlobal_eq_eval₂Hom :
    polyToGlobal.{u} g = MvPolynomial.eval₂Hom
      (AnalyticSpace.analytification.{u} g).algebraMap (analytificationCoord.{u} g) :=
  Γ_map_comp_ofMvPolynomial (analytificationInclHom.{u} g)

/-- **A variable, read as a global section of `𝒪_{X^an}`, is the corresponding coordinate
function.** The `ComplexAnalytic.polyToGlobal` companion of
`ComplexAnalytic.quotientToGlobal_mk_X`. -/
@[simp]
theorem polyToGlobal_X (i : ULift.{u} (Fin n)) :
    polyToGlobal.{u} g (MvPolynomial.X i) = analytificationCoord.{u} g i :=
  (RingHom.congr_fun (polyToGlobal_eq_eval₂Hom.{u} g) (MvPolynomial.X i)).trans
    (MvPolynomial.eval₂Hom_X' _ _ i)

/-- **The coordinates of `X^an` satisfy the defining equations.**

This is what makes the hypothesis of `ComplexAnalytic.existsUnique_hom_analytification`
meetable, and it is `ComplexAnalytic.polyToGlobal_apply_eq_zero` ; i.e.
`ComplexAnalytic.IsCutOutBy.c_app_eq_zero` ; read through
`ComplexAnalytic.polyToGlobal_eq_eval₂Hom`. Fed back into the universal property it must return
the identity. -/
theorem eval₂_analytificationCoord_eq_zero (j : Fin k) :
    MvPolynomial.eval₂ (AnalyticSpace.analytification.{u} g).algebraMap
      (analytificationCoord.{u} g) (g j) = 0 :=
  (RingHom.congr_fun (polyToGlobal_eq_eval₂Hom g) (g j)).symm.trans
    (polyToGlobal_apply_eq_zero g j)

/-! ### The universal property -/

section UniversalProperty

variable {Z : AnalyticSpace.{u}}

/-- A morphism to `ℂ^n`, moved into the `restrict ⊤` presentation of `ℂ^n`.

`ComplexAnalytic.IsCutOutBy` and everything built on it quantify over an open subset of `ℂ^n`,
so even the trivial chart is spelled as a restriction, while
`ComplexAnalytic.AnalyticSpace.complexAffineSpace n` is `ℂ^n` itself. This is the crossing, and
`ComplexAnalytic.comp_zeroLocusSubspaceι_iff` is what keeps it out of the statements below. -/
def toAmbient (φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} n) :
    Z.toLocallyRingedSpace ⟶ complexAffineSpaceTop.{u} n :=
  φ.toLRSHom ≫ (complexAffineSpace.{u} n).restrictTopIso.inv

/-- Crossing into the `restrict ⊤` presentation preserves `ℂ`-linearity, in the
`ComplexAnalytic.constantsAlgMap` spelling that
`ComplexAnalytic.IsCutOutBy.existsUnique_liftHom` demands. -/
theorem isCLinearHom_toAmbient (φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} n) :
    IsCLinearHom (toAmbient.{u} φ) Z.algebraMap (constantsAlgMap n ⊤) :=
  φ.isCLinear.comp (isCLinearHom_restrictTopIso_inv_constants n)

/-- **The hypothesis of the factorisation theorem, translated into an equation between
polynomials and sections.**

The left-hand side is what `ComplexAnalytic.IsCutOutBy.existsUnique_liftHom` asks to vanish; the
right-hand side is `gⱼ` evaluated at the coordinate pullbacks of `φ`. Three steps and no
transport: functoriality of `Γ`, then
`AlgebraicGeometry.LocallyRingedSpace.Γ_map_inv_hom_apply` to collapse the `restrictTopIso` round
trip ; which is available because `ComplexAnalytic.polySection g j` *is* the pullback of
`OkaRing.ofMvPolynomial ⊤ (g j)` along `restrictTopIso.hom`, definitionally ; and then
`ComplexAnalytic.Γ_map_ofMvPolynomial`. -/
theorem c_app_toAmbient_polySection (φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} n) (j : Fin k) :
    ((toAmbient.{u} φ).c.app (op ⊤)).hom (polySection.{u} g j) =
      MvPolynomial.eval₂ Z.algebraMap (AnalyticSpace.coordPullback φ) (g j) :=
  (LocallyRingedSpace.Γ_map_comp_apply φ.toLRSHom
      (complexAffineSpace.{u} n).restrictTopIso.inv (polySection.{u} g j)).trans
    ((congrArg (LocallyRingedSpace.Γ.map φ.toLRSHom.op).hom
        (LocallyRingedSpace.Γ_map_inv_hom_apply (complexAffineSpace.{u} n).restrictTopIso
          (OkaRing.ofMvPolynomial (⊤ : Opens (ULift.{u} (Fin n) → ℂ)) (g j)))).trans
      (Γ_map_ofMvPolynomial φ (g j)))

/-- **Being a factorisation of `φ` through the analytification is one condition with two
spellings**, and this is the only place either has to mention the other.

`ComplexAnalytic.IsCutOutBy.existsUnique_liftHom` speaks about the left-hand condition, which
lives one category down and mentions `restrictTopIso`; the universal property must speak about
the right-hand one, which mentions neither. Proving the equivalence once and feeding it to
`existsUnique_congr` is what keeps the crossing out of the headline statement.

Both directions are `Iso.inv_hom_id` and `Iso.hom_inv_id` with `Category.assoc`, in term mode
because `rw` is rejected on these goals. -/
theorem comp_zeroLocusSubspaceι_iff (φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} n)
    (ψ : Z ⟶ AnalyticSpace.analytification.{u} g) :
    ψ.toLRSHom ≫ (complexAffineSpaceTop.{u} n).zeroLocusSubspaceι (polySection.{u} g) =
        toAmbient.{u} φ ↔
      ψ ≫ analytificationInclHom.{u} g = φ := by
  constructor
  · exact fun hψ ↦ AnalyticSpace.forgetToLocallyRingedSpace.map_injective
      ((Category.assoc ψ.toLRSHom _ _).symm.trans
        ((congrArg (fun m : Z.toLocallyRingedSpace ⟶ complexAffineSpaceTop.{u} n ↦
              m ≫ (complexAffineSpace.{u} n).restrictTopIso.hom) hψ).trans
          ((Category.assoc φ.toLRSHom _ _).trans
            ((congrArg (fun m : complexAffineSpace.{u} n ⟶ complexAffineSpace.{u} n ↦
                φ.toLRSHom ≫ m) (complexAffineSpace.{u} n).restrictTopIso.inv_hom_id).trans
              (Category.comp_id φ.toLRSHom)))))
  · intro hψ
    refine Eq.trans ?_ (congrArg
      (fun m : Z.toLocallyRingedSpace ⟶ complexAffineSpace.{u} n ↦
        m ≫ (complexAffineSpace.{u} n).restrictTopIso.inv)
      (congrArg AnalyticSpace.Hom.toLRSHom hψ))
    refine Eq.trans (Category.comp_id _).symm ?_
    refine Eq.trans (congrArg (fun m : complexAffineSpaceTop.{u} n ⟶ complexAffineSpaceTop.{u} n ↦
      (ψ.toLRSHom ≫ (complexAffineSpaceTop.{u} n).zeroLocusSubspaceι (polySection.{u} g)) ≫ m)
        (complexAffineSpace.{u} n).restrictTopIso.hom_inv_id.symm) ?_
    exact ((Category.assoc _ _ _).trans
      (congrArg (fun m : Z.toLocallyRingedSpace ⟶ complexAffineSpaceTop.{u} n ↦ m)
        (Category.assoc _ _ _).symm)).trans (Category.assoc _ _ _).symm

/-- **Two morphisms into the analytification which agree on the `n` coordinates are equal.**

The uniqueness half of the universal property, in the form a consumer usually wants: it does not
require producing the tuple, nor the hypothesis that the tuple satisfies the equations. Injectivity
of `ComplexAnalytic.AnalyticSpace.coordPullback`
(`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace`, general in the
source) reduces it to `ComplexAnalytic.IsCutOutBy.hom_ext`, i.e. to the closed immersion being a
monomorphism. -/
theorem hom_ext_analytification (ψ₁ ψ₂ : Z ⟶ AnalyticSpace.analytification.{u} g)
    (h : ∀ i, AnalyticSpace.coordPullback (ψ₁ ≫ analytificationInclHom.{u} g) i =
      AnalyticSpace.coordPullback (ψ₂ ≫ analytificationInclHom.{u} g) i) : ψ₁ = ψ₂ :=
  AnalyticSpace.forgetToLocallyRingedSpace.map_injective
    (((complexAffineSpaceTop.{u} n).isCutOutBy_zeroLocusSubspaceι (polySection.{u} g)).hom_ext
      ψ₁.toLRSHom ψ₂.toLRSHom
      (((comp_zeroLocusSubspaceι_iff g (ψ₁ ≫ analytificationInclHom.{u} g) ψ₁).2 rfl).trans
        ((comp_zeroLocusSubspaceι_iff g (ψ₁ ≫ analytificationInclHom.{u} g) ψ₂).2
          (AnalyticSpace.hom_ext_complexAffineSpace _ _ fun i ↦ (h i).symm)).symm))

/-- **The universal property of the analytification of a presented affine `ℂ`-algebra.**

For every complex analytic space `Z`, a tuple `a` of `n` global sections of `𝒪_Z` satisfying the
equations `gⱼ(a) = 0` comes from exactly one morphism `Z ⟶ X^an`, via the coordinate pullbacks
along the inclusion `X^an ↪ ℂ^n`.

Existence: `ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_general` turns the tuple
into a morphism `φ : Z ⟶ ℂ^n`; `ComplexAnalytic.c_app_toAmbient_polySection` turns the equations
into the vanishing hypothesis of `ComplexAnalytic.IsCutOutBy.existsUnique_liftHom`; that theorem
factors `φ` through `X^an`. Uniqueness comes from the same `∃!`, transported along
`ComplexAnalytic.comp_zeroLocusSubspaceι_iff`.

**This is the statement `Other/Oka/Analytification/Presentation.lean` says it does not provide.** What
it does *not* provide is presentation-independence under a change of *variables*; see the module
docstring, and `ComplexAnalytic.analytificationIsoOfPresentationIdealEq` for the part that is
delivered. -/
theorem existsUnique_hom_analytification (Z : AnalyticSpace.{u})
    (a : ULift.{u} (Fin n) → Z.presheaf.obj (op ⊤))
    (ha : ∀ j, MvPolynomial.eval₂ Z.algebraMap a (g j) = 0) :
    ∃! ψ : Z ⟶ AnalyticSpace.analytification.{u} g,
      ∀ i, AnalyticSpace.coordPullback (ψ ≫ analytificationInclHom.{u} g) i = a i := by
  obtain ⟨φ, hφ⟩ := AnalyticSpace.exists_hom_complexAffineSpace_general Z a
  refine (existsUnique_congr fun ψ ↦ (comp_zeroLocusSubspaceι_iff g φ ψ).trans ?_).mp
    (IsCutOutBy.existsUnique_liftHom
      ((complexAffineSpaceTop.{u} n).isCutOutBy_zeroLocusSubspaceι (polySection.{u} g))
      (toAmbient.{u} φ) (isCLinearHom_toAmbient φ)
      fun j ↦ (c_app_toAmbient_polySection g φ j).trans
        (Eq.trans (congrArg (fun b ↦ MvPolynomial.eval₂ Z.algebraMap b (g j)) (funext hφ)) (ha j)))
  exact ⟨fun h i ↦ (congrArg (fun m ↦ AnalyticSpace.coordPullback m i) h).trans (hφ i),
    fun h ↦ AnalyticSpace.hom_ext_complexAffineSpace _ _ fun i ↦ (h i).trans (hφ i).symm⟩

/-- **The morphism `Z ⟶ X^an` determined by a tuple of sections satisfying the equations**, i.e.
the existence half of `ComplexAnalytic.existsUnique_hom_analytification` given a name.

Its defining property is `ComplexAnalytic.coordPullback_liftHom_comp`, and
`ComplexAnalytic.hom_ext_analytification` says nothing else has that property. -/
def liftHom (Z : AnalyticSpace.{u}) (a : ULift.{u} (Fin n) → Z.presheaf.obj (op ⊤))
    (ha : ∀ j, MvPolynomial.eval₂ Z.algebraMap a (g j) = 0) :
    Z ⟶ AnalyticSpace.analytification.{u} g :=
  (existsUnique_hom_analytification g Z a ha).choose

/-- The coordinate pullbacks of `ComplexAnalytic.liftHom` are the tuple it was built from. -/
theorem coordPullback_liftHom_comp (Z : AnalyticSpace.{u})
    (a : ULift.{u} (Fin n) → Z.presheaf.obj (op ⊤))
    (ha : ∀ j, MvPolynomial.eval₂ Z.algebraMap a (g j) = 0) (i : ULift.{u} (Fin n)) :
    AnalyticSpace.coordPullback (liftHom.{u} g Z a ha ≫ analytificationInclHom.{u} g) i = a i :=
  (existsUnique_hom_analytification g Z a ha).choose_spec.1 i

end UniversalProperty

/-! ### Independence of the chosen generators -/

section Generators

/-- **The equations `gⱼ(a) = 0` say exactly that the ideal `(g₁, …, g_k)` lies in the kernel of
substitution.**

This is why the universal property depends only on the ideal: `MvPolynomial.eval₂Hom` is a ring
homomorphism and the `gⱼ` generate, so the condition cannot see the generating tuple. Everything
in this section is a consequence. -/
theorem eval₂_eq_zero_iff_presentationIdeal_le_ker (Z : AnalyticSpace.{u})
    (a : ULift.{u} (Fin n) → Z.presheaf.obj (op ⊤)) :
    (∀ j, MvPolynomial.eval₂ Z.algebraMap a (g j) = 0) ↔
      presentationIdeal.{u} g ≤ RingHom.ker (MvPolynomial.eval₂Hom Z.algebraMap a) :=
  ⟨fun h ↦ Ideal.span_le.2 (Set.range_subset_iff.2 fun j ↦ h j),
    fun h j ↦ h (Ideal.subset_span ⟨j, rfl⟩)⟩

variable {k' : ℕ} {g} {g' : Fin k' → MvPolynomial (ULift.{u} (Fin n)) ℂ}

/-- A tuple satisfying the equations of `g` satisfies those of any `g'` generating a smaller
ideal. -/
theorem eval₂_eq_zero_of_presentationIdeal_le (h : presentationIdeal.{u} g' ≤ presentationIdeal g)
    {Z : AnalyticSpace.{u}} (a : ULift.{u} (Fin n) → Z.presheaf.obj (op ⊤))
    (ha : ∀ j, MvPolynomial.eval₂ Z.algebraMap a (g j) = 0) (j : Fin k') :
    MvPolynomial.eval₂ Z.algebraMap a (g' j) = 0 :=
  (eval₂_eq_zero_iff_presentationIdeal_le_ker g' Z a).2
    (h.trans ((eval₂_eq_zero_iff_presentationIdeal_le_ker g Z a).1 ha)) j

/-- The comparison morphism between the analytifications of two tuples spanning the same
ideal. -/
def analytificationCompare (h : presentationIdeal.{u} g' ≤ presentationIdeal g) :
    AnalyticSpace.analytification.{u} g ⟶ AnalyticSpace.analytification.{u} g' :=
  liftHom.{u} g' _ (analytificationCoord.{u} g)
    (eval₂_eq_zero_of_presentationIdeal_le h _ (eval₂_analytificationCoord_eq_zero g))

/-- The comparison morphism carries the coordinates of one analytification to those of the
other, which is the only property of it used below. -/
theorem coordPullback_analytificationCompare_comp
    (h : presentationIdeal.{u} g' ≤ presentationIdeal g) (i : ULift.{u} (Fin n)) :
    AnalyticSpace.coordPullback
        (analytificationCompare.{u} h ≫ analytificationInclHom.{u} g') i =
      analytificationCoord.{u} g i :=
  coordPullback_liftHom_comp g' _ _ _ i

/-- **The two comparison morphisms between analytifications of tuples spanning the same ideal
are mutually inverse.**

By uniqueness: the composite and the identity have the same coordinate pullbacks, and
`ComplexAnalytic.hom_ext_analytification` ; used here in the shape
`ComplexAnalytic.AnalyticSpace.coordPullback_comp` supplies ; says that determines a morphism
into an analytification. Note that the two tuples may have different lengths, so this is not a
statement about reordering a fixed generating set. -/
theorem analytificationCompare_comp (h : presentationIdeal.{u} g' ≤ presentationIdeal g)
    (h' : presentationIdeal.{u} g ≤ presentationIdeal g') :
    analytificationCompare.{u} h ≫ analytificationCompare.{u} h' = 𝟙 _ :=
  hom_ext_analytification g _ _ fun i ↦
    (AnalyticSpace.coordPullback_comp (analytificationCompare.{u} h)
        (analytificationCompare.{u} h' ≫ analytificationInclHom.{u} g) i).trans
      (((congrArg (LocallyRingedSpace.Γ.map (analytificationCompare.{u} h).toLRSHom.op).hom
            (coordPullback_analytificationCompare_comp h' i)).trans
          (coordPullback_analytificationCompare_comp h i)).trans
        (congrArg (fun m ↦ AnalyticSpace.coordPullback m i)
          (Category.id_comp (analytificationInclHom.{u} g)).symm))

/-- **The analytification depends only on the ideal the tuple generates, not on the tuple.** -/
def analytificationIsoOfPresentationIdealEq (h : presentationIdeal.{u} g = presentationIdeal g') :
    AnalyticSpace.analytification.{u} g ≅ AnalyticSpace.analytification.{u} g' where
  hom := analytificationCompare.{u} h.ge
  inv := analytificationCompare.{u} h.le
  hom_inv_id := analytificationCompare_comp h.ge h.le
  inv_hom_id := analytificationCompare_comp h.le h.ge

end Generators

end

end ComplexAnalytic

end
