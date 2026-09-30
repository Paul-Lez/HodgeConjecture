/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.MonicHypersurface
public import Other.Oka.Analytification.StandardEtaleAnalytification

/-!
# `A[X] ⧸ (F)` is finite over `A^an` when `F` is monic, for a presented base `A`

`Other/Oka/Analytification/MonicHypersurface.lean` proves that the analytification of
`ℂ[x₁, …, x_n, X] ⧸ (G)`, for `G` monic in the last variable, is finite over `ℂ^n`, and its
`ComplexAnalytic.isFinite_analytification_comp_proj` says in terms what that statement is missing
and what it is missing it for:

> **The target is `ℂ^n`, and the Riemann-existence line wants the analytification of a base
> algebra.** … the arrow between the two statements is
> `ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp` … **What is missing is not the arrow
> but its hypothesis**: the cancellation needs the composite above to *be* the composite through
> the base algebra's analytification, and no statement in this repository factors it that way.

This file is that factorisation and the theorem it unlocks. Over an arbitrary presentation `g` of
`A`, the structure map `A ⟶ A[X] ⧸ (F)` ; `ComplexAnalytic.hypersurfacePresHom`, which
`Other/Oka/Analytification/StandardEtaleAnalytification.lean` already builds ; analytifies to a
**finite** morphism as soon as `F` is monic in the last variable. That is the first transfer of
finiteness across `ComplexAnalytic.AnalyticSpace.analytification` in this development in which the
target is not `ℂ^n`.

## The one step that is not bookkeeping

Cancelling `A^an ↪ ℂ^n` needs the composite to `ℂ^n` to be finite, and that composite is the
hypersurface's own inclusion into `ℂ^(n+1)` followed by the projection. But **the image of that
inclusion is not the hypersurface**: it is cut out by the `k` relations of `g` as well as by `F`,
so it is a proper closed subset of `{F = 0}` as soon as `g` has a relation at all, and
`ComplexAnalytic.isFinite_comp_proj_of_range_eq` asks for an equality it cannot supply.

`ComplexAnalytic.isFinite_comp_proj_of_range_subset` is that theorem with the hypothesis weakened
to an inclusion, which is all its proof ever used ; both obligations of
`ComplexAnalytic.AnalyticSpace.isFinite_comp_of_isClosedEmbedding` are asked *along the image*,
so a smaller image is never harder. It is in `Other/Oka/AnalyticSpace/MonicProjection.lean` beside the
theorem it generalises, and that theorem is now one line of it and keeps its name and its four
consumers.

## Where `ComplexAnalytic.AnalyticSpace.coordPullback_proj` sits, and why it is here

The coordinates of `ComplexAnalytic.AnalyticSpace.proj` belong under `Other/Oka/AnalyticSpace/`, next to
the projection. **No file there sees both of the declarations it mentions**: `AnalyticSpace.proj`
is in `Other/Oka/AnalyticSpace/ProjectionStalk.lean`, whose transitive imports do not contain
`Other/Oka/AnalyticSpace/HomToComplex.lean`, where `AnalyticSpace.coordPullback` is defined, and the
import in the other direction is absent too. The earliest module whose import closure contains both
is `Other/Oka/Analytification/MonicHypersurface.lean`, this file's own import. So it is stated here,
where it is used, rather than by adding an import edge between two files under `Other/Oka/AnalyticSpace/`
; which is a decision about that directory's shape and not one this file needs to take.

## The iteration is three problems, and the price on record covered only the first two

The bullet under `## What is not here` used to read *"a module-finite extension is a quotient of an
iterated one, and the induction ; which needs the presentation of the intermediate algebras and a
comparison of the two structure maps ; is not attempted and is not a corollary"*. That sentence
runs three obstructions together, and they are of very different sizes. Measured, on taxis #1379:

* **The second step is free.** `ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom` is
  stated over an *arbitrary* presentation `g`, and `ComplexAnalytic.hypersurfacePresentation g F`
  is a presentation of the same shape one variable up. So the second step is the first at a
  different base, the `Fin.snoc` produces exactly the index arithmetic the theorem's binders want,
  and the composite is finite by the `ComplexAnalytic.AnalyticSpace.isFinite_comp` instance with
  **nothing to prove**. *"Is not a corollary"* was right about the general case and wrong about
  this one.
* **The comparison of the two structure maps is one missing composition law.** Both structure maps
  are `ComplexAnalytic.PresHom.ofRename`, and `Other/Oka/Analytification/ChangeOfVariables.lean` had only
  the *inverse-pair* statement about that constructor ; `σ ∘ τ = id` giving the identity ; which
  says nothing about a tower. The general law is `ComplexAnalytic.PresHom.ofRename_comp`, added
  there rather than here, and with it the two-step extension is one `PresHom` and not a composite.
* **The quotient is the wall, and it is not an induction at all.** A module-finite `A`-algebra is a
  *quotient* of an iterated hypersurface: adjoin one root per module generator, then kill the
  kernel. The surjection is finite on the algebraic side because it is a closed immersion, and what
  that needs analytically is that a surjection of presented algebras has closed-embedding base map.

**The third's analytic half is no longer an estimate, and this paragraph used to price it as one.**
It read *"In a spike, deleted and not committed, the statement `IsClosedEmbedding
(analytificationMap (PresHom.ofRename id h)).base` compiles in about fifteen lines"*, and went on
**"It is not here, deliberately. Nothing would consume it until the general theorem is built, and
this file's own standard is that an unused lemma with an axiom guard is worse than an absence with
a sentence."** Both halves have been paid.
`ComplexAnalytic.isClosedEmbedding_base_analytificationMap_ofRename_id`
(`Other/Oka/Analytification/SurjectionFinite.lean`) is that statement, re-derived rather than
reconstructed from this paragraph, and the estimate was right about the route and about the size: a
surjection of presented `ℂ`-algebras adds relations and no variables, so it is
`ComplexAnalytic.PresHom.ofRename` at the identity between two presentations in the *same* `n`
variables whose ideals are nested; the triangle is
`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` and
`ComplexAnalytic.coordPullback_analytificationMap_comp` ; the transported tuple of a rename at the
identity is the source's own coordinates ; and then
`ComplexAnalytic.isClosedEmbedding_base_analytificationIncl` **twice** with
`Topology.IsClosedEmbedding.of_comp_iff`. **No new topology and no Nullstellensatz**, which is the
part of the estimate worth having been right.

**And it is consumed rather than orphaned**, which is what the standard quoted above actually asks:
`ComplexAnalytic.isFinite_analytificationMap_ofRename_id` reads it through
`ComplexAnalytic.AnalyticSpace.isFinite_of_isClosedEmbedding`, so *the analytification of a
surjection of presented algebras is finite* is a theorem and not a lemma waiting for one. It is in
a sibling file rather than here because its subject is a surjection and this file's is a
hypersurface, and because nothing in it mentions monicity or a projection.

**All three of `generators, tower, kernel` are discharged, and this paragraph used to describe two
of them as an absence.** It read *"Of the triple `generators, tower, kernel` the tower is
discharged and the other two are not … What is left is a construction with nothing analytic in it:
pick module generators of the target over the source, adjoin one root per generator with
`ComplexAnalytic.towerPresHom`, and exhibit the target as the quotient of that tower by the kernel
of the resulting surjection … the two that were **not** measured are the surjection onto the target
and the identification of the composite with the original `ComplexAnalytic.PresHom`. Neither is
estimated here."* **That construction is `Other/Oka/Analytification/ModuleFiniteAnalytification.lean`,
and `ComplexAnalytic.isFinite_analytificationMap_of_finite` is the theorem it closes**: a
`ComplexAnalytic.PresHom` whose ring map is module-finite analytifies to a finite morphism, with no
monicity, no tower and no surjection in its statement. The description was accurate, including
that there is no analysis in it. The two steps priced as cheap were cheap ;
`ComplexAnalytic.exists_presentationIdeal_eq` is nine lines and the push-up is
`Polynomial.Monic.map` ; and of the two that were declined, the surjection is the spanning
statement read through `Submodule.mem_span_range_iff_exists_fun` and the identification of the
composite is `ComplexAnalytic.towerPresHom_toRingHom_mk`, *the tower's structure map is one
renaming*. **What the paragraph did not foresee is the one thing that had to be decided**: the
quotient is taken inside the tower's own polynomial ring, so it presents the target in `n + m`
variables and **not** in the presentation the theorem is handed, and the two readings are
identified by `ComplexAnalytic.analytificationIsoOfPresHom`. The heading above names a *different*
three and this push **does** close its count: of the free second step, the comparison of the two
structure maps and the quotient, the first two were already discharged when that section was
written and the third is discharged now.

**And the shape of the surjection matters.** What is proved is the same-variables case, which is
the one the module-finite argument produces ; the quotient there is taken inside the tower's own
polynomial ring; a surjection between presentations in *different* numbers of variables is not of
that form and **nothing above is evidence about it**.

## Main definitions

- `ComplexAnalytic.towerPresentation`: **the `m`-step tower** ;
  `ComplexAnalytic.hypersurfacePresentation` applied `m` times, as a presentation in `n + m`
  variables with `k + m` relations.
- `ComplexAnalytic.towerPresHom`: **its structure map**, `A ⟶ A[X₁] ⧸ (F₁) ⟶ ⋯ ⟶ ⋯[Xₘ] ⧸ (Fₘ)`,
  as one morphism of presentations.

## Main results

- `ComplexAnalytic.AnalyticSpace.coordPullback_proj`: **the `j`-th coordinate of the projection
  `ℂ^(n+1) ⟶ ℂ^n` is the `j`-th of the first `n` coordinates.**
- `ComplexAnalytic.analytificationMap_hypersurfacePresHom_comp`: **the factorisation** ; the
  analytified structure map followed by `A^an ↪ ℂ^n` is the hypersurface's own inclusion into
  `ℂ^(n+1)` followed by the projection.
- `ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom`: **the analytification of
  `A ⟶ A[X] ⧸ (F)` is finite**, for `F` monic in the last variable.
- `ComplexAnalytic.rename_localisationIncl_comp_mem`: **the two inclusions of old variables,
  composed, carry every relation of the base into the ideal of the two-step hypersurface**, for
  every `g`, `F` and `F'` ; which is the side condition of the renaming below.
- `ComplexAnalytic.hypersurfacePresHom_comp_hypersurfacePresHom`: **two adjoined roots are one
  renaming** ; the composite of the two structure maps is the map of presentations given by the
  inclusion of the old variables into the new, composed.
- `ComplexAnalytic.hypersurfacePresHom_comp_hypersurfacePresHom'`: **the same law with its
  hypothesis discharged**, at the witness above.
- `ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom_comp_hypersurfacePresHom`:
  **the analytification of `A ⟶ A[X₁] ⧸ (F₁) ⟶ (A[X₁] ⧸ (F₁))[X₂] ⧸ (F₂)` is finite**, as one
  morphism, for both polynomials monic in their last variable.
- `ComplexAnalytic.isFinite_analytificationMap_towerPresHom`: **the analytification of an
  `m`-step tower of monic hypersurfaces is finite**, for every `m` ;
  `ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom_comp_hypersurfacePresHom` at
  `m = 2`.
- `ComplexAnalytic.towerPresentation_one` and `ComplexAnalytic.towerPresHom_one`: **one step of
  the tower is one hypersurface**, on the nose.
- `ComplexAnalytic.towerPresHom_two`: **two steps of the tower are the two-step composite**, on
  the nose ; so
  `ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom_comp_hypersurfacePresHom` is
  subsumed definitionally and not merely in effect.

## What is not here

* **Two `## Main results` bullets refer back to
  `ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom_comp_hypersurfacePresHom` ;
  the one for `ComplexAnalytic.isFinite_analytificationMap_towerPresHom` and the one for
  `ComplexAnalytic.towerPresHom_two` ; and both said *the theorem above* until this was
  written.** They sit two bullets apart and only the first resolved by adjacency: for the tower's
  finiteness the bullet immediately above it is the two-step theorem, while for
  `ComplexAnalytic.towerPresHom_two` the bullet immediately above is the pair of one-step
  identifications, which nothing subsumes. A reader who applied the reading that had just worked
  got the wrong declaration ; and that both sentences are about one and the same theorem, which
  is the whole of what *subsumes* is claiming, could not be seen from the list at all. **Nothing
  about the rest of that list follows from this.**
  `ComplexAnalytic.hypersurfacePresHom_comp_hypersurfacePresHom'`'s bullet keeps two
  back-references by description ; *the same law* and *the witness above* ; and each of those
  resolves: *the same law* by adjacency, being the bullet immediately above it, and *the witness
  above* by predicate, being the only membership statement in the list. **This note is here and
  not under `## Main results`** because every backticked repository name under that heading is
  read as a result the file advertises, so a paragraph left there is counted as though it were
  more bullets; `Other/Oka/AnalyticSpace/SimpleZeroStalk.lean` keeps its
  equivalent note in the same place for the same reason.

* **No general finite morphism *in this file*, and that is now all this bullet says.** It used to
  go on: *"What nothing states is the **construction** that produces such a surjection from a
  module-finite `ComplexAnalytic.PresHom` ; the generators and the kernel ; and that is a
  statement about presentations with no analysis in it."* **Something states it.**
  `ComplexAnalytic.isFinite_analytificationMap_of_finite`
  (`Other/Oka/Analytification/ModuleFiniteAnalytification.lean`) is the general theorem, and it consumes
  this file's `ComplexAnalytic.isFinite_analytificationMap_towerPresHom` together with
  `ComplexAnalytic.isFinite_analytificationMap_ofRename_id`
  (`Other/Oka/Analytification/SurjectionFinite.lean`), which is exactly the shape the section above
  predicted. What is *not* here is the theorem itself, which is in that file because its subject is
  a module-finite map and this file's is a hypersurface.
* **The `m`-step iterate is here, and this bullet used to say it was not.** It read *"the tower is
  a dependent recursion and not a family; nothing here builds it"*, and went on that the two-step
  case needs no such recursion *"because the second step is the first at a different base, and
  that is exactly what stops being available once the base is `Nat.rec`."* **The diagnosis was
  right and the estimate was wrong.** It is a dependent recursion ; the type of the `i`-th
  polynomial mentions `i` ; and `ComplexAnalytic.towerPresentation` is four lines with no
  `Fin.cast` and no transport in it. What the bullet did not consider is the **indexing**: taking
  a `Polynomial` over `n + i` variables rather than an `MvPolynomial` over `n + i + 1` of them ;
  the shape `ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom` already asks for ;
  makes every index in the recursion definitional, and the base at `Nat.rec` is then available
  after all. **What survives is the observation itself**: each step is still the one-step theorem
  at a different base, which is exactly why the induction proves nothing new.
* **Nothing about `ComplexAnalytic.etalePresentation`.** A standard étale algebra is this
  hypersurface with `G` inverted, and inverting `G` destroys finiteness: the punctured parabola
  over the line is the witness, and `Other/Oka/Analytification/MonicHypersurface.lean`'s
  `## What is not here` gives it. Nothing here applies to it, and the localisation is where the
  finite étale line has to say something different.
* **No converse and no degree.** Nothing says the fibres have `G.natDegree` points ; that is a
  statement about `ComplexAnalytic.AnalyticSpace.degree` and about multiplicity, and finiteness is
  indifferent to it.
* **No claim that this is a scheme-theoretic statement.** What is analytified is a presentation,
  and `A ⟶ A[X] ⧸ (F)` is a map of presented `ℂ`-algebras; no `AlgebraicGeometry.Scheme` appears
  anywhere below. **This bullet said *"there is no `AlgebraicGeometry.Scheme` on this line of
  files"* until 2026-09-02**, when `Other/Oka/Analytification/SpecScheme.lean` put one there ; a
  promotion of a *gluing* of `Spec`s, which is a different subject from this file's and does not
  make anything here scheme-theoretic. The scheme-level reading is the reason the statement is
  wanted and is not what is proved.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

variable {n k : ℕ}

/-- **Pulling the `j`-th coordinate of `ℂ^n` back along the projection `ℂ^(n+1) ⟶ ℂ^n` gives the
`j`-th coordinate of `ℂ^(n+1)`**, at the index `ComplexAnalytic.uliftCastSuccEmb` names.

`ComplexAnalytic.AnalyticSpace.proj` is `ComplexAnalytic.AnalyticSpace.okaMap` at
`ComplexAnalytic.coordEmb`, so this is `ComplexAnalytic.Γ_map_okaMapHom_coord` and the two
definitional unfoldings around it. -/
theorem AnalyticSpace.coordPullback_proj (j : ULift.{u} (Fin n)) :
    AnalyticSpace.coordPullback (AnalyticSpace.proj.{u} n) j =
      coord (uliftCastSuccEmb.{u} n j) :=
  Γ_map_okaMapHom_coord (coordEmb (uliftCastSuccEmb.{u} n)) j

variable (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
  (F : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ)

/-- **The analytified structure map `(A[X] ⧸ (F))^an ⟶ A^an`, followed by the inclusion of `A^an`
into `ℂ^n`, is the inclusion of `(A[X] ⧸ (F))^an` into `ℂ^(n+1)` followed by the projection.**

The compatibility `Other/Oka/Analytification/MonicHypersurface.lean` names as the missing hypothesis of
the cancellation. Two morphisms into `ℂ^n` agree as soon as their `n` coordinate pullbacks do
(`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace`), and both sides' coordinates are
already computed: on the left by `ComplexAnalytic.coordPullback_analytificationMap_comp` and
`ComplexAnalytic.transported_hypersurfacePresHom`, on the right by naturality of the coordinate
pullback and `ComplexAnalytic.AnalyticSpace.coordPullback_proj`.

The two sides meet because `ComplexAnalytic.uliftCastSuccEmb` and
`ComplexAnalytic.localisationIncl` are the same function ; the first bundled as an embedding, the
second not ; so the last step is `rfl` and no bridge lemma is needed. **Nothing here reads `F`**:
the equality holds for every `F`, and monicity enters only in the finiteness below. -/
theorem analytificationMap_hypersurfacePresHom_comp :
    analytificationMap.{u} (hypersurfacePresHom.{u} g F) ≫ analytificationInclHom.{u} g =
      analytificationInclHom.{u} (hypersurfacePresentation.{u} g F) ≫
        AnalyticSpace.proj.{u} n := by
  refine AnalyticSpace.hom_ext_complexAffineSpace _ _ fun j ↦ ?_
  have hl : AnalyticSpace.coordPullback
      (analytificationMap.{u} (hypersurfacePresHom.{u} g F) ≫ analytificationInclHom.{u} g) j =
      analytificationCoord.{u} (hypersurfacePresentation.{u} g F) (localisationIncl.{u} n j) :=
    (coordPullback_analytificationMap_comp.{u} (hypersurfacePresHom.{u} g F) j).trans
      (transported_hypersurfacePresHom.{u} g F j)
  have hr : AnalyticSpace.coordPullback
      (analytificationInclHom.{u} (hypersurfacePresentation.{u} g F) ≫
        AnalyticSpace.proj.{u} n) j =
      analytificationCoord.{u} (hypersurfacePresentation.{u} g F) (localisationIncl.{u} n j) := by
    rw [AnalyticSpace.coordPullback_comp, AnalyticSpace.coordPullback_proj]
    rfl
  exact hl.trans hr.symm

/-- **The analytification of `A ⟶ A[X] ⧸ (F)` is a finite morphism**, for `F` monic in the last
variable and `A` presented by `g`.

`ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp` cancels the closed embedding
`A^an ↪ ℂ^n`, whose base map is injective by
`ComplexAnalytic.isClosedEmbedding_base_analytificationIncl`; the composite it needs is the
factorisation above, and that composite is finite by
`ComplexAnalytic.isFinite_comp_proj_of_range_subset` at the family
`ComplexAnalytic.polyFamily G`. The range condition is an inclusion and not an equality precisely
because the image is cut out by the `k` relations of `g` as well as by `F`; what supplies it is the
`Fin.last`-th component of `ComplexAnalytic.range_base_analytificationIncl`, the others being
discarded.

`G` is the input rather than `F` because monicity *in the last variable* is not a property of a
multivariate polynomial: `ComplexAnalytic.lastVarPolyEquiv` is where that is discussed, and taking
`G` here is the same choice `ComplexAnalytic.isFinite_analytification_comp_proj` makes. -/
theorem isFinite_analytificationMap_hypersurfacePresHom
    (G : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ)) (hG : G.Monic) :
    AnalyticSpace.IsFinite (analytificationMap.{u}
      (hypersurfacePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm G))) := by
  refine AnalyticSpace.isFinite_of_isFinite_comp _ (analytificationInclHom.{u} g)
    (isClosedEmbedding_base_analytificationIncl.{u} g).injective ?_
  rw [analytificationMap_hypersurfacePresHom_comp]
  refine isFinite_comp_proj_of_range_subset _
    (isClosedEmbedding_base_analytificationIncl.{u} _) (monic_polyFamily.{u} G hG)
    (natDegree_polyFamily.{u} G hG) (continuous_coeff_polyFamily.{u} G) ?_
  refine Set.Subset.trans (Eq.subset (range_base_analytificationIncl.{u} _)) ?_
  intro z hz
  simp only [Set.mem_setOf_eq] at hz ⊢
  rw [← eval_lastVarPolyEquiv_symm.{u} G]
  have hlast := hz (Fin.last k)
  rwa [hypersurfacePresentation, Fin.snoc_last] at hlast

variable (F' : MvPolynomial (ULift.{u} (Fin (n + 1 + 1))) ℂ)

/-- **The renaming that adjoins two roots carries the base's relations into the two-step ideal.**

The side condition of `ComplexAnalytic.PresHom.ofRename` at the composite inclusion, which the
theorem below takes as an argument. It holds for **every** `g`, `F` and `F'`: nothing here reads
any of the three, exactly as the equality below reads none of them.

`ComplexAnalytic.rename_mem_presentationIdeal` is the whole proof and **this is its first
consumer**, which is the case its own docstring names ; *"the same statement about every element,
which is what a composite of two such renamings needs"*. The element it is applied at is
`MvPolynomial.rename (localisationIncl n) (g j)`, a relation of the middle presentation rather
than a generator, and `MvPolynomial.rename_rename` is what turns the two renamings into the
composite the statement is about.

**The named `(g' := …)` is essential.** That lemma's `g` and `g'` are implicit, and after the
`rw` the goal fixes the target presentation and says nothing about the middle one, so without the
ascription `g'` is still a metavariable when the two subgoals are created. **This paragraph
described the resulting error wrongly until it was re-run**: it said elaboration reports *"a
mismatch against an unfolded `ComplexAnalytic.presentationIdeal` with an unsolved ideal in it"*,
and it does not. Deleting the ascription from the proof below and nothing else gives
`don't know how to synthesize implicit argument 'g''`, and a second of the same for `k'`, with no
occurrence of `Set.range` or of an intersection anywhere in the error. The necessity and the
diagnosis are unaffected; only the output was misreported.

The two subgoals are the same membership twice, once at each step, and it is the one
`ComplexAnalytic.hypersurfacePresHom` discharges inside its own `ofRename` argument ; the old
relations are literally among the new ones. Neither `hypersurfacePresHom` itself appears. -/
theorem rename_localisationIncl_comp_mem (j : Fin k) :
    MvPolynomial.rename (localisationIncl.{u} (n + 1) ∘ localisationIncl.{u} n) (g j) ∈
      presentationIdeal.{u}
        (hypersurfacePresentation.{u} (hypersurfacePresentation.{u} g F) F') := by
  rw [← MvPolynomial.rename_rename]
  refine rename_mem_presentationIdeal.{u}
    (g' := hypersurfacePresentation.{u} g F) (localisationIncl.{u} (n + 1)) ?_ ?_
  · intro i
    rw [presentationIdeal_hypersurfacePresentation.{u} (hypersurfacePresentation.{u} g F) F']
    exact Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
  · rw [presentationIdeal_hypersurfacePresentation.{u} g F]
    exact Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩)

/-- **Adjoining two roots one after the other is one renaming of variables.**

The composite of the two structure maps `A ⟶ A[X₁] ⧸ (F)` and
`A[X₁] ⧸ (F) ⟶ (A[X₁] ⧸ (F))[X₂] ⧸ (F')` is `ComplexAnalytic.PresHom.ofRename` at the two
inclusions of old variables composed ; which is what the sentence *"a comparison of the two
structure maps"* in this file's `## What is not here` used to ask for.

`ComplexAnalytic.PresHom.ofRename_comp` is the whole proof, because
`ComplexAnalytic.hypersurfacePresHom` **is** an `ofRename` on both sides; the second step is the
first at the base `ComplexAnalytic.hypersurfacePresentation g F`, which is a presentation like any
other, so no re-indexing happens anywhere.

`h` is an argument for the reason it is one there: it occurs only under `ofRename`, whose value
does not depend on it, and `ComplexAnalytic.rename_mem_presentationIdeal` supplies it from the two
memberships `hypersurfacePresHom` already carries. **That last clause was a sentence and is now
`ComplexAnalytic.rename_localisationIncl_comp_mem` above**, which discharges it for every `g`, `F`
and `F'`; `ComplexAnalytic.hypersurfacePresHom_comp_hypersurfacePresHom'` below is this theorem at
that witness. **Nothing here reads `F` or `F'`** ; the equality holds for every pair, and monicity
enters only in the finiteness below. -/
theorem hypersurfacePresHom_comp_hypersurfacePresHom
    (h : ∀ j, MvPolynomial.rename (localisationIncl.{u} (n + 1) ∘ localisationIncl.{u} n) (g j) ∈
      presentationIdeal.{u}
        (hypersurfacePresentation.{u} (hypersurfacePresentation.{u} g F) F')) :
    (hypersurfacePresHom.{u} (hypersurfacePresentation.{u} g F) F').comp
        (hypersurfacePresHom.{u} g F) =
      PresHom.ofRename.{u} (localisationIncl.{u} (n + 1) ∘ localisationIncl.{u} n) h :=
  PresHom.ofRename_comp.{u} _ _ _ _ _

/-- **The composite law with its side condition discharged.**

The theorem above at `ComplexAnalytic.rename_localisationIncl_comp_mem`, so that the tree carries
the statement *"two adjoined roots are one renaming"* unconditionally and not only relative to a
hypothesis. Until this landed nothing applied that theorem, and its docstring's claim that the
hypothesis is supplied was a sentence rather than a proof.

**The general form stays, and keeps its argument.** That `h` is an argument rather than a proof
term is a decision this file and `Other/Oka/Analytification/ChangeOfVariables.lean` both argue for in the
same words ; the statement then reads as a law about `ofRename` and not about a particular way of
proving its side condition ; and which proof is supplied is immaterial, since `h` occurs only under
`ofRename`, whose value does not depend on it. This one sits beside it and does not replace it. -/
theorem hypersurfacePresHom_comp_hypersurfacePresHom' :
    (hypersurfacePresHom.{u} (hypersurfacePresentation.{u} g F) F').comp
        (hypersurfacePresHom.{u} g F) =
      PresHom.ofRename.{u} (localisationIncl.{u} (n + 1) ∘ localisationIncl.{u} n)
        (rename_localisationIncl_comp_mem.{u} g F F') :=
  hypersurfacePresHom_comp_hypersurfacePresHom.{u} g F F' _

/-- **The analytification of `A ⟶ (A[X₁] ⧸ (F₁))[X₂] ⧸ (F₂)` is finite**, for both polynomials
monic in their last variable, as one morphism rather than as a composite.

`ComplexAnalytic.analytificationMap_comp` splits it, and then the two factors are the one-step
theorem above at two different bases: at `g` for the first, and at
`ComplexAnalytic.hypersurfacePresentation g ((lastVarPolyEquiv n).symm G₁)` for the second, which
is a presentation of the same shape one variable up. **The last step is `infer_instance`**, because
`ComplexAnalytic.AnalyticSpace.isFinite_comp` is an instance and the two `haveI`s are what it
needs; nothing is proved here that the one-step theorem did not already prove.

`ComplexAnalytic.hypersurfacePresHom_comp_hypersurfacePresHom` above says the morphism this is
about is one `ComplexAnalytic.PresHom.ofRename`, so this is a statement about a single map of
presentations and not only about a factorisation of one. -/
theorem isFinite_analytificationMap_hypersurfacePresHom_comp_hypersurfacePresHom
    (G₁ : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ)) (hG₁ : G₁.Monic)
    (G₂ : Polynomial (MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ)) (hG₂ : G₂.Monic) :
    AnalyticSpace.IsFinite (analytificationMap.{u}
      ((hypersurfacePresHom.{u}
          (hypersurfacePresentation.{u} g ((lastVarPolyEquiv.{u} n).symm G₁))
          ((lastVarPolyEquiv.{u} (n + 1)).symm G₂)).comp
        (hypersurfacePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm G₁)))) := by
  haveI h₁ := isFinite_analytificationMap_hypersurfacePresHom.{u} g G₁ hG₁
  haveI h₂ := isFinite_analytificationMap_hypersurfacePresHom.{u}
    (hypersurfacePresentation.{u} g ((lastVarPolyEquiv.{u} n).symm G₁)) G₂ hG₂
  rw [analytificationMap_comp]
  infer_instance

/-! ### The `m`-step tower -/

/-- **The `m`-step tower of hypersurfaces over a presented base.**

`ComplexAnalytic.hypersurfacePresentation` applied `m` times: a presentation in `n + m` variables
with `k + m` relations, whose `i`-th adjoined polynomial lives over the first `n + i` variables.
That dependence is why this is a recursion on `m` and not a family indexed by `Fin m` ; the type
of `G i` mentions `i`.

**The indexing is what makes it free.** `G` takes a `Polynomial` over `n + i` variables rather
than an `MvPolynomial` over `n + i + 1` of them, which is the shape
`ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom` already asks for; with it, every
index in the recursion is definitional and **no `Fin.cast` and no transport appears anywhere**.
At the successor step `n + (m + 1)` and `k + (m + 1)` reduce to where
`ComplexAnalytic.hypersurfacePresentation` puts them, `Fin.castSucc` makes `n + i.1` agree on
both sides, and `(Fin.last m).1` reduces to `m`. At `m = 0` the value is literally `g`, because
`n + 0` and `k + 0` reduce. -/
noncomputable def towerPresentation (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    ∀ (m : ℕ), (∀ i : Fin m, Polynomial (MvPolynomial (ULift.{u} (Fin (n + i.1))) ℂ)) →
      Fin (k + m) → MvPolynomial (ULift.{u} (Fin (n + m))) ℂ
  | 0, _ => g
  | (m + 1), G =>
      hypersurfacePresentation.{u} (towerPresentation g m fun i ↦ G i.castSucc)
        ((lastVarPolyEquiv.{u} (n + m)).symm (G (Fin.last m)))

/-- **The structure map of the tower**, `A ⟶ A[X₁] ⧸ (F₁) ⟶ ⋯ ⟶ ⋯[Xₘ] ⧸ (Fₘ)`, as one morphism
of presentations.

Each step is `ComplexAnalytic.hypersurfacePresHom` at the presentation the step below produced,
composed with what came before. The base case is `ComplexAnalytic.PresHom.id`, and that costs
nothing rather than needing to be worked around: `ComplexAnalytic.PresHom.comp ψ
(ComplexAnalytic.PresHom.id g)` **reduces to `ψ`**, which is why the two grounding lemmas below
are `rfl`. -/
noncomputable def towerPresHom (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    ∀ (m : ℕ) (G : ∀ i : Fin m, Polynomial (MvPolynomial (ULift.{u} (Fin (n + i.1))) ℂ)),
      PresHom.{u} (towerPresentation.{u} g m G) g
  | 0, _ => PresHom.id.{u} g
  | (m + 1), G =>
      PresHom.comp.{u}
        (hypersurfacePresHom.{u} (towerPresentation.{u} g m fun i ↦ G i.castSucc)
          ((lastVarPolyEquiv.{u} (n + m)).symm (G (Fin.last m))))
        (towerPresHom g m fun i ↦ G i.castSucc)

/-- **The analytification of an `m`-step tower of monic hypersurfaces is finite.**

The induction is the two-step proof below run `m` times, and it proves nothing the one-step
theorem did not: `ComplexAnalytic.analytificationMap_comp` splits the step and
`ComplexAnalytic.AnalyticSpace.isFinite_comp` closes it. **Monicity is asked of every `G i` and
of nothing else**; no relation between the steps is needed, because each step is the one-step
theorem at the base the step below produced.

Two phrasings here are essential and a reader should not tidy them away.

**Both branches open with a `change` rather than a `rw` at `ComplexAnalytic.towerPresHom`.**
Rewriting at a definition plants an auto-generated equation lemma in this module under that
definition's own name, where it is picked up by `scripts/DumpOkaDecls.lean` and by nothing else;
the `change`s are what keep this file's declaration count equal to what it declares.
(`change` and not `show`: `show` is for goals it does not alter, and `Mathlib`'s style linter
rejects one that does ; which both of these do.)

**The `change` in the base case is there for a second and different reason.** After the `| 0` split
the goal reads `analytificationMap (PresHom.id g)` but is elaborated with the indices at `n + 0`
and `k + 0`, while `ComplexAnalytic.analytificationMap_id` is stated at `n` and `k`. The two are
definitionally equal and `rw` still fails, with *"Did not find an occurrence of the pattern"* and
the note that the target is not type-correct at `instances` transparency. The `change`
re-elaborates at the reduced indices.

**The last step is `infer_instance`, exactly as in the two-step theorem below**, and this
paragraph used to say the opposite: that `infer_instance` reports `failed to synthesize` there,
that `exact @ComplexAnalytic.AnalyticSpace.isFinite_comp _ _ _ _ _ h2 h1` was required, and that
why it failed here and not below was not established. **It does not fail.** The claim was
measured against an earlier draft of this proof and carried across without a re-run; with
`infer_instance` there is no difference between this ending and the two-step theorem's at all,
which is the sentence the file should have carried. Nothing else in the proof changes and the
declaration dump is byte-identical either way, so no discipline is being traded for the shorter
form. -/
theorem isFinite_analytificationMap_towerPresHom (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    ∀ (m : ℕ) (G : ∀ i : Fin m, Polynomial (MvPolynomial (ULift.{u} (Fin (n + i.1))) ℂ))
      (_ : ∀ i, (G i).Monic),
      AnalyticSpace.IsFinite (analytificationMap.{u} (towerPresHom.{u} g m G))
  | 0, _, _ => by
      change AnalyticSpace.IsFinite (analytificationMap.{u} (PresHom.id.{u} g))
      rw [analytificationMap_id.{u}]
      infer_instance
  | (m + 1), G, hG => by
      change AnalyticSpace.IsFinite (analytificationMap.{u} (PresHom.comp.{u}
        (hypersurfacePresHom.{u} (towerPresentation.{u} g m fun i ↦ G i.castSucc)
          ((lastVarPolyEquiv.{u} (n + m)).symm (G (Fin.last m))))
        (towerPresHom.{u} g m fun i ↦ G i.castSucc)))
      rw [analytificationMap_comp.{u}]
      haveI h1 := isFinite_analytificationMap_towerPresHom g m (fun i ↦ G i.castSucc)
        (fun i ↦ hG i.castSucc)
      haveI h2 : AnalyticSpace.IsFinite (analytificationMap.{u}
          (hypersurfacePresHom.{u} (towerPresentation.{u} g m fun i ↦ G i.castSucc)
            ((lastVarPolyEquiv.{u} (n + m)).symm (G (Fin.last m))))) :=
        isFinite_analytificationMap_hypersurfacePresHom.{u}
          (towerPresentation.{u} g m fun i ↦ G i.castSucc) (G (Fin.last m)) (hG (Fin.last m))
      infer_instance

/-- **One step of the tower is one hypersurface**, on the nose. -/
theorem towerPresentation_one (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (G : ∀ i : Fin 1, Polynomial (MvPolynomial (ULift.{u} (Fin (n + i.1))) ℂ)) :
    towerPresentation.{u} g 1 G =
      hypersurfacePresentation.{u} g ((lastVarPolyEquiv.{u} n).symm (G 0)) := rfl

/-- **The one-step tower's structure map is `ComplexAnalytic.hypersurfacePresHom`**, on the nose:
the trailing `ComplexAnalytic.PresHom.id` of the base case reduces away. -/
theorem towerPresHom_one (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (G : ∀ i : Fin 1, Polynomial (MvPolynomial (ULift.{u} (Fin (n + i.1))) ℂ)) :
    towerPresHom.{u} g 1 G = hypersurfacePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm (G 0)) := rfl

/-- **The two-step tower's structure map is the composite the theorem below is stated about**, on
the nose.

This is the evidence that `ComplexAnalytic.isFinite_analytificationMap_towerPresHom` **subsumes**
`ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom_comp_hypersurfacePresHom` rather
than sitting beside it: the two theorems are about the same morphism at `m = 2`, and `rfl` is the
proof. Stated as a theorem rather than remarked on in prose, because a claim of definitional
equality that nothing checks is exactly the kind of sentence this file's history is made of. -/
theorem towerPresHom_two (g : Fin k → MvPolynomial (ULift.{u} (Fin n)) ℂ)
    (G : ∀ i : Fin 2, Polynomial (MvPolynomial (ULift.{u} (Fin (n + i.1))) ℂ)) :
    towerPresHom.{u} g 2 G =
      (hypersurfacePresHom.{u}
          (hypersurfacePresentation.{u} g ((lastVarPolyEquiv.{u} n).symm (G 0)))
          ((lastVarPolyEquiv.{u} (n + 1)).symm (G 1))).comp
        (hypersurfacePresHom.{u} g ((lastVarPolyEquiv.{u} n).symm (G 0))) := rfl

end ComplexAnalytic

end
