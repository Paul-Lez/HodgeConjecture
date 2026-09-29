/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Algebra.MvPolynomial.Equiv
public import Other.Oka.AnalyticSpace.MonicProjection
public import Other.Oka.Analytification.DistinguishedOpen
public import Other.Oka.Analytification.UniversalProperty
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# The hypersurface of a polynomial monic in the last variable, and its projection

`Other/Oka/AnalyticSpace/MonicProjection.lean` proves that a hypersurface of `ℂ^(n+1)` cut out by a
continuous family `q` of monic polynomials of one fixed degree is finite over `ℂ^n`, and its
`## What is not here` says plainly that it produces no such family:

> **No Weierstrass polynomial.** Nothing here produces the family `q` from a germ … the family
> is a hypothesis.

This file produces one, in the case the Riemann-existence line needs: `q` comes from a
**polynomial** `G` which is monic in the last variable, and its coefficients are polynomial
functions of the first `n`. With it, `ComplexAnalytic.isFinite_comp_proj_of_range_eq` applies to
the analytification of `ℂ[x₁, …, x_n, X] ⧸ (G)` with no hypothesis left over, which is
`ComplexAnalytic.isFinite_analytification_comp_proj`. Outside
`Other/Oka/AnalyticSpace/MonicProjection.lean`, where it is proved and where
`ComplexAnalytic.isFinite_comp_proj_of_isCutOutBy` is derived from it, this is a consumer of
`ComplexAnalytic.isFinite_comp_proj_of_range_eq` that discharges its closed-embedding hypothesis
with `ComplexAnalytic.AnalyticSpace.analytification`, which this development constructs.

**Not claimed: that this is the first finiteness statement about a morphism this development
builds.** It is not. `ComplexAnalytic.AnalyticSpace.isFinite_sigmaDesc` is one. What is new here
is that the target is `ℂ^n`, which is what makes `ComplexAnalytic.isFinite_comp_proj_of_range_eq`
the theorem that applies.

## The spelling of "monic in the last variable", and why it is not the obvious one

A polynomial in `n + 1` variables is a `MvPolynomial (ULift (Fin (n + 1))) ℂ`, and that type has
no `Monic` and no `natDegree`: monic *in the last variable* is not a property of it but of its
image in `Polynomial (MvPolynomial (ULift (Fin n)) ℂ)`. So the input here is an honest
`G : Polynomial (MvPolynomial (ULift (Fin n)) ℂ)` with `G.Monic`, and
`ComplexAnalytic.lastVarPolyEquiv` is the translation back.

**That is also the spelling the presentation machinery uses on the far side.**
`ComplexAnalytic.polyPresentedAlgebraEquiv` in `Other/Oka/Analytification/StandardEtale.lean` lands in
`Polynomial (ComplexAnalytic.PresentedAlgebra n k g)`, and `Mathlib`'s `StandardEtalePair.f` is
an element of `R[X]`; what `ComplexAnalytic.etalePresentation` takes is a **lift** of that to
`MvPolynomial (ULift (Fin (n + 1))) ℂ`. `lastVarPolyEquiv` is built out of the same two pieces
that equivalence is ; `ComplexAnalytic.localisationVarEquiv` and
`MvPolynomial.optionEquivLeft` ; so the two agree on which variable is the polynomial one, by
construction rather than by a compatibility lemma.

## What each hypothesis of the projection theorem costs

* `hm`, `hd` ; `Polynomial.Monic.map` and `Polynomial.Monic.natDegree_map`. The degree is
  `G.natDegree`, *fixed*, which is the hypothesis `Other/Oka/Topology/Algebra/Polynomial.lean` needs and
  cannot weaken to a bound.
* `hc` ; one `Polynomial.coeff_map` and `MvPolynomial.continuous_eval`. The coefficient of
  `q w` in degree `j` **is** `MvPolynomial.eval w (G.coeff j)`, a polynomial function of `w`.
  This is the hypothesis the projection theorem calls the only analytic input, and in the
  polynomial case it is not analytic at all.
* `hrange` ; `ComplexAnalytic.range_base_analytificationIncl`, which is where the analytic space
  enters. `ComplexAnalytic.eval_lastVarPolyEquiv_symm` is the identity that turns the zero locus
  of `G` read in `n + 1` variables into the zero locus of the family read through
  `ComplexAnalytic.uliftSnocHomeo`.

## Main definitions

- `ComplexAnalytic.lastVarPolyEquiv`: **a polynomial in `n + 1` variables, read as a polynomial
  in the last one over the first `n`.**
- `ComplexAnalytic.polyFamily`: **the family of one-variable polynomials of `G`**, its
  coefficients evaluated at a point of the base.
- `ComplexAnalytic.lastVarSection`: the entire function on `ℂ^(n+1)` that `G` defines.

## Main results

- `ComplexAnalytic.eval_eq_eval_lastVarPolyEquiv`: **evaluating a polynomial in `n + 1`
  variables is evaluating its family at the first `n` coordinates and then at the last.**
- `ComplexAnalytic.lastVarPolyEquiv_rename_localisationIncl`,
  `ComplexAnalytic.lastVarPolyEquiv_symm_C` and `ComplexAnalytic.lastVarPolyEquiv_symm_X`:
  **the equivalence and its inverse on the two blocks of variables** ; a polynomial in the first
  `n` variables is a constant, a constant is such a polynomial, and the polynomial variable is
  the last one. The two simp lemmas beside `ComplexAnalytic.lastVarPolyEquiv` go only one way
  and only at a variable; a consumer that *builds* a polynomial in `n + 1` variables out of a
  one-variable one, as `ComplexAnalytic.hypersurfacePresentation` does, needs the other three.
- `ComplexAnalytic.monic_polyFamily`, `ComplexAnalytic.natDegree_polyFamily` and
  `ComplexAnalytic.continuous_coeff_polyFamily`: **the family of a monic `G` satisfies the three
  hypotheses `ComplexAnalytic.isFinite_comp_proj_of_range_eq` asks of a family.**
- `ComplexAnalytic.evalHom_lastVarSection`: the fourth hypothesis, relating the section to the
  family, for the form of that theorem that takes a cut-out datum.
- `ComplexAnalytic.isFinite_comp_proj_of_monic`: **a hypersurface cut out by `G` monic is finite
  over `ℂ^n`**, with the hypersurface presented as a cut-out by one global section.
- `ComplexAnalytic.isFinite_analytification_comp_proj`: **the analytification of
  `ℂ[x₁, …, x_n, X] ⧸ (G)` is finite over `ℂ^n`.**

## What is not here

* **Nothing from a germ.** The Weierstrass case ; the family of the Weierstrass polynomial of a
  holomorphic germ ; is not three lines away from this and is not attempted. Its coefficients are
  elements of `OkaRing U` for a neighbourhood `U` rather than polynomials, so it needs a pullback
  of holomorphic functions along the projection. **That pullback is no longer missing**:
  `ComplexAnalytic.pullbackCylinder` in `Other/Oka/AnalyticSpace/HolomorphicFamily.lean` is one at
  `ULift (Fin n)`, built beside `OkaRing.pullbackInit` in `Other/Oka/Weierstrass.lean` rather than by
  relabelling it, since that one is stated at index type `Fin n` and for the cylinder `U.extend'`
  while everything here is at `ULift (Fin n)`. **Nor is the step before it absent any longer**:
  `LocalOkaRing.exists_monic_realize_ulift` in `Other/Oka/UliftCoord.lean` extracts a monic polynomial
  over `OkaRing W` from a germ Weierstrass polynomial and chooses the neighbourhood `W`, at
  `ULift (Fin n)`; and the index bridge that costs is **not**
  `Other/Oka/RenameIndex.lean`'s kind of work, because `OkaRing.congr` in `Other/Oka/StructureSheaf.lean` was
  already stated for an arbitrary `φ : ℂ^ι ≃L[ℂ] ℂ^κ` with `ι` and `κ` independent. What is still
  absent is the image: `ComplexAnalytic.isFinite_comp_projRestrict_of_monic` takes its
  hypersurface as a range condition and no statement produces one from a germ. That is a separate
  issue, not a corollary of this one, and `Other/Oka/AnalyticSpace/HolomorphicFamily.lean` records the
  same residue from its own side.

* **No open subset of the base in this file**, as in `Other/Oka/AnalyticSpace/MonicProjection.lean` and
  `Other/Oka/AnalyticSpace/SimpleZeroStalk.lean`, where the same restriction is absent.
  `ComplexAnalytic.isFinite_analytification_comp_proj` is about the analytification of a quotient
  by **one** relation in `n + 1` variables, and a standard étale algebra is not of that shape:
  `ComplexAnalytic.etalePresentation` has **two** more variables and two more relations,
  `Y·G - 1` and `F`. The extra `Y` is not cut out by a monic polynomial at all ; `Y·G - 1` has
  leading coefficient `G`, not `1` ; so the composite the Riemann-existence line wants is not an
  instance of the theorem below.

  Restricting the base is no longer absent from the repository, only from this file:
  `ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq` in
  `Other/Oka/AnalyticSpace/OpenBaseProjection.lean` is `ComplexAnalytic.isFinite_comp_proj_of_range_eq`
  over the cylinder above an open `V ⊆ ℂ^n`. **It is not by itself what `Y·G - 1` asks for**, and
  the difference is which space is cut down. `G` is a polynomial in all `n + 1` variables, so
  inverting it removes a closed set from the *source*, and `G ≠ 0` describes a cylinder over an
  open subset of `ℂ^n` only when `G` does not involve the last variable. Nor is cutting the source
  down harmless: the projection of `X² = x` with `X ≠ 0` to the `x`-line has image the punctured
  line, which is not closed, so over the whole base the conclusion is **false** and not merely
  unproved.

  What is true is that the inversion becomes **vacuous over an open subset of the base**, and that
  is now stated: `Other/Oka/Analytification/OpenBaseFiniteness.lean` is the open set, its closedness and
  the vacuity above its complement. **This paragraph read *"that is the shape of the remaining work
  rather than a lemma anyone has"* until that file landed**, and what it retires is the
  hypersurface half only. **Both of the two things that sentence then called *"still nowhere"* are
  somewhere now, and they stopped being nowhere in different pushes.** The identification of the
  source with a *localised* algebra is
  `ComplexAnalytic.isFinite_restrictHom_analytificationMap_etalePresHom_comp`
  (`Other/Oka/Analytification/StandardEtaleFiniteness.lean`), at `k = 0`; the stalk half is
  `ComplexAnalytic.isLocalIso_analytificationMap_etalePresHom_comp`
  (`Other/Oka/Analytification/StandardEtaleLocalIso.lean`), which landed earlier and which this
  paragraph did not track. `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` of the
  **unrestricted** morphism is still nowhere and is **false**, which is what the counterexample
  in this file is for and which nothing narrows. Of the *restricted* one this paragraph said it
  was *"waiting on a transport of `ComplexAnalytic.AnalyticSpace.IsLocalIso` along a restriction
  that nothing has"*; that transport is
  `ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom` (`Other/Oka/AnalyticSpace/OpenSubspace.lean`)
  and the class is
  `ComplexAnalytic.isFiniteEtale_restrictHom_analytificationMap_etalePresHom_comp`
  (`Other/Oka/Analytification/StandardEtaleFiniteEtale.lean`), at `k = 0`.
  The theorem below makes the
  projection of the hypersurface a closed map ; **and it asks that hypersurface to be cut out by a
  polynomial monic in the last variable, which here is `F`, so a monic lift has to be chosen.**
  `StandardEtalePair.monic_f` gives monicity of `StandardEtalePair.f` in `A[X]` over
  `A = ComplexAnalytic.PresentedAlgebra n k g`, which is a different statement from monicity in
  the last variable over `ℂ[x₁, …, x_n]`, and `ComplexAnalytic.etalePresentedAlgebraEquiv` takes
  *any* lift `F` of `StandardEtalePair.f` as a hypothesis rather than choosing one. A monic lift
  exists ; the leading coefficient `1` lifts to `1` ; so this is a choice to record and not an
  obstruction. Closedness in hand, the image of the closed set where `F` and `G` both vanish is
  closed; above its complement `V` no point of the hypersurface has `G = 0`, so there the source
  of the localised algebra *is* the hypersurface over the cylinder, which is what
  `ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq` takes, with the same family `q`
  restricted to `V`. That is what makes the base restriction the relevant one after all ; not
  because it handles the inverted `G`, but because it is where there is nothing left to invert.
  **One thing this paragraph got the wrong way round and the file that carries it out corrects**:
  the finiteness over the cylinder needs no `V` and holds over every open subset of the base, so
  `V` is not what makes the projection finite. `V` is what makes the *source* the hypersurface
  rather than an open subset of it. **And nothing here says `V` is nonempty** ; that file exhibits
  a pair `(F, G)` for which it is empty, and one for which it is everything.

  **And over `V` the step back to the base algebra is not the one the theorem below takes.**
  `ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp` cancels an injective second factor, so
  both maps have to land in one space; the plan above ends over
  `(ComplexAnalytic.AnalyticSpace.complexAffineSpace n).restrict V` while
  `ComplexAnalytic.analytificationInclHom` lands in `ℂ^n`, and **composing back up with
  `ComplexAnalytic.AnalyticSpace.ofRestrict` is not the repair it looks like**: a finite morphism
  has closed image ; `ComplexAnalytic.AnalyticSpace.IsFinite` carries `IsClosedMap` as a field ;
  and the composite's image lies inside the open `V`, so the composite is finite only if that
  image is closed in `ℂ^n`. **It is not, and the route is closed rather than open.** The image is
  `V` exactly when the projection is onto, and the projection *is* onto: the fibre over `v` is the
  root set of `q v`, which is monic of degree `d` in the family
  `ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq` takes, and a monic polynomial of
  positive degree over `ℂ` has a root. So the image is the open `V`, and an open set closed in the
  connected `ℂ^n` is `∅` or `⊤` ; **so for every proper non-empty `V`, which is every case this
  plan is for, the composite is not finite.**

  Two degenerate cases sit outside that, and neither rescues the route. `ofRestrict` at `V = ⊤`
  *is* a closed map, being an isomorphism ;
  `ComplexAnalytic.AnalyticSpace.isIso_ofRestrict_of_eq_univ`, which this sentence asserted before
  anything compiled it ; so this is a statement about the plan's proper `V` and not about open
  immersions in general. And `Polynomial.Monic` does not give positive degree:
  `StandardEtalePair` asks only `StandardEtalePair.monic_f`, so `d = 0` is permitted by the
  types ; but then `q v = 1`, the hypersurface is empty, and the composite is finite for the
  reason that there is nothing to map. The plan is not for that case either, since
  `StandardEtalePair.Ring` is the zero ring when `f` is a unit.

  **What this repository does not have is the surjectivity statement**, and that is worth
  recording ; but as the missing *citation* for a settled conclusion, not as an open question.
  `grep -rn 'surjective.*projRestrict\|range_base_projRestrict' Other/Oka/` returns **exactly
  one hit, and it is the line that prints the pattern**: the first alternative is a regular
  expression, and both of its halves stand in that order on the line quoting it ; and the second
  alternative is a bare literal that the same line contains outright, so anchoring only the first
  would not help. The command was empty until that line was written, **no declaration matches
  it**, and the one hit is the sentence saying so. **A pattern quoted inside the tree it searches
  is a member of its own corpus** ; and the repair is to say which hits are the quotation, not to
  delete the command, since naming the instrument is what makes the claim checkable at all. The
  same mechanism one level down is an *import* line sitting inside a Mathlib docstring, which
  pulls a hand-written import-closure parser into the whole of Mathlib; that one is written down
  beside the figures it damaged, in `Other/Oka/AnalyticSpace/OpenSubspace.lean`.

  The `range_base_*` family in `Other/Oka/AnalyticSpace/MonicProjection.lean` and
  `Other/Oka/AnalyticSpace/OpenBaseProjection.lean` is about the image of the hypersurface **in the
  cylinder**, not the image of its projection in the base. A reader who proves surjectivity will
  have closed this route, not opened it.

  What does repair it is restricting the inclusion too,
  with `ComplexAnalytic.AnalyticSpace.restrictHom`, whose base map is a restriction of
  `ComplexAnalytic.analytificationInclHom`'s and is therefore injective ; and, by
  `ComplexAnalytic.isClosedEmbedding_base_restrictHom` in `Other/Oka/AnalyticSpace/Restrict.lean`, a
  closed embedding as well, so the route would have been open to a cancellation lemma stated at
  either hypothesis. What comes out is finiteness over the part of the analytification lying above
  `V`, and **nothing relates that back to the whole of it**: `V` is open in `ℂ^n` and the
  analytification is closed in `ℂ^n`, so neither contains the other.

* **No `IsFiniteEtale`, and no bound on the fibres.** Both are `Other/Oka/AnalyticSpace/`'s and neither
  gains anything here; see that file's `## What is not here`, which is unchanged by this one.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic

variable {n : ℕ}

/-! ### Reading the last variable as the polynomial variable -/

/-- **A polynomial in `n + 1` variables, read as a polynomial in the last one over the first
`n`.**

`MvPolynomial.finSuccEquiv` is Mathlib's version of this and makes the variable `0` the
polynomial one; the variable that has to be split off here is the **last**, because that is the
one `ComplexAnalytic.AnalyticSpace.proj` forgets and the one
`ComplexAnalytic.localisationPresentation` adjoins. So this is built from
`ComplexAnalytic.localisationVarEquiv`, the same reindexing
`ComplexAnalytic.polyPresentedAlgebraEquiv` uses, and not from `finSuccEquiv`. -/
def lastVarPolyEquiv (n : ℕ) :
    MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ ≃ₐ[ℂ]
      Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ) :=
  (MvPolynomial.renameEquiv ℂ (localisationVarEquiv.{u} n)).trans
    (MvPolynomial.optionEquivLeft ℂ (ULift.{u} (Fin n)))

/-- The last variable is the polynomial variable. -/
@[simp]
theorem lastVarPolyEquiv_X_localisationVar :
    lastVarPolyEquiv.{u} n (MvPolynomial.X (localisationVar.{u} n)) = Polynomial.X := by
  simp [lastVarPolyEquiv]

/-- Each of the first `n` variables is a constant, namely itself. -/
@[simp]
theorem lastVarPolyEquiv_X_localisationIncl (i : ULift.{u} (Fin n)) :
    lastVarPolyEquiv.{u} n (MvPolynomial.X (localisationIncl.{u} n i)) =
      Polynomial.C (MvPolynomial.X i) := by
  simp [lastVarPolyEquiv]

/-- **A polynomial in the first `n` variables is a constant**, which is the two `simp` lemmas
above read at a whole polynomial rather than at a variable.

`MvPolynomial.algHom_ext` reduces it to the variable case, which is
`ComplexAnalytic.lastVarPolyEquiv_X_localisationIncl`: both sides are `ℂ`-algebra maps
`MvPolynomial (ULift (Fin n)) ℂ ⟶ Polynomial (MvPolynomial (ULift (Fin n)) ℂ)`, one the
renaming followed by the equivalence and the other `Polynomial.C`. -/
theorem lastVarPolyEquiv_rename_localisationIncl (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    lastVarPolyEquiv.{u} n (MvPolynomial.rename (localisationIncl.{u} n) p) = Polynomial.C p := by
  have key : ((lastVarPolyEquiv.{u} n).toAlgHom.comp
      (MvPolynomial.rename (localisationIncl.{u} n) : _ →ₐ[ℂ] _)) =
      (Polynomial.CAlgHom.comp (AlgHom.id ℂ _) :
        MvPolynomial (ULift.{u} (Fin n)) ℂ →ₐ[ℂ]
          Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ)) :=
    MvPolynomial.algHom_ext fun i ↦ by simp
  exact congrArg (fun f ↦ f p) (congrArg (fun f : _ →ₐ[ℂ] _ ↦ (f : _ → _)) key)

/-- **The constants come back as polynomials in the first `n` variables**: the inverse reading of
`ComplexAnalytic.lastVarPolyEquiv_rename_localisationIncl`.

Stated because a *consumer* of `ComplexAnalytic.lastVarPolyEquiv` builds a polynomial in `n + 1`
variables out of a one-variable one ; which is what `ComplexAnalytic.hypersurfacePresentation`
takes ; and then has to evaluate it; the two `simp` lemmas above go the other way and say
nothing about `.symm`. -/
theorem lastVarPolyEquiv_symm_C (p : MvPolynomial (ULift.{u} (Fin n)) ℂ) :
    (lastVarPolyEquiv.{u} n).symm (Polynomial.C p) =
      MvPolynomial.rename (localisationIncl.{u} n) p := by
  rw [← lastVarPolyEquiv_rename_localisationIncl.{u} p, AlgEquiv.symm_apply_apply]

/-- **The polynomial variable comes back as the last variable**, the companion of
`ComplexAnalytic.lastVarPolyEquiv_symm_C` at `Polynomial.X`. -/
theorem lastVarPolyEquiv_symm_X :
    (lastVarPolyEquiv.{u} n).symm Polynomial.X = MvPolynomial.X (localisationVar.{u} n) := by
  rw [← lastVarPolyEquiv_X_localisationVar.{u} (n := n), AlgEquiv.symm_apply_apply]

/-- **A point of `ℂ^(n+1)` is its first `n` coordinates together with its last**, in the form
`MvPolynomial.eval_rename` consumes: reading the point through
`ComplexAnalytic.localisationVarEquiv` and splitting it at `none` recovers it. -/
theorem localisationVarEquiv_comp_eq (z : ULift.{u} (Fin (n + 1)) → ℂ) :
    (fun o : Option (ULift.{u} (Fin n)) ↦
        o.elim (z (localisationVar.{u} n)) fun i ↦ z (localisationIncl.{u} n i)) ∘
      localisationVarEquiv.{u} n = z := by
  funext i
  obtain ⟨i⟩ := i
  refine Fin.lastCases ?_ ?_ i
  · change (localisationVarEquiv.{u} n (localisationVar.{u} n)).elim _ _ = _
    rw [localisationVarEquiv_localisationVar]
    rfl
  · intro j
    change (localisationVarEquiv.{u} n (localisationIncl.{u} n (ULift.up j))).elim _ _ = _
    rw [localisationVarEquiv_localisationIncl]
    rfl

/-- **Evaluating a polynomial in `n + 1` variables is evaluating its coefficients at the first
`n` coordinates and the result at the last.**

`MvPolynomial.eval_eq_eval_optionEquivLeft` is the general statement, in the mirror tree; the
only thing added here is the reindexing. -/
theorem eval_eq_eval_lastVarPolyEquiv (z : ULift.{u} (Fin (n + 1)) → ℂ)
    (p : MvPolynomial (ULift.{u} (Fin (n + 1))) ℂ) :
    MvPolynomial.eval z p =
      Polynomial.eval (z (localisationVar.{u} n))
        (Polynomial.map (MvPolynomial.eval fun i ↦ z (localisationIncl.{u} n i))
          (lastVarPolyEquiv.{u} n p)) := by
  conv_lhs => rw [← localisationVarEquiv_comp_eq z]
  rw [← MvPolynomial.eval_rename, MvPolynomial.eval_eq_eval_optionEquivLeft]
  rfl

/-! ### The family of a polynomial -/

variable (G : Polynomial (MvPolynomial (ULift.{u} (Fin n)) ℂ))

/-- **The family of one-variable polynomials of `G`**: the coefficients of `G`, which are
polynomials in the first `n` variables, evaluated at a point of `ℂ^n`. -/
def polyFamily (w : ULift.{u} (Fin n) → ℂ) : Polynomial ℂ :=
  G.map (MvPolynomial.eval w)

/-- **Every member of the family of a monic `G` is monic.** -/
theorem monic_polyFamily (hG : G.Monic) (w : ULift.{u} (Fin n) → ℂ) :
    (polyFamily.{u} G w).Monic :=
  hG.map _

/-- **Every member has the same degree**, which is the hypothesis
`ComplexAnalytic.isFinite_comp_proj_of_range_eq` cannot weaken to a bound. -/
theorem natDegree_polyFamily (hG : G.Monic) (w : ULift.{u} (Fin n) → ℂ) :
    (polyFamily.{u} G w).natDegree = G.natDegree :=
  hG.natDegree_map _

/-- **The coefficients vary continuously**, because each of them is a polynomial function of the
base point: `(polyFamily G w).coeff j` is `MvPolynomial.eval w (G.coeff j)`. No monicity is
needed and no holomorphy is used. -/
theorem continuous_coeff_polyFamily (j : ℕ) :
    Continuous fun w : ULift.{u} (Fin n) → ℂ ↦ (polyFamily.{u} G w).coeff j := by
  simp only [polyFamily, Polynomial.coeff_map]
  exact MvPolynomial.continuous_eval _

/-- **The value of `G` at a point of `ℂ^(n+1)` is the value of its family at the first `n`
coordinates, evaluated at the last.**

This is `ComplexAnalytic.eval_eq_eval_lastVarPolyEquiv` with the two spellings of the splitting
identified: `(uliftSnocHomeo n z).1` is `z ∘ localisationIncl n` and `(uliftSnocHomeo n z).2` is
`z (localisationVar n)`, both definitionally. -/
theorem eval_lastVarPolyEquiv_symm (z : ULift.{u} (Fin (n + 1)) → ℂ) :
    MvPolynomial.eval z ((lastVarPolyEquiv.{u} n).symm G) =
      (polyFamily.{u} G (uliftSnocHomeo.{u} n z).1).eval (uliftSnocHomeo.{u} n z).2 := by
  rw [eval_eq_eval_lastVarPolyEquiv, AlgEquiv.apply_symm_apply]
  rfl

/-! ### The global section of a polynomial -/

/-- **The entire function on `ℂ^(n+1)` that `G` defines**: `G` read back as a polynomial in
`n + 1` variables, then as a holomorphic function by `OkaRing.ofMvPolynomial`. -/
def lastVarSection : OkaRing (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ)) :=
  OkaRing.ofMvPolynomial ⊤ ((lastVarPolyEquiv.{u} n).symm G)

/-- **Its value at a point is the value of the family**, which is the hypothesis `hF` of
`ComplexAnalytic.isFinite_comp_proj_of_isCutOutBy`. -/
theorem evalHom_lastVarSection (z : ULift.{u} (Fin (n + 1)) → ℂ) :
    OkaRing.evalHom (U := ⊤) (x := z) trivial (lastVarSection.{u} G) =
      (polyFamily.{u} G (uliftSnocHomeo.{u} n z).1).eval (uliftSnocHomeo.{u} n z).2 := by
  rw [lastVarSection, OkaRing.evalHom_ofMvPolynomial]
  exact eval_lastVarPolyEquiv_symm.{u} G z

/-! ### Finiteness of the projection -/

variable {W : AnalyticSpace.{u}}

/-- **A hypersurface of `ℂ^(n+1)` cut out by a polynomial monic in the last variable is finite
over `ℂ^n`.**

The first consumer of `ComplexAnalytic.isFinite_comp_proj_of_isCutOutBy`: every one of its four
hypotheses on the family is supplied above, and the caller is left with the cut-out datum, which
is what says that `W` is that hypersurface. -/
theorem isFinite_comp_proj_of_monic (i : W ⟶ AnalyticSpace.complexAffineSpace.{u} (n + 1))
    (hcut : IsCutOutBy i.toLRSHom ![lastVarSection.{u} G]) (hG : G.Monic) :
    AnalyticSpace.IsFinite (i ≫ AnalyticSpace.proj.{u} n) :=
  isFinite_comp_proj_of_isCutOutBy i hcut (monic_polyFamily.{u} G hG)
    (natDegree_polyFamily.{u} G hG) (continuous_coeff_polyFamily.{u} G)
    (evalHom_lastVarSection.{u} G)

/-- **The analytification of `ℂ[x₁, …, x_n, X] ⧸ (G)`, for `G` monic in `X`, is finite over
`ℂ^n`.**

No cut-out datum is a hypothesis here: the analytification comes with its own inclusion, whose
image `ComplexAnalytic.range_base_analytificationIncl` computes and whose closed-embedding
property `ComplexAnalytic.isClosedEmbedding_base_analytificationIncl` supplies. So this goes
through `ComplexAnalytic.isFinite_comp_proj_of_range_eq` rather than through the
`ComplexAnalytic.IsCutOutBy` form above, and it has no hypothesis but the monicity of `G`.

Both of those are stated for `ComplexAnalytic.analytificationIncl` and this is about
`ComplexAnalytic.analytificationInclHom`, which is `⟨ComplexAnalytic.analytificationIncl g, _⟩`;
they apply definitionally and no bridge lemma is needed. A reader grepping the proof for
`analytificationIncl` will not find it spelled that way.

**The target is `ℂ^n`, and the Riemann-existence line wants the analytification of a base
algebra.** That analytification sits inside `ℂ^n` as a closed subspace, and the arrow between the
two statements is `ComplexAnalytic.AnalyticSpace.isFinite_of_isFinite_comp`: it cancels an
**injective second factor**, so applying it here means cancelling
`ComplexAnalytic.analytificationInclHom` for the base algebra, whose base map is injective by
`ComplexAnalytic.isClosedEmbedding_base_analytificationIncl`. **That is now done**, in
`Other/Oka/Analytification/HypersurfaceFinite.lean`:
`ComplexAnalytic.analytificationMap_hypersurfacePresHom_comp` is the factorisation this paragraph
said no statement supplied, and
`ComplexAnalytic.isFinite_analytificationMap_hypersurfacePresHom` is the conclusion ; the
analytification of `A ⟶ A[X] ⧸ (F)` is finite over `A^an` for any presented `A`.

**Until 2026-08-31 this paragraph said the factorisation was the only thing missing, and it was
one of two.** The other is not in the arrow but in
`ComplexAnalytic.isFinite_comp_proj_of_range_eq`, which the theorem below applies: its range
hypothesis is an **equality** with the hypersurface, and the analytification of a base algebra's
hypersurface is cut out by the relations of that algebra as well as by `G`, so its image is a
proper closed subset of the hypersurface as soon as the base has a relation.
`ComplexAnalytic.isFinite_comp_proj_of_range_subset` (`Other/Oka/AnalyticSpace/MonicProjection.lean`) is
that hypothesis weakened to an inclusion, which is all the proof ever used;
`ComplexAnalytic.isFinite_comp_proj_of_range_eq` is now one line of it.
`Other/Oka/AnalyticSpace/Finite.lean`'s `## Main results` names this file from the other side. -/
theorem isFinite_analytification_comp_proj (hG : G.Monic) :
    AnalyticSpace.IsFinite
      (analytificationInclHom.{u} ![(lastVarPolyEquiv.{u} n).symm G] ≫
        AnalyticSpace.proj.{u} n) := by
  refine isFinite_comp_proj_of_range_eq _
    (isClosedEmbedding_base_analytificationIncl.{u} _) (monic_polyFamily.{u} G hG)
    (natDegree_polyFamily.{u} G hG) (continuous_coeff_polyFamily.{u} G) ?_
  refine Eq.trans (range_base_analytificationIncl.{u} _) ?_
  ext z
  simp only [Set.mem_setOf_eq, Fin.forall_fin_one, Matrix.cons_val_zero]
  rw [eval_lastVarPolyEquiv_symm.{u} G]
  exact Iff.rfl

end ComplexAnalytic

end

end
