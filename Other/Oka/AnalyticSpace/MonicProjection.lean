/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.Finite
public import Other.Oka.AnalyticSpace.ProjectionStalk
public import Other.Oka.Topology.Algebra.Polynomial

/-!
# The projection of a monic hypersurface to its base is finite

Let `i : X ⟶ ℂ^(n+1)` be a closed embedding of complex analytic spaces whose image is the zero
locus of a function which, in the last variable, is a **monic polynomial of one fixed degree**
with continuously varying coefficients ; a Weierstrass polynomial, in the case this development
is aiming at. Then the composite

    X ⟶ ℂ^(n+1) ⟶ ℂ^n

with the projection forgetting the last coordinate is `ComplexAnalytic.AnalyticSpace.IsFinite`:
closed, with finite fibres.

This is the topological half of *the analytification of a standard étale morphism is finite
étale*; `Other/Oka/AnalyticSpace/SimpleZeroStalk.lean` is the stalk half, for the same composite
`i ≫ ComplexAnalytic.AnalyticSpace.proj`, and the two are what
`ComplexAnalytic.AnalyticSpace.IsFiniteEtale` asks for.

## Where the mathematics is, and it is not here

**All of it is in `Other/Oka/Topology/Algebra/Polynomial.lean`**, which is in the mirror tree and
mentions nothing analytic: the roots of a monic polynomial are bounded by its coefficients, so a
closed set of roots of a continuous family has closed image in the parameters
(`Polynomial.isClosed_fst_image_of_monic`) and meets each fibre in a finite set
(`Polynomial.finite_inter_fst_preimage_of_monic`). This file is the assembly, and it is three
steps:

* **a criterion** ; `ComplexAnalytic.AnalyticSpace.isFinite_comp_of_isClosedEmbedding` reduces
  `IsFinite (i ≫ p)` to those two statements *about the image of `i`*, which is what lets the
  projection be used even though it is not itself finite;
* **a carrier bridge** ; `ComplexAnalytic.uliftSnocHomeo`, the homeomorphism
  `ℂ^(n+1) ≃ₜ ℂ^n × ℂ` splitting off the last coordinate, across which the two set-level
  statements are read;
* **the image of `i`** ; `ComplexAnalytic.range_base_eq_of_isCutOutBy` turns
  `ComplexAnalytic.IsCutOutBy`'s `range_base` field, which is phrased with germs and maximal
  ideals, into the vanishing of a function, by `germ_mem_maximalIdeal_iff`.

## The three spellings of the hypothesis on the image

`ComplexAnalytic.isFinite_comp_proj_of_range_subset` takes the image of `i` as a set
**inclusion**, `ComplexAnalytic.isFinite_comp_proj_of_range_eq` as a set **equation**, and neither
asks anything about structure sheaves; `ComplexAnalytic.isFinite_comp_proj_of_isCutOutBy` takes
`ComplexAnalytic.IsCutOutBy i.toLRSHom ![F]` and the pointwise identity between `F` and the
family. **The inclusion is the general one and the other two are corollaries of it** ; it is what
a source cut out by **more** equations than the family gives, which is the analytification of a
base algebra's hypersurface (`Other/Oka/Analytification/HypersurfaceFinite.lean`); a caller holding an
equation should still quote **the equation form**, which is one line of the inclusion and keeps
its own name and its consumers. **The equation form** is the one a hand-built morphism satisfies ;
cut-out data for a *hand-built* morphism of analytic spaces still has to be built by hand, which
is a claim about those morphisms and not about the category:
`ComplexAnalytic.isCutOutBy_analytificationInclHom` produces the datum for the inclusion of an
analytification into `ℂ^n`, and nothing built by hand is one.
**The `ComplexAnalytic.IsCutOutBy` form** is the one the Weierstrass line will consume, and is two
lines of the equation form.

**None of the three takes the family from `F`.** The family `q` is an argument, and the hypothesis
relating it to `F` is an equation the caller proves; nothing here extracts the coefficients of a
holomorphic function in its last variable, and no holomorphy of the coefficients is used ;
continuity is all the mathematics needs, and it is all that is asked for.

## Main results

- `ComplexAnalytic.uliftSnocHomeo`: **the last coordinate splits off `ℂ^(n+1)` as a
  homeomorphism onto `ℂ^n × ℂ`**, compatibly with the projection
  (`ComplexAnalytic.base_proj_eq`).
- `ComplexAnalytic.range_base_eq_of_isCutOutBy`: **a hypersurface cut out by one global section
  of `𝒪_{ℂ^m}` has that section's zero set for its image.**
- `ComplexAnalytic.isFinite_comp_proj_of_range_subset`: **a closed subspace of a monic
  hypersurface is finite over the base**, the hypersurface being the zero locus of a continuous
  family of monic polynomials of one fixed degree. Both obligations are asked only along the image,
  so an image strictly inside the hypersurface is no harder ; which is what a subspace cut out by
  further equations, such as the analytification of a base algebra's hypersurface, needs.
- `ComplexAnalytic.isFinite_comp_proj_of_range_eq`: **the projection of a monic hypersurface to
  its base is finite**, the case of the above where the image is the whole hypersurface.
- `ComplexAnalytic.isFinite_comp_proj_of_isCutOutBy`: the same with the hypersurface presented as
  a cut-out by one global section rather than as a set.

## What is not here

* **No `IsFiniteEtale`, and no `IsLocalIso`.** The stalk half is
  `Other/Oka/AnalyticSpace/SimpleZeroStalk.lean` and the topological half of `IsLocalIso` ; that the
  underlying map is a local homeomorphism ; is neither here nor there. Nothing below says the
  composite is open, and for a monic family with repeated roots it is not a local
  homeomorphism at all, so this is not a gap that closes by an argument of the same kind.
* **No open subset of the base ; this is no longer absent, and it is not in this file.** `i`
  lands in the whole of `ℂ^(n+1)` below, and that has not changed; what has is that the transport
  exists. `ComplexAnalytic.isFinite_comp_projRestrict_of_range_eq` in
  `Other/Oka/AnalyticSpace/OpenBaseProjection.lean`, which imports this file, is the theorem below with
  `ComplexAnalytic.uliftSnocHomeo` replaced by its restriction `ComplexAnalytic.cylinderHomeo` to
  the cylinder over an open `V`. The standard étale line wants it because such an algebra inverts
  a polynomial as well as cutting one out, so its analytification lives in an open subspace, as
  it does in `Other/Oka/AnalyticSpace/SimpleZeroStalk.lean` and for the same reason. The paragraph that
  used to stand here predicted that **what is missing is the bridge and not the mathematics**,
  because the mirror-tree theorems take an arbitrary topological parameter space; that came out
  right ; `Polynomial.isClosed_fst_image_of_monic` and
  `Polynomial.finite_inter_fst_preimage_of_monic` are instantiated at `V` there, and
  `Other/Oka/Topology/Algebra/Polynomial.lean` gained nothing.
* **No Weierstrass polynomial.** Nothing here produces the family `q` from a germ, which is what
  `Other/Oka/Weierstrass.lean`'s preparation theorem is for; the family is a hypothesis. In particular
  the degree is *fixed*, not merely bounded ; a family whose leading coefficient degenerates has
  roots escaping to infinity and the projection is then not closed, which is why
  `Polynomial.isClosed_fst_image_of_monic` asks for `natDegree = d` and not `≤ d`.
* **No bound on the fibres.** A fibre is finite; that it has at most `d` points is
  `Polynomial.card_roots'` and is not specialised, here or in the mirror tree.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984]
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic

variable {n : ℕ}

/-! ### Splitting off the last coordinate -/

/-- **The homeomorphism `ℂ^(n+1) ≃ₜ ℂ^n × ℂ` splitting off the last coordinate.**

The coordinates of `ComplexAnalytic.AnalyticSpace.complexAffineSpace` are indexed by
`ULift (Fin n)`, so this is `Fin.snoc` with a `ULift` on either side of it; the inverse is
`Fin.lastCases`, which is what makes the two round trips one `Fin.lastCases` each.

`ComplexAnalytic.base_proj_eq` is the compatibility that makes it the right bridge: the first
component **is** the underlying map of `ComplexAnalytic.AnalyticSpace.proj`. -/
def uliftSnocHomeo (n : ℕ) :
    (ULift.{u} (Fin (n + 1)) → ℂ) ≃ₜ ((ULift.{u} (Fin n) → ℂ) × ℂ) where
  toFun z := (fun j ↦ z (ULift.up j.down.castSucc), z (ULift.up (Fin.last n)))
  invFun w j := Fin.lastCases w.2 (fun k ↦ w.1 (ULift.up k)) j.down
  left_inv z := by
    funext j
    obtain ⟨j⟩ := j
    refine Fin.lastCases ?_ ?_ j <;> simp
  right_inv w := by
    obtain ⟨w, c⟩ := w
    refine Prod.ext ?_ ?_
    · funext j
      obtain ⟨j⟩ := j
      simp
    · simp
  continuous_toFun := (continuous_pi fun _ ↦ continuous_apply _).prodMk (continuous_apply _)
  continuous_invFun := by
    refine continuous_pi fun j ↦ ?_
    obtain ⟨j⟩ := j
    refine Fin.lastCases ?_ ?_ j
    · simpa using continuous_snd
    · intro k
      simp only [Fin.lastCases_castSucc]
      exact (continuous_apply (ULift.up k)).comp continuous_fst

@[simp]
theorem uliftSnocHomeo_apply (z : ULift.{u} (Fin (n + 1)) → ℂ) :
    uliftSnocHomeo.{u} n z =
      (fun j ↦ z (ULift.up j.down.castSucc), z (ULift.up (Fin.last n))) :=
  rfl

/-- **Its first component is the map underlying the projection `ℂ^(n+1) ⟶ ℂ^n`.** -/
theorem uliftSnocHomeo_fst (z : ULift.{u} (Fin (n + 1)) → ℂ) :
    (uliftSnocHomeo.{u} n z).1 = okaMapFun (coordEmb (uliftCastSuccEmb.{u} n)) z := by
  rw [okaMapFun_coordEmb]
  rfl

/-- **The projection is the first projection of the product, read through
`ComplexAnalytic.uliftSnocHomeo`.**

The composite form rather than the pointwise one, because it is what lets a statement about
`Prod.fst` transfer along a homeomorphism. -/
theorem base_proj_eq (n : ℕ) :
    ⇑(AnalyticSpace.proj.{u} n).toLRSHom.base = Prod.fst ∘ uliftSnocHomeo.{u} n :=
  funext fun z ↦ (uliftSnocHomeo_fst z).symm

/-! ### The image of a hypersurface -/

/-- **A morphism cutting its source out of `ℂ^m` by a single global section has that section's
zero set for its image.**

`ComplexAnalytic.IsCutOutBy`'s `range_base` field states the image as the set where every germ
is a non-unit; on `ℂ^m` a germ is a non-unit exactly when the function vanishes, which is
`germ_mem_maximalIdeal_iff`. The `Fin 1` quantifier disappears by `fin_cases`.

Stated for one section because a hypersurface is what the finiteness theorem below is about; the
same proof at `Fin k` would give the intersection of the `k` zero sets. -/
theorem range_base_eq_of_isCutOutBy {m : ℕ} {W : AnalyticSpace.{u}}
    (i : W ⟶ AnalyticSpace.complexAffineSpace.{u} m)
    {F : OkaRing (⊤ : Opens (ULift.{u} (Fin m) → ℂ))}
    (hcut : IsCutOutBy i.toLRSHom ![F]) :
    Set.range (i.toLRSHom.base : W → _) =
      {z | OkaRing.evalHom (U := ⊤) (x := z) trivial F = 0} := by
  rw [hcut.range_base]
  ext z
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    exact (germ_mem_maximalIdeal_iff (U := ⊤) trivial F).1 (h 0)
  · intro h j
    fin_cases j
    exact (germ_mem_maximalIdeal_iff (U := ⊤) trivial F).2 h

/-! ### Finiteness of the projection -/

variable {d : ℕ} {W : AnalyticSpace.{u}}

/-- **A closed subspace of a monic hypersurface is finite over the base.**

`i` is any closed embedding of `W` into `ℂ^(n+1)` whose image is **contained in** the zero locus
of the family `q` of monic polynomials of one fixed degree `d`, read in the last coordinate; the
conclusion is that `i` followed by the projection forgetting that coordinate is closed with finite
fibres.

The whole proof is `ComplexAnalytic.AnalyticSpace.isFinite_comp_of_isClosedEmbedding` at the two
set-level theorems of `Other/Oka/Topology/Algebra/Polynomial.lean`, transported across
`ComplexAnalytic.uliftSnocHomeo`. **Continuity of the coefficients is the only analytic input and
it is a hypothesis**: no holomorphy is used, and `hc` is what a Weierstrass polynomial supplies.

**Why the hypothesis is an inclusion and not the equality
`ComplexAnalytic.isFinite_comp_proj_of_range_eq` asks for.** Both of the theorem's obligations are
*downward* closed in the image ; a smaller image inherits them: closedness of `π '' t` is asked
only of subsets `t` of that image, and the fibre obligation asks a set to be finite. So an image
sitting strictly inside the hypersurface is no harder, and this is the form a subspace cut out by
**more** equations than the one monic polynomial needs ; the zero locus of a presentation with
relations of its own, which is the analytification of a base algebra's hypersurface, is such a
subspace and the equality is then unavailable.
`ComplexAnalytic.isFinite_comp_proj_of_range_eq` is this theorem at `Eq.subset` and keeps its name
and its consumers. -/
theorem isFinite_comp_proj_of_range_subset
    (i : W ⟶ AnalyticSpace.complexAffineSpace.{u} (n + 1))
    (hi : IsClosedEmbedding (i.toLRSHom.base : W → _))
    {q : (ULift.{u} (Fin n) → ℂ) → Polynomial ℂ}
    (hm : ∀ w, (q w).Monic) (hd : ∀ w, (q w).natDegree = d)
    (hc : ∀ j, Continuous fun w ↦ (q w).coeff j)
    (hrange : Set.range (i.toLRSHom.base : W → _) ⊆
      {z | (q (uliftSnocHomeo.{u} n z).1).eval (uliftSnocHomeo.{u} n z).2 = 0}) :
    AnalyticSpace.IsFinite (i ≫ AnalyticSpace.proj.{u} n) := by
  refine AnalyticSpace.isFinite_comp_of_isClosedEmbedding i _ hi (fun t ht hsub ↦ ?_) (fun s ↦ ?_)
  · have himg : ⇑(AnalyticSpace.proj.{u} n).toLRSHom.base '' t
        = Prod.fst '' (uliftSnocHomeo.{u} n '' t) := by
      rw [base_proj_eq]
      exact Set.image_comp _ _ _
    rw [himg]
    refine Polynomial.isClosed_fst_image_of_monic hm hd hc
      ((uliftSnocHomeo.{u} n).isClosedMap t ht) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hrange (hsub hz)
  · refine Set.Finite.subset (Set.Finite.preimage (uliftSnocHomeo.{u} n).injective.injOn
      (Polynomial.finite_inter_fst_preimage_of_monic hm s fun y hy ↦ hy)) ?_
    intro z hz
    have hfib := hz.2
    rw [base_proj_eq] at hfib
    exact ⟨hrange hz.1, hfib⟩

/-- **The projection of a monic hypersurface to its base is finite.**

The special case of `ComplexAnalytic.isFinite_comp_proj_of_range_subset` where the image is the
whole hypersurface. It is kept under its own name because every consumer in the repository takes
this form, and because a caller with an equality should not have to know that the proof needs only
half of it. -/
theorem isFinite_comp_proj_of_range_eq
    (i : W ⟶ AnalyticSpace.complexAffineSpace.{u} (n + 1))
    (hi : IsClosedEmbedding (i.toLRSHom.base : W → _))
    {q : (ULift.{u} (Fin n) → ℂ) → Polynomial ℂ}
    (hm : ∀ w, (q w).Monic) (hd : ∀ w, (q w).natDegree = d)
    (hc : ∀ j, Continuous fun w ↦ (q w).coeff j)
    (hrange : Set.range (i.toLRSHom.base : W → _) =
      {z | (q (uliftSnocHomeo.{u} n z).1).eval (uliftSnocHomeo.{u} n z).2 = 0}) :
    AnalyticSpace.IsFinite (i ≫ AnalyticSpace.proj.{u} n) :=
  isFinite_comp_proj_of_range_subset.{u} i hi hm hd hc hrange.subset

/-- **The same, for a hypersurface presented by `ComplexAnalytic.IsCutOutBy`.**

`hF` is the identity that makes `F` the Weierstrass polynomial of the family `q`: its value at a
point of `ℂ^(n+1)` is the value of `q` at the first `n` coordinates, evaluated at the last one.
Nothing extracts `q` from `F`; see the module docstring. -/
theorem isFinite_comp_proj_of_isCutOutBy
    (i : W ⟶ AnalyticSpace.complexAffineSpace.{u} (n + 1))
    {F : OkaRing (⊤ : Opens (ULift.{u} (Fin (n + 1)) → ℂ))}
    (hcut : IsCutOutBy i.toLRSHom ![F])
    {q : (ULift.{u} (Fin n) → ℂ) → Polynomial ℂ}
    (hm : ∀ w, (q w).Monic) (hd : ∀ w, (q w).natDegree = d)
    (hc : ∀ j, Continuous fun w ↦ (q w).coeff j)
    (hF : ∀ z, OkaRing.evalHom (U := ⊤) (x := z) trivial F =
      (q (uliftSnocHomeo.{u} n z).1).eval (uliftSnocHomeo.{u} n z).2) :
    AnalyticSpace.IsFinite (i ≫ AnalyticSpace.proj.{u} n) :=
  isFinite_comp_proj_of_range_eq i hcut.isClosedEmbedding hm hd hc
    ((range_base_eq_of_isCutOutBy i hcut).trans (by simp only [hF]))

end ComplexAnalytic

end

end
