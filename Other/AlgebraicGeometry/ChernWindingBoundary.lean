/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernWindingCochain
public import Other.AlgebraicTopology.NormalProjectionCoclass

/-!
# The connecting map of a pair and the winding class with support

Let `S ⊆ M` be a support and `W ⊆ M` a neighbourhood.  The pair `(W, W ∖ S)` has a homology
connecting map `∂ : H₂(W, W ∖ S; ℚ) → H₁(W ∖ S; ℚ)`
(`AlgebraicTopology.Singular.relativeSingularBoundary`, already in the repository), and the
repository's relative *cohomology* is by definition the linear dual of relative homology.  So a
functional on `H₁(W ∖ S; ℚ)` is transported to a functional on `H₂(W, W ∖ S; ℚ)` simply by
precomposition with `∂`; no long exact sequence in cohomology is needed.

Composing with `ChernWinding.windingPeriod` gives, for a continuous nowhere vanishing `g` on
`W ∖ S`, the **relative winding period**

  `relativeWindingPeriod g : H₂(W, W ∖ S; ℚ) →ₗ[ℚ] ℂ`,

additive in `g` (`relativeWindingPeriod_mul`) and zero whenever `g` has a global continuous
logarithm on `W ∖ S` (`relativeWindingPeriod_eq_zero_of_exp`).  This *is* the composite
`∂ ∘ δ` of the two connecting maps that the winding homomorphism of
`Other/AlgebraicGeometry/ChernLocalModelWinding.lean` is made of, at the level of complex
periods.

The period takes complex values; the repository's supported cohomology is rational.  The
remaining input is therefore the *integrality of the periods*, isolated as

  `HasRationalWindingPeriod W S g hg : Prop`,

which says that `relativeWindingPeriod g` is the complexification of a rational functional.  It
is a statement with no sheaf theory in it: since `relativeWindingPeriod g` is, on the class of an
integral cycle, the winding number of `g` along it, it is an integer, and the obligation is the
(purely topological) fact that `H₂(W, W ∖ S; ℚ)` is spanned by classes whose boundaries come from
integral cycles.  Granted it, `windingRelativeClass` is the honest supported cohomology class.

The last section records the normalisation criterion: by
`AlgebraicTopology.Singular.chartNormalProjectionCoclass_unique`, on a flattening chart of a
codimension-one support the winding class *is* the normalised normal-chart coclass as soon as its
period on the explicit local normal class is `1`.  That single equation
(`windingPeriod g (∂ (flattenedSupportNormalClass …)) = 1`) is the entire content of the
normalisation obligation `ChernWindingChart.NormalizesCoclass`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicTopology.Singular

namespace ChernWinding

variable {M : Type} [TopologicalSpace M] (W S : Set M)

/-- The pair `(W, W ∖ S)` of a neighbourhood and the complement of the support in it. -/
abbrev supportPair : TopPair := neighborhoodSupportComplementPair W S

/-- The punctured neighbourhood `W ∖ S`, as a topological space. -/
abbrev puncturedSpace : TopCat.{0} := (supportPair W S).snd

/-! ### The relative winding period -/

/-- **The relative winding period.**  The winding period of `g` on `W ∖ S`, transported to the
relative homology of the pair `(W, W ∖ S)` along the homology connecting map.  This is the
composite `∂ ∘ δ` of the winding-number connecting map of the exponential sequence with the
connecting map of the pair. -/
def relativeWindingPeriod (g : C(puncturedSpace W S, ℂ)) (hg : ∀ y, g y ≠ 0) :
    ComplexPeriodSpace (RelativeHomology ℚ (supportPair W S) 2) :=
  (windingPeriod g hg).comp (relativeSingularBoundary (supportPair W S) 1).hom

theorem relativeWindingPeriod_apply (g : C(puncturedSpace W S, ℂ)) (hg : ∀ y, g y ≠ 0)
    (z : RelativeHomology ℚ (supportPair W S) 2) :
    relativeWindingPeriod W S g hg z =
      windingPeriod g hg ((relativeSingularBoundary (supportPair W S) 1).hom z) :=
  rfl

/-- The relative winding period is additive in the function. -/
theorem relativeWindingPeriod_mul (g h k : C(puncturedSpace W S, ℂ))
    (hg : ∀ y, g y ≠ 0) (hh : ∀ y, h y ≠ 0) (hk : ∀ y, k y ≠ 0)
    (hmul : ∀ y, k y = g y * h y) :
    relativeWindingPeriod W S k hk =
      relativeWindingPeriod W S g hg + relativeWindingPeriod W S h hh := by
  ext z
  simp only [relativeWindingPeriod_apply, LinearMap.add_apply]
  rw [windingPeriod_mul g h k hg hh hk hmul]
  rfl

/-- A function with a global continuous logarithm has vanishing relative winding period. -/
theorem relativeWindingPeriod_eq_zero_of_exp (g f : C(puncturedSpace W S, ℂ))
    (hg : ∀ y, g y ≠ 0) (hfg : ∀ y, Complex.exp (f y) = g y) :
    relativeWindingPeriod W S g hg = 0 := by
  ext z
  rw [relativeWindingPeriod_apply, windingPeriod_eq_zero_of_exp g f hg hfg]
  rfl

/-! ### Rationality of the periods, and the resulting supported class -/

/-- **The integrality obligation.**  The relative winding period of `g` is the complexification
of a rational relative cohomology class.

This is the only missing input in the construction of the winding homomorphism, and it contains
no sheaf theory: `relativeWindingPeriod` evaluated on the class of an integral relative `2`-cycle
is the winding number of `g` along the boundary `1`-cycle, hence an integer. -/
def HasRationalWindingPeriod (g : C(puncturedSpace W S, ℂ)) (hg : ∀ y, g y ≠ 0) : Prop :=
  ∃ a : RelativeCohomology ℚ (supportPair W S) 2,
    rationalPeriod (RelativeHomology ℚ (supportPair W S) 2) a = relativeWindingPeriod W S g hg

/-- The rational relative cohomology class with support cut out by the winding period. -/
def windingRelativeClass {g : C(puncturedSpace W S, ℂ)} {hg : ∀ y, g y ≠ 0}
    (h : HasRationalWindingPeriod W S g hg) :
    RelativeCohomology ℚ (supportPair W S) 2 :=
  h.choose

theorem rationalPeriod_windingRelativeClass {g : C(puncturedSpace W S, ℂ)} {hg : ∀ y, g y ≠ 0}
    (h : HasRationalWindingPeriod W S g hg) :
    rationalPeriod (RelativeHomology ℚ (supportPair W S) 2) (windingRelativeClass W S h) =
      relativeWindingPeriod W S g hg :=
  h.choose_spec

theorem windingRelativeClass_apply {g : C(puncturedSpace W S, ℂ)} {hg : ∀ y, g y ≠ 0}
    (h : HasRationalWindingPeriod W S g hg) (z : RelativeHomology ℚ (supportPair W S) 2) :
    ((windingRelativeClass W S h z : ℚ) : ℂ) = relativeWindingPeriod W S g hg z :=
  LinearMap.congr_fun (rationalPeriod_windingRelativeClass W S h) z

/-- The winding class is determined by the period. -/
theorem windingRelativeClass_unique {g : C(puncturedSpace W S, ℂ)} {hg : ∀ y, g y ≠ 0}
    (h : HasRationalWindingPeriod W S g hg) (a : RelativeCohomology ℚ (supportPair W S) 2)
    (ha : rationalPeriod (RelativeHomology ℚ (supportPair W S) 2) a =
      relativeWindingPeriod W S g hg) :
    a = windingRelativeClass W S h :=
  rationalPeriod_injective _ (ha.trans (rationalPeriod_windingRelativeClass W S h).symm)

/-- The winding class is additive in the function. -/
theorem windingRelativeClass_mul {g h k : C(puncturedSpace W S, ℂ)}
    {hg : ∀ y, g y ≠ 0} {hh : ∀ y, h y ≠ 0} {hk : ∀ y, k y ≠ 0}
    (hmul : ∀ y, k y = g y * h y)
    (hrg : HasRationalWindingPeriod W S g hg) (hrh : HasRationalWindingPeriod W S h hh)
    (hrk : HasRationalWindingPeriod W S k hk) :
    windingRelativeClass W S hrk =
      windingRelativeClass W S hrg + windingRelativeClass W S hrh := by
  refine (windingRelativeClass_unique W S hrk _ ?_).symm
  rw [map_add, rationalPeriod_windingRelativeClass, rationalPeriod_windingRelativeClass,
    relativeWindingPeriod_mul W S g h k hg hh hk hmul]

/-- The winding class of a function with a global continuous logarithm vanishes. -/
theorem windingRelativeClass_eq_zero_of_exp {g : C(puncturedSpace W S, ℂ)}
    {hg : ∀ y, g y ≠ 0} (f : C(puncturedSpace W S, ℂ))
    (hfg : ∀ y, Complex.exp (f y) = g y) (h : HasRationalWindingPeriod W S g hg) :
    windingRelativeClass W S h = 0 := by
  refine (windingRelativeClass_unique W S h 0 ?_).symm
  rw [map_zero, relativeWindingPeriod_eq_zero_of_exp W S g f hg hfg]

/-! ### The normalisation criterion on a flattening chart -/

section Normalization

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (e : OpenPartialHomeomorph M (E × (Fin 1 → ℂ))) {S}
  (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
  (x : M) (hx : x ∈ e.source) (h0 : (e x).2 = 0)

/-- **The normalisation criterion.**  On the flattening chart of a codimension-one support, the
winding class of `g` is the normalised normal-chart coclass as soon as the winding period of `g`
on the boundary of the explicit local normal class equals `1`.

The hypothesis is a single number: the winding number of `g` around the normal `1`-sphere of the
support.  This is exactly the one-variable Lelong–Poincaré computation, with no sheaf theory and
no Chern class in it. -/
theorem windingRelativeClass_eq_chartNormalProjectionCoclass
    {g : C(puncturedSpace ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) :
        Set M) S, ℂ)}
    {hg : ∀ y, g y ≠ 0}
    (h : HasRationalWindingPeriod
      ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M) S g hg)
    (hone : windingPeriod g hg
      ((relativeSingularBoundary
        (supportPair ((flattenedSupportNeighborhood E 1 e x hx :
          TopologicalSpace.Opens M) : Set M) S) 1).hom
        (flattenedSupportNormalClass E 1 e x hx S hS h0)) = 1) :
    windingRelativeClass
        ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M) S h =
      chartNormalProjectionCoclass E 1 e S hS (flattenedSupportNeighborhood E 1 e x hx)
        (flattenedSupportNeighborhood_subset_source E 1 e x hx) := by
  refine chartNormalProjectionCoclass_unique E 1 e S hS x hx h0 _ ?_
  have hval := windingRelativeClass_apply
    ((flattenedSupportNeighborhood E 1 e x hx : TopologicalSpace.Opens M) : Set M) S h
    (flattenedSupportNormalClass E 1 e x hx S hS h0)
  rw [relativeWindingPeriod_apply, hone] at hval
  exact_mod_cast hval

end Normalization

end ChernWinding
