/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ClosedSupportCodimensionVanishing
public import Other.AlgebraicGeometry.ComponentSupportDecomposition

/-!
# Codimension of a closed subset from the coheight of its points, and the vanishing

The obligation `HasCodimensionTwoSupportedVanishing` of
`Other/AlgebraicGeometry/ComponentSupportDecomposition.lean` is proved here.

The geometric input is the dimension bound: if every point of a closed subset `W` of a smooth
projective complex `d`-fold has coheight — codimension — at least `q`, then
`dim W ≤ d - q`. The proof is the chain argument: a chain of irreducible closed subsets of `W`
of length `n` gives, through `irreducibleSetEquivPoints`, a chain of points of `X` of length `n`
whose last member `y` lies in `W`; then `n ≤ height y` and `q ≤ coheight y`, while
`height y + coheight y ≤ d` on a smooth complex scheme of relative dimension `d`.

Feeding this into the canonical smooth filtration of `W` bounds the relative dimension `m` of
every stratum by `m + q ≤ d`, i.e. bounds its normal codimension below by `q`, which is exactly
the datum `ClosedSupportStrataNormalCodimension` required by
`Other/AlgebraicGeometry/ClosedSupportCodimensionVanishing.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Order

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance closedSupportCoheightAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

/-! ### The dimension bound -/

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- **Codimension from coheight.** A closed subset all of whose points have coheight at least
`q` has dimension at most `d - q`. -/
theorem topologicalKrullDim_lt_of_forall_le_coheight
    {d q : ℕ} [SmoothOfRelativeDimension d X.hom] (W : Closeds X.left)
    (hW : ∀ z ∈ W, (q : ℕ∞) ≤ coheight z) :
    topologicalKrullDim W < ((d - q + 1 : ℕ) : WithBot ℕ∞) := by
  apply krullDim_lt_coe_iff.mpr
  intro l
  let φ := IrreducibleCloseds.map (Subtype.val : ↥W → X.left) continuous_subtype_val
  have hφ : StrictMono φ :=
    IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal
  set p : LTSeries X.left :=
    (l.map φ hφ).map irreducibleSetEquivPoints (OrderIso.strictMono _) with hp
  have hlast : p.last = irreducibleSetEquivPoints (φ l.last) := by
    rw [hp, LTSeries.last_map, LTSeries.last_map]
  have hmemW : p.last ∈ W := by
    have hgen : p.last ∈ ((φ l.last : IrreducibleCloseds X.left) : Set X.left) := by
      rw [hlast]
      exact ((φ l.last).2.isGenericPoint_genericPoint (φ l.last).isClosed').mem
    have hsub : ((φ l.last : IrreducibleCloseds X.left) : Set X.left) ⊆ (W : Set X.left) :=
      closure_minimal (by rintro _ ⟨x, _, rfl⟩; exact x.2) W.isClosed
    exact hsub hgen
  have h1 : (p.length : ℕ∞) ≤ height p.last := length_le_height_last
  have h2 : (q : ℕ∞) ≤ coheight p.last := hW _ hmemW
  have h3 : height p.last + coheight p.last ≤ (d : ℕ∞) :=
    SmoothOfRelativeDimension.height_add_coheight_le_complex (f := X.hom) p.last
  have h4 : ((p.length + q : ℕ) : ℕ∞) ≤ (d : ℕ∞) := by
    push_cast
    exact le_trans (add_le_add h1 h2) h3
  have h5 : p.length + q ≤ d := by exact_mod_cast h4
  have h6 : p.length = l.length := rfl
  omega

/-! ### The normal codimension of the strata -/

omit [IsIntegral X.left] [Smooth X.hom] in
/-- Every point of every stratum of the canonical filtration of `W` lies in `W`. -/
theorem closedSupportStratum_mem (W : Closeds X.left) (k : ℕ)
    (z : closedSupportStratum X W k) : closedSupportStratumι X W k z ∈ W :=
  closedSupportFiltration_le X W k
    (((closedSupportFiltration_layer X W k).le ⟨z, rfl⟩).1)

omit [IsIntegral X.left] [Smooth X.hom] in
/-- **The strata of a closed subset of codimension at least `q` have normal codimension at
least `q`.** -/
theorem closedSupportStrataNormalCodimension_of_forall_le_coheight
    {d q : ℕ} [SmoothOfRelativeDimension d X.hom] (W : Closeds X.left)
    (hW : ∀ z ∈ W, (q : ℕ∞) ≤ coheight z) :
    ClosedSupportStrataNormalCodimension X W d q := by
  intro k z
  have hqd : q ≤ d := by
    have h1 : (q : ℕ∞) ≤ coheight (closedSupportStratumι X W k z) :=
      hW _ (closedSupportStratum_mem X W k z)
    have h2 : coheight (closedSupportStratumι X W k z) ≤ (d : ℕ∞) :=
      SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) _
    exact_mod_cast h1.trans h2
  have hdim : topologicalKrullDim (closedSupportStratum X W k) < ((d - q + 1 : ℕ) : WithBot ℕ∞) :=
    (topologicalKrullDim_reducedClosedSmoothPiece_le X.hom
      (le_refl (closedSupportFiltration X W k))).trans_lt
      ((IsEmbedding.inclusion (closedSupportFiltration_le X W k)).isInducing.topologicalKrullDim_le.trans_lt
        (topologicalKrullDim_lt_of_forall_le_coheight X (d := d) (q := q) W hW))
  obtain ⟨A, _, hzA, m, hm, hstd⟩ :=
    Smooth.exists_affine_relativeDimension_lt_of_topologicalKrullDim_lt
      (closedSupportStratumι X W k ≫ X.hom) hdim z
  exact ⟨A, hzA, m, by omega,
    smoothOfRelativeDimension_affineOpen_of_isStandardSmooth _ ‹IsAffineOpen A› hstd⟩

/-! ### The obligation -/

/-- **The codimension-two vanishing.** Rational cohomology of `X^an` with support in the
analytic support of a Zariski-closed subset of codimension at least two vanishes in degree
three; this discharges the obligation of
`Other/AlgebraicGeometry/ComponentSupportDecomposition.lean`. -/
theorem hasCodimensionTwoSupportedVanishing : HasCodimensionTwoSupportedVanishing X := by
  intro W hW
  have hstr : ClosedSupportStrataNormalCodimension X W (dim X.left) 2 :=
    closedSupportStrataNormalCodimension_of_forall_le_coheight X W hW
  exact closedSupportSectionCohomology_isZero_of_lt hstr (2 * ((1 : ℕ) : ℤ) + 1) (by norm_num)

/-- **Excision in codimension one, unconditionally.** -/
theorem hasComponentSupportDecomposition_unconditional :
    HasComponentSupportDecomposition X :=
  hasComponentSupportDecomposition X (hasCodimensionTwoSupportedVanishing X)

/-- **The step-4 assembly.** With the decomposition obligation and its codimension-two
vanishing input both discharged, the remaining obligation `HasDivisorClassOfSomeCartierData X`
of `docs/DIVISOR_HANDOFF.md` §3 follows from the local model alone (whose statement now includes
the existence of the *normalised* supported lift). -/
theorem hasDivisorClassOfSomeCartierData_of_supportedChernLift_of_localModel
    (hloc : HasChernLocalModel X) :
    HasDivisorClassOfSomeCartierData X :=
  hasDivisorClassOfSomeCartierData_of_localModel X
    (hasComponentSupportDecomposition_unconditional X) hloc

end AlgebraicGeometry.ComplexPoint
