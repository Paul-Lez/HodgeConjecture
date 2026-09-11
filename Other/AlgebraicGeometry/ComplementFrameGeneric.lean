/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ComplementFrame

/-!
# The frame of the line bundle off a codimension-two enlargement of the divisor

`Other/AlgebraicGeometry/ComplementFrame.lean` produces the frame of the line bundle off the
analytic support of the divisor only from the algebraic Hartogs statement `HasUnitOffDivisor X`.
This file avoids Hartogs by *enlarging the closed set* instead: for Cartier data `c` representing
`L`, the **good locus** `goodLocus c` is the set of points near which some local equation `c.fn i`
is the germ of a regular unit; it is Zariski open (`isOpen_goodLocus`) and its complement, the
**bad locus** `badLocus c`, satisfies:

* it contains every component of the divisor (`closure_subset_badLocus`): a unit has order of
  vanishing zero, and every open neighbourhood of a specialisation of `y` contains `y`;
* every point of it off the components of the divisor has coheight at least two
  (`two_le_coheight_of_mem_badLocus`): the generic point is good (`genericPoint_mem_goodLocus`),
  and a codimension-one point off the divisor is good because its stalk is a discrete valuation
  ring in which a rational function of order zero is a unit (`Scheme.exists_unit_mul_zpow_eq`),
  and a unit of the stalk spreads to a unit on a basic open (`nonempty_unitDatum_of_stalkUnit`).

On the analytic complement `Ω` of the bad locus every point carries unit data, and the gluing of
`ComplementFrame.lean` (`localLift`, `localLift_compatible`, `projection_localLift`) produces a
lift of the integer section `1` over `Ω` (`exists_lift_of_goodLocus`). This proves the
unconditional statement `hasComplementFrameOffCodimTwo`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance complementFrameGenericTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

/-! ### The statement -/

/-- **The frame off a codimension-two enlargement of the divisor.** For every extension `E` with
algebraic model `L` and every Cartier datum `c` representing `L`, there is a Zariski-closed set
`Z'` containing the components of `c.divisor`, all of whose other points have codimension at least
two, over whose analytic complement `E` acquires a lift of the integer section `1`. -/
def HasComplementFrameOffCodimTwo : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∀ c : Scheme.CartierData X.left, c.Represents L →
      ∃ Z' : Closeds X.left,
        (∀ y, c.divisor y ≠ 0 → closure ({y} : Set X.left) ⊆ Z') ∧
        (∀ z ∈ Z', (∀ y, c.divisor y ≠ 0 → z ∉ closure ({y} : Set X.left)) →
          (2 : ℕ∞) ≤ coheight z) ∧
        ∃ ℓ : E.middle.obj.obj (op ((analyticClosedSupport X Z').compl)),
          E.projection.hom.app (op ((analyticClosedSupport X Z').compl)) ℓ =
            (constantIntegerSheaf X).obj.map (homOfLE le_top).op
              HolomorphicUnitExtension.integerOneSection

/-- The analytic support of the divisor lies in the analytic support of any Zariski-closed set
containing the components of the divisor. -/
theorem cycleAnalyticClosedSupport_le_analyticClosedSupport (c : Scheme.CartierData X.left)
    (Z' : Closeds X.left) (h : ∀ y, c.divisor y ≠ 0 → closure ({y} : Set X.left) ⊆ Z') :
    cycleAnalyticClosedSupport X c.divisor ≤ analyticClosedSupport X Z' := by
  show componentsAnalyticClosedSupport X (cycleComponents X c.divisor) ≤ _
  rw [← analyticClosedSupport_componentsZariskiSupport]
  intro z hz
  rw [mem_analyticClosedSupport] at hz ⊢
  obtain ⟨y, hy, hzy⟩ := (mem_componentsZariskiSupport X).mp hz
  exact h y ((mem_cycleComponents_iff X c.divisor y).mp hy) hzy

/-! ### The good locus and the bad locus -/

variable {X}

/-- The good locus of a Cartier datum: the points near which some local equation is the germ of
a regular unit, i.e. the points carrying unit data (`Scheme.CartierData.UnitDatum`). -/
def goodLocus (c : Scheme.CartierData X.left) : Set X.left :=
  {p | Nonempty (c.UnitDatum p)}

omit [Smooth X.hom] in
theorem isOpen_goodLocus (c : Scheme.CartierData X.left) : IsOpen (goodLocus c) := by
  rw [isOpen_iff_forall_mem_open]
  rintro p ⟨D⟩
  exact ⟨D.opens, fun q hq => ⟨⟨D.i, D.opens, hq, D.le, D.unit, D.isUnit, D.fn_eq⟩⟩,
    D.opens.isOpen, D.mem⟩

/-- The bad locus: the Zariski-closed complement of the good locus. -/
def badLocus (c : Scheme.CartierData X.left) : Closeds X.left :=
  ⟨(goodLocus c)ᶜ, (isOpen_goodLocus c).isClosed_compl⟩

omit [Smooth X.hom] in
theorem mem_badLocus_iff {c : Scheme.CartierData X.left} {p : X.left} :
    p ∈ badLocus c ↔ ¬ Nonempty (c.UnitDatum p) := Iff.rfl

omit [Smooth X.hom] in
/-- **(a)** The bad locus contains every component of the divisor. -/
theorem closure_subset_badLocus (c : Scheme.CartierData X.left) (y : X.left)
    (hy : c.divisor y ≠ 0) : closure ({y} : Set X.left) ⊆ badLocus c := by
  rintro p hp ⟨D⟩
  have hyp : y ⤳ p := specializes_iff_mem_closure.mpr hp
  have hyV : y ∈ D.opens := hyp.mem_open D.opens.isOpen D.mem
  apply hy
  rw [c.divisor_apply_of_mem D.i y (D.le hyV), ← D.fn_eq]
  exact Scheme.ord_of_isUnit D.isUnit hyV

omit [Smooth X.hom] in
/-- A unit of the stalk at `p ∈ Uᵢ` mapping to `c.fn i` spreads to unit data at `p`. -/
theorem nonempty_unitDatum_of_stalkUnit (c : Scheme.CartierData X.left) (i : c.ι) (p : X.left)
    (hp : p ∈ c.opens i) (u : (X.left.presheaf.stalk p)ˣ)
    (hu : algebraMap (X.left.presheaf.stalk p) X.left.functionField u = c.fn i) :
    Nonempty (c.UnitDatum p) := by
  obtain ⟨W, hpW, s, hs⟩ :=
    X.left.presheaf.exists_germ_eq (x := p) (u : X.left.presheaf.stalk p)
  have hpt : p ∈ W ⊓ c.opens i := ⟨hpW, hp⟩
  set t : Γ(X.left, W ⊓ c.opens i) :=
    X.left.presheaf.map (homOfLE (inf_le_left : W ⊓ c.opens i ≤ W)).op s with ht
  have hgt : X.left.presheaf.germ _ p hpt t = (u : X.left.presheaf.stalk p) := by
    rw [ht, X.left.presheaf.germ_res_apply (homOfLE inf_le_left) p hpt s, hs]
  have hpb : p ∈ X.left.basicOpen t := by
    rw [Scheme.mem_basicOpen _ _ p hpt, hgt]
    exact u.isUnit
  have : Nonempty ((W ⊓ c.opens i : X.left.Opens)) := ⟨⟨p, hpt⟩⟩
  refine ⟨⟨i, X.left.basicOpen t, hpb, (X.left.basicOpen_le t).trans inf_le_right,
    X.left.presheaf.map (homOfLE (X.left.basicOpen_le t)).op t,
    X.left.toRingedSpace.isUnit_res_basicOpen t, ?_⟩⟩
  rw [Scheme.germToFunctionField_res, germToFunctionField_eq_algebraMap_germ hpt, hgt, hu]

omit [Smooth X.hom] in
/-- The generic point is good: a nonzero rational function is a unit of the function field, the
stalk at the generic point. -/
theorem genericPoint_mem_goodLocus (c : Scheme.CartierData X.left) :
    genericPoint X.left ∈ goodLocus c := by
  obtain ⟨i, hi⟩ := c.covers (genericPoint X.left)
  obtain ⟨W, hW, s, hs⟩ := X.left.presheaf.exists_germ_eq (x := genericPoint X.left) (c.fn i)
  have hpt : genericPoint X.left ∈ W ⊓ c.opens i := ⟨hW, hi⟩
  set t : Γ(X.left, W ⊓ c.opens i) :=
    X.left.presheaf.map (homOfLE (inf_le_left : W ⊓ c.opens i ≤ W)).op s with ht
  have hgt : X.left.presheaf.germ _ (genericPoint X.left) hpt t = c.fn i := by
    rw [ht, X.left.presheaf.germ_res_apply (homOfLE inf_le_left) _ hpt s, hs]
  have hpb : genericPoint X.left ∈ X.left.basicOpen t := by
    rw [Scheme.mem_basicOpen _ _ _ hpt, hgt]
    exact (Units.mk0 _ (c.fn_ne_zero i)).isUnit
  have : Nonempty ((W ⊓ c.opens i : X.left.Opens)) := ⟨⟨_, hpt⟩⟩
  refine ⟨⟨i, X.left.basicOpen t, hpb, (X.left.basicOpen_le t).trans inf_le_right,
    X.left.presheaf.map (homOfLE (X.left.basicOpen_le t)).op t,
    X.left.toRingedSpace.isUnit_res_basicOpen t, ?_⟩⟩
  rw [Scheme.germToFunctionField_res]
  exact hgt

/-- **(b)** Every point of the bad locus off the components of the divisor has coheight at least
two. -/
theorem two_le_coheight_of_mem_badLocus (c : Scheme.CartierData X.left) (z : X.left)
    (hz : z ∈ badLocus c) (hoff : ∀ y, c.divisor y ≠ 0 → z ∉ closure ({y} : Set X.left)) :
    (2 : ℕ∞) ≤ coheight z := by
  by_contra hlt
  rw [not_le, ENat.lt_two_iff, Order.le_one_iff] at hlt
  apply hz
  rcases hlt with h0 | h1
  · have hmax : IsMax z := Order.coheight_eq_zero.mp h0
    have hηz : z ≤ genericPoint X.left := genericPoint_specializes z
    have hzη : z ⤳ genericPoint X.left := hmax hηz
    exact hzη.mem_open (isOpen_goodLocus c) (genericPoint_mem_goodLocus c)
  · obtain ⟨i, hi⟩ := c.covers z
    have hdz : c.divisor z = 0 := by
      by_contra hne
      exact hoff z hne (subset_closure rfl)
    have hord : X.left.ord (c.fn i) z = 0 := by
      rw [← c.divisor_apply_of_mem i z hi]
      exact hdz
    have := isDiscreteValuationRing_stalk_of_coheight_eq_one X.hom h1
    obtain ⟨p, u, -, -, hfact⟩ := X.left.exists_unit_mul_zpow_eq h1 (c.fn_ne_zero i)
    rw [hord, zpow_zero, mul_one] at hfact
    exact nonempty_unitDatum_of_stalkUnit c i z hi u hfact.symm

/-! ### The lift over an analytic open carrying unit data -/

set_option maxHeartbeats 1000000 in
/-- **The lift over a good analytic open.** If every point of an analytic open `Ω` inside
`X^an ∖ |D|^an` lies over the good locus, the local lifts of `ComplementFrame.lean` glue to a
lift of the integer section `1` over `Ω`. -/
theorem exists_lift_of_goodLocus (E : HolomorphicUnitExtension X (dim X.left))
    {L : X.left.Modules} (e : (moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules)
    (c : Scheme.CartierData X.left) (hc : c.Represents L)
    (Ω : Opens (TopCat.of (ComplexPoint X)))
    (hΩ : ∀ z ∈ Ω, Point.underlying z ∈ goodLocus c) (hΩc : Ω ≤ divisorComplementOpen c) :
    ∃ ℓ : E.middle.obj.obj (op Ω),
      E.projection.hom.app (op Ω) ℓ =
        (constantIntegerSheaf X).obj.map (homOfLE (le_top : Ω ≤ ⊤)).op
          HolomorphicUnitExtension.integerOneSection := by
  obtain ⟨g, hg, hrep⟩ := hc
  let D : ∀ z : Ω, c.UnitDatum (Point.underlying (z : ComplexPoint X)) :=
    fun z => Classical.choice (hΩ z z.property)
  let W : Ω → Opens (TopCat.of (ComplexPoint X)) := fun z => Ω ⊓ liftOpen E z (D z)
  have hWΩ : ∀ z, W z ≤ Ω := fun _ => inf_le_left
  have hWl : ∀ z, W z ≤ liftOpen E z (D z) := fun _ => inf_le_right
  have hcover : Ω ≤ iSup W := fun z hz =>
    Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hz, mem_liftOpen E z (D ⟨z, hz⟩) (hΩc hz)⟩
  have hcompat : ∀ z w : Ω,
      sres E.middle (inf_le_left : W z ⊓ W w ≤ W z)
          (sres E.middle (hWl z) (localLift g E e z (D z) hg)) =
        sres E.middle (inf_le_right : W z ⊓ W w ≤ W w)
          (sres E.middle (hWl w) (localLift g E e w (D w) hg)) := by
    intro z w
    rw [sres_sres, sres_sres]
    have h := congrArg (sres E.middle (inf_le_inf (hWl z) (hWl w)))
      (localLift_compatible g E e z (D z) hg w (D w) hrep)
    rw [sres_sres, sres_sres] at h
    exact h
  obtain ⟨ℓ, hℓ, -⟩ := E.middle.existsUnique_gluing' W Ω (fun z => homOfLE (hWΩ z)) hcover
    (fun z => sres E.middle (hWl z) (localLift g E e z (D z) hg)) hcompat
  refine ⟨ℓ, ?_⟩
  show E.projection.hom.app _ ℓ = integerOneRestrict X Ω
  apply (constantIntegerSheaf X).eq_of_locally_eq' W Ω (fun z => homOfLE (hWΩ z)) hcover
  intro z
  change sres (constantIntegerSheaf X) _ (E.projection.hom.app _ ℓ) =
    sres (constantIntegerSheaf X) _ (integerOneRestrict X Ω)
  rw [sres_hom, sres_integerOneRestrict]
  have h1 : sres E.middle (hWΩ z) ℓ = sres E.middle (hWl z) (localLift g E e z (D z) hg) := hℓ z
  rw [h1, ← sres_hom, projection_localLift, sres_integerOneRestrict]

variable (X)

/-! ### The theorem -/

set_option maxHeartbeats 1000000 in
/-- **The frame off a codimension-two enlargement of the divisor**, unconditionally: the bad locus
of the Cartier datum is the required closed set. -/
theorem hasComplementFrameOffCodimTwo : HasComplementFrameOffCodimTwo X := by
  intro E L _ e c hc
  refine ⟨badLocus c, fun y hy => closure_subset_badLocus c y hy,
    fun z hz hoff => two_le_coheight_of_mem_badLocus c z hz hoff, ?_⟩
  refine exists_lift_of_goodLocus E e c hc _ ?_ ?_
  · intro z hz
    exact not_not.mp hz
  · intro z hz hmem
    exact hz (cycleAnalyticClosedSupport_le_analyticClosedSupport X c (badLocus c)
      (fun y hy => closure_subset_badLocus c y hy) hmem)

end AlgebraicGeometry.ComplexPoint
