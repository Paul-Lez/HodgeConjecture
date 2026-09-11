/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernRelativeClassNaturality
public import Other.AlgebraicGeometry.AnalytificationGenerates
public import Other.AlgebraicGeometry.HolomorphicLineBundleFrame
public import Other.AlgebraicGeometry.ComponentSupportDecomposition
public import Other.AlgebraicGeometry.UnitExtensionCorrectedLiftsOfIso

/-!
# The frame of the line bundle off the divisor

This file reduces `HasComplementFrame X` (`Other/AlgebraicGeometry/ChernRelativeClassNaturality.lean`,
the splitting datum of §4.3 step 3 of `docs/DIVISOR_HANDOFF.md`) to a single *algebraic*
statement about the local equations of a Cartier datum, `HasUnitOffDivisor X`:

> at a point `p ∈ Uᵢ` lying on no component of the divisor `c.divisor`, the local equation
> `c.fn i` is the germ of a unit of the structure sheaf on some neighbourhood of `p`.

This is the algebraic Hartogs statement: `c.fn i` has order of vanishing zero at every
codimension-one generization of `p` (its order at such a point `y` is `c.divisor y`, and
`c.divisor y ≠ 0` would put `p` on the component `closure {y}`), and a rational function that is a
unit at every codimension-one point of a *normal* local ring is a unit of that ring. Its
stalk-level form is `HasStalkUnitOfOrdEqZero X`, from which `HasUnitOffDivisor X` follows
(`hasUnitOffDivisor_of_stalkUnit`): a nonzero rational function with order zero at every
codimension-one generization of `p` is a unit of `𝒪_{X,p}`. The stalk `𝒪_{X,p}` is regular
(smoothness); that regular local rings are normal (Auslander–Buchsbaum, or Serre's criterion
`R₁ + S₂`) is not in Mathlib, and neither is the description of a Noetherian normal domain as the
intersection of its localizations at height-one primes. Nothing else is missing: everything
analytic is proved here, and `hasComplementFrame_of_stalkUnit` derives `HasComplementFrame X`
from the stalk-level statement alone.

## The reduction

Given Cartier data `c` representing `L` through generating sections `gᵢ` on `Uᵢ`
(`Scheme.CartierData.Represents`), `HasUnitOffDivisor X` supplies, at every point `p` off the
divisor, a neighbourhood `V ⊆ Uᵢ` and a unit `v` on `V` with germ `c.fn i`
(`Scheme.CartierData.UnitDatum`). The local sections `v • gᵢ|_V` of `L` are the restrictions of
one rational section: on the overlap of two such neighbourhoods they agree
(`Scheme.CartierData.UnitDatum.section_agree`), because the transition unit `u` with
`u • gᵢ = gⱼ` satisfies `germ(u) · fⱼ = fᵢ` and the germ map into the function field is injective
on nonempty opens. They generate `L` (`generates_section`).

Analytifying (`analyticSection`, `analytificationGenerates`) and transporting along the given
isomorphism `L^an ≅ E.sectionSheafOfModules` gives generating holomorphic sections
`UnitDatum.analyticFrame` of the line bundle of `E` on the analytic opens `V^an`, still agreeing
on overlaps (`analyticFrame_agree`). On `W_z := Ω ⊓ V_z^an ⊓ E.localLifts.opens z` (where
`Ω := X^an ∖ |D|^an`) such a frame differs from `E`'s canonical frame `E.frame z` by a
nowhere-vanishing holomorphic function `frameUnit`, and the section
`localLift := lift_z − ι(frameUnit)` of `E.middle` is a lift of the integer section `1` on `W_z`
(`projection_localLift`). The cocycle identity `frameUnit_cocycle`, which follows from
`smul_frame` and the agreement of the frames, says exactly that these local lifts agree on
overlaps (`localLift_compatible`), so they glue to a lift over `Ω` since `E.middle` is a sheaf.

The corollaries `hasChernWindingNaturality_of_unitOffDivisor` and
`hasDivisorClassOfSomeCartierData_of_unitOffDivisor` restate the reductions of
`ChernRelativeClassNaturality.lean` with `HasComplementFrame X` replaced by
`HasUnitOffDivisor X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open scoped Manifold ContDiff

universe u

namespace AlgebraicGeometry

/-! ### Algebraic preliminaries -/

/-- The germ in the function field of a restricted regular function is the germ of the function
itself. -/
theorem Scheme.germToFunctionField_res {S : Scheme.{u}} [IsIntegral S] {U V : S.Opens}
    (h : V ≤ U) [Nonempty V] [Nonempty U] (s : Γ(S, U)) :
    S.germToFunctionField V (S.presheaf.map (homOfLE h).op s) = S.germToFunctionField U s :=
  S.presheaf.germ_res_apply (homOfLE h) _ _ s

namespace Scheme.Modules

variable {S : Scheme.{u}} {L : S.Modules}

/-- A unit multiple of a generating section generates. -/
theorem Generates.isUnit_smul {U : S.Opens} {s : Γ(L, U)} (hs : Generates s) {v : Γ(S, U)}
    (hv : IsUnit v) : Generates (v • s) := by
  intro V h
  have hfun : (fun r : Γ(S, V) ↦ r • resSection L h (v • s)) =
      (fun r : Γ(S, V) ↦ r • resSection L h s) ∘
        fun r : Γ(S, V) ↦ r * S.presheaf.map (homOfLE h).op v := by
    funext r
    show r • resSection L h (v • s) = (r * S.presheaf.map (homOfLE h).op v) • resSection L h s
    rw [resSection_smul, mul_smul]
  rw [hfun]
  exact (hs V h).comp
    (IsUnit.isUnit_iff_mulRight_bijective.mp (hv.map (S.presheaf.map (homOfLE h).op).hom))

end Scheme.Modules

namespace Scheme.CartierData

variable {S : Scheme.{u}} [IsIntegral S] [IsNoetherian S] (c : S.CartierData)

/-- The transition condition of `Scheme.CartierData.Represents`, for a fixed family of generating
sections `g`: whenever `u • gᵢ = gⱼ` on `Uᵢ ⊓ Uⱼ`, `germ(u) · fⱼ = fᵢ` in the function field. -/
def RepresentsWith (L : S.Modules) (g : ∀ i : c.ι, Γ(L, c.opens i)) : Prop :=
  ∀ (i j : c.ι) (u : Γ(S, c.opens i ⊓ c.opens j)), IsUnit u →
    u • Scheme.Modules.resSection L inf_le_left (g i) =
      Scheme.Modules.resSection L inf_le_right (g j) →
    haveI := c.nonempty_inf i j
    S.germToFunctionField (c.opens i ⊓ c.opens j) u * c.fn j = c.fn i

theorem represents_iff (L : S.Modules) :
    c.Represents L ↔ ∃ g : ∀ i : c.ι, Γ(L, c.opens i),
      (∀ i, Scheme.Modules.Generates (g i)) ∧ c.RepresentsWith L g :=
  Iff.rfl

/-- **Local unit data off the divisor.** At a point `p` of `S`: a member `Uᵢ` of the cover, a
neighbourhood `V ⊆ Uᵢ` of `p`, and a unit `v` on `V` whose germ in the function field is the
local equation `fᵢ`. This is what makes the rational section `fᵢ · gᵢ` a regular, nowhere-vanishing
section of `L` near `p`. -/
structure UnitDatum (p : S) where
  /-- The member of the cover. -/
  i : c.ι
  /-- The neighbourhood of `p`. -/
  opens : S.Opens
  /-- The neighbourhood contains `p`. -/
  mem : p ∈ opens
  /-- The neighbourhood lies in the member of the cover. -/
  le : opens ≤ c.opens i
  /-- The unit on the neighbourhood. -/
  unit : Γ(S, opens)
  /-- It is a unit. -/
  isUnit : IsUnit unit
  /-- Its germ is the local equation. -/
  fn_eq : S.germToFunctionField (h := ⟨⟨p, mem⟩⟩) opens unit = c.fn i

namespace UnitDatum

variable {c} {L : S.Modules} (g : ∀ i : c.ι, Γ(L, c.opens i)) {p : S} (D : c.UnitDatum p)

instance nonempty_opens : Nonempty D.opens := ⟨⟨p, D.mem⟩⟩

/-- The local section `v • gᵢ|_V` of `L`: the rational section `fᵢ · gᵢ` on the neighbourhood
where it is regular. -/
def localSection : Γ(L, D.opens) := D.unit • Scheme.Modules.resSection L D.le (g D.i)

/-- The local section generates `L` on its neighbourhood. -/
theorem generates_localSection (hg : ∀ i, Scheme.Modules.Generates (g i)) :
    Scheme.Modules.Generates (D.localSection g) :=
  ((hg D.i).restrict D.le).isUnit_smul D.isUnit

/-- **The local sections are restrictions of one rational section.** Two local sections agree on
the overlap of their neighbourhoods. -/
theorem localSection_agree (hg : ∀ i, Scheme.Modules.Generates (g i))
    (hrep : c.RepresentsWith L g) {p' : S} (D' : c.UnitDatum p') :
    Scheme.Modules.resSection L inf_le_left (D.localSection g) =
      Scheme.Modules.resSection L inf_le_right (D'.localSection g) := by
  have := c.nonempty_inf D.i D'.i
  have : Nonempty ((D.opens ⊓ D'.opens : S.Opens)) := S.nonempty_inf _ _
  obtain ⟨u, hu, huij⟩ :=
    ((hg D.i).restrict (inf_le_left : c.opens D.i ⊓ c.opens D'.i ≤ c.opens D.i)).exists_isUnit_smul_eq
      ((hg D'.i).restrict (inf_le_right : c.opens D.i ⊓ c.opens D'.i ≤ c.opens D'.i))
  have hfn := hrep D.i D'.i u hu huij
  have hW : D.opens ⊓ D'.opens ≤ c.opens D.i ⊓ c.opens D'.i := inf_le_inf D.le D'.le
  have hkey : S.presheaf.map (homOfLE (inf_le_left : D.opens ⊓ D'.opens ≤ D.opens)).op D.unit =
      S.presheaf.map (homOfLE (inf_le_right : D.opens ⊓ D'.opens ≤ D'.opens)).op D'.unit *
        S.presheaf.map (homOfLE hW).op u := by
    apply S.germToFunctionField_injective (D.opens ⊓ D'.opens)
    rw [map_mul, Scheme.germToFunctionField_res, Scheme.germToFunctionField_res,
      Scheme.germToFunctionField_res, D.fn_eq, D'.fn_eq, mul_comm, hfn]
  have hu' : S.presheaf.map (homOfLE hW).op u •
      Scheme.Modules.resSection L (hW.trans inf_le_left) (g D.i) =
      Scheme.Modules.resSection L (hW.trans inf_le_right) (g D'.i) := by
    rw [← Scheme.Modules.resSection_resSection inf_le_left hW,
      ← Scheme.Modules.resSection_resSection inf_le_right hW,
      ← Scheme.Modules.resSection_smul, huij]
  show Scheme.Modules.resSection L inf_le_left (D.unit • Scheme.Modules.resSection L D.le (g D.i)) =
    Scheme.Modules.resSection L inf_le_right
      (D'.unit • Scheme.Modules.resSection L D'.le (g D'.i))
  rw [Scheme.Modules.resSection_smul, Scheme.Modules.resSection_smul,
    Scheme.Modules.resSection_resSection, Scheme.Modules.resSection_resSection, hkey, mul_smul,
    hu']

end UnitDatum

end Scheme.CartierData

namespace ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance complementFrameTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

/-! ### The algebraic obligation -/

/-- **Obligation: the local equations are units off the divisor.** At a point `p ∈ Uᵢ` lying on no
component of `c.divisor`, the local equation `c.fn i` is the germ of a unit of the structure sheaf
on a neighbourhood of `p` inside `Uᵢ`.

This is algebraic Hartogs for the regular local ring `𝒪_{X,p}`: the order of vanishing of
`c.fn i` at every codimension-one generization `y` of `p` is `c.divisor y = 0`, and in a normal
Noetherian local ring a rational function which is a unit at every height-one prime is a unit.
The missing input is the normality of regular local rings (or the description of a Noetherian
normal domain as the intersection of its localizations at height-one primes), neither of which is
in Mathlib. -/
def HasUnitOffDivisor : Prop :=
  ∀ (c : Scheme.CartierData X.left) (i : c.ι) (p : X.left), p ∈ c.opens i →
    (∀ y : X.left, c.divisor y ≠ 0 → p ∉ closure ({y} : Set X.left)) →
    ∃ (V : X.left.Opens) (hp : p ∈ V), V ≤ c.opens i ∧
      ∃ v : Γ(X.left, V), IsUnit v ∧
        X.left.germToFunctionField (h := ⟨⟨p, hp⟩⟩) V v = c.fn i

/-- **The stalk-level form of the obligation: algebraic Hartogs.** A nonzero rational function whose
order of vanishing is zero at every codimension-one generization of `p` is (the image of) a unit
of the stalk `𝒪_{X,p}`. For the regular local ring `𝒪_{X,p}` this is the statement
`𝒪_{X,p} = ⋂_{ht 𝔮 = 1} (𝒪_{X,p})_𝔮` inside the function field, i.e. the normality of regular
local rings together with the intersection description of a Noetherian normal domain. -/
def HasStalkUnitOfOrdEqZero : Prop :=
  ∀ (p : X.left) (f : X.left.functionField), f ≠ 0 →
    (∀ y : X.left, coheight y = 1 → y ⤳ p → X.left.ord f y = 0) →
    ∃ u : (X.left.presheaf.stalk p)ˣ,
      algebraMap (X.left.presheaf.stalk p) X.left.functionField u = f

omit [Smooth X.hom] in
/-- The stalk-level statement implies the unit statement: off the divisor, the local equation has
order zero at every codimension-one generization, so it is a unit of the stalk, and a unit of the
stalk spreads out to a unit on a basic open neighbourhood. -/
theorem hasUnitOffDivisor_of_stalkUnit (h : HasStalkUnitOfOrdEqZero X) : HasUnitOffDivisor X := by
  intro c i p hp hoff
  have hord : ∀ y : X.left, coheight y = 1 → y ⤳ p → X.left.ord (c.fn i) y = 0 := by
    intro y _ hyp
    have hy : y ∈ c.opens i := hyp.mem_open (c.opens i).isOpen hp
    rw [← c.divisor_apply_of_mem i y hy]
    by_contra hne
    exact hoff y hne (specializes_iff_mem_closure.mp hyp)
  obtain ⟨u, hu⟩ := h p (c.fn i) (c.fn_ne_zero i) hord
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
  refine ⟨X.left.basicOpen t, hpb, (X.left.basicOpen_le t).trans inf_le_right,
    X.left.presheaf.map (homOfLE (X.left.basicOpen_le t)).op t,
    X.left.toRingedSpace.isUnit_res_basicOpen t, ?_⟩
  have : Nonempty ((W ⊓ c.opens i : X.left.Opens)) := ⟨⟨p, hpt⟩⟩
  rw [Scheme.germToFunctionField_res, germToFunctionField_eq_algebraMap_germ hpt, hgt, hu]

/-- The obligation produces unit data at the underlying point of every complex point off the
analytic support of the divisor. -/
theorem nonempty_unitDatum (hunit : HasUnitOffDivisor X) (c : Scheme.CartierData X.left)
    (z : ComplexPoint X) (hz : z ∈ divisorComplementOpen c) :
    Nonempty (c.UnitDatum (Point.underlying z)) := by
  have hp : Point.underlying z ∈ c.opens (c.index (Point.underlying z)) :=
    c.mem_opens_index (Point.underlying z)
  have hoff : ∀ y : X.left, c.divisor y ≠ 0 →
      Point.underlying z ∉ closure ({y} : Set X.left) := by
    intro y hy hcl
    have hyc : y ∈ cycleComponents X c.divisor := (mem_cycleComponents_iff X c.divisor y).mpr hy
    exact hz (cycleComponentAnalyticClosedSupport_le_componentsAnalyticClosedSupport X hyc hcl)
  obtain ⟨V, hpV, hVle, v, hv, hfn⟩ := hunit c (c.index (Point.underlying z)) _ hp hoff
  exact ⟨⟨c.index (Point.underlying z), V, hpV, hVle, v, hv, hfn⟩⟩

/-! ### The analytic frames -/

variable {X}
variable {c : Scheme.CartierData X.left} {L : X.left.Modules} (g : ∀ i : c.ι, Γ(L, c.opens i))
  (E : HolomorphicUnitExtension X (dim X.left))
  (e : (moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules)

namespace UnitDatum

open Scheme.CartierData

variable {p : X.left} (D : c.UnitDatum p)

/-- The analytification of the local section, transported to the line bundle of `E`. -/
def analyticFrame : E.sectionSheafOfModules.val.obj (op (analyticOpen X D.opens)) :=
  e.hom.val.app (op (analyticOpen X D.opens))
    (analyticSection X (dim X.left) L D.opens (D.localSection g))

/-- The analytic frame generates. -/
theorem holomorphicGenerates_analyticFrame (hg : ∀ i, Scheme.Modules.Generates (g i)) :
    HolomorphicGenerates (analyticFrame g E e D) :=
  (analytificationGenerates X (dim X.left) L D.opens _ (D.generates_localSection g hg)).map_iso e

/-- The analytic frames agree on overlaps. -/
theorem analyticFrame_agree (hg : ∀ i, Scheme.Modules.Generates (g i))
    (hrep : c.RepresentsWith L g) {p' : X.left} (D' : c.UnitDatum p') :
    holRes E.sectionSheafOfModules (analyticOpen_mono X inf_le_left) (analyticFrame g E e D) =
      holRes E.sectionSheafOfModules (analyticOpen_mono X inf_le_right)
        (analyticFrame g E e D') := by
  have h := congrArg (analyticSection X (dim X.left) L (D.opens ⊓ D'.opens))
    (D.localSection_agree g hg hrep D')
  rw [analyticSection_res, analyticSection_res] at h
  have h' := smul_holRes_map_iso e (analyticOpen_mono X inf_le_left)
    (analyticOpen_mono X inf_le_right) 1
    (analyticSection X (dim X.left) L D.opens (D.localSection g))
    (analyticSection X (dim X.left) L D'.opens (D'.localSection g)) (by rw [one_smul]; exact h)
  rw [one_smul] at h'
  exact h'

end UnitDatum

/-! ### The local lifts -/

section LocalLifts

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Morphisms of additive sheaves preserve differences of sections. -/
theorem hom_sub {F G : AnalyticAdditiveSheaf X} (f : F ⟶ G)
    {U : Opens (TopCat.of (ComplexPoint X))} (s t : F.obj.obj (op U)) :
    f.hom.app (op U) (s - t) = f.hom.app (op U) s - f.hom.app (op U) t :=
  map_sub _ _ _

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Restriction preserves differences of sections. -/
theorem sres_sub {F : AnalyticAdditiveSheaf X} {U V : Opens (TopCat.of (ComplexPoint X))}
    (h : V ≤ U) (s t : F.obj.obj (op U)) : sres F h (s - t) = sres F h s - sres F h t :=
  map_sub _ _ _

open Scheme.CartierData

variable (z : ComplexPoint X) (D : c.UnitDatum (Point.underlying z))

/-- The open on which the local lift at `z` lives: inside `Ω`, inside the analytic open of the
unit datum, and inside the lifting neighbourhood of `E` at `z`. -/
def liftOpen : Opens (TopCat.of (ComplexPoint X)) :=
  divisorComplementOpen c ⊓ (analyticOpen X D.opens ⊓ E.localLifts.opens z)

theorem liftOpen_le_compl : liftOpen E z D ≤ divisorComplementOpen c := inf_le_left

theorem liftOpen_le_analyticOpen : liftOpen E z D ≤ analyticOpen X D.opens :=
  inf_le_right.trans inf_le_left

theorem liftOpen_le_localLifts : liftOpen E z D ≤ E.localLifts.opens z :=
  inf_le_right.trans inf_le_right

theorem mem_liftOpen (hz : z ∈ divisorComplementOpen c) : z ∈ liftOpen E z D :=
  ⟨hz, D.mem, E.localLifts.mem_opens z⟩

/-- The analytic frame restricted to the lifting open. -/
def liftFrame : E.sectionSheafOfModules.val.obj (op (liftOpen E z D)) :=
  holRes E.sectionSheafOfModules (liftOpen_le_analyticOpen E z D) (UnitDatum.analyticFrame g E e D)

theorem holomorphicGenerates_liftFrame (hg : ∀ i, Scheme.Modules.Generates (g i)) :
    HolomorphicGenerates (liftFrame g E e z D) :=
  (UnitDatum.holomorphicGenerates_analyticFrame g E e D hg).restrict _

set_option backward.isDefEq.respectTransparency false in
/-- The frame change from the analytic frame to the canonical frame of `E` at `z`. -/
theorem exists_frameUnit (hg : ∀ i, Scheme.Modules.Generates (g i)) :
    ∃ a : (holomorphicRingSheaf X (dim X.left)).obj.obj (op (liftOpen E z D)), IsUnit a ∧
      a • liftFrame g E e z D = E.frame z (liftOpen E z D) (liftOpen_le_localLifts E z D) :=
  (holomorphicGenerates_liftFrame g E e z D hg).exists_isUnit_smul_eq
    (E.holomorphicGenerates_frame z _ _)

variable (hg : ∀ i, Scheme.Modules.Generates (g i))

set_option backward.isDefEq.respectTransparency false in
/-- The chosen frame change, as an invertible holomorphic function. -/
def frameUnit : (C^ω⟮𝓘(ℂ, Fin (dim X.left) → ℂ), liftOpen E z D; ℂ⟯)ˣ :=
  (exists_frameUnit g E e z D hg).choose_spec.1.unit

set_option backward.isDefEq.respectTransparency false in
theorem unitSection_frameUnit_smul :
    unitSection (frameUnit g E e z D hg) • liftFrame g E e z D =
      E.frame z (liftOpen E z D) (liftOpen_le_localLifts E z D) := by
  have h := (exists_frameUnit g E e z D hg).choose_spec.2
  rw [← (exists_frameUnit g E e z D hg).choose_spec.1.unit_spec] at h
  exact h

/-- The frame change as a section of the sheaf of holomorphic units. -/
def frameCochain : (holomorphicUnitSheaf X (dim X.left)).obj.obj (op (liftOpen E z D)) :=
  Additive.ofMul (frameUnit g E e z D hg)

/-- The local lift of the integer section `1` at `z`: the chosen lift of `E`, corrected by the
frame change. -/
def localLift : E.middle.obj.obj (op (liftOpen E z D)) :=
  sres E.middle (liftOpen_le_localLifts E z D) (E.localLifts.lift z) -
    E.inclusion.hom.app (op (liftOpen E z D)) (frameCochain g E e z D hg)

/-- The local lift lifts the integer section `1`. -/
theorem projection_localLift :
    E.projection.hom.app (op (liftOpen E z D)) (localLift g E e z D hg) =
      integerOneRestrict X (liftOpen E z D) := by
  unfold localLift
  rw [hom_sub, inclusion_projection_apply, sub_zero]
  exact E.localLifts.map_restrictLift z _ (liftOpen_le_localLifts E z D)

variable (w : ComplexPoint X) (Dw : c.UnitDatum (Point.underlying w))

include hg in
/-- The restricted frames agree on the overlap of two lifting opens. -/
theorem holRes_liftFrame_eq (hrep : c.RepresentsWith L g) :
    holRes E.sectionSheafOfModules (inf_le_left : liftOpen E z D ⊓ liftOpen E w Dw ≤ _)
        (liftFrame g E e z D) =
      holRes E.sectionSheafOfModules (inf_le_right : liftOpen E z D ⊓ liftOpen E w Dw ≤ _)
        (liftFrame g E e w Dw) := by
  have hV : liftOpen E z D ⊓ liftOpen E w Dw ≤ analyticOpen X (D.opens ⊓ Dw.opens) :=
    fun y hy => ⟨liftOpen_le_analyticOpen E z D hy.1, liftOpen_le_analyticOpen E w Dw hy.2⟩
  unfold liftFrame
  rw [holRes_holRes, holRes_holRes,
    ← holRes_holRes (analyticOpen_mono X inf_le_left) hV,
    ← holRes_holRes (analyticOpen_mono X inf_le_right) hV,
    UnitDatum.analyticFrame_agree g E e D hg hrep Dw]

set_option backward.isDefEq.respectTransparency false in
/-- **The cocycle identity for the frame changes.** On the overlap of two lifting opens, the
frame changes differ by the transition function of `E`. -/
theorem frameUnit_cocycle (hrep : c.RepresentsWith L g) :
    ringRes (inf_le_right : liftOpen E z D ⊓ liftOpen E w Dw ≤ _)
        (unitSection (frameUnit g E e w Dw hg)) =
      unitSection (E.transitionUnit w z (liftOpen E z D ⊓ liftOpen E w Dw)
          (inf_le_right.trans (liftOpen_le_localLifts E w Dw))
          (inf_le_left.trans (liftOpen_le_localLifts E z D))) *
        ringRes (inf_le_left : liftOpen E z D ⊓ liftOpen E w Dw ≤ _)
          (unitSection (frameUnit g E e z D hg)) := by
  set V := liftOpen E z D ⊓ liftOpen E w Dw
  have hz : V ≤ liftOpen E z D := inf_le_left
  have hw : V ≤ liftOpen E w Dw := inf_le_right
  have hτ := holRes_liftFrame_eq g E e z D hg w Dw hrep
  have hcz : ringRes hz (unitSection (frameUnit g E e z D hg)) •
      holRes E.sectionSheafOfModules hz (liftFrame g E e z D) =
      holRes E.sectionSheafOfModules hz
        (E.frame z (liftOpen E z D) (liftOpen_le_localLifts E z D)) := by
    rw [← holRes_smul, unitSection_frameUnit_smul]
  have hcw : ringRes hw (unitSection (frameUnit g E e w Dw hg)) •
      holRes E.sectionSheafOfModules hw (liftFrame g E e w Dw) =
      holRes E.sectionSheafOfModules hw
        (E.frame w (liftOpen E w Dw) (liftOpen_le_localLifts E w Dw)) := by
    rw [← holRes_smul, unitSection_frameUnit_smul]
  have hfr : unitSection (E.transitionUnit w z V (hw.trans (liftOpen_le_localLifts E w Dw))
        (hz.trans (liftOpen_le_localLifts E z D))) •
      holRes E.sectionSheafOfModules hz
        (E.frame z (liftOpen E z D) (liftOpen_le_localLifts E z D)) =
      holRes E.sectionSheafOfModules hw
        (E.frame w (liftOpen E w Dw) (liftOpen_le_localLifts E w Dw)) := by
    rw [E.holRes_frame z (liftOpen_le_localLifts E z D) hz,
      E.holRes_frame w (liftOpen_le_localLifts E w Dw) hw]
    exact E.smul_frame z w V _ _
  refine ((holomorphicGenerates_liftFrame g E e w Dw hg).restrict hw).bijective.injective ?_
  show ringRes hw (unitSection (frameUnit g E e w Dw hg)) •
      holRes E.sectionSheafOfModules hw (liftFrame g E e w Dw) =
    (_ * ringRes hz (unitSection (frameUnit g E e z D hg))) •
      holRes E.sectionSheafOfModules hw (liftFrame g E e w Dw)
  rw [hcw, mul_smul, ← hτ, hcz, hfr]

set_option backward.isDefEq.respectTransparency false in
/-- The cocycle identity, read in the sheaf of holomorphic units. -/
theorem sres_frameCochain (hrep : c.RepresentsWith L g) :
    sres (holomorphicUnitSheaf X (dim X.left))
        (inf_le_right : liftOpen E z D ⊓ liftOpen E w Dw ≤ _) (frameCochain g E e w Dw hg) =
      sres (holomorphicUnitSheaf X (dim X.left))
          (inf_le_left : liftOpen E z D ⊓ liftOpen E w Dw ≤ _) (frameCochain g E e z D hg) +
        E.localLifts.transition E.shortExact w z (liftOpen E z D ⊓ liftOpen E w Dw)
          (inf_le_right.trans (liftOpen_le_localLifts E w Dw))
          (inf_le_left.trans (liftOpen_le_localLifts E z D)) := by
  refine unitOf_injective (fun y => ?_)
  exact (congrArg (fun m : C^ω⟮𝓘(ℂ, Fin (dim X.left) → ℂ),
    ((liftOpen E z D ⊓ liftOpen E w Dw : Opens (TopCat.of (ComplexPoint X)))); ℂ⟯ => m y)
    (frameUnit_cocycle g E e z D hg w Dw hrep)).trans (mul_comm _ _)

/-- **The local lifts agree on overlaps.** -/
theorem localLift_compatible (hrep : c.RepresentsWith L g) :
    sres E.middle (inf_le_left : liftOpen E z D ⊓ liftOpen E w Dw ≤ _)
        (localLift g E e z D hg) =
      sres E.middle (inf_le_right : liftOpen E z D ⊓ liftOpen E w Dw ≤ _)
        (localLift g E e w Dw hg) := by
  have hsp : E.inclusion.hom.app (op (liftOpen E z D ⊓ liftOpen E w Dw))
      (E.localLifts.transition E.shortExact w z (liftOpen E z D ⊓ liftOpen E w Dw)
        (inf_le_right.trans (liftOpen_le_localLifts E w Dw))
        (inf_le_left.trans (liftOpen_le_localLifts E z D))) =
      sres E.middle (inf_le_right.trans (liftOpen_le_localLifts E w Dw)) (E.localLifts.lift w) -
        sres E.middle (inf_le_left.trans (liftOpen_le_localLifts E z D)) (E.localLifts.lift z) :=
    E.localLifts.transition_spec E.shortExact w z _ _ _
  unfold localLift
  rw [sres_sub, sres_sub, sres_sres, sres_sres, sres_hom, sres_hom,
    sres_frameCochain g E e z D hg w Dw hrep, hom_add, hsp]
  abel

end LocalLifts

/-! ### The frame off the divisor -/

variable (X)

set_option maxHeartbeats 1000000 in
/-- **The frame off the divisor, from the algebraic unit statement.** Given
`HasUnitOffDivisor X`, every extension `E` with an algebraic model `L` represented by Cartier
data `c` acquires a lift of the integer section `1` over `X^an ∖ |D|^an`. -/
theorem hasComplementFrame_of_unitOffDivisor (hunit : HasUnitOffDivisor X) :
    HasComplementFrame X := by
  intro E L _ e c hc
  obtain ⟨g, hg, hrep⟩ := hc
  let D : ∀ z : divisorComplementOpen c, c.UnitDatum (Point.underlying (z : ComplexPoint X)) :=
    fun z => Classical.choice (nonempty_unitDatum X hunit c z z.property)
  let W : divisorComplementOpen c → Opens (TopCat.of (ComplexPoint X)) :=
    fun z => liftOpen E z (D z)
  have hcover : divisorComplementOpen c ≤ iSup W := fun z hz =>
    Opens.mem_iSup.mpr ⟨⟨z, hz⟩, mem_liftOpen E z (D ⟨z, hz⟩) hz⟩
  obtain ⟨ℓ, hℓ, -⟩ := E.middle.existsUnique_gluing' W (divisorComplementOpen c)
    (fun z => homOfLE (liftOpen_le_compl E z (D z))) hcover
    (fun z => localLift g E e z (D z) hg)
    (fun z w => localLift_compatible g E e z (D z) hg w (D w) hrep)
  refine ⟨ℓ, ?_⟩
  show E.projection.hom.app _ ℓ = integerOneRestrict X (divisorComplementOpen c)
  apply (constantIntegerSheaf X).eq_of_locally_eq' W (divisorComplementOpen c)
    (fun z => homOfLE (liftOpen_le_compl E z (D z))) hcover
  intro z
  change sres (constantIntegerSheaf X) _ (E.projection.hom.app _ ℓ) =
    sres (constantIntegerSheaf X) _ (integerOneRestrict X (divisorComplementOpen c))
  rw [sres_hom, sres_integerOneRestrict]
  have h1 : sres E.middle (liftOpen_le_compl E z (D z)) ℓ = localLift g E e z (D z) hg := hℓ z
  rw [h1]
  exact projection_localLift g E e z (D z) hg

set_option maxHeartbeats 1000000 in
/-- The frame off the divisor, from the stalk-level Hartogs statement. -/
theorem hasComplementFrame_of_stalkUnit (h : HasStalkUnitOfOrdEqZero X) : HasComplementFrame X :=
  hasComplementFrame_of_unitOffDivisor X (hasUnitOffDivisor_of_stalkUnit X h)

/-! ### Consequences for the reductions of `ChernRelativeClassNaturality.lean` -/

set_option maxHeartbeats 1000000 in
/-- `HasChernWindingNaturality X` from the algebraic unit statement and the chart formula. -/
theorem hasChernWindingNaturality_of_unitOffDivisor (hunit : HasUnitOffDivisor X)
    (hchart : HasRelativeChernChartFormula X) : HasChernWindingNaturality X :=
  hasChernWindingNaturality_of_relativeChernChartFormula X
    (hasComplementFrame_of_unitOffDivisor X hunit) hchart

set_option maxHeartbeats 1000000 in
/-- **Step 4 of `docs/DIVISOR_HANDOFF.md` §4.3**, with the frame off the divisor replaced by the
algebraic unit statement: `HasUnitOffDivisor X`, normalised winding charts and the chart formula
for the canonical relative class give `HasDivisorClassOfSomeCartierData X`. -/
theorem hasDivisorClassOfSomeCartierData_of_unitOffDivisor (hunit : HasUnitOffDivisor X)
    (hcharts : HasNormalizedWindingCharts X) (hchart : HasRelativeChernChartFormula X) :
    HasDivisorClassOfSomeCartierData X :=
  hasDivisorClassOfSomeCartierData_of_relativeChernChartFormula X
    (hasComplementFrame_of_unitOffDivisor X hunit) hcharts hchart

end ComplexPoint

end AlgebraicGeometry
