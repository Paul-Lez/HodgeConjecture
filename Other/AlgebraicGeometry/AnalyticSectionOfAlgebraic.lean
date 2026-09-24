/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicSheafGenerators
public import Other.AlgebraicGeometry.AnalytificationModules
public import Other.AlgebraicGeometry.CartierDataOfTrivializingCover

/-!
# Analytification of sections of an algebraic sheaf of modules

The unit of the analytification adjunction turns a section of an algebraic sheaf of modules over
an algebraic open `U` into a section of its analytification over the analytic open `U^an`. This
file records that operation and its two structural properties — compatibility with restriction
and semilinearity over evaluation of regular functions — and deduces that **the algebraic
transition identities transport verbatim to the analytic side**:

```
u • gᵢ|_W = gⱼ|_W   ⟹   u^an • gᵢ^an|_{W^an} = gⱼ^an|_{W^an}
```

This is unconditional. What is *not* proved here is that `gᵢ^an` generates the analytification
when `gᵢ` generates: that statement is isolated as `AnalytificationGenerates`, and everything
downstream is derived from it (see `docs/DIVISOR_HANDOFF.md` §4.2(b)).
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]

local instance analyticSectionOfAlgebraicTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

/-- Analytic opens are monotone in the algebraic open. -/
lemma analyticOpen_mono {U V : X.left.Opens} (h : V ≤ U) : analyticOpen X V ≤ analyticOpen X U :=
  fun _ hz ↦ h hz

/-- A regular function, as a section of the holomorphic structure sheaf on the analytic open. -/
def analyticFunction (U : X.left.Opens) (r : Γ(X.left, U)) :
    (holomorphicRingSheaf X d).obj.obj (op (analyticOpen X U)) :=
  (regularToHolomorphicRingSheaf X d).hom.app (op U) r

/-- The analytification of a section of an algebraic sheaf of modules, through the unit of the
analytification adjunction. -/
def analyticSection (L : X.left.Modules) (U : X.left.Opens) (g : Γ(L, U)) :
    ((moduleAnalytification X d).obj L).val.obj (op (analyticOpen X U)) :=
  ((moduleAnalytificationAdjunction X d).unit.app L).app U g

variable {X d}

@[simp]
lemma analyticFunction_one (U : X.left.Opens) :
    analyticFunction X d U (1 : Γ(X.left, U)) = 1 :=
  map_one ((regularToHolomorphicRingSheaf X d).hom.app (op U)).hom

lemma analyticFunction_mul (U : X.left.Opens) (r r' : Γ(X.left, U)) :
    analyticFunction X d U (r * r') = analyticFunction X d U r * analyticFunction X d U r' :=
  map_mul ((regularToHolomorphicRingSheaf X d).hom.app (op U)).hom r r'

/-- The evaluation of a unit of the structure sheaf is a unit of the holomorphic structure
sheaf: a nowhere-vanishing holomorphic function. -/
lemma isUnit_analyticFunction {U : X.left.Opens} {r : Γ(X.left, U)} (hr : IsUnit r) :
    IsUnit (analyticFunction X d U r) :=
  hr.map ((regularToHolomorphicRingSheaf X d).hom.app (op U)).hom

/-- Analytification of regular functions commutes with restriction. -/
lemma analyticFunction_res {U V : X.left.Opens} (h : V ≤ U) (r : Γ(X.left, U)) :
    analyticFunction X d V (X.left.presheaf.map (homOfLE h).op r) =
      (holomorphicRingSheaf X d).obj.map (homOfLE (analyticOpen_mono X h)).op
        (analyticFunction X d U r) := by
  apply Subtype.ext
  funext z
  exact (Point.evaluate_res h r (z : ComplexPoint X) z.property).symm

/-- Analytification of sections is semilinear over evaluation of regular functions. -/
lemma analyticSection_smul (L : X.left.Modules) (U : X.left.Opens) (r : Γ(X.left, U))
    (g : Γ(L, U)) :
    analyticSection X d L U (r • g) = analyticFunction X d U r • analyticSection X d L U g :=
  ((moduleAnalytificationAdjunction X d).unit.app L).app_smul r g

/-- Analytification of sections commutes with restriction. -/
lemma analyticSection_res (L : X.left.Modules) {U V : X.left.Opens} (h : V ≤ U) (g : Γ(L, U)) :
    analyticSection X d L V (Scheme.Modules.resSection L h g) =
      holRes ((moduleAnalytification X d).obj L) (analyticOpen_mono X h)
        (analyticSection X d L U g) :=
  PresheafOfModules.naturality_apply
    ((moduleAnalytificationAdjunction X d).unit.app L).val (homOfLE h).op g

/-- **Transport of transition identities.** An identity `u • a = b` between restrictions of
sections of an algebraic sheaf of modules analytifies to the identity `u^an • a^an = b^an`
between the restrictions of their analytifications. -/
theorem analyticSection_smul_res (L : X.left.Modules) {U V W : X.left.Opens}
    (hWU : W ≤ U) (hWV : W ≤ V) (u : Γ(X.left, W)) (a : Γ(L, U)) (b : Γ(L, V))
    (h : u • Scheme.Modules.resSection L hWU a = Scheme.Modules.resSection L hWV b) :
    analyticFunction X d W u •
        holRes ((moduleAnalytification X d).obj L) (analyticOpen_mono X hWU)
          (analyticSection X d L U a) =
      holRes ((moduleAnalytification X d).obj L) (analyticOpen_mono X hWV)
        (analyticSection X d L V b) := by
  have hcong := congrArg (analyticSection X d L W) h
  rwa [analyticSection_smul, analyticSection_res, analyticSection_res] at hcong

variable (X d)

/--
**Obligation.** The analytification of a generating section generates.

This is the only missing link between the algebraic and the analytic frames of an invertible
sheaf. Mathematically it is the base-change statement
`((pullback φ).obj L).over U^an ≅ (pullback (φ.over U)).obj (L.over U)` for the morphism of
ringed sites `φ = regularToHolomorphicRingSheaf X d`, combined with Mathlib's
`SheafOfModules.pullbackObjUnitToUnit` for the restricted site morphism; see
`docs/DIVISOR_HANDOFF.md` §4.2(b).
-/
def AnalytificationGenerates : Prop :=
  ∀ (L : X.left.Modules) (U : X.left.Opens) (g : Γ(L, U)),
    Scheme.Modules.Generates g →
      HolomorphicGenerates (M := (moduleAnalytification X d).obj L) (analyticSection X d L U g)

variable {X d}

/-- Given `AnalytificationGenerates`, an algebraic trivializing cover of `L` analytifies to a
holomorphic trivializing cover of the analytification of `L`, indexed by the same set. -/
def analyticTrivializingCover (hgen : AnalytificationGenerates X d) {L : X.left.Modules}
    (t : Scheme.Modules.TrivializingCover L) :
    HolomorphicTrivializingCover ((moduleAnalytification X d).obj L) where
  ι := t.ι
  opens i := analyticOpen X (t.opens i)
  covers z := t.covers (Point.underlying z)
  gen i := analyticSection X d L (t.opens i) (t.gen i)
  gen_generates i := hgen L (t.opens i) (t.gen i) (t.gen_generates i)

@[simp]
lemma analyticTrivializingCover_opens (hgen : AnalytificationGenerates X d)
    {L : X.left.Modules} (t : Scheme.Modules.TrivializingCover L) (i : t.ι) :
    (analyticTrivializingCover hgen t).opens i = analyticOpen X (t.opens i) := rfl

@[simp]
lemma analyticTrivializingCover_gen (hgen : AnalytificationGenerates X d)
    {L : X.left.Modules} (t : Scheme.Modules.TrivializingCover L) (i : t.ι) :
    (analyticTrivializingCover hgen t).gen i =
      analyticSection X d L (t.opens i) (t.gen i) := rfl

/-- The trivializing cover of the line bundle of a unit-sheaf extension given by its own local
lifts of the integer section `1`. -/
def HolomorphicUnitExtension.frames (E : HolomorphicUnitExtension X d) :
    HolomorphicTrivializingCover E.sectionSheafOfModules :=
  HolomorphicTrivializingCover.ofLocalTrivializations _ E.sectionLocalTrivializations

@[simp]
lemma HolomorphicUnitExtension.frames_opens (E : HolomorphicUnitExtension X d)
    (z : ComplexPoint X) : E.frames.opens z = E.localLifts.opens z := rfl

/-- The frames of `E.sectionSheafOfModules` obtained from an algebraic trivializing cover of an
algebraic model of `E`, transported along the given isomorphism. -/
def extensionFramesOfAlgebraic (hgen : AnalytificationGenerates X d) {L : X.left.Modules}
    (t : Scheme.Modules.TrivializingCover L) (E : HolomorphicUnitExtension X d)
    (e : (moduleAnalytification X d).obj L ≅ E.sectionSheafOfModules) :
    HolomorphicTrivializingCover E.sectionSheafOfModules :=
  (analyticTrivializingCover hgen t).transport e

@[simp]
lemma extensionFramesOfAlgebraic_opens (hgen : AnalytificationGenerates X d)
    {L : X.left.Modules} (t : Scheme.Modules.TrivializingCover L)
    (E : HolomorphicUnitExtension X d)
    (e : (moduleAnalytification X d).obj L ≅ E.sectionSheafOfModules) (i : t.ι) :
    (extensionFramesOfAlgebraic hgen t E e).opens i = analyticOpen X (t.opens i) := rfl

/-- **Comparison with the extension's own frames.** On any open contained both in a member of
the analytified algebraic cover and in one of the local-lift neighbourhoods of `E`, the two
local frames of `E.sectionSheafOfModules` differ by a unit of the holomorphic structure sheaf,
i.e. by a nowhere-vanishing holomorphic function. Consequently the transition cocycle of the
analytified algebraic frames and the cocycle `E.transitionUnit` of `E`'s own frames are
cohomologous on the common refinement of the two covers. -/
theorem exists_isUnit_frameChange_extension (hgen : AnalytificationGenerates X d)
    {L : X.left.Modules} (t : Scheme.Modules.TrivializingCover L)
    (E : HolomorphicUnitExtension X d)
    (e : (moduleAnalytification X d).obj L ≅ E.sectionSheafOfModules)
    (i : t.ι) (z : ComplexPoint X) {V : Opens (TopCat.of (ComplexPoint X))}
    (h : V ≤ analyticOpen X (t.opens i)) (h' : V ≤ E.localLifts.opens z) :
    ∃ u : (holomorphicRingSheaf X d).obj.obj (op V), IsUnit u ∧
      u • holRes E.sectionSheafOfModules h ((extensionFramesOfAlgebraic hgen t E e).gen i) =
        holRes E.sectionSheafOfModules h' (E.frames.gen z) :=
  HolomorphicTrivializingCover.exists_isUnit_frameChange
    (extensionFramesOfAlgebraic hgen t E e) E.frames i z h h'

section Integral

variable [IsIntegral X.left]

/-- **The analytified local equations are the transition functions of the analytic frames.**
The local equation `fᵢ` of the rational section of `L` determined by the trivializing cover `t`
is the germ of the algebraic transition unit `uᵢ`; this says that the evaluation of `uᵢ` is the
transition function between the analytified frames on `Uᵢ^an` and on the reference member. -/
theorem analyticSection_transitionUnit (L : X.left.Modules)
    (t : Scheme.Modules.TrivializingCover L) (i : t.ι) :
    analyticFunction X d (t.overlap i) (t.transitionUnit i) •
        holRes ((moduleAnalytification X d).obj L) (analyticOpen_mono X inf_le_left)
          (analyticSection X d L (t.opens i) (t.gen i)) =
      holRes ((moduleAnalytification X d).obj L) (analyticOpen_mono X inf_le_right)
        (analyticSection X d L (t.opens t.base) (t.gen t.base)) :=
  analyticSection_smul_res L inf_le_left inf_le_right _ _ _ (t.transitionUnit_smul i)

/-- The same identity for the frames of `E.sectionSheafOfModules`: the transition functions of
the frames coming from an algebraic model are the evaluations of the algebraic ones. -/
theorem extensionFramesOfAlgebraic_transitionUnit (hgen : AnalytificationGenerates X d)
    {L : X.left.Modules} (t : Scheme.Modules.TrivializingCover L)
    (E : HolomorphicUnitExtension X d)
    (e : (moduleAnalytification X d).obj L ≅ E.sectionSheafOfModules) (i : t.ι) :
    analyticFunction X d (t.overlap i) (t.transitionUnit i) •
        holRes E.sectionSheafOfModules (analyticOpen_mono X inf_le_left)
          ((extensionFramesOfAlgebraic hgen t E e).gen i) =
      holRes E.sectionSheafOfModules (analyticOpen_mono X inf_le_right)
        ((extensionFramesOfAlgebraic hgen t E e).gen t.base) :=
  smul_holRes_map_iso e _ _ _ _ _ (analyticSection_transitionUnit L t i)

end Integral

end AlgebraicGeometry.ComplexPoint
