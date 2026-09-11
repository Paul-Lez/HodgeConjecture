/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ChernLocalModel
public import Other.AlgebraicGeometry.AnalyticSectionOfAlgebraic
public import Other.AlgebraicGeometry.CartierLocalForm
public import Other.AlgebraicGeometry.CycleComponentRestrictionInjective

/-!
# The winding-number reduction of the local model of the first Chern class

This file reduces `HasChernLocalModel X` — the last analytic obligation of §4.3 step 4 of
`docs/DIVISOR_HANDOFF.md` — to two obligations of strictly local nature, by introducing the object
that the Lelong–Poincaré computation is really about: the **winding homomorphism** of a chart.

## The mathematics

Let `Z = Z_x` be the component of a codimension-one point `x` of the divisor of a Cartier datum
`c`, and let `z` be a point of the smooth locus of `Z`. Choose a normal chart `V ∋ z` inside the
smooth-support open `cycleComponentSmoothSupportAmbientOpen X x`, small enough that

* `V` lies inside the analytification of an affine open on which the Cartier datum has an
  algebraic local form `c.fn i = u · h ^ n`, `n = c.divisor x`, `ord_x h = 1`, `h` cutting out
  `Z ∩ V` exactly (`Scheme.CartierData.exists_localForm`, `CartierLocalForm.lean`), and
* every invertible holomorphic function on `V` is an exponential (`V` a polydisc).

On `V` the line bundle is trivialised by the analytified generating section, and on `V ∖ Z` it is
trivialised by the rational section; the two frames differ by the analytification `h^an` of the
local equation, up to the unit `u^an`. The Chern class is computed by the composite

  `w : Γ(V ∖ Z, 𝒪ˣ) --δ--> H¹(V ∖ Z; ℚ) --∂--> H²_{Z}(V; ℚ)`,

`δ` the connecting map of the exponential sequence on the punctured chart — the winding number
`(1/2πi) ∮ d log` — and `∂` the connecting map of the pair `(V, V ∖ Z)`. The three facts that
together give the local model are

* **(a) naturality**: the restriction to `V` of the component piece `γ x` of a supported lift of
  the rational first Chern class is `w (u^an · (h^an) ^ n)`;
* **(b) winding**: `w` kills every invertible function that extends across `Z`, because such a
  function has a holomorphic logarithm on the polydisc `V`; hence
  `w (u^an · (h^an) ^ n) = n • w (h^an)`, additivity in `n` being automatic because the sections of
  `holomorphicUnitSheaf` are written *additively*;
* **(c) normalisation**: `w (h^an)` is the restriction to `V` of the repository's normalised
  normal-chart coclass `cycleComponentSmoothSupportCoclassSection`.

Combining, the restriction of `γ x` to `V` is `n` times the coclass. Both sides are sections of the
sheaf `supportRelativeCohomologySheaf`, so it is enough to check the equality on a cover of the
smooth-support open; the charts cover the part of it lying on `Z`, and on the complement of `Z`
*every* section of that sheaf vanishes — this is proved here, as
`supportRelativeCohomologySheaf_section_eq_zero`, from the fact that the sheafification map is an
isomorphism on stalks (`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`) together with the
repository's `supportRelativeCohomologyGerm_eq_zero_of_not_mem`.

## What this file contains

`ChernWindingChart X c x d p q` is the chart datum: an analytic open `V ∋ q` inside the
smooth-support open and inside the analytification of the affine open of an algebraic local form
of `c` at `x`, the analytified local equation `coord` as a unit on the punctured chart, the
hypothesis that every unit on `V` is an exponential, and an additive `winding` map
`Γ(V ∖ Z, 𝒪ˣ) →+ H²_{Z}(V)` landing in the sections over `V` of the local relative-cohomology
sheaf. The three facts above are the predicates

* `ChernWindingChart.ComputesClass` — (a),
* `ChernWindingChart.HasTrivialUnitWinding` — (b),
* `ChernWindingChart.NormalizesCoclass` — (c),

and `ChernWindingChart.restrict_eq_zsmul_coclass` **proves** that (a) + (b) + (c) give the local
form of the conclusion. The two remaining obligations are

* `HasNormalizedWindingCharts X` — normalised winding charts exist at every point of the component
  inside its smooth-support open *off a Zariski-closed subset `B ⊊ Z_x` not containing the generic
  point* ((b) and (c)); this mentions no line bundle and no Chern class, and is the pure
  one-variable analysis. The exceptional set `B` is forced:
  `Other/AlgebraicGeometry/ChernWindingLocalFormObstruction.lean` shows
  (`exists_chernWindingChart_imp_divisor_eq_zero`) that a chart at `q` can exist only if `q` lies
  on no other component of the divisor, because the affine open of an algebraic `LocalForm` never
  meets another component; and, more generally, the affine open of any given local form only
  covers a dense open of `Z_x`. Requiring charts on the complement of a proper Zariski-closed
  subset of `Z_x` is exactly what a single local form (`Scheme.CartierData.exists_localForm`)
  can deliver, and it costs nothing, by the gluing lemma
  `cycleComponentSmoothSupport_restriction_injective`
  (`Other/AlgebraicGeometry/CycleComponentRestrictionInjective.lean`): since every point of `B`
  has codimension at least two in `X`, restriction of sections of the local relative-cohomology
  sheaf from the smooth-support open `U` to `U ∖ B^an` is injective, so an equality of sections
  over `U` may be checked over `U ∖ B^an`.
* `HasChernWindingNaturality X` — there *exists* a supported lift `β` of the first Chern class for
  which (a) holds on *every* normalised winding chart; this is the Chern-class half, and is where
  §4.2(a) of the handoff (a cocycle description of the connecting map `H¹(𝒪ˣ) → H²(ℤ)`) is needed.
  The lift must be quantified existentially: an arbitrary lift of `c₁` has the wrong local
  multiplicities — for `X = ℙ¹`, `L = 𝒪`, `s = z`, `D = [0] − [∞]`, `c₁ = 0`, both `(1, −1)` and
  `(2, −2)` lift `c₁` in `H²_{\{0,∞\}}(ℙ¹, ℚ) ≅ ℚ²` — so the obligation includes constructing the
  canonical one, the relative first Chern class cut out by the frame of the bundle off `|D|^an`.
  The decomposition `γ` is still quantified universally, which is harmless because it is unique.

`hasChernLocalModel_of_winding` **proves** that the two together give `HasChernLocalModel X`, and
`hasChernWindingNaturality_of_localModel` proves the converse implication for the second one, so
that, granted normalised charts, `HasChernWindingNaturality X ↔ HasChernLocalModel X`: the
reduction is faithful and does not weaken the target.

The winding homomorphism is *data* in the chart rather than a construction, because neither `∂`
(the connecting map of the pair in the repository's `RelativeCohomology`, which has no long exact
sequence yet) nor `δ` (which needs the exponential sequence on an open subspace together with the
Betti comparison) exists in the repository. Constructing `w` is the first step of any attack on
`HasNormalizedWindingCharts`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Order
open AlgebraicTopology.Singular

namespace AlgebraicTopology.Singular

/-! ### Vanishing of the local relative-cohomology sheaf off its support -/

variable (M : TopCat.{0}) (S : Set M) (n : ℕ)

/-- Off a closed support the local relative-cohomology sheaf has vanishing stalks: every germ is
the germ of an actual relative class (the sheafification map is an isomorphism on stalks), and
every such germ vanishes off the support. -/
theorem supportRelativeCohomologySheaf_subsingleton_stalk (hS : IsClosed S)
    (y : M) (hy : y ∉ S) :
    Subsingleton ((supportRelativeCohomologySheaf M S n).presheaf.stalk y) := by
  constructor
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y AddCommGrpCat
    (supportRelativeCohomologyPresheaf M S n)
  have hsurj : Function.Surjective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology M)
        (supportRelativeCohomologyPresheaf M S n))) :=
    (ConcreteCategory.bijective_of_isIso _).2
  have key : ∀ t : (supportRelativeCohomologySheaf M S n).presheaf.stalk y, t = 0 := by
    intro t
    obtain ⟨t₀, rfl⟩ := hsurj t
    obtain ⟨V, hyV, a, rfl⟩ := (supportRelativeCohomologyPresheaf M S n).exists_germ_eq t₀
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact supportRelativeCohomologyGerm_eq_zero_of_not_mem M S n hS V y hyV hy a
  intro a b
  rw [key a, key b]

/-- Every section of the local relative-cohomology sheaf over an open set disjoint from the
(closed) support vanishes. -/
theorem supportRelativeCohomologySheaf_section_eq_zero (hS : IsClosed S) (V : Opens M)
    (hV : ∀ y ∈ V, y ∉ S)
    (s : (supportRelativeCohomologySheaf M S n).obj.obj (op V)) : s = 0 := by
  refine TopCat.Presheaf.section_ext _ V s 0 fun y hy => ?_
  have := supportRelativeCohomologySheaf_subsingleton_stalk M S n hS y (hV y hy)
  exact Subsingleton.elim _ _

end AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernLocalModelWindingAnalyticTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable (c : Scheme.CartierData X.left) (x : X.left) (d p : ℕ)
  [SmoothOfRelativeDimension d X.hom]

/-- A local winding chart at a point `q` of the smooth-support open of the component of `x`. -/
structure ChernWindingChart (q : ComplexPoint X) where
  /-- index of a member of the Cartier cover containing `x` -/
  index : c.ι
  /-- the algebraic local form of the Cartier datum at `x` -/
  localForm : c.LocalForm index x
  /-- the analytic chart -/
  carrier : Opens (ComplexPoint X)
  mem : q ∈ carrier
  le : carrier ≤ cycleComponentSmoothSupportAmbientOpen X x
  le_analytic : carrier ≤ analyticOpen X localForm.opens
  /-- the analytified local equation, as a unit on the punctured chart -/
  coord : (holomorphicUnitSheaf X d).obj.obj
    (op (carrier ⊓ (cycleComponentAnalyticClosedSupport X x).compl))
  coord_eq : ((Additive.toMul coord).val :
      (holomorphicRingSheaf X d).obj.obj
        (op (carrier ⊓ (cycleComponentAnalyticClosedSupport X x).compl))) =
    (holomorphicRingSheaf X d).obj.map
      (homOfLE (le_trans inf_le_left le_analytic)).op
      (analyticFunction X d localForm.opens localForm.equation)
  /-- the winding homomorphism -/
  winding : ((holomorphicUnitSheaf X d).obj.obj
      (op (carrier ⊓ (cycleComponentAnalyticClosedSupport X x).compl))) →+
    ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
      (2 * p)).obj.obj (op carrier))
  /-- every invertible holomorphic function on the chart is an exponential -/
  exists_log : ∀ u : (holomorphicUnitSheaf X d).obj.obj (op carrier),
    ∃ f : (holomorphicAdditiveSheaf X d).obj.obj (op carrier),
      (holomorphicExponential X d).hom.app (op carrier) f = u

namespace ChernWindingChart

variable {X c x d p} {q : ComplexPoint X} (ch : ChernWindingChart X c x d p q)

/-- The punctured chart: the chart minus the support of the component. -/
abbrev punctured : Opens (ComplexPoint X) :=
  ch.carrier ⊓ (cycleComponentAnalyticClosedSupport X x).compl

theorem punctured_le : ch.punctured ≤ ch.carrier := inf_le_left

/-- Restriction of an invertible holomorphic function from the chart to the punctured chart. -/
abbrev restrictUnit (u : (holomorphicUnitSheaf X d).obj.obj (op ch.carrier)) :
    (holomorphicUnitSheaf X d).obj.obj (op ch.punctured) :=
  (holomorphicUnitSheaf X d).obj.map (homOfLE ch.punctured_le).op u

/-- **(b) Winding.** The winding homomorphism kills every invertible holomorphic function that
extends across the component. -/
def HasTrivialUnitWinding : Prop :=
  ∀ u : (holomorphicUnitSheaf X d).obj.obj (op ch.carrier), ch.winding (ch.restrictUnit u) = 0

/-- **(c) Normalisation.** The winding class of the analytified local equation is the restriction
to the chart of the repository's normalised normal-chart coclass. -/
def NormalizesCoclass (hx : coheight x = p) : Prop :=
  ch.winding ch.coord =
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
      (2 * p)).obj.map (homOfLE ch.le).op
      (cycleComponentSmoothSupportCoclassSection X x (d := d) hx)

/-- **(a) Naturality.** The restriction to the chart of the supported class `a` is the winding
class of the local equation of the bundle, namely of `u * h ^ n`. -/
def ComputesClass (n : ℤ)
    (a : (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
      (2 * p)).obj.obj (op (cycleComponentSmoothSupportAmbientOpen X x))) : Prop :=
  ∃ u : (holomorphicUnitSheaf X d).obj.obj (op ch.carrier),
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
        (2 * p)).obj.map (homOfLE ch.le).op a =
      ch.winding (ch.restrictUnit u + n • ch.coord)

/-- **The local combination of (a), (b) and (c).** -/
theorem restrict_eq_zsmul_coclass (hx : coheight x = p) (n : ℤ)
    (a : (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
      (2 * p)).obj.obj (op (cycleComponentSmoothSupportAmbientOpen X x)))
    (ha : ch.ComputesClass n a) (hb : ch.HasTrivialUnitWinding)
    (hc : ch.NormalizesCoclass hx) :
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
        (2 * p)).obj.map (homOfLE ch.le).op a =
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
        (2 * p)).obj.map (homOfLE ch.le).op
        (n • cycleComponentSmoothSupportCoclassSection X x (d := d) hx) := by
  obtain ⟨u, hu⟩ := ha
  rw [hu, map_add, hb u, zero_add, map_zsmul, hc, map_zsmul]

end ChernWindingChart

variable {c x d p}

/-! ### Non-vacuity -/

/-- Given a chart whose winding homomorphism is normalised — (b) and (c) — the naturality
statement (a) is *equivalent* to the local form of the conclusion: it holds with the trivial unit
as soon as the restriction of the class to the chart is `n` times the coclass. This is the
non-vacuity check for `ChernWindingChart.ComputesClass`: the predicate is satisfiable, and the
content of obligation (a) below is entirely in the passage from the first Chern class to the
winding of the local equation, not in the shape of the statement. -/
theorem computesClass_of_restrict_eq {q : ComplexPoint X}
    (ch : ChernWindingChart X c x d p q)
    (hx : coheight x = p) (n : ℤ) (hb : ch.HasTrivialUnitWinding)
    (hc : ch.NormalizesCoclass hx)
    (a : (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
      (2 * p)).obj.obj (op (cycleComponentSmoothSupportAmbientOpen X x)))
    (ha : (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * p)).obj.map (homOfLE ch.le).op a =
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * p)).obj.map (homOfLE ch.le).op
        (n • cycleComponentSmoothSupportCoclassSection X x (d := d) hx)) :
    ch.ComputesClass n a := by
  refine ⟨0, ?_⟩
  rw [map_add, hb 0, zero_add, map_zsmul, hc, ha, map_zsmul]

/-! ### The two obligations and the reduction -/

/-- **Obligation (b) + (c): normalised winding charts exist.**

At every point of the smooth-support open of a codimension-one component `Z_x`, and for every
Cartier datum `c`, there is an analytic chart carrying an algebraic local form of `c` at `x`, on
which every invertible holomorphic function is an exponential, together with a winding
homomorphism from the invertible holomorphic functions on the punctured chart to the local
relative cohomology of the chart along `Z_x`, which

* kills the invertible functions that extend across `Z_x` (`HasTrivialUnitWinding`), and
* sends the analytified local equation to the repository's normalised normal-chart coclass
  (`NormalizesCoclass`).

Mathematically the winding homomorphism is `∂ ∘ δ`, where `δ` is the connecting map of the
exponential sequence on the punctured chart (the winding number `(1/2πi) ∮ d log`) and `∂` is the
connecting map `H¹(V ∖ Z) → H²_Z(V)` of the pair. (b) is then the statement that a unit on a
polydisc has a holomorphic logarithm (`ContMDiffAt.exists_holomorphic_log`), and (c) is the
one-variable computation `∂ δ z₁ = ` normal coclass. This obligation involves no line bundle and
no Chern class.

**The exceptional set.** The charts are only required at the points of the smooth-support open
lying on `Z_x` *and off a Zariski-closed subset `B ⊆ Z_x` not containing the generic point `x`*,
which the obligation may choose (depending on `c` and `x`). This is forced by
`Other/AlgebraicGeometry/ChernWindingLocalFormObstruction.lean`
(`exists_chernWindingChart_imp_divisor_eq_zero`): the affine open of an algebraic local form of
`c` at `x` never meets another component of the divisor, so no chart can exist at a point of
`Z_x ∩ Z_y`, `y ≠ x`; and the affine open of a single local form only covers a dense open of
`Z_x` anyway. Taking `B = Z_x ∖ (affine open of the local form)` is the intended choice. The
reduction still goes through because every point of `B` is a proper specialisation of `x`, hence
has codimension at least two in `X`, and restriction of the local relative-cohomology sheaf from
the smooth-support open to the complement of `B^an` is injective
(`cycleComponentSmoothSupport_restriction_injective`). -/
def HasNormalizedWindingCharts : Prop :=
  ∀ (c : Scheme.CartierData X.left) (x : X.left) (hx : coheight x = ((1 : ℕ) : ℕ∞)),
    ∃ B : Closeds X.left, (B : Set X.left) ⊆ closure ({x} : Set X.left) ∧ x ∉ B ∧
      ∀ q ∈ cycleComponentSmoothSupportAmbientOpen X x, q ∈ cycleComponentSupport X x →
        Point.underlying q ∉ B →
        ∃ ch : ChernWindingChart X c x (dim X.left) 1 q,
          ch.HasTrivialUnitWinding ∧ ch.NormalizesCoclass hx

/-- The previous, pointwise form of the obligation — charts at *every* point of the
smooth-support open lying on the component — implies the generic one (take `B = ∅`). It is
false in general (`ChernWindingLocalFormObstruction.lean`), so this is only a compatibility
lemma. -/
theorem hasNormalizedWindingCharts_of_forall
    (h : ∀ (c : Scheme.CartierData X.left) (x : X.left) (hx : coheight x = ((1 : ℕ) : ℕ∞)),
      ∀ q ∈ cycleComponentSmoothSupportAmbientOpen X x, q ∈ cycleComponentSupport X x →
        ∃ ch : ChernWindingChart X c x (dim X.left) 1 q,
          ch.HasTrivialUnitWinding ∧ ch.NormalizesCoclass hx) :
    HasNormalizedWindingCharts X :=
  fun c x hx => ⟨⊥, Set.empty_subset _, Set.notMem_empty x, fun q hq hqS _ => h c x hx q hq hqS⟩

/-- **Obligation (a): naturality of the supported first Chern class.**

There is a supported lift `β` of the rational first Chern class — the *relative* first Chern class
cut out by the frame of the bundle off `|D|^an` — such that for *every* normalised winding chart,
the restriction to the chart of the component piece `γ x` of any decomposition of `β` is the
winding class of the local equation `u · h ^ (c.divisor x)` of the bundle.

The lift is quantified **existentially**: an arbitrary lift of the first Chern class does not have
the right local multiplicities (see the docstring of `HasChernLocalModel` for the `ℙ¹`
counterexample), so this obligation includes the construction of the canonical one. The
decomposition `γ` is quantified universally, which is harmless: it is unique, because the
codimension-two vanishing makes the enlargement maps jointly bijective, not merely surjective.

This is the Chern-class half of the local model: it is where §4.2(a) of
`docs/DIVISOR_HANDOFF.md` — a description of the connecting map `H¹(𝒪ˣ) → H²(ℤ)` by the cocycle of
the transition units — enters, through `Scheme.CartierData.Represents` and
`extensionFramesOfAlgebraic_transitionUnit`: on the chart the bundle is framed by the analytified
generating section, and the rational section frames it off `Z_x`, the two frames differing by the
analytification of the local equation `c.fn index = u · h ^ (c.divisor x)`. -/
def HasChernWindingNaturality : Prop :=
  ∀ (E : HolomorphicUnitExtension X (dim X.left)) (L : X.left.Modules),
    TauCeti.SheafOfModules.IsInvertible L →
    ((moduleAnalytification X (dim X.left)).obj L ≅ E.sectionSheafOfModules) →
    ∀ c : Scheme.CartierData X.left, c.Represents L →
      ∃ β : SupportedInjectiveHomology X (cycleAnalyticClosedSupport X c.divisor)
          (2 * ((1 : ℕ) : ℤ)),
        supportedInjectiveToAmbient X (cycleAnalyticClosedSupport X c.divisor)
            (2 * ((1 : ℕ) : ℤ)) β =
          rationalCohomologyAddEquivAmbientInjectiveHomology X (2 * ((1 : ℕ) : ℤ))
            (integralToRationalCohomology X 2 E.firstChernClass) ∧
        ∀ γ : ∀ x : X.left,
            SupportedInjectiveHomology X (cycleComponentAnalyticClosedSupport X x)
              (2 * ((1 : ℕ) : ℤ)),
          β = ∑ x ∈ cycleComponents X c.divisor,
              componentContribution X (cycleComponents X c.divisor) x (2 * ((1 : ℕ) : ℤ)) (γ x) →
          ∀ x ∈ cycleComponents X c.divisor, ∀ hx : coheight x = ((1 : ℕ) : ℕ∞),
          ∀ (q : ComplexPoint X) (ch : ChernWindingChart X c x (dim X.left) 1 q),
            ch.HasTrivialUnitWinding → ch.NormalizesCoclass hx →
            ch.ComputesClass (c.divisor x)
              ((cycleComponentSupportedClassNormalizationIso X x (d := dim X.left) hx).hom (γ x))

/-- Obligation (a) is no stronger than the target: if the local model holds, then its normalised
lift makes every normalised winding chart compute the class. Together with
`hasChernLocalModel_of_winding` this shows that, granted `HasNormalizedWindingCharts X`,
obligation (a) is *equivalent* to `HasChernLocalModel X`; in particular the reduction does not
weaken the target. -/
theorem hasChernWindingNaturality_of_localModel (h : HasChernLocalModel X) :
    HasChernWindingNaturality X := by
  intro E L hL iso c hc
  obtain ⟨β, hβ, hlocal⟩ := h E L hL iso c hc
  refine ⟨β, hβ, ?_⟩
  intro γ hγ x hxs hx q ch hb hcn
  refine computesClass_of_restrict_eq X ch hx (c.divisor x) hb hcn _ ?_
  exact congrArg ((supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
    (cycleComponentSupport X x) (2 * 1)).obj.map (homOfLE ch.le).op)
    (hlocal γ hγ x hxs hx)

/-- Restriction along a composite of open inclusions, for sections of a sheaf on a space. -/
theorem sheaf_map_map_eq {M : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat M)
    {U V W : Opens M} (f : W ⟶ V) (g : V ⟶ U) (h : W ⟶ U) (a : F.obj.obj (op U)) :
    F.obj.map f.op (F.obj.map g.op a) = F.obj.map h.op a := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 2

/-- **The reduction.** The existence of normalised winding charts (obligations (b) and (c)) and
the naturality of the supported first Chern class on them (obligation (a)) together imply the
local model `HasChernLocalModel X`, hence, with `hasDivisorClassOfSomeCartierData_of_localModel`,
the remaining obligation of `docs/DIVISOR_HANDOFF.md` §3.

The equality of sections over the smooth-support open `U` is first reduced, by the injectivity
of restriction `cycleComponentSmoothSupport_restriction_injective`, to an equality over
`U ∖ B^an`, `B` the exceptional set of the charts; that open is covered by the charts (at its
points on `Z_x`, all of which lie off `B`) together with its part off `Z_x`, where every section
of the sheaf vanishes. -/
theorem hasChernLocalModel_of_winding (h₁ : HasNormalizedWindingCharts X)
    (h₂ : HasChernWindingNaturality X) : HasChernLocalModel X := by
  intro E L hL iso c hc
  obtain ⟨β, hβ, hnat⟩ := h₂ E L hL iso c hc
  refine ⟨β, hβ, ?_⟩
  intro γ hγ x hxs hx
  obtain ⟨B, hB, hxB, hch⟩ := h₁ c x hx
  choose ch hunit hnorm using
    fun q : {q : ComplexPoint X // q ∈ cycleComponentSmoothSupportAmbientOpen X x ∧
        q ∈ cycleComponentSupport X x ∧ Point.underlying q ∉ B} =>
      hch q.1 q.2.1 q.2.2.1 q.2.2.2
  -- reduce to the complement of the exceptional set, where restriction is injective
  refine cycleComponentSmoothSupport_restriction_injective X x (d := dim X.left) hx B hB hxB ?_
  -- the charts cover the part of that open lying on the component; the rest is covered by the
  -- complement of the component, where the whole sheaf vanishes.
  refine TopCat.Sheaf.eq_of_locally_eq'
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x)
      (2 * 1))
    (fun q : Option {q : ComplexPoint X // q ∈ cycleComponentSmoothSupportAmbientOpen X x ∧
        q ∈ cycleComponentSupport X x ∧ Point.underlying q ∉ B} =>
      q.elim ((cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl) ⊓
        (cycleComponentAnalyticClosedSupport X x).compl)
        fun q => (ch q).carrier ⊓
          (cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl))
    (cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl)
    (fun q => match q with
      | none => homOfLE inf_le_left
      | some _ => homOfLE inf_le_right) ?_ _ _ ?_
  · intro y hy
    rw [Opens.mem_iSup]
    by_cases hyS : y ∈ cycleComponentSupport X x
    · exact ⟨some ⟨y, hy.1, hyS, hy.2⟩, (ch ⟨y, hy.1, hyS, hy.2⟩).mem, hy⟩
    · exact ⟨none, hy, hyS⟩
  · rintro (_ | q)
    · have hVS : ∀ y ∈ ((cycleComponentSmoothSupportAmbientOpen X x ⊓
          (analyticClosedSupport X B).compl) ⊓
          (cycleComponentAnalyticClosedSupport X x).compl :
            Opens (TopCat.of (ComplexPoint X))), y ∉ cycleComponentSupport X x :=
        fun _ hy => hy.2
      exact (AlgebraicTopology.Singular.supportRelativeCohomologySheaf_section_eq_zero
          (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x) (2 * 1)
          (cycleComponentAnalyticClosedSupport X x).isClosed _ hVS _).trans
        (AlgebraicTopology.Singular.supportRelativeCohomologySheaf_section_eq_zero
          (TopCat.of (ComplexPoint X)) (cycleComponentSupport X x) (2 * 1)
          (cycleComponentAnalyticClosedSupport X x).isClosed _ hVS _).symm
    · have key := (ch q).restrict_eq_zsmul_coclass hx (c.divisor x) _
        (hnat γ hγ x hxs hx q.1 (ch q) (hunit q) (hnorm q)) (hunit q) (hnorm q)
      let F := supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * 1)
      let U' : Opens (ComplexPoint X) :=
        cycleComponentSmoothSupportAmbientOpen X x ⊓ (analyticClosedSupport X B).compl
      let i : (ch q).carrier ⊓ U' ⟶ U' := homOfLE inf_le_right
      let j : U' ⟶ cycleComponentSmoothSupportAmbientOpen X x := homOfLE inf_le_left
      let k : (ch q).carrier ⊓ U' ⟶ (ch q).carrier := homOfLE inf_le_left
      let l : (ch q).carrier ⟶ cycleComponentSmoothSupportAmbientOpen X x := homOfLE (ch q).le
      let m : (ch q).carrier ⊓ U' ⟶ cycleComponentSmoothSupportAmbientOpen X x :=
        homOfLE (le_trans inf_le_left (ch q).le)
      have key' := congrArg (F.obj.map k.op) key
      exact (sheaf_map_map_eq F i j m _).trans
        ((sheaf_map_map_eq F k l m _).symm.trans (key'.trans
          ((sheaf_map_map_eq F k l m _).trans (sheaf_map_map_eq F i j m _).symm)))

end AlgebraicGeometry.ComplexPoint
