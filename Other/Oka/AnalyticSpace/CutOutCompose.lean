/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.CutOutCancel
public import Other.Oka.AnalyticSpace.LocalModel

/-!
# Composing cut-out data: cutting a subspace down further, inside the same ambient space

`ComplexAnalytic.IsCutOutBy i f` says that the closed immersion `i` exhibits its source as the
subspace of its target cut out by the global sections `f`. `Other/Oka/AnalyticSpace/CutOutCancel.lean`
**cancels** such data: from a datum for `iW : W ⟶ Z` and one for `j ≫ iW : Y ⟶ Z` it produces the
datum for `j : Y ⟶ W`. This file goes the other way
(`ComplexAnalytic.IsCutOutBy.comp_append`): from a datum for `iW` by `f₁` and one for `j` by the
**pullbacks of `f₂` along `iW`**, it produces the datum for `j ≫ iW` by `f₁` together with `f₂`.

That is the direction a *construction* runs in. A cancellation takes a subspace that is already
known to sit inside the ambient space and re-reads it relative to an intermediate one; a
composition builds a new subspace of the intermediate space and asks what it is inside the
ambient one. **`ComplexAnalytic.AnalyticSpace.ofCutOut` is why the question has to be asked**: its
ambient space is fixed by its signature to an open subspace of some `ℂ^n`, so a subspace of a
local model becomes an object of `ComplexAnalytic.AnalyticSpace` only once it is presented as a
subspace of that `ℂ^n|V`, and the presentation is exactly the appended family.

## The consumer, and the case this does not cover

`ComplexAnalytic.AnalyticSpace.ofCutOutZeroLocus` is the construction this was written for: **a
local model cut down by the pullbacks of finitely many further sections of its ambient `ℂ^n|V` is
again a local model**, with the appended family presenting it. The fibre product of two local
models over a third is the shape that wants it ; it is
`ComplexAnalytic.AnalyticSpace.prodCutOut` cut down by the `p` differences of the two composites
to `ℂ^p` ; and **this file does not reach it**, because those differences are sections of the
product rather than of the product's ambient space and nothing here manufactures a lift.

**What is needed for that is a lift on a neighbourhood rather than a global one**, and
`AlgebraicGeometry.LocallyRingedSpace.exists_localLift_family`
(`Other/Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`) already supplies one along any morphism whose
stalk maps are surjective, which every cut-out datum's is. Assembling that into a chart is a
`ComplexAnalytic.HasLocalModels` argument over a restriction of a restriction, and it is not here.

**It is in `Other/Oka/AnalyticSpace/ZeroLocus.lean`**, which imports this file ; one edge, measured ;
and which runs that assembly for the zero locus of finitely many global sections of an *arbitrary*
complex analytic space. **The sentence ending `nothing here manufactures a lift` and the one
ending `and it is not here` are about this file and are unchanged by it**:
`ComplexAnalytic.IsCutOutBy.comp_append` is still what that assembly calls, and the
lift is still not manufactured below. **What that file supplies is an ingredient of the fibre
product of two local models and not the fibre product**: it cuts a space down by *its own* global
sections, where the paragraph ending `nothing here manufactures a lift` needs the `p` differences
of two composites to `ℂ^p`, which are sections of
`ComplexAnalytic.AnalyticSpace.prodCutOut` and are exactly that. This paragraph
was added on 2026-09-07 by the push that added that file.

**That sentence read `is still what that assembly's last step calls` until 2026-09-07, and it was
false when written rather than falsified later, so this is a correction and not one of this
repository's dated records.** `Other/Oka/AnalyticSpace/ZeroLocus.lean`'s `## The route` numbers five
steps and `ComplexAnalytic.IsCutOutBy.comp_append` is the fourth; the fifth is the two changes of
chart, which call `ComplexAnalytic.IsCutOutBy.comp_iso` and
`ComplexAnalytic.IsCutOutBy.iso_comp`, and the proof there reads the same way round ; the datum
the existential is handed is the one those two produce. **The clause the sentence was making its
point with is true without the numeral**, which is why the numeral is gone rather than corrected
to *fourth*: what matters is that the assembly still calls this file's lemma.
**The sister sentence read `where the paragraph above needs the p differences of two composites`
until the same date and now names that paragraph by the words it ends with**, for taxis #1709's
reason: a pointer that reaches a paragraph by position cannot survive a paragraph being inserted
between the two, and a quotation can.

## What each of the four conditions costs

**Nothing here is analysis**; `ComplexAnalytic.IsCutOutBy.comp_append` is four statements about a
factorisation `j ≫ iW` of closed immersions of locally ringed spaces, and the corollaries below
are it applied to a zero locus. The file is beside `Other/Oka/AnalyticSpace/CutOutCancel.lean` rather
than in the mirror tree because `ComplexAnalytic.IsCutOutBy` is declared in this repository.

* **The closed embedding** is `Topology.IsClosedEmbedding.comp` and nothing else. Both halves are
  hypotheses here, where the cancellation had to recover one of them from a preimage.
* **`range_base`** splits over `Fin.append f₁ f₂` in both directions. Left to right, the `f₁` half
  is `hW.range_base` at a point of `Set.range iW.base` and the `f₂` half is `hY.range_base`
  transferred along `iW`'s stalk map. Right to left, **the `f₁` half is what produces the point of
  `W` to work at**: a point of the ambient space at which the germs of `f₁` lie in the maximal
  ideal is in the image of `iW` by `hW.range_base`, and only then does the `f₂` half say anything.
  That asymmetry is the whole difference from the cancellation's proof of the same field.
* **The transfer itself** is that `iW`'s stalk map is a **local** ring homomorphism, so it
  reflects units as well as preserving them; `htrans` in the proof below is that statement and it
  is quoted verbatim from `ComplexAnalytic.IsCutOutBy.of_comp_append`, where it appears with the
  same two sides.
* **`surjective_stalkMap`** is `AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp` and the
  composite of two surjections, and asks nothing of either family.
* **`ker_stalkMap` is where the surjectivity of `iW`'s stalk map is spent**, as in the
  cancellation, but through the opposite lemma. Writing `φ` for that stalk map and `ψ` for `j`'s,
  `RingHom.comap_ker` gives `RingHom.ker (ψ.comp φ) = Ideal.comap φ (RingHom.ker ψ)`;
  `hY.ker_stalkMap` presents `RingHom.ker ψ` as a span, which `Ideal.map_span` turns into
  `Ideal.map φ` of the span of the germs of `f₂`; and `Ideal.comap_map_of_surjective` collapses
  `Ideal.comap φ (Ideal.map φ ·)` to a join with `RingHom.ker φ`, which is `hW.ker_stalkMap`.
  The cancellation used `Ideal.map_comap_of_surjective` at the same point, which is the reason
  `Other/Oka/AnalyticSpace/CutOutCancel.lean` records that this direction *"is a different proof"*.

## Why the hypothesis is the pullbacks and not an arbitrary family

`ComplexAnalytic.IsCutOutBy.comp_append` asks that the inner subspace be cut out by the pullbacks
of `f₂` along `iW` ; sections of the **ambient** space, carried to `W` ; and not by an arbitrary
family on `W`. That is not a convenience: the conclusion presents the composite inside `Z`, and a
family on `W` with no ambient preimage names no ideal of `𝒪_Z`. It is also the exact hypothesis
`ComplexAnalytic.IsCutOutBy.of_comp_append` *concludes*, so the two are inverse to each other on
the nose and neither needs a compatibility lemma to be read against the other.

**Those pullbacks were spelled `iW.pullbackΓ (f₂ r)` here until 2026-09-07**, which is not a term.
`pullbackΓ` is declared for morphisms of *analytic* spaces
(`ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ`, an `abbrev` in `Other/Oka/AnalyticSpace/Basic.lean`),
and `iW` is a morphism of locally ringed spaces; the statement below writes its action on global
sections out through `AlgebraicGeometry.LocallyRingedSpace.Γ` instead.

**`scripts/check_docstring_names.py` was silent on it twice over, and the two reasons are
different.** Its candidates are backticked spans with no whitespace in them, so a spelling
carrying an argument was never a candidate at all; and written bare it would have been a
candidate and would have passed ; not by resolving, but by that script's **short-head rule**.
`MAX_LOCAL_HEAD` is 2 in that script, and `is_local_binder` accepts a candidate whose head
component is at most two characters and is not a root namespace, as field notation on a local
binder; that test is tried before the field-notation rule and **the tail is not consulted at
all**. `iW` is two characters and is not a root namespace. The same rule is what covers
`hY.range_base` and `hY.ker_stalkMap` in the section above, which happen to be right.

**Four plantings in this checkout on 2026-09-07 say which rule fires, rather than a reading of the
script.** Put a candidate in this paragraph and run the checker. `iW.pullbackΓ` passes at
*0 unresolved*. `iW.zzzBogusNotAName`, whose tail names nothing whatever, passes at *0 unresolved*
too. The same tail under a head one character longer is **reported** at *1 unresolved*, *"names
nothing in the environment"* ; and that control is written here as *iWx.pullbackΓ* without
backticks, because backticking it is what would make the checker report it, which is the point.
*Eq.symmm* is reported too, and it is the *not a root namespace* half of the rule that reports
it ; a head of two characters is not on its own enough. The head decides and the tail is not
read.

**The second reason was given here as resolution until 2026-09-07** ; *"it would still have
resolved, because the head of such a token is a bound variable of the theorem, leaving the checker
no type to consult, and a declaration ending in that component existing anywhere in the
environment is enough"* ; and that was inferred rather than run, and is false. It is kept as this
paragraph's dated record and nothing is struck. `scripts/DumpEnvNames.lean` wrote **336927** rows
on that date, **331311** of them declarations and **5616** modules, and among them the constants
named `iW` number **0**, those whose last component is `iW` number **0**, and those with `iW` at
the root number **0**. The field-notation rule needs a proper prefix of the candidate to resolve
to a declaration, which for a two-component name is the head, so it cannot fire here; and the
suffix rule matches whole components, of which `iW.pullbackΓ` is not a run in
`ComplexAnalytic.AnalyticSpace.Hom.pullbackΓ`.

**Neither reason is a defect in the checker ; and what a green run settles is narrower than this
paragraph said until 2026-09-07** (*"what it settles is whether a name exists, not whether it
exists at the type it is written at"*, kept here as a dated record). For a citation the short-head
rule accepts, it settles nothing about the tail, not even that the tail names something. So a run
reporting 0 unresolved is not evidence about a spelling whose head is one or two characters and is
not a root namespace.

## An import relation that was inferred rather than measured

The `ComplexAnalytic.AnalyticSpace.ofCutOutZeroLocus` bullet read *"that declaration arriving in
`Other/Oka/AnalyticSpace/CutOutProduct.lean`, which is downstream of this file"* until 2026-09-07.
**The two files are incomparable.** Neither is in the other's import closure, and on that date
`Oka.lean` was the only module importing either. The figures that replaced the word are a run of
2026-09-07 over this checkout: closures of **42** and **65** modules under `Other/Oka/`, each counting
the file itself, so importing that file here costs **25** and importing this one there costs
**2**.

**The instrument is worth naming, because the obvious one gets both totals wrong.** A `^import`
regex over the raw file text follows an `import` written inside a comment, and in this tree it
also misses every `public import` line; `scripts/import_cost.py`'s parser masks and matches both,
and it is that parser and that pattern, rather than the script's command line, which produced the
four figures above ; the script prices a mirror file against a Mathlib target and does not take
these two module names as arguments. Against the naive regex the same two closures come out at
**28** and **51**, each **14** modules short, all fourteen behind a `public import` under
`Other/Oka/Algebra/Category/ModuleCat/Sheaf/`: the modules the naive closure does reach that carry such
an import are `Other/Oka/Algebra/Category/ModuleCat/Sheaf/Coherent/Criterion.lean` and
`Other/Oka/Algebra/Category/ModuleCat/Sheaf/Coherent/Free.lean`.
Swept at `ca96745` over every tracked `.lean` file, the tree holds eight comment-embedded `import`
matches across seven files, and every one of them names a module that does not exist, so it is the
`public import` and not the comment that costs here. **That clause opened *"At this commit the tree
holds eight comment-embedded `import` matches across seven files"* until 2026-09-07**, and the
figure was exact at `ca96745`, the commit that wrote it; what retired the wording is the pin and not
the count. lana-agents/oka#494 wrapped a line of prose onto `import` in
`Other/Oka/Analytification/SpecDistinguishedOpen.lean` and took the tree to **nine** matches across
**eight** files at `db7b658`; the push carrying this record is taxis #1847 and returns it to eight
across seven. **Neither that file nor this one is in the other's import closure** ; measured with
`scripts/import_cost.py`'s `IMPORT` pattern over its nesting-aware `strip_comments`, which is the
same instrument as the figures above ; so a count of the whole tree pinned to *this commit* can be
falsified by a push this file cannot reach, and leaves a reader no commit to measure at. **The
count is not what the argument needs**: the essential half is that every match names a module
that does not exist, and that held at eight, at nine and at eight again.
**The two costs survive the naive regex unchanged**, 25 and 2 either way, so a delta that agrees
is not evidence that either closure was computed correctly.

## Main results

- `ComplexAnalytic.IsCutOutBy.comp_append`: **the composition** ; if `iW` cuts out `W` inside `Z`
  by `f₁` and `j` cuts out `Y` inside `W` by the pullbacks of `f₂` along `iW`, then `j ≫ iW` cuts
  out `Y` inside `Z` by `Fin.append f₁ f₂`.
- `ComplexAnalytic.IsCutOutBy.comp_of_range_eq`: the same at the family a caller holds, whose
  range is the union of the two ranges and which need not be a literal `Fin.append`.
- `ComplexAnalytic.IsCutOutBy.zeroLocusSubspaceι_comp`: **the zero locus inside a cut-out
  subspace of the pullbacks of ambient sections is cut out of the ambient space by the appended
  family.** This is the composition at the datum
  `AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι`, which holds for every
  locally ringed space and every finite family, so the hypotheses of the composition are met by
  something rather than only satisfiable in principle.
- `ComplexAnalytic.AnalyticSpace.ofCutOutZeroLocus`: **a local model cut down by the pullbacks of
  further sections of its ambient `ℂ^n|V` is a complex analytic space.** Its closed immersion
  into that `ℂ^n|V` as a morphism of *analytic* spaces is
  `ComplexAnalytic.AnalyticSpace.ofCutOutHom` at the same datum and is not restated here, that
  declaration being in `Other/Oka/AnalyticSpace/CutOutProduct.lean`, which this file does not import and
  which importing would add 25 modules to an import closure of 42; the immersion of locally
  ringed spaces is `AlgebraicGeometry.LocallyRingedSpace.zeroLocusSubspaceι` composed with `i`,
  and it is what the cut-out datum below is stated about. **This bullet gave that file as being
  downstream of this one until 2026-09-07**, when the relation was measured and the two came out
  incomparable; *An import relation that was inferred rather than measured* says with what.
- `ComplexAnalytic.isLocalModel_zeroLocusSubspace_of_isCutOutBy`: the same conclusion as the
  property rather than as an object.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

variable {Z W Y : LocallyRingedSpace.{u}}

/-- **Composing cut-out data**: if `iW` cuts out `W` inside `Z` by `f₁`, and `j` cuts out `Y`
inside `W` by the pullbacks of `f₂` along `iW`, then `j ≫ iW` cuts out `Y` inside `Z` by `f₁`
together with `f₂`.

The converse of `ComplexAnalytic.IsCutOutBy.of_comp_append`, and the module docstring says what
each of the four conditions costs and where the two proofs part company. -/
theorem IsCutOutBy.comp_append {iW : W ⟶ Z} {j : Y ⟶ W} {k₁ k₂ : ℕ}
    {f₁ : Fin k₁ → Z.presheaf.obj (op ⊤)} {f₂ : Fin k₂ → Z.presheaf.obj (op ⊤)}
    (hW : IsCutOutBy iW f₁)
    (hY : IsCutOutBy j (fun r ↦ (LocallyRingedSpace.Γ.map iW.op).hom (f₂ r))) :
    IsCutOutBy (j ≫ iW) (Fin.append f₁ f₂) := by
  have hbase : ⇑(j ≫ iW).base = ⇑iW.base ∘ ⇑j.base := rfl
  have htrans (w : W) (s : Z.presheaf.obj (op ⊤)) :
      W.presheaf.Γgerm w ((LocallyRingedSpace.Γ.map iW.op).hom s) ∈
          IsLocalRing.maximalIdeal (W.presheaf.stalk w) ↔
        Z.presheaf.Γgerm (iW.base w) s ∈
          IsLocalRing.maximalIdeal (Z.presheaf.stalk (iW.base w)) := by
    rw [LocallyRingedSpace.Γgerm_Γ_map, IsLocalRing.mem_maximalIdeal,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      isUnit_map_iff (iW.stalkMap w).hom]
  have hsplit : ∀ y : Y, ((j ≫ iW).stalkMap y).hom =
      (j.stalkMap y).hom.comp (iW.stalkMap (j.base y)).hom := by
    intro y
    rw [LocallyRingedSpace.stalkMap_comp]
    rfl
  refine ⟨hbase ▸ hW.isClosedEmbedding.comp hY.isClosedEmbedding, ?_, fun y ↦ ?_, fun y ↦ ?_⟩
  · ext z
    simp only [hbase, Set.mem_range, Function.comp_apply, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, rfl⟩
      have hw : j.base y ∈ Set.range j.base := ⟨y, rfl⟩
      rw [hY.range_base] at hw
      intro jj
      refine Fin.addCases (motive := fun jj ↦
          Z.presheaf.Γgerm (iW.base (j.base y)) (Fin.append f₁ f₂ jj) ∈
            IsLocalRing.maximalIdeal (Z.presheaf.stalk (iW.base (j.base y))))
        (fun l ↦ ?_) (fun r ↦ ?_) jj
      · rw [Fin.append_left]
        have hmem : iW.base (j.base y) ∈ Set.range iW.base := ⟨j.base y, rfl⟩
        rw [hW.range_base] at hmem
        exact hmem l
      · rw [Fin.append_right]
        exact (htrans (j.base y) (f₂ r)).1 (hw r)
    · intro hz
      have hmem : z ∈ Set.range iW.base := by
        rw [hW.range_base]
        intro l
        exact Fin.append_left f₁ f₂ l ▸ hz (Fin.castAdd k₂ l)
      obtain ⟨w, rfl⟩ := hmem
      have hw : w ∈ Set.range j.base := by
        rw [hY.range_base]
        intro r
        exact (htrans w (f₂ r)).2 (Fin.append_right f₁ f₂ r ▸ hz (Fin.natAdd k₁ r))
      obtain ⟨y, rfl⟩ := hw
      exact ⟨y, rfl⟩
  · intro a
    obtain ⟨b, hb⟩ := hY.surjective_stalkMap y a
    obtain ⟨c, hc⟩ := hW.surjective_stalkMap (j.base y) b
    exact ⟨c, (DFunLike.congr_fun (hsplit y) c).trans
      ((congrArg (j.stalkMap y).hom hc).trans hb)⟩
  · have hφ : Function.Surjective (iW.stalkMap (j.base y)).hom :=
      hW.surjective_stalkMap (j.base y)
    have hgerm : ∀ r, W.presheaf.Γgerm (j.base y)
        ((LocallyRingedSpace.Γ.map iW.op).hom (f₂ r)) =
          (iW.stalkMap (j.base y)).hom
            (Z.presheaf.Γgerm (iW.base (j.base y)) (f₂ r)) :=
      fun r ↦ LocallyRingedSpace.Γgerm_Γ_map iW (f₂ r) (j.base y)
    have hset : (Set.range fun r ↦ W.presheaf.Γgerm (j.base y)
          ((LocallyRingedSpace.Γ.map iW.op).hom (f₂ r))) =
        ⇑(iW.stalkMap (j.base y)).hom ''
          (Set.range fun r ↦ Z.presheaf.Γgerm (iW.base (j.base y)) (f₂ r)) := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext hgerm)
    have hkerψ : RingHom.ker (j.stalkMap y).hom =
        Ideal.map (iW.stalkMap (j.base y)).hom
          (Ideal.span (Set.range fun r ↦
            Z.presheaf.Γgerm (iW.base (j.base y)) (f₂ r))) := by
      rw [hY.ker_stalkMap y, Ideal.map_span, hset]
    have hcomap : RingHom.ker ((j.stalkMap y).hom.comp (iW.stalkMap (j.base y)).hom) =
        Ideal.span (Set.range fun jj ↦
          Z.presheaf.Γgerm (iW.base (j.base y)) (Fin.append f₁ f₂ jj)) := by
      rw [← RingHom.comap_ker, hkerψ, Ideal.comap_map_of_surjective _ hφ,
        ← RingHom.ker_eq_comap_bot, hW.ker_stalkMap (j.base y), ← Ideal.span_union]
      congr 1
      rw [show (fun jj ↦ Z.presheaf.Γgerm (iW.base (j.base y)) (Fin.append f₁ f₂ jj)) =
          (fun s ↦ Z.presheaf.Γgerm (iW.base (j.base y)) s) ∘ Fin.append f₁ f₂ from rfl,
        Set.range_comp, Fin.range_append, Set.image_union, ← Set.range_comp, ← Set.range_comp]
      exact Set.union_comm _ _
    rw [hsplit y]
    exact hcomap

/-- **The composition at the family a caller holds.**

`ComplexAnalytic.IsCutOutBy.comp_append` concludes at a literal `Fin.append`, and a caller who
has to *state* the conclusion rarely wants one: the two blocks may arrive in the other order or
as a `Fin.snoc`. Since `ComplexAnalytic.IsCutOutBy` sees a family only through its range
(`ComplexAnalytic.IsCutOutBy.of_range_eq`), the set equation is the honest hypothesis, and this
is the same theorem stated at it. It is the mirror of
`ComplexAnalytic.IsCutOutBy.of_comp_of_range_eq`, which does this for the cancellation. -/
theorem IsCutOutBy.comp_of_range_eq {iW : W ⟶ Z} {j : Y ⟶ W} {k k₁ k₂ : ℕ}
    {f : Fin k → Z.presheaf.obj (op ⊤)} {f₁ : Fin k₁ → Z.presheaf.obj (op ⊤)}
    {f₂ : Fin k₂ → Z.presheaf.obj (op ⊤)} (hW : IsCutOutBy iW f₁)
    (hY : IsCutOutBy j (fun r ↦ (LocallyRingedSpace.Γ.map iW.op).hom (f₂ r)))
    (hf : Set.range f = Set.range f₁ ∪ Set.range f₂) : IsCutOutBy (j ≫ iW) f :=
  (hW.comp_append hY).of_range_eq (by rw [Fin.range_append, hf])

/-- **A cut-out subspace, cut down by the zero locus of the pullbacks of further ambient
sections, is cut out of the ambient space by the two families appended.**

`ComplexAnalytic.IsCutOutBy.comp_append` at
`AlgebraicGeometry.LocallyRingedSpace.isCutOutBy_zeroLocusSubspaceι`, which holds for an arbitrary
locally ringed space and an arbitrary finite family
(`Other/Oka/Geometry/RingedSpace/ZeroLocus.lean` discharges all four conditions once). So the inner
datum the composition asks for costs nothing to produce, and the object it is about is named
rather than hypothetical. -/
theorem IsCutOutBy.zeroLocusSubspaceι_comp {iW : W ⟶ Z} {k₁ k₂ : ℕ}
    {f₁ : Fin k₁ → Z.presheaf.obj (op ⊤)} (hW : IsCutOutBy iW f₁)
    (f₂ : Fin k₂ → Z.presheaf.obj (op ⊤)) :
    IsCutOutBy
      (W.zeroLocusSubspaceι (fun r ↦ (LocallyRingedSpace.Γ.map iW.op).hom (f₂ r)) ≫ iW)
      (Fin.append f₁ f₂) :=
  hW.comp_append (W.isCutOutBy_zeroLocusSubspaceι _)

variable {n k₁ k₂ : ℕ} {V : Opens (complexAffineSpace.{u} n)} {M : LocallyRingedSpace.{u}}
  {i : M ⟶ (complexAffineSpace.{u} n).restrict V.isOpenEmbedding}
  {f : Fin k₁ → ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤)}

/-- **A local model cut down by the pullbacks of further sections of its ambient `ℂ^n|V` is a
local model.**

`ComplexAnalytic.IsCutOutBy.zeroLocusSubspaceι_comp` presents the smaller space inside `ℂ^n|V`
itself, which is what `ComplexAnalytic.isLocalModel_of_isCutOutBy` asks for; presented inside the
larger local model it would say nothing, that predicate quantifying over immersions into an open
subspace of some `ℂ^n` and not over immersions into an arbitrary space. -/
theorem isLocalModel_zeroLocusSubspace_of_isCutOutBy (hcut : IsCutOutBy i f)
    (g : Fin k₂ → ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤)) :
    IsLocalModel (M.zeroLocusSubspace fun r ↦ (LocallyRingedSpace.Γ.map i.op).hom (g r)) :=
  isLocalModel_of_isCutOutBy (hcut.zeroLocusSubspaceι_comp g)

namespace AnalyticSpace

/-- **A local model cut down by the pullbacks of further sections of its ambient `ℂ^n|V`, as a
complex analytic space.**

`ComplexAnalytic.AnalyticSpace.ofCutOut` at
`ComplexAnalytic.IsCutOutBy.zeroLocusSubspaceι_comp`, so the `ℂ`-algebra structure is the one
pulled back along the composite immersion into `ℂ^n|V` and not along the immersion into the
larger local model. The two agree, that composite being the one immersion followed by the other,
but only the first is what `ComplexAnalytic.AnalyticSpace.ofCutOut` installs. -/
noncomputable def ofCutOutZeroLocus (hcut : IsCutOutBy i f)
    (g : Fin k₂ → ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤)) :
    AnalyticSpace.{u} :=
  AnalyticSpace.ofCutOut (hcut.zeroLocusSubspaceι_comp g)

/-- The underlying locally ringed space of
`ComplexAnalytic.AnalyticSpace.ofCutOutZeroLocus` is the zero locus it was built from, so a
caller may cross between the two levels without transporting anything. -/
lemma ofCutOutZeroLocus_toLocallyRingedSpace (hcut : IsCutOutBy i f)
    (g : Fin k₂ → ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op ⊤)) :
    (ofCutOutZeroLocus hcut g).toLocallyRingedSpace =
      M.zeroLocusSubspace fun r ↦ (LocallyRingedSpace.Γ.map i.op).hom (g r) :=
  rfl

end AnalyticSpace

end ComplexAnalytic

end
