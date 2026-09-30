/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.HolomorphicMapOpen
public import Other.Oka.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# `Hom(Z, ℂ^m) ≃ Γ(Z, 𝒪_Z)^m` for every complex analytic space

For a complex analytic space `Z` and a family of `m` global sections of `𝒪_Z`, a morphism of
complex analytic spaces `Z ⟶ ℂ^m` pulling the coordinates back to them:

```
ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_general
    (Z : AnalyticSpace) (g : ULift (Fin m) → Γ(Z, 𝒪_Z)) :
  ∃ φ : Z ⟶ ℂ^m, ∀ j, coordPullback φ j = g j
```

Uniqueness (`ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace`) has been `m`-fold and
general in `Z` since taxis #653, so this makes
`ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquivGeneral` a bijection
`Hom(Z, ℂ^m) ≃ Γ(Z, 𝒪_Z)^m` for an arbitrary complex analytic space ; taxis #610. Existence was
previously known `m`-fold only for `Z = ℂ^n`, and for a general `Z` only at `m = 1`.

## `ℂ^m` is not built as a product, and could not be

**Nothing here needs a product of complex analytic spaces, and nothing below uses one.** `ℂ^m`
is a concrete space and `ComplexAnalytic.AnalyticSpace.okaMapOpen` maps into it directly from a
family of holomorphic functions on an open subset of `ℂ^n`, so the `m` sections travel together
through one chart and one local morphism from beginning to end. The route that *would* need a
product ; take the `m` morphisms `Z ⟶ ℂ` that the `m = 1` statement gives and assemble them ; is
not taken. `ComplexAnalytic.nodeToLine_ne` is what makes that concrete: the node's two coordinate
functions give two different morphisms `node ⟶ ℂ`, and nothing below combines them into a
single morphism `node ⟶ ℂ²`.

**The heading says *could not be*, and the reason is circularity rather than absence.**
`Other/Oka/AnalyticSpace/AffineProduct.lean` reads a binary product off this file's bijection ;
`ComplexAnalytic.AnalyticSpace.isLimitBinaryFanAffineProd` makes `ℂ^(n+m)` the product of `ℂ^n`
and `ℂ^m`, and `ComplexAnalytic.AnalyticSpace.isTerminalComplexAffineSpaceZero` makes `ℂ^0`
terminal. That file imports this one, so the product is a consequence of the bijection below and
could not have been an ingredient of it. **This paragraph read *nothing in the development gives
products of complex analytic spaces* until that file landed**, and the sentence it is replaced by
is the one that was doing the work all along.

Consequently **`m` enters the proof in exactly two places**: the family version of the local
lift, and one `section_ext_of_cover` per coordinate in the gluing. Everything else ; the chart,
the cover, the `ℂ`-linearity, the compatibility on overlaps ; is independent of `m`.

## The `m = 1` statements

`exists_hom_complexLine_general`, `exists_hom_complexLine_of_local`,
`exists_hom_complexLine_restrict` and `homComplexLineEquivGeneral` all remain, and each is the
`m = 1` case of its `m`-fold sibling **instantiated rather than reproved**. They are kept rather
than deleted because the `m = 1` spelling ; one section, one equation, no index ; is what their
callers use, and because `homComplexLineEquivGeneral` is genuinely a different statement: it is
a bijection onto `Γ(Z, 𝒪_Z)`, not onto `ULift (Fin 1) → Γ(Z, 𝒪_Z)`. That is the choice taxis
#720 asked to be made explicitly; it extends the one taxis #655 made rather than reopening it.

## The three steps

1. **The chart step** ; `exists_chartLift`. Near each point, the whole family `g` consists of
   pullbacks of sections of `𝒪_{ℂ^n|V}` along **one** chart ; one chart for all `m`, which is
   what makes step 2 possible without a product. The chart comes from
   `AnalyticSpace.local_model` and does not depend on `g` at all; the sections from
   `AlgebraicGeometry.LocallyRingedSpace.exists_localLift_family`, which intersects the finitely
   many opens the single-section version returns, applied not to the chart `i` itself
   but to `i` **composed with the inclusion of its target into `ℂ^n`** ; which is what makes the
   lifted section live on an open of `ℂ^n` rather than on an open of `ℂ^n|V`. Taxis #709
   predicted three seams here; this removes one of them before it appears, and the two that
   remain are the ones listed below.
2. **The local morphism** ; `exists_local_hom_of_chartLift`: compose the chart with the morphism
   `ℂ^n|V ⟶ ℂ^m` that `exists_hom_complexAffineSpace_restrict` builds from those sections. That
   one is a single line, because `okaMapOpen` was `m`-fold already and only its *statement* was
   one-dimensional.
3. **The gluing** ; `exists_hom_complexAffineSpace_of_local`.

## What the gluing needs, and where each part comes from

* **The overlaps must be analytic spaces**, so that uniqueness applies to them. That is
  `ComplexAnalytic.AnalyticSpace.restrict` (taxis #664), and it is why
  `AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens` (taxis #693) rather
  than the pullback-form gluing is the theorem used: the categorical pullback of two open
  subspace inclusions is not an analytic space, so the compatibility hypothesis of the older
  lemma cannot be met by the tool meant to meet it.
* **The compatibility itself is uniqueness, not a computation.** Two local morphisms restricted
  to an overlap have the same `j`-th coordinate pullback there ; both are `g j` restricted ; so
  `ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` says they are equal. That is
  `ComplexAnalytic.AnalyticSpace.restrictLE_comp_eq`. **It is also why the two
  independence-of-choices arguments the original plan for this theorem called for are not
  needed**: uniqueness on an overlap replaces both. `AnalyticAt.dslope_comp` was built for one of
  them and is consequently unused; its disposition is recorded in the `## Status` section of
  `Other/Oka/Analytic/DividedDifference.lean` and should be read there rather than re-derived here.
* **The glued morphism must be recognised as a morphism of *analytic* spaces**, and its
  coordinate pullback must be recognised as `g`. Both are equalities of global sections that
  hold on each member of the cover, so both are
  `AlgebraicGeometry.LocallyRingedSpace.section_ext_of_cover`. `ℂ`-linearity is a condition on
  global sections only (`ComplexAnalytic.IsCLinearHom`), which is what makes this work.

## What the chart step needs, and the seam that made it hard

`exists_localLift` produces a section over an open subset `A` of the chart target and, in
general, over nothing larger. Two seams follow, and they are not symmetric.

* **The source open lives in `Z|U₀`, not in `Z`.** `X|U|W` and `X|W'`, for `W'` the image of `W`,
  are two open immersions into `X` with the same image, so `IsOpenImmersion.lift` produces the
  comparison morphism and `AlgebraicGeometry.LocallyRingedSpace.Γ_map_over_ambient` computes its
  action on sections. No isomorphism is needed ; only a morphism over `X`.
* **The chart's sheaf map has to be evaluated on a section that does not extend.**
  `ComplexAnalytic.restrictHom_fac` computes `Γ.map (restrictHom i A).op` only on sections pulled
  back from the global sections of the chart target, and `restrictHom` is an
  `IsOpenImmersion.lift`, so its sheaf map is not otherwise computable.
  `ComplexAnalytic.Γ_map_restrictHom_toRestrictΓ` is what closes this, entirely on stalks.

**Neither needed an equation of opens.** The obvious plan is to reach for
`U.isOpenEmbedding.isOpenMap.functor.obj ⊤ = U` and transport along it. Getting that equation is
not the difficulty ; it is `TopologicalSpace.Opens.isOpenEmbedding_obj_top`, a Mathlib `@[simp]`
lemma. **Transporting along it is**, and it is never necessary:
`TopCat.Presheaf.germ_res_apply` moves a germ across a `≤`, and the two
inequalities one needs ; `functor.obj O ≤ U` and `O ≤ (Opens.map ι).obj (functor.obj O)` ; are
the `.le` of that same `@[simp]` lemma and the unit of `IsOpenMap.adjunction`. Every predicted
transport evaporates.

The equation is nonetheless not *definitional*, even at `⊤` and even over `ℂ^n` ; taxis #702 ;
so a transport really would have to be carried, not discharged by `rfl`. Both facts are needed
to see why the `≤` route is the cheap one.

## Main results

- `ComplexAnalytic.AnalyticSpace.restrictLE_comp_eq`: **two local morphisms to `ℂ^m` with the
  same coordinate pullbacks agree on the overlap.**
- `ComplexAnalytic.AnalyticSpace.coordPullback_ofRestrict_comp`: restricting a global morphism
  to `ℂ^m` supplies the local data, with the sections restricted along.
- `ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_of_local`: **a family of global
  sections which is locally a tuple of coordinate pullbacks is globally one**, and
  `ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_of_local` at `m = 1`.
- `ComplexAnalytic.AnalyticSpace.exists_local_hom_of_chartLift`: a chart on which the whole
  family lifts supplies the local morphism.
- `ComplexAnalytic.AnalyticSpace.exists_chartLift`: **near each point, a family of global
  sections of `𝒪_Z` consists of pullbacks of sections of `𝒪_{ℂ^n|V}` along one chart.**
- `ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_general`: **every family of `m`
  global sections of `𝒪_Z` is the tuple of coordinate pullbacks along a morphism `Z ⟶ ℂ^m`**,
  and `ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_general` at `m = 1`.
- `ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquivGeneral`:
  **`Hom(Z, ℂ^m) ≃ Γ(Z, 𝒪_Z)^m`**, with
  `ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquiv_eq` identifying it at `Z = ℂ^n` with
  the `ℂ^n` bijection that already existed.
- `ComplexAnalytic.AnalyticSpace.homComplexLineEquivGeneral`: **`Hom(Z, ℂ) ≃ Γ(Z, 𝒪_Z)`**. Not
  an instance of the previous one ; its target is `Γ(Z, 𝒪_Z)` rather than
  `ULift (Fin 1) → Γ(Z, 𝒪_Z)` ; but its surjectivity is.
- `ComplexAnalytic.AnalyticSpace.symm_homComplexAffineSpaceEquivGeneral_coordPullback` and
  `ComplexAnalytic.AnalyticSpace.coordPullback_symm_homComplexAffineSpaceEquivGeneral`, and the
  same pair for the `m = 1` bijection: **both round trips**, which is what makes the choice term
  in each inverse harmless to a consumer.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

noncomputable section

namespace ComplexAnalytic.AnalyticSpace

/-- **Restricting a local morphism to a smaller open subspace restricts its coordinate
pullback.** -/
theorem coordPullback_restrictLE_comp (Z : AnalyticSpace.{u}) {m : ℕ}
    (g : Z.presheaf.obj (op ⊤)) {V W : Z.Opens} (h : V ≤ W)
    (ψ : Z.restrict W ⟶ AnalyticSpace.complexAffineSpace.{u} m) (j : ULift.{u} (Fin m))
    (hψ : AnalyticSpace.coordPullback ψ j = Z.resΓ W g) :
    AnalyticSpace.coordPullback (Z.restrictLE h ≫ ψ) j = Z.resΓ V g :=
  (AnalyticSpace.coordPullback_comp (Z.restrictLE h) ψ j).trans
    ((congrArg (fun a ↦ (LocallyRingedSpace.Γ.map
        (Z.toLocallyRingedSpace.restrictLE h).op).hom a) hψ).trans (Z.resΓ_restrictLE h g))

/-- **Restricting a global morphism to `ℂ^m` supplies the local data**, with the local sections
being the restrictions of the global ones.

This is `ComplexAnalytic.AnalyticSpace.coordPullback_comp` for the inclusion of an open
subspace, and it is what makes the hypothesis of
`ComplexAnalytic.AnalyticSpace.exists_hom_complexLine_of_local` satisfiable at any cover of a
`Z` for which the conclusion is already known ; which is how the assembly is tested. -/
theorem coordPullback_ofRestrict_comp (Z : AnalyticSpace.{u}) {m : ℕ} (U : Z.Opens)
    (φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} m) (j : ULift.{u} (Fin m)) :
    AnalyticSpace.coordPullback (Z.ofRestrict U ≫ φ) j =
      Z.resΓ U (AnalyticSpace.coordPullback φ j) :=
  AnalyticSpace.coordPullback_comp (Z.ofRestrict U) φ j

/-- **Two local morphisms to `ℂ^m` whose coordinate pullbacks are the restrictions of one
global family of sections agree on the overlap.**

This is the compatibility hypothesis of
`AlgebraicGeometry.LocallyRingedSpace.existsUnique_glueMorphisms_of_opens`, and it is discharged
by *uniqueness*: both restricted morphisms pull the `j`-th coordinate back to `g j` restricted to
`V ⊓ W`, and `ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace` applies because
`Z|(V ⊓ W)` is an analytic space. No agreement of the two morphisms is assumed and none is
computed. -/
theorem restrictLE_comp_eq (Z : AnalyticSpace.{u}) {m : ℕ}
    (g : ULift.{u} (Fin m) → Z.presheaf.obj (op ⊤))
    {V W : Z.Opens} (ψV : Z.restrict V ⟶ AnalyticSpace.complexAffineSpace.{u} m)
    (ψW : Z.restrict W ⟶ AnalyticSpace.complexAffineSpace.{u} m)
    (hV : ∀ j, AnalyticSpace.coordPullback ψV j = Z.resΓ V (g j))
    (hW : ∀ j, AnalyticSpace.coordPullback ψW j = Z.resΓ W (g j)) :
    Z.restrictLE (inf_le_left : V ⊓ W ≤ V) ≫ ψV =
      Z.restrictLE (inf_le_right : V ⊓ W ≤ W) ≫ ψW :=
  AnalyticSpace.hom_ext_complexAffineSpace _ _ fun j ↦
    (Z.coordPullback_restrictLE_comp (g j) inf_le_left ψV j (hV j)).trans
      (Z.coordPullback_restrictLE_comp (g j) inf_le_right ψW j (hW j)).symm

/-- **A family of `m` global sections of `𝒪_Z` which is locally the tuple of coordinate
pullbacks of a morphism to `ℂ^m` is globally one.**

The cover is indexed by the points of `Z`, each point contributing the neighbourhood the
hypothesis supplies for it; that is a `Type u` because the carrier is, which is what
`existsUnique_glueMorphisms_of_opens` requires of its index type.

The glued morphism arrives as a morphism of *locally ringed* spaces. Both remaining obligations
; that it is `ℂ`-linear, and that its `j`-th coordinate pullback is `g j` ; are equalities of
global sections which hold after restriction to each member of the cover, so both are
`AlgebraicGeometry.LocallyRingedSpace.section_ext_of_cover`. `ℂ`-linearity being a condition on
global sections *only* is what makes the first of those an instance of the second, and is also
why it does not have to be reproved per coordinate: **`m` enters this proof in exactly one
place**, the second `section_ext_of_cover`, which is now run once for each `j`. -/
theorem exists_hom_complexAffineSpace_of_local (Z : AnalyticSpace.{u}) {m : ℕ}
    (g : ULift.{u} (Fin m) → Z.presheaf.obj (op ⊤))
    (hloc : ∀ z : Z, ∃ (U : Z.Opens) (_ : z ∈ U)
      (ψ : Z.restrict U ⟶ AnalyticSpace.complexAffineSpace.{u} m),
      ∀ j, AnalyticSpace.coordPullback ψ j = Z.resΓ U (g j)) :
    ∃ φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} m,
      ∀ j, AnalyticSpace.coordPullback φ j = g j := by
  choose U hzU ψ hψ using hloc
  have hcover : ∀ x : Z.toLocallyRingedSpace, ∃ i, x ∈ U i := fun x ↦ ⟨x, hzU x⟩
  obtain ⟨φ₀, hφ₀, -⟩ := LocallyRingedSpace.existsUnique_glueMorphisms_of_opens U hcover
    (fun i ↦ (ψ i).toLRSHom) fun i j ↦ congrArg
      (fun χ : Z.restrict (U i ⊓ U j) ⟶ AnalyticSpace.complexAffineSpace.{u} m ↦ χ.toLRSHom)
      (Z.restrictLE_comp_eq g (ψ i) (ψ j) (hψ i) (hψ j))
  -- pulling a section back along `φ₀` and restricting to `U i` is pulling it back along `ψ i`
  have key : ∀ (i : Z) (a : (AnalyticSpace.complexAffineSpace.{u} m).presheaf.obj (op ⊤)),
      (LocallyRingedSpace.Γ.map
          (Z.toLocallyRingedSpace.ofRestrict (U i).isOpenEmbedding).op).hom
            ((LocallyRingedSpace.Γ.map φ₀.op).hom a) =
        (LocallyRingedSpace.Γ.map (ψ i).toLRSHom.op).hom a := fun i a ↦
    (LocallyRingedSpace.Γ_map_comp_apply _ φ₀ a).symm.trans
      (congrArg (fun n : Z.toLocallyRingedSpace.restrict (U i).isOpenEmbedding ⟶
          (AnalyticSpace.complexAffineSpace.{u} m).toLocallyRingedSpace ↦
        (LocallyRingedSpace.Γ.map n.op).hom a) (hφ₀ i))
  have hclin : IsCLinearHom φ₀ Z.algebraMap
      (AnalyticSpace.complexAffineSpace.{u} m).algebraMap := fun c ↦
    LocallyRingedSpace.section_ext_of_cover Z.toLocallyRingedSpace U hcover _ _ fun i ↦
      (key i _).trans (((ψ i).isCLinear c).trans
        (isCLinearHom_ofRestrict Z.toLocallyRingedSpace Z.algebraMap (U i) c).symm)
  exact ⟨⟨φ₀, hclin⟩, fun j ↦
    LocallyRingedSpace.section_ext_of_cover Z.toLocallyRingedSpace U hcover _ _ fun i ↦
      (key i _).trans (hψ i j)⟩

/-- **A global section of `𝒪_Z` which is locally the coordinate pullback of a morphism to `ℂ` is
globally one.**

The `m = 1` case of
`ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_of_local`, instantiated rather than
reproved. It is kept under its own name because the `m = 1` spelling ; one section, one
equation, no index ; is what its callers and every statement about it use. -/
theorem exists_hom_complexLine_of_local (Z : AnalyticSpace.{u}) (g : Z.presheaf.obj (op ⊤))
    (hloc : ∀ z : Z, ∃ (U : Z.Opens) (_ : z ∈ U)
      (ψ : Z.restrict U ⟶ AnalyticSpace.complexAffineSpace.{u} 1),
      AnalyticSpace.coordPullback ψ (ULift.up 0) = Z.resΓ U g) :
    ∃ φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} 1,
      AnalyticSpace.coordPullback φ (ULift.up 0) = g :=
  let ⟨φ, hφ⟩ := Z.exists_hom_complexAffineSpace_of_local (m := 1) (fun _ ↦ g) fun z ↦
    let ⟨U, hzU, ψ, hψ⟩ := hloc z
    ⟨U, hzU, ψ, fun j ↦ by rw [Subsingleton.elim j (ULift.up 0)]; exact hψ⟩
  ⟨φ, hφ (ULift.up 0)⟩

/-- **A chart on which the whole family lifts supplies the local morphism.**

Composing the chart with the morphism `ℂ^n|V ⟶ ℂ^m` that
`ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_restrict` builds from `s`, and
using naturality of `ComplexAnalytic.AnalyticSpace.coordPullback`, gives the hypothesis of
`ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_of_local` at that point. Nothing
about `c` is used beyond its being a morphism of analytic spaces ; it need not be a closed
immersion, and no cut-out data enters.

**One chart carries all `m` sections**, which is the whole reason
`ComplexAnalytic.AnalyticSpace.exists_chartLift` is stated for a family rather than applied `m`
times: `m` separate charts could not be composed into a single morphism to `ℂ^m` without a
product of analytic spaces, and no product is available to this file, which is upstream of
`Other/Oka/AnalyticSpace/AffineProduct.lean`. -/
theorem exists_local_hom_of_chartLift (Z : AnalyticSpace.{u}) {m : ℕ}
    (g : ULift.{u} (Fin m) → Z.presheaf.obj (op ⊤))
    {W : Z.Opens} {n : ℕ} {V : TopologicalSpace.Opens (complexAffineSpace.{u} n)}
    (c : Z.restrict W ⟶ (AnalyticSpace.complexAffineSpace.{u} n).restrict V)
    (s : ULift.{u} (Fin m) →
      ((AnalyticSpace.complexAffineSpace.{u} n).restrict V).presheaf.obj (op ⊤))
    (hs : ∀ j, (LocallyRingedSpace.Γ.map c.toLRSHom.op).hom (s j) = Z.resΓ W (g j)) :
    ∃ ψ : Z.restrict W ⟶ AnalyticSpace.complexAffineSpace.{u} m,
      ∀ j, AnalyticSpace.coordPullback ψ j = Z.resΓ W (g j) := by
  obtain ⟨φ, hφ⟩ := AnalyticSpace.exists_hom_complexAffineSpace_restrict s
  exact ⟨c ≫ φ, fun j ↦ ((AnalyticSpace.coordPullback_comp c φ j).trans
    (congrArg (fun a ↦ (LocallyRingedSpace.Γ.map c.toLRSHom.op).hom a) (hφ j))).trans (hs j)⟩

/-- **Near each point, a global section of `𝒪_Z` is the pullback of a section of `𝒪_{ℂ^n|V}`
along a chart.**

Nothing is claimed about the chart beyond its being a morphism of analytic spaces: it need not
be a closed immersion, and no cut-out data appears in the statement. `IsCutOutBy` is used only
inside the proof, for the stalk-surjectivity that `exists_localLift` needs.

**The chart is composed with the inclusion of its target into `ℂ^n` before the lift is taken.**
That is the one design choice that matters: `exists_localLift` then produces its section over an
open of `ℂ^n` rather than over an open of `ℂ^n|V`, so the chart target of the conclusion can be
that open itself and no comparison of `ℂ^n|V|A` with `ℂ^n|A'` is ever needed. The composite is
still surjective on stalks, because the inclusion of an open subspace is an isomorphism on
stalks. -/
theorem exists_chartLift (Z : AnalyticSpace.{u}) {m : ℕ}
    (g : ULift.{u} (Fin m) → Z.presheaf.obj (op ⊤)) (z : Z) :
    ∃ (W : Z.Opens) (_ : z ∈ W) (n : ℕ)
      (V : TopologicalSpace.Opens (_root_.complexAffineSpace.{u} n))
      (c : Z.restrict W ⟶ (ComplexAnalytic.AnalyticSpace.complexAffineSpace.{u} n).restrict V)
      (s : ULift.{u} (Fin m) →
        ((ComplexAnalytic.AnalyticSpace.complexAffineSpace.{u} n).restrict V).presheaf.obj
          (op ⊤)),
      ∀ j, (LocallyRingedSpace.Γ.map c.toLRSHom.op).hom (s j) = Z.resΓ W (g j) := by
  obtain ⟨U₀, n, k, V, i, f, hcut, hlin⟩ := Z.local_model z
  have hsurj : ∀ x : Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding,
      Function.Surjective
        (((i ≫ (_root_.complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding).stalkMap x).hom) :=
      fun x c ↦ by
    obtain ⟨b, rfl⟩ := hcut.surjective_stalkMap x c
    obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (((_root_.complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding).stalkMap
        (i.base x))).surjective b
    refine ⟨a, ?_⟩
    rw [LocallyRingedSpace.stalkMap_comp]
    exact ConcreteCategory.comp_apply _ _ a
  obtain ⟨A, hA, u, B', hB'top, hB'A, hxB', heq⟩ :=
    LocallyRingedSpace.exists_localLift_family
      (i ≫ (_root_.complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding) hsurj (B₀ := ⊤)
      (fun j : Fin m ↦ Z.resΓ U₀.1 (g (ULift.up j)))
      (⟨z, U₀.2⟩ : Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding) trivial
  have hW : U₀.1.isOpenEmbedding.isOpenMap.functor.obj B' ≤
      U₀.1.isOpenEmbedding.isOpenMap.functor.obj
        ((Opens.map (i ≫ (_root_.complexAffineSpace.{u} n).ofRestrict
          V.isOpenEmbedding).base).obj A) :=
    (U₀.1.isOpenEmbedding.isOpenMap.functor.map (homOfLE hB'A)).le
  have hr1 := LocallyRingedSpace.range_ofRestrict Z.toLocallyRingedSpace
    (U₀.1.isOpenEmbedding.isOpenMap.functor.obj B')
  have hr2 := LocallyRingedSpace.range_ofRestrict_comp Z.toLocallyRingedSpace U₀.1
    ((Opens.map (i ≫ (_root_.complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding).base).obj A)
  have hrange : Set.range ((Z.toLocallyRingedSpace.ofRestrict
        (U₀.1.isOpenEmbedding.isOpenMap.functor.obj B').isOpenEmbedding).base) ⊆
      Set.range (((Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).ofRestrict
        ((Opens.map (i ≫ (_root_.complexAffineSpace.{u} n).ofRestrict
          V.isOpenEmbedding).base).obj A).isOpenEmbedding ≫
        Z.toLocallyRingedSpace.ofRestrict U₀.1.isOpenEmbedding).base) :=
    (hr1.subset.trans hW).trans hr2.symm.subset
  refine ⟨U₀.1.isOpenEmbedding.isOpenMap.functor.obj B',
    ⟨⟨z, U₀.2⟩, hxB', rfl⟩, n, A,
    ⟨LocallyRingedSpace.IsOpenImmersion.lift _ _ hrange ≫
      -- Qualified: inside `namespace AnalyticSpace` the bare name resolves to
      -- `ComplexAnalytic.AnalyticSpace.restrictHom`, which is the analytic-space one.
      ComplexAnalytic.restrictHom
        (i ≫ (_root_.complexAffineSpace.{u} n).ofRestrict V.isOpenEmbedding) A, ?_⟩,
    fun j ↦ (_root_.complexAffineSpace.{u} n).toRestrictΓ A (u j.down), ?_⟩
  · exact IsCLinearHom.of_comp (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hrange)
      (isCLinearHom_ofRestrict Z.toLocallyRingedSpace Z.algebraMap _)
      ((isCLinearHom_ofRestrict (Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding) _ _).comp
        (isCLinearHom_ofRestrict Z.toLocallyRingedSpace Z.algebraMap U₀.1))
      |>.comp (isCLinearHom_restrictHom (hlin.comp (isCLinearHom_ofRestrict_constants n V)) A)
  · intro j
    refine Eq.trans (LocallyRingedSpace.Γ_map_comp_apply _ _ _) ?_
    refine Eq.trans (congrArg
      (fun b ↦ (LocallyRingedSpace.Γ.map
        (LocallyRingedSpace.IsOpenImmersion.lift _ _ hrange).op).hom b)
      (Γ_map_restrictHom_toRestrictΓ _ A (u j.down))) ?_
    refine Eq.trans (LocallyRingedSpace.Γ_map_over_ambient Z.toLocallyRingedSpace U₀.1 _ _ hW _
      (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hrange) _) ?_
    refine Eq.trans (congrArg (Z.toLocallyRingedSpace.toRestrictΓ
        (U₀.1.isOpenEmbedding.isOpenMap.functor.obj B'))
      (LocallyRingedSpace.restrict_map_apply Z.toLocallyRingedSpace U₀.1 hB'A hW _).symm) ?_
    refine Eq.trans (congrArg (Z.toLocallyRingedSpace.toRestrictΓ
        (U₀.1.isOpenEmbedding.isOpenMap.functor.obj B')) (heq j.down)) ?_
    refine Eq.trans (congrArg (Z.toLocallyRingedSpace.toRestrictΓ
        (U₀.1.isOpenEmbedding.isOpenMap.functor.obj B'))
      (LocallyRingedSpace.restrict_map_apply Z.toLocallyRingedSpace U₀.1 hB'top
        (U₀.1.isOpenEmbedding.isOpenMap.functor.map (homOfLE hB'top)).le _)) ?_
    refine Eq.trans (congrArg (Z.toLocallyRingedSpace.toRestrictΓ
        (U₀.1.isOpenEmbedding.isOpenMap.functor.obj B'))
      (congrArg (fun b ↦ (Z.toLocallyRingedSpace.presheaf.map
          (homOfLE (U₀.1.isOpenEmbedding.isOpenMap.functor.map (homOfLE hB'top)).le).op).hom b)
        (LocallyRingedSpace.Γ_map_ofRestrict_apply Z.toLocallyRingedSpace U₀.1 (g j)))) ?_
    refine Eq.trans (congrArg (Z.toLocallyRingedSpace.toRestrictΓ
        (U₀.1.isOpenEmbedding.isOpenMap.functor.obj B'))
      (LocallyRingedSpace.map_map_apply Z.toLocallyRingedSpace _ le_top le_top (g j))) ?_
    exact (LocallyRingedSpace.map_map_apply Z.toLocallyRingedSpace _ le_top le_top (g j)).trans
      (LocallyRingedSpace.Γ_map_ofRestrict_apply Z.toLocallyRingedSpace _ (g j)).symm

/-- **Every family of `m` global sections of `𝒪_Z` is the tuple of coordinate pullbacks along a
morphism of complex analytic spaces `Z ⟶ ℂ^m`, for every complex analytic space `Z`.**

This is the existence half of taxis #610, and the last of it that was open.

Note what does *not* appear in the proof: any product of analytic spaces. `ℂ^m` is a concrete
space and `ComplexAnalytic.AnalyticSpace.okaMapOpen` maps into it directly from a family of
holomorphic functions, so the `m` sections are carried by one chart and one local morphism
throughout. Assembling `m` separate morphisms `Z ⟶ ℂ` into one `Z ⟶ ℂ^m` would need a product,
and the product that `Other/Oka/AnalyticSpace/AffineProduct.lean` builds is built out of this theorem
rather than the other way round. -/
theorem exists_hom_complexAffineSpace_general (Z : AnalyticSpace.{u}) {m : ℕ}
    (g : ULift.{u} (Fin m) → Z.presheaf.obj (op ⊤)) :
    ∃ φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} m,
      ∀ j, AnalyticSpace.coordPullback φ j = g j :=
  exists_hom_complexAffineSpace_of_local Z g fun z ↦ by
    obtain ⟨W, hzW, n, V, c, s, hs⟩ := exists_chartLift Z g z
    obtain ⟨ψ, hψ⟩ := exists_local_hom_of_chartLift Z g c s hs
    exact ⟨W, hzW, ψ, hψ⟩

/-- **Every global section of `𝒪_Z` is the pullback of the coordinate along a morphism of complex
analytic spaces `Z ⟶ ℂ`, for every complex analytic space `Z`.**

This is the existence half of taxis #628. It is the `m = 1` case of
`ComplexAnalytic.AnalyticSpace.exists_hom_complexAffineSpace_general`, instantiated rather than
reproved, and kept under its own name because the `m = 1` spelling is what its callers use. -/
theorem exists_hom_complexLine_general (Z : AnalyticSpace.{u}) (g : Z.presheaf.obj (op ⊤)) :
    ∃ φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} 1,
      AnalyticSpace.coordPullback φ (ULift.up 0) = g :=
  let ⟨φ, hφ⟩ := Z.exists_hom_complexAffineSpace_general (m := 1) fun _ ↦ g
  ⟨φ, hφ (ULift.up 0)⟩

/-- **`Hom(Z, ℂ) ≃ Γ(Z, 𝒪_Z)` for every complex analytic space `Z`**, the correspondence being
the pullback of the coordinate.

Injectivity is `ComplexAnalytic.AnalyticSpace.hom_ext_complexLine`, which has been general in `Z`
since taxis #653; surjectivity is `exists_hom_complexLine_general`.

**This is the only bijection of this shape in the development.** There were briefly three ; one
for `ℂ^n`, one for `ℂ^n|V`, and this one ; with the same forward map at three sources; the first
two are subsumed by this at `Z = ℂ^n` and `Z = ℂ^n|V` and were deleted rather than kept in
parallel (taxis #655). Their *existence* halves, `exists_hom_complexLine` and
`exists_hom_complexLine_restrict`, are not redundant and remain: the second is what
`exists_local_hom_of_chartLift` consumes, so the general case is built on the special one rather
than replacing it.

This is `Equiv.ofBijective`, so **its inverse is a choice term**. The forward map is
`ComplexAnalytic.AnalyticSpace.coordPullback` and is the thing to state results about; the two
lemmas below say what the inverse does without unfolding the choice, and that is what a consumer
needs. -/
noncomputable def homComplexLineEquivGeneral (Z : AnalyticSpace.{u}) :
    (Z ⟶ AnalyticSpace.complexAffineSpace.{u} 1) ≃ Z.presheaf.obj (op ⊤) :=
  Equiv.ofBijective (fun φ ↦ AnalyticSpace.coordPullback φ (ULift.up 0))
    ⟨fun _ _ h ↦ AnalyticSpace.hom_ext_complexLine _ _ h, exists_hom_complexLine_general Z⟩

/-- `ComplexAnalytic.AnalyticSpace.homComplexLineEquivGeneral` is the pullback of the
coordinate. -/
@[simp]
lemma homComplexLineEquivGeneral_apply (Z : AnalyticSpace.{u})
    (φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} 1) :
    homComplexLineEquivGeneral Z φ = AnalyticSpace.coordPullback φ (ULift.up 0) :=
  rfl

/-- **The inverse of `ComplexAnalytic.AnalyticSpace.homComplexLineEquivGeneral` recovers the
morphism a coordinate pullback came from**, with no choice left in it.

The inverse is a choice term, so a consumer who has to unfold `Equiv.ofBijective` has been handed
nothing. This is the half that says the choice is pinned on the image. -/
@[simp]
lemma symm_homComplexLineEquivGeneral_coordPullback (Z : AnalyticSpace.{u})
    (φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} 1) :
    (homComplexLineEquivGeneral Z).symm (AnalyticSpace.coordPullback φ (ULift.up 0)) = φ :=
  (homComplexLineEquivGeneral Z).symm_apply_apply φ

/-- **The morphism attached to a section does pull the coordinate back to that section.**

This is the other round trip, and it is the one an existence argument uses: it says
`(homComplexLineEquivGeneral Z).symm g` is a morphism with a named coordinate pullback rather
than an opaque choice. Together with
`ComplexAnalytic.AnalyticSpace.base_eq_eval_coordPullback` it makes that morphism computable on
points. -/
@[simp]
lemma coordPullback_symm_homComplexLineEquivGeneral (Z : AnalyticSpace.{u})
    (g : Z.presheaf.obj (op ⊤)) :
    AnalyticSpace.coordPullback ((homComplexLineEquivGeneral Z).symm g) (ULift.up 0) = g :=
  (homComplexLineEquivGeneral Z).apply_symm_apply g

/-- **`Hom(Z, ℂ^m) ≃ Γ(Z, 𝒪_Z)^m`**: a morphism of complex analytic spaces from `Z` to `ℂ^m` is
the same thing as an `m`-tuple of global holomorphic functions on `Z`, the correspondence being
the tuple of pullbacks of the coordinates.

Injectivity is `ComplexAnalytic.AnalyticSpace.hom_ext_complexAffineSpace`, which has been
`m`-fold and general in `Z` since taxis #653; surjectivity is
`exists_hom_complexAffineSpace_general`.

**This is taxis #610 and it subsumes `ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquiv`**,
which is this at `Z = ℂ^n` ; see `ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquiv_eq`.
It does **not** subsume `ComplexAnalytic.AnalyticSpace.homComplexLineEquivGeneral`, which is a
bijection onto `Γ(Z, 𝒪_Z)` rather than onto `ULift (Fin 1) → Γ(Z, 𝒪_Z)`: the two have different
targets and the `m = 1` spelling is the one callers want.

This is `Equiv.ofBijective`, so **its inverse is a choice term**. The forward map is
`ComplexAnalytic.AnalyticSpace.coordPullback` and is the thing to state results about; the two
lemmas below say what the inverse does without unfolding the choice. -/
noncomputable def homComplexAffineSpaceEquivGeneral (Z : AnalyticSpace.{u}) (m : ℕ) :
    (Z ⟶ AnalyticSpace.complexAffineSpace.{u} m) ≃
      (ULift.{u} (Fin m) → Z.presheaf.obj (op ⊤)) :=
  Equiv.ofBijective AnalyticSpace.coordPullback
    ⟨fun _ _ h ↦ AnalyticSpace.hom_ext_complexAffineSpace _ _ (congrFun h),
      fun g ↦ (exists_hom_complexAffineSpace_general Z g).imp fun _ h ↦ funext h⟩

/-- `ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquivGeneral` is the tuple of pullbacks
of the coordinates, applied to an argument. -/
@[simp]
lemma homComplexAffineSpaceEquivGeneral_apply (Z : AnalyticSpace.{u}) {m : ℕ}
    (φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} m) :
    homComplexAffineSpaceEquivGeneral Z m φ = AnalyticSpace.coordPullback φ :=
  rfl

/-- **The inverse of `ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquivGeneral` recovers
the morphism a tuple of coordinate pullbacks came from**, with no choice left in it. -/
@[simp]
lemma symm_homComplexAffineSpaceEquivGeneral_coordPullback (Z : AnalyticSpace.{u}) {m : ℕ}
    (φ : Z ⟶ AnalyticSpace.complexAffineSpace.{u} m) :
    (homComplexAffineSpaceEquivGeneral Z m).symm (AnalyticSpace.coordPullback φ) = φ :=
  (homComplexAffineSpaceEquivGeneral Z m).symm_apply_apply φ

/-- **The morphism attached to a tuple of sections does pull the coordinates back to that
tuple.**

This is the other round trip, and it is the one an existence argument uses: it says
`(homComplexAffineSpaceEquivGeneral Z m).symm g` is a morphism with named coordinate pullbacks
rather than an opaque choice. -/
@[simp]
lemma coordPullback_symm_homComplexAffineSpaceEquivGeneral (Z : AnalyticSpace.{u}) {m : ℕ}
    (g : ULift.{u} (Fin m) → Z.presheaf.obj (op ⊤)) :
    AnalyticSpace.coordPullback ((homComplexAffineSpaceEquivGeneral Z m).symm g) = g :=
  (homComplexAffineSpaceEquivGeneral Z m).apply_symm_apply g

/-- The `ℂ^n` bijection `ComplexAnalytic.AnalyticSpace.homComplexAffineSpaceEquiv` is the
general one at `Z = ℂ^n`.

Both are `Equiv.ofBijective` of the same forward map, so this is `rfl` on the function and
`Equiv.ext` on the bijection. It is stated rather than either declaration being deleted:
`homComplexAffineSpaceEquiv`'s inverse is named on `okaMap` in
`Other/Oka/AnalyticSpace/HomToComplex.lean`, which is a computation about `ℂ^n` that the general
statement does not make, and that file is upstream of this one. -/
theorem homComplexAffineSpaceEquiv_eq (n m : ℕ) :
    homComplexAffineSpaceEquiv.{u} n m =
      homComplexAffineSpaceEquivGeneral.{u} (AnalyticSpace.complexAffineSpace.{u} n) m :=
  Equiv.ext fun _ ↦ rfl

end ComplexAnalytic.AnalyticSpace

end

end
