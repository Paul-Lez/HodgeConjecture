/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.Evaluation

/-!
# The value of a section of the structure sheaf is continuous in the point

`Other/Oka/AnalyticSpace/Evaluation.lean` makes a section `g` of `𝒪_Z` over an open `U` of a complex
analytic space into a function `U → ℂ`, by evaluating in the residue field. This file proves
that function is **continuous**:

```
ComplexAnalytic.AnalyticSpace.continuous_eval :
    Continuous fun z : U ↦ Z.eval z.1 z.2 g
```

Continuity is not formal. `AnalyticSpace.eval` is defined one point at a time ; the value at `z`
is read off from the local ring `𝒪_{Z,z}` and its maximal ideal ; and nothing in that definition
relates the values at two different points. What relates them is the existence of a chart: a
chart turns a section into a holomorphic function on an open subset of `ℂ^n`, and the values of
a holomorphic function do vary continuously.

## The argument

Continuity is local, so fix `z₀ ∈ U` and take a chart at it: an open `U₀ ∋ z₀` and a closed
immersion `i : Z|U₀ ⟶ ℂ^n|V` cutting `Z|U₀` out, which is `ℂ`-linear. Since `i` is surjective on
stalks, `AlgebraicGeometry.LocallyRingedSpace.exists_localLift` gives a neighbourhood `B'` of
`z₀` in the chart, an open `A ⊆ V` and a *holomorphic function* `u` on `A` whose pullback along
`i` agrees with `g` on `B'`. On `B'` the value of `g` is then the value of `u`
(`ComplexAnalytic.evalStalk_chart`), which is continuous in the point because `u` is holomorphic
; that is `OkaRing.continuous_evalHom`, and it is the only step of the argument that is
analysis rather than bookkeeping.

The step that carries the weight is `ComplexAnalytic.evalStalk_chart`, and the way it is proved
is worth recording: **not** by chaining the `IsLocalRing.IsCoefficientField.evalHom_map`
transports that build `AnalyticSpace.evalStalk` in the first place, but by using that
`evalStalk` is *characterised* by `AnalyticSpace.evalStalk_eq_iff` ; `evalStalk z a = c` exactly
when `a - c` lies in the maximal ideal. The chart map sends the maximal ideal at a point of
`ℂ^n|V` into the maximal ideal at the corresponding point of `Z`, because it is a composite of
isomorphisms with `i.stalkMap`, which is a local homomorphism; that is the whole proof, and it
needs no compatibility of the two `IsCoefficientField` structures.

## Main results

- `ComplexAnalytic.AnalyticSpace.continuous_eval`: **the value of a section of `𝒪_Z` over `U`
  is a continuous function on `U`.**
- `ComplexAnalytic.AnalyticSpace.continuous_eval_top`: the same for a global section, as a
  function on `Z`.
- `ComplexAnalytic.evalStalk_chart`: on a chart, the value of the pullback of a holomorphic
  function is the value of that function.

## References

- [Hans Grauert and Reinhold Remmert, *Coherent analytic sheaves*][grauert-remmert1984], §A
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry IsLocalRing

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ComplexAnalytic

section Chart

variable {n : ℕ} (V : Opens (complexAffineSpace.{u} n))

/-- **The germ of a section of an open subspace of `ℂ^n` lies in the maximal ideal of its stalk
exactly when the corresponding holomorphic function vanishes at the point.**

This is `germ_mem_maximalIdeal_iff` transported along
`AlgebraicGeometry.LocallyRingedSpace.restrictStalkIso`, which identifies the stalks of the open
subspace with the stalks of `ℂ^n`. -/
lemma germ_restrict_mem_maximalIdeal_iff
    {A : Opens ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding)}
    {y : (complexAffineSpace.{u} n).restrict V.isOpenEmbedding} (hy : y ∈ A)
    (v : ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op A)) :
    ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.germ A y hy v ∈
        maximalIdeal (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.stalk y) ↔
      OkaRing.evalHom (U := V.isOpenEmbedding.isOpenMap.functor.obj A) ⟨y, hy, rfl⟩ v = 0 := by
  have hiso := LocallyRingedSpace.restrictStalkIso_hom_eq_germ_apply
    (complexAffineSpace.{u} n) V.isOpenEmbedding A y hy v
  set e := (complexAffineSpace.{u} n).restrictStalkIso V.isOpenEmbedding y
  have hunit : ∀ x, IsUnit (e.hom x) ↔ IsUnit x := by
    refine fun x ↦ ⟨fun h ↦ ?_, fun h ↦ h.map e.hom.hom⟩
    have h2 := h.map e.inv.hom
    rwa [← ConcreteCategory.comp_apply, e.hom_inv_id, ConcreteCategory.id_apply] at h2
  rw [mem_maximalIdeal, mem_nonunits_iff, ← hunit _, hiso, ← mem_nonunits_iff,
    ← mem_maximalIdeal]
  exact germ_mem_maximalIdeal_iff _ v

end Chart

section ChartEval

variable {Z : AnalyticSpace.{u}} {U₀ : Opens Z} {n : ℕ} {V : Opens (complexAffineSpace.{u} n)}
  {i : Z.toLocallyRingedSpace.restrict U₀.isOpenEmbedding ⟶
    (complexAffineSpace.{u} n).restrict V.isOpenEmbedding}

/-- **On a chart, the value of a germ pulled back from `ℂ^n` is the value upstairs.**

`ComplexAnalytic.eval_ofCutOut` is the special case in which the analytic space *is* the
subspace cut out and the section is global; this is the version needed when the chart covers
only a neighbourhood and the holomorphic function is defined only on an open `A ⊆ V`, which is
what a local lift produces.

The proof does not chain the transports which define `AnalyticSpace.evalStalk`. It uses
`AnalyticSpace.evalStalk_eq_iff`: subtracting the constant reduces the claim to the statement
that the composite `𝒪_{ℂ^n|V, i w} → 𝒪_{Z|U₀, w} → 𝒪_{Z, w}` carries non-units to non-units,
which holds because `i.stalkMap` is a local homomorphism and the other factor is an
isomorphism. -/
theorem evalStalk_chart
    (hlin : IsCLinearHom i (Z.toLocallyRingedSpace.resAlgMap Z.algebraMap U₀)
      (constantsAlgMap n V))
    (w : Z.toLocallyRingedSpace.restrict U₀.isOpenEmbedding)
    {A : Opens ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding)} (hA : i.base w ∈ A)
    (v : ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op A)) :
    Z.evalStalk w.1
        ((Z.toLocallyRingedSpace.restrictStalkIso U₀.isOpenEmbedding w).hom
          ((i.stalkMap w).hom
            (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.germ A
              (i.base w) hA v))) =
      OkaRing.evalHom (U := V.isOpenEmbedding.isOpenMap.functor.obj A) ⟨i.base w, hA, rfl⟩ v := by
  set e := Z.toLocallyRingedSpace.restrictStalkIso U₀.isOpenEmbedding w
  set c := OkaRing.evalHom (U := V.isOpenEmbedding.isOpenMap.functor.obj A) ⟨i.base w, hA, rfl⟩ v
    with hc
  set cst : ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.obj (op A) :=
    ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.map (homOfLE le_top).op
      (constantsAlgMap n V c) with hcst
  have hconst : e.hom ((i.stalkMap w).hom
      (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.germ A
        (i.base w) hA cst)) = Z.stalkAlgMap w.1 c := by
    rw [hcst, ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.germ_res_apply
        (homOfLE le_top) (i.base w) hA (constantsAlgMap n V c),
      show ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.germ ⊤
          (i.base w) trivial (constantsAlgMap n V c) =
        ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).stalkAlgMap
          (constantsAlgMap n V) (i.base w) c from rfl,
      hlin.stalkAlgMap w c]
    exact LocallyRingedSpace.restrictStalkIso_hom_stalkAlgMap _ Z.algebraMap U₀ w c
  have hmem : ((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.germ A
      (i.base w) hA (v - cst) ∈
      maximalIdeal (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.stalk
        (i.base w)) := by
    rw [germ_restrict_mem_maximalIdeal_iff]
    refine (map_sub _ v cst).trans (sub_eq_zero.2 ?_)
    rw [hcst]
    exact hc.symm.trans
      ((OkaRing.evalHom_restrict _ _ _).trans (OkaRing.evalHom_algebraMap _ c)).symm
  have hsub : e.hom ((i.stalkMap w).hom
        (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.germ A
          (i.base w) hA v)) -
      e.hom ((i.stalkMap w).hom
        (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.germ A
          (i.base w) hA cst)) =
      e.hom ((i.stalkMap w).hom
        (((complexAffineSpace.{u} n).restrict V.isOpenEmbedding).presheaf.germ A
          (i.base w) hA (v - cst))) := by
    simp only [map_sub]
  rw [Z.evalStalk_eq_iff, ← hconst, mem_maximalIdeal, mem_nonunits_iff]
  rw [mem_maximalIdeal, mem_nonunits_iff] at hmem
  exact fun hu ↦ hmem ((i.prop w).map_nonunit _
    ((isUnit_map_iff e.commRingCatIsoToRingEquiv _).1 ((congrArg IsUnit hsub).mp hu)))

end ChartEval

namespace AnalyticSpace

variable (Z : AnalyticSpace.{u}) {U : Opens Z} (g : Z.presheaf.obj (op U))

/-- **The value of a section is continuous at each point**, which is
`ComplexAnalytic.AnalyticSpace.continuous_eval` in local form.

The chart at `z₀` and `AlgebraicGeometry.LocallyRingedSpace.exists_localLift` produce a
holomorphic function on an open subset of `ℂ^n` whose values are the values of `g` on a
neighbourhood of `z₀`; continuity there is continuity of a holomorphic function. -/
theorem continuousAt_eval (z₀ : U) :
    ContinuousAt (fun z : U ↦ Z.eval z.1 z.2 g) z₀ := by
  obtain ⟨U₀, n, k, V, i, f, hcut, hlin⟩ := Z.local_model z₀.1
  set B : TopologicalSpace.Opens (Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding) :=
    ⟨Subtype.val ⁻¹' (U : Set Z), U.2.preimage continuous_subtype_val⟩
  have hBU : U₀.1.isOpenEmbedding.isOpenMap.functor.obj B ≤ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  set t : (Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).presheaf.obj (op B) :=
    Z.presheaf.map (homOfLE hBU).op g
  obtain ⟨A, hA, u, B', hB'B, hB'A, hx₀B', hres⟩ :=
    LocallyRingedSpace.exists_localLift i hcut.surjective_stalkMap t ⟨z₀.1, U₀.2⟩ z₀.2
  set W : TopologicalSpace.Opens Z := U₀.1.isOpenEmbedding.isOpenMap.functor.obj B'
  have hWU₀ : ∀ z ∈ W, z ∈ U₀.1 := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hWU : W ≤ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hBU ⟨x, hB'B hx, rfl⟩
  have hval : ∀ (x : Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding) (hx : x ∈ B'),
      Z.eval x.1 (hWU ⟨x, hx, rfl⟩) g =
        OkaRing.evalHom (U := V.isOpenEmbedding.isOpenMap.functor.obj A)
          ⟨i.base x, hB'A hx, rfl⟩ u := by
    intro x hx
    have h2 : (Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).presheaf.germ
          ((TopologicalSpace.Opens.map i.base).obj A) x (hB'A hx) (i.c.app (op A) u) =
        (Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).presheaf.germ B x (hB'B hx) t := by
      have e1 := (Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).presheaf.germ_res_apply
        (homOfLE hB'A) x hx (i.c.app (op A) u)
      have e2 := (Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).presheaf.germ_res_apply
        (homOfLE hB'B) x hx t
      exact e1.symm.trans ((congrArg
        (fun s ↦ (Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding).presheaf.germ B' x hx s)
        hres).trans e2)
    have h1 : Z.presheaf.germ U x.1 (hWU ⟨x, hx, rfl⟩) g =
        (Z.toLocallyRingedSpace.restrictStalkIso U₀.1.isOpenEmbedding x).hom
          ((i.stalkMap x).hom
            (((complexAffineSpace.{u} n).toLocallyRingedSpace.restrict
                V.isOpenEmbedding).presheaf.germ A (i.base x) (hB'A hx) u)) :=
      (((congrArg
            (fun z ↦ (Z.toLocallyRingedSpace.restrictStalkIso U₀.1.isOpenEmbedding x).hom z)
            ((LocallyRingedSpace.stalkMap_germ_apply i A x (hB'A hx) u).trans h2)).trans
          (LocallyRingedSpace.restrictStalkIso_hom_eq_germ_apply Z.toLocallyRingedSpace
            U₀.1.isOpenEmbedding B x (hB'B hx) t)).trans
        (Z.presheaf.germ_res_apply (homOfLE hBU) x.1 ⟨x, hB'B hx, rfl⟩ g)).symm
    rw [eval_apply, h1]
    exact evalStalk_chart hlin x (hB'A hx) u
  have hmemB' : ∀ (z : Z) (hz : z ∈ W), (⟨z, hWU₀ z hz⟩ :
      Z.toLocallyRingedSpace.restrict U₀.1.isOpenEmbedding) ∈ B' := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy
  set S : Set U := {z : U | (z : Z) ∈ W}
  have hSopen : IsOpen S := W.2.preimage continuous_subtype_val
  have hz₀S : z₀ ∈ S := ⟨⟨z₀.1, U₀.2⟩, hx₀B', rfl⟩
  refine ContinuousOn.continuousAt ?_ (hSopen.mem_nhds hz₀S)
  rw [continuousOn_iff_continuous_domRestrict]
  have hqcont : Continuous fun z : S ↦
      ((i.base ⟨z.1.1, hWU₀ _ z.2⟩ :
        ((complexAffineSpace.{u} n).toLocallyRingedSpace.restrict V.isOpenEmbedding)).1 :
          ULift.{u} (Fin n) → ℂ) :=
    continuous_subtype_val.comp (i.base.hom.continuous.comp
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _))
  have hmaps : ∀ z : S, ((i.base ⟨z.1.1, hWU₀ _ z.2⟩ :
      ((complexAffineSpace.{u} n).toLocallyRingedSpace.restrict V.isOpenEmbedding)).1 :
        ULift.{u} (Fin n) → ℂ) ∈ V.isOpenEmbedding.isOpenMap.functor.obj A :=
    fun z ↦ ⟨i.base ⟨z.1.1, hWU₀ _ z.2⟩, hB'A (hmemB' _ z.2), rfl⟩
  have hrestrict : (S.domRestrict fun z : U ↦ Z.eval z.1 z.2 g) =
      (fun y : V.isOpenEmbedding.isOpenMap.functor.obj A ↦ OkaRing.evalHom y.2 u) ∘
        fun z : S ↦ (⟨_, hmaps z⟩ : V.isOpenEmbedding.isOpenMap.functor.obj A) :=
    funext fun z ↦ hval _ (hmemB' _ z.2)
  rw [hrestrict]
  exact (OkaRing.continuous_evalHom u).comp (hqcont.subtype_mk hmaps)

/-- **The value of a section of `𝒪_Z` over `U` is a continuous function on `U`.**

Together with `ComplexAnalytic.AnalyticSpace.eval` this says that a section of the structure
sheaf of a complex analytic space really is a continuous `ℂ`-valued function on its domain ;
not merely a family of residue-field values. As for a scheme, the function does not determine
the section: a nilpotent section is nonzero and has all values `0`. -/
theorem continuous_eval : Continuous fun z : U ↦ Z.eval z.1 z.2 g :=
  continuous_iff_continuousAt.2 (Z.continuousAt_eval g)

/-- **A global section of `𝒪_Z` is a continuous function on `Z`.**

`ComplexAnalytic.AnalyticSpace.continuous_eval` at `U = ⊤`, with the identification of `⊤` with
`Z` carried out. -/
theorem continuous_eval_top (g : Z.presheaf.obj (op ⊤)) :
    Continuous fun z : Z ↦ Z.eval (U := ⊤) z trivial g := by
  have h : Continuous fun z : (⊤ : Opens Z) ↦ Z.eval z.1 z.2 g := Z.continuous_eval g
  have hc : Continuous fun z : Z ↦ (⟨z, trivial⟩ : (⊤ : Opens Z)) :=
    continuous_induced_rng.2 continuous_id
  have hcomp := h.comp hc
  exact hcomp.congr fun z ↦ rfl

end AnalyticSpace

end ComplexAnalytic

end
