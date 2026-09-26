/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.Restrict
public import Other.Oka.Data.Fin.Tuple.Basic

/-!
# Cancelling a cut-out datum: cutting out inside a subspace rather than inside the ambient space

`ComplexAnalytic.IsCutOutBy i f` says that the closed immersion `i` exhibits its source as the
subspace of its target cut out by the global sections `f`. Every datum in this repository cuts a
subspace out of an **ambient** space ; `ComplexAnalytic.isCutOutBy_analytificationInclHom` cuts an
analytification out of `ℂ^n`, and `ComplexAnalytic.IsCutOutBy.restrictOpen` shrinks such a datum
to an open of the same ambient space. This file supplies the missing **cancellation**: given a
datum for `iW : W ⟶ Z` by `f₁` and one for `j ≫ iW : Y ⟶ Z` by `f₁` together with a further
family `f₂`, the morphism `j : Y ⟶ W` cuts `Y` out of `W` by the **pullbacks of `f₂` along
`iW`** (`ComplexAnalytic.IsCutOutBy.of_comp_append`).

That is what a consumer needs when the ambient space is not where the geometry is: a hypersurface
in `ℂ^(n+1)` cut down by further relations is a subspace of the hypersurface, and a statement
about the smaller one relative to the larger one cannot be read off two data that both point at
`ℂ^(n+1)`.

## What each of the four conditions costs

**Nothing here is analysis and nothing here is about complex analytic spaces**; it is four
statements about a factorisation `j ≫ iW` of closed immersions of locally ringed spaces.

* **The closed embedding** is `IsEmbedding.of_comp` for the embedding half and, for the closed
  half, the observation that `Set.range j.base` is the `iW`-preimage of `Set.range (j ≫ iW).base`
  ; which uses only that `iW.base` is injective. That observation is `hrange` in the proof below,
  and the one other field read through it is `range_base`; the two stalk conditions never mention
  it.
* **`range_base`** splits the conjunction over `Fin.append f₁ f₂` into its two halves. The `f₁`
  half is **free and carries no hypothesis about `Y`**: every point of `W` lies in the image of
  `iW`, so `hW.range_base` already puts the germs of `f₁` in the maximal ideal there. The `f₂`
  half transfers along `iW`'s stalk map, which is a **local** ring homomorphism and so reflects
  units as well as preserving them.
* **`surjective_stalkMap`** is `Function.Surjective.of_comp` against
  `AlgebraicGeometry.LocallyRingedSpace.stalkMap_comp`, and asks nothing of `hW`.
* **`ker_stalkMap` is the only condition that uses `hW`'s own kernel**, and it is where the
  surjectivity of `iW`'s stalk map is spent. Writing `φ` for that stalk map and `ψ` for `j`'s,
  `RingHom.comap_ker` gives `ker (ψ ∘ φ) = φ⁻¹ (ker ψ)` and `Ideal.map_comap_of_surjective` turns
  that into `ker ψ = φ (ker (ψ ∘ φ))`. The image of the generating set splits: the germs of `f₁`
  lie in `ker φ` by `hW.ker_stalkMap`, so they contribute `0`, and the germs of `f₂` map to the
  germs of their pullbacks.

## Why `Fin.append` and not a subfamily

`ComplexAnalytic.IsCutOutBy` is indexed by `Fin k`, so "the big family contains the small one" has
to be spelled. `Fin.append` is the cheapest spelling to *prove* about, because `Fin.addCases`
splits a quantifier over it in one step. It is the wrong spelling for a *caller*, whose family
arrives as a `Fin.snoc` or in the other order, so
`ComplexAnalytic.IsCutOutBy.of_comp_of_range_eq` restates the same theorem with the hypothesis
`Set.range f = Set.range f₁ ∪ Set.range f₂` and no `Fin.append` in it. **Both directions of that
are free**, because `ComplexAnalytic.IsCutOutBy` depends on its family only through its range:
that is `ComplexAnalytic.IsCutOutBy.of_range_eq`, which is worth having on its own and is stated
first.

## What is not here

* **No converse.** Nothing below says that a datum for `j : Y ⟶ W` and one for `iW` compose to a
  datum for `j ≫ iW`. That direction is `ComplexAnalytic.IsCutOutBy.comp_append` in
  `Other/Oka/AnalyticSpace/CutOutCompose.lean`, and it is a different proof, the kernel computation
  running the other way and needing `Ideal.comap` of a span where this one needs `Ideal.map`.
  **This bullet ended *"and nothing in the tree wants it yet"* until 2026-09-07**, by which date
  the construction of a subspace of a local model wanted it.
* **No analytification and no `ℂ^n`.** The consumer this was written for is the local-isomorphism
  half of a standard étale analytification over a presented base, but no statement here mentions
  a polynomial, a presentation, or `ComplexAnalytic.AnalyticSpace`.
* **No `IsLocalIso` and no transport of any morphism class.**
  `ComplexAnalytic.AnalyticSpace.isLocalIso_of_isCutOutBy_pullbackΓ` is the consumer that turns
  two cut-out data into a local isomorphism; this file only *produces* the second of its two
  data.

## Main results

- `ComplexAnalytic.IsCutOutBy.of_range_eq`: **being cut out depends on the cutting family only
  through its range**, so the family may be reindexed at will.
- `ComplexAnalytic.IsCutOutBy.of_comp_append`: **the cancellation** ; if `iW` cuts out `W` by
  `f₁` and `j ≫ iW` cuts out `Y` by `Fin.append f₁ f₂`, then `j` cuts out `Y` inside `W` by the
  pullbacks of `f₂` along `iW`.
- `ComplexAnalytic.IsCutOutBy.of_comp_of_range_eq`: the same statement at the hypothesis a caller
  holds, `Set.range f = Set.range f₁ ∪ Set.range f₂`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Topology

universe u

namespace ComplexAnalytic

variable {Z W Y : LocallyRingedSpace.{u}}

/-- **Being cut out by global sections depends on the family only through its range.**

Both conditions that mention the family read it through its range: `range_base` is a `∀` over the
index and `ker_stalkMap` is a span over `Set.range`. So a family may be reindexed, repeated or
permuted freely, and in particular the arity `k` is not an invariant of the datum.

This is what lets `ComplexAnalytic.IsCutOutBy.of_comp_append` be stated at `Fin.append`, which is
convenient to prove about and which no caller holds. -/
theorem IsCutOutBy.of_range_eq {i : Y ⟶ Z} {k k' : ℕ} {f : Fin k → Z.presheaf.obj (op ⊤)}
    {f' : Fin k' → Z.presheaf.obj (op ⊤)} (hcut : IsCutOutBy i f)
    (h : Set.range f' = Set.range f) : IsCutOutBy i f' where
  isClosedEmbedding := hcut.isClosedEmbedding
  range_base := by
    rw [hcut.range_base]
    ext z
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hz j'
      obtain ⟨j, hj⟩ : f' j' ∈ Set.range f := h ▸ Set.mem_range_self j'
      exact hj ▸ hz j
    · intro hz j
      obtain ⟨j', hj'⟩ : f j ∈ Set.range f' := h.symm ▸ Set.mem_range_self j
      exact hj' ▸ hz j'
  surjective_stalkMap := hcut.surjective_stalkMap
  ker_stalkMap y := by
    rw [hcut.ker_stalkMap y]
    congr 1
    rw [show (fun j' ↦ Z.presheaf.Γgerm (i.base y) (f' j')) =
        (fun s ↦ Z.presheaf.Γgerm (i.base y) s) ∘ f' from rfl,
      show (fun j ↦ Z.presheaf.Γgerm (i.base y) (f j)) =
        (fun s ↦ Z.presheaf.Γgerm (i.base y) s) ∘ f from rfl,
      Set.range_comp, Set.range_comp, h]

/-- **Cancelling a cut-out datum**: if `iW` cuts out `W` inside `Z` by `f₁`, and `j ≫ iW` cuts
out `Y` inside `Z` by `f₁` together with `f₂`, then `j` cuts out `Y` inside `W` by the pullbacks
of `f₂` along `iW`.

The module docstring says what each of the four conditions costs. The one hypothesis that is
**not** used anywhere is `hW.isClosedEmbedding`'s closedness ; only the injectivity of `iW.base`
is, and it is read for one thing: to identify `Set.range j.base` as the `iW`-preimage of
`Set.range (j ≫ iW).base`, in `hrange` below. **The embedding half does not read it either**:
`IsEmbedding.of_comp` asks for two continuities and an embedding of the composite, so the
injectivity of `j.base` comes out of `hY`. The closedness of `Set.range j.base` comes from `hY`
too, not from `hW`. -/
theorem IsCutOutBy.of_comp_append {iW : W ⟶ Z} {j : Y ⟶ W} {k₁ k₂ : ℕ}
    {f₁ : Fin k₁ → Z.presheaf.obj (op ⊤)} {f₂ : Fin k₂ → Z.presheaf.obj (op ⊤)}
    (hW : IsCutOutBy iW f₁) (hY : IsCutOutBy (j ≫ iW) (Fin.append f₁ f₂)) :
    IsCutOutBy j (fun r ↦ (LocallyRingedSpace.Γ.map iW.op).hom (f₂ r)) := by
  have hbase : ⇑(j ≫ iW).base = ⇑iW.base ∘ ⇑j.base := rfl
  have hrange : Set.range j.base = iW.base ⁻¹' Set.range (j ≫ iW).base := by
    ext w
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hW.isClosedEmbedding.injective hy⟩
  have hf1 (w : W) (l : Fin k₁) :
      Z.presheaf.Γgerm (iW.base w) (f₁ l) ∈
        IsLocalRing.maximalIdeal (Z.presheaf.stalk (iW.base w)) := by
    have hmem : iW.base w ∈ Set.range iW.base := ⟨w, rfl⟩
    rw [hW.range_base] at hmem
    exact hmem l
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
  refine ⟨?_, ?_, fun y ↦ ?_, fun y ↦ ?_⟩
  · refine ⟨IsEmbedding.of_comp j.base.hom.continuous iW.base.hom.continuous
      (hbase ▸ hY.isClosedEmbedding.isEmbedding), ?_⟩
    rw [hrange]
    exact hY.isClosedEmbedding.isClosed_range.preimage iW.base.hom.continuous
  · rw [hrange]
    ext w
    simp only [Set.mem_preimage, hY.range_base, Set.mem_setOf_eq]
    constructor
    · intro hz r
      rw [htrans w (f₂ r)]
      exact Fin.append_right f₁ f₂ r ▸ hz (Fin.natAdd k₁ r)
    · intro hz jj
      refine Fin.addCases (motive := fun jj ↦ Z.presheaf.Γgerm (iW.base w) (Fin.append f₁ f₂ jj) ∈
        IsLocalRing.maximalIdeal (Z.presheaf.stalk (iW.base w))) (fun l ↦ ?_) (fun r ↦ ?_) jj
      · rw [Fin.append_left]
        exact hf1 w l
      · rw [Fin.append_right]
        exact (htrans w (f₂ r)).1 (hz r)
  · exact Function.Surjective.of_comp (g := (iW.stalkMap (j.base y)).hom)
      (by rw [← RingHom.coe_comp, ← hsplit y]; exact hY.surjective_stalkMap y)
  · set φ := (iW.stalkMap (j.base y)).hom with hφdef
    set ψ := (j.stalkMap y).hom with hψdef
    have hφ : Function.Surjective φ := hW.surjective_stalkMap (j.base y)
    have hkercomp : RingHom.ker (ψ.comp φ) =
        Ideal.span (Set.range fun jj ↦ Z.presheaf.Γgerm (iW.base (j.base y))
          (Fin.append f₁ f₂ jj)) := by
      rw [← hsplit y]
      exact hY.ker_stalkMap y
    have hker : RingHom.ker ψ = Ideal.map φ (RingHom.ker (ψ.comp φ)) := by
      rw [← RingHom.comap_ker, Ideal.map_comap_of_surjective φ hφ]
    have hzero (l : Fin k₁) : φ (Z.presheaf.Γgerm (iW.base (j.base y)) (f₁ l)) = 0 := by
      have hmem : Z.presheaf.Γgerm (iW.base (j.base y)) (f₁ l) ∈ RingHom.ker φ := by
        rw [hφdef, hW.ker_stalkMap (j.base y)]
        exact Ideal.subset_span ⟨l, rfl⟩
      exact hmem
    rw [hker, hkercomp, Ideal.map_span φ]
    refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
    · rintro _ ⟨_, ⟨jj, rfl⟩, rfl⟩
      refine Fin.addCases (motive := fun jj ↦ φ (Z.presheaf.Γgerm (iW.base (j.base y))
        (Fin.append f₁ f₂ jj)) ∈ Ideal.span (Set.range fun r ↦ W.presheaf.Γgerm (j.base y)
          ((LocallyRingedSpace.Γ.map iW.op).hom (f₂ r)))) (fun l ↦ ?_) (fun r ↦ ?_) jj
      · rw [Fin.append_left, hzero l]
        exact Ideal.zero_mem _
      · rw [Fin.append_right, hφdef, ← LocallyRingedSpace.Γgerm_Γ_map]
        exact Ideal.subset_span ⟨r, rfl⟩
    · rintro _ ⟨r, rfl⟩
      refine Ideal.subset_span ⟨Z.presheaf.Γgerm (iW.base (j.base y))
        (Fin.append f₁ f₂ (Fin.natAdd k₁ r)), ⟨Fin.natAdd k₁ r, rfl⟩, ?_⟩
      rw [Fin.append_right, hφdef, ← LocallyRingedSpace.Γgerm_Γ_map]

/-- **The cancellation at the hypothesis a caller holds.**

`ComplexAnalytic.IsCutOutBy.of_comp_append` asks for the big family to be literally
`Fin.append f₁ f₂`, and no caller's is: `ComplexAnalytic.hypersurfacePresentation` produces a
`Fin.snoc`, and the subfamily cutting out the intermediate space need not come first. Since
`ComplexAnalytic.IsCutOutBy` sees a family only through its range
(`ComplexAnalytic.IsCutOutBy.of_range_eq`), the honest hypothesis is the set equation, and this
is that statement. -/
theorem IsCutOutBy.of_comp_of_range_eq {iW : W ⟶ Z} {j : Y ⟶ W} {k k₁ k₂ : ℕ}
    {f : Fin k → Z.presheaf.obj (op ⊤)} {f₁ : Fin k₁ → Z.presheaf.obj (op ⊤)}
    {f₂ : Fin k₂ → Z.presheaf.obj (op ⊤)} (hW : IsCutOutBy iW f₁)
    (hY : IsCutOutBy (j ≫ iW) f) (hf : Set.range f = Set.range f₁ ∪ Set.range f₂) :
    IsCutOutBy j (fun r ↦ (LocallyRingedSpace.Γ.map iW.op).hom (f₂ r)) :=
  IsCutOutBy.of_comp_append hW (hY.of_range_eq (by rw [Fin.range_append, hf]))

end ComplexAnalytic

end
