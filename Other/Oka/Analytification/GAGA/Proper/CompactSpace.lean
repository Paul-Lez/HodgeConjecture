/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analytification.GAGA.Proper.Chow
public import Other.Oka.Analytification.GAGA.Proper.Induction
public import Other.Oka.Analytification.RET.ClosedPoints

/-!
# The analytification of a proper scheme is compact

For a proper scheme `X` over `ℂ`, the analytic space `X^an` is compact
(`ComplexAnalytic.IsProperℂ.compactSpace_analytification`).

- A surjective morphism `f : Y ⟶ X` of schemes locally of finite type over `ℂ` analytifies to a
  surjective map (`ComplexAnalytic.surjective_analytification_map`): the points of `X^an` are the
  closed points of `X`, and the fibre of `f` over a closed point, being closed and nonempty,
  contains a closed point of the Jacobson space `Y`.
- For `X` projective, `X^an` is a closed subspace of the compact space `ℙⁿ_an`.
- For `X` proper, `X^an` is the finite union of the preimages `π⁻¹ C` of the irreducible
  components `C` of `X`. Each `π⁻¹ C` is the image of `C_red^an`, and by Chow's lemma
  (`ComplexAnalytic.exists_chow_isProjectiveℂ`) there is a projective `Y'` with a morphism
  `Y' ⟶ C_red` which is proper and an isomorphism over a dense open, hence surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace ComplexAnalytic

/-- **Surjective morphisms analytify to surjective maps.** -/
theorem surjective_analytification_map {Y X : SchemeLFTℂ.{u}} (f : Y ⟶ X)
    (hf : Function.Surjective f.hom.left.base) :
    Function.Surjective (analytification.map f).toLRSHom.base := by
  intro x
  have hx : IsClosed {(analytificationπ X).left.base x} :=
    (mem_range_analytificationπ_base_iff X _).1 ⟨x, rfl⟩
  have hF : IsClosed (f.hom.left.base ⁻¹' {(analytificationπ X).left.base x}) :=
    hx.preimage f.hom.left.base.hom.continuous
  obtain ⟨y, hyF, hyc⟩ := nonempty_inter_closedPoints (hf _) hF.isLocallyClosed
  obtain ⟨y', rfl⟩ := (mem_range_analytificationπ_base_iff Y y).2 hyc
  refine ⟨y', analytificationπ_base_injective X ?_⟩
  rw [analytificationπ_base_map_apply]
  exact hyF

/-- **The analytification of a projective scheme is compact.** -/
theorem IsProjectiveℂ.compactSpace_analytification {X : SchemeLFTℂ.{u}} (hX : IsProjectiveℂ X) :
    CompactSpace (analytification.obj X) := by
  obtain ⟨n, i, hi⟩ := hX
  exact (isClosedEmbedding_analytification_map i).compactSpace

/-- A morphism which is proper and an isomorphism over a nonempty open subset of an irreducible
target is surjective. -/
lemma surjective_of_isIso_morphismRestrict {Y' Y : Scheme.{u}} [IrreducibleSpace Y]
    (p : Y' ⟶ Y) [UniversallyClosed p] (U : Y.Opens) (hU : (U : Set Y).Nonempty)
    [IsIso (p ∣_ U)] : Function.Surjective p.base := by
  have hsub : (U : Set Y) ⊆ Set.range p.base := fun y hy ↦ by
    obtain ⟨w, hw⟩ := (p ∣_ U).surjective ⟨y, hy⟩
    exact ⟨w.1, (morphismRestrict_base_coe p U w).symm.trans (congrArg Subtype.val hw)⟩
  have hcl := (U.isOpen.dense hU).closure_eq
  rw [← Set.range_eq_univ, ← Set.univ_subset_iff, ← hcl]
  exact (p.isClosedMap.isClosed_range).closure_subset_iff.2 hsub

/-- A closed embedding with irreducible image has irreducible source. -/
lemma irreducibleSpace_of_isClosedEmbedding {Y X : Type*} [TopologicalSpace Y]
    [TopologicalSpace X] {f : Y → X} (hf : IsClosedEmbedding f) (h : IsIrreducible (Set.range f)) :
    IrreducibleSpace Y := by
  haveI := Subtype.irreducibleSpace h
  let e := hf.isEmbedding.toHomeomorph
  exact e.symm.surjective.irreducibleSpace e.symm.continuous

/-- **The analytification of a proper scheme is compact.** -/
theorem IsProperℂ.compactSpace_analytification {X : SchemeLFTℂ.{u}} (hX : IsProperℂ X) :
    CompactSpace (analytification.obj X) := by
  haveI := hX.compactSpace
  haveI : IsNoetherian X.obj.left := {}
  have key : ∀ C ∈ irreducibleComponents X.obj.left,
      IsCompact ((analytificationπ X).left.base ⁻¹' C) := by
    intro C hC
    let Z : Closeds X.obj.left := ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩
    let Y := X.reducedSubscheme Z
    let ι := X.reducedSubschemeι Z
    have hrange : Set.range ι.hom.left.base = C := X.range_reducedSubschemeι Z
    haveI : IrreducibleSpace Y.obj.left :=
      irreducibleSpace_of_isClosedEmbedding ι.hom.left.isClosedEmbedding (hrange ▸ hC.1)
    haveI : IsIntegral Y.obj.left := isIntegral_of_irreducibleSpace_of_isReduced _
    have hYp : IsProperℂ Y := IsProperℂ.of_isClosedImmersion ι hX
    haveI : IsProper Y.obj.hom := hYp
    obtain ⟨Y', p, U, hY', hU, hpU, -⟩ := exists_chow_isProjectiveℂ Y
    haveI := hpU
    haveI := hY'.compactSpace_analytification
    haveI : IsProper (p.hom.left ≫ Y.obj.hom) := by
      rw [Over.w p.hom]
      exact hY'.isProperℂ
    haveI : IsProper p.hom.left := IsProper.of_comp p.hom.left Y.obj.hom
    have hpan := surjective_analytification_map p
      (surjective_of_isIso_morphismRestrict p.hom.left U hU)
    have hrange' : (analytificationπ X).left.base ⁻¹' C =
        Set.range ((analytification.map ι).toLRSHom.base ∘
          (analytification.map p).toLRSHom.base) := by
      rw [Set.range_comp, hpan.range_eq, Set.image_univ,
        range_analytification_map_of_isClosedImmersion, hrange]
      rfl
    rw [hrange']
    exact isCompact_range ((analytification.map ι).toLRSHom.base.hom.continuous.comp
      (analytification.map p).toLRSHom.base.hom.continuous)
  refine ⟨?_⟩
  have huniv : (Set.univ : Set (analytification.obj X)) =
      ⋃ C ∈ irreducibleComponents X.obj.left, (analytificationπ X).left.base ⁻¹' C := by
    refine (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion₂.2 ⟨_,
      irreducibleComponent_mem_irreducibleComponents ((analytificationπ X).left.base x),
      mem_irreducibleComponent⟩).symm
  rw [huniv]
  exact NoetherianSpace.finite_irreducibleComponents.isCompact_biUnion key

end ComplexAnalytic

end
