/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Closures of graphs

For morphisms `sY : Y ⟶ S`, `sP : P ⟶ S`, an open `U ⊆ Y` and `g : U ⟶ P` over `S`, the graph
`U ⟶ Y ×_S P` is an immersion (`AlgebraicGeometry.graphMap`). If `U ⟶ Y` is quasi-compact and
`P` is separated over `S`, the preimage of `U` is scheme-theoretically dense in the
scheme-theoretic image `Γ̄` of the graph, and the first projection `Γ̄ ⟶ Y` restricts to an
isomorphism over `U` (`AlgebraicGeometry.isIso_graphClosureFst_restrict`). Morphisms to a
separated scheme agreeing on a scheme-theoretically dense open agree
(`AlgebraicGeometry.ext_of_isSchemeTheoreticallyDominant_of_isSeparated`).

We also record two criteria used in the proof of Chow's lemma:

- `AlgebraicGeometry.isClosedImmersion_morphismRestrict_of_graph`: let `c : X ⟶ Y ×_S P` be a
  closed immersion with projections `π`, `q`, let `V ⊆ P` be open, `t : T ⟶ V` a closed
  immersion and `ρ : T ⟶ Y` over `S`. If `q` and `π` factor over `q⁻¹ V` as `t ∘ u` and `ρ ∘ u`,
  then `q⁻¹ V ⟶ V` is a closed immersion.
- `AlgebraicGeometry.isClosedImmersion_of_isClosed_range_of_cover`: a morphism with closed
  range which is a closed immersion over each member of a family of opens covering its range is
  a closed immersion.
-/

@[expose] public section

open CategoryTheory Limits

universe u

set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

variable {X Y P S : Scheme.{u}} {sY : Y ⟶ S} {sP : P ⟶ S}

/-- Let `c : X ⟶ Y ×_S P` be a closed immersion, `V ⊆ P` open, `t : T ⟶ V` a closed immersion
and `ρ : T ⟶ Y` over `S`. If on `q⁻¹ V` (`q = c ≫ snd`) the projections to `V` and `Y` factor
as `u ≫ t` and `u ≫ ρ`, then `q⁻¹ V ⟶ V` is a closed immersion. -/
theorem isClosedImmersion_morphismRestrict_of_graph (c : X ⟶ pullback sY sP)
    [IsClosedImmersion c] (V : P.Opens) {T : Scheme.{u}} (t : T ⟶ V) [IsClosedImmersion t]
    (ρ : T ⟶ Y) (hρ : ρ ≫ sY = t ≫ V.ι ≫ sP)
    (u : ((c ≫ pullback.snd sY sP) ⁻¹ᵁ V).toScheme ⟶ T)
    (hu₁ : u ≫ t = (c ≫ pullback.snd sY sP) ∣_ V)
    (hu₂ : u ≫ ρ = Scheme.Opens.ι _ ≫ c ≫ pullback.fst sY sP) :
    IsClosedImmersion ((c ≫ pullback.snd sY sP) ∣_ V) := by
  rw [← hu₁]
  suffices IsClosedImmersion u from inferInstance
  let O : (pullback sY sP).Opens := pullback.snd sY sP ⁻¹ᵁ V
  let γ : T ⟶ pullback sY sP := pullback.lift ρ (t ≫ V.ι) (by rw [hρ, Category.assoc])
  have hγ : Set.range γ ⊆ (O : Set _) := by
    rintro _ ⟨x, rfl⟩
    change pullback.snd sY sP (γ x) ∈ V
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply]
    exact (t x).2
  let γ' : T ⟶ O := IsOpenImmersion.lift O.ι γ (by simpa using hγ)
  have hγ' : γ' ≫ O.ι = γ := IsOpenImmersion.lift_fac _ _ _
  have : Mono γ := by
    have : Mono (γ ≫ pullback.snd sY sP) := by rw [pullback.lift_snd]; infer_instance
    exact mono_of_mono γ (pullback.snd sY sP)
  have : Mono γ' := by
    have : Mono (γ' ≫ O.ι) := by rw [hγ']; infer_instance
    exact mono_of_mono γ' O.ι
  have key : u ≫ γ' = (X.isoOfEq (by rfl : c ⁻¹ᵁ O = _)).inv ≫ (c ∣_ O) := by
    rw [← cancel_mono O.ι, Category.assoc, hγ', Category.assoc, morphismRestrict_ι]
    apply pullback.hom_ext
    · simp only [γ, Category.assoc, pullback.lift_fst, hu₂, Scheme.isoOfEq_inv_ι_assoc]
    · simp only [γ, Category.assoc, pullback.lift_snd, reassoc_of% hu₁, morphismRestrict_ι,
        Scheme.isoOfEq_inv_ι_assoc]
  have : IsClosedImmersion (u ≫ γ') := key ▸ inferInstance
  exact IsClosedImmersion.of_comp u γ'

/-- A morphism with closed range is a closed immersion if it is one over each member of a family
of opens covering its range. -/
theorem isClosedImmersion_of_isClosed_range_of_cover {X P : Scheme.{u}} (q : X ⟶ P)
    (hq : IsClosed (Set.range q)) {α : Type*} (V : α → P.Opens)
    (hV : ∀ x, ∃ a, q x ∈ V a) (h : ∀ a, IsClosedImmersion (q ∣_ V a)) :
    IsClosedImmersion q := by
  let O : P.Opens := ⟨(Set.range q)ᶜ, hq.isOpen_compl⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun o : Option α ↦ o.elim O V) ?_ ?_
  · rw [eq_top_iff]
    intro p _
    by_cases hp : p ∈ Set.range q
    · obtain ⟨x, rfl⟩ := hp
      obtain ⟨a, ha⟩ := hV x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨some a, ha⟩
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨none, hp⟩
  · rintro (_ | a)
    · have : IsEmpty (q ⁻¹ᵁ O) := ⟨fun ⟨x, hx⟩ ↦ hx ⟨x, rfl⟩⟩
      change IsClosedImmersion (q ∣_ O)
      infer_instance
    · exact h a

/-- The morphism to the scheme-theoretic image of a quasi-compact morphism is
scheme-theoretically dominant. -/
instance isSchemeTheoreticallyDominant_toImage {X Z : Scheme.{u}} (f : X ⟶ Z)
    [QuasiCompact f] : IsSchemeTheoreticallyDominant f.toImage := by
  rw [isSchemeTheoreticallyDominant_iff]
  let W : Z.affineOpens → f.image.affineOpens := fun V ↦ ⟨f.imageι ⁻¹ᵁ V.1, V.2.preimage _⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top W ?_ fun V ↦ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.imageι x)) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV⟩, hxV⟩
  · rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (f.toImage_app_injective V)

/-- The restriction of a quasi-compact scheme-theoretically dominant morphism to an open of the
target is scheme-theoretically dominant. -/
instance isSchemeTheoreticallyDominant_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] (V : Y.Opens) :
    IsSchemeTheoreticallyDominant (f ∣_ V) :=
  .of_isPullback (isPullback_morphismRestrict f V).flip

/-- If `g ≫ V.ι` is quasi-compact and scheme-theoretically dominant, so is `g`. -/
lemma IsSchemeTheoreticallyDominant.of_comp_ι {X Y : Scheme.{u}} {V : Y.Opens}
    (g : X ⟶ V) [IsSchemeTheoreticallyDominant (g ≫ V.ι)] [QuasiCompact (g ≫ V.ι)] :
    IsSchemeTheoreticallyDominant g := by
  refine .of_isPullback (f := g ≫ V.ι) (g := V.ι) (pX := 𝟙 X) (IsPullback.flip ?_)
  refine IsOpenImmersion.isPullback g (𝟙 X) V.ι (g ≫ V.ι) (Category.id_comp _) ?_
  ext x
  exact iff_of_true ⟨g x, rfl⟩ ⟨x, rfl⟩

/-- If the source of a scheme-theoretically dominant morphism `i` factors through an open `V`,
then `V ⟶ X` is scheme-theoretically dominant. -/
lemma IsSchemeTheoreticallyDominant.ι_of_fac {W X : Scheme.{u}} {V : X.Opens} (g : W ⟶ V)
    (i : W ⟶ X) [IsSchemeTheoreticallyDominant i] (h : g ≫ V.ι = i) :
    IsSchemeTheoreticallyDominant V.ι := by
  rw [isSchemeTheoreticallyDominant_iff, eq_bot_iff, ← i.ker_eq_bot, ← h]
  exact Scheme.Hom.le_ker_comp _ _

/-- Let `f g : X ⟶ Y` agree over some separated `s : Y ⟶ Z`. Then `f = g` if `ι ≫ f = ι ≫ g`
for some scheme-theoretically dominant `ι`. -/
lemma ext_of_isSchemeTheoreticallyDominant_of_isSeparated {W X Y Z : Scheme.{u}} {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have hι : ι' ≫ f' = ι' ≫ g' := by ext1; exact hU
  have hfac : (equalizer.lift ι' hι).left ≫ (equalizer.ι f' g').left = ι := by
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have : IsIso (equalizer.ι f' g').left := by
    have : IsSchemeTheoreticallyDominant
        ((equalizer.lift ι' hι).left ≫ (equalizer.ι f' g').left) := by
      rw [hfac]; exact (inferInstance : IsSchemeTheoreticallyDominant ι)
    rw [IsClosedImmersion.isIso_iff_ker_eq_bot, eq_bot_iff,
      ← ((equalizer.lift ι' hι).left ≫ (equalizer.ι f' g').left).ker_eq_bot]
    exact Scheme.Hom.le_ker_comp _ _
  exact (cancel_epi (equalizer.ι f' g').left).1 congr($(equalizer.condition f' g').left)

/-- The scheme-theoretic image of a quasi-compact morphism from a reduced scheme is reduced. -/
lemma isReduced_image {X Z : Scheme.{u}} (f : X ⟶ Z) [QuasiCompact f] [IsReduced X] :
    IsReduced f.image :=
  IsSchemeTheoreticallyDominant.isReduced f.toImage

section graph

variable {Y P S : Scheme.{u}} (sY : Y ⟶ S) (sP : P ⟶ S) (U : Y.Opens) (g : U.toScheme ⟶ P)
  (hg : g ≫ sP = U.ι ≫ sY)

/-- The graph `U ⟶ Y ×_S P` of a morphism `g : U ⟶ P` over `S` defined on an open `U ⊆ Y`. -/
noncomputable def graphMap : U.toScheme ⟶ pullback sY sP := pullback.lift U.ι g hg.symm

@[reassoc (attr := simp)]
lemma graphMap_fst : graphMap sY sP U g hg ≫ pullback.fst sY sP = U.ι := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma graphMap_snd : graphMap sY sP U g hg ≫ pullback.snd sY sP = g := pullback.lift_snd _ _ _

instance : IsImmersion (graphMap sY sP U g hg) := by
  have : IsImmersion (graphMap sY sP U g hg ≫ pullback.fst sY sP) := by
    rw [graphMap_fst]; infer_instance
  exact IsImmersion.of_comp _ (pullback.fst sY sP)

/-- The graph of `g` is quasi-compact if `U ⟶ Y` is. -/
lemma quasiCompact_graphMap [QuasiCompact U.ι] [QuasiSeparated sP] :
    QuasiCompact (graphMap sY sP U g hg) := by
  have : QuasiCompact (graphMap sY sP U g hg ≫ pullback.fst sY sP) := by
    rw [graphMap_fst]; infer_instance
  exact QuasiCompact.of_comp _ (pullback.fst sY sP)

variable [QuasiCompact U.ι] [IsSeparated sP]

/-- The projection `Γ̄ ⟶ Y` from the scheme-theoretic image of the graph. -/
noncomputable abbrev graphClosureFst : (graphMap sY sP U g hg).image ⟶ Y :=
  (graphMap sY sP U g hg).imageι ≫ pullback.fst sY sP

/-- The projection `Γ̄ ⟶ P` from the scheme-theoretic image of the graph. -/
noncomputable abbrev graphClosureSnd : (graphMap sY sP U g hg).image ⟶ P :=
  (graphMap sY sP U g hg).imageι ≫ pullback.snd sY sP

include hg in
/-- The scheme-theoretic image of the graph is reduced if `Y` is. -/
lemma isReduced_graphClosure [IsReduced Y] : IsReduced (graphMap sY sP U g hg).image :=
  have := quasiCompact_graphMap sY sP U g hg
  isReduced_image _

/-- The open immersion `U ⟶ π⁻¹ U` into the preimage of `U` in the closure of the graph. -/
noncomputable def graphClosureι :
    U.toScheme ⟶ (graphClosureFst sY sP U g hg ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (graphClosureFst sY sP U g hg ⁻¹ᵁ U).ι (graphMap sY sP U g hg).toImage
    (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      change graphClosureFst sY sP U g hg ((graphMap sY sP U g hg).toImage x) ∈ U
      rw [← Scheme.Hom.comp_apply]
      simp)

omit [QuasiCompact U.ι] [IsSeparated sP] in
@[reassoc]
lemma graphClosureι_ι : graphClosureι sY sP U g hg ≫ (graphClosureFst sY sP U g hg ⁻¹ᵁ U).ι =
    (graphMap sY sP U g hg).toImage :=
  IsOpenImmersion.lift_fac _ _ _

instance : IsSchemeTheoreticallyDominant (graphClosureι sY sP U g hg) := by
  have := quasiCompact_graphMap sY sP U g hg
  have : IsSchemeTheoreticallyDominant
      (graphClosureι sY sP U g hg ≫ (graphClosureFst sY sP U g hg ⁻¹ᵁ U).ι) := by
    rw [graphClosureι_ι]; infer_instance
  have : QuasiCompact (graphClosureι sY sP U g hg ≫ (graphClosureFst sY sP U g hg ⁻¹ᵁ U).ι) := by
    rw [graphClosureι_ι]; infer_instance
  exact .of_comp_ι _

/-- The preimage of `U` is scheme-theoretically dense in the closure of the graph. -/
instance : IsSchemeTheoreticallyDominant (graphClosureFst sY sP U g hg ⁻¹ᵁ U).ι := by
  have := quasiCompact_graphMap sY sP U g hg
  exact .ι_of_fac _ _ (graphClosureι_ι sY sP U g hg)

/-- **The closure of the graph is isomorphic to `U` over `U`.** -/
lemma isIso_graphClosureFst_restrict : IsIso (graphClosureFst sY sP U g hg ∣_ U) := by
  set Γ := graphMap sY sP U g hg
  set π := graphClosureFst sY sP U g hg
  set ι' := graphClosureι sY sP U g hg
  have hπ : Γ.toImage ≫ π = U.ι := by simp [π, Γ]
  have hq : Γ.toImage ≫ graphClosureSnd sY sP U g hg = g := by simp [Γ]
  have hι' : ι' ≫ (π ⁻¹ᵁ U).ι = Γ.toImage := graphClosureι_ι ..
  have h₂ : ι' ≫ π ∣_ U = 𝟙 _ := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hι', hπ,
      Category.id_comp]
  refine ⟨ι', ?_, h₂⟩
  rw [← cancel_mono ((π ⁻¹ᵁ U).ι ≫ Γ.imageι), Category.assoc, reassoc_of% hι',
    Γ.toImage_imageι, Category.id_comp]
  apply pullback.hom_ext
  · simp only [Category.assoc, graphMap_fst, Γ]
    exact morphismRestrict_ι π U
  · simp only [Category.assoc, graphMap_snd, Γ]
    refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated sP ?_ ι' ?_
    · simp only [Category.assoc, hg]
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Category.assoc,
        pullback.condition]
    · simp only [reassoc_of% h₂, reassoc_of% hι']
      exact hq.symm

end graph

/-- The scheme-theoretic image of a quasi-compact morphism from an irreducible scheme is
irreducible. -/
lemma irreducibleSpace_image {X Z : Scheme.{u}} (f : X ⟶ Z) [QuasiCompact f]
    [IrreducibleSpace X] : IrreducibleSpace f.image := by
  refine (irreducibleSpace_def _).2 ?_
  have h := (IrreducibleSpace.isIrreducible_univ X).image f.toImage
    f.toImage.continuous.continuousOn
  rw [Set.image_univ] at h
  simpa [f.toImage.denseRange.closure_range] using h.closure

end AlgebraicGeometry

end
