/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AlgebraicGeometry.Modules.Coherent
public import Other.Oka.AlgebraicGeometry.Modules.Support
public import Other.Oka.Analytification.GAGA.ClosedImmersionPushforward
public import Other.Oka.Analytification.GAGA.ComparisonAdditive
public import Other.Oka.Analytification.GAGA.FiveLemma
public import Other.Oka.Analytification.GAGA.Proper.Basic
public import Other.Oka.Analytification.SchemeLFTNoetherian
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesClosedEmbeddingUnit
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.PullbackCoherent

/-!
# Noetherian induction for the GAGA comparison map

Let `X` be a scheme locally of finite type over `ℂ` with quasi-compact underlying space. We show
that the GAGA comparison maps `Hᵠ(X, F) → Hᵠ(X^an, F^an)` are bijective for all coherent `F`
(`ComplexAnalytic.gagaMap_bijective_of_genericGAGA`), provided `X` satisfies
`ComplexAnalytic.GenericGAGA`: for every closed integral subscheme `Y` of `X` and every coherent
`F` on `Y`, there are a nonempty open `U ⊆ Y` and a morphism `F ⟶ A` to a coherent sheaf `A` for
which the comparison maps are bijective, such that `F ⟶ A` is bijective on stalks at the points
of `U`.

The proof is a noetherian induction on the closed subset `Z ⊆ X` off which `F` vanishes:

- a coherent `F` vanishing off `Z` is killed by a power of the ideal of the reduced closed
  subscheme `ι : Z_red ⟶ X` (`AlgebraicGeometry.exists_pow_pushforwardStalkIdeal_le_annihilator`),
  so it is an iterated extension of sheaves `ι_* G` with `G` coherent on `Z_red`
  (`ComplexAnalytic.gagaMap_bijective_of_pow_le_annihilator`);
- a coherent sheaf on `Z_red` vanishing off a proper closed subset of `Z_red` is handled by the
  induction hypothesis;
- if `Z` is irreducible, `Z_red` is integral, and the hypothesis provides `F ⟶ A` whose kernel and
  cokernel vanish off a proper closed subset;
- if `Z = Z₁ ∪ Z₂` with `Zᵢ` proper closed, the unit `G ⟶ i_* i^* G` for the reduced subscheme
  `i : (Z₂)_red ⟶ Z_red` is surjective with kernel vanishing off `Z₁`.

The statement for sheaves vanishing off a closed subset is
`ComplexAnalytic.gagaMap_bijective_of_forall_notMem`.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Topology

universe u

noncomputable section

namespace ComplexAnalytic



/-- The GAGA comparison map of a zero sheaf is bijective. -/
lemma gagaMap_bijective_of_isZero {X : SchemeLFTℂ.{u}}
    {F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf} (hF : IsZero F) (q : ℕ) :
    Function.Bijective (gagaMap X F q) := by
  have h₁ : ∀ x : LocallyRingedSpace.H F q, x = 0 := fun x ↦ by
    rw [← LocallyRingedSpace.H.map_id_apply x, hF.eq_of_src (𝟙 F) 0,
      LocallyRingedSpace.H.map_zero_apply]
  have hF' := (analytificationModules X).map_isZero hF
  have h₂ : ∀ y : LocallyRingedSpace.H ((analytificationModules X).obj F) q, y = 0 := fun y ↦ by
    rw [← LocallyRingedSpace.H.map_id_apply y, hF'.eq_of_src (𝟙 _) 0,
      LocallyRingedSpace.H.map_zero_apply]
  exact ⟨fun a b _ ↦ (h₁ a).trans (h₁ b).symm, fun y ↦ ⟨0, (h₂ _).trans (h₂ y).symm⟩⟩

/-- For a closed immersion `i : Z ⟶ X`, the comparison map of `i_* G` is bijective if and only if
the one of `G` is. -/
lemma bijective_gagaMap_pushforward_iff_of_isClosedImmersion {Z X : SchemeLFTℂ.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i.hom.left]
    (G : SheafOfModules.{u} Z.obj.left.toLocallyRingedSpace.ringSheaf)
    (q : ℕ) :
    Function.Bijective
        (gagaMap X ((SheafOfModules.pushforward.{u} i.hom.left.toLRSHom.toRingSheafHom).obj G) q) ↔
      Function.Bijective (gagaMap Z G q) := by
  haveI := isIso_analytificationPushforwardBaseChange i G
  exact bijective_gagaMap_pushforward_iff i G q

/-! ### The reduced closed subscheme on a closed subset -/

variable (X : SchemeLFTℂ.{u}) (Z : Closeds X.obj.left)

/-- **The reduced closed subscheme on a closed subset `Z` of `X`**, as a scheme locally of finite
type over `ℂ`. -/
def SchemeLFTℂ.reducedSubscheme : SchemeLFTℂ.{u} :=
  ⟨Over.mk ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ X.obj.hom), by
    haveI : LocallyOfFiniteType X.obj.hom := X.property
    haveI : LocallyOfFiniteType (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι :=
      inferInstance
    change LocallyOfFiniteType ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ X.obj.hom)
    infer_instance⟩

/-- The inclusion of the reduced closed subscheme on `Z`. -/
def SchemeLFTℂ.reducedSubschemeι : X.reducedSubscheme Z ⟶ X :=
  ObjectProperty.homMk (Over.homMk (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι rfl)

@[simp]
lemma SchemeLFTℂ.reducedSubschemeι_hom_left :
    (X.reducedSubschemeι Z).hom.left = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι :=
  rfl

/-- The inclusion of the reduced closed subscheme is a closed immersion. -/
instance : IsClosedImmersion (X.reducedSubschemeι Z).hom.left :=
  inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)

/-- The reduced closed subscheme is reduced. -/
instance : IsReduced (X.reducedSubscheme Z).obj.left :=
  inferInstanceAs (IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)

/-- The image of the reduced closed subscheme on `Z` is `Z`. -/
lemma SchemeLFTℂ.range_reducedSubschemeι :
    Set.range (X.reducedSubschemeι Z).hom.left.base = Z := by
  exact (Scheme.IdealSheafData.range_subschemeι _).trans
    (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)

/-! ### Dévissage along a closed immersion -/

variable {X} {Y : SchemeLFTℂ.{u}} (j : Y ⟶ X) [IsClosedImmersion j.hom.left]

/-- **Dévissage along a closed immersion.** Let `j : Y ⟶ X` be a closed immersion such that the
comparison maps of all coherent sheaves on `Y` are bijective. If a coherent sheaf `F` on `X` is
killed stalkwise by the `n`-th power of the ideal of `Y`, then the comparison maps of `F` are
bijective. -/
theorem gagaMap_bijective_of_pow_le_annihilator
    (hY : ∀ G : SheafOfModules.{u} Y.obj.left.toLocallyRingedSpace.ringSheaf, G.IsCoherent →
      ∀ q, Function.Bijective (gagaMap Y G q))
    (n : ℕ) (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent]
    (hF : ∀ x, j.hom.left.toLRSHom.pushforwardStalkIdeal x ^ n ≤
      Module.annihilator _ ((X.obj.left.toLocallyRingedSpace.stalkFunctor x).obj F)) (q : ℕ) :
    Function.Bijective (gagaMap X F q) := by
  induction n generalizing F q with
  | zero =>
    refine gagaMap_bijective_of_isZero
      (LocallyRingedSpace.isZero_of_forall_subsingleton_stalk F fun x ↦ ⟨fun a b ↦ ?_⟩) q
    have h1 : (1 : X.obj.left.presheaf.stalk x) ∈ Module.annihilator _ _ :=
      hF x (by rw [pow_zero, Ideal.one_eq_top]; trivial)
    rw [← one_smul (X.obj.left.presheaf.stalk x) a, ← one_smul (X.obj.left.presheaf.stalk x) b,
      Module.mem_annihilator.1 h1 a, Module.mem_annihilator.1 h1 b]
  | succ n ih =>
    let f := j.hom.left.toLRSHom
    let G := f.pullbackModules.obj F
    let η : F ⟶ (SheafOfModules.pushforward.{u} f.toRingSheafHom).obj G :=
      f.pullbackModulesAdj.unit.app F
    have hf : IsClosedEmbedding f.base := j.hom.left.isClosedEmbedding
    have hs : ∀ y, Function.Surjective (f.stalkMap y) := fun y ↦ j.hom.left.stalkMap_surjective y
    haveI : Epi η := f.epi_pullbackModulesAdj_unit_app hf hs F
    haveI hG : G.IsCoherent :=
      LocallyRingedSpace.isCoherent_pullbackModules_of_isCoherentStructureSheaf
        Y.obj.left.isCoherentStructureSheaf f F
    haveI : ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj G).IsCoherent :=
      isCoherent_pushforward_of_isClosedImmersion j.hom.left G
    haveI : (kernel η).IsCoherent := SheafOfModules.IsCoherent.kernel η
    let S := ShortComplex.mk (kernel.ι η) η (kernel.condition η)
    have hS : S.ShortExact := ⟨ShortComplex.exact_of_f_is_kernel S (kernelIsKernel η)⟩
    refine gagaMap_bijective_X₂_of_shortExact hS (fun q ↦ ih (kernel η) ?_ q)
      (fun q ↦ (bijective_gagaMap_pushforward_iff_of_isClosedImmersion j G q).2 (hY G hG q)) q
    intro x r hr
    rw [Module.mem_annihilator]
    intro m
    have hm := f.mem_smul_top_of_stalkFunctor_map_unit_eq_zero hf hs F x
      ((X.obj.left.toLocallyRingedSpace.stalkFunctor x).map (kernel.ι η) m)
      (LocallyRingedSpace.stalkFunctor_map_map_eq_zero _ _ (kernel.condition η) x m)
    apply LocallyRingedSpace.injective_stalk_of_mono (kernel.ι η) x
    rw [map_smul, map_zero]
    refine Submodule.smul_induction_on hm (fun a ha z _ ↦ ?_) (fun z₁ z₂ h₁ h₂ ↦ ?_)
    · have h := Module.mem_annihilator.1 (hF x (by rw [pow_succ]; exact Ideal.mul_mem_mul hr ha)) z
      rw [mul_smul] at h
      exact h
    · rw [smul_add, h₁, h₂, add_zero]

/-! ### The two inductive steps -/

section Steps

variable {Y : SchemeLFTℂ.{u}}
  (hT : ∀ T : Closeds Y.obj.left, T ≠ ⊤ →
    ∀ K : SheafOfModules.{u} Y.obj.left.toLocallyRingedSpace.ringSheaf, K.IsCoherent →
      (∀ y ∉ T, Subsingleton ((Y.obj.left.toLocallyRingedSpace.stalkFunctor y).obj K)) →
        ∀ q, Function.Bijective (gagaMap Y K q))
include hT

/-- **Generic isomorphisms.** Suppose the comparison maps are bijective for coherent sheaves on
`Y` vanishing off a proper closed subset. If `φ : F ⟶ A` is a morphism of coherent sheaves which
is bijective on stalks at the points of a nonempty open `U` and the comparison maps of `A` are
bijective, then so are those of `F`. -/
theorem gagaMap_bijective_of_bijective_stalkFunctor_map
    {F A : SheafOfModules.{u} Y.obj.left.toLocallyRingedSpace.ringSheaf} [F.IsCoherent]
    [A.IsCoherent] (φ : F ⟶ A) (U : Y.obj.left.Opens) (hU : (U : Set Y.obj.left).Nonempty)
    (hA : ∀ q, Function.Bijective (gagaMap Y A q))
    (hφ : ∀ y ∈ U, Function.Bijective ((Y.obj.left.toLocallyRingedSpace.stalkFunctor y).map φ))
    (q : ℕ) : Function.Bijective (gagaMap Y F q) := by
  let T : Closeds Y.obj.left := ⟨(U : Set Y.obj.left)ᶜ, U.isOpen.isClosed_compl⟩
  have hT' : T ≠ ⊤ := by
    intro h
    obtain ⟨y, hy⟩ := hU
    have hyT : y ∈ (T : Set Y.obj.left) := by rw [h]; trivial
    exact hyT hy
  have hK : ∀ q, Function.Bijective (gagaMap Y (kernel φ) q) := by
    refine hT T hT' _ (SheafOfModules.IsCoherent.kernel φ) fun y hy ↦ ?_
    have hyU : y ∈ U := not_not.1 hy
    have h0 : ∀ m : (Y.obj.left.toLocallyRingedSpace.stalkFunctor y).obj (kernel φ), m = 0 := by
      intro m
      apply LocallyRingedSpace.injective_stalk_of_mono (kernel.ι φ) y
      apply (hφ y hyU).1
      rw [LocallyRingedSpace.stalkFunctor_map_map_eq_zero _ _ (kernel.condition φ) y m,
        map_zero, map_zero]
    exact ⟨fun a b ↦ (h0 a).trans (h0 b).symm⟩
  have hC : ∀ q, Function.Bijective (gagaMap Y (cokernel φ) q) :=
    hT T hT' _ (SheafOfModules.IsCoherent.cokernel φ) fun y hy ↦
      (LocallyRingedSpace.subsingleton_stalk_cokernel_iff φ y).2 (hφ y (not_not.1 hy)).2
  let S₁ := ShortComplex.mk (Abelian.image.ι φ) (cokernel.π φ) (kernel.condition _)
  have hS₁ : S₁.ShortExact :=
    ⟨ShortComplex.exact_of_f_is_kernel S₁ (kernelIsKernel (cokernel.π φ))⟩
  have hI := gagaMap_bijective_X₁_of_shortExact hS₁ hA hC
  have w : kernel.ι φ ≫ Abelian.factorThruImage φ = 0 := by
    haveI : Mono (Abelian.image.ι φ) := equalizer.ι_mono
    refine (cancel_mono (Abelian.image.ι φ)).1 ?_
    exact (Category.assoc _ _ _).trans ((congrArg (kernel.ι φ ≫ ·) (Abelian.image.fac φ)).trans
      ((kernel.condition φ).trans zero_comp.symm))
  let S₂ := ShortComplex.mk (kernel.ι φ) (Abelian.factorThruImage φ) w
  have hS₂ : S₂.ShortExact :=
    ⟨ShortComplex.exact_of_f_is_kernel S₂
      (isKernelOfComp (Abelian.image.ι φ) φ (kernelIsKernel φ) w (Abelian.image.fac φ))⟩
  exact gagaMap_bijective_X₂_of_shortExact hS₂ hK hI q

/-- **Reducible case.** Suppose `Y` is reduced and the comparison maps are bijective for coherent
sheaves on `Y` vanishing off a proper closed subset. If `Y = Z₁ ∪ Z₂` for proper closed subsets
`Zᵢ`, then the comparison maps of every coherent sheaf on `Y` are bijective. -/
theorem gagaMap_bijective_of_union_eq_univ [IsReduced Y.obj.left] (Z₁ Z₂ : Closeds Y.obj.left)
    (h₁ : Z₁ ≠ ⊤) (h₂ : Z₂ ≠ ⊤) (hcov : (Z₁ : Set Y.obj.left) ∪ Z₂ = Set.univ)
    (G : SheafOfModules.{u} Y.obj.left.toLocallyRingedSpace.ringSheaf) [G.IsCoherent] (q : ℕ) :
    Function.Bijective (gagaMap Y G q) := by
  let i := (Scheme.IdealSheafData.vanishingIdeal Z₂).subschemeι
  let f := i.toLRSHom
  have hf : IsClosedEmbedding f.base := i.isClosedEmbedding
  have hs : ∀ y, Function.Surjective (f.stalkMap y) := fun y ↦ i.stalkMap_surjective y
  have hrange : Set.range f.base = Z₂ := (Scheme.IdealSheafData.range_subschemeι _).trans
    (Scheme.IdealSheafData.coe_support_vanishingIdeal Z₂)
  haveI : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal Z₂).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian i
  let P := f.pullbackModules.obj G
  haveI : P.IsCoherent := LocallyRingedSpace.isCoherent_pullbackModules_of_isCoherentStructureSheaf
    (Scheme.isCoherentStructureSheaf _) f G
  haveI : ((SheafOfModules.pushforward.{u} f.toRingSheafHom).obj P).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion i P
  let η : G ⟶ (SheafOfModules.pushforward.{u} f.toRingSheafHom).obj P :=
    f.pullbackModulesAdj.unit.app G
  haveI : Epi η := f.epi_pullbackModulesAdj_unit_app hf hs G
  let S := ShortComplex.mk (kernel.ι η) η (kernel.condition η)
  have hS : S.ShortExact := ⟨ShortComplex.exact_of_f_is_kernel S (kernelIsKernel η)⟩
  refine gagaMap_bijective_X₂_of_shortExact hS ?_ ?_ q
  · refine hT Z₁ h₁ _ (SheafOfModules.IsCoherent.kernel η) fun y hy ↦ ?_
    have hI : f.pushforwardStalkIdeal y = ⊥ := by
      refine i.pushforwardStalkIdeal_eq_bot
        (V := ⟨(Z₁ : Set Y.obj.left)ᶜ, Z₁.isClosed.isOpen_compl⟩) hy fun z hz ↦ ?_
      rw [hrange]
      exact ((Set.eq_univ_iff_forall.1 hcov) z).resolve_left hz
    have h0 : ∀ m : (Y.obj.left.toLocallyRingedSpace.stalkFunctor y).obj (kernel η), m = 0 := by
      intro m
      apply LocallyRingedSpace.injective_stalk_of_mono (kernel.ι η) y
      have hm := f.mem_smul_top_of_stalkFunctor_map_unit_eq_zero hf hs G y
        ((Y.obj.left.toLocallyRingedSpace.stalkFunctor y).map (kernel.ι η) m)
        (LocallyRingedSpace.stalkFunctor_map_map_eq_zero _ _ (kernel.condition η) y m)
      rw [hI, Submodule.bot_smul, Submodule.mem_bot] at hm
      rw [hm, map_zero]
    exact ⟨fun a b ↦ (h0 a).trans (h0 b).symm⟩
  · exact hT Z₂ h₂ _ inferInstance fun y hy ↦
      f.subsingleton_stalk_pushforward hf.isClosed_range y (by rwa [hrange]) P

end Steps

/-! ### The noetherian induction -/

/-- **Generic GAGA on closed integral subschemes.** For every closed immersion `Y ⟶ X` over `ℂ`
with `Y` integral and every coherent sheaf `F` on `Y`, there are a nonempty open `U ⊆ Y`, a
coherent sheaf `A` on `Y` whose comparison maps `Hᵠ(Y, A) → Hᵠ(Y^an, A^an)` are bijective and a
morphism `φ : F ⟶ A` which is bijective on stalks at the points of `U`. -/
def GenericGAGA (X : SchemeLFTℂ.{u}) : Prop :=
  ∀ (Y : SchemeLFTℂ.{u}) (j : Y ⟶ X), IsClosedImmersion j.hom.left → IsIntegral Y.obj.left →
    ∀ F : SheafOfModules.{u} Y.obj.left.toLocallyRingedSpace.ringSheaf, F.IsCoherent →
      ∃ (U : Y.obj.left.Opens) (A : SheafOfModules.{u} Y.obj.left.toLocallyRingedSpace.ringSheaf)
        (φ : F ⟶ A), (U : Set Y.obj.left).Nonempty ∧ A.IsCoherent ∧
          (∀ q, Function.Bijective (gagaMap Y A q)) ∧
          ∀ y ∈ U, Function.Bijective ((Y.obj.left.toLocallyRingedSpace.stalkFunctor y).map φ)

variable (X) in
/-- **GAGA by noetherian induction.** Let `X` be a scheme locally of finite type over `ℂ` with
quasi-compact underlying space, satisfying `ComplexAnalytic.GenericGAGA`. Then for every closed
subset `Z ⊆ X` and every coherent sheaf `F` on `X` whose stalks vanish off `Z`, the comparison
maps `Hᵠ(X, F) → Hᵠ(X^an, F^an)` are bijective. -/
theorem gagaMap_bijective_of_forall_notMem [CompactSpace X.obj.left] (H : GenericGAGA X)
    (Z : Closeds X.obj.left) (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf)
    [F.IsCoherent]
    (hF : ∀ x ∉ Z, Subsingleton ((X.obj.left.toLocallyRingedSpace.stalkFunctor x).obj F))
    (q : ℕ) : Function.Bijective (gagaMap X F q) := by
  haveI : IsNoetherian X.obj.left := {}
  induction Z using WellFoundedLT.induction generalizing F q with
  | _ Z ih =>
  let Y := X.reducedSubscheme Z
  let ι := X.reducedSubschemeι Z
  have hι : IsClosedEmbedding ι.hom.left.base := ι.hom.left.isClosedEmbedding
  -- coherent sheaves on `Y` vanishing off a proper closed subset
  have hT : ∀ T : Closeds Y.obj.left, T ≠ ⊤ →
      ∀ K : SheafOfModules.{u} Y.obj.left.toLocallyRingedSpace.ringSheaf, K.IsCoherent →
        (∀ y ∉ T, Subsingleton ((Y.obj.left.toLocallyRingedSpace.stalkFunctor y).obj K)) →
          ∀ q, Function.Bijective (gagaMap Y K q) := by
    intro T hT K hK hKT q
    let Z' : Closeds X.obj.left := ⟨ι.hom.left.base '' T, hι.isClosedMap _ T.isClosed⟩
    have hZ' : Z' < Z := by
      refine lt_of_le_of_ne ?_ fun h ↦ hT ?_
      · rintro _ ⟨y, -, rfl⟩
        rw [← SetLike.mem_coe, ← X.range_reducedSubschemeι Z]
        exact ⟨y, rfl⟩
      · refine Closeds.ext (Set.eq_univ_of_forall fun y ↦ ?_)
        have hy : ι.hom.left.base y ∈ (Z' : Set X.obj.left) := by
          rw [h, ← X.range_reducedSubschemeι Z]
          exact ⟨y, rfl⟩
        obtain ⟨y', hy', e⟩ := hy
        rwa [← hι.injective e]
    haveI := isCoherent_pushforward_of_isClosedImmersion ι.hom.left K
    refine (bijective_gagaMap_pushforward_iff_of_isClosedImmersion ι K q).1
      (ih Z' hZ' _ (fun x hx ↦ ?_) q)
    by_cases hx' : x ∈ Set.range ι.hom.left.base
    · obtain ⟨y, rfl⟩ := hx'
      haveI := hKT y fun hy ↦ hx ⟨y, hy, rfl⟩
      exact (ι.hom.left.toLRSHom.bijective_stalkPushforwardModules hι.isInducing K y).1.subsingleton
    · exact ι.hom.left.toLRSHom.subsingleton_stalk_pushforward hι.isClosed_range x hx' K
  -- all coherent sheaves on `Y`
  have hY : ∀ G : SheafOfModules.{u} Y.obj.left.toLocallyRingedSpace.ringSheaf, G.IsCoherent →
      ∀ q, Function.Bijective (gagaMap Y G q) := by
    intro G hG q
    by_cases hirr : IrreducibleSpace Y.obj.left
    · haveI : IsIntegral Y.obj.left := isIntegral_of_irreducibleSpace_of_isReduced _
      obtain ⟨U, A, φ, hU, hA, hAq, hφ⟩ := H Y ι inferInstance inferInstance G hG
      exact gagaMap_bijective_of_bijective_stalkFunctor_map hT φ U hU hAq hφ q
    by_cases hne : Nonempty Y.obj.left
    · have hpre : ¬ IsPreirreducible (Set.univ : Set Y.obj.left) := fun h ↦
        hirr ((irreducibleSpace_def _).2 ⟨Set.univ_nonempty, h⟩)
      rw [isPreirreducible_iff_isClosed_union_isClosed] at hpre
      push Not at hpre
      obtain ⟨z₁, z₂, hz₁, hz₂, hcov, hn₁, hn₂⟩ := hpre
      refine gagaMap_bijective_of_union_eq_univ hT ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
        (fun h ↦ hn₁ (congrArg (fun C : Closeds Y.obj.left ↦ (C : Set Y.obj.left)) h).ge)
        (fun h ↦ hn₂ (congrArg (fun C : Closeds Y.obj.left ↦ (C : Set Y.obj.left)) h).ge)
        (Set.univ_subset_iff.1 hcov) G q
    · exact gagaMap_bijective_of_isZero (LocallyRingedSpace.isZero_of_forall_subsingleton_stalk
        G fun y ↦ (hne ⟨y⟩).elim) q
  obtain ⟨n, hn⟩ := exists_pow_pushforwardStalkIdeal_le_annihilator ι.hom.left F fun x hx ↦
    hF x (by rwa [X.range_reducedSubschemeι Z] at hx)
  exact gagaMap_bijective_of_pow_le_annihilator ι hY n F hn q

variable (X) in
/-- **GAGA from generic GAGA on closed integral subschemes.** Let `X` be a scheme locally of
finite type over `ℂ` with quasi-compact underlying space, satisfying
`ComplexAnalytic.GenericGAGA`. Then for every coherent sheaf `F` on `X` the comparison maps
`Hᵠ(X, F) → Hᵠ(X^an, F^an)` are bijective. -/
theorem gagaMap_bijective_of_genericGAGA [CompactSpace X.obj.left] (H : GenericGAGA X)
    (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent] (q : ℕ) :
    Function.Bijective (gagaMap X F q) :=
  gagaMap_bijective_of_forall_notMem X H ⊤ F (fun _ hx ↦ (hx trivial).elim) q

/-- **GAGA for proper schemes from generic GAGA.** For a proper scheme `X` over `ℂ` satisfying
`ComplexAnalytic.GenericGAGA` and a coherent sheaf `F` on `X`, the comparison maps
`Hᵠ(X, F) → Hᵠ(X^an, F^an)` are bijective. -/
theorem IsProperℂ.gagaMap_bijective_of_genericGAGA (hX : IsProperℂ X) (H : GenericGAGA X)
    (F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [F.IsCoherent] (q : ℕ) :
    Function.Bijective (gagaMap X F q) :=
  haveI := hX.compactSpace
  ComplexAnalytic.gagaMap_bijective_of_genericGAGA X H F q

end ComplexAnalytic

end
