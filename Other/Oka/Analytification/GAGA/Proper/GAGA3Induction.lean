/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.SupportAnnihilatorScheme
public import Other.Oka.Analytification.GAGA.ClosedImmersionCoherent
public import Other.Oka.Analytification.GAGA.ClosedImmersionIdeal
public import Other.Oka.Analytification.GAGA.Proper.CompactSpace
public import Other.Oka.Analytification.GAGA.Proper.GAGA2
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.ArtinRees

/-!
# Noetherian induction for GAGA-3

Let `X` be a proper scheme over `ℂ` with comparison morphism `π : X^an ⟶ X`. We show that every
coherent sheaf on `X^an` is the analytification of a coherent sheaf on `X`
(`ComplexAnalytic.exists_iso_analytificationModules_of_generic`), assuming

- `ComplexAnalytic.AnalytificationFullOnCoherent X` (GAGA-2): every morphism `F^an ⟶ G^an`
  between analytifications of coherent sheaves is the analytification of a morphism `F ⟶ G`;
- `ComplexAnalytic.GenericAlgebraization X`: for every irreducible closed subscheme `T` of `X`
  and every coherent `M` on `T^an` there are a coherent `B` on `T` and `ψ : M ⟶ B^an` which is
  bijective on stalks over a nonempty open subset of `T`.

The proof is a noetherian induction on the closed subsets `Z ⊆ X`, proving
`ComplexAnalytic.AlgebraizesOver X Z`: every coherent `M` on `X^an` with vanishing stalks off
`π⁻¹ Z` is algebraic. The key step (`ComplexAnalytic.isAnalytificationOfCoherent_of_hom`) is:
if `ψ : M ⟶ B^an` is bijective on stalks off `π⁻¹ W` and `ComplexAnalytic.AlgebraizesOver X W`
holds, then `M` is algebraic. Writing `𝓘` for the ideal of the reduced subscheme on `W` and
`K = ker ψ`, a power `𝓘ᴺ` kills `K` (Rückert's Nullstellensatz,
`ComplexAnalytic.AnalyticSpace.exists_pow_map_pushforwardStalkIdeal_le_annihilator`), so by
Artin–Rees in the noetherian local rings of `X^an`, `𝓘ᵏ M_x ∩ K_x = 0` for `k ≫ 0`; as this
condition spreads to a neighbourhood, compactness of `X^an` gives a uniform `k`. Then
`M ⟶ B^an ⊕ M/𝓘ᵏM` is injective with cokernel vanishing off `π⁻¹ W`, and `M/𝓘ᵏM` and the
cokernel are algebraic by hypothesis, so `M` is the kernel of the analytification of a morphism
of coherent sheaves.

For the induction step, a coherent `M` vanishing off `π⁻¹ Z` is killed by a power `𝓘_Zⁿ`, hence
is the pushforward of a coherent sheaf on the closed subscheme `T = V(𝓘_Zⁿ)`
(`AlgebraicGeometry.LocallyRingedSpace.Hom.isIso_pullbackModulesAdj_unit_app_of_smul_eq_zero`).
If `Z` is irreducible, so is `T`, and the generic hypothesis provides `ψ`
(`ComplexAnalytic.isAnalytificationOfCoherent_of_isIrreducible`). If `Z ⊆ Z₁ ∪ Z₂`, the unit
`M ⟶ M/𝓘_{Z₂}ⁿM` is bijective on stalks off `π⁻¹ Z₁` for `n ≫ 0`
(`ComplexAnalytic.isAnalytificationOfCoherent_of_subset_union`).

Combined with GAGA-2 for proper schemes (`ComplexAnalytic.gaga₂_of_isProperℂ`), this gives GAGA-3
assuming `ComplexAnalytic.RelativeAnalyticSerre` and `ComplexAnalytic.GenericAlgebraization X`
(`ComplexAnalytic.gaga₃_of_isProperℂ`).
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Topology

universe u

noncomputable section

namespace ComplexAnalytic

variable {X : SchemeLFTℂ.{u}}

/-- A sheaf of modules on `X^an` is **algebraic** if it is isomorphic to the analytification of a
coherent sheaf on `X`. -/
def IsAnalytificationOfCoherent
    (M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf) : Prop :=
  ∃ F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf,
    F.IsCoherent ∧ Nonempty ((analytificationModules X).obj F ≅ M)

variable (X) in
/-- **GAGA-3 over a closed subset** `Z ⊆ X`: every coherent sheaf on `X^an` whose stalks vanish
at the points of `X^an` not lying over `Z` is algebraic. -/
def AlgebraizesOver (Z : Closeds X.obj.left) : Prop :=
  ∀ M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf,
    M.IsCoherent → (∀ x, (analytificationπLRS X).base x ∉ Z →
      Subsingleton (((analytification.obj X).toLocallyRingedSpace.stalkFunctor x).obj M)) →
    IsAnalytificationOfCoherent M

variable (X) in
/-- **GAGA-2 on coherent sheaves**, as a hypothesis: for coherent sheaves `F`, `G` on `X`, every
morphism `F^an ⟶ G^an` is the analytification of a morphism `F ⟶ G`. -/
def AnalytificationFullOnCoherent : Prop :=
  ∀ F G : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf, F.IsCoherent →
    G.IsCoherent → Function.Surjective ((analytificationModules X).map : (F ⟶ G) → _)

variable (X) in
/-- **Generic algebraization on irreducible closed subschemes**, as a hypothesis: for every closed
immersion `T ⟶ X` with `T` irreducible and every coherent sheaf `M` on `T^an`, there are a
nonempty open `U ⊆ T`, a coherent sheaf `B` on `T` and a morphism `ψ : M ⟶ B^an` which is
bijective on stalks at the points of `T^an` lying over `U`. -/
def GenericAlgebraization : Prop :=
  ∀ (T : SchemeLFTℂ.{u}) (i : T ⟶ X), IsClosedImmersion i.hom.left → IrreducibleSpace T.obj.left →
    ∀ M : SheafOfModules.{u} (analytification.obj T).toLocallyRingedSpace.ringSheaf,
      M.IsCoherent →
      ∃ (U : T.obj.left.Opens) (B : SheafOfModules.{u} T.obj.left.toLocallyRingedSpace.ringSheaf)
        (ψ : M ⟶ (analytificationModules T).obj B), (U : Set T.obj.left).Nonempty ∧
          B.IsCoherent ∧ ∀ z : analytification.obj T, (analytificationπLRS T).base z ∈ U →
            Function.Bijective
              (((analytification.obj T).toLocallyRingedSpace.stalkFunctor z).map ψ)

/-- A zero sheaf on `X^an` is algebraic. -/
lemma isAnalytificationOfCoherent_of_isZero
    {M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf}
    (hM : IsZero M) : IsAnalytificationOfCoherent M := by
  haveI : (SheafOfModules.unit X.obj.left.toLocallyRingedSpace.ringSheaf).IsCoherent :=
    X.obj.left.isCoherentStructureSheaf
  let U := SheafOfModules.unit X.obj.left.toLocallyRingedSpace.ringSheaf
  have hK : IsZero (kernel (𝟙 U)) := by
    have h : kernel.ι (𝟙 U) = 0 := by simpa using kernel.condition (𝟙 U)
    exact IsZero.of_mono_eq_zero _ h
  exact ⟨kernel (𝟙 U), SheafOfModules.IsCoherent.kernel _,
    ⟨((analytificationModules X).map_isZero hK).iso hM⟩⟩

/-! ### Closed subschemes and their analytic ideals -/

section Ideal

variable (X) (J : X.obj.left.IdealSheafData)

/-- The stalk at `x ∈ X^an` of the ideal of `V(J)^an`. -/
abbrev analyticIdeal (x : analytification.obj X) :
    Ideal ((analytification.obj X).toLocallyRingedSpace.presheaf.stalk x) :=
  (analytification.map (X.subschemeι J)).toLRSHom.pushforwardStalkIdeal x

/-- The ideal of `V(Jⁿ)^an` is the `n`-th power of the ideal of `V(J)^an`. -/
lemma analyticIdeal_pow (n : ℕ) (x : analytification.obj X) :
    analyticIdeal X (J ^ n) x = analyticIdeal X J x ^ n :=
  pushforwardStalkIdeal_analytification_map_subschemeι_pow X J n x

/-- Off `π⁻¹ V(J)`, the stalks of a pushforward from `V(J)^an` vanish. -/
lemma subsingleton_stalk_pushforward_subschemeι (x : analytification.obj X)
    (hx : (analytificationπLRS X).base x ∉ J.support)
    (G : SheafOfModules.{u} (analytification.obj (X.subscheme J)).toLocallyRingedSpace.ringSheaf) :
    Subsingleton (((analytification.obj X).toLocallyRingedSpace.stalkFunctor x).obj
      ((SheafOfModules.pushforward.{u}
        (analytification.map (X.subschemeι J)).toLRSHom.toRingSheafHom).obj G)) := by
  refine (analytification.map (X.subschemeι J)).toLRSHom.subsingleton_stalk_pushforward
    (isClosedEmbedding_analytification_map _).isClosed_range x (fun h ↦ hx ?_) G
  rw [range_analytification_map_of_isClosedImmersion, SchemeLFTℂ.range_subschemeι] at h
  exact h

/-- The pushforward of the pullback of a coherent sheaf along the analytification of a closed
immersion is coherent. -/
lemma isCoherent_pushforward_pullbackModules {T : SchemeLFTℂ.{u}} (i : T ⟶ X)
    [IsClosedImmersion i.hom.left]
    (M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf)
    [M.IsCoherent] :
    ((SheafOfModules.pushforward.{u} (analytification.map i).toLRSHom.toRingSheafHom).obj
      ((analytification.map i).toLRSHom.pullbackModules.obj M)).IsCoherent := by
  haveI := LocallyRingedSpace.isCoherent_pullbackModules_of_isCoherentStructureSheaf
    (analytification.obj T).isCoherentStructureSheaf (analytification.map i).toLRSHom M
  exact isCoherent_pushforward_analytification_map i _

variable {X} in
/-- **Rückert's Nullstellensatz on a compact `X^an`**: a coherent sheaf vanishing off `π⁻¹ V(J)` is
killed by a power of the ideal of `V(J)^an`. -/
lemma exists_pow_analyticIdeal_le_annihilator [CompactSpace (analytification.obj X)]
    (M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf)
    [M.IsCoherent] (hM : ∀ x, (analytificationπLRS X).base x ∉ J.support →
      Subsingleton (((analytification.obj X).toLocallyRingedSpace.stalkFunctor x).obj M)) :
    ∃ N : ℕ, ∀ x, analyticIdeal X J x ^ N ≤
      Module.annihilator _
        (((analytification.obj X).toLocallyRingedSpace.stalkFunctor x).obj M) := by
  obtain ⟨N, hN⟩ := AnalyticSpace.exists_pow_map_pushforwardStalkIdeal_le_annihilator
    (analytificationπLRS X) J.subschemeι M fun x hx ↦
      hM x fun h ↦ hx (by rw [Scheme.IdealSheafData.range_subschemeι]; exact h)
  refine ⟨N, fun x ↦ ?_⟩
  rw [analyticIdeal, pushforwardStalkIdeal_analytification_map]
  exact hN x

/-- The kernel of the unit `M ⟶ (ι^an)_* (ι^an)^* M` of `ι : V(J) ⟶ X`, at a stalk, is
`𝓘_x M_x`. -/
lemma stalkFunctor_map_unit_eq_zero_iff
    (M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf)
    (x : analytification.obj X)
    (m : ((analytification.obj X).toLocallyRingedSpace.stalkFunctor x).obj M) :
    ((analytification.obj X).toLocallyRingedSpace.stalkFunctor x).map
        ((analytification.map (X.subschemeι J)).toLRSHom.pullbackModulesAdj.unit.app M) m = 0 ↔
      m ∈ analyticIdeal X J x •
        (⊤ : Submodule ((analytification.obj X).toLocallyRingedSpace.presheaf.stalk x) _) := by
  let f := (analytification.map (X.subschemeι J)).toLRSHom
  refine ⟨f.mem_smul_top_of_stalkFunctor_map_unit_eq_zero
    (isClosedEmbedding_analytification_map _) (surjective_stalkMap_analytification_map _) M x m,
    fun hm ↦ ?_⟩
  refine Submodule.smul_induction_on hm (fun a ha n _ ↦ ?_) (fun n₁ n₂ h₁ h₂ ↦ ?_)
  · erw [map_smul]
    exact f.smul_eq_zero_of_mem_pushforwardStalkIdeal _ x a ha _
  · erw [map_add, h₁, h₂, add_zero]

end Ideal

/-! ### The key step -/

section Key

/-- If `M` embeds into `B^an ⊞ G^an` with cokernel isomorphic to `H^an`, for coherent `B`, `G`,
`H`, and analytification is full on coherent sheaves, then `M` is algebraic. -/
lemma isAnalytificationOfCoherent_of_mono (h2 : AnalytificationFullOnCoherent X)
    {M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf}
    {B G H : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf}
    (hB : B.IsCoherent) (hG : G.IsCoherent) (hH : H.IsCoherent)
    (Φ : M ⟶ (analytificationModules X).obj B ⊞ (analytificationModules X).obj G) [Mono Φ]
    (eH : (analytificationModules X).obj H ≅ cokernel Φ) :
    IsAnalytificationOfCoherent M := by
  let an := analytificationModules X
  haveI : PreservesBinaryBiproduct B G an := preservesBinaryBiproduct_of_preservesBinaryProduct an
  haveI := SheafOfModules.IsCoherent.isFiniteType B
  haveI := SheafOfModules.IsCoherent.isFiniteType G
  haveI := LocallyRingedSpace.isFiniteType_biprod B G
  haveI hE : (B ⊞ G).IsCoherent := SheafOfModules.IsCoherent.biprod
  obtain ⟨g, hg⟩ := h2 (B ⊞ G) H hE hH ((an.mapBiprod B G).hom ≫ cokernel.π Φ ≫ eH.inv)
  have i1 : an.obj (kernel g) ≅ kernel (an.map g) := PreservesKernel.iso an g
  have i2 : kernel (an.map g) ≅ kernel ((an.mapBiprod B G).hom ≫ cokernel.π Φ ≫ eH.inv) :=
    kernelIsoOfEq hg
  have i3 : kernel ((an.mapBiprod B G).hom ≫ cokernel.π Φ ≫ eH.inv) ≅
      kernel (cokernel.π Φ ≫ eH.inv) := kernelIsIsoComp _ _
  have i4 : kernel (cokernel.π Φ ≫ eH.inv) ≅ kernel (cokernel.π Φ) :=
    kernelCompMono (cokernel.π Φ) eH.inv
  have i5 : M ≅ kernel (cokernel.π Φ) :=
    IsLimit.conePointUniqueUpToIso (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel Φ))
      (limit.isLimit _)
  exact ⟨kernel g, SheafOfModules.IsCoherent.kernel g, ⟨i1 ≪≫ i2 ≪≫ i3 ≪≫ i4 ≪≫ i5.symm⟩⟩

variable [CompactSpace (analytification.obj X)]

/-- **The key step.** Let `W ⊆ X` be closed with `ComplexAnalytic.AlgebraizesOver X W`, and assume
GAGA-2 on `X`. If a coherent sheaf `M` on `X^an` admits a morphism `ψ : M ⟶ B^an` to the
analytification of a coherent sheaf which is bijective on stalks at the points not lying over
`W`, then `M` is algebraic. -/
theorem isAnalytificationOfCoherent_of_hom (h2 : AnalytificationFullOnCoherent X)
    (W : Closeds X.obj.left) (hW : AlgebraizesOver X W)
    (M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf) [M.IsCoherent]
    (B : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf) [hB : B.IsCoherent]
    (ψ : M ⟶ (analytificationModules X).obj B)
    (hψ : ∀ x, (analytificationπLRS X).base x ∉ W →
      Function.Bijective (((analytification.obj X).toLocallyRingedSpace.stalkFunctor x).map ψ)) :
    IsAnalytificationOfCoherent M := by
  classical
  let Y := (analytification.obj X).toLocallyRingedSpace
  let J := Scheme.IdealSheafData.vanishingIdeal W
  have hJ : ∀ x : X.obj.left, x ∉ J.support ↔ x ∉ W := fun x ↦ by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let f : ∀ n : ℕ, _ ⟶ Y := fun n ↦ (analytification.map (X.subschemeι (J ^ n))).toLRSHom
  let η : ∀ n : ℕ, M ⟶ (SheafOfModules.pushforward.{u} (f n).toRingSheafHom).obj
      ((f n).pullbackModules.obj M) := fun n ↦ (f n).pullbackModulesAdj.unit.app M
  have hη : ∀ n x m, (Y.stalkFunctor x).map (η n) m = 0 ↔
      m ∈ analyticIdeal X J x ^ n • (⊤ : Submodule (Y.presheaf.stalk x) _) := fun n x m ↦ by
    rw [← analyticIdeal_pow]
    exact stalkFunctor_map_unit_eq_zero_iff X (J ^ n) M x m
  haveI hMn : ∀ n, ((SheafOfModules.pushforward.{u} (f n).toRingSheafHom).obj
      ((f n).pullbackModules.obj M)).IsCoherent := fun n ↦
    isCoherent_pushforward_pullbackModules X (X.subschemeι (J ^ n)) M
  clear_value η
  -- the kernel of `ψ` is killed by a power of the ideal of `W`
  haveI := isCoherent_analytificationModules X B
  haveI : (kernel ψ).IsCoherent := SheafOfModules.IsCoherent.kernel ψ
  obtain ⟨N, hN⟩ := exists_pow_analyticIdeal_le_annihilator J (kernel ψ) fun x hx ↦ by
    refine ⟨fun a b ↦ ?_⟩
    have h0 : ∀ c : (Y.stalkFunctor x).obj (kernel ψ), c = 0 := fun c ↦
      LocallyRingedSpace.injective_stalk_of_mono (kernel.ι ψ) x ((hψ x ((hJ _).1 hx)).1
        ((LocallyRingedSpace.stalkFunctor_map_map_eq_zero _ _ (kernel.condition ψ) x c).trans
          (by rw [map_zero, map_zero])))
    rw [h0 a, h0 b]
  -- by Artin–Rees, `𝓘ᵏ M ∩ ker ψ = 0` for `k ≫ 0`
  haveI : CompactSpace Y := ‹CompactSpace (analytification.obj X)›
  obtain ⟨k₀, hk₀⟩ := LocallyRingedSpace.exists_forall_pow_smul_top_inf_ker_eq_bot ψ η
    (analyticIdeal X J) hη N hN
  let k := k₀ + 1
  have hk : ∀ y, analyticIdeal X J y ^ k • ⊤ ⊓
      LinearMap.ker ((Y.stalkFunctor y).map ψ).hom = ⊥ := hk₀ k (Nat.le_succ _)
  -- `M / 𝓘ᵏ M` is algebraic
  obtain ⟨G, hG, ⟨eG⟩⟩ := hW _ (hMn k) fun x hx ↦
    subsingleton_stalk_pushforward_subschemeι X (J ^ k) x
      (by rw [Scheme.IdealSheafData.support_pow _ _ (Nat.succ_ne_zero _)]; exact (hJ _).2 hx) _
  haveI := hG
  -- the embedding `M ⟶ B^an ⊞ G^an`
  let an := analytificationModules X
  haveI : PreservesBinaryBiproduct B G an := preservesBinaryBiproduct_of_preservesBinaryProduct an
  let Φ₀ : M ⟶ an.obj B ⊞ an.obj G := biprod.lift ψ (η k ≫ eG.inv)
  have hΦ₀ : ∀ x m, (Y.stalkFunctor x).map Φ₀ m = 0 → m = 0 := by
    intro x m hm
    have h1 : (Y.stalkFunctor x).map ψ m = 0 := by
      rw [← biprod.lift_fst ψ (η k ≫ eG.inv), Functor.map_comp, ConcreteCategory.comp_apply, hm,
        map_zero]
    have h2 : (Y.stalkFunctor x).map (η k) m = 0 := by
      have h3 : (Y.stalkFunctor x).map (η k ≫ eG.inv) m = 0 := by
        rw [← biprod.lift_snd ψ (η k ≫ eG.inv), Functor.map_comp, ConcreteCategory.comp_apply,
          hm, map_zero]
      rw [Functor.map_comp, ConcreteCategory.comp_apply] at h3
      rw [← ((Y.stalkFunctor x).mapIso eG).toLinearEquiv.symm.map_eq_zero_iff]
      exact h3
    have hmem : m ∈ analyticIdeal X J x ^ k • ⊤ ⊓
        LinearMap.ker ((Y.stalkFunctor x).map ψ).hom := ⟨(hη k x m).1 h2, h1⟩
    rw [hk x] at hmem
    exact hmem
  haveI : Mono Φ₀ := LocallyRingedSpace.mono_of_forall_injective_stalk Φ₀ fun x ↦
    (injective_iff_map_eq_zero _).2 (hΦ₀ x)
  -- the cokernel of `Φ₀` is algebraic
  haveI := isCoherent_analytificationModules X G
  haveI := SheafOfModules.IsCoherent.isFiniteType (an.obj B)
  haveI := SheafOfModules.IsCoherent.isFiniteType (an.obj G)
  haveI := LocallyRingedSpace.isFiniteType_biprod (an.obj B) (an.obj G)
  haveI : (an.obj B ⊞ an.obj G).IsCoherent := SheafOfModules.IsCoherent.biprod
  haveI : (cokernel Φ₀).IsCoherent := SheafOfModules.IsCoherent.cokernel Φ₀
  obtain ⟨H, hH, ⟨eH⟩⟩ := hW (cokernel Φ₀) inferInstance fun x hx ↦ by
    haveI : Subsingleton ((Y.stalkFunctor x).obj (an.obj G)) :=
      ((Y.stalkFunctor x).mapIso eG).toLinearEquiv.toEquiv.subsingleton_congr.2
        (subsingleton_stalk_pushforward_subschemeι X (J ^ k) x
          (by rw [Scheme.IdealSheafData.support_pow _ _ (Nat.succ_ne_zero _)]
              exact (hJ _).2 hx) _)
    exact (LocallyRingedSpace.subsingleton_stalk_cokernel_iff Φ₀ x).2
      (LocallyRingedSpace.surjective_stalkFunctor_map_biprod_lift _ _ x (hψ x hx).2)
  exact isAnalytificationOfCoherent_of_mono h2 hB hG hH Φ₀ eH

end Key

/-! ### The inductive steps -/

section Steps

variable [CompactSpace (analytification.obj X)]

/-- **The reducible step.** Let `Z ⊆ Z₁ ∪ Z₂` be closed subsets of `X` such that
`ComplexAnalytic.AlgebraizesOver X Zᵢ` holds for `i = 1, 2`, and assume GAGA-2 on `X`. Then every
coherent sheaf on `X^an` whose stalks vanish off `π⁻¹ Z` is algebraic. -/
theorem isAnalytificationOfCoherent_of_subset_union (h2 : AnalytificationFullOnCoherent X)
    (Z Z₁ Z₂ : Closeds X.obj.left) (hcov : (Z : Set X.obj.left) ⊆ Z₁ ∪ Z₂)
    (h₁ : AlgebraizesOver X Z₁) (h₂ : AlgebraizesOver X Z₂)
    (M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf) [M.IsCoherent]
    (hM : ∀ x, (analytificationπLRS X).base x ∉ Z →
      Subsingleton (((analytification.obj X).toLocallyRingedSpace.stalkFunctor x).obj M)) :
    IsAnalytificationOfCoherent M := by
  let Y := (analytification.obj X).toLocallyRingedSpace
  let J := Scheme.IdealSheafData.vanishingIdeal Z
  let J₂ := Scheme.IdealSheafData.vanishingIdeal Z₂
  have hJ : ∀ (C : Closeds X.obj.left) (p : X.obj.left),
      p ∉ (Scheme.IdealSheafData.vanishingIdeal C).support ↔ p ∉ C := fun C p ↦ by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨N, hN⟩ := exists_pow_analyticIdeal_le_annihilator J M fun x hx ↦
    hM x ((hJ Z _).1 hx)
  let n := N + 1
  let f := (analytification.map (X.subschemeι (J₂ ^ n))).toLRSHom
  let η := f.pullbackModulesAdj.unit.app M
  have hP := isCoherent_pushforward_pullbackModules X (X.subschemeι (J₂ ^ n)) M
  have hsupp : ∀ x, (analytificationπLRS X).base x ∉ Z₂ →
      (analytificationπLRS X).base x ∉ (J₂ ^ n).support := fun x hx ↦ by
    rw [Scheme.IdealSheafData.support_pow _ _ (Nat.succ_ne_zero _)]
    exact (hJ Z₂ _).2 hx
  obtain ⟨G, hG, ⟨e⟩⟩ := h₂ _ hP fun x hx ↦
    subsingleton_stalk_pushforward_subschemeι X (J₂ ^ n) x (hsupp x hx) _
  haveI : Epi η := f.epi_pullbackModulesAdj_unit_app (isClosedEmbedding_analytification_map _)
    (surjective_stalkMap_analytification_map _) M
  refine @isAnalytificationOfCoherent_of_hom _ _ h2 Z₁ h₁ M _ G hG (η ≫ e.inv) fun x hx ↦ ?_
  have hinj : Function.Injective ((Y.stalkFunctor x).map η) := by
    refine (injective_iff_map_eq_zero _).2 fun m hm ↦ ?_
    have hm' := (stalkFunctor_map_unit_eq_zero_iff X (J₂ ^ n) M x m).1 hm
    rw [analyticIdeal_pow] at hm'
    have hle : analyticIdeal X J₂ x ≤ analyticIdeal X J x := by
      rw [analyticIdeal, analyticIdeal, pushforwardStalkIdeal_analytification_map,
        pushforwardStalkIdeal_analytification_map]
      exact Ideal.map_mono (Scheme.IdealSheafData.pushforwardStalkIdeal_subschemeι_vanishingIdeal_le
        (V := ⟨(Z₁ : Set X.obj.left)ᶜ, Z₁.isClosed.isOpen_compl⟩) hx
        fun p ⟨hpZ, hpV⟩ ↦ (hcov hpZ).resolve_left hpV)
    have hann : analyticIdeal X J₂ x ^ n ≤ Module.annihilator _ ((Y.stalkFunctor x).obj M) :=
      (Ideal.pow_right_mono hle n).trans ((Ideal.pow_le_pow_right (Nat.le_succ N)).trans (hN x))
    have := Submodule.smul_mono_left (N := ⊤) hann hm'
    rwa [← Submodule.annihilator_top, Submodule.annihilator_smul, Submodule.mem_bot] at this
  have hbij : Function.Bijective ((Y.stalkFunctor x).map η) :=
    ⟨hinj, LocallyRingedSpace.surjective_stalk_of_epi η x⟩
  rw [Functor.map_comp, ConcreteCategory.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).comp hbij

/-- **The irreducible step.** Let `Z ⊆ X` be an irreducible closed subset such that
`ComplexAnalytic.AlgebraizesOver X W` holds for all closed `W ⊊ Z`, and assume GAGA-2 on `X` and
`ComplexAnalytic.GenericAlgebraization X`. Then every coherent sheaf on `X^an` whose stalks vanish
off `π⁻¹ Z` is algebraic. -/
theorem isAnalytificationOfCoherent_of_isIrreducible (h2 : AnalytificationFullOnCoherent X)
    (hgen : GenericAlgebraization X) (Z : Closeds X.obj.left)
    (hZ : IsIrreducible (Z : Set X.obj.left)) (ih : ∀ W < Z, AlgebraizesOver X W)
    (M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf) [M.IsCoherent]
    (hM : ∀ x, (analytificationπLRS X).base x ∉ Z →
      Subsingleton (((analytification.obj X).toLocallyRingedSpace.stalkFunctor x).obj M)) :
    IsAnalytificationOfCoherent M := by
  let Y := (analytification.obj X).toLocallyRingedSpace
  let J := Scheme.IdealSheafData.vanishingIdeal Z
  have hJ : ∀ p : X.obj.left, p ∉ J.support ↔ p ∉ Z := fun p ↦ by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨N, hN⟩ := exists_pow_analyticIdeal_le_annihilator J M fun x hx ↦ hM x ((hJ _).1 hx)
  let n := N + 1
  let T := X.subscheme (J ^ n)
  let i : T ⟶ X := X.subschemeι (J ^ n)
  let f := (analytification.map i).toLRSHom
  have hf := isClosedEmbedding_analytification_map i
  have hrange : Set.range i.hom.left.base = Z := by
    rw [SchemeLFTℂ.range_subschemeι, Scheme.IdealSheafData.support_pow _ _ (Nat.succ_ne_zero _),
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  -- `M` is the pushforward of a coherent sheaf on `T^an`
  haveI : IsIso (f.pullbackModulesAdj.unit.app M) :=
    f.isIso_pullbackModulesAdj_unit_app_of_smul_eq_zero hf
      (surjective_stalkMap_analytification_map i) M fun x r hr m ↦ by
        have hr' : r ∈ analyticIdeal X J x ^ N := by
          have h : r ∈ analyticIdeal X (J ^ n) x := hr
          rw [analyticIdeal_pow] at h
          exact Ideal.pow_le_pow_right (Nat.le_succ N) h
        exact Module.mem_annihilator.1 (hN x hr') m
  let M' := f.pullbackModules.obj M
  have hM' : M'.IsCoherent :=
    LocallyRingedSpace.isCoherent_pullbackModules_of_isCoherentStructureSheaf
      (analytification.obj T).isCoherentStructureSheaf f M
  haveI : IrreducibleSpace T.obj.left :=
    irreducibleSpace_of_isClosedEmbedding i.hom.left.isClosedEmbedding (hrange ▸ hZ)
  obtain ⟨U, B', ψ', hU, hB', hψ'⟩ := hgen T i inferInstance inferInstance M' hM'
  let B := (SheafOfModules.pushforward.{u} i.hom.left.toLRSHom.toRingSheafHom).obj B'
  have hB : B.IsCoherent := @isCoherent_pushforward_of_isClosedImmersion _ _ i.hom.left B' _ _ hB'
  haveI := isIso_analytificationPushforwardBaseChange i B'
  let ψ : M ⟶ (analytificationModules X).obj B := f.pullbackModulesAdj.unit.app M ≫
    (SheafOfModules.pushforward.{u} f.toRingSheafHom).map ψ' ≫
      inv (analytificationPushforwardBaseChange i B')
  -- the locus off which `ψ` is bijective on stalks
  let W : Closeds X.obj.left := ⟨i.hom.left.base '' (U : Set T.obj.left)ᶜ,
    i.hom.left.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl⟩
  have hWZ : W < Z := by
    refine lt_of_le_of_ne (fun p ⟨t, _, ht⟩ ↦ by rw [← SetLike.mem_coe, ← hrange]; exact ⟨t, ht⟩)
      fun h ↦ ?_
    obtain ⟨u, hu⟩ := hU
    have hu' : i.hom.left.base u ∈ (W : Set X.obj.left) := by
      rw [h, ← hrange]
      exact ⟨u, rfl⟩
    obtain ⟨t, ht, htu⟩ := hu'
    exact ht (i.hom.left.isClosedEmbedding.injective htu ▸ hu)
  refine @isAnalytificationOfCoherent_of_hom _ _ h2 W (ih W hWZ) M _ B hB ψ fun x hx ↦ ?_
  have hmid : Function.Bijective ((Y.stalkFunctor x).map
      ((SheafOfModules.pushforward.{u} f.toRingSheafHom).map ψ')) := by
    by_cases hxr : x ∈ Set.range f.base
    · obtain ⟨z, rfl⟩ := hxr
      refine f.bijective_stalkFunctor_map_pushforward_of_isInducing hf.isInducing ψ' z
        (hψ' z ?_)
      by_contra hzU
      exact hx ⟨_, hzU, (analytificationπ_base_map i z).symm⟩
    · haveI := f.subsingleton_stalk_pushforward hf.isClosed_range x hxr M'
      haveI := f.subsingleton_stalk_pushforward hf.isClosed_range x hxr
        ((analytificationModules T).obj B')
      exact ⟨fun a b _ ↦ Subsingleton.elim a b, fun b ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  have b1 := ((Y.stalkFunctor x).mapIso
    (asIso (f.pullbackModulesAdj.unit.app M))).toLinearEquiv.bijective
  have b3 := ((Y.stalkFunctor x).mapIso
    (asIso (inv (analytificationPushforwardBaseChange i B')))).toLinearEquiv.bijective
  simp only [ψ, Functor.map_comp, ConcreteCategory.coe_comp]
  exact b3.comp (hmid.comp b1)

end Steps

/-! ### The noetherian induction -/

variable (X) in
/-- **GAGA-3 by noetherian induction.** Let `X` be a proper scheme over `ℂ` satisfying GAGA-2
(`ComplexAnalytic.AnalytificationFullOnCoherent X`) and
`ComplexAnalytic.GenericAlgebraization X`. Then for every closed subset `Z ⊆ X`, every coherent
sheaf on `X^an` whose stalks vanish off `π⁻¹ Z` is algebraic. -/
theorem algebraizesOver_of_generic (hX : IsProperℂ X) (h2 : AnalytificationFullOnCoherent X)
    (hgen : GenericAlgebraization X) (Z : Closeds X.obj.left) : AlgebraizesOver X Z := by
  haveI := hX.compactSpace
  haveI := hX.compactSpace_analytification
  haveI : IsNoetherian X.obj.left := {}
  induction Z using WellFoundedLT.induction with
  | _ Z ih =>
  intro M hM hsupp
  by_cases hne : (Z : Set X.obj.left).Nonempty
  · by_cases hirr : IsIrreducible (Z : Set X.obj.left)
    · exact isAnalytificationOfCoherent_of_isIrreducible h2 hgen Z hirr ih M hsupp
    have hpre : ¬ IsPreirreducible (Z : Set X.obj.left) := fun h ↦ hirr ⟨hne, h⟩
    rw [isPreirreducible_iff_isClosed_union_isClosed] at hpre
    push Not at hpre
    obtain ⟨z₁, z₂, hz₁, hz₂, hcov, hn₁, hn₂⟩ := hpre
    have hlt : ∀ (z : Set X.obj.left) (hz : IsClosed z), ¬ (Z : Set X.obj.left) ⊆ z →
        Z ⊓ ⟨z, hz⟩ < Z := fun z hz hn ↦
      lt_of_le_of_ne inf_le_left fun h ↦ hn fun p hp ↦ by
        rw [← h] at hp
        exact hp.2
    exact isAnalytificationOfCoherent_of_subset_union h2 Z (Z ⊓ ⟨z₁, hz₁⟩) (Z ⊓ ⟨z₂, hz₂⟩)
      (fun p hp ↦ (hcov hp).imp (fun h ↦ ⟨hp, h⟩) (fun h ↦ ⟨hp, h⟩))
      (ih _ (hlt z₁ hz₁ hn₁)) (ih _ (hlt z₂ hz₂ hn₂)) M hsupp
  · exact isAnalytificationOfCoherent_of_isZero
      (LocallyRingedSpace.isZero_of_forall_subsingleton_stalk M fun x ↦
        hsupp x fun hx ↦ hne ⟨_, hx⟩)

variable (X) in
/-- **GAGA-3 for proper schemes, from GAGA-2 and generic algebraization.** Let `X` be a proper
scheme over `ℂ` satisfying `ComplexAnalytic.AnalytificationFullOnCoherent X` and
`ComplexAnalytic.GenericAlgebraization X`. Then every coherent sheaf on `X^an` is isomorphic to
the analytification of a coherent sheaf on `X`. -/
theorem exists_iso_analytificationModules_of_generic (hX : IsProperℂ X)
    (h2 : AnalytificationFullOnCoherent X) (hgen : GenericAlgebraization X)
    (M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf)
    [M.IsCoherent] :
    ∃ F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf,
      F.IsCoherent ∧ Nonempty ((analytificationModules X).obj F ≅ M) :=
  algebraizesOver_of_generic X hX h2 hgen ⊤ M inferInstance fun _ hx ↦ (hx trivial).elim

/-- GAGA-2 for proper schemes (`ComplexAnalytic.gaga₂_of_isProperℂ`, assuming the analytic relative
Serre theorem) provides `ComplexAnalytic.AnalytificationFullOnCoherent`. -/
theorem IsProperℂ.analytificationFullOnCoherent (hX : IsProperℂ X)
    (h : RelativeAnalyticSerre.{u}) : AnalytificationFullOnCoherent X :=
  fun F G hF hG ↦ haveI := hF; haveI := hG; (gaga₂_of_isProperℂ hX h F G).2

variable (X) in
/-- **GAGA-3 for proper schemes**, assuming the analytic relative Serre theorem
`ComplexAnalytic.RelativeAnalyticSerre` and `ComplexAnalytic.GenericAlgebraization X`: every
coherent sheaf on `X^an` is isomorphic to the analytification of a coherent sheaf on `X`. -/
theorem gaga₃_of_isProperℂ (hX : IsProperℂ X) (h : RelativeAnalyticSerre.{u})
    (hgen : GenericAlgebraization X)
    (M : SheafOfModules.{u} (analytification.obj X).toLocallyRingedSpace.ringSheaf)
    [M.IsCoherent] :
    ∃ F : SheafOfModules.{u} X.obj.left.toLocallyRingedSpace.ringSheaf,
      F.IsCoherent ∧ Nonempty ((analytificationModules X).obj F ≅ M) :=
  exists_iso_analytificationModules_of_generic X hX (hX.analytificationFullOnCoherent h) hgen M

end ComplexAnalytic

end
