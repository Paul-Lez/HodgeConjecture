/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularChainPresheafFlasque
public import Other.AlgebraicTopology.SingularCoefficientBaseChange

/-!
# Coefficients of relative singular chains

A coefficient of an ambient singular chain at a fixed simplex descends to
`C_n(X, X \ U)` whenever that simplex meets `U`.  This is the elementary
coordinate used to glue relative chains over an open cover.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open scoped Simplicial

namespace AlgebraicTopology.Singular

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [Field R] (X : TopCat)

/-- The type of singular `n`-simplices of `X`. -/
abbrev SingularSimplexIndex (n : ℕ) :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))

/-- Coefficient of an absolute singular chain at a fixed singular simplex. -/
def singularChainCoefficient (n : ℕ) (σ : SingularSimplexIndex X n) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom <|
    (Finsupp.lapply σ).comp
      (chainGroupFinsuppIso R X n).toLinearEquiv.toLinearMap

@[simp]
theorem singularChainCoefficient_iota_same (n : ℕ)
    (σ : SingularSimplexIndex X n) (r : R) :
    (singularChainCoefficient R X n σ).hom
        ((SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
          (TopCat.toSSet.obj X) σ).hom r) = r := by
  classical
  change (chainGroupFinsuppIso R X n).hom.hom
      ((SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
        (TopCat.toSSet.obj X) σ).hom r) σ = r
  have h := chainGroupFinsuppIso_iota R X n σ r
  change (chainGroupFinsuppIso R X n).hom.hom
      ((SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
        (TopCat.toSSet.obj X) σ).hom r) = Finsupp.single σ r at h
  rw [h]
  simp

@[simp]
theorem singularChainCoefficient_iota_of_ne (n : ℕ)
    (σ τ : SingularSimplexIndex X n) (h : τ ≠ σ) (r : R) :
    (singularChainCoefficient R X n σ).hom
        ((SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
          (TopCat.toSSet.obj X) τ).hom r) = 0 := by
  classical
  change (chainGroupFinsuppIso R X n).hom.hom
      ((SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
        (TopCat.toSSet.obj X) τ).hom r) σ = 0
  have hcoeff := chainGroupFinsuppIso_iota R X n τ r
  change (chainGroupFinsuppIso R X n).hom.hom
      ((SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
        (TopCat.toSSet.obj X) τ).hom r) = Finsupp.single τ r at hcoeff
  rw [hcoeff]
  simp [h]

/-- A singular simplex meets an open set if one of its points lies in it. -/
def SingularSimplexIndex.MeetsOpen {n : ℕ} (σ : SingularSimplexIndex X n)
    (U : Opens X) : Prop :=
  ∃ t : stdSimplex ℝ (Fin (n + 1)),
    X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) σ t ∈ U

theorem subspace_simplex_ne_of_meetsOpen
    (n : ℕ) (U : Opens X) (σ : SingularSimplexIndex X n)
    (hσ : σ.MeetsOpen X U)
    (τ : SingularSimplexIndex (TopCat.of ↥((U : Set X)ᶜ)) n) :
    (TopCat.toSSet.map (TopPair.ofSubset (X := X) ((U : Set X)ᶜ)).map).app
        (Opposite.op (SimplexCategory.mk n)) τ ≠ σ := by
  intro h
  obtain ⟨t, ht⟩ := hσ
  have hvalue := congrArg
    (fun q : SingularSimplexIndex X n ↦
      X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) q t) h
  have hcompl :
      X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n))
          ((TopCat.toSSet.map (TopPair.ofSubset (X := X) ((U : Set X)ᶜ)).map).app
            (Opposite.op (SimplexCategory.mk n)) τ) t ∈ (U : Set X)ᶜ := by
    exact ((TopCat.of ↥((U : Set X)ᶜ)).toSSetObjEquiv
      (Opposite.op (SimplexCategory.mk n)) τ t).2
  rw [hvalue] at hcompl
  exact hcompl ht

theorem subspaceChainMap_comp_singularChainCoefficient
    (n : ℕ) (U : Opens X) (σ : SingularSimplexIndex X n)
    (hσ : σ.MeetsOpen X U) :
    ((chainPairFunctor R).obj (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).hom.f n ≫
      singularChainCoefficient R X n σ = 0 := by
  change (SSet.chainComplexMap
      (TopCat.toSSet.map (TopPair.ofSubset (X := X) ((U : Set X)ᶜ)).map)
      (ModuleCat.of R R)).f n ≫ singularChainCoefficient R X n σ = 0
  apply SSet.chainComplex_hom_ext
  intro τ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (singularChainCoefficient R X n σ).hom
      ((SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
        (TopCat.toSSet.obj X)
          ((TopCat.toSSet.map
            (TopPair.ofSubset (X := X) ((U : Set X)ᶜ)).map).app
              (Opposite.op (SimplexCategory.mk n)) τ)).hom r) = 0
  rw [singularChainCoefficient_iota_of_ne R X n σ _
    (subspace_simplex_ne_of_meetsOpen X n U σ hσ τ)]

/-- The coefficient at `σ` on a relative chain supported in `U`.  The hypothesis
that `σ` meets `U` makes the coefficient independent of the absolute-chain
representative. -/
def relativeChainCoefficient (n : ℕ) (U : Opens X)
    (σ : SingularSimplexIndex X n) (hσ : σ.MeetsOpen X U) :
    ((relativeChainFunctor R).obj (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).X n ⟶
      ModuleCat.of R R :=
  (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel
    (R := R) (TopPair.ofSubset (X := X) ((U : Set X)ᶜ)) n).desc
      (CokernelCofork.ofπ (singularChainCoefficient R X n σ)
        (subspaceChainMap_comp_singularChainCoefficient R X n U σ hσ))

@[reassoc]
theorem relativeChainProjection_comp_relativeChainCoefficient
    (n : ℕ) (U : Opens X) (σ : SingularSimplexIndex X n)
    (hσ : σ.MeetsOpen X U) :
    (relativeChainProjection R (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).f n ≫
      relativeChainCoefficient R X n U σ hσ =
        singularChainCoefficient R X n σ := by
  unfold relativeChainCoefficient
  exact (Cofork.IsColimit.π_desc
    (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel
      (R := R) (TopPair.ofSubset (X := X) ((U : Set X)ᶜ)) n)).trans
        (CokernelCofork.π_ofπ _ _ _)

/-! ### Canonical representatives -/

/-- `Finsupp.filter` as a linear endomorphism. -/
def finsuppFilterLinearMap {α : Type} (p : α → Prop) [DecidablePred p] :
    (α →₀ R) →ₗ[R] (α →₀ R) where
  toFun := Finsupp.filter p
  map_add' a b := by exact Finsupp.filter_add
  map_smul' r a := by
    ext z
    by_cases hz : p z <;> simp [Finsupp.filter_apply, hz]

/-- Keep precisely those simplices which meet `U`. -/
def singularChainMeetOpenFilter (n : ℕ) (U : Opens X) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n ⟶
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n := by
  classical
  exact (chainGroupFinsuppIso R X n).hom ≫
    ModuleCat.ofHom (finsuppFilterLinearMap R
      (fun σ : SingularSimplexIndex X n ↦
        SingularSimplexIndex.MeetsOpen X σ U)) ≫
    (chainGroupFinsuppIso R X n).inv

@[simp]
theorem singularChainMeetOpenFilter_iota_of_meets
    (n : ℕ) (U : Opens X) (σ : SingularSimplexIndex X n)
    (hσ : σ.MeetsOpen X U) :
    SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
        (TopCat.toSSet.obj X) σ ≫ singularChainMeetOpenFilter R X n U =
      SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
        (TopCat.toSSet.obj X) σ := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (chainGroupFinsuppIso R X n).inv.hom
      (Finsupp.filter (fun τ : SingularSimplexIndex X n ↦
        SingularSimplexIndex.MeetsOpen X τ U)
        ((chainGroupFinsuppIso R X n).hom.hom
          ((SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
            (TopCat.toSSet.obj X) σ).hom r))) =
      (SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
        (TopCat.toSSet.obj X) σ).hom r
  have hcoeff := chainGroupFinsuppIso_iota R X n σ r
  change (chainGroupFinsuppIso R X n).hom.hom
      ((SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
        (TopCat.toSSet.obj X) σ).hom r) = Finsupp.single σ r at hcoeff
  rw [hcoeff, Finsupp.filter_single_of_pos
    (p := fun τ : SingularSimplexIndex X n ↦
      SingularSimplexIndex.MeetsOpen X τ U) hσ]
  rw [← hcoeff]
  simpa using ConcreteCategory.congr_hom
    (Iso.hom_inv_id (chainGroupFinsuppIso R X n))
      ((SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
        (TopCat.toSSet.obj X) σ).hom r)

@[simp]
theorem singularChainMeetOpenFilter_iota_of_not_meets
    (n : ℕ) (U : Opens X) (σ : SingularSimplexIndex X n)
    (hσ : ¬σ.MeetsOpen X U) :
    SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
        (TopCat.toSSet.obj X) σ ≫ singularChainMeetOpenFilter R X n U = 0 := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (chainGroupFinsuppIso R X n).inv.hom
      (Finsupp.filter (fun τ : SingularSimplexIndex X n ↦
        SingularSimplexIndex.MeetsOpen X τ U)
        ((chainGroupFinsuppIso R X n).hom.hom
          ((SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
            (TopCat.toSSet.obj X) σ).hom r))) = 0
  have hcoeff := chainGroupFinsuppIso_iota R X n σ r
  change (chainGroupFinsuppIso R X n).hom.hom
      ((SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
        (TopCat.toSSet.obj X) σ).hom r) = Finsupp.single σ r at hcoeff
  rw [hcoeff, Finsupp.filter_single_of_neg
    (p := fun τ : SingularSimplexIndex X n ↦
      SingularSimplexIndex.MeetsOpen X τ U) hσ]
  simp

@[reassoc]
theorem singularChainMeetOpenFilter_comp_coefficient_of_meets
    (n : ℕ) (U : Opens X) (σ : SingularSimplexIndex X n)
    (hσ : σ.MeetsOpen X U) :
    singularChainMeetOpenFilter R X n U ≫
      singularChainCoefficient R X n σ =
        singularChainCoefficient R X n σ := by
  apply SSet.chainComplex_hom_ext
  intro τ
  by_cases hτ : SingularSimplexIndex.MeetsOpen X τ U
  · rw [← Category.assoc,
      singularChainMeetOpenFilter_iota_of_meets R X n U τ hτ]
  · rw [← Category.assoc,
      singularChainMeetOpenFilter_iota_of_not_meets R X n U τ hτ,
      zero_comp]
    have hne : τ ≠ σ := fun h ↦ hτ (h ▸ hσ)
    symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (singularChainCoefficient R X n σ).hom
      ((SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
        (TopCat.toSSet.obj X) τ).hom r) = 0
    exact singularChainCoefficient_iota_of_ne R X n σ τ hne r

@[reassoc]
theorem singularChainMeetOpenFilter_comp_coefficient_of_not_meets
    (n : ℕ) (U : Opens X) (σ : SingularSimplexIndex X n)
    (hσ : ¬σ.MeetsOpen X U) :
    singularChainMeetOpenFilter R X n U ≫
      singularChainCoefficient R X n σ = 0 := by
  apply SSet.chainComplex_hom_ext
  intro τ
  by_cases hτ : SingularSimplexIndex.MeetsOpen X τ U
  · rw [← Category.assoc,
      singularChainMeetOpenFilter_iota_of_meets R X n U τ hτ]
    have hne : τ ≠ σ := fun h ↦ hσ (h ▸ hτ)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (singularChainCoefficient R X n σ).hom
      ((SSet.ιChainComplex (C := ModuleCat R) (R := ModuleCat.of R R)
        (TopCat.toSSet.obj X) τ).hom r) = 0
    exact singularChainCoefficient_iota_of_ne R X n σ τ hne r
  · rw [← Category.assoc,
      singularChainMeetOpenFilter_iota_of_not_meets R X n U τ hτ,
      zero_comp]
    simp

/-- Regard a singular simplex whose image lies in a subset as a simplex of the
corresponding subspace. -/
def singularSimplexLiftToSubsetField
    (s : Set X) {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n)
    (hσ : Set.range (X.toSSetObjEquiv n σ) ⊆ s) :
    (TopCat.toSSet.obj (TopCat.of ↥s)).obj n :=
  ((TopCat.of ↥s).toSSetObjEquiv n).symm
    ⟨fun t ↦ ⟨X.toSSetObjEquiv n σ t, hσ ⟨t, rfl⟩⟩,
      Continuous.subtype_mk (X.toSSetObjEquiv n σ).continuous _⟩

@[simp]
theorem singularSimplexLiftToSubsetField_comp_inclusion
    (s : Set X) {n : SimplexCategoryᵒᵖ}
    (σ : (TopCat.toSSet.obj X).obj n)
    (hσ : Set.range (X.toSSetObjEquiv n σ) ⊆ s) :
    (TopCat.toSSet.map (TopPair.ofSubset (X := X) s).map).app n
      (singularSimplexLiftToSubsetField X s σ hσ) = σ := by
  apply (X.toSSetObjEquiv n).injective
  ext t
  rfl

theorem not_meetsOpen_iff_range_subset_compl
    (n : ℕ) (U : Opens X) (σ : SingularSimplexIndex X n) :
    ¬σ.MeetsOpen X U ↔
      Set.range (X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk n)) σ) ⊆
        (U : Set X)ᶜ := by
  constructor
  · intro h z hz
    obtain ⟨t, rfl⟩ := hz
    intro ht
    exact h ⟨t, ht⟩
  · intro h ⟨t, ht⟩
    exact h ⟨t, rfl⟩ ht

/-- Removing all simplices contained in `X \ U` does not change a relative
chain class supported in `U`. -/
@[reassoc]
theorem singularChainMeetOpenFilter_comp_relativeChainProjection
    (n : ℕ) (U : Opens X) :
    singularChainMeetOpenFilter R X n U ≫
        (relativeChainProjection R
          (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).f n =
      (relativeChainProjection R
        (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).f n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  by_cases hσ : SingularSimplexIndex.MeetsOpen X σ U
  · rw [← Category.assoc, singularChainMeetOpenFilter_iota_of_meets R X n U σ hσ]
  · rw [← Category.assoc, singularChainMeetOpenFilter_iota_of_not_meets R X n U σ hσ,
      zero_comp]
    let hsub := (not_meetsOpen_iff_range_subset_compl X n U σ).mp hσ
    let τ := singularSimplexLiftToSubsetField X ((U : Set X)ᶜ) σ hsub
    have hτ := iota_subspace_relativeChainProjection R
      (TopPair.ofSubset (X := X) ((U : Set X)ᶜ)) τ
    rw [singularSimplexLiftToSubsetField_comp_inclusion] at hτ
    exact hτ.symm

/-- The meet-open filter kills chains coming from the complement. -/
theorem subspaceChainMap_comp_singularChainMeetOpenFilter
    (n : ℕ) (U : Opens X) :
    ((chainPairFunctor R).obj
        (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).hom.f n ≫
      singularChainMeetOpenFilter R X n U = 0 := by
  change (SSet.chainComplexMap
      (TopCat.toSSet.map
        (TopPair.ofSubset (X := X) ((U : Set X)ᶜ)).map)
      (ModuleCat.of R R)).f n ≫ singularChainMeetOpenFilter R X n U = 0
  apply SSet.chainComplex_hom_ext
  intro τ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  apply singularChainMeetOpenFilter_iota_of_not_meets
  intro ⟨t, ht⟩
  exact ((TopCat.of ↥((U : Set X)ᶜ)).toSSetObjEquiv
    (Opposite.op (SimplexCategory.mk n)) τ t).2 ht

/-- The canonical representative of a relative chain: keep exactly the
ambient simplices meeting the support open. -/
def relativeChainCanonicalRepresentative (n : ℕ) (U : Opens X) :
    ((relativeChainFunctor R).obj
        (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).X n ⟶
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n :=
  (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel
    (R := R) (TopPair.ofSubset (X := X) ((U : Set X)ᶜ)) n).desc
      (CokernelCofork.ofπ (singularChainMeetOpenFilter R X n U)
        (subspaceChainMap_comp_singularChainMeetOpenFilter R X n U))

@[reassoc]
theorem relativeChainProjection_comp_canonicalRepresentative
    (n : ℕ) (U : Opens X) :
    (relativeChainProjection R
        (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).f n ≫
      relativeChainCanonicalRepresentative R X n U =
        singularChainMeetOpenFilter R X n U := by
  unfold relativeChainCanonicalRepresentative
  exact (Cofork.IsColimit.π_desc
    (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel
      (R := R) (TopPair.ofSubset (X := X) ((U : Set X)ᶜ)) n)).trans
        (CokernelCofork.π_ofπ _ _ _)

@[reassoc (attr := simp)]
theorem canonicalRepresentative_comp_relativeChainProjection
    (n : ℕ) (U : Opens X) :
    relativeChainCanonicalRepresentative R X n U ≫
      (relativeChainProjection R
        (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).f n = 𝟙 _ := by
  let π : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n ⟶
      ((relativeChainFunctor R).obj
        (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).X n :=
    (relativeChainProjection R
      (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).f n
  have hpi : Epi π :=
    Cofork.IsColimit.epi
      (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel
        (R := R) (TopPair.ofSubset (X := X) ((U : Set X)ᶜ)) n)
  letI := hpi
  apply (cancel_epi π).mp
  calc
    π ≫ (relativeChainCanonicalRepresentative R X n U ≫ π) =
        (π ≫ relativeChainCanonicalRepresentative R X n U) ≫ π :=
      Category.assoc _ _ _ |>.symm
    _ = singularChainMeetOpenFilter R X n U ≫ π := by
      rw [show π = (relativeChainProjection R
        (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).f n from rfl,
        relativeChainProjection_comp_canonicalRepresentative]
    _ = π := by
      rw [show π = (relativeChainProjection R
        (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).f n from rfl,
        singularChainMeetOpenFilter_comp_relativeChainProjection]
    _ = π ≫ 𝟙 _ := (Category.comp_id _).symm

@[reassoc]
theorem canonicalRepresentative_comp_coefficient_of_meets
    (n : ℕ) (U : Opens X) (σ : SingularSimplexIndex X n)
    (hσ : σ.MeetsOpen X U) :
    relativeChainCanonicalRepresentative R X n U ≫
      singularChainCoefficient R X n σ =
        relativeChainCoefficient R X n U σ hσ := by
  let π : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n ⟶
      ((relativeChainFunctor R).obj
        (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).X n :=
    (relativeChainProjection R
      (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).f n
  have hpi : Epi π :=
    Cofork.IsColimit.epi
      (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel
        (R := R) (TopPair.ofSubset (X := X) ((U : Set X)ᶜ)) n)
  letI := hpi
  apply (cancel_epi π).mp
  calc
    π ≫ (relativeChainCanonicalRepresentative R X n U ≫
        singularChainCoefficient R X n σ) =
      (π ≫ relativeChainCanonicalRepresentative R X n U) ≫
        singularChainCoefficient R X n σ := (Category.assoc _ _ _).symm
    _ = singularChainMeetOpenFilter R X n U ≫
        singularChainCoefficient R X n σ := by
      rw [show π = (relativeChainProjection R
        (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).f n from rfl,
        relativeChainProjection_comp_canonicalRepresentative]
    _ = singularChainCoefficient R X n σ :=
      singularChainMeetOpenFilter_comp_coefficient_of_meets R X n U σ hσ
    _ = π ≫ relativeChainCoefficient R X n U σ hσ := by
      rw [show π = (relativeChainProjection R
        (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).f n from rfl,
        relativeChainProjection_comp_relativeChainCoefficient]

@[reassoc]
theorem canonicalRepresentative_comp_coefficient_of_not_meets
    (n : ℕ) (U : Opens X) (σ : SingularSimplexIndex X n)
    (hσ : ¬σ.MeetsOpen X U) :
    relativeChainCanonicalRepresentative R X n U ≫
      singularChainCoefficient R X n σ = 0 := by
  let π : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of R R)).X n ⟶
      ((relativeChainFunctor R).obj
        (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).X n :=
    (relativeChainProjection R
      (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).f n
  have hpi : Epi π :=
    Cofork.IsColimit.epi
      (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel
        (R := R) (TopPair.ofSubset (X := X) ((U : Set X)ᶜ)) n)
  letI := hpi
  apply (cancel_epi π).mp
  calc
    π ≫ (relativeChainCanonicalRepresentative R X n U ≫
        singularChainCoefficient R X n σ) =
      (π ≫ relativeChainCanonicalRepresentative R X n U) ≫
        singularChainCoefficient R X n σ := (Category.assoc _ _ _).symm
    _ = singularChainMeetOpenFilter R X n U ≫
        singularChainCoefficient R X n σ := by
      rw [show π = (relativeChainProjection R
        (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).f n from rfl,
        relativeChainProjection_comp_canonicalRepresentative]
    _ = 0 :=
      singularChainMeetOpenFilter_comp_coefficient_of_not_meets R X n U σ hσ
    _ = π ≫ 0 := by simp

/-- Restriction of a relative chain preserves every coefficient whose simplex
meets the smaller open. -/
@[reassoc]
theorem supportInclusionPairMap_comp_relativeChainCoefficient
    (n : ℕ) {U V : Opens X} (i : V ⟶ U)
    (σ : SingularSimplexIndex X n) (hσ : σ.MeetsOpen X V) :
    ((relativeChainFunctor R).map (supportInclusionPairMap X
        (show (V : Set X) ⊆ U from i.le))).f n ≫
        relativeChainCoefficient R X n V σ hσ =
      relativeChainCoefficient R X n U σ
        ⟨hσ.choose, i.le hσ.choose_spec⟩ := by
  let hVU : (V : Set X) ⊆ U := i.le
  let f := ((relativeChainFunctor R).map
    (supportInclusionPairMap X hVU)).f n
  let πU := (relativeChainProjection R
    (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).f n
  have hpi : Epi πU :=
    Cofork.IsColimit.epi
      (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel
        (R := R) (TopPair.ofSubset (X := X) ((U : Set X)ᶜ)) n)
  letI := hpi
  apply (cancel_epi πU).mp
  have hfac := congrArg (fun f ↦ f.f n)
    (relativeChainProjection_supportInclusion R X hVU)
  change πU ≫ f =
      (relativeChainProjection R
        (TopPair.ofSubset (X := X) ((V : Set X)ᶜ))).f n at hfac
  calc
    πU ≫ (f ≫ relativeChainCoefficient R X n V σ hσ) =
        (πU ≫ f) ≫ relativeChainCoefficient R X n V σ hσ :=
      (Category.assoc _ _ _).symm
    _ = (relativeChainProjection R
          (TopPair.ofSubset (X := X) ((V : Set X)ᶜ))).f n ≫
        relativeChainCoefficient R X n V σ hσ := by rw [hfac]
    _ = singularChainCoefficient R X n σ :=
      relativeChainProjection_comp_relativeChainCoefficient R X n V σ hσ
    _ = πU ≫ relativeChainCoefficient R X n U σ
        ⟨hσ.choose, i.le hσ.choose_spec⟩ := by
      rw [show πU = (relativeChainProjection R
        (TopPair.ofSubset (X := X) ((U : Set X)ᶜ))).f n from rfl,
        relativeChainProjection_comp_relativeChainCoefficient]

end AlgebraicTopology.Singular
