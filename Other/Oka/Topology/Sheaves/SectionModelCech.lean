/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Analysis.LocallyConvex.Schwartz
public import Other.Oka.Topology.Sheaves.Cohomology.CechDegreeOne
public import Other.Oka.Topology.Sheaves.SectionModel

/-!
# Finiteness of Čech cohomology in degree one from a Fréchet section model

Let `M` be a section model of the abelian sheaf `F` (`TopCat.Sheaf.SectionModel`) by Fréchet
spaces, indexed by a countable type. Čech cochains of a finite family of opens are then
identified with the Fréchet spaces `TopCat.Sheaf.SectionModel.Cochain` of families of model
sections, the Čech differential and refinement with continuous linear maps
(`TopCat.Sheaf.SectionModel.dL`, `TopCat.Sheaf.SectionModel.refineL`).

**Cartan–Serre argument** (`TopCat.Sheaf.SectionModel.finiteDimensional_of_cech`). Let `U`, `V`
be finite families of opens with `V i` of compact closure inside `U i`, such that every Čech
`1`-cocycle of `V` is the refinement of a cocycle of `U` up to a coboundary. If restriction to
relatively compact opens is compact on the model, then the map
`Z¹(U) × C⁰(V) → Z¹(V)`, `(z, c) ↦ z|_V + d c` is surjective and differs from `(z, c) ↦ d c` by a
compact operator, so by Schwartz's theorem the cokernel `Z¹(V) / B¹(V)` is finite dimensional.
Consequently every `ℂ`-linear quotient of the cocycles of `V` vanishing on coboundaries (such as
`H¹(X, F)`) is finite dimensional.
-/

@[expose] public section

universe u v

open CategoryTheory TopologicalSpace Opposite Topology Filter Set TopCat.Presheaf

namespace TopCat.Sheaf.SectionModel

variable {X : TopCat.{u}} {F : AbSheaf X} {𝒬 : Type u} {E : 𝒬 → Type v}
  [∀ q, AddCommGroup (E q)] [∀ q, Module ℂ (E q)]

section Basic

variable [∀ q, UniformSpace (E q)] [∀ q, IsUniformAddGroup (E q)] [∀ q, ContinuousSMul ℂ (E q)]
  (M : SectionModel F E) {ι : Type u} (U : ι → Opens X)

/-- Čech `n`-cochains of the family `U`, read in the model. -/
abbrev Cochain (n : ℕ) : Type _ := ∀ σ : Fin (n + 1) → ι, M.sub (cechOpen U σ)

/-- Čech cochains of `F` are cochains in the model. -/
noncomputable def cochainEquiv (n : ℕ) : CechCochain U F.obj n ≃+ M.Cochain U n :=
  AddEquiv.piCongrRight fun σ ↦ M.sectionsEquiv (cechOpen U σ)

omit [∀ q, IsUniformAddGroup (E q)] [∀ q, ContinuousSMul ℂ (E q)] in
lemma cochainEquiv_apply (n : ℕ) (c : CechCochain U F.obj n) (σ : Fin (n + 1) → ι) :
    M.cochainEquiv U n c σ = M.sectionsEquiv _ (c σ) :=
  rfl

/-- The Čech differential on model cochains. -/
noncomputable def dL (n : ℕ) : M.Cochain U n →L[ℂ] M.Cochain U (n + 1) :=
  ContinuousLinearMap.pi fun τ ↦ ∑ j : Fin (n + 2), ((-1 : ℂ) ^ (j : ℕ)) •
    (M.subRes (cechOpen_le_comp U τ j.succAbove)).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun σ : Fin (n + 1) → ι ↦ M.sub (cechOpen U σ))
        (τ ∘ j.succAbove))

lemma dL_apply (n : ℕ) (c : M.Cochain U n) (τ : Fin (n + 2) → ι) :
    M.dL U n c τ = ∑ j : Fin (n + 2), ((-1 : ℂ) ^ (j : ℕ)) •
      M.subRes (cechOpen_le_comp U τ j.succAbove) (c (τ ∘ j.succAbove)) := by
  simp [dL]

/-- The model differential is the Čech differential. -/
lemma cochainEquiv_cechD (n : ℕ) (c : CechCochain U F.obj n) :
    M.cochainEquiv U (n + 1) (cechD U F.obj n c) = M.dL U n (M.cochainEquiv U n c) := by
  funext τ
  rw [cochainEquiv_apply, cechD_apply, dL_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul, sectionsEquiv_map, cochainEquiv_apply, ← Int.cast_smul_eq_zsmul ℂ]
  push_cast
  rfl

section Refine

variable {V : ι → Opens X} (hVU : ∀ i, V i ≤ U i)

/-- Refinement of model cochains along `V i ≤ U i`. -/
noncomputable def refineL (n : ℕ) : M.Cochain U n →L[ℂ] M.Cochain V n :=
  ContinuousLinearMap.pi fun σ ↦ (M.subRes (cechOpen_le_cechOpen_comp U hVU σ)).comp
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun σ : Fin (n + 1) → ι ↦ M.sub (cechOpen U σ)) σ)

omit [∀ q, IsUniformAddGroup (E q)] [∀ q, ContinuousSMul ℂ (E q)] in
lemma refineL_apply (n : ℕ) (c : M.Cochain U n) (σ : Fin (n + 1) → ι) :
    M.refineL U hVU n c σ = M.subRes (cechOpen_le_cechOpen_comp U hVU σ) (c σ) :=
  rfl

omit [∀ q, IsUniformAddGroup (E q)] [∀ q, ContinuousSMul ℂ (E q)] in
/-- The model refinement is the Čech refinement. -/
lemma cochainEquiv_cechRefine (n : ℕ) (c : CechCochain U F.obj n) :
    M.cochainEquiv V n (cechRefine U (τ := id) hVU F.obj n c) =
      M.refineL U hVU n (M.cochainEquiv U n c) := by
  funext σ
  rw [cochainEquiv_apply, cechRefine_apply, refineL_apply, cochainEquiv_apply,
    sectionsEquiv_map]
  rfl

end Refine

omit [∀ q, IsUniformAddGroup (E q)] [∀ q, ContinuousSMul ℂ (E q)] in
/-- The model cochain of the image of a cochain under `smulHom c` is `c •` the model cochain. -/
lemma cochainEquiv_smulHom (n : ℕ) (c : ℂ) (z : CechCochain U F.obj n) :
    M.cochainEquiv U n (cechCochainMap U (M.smulHom c).hom n z) =
      c • M.cochainEquiv U n z := by
  funext σ
  ext q
  simp only [cochainEquiv_apply, Pi.smul_apply, Submodule.coe_smul, sectionsEquiv_apply_coe]
  change (M.ε q.1).symm (F.obj.map _ ((M.smulHom c).hom.app _ (z σ))) = _
  rw [← ConcreteCategory.comp_apply, ← (M.smulHom c).hom.naturality,
    ConcreteCategory.comp_apply]
  apply (M.ε q.1).injective
  rw [M.ε_smul, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- `d ∘ d = 0` on model cochains. -/
lemma dL_dL (n : ℕ) (c : M.Cochain U n) : M.dL U (n + 1) (M.dL U n c) = 0 := by
  obtain ⟨c, rfl⟩ := (M.cochainEquiv U n).surjective c
  rw [← cochainEquiv_cechD, ← cochainEquiv_cechD, cechD_cechD, map_zero]

/-- Refinement commutes with the model differential. -/
lemma dL_refineL {V : ι → Opens X} (hVU : ∀ i, V i ≤ U i) (n : ℕ) (c : M.Cochain U n) :
    M.dL V n (M.refineL U hVU n c) = M.refineL U hVU (n + 1) (M.dL U n c) := by
  obtain ⟨c, rfl⟩ := (M.cochainEquiv U n).surjective c
  rw [← cochainEquiv_cechRefine, ← cochainEquiv_cechD, ← cochainEquiv_cechD,
    ← cochainEquiv_cechRefine, cechD_cechRefine]

end Basic

section Frechet

variable [∀ q, UniformSpace (E q)] [∀ q, IsUniformAddGroup (E q)] [∀ q, ContinuousSMul ℂ (E q)]
  [∀ q, T2Space (E q)] [∀ q, FirstCountableTopology (E q)] [∀ q, CompleteSpace (E q)]
  [∀ q, LocallyConvexSpace ℝ (E q)] [Countable 𝒬]
  (M : SectionModel F E) {ι : Type u} [Finite ι]

/-- Čech `1`-cocycles of the family `U`, read in the model: a closed subspace of the model
cochains. -/
noncomputable abbrev Z1 (U : ι → Opens X) : Submodule ℂ (M.Cochain U 1) :=
  LinearMap.ker (M.dL U 1 : M.Cochain U 1 →ₗ[ℂ] M.Cochain U 2)

omit [∀ q, FirstCountableTopology (E q)] [∀ q, CompleteSpace (E q)]
  [∀ q, LocallyConvexSpace ℝ (E q)] [Countable 𝒬] [Finite ι] in
lemma isClosed_Z1 (U : ι → Opens X) : IsClosed (M.Z1 U : Set (M.Cochain U 1)) :=
  (M.dL U 1).isClosed_ker

instance (U : ι → Opens X) : CompleteSpace (M.Z1 U) := (M.isClosed_Z1 U).completeSpace_coe

instance (U : ι → Opens X) : IsUniformAddGroup (M.Z1 U) :=
  (M.Z1 U).toAddSubgroup.isUniformAddGroup

instance (U : ι → Opens X) : FirstCountableTopology (M.Z1 U) :=
  TopologicalSpace.firstCountableTopology_induced _ (M.Cochain U 1) ((↑) : M.Z1 U → _)

instance (U : ι → Opens X) : LocallyConvexSpace ℝ (M.Z1 U) :=
  Topology.IsInducing.locallyConvexSpace (f := (M.Z1 U).subtype.restrictScalars ℝ)
    Topology.IsInducing.subtypeVal

omit [∀ q, LocallyConvexSpace ℝ (E q)] in
/-- If `V i` has compact closure inside `U i` for all `i`, refinement of model cochains is a
compact operator. -/
lemma isCompactOperator_refineL
    (hK : ∀ (W : Opens X) (x : X), x ∈ W → ∃ (q q' : 𝒬) (h : M.Q q' ≤ M.Q q),
      x ∈ M.Q q' ∧ M.Q q ≤ W ∧ IsCompactOperator (M.resL q q' h))
    (U : ι → Opens X) {V : ι → Opens X} (hVU : ∀ i, V i ≤ U i)
    (hVc : ∀ i, IsCompact (closure (V i : Set X))) (hVcl : ∀ i, closure (V i : Set X) ⊆ U i)
    (n : ℕ) : IsCompactOperator (M.refineL U hVU n) := by
  refine IsCompactOperator.piMap (f := fun σ ↦ M.subRes (cechOpen_le_cechOpen_comp U hVU σ))
    fun σ ↦ M.isCompactOperator_subRes hK _ ?_ ?_
  · refine (hVc (σ 0)).of_isClosed_subset isClosed_closure (closure_mono ?_)
    exact (iInf_le (fun a ↦ V (σ a)) 0 : cechOpen V σ ≤ V (σ 0))
  · intro x hx
    change x ∈ ((⨅ a, U (σ a) : Opens X) : Set X)
    rw [Opens.coe_iInf, mem_iInter]
    exact fun a ↦ hVcl (σ a) (closure_mono (iInf_le (fun a ↦ V (σ a)) a) hx)

/-- **Cartan–Serre finiteness, abstract form.** Let `U`, `V` be finite families of opens with
`V i` of compact closure inside `U i`, such that every Čech `1`-cocycle of `V` is the refinement
of a `1`-cocycle of `U` up to a coboundary, and assume that restriction between suitable small
model opens is compact. Then every `ℂ`-vector space `T` which is a quotient of the `1`-cocycles
of `V` by a map `κ` vanishing on coboundaries and compatible with the `ℂ`-action is finite
dimensional. -/
theorem finiteDimensional_of_cech
    (hK : ∀ (W : Opens X) (x : X), x ∈ W → ∃ (q q' : 𝒬) (h : M.Q q' ≤ M.Q q),
      x ∈ M.Q q' ∧ M.Q q ≤ W ∧ IsCompactOperator (M.resL q q' h))
    {U V : ι → Opens X} (hVU : ∀ i, V i ≤ U i)
    (hVc : ∀ i, IsCompact (closure (V i : Set X))) (hVcl : ∀ i, closure (V i : Set X) ⊆ U i)
    (hu : ∀ w : CechCochain V F.obj 1, cechD V F.obj 1 w = 0 →
      ∃ (z : CechCochain U F.obj 1) (b : CechCochain V F.obj 0), cechD U F.obj 1 z = 0 ∧
        w = cechRefine U (τ := id) hVU F.obj 1 z + cechD V F.obj 0 b)
    {T : Type*} [AddCommGroup T] [Module ℂ T] (κ : (cechD V F.obj 1).ker →+ T)
    (hκ : Function.Surjective κ)
    (hκ₀ : ∀ b : CechCochain V F.obj 0, κ ⟨cechD V F.obj 0 b, cechD_cechD V F.obj 0 b⟩ = 0)
    (hκs : ∀ (c : ℂ) (z : (cechD V F.obj 1).ker),
      κ ⟨cechCochainMap V (M.smulHom c).hom 1 z, by
        rw [AddMonoidHom.mem_ker, cechD_cechCochainMap, z.2, map_zero]⟩ = c • κ z) :
    FiniteDimensional ℂ T := by
  classical
  have := Fintype.ofFinite ι
  let Zu := M.Z1 U
  let Zv := M.Z1 V
  let R : Zu × M.Cochain V 0 →L[ℂ] M.Cochain V 1 :=
    (M.refineL U hVU 1).comp (Zu.subtypeL.comp (ContinuousLinearMap.fst ℂ _ _))
  have hR : ∀ e, R e ∈ Zv := fun e ↦ by
    change M.dL V 1 (M.refineL U hVU 1 e.1.1) = 0
    rw [dL_refineL, show M.dL U 1 e.1.1 = 0 from e.1.2, map_zero]
  let D : Zu × M.Cochain V 0 →L[ℂ] M.Cochain V 1 :=
    (M.dL V 0).comp (ContinuousLinearMap.snd ℂ _ _)
  have hD : ∀ e, D e ∈ Zv := fun e ↦ M.dL_dL V 0 e.2
  let u : Zu × M.Cochain V 0 →L[ℂ] Zv :=
    (R + D).codRestrict Zv fun e ↦ Zv.add_mem (hR e) (hD e)
  let w : Zu × M.Cochain V 0 →L[ℂ] Zv := (-R).codRestrict Zv fun e ↦ Zv.neg_mem (hR e)
  have huw : ∀ e, ((u + w) e : M.Cochain V 1) = M.dL V 0 e.2 := fun e ↦ by
    change R e + D e + -R e = _
    abel_nf
    rfl
  have hu_surj : Function.Surjective u := fun y ↦ by
    obtain ⟨y', hy'⟩ := (M.cochainEquiv V 1).surjective y
    have hy'd : cechD V F.obj 1 y' = 0 := (M.cochainEquiv V 2).injective (by
      rw [cochainEquiv_cechD, hy', map_zero]; exact y.2)
    obtain ⟨z, b, hz, rfl⟩ := hu y' hy'd
    refine ⟨(⟨M.cochainEquiv U 1 z, ?_⟩, M.cochainEquiv V 0 b), Subtype.ext ?_⟩
    · change M.dL U 1 _ = 0
      rw [← cochainEquiv_cechD, hz, map_zero]
    · refine Eq.trans ?_ hy'
      rw [map_add, cochainEquiv_cechRefine]
      conv_rhs => rw [cochainEquiv_cechD]
      rfl
  have hw : IsCompactOperator w := by
    refine IsCompactOperator.codRestrict ?_ _ (M.isClosed_Z1 V)
    exact ((M.isCompactOperator_refineL hK U hVU hVc hVcl 1).comp_clm
      (Zu.subtypeL.comp (ContinuousLinearMap.fst ℂ _ _))).neg
  have hfin := IsCompactOperator.finiteDimensional_quotient_range_add_of_locallyConvex
    hu_surj hw
  -- the map to `T`
  let ψ₀ : Zv → (cechD V F.obj 1).ker := fun y ↦ ⟨(M.cochainEquiv V 1).symm y, by
    rw [AddMonoidHom.mem_ker]
    apply (M.cochainEquiv V 2).injective
    rw [cochainEquiv_cechD, AddEquiv.apply_symm_apply, map_zero]
    exact y.2⟩
  let ψ : Zv →ₗ[ℂ] T :=
    { toFun y := κ (ψ₀ y)
      map_add' y₁ y₂ := by
        rw [← map_add]
        congr 1
        exact Subtype.ext (map_add _ _ _)
      map_smul' c y := by
        rw [RingHom.id_apply, ← hκs]
        congr 1
        refine Subtype.ext ((M.cochainEquiv V 1).injective ?_)
        change M.cochainEquiv V 1 ((M.cochainEquiv V 1).symm (c • y : M.Cochain V 1)) =
          M.cochainEquiv V 1 (cechCochainMap V (M.smulHom c).hom 1
            ((M.cochainEquiv V 1).symm (y : M.Cochain V 1)))
        rw [cochainEquiv_smulHom, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] }
  have hψ : LinearMap.range (u + w).toLinearMap ≤ LinearMap.ker ψ := by
    rintro _ ⟨e, rfl⟩
    obtain ⟨b, hb⟩ := (M.cochainEquiv V 0).surjective e.2
    rw [LinearMap.mem_ker]
    change κ (ψ₀ ((u + w) e)) = 0
    have : ψ₀ ((u + w) e) = ⟨cechD V F.obj 0 b, cechD_cechD V F.obj 0 b⟩ := by
      refine Subtype.ext ((M.cochainEquiv V 1).injective ?_)
      change M.cochainEquiv V 1 ((M.cochainEquiv V 1).symm ((u + w) e : M.Cochain V 1)) = _
      rw [AddEquiv.apply_symm_apply, huw, cochainEquiv_cechD, hb]
    rw [this, hκ₀]
  have hψs : Function.Surjective ψ := fun t ↦ by
    obtain ⟨z, rfl⟩ := hκ t
    refine ⟨⟨M.cochainEquiv V 1 z, ?_⟩, ?_⟩
    · change M.dL V 1 _ = 0
      rw [← cochainEquiv_cechD, z.2, map_zero]
    · change κ (ψ₀ _) = κ z
      congr 1
      exact Subtype.ext ((M.cochainEquiv V 1).symm_apply_apply z.1)
  exact Module.Finite.of_surjective ((LinearMap.range (u + w).toLinearMap).liftQ ψ hψ)
    (by rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]
        exact hψs)

end Frechet

end TopCat.Sheaf.SectionModel

end
