/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Other.Oka.Analysis.Normed.Operator.Compact.Pi
public import Other.Oka.Topology.Algebra.Module.OpenMapping
public import Other.Oka.Topology.Sheaves.Cohomology.Basic

/-!
# Fréchet models of the sections of a sheaf

Let `F` be an abelian sheaf on a topological space `X`. A *section model*
(`TopCat.Sheaf.SectionModel`) consists of a family of opens `Q q` forming a basis of the topology,
and for each `q` a topological `ℂ`-vector space `E q` with an additive isomorphism
`ε q : E q ≃+ F(Q q)`, such that the restriction maps `F(Q q) → F(Q q')` read through `ε` are
continuous and `ℂ`-linear, the `ℂ`-action on `E q` coming from a family of endomorphisms of `F`.

For every open `W` the sections `F(W)` are then identified with the closed subspace
`TopCat.Sheaf.SectionModel.sub W` of compatible families in `∏_{Q q ≤ W} E q`
(`TopCat.Sheaf.SectionModel.sectionsEquiv`), which carries the product topology; restrictions
become coordinate projections (`TopCat.Sheaf.SectionModel.subRes`).

If the `E q` are Fréchet spaces and `𝒬` is countable, all these spaces are Fréchet. The main
analytic statement is **locality of the topology**
(`TopCat.Sheaf.SectionModel.isClosedEmbedding_family`): for a countable
family of `Q (v j) ≤ Q q` covering `Q q`, `E q → ∏ⱼ E (v j)` is a closed embedding (by the open
mapping theorem), and its consequence, **compactness of restriction**
(`TopCat.Sheaf.SectionModel.isCompactOperator_subRes`): if every point has arbitrarily small pairs
`Q q' ≤ Q q` with compact restriction `E q → E q'`, then `F(W) → F(W')` is a compact operator
whenever `W'` has compact closure inside `W`.
-/

@[expose] public section

universe u v

open CategoryTheory TopologicalSpace Opposite Topology Filter Set

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (F : AbSheaf X) {𝒬 : Type u} (E : 𝒬 → Type v)
  [∀ q, AddCommGroup (E q)] [∀ q, Module ℂ (E q)]

section Basic

variable [∀ q, TopologicalSpace (E q)]

/-- A *section model* of the abelian sheaf `F`: a basis `Q` of opens of `X` and topological
`ℂ`-vector spaces `E q ≃+ F(Q q)` in which restriction is continuous, the `ℂ`-action coming from
endomorphisms `smulHom c` of `F`. -/
structure SectionModel where
  /-- The model opens. -/
  Q : 𝒬 → Opens X
  /-- The identification of the model space with the sections over the model open. -/
  ε : ∀ q, E q ≃+ F.obj.obj (op (Q q))
  /-- The endomorphisms of `F` inducing the `ℂ`-action. -/
  smulHom : ℂ → (F ⟶ F)
  ε_smul : ∀ q (c : ℂ) (x : E q), ε q (c • x) = (smulHom c).hom.app (op (Q q)) (ε q x)
  continuous_res : ∀ q q' (h : Q q' ≤ Q q),
    Continuous fun x : E q ↦ (ε q').symm (F.obj.map (homOfLE h).op (ε q x))
  exists_mem_le : ∀ (W : Opens X) (x : X), x ∈ W → ∃ q, x ∈ Q q ∧ Q q ≤ W

namespace SectionModel

variable {F E} (M : SectionModel F E)

/-- Restriction `E q → E q'` for `Q q' ≤ Q q`. -/
def res (q q' : 𝒬) (h : M.Q q' ≤ M.Q q) : E q →+ E q' :=
  (M.ε q').symm.toAddMonoidHom.comp ((F.obj.map (homOfLE h).op).hom.comp (M.ε q).toAddMonoidHom)

lemma ε_res {q q' : 𝒬} (h : M.Q q' ≤ M.Q q) (x : E q) :
    M.ε q' (M.res q q' h x) = F.obj.map (homOfLE h).op (M.ε q x) := by
  simp [res]

lemma res_apply {q q' : 𝒬} (h : M.Q q' ≤ M.Q q) (x : E q) :
    M.res q q' h x = (M.ε q').symm (F.obj.map (homOfLE h).op (M.ε q x)) :=
  rfl

lemma res_smul {q q' : 𝒬} (h : M.Q q' ≤ M.Q q) (c : ℂ) (x : E q) :
    M.res q q' h (c • x) = c • M.res q q' h x := by
  apply (M.ε q').injective
  rw [ε_res, M.ε_smul, M.ε_smul, ε_res, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, NatTrans.naturality]

lemma res_self (q : 𝒬) (x : E q) : M.res q q le_rfl x = x := by
  apply (M.ε q).injective
  rw [ε_res, show (homOfLE (le_refl (M.Q q))).op = 𝟙 (op (M.Q q)) from rfl, F.obj.map_id]
  rfl

lemma res_res {q q' q'' : 𝒬} (h : M.Q q' ≤ M.Q q) (h' : M.Q q'' ≤ M.Q q') (x : E q) :
    M.res q' q'' h' (M.res q q' h x) = M.res q q'' (h'.trans h) x := by
  apply (M.ε q'').injective
  rw [ε_res, ε_res, ε_res, ← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  rfl

/-- Restriction `E q → E q'` as a continuous `ℂ`-linear map. -/
def resL (q q' : 𝒬) (h : M.Q q' ≤ M.Q q) : E q →L[ℂ] E q' where
  toFun := M.res q q' h
  map_add' := map_add _
  map_smul' := M.res_smul h
  cont := M.continuous_res q q' h

@[simp]
lemma resL_apply {q q' : 𝒬} (h : M.Q q' ≤ M.Q q) (x : E q) : M.resL q q' h x = M.res q q' h x :=
  rfl

section Family

variable {J : Type u} (v : J → 𝒬)

/-- The compatible families in `∏ⱼ E (v j)`: those whose restrictions to every smaller model
open agree. -/
def compat : Submodule ℂ (∀ j, E (v j)) where
  carrier := {y | ∀ j₁ j₂ q (h₁ : M.Q q ≤ M.Q (v j₁)) (h₂ : M.Q q ≤ M.Q (v j₂)),
    M.res _ q h₁ (y j₁) = M.res _ q h₂ (y j₂)}
  add_mem' {a b} ha hb j₁ j₂ q h₁ h₂ := by
    simp only [Pi.add_apply, map_add, ha j₁ j₂ q h₁ h₂, hb j₁ j₂ q h₁ h₂]
  zero_mem' j₁ j₂ q h₁ h₂ := by simp
  smul_mem' c a ha j₁ j₂ q h₁ h₂ := by
    simp only [Pi.smul_apply, res_smul, ha j₁ j₂ q h₁ h₂]

lemma mem_compat {y : ∀ j, E (v j)} :
    y ∈ M.compat v ↔ ∀ j₁ j₂ q (h₁ : M.Q q ≤ M.Q (v j₁)) (h₂ : M.Q q ≤ M.Q (v j₂)),
      M.res _ q h₁ (y j₁) = M.res _ q h₂ (y j₂) :=
  Iff.rfl

lemma isClosed_compat [∀ q, T2Space (E q)] : IsClosed (M.compat v : Set (∀ j, E (v j))) := by
  have : (M.compat v : Set (∀ j, E (v j))) = ⋂ (j₁ : J) (j₂ : J) (q : 𝒬)
      (h₁ : M.Q q ≤ M.Q (v j₁)) (h₂ : M.Q q ≤ M.Q (v j₂)),
      {y | M.resL _ q h₁ (y j₁) = M.resL _ q h₂ (y j₂)} := by
    ext y
    simp [mem_compat]
  rw [this]
  exact isClosed_iInter fun j₁ ↦ isClosed_iInter fun j₂ ↦ isClosed_iInter fun q ↦
    isClosed_iInter fun h₁ ↦ isClosed_iInter fun h₂ ↦
      isClosed_eq ((M.resL _ q h₁).continuous.comp (continuous_apply j₁))
        ((M.resL _ q h₂).continuous.comp (continuous_apply j₂))

variable {W : Opens X} (hv : ∀ j, M.Q (v j) ≤ W)

/-- The restrictions of a section over `W` to the model opens `Q (v j) ≤ W`. -/
def family : F.obj.obj (op W) →+ ∀ j, E (v j) where
  toFun s j := (M.ε (v j)).symm (F.obj.map (homOfLE (hv j)).op s)
  map_zero' := by ext; simp
  map_add' s t := by ext; simp

lemma family_apply (s : F.obj.obj (op W)) (j : J) :
    M.family v hv s j = (M.ε (v j)).symm (F.obj.map (homOfLE (hv j)).op s) :=
  rfl

lemma res_family (s : F.obj.obj (op W)) (j : J) (q : 𝒬) (h : M.Q q ≤ M.Q (v j)) :
    M.res _ q h (M.family v hv s j) = (M.ε q).symm (F.obj.map (homOfLE (h.trans (hv j))).op s) := by
  rw [res_apply, family_apply, AddEquiv.apply_symm_apply, ← ConcreteCategory.comp_apply,
    ← F.obj.map_comp]
  rfl

lemma family_mem_compat (s : F.obj.obj (op W)) : M.family v hv s ∈ M.compat v :=
  fun j₁ j₂ q h₁ h₂ ↦ by rw [res_family, res_family]

/-- Two sections over an open `V` agreeing on every model open inside `V` are equal. -/
lemma eq_of_forall_map_eq {V : Opens X} {s t : F.obj.obj (op V)}
    (h : ∀ q (hq : M.Q q ≤ V), F.obj.map (homOfLE hq).op s = F.obj.map (homOfLE hq).op t) :
    s = t := by
  refine TopCat.Sheaf.eq_of_locally_eq' (F := (F : X.Sheaf AddCommGrpCat.{u}))
    (fun q : {q // M.Q q ≤ V} ↦ M.Q q.1) V (fun q ↦ homOfLE q.2) ?_ s t fun q ↦ h q.1 q.2
  intro x hx
  obtain ⟨q, hxq, hq⟩ := M.exists_mem_le V x hx
  exact Opens.mem_iSup.2 ⟨⟨q, hq⟩, hxq⟩

variable {v hv}

include hv in
lemma family_injective (hcov : W ≤ ⨆ j, M.Q (v j)) : Function.Injective (M.family v hv) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Sheaf.eq_of_locally_eq' (F := (F : X.Sheaf AddCommGrpCat.{u}))
    (fun j ↦ M.Q (v j)) W (fun j ↦ homOfLE (hv j)) hcov s 0 fun j ↦ ?_
  have := congrFun hs j
  rw [family_apply, Pi.zero_apply, AddEquiv.map_eq_zero_iff] at this
  rw [this, map_zero]

include hv in
lemma exists_family_eq (hcov : W ≤ ⨆ j, M.Q (v j)) {y : ∀ j, E (v j)} (hy : y ∈ M.compat v) :
    ∃ s, M.family v hv s = y := by
  let sf : ∀ j, F.obj.obj (op (M.Q (v j))) := fun j ↦ M.ε (v j) (y j)
  have hc : TopCat.Presheaf.IsCompatible (F : X.Sheaf AddCommGrpCat.{u}).1
      (fun j ↦ M.Q (v j)) sf := fun j₁ j₂ ↦ by
    refine M.eq_of_forall_map_eq fun q hq ↦ ?_
    rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← ConcreteCategory.comp_apply,
      ← F.obj.map_comp]
    have h₁ : M.Q q ≤ M.Q (v j₁) := hq.trans inf_le_left
    have h₂ : M.Q q ≤ M.Q (v j₂) := hq.trans inf_le_right
    change F.obj.map (homOfLE h₁).op (M.ε _ (y j₁)) = F.obj.map (homOfLE h₂).op (M.ε _ (y j₂))
    rw [← ε_res, ← ε_res, hy j₁ j₂ q h₁ h₂]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := (F : X.Sheaf AddCommGrpCat.{u}))
    (fun j ↦ M.Q (v j)) W (fun j ↦ homOfLE (hv j)) hcov sf hc
  refine ⟨s, funext fun j ↦ ?_⟩
  rw [family_apply]
  erw [hs j]
  exact (M.ε (v j)).symm_apply_apply (y j)

end Family

section Sub

/-- The model opens contained in `W`. -/
abbrev Idx (W : Opens X) : Type u := {q : 𝒬 // M.Q q ≤ W}

/-- The model of the sections over `W`: the compatible families in `∏_{Q q ≤ W} E q`. -/
abbrev sub (W : Opens X) : Submodule ℂ (∀ q : M.Idx W, E q.1) :=
  M.compat (Subtype.val : M.Idx W → 𝒬)

lemma le_iSup_Idx (W : Opens X) : W ≤ ⨆ q : M.Idx W, M.Q q.1 := fun x hx ↦ by
  obtain ⟨q, hxq, hq⟩ := M.exists_mem_le W x hx
  exact Opens.mem_iSup.2 ⟨⟨q, hq⟩, hxq⟩

/-- **The sections of `F` over `W` are the compatible families of model sections.** -/
noncomputable def sectionsEquiv (W : Opens X) : F.obj.obj (op W) ≃+ M.sub W :=
  AddEquiv.ofBijective ((M.family Subtype.val fun q ↦ q.2).codRestrict _
    (M.family_mem_compat _ _))
    ⟨fun _ _ h ↦ M.family_injective (M.le_iSup_Idx W) (congrArg Subtype.val h), fun y ↦ by
      obtain ⟨s, hs⟩ := M.exists_family_eq (M.le_iSup_Idx W) y.2
      exact ⟨s, Subtype.ext hs⟩⟩

lemma sectionsEquiv_apply_coe {W : Opens X} (s : F.obj.obj (op W)) (q : M.Idx W) :
    (M.sectionsEquiv W s : ∀ q : M.Idx W, E q.1) q =
      (M.ε q.1).symm (F.obj.map (homOfLE q.2).op s) :=
  rfl

/-- The coordinate projection `∏_{Q q ≤ W} E q → ∏_{Q q ≤ W'} E q` for `W' ≤ W`. -/
def subResFun {W W' : Opens X} (h : W' ≤ W) (x : M.sub W) : M.sub W' :=
  ⟨fun q ↦ (x : ∀ q : M.Idx W, E q.1) ⟨q.1, q.2.trans h⟩,
    (M.mem_compat _).2 fun j₁ j₂ q h₁ h₂ ↦
      (M.mem_compat _).1 x.2 ⟨j₁.1, j₁.2.trans h⟩ ⟨j₂.1, j₂.2.trans h⟩ q h₁ h₂⟩

/-- The coordinate projection `∏_{Q q ≤ W} E q → ∏_{Q q ≤ W'} E q` for `W' ≤ W`, as a continuous
linear map between the models of the sections. -/
def subRes {W W' : Opens X} (h : W' ≤ W) : M.sub W →L[ℂ] M.sub W' where
  toFun := M.subResFun h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := Continuous.subtype_mk (continuous_pi fun q ↦
    (continuous_apply (⟨q.1, q.2.trans h⟩ : M.Idx W)).comp continuous_subtype_val) _

lemma subRes_apply_coe {W W' : Opens X} (h : W' ≤ W) (x : M.sub W) (q : M.Idx W') :
    (M.subRes h x : ∀ q : M.Idx W', E q.1) q = (x : ∀ q : M.Idx W, E q.1) ⟨q.1, q.2.trans h⟩ :=
  rfl

/-- Restriction of sections is the coordinate projection. -/
lemma sectionsEquiv_map {W W' : Opens X} (h : W' ≤ W) (s : F.obj.obj (op W)) :
    M.sectionsEquiv W' (F.obj.map (homOfLE h).op s) = M.subRes h (M.sectionsEquiv W s) := by
  ext q
  rw [sectionsEquiv_apply_coe, subRes_apply_coe, sectionsEquiv_apply_coe,
    ← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  rfl

end Sub

end SectionModel

end Basic

section Frechet

variable [∀ q, UniformSpace (E q)] [∀ q, IsUniformAddGroup (E q)] [∀ q, ContinuousSMul ℂ (E q)]
  [∀ q, T2Space (E q)] [∀ q, FirstCountableTopology (E q)] [∀ q, CompleteSpace (E q)]

namespace SectionModel

variable {F E} (M : SectionModel F E)

section Instances

variable {J : Type u} (v : J → 𝒬)

instance : IsUniformAddGroup (M.compat v) := (M.compat v).toAddSubgroup.isUniformAddGroup

instance : T2Space (M.compat v) := inferInstance

instance [Countable J] : FirstCountableTopology (M.compat v) :=
  TopologicalSpace.firstCountableTopology_induced _ (∀ j, E (v j)) ((↑) : M.compat v → _)

instance : CompleteSpace (M.compat v) := (M.isClosed_compat v).completeSpace_coe

instance [∀ q, LocallyConvexSpace ℝ (E q)] : LocallyConvexSpace ℝ (M.compat v) :=
  Topology.IsInducing.locallyConvexSpace (f := (M.compat v).subtype.restrictScalars ℝ)
    Topology.IsInducing.subtypeVal

end Instances

/-- **Locality of the model topology.** For a countable family of model opens `Q (v j) ≤ Q q`
covering `Q q`, the restrictions `E q → ∏ⱼ E (v j)` form a closed embedding. -/
theorem isClosedEmbedding_family {J : Type u} [Countable J] (q : 𝒬) (v : J → 𝒬)
    (hv : ∀ j, M.Q (v j) ≤ M.Q q) (hcov : M.Q q ≤ ⨆ j, M.Q (v j)) :
    IsClosedEmbedding (fun (x : E q) (j : J) ↦ M.res q (v j) (hv j) x) := by
  let Φ : E q →L[ℂ] (∀ j, E (v j)) := ContinuousLinearMap.pi fun j ↦ M.resL q (v j) (hv j)
  have hΦ : ∀ x, Φ x = M.family v hv (M.ε q x) := fun _ ↦ rfl
  let Φ' : E q →L[ℂ] M.compat v :=
    Φ.codRestrict (M.compat v) fun x ↦ (hΦ x).symm ▸ M.family_mem_compat v hv _
  have hinj : Function.Injective Φ' := fun x y hxy ↦ (M.ε q).injective
    (M.family_injective hcov (by rw [← hΦ, ← hΦ]; exact congrArg Subtype.val hxy))
  have hsurj : Function.Surjective Φ' := fun y ↦ by
    obtain ⟨s, hs⟩ := M.exists_family_eq hcov y.2
    exact ⟨(M.ε q).symm s, Subtype.ext ((hΦ _).trans (by rw [AddEquiv.apply_symm_apply]; exact hs))⟩
  have hemb : IsOpenEmbedding Φ' := IsOpenEmbedding.of_continuous_injective_isOpenMap
    Φ'.continuous hinj (Φ'.isOpenMap_of_surjective hsurj)
  have hcl : IsClosedEmbedding Φ' :=
    ⟨hemb.isEmbedding, by rw [hsurj.range_eq]; exact isClosed_univ⟩
  exact (M.isClosed_compat v).isClosedEmbedding_subtypeVal.comp hcl

omit [∀ q, IsUniformAddGroup (E q)] [∀ q, ContinuousSMul ℂ (E q)]
  [∀ q, FirstCountableTopology (E q)] [∀ q, CompleteSpace (E q)] in
/-- A compact subset of the model of the sections over `W'`: the families all of whose
coordinates lie in given compact sets. -/
lemma isCompact_setOf_forall_mem {W : Opens X} (L : ∀ q : M.Idx W, Set (E q.1))
    (hL : ∀ q, IsCompact (L q)) :
    IsCompact {y : M.sub W | ∀ q, (y : ∀ q : M.Idx W, E q.1) q ∈ L q} := by
  have : {y : M.sub W | ∀ q, (y : ∀ q : M.Idx W, E q.1) q ∈ L q} =
      Subtype.val ⁻¹' univ.pi L := by
    ext y
    simp
  rw [this]
  exact (M.isClosed_compat _).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_univ_pi hL)

variable [Countable 𝒬]

/-- **Restriction to a relatively compact open is a compact operator.** Assume that every point
of every open `W` lies in a model open `Q q'` with `Q q' ≤ Q q ≤ W` for which the restriction
`E q → E q'` is a compact operator. Then for `W'` with compact closure inside `W`, the
restriction `F(W) → F(W')` is a compact operator on the models. -/
theorem isCompactOperator_subRes
    (hK : ∀ (W : Opens X) (x : X), x ∈ W → ∃ (q q' : 𝒬) (h : M.Q q' ≤ M.Q q),
      x ∈ M.Q q' ∧ M.Q q ≤ W ∧ IsCompactOperator (M.resL q q' h))
    {W W' : Opens X} (h : W' ≤ W) (hc : IsCompact (closure (W' : Set X)))
    (hcl : closure (W' : Set X) ⊆ W) : IsCompactOperator (M.subRes h) := by
  classical
  choose qf qf' hqf hxq' hqW hcomp using fun x : closure (W' : Set X) ↦ hK W x.1 (hcl x.2)
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x : closure (W' : Set X) ↦
    (M.Q (qf' x) : Set X)) (fun x ↦ (M.Q (qf' x)).isOpen)
    (fun y hy ↦ mem_iUnion.2 ⟨⟨y, hy⟩, hxq' ⟨y, hy⟩⟩)
  choose K hKc hKn using fun k : t ↦ hcomp k.1
  have hqW' : ∀ k : t, M.Q (qf' k.1) ≤ W := fun k ↦ (hqf k.1).trans (hqW k.1)
  -- the neighbourhood of `0`
  let N : Set (M.sub W) := {x | ∀ k : t, (x : ∀ q : M.Idx W, E q.1) ⟨qf k.1, hqW k.1⟩ ∈
    M.resL (qf k.1) (qf' k.1) (hqf k.1) ⁻¹' K k}
  have hN : N ∈ 𝓝 (0 : M.sub W) := by
    refine (Filter.eventually_all.2 fun k ↦ ?_)
    exact ((continuous_apply _).comp continuous_subtype_val).continuousAt.preimage_mem_nhds
      (by simpa using hKn k)
  -- the compact set
  let J : M.Idx W' → Type u := fun q ↦ {p : t × 𝒬 // M.Q p.2 ≤ M.Q q.1 ⊓ M.Q (qf' p.1.1)}
  have hJv : ∀ q (p : J q), M.Q p.1.2 ≤ M.Q q.1 := fun q p ↦ p.2.trans inf_le_left
  have hJcov : ∀ q : M.Idx W', M.Q q.1 ≤ ⨆ p : J q, M.Q p.1.2 := fun q x hx ↦ by
    obtain ⟨k, hkt, hxk⟩ := mem_iUnion₂.1 (ht (subset_closure (q.2 hx)))
    obtain ⟨q'', hxq'', hq''⟩ := M.exists_mem_le (M.Q q.1 ⊓ M.Q (qf' k)) x ⟨hx, hxk⟩
    exact Opens.mem_iSup.2 ⟨⟨(⟨k, hkt⟩, q''), hq''⟩, hxq''⟩
  let L : ∀ q : M.Idx W', Set (E q.1) := fun q ↦
    (fun (x : E q.1) (p : J q) ↦ M.res q.1 p.1.2 (hJv q p) x) ⁻¹'
      univ.pi fun p ↦ M.res (qf' p.1.1.1) p.1.2 (p.2.trans inf_le_right) '' K p.1.1
  have hL : ∀ q, IsCompact (L q) := fun q ↦
    (M.isClosedEmbedding_family q.1 (fun p : J q ↦ p.1.2) (hJv q) (hJcov q)).isCompact_preimage
      (isCompact_univ_pi fun p ↦ (hKc p.1.1).image (M.resL _ _ _).continuous)
  refine ⟨_, M.isCompact_setOf_forall_mem L hL, Filter.mem_of_superset hN fun x hx q ↦ ?_⟩
  intro p _
  obtain ⟨⟨k, q''⟩, hq''⟩ := p
  have hk := hx k
  have hx₁ := (M.mem_compat _).1 x.2 ⟨q.1, q.2.trans h⟩ ⟨qf' k.1, hqW' k⟩ q''
    (hq''.trans inf_le_left) (hq''.trans inf_le_right)
  have hx₂ := (M.mem_compat _).1 x.2 ⟨qf k.1, hqW k.1⟩ ⟨qf' k.1, hqW' k⟩ (qf' k.1)
    (hqf k.1) le_rfl
  rw [res_self] at hx₂
  refine ⟨_, hk, ?_⟩
  rw [resL_apply, hx₂]
  exact hx₁.symm

end SectionModel

end Frechet

end TopCat.Sheaf

end
