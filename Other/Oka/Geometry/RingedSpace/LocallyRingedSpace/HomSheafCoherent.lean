/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.HomSheafPullbackIso
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.LocallyFree
public import Other.Oka.Geometry.RingedSpace.LocallyRingedSpace.CoherentLocalPresentation
public import Other.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Free

/-!
# The sheaf of homomorphisms between coherent sheaves is coherent

For coherent sheaves of modules `F`, `G` on a locally ringed space `Y`, the sheaf of homomorphisms
`𝓗om(F, G)` is coherent (`AlgebraicGeometry.LocallyRingedSpace.isCoherent_homSheaf`).

`𝓗om(-, G)` is an additive contravariant functor
(`AlgebraicGeometry.LocallyRingedSpace.homSheafMap`), so it turns biproducts into biproducts and
`𝓗om(𝒪ⁿ, G) ≅ Gⁿ` is coherent; it turns cokernels into kernels, so `𝓗om(F, G)` is coherent if `F`
is a cokernel of finite free sheaves. Every coherent `F` is locally such a cokernel, and on an
open `U`, `𝓗om(F, G)|_U ≅ 𝓗om(F|_U, G|_U)`
(`AlgebraicGeometry.LocallyRingedSpace.isIso_homSheafPullbackComp` for the open immersion).
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace AlgebraicGeometry.LocallyRingedSpace

variable {Y : LocallyRingedSpace.{u}}

section Functoriality

variable {F₁ F₂ F₃ : SheafOfModules.{u} Y.ringSheaf} (G : SheafOfModules.{u} Y.ringSheaf)

/-- **Contravariant functoriality of `𝓗om(-, G)`**: precomposition with `φ : F₁ ⟶ F₂`. -/
def homSheafMap (φ : F₁ ⟶ F₂) : homSheaf F₂ G ⟶ homSheaf F₁ G :=
  modHomMk (fun U ↦
      { toFun h := (φ ≫ (show F₂ ⟶ restrictExtend G U from h) : F₁ ⟶ restrictExtend G U)
        map_zero' := comp_zero
        map_add' _ _ := Preadditive.comp_add _ _ _ _ _ _ })
    (fun U a h ↦ (Category.assoc φ (show F₂ ⟶ restrictExtend G U from h)
      (restrictExtendSMul G U a)).symm)
    (fun U _ hVU h ↦ (Category.assoc φ (show F₂ ⟶ restrictExtend G U from h)
      (restrictExtendRes G hVU)).symm)

lemma homSheafMap_app (φ : F₁ ⟶ F₂) (U : Opens Y.toPresheafedSpace)
    (h : (homSheaf F₂ G).val.obj (op U)) :
    (homSheafMap G φ).val.app (op U) h =
      (φ ≫ (show F₂ ⟶ restrictExtend G U from h) : F₁ ⟶ restrictExtend G U) :=
  rfl

lemma homSheafMap_id : homSheafMap G (𝟙 F₁) = 𝟙 _ :=
  modHom_ext fun _ h ↦ Category.id_comp (show F₁ ⟶ _ from h)

lemma homSheafMap_comp (φ : F₁ ⟶ F₂) (ψ : F₂ ⟶ F₃) :
    homSheafMap G (φ ≫ ψ) = homSheafMap G ψ ≫ homSheafMap G φ :=
  modHom_ext fun _ h ↦ Category.assoc φ ψ (show F₃ ⟶ _ from h)

lemma homSheafMap_add (φ φ' : F₁ ⟶ F₂) :
    homSheafMap G (φ + φ') = homSheafMap G φ + homSheafMap G φ' :=
  modHom_ext fun _ h ↦ Preadditive.add_comp _ _ _ φ φ' (show F₂ ⟶ _ from h)

lemma homSheafMap_zero : homSheafMap G (0 : F₁ ⟶ F₂) = 0 :=
  modHom_ext fun _ h ↦ zero_comp (f := show F₂ ⟶ _ from h)

/-- `𝓗om(-, G)` sends isomorphisms to isomorphisms. -/
def homSheafMapIso (e : F₁ ≅ F₂) : homSheaf F₂ G ≅ homSheaf F₁ G where
  hom := homSheafMap G e.hom
  inv := homSheafMap G e.inv
  hom_inv_id := by rw [← homSheafMap_comp, e.inv_hom_id, homSheafMap_id]
  inv_hom_id := by rw [← homSheafMap_comp, e.hom_inv_id, homSheafMap_id]

/-- **`𝓗om(-, G)` turns biproducts into biproducts.** -/
def homSheafBiprodIso (A B : SheafOfModules.{u} Y.ringSheaf) :
    homSheaf (A ⊞ B) G ≅ homSheaf A G ⊞ homSheaf B G :=
  biprod.uniqueUpToIso _ _
    (isBinaryBilimitOfTotal
      { pt := homSheaf (A ⊞ B) G
        fst := homSheafMap G biprod.inl
        snd := homSheafMap G biprod.inr
        inl := homSheafMap G biprod.fst
        inr := homSheafMap G biprod.snd
        inl_fst := by rw [← homSheafMap_comp, biprod.inl_fst, homSheafMap_id]
        inl_snd := by rw [← homSheafMap_comp, biprod.inr_fst, homSheafMap_zero]
        inr_fst := by rw [← homSheafMap_comp, biprod.inl_snd, homSheafMap_zero]
        inr_snd := by rw [← homSheafMap_comp, biprod.inr_snd, homSheafMap_id] }
      (by
        dsimp
        rw [← homSheafMap_comp G biprod.fst biprod.inl, ← homSheafMap_comp G biprod.snd biprod.inr,
          ← homSheafMap_add, biprod.total, homSheafMap_id]))

end Functoriality

section Cokernel

variable {P₁ P₂ F : SheafOfModules.{u} Y.ringSheaf} (G : SheafOfModules.{u} Y.ringSheaf)
  (ψ : P₁ ⟶ P₂) (g : P₂ ⟶ F)

lemma homSheafMap_comp_homSheafMap_eq_zero (H : ψ ≫ g = 0) :
    homSheafMap G g ≫ homSheafMap G ψ = 0 := by
  rw [← homSheafMap_comp, H, homSheafMap_zero]

/-- **`𝓗om(-, G)` turns cokernels into kernels**: for a cokernel `P₁ ⟶ P₂ ⟶ F ⟶ 0`, the sequence
`0 ⟶ 𝓗om(F, G) ⟶ 𝓗om(P₂, G) ⟶ 𝓗om(P₁, G)` is exact. -/
lemma isIso_kernelLift_homSheafMap (H : ψ ≫ g = 0) (hc : IsColimit (CokernelCofork.ofπ g H)) :
    IsIso (kernel.lift (homSheafMap G ψ) (homSheafMap G g)
      (homSheafMap_comp_homSheafMap_eq_zero G ψ g H)) := by
  haveI : Epi g := epi_of_isColimit_cofork hc
  let L := kernel.lift (homSheafMap G ψ) (homSheafMap G g)
    (homSheafMap_comp_homSheafMap_eq_zero G ψ g H)
  have hL : ∀ U (h : (homSheaf F G).val.obj (op U)),
      (kernel.ι (homSheafMap G ψ)).val.app (op U) (L.val.app (op U) h) =
        (homSheafMap G g).val.app (op U) h := fun U h ↦
    congrArg (fun φ : homSheaf F G ⟶ homSheaf P₂ G ↦ φ.val.app (op U) h) (kernel.lift_ι _ _ _)
  refine (modIsoOfBijective L fun U ↦ ⟨fun h h' e ↦ ?_, fun k ↦ ?_⟩).isIso_hom
  · have e' := congrArg ((kernel.ι (homSheafMap G ψ)).val.app (op U)) e
    rw [hL, hL] at e'
    exact (cancel_epi g).1 e'
  · let b : P₂ ⟶ restrictExtend G U := (kernel.ι (homSheafMap G ψ)).val.app (op U) k
    have hb : ψ ≫ b = 0 :=
      SheafOfModules.val_app_apply_eq_zero_of_mem_kernel (homSheafMap G ψ) (op U) k
    let h : F ⟶ restrictExtend G U := hc.desc (CokernelCofork.ofπ b hb)
    have hh : g ≫ h = b := hc.fac (CokernelCofork.ofπ b hb) WalkingParallelPair.one
    refine ⟨h, SheafOfModules.kernel_ι_val_app_injective (homSheafMap G ψ) (op U) ?_⟩
    rw [hL]
    exact hh

end Cokernel

section Unit

/-- The structure sheaf is presented by the generator `1` and no relations. -/
def unitLocalPresentation : LocalPresentation (SheafOfModules.unit Y.ringSheaf) ⊤ where
  n := 1
  s _ := (1 : Y.presheaf.obj (op ⊤))
  gen W' _ t y hy := ⟨W', le_rfl, hy, fun _ ↦ t, by
    rw [Fin.sum_univ_one, modRes_self]
    change (show Y.presheaf.obj (op W') from t) = (show Y.presheaf.obj (op W') from t) *
      TopCat.Presheaf.restrictOpen (1 : Y.presheaf.obj (op ⊤)) W' le_top
    rw [yres_one, mul_one]⟩
  m := 0
  g := Fin.elim0
  rel l := l.elim0
  relgen W' _ a ha y hy := ⟨W', le_rfl, hy, Fin.elim0, fun i ↦ by
    rw [Fin.sum_univ_one] at ha
    change a 0 * TopCat.Presheaf.restrictOpen (1 : Y.presheaf.obj (op ⊤)) W' le_top = 0 at ha
    rw [yres_one, mul_one] at ha
    rw [Fin.sum_univ_zero, Subsingleton.elim i 0, ha, yres_zero]⟩

variable (G : SheafOfModules.{u} Y.ringSheaf)

lemma bijective_homSheafEval_unit (U : Opens Y.toPresheafedSpace) :
    Function.Bijective
      ((homSheafEval G ((unitLocalPresentation (Y := Y)).s ⟨0, Nat.one_pos⟩)).val.app (op U)) := by
  let P := unitLocalPresentation (Y := Y)
  refine ⟨fun h h' e ↦ ?_, fun z ↦ ?_⟩
  · rw [← sub_eq_zero, ← map_sub] at e
    refine sub_eq_zero.1 (P.toLocalGenerators.homSec_eq_zero G le_top _ fun i ↦ ?_)
    have e' := congrArg (fun w ↦ modRes (N := G) (restrictExtendSec w) (⊤ ⊓ U) (by order)) e
    simp only [restrictExtendSec_homSheafEval, modRes_res, modRes_self,
      restrictExtendSec_zero, modRes_zero] at e'
    exact e'
  · let k : Fin P.n → G.val.obj (op U) := fun _ ↦ modRes (restrictExtendSec z) U (by order)
    refine ⟨P.homSecOf G le_top k (fun l ↦ (show Fin 0 from l).elim0), restrictExtend_ext ?_⟩
    rw [restrictExtendSec_homSheafEval]
    erw [P.homSecOf_s G le_top k (fun l ↦ (show Fin 0 from l).elim0) ⟨0, Nat.one_pos⟩]
    simp only [k, modRes_res, modRes_self]

/-- **`𝓗om(𝒪, G) ≅ G`**, by evaluation at `1`. -/
def homSheafUnitIso : homSheaf (SheafOfModules.unit Y.ringSheaf) G ≅ G :=
  modIsoOfBijective _ (bijective_homSheafEval_unit G) ≪≫ (restrictExtendTopIso G).symm

end Unit

section Coherence

/-- A zero sheaf of modules is coherent. -/
lemma isCoherent_of_isZero {M : SheafOfModules.{u} Y.ringSheaf} (hM : IsZero M) : M.IsCoherent := by
  have hempty : (SheafOfModules.free (R := Y.ringSheaf) PEmpty.{u + 1}).IsCoherent := by
    constructor
    · exact inferInstance
    intro X K _ φ
    haveI : HasBinaryProducts (Over X) := Over.ConstructProducts.over_binaryProduct_of_pullback
    have hz : IsZero ((SheafOfModules.free (R := Y.ringSheaf) PEmpty.{u + 1}).over X) :=
      (SheafOfModules.isZero_free_of_isEmpty (R := Y.ringSheaf.over X) PEmpty.{u + 1}).of_iso
        (SheafOfModules.overFreeIso _ X).symm
    obtain rfl := hz.eq_zero_of_tgt φ
    exact SheafOfModules.IsFiniteType.of_iso
      (M := SheafOfModules.free (R := Y.ringSheaf.over X) K) kernelZeroIsoSource.symm
  exact SheafOfModules.IsCoherent.of_iso.{u}
    ((SheafOfModules.isZero_free_of_isEmpty (R := Y.ringSheaf) PEmpty.{u + 1}).iso hM)

/-- A biproduct of sheaves of modules of finite type is of finite type. -/
lemma isFiniteType_biprod (A B : SheafOfModules.{u} Y.ringSheaf) [A.IsFiniteType]
    [B.IsFiniteType] : (A ⊞ B).IsFiniteType := by
  refine isFiniteType_of_isLocallyFinitelyGeneratedModule _ fun x ↦ (?_ :
    ∃ (W : Opens Y.toPresheafedSpace) (k : ℕ) (s : Fin k → (A ⊞ B).val.obj (op W)), x ∈ W ∧
      ∀ (W' : Opens Y.toPresheafedSpace) (hW' : W' ≤ W) (t : (A ⊞ B).val.obj (op W')), ∀ y ∈ W',
        ∃ (W'' : Opens Y.toPresheafedSpace) (hW'' : W'' ≤ W'), y ∈ W'' ∧
          ∃ c : Fin k → Y.presheaf.obj (op W''),
            modRes t W'' hW'' = ∑ l, c l • modRes (s l) W'' (hW''.trans hW'))
  obtain ⟨WA, p, a, hxA, hA⟩ : ∃ (W₀ : Opens Y.toPresheafedSpace) (k : ℕ)
      (u : Fin k → A.val.obj (op W₀)), x ∈ W₀ ∧ ∀ (W' : Opens Y.toPresheafedSpace)
      (hW' : W' ≤ W₀) (t : A.val.obj (op W')), ∀ y ∈ W',
        ∃ (W'' : Opens Y.toPresheafedSpace) (hW'' : W'' ≤ W'), y ∈ W'' ∧
          ∃ c : Fin k → Y.presheaf.obj (op W''),
            modRes t W'' hW'' = ∑ l, c l • modRes (u l) W'' (hW''.trans hW') :=
    isLocallyFinitelyGeneratedModule_of_isFiniteType A x
  obtain ⟨WB, q, b, hxB, hB⟩ : ∃ (W₀ : Opens Y.toPresheafedSpace) (k : ℕ)
      (u : Fin k → B.val.obj (op W₀)), x ∈ W₀ ∧ ∀ (W' : Opens Y.toPresheafedSpace)
      (hW' : W' ≤ W₀) (t : B.val.obj (op W')), ∀ y ∈ W',
        ∃ (W'' : Opens Y.toPresheafedSpace) (hW'' : W'' ≤ W'), y ∈ W'' ∧
          ∃ c : Fin k → Y.presheaf.obj (op W''),
            modRes t W'' hW'' = ∑ l, c l • modRes (u l) W'' (hW''.trans hW') :=
    isLocallyFinitelyGeneratedModule_of_isFiniteType B x
  let inl : A ⟶ A ⊞ B := biprod.inl
  let inr : B ⟶ A ⊞ B := biprod.inr
  refine ⟨WA ⊓ WB, p + q, Fin.append
    (fun i ↦ inl.val.app (op (WA ⊓ WB)) (modRes (a i) (WA ⊓ WB) inf_le_left))
    (fun j ↦ inr.val.app (op (WA ⊓ WB)) (modRes (b j) (WA ⊓ WB) inf_le_right)), ⟨hxA, hxB⟩,
    fun W' hW' t y hy ↦ ?_⟩
  have htot : t = inl.val.app (op W') ((biprod.fst : A ⊞ B ⟶ A).val.app (op W') t) +
      inr.val.app (op W') ((biprod.snd : A ⊞ B ⟶ B).val.app (op W') t) :=
    (congrArg (fun φ : A ⊞ B ⟶ A ⊞ B ↦ φ.val.app (op W') t) biprod.total).symm
  obtain ⟨W₁, h₁, hy₁, c, hc⟩ :=
    hA W' (hW'.trans inf_le_left) ((biprod.fst : A ⊞ B ⟶ A).val.app (op W') t) y hy
  obtain ⟨W₂, h₂, hy₂, d, hd⟩ := hB W₁ (h₁.trans (hW'.trans inf_le_right))
    (modRes ((biprod.snd : A ⊞ B ⟶ B).val.app (op W') t) W₁ h₁) y hy₁
  refine ⟨W₂, h₂.trans h₁, hy₂, Fin.append (fun i ↦ TopCat.Presheaf.restrictOpen (c i) W₂ h₂) d,
    ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  conv_lhs => rw [htot]
  have eA : modRes ((biprod.fst : A ⊞ B ⟶ A).val.app (op W') t) W₂ (h₂.trans h₁) =
      ∑ i, TopCat.Presheaf.restrictOpen (c i) W₂ h₂ •
        modRes (modRes (a i) (WA ⊓ WB) inf_le_left) W₂ (h₂.trans (h₁.trans hW')) := by
    refine (modRes_res _ _ _).symm.trans ((congrArg (fun z ↦ modRes z W₂ h₂) hc).trans
      ((modRes_sum_smul_of h₂ c _).trans (Finset.sum_congr rfl fun i _ ↦ ?_)))
    rw [modRes_res, modRes_res]
  have eB : modRes ((biprod.snd : A ⊞ B ⟶ B).val.app (op W') t) W₂ (h₂.trans h₁) =
      ∑ j, d j • modRes (modRes (b j) (WA ⊓ WB) inf_le_right) W₂ (h₂.trans (h₁.trans hW')) := by
    refine (modRes_res _ _ _).symm.trans (hd.trans (Finset.sum_congr rfl fun j _ ↦ ?_))
    rw [modRes_res]
  rw [modRes_add, ← modHom_modRes inl, ← modHom_modRes inr, eA, eB, map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [modHom_smul, modHom_modRes]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [modHom_smul, modHom_modRes]


/-- `𝓗om(F, G)` vanishes if `F` does. -/
lemma isZero_homSheaf {F : SheafOfModules.{u} Y.ringSheaf} (hF : IsZero F)
    (G : SheafOfModules.{u} Y.ringSheaf) : IsZero (homSheaf F G) :=
  (IsZero.iff_id_eq_zero _).2 (modHom_ext fun _ _ ↦ hF.eq_of_src _ _)

set_option maxHeartbeats 400000 in
-- the induction motive is compared with the statements of the induction steps, whose coherence
-- instances are elaborated separately
/-- **`𝓗om(𝒪ⁿ, G)` is coherent** for `G` coherent. -/
lemma isCoherent_homSheaf_free (G : SheafOfModules.{u} Y.ringSheaf) [G.IsCoherent] (K : Type u)
    [Finite K] : (homSheaf (SheafOfModules.free (R := Y.ringSheaf) K) G).IsCoherent := by
  have hequiv : ∀ {α β : Type u}, α ≃ β →
      (homSheaf (SheafOfModules.free (R := Y.ringSheaf) α) G).IsCoherent →
      (homSheaf (SheafOfModules.free (R := Y.ringSheaf) β) G).IsCoherent := fun e h ↦
    haveI := h
    SheafOfModules.IsCoherent.of_iso.{u}
      (homSheafMapIso G (SheafOfModules.freeCongr (R := Y.ringSheaf) e)).symm
  have hempty : (homSheaf (SheafOfModules.free (R := Y.ringSheaf) PEmpty.{u + 1}) G).IsCoherent :=
    isCoherent_of_isZero (isZero_homSheaf
      (SheafOfModules.isZero_free_of_isEmpty (R := Y.ringSheaf) PEmpty.{u + 1}) G)
  have hoption : ∀ {α : Type u} [Fintype α],
      (homSheaf (SheafOfModules.free (R := Y.ringSheaf) α) G).IsCoherent →
      (homSheaf (SheafOfModules.free (R := Y.ringSheaf) (Option α)) G).IsCoherent := by
    intro α _ h
    haveI := h
    haveI : (homSheaf (SheafOfModules.free (R := Y.ringSheaf) PUnit.{u + 1}) G).IsCoherent :=
      SheafOfModules.IsCoherent.of_iso.{u}
        ((homSheafUnitIso G).symm ≪≫
          homSheafMapIso G (SheafOfModules.freePUnitIso (R := Y.ringSheaf)))
    haveI := isFiniteType_biprod (homSheaf (SheafOfModules.free (R := Y.ringSheaf) α) G)
      (homSheaf (SheafOfModules.free (R := Y.ringSheaf) PUnit.{u + 1}) G)
    haveI : (homSheaf (SheafOfModules.free (R := Y.ringSheaf) α) G ⊞
        homSheaf (SheafOfModules.free (R := Y.ringSheaf) PUnit.{u + 1}) G).IsCoherent :=
      SheafOfModules.IsCoherent.biprod
    exact SheafOfModules.IsCoherent.of_iso.{u}
      ((homSheafBiprodIso G (SheafOfModules.free (R := Y.ringSheaf) α)
        (SheafOfModules.free (R := Y.ringSheaf) PUnit.{u + 1})).symm ≪≫ homSheafMapIso G
        (SheafOfModules.freeCongr (R := Y.ringSheaf) (Equiv.optionEquivSumPUnit α) ≪≫
          SheafOfModules.freeSumBiprodIso (R := Y.ringSheaf) α PUnit.{u + 1}))
  exact Finite.induction_empty_option
    (P := fun α ↦ (homSheaf (SheafOfModules.free (R := Y.ringSheaf) α) G).IsCoherent)
    (fun e h ↦ hequiv e h) hempty (fun h ↦ hoption h) K

/-- `𝓗om(F, G)` is coherent if `F` is the cokernel of a morphism of finite free sheaves and `G`
is coherent. -/
lemma isCoherent_homSheaf_of_isColimit {F : SheafOfModules.{u} Y.ringSheaf}
    (G : SheafOfModules.{u} Y.ringSheaf) [G.IsCoherent] {I K : Type u} [Finite I] [Finite K]
    (ψ : SheafOfModules.free (R := Y.ringSheaf) I ⟶ SheafOfModules.free K)
    (g : SheafOfModules.free K ⟶ F) (H : ψ ≫ g = 0)
    (hc : IsColimit (CokernelCofork.ofπ g H)) : (homSheaf F G).IsCoherent := by
  haveI := isCoherent_homSheaf_free G K
  haveI := isCoherent_homSheaf_free G I
  haveI := isIso_kernelLift_homSheafMap G ψ g H hc
  haveI : (kernel (homSheafMap G ψ)).IsCoherent := SheafOfModules.IsCoherent.kernel _
  exact SheafOfModules.IsCoherent.of_iso.{u} (asIso (kernel.lift (homSheafMap G ψ)
    (homSheafMap G g) (homSheafMap_comp_homSheafMap_eq_zero G ψ g H))).symm

/-- **The sheaf of homomorphisms between coherent sheaves is coherent.** -/
theorem isCoherent_homSheaf (F G : SheafOfModules.{u} Y.ringSheaf) [F.IsCoherent]
    [G.IsCoherent] : (homSheaf F G).IsCoherent := by
  refine isCoherent_of_isCoherent_restrictModules Y _ fun y ↦ ?_
  obtain ⟨U, hy, I, K, _, _, ψ, g, H, ⟨hc⟩⟩ := exists_restrictModules_isColimit_cokernelCofork Y F y
  refine ⟨U, hy, ?_⟩
  haveI : ((Y.ofRestrict U.isOpenEmbedding).pullbackModules.obj F).IsCoherent :=
    isCoherent_restrictModules F U
  haveI : ((Y.ofRestrict U.isOpenEmbedding).pullbackModules.obj G).IsCoherent :=
    isCoherent_restrictModules G U
  haveI := isIso_homSheafPullbackComp (Y.ofRestrict U.isOpenEmbedding) F G
    (flat_stalkMap_of_isIso _)
  haveI : ((Y.restrictModules U).obj G).IsCoherent := isCoherent_restrictModules G U
  exact @SheafOfModules.IsCoherent.of_iso.{u} _ _ _ _ _ _ _ _ _ _
    (asIso (homSheafPullbackComp (Y.ofRestrict U.isOpenEmbedding) F G)).symm
    (isCoherent_homSheaf_of_isColimit ((Y.restrictModules U).obj G) ψ g H hc)

end Coherence

end AlgebraicGeometry.LocallyRingedSpace

end
