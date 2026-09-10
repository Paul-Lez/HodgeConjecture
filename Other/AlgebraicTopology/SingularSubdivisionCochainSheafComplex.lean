/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicTopology.SingularSubdivisionCochainSheaf
public import Other.AlgebraicTopology.SingularExcisionComplex

import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Complex singular cochains and sheafification

The small-chain argument for complex-valued singular cochains.  It supplies the
complex-coefficient global comparison corresponding to the rational comparison in
\`SingularSubdivisionCochainSheaf\`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Simplicial

namespace AlgebraicTopology.Singular

section ComplexCover

variable {κ : Type} (Y : TopCat.{0}) (U : κ → Set Y)

/-- Restriction of complex singular cochains to chains subordinate to a family of subsets. -/
def complexCochainRestrictionToCoverSmall :
    ((TopCat.toSSet.obj Y).chainComplex
        (ModuleCat.of ℂ ℂ)).linearDualCochainComplex ⟶
      (CoverSmallComplexSingularChainComplex Y U).linearDualCochainComplex :=
  HomologicalComplex.linearDualMap (coverSmallComplexSingularChainInclusion Y U)

/-- The chain map from one member of a family into the cover-small complex chains. -/
def coverMemberToSmallComplexSingularChains (j : κ) :
    (TopCat.toSSet.obj (TopCat.of (U j))).chainComplex (ModuleCat.of ℂ ℂ) ⟶
      CoverSmallComplexSingularChainComplex Y U :=
  SSet.chainComplexMap (coverMemberToSmallSingularSet Y U j) (ModuleCat.of ℂ ℂ)

@[reassoc]
lemma coverMemberToSmallComplexSingularChains_comp_inclusion (j : κ) :
    coverMemberToSmallComplexSingularChains Y U j ≫
        coverSmallComplexSingularChainInclusion Y U =
      SSet.chainComplexMap
        (TopCat.toSSet.map (topologicalSubsetInclusion Y (U j)))
        (ModuleCat.of ℂ ℂ) := by
  change ((SSet.chainComplexFunctor (ModuleCat ℂ)).obj
      (ModuleCat.of ℂ ℂ)).map (coverMemberToSmallSingularSet Y U j) ≫
    ((SSet.chainComplexFunctor (ModuleCat ℂ)).obj
      (ModuleCat.of ℂ ℂ)).map (coverSmallSingularSubcomplex Y U).ι = _
  rw [← Functor.map_comp, coverMemberToSmallSingularSet_comp_inclusion]

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing on every member of a covering sieve implies vanishing on all chains subordinate
to the associated family of open subsets. -/
lemma complexCochainRestrictionToCoveringSieve_eq_zero
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (n : ℕ)
    (φ : ((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of ℂ ℂ)).linearDualCochainComplex.X n)
    (hφ : ∀ I : S.Arrow,
      (singularCochainPresheaf ℂ Y n).map I.f.op
        ((singularCochainComplexIsoTopOpen ℂ Y).hom.f n φ) = 0) :
    (complexCochainRestrictionToCoverSmall Y
      (coveringSieveOpenFamily Y S)).f n φ = 0 := by
  change Module.Dual ℂ
    (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℂ ℂ)).X n) at φ
  change ((coverSmallComplexSingularChainInclusion Y
    (coveringSieveOpenFamily Y S)).f n).hom.dualMap φ = 0
  apply_fun ModuleCat.ofHom
  apply SSet.chainComplex_hom_ext
  intro x
  obtain ⟨I, y, hy⟩ :=
    (mem_coverSmallSingularSubcomplex_iff_exists_preimage Y
      (coveringSieveOpenFamily Y S) x.1).mp x.2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have hI := congrArg
    (fun ψ : OpenCochains ℂ Y (.op I.Y) n ↦ ψ
      (((TopCat.toSSet.obj (TopCat.of (coveringSieveOpenFamily Y S I))).ιChainComplex
        (R := ModuleCat.of ℂ ℂ) y).hom a))
    (hφ I)
  dsimp only [singularCochainPresheaf, singularCochainComplexIsoTopOpen,
    HomologicalComplex.linearDualIso, HomologicalComplex.linearDualMap] at hI
  change φ (ModuleCat.Hom.hom
      (((openSingularChainComplexFunctor ℂ Y).map I.f).f n ≫
        (topOpenSingularChainComplexIso ℂ Y).hom.f n)
      (((TopCat.toSSet.obj (TopCat.of (coveringSieveOpenFamily Y S I))).ιChainComplex
        (R := ModuleCat.of ℂ ℂ) y).hom a)) = 0 at hI
  have hchain := HomologicalComplex.congr_hom
    (openSingularChainToTop_comp_topOpenIso ℂ Y I.f) n
  have hchain' :
      ((openSingularChainComplexFunctor ℂ Y).map I.f).f n ≫
          (topOpenSingularChainComplexIso ℂ Y).hom.f n =
        (SSet.chainComplexMap
          (TopCat.toSSet.map (topologicalSubsetInclusion Y I.Y))
          (ModuleCat.of ℂ ℂ)).f n := by
    simpa only [HomologicalComplex.comp_f] using hchain
  rw [hchain'] at hI
  have hiota := ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f
      (TopCat.toSSet.obj (TopCat.of (coveringSieveOpenFamily Y S I)))
      (TopCat.toSSet.obj Y)
      (TopCat.toSSet.map (topologicalSubsetInclusion Y
        (coveringSieveOpenFamily Y S I)))
      (ModuleCat.of ℂ ℂ) y) a
  simp only [ConcreteCategory.comp_apply] at hiota
  have hI' : φ
      (((TopCat.toSSet.obj Y).ιChainComplex
        (R := ModuleCat.of ℂ ℂ)
        ((TopCat.toSSet.map (topologicalSubsetInclusion Y
          (coveringSieveOpenFamily Y S I))).app _ y)).hom a) = 0 := by
    calc
      _ = φ ((SSet.chainComplexMap
          (TopCat.toSSet.map (topologicalSubsetInclusion Y
            (coveringSieveOpenFamily Y S I)))
          (ModuleCat.of ℂ ℂ)).f n
          (((TopCat.toSSet.obj
            (TopCat.of (coveringSieveOpenFamily Y S I))).ιChainComplex
              (R := ModuleCat.of ℂ ℂ) y).hom a)) := congrArg φ hiota.symm
      _ = 0 := hI
  change φ (ModuleCat.Hom.hom
    (((coverSmallSingularSubcomplex Y
      (coveringSieveOpenFamily Y S) : SSet).ιChainComplex
        (R := ModuleCat.of ℂ ℂ) x) ≫
      (coverSmallComplexSingularChainInclusion Y
        (coveringSieveOpenFamily Y S)).f n) a) = 0
  dsimp only [coverSmallComplexSingularChainInclusion] at ⊢
  rw [SSet.ι_chainComplexMap_f]
  simpa [hy] using hI'
  · intro f g h
    exact congrArg ModuleCat.Hom.hom h

set_option backward.isDefEq.respectTransparency false in
/-- Conversely, vanishing on the cover-small chains associated to a covering sieve implies
vanishing after restriction along every arrow of that sieve. -/
lemma complexCochainRestrictionToCoveringSieve_local_zero
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (n : ℕ)
    (φ : ((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of ℂ ℂ)).linearDualCochainComplex.X n)
    (hφ : (complexCochainRestrictionToCoverSmall Y
      (coveringSieveOpenFamily Y S)).f n φ = 0) :
    ∀ I : S.Arrow,
      (singularCochainPresheaf ℂ Y n).map I.f.op
        ((singularCochainComplexIsoTopOpen ℂ Y).hom.f n φ) = 0 := by
  intro I
  change Module.Dual ℂ
    (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℂ ℂ)).X n) at φ
  change ((coverSmallComplexSingularChainInclusion Y
    (coveringSieveOpenFamily Y S)).f n).hom.dualMap φ = 0 at hφ
  change (((openSingularChainComplexFunctor ℂ Y).map I.f).f n).hom.dualMap
    (((topOpenSingularChainComplexIso ℂ Y).hom.f n).hom.dualMap φ) = 0
  apply LinearMap.ext
  intro c
  have hc := LinearMap.congr_fun hφ
    (((coverMemberToSmallComplexSingularChains Y
      (coveringSieveOpenFamily Y S) I).f n).hom c)
  have htop := HomologicalComplex.congr_hom
    (openSingularChainToTop_comp_topOpenIso ℂ Y I.f) n
  have hmember := HomologicalComplex.congr_hom
    (coverMemberToSmallComplexSingularChains_comp_inclusion Y
      (coveringSieveOpenFamily Y S) I) n
  simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at hc ⊢
  calc
    φ ((topOpenSingularChainComplexIso ℂ Y).hom.f n
        (((openSingularChainComplexFunctor ℂ Y).map I.f).f n c)) =
      φ ((SSet.chainComplexMap
        (TopCat.toSSet.map (topologicalSubsetInclusion Y I.Y))
        (ModuleCat.of ℂ ℂ)).f n c) :=
          congrArg φ (ConcreteCategory.congr_hom htop c)
    _ = φ ((coverSmallComplexSingularChainInclusion Y
          (coveringSieveOpenFamily Y S)).f n
        ((coverMemberToSmallComplexSingularChains Y
          (coveringSieveOpenFamily Y S) I).f n c)) :=
            congrArg φ (ConcreteCategory.congr_hom hmember c).symm
    _ = 0 := hc

/-- Restriction to cover-small complex chains is surjective in every cochain degree. -/
lemma complexCochainRestrictionToCoverSmall_surjective (n : ℕ) :
    Function.Surjective ((complexCochainRestrictionToCoverSmall Y U).f n) := by
  apply LinearMap.dualMap_surjective_of_injective
  rw [← ModuleCat.mono_iff_injective]
  exact Functor.map_mono
    (HomologicalComplex.eval (ModuleCat ℂ) (ComplexShape.down ℕ) n)
    (coverSmallComplexSingularChainInclusion Y U)

/-- Restriction to cover-small complex chains is an epimorphism of cochain complexes. -/
instance complexCochainRestrictionToCoverSmall_epi :
    Epi (complexCochainRestrictionToCoverSmall Y U) :=
  HomologicalComplex.epi_of_epi_f _ fun n ↦ by
    rw [ModuleCat.epi_iff_surjective]
    exact complexCochainRestrictionToCoverSmall_surjective Y U n

/-- An open cover gives a homotopy equivalence from all complex cochains to its cover-small
cochains. -/
def complexCochainHomotopyEquivCoverSmall
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomotopyEquiv
      ((TopCat.toSSet.obj Y).chainComplex
        (ModuleCat.of ℂ ℂ)).linearDualCochainComplex
      (CoverSmallComplexSingularChainComplex Y U).linearDualCochainComplex :=
  HomologicalComplex.linearDualHomotopyEquiv
    (coverSmallComplexChainHomotopyEquiv_of_openCover Y U hUopen hUcover)

lemma complexCochainHomotopyEquivCoverSmall_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (complexCochainHomotopyEquivCoverSmall Y U hUopen hUcover).hom =
      complexCochainRestrictionToCoverSmall Y U := by
  dsimp [complexCochainHomotopyEquivCoverSmall,
    complexCochainRestrictionToCoverSmall]
  change HomologicalComplex.linearDualMap
      (coverSmallComplexChainHomotopyEquiv_of_openCover
        Y U hUopen hUcover).hom = _
  rw [coverSmallComplexChainHomotopyEquiv_of_openCover_hom]

/-- Restriction from all complex cochains to cover-small cochains is a quasi-isomorphism for an
open cover. -/
theorem complexCochainRestrictionToCoverSmall_quasiIso
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (complexCochainRestrictionToCoverSmall Y U) := by
  rw [← complexCochainHomotopyEquivCoverSmall_hom Y U hUopen hUcover]
  infer_instance

/-- The complex of complex cochains vanishing on every chain subordinate to an open cover is
acyclic. -/
theorem complexCoverSmallCochainKernel_acyclic
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (kernel (complexCochainRestrictionToCoverSmall Y U)).Acyclic := by
  let := complexCochainRestrictionToCoverSmall_quasiIso Y U hUopen hUcover
  exact HomologicalComplex.kernel_acyclic_of_epi_of_quasiIso
    (complexCochainRestrictionToCoverSmall Y U)

set_option backward.isDefEq.respectTransparency false in
/-- A closed complex cochain which vanishes on all cover-small chains has a primitive which
also vanishes on all cover-small chains. -/
theorem exists_complexCoverSmallKernel_primitive
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ)
    (φ : ((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of ℂ ℂ)).linearDualCochainComplex.X n)
    (hφsmall : (complexCochainRestrictionToCoverSmall Y U).f n φ = 0)
    (hφclosed : (((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of ℂ ℂ)).linearDualCochainComplex.d n (n + 1)) φ = 0) :
    ∃ ψ : ((TopCat.toSSet.obj Y).chainComplex
        (ModuleCat.of ℂ ℂ)).linearDualCochainComplex.X
          ((ComplexShape.up ℕ).prev n),
      (((TopCat.toSSet.obj Y).chainComplex
          (ModuleCat.of ℂ ℂ)).linearDualCochainComplex.sc n).f ψ = φ ∧
        (complexCochainRestrictionToCoverSmall Y U).f
          ((ComplexShape.up ℕ).prev n) ψ = 0 := by
  let F := ((TopCat.toSSet.obj Y).chainComplex
    (ModuleCat.of ℂ ℂ)).linearDualCochainComplex
  let q := complexCochainRestrictionToCoverSmall Y U
  let K := kernel q
  let E : (kernel q).X n ≅ ModuleCat.of ℂ (q.f n).hom.ker :=
    asIso (kernelComparison q (HomologicalComplex.eval (ModuleCat ℂ)
      (ComplexShape.up ℕ) n)) ≪≫ ModuleCat.kernelIsoKer (q.f n)
  let z : (kernel q).X n := E.inv ⟨φ, hφsmall⟩
  have hzmap : (kernel.ι q).f n z = φ := by
    let ev := HomologicalComplex.eval (ModuleCat ℂ) (ComplexShape.up ℕ) n
    have hc := ConcreteCategory.congr_hom (kernelComparison_comp_ι q ev) z
    have hk := ModuleCat.kernelIsoKer_hom_ker_subtype_apply
      (q.f n) ((kernelComparison q ev) z)
    have hE : E.hom z = (⟨φ, hφsmall⟩ : (q.f n).hom.ker) := by
      simp [z]
    calc
      (kernel.ι q).f n z = kernel.ι (ev.map q) ((kernelComparison q ev) z) := hc.symm
      _ = ((ModuleCat.kernelIsoKer (q.f n)).hom
          ((kernelComparison q ev) z)).1 := hk.symm
      _ = φ := congrArg Subtype.val hE
  have hzclosed : (K.sc n).g z = 0 := by
    change K.d n ((ComplexShape.up ℕ).next n) z = 0
    rw [show (ComplexShape.up ℕ).next n = n + 1 by simp]
    apply (ModuleCat.mono_iff_injective ((kernel.ι q).f (n + 1))).mp inferInstance
    rw [map_zero]
    change (K.d n (n + 1) ≫ (kernel.ι q).f (n + 1)) z = 0
    rw [← (kernel.ι q).comm n (n + 1)]
    change F.d n (n + 1) ((kernel.ι q).f n z) = 0
    rw [hzmap]
    exact hφclosed
  have hacyclic := complexCoverSmallCochainKernel_acyclic Y U hUopen hUcover
  obtain ⟨p, hp⟩ := (ShortComplex.moduleCat_exact_iff (K.sc n)).mp
    (hacyclic n) z hzclosed
  change K.X ((ComplexShape.up ℕ).prev n) at p
  change K.d ((ComplexShape.up ℕ).prev n) n p = z at hp
  refine ⟨(kernel.ι q).f ((ComplexShape.up ℕ).prev n) p, ?_, ?_⟩
  · change F.d ((ComplexShape.up ℕ).prev n) n
      ((kernel.ι q).f ((ComplexShape.up ℕ).prev n) p) = φ
    calc
      _ = (kernel.ι q).f n
          (K.d ((ComplexShape.up ℕ).prev n) n p) :=
        by
          simpa only [ConcreteCategory.comp_apply, F, K] using
            (ConcreteCategory.congr_hom
              ((kernel.ι q).comm ((ComplexShape.up ℕ).prev n) n) p)
      _ = φ := by rw [hp, hzmap]
  · have hcondition := HomologicalComplex.congr_hom (kernel.condition q)
      ((ComplexShape.up ℕ).prev n)
    exact ConcreteCategory.congr_hom hcondition p

set_option backward.isDefEq.respectTransparency false in
/-- A closed cochain on the top open which vanishes along a covering sieve has a primitive that
still vanishes along the same sieve. -/
theorem exists_topOpenComplexLocallyZero_primitive
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (n : ℕ)
    (φ : (TopOpenSingularChainComplex ℂ Y).linearDualCochainComplex.X n)
    (hφlocal : ∀ I : S.Arrow,
      (singularCochainPresheaf ℂ Y n).map I.f.op φ = 0)
    (hφclosed : ((TopOpenSingularChainComplex ℂ Y).linearDualCochainComplex.d
      n (n + 1)) φ = 0) :
    ∃ ψ : (TopOpenSingularChainComplex ℂ Y).linearDualCochainComplex.X
        ((ComplexShape.up ℕ).prev n),
      ((TopOpenSingularChainComplex ℂ Y).linearDualCochainComplex.sc n).f ψ = φ ∧
        ∀ I : S.Arrow,
          (singularCochainPresheaf ℂ Y ((ComplexShape.up ℕ).prev n)).map I.f.op ψ = 0 := by
  let A := (SingularChainComplex ℂ Y).linearDualCochainComplex
  let B := (TopOpenSingularChainComplex ℂ Y).linearDualCochainComplex
  let e := singularCochainComplexIsoTopOpen ℂ Y
  let φ' : A.X n := e.inv.f n φ
  have heφ : e.hom.f n φ' = φ := by
    have hc := ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom e.inv_hom_id n) φ
    simpa only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
      HomologicalComplex.id_f, ConcreteCategory.id_apply, φ'] using hc
  have hlocal' : ∀ I : S.Arrow,
      (singularCochainPresheaf ℂ Y n).map I.f.op (e.hom.f n φ') = 0 := by
    intro I
    rw [heφ]
    exact hφlocal I
  have hsmall : (complexCochainRestrictionToCoverSmall Y
      (coveringSieveOpenFamily Y S)).f n φ' = 0 :=
    complexCochainRestrictionToCoveringSieve_eq_zero Y S n φ' hlocal'
  have hclosed' : A.d n (n + 1) φ' = 0 := by
    change A.d n (n + 1) (e.inv.f n φ) = 0
    have hc := ConcreteCategory.congr_hom (e.inv.comm n (n + 1)) φ
    calc
      _ = e.inv.f (n + 1) (B.d n (n + 1) φ) := by
        simpa only [ConcreteCategory.comp_apply, A, B] using hc
      _ = 0 := by rw [hφclosed, map_zero]
  obtain ⟨ψ, hψ, hψsmall⟩ := exists_complexCoverSmallKernel_primitive Y
    (coveringSieveOpenFamily Y S)
    (coveringSieveOpenFamily_isOpen Y S)
    (coveringSieveOpenFamily_iUnion Y S) n φ' hsmall hclosed'
  change A.X ((ComplexShape.up ℕ).prev n) at ψ
  change A.d ((ComplexShape.up ℕ).prev n) n ψ = φ' at hψ
  refine ⟨e.hom.f ((ComplexShape.up ℕ).prev n) ψ, ?_, ?_⟩
  · change B.d ((ComplexShape.up ℕ).prev n) n
      (e.hom.f ((ComplexShape.up ℕ).prev n) ψ) = φ
    have hc := ConcreteCategory.congr_hom
      (e.hom.comm ((ComplexShape.up ℕ).prev n) n) ψ
    calc
      _ = e.hom.f n (A.d ((ComplexShape.up ℕ).prev n) n ψ) := by
        simpa only [ConcreteCategory.comp_apply, A, B] using hc
      _ = e.hom.f n φ' := congrArg (e.hom.f n) hψ
      _ = φ := heφ
  · simpa only [e] using
      (complexCochainRestrictionToCoveringSieve_local_zero
        Y S ((ComplexShape.up ℕ).prev n) ψ hψsmall)

set_option backward.isDefEq.respectTransparency false in
/-- The actual kernel of the map from top-open complex cochains to global first-plus cochains is
acyclic. -/
theorem topOpenToGlobalSingularCochainPlusComplex_kernel_acyclic_complex :
    (kernel (topOpenToGlobalSingularCochainPlusComplex ℂ Y)).Acyclic := by
  let C := globalRawSingularCochainComplex ℂ Y
  let B := topOpenForgottenSingularCochainComplex ℂ Y
  let e := globalRawSingularCochainComplexIso ℂ Y
  let f := topOpenToGlobalSingularCochainPlusComplex ℂ Y
  let K := kernel f
  intro n
  rw [K.exactAt_iff, ShortComplex.ab_exact_iff]
  intro z hzclosed
  let φ : OpenCochains ℂ Y (.op ⊤) n := (kernel.ι f).f n z
  have hφplus : f.f n φ = 0 := by
    have hcondition := HomologicalComplex.congr_hom (kernel.condition f) n
    exact ConcreteCategory.congr_hom hcondition z
  change ((Opens.grothendieckTopology Y).toPlus
    (singularCochainPresheaf ℂ Y n)).app (.op ⊤) φ = 0 at hφplus
  obtain ⟨S, hφlocal⟩ :=
    (singularCochain_toPlus_eq_zero_iff ℂ Y ⊤ n φ).mp hφplus
  have hφclosed : ((TopOpenSingularChainComplex ℂ Y).linearDualCochainComplex.d
      n (n + 1)) φ = 0 := by
    change K.d n ((ComplexShape.up ℕ).next n) z = 0 at hzclosed
    rw [show (ComplexShape.up ℕ).next n = n + 1 by simp] at hzclosed
    apply_fun (kernel.ι f).f (n + 1) at hzclosed
    rw [map_zero] at hzclosed
    have hc := ConcreteCategory.congr_hom ((kernel.ι f).comm n (n + 1)) z
    have hC : C.d n (n + 1) φ = 0 := by
      calc
        _ = (kernel.ι f).f (n + 1) (K.d n (n + 1) z) := by
          simpa only [ConcreteCategory.comp_apply, C, K] using hc
        _ = 0 := hzclosed
    change B.d n (n + 1) φ = 0
    have hc := ConcreteCategory.congr_hom (e.hom.comm n (n + 1)) φ
    have hc' : B.d n (n + 1) φ = C.d n (n + 1) φ := by
      simp only [ConcreteCategory.comp_apply] at hc
      simpa only [e, B, C,
        globalRawSingularCochainComplexIso_hom_f_apply] using hc
    rw [hc', hC]
  obtain ⟨ψ, hψ, hψlocal⟩ :=
    exists_topOpenComplexLocallyZero_primitive Y S n φ hφlocal hφclosed
  have hψplus : f.f ((ComplexShape.up ℕ).prev n) ψ = 0 := by
    change ((Opens.grothendieckTopology Y).toPlus
      (singularCochainPresheaf ℂ Y ((ComplexShape.up ℕ).prev n))).app
        (.op ⊤) ψ = 0
    exact (singularCochain_toPlus_eq_zero_iff ℂ Y ⊤
      ((ComplexShape.up ℕ).prev n) ψ).mpr ⟨S, hψlocal⟩
  let ev := HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ)
    ((ComplexShape.up ℕ).prev n)
  let E : K.X ((ComplexShape.up ℕ).prev n) ≅
      AddCommGrpCat.of (f.f ((ComplexShape.up ℕ).prev n)).hom.ker :=
    asIso (kernelComparison f ev) ≪≫
      AddCommGrpCat.kernelIsoKer (f.f ((ComplexShape.up ℕ).prev n))
  let p : K.X ((ComplexShape.up ℕ).prev n) := E.inv ⟨ψ, hψplus⟩
  have hpmap : (kernel.ι f).f ((ComplexShape.up ℕ).prev n) p = ψ := by
    have hc := ConcreteCategory.congr_hom (kernelComparison_comp_ι f ev) p
    have hk := ConcreteCategory.congr_hom
      (AddCommGrpCat.kernelIsoKer_hom_comp_subtype
        (f.f ((ComplexShape.up ℕ).prev n))) ((kernelComparison f ev) p)
    have hE : E.hom p =
        (⟨ψ, hψplus⟩ : (f.f ((ComplexShape.up ℕ).prev n)).hom.ker) := by
      simp [p]
    calc
      (kernel.ι f).f ((ComplexShape.up ℕ).prev n) p =
          kernel.ι (ev.map f) ((kernelComparison f ev) p) := hc.symm
      _ = ((AddCommGrpCat.kernelIsoKer
          (f.f ((ComplexShape.up ℕ).prev n))).hom
            ((kernelComparison f ev) p)).1 := hk.symm
      _ = ψ := congrArg Subtype.val hE
  refine ⟨p, ?_⟩
  change K.d ((ComplexShape.up ℕ).prev n) n p = z
  apply (AddCommGrpCat.mono_iff_injective ((kernel.ι f).f n)).mp inferInstance
  have hc := ConcreteCategory.congr_hom
    ((kernel.ι f).comm ((ComplexShape.up ℕ).prev n) n) p
  have hψC : C.d ((ComplexShape.up ℕ).prev n) n ψ = φ := by
    change B.d ((ComplexShape.up ℕ).prev n) n ψ = φ at hψ
    have hc := ConcreteCategory.congr_hom
      (e.hom.comm ((ComplexShape.up ℕ).prev n) n) ψ
    have hc' : B.d ((ComplexShape.up ℕ).prev n) n ψ =
        C.d ((ComplexShape.up ℕ).prev n) n ψ := by
      simp only [ConcreteCategory.comp_apply] at hc
      simpa only [e, B, C,
        globalRawSingularCochainComplexIso_hom_f_apply] using hc
    exact hc'.symm.trans hψ
  calc
    (kernel.ι f).f n (K.d ((ComplexShape.up ℕ).prev n) n p) =
        C.d ((ComplexShape.up ℕ).prev n) n
          ((kernel.ι f).f ((ComplexShape.up ℕ).prev n) p) := by
      simpa only [ConcreteCategory.comp_apply, C, K] using hc.symm
    _ = C.d ((ComplexShape.up ℕ).prev n) n ψ := by rw [hpmap]
    _ = φ := hψC
    _ = (kernel.ι f).f n z := rfl
/-- The map from top-open complex cochains to global first-plus cochains is a
quasi-isomorphism. -/
theorem topOpenToGlobalSingularCochainPlusComplex_quasiIso_complex :
    QuasiIso (topOpenToGlobalSingularCochainPlusComplex ℂ Y) :=
  HomologicalComplex.quasiIso_of_epi_of_kernel_acyclic
    (topOpenToGlobalSingularCochainPlusComplex ℂ Y)
    (topOpenToGlobalSingularCochainPlusComplex_kernel_acyclic_complex Y)


end ComplexCover

namespace HereditarilyParacompact

/-- On a paracompact Hausdorff space, ordinary complex cochains map quasi-isomorphically to
global sections of the double-plus singular-cochain complex. -/
theorem topOpenToGlobalSingularCochainPlusPlusComplex_quasiIso_complex
    {Y : TopCat.{0}} [ParacompactSpace Y] [T2Space Y] :
    QuasiIso (topOpenToGlobalSingularCochainPlusPlusComplex ℂ Y) := by
  change QuasiIso
    (topOpenToGlobalSingularCochainPlusComplex ℂ Y ≫
      globalSingularCochainPlusToPlusPlusComplex ℂ Y)
  let := topOpenToGlobalSingularCochainPlusComplex_quasiIso_complex (Y := Y)
  infer_instance

/-- On a paracompact Hausdorff space, ordinary complex singular cochains compute global
sections of the singular-cochain sheaf resolution. -/
theorem topOpenToGlobalSingularCochainSheafComplex_quasiIso_complex
    {Y : TopCat.{0}} [ParacompactSpace Y] [T2Space Y] :
    QuasiIso (topOpenToGlobalSingularCochainSheafComplex ℂ Y) := by
  change QuasiIso
    (topOpenToGlobalSingularCochainPlusPlusComplex ℂ Y ≫
      (globalSingularCochainPlusPlusComplexIsoSheafComplex ℂ Y).hom)
  let := topOpenToGlobalSingularCochainPlusPlusComplex_quasiIso_complex (Y := Y)
  infer_instance

end HereditarilyParacompact

end AlgebraicTopology.Singular
