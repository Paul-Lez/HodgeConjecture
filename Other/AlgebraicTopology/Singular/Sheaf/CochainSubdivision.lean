/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Other.Algebra.Homology.LinearDual
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.SubdivisionCochain
public import Other.AlgebraicTopology.Sheaf.FlasqueGlobalSections
public import Other.AlgebraicTopology.Singular.CochainCohomology
public import Other.AlgebraicTopology.SingularExcisionScalar
public import Other.AlgebraicTopology.SimplicialCochainExtension

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped Simplicial

universe u

namespace AlgebraicTopology.Singular

/-- Lift a singular simplex through an inclusion of open subsets, provided all of its values lie
in the smaller open subset. -/
noncomputable def openSimplexLift {X : TopCat.{u}} {U V : Opens X} (n : ℕ)
    (s : OpenSimplex X (.op U) n)
    (h : ∀ z, (((TopCat.of U).toSSetObjEquiv
      (Opposite.op (SimplexCategory.mk n)) s z : U) : X) ∈ V) :
    OpenSimplex X (.op V) n :=
  let m := Opposite.op (SimplexCategory.mk n)
  let fs := (TopCat.of U).toSSetObjEquiv m s
  let f : C(stdSimplex ℝ (Fin (n + 1)), TopCat.of V) :=
    ⟨fun z ↦ ⟨((fs z : U) : X), h z⟩,
      Continuous.subtype_mk
        (continuous_subtype_val.comp fs.continuous) _⟩
  (TopCat.of V).toSSetObjEquiv m |>.symm f

@[simp]
lemma openSimplexMap_openSimplexLift {X : TopCat.{u}} {U V : Opens X} (i : V ⟶ U) (n : ℕ)
    (s : OpenSimplex X (.op U) n)
    (h : ∀ z, (((TopCat.of U).toSSetObjEquiv
      (Opposite.op (SimplexCategory.mk n)) s z : U) : X) ∈ V) :
    openSimplexMap X i.op n (openSimplexLift n s h) = s := by
  apply (TopCat.of U).toSSetObjEquiv
    (Opposite.op (SimplexCategory.mk n)) |>.injective
  rfl

variable (R : Type u) [CommRing R] (X : TopCat.{u})

/-- Ordinary singular cochain cohomology is canonically linearly equivalent to the cohomology of
cochains on the top open subset. -/
noncomputable def cochainCohomologyEquivTopOpen (n : ℕ) :
    CochainCohomology R X n ≃ₗ[R]
      ((TopOpenSingularChainComplex R X).sc n).linearDual.homology :=
  HomologicalComplex.HomotopyEquiv.linearDualCohomologyEquiv
    (HomotopyEquiv.ofIso (topOpenSingularChainComplexIso R X)) n

section RationalCover
variable {κ : Type} (Y : TopCat.{0}) (U : κ → Set Y)

/-- The cover-small homotopy equivalence, with its source written as cochains on the top open
subset. -/
def topOpenRationalCochainHomotopyEquivCoverSmall
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomotopyEquiv
      (TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex
      (CoverSmallRationalSingularChainComplex Y U).linearDualCochainComplex :=
    let e₁ : HomotopyEquiv
        (TopOpenSingularChainComplex ℚ Y).linearDualCochainComplex
        ((TopCat.toSSet.obj Y).chainComplex
          (ModuleCat.of ℚ ℚ)).linearDualCochainComplex :=
      HomotopyEquiv.ofIso (singularCochainComplexIsoTopOpen ℚ Y).symm
    e₁.trans
      (rationalCochainHomotopyEquivCoverSmall Y U hUopen hUcover)

lemma topOpenRationalCochainHomotopyEquivCoverSmall_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (topOpenRationalCochainHomotopyEquivCoverSmall Y U hUopen hUcover).hom =
      topOpenRationalCochainRestrictionToCoverSmall Y U := by
  change (singularCochainComplexIsoTopOpen ℚ Y).inv ≫
      (rationalCochainHomotopyEquivCoverSmall Y U hUopen hUcover).hom =
    (singularCochainComplexIsoTopOpen ℚ Y).inv ≫
      rationalCochainRestrictionToCoverSmall Y U
  rw [rationalCochainHomotopyEquivCoverSmall_hom]

/-- For an open cover, restriction from top-open rational cochains to cover-small cochains is a
quasi-isomorphism. -/
theorem topOpenRationalCochainRestrictionToCoverSmall_quasiIso
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (topOpenRationalCochainRestrictionToCoverSmall Y U) := by
  rw [← topOpenRationalCochainHomotopyEquivCoverSmall_hom Y U hUopen hUcover]
  infer_instance

/-- The complex of top-open rational cochains vanishing on all chains subordinate to an open
cover is acyclic. -/
theorem topOpenRationalCoverSmallCochainKernel_acyclic
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (kernel (topOpenRationalCochainRestrictionToCoverSmall Y U)).Acyclic := by
  let := topOpenRationalCochainRestrictionToCoverSmall_quasiIso
    Y U hUopen hUcover
  exact HomologicalComplex.kernel_acyclic_of_epi_of_quasiIso
    (topOpenRationalCochainRestrictionToCoverSmall Y U)

end RationalCover

variable (R : Type) [CommRing R] {κ : Type} (Y : TopCat.{0}) (U : κ → Set Y)

section ScalarCover

/-- Restriction of rational singular cochains to chains subordinate to a family of subsets. -/
def scalarCochainRestrictionToCoverSmall :
    ((TopCat.toSSet.obj Y).chainComplex
        (ModuleCat.of R R)).linearDualCochainComplex ⟶
      (CoverSmallScalarSingularChainComplex R Y U).linearDualCochainComplex :=
  HomologicalComplex.linearDualMap (coverSmallScalarSingularChainInclusion R Y U)

/-- The chain map from one member of a family into the cover-small rational chains. -/
def coverMemberToSmallScalarSingularChains (j : κ) :
    (TopCat.toSSet.obj (TopCat.of (U j))).chainComplex (ModuleCat.of R R) ⟶
      CoverSmallScalarSingularChainComplex R Y U :=
  SSet.chainComplexMap (coverMemberToSmallSingularSet Y U j) (ModuleCat.of R R)

@[reassoc]
lemma coverMemberToSmallScalarSingularChains_comp_inclusion (j : κ) :
    coverMemberToSmallScalarSingularChains R Y U j ≫
        coverSmallScalarSingularChainInclusion R Y U =
      SSet.chainComplexMap
        (TopCat.toSSet.map (topologicalSubsetInclusion Y (U j)))
        (ModuleCat.of R R) := by
  change ((SSet.chainComplexFunctor (ModuleCat R)).obj
      (ModuleCat.of R R)).map (coverMemberToSmallSingularSet Y U j) ≫
    ((SSet.chainComplexFunctor (ModuleCat R)).obj
      (ModuleCat.of R R)).map (coverSmallSingularSubcomplex Y U).ι = _
  rw [← Functor.map_comp, coverMemberToSmallSingularSet_comp_inclusion]

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing on every member of a covering sieve implies vanishing on all chains subordinate
to the associated family of open subsets. -/
lemma scalarCochainRestrictionToCoveringSieve_eq_zero
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (n : ℕ)
    (φ : ((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of R R)).linearDualCochainComplex.X n)
    (hφ : ∀ I : S.Arrow,
      (singularCochainPresheaf R Y n).map I.f.op
        ((singularCochainComplexIsoTopOpen R Y).hom.f n φ) = 0) :
    (scalarCochainRestrictionToCoverSmall R Y
      (coveringSieveOpenFamily Y S)).f n φ = 0 := by
  change Module.Dual R
    (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).X n) at φ
  change ((coverSmallScalarSingularChainInclusion R Y
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
    (fun ψ : OpenCochains R Y (.op I.Y) n ↦ ψ
      (((TopCat.toSSet.obj (TopCat.of (coveringSieveOpenFamily Y S I))).ιChainComplex
        (R := ModuleCat.of R R) y).hom a))
    (hφ I)
  dsimp only [singularCochainPresheaf, singularCochainComplexIsoTopOpen,
    HomologicalComplex.linearDualIso, HomologicalComplex.linearDualMap] at hI
  change φ (ModuleCat.Hom.hom
      (((openSingularChainComplexFunctor R Y).map I.f).f n ≫
        (topOpenSingularChainComplexIso R Y).hom.f n)
      (((TopCat.toSSet.obj (TopCat.of (coveringSieveOpenFamily Y S I))).ιChainComplex
        (R := ModuleCat.of R R) y).hom a)) = 0 at hI
  have hchain := HomologicalComplex.congr_hom
    (openSingularChainToTop_comp_topOpenIso R Y I.f) n
  have hchain' :
      ((openSingularChainComplexFunctor R Y).map I.f).f n ≫
          (topOpenSingularChainComplexIso R Y).hom.f n =
        (SSet.chainComplexMap
          (TopCat.toSSet.map (topologicalSubsetInclusion Y I.Y))
          (ModuleCat.of R R)).f n := by
    simpa only [HomologicalComplex.comp_f] using hchain
  rw [hchain'] at hI
  have hiota := ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f
      (TopCat.toSSet.obj (TopCat.of (coveringSieveOpenFamily Y S I)))
      (TopCat.toSSet.obj Y)
      (TopCat.toSSet.map (topologicalSubsetInclusion Y
        (coveringSieveOpenFamily Y S I)))
      (ModuleCat.of R R) y) a
  simp only [ConcreteCategory.comp_apply] at hiota
  have hI' : φ
      (((TopCat.toSSet.obj Y).ιChainComplex
        (R := ModuleCat.of R R)
        ((TopCat.toSSet.map (topologicalSubsetInclusion Y
          (coveringSieveOpenFamily Y S I))).app _ y)).hom a) = 0 := by
    calc
      _ = φ ((SSet.chainComplexMap
          (TopCat.toSSet.map (topologicalSubsetInclusion Y
            (coveringSieveOpenFamily Y S I)))
          (ModuleCat.of R R)).f n
          (((TopCat.toSSet.obj
            (TopCat.of (coveringSieveOpenFamily Y S I))).ιChainComplex
              (R := ModuleCat.of R R) y).hom a)) := congrArg φ hiota.symm
      _ = 0 := hI
  change φ (ModuleCat.Hom.hom
    (((coverSmallSingularSubcomplex Y
      (coveringSieveOpenFamily Y S) : SSet).ιChainComplex
        (R := ModuleCat.of R R) x) ≫
      (coverSmallScalarSingularChainInclusion R Y
        (coveringSieveOpenFamily Y S)).f n) a) = 0
  dsimp only [coverSmallScalarSingularChainInclusion] at ⊢
  rw [SSet.ι_chainComplexMap_f]
  simpa [hy] using hI'
  · intro f g h
    exact congrArg ModuleCat.Hom.hom h

set_option backward.isDefEq.respectTransparency false in
/-- Conversely, vanishing on the cover-small chains associated to a covering sieve implies
vanishing after restriction along every arrow of that sieve. -/
lemma scalarCochainRestrictionToCoveringSieve_local_zero
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (n : ℕ)
    (φ : ((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of R R)).linearDualCochainComplex.X n)
    (hφ : (scalarCochainRestrictionToCoverSmall R Y
      (coveringSieveOpenFamily Y S)).f n φ = 0) :
    ∀ I : S.Arrow,
      (singularCochainPresheaf R Y n).map I.f.op
        ((singularCochainComplexIsoTopOpen R Y).hom.f n φ) = 0 := by
  intro I
  change Module.Dual R
    (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).X n) at φ
  change ((coverSmallScalarSingularChainInclusion R Y
    (coveringSieveOpenFamily Y S)).f n).hom.dualMap φ = 0 at hφ
  change (((openSingularChainComplexFunctor R Y).map I.f).f n).hom.dualMap
    (((topOpenSingularChainComplexIso R Y).hom.f n).hom.dualMap φ) = 0
  apply LinearMap.ext
  intro c
  have hc := LinearMap.congr_fun hφ
    (((coverMemberToSmallScalarSingularChains R Y
      (coveringSieveOpenFamily Y S) I).f n).hom c)
  have htop := HomologicalComplex.congr_hom
    (openSingularChainToTop_comp_topOpenIso R Y I.f) n
  have hmember := HomologicalComplex.congr_hom
    (coverMemberToSmallScalarSingularChains_comp_inclusion R Y
      (coveringSieveOpenFamily Y S) I) n
  simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at hc ⊢
  calc
    φ ((topOpenSingularChainComplexIso R Y).hom.f n
        (((openSingularChainComplexFunctor R Y).map I.f).f n c)) =
      φ ((SSet.chainComplexMap
        (TopCat.toSSet.map (topologicalSubsetInclusion Y I.Y))
        (ModuleCat.of R R)).f n c) :=
          congrArg φ (ConcreteCategory.congr_hom htop c)
    _ = φ ((coverSmallScalarSingularChainInclusion R Y
          (coveringSieveOpenFamily Y S)).f n
        ((coverMemberToSmallScalarSingularChains R Y
          (coveringSieveOpenFamily Y S) I).f n c)) :=
            congrArg φ (ConcreteCategory.congr_hom hmember c).symm
    _ = 0 := hc

/-- Restriction to cover-small rational chains is surjective in every cochain degree. -/
lemma scalarCochainRestrictionToCoverSmall_surjective (n : ℕ) :
    Function.Surjective ((scalarCochainRestrictionToCoverSmall R Y U).f n) := by
  exact SSet.Subcomplex.dualMap_surjective R (coverSmallSingularSubcomplex Y U) n

/-- Restriction to cover-small rational chains is an epimorphism of cochain complexes. -/
instance scalarCochainRestrictionToCoverSmall_epi :
    Epi (scalarCochainRestrictionToCoverSmall R Y U) :=
  HomologicalComplex.epi_of_epi_f _ fun n ↦ by
    rw [ModuleCat.epi_iff_surjective]
    exact scalarCochainRestrictionToCoverSmall_surjective R Y U n

/-- An open cover gives a homotopy equivalence from all rational cochains to its cover-small
cochains. -/
def scalarCochainHomotopyEquivCoverSmall
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomotopyEquiv
      ((TopCat.toSSet.obj Y).chainComplex
        (ModuleCat.of R R)).linearDualCochainComplex
      (CoverSmallScalarSingularChainComplex R Y U).linearDualCochainComplex :=
  HomologicalComplex.linearDualHomotopyEquiv
    (coverSmallScalarChainHomotopyEquiv_of_openCover R Y U hUopen hUcover)

lemma scalarCochainHomotopyEquivCoverSmall_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (scalarCochainHomotopyEquivCoverSmall R Y U hUopen hUcover).hom =
      scalarCochainRestrictionToCoverSmall R Y U := by
  dsimp [scalarCochainHomotopyEquivCoverSmall,
    scalarCochainRestrictionToCoverSmall]
  change HomologicalComplex.linearDualMap
      (coverSmallScalarChainHomotopyEquiv_of_openCover R
        Y U hUopen hUcover).hom = _
  rw [coverSmallScalarChainHomotopyEquiv_of_openCover_hom]

/-- Restriction from all rational cochains to cover-small cochains is a quasi-isomorphism for an
open cover. -/
theorem scalarCochainRestrictionToCoverSmall_quasiIso
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (scalarCochainRestrictionToCoverSmall R Y U) := by
  rw [← scalarCochainHomotopyEquivCoverSmall_hom R Y U hUopen hUcover]
  infer_instance

/-- The complex of rational cochains vanishing on every chain subordinate to an open cover is
acyclic. -/
theorem scalarCoverSmallCochainKernel_acyclic
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (kernel (scalarCochainRestrictionToCoverSmall R Y U)).Acyclic := by
  let := scalarCochainRestrictionToCoverSmall_quasiIso R Y U hUopen hUcover
  exact HomologicalComplex.kernel_acyclic_of_epi_of_quasiIso
    (scalarCochainRestrictionToCoverSmall R Y U)

set_option backward.isDefEq.respectTransparency false in
/-- A closed rational cochain which vanishes on all cover-small chains has a primitive which
also vanishes on all cover-small chains. -/
theorem exists_coverSmallKernel_primitive_of_commRing
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ)
    (φ : ((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of R R)).linearDualCochainComplex.X n)
    (hφsmall : (scalarCochainRestrictionToCoverSmall R Y U).f n φ = 0)
    (hφclosed : (((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of R R)).linearDualCochainComplex.d n (n + 1)) φ = 0) :
    ∃ ψ : ((TopCat.toSSet.obj Y).chainComplex
        (ModuleCat.of R R)).linearDualCochainComplex.X
          ((ComplexShape.up ℕ).prev n),
      (((TopCat.toSSet.obj Y).chainComplex
          (ModuleCat.of R R)).linearDualCochainComplex.sc n).f ψ = φ ∧
        (scalarCochainRestrictionToCoverSmall R Y U).f
          ((ComplexShape.up ℕ).prev n) ψ = 0 := by
  let F := ((TopCat.toSSet.obj Y).chainComplex
    (ModuleCat.of R R)).linearDualCochainComplex
  let q := scalarCochainRestrictionToCoverSmall R Y U
  let K := kernel q
  let E : (kernel q).X n ≅ ModuleCat.of R (q.f n).hom.ker :=
    asIso (kernelComparison q (HomologicalComplex.eval (ModuleCat R)
      (ComplexShape.up ℕ) n)) ≪≫ ModuleCat.kernelIsoKer (q.f n)
  let z : (kernel q).X n := E.inv ⟨φ, hφsmall⟩
  have hzmap : (kernel.ι q).f n z = φ := by
    let ev := HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n
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
  have hacyclic := scalarCoverSmallCochainKernel_acyclic R Y U hUopen hUcover
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
theorem exists_topOpenLocallyZero_primitive_of_commRing
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (n : ℕ)
    (φ : (TopOpenSingularChainComplex R Y).linearDualCochainComplex.X n)
    (hφlocal : ∀ I : S.Arrow,
      (singularCochainPresheaf R Y n).map I.f.op φ = 0)
    (hφclosed : ((TopOpenSingularChainComplex R Y).linearDualCochainComplex.d
      n (n + 1)) φ = 0) :
    ∃ ψ : (TopOpenSingularChainComplex R Y).linearDualCochainComplex.X
        ((ComplexShape.up ℕ).prev n),
      ((TopOpenSingularChainComplex R Y).linearDualCochainComplex.sc n).f ψ = φ ∧
        ∀ I : S.Arrow,
          (singularCochainPresheaf R Y ((ComplexShape.up ℕ).prev n)).map I.f.op ψ = 0 := by
  let A := (SingularChainComplex R Y).linearDualCochainComplex
  let B := (TopOpenSingularChainComplex R Y).linearDualCochainComplex
  let e := singularCochainComplexIsoTopOpen R Y
  let φ' : A.X n := e.inv.f n φ
  have heφ : e.hom.f n φ' = φ := by
    have hc := ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom e.inv_hom_id n) φ
    simpa only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
      HomologicalComplex.id_f, ConcreteCategory.id_apply, φ'] using hc
  have hlocal' : ∀ I : S.Arrow,
      (singularCochainPresheaf R Y n).map I.f.op (e.hom.f n φ') = 0 := by
    intro I
    rw [heφ]
    exact hφlocal I
  have hsmall : (scalarCochainRestrictionToCoverSmall R Y
      (coveringSieveOpenFamily Y S)).f n φ' = 0 :=
    scalarCochainRestrictionToCoveringSieve_eq_zero R Y S n φ' hlocal'
  have hclosed' : A.d n (n + 1) φ' = 0 := by
    change A.d n (n + 1) (e.inv.f n φ) = 0
    have hc := ConcreteCategory.congr_hom (e.inv.comm n (n + 1)) φ
    calc
      _ = e.inv.f (n + 1) (B.d n (n + 1) φ) := by
        simpa only [ConcreteCategory.comp_apply, A, B] using hc
      _ = 0 := by rw [hφclosed, map_zero]
  obtain ⟨ψ, hψ, hψsmall⟩ := exists_coverSmallKernel_primitive_of_commRing R Y
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
      (scalarCochainRestrictionToCoveringSieve_local_zero R
        Y S ((ComplexShape.up ℕ).prev n) ψ hψsmall)

set_option backward.isDefEq.respectTransparency false in
/-- The actual kernel of the map from top-open rational cochains to global first-plus cochains is
acyclic. -/
theorem topOpenToGlobalSingularCochainPlusComplex_kernel_acyclic_of_commRing :
    (kernel (topOpenToGlobalSingularCochainPlusComplex R Y)).Acyclic := by
  let C := globalRawSingularCochainComplex R Y
  let B := topOpenForgottenSingularCochainComplex R Y
  let e := globalRawSingularCochainComplexIso R Y
  let f := topOpenToGlobalSingularCochainPlusComplex R Y
  let K := kernel f
  intro n
  rw [K.exactAt_iff, ShortComplex.ab_exact_iff]
  intro z hzclosed
  let φ : OpenCochains R Y (.op ⊤) n := (kernel.ι f).f n z
  have hφplus : f.f n φ = 0 := by
    have hcondition := HomologicalComplex.congr_hom (kernel.condition f) n
    exact ConcreteCategory.congr_hom hcondition z
  change ((Opens.grothendieckTopology Y).toPlus
    (singularCochainPresheaf R Y n)).app (.op ⊤) φ = 0 at hφplus
  obtain ⟨S, hφlocal⟩ :=
    (singularCochain_toPlus_eq_zero_iff R Y ⊤ n φ).mp hφplus
  have hφclosed : ((TopOpenSingularChainComplex R Y).linearDualCochainComplex.d
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
    exists_topOpenLocallyZero_primitive_of_commRing R Y S n φ hφlocal hφclosed
  have hψplus : f.f ((ComplexShape.up ℕ).prev n) ψ = 0 := by
    change ((Opens.grothendieckTopology Y).toPlus
      (singularCochainPresheaf R Y ((ComplexShape.up ℕ).prev n))).app
        (.op ⊤) ψ = 0
    exact (singularCochain_toPlus_eq_zero_iff R Y ⊤
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

/-- The map from top-open rational cochains to global first-plus cochains is a
quasi-isomorphism. -/
theorem topOpenToGlobalSingularCochainPlusComplex_quasiIso_of_commRing :
    QuasiIso (topOpenToGlobalSingularCochainPlusComplex R Y) :=
  HomologicalComplex.quasiIso_of_epi_of_kernel_acyclic
    (topOpenToGlobalSingularCochainPlusComplex R Y)
    (topOpenToGlobalSingularCochainPlusComplex_kernel_acyclic_of_commRing R Y)

/-- Restriction from cochains on the top open subset to chains subordinate to a family of
subsets. -/
def topOpenScalarCochainRestrictionToCoverSmall :
    (TopOpenSingularChainComplex R Y).linearDualCochainComplex ⟶
      (CoverSmallScalarSingularChainComplex R Y U).linearDualCochainComplex :=
  (singularCochainComplexIsoTopOpen R Y).inv ≫
    scalarCochainRestrictionToCoverSmall R Y U

instance topOpenScalarCochainRestrictionToCoverSmall_epi :
    Epi (topOpenScalarCochainRestrictionToCoverSmall R Y U) := by
  apply HomologicalComplex.epi_of_epi_f _ fun n ↦ ?_
  rw [ModuleCat.epi_iff_surjective]
  have h₁ : Function.Surjective
      ((singularCochainComplexIsoTopOpen R Y).inv.f n) := by
    rw [← ModuleCat.epi_iff_surjective]
    infer_instance
  have h₂ := scalarCochainRestrictionToCoverSmall_surjective R Y U n
  intro z
  obtain ⟨y, hy⟩ := h₂ z
  obtain ⟨x, hx⟩ := h₁ y
  refine ⟨x, ?_⟩
  change (scalarCochainRestrictionToCoverSmall R Y U).f n
      ((singularCochainComplexIsoTopOpen R Y).inv.f n x) = z
  rw [hx, hy]

set_option backward.isDefEq.respectTransparency false in
/-- The cover-small homotopy equivalence, with its source written as cochains on the top open
subset. -/
def topOpenScalarCochainHomotopyEquivCoverSmall
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomotopyEquiv
      (TopOpenSingularChainComplex R Y).linearDualCochainComplex
      (CoverSmallScalarSingularChainComplex R Y U).linearDualCochainComplex :=
  by
    let e₁ : HomotopyEquiv
        (TopOpenSingularChainComplex R Y).linearDualCochainComplex
        ((TopCat.toSSet.obj Y).chainComplex
          (ModuleCat.of R R)).linearDualCochainComplex :=
      HomotopyEquiv.ofIso (singularCochainComplexIsoTopOpen R Y).symm
    exact e₁.trans
      (scalarCochainHomotopyEquivCoverSmall R Y U hUopen hUcover)

set_option backward.isDefEq.respectTransparency false in
lemma topOpenScalarCochainHomotopyEquivCoverSmall_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (topOpenScalarCochainHomotopyEquivCoverSmall R Y U hUopen hUcover).hom =
      topOpenScalarCochainRestrictionToCoverSmall R Y U := by
  change (singularCochainComplexIsoTopOpen R Y).inv ≫
      (scalarCochainHomotopyEquivCoverSmall R Y U hUopen hUcover).hom =
    (singularCochainComplexIsoTopOpen R Y).inv ≫
      scalarCochainRestrictionToCoverSmall R Y U
  rw [scalarCochainHomotopyEquivCoverSmall_hom]

/-- For an open cover, restriction from top-open rational cochains to cover-small cochains is a
quasi-isomorphism. -/
theorem topOpenScalarCochainRestrictionToCoverSmall_quasiIso
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (topOpenScalarCochainRestrictionToCoverSmall R Y U) := by
  rw [← topOpenScalarCochainHomotopyEquivCoverSmall_hom R Y U hUopen hUcover]
  infer_instance

/-- The complex of top-open rational cochains vanishing on all chains subordinate to an open
cover is acyclic. -/
theorem topOpenScalarCoverSmallCochainKernel_acyclic
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (kernel (topOpenScalarCochainRestrictionToCoverSmall R Y U)).Acyclic := by
  let := topOpenScalarCochainRestrictionToCoverSmall_quasiIso R
    Y U hUopen hUcover
  exact HomologicalComplex.kernel_acyclic_of_epi_of_quasiIso
    (topOpenScalarCochainRestrictionToCoverSmall R Y U)

theorem topOpenToGlobalSingularCochainPlusPlusComplex_quasiIso_of_commRing
    {Y : TopCat.{0}} [ParacompactSpace Y] [T2Space Y] :
    QuasiIso (topOpenToGlobalSingularCochainPlusPlusComplex R Y) := by
  change QuasiIso
    (topOpenToGlobalSingularCochainPlusComplex R Y ≫
      globalSingularCochainPlusToPlusPlusComplex R Y)
  letI := topOpenToGlobalSingularCochainPlusComplex_quasiIso_of_commRing R Y
  infer_instance

theorem topOpenToGlobalSingularCochainSheafComplex_quasiIso_of_commRing
    {Y : TopCat.{0}} [ParacompactSpace Y] [T2Space Y] :
    QuasiIso (topOpenToGlobalSingularCochainSheafComplex R Y) := by
  change QuasiIso
    (topOpenToGlobalSingularCochainPlusPlusComplex R Y ≫
      (globalSingularCochainPlusPlusComplexIsoSheafComplex R Y).hom)
  letI := topOpenToGlobalSingularCochainPlusPlusComplex_quasiIso_of_commRing R
    (Y := Y)
  infer_instance

end ScalarCover


end AlgebraicTopology.Singular

namespace AlgebraicTopology.Singular

variable {R : Type u} [CommRing R] {X : TopCat.{u}}

/-- Every positive sheaf-cohomology group of a term of the singular-cochain resolution vanishes
on a hereditarily paracompact Hausdorff space. -/
lemma singularCochainSheaf_cohomology_succ_eq_zero
    [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (n q : ℕ) (x : Abelian.Ext
      𝓒(X; ULift.{u} ℤ)
      (singularCochainSheaf R X n) (q + 1)) :
    x = 0 :=
  TopCat.Sheaf.IsFlasque.cohomology_succ_eq_zero
    (singularCochainSheaf R X n) q x

end AlgebraicTopology.Singular
