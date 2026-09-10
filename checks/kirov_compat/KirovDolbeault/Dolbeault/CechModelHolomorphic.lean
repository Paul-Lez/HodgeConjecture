/-
  Čech finiteness — corrected holomorphic-shrinking model scaffold.

  This file introduces the shape the soundness note points at: the shrinking side is modeled by
  bounded-holomorphic functions on relatively-compact open shrinkings `Wov p`, not by bounded-
  continuous functions on compact sets.  It is a parallel scaffold, leaving the current continuous
  branch intact while giving future proof work the right target.

  The file is intentionally small: it only defines the corrected data bundle and the raw restriction
  operator.  The compactness theorem and the Leray discharge will be built on top of this branch.
-/
import KirovDolbeault.Dolbeault.CechFinitenessAbstract
import KirovDolbeault.Dolbeault.CechModelBridge
import KirovDolbeault.Dolbeault.CechComplex
import KirovDolbeault.Montel.Cover

open scoped Manifold ContDiff Topology
open Metric Topology BoundedContinuousFunction
open Jacobians.Montel

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The corrected holomorphic-shrinking overlap data -/

/-- Corrected overlap data for the holomorphic-shrinking branch: the cover side stays
`BddHol (Uov p)`, while the shrinking side is `BddHol (Wov p)` for an open relatively-compact
shrinking `Wov p ⋐ Uov p`. -/
structure HolomorphicDiskOverlapData where
  /-- Overlap index. -/
  J : Type
  [fintypeJ : Fintype J]
  [decEqJ : DecidableEq J]
  /-- Chart-image of each overlap on the cover side. -/
  Uov : J → Set ℂ
  hUov : ∀ p, IsOpen (Uov p)
  /-- Open shrinking of each overlap, intended to be relatively compact in `Uov p`. -/
  Wov : J → Set ℂ
  hWov : ∀ p, IsOpen (Wov p)
  /-- `closure (Wov p)` is compact. -/
  hKcpt : ∀ p, IsCompact (closure (Wov p))
  /-- The shrinking sits inside the cover-open after closure. -/
  hWU : ∀ p, closure (Wov p) ⊆ Uov p

attribute [instance] HolomorphicDiskOverlapData.fintypeJ HolomorphicDiskOverlapData.decEqJ

namespace HolomorphicDiskOverlapData

variable (d : HolomorphicDiskOverlapData)

/-- Cover 1-cochains: bounded-holomorphic functions on the overlap opens. -/
abbrev Ccov : Type := ∀ p : d.J, BddHol (d.Uov p)

/-- Corrected shrinking 1-cochains: bounded-holomorphic functions on the open shrinkings. -/
abbrev Cshr : Type := ∀ p : d.J, BddHol (d.Wov p)

noncomputable instance : NormedAddCommGroup d.Ccov := inferInstance
noncomputable instance : NormedSpace ℂ d.Ccov := inferInstance
noncomputable instance : NormedAddCommGroup d.Cshr := inferInstance
noncomputable instance : NormedSpace ℂ d.Cshr := inferInstance

noncomputable instance : CompleteSpace d.Ccov := by
  haveI : ∀ p, CompleteSpace (BddHol (d.Uov p)) := fun p => BddHol.completeSpace (d.hUov p)
  infer_instance

noncomputable instance : CompleteSpace d.Cshr := by
  haveI : ∀ p, CompleteSpace (BddHol (d.Wov p)) := fun p => BddHol.completeSpace (d.hWov p)
  infer_instance

/-- The raw cover → corrected-shrinking restriction, componentwise `BddHol.restrictOpenCLM`. -/
noncomputable def rhoRaw : d.Ccov →L[ℂ] d.Cshr :=
  ContinuousLinearMap.pi
    (fun p => (BddHol.restrictOpenCLM (subset_closure.trans (d.hWU p))).comp
      (ContinuousLinearMap.proj p))

theorem rhoRaw_apply (f : d.Ccov) (p : d.J) :
    d.rhoRaw f p = BddHol.restrictOpenCLM (subset_closure.trans (d.hWU p)) (f p) := by
  simp [rhoRaw, BddHol.restrictOpenCLM]

/-- **STEP 3 on the corrected branch.**  The cochain restriction `ρ` (cover → holomorphic shrinking)
is a compact operator: componentwise it is `BddHol.restrictOpenCLM`, compact for a relatively
compact open shrinking `Wov p ⋐ Uov p`, and a finite product of compacts is compact. -/
theorem rhoRaw_compact : IsCompactOperator d.rhoRaw := by
  apply CechFiniteness.isCompactOperator_pi (fun p => BddHol.restrictOpenCLM (subset_closure.trans (d.hWU p)))
  intro p
  exact BddHol.isCompactOperator_restrictOpenCLM_of_compact (d.hUov p) (d.hWov p) (d.hKcpt p)
    (d.hWU p)

end HolomorphicDiskOverlapData

/-! ### Concrete corrected geometry from `Montel.Cover` -/

/-- The chart center corresponding to the `Fin`-enumeration of `chartCover`. -/
noncomputable def montel_coverCenter (a : Fin ((chartCover : Finset X).card)) : X :=
  ((chartCover : Finset X).equivFin.symm a : X)

omit [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem montel_coverCenter_mem (a : Fin ((chartCover : Finset X).card)) :
    montel_coverCenter (X := X) a ∈ (chartCover : Finset X) :=
  ((chartCover : Finset X).equivFin.symm a).2

omit [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem montel_chartOpen_subset_chartAt_source (x : X) (hx : x ∈ (chartCover : Finset X)) :
    chartOpen (X := X) x ⊆ (chartAt (H := ℂ) x).source :=
  (chartOpen_subset_shrunkChart x).trans (shrunkChart_subset_source x hx)

omit [ConnectedSpace X] [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem montel_innerChartOpen_subset_chartOpen (x : X) :
    innerChartOpen (X := X) x ⊆ chartOpen (X := X) x := by
  intro y hy
  exact closure_innerChartOpen_subset_chartOpen x (subset_closure hy)

/-- The outer holomorphic shrinking geometry from `Montel.Cover`: `Uov` is the open chart image of
the `chartOpen` overlap, while `Wov` is the open chart image of the smaller `innerChartOpen` overlap.
The latter has compact closure inside `Uov`, giving the corrected branch a genuine relatively-compact
open shrinking. -/
noncomputable def chartCoverHolomorphicDiskOverlapData : HolomorphicDiskOverlapData where
  J := Fin ((chartCover : Finset X).card) × Fin ((chartCover : Finset X).card)
  Uov p :=
    (chartAt (H := ℂ) (montel_coverCenter (X := X) p.1)) ''
      (chartOpen (X := X) (montel_coverCenter (X := X) p.1) ∩
        chartOpen (X := X) (montel_coverCenter (X := X) p.2))
  hUov p :=
    (chartAt (H := ℂ) (montel_coverCenter (X := X) p.1)).isOpen_image_of_subset_source
      ((chartOpen_isOpen (montel_coverCenter (X := X) p.1)).inter
        (chartOpen_isOpen (montel_coverCenter (X := X) p.2)))
      (Set.inter_subset_left.trans
        (montel_chartOpen_subset_chartAt_source (X := X) (montel_coverCenter (X := X) p.1)
          (montel_coverCenter_mem (X := X) p.1)))
  Wov p :=
    (chartAt (H := ℂ) (montel_coverCenter (X := X) p.1)) ''
      (innerChartOpen (X := X) (montel_coverCenter (X := X) p.1) ∩
        innerChartOpen (X := X) (montel_coverCenter (X := X) p.2))
  hWov p :=
    (chartAt (H := ℂ) (montel_coverCenter (X := X) p.1)).isOpen_image_of_subset_source
      ((innerChartOpen_isOpen (montel_coverCenter (X := X) p.1)).inter
        (innerChartOpen_isOpen (montel_coverCenter (X := X) p.2)))
      (Set.inter_subset_left.trans
        ((montel_innerChartOpen_subset_chartOpen (X := X) (montel_coverCenter (X := X) p.1)).trans
          (montel_chartOpen_subset_chartAt_source (X := X) (montel_coverCenter (X := X) p.1)
            (montel_coverCenter_mem (X := X) p.1))))
  hKcpt p := by
    let K : Set X :=
      innerShrunkChart (X := X) (montel_coverCenter (X := X) p.1) ∩
        innerShrunkChart (X := X) (montel_coverCenter (X := X) p.2)
    have hK : IsCompact K :=
      ((innerShrunkChart_isClosed (montel_coverCenter (X := X) p.1)).inter
        (innerShrunkChart_isClosed (montel_coverCenter (X := X) p.2))).isCompact
    have hsubK : K ⊆ (chartAt (H := ℂ) (montel_coverCenter (X := X) p.1)).source := by
      exact (Set.inter_subset_left.trans (innerShrunkChart_subset_chartOpen (X := X)
        (montel_coverCenter (X := X) p.1))).trans
        (montel_chartOpen_subset_chartAt_source (X := X) (montel_coverCenter (X := X) p.1)
          (montel_coverCenter_mem (X := X) p.1))
    have hclosedK : IsClosed ((chartAt (H := ℂ) (montel_coverCenter (X := X) p.1)) '' K) :=
      (hK.image_of_continuousOn ((chartAt (H := ℂ) (montel_coverCenter (X := X) p.1)).continuousOn.mono
        hsubK)).isClosed
    have hsubW : (chartAt (H := ℂ) (montel_coverCenter (X := X) p.1)) ''
        (innerChartOpen (X := X) (montel_coverCenter (X := X) p.1) ∩
          innerChartOpen (X := X) (montel_coverCenter (X := X) p.2)) ⊆
        (chartAt (H := ℂ) (montel_coverCenter (X := X) p.1)) '' K := by
      apply Set.image_mono
      exact Set.inter_subset_inter subset_closure subset_closure
    exact (hK.image_of_continuousOn ((chartAt (H := ℂ) (montel_coverCenter (X := X) p.1)).continuousOn.mono
      hsubK)).of_isClosed_subset isClosed_closure (closure_minimal hsubW hclosedK)
  hWU p := by
    let K : Set X :=
      innerShrunkChart (X := X) (montel_coverCenter (X := X) p.1) ∩
        innerShrunkChart (X := X) (montel_coverCenter (X := X) p.2)
    have hK : IsCompact K :=
      ((innerShrunkChart_isClosed (montel_coverCenter (X := X) p.1)).inter
        (innerShrunkChart_isClosed (montel_coverCenter (X := X) p.2))).isCompact
    have hsubK : K ⊆ (chartAt (H := ℂ) (montel_coverCenter (X := X) p.1)).source := by
      exact (Set.inter_subset_left.trans (innerShrunkChart_subset_chartOpen (X := X)
        (montel_coverCenter (X := X) p.1))).trans
        (montel_chartOpen_subset_chartAt_source (X := X) (montel_coverCenter (X := X) p.1)
          (montel_coverCenter_mem (X := X) p.1))
    have hclosedK : IsClosed ((chartAt (H := ℂ) (montel_coverCenter (X := X) p.1)) '' K) :=
      (hK.image_of_continuousOn ((chartAt (H := ℂ) (montel_coverCenter (X := X) p.1)).continuousOn.mono
        hsubK)).isClosed
    have hsub : (chartAt (H := ℂ) (montel_coverCenter (X := X) p.1)) ''
        (innerChartOpen (X := X) (montel_coverCenter (X := X) p.1) ∩
          innerChartOpen (X := X) (montel_coverCenter (X := X) p.2)) ⊆
        (chartAt (H := ℂ) (montel_coverCenter (X := X) p.1)) '' K := by
      apply Set.image_mono
      exact Set.inter_subset_inter subset_closure subset_closure
    exact (closure_minimal hsub hclosedK).trans (Set.image_mono
      (Set.inter_subset_inter
        (innerShrunkChart_subset_chartOpen (X := X) (montel_coverCenter (X := X) p.1))
        (innerShrunkChart_subset_chartOpen (X := X) (montel_coverCenter (X := X) p.2))))


/-! ### The corrected coboundary bundle -/

/-- Corrected coboundary data for the holomorphic-shrinking branch.  It mirrors `Coboundaries`, but
the shrinking cochains live in `BddHol (Wov p)` rather than `→ᵇ` on compacts. -/
structure HolomorphicCoboundaries (d : HolomorphicDiskOverlapData) where
  /-- 0-cochain Banach space on the shrinking. -/
  C0 : Type
  [ng0 : NormedAddCommGroup C0]
  [ns0 : NormedSpace ℂ C0]
  [cs0 : CompleteSpace C0]
  /-- 2-cochain Banach space on the shrinking. -/
  C2 : Type
  [ng2 : NormedAddCommGroup C2]
  [ns2 : NormedSpace ℂ C2]
  /-- 2-cochain Banach space on the cover. -/
  C2cov : Type
  [ng2c : NormedAddCommGroup C2cov]
  [ns2c : NormedSpace ℂ C2cov]
  /-- The shrinking-side `δ⁰`. -/
  δ0 : C0 →L[ℂ] d.Cshr
  /-- The shrinking-side `δ¹`. -/
  δ1 : d.Cshr →L[ℂ] C2
  /-- The cover-side `δ¹`. -/
  δ1cov : d.Ccov →L[ℂ] C2cov
  /-- `δ¹∘δ⁰ = 0` on the shrinking. -/
  hδδ : δ1.comp δ0 = 0
  /-- Restriction carries cover-cocycles to shrinking-cocycles. -/
  hcomm : ∀ x : d.Ccov, δ1cov x = 0 → δ1 (d.rhoRaw x) = 0
  /-- The corrected Leray/disk-acyclicity witness. -/
  leray : ∀ s : d.Cshr, δ1 s = 0 →
    ∃ (η : C0) (x : d.Ccov), δ1cov x = 0 ∧ s = δ0 η + d.rhoRaw x

attribute [instance] HolomorphicCoboundaries.ng0 HolomorphicCoboundaries.ns0 HolomorphicCoboundaries.cs0
  HolomorphicCoboundaries.ng2 HolomorphicCoboundaries.ns2 HolomorphicCoboundaries.ng2c
  HolomorphicCoboundaries.ns2c

namespace HolomorphicCoboundaries

variable {d : HolomorphicDiskOverlapData} (c : HolomorphicCoboundaries d)

/-- `Z¹(cover) = ker δ¹(cover)`, a closed subspace of the cover 1-cochains. -/
noncomputable def Z1cov : Submodule ℂ d.Ccov := LinearMap.ker c.δ1cov.toLinearMap

/-- `Z¹(shrinking) = ker δ¹(shrinking)`, a closed subspace of the shrinking 1-cochains. -/
noncomputable def Z1shr : Submodule ℂ d.Cshr := LinearMap.ker c.δ1.toLinearMap

theorem isClosed_Z1cov : IsClosed (c.Z1cov : Set d.Ccov) := c.δ1cov.isClosed_ker

theorem isClosed_Z1shr : IsClosed (c.Z1shr : Set d.Cshr) := c.δ1.isClosed_ker

noncomputable instance : CompleteSpace c.Z1cov := c.δ1cov.isClosed_ker.completeSpace_coe
noncomputable instance : CompleteSpace c.Z1shr := c.δ1.isClosed_ker.completeSpace_coe

/-- The coboundary `δ : C⁰ →L[ℂ] Z¹(shrinking)` (i.e. `δ⁰` corestricted to the cocycles, using
`δ¹∘δ⁰=0`). -/
noncomputable def δ : c.C0 →L[ℂ] c.Z1shr :=
  c.δ0.codRestrict c.Z1shr fun x => by
    show c.δ1 (c.δ0 x) = 0
    have := congrArg (fun T => T x) c.hδδ
    simpa using this

/-- The restriction `ρ : Z¹(cover) →L[ℂ] Z¹(shrinking)` (the raw restriction `rhoRaw` restricted to
the cocycle subspaces, using the commuting square `hcomm`). -/
noncomputable def ρ : c.Z1cov →L[ℂ] c.Z1shr :=
  (d.rhoRaw.comp c.Z1cov.subtypeL).codRestrict c.Z1shr fun x => c.hcomm x.1 x.2

/-- `subtypeL ∘ ρ = rhoRaw ∘ subtypeL` — the defining commuting identity for `ρ`. -/
theorem subtypeL_comp_ρ :
    c.Z1shr.subtypeL.comp c.ρ = d.rhoRaw.comp c.Z1cov.subtypeL := by
  ext x
  rfl

/-- The restriction `ρ : Z¹(cover) →L Z¹(shrinking)` is compact. -/
theorem ρ_compact : IsCompactOperator c.ρ := by
  apply CechFiniteness.isCompactOperator_of_subtypeL_comp c.isClosed_Z1shr c.ρ
  rw [c.subtypeL_comp_ρ]
  exact d.rhoRaw_compact.comp_clm c.Z1cov.subtypeL

/-- The sup-norm `H¹` of the corrected holomorphic branch: `Z¹(shrinking) ⧸ B¹`. -/
abbrev supH1 : Type := c.Z1shr ⧸ LinearMap.range c.δ.toLinearMap

/-- Finiteness of the corrected branch's sup-norm `H¹`, conditional on Leray surjectivity. -/
theorem finiteDimensional_supH1
    (hsurj : Function.Surjective (fun p : c.C0 × c.Z1cov => c.δ p.1 + c.ρ p.2)) :
    FiniteDimensional ℂ c.supH1 :=
  CechFiniteness.finiteDimensional_h1_of_leray_compact c.δ c.ρ hsurj c.ρ_compact

/-- Leray surjectivity for the corrected holomorphic branch. -/
theorem leray_surjective (d : HolomorphicDiskOverlapData) (c : HolomorphicCoboundaries d) :
    Function.Surjective (fun p : c.C0 × c.Z1cov => c.δ p.1 + c.ρ p.2) := by
  intro t
  have ht : c.δ1 t.1 = 0 := t.2
  obtain ⟨η, x, hx, heq⟩ := c.leray t.1 ht
  refine ⟨(η, ⟨x, hx⟩), ?_⟩
  apply Subtype.ext
  show c.δ0 η + d.rhoRaw x = t.1
  exact heq.symm

end HolomorphicCoboundaries

namespace HolomorphicDiskOverlapData

variable (d : HolomorphicDiskOverlapData)

/-- The trivial acyclic corrected model. -/
noncomputable def trivialCoboundaries : HolomorphicCoboundaries d where
  C0 := d.Cshr
  C2 := PUnit
  C2cov := PUnit
  δ0 := ContinuousLinearMap.id ℂ d.Cshr
  δ1 := 0
  δ1cov := 0
  hδδ := by simp
  hcomm := fun _ _ => by simp
  leray := fun s _ => ⟨s, 0, by simp, by simp⟩

/-- The corrected trivial model is acyclic. -/
theorem supH1_trivialCoboundaries_subsingleton :
    Subsingleton (d.trivialCoboundaries).supH1 := by
  rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]
  intro z
  refine ⟨(z : d.Cshr), Subtype.ext ?_⟩
  rw [ContinuousLinearMap.coe_coe, HolomorphicCoboundaries.δ,
    ContinuousLinearMap.coe_codRestrict_apply]
  rfl

/-- The empty overlap-index corrected model. -/
def empty : HolomorphicDiskOverlapData where
  J := Fin 0
  Uov := fun p => p.elim0
  hUov := fun p => p.elim0
  Wov := fun p => p.elim0
  hWov := fun p => p.elim0
  hKcpt := fun p => p.elim0
  hWU := fun p => p.elim0

instance : Subsingleton (HolomorphicDiskOverlapData.empty.trivialCoboundaries).supH1 :=
  HolomorphicDiskOverlapData.empty.supH1_trivialCoboundaries_subsingleton

/-- The corrected holomorphic branch has the same acyclic existence theorem as the old branch:
if the germ-class `H¹` is a subsingleton, the trivial corrected model suffices. -/
theorem exists_holomorphicCechModel_of_subsingleton (𝔘 : FiniteFamily X) (D : Divisor X)
    [Subsingleton (𝔘.cechH1 D)] :
    ∃ (d : HolomorphicDiskOverlapData) (c : HolomorphicCoboundaries d),
      Nonempty (𝔘.cechH1 D ≃ₗ[ℂ] c.supH1) :=
  ⟨HolomorphicDiskOverlapData.empty, HolomorphicDiskOverlapData.empty.trivialCoboundaries,
    ⟨LinearEquiv.ofSubsingleton _ _⟩⟩

end HolomorphicDiskOverlapData

end Jacobians.Dolbeault
