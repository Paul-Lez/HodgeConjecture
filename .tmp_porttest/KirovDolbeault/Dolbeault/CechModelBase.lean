/-
  Dolbeault ladder — the sup-norm Čech model TYPES and abstract finiteness spine (Forster 14.9).

  This is the *type / abstract-spine* base of the manifold instantiation of the Čech finiteness node.
  It was split out of `CechFinitenessWiring.lean` to BREAK an import cycle: the model types
  (`DiskOverlapData`, `Coboundaries`, `supH1`) are consumed by `CechModelArtificial` /
  `CechModelGeometry`, which in turn feed (transitively) the general-divisor finiteness term
  `CechFinitenessDtwist.exists_cechModel_general`; that term is what discharges
  `CechFinitenessWiring.exists_cechModel`.  Keeping the types here (importing only the abstract spine)
  lets `CechFinitenessWiring` import `CechFinitenessDtwist` without a cycle.

  This file ASSEMBLES the proven abstract finiteness spine
  (`CechFinitenessAbstract.finiteDimensional_h1_of_leray_compact`, `isCompactOperator_pi`,
  `isCompactOperator_of_subtypeL_comp`) against the proven disk-Montel atom
  (`BddHol.isCompactOperator_restrictCLM`) to provide the finiteness machinery used to discharge
  `DolbeaultLadder.finiteDimensional_cechH1`.

  CHOSEN SUP-NORM COCHAIN ENCODING (the Leray chart-disk cover, read in charts):
  the 1-cochains on the COVER live in `Π_p BddHol (Uov p)` (bounded-holomorphic on the chart-image
  of each overlap, an open set in `ℂ`); the 1-cochains on the relatively-compact SHRINKING live in
  `Π_p (Kov p →ᵇ ℂ)` (the Montel atom restricts `BddHol U →L[ℂ] (K →ᵇ ℂ)` for `K` compact, so the
  shrinking side is a product of `→ᵇ` spaces, NOT `BddHol`). Cocycle subspaces are kernels of the
  sup-norm coboundary `δ¹`, hence closed (so Banach). This data is packaged in `DiskOverlapData`
  (the geometric overlap data) + `Coboundaries` (the sup-norm `δ⁰/δ¹` and the commuting square for
  restriction).

  WHAT IS PROVEN HERE (axiom-clean, `[propext, Classical.choice, Quot.sound]`):
    * `DiskOverlapData` Banach instances; `rhoRaw` + `rhoRaw_compact` (STEP 3 — the Montel payoff).
    * `finiteDimensional_supH1` — STEP 5: builds the cocycle `δ`/`ρ`, transports compactness to the
      closed cocycle subspace, and applies the abstract reduction. Fully proven *given* the Leray
      surjectivity (an explicit argument).
    * `leray_surjective` — STEP 4: the Leray surjectivity, derived from the model's `leray` field.
    * `exists_cechModel_of_subsingleton` — the assembled acyclic case (`H¹ = 0`).

  KEY DESIGN POINT (soundness): the Leray surjectivity `(η,ξ) ↦ δη + ρξ` is FALSE for an arbitrary
  abstract `(δ, ρ)` — a *compact* `ρ` (which `rhoRaw_compact` proves ours is) cannot surject onto an
  infinite-dimensional cocycle space. Surjectivity holds only for a genuine *acyclic* Leray model.
  We therefore record the acyclicity as the `Coboundaries.leray` field (the disk-`H¹=0` witness):
  `leray_surjective` then unpacks it, and the honest analytic obligation is concentrated
  where the model is CONSTRUCTED — discharged in `CechFinitenessDtwist.exists_cechModel_general`.
-/
import KirovDolbeault.Dolbeault.CechFinitenessAbstract
import KirovDolbeault.Dolbeault.BddHol
import KirovDolbeault.Dolbeault.CechModelBridge
import KirovDolbeault.Dolbeault.DbarDiskCohomology
import KirovDolbeault.Dolbeault.CechH0

open Jacobians.Dolbeault.CechFiniteness ContinuousLinearMap
open BoundedContinuousFunction
open scoped Manifold ContDiff Topology

namespace Jacobians.Dolbeault

/-! ### STEP 1 — the geometric overlap data (chart-disk cover + relatively-compact shrinking) -/

/-- **Sup-norm cochain geometry.** The finite pair-index `J` of a Leray chart-disk cover, with, for
each overlap `p`, the chart-image cover-open `Uov p ⊆ ℂ` and a relatively-compact convex shrinking
`Kov p ⋐ Uov p`. This is exactly the geometric input the disk-Montel atom needs (open `U`, compact
convex `K ⊆ U`). The cover 1-cochains live in `Π_p BddHol (Uov p)`, the shrinking 1-cochains in
`Π_p (Kov p →ᵇ ℂ)`. -/
structure DiskOverlapData where
  /-- The finite pair-index of the cover (overlaps). -/
  J : Type
  [fintypeJ : Fintype J]
  [decEqJ : DecidableEq J]
  /-- Chart-image of each overlap on the COVER (an open set in `ℂ`). -/
  Uov : J → Set ℂ
  hUov : ∀ p, IsOpen (Uov p)
  /-- The relatively-compact SHRINKING of each overlap (a compact set in `ℂ`).  No convexity is
  required: the restriction operator is compact for any compact `K ⊆ U`
  (`BddHol.isCompactOperator_restrictCLM_of_compact`), so `Kov` can be a chart-image of an overlap
  (which is NOT convex across charts). -/
  Kov : J → Set ℂ
  hKcpt : ∀ p, IsCompact (Kov p)
  hKU : ∀ p, Kov p ⊆ Uov p

attribute [instance] DiskOverlapData.fintypeJ DiskOverlapData.decEqJ

namespace DiskOverlapData

variable (d : DiskOverlapData)

/-- Each shrinking compact carries a `CompactSpace` (so `Kov p →ᵇ ℂ` is a Banach space). -/
noncomputable instance compactSpace (p : d.J) : CompactSpace (d.Kov p) :=
  isCompact_iff_compactSpace.mp (d.hKcpt p)

/-- COVER 1-cochains: bounded-holomorphic on each overlap chart-image. -/
abbrev Ccov : Type := ∀ p : d.J, BddHol (d.Uov p)

/-- SHRINKING 1-cochains: bounded-continuous on each compact shrunk overlap (where the Montel atom
lands). -/
abbrev Cshr : Type := ∀ p : d.J, (d.Kov p →ᵇ ℂ)

noncomputable instance : NormedAddCommGroup d.Ccov := inferInstance
noncomputable instance : NormedSpace ℂ d.Ccov := inferInstance
noncomputable instance : NormedAddCommGroup d.Cshr := inferInstance
noncomputable instance : NormedSpace ℂ d.Cshr := inferInstance

/-- `Π_p BddHol (Uov p)` is a Banach space (finite product of the Banach `BddHol`). -/
noncomputable instance : CompleteSpace d.Ccov := by
  haveI : ∀ p, CompleteSpace (BddHol (d.Uov p)) := fun p => BddHol.completeSpace (d.hUov p)
  infer_instance

/-- `Π_p (Kov p →ᵇ ℂ)` is a Banach space. -/
noncomputable instance : CompleteSpace d.Cshr := inferInstance

/-! ### STEP 2/3 — the restriction operator `ρ` cover → shrinking, and its compactness -/

/-- The raw cochain restriction `Π_p BddHol (Uov p) →L[ℂ] Π_p (Kov p →ᵇ ℂ)`, componentwise
`BddHol.restrictCLM`. -/
noncomputable def rhoRaw : d.Ccov →L[ℂ] d.Cshr :=
  ContinuousLinearMap.pi (fun p => (BddHol.restrictCLM (d.hKU p)).comp (proj p))

@[simp] theorem rhoRaw_apply (f : d.Ccov) (p : d.J) :
    d.rhoRaw f p = BddHol.restrictCLM (d.hKU p) (f p) := by
  simp only [rhoRaw, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

/-- **STEP 3 (the Montel payoff).** The cochain restriction `ρ` (cover → shrinking) is a COMPACT
operator: componentwise it is `BddHol.restrictCLM`, compact by the disk-Montel atom
(`BddHol.isCompactOperator_restrictCLM_of_compact`, valid for any compact shrunk overlap — no
convexity), and a finite product of compacts is compact (`isCompactOperator_pi`). -/
theorem rhoRaw_compact : IsCompactOperator d.rhoRaw := by
  apply isCompactOperator_pi (fun p => BddHol.restrictCLM (d.hKU p))
  intro p
  exact BddHol.isCompactOperator_restrictCLM_of_compact (d.hUov p) (d.hKcpt p) (d.hKU p)

end DiskOverlapData

/-! ### The sup-norm coboundary bundle and the cocycle spaces -/

/-- **Sup-norm coboundary data** completing `DiskOverlapData` to a Čech `δ`-complex. We need the
shrinking-side coboundaries `δ⁰ : C0 → C¹(shrinking)` and `δ¹ : C¹(shrinking) → C²(shrinking)` with
`δ¹∘δ⁰ = 0`, a coboundary `δ¹` on the COVER side (whose kernel is `Z¹(cover)`), and the commuting
square saying restriction `ρ` carries cover-cocycles to shrinking-cocycles. These are the analytic
inputs that make `Z¹/B¹` the sup-norm `H¹`. -/
structure Coboundaries (d : DiskOverlapData) where
  /-- 0-cochain Banach space on the shrinking. -/
  C0 : Type
  [ng0 : NormedAddCommGroup C0]
  [ns0 : NormedSpace ℂ C0]
  [cs0 : CompleteSpace C0]
  /-- 2-cochain Banach space on the shrinking. -/
  C2 : Type
  [ng2 : NormedAddCommGroup C2]
  [ns2 : NormedSpace ℂ C2]
  /-- 2-cochain Banach space on the cover (target of the cover-side `δ¹`). -/
  C2cov : Type
  [ng2c : NormedAddCommGroup C2cov]
  [ns2c : NormedSpace ℂ C2cov]
  /-- The shrinking-side `δ⁰`. -/
  δ0 : C0 →L[ℂ] d.Cshr
  /-- The shrinking-side `δ¹`. -/
  δ1 : d.Cshr →L[ℂ] C2
  /-- The cover-side `δ¹` (its kernel is `Z¹(cover)`). -/
  δ1cov : d.Ccov →L[ℂ] C2cov
  /-- `δ¹∘δ⁰ = 0` on the shrinking (so `B¹ ⊆ Z¹`). -/
  hδδ : δ1.comp δ0 = 0
  /-- Restriction carries cover-cocycles to shrinking-cocycles (the commuting square). -/
  hcomm : ∀ x : d.Ccov, δ1cov x = 0 → δ1 (d.rhoRaw x) = 0
  /-- **The Leray / disk-acyclicity witness.** Every shrinking 1-cocycle `s` (i.e. `δ¹s = 0`) is,
  modulo a shrinking-coboundary `δ⁰η`, the restriction `ρ x` of a COVER 1-cocycle `x`
  (`δ¹_cov x = 0`). This is the genuine analytic content of the Leray model — it is precisely
  `H¹(disk, 𝒪) = 0` on each chart-disk (the disk-acyclicity supplied by the proven full-disk
  ∂̄-solvability `DbarDiskCohomology.dbar_solvable_ball` / `dbar_holo_splitting_ball`) together with
  the Čech-refinement comparison. Without this field the abstract data is NOT a Leray model and
  surjectivity is FALSE (a compact `ρ` cannot surject an infinite-dimensional `Z¹`); bundling it here
  is what makes `Coboundaries d` mean "an acyclic chart-disk Leray model". The honest analytic
  obligation therefore lives entirely in the model construction. -/
  leray : ∀ s : d.Cshr, δ1 s = 0 →
    ∃ (η : C0) (x : d.Ccov), δ1cov x = 0 ∧ s = δ0 η + d.rhoRaw x

attribute [instance] Coboundaries.ng0 Coboundaries.ns0 Coboundaries.cs0
  Coboundaries.ng2 Coboundaries.ns2 Coboundaries.ng2c Coboundaries.ns2c

namespace Coboundaries

variable {d : DiskOverlapData} (c : Coboundaries d)

/-- `Z¹(cover) = ker δ¹(cover)`, a closed subspace of the cover 1-cochains. -/
noncomputable def Z1cov : Submodule ℂ d.Ccov := LinearMap.ker c.δ1cov.toLinearMap

/-- `Z¹(shrinking) = ker δ¹(shrinking)`, a closed subspace of the shrinking 1-cochains. -/
noncomputable def Z1shr : Submodule ℂ d.Cshr := LinearMap.ker c.δ1.toLinearMap

theorem isClosed_Z1cov : IsClosed (c.Z1cov : Set d.Ccov) := c.δ1cov.isClosed_ker

theorem isClosed_Z1shr : IsClosed (c.Z1shr : Set d.Cshr) := c.δ1.isClosed_ker

noncomputable instance : CompleteSpace c.Z1cov := c.δ1cov.isClosed_ker.completeSpace_coe
noncomputable instance : CompleteSpace c.Z1shr := c.δ1.isClosed_ker.completeSpace_coe

/-- The coboundary `δ : C⁰ →L[ℂ] Z¹(shrinking)` (i.e. `δ⁰` corestricted to the cocycles, using
`δ¹∘δ⁰=0`). Its range is `B¹`, and `Z¹/range δ` is the sup-norm `H¹`. -/
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
  ext x; rfl

/-- **STEP 3 on the cocycle subspace.** `ρ : Z¹(cover) →L Z¹(shrinking)` is a COMPACT operator:
`rhoRaw` is compact (`DiskOverlapData.rhoRaw_compact`), `ρ` includes into it via the closed cocycle
subspace, and `isCompactOperator_of_subtypeL_comp` transports compactness back. -/
theorem ρ_compact : IsCompactOperator c.ρ := by
  apply isCompactOperator_of_subtypeL_comp c.isClosed_Z1shr c.ρ
  rw [c.subtypeL_comp_ρ]
  exact d.rhoRaw_compact.comp_clm c.Z1cov.subtypeL

/-- **The sup-norm `H¹`** of the cover/shrinking pair: `Z¹(shrinking) ⧸ B¹`, where `B¹ = range δ`.
This is the object the abstract reduction makes finite-dimensional; it is compared to the genuine
germ-class `cechH1` by `cechH1_model`. -/
abbrev supH1 : Type := c.Z1shr ⧸ LinearMap.range c.δ.toLinearMap

/-- **STEP 5 — finiteness of the sup-norm `H¹`.** Given the Leray surjectivity of `(η,ξ) ↦ δη + ρξ`,
the abstract reduction `finiteDimensional_h1_of_leray_compact` (with `ρ` compact by `ρ_compact`)
gives `supH1` finite-dimensional. Fully proven modulo the surjectivity argument. -/
theorem finiteDimensional_supH1
    (hsurj : Function.Surjective (fun p : c.C0 × c.Z1cov => c.δ p.1 + c.ρ p.2)) :
    FiniteDimensional ℂ c.supH1 :=
  finiteDimensional_h1_of_leray_compact c.δ c.ρ hsurj c.ρ_compact

end Coboundaries

/-! ### STEP 4 — the Leray surjectivity (PROVEN from the model's `leray` field) -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **STEP 4 — Leray surjectivity (PROVEN).** For any chart-disk Leray model `c`, the combined map
`(η, ξ) ↦ δη + ρξ` (shrinking-coboundary ⊕ cover-restriction) is surjective onto `Z¹(shrinking)`.

This unpacks the model's `leray` field (the disk-acyclicity witness): given a shrinking cocycle
`t ∈ Z¹(shrinking)` (so `δ¹ t = 0`), `c.leray` produces `η : C⁰` and a cover cocycle `x`
(`δ¹_cov x = 0`) with `t = δ⁰η + ρ_raw x`; corestricting to the cocycle subspaces (`c.δ`, `c.ρ`),
the pair `(η, ⟨x, _⟩)` maps to `t`. The genuine analytic content (`H¹(disk, 𝒪) = 0` + Čech
refinement) is carried by the `leray` field and discharged where the model is built; here it is pure
bookkeeping. -/
theorem leray_surjective (d : DiskOverlapData) (c : Coboundaries d) :
    Function.Surjective (fun p : c.C0 × c.Z1cov => c.δ p.1 + c.ρ p.2) := by
  intro t
  -- `t : Z¹(shrinking)`, so `t.1 : Cshr` with `δ¹ t.1 = 0`.
  have ht : c.δ1 t.1 = 0 := t.2
  obtain ⟨η, x, hx, heq⟩ := c.leray t.1 ht
  refine ⟨(η, ⟨x, hx⟩), ?_⟩
  -- Both `δ` and `ρ` are corestrictions, so the underlying value of `δ η + ρ ⟨x,_⟩` is
  -- `δ⁰η + ρ_raw x = t.1`; conclude by `Subtype.ext`.
  apply Subtype.ext
  show c.δ0 η + d.rhoRaw x = t.1
  exact heq.symm

/-! ### The trivial acyclic model and the assembled `exists_cechModel` for the acyclic case

These bank the END-TO-END model assembly (`DiskOverlapData` + `Coboundaries` with its `leray`
disk-acyclicity field + the bundled comparison) for exactly the case the completed disk-acyclicity
produces — a SUBSINGLETON germ-class `H¹` (`H¹(disk, 𝒪) = 0`).  The general `exists_cechModel` (an
arbitrary cover with a non-acyclic `H¹`) is discharged by the general-divisor term
`CechFinitenessDtwist.exists_cechModel_general`; the acyclic case is fully discharged here, and the
geometric instantiation via `SharedChartCover.hasGluedDbarDatum` is banked in
`CechModelConstruction.lean` (which imports `CechFinitenessWiring`). -/

namespace DiskOverlapData

variable (d : DiskOverlapData)

/-- **The trivial acyclic `Coboundaries`.**  For any `DiskOverlapData d`, the `Coboundaries d` with
`C⁰ = Cshr`, `δ⁰ = id`, `δ¹ = 0`, `δ¹_cov = 0`.  Structural fields hold trivially; the genuine
analytic `leray` field is DISCHARGED (every shrinking cocycle `s` is `δ⁰ s + ρ 0 = s`).  Its sup-norm
`H¹` is `0` (`supH1_trivialCoboundaries_subsingleton`) — the `leray` disk-acyclicity field wired at the
acyclic extreme, the shape the completed `hasGluedDbarDatum` lands in. -/
noncomputable def trivialCoboundaries : Coboundaries d where
  C0 := d.Cshr
  C2 := PUnit
  C2cov := PUnit
  δ0 := ContinuousLinearMap.id ℂ d.Cshr
  δ1 := 0
  δ1cov := 0
  hδδ := by simp
  hcomm := fun _ _ => by simp
  leray := fun s _ => ⟨s, 0, by simp, by simp⟩

/-- **The trivial model is acyclic.**  `(trivialCoboundaries d).supH1` is a subsingleton: its
`Z¹(shrinking) = ker δ¹ = Cshr` (`δ¹ = 0`) and `range δ = ⊤` (`δ` corestricts the surjective `δ⁰ =
id`), so the quotient is trivial. -/
theorem supH1_trivialCoboundaries_subsingleton :
    Subsingleton (d.trivialCoboundaries).supH1 := by
  rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]
  intro z
  refine ⟨(z : d.Cshr), Subtype.ext ?_⟩
  rw [ContinuousLinearMap.coe_coe, Coboundaries.δ, ContinuousLinearMap.coe_codRestrict_apply]
  rfl

/-- A `DiskOverlapData` with empty overlap index (so `Ccov`/`Cshr` are subsingletons) — the carrier of
the trivial model that witnesses the acyclic `exists_cechModel`. -/
def empty : DiskOverlapData where
  J := Fin 0
  Uov := fun p => p.elim0
  hUov := fun p => p.elim0
  Kov := fun p => p.elim0
  hKcpt := fun p => p.elim0
  hKU := fun p => p.elim0

/-- The sup-norm `H¹` of the empty model's trivial `Coboundaries` is a subsingleton (instance of
`supH1_trivialCoboundaries_subsingleton`). -/
instance : Subsingleton (DiskOverlapData.empty.trivialCoboundaries).supH1 :=
  DiskOverlapData.empty.supH1_trivialCoboundaries_subsingleton

end DiskOverlapData

/-- **`exists_cechModel` for a subsingleton germ-class `H¹` (the assembled acyclic case, complete).**
If the genuine germ-class `𝔘.cechH1 D` is a SUBSINGLETON, then `exists_cechModel 𝔘 D` holds: take the
trivial acyclic model (`DiskOverlapData.empty` with its `trivialCoboundaries`, whose `leray`
disk-acyclicity field is discharged and whose `supH1` is `0`); the comparison `𝔘.cechH1 D ≃ₗ supH1` is
then `LinearEquiv.ofSubsingleton` (both sides subsingleton `ℂ`-modules).  This is the end-to-end model
assembly for exactly the case the completed disk-acyclicity produces (`H¹ = 0`); it is correctly tied
to `(𝔘, D)` via the existential (not a free `c`).  The geometric instantiation — a `SharedChartCover`
at `D = 0` discharging the subsingleton hypothesis via `hasGluedDbarDatum` — is
`CechModelConstruction.exists_cechModel_of_sharedChart_zero`. -/
theorem exists_cechModel_of_subsingleton (𝔘 : FiniteFamily X) (D : Divisor X)
    [Subsingleton (𝔘.cechH1 D)] :
    ∃ (d : DiskOverlapData) (c : Coboundaries d), Nonempty (𝔘.cechH1 D ≃ₗ[ℂ] c.supH1) :=
  ⟨DiskOverlapData.empty, DiskOverlapData.empty.trivialCoboundaries,
    ⟨LinearEquiv.ofSubsingleton _ _⟩⟩

end Jacobians.Dolbeault
