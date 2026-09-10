/-
  Dolbeault ladder — the ARTIFICIAL (single-point) chart-disk model of `exists_cechModel`.

  This file gives a fully complete, axiom-clean witness for the *bundled* model existential
  `exists_cechModel_of_finiteDimensional`: assuming only that the genuine germ-class `H¹`,
  `𝔘.cechH1 D`, is finite-dimensional, it produces a `DiskOverlapData` + `Coboundaries` whose
  sup-norm `H¹` is `ℂ`-linearly isomorphic to `𝔘.cechH1 D`.

  THE TRICK (soundness). The honest `CechFinitenessWiring.exists_cechModel` builds a model whose
  `rhoRaw` is a COMPACT operator from the cover cochains to the shrinking cochains; the `leray`
  field of such a model would force a compact operator to surject the (possibly
  infinite-dimensional) cocycle space — impossible unless the cocycle space is finite-dimensional.
  Here we sidestep that by choosing each `Kov p` to be a SINGLE point `{0}`. Then `↥{0} →ᵇ ℂ ≅ ℂ`
  and the shrinking cochains `d.Cshr = ∀ p : Fin k, (↥{0} →ᵇ ℂ)` are FINITE-dimensional. A compact
  `rhoRaw` may freely surject a finite-dimensional target, so the `leray` field is genuinely
  provable (every shrinking cochain is the restriction of a CONSTANT bounded-holomorphic function).

  We then set `δ0 = δ1 = δ1cov = 0`. With `δ1 = 0` the cocycle space `Z¹(shrinking)` is all of
  `Cshr` (`ker 0 = ⊤`), and with `δ0 = 0` the coboundary `δ` is `0`, so `B¹ = range δ = ⊥`. Hence
  `c.supH1 = Cshr ⧸ ⊥ ≅ Cshr ≅ (Fin k → ℂ)`. Matching the dimension `k = finrank (𝔘.cechH1 D)`
  with `(Module.finBasis ℂ _).equivFun` closes the comparison.

  This is an ARTIFICIAL model: it does NOT compute `cechH1` from the actual cover geometry. It is a
  consistency witness — it shows the *shape* of the `exists_cechModel` conclusion is inhabitable for
  any finite-dimensional germ-class `H¹`, with the `leray`/compact-`rhoRaw` consistency respected
  (the one-point `Kov` keeps the shrinking side finite-dimensional). It is NOT a replacement for the
  honest manifold/Čech assembly.
-/
-- Only the model TYPES / abstract spine (`DiskOverlapData`, `Coboundaries`, `supH1`) are needed
-- here, so we import `CechModelBase` (not `CechFinitenessWiring`); this is what keeps
-- `CechFinitenessWiring → CechFinitenessDtwist → … → CechModelArtificial` acyclic.
import KirovDolbeault.Dolbeault.CechModelBase

open Jacobians.Dolbeault
open BoundedContinuousFunction
open scoped Manifold ContDiff Topology

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The one-point bounded-continuous-function space `↥{0} →ᵇ ℂ ≅ ℂ` -/

/-- A bounded-continuous function on the one-point space `↥({(0:ℂ)} : Set ℂ)` is determined by its
single value, giving `(↥{0} →ᵇ ℂ) ≃ₗ[ℂ] ℂ`. -/
noncomputable def onePointBcfEquiv : (↥({(0:ℂ)} : Set ℂ) →ᵇ ℂ) ≃ₗ[ℂ] ℂ := by
  haveI : Unique (↥({(0:ℂ)} : Set ℂ)) := Set.uniqueSingleton 0
  exact
    ({ toFun := fun f => f default, map_add' := by intro f g; simp,
       map_smul' := by intro c f; simp,
       invFun := fun z => BoundedContinuousFunction.const _ z,
       left_inv := by intro f; ext x; rw [Unique.eq_default x]; simp,
       right_inv := by intro z; simp }
     : (↥({(0:ℂ)} : Set ℂ) →ᵇ ℂ) ≃ₗ[ℂ] ℂ)

/-! ### A constant bounded-holomorphic function on the unit disk realizing any value -/

/-- The constant-`c` element of `BddHol (Metric.ball 0 1)`: the function equal to `c` on the ball and
`0` outside, which is analytic on the ball (it agrees with the constant `c` there) and bounded. -/
noncomputable def bddHolConst (c : ℂ) : BddHol (Metric.ball (0 : ℂ) 1) :=
  (⟨(Metric.ball (0 : ℂ) 1).indicator (fun _ => c),
    ⟨(analyticOn_const (v := c)).congr (fun z hz => by simp [Set.indicator_of_mem hz]),
      fun z hz => by simp [Set.indicator_of_notMem hz],
      ⟨‖c‖, fun z hz => by simp [Set.indicator_of_mem hz]⟩⟩⟩ :
    ↥(BddHolCarrier (Metric.ball (0 : ℂ) 1)))

@[simp] theorem bddHolConst_toFun_mem (c : ℂ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    (bddHolConst c).toFun z = c := by
  simp only [bddHolConst, BddHol.toFun, BddHol.toCarrier]
  simp [Set.indicator_of_mem hz]

/-! ### The artificial `DiskOverlapData`: `Fin k` copies of the unit disk with a one-point shrinking -/

/-- The single-point chart-disk overlap data on `Fin k`: every overlap is the unit disk
`Metric.ball 0 1`, every shrinking is the single point `{0}`. -/
def artificialData (k : ℕ) : DiskOverlapData where
  J := Fin k
  Uov := fun _ => Metric.ball (0 : ℂ) 1
  hUov := fun _ => Metric.isOpen_ball
  Kov := fun _ => {(0 : ℂ)}
  hKcpt := fun _ => isCompact_singleton
  hKU := fun _ z hz => by
    rw [Set.mem_singleton_iff] at hz
    subst hz
    simp [Metric.mem_ball]

@[simp] theorem artificialData_Uov (k : ℕ) (p : Fin k) :
    (artificialData k).Uov p = Metric.ball (0 : ℂ) 1 := rfl

@[simp] theorem artificialData_Kov (k : ℕ) (p : Fin k) :
    (artificialData k).Kov p = {(0 : ℂ)} := rfl

/-- `rhoRaw` of the artificial model is SURJECTIVE: each component
`BddHol.restrictCLM : BddHol (ball 0 1) → (↥{0} →ᵇ ℂ)` is surjected by a constant
bounded-holomorphic function, since the one-point bcf is determined by its value at `0`. -/
theorem artificialData_rhoRaw_surjective (k : ℕ) :
    Function.Surjective (artificialData k).rhoRaw := by
  intro s
  -- For each `p`, `(artificialData k).Kov p = {0}` is the one-point space.
  haveI hu : ∀ p : Fin k, Unique (↥((artificialData k).Kov p)) := fun _ => Set.uniqueSingleton 0
  -- Take the constant `BddHol` whose value is `s p` evaluated at the unique point.
  refine ⟨fun p => bddHolConst (s p default), ?_⟩
  funext p
  rw [DiskOverlapData.rhoRaw_apply]
  ext z
  -- The unique point of `↥{0}` is `default`, with value `0 ∈ ball 0 1`.
  rw [Unique.eq_default z]
  rw [BddHol.restrictCLM_apply, BddHol.restrict_apply]
  -- `(default : ↥{0}).1 = 0 ∈ ball 0 1`, so the constant `BddHol` evaluates to `s p default`.
  have hval : ((default : ↥((artificialData k).Kov p)) : ℂ) = 0 :=
    Set.eq_of_mem_singleton (default : ↥((artificialData k).Kov p)).2
  have hmem : ((default : ↥((artificialData k).Kov p)) : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [hval]; simp [Metric.mem_ball]
  exact bddHolConst_toFun_mem _ hmem

/-! ### The artificial `Coboundaries`: all coboundary maps zero, `leray` = `rhoRaw` surjectivity -/

/-- The trivial-`δ` `Coboundaries` on the artificial model: `C0 = C2 = C2cov = PUnit`, every
coboundary map is `0`. The `leray` field reduces (since `δ0 = δ1 = δ1cov = 0`) to the surjectivity
of `rhoRaw`, which holds because the one-point shrinking is realized by constant
bounded-holomorphic functions. -/
noncomputable def artificialCoboundaries (k : ℕ) : Coboundaries (artificialData k) where
  C0 := PUnit
  C2 := PUnit
  C2cov := PUnit
  δ0 := 0
  δ1 := 0
  δ1cov := 0
  hδδ := ContinuousLinearMap.zero_comp _
  hcomm := fun _ _ => by simp
  leray := fun s _ => by
    obtain ⟨x, hx⟩ := artificialData_rhoRaw_surjective k s
    exact ⟨PUnit.unit, x, by simp, by simpa using hx.symm⟩

/-! ### The comparison `(Fin k → ℂ) ≃ₗ supH1` of the artificial model -/

/-- The shrinking cochains of the artificial model are `(Fin k → ℂ)`, via the one-point bcf equiv on
each factor. -/
noncomputable def artificialCshrEquiv (k : ℕ) :
    (Fin k → ℂ) ≃ₗ[ℂ] (artificialData k).Cshr :=
  LinearEquiv.piCongrRight (fun _ => onePointBcfEquiv.symm)

/-- `Z¹(shrinking)` of the artificial model is `⊤` (`δ¹ = 0`). -/
theorem artificialCoboundaries_Z1shr_eq_top (k : ℕ) :
    (artificialCoboundaries k).Z1shr = ⊤ := by
  rw [Coboundaries.Z1shr, LinearMap.ker_eq_top]
  rfl

/-- The coboundary `δ` of the artificial model is `0` (`δ0 = 0`), so `range δ = ⊥`. -/
theorem artificialCoboundaries_range_δ_eq_bot (k : ℕ) :
    LinearMap.range (artificialCoboundaries k).δ.toLinearMap = ⊥ := by
  rw [LinearMap.range_eq_bot]
  exact LinearMap.ext fun x => Subtype.ext rfl

/-- `supH1` of the artificial model is `ℂ`-linearly isomorphic to the shrinking cochains `Cshr`:
`B¹ = range δ = ⊥` (so `Cshr ⧸ B¹ ≅ ↥Z¹`) and `Z¹ = ⊤` (so `↥Z¹ ≅ Cshr`). -/
noncomputable def artificialSupH1Equiv (k : ℕ) :
    (artificialCoboundaries k).supH1 ≃ₗ[ℂ] (artificialData k).Cshr :=
  -- `supH1 = ↥Z1shr ⧸ range δ`; range δ = ⊥, so `≅ ↥Z1shr`; Z1shr = ⊤, so `↥Z1shr ≅ Cshr`.
  ((LinearMap.range (artificialCoboundaries k).δ.toLinearMap).quotEquivOfEqBot
      (artificialCoboundaries_range_δ_eq_bot k)).trans
    ((LinearEquiv.ofEq _ _ (artificialCoboundaries_Z1shr_eq_top k)).trans Submodule.topEquiv)

/-! ### The bundled artificial model and the headline existential -/

/-- **The artificial (single-point) model witnesses the bundled `exists_cechModel` shape.** For any
finite-dimensional germ-class `H¹`, there is a `DiskOverlapData` + `Coboundaries` whose sup-norm
`H¹` is `ℂ`-linearly isomorphic to `𝔘.cechH1 D`.

Soundness: the model is artificial (it does NOT read the cover geometry); it uses a ONE-POINT
shrinking `Kov = {0}`, which keeps the shrinking cochains finite-dimensional, so the `leray` field
(forcing the compact `rhoRaw` to surject) is consistent and provable. The comparison composes
`𝔘.cechH1 D ≅ (Fin k → ℂ) ≅ Cshr ≅ supH1` with `k = finrank ℂ (𝔘.cechH1 D)`. -/
theorem exists_cechModel_of_finiteDimensional
    (𝔘 : FiniteCover X) (D : Divisor X) [FiniteDimensional ℂ (𝔘.cechH1 D)] :
    ∃ (d : Jacobians.Dolbeault.DiskOverlapData) (c : Jacobians.Dolbeault.Coboundaries d),
      Nonempty (𝔘.cechH1 D ≃ₗ[ℂ] c.supH1) := by
  set k := Module.finrank ℂ (𝔘.cechH1 D) with hk
  refine ⟨artificialData k, artificialCoboundaries k, ⟨?_⟩⟩
  -- Step 1: `𝔘.cechH1 D ≃ₗ (Fin k → ℂ)` from the finite basis (`finrank = k` definitionally).
  have e1 : (𝔘.cechH1 D) ≃ₗ[ℂ] (Fin k → ℂ) := (Module.finBasis ℂ (𝔘.cechH1 D)).equivFun
  -- Step 2: `(Fin k → ℂ) ≃ₗ Cshr`.
  have e2 : (Fin k → ℂ) ≃ₗ[ℂ] (artificialData k).Cshr := artificialCshrEquiv k
  -- Step 3: `Cshr ≃ₗ supH1`.
  have e3 : (artificialData k).Cshr ≃ₗ[ℂ] (artificialCoboundaries k).supH1 :=
    (artificialSupH1Equiv k).symm
  exact e1.trans (e2.trans e3)

end Jacobians.Dolbeault
