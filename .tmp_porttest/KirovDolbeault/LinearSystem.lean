/-
  Linear system `L(D)`, its dimension `l(D)`, and the `MeromorphicFunction` ℂ-algebra + `orderW`.

  EXTRACTED VERBATIM from `RiemannRoch.lean` (2026-06-04, no logic change) so the Čech/Dolbeault
  ladder (`CechSection` → … → `DolbeaultLadder`) can depend on `lDim`/`linearSystem`/`orderW`
  WITHOUT importing `RiemannRoch`.  This breaks the dependency cycle that put `RiemannRoch` — which
  *states* the interface obligation `exists_riemannRoch_divisor` — UPSTREAM of the ladder that *proves*
  its content (`DolbeaultLadder.riemannRoch_equality_of_ladder`), so the ladder's proof could never
  feed back to discharge the interface.  With this split the ladder is free of `RiemannRoch`, and
  `RiemannRoch` (downstream) can import the ladder to connect the two (the upstream→downstream
  assembly of the Riemann–Roch spine).

  Contents (all axiom-clean, charted-space-only footprint via `omit`, so they apply to open
  submanifolds `↥U`): `MeromorphicFunction.ext`/`toFun_injective`; the pointwise meromorphy lemmas
  `IsMeromorphic.{add,neg,sub,const_smul,nsmul,zsmul}`; the ℂ-vector-space instances on
  `MeromorphicFunction X` (`Module ℂ`); `orderW` and its faithfulness/identity theorems; and the
  linear system `linearSystem D`, the germ-zero junk submodule `germZeroSubmodule`, and `lDim`.
-/
import KirovDolbeault.Abel
import KirovDolbeault.MeromorphicLiouville

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace MeromorphicFunction

-- The structural facts and the ℂ-module algebra below use only the charted-space structure (no
-- compactness/connectedness), so they apply to open submanifolds `↥U` too. Omit the unused
-- hypotheses so the derived instances have a minimal typeclass footprint.
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]

/-- Two meromorphic functions are equal iff their underlying maps agree (the meromorphy
field is a `Prop`, hence proof-irrelevant). -/
@[ext] theorem ext {f g : MeromorphicFunction X} (h : f.toFun = g.toFun) : f = g := by
  obtain ⟨ft, fh⟩ := f
  obtain ⟨gt, gh⟩ := g
  subst h
  rfl

theorem toFun_injective :
    Function.Injective (MeromorphicFunction.toFun : MeromorphicFunction X → (X → ℂ)) :=
  fun _ _ h => ext h

end MeromorphicFunction

/-! ### Meromorphy is preserved by the pointwise vector-space operations

These need only the charted-space structure, not the full compact-manifold hypotheses. -/

section
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]

theorem IsMeromorphic.add {f g : X → ℂ} (hf : IsMeromorphic X f) (hg : IsMeromorphic X g) :
    IsMeromorphic X (f + g) := fun x => (hf x).add (hg x)

theorem IsMeromorphic.neg {f : X → ℂ} (hf : IsMeromorphic X f) :
    IsMeromorphic X (-f) := fun x => (hf x).neg

theorem IsMeromorphic.sub {f g : X → ℂ} (hf : IsMeromorphic X f) (hg : IsMeromorphic X g) :
    IsMeromorphic X (f - g) := by rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem IsMeromorphic.const_smul (c : ℂ) {f : X → ℂ} (hf : IsMeromorphic X f) :
    IsMeromorphic X (c • f) := fun x => (MeromorphicAt.const c _).smul (hf x)

theorem IsMeromorphic.nsmul (n : ℕ) {f : X → ℂ} (hf : IsMeromorphic X f) :
    IsMeromorphic X (n • f) := by
  have h : (n • f : X → ℂ) = (n : ℂ) • f := by funext x; simp [nsmul_eq_mul]
  rw [h]; exact hf.const_smul _

theorem IsMeromorphic.zsmul (n : ℤ) {f : X → ℂ} (hf : IsMeromorphic X f) :
    IsMeromorphic X (n • f) := by
  have h : (n • f : X → ℂ) = (n : ℂ) • f := by funext x; simp [zsmul_eq_mul]
  rw [h]; exact hf.const_smul _

end

/-! ### The ℂ-vector-space structure on `MeromorphicFunction X`

Built by transporting the structure on `X → ℂ` along the injective map `toFun`. -/

namespace MeromorphicFunction

section Algebra
-- The ℂ-vector-space algebra uses only the charted-space structure; omit the rest so the module
-- instances apply to open submanifolds `↥U` (which are not compact) — used by the Dolbeault Čech layer.
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]

noncomputable instance : Zero (MeromorphicFunction X) := ⟨⟨fun _ => 0, IsMeromorphic.zero X⟩⟩
noncomputable instance : Add (MeromorphicFunction X) :=
  ⟨fun f g => ⟨f.toFun + g.toFun, IsMeromorphic.add f.meromorphic g.meromorphic⟩⟩
noncomputable instance : Neg (MeromorphicFunction X) :=
  ⟨fun f => ⟨-f.toFun, IsMeromorphic.neg f.meromorphic⟩⟩
noncomputable instance : Sub (MeromorphicFunction X) :=
  ⟨fun f g => ⟨f.toFun - g.toFun, IsMeromorphic.sub f.meromorphic g.meromorphic⟩⟩
noncomputable instance : SMul ℕ (MeromorphicFunction X) :=
  ⟨fun n f => ⟨n • f.toFun, IsMeromorphic.nsmul n f.meromorphic⟩⟩
noncomputable instance : SMul ℤ (MeromorphicFunction X) :=
  ⟨fun n f => ⟨n • f.toFun, IsMeromorphic.zsmul n f.meromorphic⟩⟩
noncomputable instance : SMul ℂ (MeromorphicFunction X) :=
  ⟨fun c f => ⟨c • f.toFun, IsMeromorphic.const_smul c f.meromorphic⟩⟩

@[simp] theorem add_toFun (f g : MeromorphicFunction X) :
    (f + g).toFun = f.toFun + g.toFun := rfl
@[simp] theorem zero_toFun : (0 : MeromorphicFunction X).toFun = 0 := rfl
@[simp] theorem neg_toFun (f : MeromorphicFunction X) : (-f).toFun = -f.toFun := rfl
@[simp] theorem sub_toFun (f g : MeromorphicFunction X) :
    (f - g).toFun = f.toFun - g.toFun := rfl
@[simp] theorem smul_toFun (c : ℂ) (f : MeromorphicFunction X) :
    (c • f).toFun = c • f.toFun := rfl

noncomputable instance : AddCommGroup (MeromorphicFunction X) :=
  toFun_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The underlying-map homomorphism, used to transport the `Module` structure. -/
def toFunHom : MeromorphicFunction X →+ (X → ℂ) where
  toFun := MeromorphicFunction.toFun
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance : Module ℂ (MeromorphicFunction X) :=
  toFun_injective.module ℂ toFunHom (fun _ _ => rfl)

end Algebra

/-- The order of `f` at `x` as `WithTop ℤ` — the meromorphic order *before* the `untop₀` that
defines `orderAtPoint`. It is `⊤` exactly when `f` vanishes in a punctured neighbourhood of `x`;
phrasing `L(D)` on this order makes the zero function a member of every `L(D)` automatically. -/
noncomputable def orderW (f : MeromorphicFunction X) (x : X) : WithTop ℤ :=
  meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)

theorem orderW_zero (x : X) : (0 : MeromorphicFunction X).orderW x = ⊤ := by
  rw [orderW, meromorphicOrderAt_eq_top_iff]
  exact Filter.Eventually.of_forall fun _ => rfl

/-- The chart is a local homeomorphism near `y`, so an eventually-property of `g` on the punctured
neighbourhood `𝓝[≠] y` transfers to the chart-pulled-back function on `𝓝[≠] (chart y)`. -/
theorem eventually_comp_chart_iff (g : X → ℂ) (y : X) (P : ℂ → Prop) :
    (∀ᶠ w in 𝓝[≠] ((chartAt (H := ℂ) y) y), P ((g ∘ (chartAt (H := ℂ) y).symm) w))
      ↔ ∀ᶠ z in 𝓝[≠] y, P (g z) := by
  have hy : y ∈ (chartAt (H := ℂ) y).source := mem_chart_source ℂ y
  have hyt : (chartAt (H := ℂ) y) y ∈ (chartAt (H := ℂ) y).target :=
    (chartAt (H := ℂ) y).map_source hy
  have hey : (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y) = y :=
    (chartAt (H := ℂ) y).left_inv hy
  rw [eventually_nhdsWithin_iff, eventually_nhdsWithin_iff]
  constructor
  · intro h
    have h2 := ((chartAt (H := ℂ) y).continuousAt hy).eventually h
    filter_upwards [h2, (chartAt (H := ℂ) y).open_source.mem_nhds hy] with z hz hz_src
    intro hz_mem
    have hz_ne : z ≠ y := hz_mem
    have hchart : (chartAt (H := ℂ) y) z ∈ ({(chartAt (H := ℂ) y) y} : Set ℂ)ᶜ :=
      fun heq => hz_ne ((chartAt (H := ℂ) y).injOn hz_src hy heq)
    have := hz hchart
    rwa [Function.comp_apply, (chartAt (H := ℂ) y).left_inv hz_src] at this
  · intro h
    have hsymm : ContinuousAt (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y) :=
      (chartAt (H := ℂ) y).continuousAt_symm hyt
    have h2 := hsymm.eventually (p := fun z => z ∈ ({y} : Set X)ᶜ → P (g z)) (by rw [hey]; exact h)
    filter_upwards [h2, (chartAt (H := ℂ) y).open_target.mem_nhds hyt] with w hw hw_tgt
    intro hw_mem
    have hw_ne : w ≠ (chartAt (H := ℂ) y) y := hw_mem
    have hsymm_ne : (chartAt (H := ℂ) y).symm w ∈ ({y} : Set X)ᶜ := by
      intro heq
      apply hw_ne
      have hr := (chartAt (H := ℂ) y).right_inv hw_tgt
      rw [Set.mem_singleton_iff.mp heq] at hr
      exact hr.symm
    have := hw hsymm_ne
    rw [Function.comp_apply]; exact this

/-- `orderW f y = ⊤` (the germ vanishes) iff `f.toFun` vanishes throughout a punctured
neighbourhood of `y` (intrinsic — the chart drops out). -/
theorem orderW_eq_top_iff (f : MeromorphicFunction X) (y : X) :
    f.orderW y = ⊤ ↔ ∀ᶠ z in 𝓝[≠] y, f.toFun z = 0 := by
  rw [orderW, meromorphicOrderAt_eq_top_iff]
  exact eventually_comp_chart_iff f.toFun y (· = 0)

/-- `orderW f y ≠ ⊤` (the germ is nonzero) iff `f.toFun` is eventually nonzero on a punctured
neighbourhood of `y`. -/
theorem orderW_ne_top_iff (f : MeromorphicFunction X) (y : X) :
    f.orderW y ≠ ⊤ ↔ ∀ᶠ z in 𝓝[≠] y, f.toFun z ≠ 0 := by
  rw [orderW, meromorphicOrderAt_ne_top_iff_eventually_ne_zero (f.meromorphic y)]
  exact eventually_comp_chart_iff f.toFun y (· ≠ 0)

/-- **Faithfulness / identity theorem.** If the germ of `f` is nonzero at even one point, it is
nonzero (`orderW ≠ ⊤`) at *every* point. The set `{y | orderW f y = ⊤}` and its complement are
both open (via the two intrinsic characterizations above), so on the connected `X` it is empty. -/
theorem orderW_ne_top_of_exists (f : MeromorphicFunction X)
    (h₀ : ∃ x₀, f.orderW x₀ ≠ ⊤) (x : X) : f.orderW x ≠ ⊤ := by
  obtain ⟨x₀, hx₀⟩ := h₀
  have hUopen : IsOpen {y : X | f.orderW y = ⊤} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    rw [Set.mem_setOf_eq, orderW_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff] at hy
    obtain ⟨V, hV, hVopen, hyV⟩ := hy
    refine Filter.mem_of_superset (hVopen.mem_nhds hyV) fun y' hy'V => ?_
    rw [Set.mem_setOf_eq, orderW_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff]
    rcases eq_or_ne y' y with rfl | hy'
    · exact ⟨V, hV, hVopen, hy'V⟩
    · exact ⟨V \ {y}, fun z hz _ => hV z hz.1 hz.2, hVopen.sdiff isClosed_singleton, ⟨hy'V, hy'⟩⟩
  have hUclosed : IsClosed {y : X | f.orderW y = ⊤} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    have hyne : f.orderW y ≠ ⊤ := hy
    rw [orderW_ne_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff] at hyne
    obtain ⟨W, hW, hWopen, hyW⟩ := hyne
    refine Filter.mem_of_superset (hWopen.mem_nhds hyW) fun y' hy'W => ?_
    show f.orderW y' ≠ ⊤
    rw [orderW_ne_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff]
    rcases eq_or_ne y' y with rfl | hy'ne
    · exact ⟨W, hW, hWopen, hy'W⟩
    · exact ⟨W \ {y}, fun z hz _ => hW z hz.1 hz.2, hWopen.sdiff isClosed_singleton, ⟨hy'W, hy'ne⟩⟩
  rcases isClopen_iff.mp ⟨hUclosed, hUopen⟩ with hU | hU
  · show x ∉ {y : X | f.orderW y = ⊤}
    rw [hU]; exact Set.notMem_empty x
  · exact absurd (hU.ge (Set.mem_univ x₀)) hx₀

end MeromorphicFunction

/-! ## Part 2: the linear system `L(D)`, its dimension `l(D)`, and the isolated RR inputs -/

/-- The complete linear system `L(D)` = meromorphic functions with `div f ≥ −D`, phrased on the
`WithTop ℤ` order (so the zero function, order `⊤`, is automatically a member). A `Submodule ℂ`. -/
noncomputable def linearSystem (D : Divisor X) : Submodule ℂ (MeromorphicFunction X) where
  carrier := {f | ∀ x, (-(D x) : WithTop ℤ) ≤ f.orderW x}
  add_mem' {f g} hf hg := fun x =>
    le_trans (le_min (hf x) (hg x)) (meromorphicOrderAt_add (f.meromorphic x) (g.meromorphic x))
  zero_mem' := fun x => by rw [MeromorphicFunction.orderW_zero]; exact le_top
  smul_mem' c f hf := fun x => by
    rcases eq_or_ne c 0 with hc | hc
    · have h0 : (c • f).orderW x = ⊤ := by
        rw [hc, zero_smul]; exact MeromorphicFunction.orderW_zero x
      rw [h0]; exact le_top
    · rw [show (c • f).orderW x = f.orderW x from
        meromorphicOrderAt_smul_of_ne_zero analyticAt_const (by simpa using hc)]
      exact hf x

/-- **Germ-zero "junk" functions.** `MeromorphicFunction.toFun` carries removable-singularity
junk (cf. the `toSphere` note): e.g. the indicator of a single point is a *nonzero* meromorphic
function whose germ is `0` everywhere (`orderW ≡ ⊤`). Such functions lie in EVERY `L(D)`, and
point-indicators are linearly independent, so the naive `finrank ℂ (L(D))` is wrong (the space is
infinite-dimensional, forcing `finrank = 0` for all `D`, which makes RR false). We quotient them
out so `l(D)` is the genuine, finite dimension. -/
noncomputable def germZeroSubmodule : Submodule ℂ (MeromorphicFunction X) where
  carrier := {f | ∀ x, f.orderW x = ⊤}
  add_mem' {f g} hf hg := fun x => by
    have h : min (f.orderW x) (g.orderW x) ≤ (f + g).orderW x :=
      meromorphicOrderAt_add (f.meromorphic x) (g.meromorphic x)
    rw [hf x, hg x, min_self] at h
    exact top_le_iff.mp h
  zero_mem' := fun x => MeromorphicFunction.orderW_zero x
  smul_mem' c f hf := fun x => by
    rcases eq_or_ne c 0 with hc | hc
    · rw [hc, zero_smul]; exact MeromorphicFunction.orderW_zero x
    · rw [show (c • f).orderW x = f.orderW x from
        meromorphicOrderAt_smul_of_ne_zero analyticAt_const (by simpa using hc)]
      exact hf x

/-- `l(D) = dim_ℂ (L(D) ⧸ germ-zero junk)` (Forster's `h⁰(X, O_D)`) — the genuine dimension of
the linear system, with the `toFun`-junk quotiented out. -/
noncomputable def lDim (D : Divisor X) : ℕ :=
  Module.finrank ℂ
    (↥(linearSystem (X := X) D) ⧸ (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) D))


/-- **A function in `L(0)` is germ-constant** (Liouville). With no pole (`orderW ≥ 0`), the
limit-repair `holoRepr` is holomorphic (`mdifferentiable_holoRepr`), hence constant on the compact
connected `X` (`exists_eq_const_of_compactSpace`); off-center the chart pullback equals that
constant, so `f.toFun` agrees with it on every punctured neighbourhood. This is the repo's
Liouville-for-meromorphic content (`MeromorphicLiouville`), reused — no new analysis. -/
theorem germ_eq_const_of_mem_linearSystem_zero (f : MeromorphicFunction X)
    (hf : f ∈ linearSystem (X := X) 0) : ∃ c : ℂ, ∀ x, ∀ᶠ z in 𝓝[≠] x, f.toFun z = c := by
  have hpos : ∀ x, 0 ≤ f.orderAtPoint x := by
    intro x
    have hx := hf x
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hx
    exact untop₀_nonneg_iff.mpr hx
  obtain ⟨c, hc_const⟩ := (f.mdifferentiable_holoRepr hpos).exists_eq_const_of_compactSpace
  have hc : ∀ y, f.holoRepr y = c := fun y => congrFun hc_const y
  refine ⟨c, fun x => ?_⟩
  set φ := chartAt (H := ℂ) x with hφ
  obtain ⟨V, hVopen, hzV, hFV, hrepr⟩ := f.exists_holoRepr_eq_NFOn x (hpos x)
  have hF_eq : (f.toFun ∘ φ.symm) =ᶠ[𝓝[≠] (φ x)] (fun _ => c) := by
    have h1 := hFV.toMeromorphicNFOn_eq_self_on_nhdsNE hzV
    have h2 : (fun w => toMeromorphicNFOn (f.toFun ∘ φ.symm) V w) =ᶠ[𝓝[≠] (φ x)] (fun _ => c) := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hVopen.mem_nhds hzV)] with w hw
      rw [← hrepr w hw]; exact hc _
    exact h1.symm.trans h2
  exact (MeromorphicFunction.eventually_comp_chart_iff f.toFun x (· = c)).mp hF_eq

/-- `l(0) = 1`: `L(0)/germZero ≅ ℂ` (the constants). Spanned by the class of the constant `1`
(nonzero, since its order is `0 ≠ ⊤`), and every member is germ-constant by Liouville, hence a
scalar multiple of it. Elementary finiteness — uses Liouville, not the wall. -/
theorem lDim_zero_eq_one : lDim (X := X) 0 = 1 := by
  have h1m : IsMeromorphic X (fun _ : X => (1 : ℂ)) := fun x => MeromorphicAt.const 1 _
  have horder1 : ∀ x, MeromorphicFunction.orderW (⟨fun _ => 1, h1m⟩ : MeromorphicFunction X) x = 0 := by
    intro x
    show meromorphicOrderAt ((fun _ : X => (1 : ℂ)) ∘ (chartAt (H := ℂ) x).symm) _ = 0
    rw [show ((fun _ : X => (1 : ℂ)) ∘ (chartAt (H := ℂ) x).symm) = (fun _ => (1 : ℂ)) from rfl,
      meromorphicOrderAt_const]
    simp
  have hmem1 : (⟨fun _ => 1, h1m⟩ : MeromorphicFunction X) ∈ linearSystem (X := X) 0 := by
    intro x
    rw [horder1 x]
    simp
  set q : ↥(linearSystem (X := X) 0) := ⟨⟨fun _ => 1, h1m⟩, hmem1⟩ with hq
  rw [lDim]
  refine finrank_eq_one (Submodule.Quotient.mk q) ?_ ?_
  · -- `[const 1] ≠ 0`: else `const 1 ∈ germZero`, but its order is `0 ≠ ⊤`.
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    intro hmem
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have : MeromorphicFunction.orderW (⟨fun _ => 1, h1m⟩ : MeromorphicFunction X) x = ⊤ :=
      (Submodule.mem_comap.mp hmem) x
    rw [horder1 x] at this
    exact (by decide : (0 : WithTop ℤ) ≠ ⊤) this
  · -- surjectivity: every class is `c • [const 1]` for the germ-constant value `c`.
    intro w
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨c, hgc⟩ := germ_eq_const_of_mem_linearSystem_zero g.1 g.2
    refine ⟨c, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    show ((c • q - g : ↥(linearSystem (X := X) 0)) : MeromorphicFunction X) ∈ germZeroSubmodule
    intro x
    rw [MeromorphicFunction.orderW_eq_top_iff]
    filter_upwards [hgc x] with z hz
    show c • (1 : ℂ) - g.1.toFun z = 0
    rw [hz]; simp

end Jacobians
