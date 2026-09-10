/-
  Dolbeault ladder — **general-divisor Čech `H¹` finiteness** (Forster GTM 81 §16, the skyscraper
  reduction), reducing the arbitrary-divisor case to the already-proven `D = 0` case.

  ## What this file proves

      `finiteDimensional_cechH1_general (𝔘 : FiniteCover X) (D : Divisor X) :
         FiniteDimensional ℂ (𝔘.cechH1 D)`

  for an ARBITRARY finite cover `𝔘` and an ARBITRARY divisor `D`.  The `D = 0` case
  (`CechFinitenessAssembly.finiteDimensional_cechH1_zero`) is the proven base; we climb the divisor
  one point at a time.

  ## The argument (a LIGHT skyscraper reduction — no snake lemma, no acyclicity, no witness)

  The sheaves `𝒪_D ⊆ 𝒪_{D+P}` differ only in the allowed pole order at the single point `P`.  At every
  open `W`, the **stalk quotient** `OmegaDGerm (D+P) W ⧸ OmegaDGerm D W` is at most `1`-dimensional: the
  order-`(−D(P)−1)` principal-part coefficient `coeffGermLin` has kernel exactly `OmegaDGerm D W`
  (`ker_coeffGermLin`), so the quotient injects into `ℂ`.  Consequently, for the *finite* index types of
  the Čech complex:

    * `sections0 (D+P) ⧸ sections0 D` is finite-dimensional (a finite product of stalk quotients);
    * `sections1 (D+P) ⧸ sections1 D` is finite-dimensional likewise;
    * hence `cocycles1 (D+P) ⧸ cocycles1 D` is finite-dimensional (it injects into the `sections1`
      quotient), and `coboundaries1 (D+P) ⧸ coboundaries1 D` is too (a quotient of the `sections0` one).

  From these finite "correction" spaces, finiteness of `H¹` propagates BOTH ways along the inclusion
  `h1Map : H¹(𝒪_D) → H¹(𝒪_{D+P})`:

    * **forward** (`H¹(D)` finite ⟹ `H¹(D+P)` finite): `range h1Map` is finite (image of a finite-dim
      space) and `coker h1Map` is a quotient of `cocycles1(D+P)/cocycles1(D)` (finite), so
      `H¹(D+P)` is an extension of two finite-dim spaces (`Module.Finite.of_submodule_quotient`);
    * **backward** (`H¹(D+P)` finite ⟹ `H¹(D)` finite): `ker h1Map` is a quotient of
      `coboundaries1(D+P)/coboundaries1(D)` (finite) and `H¹(D)/ker h1Map ≅ range h1Map` (finite), so
      `H¹(D)` is again an extension of two finite-dim spaces.

  The bidirectional per-point step (`finiteDimensional_cechH1_add_single_iff`) then drives an induction:
  `Int.induction_on` on the coefficient (a single point, `±1` at a time) and `Finsupp.induction` on the
  divisor (one point at a time), with base `D = 0`.

  Everything is complete and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/
import KirovDolbeault.Dolbeault.CechFinitenessAssembly
import KirovDolbeault.Dolbeault.SkyscraperArrow

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The skyscraper stalk quotient is finite-dimensional (≤ 1) -/

/-- **The skyscraper stalk quotient is at most `1`-dimensional.**  At any open `W ∋ P`, the order-
`(−D(P)−1)` principal-part coefficient `coeffGermLin` has kernel exactly `OmegaDGerm D W`
(`ker_coeffGermLin`), so the quotient `OmegaDGerm (D+P) W ⧸ OmegaDGerm D W` injects into `ℂ` and is
finite-dimensional. -/
theorem finiteDimensional_stalkQuotient {W : Opens X} {D : Divisor X} {P : X} (hP : P ∈ W) :
    FiniteDimensional ℂ
      (OmegaDGerm (D + Finsupp.single P 1) W ⧸
        (OmegaDGerm D W).submoduleOf (OmegaDGerm (D + Finsupp.single P 1) W)) := by
  -- The descended coefficient map `quotient ↪ ℂ` (kernel is exactly `OmegaDGerm D W`).
  have hker : (OmegaDGerm D W).submoduleOf (OmegaDGerm (D + Finsupp.single P 1) W)
      = LinearMap.ker (coeffGermLin hP (D := D)) := (ker_coeffGermLin hP).symm
  rw [hker]
  -- `quotient by ker(coeffGermLin) ≅ range(coeffGermLin) ⊆ ℂ`, a finite-dim space.
  exact Module.Finite.equiv (LinearMap.quotKerEquivRange (coeffGermLin hP (D := D))).symm

/-- For an open `W` NOT containing `P`, the stalk quotient is `0` (the section spaces coincide). -/
theorem finiteDimensional_stalkQuotient_of_not_mem {W : Opens X} {D : Divisor X} {P : X}
    (hP : P ∉ W) :
    FiniteDimensional ℂ
      (OmegaDGerm (D + Finsupp.single P 1) W ⧸
        (OmegaDGerm D W).submoduleOf (OmegaDGerm (D + Finsupp.single P 1) W)) := by
  -- The two section spaces coincide, so the quotient is by `⊤` (subsingleton, hence finite-dim).
  have heq : OmegaDGerm (D + Finsupp.single P 1) W = OmegaDGerm D W :=
    OmegaDGerm_add_single_eq_of_not_mem hP
  haveI : Subsingleton (OmegaDGerm (D + Finsupp.single P 1) W ⧸
      (OmegaDGerm D W).submoduleOf (OmegaDGerm (D + Finsupp.single P 1) W)) := by
    rw [Submodule.Quotient.subsingleton_iff, Submodule.submoduleOf, heq,
      Submodule.comap_subtype_self]
  infer_instance

/-! ### The Pi-section quotient is finite-dimensional (the common shape of `sections0`/`sections1`) -/

/-- The `𝒪_D` Pi-section submodule over a finite family of opens `W : ι → Opens X`: tuples of germs
with each component a `𝒪_D`-germ.  Both `sections0 D` and `sections1 D` are instances of this (with
`W` the cover-sets resp. the pairwise overlaps).  Definitionally a `Submodule` of `∀ i, MGerm (W i)`. -/
def piSec {ι : Type*} (W : ι → Opens X) (D : Divisor X) : Submodule ℂ (∀ i, MGerm (W i)) where
  carrier := {f | ∀ i, f i ∈ OmegaDGerm D (W i)}
  add_mem' hf hg i := add_mem (hf i) (hg i)
  zero_mem' _ := Submodule.zero_mem _
  smul_mem' c _ hf i := Submodule.smul_mem _ c (hf i)

open scoped Classical in
/-- The component coefficient functional `piSec W (D+P) →ₗ[ℂ] ℂ` at index `i`: the order-`(−D(P)−1)`
principal-part coefficient at `P` on `W i` when `P ∈ W i` (`coeffGermLin`), and `0` otherwise.  Its
vanishing characterises `𝒪_D`-membership of the `i`-component (`piSec_coeff_eq_zero_iff`). -/
noncomputable def piSec_coeff {ι : Type*} (W : ι → Opens X) (D : Divisor X) (P : X) (i : ι) :
    piSec W (D + Finsupp.single P 1) →ₗ[ℂ] ℂ :=
  if h : P ∈ W i then
    (coeffGermLin h).comp
      (((LinearMap.proj i).comp (piSec W (D + Finsupp.single P 1)).subtype).codRestrict
        (OmegaDGerm (D + Finsupp.single P 1) (W i)) (fun f => f.2 i))
  else 0

/-- The component coefficient vanishes iff the `i`-component is a `𝒪_D`-germ.  When `P ∈ W i` this is
`ker_coeffGermLin`; when `P ∉ W i` the coefficient is `0` and the `D` / `D+P` section spaces coincide
(`OmegaDGerm_add_single_eq_of_not_mem`), so membership is automatic. -/
theorem piSec_coeff_eq_zero_iff {ι : Type*} (W : ι → Opens X) (D : Divisor X) (P : X) (i : ι)
    (f : piSec W (D + Finsupp.single P 1)) :
    piSec_coeff W D P i f = 0 ↔ (f : ∀ i, MGerm (W i)) i ∈ OmegaDGerm D (W i) := by
  unfold piSec_coeff
  by_cases h : P ∈ W i
  · rw [dif_pos h, LinearMap.comp_apply, ← LinearMap.mem_ker, ker_coeffGermLin,
      Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
    rfl
  · rw [dif_neg h]
    simp only [LinearMap.zero_apply, true_iff]
    rw [← OmegaDGerm_add_single_eq_of_not_mem h]
    exact f.2 i

/-- **The Pi-section skyscraper-correction quotient is finite-dimensional.**  Over a *finite* family
`W : ι → Opens X`, the quotient `piSec W (D+P) ⧸ piSec W D` injects, via the tuple of component
principal-part coefficients `piSec_coeff`, into the clean finite-dimensional `ι → ℂ`; the kernel of
that tuple map is exactly `piSec W D` (`piSec_coeff_eq_zero_iff`), so the quotient is
finite-dimensional.  (Routing through `ι → ℂ` rather than the product of stalk quotients avoids the
heavy `Module`-instance synthesis on the dependent product of `OmegaDGerm`-quotients.) -/
theorem finiteDimensional_piSec_quotient {ι : Type*} [Fintype ι] (W : ι → Opens X)
    (D : Divisor X) (P : X) :
    FiniteDimensional ℂ
      (piSec W (D + Finsupp.single P 1) ⧸ (piSec W D).submoduleOf (piSec W (D + Finsupp.single P 1))) := by
  classical
  -- The tuple-of-coefficients map `G : piSec W (D+P) →ₗ (ι → ℂ)`.
  set G : piSec W (D + Finsupp.single P 1) →ₗ[ℂ] (ι → ℂ) :=
    LinearMap.pi (fun i => piSec_coeff W D P i) with hG
  -- `ker G = piSec W D`: componentwise via `piSec_coeff_eq_zero_iff`.
  have hkerG : LinearMap.ker G = (piSec W D).submoduleOf (piSec W (D + Finsupp.single P 1)) := by
    refine Submodule.ext fun f => ?_
    rw [LinearMap.mem_ker, hG, funext_iff, Submodule.submoduleOf, Submodule.mem_comap,
      Submodule.coe_subtype]
    constructor
    · intro hf i
      have := hf i
      rw [LinearMap.pi_apply, Pi.zero_apply] at this
      exact (piSec_coeff_eq_zero_iff W D P i f).mp this
    · intro hf i
      rw [LinearMap.pi_apply, Pi.zero_apply]
      exact (piSec_coeff_eq_zero_iff W D P i f).mpr (hf i)
  -- The quotient by `ker G` injects into `ι → ℂ` (finite-dim), hence is finite-dim.
  rw [← hkerG]
  exact Module.Finite.equiv (LinearMap.quotKerEquivRange G).symm

/-! ### Abstract finiteness propagation through `⊓` and `map` (for cocycles / coboundaries) -/

/-- **Finiteness through `⊓`.**  For `A ≤ B` and any `K`, the quotient `(K ⊓ B) ⧸ (K ⊓ A)` injects into
`B ⧸ A` (the inclusion `K ⊓ B ↪ B`), so it is finite-dimensional whenever `B ⧸ A` is.  (Used for
`cocycles1 = ker δ¹ ⊓ sections1`: `K = ker δ¹`, `A/B = sections1 D / sections1 (D+P)`.) -/
theorem finiteDimensional_inf_quotient {M : Type*} [AddCommGroup M] [Module ℂ M]
    (K A B : Submodule ℂ M) (_hAB : A ≤ B)
    (hfin : FiniteDimensional ℂ (B ⧸ A.submoduleOf B)) :
    FiniteDimensional ℂ
      ((K ⊓ B : Submodule ℂ M) ⧸ (K ⊓ A).submoduleOf (K ⊓ B : Submodule ℂ M)) := by
  refine FiniteDimensional.of_injective
    (Submodule.mapQ ((K ⊓ A).submoduleOf (K ⊓ B : Submodule ℂ M)) (A.submoduleOf B)
      (Submodule.inclusion (inf_le_right : (K ⊓ B : Submodule ℂ M) ≤ B)) ?_) ?_
  · -- the inclusion carries `(K⊓A).submoduleOf(K⊓B)` into `A.submoduleOf B`.
    intro x hx
    rw [Submodule.mem_comap, Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
    rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at hx
    exact (Submodule.mem_inf.mp hx).2
  · -- injectivity: `x ∈ K⊓B` with `(x:M) ∈ A` ⟹ `x ∈ K⊓A` (so `comap incl q ≤ ker mkQ`).
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, ← le_bot_iff,
      Submodule.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_comap, Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at hy
    rw [Submodule.mem_comap, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype, Submodule.mem_inf]
    exact ⟨(Submodule.mem_inf.mp y.2).1, hy⟩

/-- **Finiteness through `map`.**  For `A0 ≤ B0` and a linear map `f`, the quotient
`(map f B0) ⧸ (map f A0)` is a quotient (surjective image) of `B0 ⧸ A0` (via `f` descended), so it is
finite-dimensional whenever `B0 ⧸ A0` is.  (Used for `coboundaries1 = map δ⁰ sections0`.) -/
theorem finiteDimensional_map_quotient {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (f : M →ₗ[ℂ] N) (A0 B0 : Submodule ℂ M) (_hAB : A0 ≤ B0)
    (hfin : FiniteDimensional ℂ (B0 ⧸ A0.submoduleOf B0)) :
    FiniteDimensional ℂ ((B0.map f) ⧸ (A0.map f).submoduleOf (B0.map f)) := by
  -- `f` restricted to `B0` corestricted to `map f B0`, surjective and carrying `A0`-classes.
  set g : B0 →ₗ[ℂ] B0.map f :=
    (f.domRestrict B0).codRestrict (B0.map f) (fun b => ⟨b.1, b.2, rfl⟩) with hg
  have hgsurj : Function.Surjective g := by
    rintro ⟨n, b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩
  -- descend `mkQ ∘ g : B0 → (map f B0)/(map f A0)`, killing `A0`.
  set h : B0 →ₗ[ℂ] (B0.map f) ⧸ (A0.map f).submoduleOf (B0.map f) :=
    ((A0.map f).submoduleOf (B0.map f)).mkQ.comp g with hh
  have hhsurj : Function.Surjective h :=
    (Submodule.mkQ_surjective _).comp hgsurj
  have hker : A0.submoduleOf B0 ≤ LinearMap.ker h := by
    intro a ha
    rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at ha
    rw [LinearMap.mem_ker, hh, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap,
      Submodule.coe_subtype]
    exact ⟨a.1, ha, rfl⟩
  -- the descended surjection `B0/A0 ↠ (map f B0)/(map f A0)`.
  have hsurj : Function.Surjective ((A0.submoduleOf B0).liftQ h hker) := by
    rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]
    exact hhsurj
  exact FiniteDimensional.of_surjective _ hsurj

namespace FiniteCover

open FiniteFamily

variable (𝔘 : FiniteCover X) (D : Divisor X) (P : X)

/-- `sections1 (D+P) ⧸ sections1 D` is finite-dimensional: it injects into the finite product
`∏ p, (OmegaDGerm (D+P) (U_p) ⧸ OmegaDGerm D (U_p))` of stalk quotients (each ≤ 1-dim, finitely many
overlaps `p : ι × ι`). -/
theorem finiteDimensional_sections1_quotient :
    FiniteDimensional ℂ
      (𝔘.sections1 (D + Finsupp.single P 1) ⧸
        (𝔘.sections1 D).submoduleOf (𝔘.sections1 (D + Finsupp.single P 1))) :=
  finiteDimensional_piSec_quotient (fun p : 𝔘.ι × 𝔘.ι => 𝔘.U p.1 ⊓ 𝔘.U p.2) D P

/-- `sections0 (D+P) ⧸ sections0 D` is finite-dimensional (degree-0 analogue). -/
theorem finiteDimensional_sections0_quotient :
    FiniteDimensional ℂ
      (𝔘.sections0 (D + Finsupp.single P 1) ⧸
        (𝔘.sections0 D).submoduleOf (𝔘.sections0 (D + Finsupp.single P 1))) :=
  finiteDimensional_piSec_quotient (fun i : 𝔘.ι => 𝔘.U i) D P

/-- `cocycles1 (D+P) ⧸ cocycles1 D` is finite-dimensional: the cocycle quotient injects into the
section quotient `sections1 (D+P) ⧸ sections1 D` (`cocycles1 = ker δ¹ ⊓ sections1`). -/
theorem finiteDimensional_cocycles1_quotient :
    FiniteDimensional ℂ
      (𝔘.cocycles1 (D + Finsupp.single P 1) ⧸
        (𝔘.cocycles1 D).submoduleOf (𝔘.cocycles1 (D + Finsupp.single P 1))) :=
  finiteDimensional_inf_quotient (LinearMap.ker 𝔘.cechDelta1) (𝔘.sections1 D)
    (𝔘.sections1 (D + Finsupp.single P 1)) (𝔘.sections1_le_add_single D P)
    (𝔘.finiteDimensional_sections1_quotient D P)

/-- `coboundaries1 (D+P) ⧸ coboundaries1 D` is finite-dimensional: it is a quotient of the degree-0
section quotient `sections0 (D+P) ⧸ sections0 D` (`coboundaries1 = δ⁰(sections0)`). -/
theorem finiteDimensional_coboundaries1_quotient :
    FiniteDimensional ℂ
      (𝔘.coboundaries1 (D + Finsupp.single P 1) ⧸
        (𝔘.coboundaries1 D).submoduleOf (𝔘.coboundaries1 (D + Finsupp.single P 1))) :=
  finiteDimensional_map_quotient 𝔘.cechDelta0 (𝔘.sections0 D)
    (𝔘.sections0 (D + Finsupp.single P 1)) (𝔘.sections0_le_add_single D P)
    (𝔘.finiteDimensional_sections0_quotient D P)

/-! ### The per-point step (both directions) -/

/-- `h1Map` on a cocycle class is the class of the cocycle inclusion: `h1Map [c] = [incl c]`.  (The
defining `Submodule.mapQ` computation.) -/
theorem h1Map_mk (c : 𝔘.cocycles1 D) :
    𝔘.h1Map D P (Submodule.Quotient.mk c)
      = Submodule.Quotient.mk (𝔘.cocyclesIncl D P c) := by
  rw [FiniteCover.h1Map, Submodule.mapQ_apply]

/-- **Forward per-point step.**  `H¹(𝒪_D)` finite ⟹ `H¹(𝒪_{D+P})` finite.  `range h1Map` is finite
(image of finite-dim `H¹(𝒪_D)`); `coker h1Map` is a quotient of `cocycles1(D+P)/cocycles1(D)`
(finite, `finiteDimensional_cocycles1_quotient`); so `H¹(𝒪_{D+P})` is the extension of two finite-dim
spaces (`Module.Finite.of_submodule_quotient`). -/
theorem finiteDimensional_cechH1_add_single_of
    (h : FiniteDimensional ℂ (𝔘.cechH1 D)) :
    FiniteDimensional ℂ (𝔘.cechH1 (D + Finsupp.single P 1)) := by
  haveI := h
  -- `range (h1Map D P)` is finite-dimensional (image of finite-dim `H¹(𝒪_D)`).
  haveI hrange : FiniteDimensional ℂ (LinearMap.range (𝔘.h1Map D P)) :=
    FiniteDimensional.of_surjective (𝔘.h1Map D P).rangeRestrict
      (LinearMap.surjective_rangeRestrict _)
  -- `coker (h1Map D P)` is finite-dimensional, via a surjection from `cocycles1(D+P)/cocycles1(D)`.
  haveI hcoker : FiniteDimensional ℂ
      (𝔘.cechH1 (D + Finsupp.single P 1) ⧸ LinearMap.range (𝔘.h1Map D P)) := by
    haveI hcq := 𝔘.finiteDimensional_cocycles1_quotient D P
    -- `Φ : cocycles1(D+P) → coker(h1Map)`, the H¹-class composed with the coker projection.
    set Φ : 𝔘.cocycles1 (D + Finsupp.single P 1) →ₗ[ℂ]
        (𝔘.cechH1 (D + Finsupp.single P 1) ⧸ LinearMap.range (𝔘.h1Map D P)) :=
      (LinearMap.range (𝔘.h1Map D P)).mkQ.comp
        ((𝔘.coboundaries1 (D + Finsupp.single P 1)).submoduleOf
          (𝔘.cocycles1 (D + Finsupp.single P 1))).mkQ with hΦ
    have hΦsurj : Function.Surjective Φ :=
      (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
    -- `Φ` kills `cocycles1(D)`: a `D`-cocycle's `(D+P)`-class is `h1Map` of its `D`-class, hence in range.
    have hker : (𝔘.cocycles1 D).submoduleOf (𝔘.cocycles1 (D + Finsupp.single P 1))
        ≤ LinearMap.ker Φ := by
      intro c hc
      rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at hc
      rw [LinearMap.mem_ker, hΦ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
      exact ⟨Submodule.Quotient.mk ⟨(c : 𝔘.Cochain1), hc⟩, by rw [𝔘.h1Map_mk]; rfl⟩
    -- the descended surjection `cocycles1(D+P)/cocycles1(D) ↠ coker(h1Map)`.
    have hsurj : Function.Surjective
        (((𝔘.cocycles1 D).submoduleOf (𝔘.cocycles1 (D + Finsupp.single P 1))).liftQ Φ hker) := by
      rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]; exact hΦsurj
    exact FiniteDimensional.of_surjective _ hsurj
  -- `H¹(𝒪_{D+P})` is the extension of `range (h1Map)` by its cokernel.
  exact Module.Finite.of_submodule_quotient (LinearMap.range (𝔘.h1Map D P))

/-- `ker (h1Map D P)` is finite-dimensional.  An element is a `D`-cocycle class `[c]_D` whose
`(D+P)`-class vanishes, i.e. `c ∈ cocycles1 D ⊓ coboundaries1 (D+P)`; the H¹-class map surjects that
intersection onto `ker (h1Map D P)` (killing `cocycles1 D ⊓ coboundaries1 D`), and the resulting
domain quotient injects into the finite `coboundaries1 (D+P)/coboundaries1 D`
(`finiteDimensional_inf_quotient`). -/
theorem finiteDimensional_ker_h1Map :
    FiniteDimensional ℂ (LinearMap.ker (𝔘.h1Map D P)) := by
  haveI hinf := finiteDimensional_inf_quotient (𝔘.cocycles1 D)
    (𝔘.coboundaries1 D) (𝔘.coboundaries1 (D + Finsupp.single P 1))
    (𝔘.coboundaries1_le_add_single D P) (𝔘.finiteDimensional_coboundaries1_quotient D P)
  set S : Submodule ℂ 𝔘.Cochain1 := 𝔘.cocycles1 D ⊓ 𝔘.coboundaries1 (D + Finsupp.single P 1) with hS
  have hSc : S ≤ 𝔘.cocycles1 D := inf_le_left
  -- `Θ : ↥S → ker(h1Map)`, `x ↦ [x]_D` (a coboundary of `D+P`, so its `(D+P)`-class — `h1Map` — is 0).
  set Θ : S →ₗ[ℂ] LinearMap.ker (𝔘.h1Map D P) :=
    (((𝔘.coboundaries1 D).submoduleOf (𝔘.cocycles1 D)).mkQ.comp
      (Submodule.inclusion hSc)).codRestrict (LinearMap.ker (𝔘.h1Map D P)) (fun x => by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, 𝔘.h1Map_mk,
          Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap,
          Submodule.coe_subtype]
        exact (Submodule.mem_inf.mp x.2).2) with hΘ
  have hΘsurj : Function.Surjective Θ := by
    rintro ⟨k, hk⟩
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ k
    rw [LinearMap.mem_ker, 𝔘.h1Map_mk, Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf,
      Submodule.mem_comap, Submodule.coe_subtype] at hk
    refine ⟨⟨(c : 𝔘.Cochain1), Submodule.mem_inf.mpr ⟨c.2, hk⟩⟩, ?_⟩
    apply Subtype.ext
    rw [hΘ]
    simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
    rfl
  -- `Θ` kills `cocycles1 D ⊓ coboundaries1 D` (those are `D`-coboundaries, so `[·]_D = 0`).
  have hker : (𝔘.cocycles1 D ⊓ 𝔘.coboundaries1 D).submoduleOf S ≤ LinearMap.ker Θ := by
    intro x hx
    rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype, Submodule.mem_inf] at hx
    rw [LinearMap.mem_ker, hΘ]
    apply Subtype.ext
    simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
      ZeroMemClass.coe_zero]
    rw [Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap,
      Submodule.coe_subtype]
    exact hx.2
  -- the descended surjection from the finite inf-quotient onto `ker(h1Map)`.
  have hsurj : Function.Surjective
      (((𝔘.cocycles1 D ⊓ 𝔘.coboundaries1 D).submoduleOf S).liftQ Θ hker) := by
    rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]; exact hΘsurj
  exact FiniteDimensional.of_surjective _ hsurj

/-- **Backward per-point step.**  `H¹(𝒪_{D+P})` finite ⟹ `H¹(𝒪_D)` finite.  `ker (h1Map D P)` is
finite-dimensional (`finiteDimensional_ker_h1Map`), and `H¹(𝒪_D)/ker (h1Map) ≅ range (h1Map) ⊆
H¹(𝒪_{D+P})` is finite; so `H¹(𝒪_D)` is the extension of two finite-dim spaces
(`Module.Finite.of_submodule_quotient`). -/
theorem finiteDimensional_cechH1_of_add_single
    (h : FiniteDimensional ℂ (𝔘.cechH1 (D + Finsupp.single P 1))) :
    FiniteDimensional ℂ (𝔘.cechH1 D) := by
  haveI := h
  haveI := 𝔘.finiteDimensional_ker_h1Map D P
  -- `H¹(𝒪_D)/ker (h1Map) ≅ range (h1Map) ⊆ H¹(𝒪_{D+P})`, finite.
  haveI hquot : FiniteDimensional ℂ (𝔘.cechH1 D ⧸ LinearMap.ker (𝔘.h1Map D P)) :=
    Module.Finite.equiv (LinearMap.quotKerEquivRange (𝔘.h1Map D P)).symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker (𝔘.h1Map D P))

/-- **The bidirectional per-point step.**  `H¹(𝒪_{D+P})` is finite iff `H¹(𝒪_D)` is. -/
theorem finiteDimensional_cechH1_add_single_iff :
    FiniteDimensional ℂ (𝔘.cechH1 (D + Finsupp.single P 1)) ↔
      FiniteDimensional ℂ (𝔘.cechH1 D) :=
  ⟨𝔘.finiteDimensional_cechH1_of_add_single D P,
    𝔘.finiteDimensional_cechH1_add_single_of D P⟩

/-! ### Divisor induction -/

/-- `H¹(𝒪_{D + single P k})` is finite iff `H¹(𝒪_D)` is, for any integer `k` (induct on `k` via
`Int.induction_on`; `±1` at a time is the per-point step). -/
theorem finiteDimensional_cechH1_add_singlePoint_iff (k : ℤ) :
    FiniteDimensional ℂ (𝔘.cechH1 (D + Finsupp.single P k)) ↔
      FiniteDimensional ℂ (𝔘.cechH1 D) := by
  induction k using Int.induction_on with
  | zero => rw [Finsupp.single_zero, add_zero]
  | succ k ih =>
    -- `D + single P (↑k+1) = (D + single P ↑k) + single P 1`; per-point step, then `ih`.
    rw [show (Finsupp.single P ((k : ℤ) + 1) : Divisor X)
        = Finsupp.single P (k : ℤ) + Finsupp.single P 1 from by rw [← Finsupp.single_add],
      ← add_assoc, 𝔘.finiteDimensional_cechH1_add_single_iff (D + Finsupp.single P (k : ℤ)) P]
    exact ih
  | pred k ih =>
    -- `(D + single P (−↑k−1)) + single P 1 = D + single P (−↑k)`; per-point step bridges them.
    rw [← ih,
      (𝔘.finiteDimensional_cechH1_add_single_iff (D + Finsupp.single P (-(k : ℤ) - 1)) P).symm,
      add_assoc, ← Finsupp.single_add, show (-(k : ℤ) - 1 + 1) = -(k : ℤ) from by ring]

/-- **Finiteness of `H¹(𝒪_D)` for any divisor `D`, on a FIXED cover, from the `D = 0` case** (the
divisor induction).  `Finsupp.induction` on `D` adds one point at a time; each addition is the
single-point step. -/
theorem finiteDimensional_cechH1_of_zero (h0 : FiniteDimensional ℂ (𝔘.cechH1 (0 : Divisor X)))
    (D : Divisor X) :
    FiniteDimensional ℂ (𝔘.cechH1 D) := by
  induction D using Finsupp.induction with
  | zero => exact h0
  | single_add a b f _ _ ih =>
    -- `single a b + f = f + single a b`; the single-point step bridges `cechH1 f` and `cechH1 (…)`.
    rw [add_comm]
    exact (𝔘.finiteDimensional_cechH1_add_singlePoint_iff f a b).mpr ih

end FiniteCover

/-! ### The general theorem (any cover, any divisor) -/

/-- **General-divisor Čech `H¹` finiteness (Forster 14.9 + §16 skyscraper).**  For an arbitrary finite
cover `𝔘` and an arbitrary divisor `D`, `H¹(𝔘, 𝒪_D)` is finite-dimensional.  The proven `D = 0` case
(`finiteDimensional_cechH1_zero`) is climbed to general `D` one point at a time via the skyscraper stalk
quotient (`finiteDimensional_cechH1_of_zero`). -/
theorem finiteDimensional_cechH1_general (𝔘 : FiniteCover X) (D : Divisor X) :
    FiniteDimensional ℂ (𝔘.cechH1 D) :=
  𝔘.finiteDimensional_cechH1_of_zero (finiteDimensional_cechH1_zero 𝔘) D

/-- **`exists_cechModel 𝔘 D` — the full, general-divisor statement, PROVEN complete.**  Combines the
general-divisor finiteness `finiteDimensional_cechH1_general` (this file) with the artificial
single-point Montel model `exists_cechModel_of_finiteDimensional` (`CechModelArtificial`).  This is
exactly the statement of `CechFinitenessWiring.exists_cechModel` for an ARBITRARY divisor `D` — the
finiteness node's keystone — with no remaining hypotheses.  (The `CechFinitenessWiring.exists_cechModel`
declaration itself is discharged by this term once the model-types import cycle is broken; see the
project notes.) -/
theorem exists_cechModel_general (𝔘 : FiniteCover X) (D : Divisor X) :
    ∃ (d : DiskOverlapData) (c : Coboundaries d), Nonempty (𝔘.cechH1 D ≃ₗ[ℂ] c.supH1) :=
  haveI : FiniteDimensional ℂ (𝔘.cechH1 D) := finiteDimensional_cechH1_general 𝔘 D
  exists_cechModel_of_finiteDimensional 𝔘 D

end Jacobians.Dolbeault
