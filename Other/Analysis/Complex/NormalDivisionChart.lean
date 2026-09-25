/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache 2.0 License as described in the file LICENSE.
-/
module

public import Other.Analysis.Complex.NormalDivisionFinOne
public import Mathlib.Topology.OpenPartialHomeomorph.IsImage

@[expose] public section

open Filter Topology Set

namespace Complex

variable {M E : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Shrink a chart around a point so that an analytic function with a simple normal derivative
factors on the full restricted chart source.  The quotient supplied by
`exists_nhds_normalQuotientFinOne_factor` lives on the coordinate target; restricting the source
to its inverse image makes the factorization available on the whole chart, including the normal
zero locus. -/
theorem exists_restricted_normalDivision_chart
    (e : OpenPartialHomeomorph M (E × (Fin 1 → ℂ)))
    {f : M → ℂ} {q : M} (hq : q ∈ e.source)
    (hcenter : (e q).2 = 0)
    (hanalytic : AnalyticOnNhd ℂ (fun v ↦ f (e.symm v)) e.target)
    (hzero : ∀ v ∈ e.target, v.2 = 0 → f (e.symm v) = 0)
    (hk : fderiv ℂ (fun v ↦ f (e.symm v)) (e q)
      (0, fun _ : Fin 1 ↦ (1 : ℂ)) ≠ 0) :
    ∃ U : Set (E × (Fin 1 → ℂ)), U ∈ 𝓝 (e q) ∧ IsOpen U ∧ U ⊆ e.target ∧
      ∃ e' : OpenPartialHomeomorph M (E × (Fin 1 → ℂ)),
        q ∈ e'.source ∧ e'.source ⊆ e.source ∧
          e'.source = e.source ∩ e ⁻¹' U ∧
          (∀ y ∈ e'.source, e' y = e y) ∧
          (∀ y ∈ e'.source, e' y ∈ U) ∧
          ∃ u : C((e'.source : Set M), ℂ),
            (∀ y, u y ≠ 0) ∧
              (∀ y : e'.source,
                f y = (e' y).2 0 * u y) := by
  obtain ⟨U, hUn, hUopen, hUsub, u, hu, hfactor⟩ :=
    exists_nhds_normalQuotientFinOne_factor e.open_target hzero hanalytic
      (e.map_source hq) hcenter hk
  let A := e.source ∩ e ⁻¹' U
  have hAopen : IsOpen A := e.isOpen_inter_preimage hUopen
  let e' := e.restrOpen A hAopen
  have hqU : e q ∈ U := mem_of_mem_nhds hUn
  have hqA : q ∈ A := ⟨hq, hqU⟩
  have hq' : q ∈ e'.source := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hq, hqA⟩
  have hchartU : ∀ y : e'.source, e' y ∈ U := by
    intro y
    exact y.property.2.2
  let chartMap : C((e'.source : Set M), U) :=
    ⟨fun y ↦ ⟨e' y, hchartU y⟩,
      (continuousOn_iff_continuous_domRestrict.mp e'.continuousOn).subtype_mk _⟩
  let u' := u.comp chartMap
  refine ⟨U, hUn, hUopen, hUsub, e', hq', ?_, ?_, ?_, ?_, u', ?_, ?_⟩
  · intro y hy
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    exact hy.1
  · simp only [e', OpenPartialHomeomorph.restrOpen_source]
    ext y
    simp [A]
  · intro y hy
    rfl
  · intro y hy
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    exact hy.2.2
  · intro y
    exact hu (chartMap y)
  · intro y
    have hyU : e y ∈ U := by
      exact y.property.2.2
    have hfac := hfactor (chartMap y)
    have hleft : e.symm (chartMap y) = (y : M) := by
      change e.symm (e (y : M)) = (y : M)
      exact e.left_inv y.property.1
    rw [hleft] at hfac
    change f (y : M) = (e' y).2 0 * u (chartMap y) at hfac
    exact hfac

end Complex
