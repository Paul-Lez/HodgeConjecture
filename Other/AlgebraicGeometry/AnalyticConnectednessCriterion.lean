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

public import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexAnalyticSheaf
public import Other.AlgebraicGeometry.ProjectiveAnalytificationConnected
public import Mathlib.Topology.Connected.Clopen

@[expose] public noncomputable section

open CategoryTheory Topology
open scoped ContDiff Manifold

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- The characteristic function of a clopen subset is holomorphic, without a connectedness
assumption. -/
theorem contMDiff_clopenIndicator [SmoothOfRelativeDimension d X.hom]
    (s : Set (ComplexPoint X)) (hs : IsClopen s) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (s.indicator fun _ => (1 : ℂ)) := by
  classical
  intro x
  by_cases hx : x ∈ s
  · apply contMDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hs.isOpen.mem_nhds hx] with y hy
    exact Set.indicator_of_mem hy _
  · apply contMDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hs.compl.isOpen.mem_nhds hx] with y hy
    exact Set.indicator_of_notMem hy _

/-- A clopen characteristic function as a global section of the actual holomorphic sheaf. -/
def clopenIndicatorSection [SmoothOfRelativeDimension d X.hom]
    (s : Set (ComplexPoint X)) (hs : IsClopen s) :
    (holomorphicFunctionSheaf X d).presheaf.obj (Opposite.op ⊤) := by
  change C^ω⟮𝓘(ℂ, Fin d → ℂ), (⊤ : TopologicalSpace.Opens (ComplexPoint X)); ℂ⟯
  exact ⟨fun x => s.indicator (fun _ => (1 : ℂ)) x.1,
    (contMDiff_clopenIndicator X d s hs).comp contMDiff_subtype_val⟩

lemma clopenIndicatorSection_idempotent [SmoothOfRelativeDimension d X.hom]
    (s : Set (ComplexPoint X)) (hs : IsClopen s) :
    clopenIndicatorSection X d s hs * clopenIndicatorSection X d s hs =
      clopenIndicatorSection X d s hs := by
  classical
  apply ContMDiffMap.ext
  intro x
  change (s.indicator (fun _ => (1 : ℂ)) x.1) *
    (s.indicator (fun _ => (1 : ℂ)) x.1) = s.indicator (fun _ => (1 : ℂ)) x.1
  by_cases hx : x.1 ∈ s <;> simp [hx]

/-- Constancy of holomorphic idempotents implies connectedness. This criterion keeps the global
algebraization input separate from the local holomorphicity of characteristic functions. -/
theorem connectedSpace_of_holomorphicIdempotents_constant
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension d X.hom]
    (h : ∀ f : ComplexPoint X → ℂ,
      ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω f →
      (∀ x, f x * f x = f x) → ∀ x y, f x = f y) :
    ConnectedSpace (ComplexPoint X) := by
  classical
  refine connectedSpace_iff_clopen.mpr ⟨inferInstance, fun s hs => ?_⟩
  by_cases he : s = ∅
  · exact Or.inl he
  right
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr he
  apply Set.eq_univ_of_forall
  intro y
  have hi : ∀ z, (s.indicator fun _ => (1 : ℂ)) z *
      (s.indicator fun _ => (1 : ℂ)) z = (s.indicator fun _ => (1 : ℂ)) z := by
    intro z
    by_cases hz : z ∈ s <;> simp [hz]
  have hy := h _ (contMDiff_clopenIndicator X d s hs) hi x y
  by_contra hn
  simp [hx, hn] at hy

/-- Triviality of idempotents in the ring of global holomorphic functions implies analytic
connectedness. An algebraization theorem can discharge this ring-theoretic premise. -/
theorem connectedSpace_of_holomorphicSection_idempotents
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension d X.hom]
    (h : ∀ f : (holomorphicFunctionSheaf X d).presheaf.obj (Opposite.op ⊤),
      f * f = f → f = 0 ∨ f = 1) : ConnectedSpace (ComplexPoint X) := by
  classical
  refine connectedSpace_iff_clopen.mpr ⟨inferInstance, fun s hs => ?_⟩
  rcases h _ (clopenIndicatorSection_idempotent X d s hs) with hz | ho
  · left
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have he := congrArg (fun f : (holomorphicFunctionSheaf X d).presheaf.obj
      (Opposite.op ⊤) => f.1 ⟨x, trivial⟩) hz
    change s.indicator (fun _ => (1 : ℂ)) x = 0 at he
    simp [hx] at he
  · right
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    have he := congrArg (fun f : (holomorphicFunctionSheaf X d).presheaf.obj
      (Opposite.op ⊤) => f.1 ⟨x, trivial⟩) ho
    change s.indicator (fun _ => (1 : ℂ)) x = 1 at he
    simp [hx] at he

end AlgebraicGeometry.ComplexPoint
