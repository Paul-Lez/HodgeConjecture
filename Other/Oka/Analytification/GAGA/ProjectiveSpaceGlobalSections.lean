/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten

Adapted from https://github.com/chrisflav/oka at commit
441d02e06e68ba6ebeddd7e0e7240c766c3c3c09 for Mathlib v4.33.1.
-/
module
public import Other.Oka.AnalyticSpace.Continuity
public import Other.Oka.Analytification.GAGA.Liouville
public import Other.Oka.Analytification.GAGA.ProjectiveSpaceAn

/-!
# Global sections of `𝒪` on `ℙⁿ_an`

**Every global section of the structure sheaf of `ℙⁿ_an` is constant**:
`ℂ → Γ(ℙⁿ_an, 𝒪)` is bijective (`ComplexAnalytic.projectiveSpaceAn.globalSectionsEquiv`).

A global section `s` is a continuous function on the compact space `ℙⁿ_an`, hence bounded; its
pullback to each chart `ℂⁿ` is therefore a bounded holomorphic function, constant by Liouville's
theorem. All charts contain the point `[1 : ⋯ : 1]`, so the constants agree, and a section whose
pullbacks to all charts vanish is zero, because the charts are open immersions covering
`ℙⁿ_an` (so its germs vanish).
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Topology

universe u

namespace ComplexAnalytic

open AnalyticSpace

namespace projectiveSpaceAn

variable {n : ℕ}

/-- The value of the pullback of a global section along a chart is its value at the image. -/
lemma eval_pullbackΓ_chart (i : Fin (n + 1)) (s : (projectiveSpaceAn.{u} n).presheaf.obj (op ⊤))
    (z : AnalyticSpace.complexAffineSpace.{u} n) :
    (AnalyticSpace.complexAffineSpace.{u} n).eval (U := ⊤) z trivial
        ((projectiveSpaceAnChart.{u} i).pullbackΓ s) =
      (projectiveSpaceAn.{u} n).eval (U := ⊤) ((projectiveSpaceAnChart.{u} i).toLRSHom.base z)
        trivial s :=
  eval_c_app (projectiveSpaceAnChart.{u} i).toLRSHom (projectiveSpaceAnChart.{u} i).isCLinear
    (U := ⊤) z trivial s

/-- **A global section of `𝒪_{ℙⁿ_an}` whose pullbacks to all charts vanish is zero.** -/
theorem eq_zero_of_pullbackΓ_chart_eq_zero (t : (projectiveSpaceAn.{u} n).presheaf.obj (op ⊤))
    (ht : ∀ i, (projectiveSpaceAnChart.{u} i).pullbackΓ t = 0) : t = 0 := by
  refine TopCat.Presheaf.section_ext (projectiveSpaceAn.{u} n).sheaf ⊤ t 0 fun x hx ↦ ?_
  obtain ⟨i, z, rfl⟩ := exists_mem_range_chart x
  set ψ := (projectiveSpaceAnChart.{u} i).toLRSHom
  apply (ConcreteCategory.bijective_of_isIso (ψ.stalkMap z)).1
  change ψ.stalkMap z ((projectiveSpaceAn.{u} n).presheaf.germ ⊤ (ψ.base z) hx t) =
    ψ.stalkMap z ((projectiveSpaceAn.{u} n).presheaf.germ ⊤ (ψ.base z) hx 0)
  rw [LocallyRingedSpace.stalkMap_germ_apply, LocallyRingedSpace.stalkMap_germ_apply, map_zero]
  exact congrArg _ (ht i)

/-- The point `[1 : ⋯ : 1]`, which lies in every chart. -/
noncomputable def basePoint (n : ℕ) : projectiveSpaceAn.{u} n :=
  pointOfVec.{u} (fun _ ↦ 1) (Function.ne_iff.2 ⟨0, one_ne_zero⟩)

lemma basePoint_mem_range_chart (i : Fin (n + 1)) :
    basePoint.{u} n ∈ Set.range (projectiveSpaceAnChart.{u} i).toLRSHom.base :=
  (mem_range_chart_pointOfVec_iff _ _ i).2 one_ne_zero

/-- **Every global section of `𝒪_{ℙⁿ_an}` is constant**, equal to its value at any point. -/
theorem eq_algebraMap_eval (s : (projectiveSpaceAn.{u} n).presheaf.obj (op ⊤))
    (x₀ : projectiveSpaceAn.{u} n) :
    s = (projectiveSpaceAn.{u} n).algebraMap
      ((projectiveSpaceAn.{u} n).eval (U := ⊤) x₀ trivial s) := by
  set f : projectiveSpaceAn.{u} n → ℂ := fun x ↦ (projectiveSpaceAn.{u} n).eval (U := ⊤) x
    trivial s
  have hbdd : Bornology.IsBounded (Set.range f) :=
    (isCompact_range ((projectiveSpaceAn.{u} n).continuous_eval_top s)).isBounded
  set d := f (basePoint.{u} n)
  -- on each chart, the pullback of `s` is the constant `d`
  have hchart : ∀ i, (projectiveSpaceAnChart.{u} i).pullbackΓ s =
      (AnalyticSpace.complexAffineSpace.{u} n).algebraMap d := by
    intro i
    obtain ⟨w, hw⟩ := basePoint_mem_range_chart.{u} (n := n) i
    have hb : Bornology.IsBounded (Set.range fun z : AnalyticSpace.complexAffineSpace.{u} n ↦
        (AnalyticSpace.complexAffineSpace.{u} n).eval (U := ⊤) z trivial
          ((projectiveSpaceAnChart.{u} i).pullbackΓ s)) := by
      refine hbdd.subset ?_
      rintro _ ⟨z, rfl⟩
      exact ⟨_, (eval_pullbackΓ_chart i s z).symm⟩
    rw [complexAffineSpace_eq_algebraMap_of_bounded _ hb w, eval_pullbackΓ_chart, hw]
  have hval : ∀ x, f x = d := by
    intro x
    obtain ⟨i, z, rfl⟩ := exists_mem_range_chart x
    have := eval_pullbackΓ_chart i s z
    rw [hchart i, eval_algebraMap] at this
    exact this.symm
  rw [show (projectiveSpaceAn.{u} n).eval (U := ⊤) x₀ trivial s = d from hval x₀, ← sub_eq_zero]
  refine eq_zero_of_pullbackΓ_chart_eq_zero _ fun i ↦ ?_
  refine (map_sub (LocallyRingedSpace.Γ.map (projectiveSpaceAnChart.{u} i).toLRSHom.op).hom
    s _).trans (sub_eq_zero.2 ((hchart i).trans ?_))
  exact ((projectiveSpaceAnChart.{u} i).isCLinear d).symm

/-- **`H⁰(ℙⁿ_an, 𝒪) = ℂ`**: the constants are all the global sections. -/
theorem bijective_algebraMap : Function.Bijective (projectiveSpaceAn.{u} n).algebraMap :=
  ⟨fun a b h ↦ by
    have := congrArg ((projectiveSpaceAn.{u} n).eval (U := ⊤) (basePoint.{u} n) trivial) h
    rwa [eval_algebraMap, eval_algebraMap] at this,
  fun s ↦ ⟨_, (eq_algebraMap_eval s (basePoint.{u} n)).symm⟩⟩

/-- **`Γ(ℙⁿ_an, 𝒪) ≅ ℂ`**, via the constants. -/
noncomputable def globalSectionsEquiv : ℂ ≃+* (projectiveSpaceAn.{u} n).presheaf.obj (op ⊤) :=
  RingEquiv.ofBijective _ bijective_algebraMap

@[simp]
lemma globalSectionsEquiv_apply (c : ℂ) :
    globalSectionsEquiv.{u} (n := n) c = (projectiveSpaceAn.{u} n).algebraMap c :=
  rfl

end projectiveSpaceAn

end ComplexAnalytic

end
