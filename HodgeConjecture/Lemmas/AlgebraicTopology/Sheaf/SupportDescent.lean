/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Descent with closed support

Compatible local sections over a closed support descend with zero on its complement.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X)

/-- Compatible sections that vanish off a closed support have a unique global descent. -/
theorem existsUnique_section_of_isClosed_cover
    {S : Set X} (hS : IsClosed S) {ι : Type u}
    (U : ι → Opens X) (s : ∀ a, F.obj.obj (op (U a)))
    (hcover : ∀ x ∈ S, ∃ a, x ∈ U a)
    (hcompat : ∀ a b x, x ∈ S → (ha : x ∈ U a) → (hb : x ∈ U b) →
      F.presheaf.germ (U a) x ha (s a) = F.presheaf.germ (U b) x hb (s b))
    (hzero : ∀ a x, (ha : x ∈ U a) → x ∉ S → F.presheaf.germ (U a) x ha (s a) = 0) :
    ∃! t : F.obj.obj (op ⊤),
      (∀ a, F.obj.map (homOfLE (show U a ≤ ⊤ from le_top)).op t = s a) ∧
        F.obj.map (homOfLE (show (⟨Sᶜ, hS.isOpen_compl⟩ : Opens X) ≤ ⊤ from le_top)).op t = 0 := by
  let V : Option ι → Opens X
    | some a => U a
    | none => ⟨Sᶜ, hS.isOpen_compl⟩
  let r : ∀ a, F.obj.obj (op (V a))
    | some a => s a
    | none => 0
  have hV : (⊤ : Opens X) ≤ iSup V := by
    intro x _
    by_cases hx : x ∈ S
    · obtain ⟨a, hxa⟩ := hcover x hx
      exact Opens.mem_iSup.mpr ⟨some a, hxa⟩
    · exact Opens.mem_iSup.mpr ⟨none, hx⟩
  have hr : TopCat.Presheaf.IsCompatible F.presheaf V r := by
    rintro (_ | a) (_ | b)
    all_goals
      apply TopCat.Presheaf.section_ext F
      intro x hx
      simp only [F.presheaf.germ_res_apply, r, V, map_zero]
    · exact (hzero b x hx.2 hx.1).symm
    · exact hzero a x hx.1 hx.2
    · by_cases hxS : x ∈ S
      · exact hcompat a b x hxS hx.1 hx.2
      · exact (hzero a x hx.1 hxS).trans (hzero b x hx.2 hxS).symm
  obtain ⟨t, ht, hut⟩ := F.existsUnique_gluing' V ⊤ (fun _ => homOfLE le_top) hV r hr
  refine ⟨t, ⟨fun a => ht (some a), ht none⟩, fun t' ht' => hut t' ?_⟩
  rintro (_ | a)
  · exact ht'.2
  · exact ht'.1 a

end TopCat.Sheaf
