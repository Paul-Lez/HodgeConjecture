/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.CartierLocalForm
public import Other.AlgebraicGeometry.ChernLocalModelWinding

/-!
# Where an algebraic local form can live

This file records an **obstruction**, and it is a negative result: the affine open `V₀` of a
`Scheme.CartierData.LocalForm` at a codimension-one point `x` can never meet another component of
the divisor.

Indeed, on `V₀` the Cartier local equation factors as `u · h ^ n` with `u` a *unit* on `V₀` and
`h` invertible outside `Z_x = closure {x}`; so at a codimension-one point `y ∈ V₀` off `Z_x` both
factors have order of vanishing zero, whence `c.divisor y = 0`
(`Scheme.CartierData.LocalForm.divisor_eq_zero_of_notMem_closure`).

The consequence for §4.3 step 4 item 3 of `docs/DIVISOR_HANDOFF.md` is stated as
`AlgebraicGeometry.ComplexPoint.exists_chernWindingChart_imp_divisor_eq_zero`: a
`ChernWindingChart X c x d p q` forces `c.divisor y = 0` for *every* codimension-one `y ≠ x`
whose closure contains the underlying point of `q`.  In other words a winding chart at `q` exists
only when `q` lies on no component of `|D|` other than `Z_x`.

Since `HasNormalizedWindingCharts` quantifies over **all** `q` in
`cycleComponentSmoothSupportAmbientOpen X x ∩ cycleComponentSupport X x` — a set that does meet
the other components of `D`, for instance at the node of a pair of lines in `ℙ²`, where the
smooth locus of each line contains the intersection point — that proposition is **false** as
stated whenever `D` has two components meeting on the smooth locus of one of them.  The fix
belongs in `ChernLocalModelWinding.lean` and is not made here; see the report accompanying this
file.  Mathematically the fix is harmless: the locus where two components of `D` meet is closed
of codimension at least two, and the repository already has the corresponding supported vanishing
(`hasCodimensionTwoSupportedVanishing`, `ClosedSupportCoheightDimension.lean`), so the charts only
need to cover the complement of that locus.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

namespace Scheme.CartierData.LocalForm

variable {S : Scheme.{u}} [IsIntegral S] [IsNoetherian S] {c : S.CartierData} {i : c.ι} {x : S}

/-- The local equation of a local form is a nonzero rational function. -/
theorem equation_functionField_ne_zero (f : c.LocalForm i x) :
    S.germToFunctionField (h := ⟨⟨x, f.mem⟩⟩) f.opens f.equation ≠ 0 := by
  intro h0
  have := f.ord_equation
  rw [h0] at this
  simp at this

/-- The comparison unit of a local form is a nonzero rational function. -/
theorem unit_functionField_ne_zero (f : c.LocalForm i x) :
    S.germToFunctionField (h := ⟨⟨x, f.mem⟩⟩) f.opens (f.unit : Γ(S, f.opens)) ≠ 0 := by
  have hne : Nonempty f.opens := ⟨⟨x, f.mem⟩⟩
  have : IsDomain Γ(S, f.opens) := @IsIntegral.component_integral S _ f.opens hne
  intro h0
  refine f.unit.ne_zero (S.germToFunctionField_injective f.opens ?_)
  rw [h0, map_zero]

/-- Off `Z_x`, the local equation of a local form has order of vanishing zero. -/
theorem ord_equation_eq_zero_of_notMem_closure (f : c.LocalForm i x) {y : S} (hy : y ∈ f.opens)
    (hyx : y ∉ closure ({x} : Set S)) :
    S.ord (S.germToFunctionField (h := ⟨⟨x, f.mem⟩⟩) f.opens f.equation) y = 0 := by
  have : Nonempty f.opens := ⟨⟨x, f.mem⟩⟩
  have hyb : y ∈ S.basicOpen f.equation := by
    by_contra hc
    exact hyx (f.mem_closure_of_notMem_basicOpen y hy hc)
  have : Nonempty ((S.basicOpen f.equation : S.Opens)) := ⟨⟨y, hyb⟩⟩
  have hunit : IsUnit (S.presheaf.map
      (homOfLE (S.basicOpen_le f.equation) : S.basicOpen f.equation ⟶ f.opens).op f.equation) :=
    S.toRingedSpace.isUnit_res_basicOpen f.equation
  have hres : S.germToFunctionField (h := ⟨⟨y, hyb⟩⟩) (S.basicOpen f.equation)
      (S.presheaf.map (homOfLE (S.basicOpen_le f.equation)).op f.equation) =
      S.germToFunctionField (h := ⟨⟨x, f.mem⟩⟩) f.opens f.equation := by
    rw [germToFunctionField_eq_algebraMap_germ hyb, germToFunctionField_eq_algebraMap_germ f.mem,
      S.presheaf.germ_res_apply (homOfLE (S.basicOpen_le f.equation)) y hyb f.equation]
    exact algebraMap_germ_eq_of_mem hy f.mem f.equation
  rw [← hres]
  exact Scheme.ord_of_isUnit hunit hyb

/-- **The obstruction.**  At a point of the affine open of a local form that lies off `Z_x`, the
divisor of the Cartier datum vanishes: the local form sees only the component of `x`. -/
theorem divisor_eq_zero_of_notMem_closure (f : c.LocalForm i x) {y : S} (hy : y ∈ f.opens)
    (hyx : y ∉ closure ({x} : Set S)) : c.divisor y = 0 := by
  have : Nonempty f.opens := ⟨⟨x, f.mem⟩⟩
  have hU := f.unit_functionField_ne_zero
  have hH := f.equation_functionField_ne_zero
  have hHn : (S.germToFunctionField (h := ⟨⟨x, f.mem⟩⟩) f.opens f.equation) ^ (c.divisor x)
      ≠ 0 := zpow_ne_zero _ hH
  rw [c.divisor_apply_of_mem i y (f.le hy), f.fn_eq, Scheme.ord_mul hU hHn,
    Scheme.ord_of_isUnit f.unit.isUnit hy]
  have hzpow : S.ord ((S.germToFunctionField (h := ⟨⟨x, f.mem⟩⟩) f.opens f.equation) ^
      (c.divisor x)) y = 0 := by
    by_cases hy1 : coheight y = 1
    · rw [Scheme.ord_eq_iff hy1 hHn, map_zpow₀,
        (Scheme.ord_eq_iff hy1 hH).1 (f.ord_equation_eq_zero_of_notMem_closure hy hyx)]
      simp
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hy1 _
  rw [hzpow, add_zero]

/-- A codimension-one point on which the divisor does not vanish, other than `x` itself, does not
lie in the affine open of any local form at `x`. -/
theorem notMem_of_divisor_ne_zero (f : c.LocalForm i x) (hx : coheight x = 1) {y : S}
    (hy1 : coheight y = 1) (hyx : y ≠ x) (hyd : c.divisor y ≠ 0) : y ∉ f.opens := by
  intro hy
  refine hyd (f.divisor_eq_zero_of_notMem_closure hy ?_)
  intro hycl
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hycl
  have hlt : y < x := ⟨hxy, fun hyx0 => hyx (hyx0.antisymm hxy).eq⟩
  have hcolt := Order.coheight_strictAnti hlt (by simp [hx])
  rw [hy1, hx] at hcolt
  exact absurd hcolt (by simp)

end Scheme.CartierData.LocalForm

namespace ComplexPoint

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

local instance chernWindingLocalFormObstructionTopology :
    TopologicalSpace (ComplexPoint X) := Point.analyticTopology

attribute [local instance] isNoetherian_of_isProjective

variable {X}

/-- **The consequence for winding charts.**  If a winding chart exists at a complex point `q`,
then every codimension-one point `y ≠ x` whose closure contains the underlying point of `q`
carries no divisor: `q` lies on no component of `|D|` other than `Z_x`.

In particular `HasNormalizedWindingCharts` cannot hold when two components of the divisor meet
at a point of the smooth locus of one of them — for instance at the node of a pair of lines in
`ℙ²` — since that point lies in `cycleComponentSmoothSupportAmbientOpen X x` and in
`cycleComponentSupport X x`, over which the proposition quantifies. -/
theorem exists_chernWindingChart_imp_divisor_eq_zero
    {c : Scheme.CartierData X.left} {x : X.left} {d p : ℕ}
    [SmoothOfRelativeDimension d X.hom] {q : ComplexPoint X}
    (ch : ChernWindingChart X c x d p q) (hx : coheight x = 1)
    {y : X.left} (hy1 : coheight y = 1) (hyx : y ≠ x)
    (hq : Point.underlying q ∈ closure ({y} : Set X.left)) :
    c.divisor y = 0 := by
  by_contra hyd
  have hqmem : Point.underlying q ∈ ch.localForm.opens := ch.le_analytic ch.mem
  obtain ⟨z, hz, hz'⟩ := mem_closure_iff.mp hq _ ch.localForm.opens.isOpen hqmem
  exact ch.localForm.notMem_of_divisor_ne_zero hx hy1 hyx hyd
    (by rwa [Set.mem_singleton_iff.mp hz'] at hz)

end ComplexPoint

end AlgebraicGeometry
