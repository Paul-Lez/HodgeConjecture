/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.HolomorphicSheafGenerators

/-!
# Multipliers of a morphism transform by the frame changes

If `M` and `M'` are trivialised on two opens `U` and `V` by generating sections, a morphism
`φ : M ⟶ M'` is multiplication by a holomorphic function on each of them, and on the overlap the
two multipliers differ by the ratio of the two frame changes.  This is the cocycle relation that
turns a morphism of analytic twists into a single homogeneous function on the coordinate cone.
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace Opposite

namespace AlgebraicGeometry.ComplexPoint

variable {X : Over (Spec ↧ℂ)} {d : ℕ} [SmoothOfRelativeDimension d X.hom]

local instance holomorphicMultiplierTransitionTopology : TopologicalSpace (ComplexPoint X) :=
  Point.analyticTopology

variable {M M' : SheafOfModules (holomorphicRingSheaf X d)}

/-- The holomorphic structure sheaf has commutative section rings. -/
theorem holomorphic_mul_comm {U : Opens (TopCat.of (ComplexPoint X))}
    (x y : (holomorphicRingSheaf X d).obj.obj (op U)) : x * y = y * x :=
  mul_comm (G := (holomorphicFunctionSheaf X d).obj.obj (op U)) x y

/-- Restriction of a section of the holomorphic structure sheaf. -/
abbrev holRingRes {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U)
    (r : (holomorphicRingSheaf X d).obj.obj (op U)) :
    (holomorphicRingSheaf X d).obj.obj (op V) :=
  (holomorphicRingSheaf X d).obj.map (homOfLE h).op r

/-- A morphism of sheaves of modules commutes with restriction of sections. -/
theorem holRes_app (φ : M ⟶ M') {U V : Opens (TopCat.of (ComplexPoint X))} (h : V ≤ U)
    (s : M.val.obj (op U)) :
    holRes M' h (φ.val.app (op U) s) = φ.val.app (op V) (holRes M h s) :=
  (PresheafOfModules.naturality_apply φ.val (homOfLE h).op s).symm

/-- **The multiplier transition law.**  If `sU`, `sV` are sections of `M` over `U`, `V` whose
restrictions to `W` differ by `u`, if `tU`, `tV` are sections of `M'` over `U`, `V` whose
restrictions differ by `v`, if `φ` multiplies `sU` into `hU • tU` and `sV` into `hV • tV`, and if
`tV` generates on `W`, then `hU · v = u · hV` on `W`. -/
theorem multiplier_transition (φ : M ⟶ M')
    {U V W : Opens (TopCat.of (ComplexPoint X))} (hWU : W ≤ U) (hWV : W ≤ V)
    {sU : M.val.obj (op U)} {sV : M.val.obj (op V)}
    {tU : M'.val.obj (op U)} {tV : M'.val.obj (op V)}
    (htV : HolomorphicGenerates tV)
    {u v : (holomorphicRingSheaf X d).obj.obj (op W)}
    (hu : u • holRes M hWV sV = holRes M hWU sU)
    (hv : v • holRes M' hWV tV = holRes M' hWU tU)
    {hU : (holomorphicRingSheaf X d).obj.obj (op U)}
    {hV : (holomorphicRingSheaf X d).obj.obj (op V)}
    (hsU : φ.val.app (op U) sU = hU • tU)
    (hsV : φ.val.app (op V) sV = hV • tV) :
    holRingRes hWU hU * v = u * holRingRes hWV hV := by
  have key : (holRingRes hWU hU * v) • holRes M' hWV tV = (u * holRingRes hWV hV) • holRes M' hWV tV := by
    calc (holRingRes hWU hU * v) • holRes M' hWV tV
        = holRingRes hWU hU • (v • holRes M' hWV tV) := by rw [mul_smul]
      _ = holRingRes hWU hU • holRes M' hWU tU := by rw [hv]
      _ = holRes M' hWU (hU • tU) := by rw [holRes_smul]
      _ = holRes M' hWU (φ.val.app (op U) sU) := by rw [hsU]
      _ = φ.val.app (op W) (holRes M hWU sU) := holRes_app φ hWU sU
      _ = φ.val.app (op W) (u • holRes M hWV sV) := by rw [hu]
      _ = u • φ.val.app (op W) (holRes M hWV sV) := (φ.val.app (op W)).hom.map_smul u _
      _ = u • holRes M' hWV (φ.val.app (op V) sV) := by rw [holRes_app φ hWV sV]
      _ = u • holRes M' hWV (hV • tV) := by rw [hsV]
      _ = u • (holRingRes hWV hV • holRes M' hWV tV) := by rw [holRes_smul]
      _ = (u * holRingRes hWV hV) • holRes M' hWV tV := by rw [mul_smul]
  have hgen := htV.restrict hWV
  have hinj := hgen.smul_left_injective (le_rfl : W ≤ W)
  apply hinj
  simpa only [holRes_rfl] using key

/-- When the two frames of `M` and of `M'` have the *same* frame change on the overlap, the
multipliers agree there. -/
theorem multiplier_eq_of_same_transition (φ : M ⟶ M')
    {U V W : Opens (TopCat.of (ComplexPoint X))} (hWU : W ≤ U) (hWV : W ≤ V)
    {sU : M.val.obj (op U)} {sV : M.val.obj (op V)}
    {tU : M'.val.obj (op U)} {tV : M'.val.obj (op V)}
    (htV : HolomorphicGenerates tV)
    {u : (holomorphicRingSheaf X d).obj.obj (op W)} (huunit : IsUnit u)
    (hu : u • holRes M hWV sV = holRes M hWU sU)
    (hv : u • holRes M' hWV tV = holRes M' hWU tU)
    {hU : (holomorphicRingSheaf X d).obj.obj (op U)}
    {hV : (holomorphicRingSheaf X d).obj.obj (op V)}
    (hsU : φ.val.app (op U) sU = hU • tU)
    (hsV : φ.val.app (op V) sV = hV • tV) :
    holRingRes hWU hU = holRingRes hWV hV := by
  have h := multiplier_transition φ hWU hWV htV hu hv hsU hsV
  rw [holomorphic_mul_comm (holRingRes hWU hU) u] at h
  exact huunit.mul_left_cancel h

end AlgebraicGeometry.ComplexPoint
