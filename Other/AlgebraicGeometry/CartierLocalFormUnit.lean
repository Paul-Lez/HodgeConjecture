/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Other.AlgebraicGeometry.ComplementFrame

/-!
# Cartier unit data from the codimension-one local form

A local form `f = u * h^m` gives unit data on the basic open of the prime equation `h`.
The constructed unit retains the integer multiplicity `m`, including negative values.
Its image in the function field is the original Cartier function.
-/
@[expose] public noncomputable section
open CategoryTheory TopologicalSpace Opposite Order
namespace AlgebraicGeometry.Scheme.CartierData.LocalForm
universe u
variable {S : Scheme.{u}} [IsIntegral S] [IsNoetherian S]
  {c : S.CartierData} {i : c.ι} {x : S} (F : c.LocalForm i x)

/-- The prime equation becomes a unit on its basic open. -/
def equationUnit : Γ(S, S.basicOpen F.equation)ˣ :=
  (S.toRingedSpace.isUnit_res_basicOpen F.equation).unit

lemma equationUnit_val : (F.equationUnit : Γ(S, S.basicOpen F.equation)) =
    S.presheaf.map (homOfLE (S.basicOpen_le F.equation)).op F.equation :=
  (S.toRingedSpace.isUnit_res_basicOpen F.equation).unit_spec

/-- The actual Cartier function on the complement of the prime equation's zero locus. -/
def cartierUnit : Γ(S, S.basicOpen F.equation)ˣ :=
  Units.map (S.presheaf.map (homOfLE (S.basicOpen_le F.equation)).op).hom F.unit *
    F.equationUnit ^ (c.divisor x)

lemma germ_cartierUnit [Nonempty (S.basicOpen F.equation)] :
    S.germToFunctionField (S.basicOpen F.equation) (F.cartierUnit : Γ(S, S.basicOpen F.equation)) =
      c.fn i := by
  let : Nonempty F.opens := ⟨⟨x, F.mem⟩⟩
  have hz : S.germToFunctionField (S.basicOpen F.equation)
      ((F.equationUnit ^ (c.divisor x) : Γ(S, S.basicOpen F.equation)ˣ) :
        Γ(S, S.basicOpen F.equation)) =
      (S.germToFunctionField F.opens F.equation) ^ (c.divisor x) := by
    have h := congrArg (fun a : S.functionFieldˣ => (a : S.functionField))
      ((Units.map (S.germToFunctionField (S.basicOpen F.equation)).hom.toMonoidHom).map_zpow
        F.equationUnit (c.divisor x))
    simp only [Units.coe_map, Units.val_zpow_eq_zpow_val, F.equationUnit_val] at h
    change S.germToFunctionField (S.basicOpen F.equation) _ =
      (S.germToFunctionField (S.basicOpen F.equation)
        (S.presheaf.map (homOfLE (S.basicOpen_le F.equation)).op F.equation)) ^ (c.divisor x) at h
    rw [Scheme.germToFunctionField_res] at h
    exact h
  rw [cartierUnit, Units.val_mul, map_mul, hz, Units.coe_map]
  erw [Scheme.germToFunctionField_res, F.fn_eq]

/-- A local form supplies unit data at every point off its prime divisor. -/
def toUnitDatum (p : S) (hp : p ∈ S.basicOpen F.equation) : c.UnitDatum p where
  i := i
  opens := S.basicOpen F.equation
  mem := hp
  le := (S.basicOpen_le F.equation).trans F.le
  unit := F.cartierUnit
  isUnit := F.cartierUnit.isUnit
  fn_eq := by
    let : Nonempty (S.basicOpen F.equation) := ⟨⟨p, hp⟩⟩
    exact F.germ_cartierUnit

end AlgebraicGeometry.Scheme.CartierData.LocalForm
