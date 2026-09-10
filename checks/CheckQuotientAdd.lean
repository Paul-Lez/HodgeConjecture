import Mathlib.GroupTheory.QuotientGroup.Basic

#check QuotientAddGroup.mk'
#check QuotientAddGroup.eq_zero_iff
#check QuotientAddGroup.quotientKerEquivRange
#check QuotientAddGroup.Quotient
#check QuotientAddGroup.quotient

example {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (x : G) :
    QuotientAddGroup.mk' H x = 0 ↔ x ∈ H := by
  exact QuotientAddGroup.eq_zero_iff x

example {G K : Type*} [AddCommGroup G] [AddCommGroup K] (f : G →+ K) (x : K) :
    QuotientAddGroup.mk' f.range x = 0 ↔ ∃ y, f y = x := by
  change QuotientAddGroup.mk x = 0 ↔ ∃ y, f y = x
  rw [QuotientAddGroup.eq_zero_iff]
  rfl
