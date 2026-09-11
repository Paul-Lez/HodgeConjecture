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

public import Other.AlgebraicGeometry.ChowCycleClassDescent

/-!
# Principal divisors and functorial cycle classes

This file separates the two geometric ingredients in the proof that a cycle class respects
rational equivalence.  If `D` is a principal divisor on a closed integral carrier, they are:

* the class on the ambient space commutes with proper pushforward from `D.carrier`; and
* the divisor of `D.rationalFunction` has zero class on the carrier.

The first part is a Gysin/proper-pushforward theorem and the second is the codimension-one
principal-divisor theorem (equivalently, the first Chern class of a principal Cartier divisor is
zero).  Once these two statements have been constructed, all remaining descent is formal.  In
particular, none of the definitions below stores either an ambient principal-divisor vanishing
statement or a map out of a Chow group.

We also bundle `D.divisor` canonically as a codimension-one cycle.  Its purity is not an extra
hypothesis: `Scheme.ord` is definitionally zero away from points of coheight one.
-/

@[expose] public noncomputable section

open CategoryTheory Order

namespace AlgebraicGeometry

universe u

namespace PrincipalDivisor

variable {X : Scheme.{u}} {p : ℕ} (D : PrincipalDivisor X p)

/-- The divisor of a nonzero rational function is canonically a codimension-one cycle on its
integral carrier.  No purity datum is needed: the order-of-vanishing function is zero at every
point whose coheight is not one. -/
def codimensionOneDivisor : codimensionCycleSubgroup D.carrier 1 :=
  let := D.isIntegral
  let := D.isNoetherian
  ⟨D.divisor, by
    intro y hy
    by_contra hcodim
    apply hy
    rw [divisor_apply, orderFunction]
    exact Scheme.ord_eq_zero_of_coheight_neq_one hcodim D.rationalFunction⟩

@[simp]
lemma codimensionOneDivisor_apply (y : D.carrier) :
    D.codimensionOneDivisor y = D.orderFunction y :=
  rfl

/-- Forgetting the codimension condition on the canonical codimension-one divisor recovers the
original algebraic divisor. -/
@[simp]
lemma codimensionCycleInclusion_codimensionOneDivisor :
    codimensionCycleInclusion D.carrier 1 D.codimensionOneDivisor = D.divisor :=
  rfl

end PrincipalDivisor

/-! ### Reduction to the carrier divisor -/

/-- Compatibility of cycle-class maps with the proper pushforward in a principal-divisor datum,
with an explicit Gysin map between the two target groups. -/
def CycleClassCommutesWithPrincipalDivisorPushforwardVia
    {X : Scheme.{u}} {p : ℕ} {N M : Type*} [AddCommGroup N] [AddCommGroup M]
    (D : PrincipalDivisor X p)
    (carrierClass : AlgebraicCycle D.carrier ℤ →+ N)
    (ambientClass : AlgebraicCycle X ℤ →+ M)
    (gysin : N →+ M) : Prop :=
  let := D.isClosedImmersion
  ∀ c, ambientClass
      (AlgebraicCycle.map D.inclusion (fun _ : D.carrier ↦ ()) (fun _ : X ↦ ()) c) =
    gysin (carrierClass c)

/-- Compatibility of two additive cycle-class maps with the proper pushforward occurring in a
fixed principal-divisor datum.

The source map may already include the Gysin map into the ambient target.  Stating compatibility
for every source cycle, rather than only for `D.divisor`, makes this exactly the reusable
proper-pushforward naturality theorem needed elsewhere. -/
def CycleClassCommutesWithPrincipalDivisorPushforward
    {X : Scheme.{u}} {p : ℕ} {M : Type*} [AddCommGroup M]
    (D : PrincipalDivisor X p)
    (carrierClass : AlgebraicCycle D.carrier ℤ →+ M)
    (ambientClass : AlgebraicCycle X ℤ →+ M) : Prop :=
  let := D.isClosedImmersion
  ∀ c, ambientClass
      (AlgebraicCycle.map D.inclusion (fun _ : D.carrier ↦ ()) (fun _ : X ↦ ()) c) =
    carrierClass c

/-- Proper-pushforward compatibility through a Gysin map identifies the ambient class of a
principal divisor with the Gysin image of its intrinsic carrier-divisor class. -/
lemma principalDivisor_class_eq_gysin_carrier_divisor_class
    {X : Scheme.{u}} {p : ℕ} {N M : Type*} [AddCommGroup N] [AddCommGroup M]
    (D : PrincipalDivisor X p)
    (carrierClass : AlgebraicCycle D.carrier ℤ →+ N)
    (ambientClass : AlgebraicCycle X ℤ →+ M)
    (gysin : N →+ M)
    (hpush : CycleClassCommutesWithPrincipalDivisorPushforwardVia
      D carrierClass ambientClass gysin) :
    ambientClass D.pushforwardCycle = gysin (carrierClass D.divisor) :=
  hpush D.divisor

/-- The ambient principal-divisor class vanishes if the intrinsic divisor class vanishes and
cycle classes commute with the carrier's Gysin map. -/
lemma principalDivisor_class_eq_zero_of_gysin_carrier_divisor_class_eq_zero
    {X : Scheme.{u}} {p : ℕ} {N M : Type*} [AddCommGroup N] [AddCommGroup M]
    (D : PrincipalDivisor X p)
    (carrierClass : AlgebraicCycle D.carrier ℤ →+ N)
    (ambientClass : AlgebraicCycle X ℤ →+ M)
    (gysin : N →+ M)
    (hpush : CycleClassCommutesWithPrincipalDivisorPushforwardVia
      D carrierClass ambientClass gysin)
    (hdivisor : carrierClass D.divisor = 0) :
    ambientClass D.pushforwardCycle = 0 := by
  rw [principalDivisor_class_eq_gysin_carrier_divisor_class
    D carrierClass ambientClass gysin hpush, hdivisor, map_zero]

/-- Proper-pushforward compatibility identifies the ambient class of a principal divisor with
the class of its divisor on the carrier. -/
lemma principalDivisor_class_eq_carrier_divisor_class
    {X : Scheme.{u}} {p : ℕ} {M : Type*} [AddCommGroup M]
    (D : PrincipalDivisor X p)
    (carrierClass : AlgebraicCycle D.carrier ℤ →+ M)
    (ambientClass : AlgebraicCycle X ℤ →+ M)
    (hpush : CycleClassCommutesWithPrincipalDivisorPushforward
      D carrierClass ambientClass) :
    ambientClass D.pushforwardCycle = carrierClass D.divisor :=
  hpush D.divisor

/-- The ambient class of a principal divisor vanishes once proper-pushforward compatibility and
the intrinsic codimension-one principal-divisor theorem on its carrier are known. -/
lemma principalDivisor_class_eq_zero_of_carrier_divisor_class_eq_zero
    {X : Scheme.{u}} {p : ℕ} {M : Type*} [AddCommGroup M]
    (D : PrincipalDivisor X p)
    (carrierClass : AlgebraicCycle D.carrier ℤ →+ M)
    (ambientClass : AlgebraicCycle X ℤ →+ M)
    (hpush : CycleClassCommutesWithPrincipalDivisorPushforward
      D carrierClass ambientClass)
    (hdivisor : carrierClass D.divisor = 0) :
    ambientClass D.pushforwardCycle = 0 := by
  rw [principalDivisor_class_eq_carrier_divisor_class
    D carrierClass ambientClass hpush, hdivisor]

/-- Carrierwise Gysin compatibility and codimension-one divisor vanishing imply that an additive
cycle-class map kills the full subgroup generated by principal divisors.

This is the useful interface for a geometric cycle-class theory: `carrierClass D` is the
codimension-one class on `D.carrier`, already followed by proper pushforward to the fixed ambient
target.  The conclusion, including closure under sums and negatives, is constructed rather than
stored as data. -/
lemma principalDivisorSubgroup_le_ker_of_carrier_divisor_classes
    {X : Scheme.{u}} {p : ℕ} {M : Type*} [AddCommGroup M]
    (ambientClass : AlgebraicCycle X ℤ →+ M)
    (carrierClass : ∀ D : PrincipalDivisor X p,
      AlgebraicCycle D.carrier ℤ →+ M)
    (hpush : ∀ D, CycleClassCommutesWithPrincipalDivisorPushforward
      D (carrierClass D) ambientClass)
    (hdivisor : ∀ D, carrierClass D D.divisor = 0) :
    principalDivisorSubgroup X p ≤ ambientClass.ker := by
  rw [principalDivisorSubgroup_le_ker_iff]
  intro D
  exact principalDivisor_class_eq_zero_of_carrier_divisor_class_eq_zero
    D (carrierClass D) ambientClass (hpush D) (hdivisor D)

/-- A componentwise cycle-class map kills rational equivalences after its carrierwise Gysin
compatibility and the intrinsic codimension-one principal-divisor theorem have been proved. -/
lemma rationalEquivalenceSubgroup_le_cycleClassOnCyclesOfComponents_ker_of_carrier
    {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (componentClass : ∀ (x : X), coheight x = p → M)
    (carrierClass : ∀ D : PrincipalDivisor X p,
      AlgebraicCycle D.carrier ℤ →+ M)
    (hpush : ∀ D, CycleClassCommutesWithPrincipalDivisorPushforward D
      (carrierClass D)
      (cycleClassOnAlgebraicCyclesOfComponents componentClass))
    (hdivisor : ∀ D, carrierClass D D.divisor = 0) :
    rationalEquivalenceSubgroup X p ≤
      (cycleClassOnCyclesOfComponents componentClass).ker :=
  fun _ hc ↦ principalDivisorSubgroup_le_ker_of_carrier_divisor_classes
    (cycleClassOnAlgebraicCyclesOfComponents componentClass)
    carrierClass hpush hdivisor hc

namespace ChowGroup

/-- Construct the integral Chow-group cycle-class map from carrierwise proper-pushforward
compatibility and codimension-one principal-divisor vanishing.  The map and the ambient
principal-divisor theorem are both derived. -/
def cycleClassOfComponentsOfCarrierDivisors
    {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (componentClass : ∀ (x : X), coheight x = p → M)
    (carrierClass : ∀ D : PrincipalDivisor X p,
      AlgebraicCycle D.carrier ℤ →+ M)
    (hpush : ∀ D, CycleClassCommutesWithPrincipalDivisorPushforward D
      (carrierClass D)
      (cycleClassOnAlgebraicCyclesOfComponents componentClass))
    (hdivisor : ∀ D, carrierClass D D.divisor = 0) :
    ChowGroup X p →+ M :=
  liftCycleClass (cycleClassOnCyclesOfComponents componentClass)
    (rationalEquivalenceSubgroup_le_cycleClassOnCyclesOfComponents_ker_of_carrier
      componentClass carrierClass hpush hdivisor)

@[simp]
lemma cycleClassOfComponentsOfCarrierDivisors_mk
    {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M]
    (componentClass : ∀ (x : X), coheight x = p → M)
    (carrierClass : ∀ D : PrincipalDivisor X p,
      AlgebraicCycle D.carrier ℤ →+ M)
    (hpush : ∀ D, CycleClassCommutesWithPrincipalDivisorPushforward D
      (carrierClass D)
      (cycleClassOnAlgebraicCyclesOfComponents componentClass))
    (hdivisor : ∀ D, carrierClass D D.divisor = 0)
    (z : codimensionCycleSubgroup X p) :
    cycleClassOfComponentsOfCarrierDivisors componentClass carrierClass hpush hdivisor (mk z) =
      cycleClassOnCyclesOfComponents componentClass z :=
  liftCycleClass_mk _ _ _

/-- Construct the rational Chow-group cycle-class map from carrierwise geometric theorems. -/
def rationalCycleClassOfComponentsOfCarrierDivisors
    {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M] [Module ℚ M]
    (componentClass : ∀ (x : X), coheight x = p → M)
    (carrierClass : ∀ D : PrincipalDivisor X p,
      AlgebraicCycle D.carrier ℤ →+ M)
    (hpush : ∀ D, CycleClassCommutesWithPrincipalDivisorPushforward D
      (carrierClass D)
      (cycleClassOnAlgebraicCyclesOfComponents componentClass))
    (hdivisor : ∀ D, carrierClass D D.divisor = 0) :
    RationalChowGroup X p →ₗ[ℚ] M :=
  rationalExtension <|
    cycleClassOfComponentsOfCarrierDivisors componentClass carrierClass hpush hdivisor

@[simp]
lemma rationalCycleClassOfComponentsOfCarrierDivisors_component
    {X : Scheme.{u}} [CompactSpace X] {p : ℕ}
    {M : Type*} [AddCommGroup M] [Module ℚ M]
    (componentClass : ∀ (x : X), coheight x = p → M)
    (carrierClass : ∀ D : PrincipalDivisor X p,
      AlgebraicCycle D.carrier ℤ →+ M)
    (hpush : ∀ D, CycleClassCommutesWithPrincipalDivisorPushforward D
      (carrierClass D)
      (cycleClassOnAlgebraicCyclesOfComponents componentClass))
    (hdivisor : ∀ D, carrierClass D D.divisor = 0)
    (x : X) (hx : coheight x = p) :
    rationalCycleClassOfComponentsOfCarrierDivisors
        componentClass carrierClass hpush hdivisor
        (toRational (mk (codimensionCycleSubgroup.single x hx 1))) =
      componentClass x hx := by
  rw [rationalCycleClassOfComponentsOfCarrierDivisors, toRational_apply,
    rationalExtension_tmul, one_smul,
    cycleClassOfComponentsOfCarrierDivisors_mk,
    cycleClassOnCyclesOfComponents_single]
  simp

end ChowGroup

end AlgebraicGeometry
