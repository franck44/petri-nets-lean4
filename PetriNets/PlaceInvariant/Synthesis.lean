/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.PlaceInvariant.Algebra
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Synthesis of place invariants

Provides an integer-linear map whose kernel consists exactly of the place
invariant coefficient functions of a weighted P/T net, together with a linear
equivalence between that kernel and `PlaceInvariant net`.

A place coefficient function `y : P → ℤ` defines a place invariant exactly
when its product with the incidence matrix is zero. Expressing this condition
as a kernel provides the algebraic foundation for synthesising place
invariants.

The purpose of this map is to test arbitrary candidate coefficient functions,
not only coefficient functions already known to define place invariants. Given
a candidate `y`, it computes one integer for each transition: the weighted change
that the transition produces according to `y`. Thus, `placeInvariantMap y` is
a table of how much the quantity measured by `y` changes when each transition
fires. A nonzero value identifies a transition for which `y` is not preserved.
If every value is zero, `y` satisfies the place-invariant condition.

We call this map `placeInvariantMap`. Synthesising place invariants
then amounts to finding its zero inputs, that is, computing its kernel using
integer linear algebra.

## Example

Consider a net with three places and two transitions.

p₁ ──t₁──▶ p₂ ──t₂──▶ p₃

Transition `t₁` moves one token from `p₁` to `p₂`, while `t₂` moves one token from `p₂` to `p₃`.
Its incidence matrix is

```text
    t₁  t₂
p₁  -1   0
p₂   1  -1
p₃   0   1
```

Here `P = Fin 3` and `T = Fin 2`, so `placeInvariantMap` has type

```lean
(Fin 3 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ).
```

The input `y : Fin 3 → ℤ` assigns an integer coefficient to each of the three
places. The output assigns one integer to each transition: its weighted
incidence contribution. Concretely, the map sends a coefficient vector
`y = (a, b, c)` to

```text
y · C = (-a + b, -b + c).
```

For `y = (1, 1, 1)`, `placeInvariantMap` therefore computes

```text
y · C = (0, 0).
```

Thus `y` belongs to the kernel of `placeInvariantMap`; it represents the
invariant stating that the total number of tokens in `p₁`, `p₂`, and `p₃` is
preserved.
-/

@[expose] public section

namespace PetriNet

/-! ## The candidate coefficient map -/

/-- The integer-linear map that sends a place coefficient function `y` to its
row-vector product with the incidence matrix `C`.

The type `(P → ℤ) →ₗ[ℤ] (T → ℤ)` means that the input assigns an integer
coefficient to every place and the output assigns the resulting weighted
incidence contribution to every transition. The symbol `→ₗ[ℤ]` records that
this function preserves addition and integer scalar multiplication.

For each transition `t`, the resulting value is
`∑ p, y p * net.incidence p t`. Hence, the place invariants are precisely the
coefficient functions in the kernel of this map. -/
def WeightedNet.placeInvariantMap {P T : Type*} [Fintype P]
    (net : WeightedNet P T) : (P → ℤ) →ₗ[ℤ] (T → ℤ) :=
  net.incidence.vecMulLinear

/-- Applying `placeInvariantMap` to a place coefficient vector is identical to
multiplying that vector to the incidence matrix. -/
@[simp]
theorem WeightedNet.placeInvariantMap_apply {P T : Type*} [Fintype P]
    (net : WeightedNet P T) (y : P → ℤ) :
    net.placeInvariantMap y = Matrix.vecMul y net.incidence := rfl

/-! ## Equivalence with the kernel -/

/-- The place invariants of `net` are linearly equivalent to the kernel of
`placeInvariantMap`. This identifies the type of place invariants precisely
with the set of coefficient functions `y` satisfying `y · C = 0`.

As a linear equivalence, `placeInvariantEquivKer` provides two mutually
inverse linear maps. The forward map `placeInvariantEquivKer net inv` sends a
place invariant to its coefficient function in the kernel. The reverse map
`(placeInvariantEquivKer net).symm y` constructs a place invariant from a
kernel element. Both maps preserve addition and integer scalar multiplication.

The equivalence is constructed as follows:

* The forward map sends an invariant `inv` to `inv.coeff`. Kernel membership
  follows from the theorem `coeff_vecMul_incidence_eq_zero` we proved in `PetriNets.PlaceInvariant.lean`.
* The inverse map takes an element `y` of the kernel. Such an element contains
  both a coefficient function `y.1` and a proof `y.2` that
  `placeInvariantMap y.1 = 0`. Evaluating this equality at a transition `t`
  gives the `condition` required to construct a `PlaceInvariant`.
* The two maps are inverse because both preserve the coefficient function.
  `PlaceInvariant.ext` proves equality of invariants, while `Subtype.ext`
  proves equality of elements of the kernel.
* Finally, `coeff_add` and `coeff_smul` show that the forward map preserves
  addition and integer scalar multiplication, making the equivalence linear.
-/
def WeightedNet.placeInvariantEquivKer
    {P T : Type*} [Fintype P] (net : WeightedNet P T) :
    WeightedNet.PlaceInvariant net ≃ₗ[ℤ] LinearMap.ker net.placeInvariantMap where
  toFun inv :=
    ⟨inv.coeff, by
      rw [LinearMap.mem_ker]
      exact inv.coeff_vecMul_incidence_eq_zero⟩
  invFun y :=
    { coeff := y.1
      condition := by
        intro t
        have h := congrFun (LinearMap.mem_ker.mp y.2) t
        exact h }
  left_inv inv := by
    apply WeightedNet.PlaceInvariant.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    rfl
  map_add' inv₁ inv₂ := by
    apply Subtype.ext
    exact WeightedNet.PlaceInvariant.coeff_add inv₁ inv₂
  map_smul' k inv := by
    apply Subtype.ext
    exact WeightedNet.PlaceInvariant.coeff_smul k inv

/-- The forward direction of `placeInvariantEquivKer` sends a place invariant
to its coefficient function. -/
@[simp]
theorem WeightedNet.placeInvariantEquivKer_apply
    {P T : Type*} [Fintype P] (net : WeightedNet P T)
    (inv : WeightedNet.PlaceInvariant net) :
    (net.placeInvariantEquivKer inv).1 = inv.coeff := rfl

/-- The inverse direction of `placeInvariantEquivKer` constructs a place
invariant with the coefficient function carried by the kernel element. -/
@[simp]
theorem WeightedNet.placeInvariantEquivKer_symm_apply_coeff
    {P T : Type*} [Fintype P] (net : WeightedNet P T)
    (y : LinearMap.ker net.placeInvariantMap) :
    ((net.placeInvariantEquivKer).symm y).coeff = y.1 := rfl

end PetriNet
