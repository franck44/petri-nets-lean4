/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.PlaceInvariant.Algebra

/-!
# Examples of place-invariant operations

This module illustrates the notation provided by the algebraic typeclass
instances for place invariants. The examples are checked by Lean but do not
introduce declarations into the library API.

The fact that each expression below can be constructed with type
`WeightedNet.PlaceInvariant net` means that its coefficient function satisfies
the invariant condition. The corresponding typeclass instance constructs both
the new coefficient function and the proof of this condition.
-/

@[expose] public section

namespace PetriNet

variable {P T : Type*} [Fintype P] {net : WeightedNet P T}

/-- The zero coefficient function is a place invariant of every net. -/
example : WeightedNet.PlaceInvariant net := 0

/-- Place invariants of the same net can be added pointwise. -/
example (inv₁ inv₂ : WeightedNet.PlaceInvariant net) :
    WeightedNet.PlaceInvariant net :=
  inv₁ + inv₂

/-- Every place invariant can be negated. -/
example (inv : WeightedNet.PlaceInvariant net) :
    WeightedNet.PlaceInvariant net :=
  -inv

/-- A place invariant can be multiplied by an integer. -/
example (inv : WeightedNet.PlaceInvariant net) :
    WeightedNet.PlaceInvariant net :=
  (-3 : ℤ) • inv

/-- The coefficient lemmas expose the pointwise meaning of the notation. -/
example (inv₁ inv₂ : WeightedNet.PlaceInvariant net) (p : P) :
    (inv₁ + inv₂).coeff p = inv₁.coeff p + inv₂.coeff p := by
  simp

end PetriNet
