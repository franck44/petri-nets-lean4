module

public import Mathlib
public import Cslib

/-!
# Weighted place/transition nets

This module defines the underlying structure of a weighted P/T net. A weight of zero represents the absence of an arc.
-/

namespace PetriNet

/-- A weighted place/transition net over types of places and transitions.

`pre p t` is the number of tokens consumed from place `p` when transition `t`
fires. `post p t` is the number of tokens produced in `p`.
-/
structure WeightedNet (Place : Type*) (Transition : Type*) where
  pre : Place → Transition → ℕ
  post : Place → Transition → ℕ

end PetriNet
