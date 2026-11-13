/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Incidence
public import PetriNets.Reachability

/-!
# State equations for weighted P/T nets

A firing-count vector is associated with each finite transition sequence. For a
list `ts`, the value `firingCount ts t` gives the number of occurrences of
transition `t` in `ts`.

The count vector is represented as an ordinary function `T → ℕ`. Although its
type does not imply finite support, its support is finite because it is
derived from a finite list. Finiteness assumptions on the transition type `T`
will be introduced only when needed, typically for sums over all transitions.

Equality on `T` must be decidable because the firing-count vector counts
occurrences of each transition in a list.
-/

@[expose] public section

namespace PetriNet

/-- The firing-count vector of a transition sequence. -/
def firingCount {T : Type*} [DecidableEq T] (ts : List T) : T → ℕ :=
  fun t => ts.count t

/-- The empty transition sequence has the zero firing-count vector. -/
@[simp]
theorem firingCount_nil {T : Type*} [DecidableEq T] :
    firingCount ([] : List T) = (0 : T → ℕ) := by
  funext t
  simp [firingCount]

/-- Prepending `t` to a transition sequence increments the `t` coordinate of
its firing-count vector and leaves every other coordinate unchanged. -/
@[simp]
theorem firingCount_cons {T : Type*} [DecidableEq T] (t : T) (ts : List T) :
    firingCount (t :: ts) =
      fun u => if u = t then firingCount ts u + 1 else firingCount ts u := by
  funext u
  by_cases h : u = t
  · simp [h, firingCount]
  . simp [h, firingCount, Ne.symm, List.count_cons_of_ne]

/-- The firing-count vector of concatenated transition sequences is the
pointwise sum of their firing-count vectors. -/
@[simp]
theorem firingCount_append {T : Type*} [DecidableEq T]
    (ts₁ ts₂ : List T) :
    firingCount (ts₁ ++ ts₂) = firingCount ts₁ + firingCount ts₂ := by
  funext t
  simp [firingCount]

end PetriNet
