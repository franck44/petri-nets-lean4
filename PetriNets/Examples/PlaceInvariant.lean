/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.PlaceInvariant.Algebra
public import Mathlib.Data.Fin.VecNotation

/-!
# Place-invariant examples

Provides generic examples of the algebraic notation for place invariants and
a concrete two-place net illustrating preservation and a non-reachability
proof. The examples are checked by Lean but do not introduce declarations
into the library API.

The fact that each expression below can be constructed with type
`WeightedNet.PlaceInvariant net` means that its coefficient function satisfies
the invariant condition. The corresponding typeclass instance constructs both
the new coefficient function and the proof of this condition.
-/

@[expose] public section

namespace PetriNet

/-! ## Generic algebraic operations -/

section Generic

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

end Generic

namespace TwoPlaceNet

/-!
## A concrete total-token invariant

Consider a minimal net with two places and one transition:

```text
(p₁) ──▶ [t] ──▶ (p₂)
```

The transition consumes one token from `p₁` and produces one token in `p₂`.
Consequently, the total number of tokens in the two places is invariant.
-/

/-- The two places of the token-transfer net. -/
abbrev P := Fin 2

/-- The transition type of the token-transfer net. Since `Unit` has exactly one
value, its sole transition is written `()`. -/
abbrev T := Unit

/-- The input place. -/
def p₁ : P := 0

/-- The output place. -/
def p₂ : P := 1

/-- A net with a single transition from `p₁` to `p₂`. -/
def net : WeightedNet P T where
  pre p _ := if p = p₁ then 1 else 0
  post p _ := if p = p₂ then 1 else 0

/-- Giving both places coefficient one yields the total-token invariant. -/
def totalInvariant : WeightedNet.PlaceInvariant net where
  coeff _ := 1
  condition := by
    intro _
    rw [Fin.sum_univ_two]
    simp
    simp_rw [WeightedNet.incidence]
    simp [net, p₁, p₂]

/-- The marking with one token in `p₁` and none in `p₂`. -/
def src : Marking P := ![1, 0]

/-- The marking reached by moving the token from `p₁` to `p₂`. -/
def tgt : Marking P := ![0, 1]

/-- A marking containing two tokens in `p₁`. -/
def M₂ : Marking P := ![2, 0]

/-- The single transition moves the token from `src` to `tgt`. -/
theorem fires_src_tgt : net.Fires src () tgt := by
  constructor
  · intro p
    fin_cases p <;> simp [net, src, p₁, p₂]
  · intro p
    fin_cases p <;> simp [net, src, tgt, p₁, p₂]

/-- The source marking has total invariant value one. -/
example : totalInvariant.value src = 1 := by
  simp [WeightedNet.PlaceInvariant.value, Fin.sum_univ_two, totalInvariant, src]

/-- Moving the token preserves the total invariant value by the general
one-step preservation theorem. -/
example : totalInvariant.value tgt = totalInvariant.value src := by
  exact totalInvariant.value_eq_of_fires fires_src_tgt

/-- Scaling the invariant by two doubles its value at the source marking. -/
example : ((2 : ℤ) • totalInvariant).value src = 2 := by
  simp [WeightedNet.PlaceInvariant.value, Fin.sum_univ_two, totalInvariant, src]

/-- The two-token marking `M₂` is not reachable from the one-token source
marking. -/
example : ¬net.Reachable src M₂ := by
  apply totalInvariant.not_reachable_of_value_ne
  simp [WeightedNet.PlaceInvariant.value, Fin.sum_univ_two, totalInvariant, src,
    M₂]

end TwoPlaceNet

end PetriNet
