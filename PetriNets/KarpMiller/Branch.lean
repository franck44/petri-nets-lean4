/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraph.Acceleration

/-!
# Karp–Miller branches

Provides branches for the depth-first implementation of the Karp–Miller
algorithm. A branch stores its current ω-marking and the ancestor markings
in order from the root to its parent.

When constructing a successor, the algorithm uses the complete history,
including the current marking, to select the places to accelerate. If the
current marking already occurs among the ancestors, the algorithm stops
expanding that branch.
-/

@[expose] public section

namespace PetriNet.KarpMiller

variable {P : Type*}

/-- A branch of the Karp–Miller DFS tree, represented by its current
ω-marking and its ancestor markings, ordered from the root towards its
parent. -/
structure Branch (P : Type*) where
  marking : OmegaMarking P
  ancestors : List (OmegaMarking P)

namespace Branch

/-- The complete history of a branch: its ancestors followed by its current
marking. This list is nonempty by construction. -/
def history (branch : Branch P) :
    List (OmegaMarking P) :=
  branch.ancestors ++ [branch.marking]

/-- The root node carrying the initial ω-marking. -/
def root (m₀ : OmegaMarking P) : Branch P where
  marking := m₀
  ancestors := []

/-- The root node obtained by embedding an ordinary initial marking. -/
def initial (m₀ : Marking P) : Branch P :=
  root m₀.toOmega

/-- Extend a branch with a new current marking. -/
def append (branch : Branch P)
    (m : OmegaMarking P) : Branch P where
  marking := m
  ancestors := branch.history

/-- `branch ++ m` extends `branch` with the successor marking `m`. -/
instance : HAppend (Branch P) (OmegaMarking P) (Branch P) where
  hAppend := append

@[simp]
theorem append_marking (branch : Branch P) (m : OmegaMarking P) :
    (branch ++ m).marking = m :=
  rfl

@[simp]
theorem append_ancestors (branch : Branch P) (m : OmegaMarking P) :
    (branch ++ m).ancestors = branch.history :=
  rfl

/-- A branch is a first occurrence when its current marking does not duplicate
an ancestor. -/
def IsFirstOccurrence (branch : Branch P) : Prop :=
  branch.marking ∉ branch.ancestors

section FinitePlaces

variable [FinEnum P]

/-- The places accelerated when the Karp–Miller algorithm expands `branch`.

Expanding a branch first fires a transition and produces a successor
marking `m`. The algorithm then compares `m` with the complete history of the
branch. A place `p` is accelerated when some
marking `a` in the history of `branch` satisfies:

```text
a ≤ m    and    a p < m p.
```

The value of every such place is replaced by `ω`. This acceleration ensures
that persistent growth is eventually represented by `ω`, which is essential
for termination of the Karp–Miller construction. -/
def acceleratedPlaces (m : OmegaMarking P) (branch : Branch P) : Finset P :=
  Finset.univ.filter fun p =>
    ∃ a ∈ branch.history, a ≤ m ∧ a p < m p

end FinitePlaces

end Branch

end PetriNet.KarpMiller
