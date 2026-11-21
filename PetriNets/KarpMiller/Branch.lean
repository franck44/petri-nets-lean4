/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraph

/-!
# Karp–Miller branches

This module defines the branches used by the DFS implementation of the
Karp–Miller algorithm. A branch stores its current ω-marking together with
the markings of its ancestors. Its history is used to determine which places
must be accelerated when a successor is constructed.
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

/-- Two branches are equal when their markings and ancestor lists are equal. -/
@[ext]
theorem ext {left right : Branch P}
    (hmarking : left.marking = right.marking)
    (hancestors : left.ancestors = right.ancestors) : left = right := by
  cases left
  cases right
  simp_all

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

/-- If a branch has no duplicate ancestors and is a first occurrence, then
its complete history has no duplicates. -/
theorem history_nodup {branch : Branch P}
    (hancestors : branch.ancestors.Nodup) (hfirst : branch.IsFirstOccurrence) :
    branch.history.Nodup := by
  change branch.marking ∉ branch.ancestors at hfirst
  simp [history, List.nodup_append, hancestors]
  intro m hm heq
  apply hfirst
  exact heq ▸ hm

section FinitePlaces

variable [FinEnum P]

/-- The prefix of `branch` up to the first occurrence of its final marking.

If the final marking does not appear among the ancestors, the branch is
already a first occurrence and is retained unchanged. Otherwise, the ancestor
list is truncated immediately before the first occurrence of the final
marking. Note that `List.idxOf` returns the length of the list if the element
is not found. -/
def canonicalBranch (branch : Branch P) : Branch P where
  marking := branch.marking
  ancestors := branch.ancestors.take
    (branch.ancestors.idxOf branch.marking)

/-- The canonical first occurrence retains the final marking. -/
@[simp]
theorem canonicalBranch_marking (branch : Branch P) :
    branch.canonicalBranch.marking = branch.marking :=
  rfl

/-- The canonical representative branch is always a first occurrence branch. -/
theorem canonicalBranch_isFirstOccurrence (branch : Branch P) :
    branch.canonicalBranch.IsFirstOccurrence := by
  change branch.marking ∉
    branch.ancestors.take (branch.ancestors.idxOf branch.marking)
  intro hmem
  have hmemAncestors : branch.marking ∈ branch.ancestors :=
    List.mem_of_mem_take hmem
  rw [List.mem_take_iff_idxOf_lt hmemAncestors] at hmem
  exact Nat.lt_irrefl _ hmem

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

/-- A place is selected for acceleration when a marking in the branch history
is below the successor marking and is strictly smaller at that place. -/
theorem mem_acceleratedPlaces {m a : OmegaMarking P} {branch : Branch P}
    {p : P} (ha : a ∈ branch.history) (hle : a ≤ m) (hlt : a p < m p) :
    p ∈ acceleratedPlaces m branch := by
  simp only [acceleratedPlaces, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨a, ha, hle, hlt⟩

/-- A marking with no accelerated place is left unchanged. -/
theorem accelerate_eq_self_of_acceleratedPlaces_eq_empty
    {m : OmegaMarking P} {branch : Branch P}
    (h : acceleratedPlaces m branch = ∅) :
    OmegaMarking.accelerateFinset (acceleratedPlaces m branch) m = m := by
  funext p
  rw [h]
  simp [OmegaMarking.accelerateFinset]

end FinitePlaces

end Branch

end PetriNet.KarpMiller
