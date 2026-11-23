/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Coverability

/-!
# Covering-graph nodes

Provides the history-carrying nodes of the (algorithm-independent) covering
graph.

A node records an ω-marking and a sequence of ω-markings (ancestors) from the initial
marking of the net that can be visited to reach it.

The ancestors are used to prune the search space by identifying repeated occurrences of ω-markings along a branch.
-/

@[expose] public section

namespace PetriNet.CoveringGraphV2

/-- A node is an ω-marking together with a sequence of ancestor ω-markings.
The ancestor list should record a witness sequence of ω-markings from the root to reach
the current marking. -/
structure Node (P : Type*) where
  /-- The ω-marking labelling the node. -/
  marking : OmegaMarking P
  /-- The markings preceding the node, ordered from root to parent. -/
  ancestors : List (OmegaMarking P)

namespace Node

variable {P : Type*}

/-- The complete history: the ancestors followed by the current
marking. It is nonempty by construction. -/
def history (node : Node P) : List (OmegaMarking P) :=
  node.ancestors ++ [node.marking]

/-- The root node carrying an ω-marking. -/
def root (m₀ : OmegaMarking P) : Node P where
  marking := m₀
  ancestors := []

/-- The root node obtained from a concrete initial marking. -/
def initial (m₀ : Marking P) : Node P :=
  root m₀

/-- Extend a node with a successor marking. The complete history of the
source becomes the ancestor list of the successor. -/
def append (node : Node P) (m : OmegaMarking P) : Node P where
  marking := m
  ancestors := node.history

/-- `node ++ m` extends `node` with successor marking `m`. -/
instance : HAppend (Node P) (OmegaMarking P) (Node P) where
  hAppend := append

@[simp]
theorem append_marking (node : Node P) (m : OmegaMarking P) :
    (node ++ m).marking = m :=
  rfl

@[simp]
theorem append_ancestors (node : Node P) (m : OmegaMarking P) :
    (node ++ m).ancestors = node.history :=
  rfl

/-- A node is a first occurrence when its marking does not already
occur in its ancestors. -/
def IsFirstOccurrence (node : Node P) : Prop :=
  node.marking ∉ node.ancestors

/-- If the ancestors contain no duplicate and the current marking is a first
occurrence, then the complete history contains no duplicate. -/
theorem history_nodup {node : Node P}
    (hancestors : node.ancestors.Nodup) (hfirst : node.IsFirstOccurrence) :
    node.history.Nodup := by
  change node.marking ∉ node.ancestors at hfirst
  simp [history, List.nodup_append, hancestors]
  intro m hm heq
  apply hfirst
  exact heq ▸ hm

end Node

end PetriNet.CoveringGraphV2
