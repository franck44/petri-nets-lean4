/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Coverability

/-!
# Covering-graph nodes

Provides nodes for the algorithm-independent covering graph of a weighted
P/T net.

A node stores its current ω-marking and a list of ancestor markings. For a
reachable node, that list records the markings along its path from the root
to its parent. The node's history consists of its ancestors followed by its
current marking.

The covering graph uses this history to decide which places to accelerate.
It stops expanding a node when its current marking already occurs among
its ancestors.
-/

@[expose] public section

namespace PetriNet.CoveringGraph

/-- A covering node stores its current ω-marking and its ancestor list. -/
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

end Node

end PetriNet.CoveringGraph
