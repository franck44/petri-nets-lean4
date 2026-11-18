/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraph

/-!
# The Karp–Miller construction

This module formalises the Karp–Miller algorithm for constructing a covering
graph of a weighted P/T net.

The construction is first defined declaratively, independently of a DFS, BFS,
or worklist implementation. A construction node stores its current ω-marking
and the list of its proper ancestors. Retaining these ancestors is necessary
because acceleration at the current marking depends on earlier markings on
the same branch.

Different construction nodes may carry the same current ω-marking. When the
current marking duplicates an ancestor on its branch, the node is retained as
a closed leaf and is not expanded further. Such duplicate tree nodes will
later be identified when the completed construction is projected to a
marking-based covering graph.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, Chapter 14.
  DOI: 10.1007/978-3-642-33278-4.
-/

@[expose] public section

namespace PetriNet

namespace KarpMiller

/-- A node stores its current value and the list of proper ancestors on its
branch, ordered from the root towards its parent.

The ancestor list is not required to be duplicate-free: a newly generated
node whose value duplicates an ancestor is retained as a closed leaf. The
Karp–Miller construction uses `Node (OmegaMarking P)`. -/
structure Node (Marking : Type*) where
  marking : Marking
  ancestors : List Marking

/-- A Karp–Miller construction node labelled by an ω-marking over `P`. -/
abbrev KarpMillerNode (P : Type*) := Node (OmegaMarking P)

namespace Node

/-- The complete history of a node: all its proper ancestors followed by its
current marking. This list is nonempty by construction. -/
def history {P : Type*} (node : KarpMillerNode P) :
    List (OmegaMarking P) :=
  node.ancestors ++ [node.marking]

/-- The root node carrying the initial ω-marking. -/
def root {P : Type*} (m₀ : OmegaMarking P) : KarpMillerNode P where
  marking := m₀
  ancestors := []

/-- The root node obtained by embedding an ordinary initial marking. -/
def initial {P : Type*} (m₀ : Marking P) : KarpMillerNode P :=
  root m₀.toOmega

/-- Append a marking to a Karp–Miller branch and make it the current marking.

If `node` represents the branch

```text
m₀ → ⋯ → mₙ,
```

then `append m node` represents

```text
m₀ → ⋯ → mₙ → m.
```

The complete history of `node` becomes the proper-ancestor list of the new
node. No freshness condition is imposed: `m` may equal an ancestor, in which
case the result is a duplicate leaf. -/
def append {P : Type*} (m : OmegaMarking P)
    (node : KarpMillerNode P) : KarpMillerNode P where
  marking := m
  ancestors := node.history

/-- A node is a duplicate leaf when its current marking already occurs among
its proper ancestors. Such a node is retained in the construction but is not
expanded. -/
def IsDuplicate {P : Type*} (node : KarpMillerNode P) : Prop :=
  node.marking ∈ node.ancestors

/-- A node is open when its marking does not duplicate an ancestor and it may
therefore be expanded. -/
def IsOpen {P : Type*} (node : KarpMillerNode P) : Prop :=
  ¬ node.IsDuplicate

/-- The set of places to be accelerated at the current node.

If the current node `n` holds marking `m = n.marking`, a place `p` is considered for acceleration
when some proper ancestor node `a ∈ node.ancestors` satisfies:

```text
a ≤ n.marking    and    a p < n.marking p.
``` -/
def acceleratedPlaces {P : Type*} (node : KarpMillerNode P) : Set P :=
  {p | ∃ a ∈ node.ancestors,
    a ≤ node.marking ∧ a p < node.marking p}

end Node

end KarpMiller

end PetriNet
