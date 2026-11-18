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

/-- A node is a duplicate leaf when its current marking already occurs among
its proper ancestors. Such a node is retained in the construction but is not
expanded. -/
def IsDuplicate {P : Type*} (node : KarpMillerNode P) : Prop :=
  node.marking ∈ node.ancestors

/-- A node is open when its marking does not duplicate an ancestor and it may
therefore be expanded. -/
def IsOpen {P : Type*} (node : KarpMillerNode P) : Prop :=
  ¬ node.IsDuplicate

end Node

end KarpMiller

end PetriNet
