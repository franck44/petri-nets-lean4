/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller.Termination
public import Mathlib.Data.FinEnum

/-!
# The Karp–Miller construction

This module formalises the Karp–Miller algorithm for constructing a covering
graph of a weighted P/T net. The construction is implemented using a
depth-first search (DFS).

A DFS branch stores its current ω-marking and its ancestor markings because
acceleration depends on the history of the branch. The executable successor
functions enumerate enabled transitions, accelerate their successor
markings, and extend a fresh branch. These computed successors define the DFS
labelled transition system.

When the current marking already occurs among the ancestors, the branch is
not fresh and becomes a leaf. The completed finite DFS tree retains these
closed leaves.

Termination of `dfs` is justified by the well-founded recursive-call relation
`DfsCall`.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, Chapter 14.
  DOI: 10.1007/978-3-642-33278-4.
-/

@[expose] public section

namespace PetriNet

namespace KarpMiller

variable {P T : Type*}
variable {net : WeightedNet P T}

section FinitePlaces

variable [FinEnum P] [FinEnum T]

/-- A finite Karp–Miller tree. Each child is paired with the transition used
to generate it from the marking stored at the parent node. -/
inductive KarpMillerTree (P T : Type*) where
  | node (rootValue : Branch P)
      (children : List (T × KarpMillerTree P T))

/-- The Karp–Miller node value stored at a tree vertex. -/
def KarpMillerTree.rootValue :
    KarpMillerTree P T → Branch P
  | .node rootValue _ => rootValue

/-- The labelled immediate subtrees of a Karp–Miller tree. -/
def KarpMillerTree.children :
    KarpMillerTree P T → List (T × KarpMillerTree P T)
  | .node _ children => children

/-- A Karp–Miller tree is a leaf when it has no child subtree. -/
def KarpMillerTree.IsLeaf (tree : KarpMillerTree P T) : Prop :=
  tree.children = []

/-- A Karp–Miller tree is valid when each labelled parent–child edge belongs
to the DFS LTS and every child subtree is itself valid. -/
inductive KarpMillerTree.IsValid (net : WeightedNet P T) :
    KarpMillerTree P T → Prop where
  | node {rootValue : Branch P}
      {children : List (T × KarpMillerTree P T)}
      (validSteps : ∀ t child, (t, child) ∈ children →
        (dfsLTS net).Tr rootValue t child.rootValue)
      (validSubtrees : ∀ t child, (t, child) ∈ children →
        child.IsValid net) :
      IsValid net (.node rootValue children)

/-- Every immediate edge of a valid Karp–Miller tree belongs to the DFS LTS. -/
theorem KarpMillerTree.IsValid.tr_of_mem_children
    {tree child : KarpMillerTree P T} {t : T}
    (hvalid : tree.IsValid net) (hmem : (t, child) ∈ tree.children) :
    (dfsLTS net).Tr tree.rootValue t child.rootValue := by
  cases hvalid with
  | node validSteps _ => exact validSteps t child hmem

/-- Construct the complete Karp–Miller tree by depth-first search.

The recursive calls are exactly the branches returned by `dfsSuccessors`.
Their termination is justified by `dfsCall_wellFounded`; its accessibility
proof is used only by Lean's termination checker and is erased from the
compiled algorithm. -/
def dfs (net : WeightedNet P T) (src : Branch P) :
    KarpMillerTree P T :=
  .node src <| (dfsSuccessors net src).attach.map fun candidate =>
    (candidate.1.1, dfs net candidate.1.2)
termination_by (dfsCall_wellFounded (net := net) (T := T)).wrap src
decreasing_by
  exact ⟨candidate.1.1, candidate.2⟩

/-- The tree constructed by `dfs` has the source branch as its root. -/
@[simp]
theorem dfs_rootValue (net : WeightedNet P T) (src : Branch P) :
    (dfs net src).rootValue = src := by
  rw [dfs]
  rfl

end FinitePlaces

end KarpMiller

end PetriNet
