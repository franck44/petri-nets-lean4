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

Termination of `karpMillerDFS` is justified by the well-founded recursive-call
relation `DfsCall`.

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

/-- `tree.HasNode branch` means that `branch` occurs as a node value somewhere
in `tree`. The root occurs directly; a node of any immediate subtree also
occurs in the whole tree. -/
inductive KarpMillerTree.HasNode :
    KarpMillerTree P T → Branch P → Prop where
  | root {rootValue children} :
      HasNode (.node rootValue children) rootValue
  | child {rootValue children t subtree branch}
      (hchild : (t, subtree) ∈ children)
      (hnode : subtree.HasNode branch) :
      HasNode (.node rootValue children) branch

omit [FinEnum P] [FinEnum T] in
/-- A node of an immediate child subtree is also a node of the whole tree. -/
theorem KarpMillerTree.HasNode.of_child
    {tree subtree : KarpMillerTree P T} {t : T} {branch : Branch P}
    (hchild : (t, subtree) ∈ tree.children)
    (hnode : subtree.HasNode branch) : tree.HasNode branch := by
  cases tree
  exact KarpMillerTree.HasNode.child hchild hnode

/-- Construct the complete Karp–Miller tree by depth-first search.

The recursive calls are exactly the branches returned by `dfsSuccessors`.
Their termination is justified by `dfsCall_wellFounded`; its accessibility
proof is used only by Lean's termination checker and is erased from the
compiled algorithm. -/
def karpMillerDFS (net : WeightedNet P T) (src : Branch P) :
    KarpMillerTree P T :=
  .node src <| (dfsSuccessors net src).attach.map fun candidate =>
    (candidate.1.1, karpMillerDFS net candidate.1.2)
termination_by (dfsCall_wellFounded (net := net) (T := T)).wrap src
decreasing_by
  exact ⟨candidate.1.1, candidate.2⟩

/-- The tree constructed by `karpMillerDFS` has the source branch as its
root. -/
@[simp]
theorem karpMillerDFS_rootValue (net : WeightedNet P T) (src : Branch P) :
    (karpMillerDFS net src).rootValue = src := by
  rw [karpMillerDFS]
  rfl

/-- The source branch occurs at the root of the tree constructed from it. -/
theorem karpMillerDFS_hasNode_root (net : WeightedNet P T) (src : Branch P) :
    (karpMillerDFS net src).HasNode src := by
  rw [karpMillerDFS]
  exact KarpMillerTree.HasNode.root

/-- If `src` is fresh and `t` is enabled, its computed successor occurs as an
immediate node of the Karp–Miller tree rooted at `src`. -/
theorem karpMillerDFS_hasNode_succBranch (net : WeightedNet P T)
    (src : Branch P) (t : T) (hfresh : src.IsFresh)
    (henabled : net.OmegaEnabled src.marking t) :
    (karpMillerDFS net src).HasNode (succBranch net src t) := by
  rw [karpMillerDFS]
  apply KarpMillerTree.HasNode.child
    (t := t) (subtree := karpMillerDFS net (succBranch net src t))
  · simp only [List.mem_map]
    have hsuccessor :
        (t, succBranch net src t) ∈ dfsSuccessors net src :=
      mem_dfsSuccessors_iff.mpr ⟨hfresh, henabled, rfl⟩
    refine ⟨⟨(t, succBranch net src t), hsuccessor⟩, ?_, rfl⟩
    simp
  · exact karpMillerDFS_hasNode_root net (succBranch net src t)

/-- Lift one ordinary firing step to the Karp–Miller tree rooted at a fresh
branch. If `src.marking` covers `m` and `m` fires `t` to `m'`, the computed
successor occurs in the tree and covers `m'`.

The result completes the following order-enriched simulation diagram:

```text
                  Fires t
       m --------------------------> m'
       |                              |
       | toOmega ≤                    | toOmega ≤
       v                              v
src.marking ----------------> tgt.marking
              tree child t
```

Here `tgt` is `succBranch net src t`, an immediate child of `src` in
`karpMillerDFS net src`. The diagram commutes using the covering order rather
than equality: acceleration may replace finite components of the lower target
by `ω`.

This is the local over-approximation step. Lifting a complete firing sequence
additionally requires handling a non-fresh leaf by returning to the equal
ancestor stored in its branch. -/
theorem lift_fires_to_karpMillerDFS
    (net : WeightedNet P T) {m m' : Marking P} {src : Branch P} {t : T}
    (hfresh : src.IsFresh) (hcover : m.toOmega ≤ src.marking)
    (hfires : net.Fires m t m') :
    ∃ tgt, (karpMillerDFS net src).HasNode tgt ∧ m'.toOmega ≤ tgt.marking := by
  obtain ⟨henabled, hle⟩ := fires_le_succBranch hcover hfires
  exact ⟨succBranch net src t,
    karpMillerDFS_hasNode_succBranch net src t hfresh henabled, hle⟩

end FinitePlaces

end KarpMiller

end PetriNet
