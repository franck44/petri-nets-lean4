/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller.Termination
public import PetriNets.CoveringGraph.LTS
public import Mathlib.Data.FinEnum

/-!
# The Karp–Miller construction

This module formalises the Karp–Miller algorithm for constructing a covering
graph of a weighted P/T net. The construction is implemented using a
depth-first search (DFS).

A DFS branch stores its current ω-marking and its ancestor markings because
acceleration depends on the history of the branch. The executable successor
functions enumerate enabled transitions, accelerate their successor
markings, and extend a first-occurrence branch. These computed successors define the DFS
labelled transition system.

When the current marking already occurs among the ancestors, the branch is
not a first occurrence and becomes a leaf. The completed finite DFS tree retains these
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
  | node (rootMarking : OmegaMarking P)
      (children : List (T × KarpMillerTree P T))

/-- The ω-marking stored at the root of a Karp–Miller tree. -/
def KarpMillerTree.rootMarking :
    KarpMillerTree P T → OmegaMarking P
  | .node rootMarking _ => rootMarking

/-- The labelled immediate subtrees of a Karp–Miller tree. -/
def KarpMillerTree.children :
    KarpMillerTree P T → List (T × KarpMillerTree P T)
  | .node _ children => children

/-- `tree.HasNode m` means that the ω-marking `m` occurs at some node of
`tree`. The root marking occurs directly; a marking occurring in any
immediate subtree also occurs in the whole tree. -/
inductive KarpMillerTree.HasNode :
    KarpMillerTree P T → OmegaMarking P → Prop where
  | root {rootMarking children} :
      HasNode (.node rootMarking children) rootMarking
  | child {rootMarking children t subtree m}
      (hchild : (t, subtree) ∈ children)
      (hnode : subtree.HasNode m) :
      HasNode (.node rootMarking children) m

/-- Construct the complete Karp–Miller tree by depth-first search, starting
from the root branch `src`. For a net with initial marking `m₀`, the initial
call is:

```lean
karpMillerDFS net (Branch.initial m₀)
```

Recursive calls receive the current branch, whose ancestors record the path
from the root to its parent. This history is used internally for acceleration
and duplicate detection; only the current ω-marking of each branch is stored
in the resulting tree.

The recursive calls are exactly the branches returned by `successors`.
Their termination is justified by `dfsCall_wellFounded`; its accessibility
proof is used only by Lean's termination checker and is erased from the
compiled algorithm. -/
def karpMillerDFS (net : WeightedNet P T) (src : Branch P) :
    KarpMillerTree P T :=
  .node src.marking <| (successors net src).attach.map fun candidate =>
    (candidate.1.1, karpMillerDFS net candidate.1.2)
termination_by (dfsCall_wellFounded (net := net) (T := T)).wrap src
decreasing_by
  exact ⟨candidate.1.1, candidate.2⟩

/-- The source marking occurs at the root of the tree constructed from its
branch. -/
theorem karpMillerDFS_hasNode_root (net : WeightedNet P T) (src : Branch P) :
    (karpMillerDFS net src).HasNode src.marking := by
  rw [karpMillerDFS]
  exact KarpMillerTree.HasNode.root

/-- A covering execution reaches a marking stored by the executable DFS. -/
private theorem karpMillerDFS_hasNode_of_coveringMTr
    (net : WeightedNet P T) {src tgt : CoveringGraph.Node P} {labels : List T}
    (hexec : (CoveringGraph.coveringLTS net).MTr src labels tgt) :
    (karpMillerDFS net (branchOfNode src)).HasNode tgt.marking := by
  induction hexec with
  | refl => exact karpMillerDFS_hasNode_root net _
  | @stepL src t next labels tgt htr _ ih =>
      rw [karpMillerDFS]
      apply KarpMillerTree.HasNode.child
        (t := t) (subtree := karpMillerDFS net (branchOfNode next))
      · simp only [List.mem_map]
        have hmem : (t, branchOfNode next) ∈ successors net (branchOfNode src) :=
          mem_successors_iff_coveringLTS_tr.mpr htr
        exact ⟨⟨(t, branchOfNode next), hmem⟩, by simp, rfl⟩
      · exact ih

/-- Each tree label comes from a covering execution starting at its root. -/
private theorem exists_coveringMTr_of_karpMillerDFS_hasNode
    (net : WeightedNet P T) (src : Branch P) {mω : OmegaMarking P}
    (hnode : (karpMillerDFS net src).HasNode mω) :
    ∃ labels node,
      (CoveringGraph.coveringLTS net).MTr (nodeOfBranch src) labels node ∧
        node.marking = mω := by
  rw [karpMillerDFS] at hnode
  cases hnode with
  | root => exact ⟨[], nodeOfBranch src, Cslib.LTS.MTr.refl, rfl⟩
  | @child root children t subtree mω hchild hsubtree =>
      simp only [List.mem_map] at hchild
      obtain ⟨candidate, _, heq⟩ := hchild
      rcases candidate with ⟨⟨u, next⟩, hnext⟩
      simp only at heq
      cases heq
      obtain ⟨labels, node, hexec, hmarking⟩ :=
        exists_coveringMTr_of_karpMillerDFS_hasNode net next hsubtree
      exact ⟨t :: labels, node,
        hexec.stepL (mem_successors_iff_coveringLTS_tr.mp hnext), hmarking⟩
termination_by (dfsCall_wellFounded (net := net)).wrap src
decreasing_by exact ⟨t, hnext⟩

/-- Every marking in the Karp–Miller tree labels a reachable covering-LTS node. -/
theorem exists_coveringLTS_canReach_of_karpMillerDFS_hasNode
    (net : WeightedNet P T) (m₀ : Marking P) (mω : OmegaMarking P)
    (h : (karpMillerDFS net (Branch.initial m₀)).HasNode mω) :
    ∃ node, (CoveringGraph.coveringLTS net).CanReach
      (CoveringGraph.Node.initial m₀) node ∧ node.marking = mω := by
  obtain ⟨ts, node, hexec, hmarking⟩ :=
    exists_coveringMTr_of_karpMillerDFS_hasNode net (Branch.initial m₀) h
  exact ⟨node, ⟨ts, hexec⟩, hmarking⟩

/-- Every reachable covering-LTS label occurs in the Karp–Miller tree. -/
theorem karpMillerDFS_hasNode_of_exists_coveringLTS_canReach
    (net : WeightedNet P T) (m₀ : Marking P) (mω : OmegaMarking P)
    (h : ∃ node, (CoveringGraph.coveringLTS net).CanReach
      (CoveringGraph.Node.initial m₀) node ∧ node.marking = mω) :
    (karpMillerDFS net (Branch.initial m₀)).HasNode mω := by
  obtain ⟨node, ⟨ts, hexec⟩, rfl⟩ := h
  exact karpMillerDFS_hasNode_of_coveringMTr net hexec

/-- The Karp–Miller tree contains exactly the ω-markings labelling nodes
reachable from the initial node of the covering LTS. -/
theorem karpMillerDFS_hasNode_iff_exists_coveringLTS_canReach
    (net : WeightedNet P T) (m₀ : Marking P) (mω : OmegaMarking P) :
    (karpMillerDFS net (Branch.initial m₀)).HasNode mω ↔
      ∃ node, (CoveringGraph.coveringLTS net).CanReach
        (CoveringGraph.Node.initial m₀) node ∧ node.marking = mω :=
  ⟨exists_coveringLTS_canReach_of_karpMillerDFS_hasNode net m₀ mω,
    karpMillerDFS_hasNode_of_exists_coveringLTS_canReach net m₀ mω⟩

end FinitePlaces

end KarpMiller

end PetriNet
