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

/-- A Karp–Miller tree is a leaf when it has no child subtree. -/
def KarpMillerTree.IsLeaf (tree : KarpMillerTree P T) : Prop :=
  tree.children = []

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

omit [FinEnum P] [FinEnum T] in
/-- A node of an immediate child subtree is also a node of the whole tree. -/
theorem KarpMillerTree.HasNode.of_child
    {tree subtree : KarpMillerTree P T} {t : T} {m : OmegaMarking P}
    (hchild : (t, subtree) ∈ tree.children)
    (hnode : subtree.HasNode m) : tree.HasNode m := by
  cases tree
  exact KarpMillerTree.HasNode.child hchild hnode

/-- A Karp–Miller tree covers an ordinary marking `m` when one of its nodes
has an ω-marking greater than or equal to `m.toOmega`. This is the induction
invariant used to simulate ordinary firing sequences in the finite tree. -/
def KarpMillerTree.Covers (tree : KarpMillerTree P T)
    (m : Marking P) : Prop :=
  ∃ mω, tree.HasNode mω ∧ m.toOmega ≤ mω

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

/-- The tree constructed by `karpMillerDFS` stores the source marking at its
root. -/
@[simp]
theorem karpMillerDFS_rootMarking (net : WeightedNet P T) (src : Branch P) :
    (karpMillerDFS net src).rootMarking = src.marking := by
  rw [karpMillerDFS]
  rfl

/-- The source marking occurs at the root of the tree constructed from its
branch. -/
theorem karpMillerDFS_hasNode_root (net : WeightedNet P T) (src : Branch P) :
    (karpMillerDFS net src).HasNode src.marking := by
  rw [karpMillerDFS]
  exact KarpMillerTree.HasNode.root

/-- If `src` is a first occurrence and `t` is enabled, its computed successor occurs as an
immediate node of the Karp–Miller tree rooted at `src`. -/
theorem karpMillerDFS_hasNode_succBranch (net : WeightedNet P T)
    (src : Branch P) (t : T) (hfirst : src.IsFirstOccurrence)
    (henabled : net.OmegaEnabled src.marking t) :
    (karpMillerDFS net src).HasNode (succBranch net src t).marking := by
  rw [karpMillerDFS]
  apply KarpMillerTree.HasNode.child
    (t := t) (subtree := karpMillerDFS net (succBranch net src t))
  · simp only [List.mem_map]
    have hsuccessor :
        (t, succBranch net src t) ∈ successors net src :=
      mem_successors_iff.mpr ⟨hfirst, henabled, rfl⟩
    refine ⟨⟨(t, succBranch net src t), hsuccessor⟩, ?_, rfl⟩
    simp
  · exact karpMillerDFS_hasNode_root net (succBranch net src t)

/-- Every branch reached by a finite execution of `dfsLTS` has its marking in
the Karp–Miller tree constructed from the execution's source branch. -/
theorem karpMillerDFS_hasNode_of_mTr
    (net : WeightedNet P T) {src tgt : Branch P} {labels : List T}
    (hexec : (dfsLTS net).MTr src labels tgt) :
    (karpMillerDFS net src).HasNode tgt.marking := by
  induction hexec with
  | refl => exact karpMillerDFS_hasNode_root net _
  | @stepL src t next labels tgt htr htail ih =>
      rw [karpMillerDFS]
      apply KarpMillerTree.HasNode.child
        (t := t) (subtree := karpMillerDFS net next)
      · simp only [List.mem_map]
        refine ⟨⟨(t, next), ?_⟩, ?_, rfl⟩
        · exact htr
        · simp
      · exact ih

/-- A node stored in the Karp–Miller tree is the marking of a branch reachable
from the tree's source in `dfsLTS`.

The proof follows the recursive construction of `karpMillerDFS`. The root
gives the empty execution. For a node in a child subtree, the child transition
is prefixed to the execution obtained recursively from that subtree. -/
private theorem exists_dfsMTr_of_karpMillerDFS_hasNode
    (net : WeightedNet P T) (src : Branch P) {mω : OmegaMarking P}
    (hnode : (karpMillerDFS net src).HasNode mω) :
    ∃ labels branch,
      (dfsLTS net).MTr src labels branch ∧ branch.marking = mω := by
  rw [karpMillerDFS] at hnode
  cases hnode with
  | root =>
      exact ⟨[], src, Cslib.LTS.MTr.refl, rfl⟩
  | @child root children t subtree mω hchild hsubtree =>
      simp only [List.mem_map] at hchild
      obtain ⟨candidate, hcandidate, heq⟩ := hchild
      rcases candidate with ⟨⟨u, next⟩, hnext⟩
      simp only at heq
      cases heq
      obtain ⟨labels, branch, hexec, hmarking⟩ :=
        exists_dfsMTr_of_karpMillerDFS_hasNode net next hsubtree
      exact ⟨t :: labels, branch, hexec.stepL hnext, hmarking⟩
termination_by (dfsCall_wellFounded (net := net) (T := T)).wrap src
decreasing_by
  exact ⟨t, hnext⟩

/-- Nodes of the Karp–Miller tree are exactly the markings of branches
reachable from the tree's source in `dfsLTS`.

```text
(karpMillerDFS net src).HasNode mω
  ↔ ∃ labels branch,
      src ──labels──▶ branch ∧ branch.marking = mω
```
-/
theorem karpMillerDFS_hasNode_iff_exists_dfsMTr
    (net : WeightedNet P T) (src : Branch P) (mω : OmegaMarking P) :
    (karpMillerDFS net src).HasNode mω ↔
      ∃ labels branch,
        (dfsLTS net).MTr src labels branch ∧ branch.marking = mω := by
  constructor
  · exact exists_dfsMTr_of_karpMillerDFS_hasNode net src
  · rintro ⟨labels, branch, hexec, hmarking⟩
    rw [← hmarking]
    exact karpMillerDFS_hasNode_of_mTr net hexec

private def nodeOfBranch (branch : Branch P) : CoveringGraph.Node P :=
  ⟨branch.marking, branch.ancestors⟩

/-- A DFS execution translates to a covering execution with the same labels. -/
private theorem coveringMTr_of_dfsMTr
    (net : WeightedNet P T) {src tgt : Branch P} {ts : List T}
    (h : (dfsLTS net).MTr src ts tgt) :
    (CoveringGraph.coveringLTS net).MTr (nodeOfBranch src) ts (nodeOfBranch tgt) := by
  induction h with
  | refl => exact Cslib.LTS.MTr.refl
  | stepL hstep _ ih =>
      obtain ⟨hfirst, henabled, rfl⟩ := mem_successors_iff.mp hstep
      exact Cslib.LTS.MTr.stepL
        (CoveringGraph.coveringLTS_tr_iff.mpr ⟨hfirst, henabled, rfl⟩) ih

/-- Every marking in the Karp–Miller tree labels a reachable covering-LTS node. -/
theorem exists_coveringLTS_canReach_of_karpMillerDFS_hasNode
    (net : WeightedNet P T) (m₀ : Marking P) (mω : OmegaMarking P)
    (h : (karpMillerDFS net (Branch.initial m₀)).HasNode mω) :
    ∃ node, (CoveringGraph.coveringLTS net).CanReach
      (CoveringGraph.Node.initial m₀) node ∧ node.marking = mω := by
  obtain ⟨ts, branch, hexec, hmarking⟩ :=
    (karpMillerDFS_hasNode_iff_exists_dfsMTr net (Branch.initial m₀) mω).mp h
  exact ⟨nodeOfBranch branch, ⟨ts, coveringMTr_of_dfsMTr net hexec⟩, hmarking⟩

private def branchOfNode (node : CoveringGraph.Node P) : Branch P :=
  ⟨node.marking, node.ancestors⟩

/-- A covering execution translates to a DFS execution with the same labels. -/
private theorem dfsMTr_of_coveringMTr
    (net : WeightedNet P T) {src tgt : CoveringGraph.Node P} {ts : List T}
    (h : (CoveringGraph.coveringLTS net).MTr src ts tgt) :
    (dfsLTS net).MTr (branchOfNode src) ts (branchOfNode tgt) := by
  induction h with
  | refl => exact Cslib.LTS.MTr.refl
  | stepL hstep _ ih =>
      obtain ⟨hfirst, henabled, rfl⟩ := CoveringGraph.coveringLTS_tr_iff.mp hstep
      exact Cslib.LTS.MTr.stepL
        (mem_successors_iff.mpr ⟨hfirst, henabled, rfl⟩) ih

/-- Every marking labelling a reachable covering-LTS node occurs in the
Karp–Miller tree. -/
theorem karpMillerDFS_hasNode_of_exists_coveringLTS_canReach
    (net : WeightedNet P T) (m₀ : Marking P) (mω : OmegaMarking P)
    (h : ∃ node, (CoveringGraph.coveringLTS net).CanReach
      (CoveringGraph.Node.initial m₀) node ∧ node.marking = mω) :
    (karpMillerDFS net (Branch.initial m₀)).HasNode mω := by
  obtain ⟨node, ⟨ts, hexec⟩, rfl⟩ := h
  exact karpMillerDFS_hasNode_of_mTr net (dfsMTr_of_coveringMTr net hexec)

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
