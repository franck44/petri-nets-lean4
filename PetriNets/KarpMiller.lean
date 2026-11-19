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

The recursive calls are exactly the branches returned by `dfsSuccessors`.
Their termination is justified by `dfsCall_wellFounded`; its accessibility
proof is used only by Lean's termination checker and is erased from the
compiled algorithm. -/
def karpMillerDFS (net : WeightedNet P T) (src : Branch P) :
    KarpMillerTree P T :=
  .node src.marking <| (dfsSuccessors net src).attach.map fun candidate =>
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

/-- The tree rooted at `src` covers every ordinary marking already covered by
`src.marking`. In particular, the initial Karp–Miller tree covers its initial
marking. -/
theorem karpMillerDFS_covers_root (net : WeightedNet P T)
    (src : Branch P) {m : Marking P} (hcover : m.toOmega ≤ src.marking) :
    (karpMillerDFS net src).Covers m := by
  exact ⟨src.marking, karpMillerDFS_hasNode_root net src, hcover⟩

/-- The Karp–Miller tree constructed from an initial marking covers that
marking at its root. This is the base case of firing-sequence simulation. -/
theorem karpMillerDFS_covers_initial (net : WeightedNet P T) (m₀ : Marking P) :
    (karpMillerDFS net (Branch.initial m₀)).Covers m₀ := by
  apply karpMillerDFS_covers_root
  exact le_rfl

/-- If `src` is fresh and `t` is enabled, its computed successor occurs as an
immediate node of the Karp–Miller tree rooted at `src`. -/
theorem karpMillerDFS_hasNode_succBranch (net : WeightedNet P T)
    (src : Branch P) (t : T) (hfresh : src.IsFresh)
    (henabled : net.OmegaEnabled src.marking t) :
    (karpMillerDFS net src).HasNode (succBranch net src t).marking := by
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
    (karpMillerDFS net src).Covers m' := by
  obtain ⟨henabled, hle⟩ := fires_le_succBranch hcover hfires
  exact ⟨(succBranch net src t).marking,
    karpMillerDFS_hasNode_succBranch net src t hfresh henabled, hle⟩

/-- Lift one concrete firing from a fresh covering branch reachable in
`dfsLTS`. The target branch is the computed successor of `src`, reached by
appending the same transition `t` to the DFS path. -/
theorem lift_fires_to_dfsMTr_of_fresh
    (net : WeightedNet P T) {m₀ m m' : Marking P}
    {src : Branch P} {labels : List T} {t : T}
    (hexec : (dfsLTS net).MTr (Branch.initial m₀) labels src)
    (hfresh : src.IsFresh) (hcover : m.toOmega ≤ src.marking)
    (hfires : net.Fires m t m') :
    ∃ nextLabels tgt,
      (dfsLTS net).MTr (Branch.initial m₀) nextLabels tgt ∧
      m'.toOmega ≤ tgt.marking := by
  obtain ⟨henabled, hle⟩ := fires_le_succBranch hcover hfires
  let tgt := succBranch net src t
  have hstep : (dfsLTS net).Tr src t tgt :=
    mem_dfsSuccessors_iff.mpr ⟨hfresh, henabled, rfl⟩
  exact ⟨labels ++ [t], tgt,
    Cslib.LTS.MTr.stepR (dfsLTS net) hexec hstep, hle⟩

/-- Lift one concrete firing from a non-fresh covering branch reachable in
`dfsLTS`. The proof redirects to an earlier fresh branch with the same
marking, then follows its computed successor. -/
theorem lift_fires_to_dfsMTr_of_not_fresh
    (net : WeightedNet P T) {m₀ m m' : Marking P}
    {src : Branch P} {labels : List T} {t : T}
    (hexec : (dfsLTS net).MTr (Branch.initial m₀) labels src)
    (hnotfresh : ¬ src.IsFresh) (hcover : m.toOmega ≤ src.marking)
    (hfires : net.Fires m t m') :
    ∃ nextLabels tgt,
      (dfsLTS net).MTr (Branch.initial m₀) nextLabels tgt ∧
      m'.toOmega ≤ tgt.marking := by
  obtain ⟨pre, ancestor, hpre, hancestorFresh, hmarking⟩ :=
    exists_fresh_predecessor_of_not_fresh hexec hnotfresh
  have hcoverAncestor : m.toOmega ≤ ancestor.marking := by
    rw [hmarking]
    exact hcover
  obtain ⟨henabled, hle⟩ :=
    fires_le_succBranch hcoverAncestor hfires
  let tgt := succBranch net ancestor t
  have hstep : (dfsLTS net).Tr ancestor t tgt :=
    mem_dfsSuccessors_iff.mpr ⟨hancestorFresh, henabled, rfl⟩
  exact ⟨pre ++ [t], tgt,
    Cslib.LTS.MTr.stepR (dfsLTS net) hpre hstep, hle⟩

/-- Lift one concrete firing while maintaining a covering branch reachable
in `dfsLTS` from the initial branch. The proof dispatches to the ordinary
successor lemma when the current branch is fresh and to the redirection lemma
when it is not. -/
theorem lift_fires_to_dfsMTr
    (net : WeightedNet P T) {m₀ m m' : Marking P}
    {src : Branch P} {labels : List T} {t : T}
    (hexec : (dfsLTS net).MTr (Branch.initial m₀) labels src)
    (hcover : m.toOmega ≤ src.marking) (hfires : net.Fires m t m') :
    ∃ nextLabels tgt,
      (dfsLTS net).MTr (Branch.initial m₀) nextLabels tgt ∧
      m'.toOmega ≤ tgt.marking := by
  by_cases hfresh : src.IsFresh
  · exact lift_fires_to_dfsMTr_of_fresh net hexec hfresh hcover hfires
  · exact lift_fires_to_dfsMTr_of_not_fresh net hexec hfresh hcover hfires

/-- Lift a concrete firing sequence to a reachable branch of `dfsLTS` whose
ω-marking covers the concrete target. At each step the proof uses either the
fresh-successor case or redirects a duplicate branch to an earlier fresh
occurrence with the same marking. -/
theorem lift_firesSequence_to_dfsMTr
    (net : WeightedNet P T) {m₀ src tgt : Marking P}
    {branch : Branch P} {labels : List T} {ts : List T}
    (hexec : (dfsLTS net).MTr (Branch.initial m₀) labels branch)
    (hcover : src.toOmega ≤ branch.marking)
    (hseq : net.FiresSequence src ts tgt) :
    ∃ nextLabels next,
      (dfsLTS net).MTr (Branch.initial m₀) nextLabels next ∧
      tgt.toOmega ≤ next.marking := by
  induction hseq generalizing branch labels with
  | nil => exact ⟨labels, branch, hexec, hcover⟩
  | cons head tail ih =>
      obtain ⟨nextLabels, next, hnext, hcoverNext⟩ :=
        lift_fires_to_dfsMTr net hexec hcover head
      exact ih hnext hcoverNext

end FinitePlaces

end KarpMiller

end PetriNet
