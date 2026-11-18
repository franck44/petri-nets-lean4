/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraph
public import Mathlib.Data.FinEnum

/-!
# The Karp–Miller construction

This module formalises the Karp–Miller algorithm for constructing a covering
graph of a weighted P/T net.

The construction is first defined declaratively, independently of a DFS, BFS,
or worklist implementation. A construction node stores its current ω-marking
and the markings of the previous nodes on its branch. Retaining these
ancestors is necessary because acceleration at the current marking depends on
earlier markings on the same branch.

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

/-- A node stores its current value and the values of the previous nodes on
its branch, ordered from the root towards its parent.

The ancestor list is not required to be duplicate-free: a newly generated
node whose value duplicates an ancestor is retained as a closed leaf. The
Karp–Miller construction uses `Node (OmegaMarking P)`. -/
structure Node (Marking : Type*) where
  marking : Marking
  ancestors : List Marking

/-- A Karp–Miller construction node labelled by an ω-marking over `P`. -/
abbrev KarpMillerNode (P : Type*) := Node (OmegaMarking P)

namespace Node

/-- The complete history of a node: its ancestors followed by its current
marking. This list is nonempty by construction. -/
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

The complete history of `node` becomes the ancestor list of the new
node. No freshness condition is imposed: `m` may equal an ancestor, in which
case the result is a duplicate leaf. -/
def append {P : Type*} (m : OmegaMarking P)
    (node : KarpMillerNode P) : KarpMillerNode P where
  marking := m
  ancestors := node.history

/-- A node is a duplicate leaf when its current marking already occurs among
its ancestors. Such a node is retained in the construction but is not
expanded. -/
def IsDuplicate {P : Type*} (node : KarpMillerNode P) : Prop :=
  node.marking ∈ node.ancestors

/-- A node is open when its marking does not duplicate an ancestor and it may
therefore be expanded. -/
def IsOpen {P : Type*} (node : KarpMillerNode P) : Prop :=
  ¬ node.IsDuplicate

/-- The places to accelerate in a marking produced after `node`.

A place `p` is accelerated in `m` when some marking `a` in the complete
history of `node` satisfies:

```text
a ≤ m    and    a p < m p.
``` -/
def acceleratedPlaces {P : Type*} [FinEnum P]
    (m : OmegaMarking P) (node : KarpMillerNode P) : Finset P :=
  Finset.univ.filter fun p =>
    ∃ a ∈ node.history, a ≤ m ∧ a p < m p

/-- A marking with no accelerated place is left unchanged. -/
theorem accelerate_eq_self_of_acceleratedPlaces_eq_empty
    {P : Type*} [FinEnum P]
    {m : OmegaMarking P} {node : KarpMillerNode P}
    (h : acceleratedPlaces m node = ∅) :
    OmegaMarking.accelerateFinset (acceleratedPlaces m node) m = m := by
  funext p
  rw [h]
  simp [OmegaMarking.accelerateFinset]

end Node

/-- The marking obtained by applying the firing arithmetic for `t` at `m`.
When `t` is enabled, this is its unique ω-firing result. -/
def firingResult {P T : Type*} (net : WeightedNet P T)
    (m : OmegaMarking P) (t : T) : OmegaMarking P :=
  fun p => m p - net.pre p t + net.post p t

/-- Compute a Karp–Miller successor without checking that the source is open
or the transition is enabled. This helper performs the firing arithmetic,
computes the places to accelerate, accelerates the result, and appends it to
the source branch. The checked executable interface is `successor?`. -/
def uncheckedSuccessor {P T : Type*} [FinEnum P]
    (net : WeightedNet P T) (src : KarpMillerNode P) (t : T) :
    KarpMillerNode P :=
  let m := firingResult net src.marking t
  Node.append
    (OmegaMarking.accelerateFinset (Node.acceleratedPlaces m src) m) src

/-- Executable Karp–Miller successor. It returns `none` when the source is a
duplicate leaf or `t` is disabled, and otherwise returns the constructed
successor node. -/
def successor? {P T : Type*}
    [FinEnum P] [FinEnum T]
    (net : WeightedNet P T) (src : KarpMillerNode P) (t : T) :
    Option (KarpMillerNode P) :=
  if src.marking ∈ src.ancestors then none
  else if (∀ p, (net.pre p t : ℕ∞) ≤ src.marking p) then
    some (uncheckedSuccessor net src t)
    else none

/-- A Karp–Miller construction step exposed as an LTS relation.

An open node `src` takes a transition `t` enabled at `src.marking`. Firing `t`
produces a marking `m`, which is then accelerated to obtain the marking
stored in `tgt`:

```text
src.marking --t→ m --acceleration→ tgt.marking
```

The places to accelerate are computed from `m` and `src.history`. The final
node `tgt` appends the accelerated marking, not `m`, to the current branch. A
duplicate node is closed and therefore has no outgoing Karp–Miller step. -/
def Step {P T : Type*}
    [FinEnum P] [FinEnum T]
    (net : WeightedNet P T)
    (src : KarpMillerNode P) (t : T) (tgt : KarpMillerNode P) : Prop :=
  successor? net src t = some tgt

/-- The LTS generated by the executable Karp–Miller successor function. Its
states retain branch histories; projection to an LTS of ω-markings will be
defined separately. -/
def lts {P T : Type*}
    [FinEnum P] [FinEnum T]
    (net : WeightedNet P T) :
    Cslib.LTS (KarpMillerNode P) T where
  Tr := Step net

/-- The source of every Karp–Miller step is open. -/
theorem Step.isOpen {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T}
    {src tgt : KarpMillerNode P} {t : T}
    (hstep : Step net src t tgt) : src.IsOpen := by
  change src.marking ∉ src.ancestors
  intro hdup
  simp [Step, successor?, hdup] at hstep

/-- A duplicate node is a leaf: it has no outgoing Karp–Miller step. -/
theorem Node.IsDuplicate.no_step {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T}
    {src : KarpMillerNode P} (hdup : src.IsDuplicate)
    (t : T) (tgt : KarpMillerNode P) :
    ¬ Step net src t tgt := by
  intro hstep
  exact hstep.isOpen hdup

/-- The Karp–Miller LTS is deterministic because `successor?` is a function. -/
theorem lts_deterministic {P T : Type*}
    [FinEnum P] [FinEnum T]
    (net : WeightedNet P T) :
    (lts net).Deterministic := by
  constructor
  intro src t tgt₁ tgt₂ h₁ h₂
  change successor? net src t = some tgt₁ at h₁
  change successor? net src t = some tgt₂ at h₂
  exact Option.some.inj (h₁.symm.trans h₂)

/-- If a node's ancestors contain no duplicates and the node is open,
then the node is not a duplicate and its complete history contains no duplicates. -/
theorem Node.history_nodup {P : Type*} {node : KarpMillerNode P}
    (hancestors : node.ancestors.Nodup) (hopen : node.IsOpen) :
    node.history.Nodup := by
  change node.marking ∉ node.ancestors at hopen
  simp [Node.history, List.nodup_append, hancestors]
  intro a ha heq
  apply hopen
  exact heq ▸ ha

/-- The ancestors of the target of a Karp–Miller step `src t tgt`
are exactly the complete history of `src`. -/
theorem Step.ancestors_eq_history {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T}
    {src tgt : KarpMillerNode P} {t : T}
    (hstep : Step net src t tgt) :
    tgt.ancestors = src.history := by
  rw [Step, successor?] at hstep
  split at hstep
  · contradiction
  · split at hstep
    · obtain rfl := Option.some.inj hstep.symm
      rfl
    · contradiction

/-- A Karp–Miller step `src t tgt` results in `tgt.ancestors` having no duplicates provided
that `src.ancestors` has no duplicates. In other words, the no-duplicates property in ancestors is an invariant preserved by Karp–Miller steps (proved in the `reachable_ancestors_nodup` theorem). -/
theorem Step.ancestors_nodup {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T}
    {src tgt : KarpMillerNode P} {t : T}
    (hstep : Step net src t tgt) (hsrc : src.ancestors.Nodup) :
    tgt.ancestors.Nodup := by
  rw [hstep.ancestors_eq_history]
  exact src.history_nodup hsrc hstep.isOpen

/-- Every node reachable from the initial Karp–Miller node has a
duplicate-free list of ancestors. -/
theorem reachable_ancestors_nodup {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T}
    {m₀ : Marking P} {node : KarpMillerNode P}
    (hreach : (lts net).CanReach (Node.initial m₀) node) :
    node.ancestors.Nodup := by
  obtain ⟨labels, hmtr⟩ := hreach
  have preserve {src tgt : KarpMillerNode P} {labels : List T}
      (h : (lts net).MTr src labels tgt) (hsrc : src.ancestors.Nodup) :
      tgt.ancestors.Nodup := by
    induction h with
    | refl => exact hsrc
    | stepL hstep _ ih => exact ih (hstep.ancestors_nodup hsrc)
  exact preserve hmtr (by simp [Node.initial, Node.root])

/-- A finite Karp–Miller tree. Each child is paired with the transition used
to generate it from the marking stored at the parent node. -/
inductive KarpMillerTree (P T : Type*) where
  | node (root : KarpMillerNode P)
      (children : List (T × KarpMillerTree P T))

/-- A printable view of a Karp–Miller tree.

Markings are functions and therefore cannot be printed directly. This view
replaces each marking by the finite list of its place/value pairs and omits
the ancestor history stored internally by the algorithm. -/
inductive KarpMillerTree.View (P T : Type*) where
  | node (marking : List (P × String))
      (children : List (T × KarpMillerTree.View P T))
  deriving Repr

/-- Render a token count, using `ω` for the top element. -/
def omegaValueToString (n : ℕ∞) : String :=
  if n = ⊤ then "ω" else toString (n.untopD 0)

mutual
  /-- Convert a Karp–Miller tree to its printable view. -/
  def KarpMillerTree.toView {P T : Type*} [FinEnum P] :
      KarpMillerTree P T → KarpMillerTree.View P T
    | .node root children =>
        .node
          ((FinEnum.toList P).map fun p =>
            (p, omegaValueToString (root.marking p)))
          (KarpMillerTree.childrenToViews children)

  /-- Convert a list of labelled child trees to printable views. -/
  def KarpMillerTree.childrenToViews {P T : Type*} [FinEnum P] :
      List (T × KarpMillerTree P T) →
        List (T × KarpMillerTree.View P T)
    | [] => []
    | (t, tree) :: children =>
        (t, tree.toView) :: KarpMillerTree.childrenToViews children
end

/-- Render the marking at a tree node as a DOT label, with one place per line. -/
def KarpMillerTree.markingDotLabel {P : Type*}
    [FinEnum P] [ToString P] (node : KarpMillerNode P) : String :=
  String.intercalate "\\n" <|
    (FinEnum.toList P).map fun p =>
      s!"{toString p} = {omegaValueToString (node.marking p)}"

mutual
  /-- Generate the DOT statements for a tree and return the next unused node
  identifier. -/
  def KarpMillerTree.toDotLines {P T : Type*}
      [FinEnum P] [ToString P] [ToString T]
      (tree : KarpMillerTree P T) (id : ℕ) : ℕ × List String :=
    match tree with
    | .node root children =>
        let nodeLine :=
          s!"  n{id} [label=\"{KarpMillerTree.markingDotLabel root}\"];"
        let result := KarpMillerTree.childrenToDotLines children id (id + 1)
        (result.1, nodeLine :: result.2)

  /-- Generate DOT edges and subtrees for a list of labelled children. -/
  def KarpMillerTree.childrenToDotLines {P T : Type*}
      [FinEnum P] [ToString P] [ToString T]
      (children : List (T × KarpMillerTree P T))
      (parentId nextId : ℕ) : ℕ × List String :=
    match children with
    | [] => (nextId, [])
    | (t, tree) :: rest =>
        let childId := nextId
        let childResult := tree.toDotLines childId
        let restResult :=
          KarpMillerTree.childrenToDotLines rest parentId childResult.1
        let edgeLine :=
          s!"  n{parentId} -> n{childId} [label=\"{toString t}\"];"
        (restResult.1, edgeLine :: childResult.2 ++ restResult.2)
end

/-- Export a finite Karp–Miller tree in Graphviz DOT format. -/
def KarpMillerTree.toDot {P T : Type*}
    [FinEnum P] [ToString P] [ToString T]
    (tree : KarpMillerTree P T) : String :=
  let lines := (tree.toDotLines 0).2
  String.intercalate "\n" <|
    ["digraph KarpMiller {", "  rankdir=LR;", "  node [shape=box];"] ++
      lines ++ ["}"]

/-- Enumerate all successful labelled successors of a Karp–Miller node.

The finite transition type supplies the list of candidate transitions.
Disabled transitions and transitions from duplicate nodes are discarded by
`successor?`. -/
def successors {P T : Type*}
    [FinEnum P] [FinEnum T]
    (net : WeightedNet P T) (src : KarpMillerNode P) :
    List (T × KarpMillerNode P) :=
  (FinEnum.toList T).filterMap fun t =>
    (successor? net src t).map fun tgt => (t, tgt)

/-- Depth-first Karp–Miller exploration with a bound on the remaining branch
depth.

At zero fuel the computation returns `none`. With successor fuel, a duplicate
node becomes a leaf. Otherwise all successful children are recursively
explored with one less unit of fuel. The result is `none` if any child needs
more fuel, and `some tree` when the complete subtree fits within the supplied
bound. -/
def dfsFuel {P T : Type*}
    [FinEnum P] [FinEnum T]
    (net : WeightedNet P T) : ℕ → KarpMillerNode P →
      Option (KarpMillerTree P T)
  | 0, _ => none
  | n + 1, src => do
      let children ← (successors net src).mapM fun (t, tgt) => do
        let tree ← dfsFuel net n tgt
        pure (t, tree)
      pure (.node src children)

end KarpMiller

end PetriNet
