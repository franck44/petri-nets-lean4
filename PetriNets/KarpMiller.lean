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

/-- A Karp–Miller step preserves every place already equal to `ω`. -/
theorem Step.preserves_top {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T} {src tgt : KarpMillerNode P} {t : T}
    (hstep : Step net src t tgt) {p : P}
    (hp : src.marking p = ⊤) :
    tgt.marking p = ⊤ := by
  unfold Step successor? at hstep
  split at hstep
  · contradiction
  · split at hstep
    · simp only [Option.some.injEq] at hstep
      subst tgt
      simp [uncheckedSuccessor, Node.append,
        OmegaMarking.accelerateFinset, firingResult, hp]
    · contradiction

/-- Along a Karp–Miller step, the set of places equal to `ω` can only grow. -/
theorem omegaPlaces_mono_of_step {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T} {src tgt : KarpMillerNode P} {t : T}
    (hstep : Step net src t tgt) :
    OmegaMarking.omegaPlaces src.marking ⊆
      OmegaMarking.omegaPlaces tgt.marking := by
  intro p hp
  rw [OmegaMarking.mem_omegaPlaces] at hp ⊢
  exact hstep.preserves_top hp

/-- If a Karp–Miller step does not introduce a new `ω`-place, acceleration
does not change its raw firing result.

A place selected for acceleration has value `ω` in the target. Equality of
the source and target ω-place sets implies that it was already `ω` in the
source, and firing preserves that value. Every unselected place retains its
raw firing value by definition. -/
theorem Step.marking_eq_firingResult_of_omegaPlaces_eq
    {P T : Type*} [FinEnum P] [FinEnum T]
    {net : WeightedNet P T} {src tgt : KarpMillerNode P} {t : T}
    (hstep : Step net src t tgt)
    (homega : OmegaMarking.omegaPlaces src.marking =
      OmegaMarking.omegaPlaces tgt.marking) :
    tgt.marking = firingResult net src.marking t := by
  have htgt : uncheckedSuccessor net src t = tgt := by
    unfold Step successor? at hstep
    split at hstep
    · contradiction
    · split at hstep
      · exact Option.some.inj hstep
      · contradiction
  rw [← htgt] at homega ⊢
  funext p
  by_cases hp : p ∈ Node.acceleratedPlaces
      (firingResult net src.marking t) src
  · have htgtTop :
        (uncheckedSuccessor net src t).marking p = ⊤ := by
      simp [uncheckedSuccessor, Node.append,
        OmegaMarking.accelerateFinset, hp]
    have hpTgt : p ∈ OmegaMarking.omegaPlaces
        (uncheckedSuccessor net src t).marking := by
      rw [OmegaMarking.mem_omegaPlaces]
      exact htgtTop
    rw [← homega, OmegaMarking.mem_omegaPlaces] at hpTgt
    simp [uncheckedSuccessor, Node.append,
      OmegaMarking.accelerateFinset, firingResult, hp, hpTgt]
  · simp [uncheckedSuccessor, Node.append,
      OmegaMarking.accelerateFinset, hp]

/-- A Karp–Miller node has no outgoing step exactly when it is a duplicate or
its ω-marking enables no transition. -/
theorem no_step_iff_duplicate_or_terminal {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T} {src : KarpMillerNode P} :
    (∀ t tgt, ¬ Step net src t tgt) ↔
      src.IsDuplicate ∨ ∀ t, ¬ net.OmegaEnabled src.marking t := by
  constructor
  · intro hnone
    by_cases hdup : src.IsDuplicate
    · exact Or.inl hdup
    · right
      intro t henabled
      apply hnone t (uncheckedSuccessor net src t)
      have hnotmem : src.marking ∉ src.ancestors := by
        simpa [Node.IsDuplicate] using hdup
      have henabled' : ∀ p, (net.pre p t : ℕ∞) ≤ src.marking p :=
        henabled
      simp [Step, successor?, hnotmem, henabled']
  · rintro (hdup | hterminal) t tgt hstep
    · have hmem : src.marking ∈ src.ancestors := by
        simpa [Node.IsDuplicate] using hdup
      simp [Step, successor?, hmem] at hstep
    · by_cases hdup : src.IsDuplicate
      · have hmem : src.marking ∈ src.ancestors := by
          simpa [Node.IsDuplicate] using hdup
        simp [Step, successor?, hmem] at hstep
      · have hdisabled : ¬ ∀ p, (net.pre p t : ℕ∞) ≤ src.marking p :=
          hterminal t
        have hnotmem : src.marking ∉ src.ancestors := by
          simpa [Node.IsDuplicate] using hdup
        simp [Step, successor?, hnotmem, hdisabled] at hstep

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

/-- Along an infinite Karp–Miller execution, the set of `ω`-places at an
earlier position is contained in the set at every later position. -/
theorem omegaPlaces_mono_of_omegaExecution {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T}
    {nodes : Cslib.ωSequence (KarpMillerNode P)}
    {labels : Cslib.ωSequence T}
    (hexec : (lts net).OmegaExecution nodes labels)
    {i j : ℕ} (hij : i ≤ j) :
    OmegaMarking.omegaPlaces (nodes i).marking ⊆
      OmegaMarking.omegaPlaces (nodes j).marking := by
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact Finset.Subset.rfl
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with (rfl | hij')
      · exact Finset.Subset.rfl
      · exact (ih (Nat.le_of_lt_succ hij')).trans
          (omegaPlaces_mono_of_step (hexec j))

/-- On every infinite Karp–Miller execution, the set of places equal to `ω`
is constant from some position onwards.

The sets grow monotonically and are all subsets of the finite place type.
Choose a position at which their cardinality is maximal; every later set has
the same cardinality and therefore equals it. -/
theorem exists_omegaPlaces_stable_from {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T}
    {nodes : Cslib.ωSequence (KarpMillerNode P)}
    {labels : Cslib.ωSequence T}
    (hexec : (lts net).OmegaExecution nodes labels) :
    ∃ n₀, ∀ n, n₀ ≤ n →
      OmegaMarking.omegaPlaces (nodes n).marking =
        OmegaMarking.omegaPlaces (nodes n₀).marking := by
  let cardAt (n : ℕ) :=
    (OmegaMarking.omegaPlaces (nodes n).marking).card
  have himage : (cardAt '' (Set.univ : Set ℕ)).Finite := by
    apply (Set.finite_Iic (Finset.univ : Finset P).card).subset
    rintro k ⟨n, _, rfl⟩
    exact Finset.card_le_univ _
  obtain ⟨n₀, _, hmax⟩ :=
    Set.Finite.exists_maximalFor' cardAt Set.univ himage Set.univ_nonempty
  refine ⟨n₀, fun n hn => ?_⟩
  have hsub := omegaPlaces_mono_of_omegaExecution hexec hn
  have hcard : cardAt n ≤ cardAt n₀ := by
    by_cases hle : cardAt n₀ ≤ cardAt n
    · exact hmax (Set.mem_univ n) hle
    · omega
  exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- On a suffix where the set of ω-places is stable, every Karp–Miller target
marking is exactly the raw result of firing the corresponding transition. -/
theorem marking_eq_firingResult_of_omegaPlaces_stable
    {P T : Type*} [FinEnum P] [FinEnum T]
    {net : WeightedNet P T}
    {nodes : Cslib.ωSequence (KarpMillerNode P)}
    {labels : Cslib.ωSequence T}
    (hexec : (lts net).OmegaExecution nodes labels)
    {n₀ n : ℕ}
    (hstable : ∀ k, n₀ ≤ k →
      OmegaMarking.omegaPlaces (nodes k).marking =
        OmegaMarking.omegaPlaces (nodes n₀).marking)
    (hn : n₀ ≤ n) :
    (nodes (n + 1)).marking =
      firingResult net (nodes n).marking (labels n) := by
  apply (hexec n).marking_eq_firingResult_of_omegaPlaces_eq
  exact (hstable n hn).trans
    (hstable (n + 1) (hn.trans (Nat.le_succ n))).symm

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

/-- Every marking occurring earlier on an infinite Karp–Miller execution is
stored in the ancestor list of every later node.

For consecutive nodes this follows because a step places the source marking
at the head of the target history. For a more distant node, the existing
ancestor membership is carried forward by each subsequent step. -/
theorem marking_mem_ancestors_of_omegaExecution {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T}
    {nodes : Cslib.ωSequence (KarpMillerNode P)}
    {labels : Cslib.ωSequence T}
    (hexec : (lts net).OmegaExecution nodes labels)
    {i j : ℕ} (hij : i < j) :
    (nodes i).marking ∈ (nodes j).ancestors := by
  induction j with
  | zero => omega
  | succ j ih =>
      rw [(hexec j).ancestors_eq_history]
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hij) with (rfl | hij')
      · simp [Node.history]
      · simp [Node.history, ih hij']

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
  | node (rootValue : KarpMillerNode P)
      (children : List (T × KarpMillerTree P T))

/-- The Karp–Miller node value stored at a tree vertex. -/
def KarpMillerTree.rootValue {P T : Type*} :
    KarpMillerTree P T → KarpMillerNode P
  | .node rootValue _ => rootValue

/-- The labelled immediate subtrees of a Karp–Miller tree. -/
def KarpMillerTree.children {P T : Type*} :
    KarpMillerTree P T → List (T × KarpMillerTree P T)
  | .node _ children => children

/-- A Karp–Miller tree is a leaf when it has no child subtree. -/
def KarpMillerTree.IsLeaf {P T : Type*}
    (tree : KarpMillerTree P T) : Prop :=
  tree.children = []

/-- A Karp–Miller tree is valid when each labelled parent–child edge is a
Karp–Miller step and every child subtree is itself valid. -/
inductive KarpMillerTree.IsValid {P T : Type*}
    [FinEnum P] [FinEnum T]
    (net : WeightedNet P T) : KarpMillerTree P T → Prop where
  | node {rootValue : KarpMillerNode P}
      {children : List (T × KarpMillerTree P T)}
      (validSteps : ∀ t child, (t, child) ∈ children →
        Step net rootValue t child.rootValue)
      (validSubtrees : ∀ t child, (t, child) ∈ children →
        child.IsValid net) :
      IsValid net (.node rootValue children)

/-- Every immediate edge of a valid Karp–Miller tree is a Karp–Miller step. -/
theorem KarpMillerTree.IsValid.step_of_mem_children
    {P T : Type*} [FinEnum P] [FinEnum T]
    {net : WeightedNet P T} {tree child : KarpMillerTree P T} {t : T}
    (hvalid : tree.IsValid net) (hmem : (t, child) ∈ tree.children) :
    Step net tree.rootValue t child.rootValue := by
  cases hvalid with
  | node validSteps _ => exact validSteps t child hmem

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
    | .node rootValue children =>
        .node
          ((FinEnum.toList P).map fun p =>
            (p, omegaValueToString (rootValue.marking p)))
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
    | .node rootValue children =>
        let nodeLine :=
          s!"  n{id} [label=\"{KarpMillerTree.markingDotLabel rootValue}\"];"
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

/-- Every pair returned by `successors` is a genuine Karp–Miller step. -/
theorem step_of_mem_successors {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T} {src tgt : KarpMillerNode P} {t : T}
    (h : (t, tgt) ∈ successors net src) :
    Step net src t tgt := by
  simp only [successors, List.mem_filterMap] at h
  obtain ⟨u, _, hu⟩ := h
  rw [Option.map_eq_some_iff] at hu
  obtain ⟨node, hsuccessor, hpair⟩ := hu
  cases hpair
  exact hsuccessor

/-- Every Karp–Miller step is returned by the executable successor
enumeration. -/
theorem mem_successors_of_step {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T} {src tgt : KarpMillerNode P} {t : T}
    (h : Step net src t tgt) :
    (t, tgt) ∈ successors net src := by
  simp only [successors, List.mem_filterMap]
  refine ⟨t, FinEnum.mem_toList t, ?_⟩
  simp [Step] at h
  simp [h]

/-- The executable successor list contains exactly the declarative
Karp–Miller steps. -/
theorem mem_successors_iff {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T} {src tgt : KarpMillerNode P} {t : T} :
    (t, tgt) ∈ successors net src ↔ Step net src t tgt :=
  ⟨step_of_mem_successors, mem_successors_of_step⟩

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

/-- A tree returned by `dfsFuel` has the source node supplied to the search
as its root. -/
theorem dfsFuel_rootValue {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T} {fuel : ℕ}
    {src : KarpMillerNode P} {tree : KarpMillerTree P T}
    (h : dfsFuel net fuel src = some tree) :
    tree.rootValue = src := by
  cases fuel with
  | zero => simp [dfsFuel] at h
  | succ n =>
      unfold dfsFuel at h
      cases hchildren : (successors net src).mapM (fun x =>
          (dfsFuel net n x.2).bind fun subtree => some (x.1, subtree)) with
      | none => simp [hchildren] at h
      | some children =>
          simp [hchildren] at h
          subst tree
          rfl

/-- A candidate occurring in a successful `mapM` traversal produces a
corresponding labelled child tree. -/
theorem exists_child_of_mem_mapM_dfsFuel {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T} {n : ℕ}
    {candidates : List (T × KarpMillerNode P)}
    {children : List (T × KarpMillerTree P T)}
    {t : T} {tgt : KarpMillerNode P}
    (hmap : candidates.mapM (fun x =>
        (dfsFuel net n x.2).bind fun tree => some (x.1, tree)) =
      some children)
    (hmem : (t, tgt) ∈ candidates) :
    ∃ child, (t, child) ∈ children ∧ dfsFuel net n tgt = some child := by
  induction candidates generalizing children with
  | nil => simp at hmem
  | cons candidate candidates ih =>
      rcases candidate with ⟨u, node⟩
      rw [List.mapM_cons] at hmap
      cases htree : dfsFuel net n node with
      | none => simp [htree] at hmap
      | some tree =>
          cases hchildren : candidates.mapM (fun x =>
              (dfsFuel net n x.2).bind fun subtree =>
                some (x.1, subtree)) with
          | none => simp [htree, hchildren] at hmap
          | some rest =>
              simp [htree, hchildren] at hmap
              subst children
              simp only [List.mem_cons] at hmem
              rcases hmem with hhead | htail
              · cases hhead
                exact ⟨tree, by simp, htree⟩
              · obtain ⟨child, hchild, hdfs⟩ := ih hchildren htail
                exact ⟨child, by simp [hchild], hdfs⟩

/-- Every outgoing Karp–Miller step occurs among the immediate children of a
successfully constructed DFS tree. -/
theorem exists_child_of_dfsFuel {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T} {fuel : ℕ}
    {src tgt : KarpMillerNode P} {t : T}
    {tree : KarpMillerTree P T}
    (hdfs : dfsFuel net fuel src = some tree)
    (hstep : Step net src t tgt) :
    ∃ child, (t, child) ∈ tree.children ∧ child.rootValue = tgt := by
  cases fuel with
  | zero => simp [dfsFuel] at hdfs
  | succ n =>
      unfold dfsFuel at hdfs
      cases hchildren : (successors net src).mapM (fun x =>
          (dfsFuel net n x.2).bind fun subtree => some (x.1, subtree)) with
      | none => simp [hchildren] at hdfs
      | some children =>
          simp [hchildren] at hdfs
          subst tree
          obtain ⟨child, hchild, hchildDfs⟩ :=
            exists_child_of_mem_mapM_dfsFuel hchildren
              (mem_successors_of_step hstep)
          refine ⟨child, hchild, ?_⟩
          exact dfsFuel_rootValue hchildDfs

/-- If a list of candidate steps is recursively explored successfully, the
resulting child trees are valid and remain connected to their parent by those
steps. This is the list-processing part of `dfsFuel_isValid`. -/
theorem validChildren_of_mapM_dfsFuel {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T} {n : ℕ} {src : KarpMillerNode P}
    {candidates : List (T × KarpMillerNode P)}
    {children : List (T × KarpMillerTree P T)}
    (hsteps : ∀ t tgt, (t, tgt) ∈ candidates → Step net src t tgt)
    (hvalid : ∀ {tgt tree}, dfsFuel net n tgt = some tree → tree.IsValid net)
    (hmap : candidates.mapM (fun x =>
        (dfsFuel net n x.2).bind fun tree => some (x.1, tree)) =
      some children) :
    children.Forall fun (t, child) =>
      Step net src t child.rootValue ∧ child.IsValid net := by
  induction candidates generalizing children with
  | nil =>
      simp at hmap
      subst children
      simp
  | cons candidate candidates ih =>
      rcases candidate with ⟨t, tgt⟩
      rw [List.mapM_cons] at hmap
      cases htree : dfsFuel net n tgt with
      | none => simp [htree] at hmap
      | some tree =>
          cases hchildren : candidates.mapM (fun x =>
              (dfsFuel net n x.2).bind fun subtree =>
                some (x.1, subtree)) with
          | none => simp [htree, hchildren] at hmap
          | some rest =>
              simp [htree, hchildren] at hmap
              subst children
              simp only [List.forall_cons]
              constructor
              · constructor
                · rw [dfsFuel_rootValue htree]
                  exact hsteps t tgt (by simp)
                · exact hvalid htree
              · apply ih
                · intro u node hmem
                  exact hsteps u node (by simp [hmem])
                · exact hchildren

/-- Every tree successfully constructed by `dfsFuel` is valid: each of its
labelled edges is a Karp–Miller step, recursively throughout the tree. -/
theorem dfsFuel_isValid {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T} {fuel : ℕ}
    {src : KarpMillerNode P} {tree : KarpMillerTree P T}
    (h : dfsFuel net fuel src = some tree) :
    tree.IsValid net := by
  induction fuel generalizing src tree with
  | zero => simp [dfsFuel] at h
  | succ n ih =>
      unfold dfsFuel at h
      cases hchildren : (successors net src).mapM (fun x =>
          (dfsFuel net n x.2).bind fun subtree => some (x.1, subtree)) with
      | none => simp [hchildren] at h
      | some children =>
          simp [hchildren] at h
          subst tree
          have hvalidChildren := validChildren_of_mapM_dfsFuel
            (fun _ _ hmem => step_of_mem_successors hmem)
            (fun hsubtree => ih hsubtree) hchildren
          apply KarpMillerTree.IsValid.node
          · intro t child hmem
            exact ((List.forall_iff_forall_mem.mp hvalidChildren)
              (t, child) hmem).1
          · intro t child hmem
            exact ((List.forall_iff_forall_mem.mp hvalidChildren)
              (t, child) hmem).2

/-- A successfully constructed DFS tree is a leaf exactly when its root has
no outgoing Karp–Miller step. -/
theorem dfsFuel_isLeaf_iff_no_step {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T} {fuel : ℕ}
    {src : KarpMillerNode P} {tree : KarpMillerTree P T}
    (hdfs : dfsFuel net fuel src = some tree) :
    tree.IsLeaf ↔ ∀ t tgt, ¬ Step net src t tgt := by
  constructor
  · intro hleaf t tgt hstep
    obtain ⟨child, hchild, _⟩ := exists_child_of_dfsFuel hdfs hstep
    change tree.children = [] at hleaf
    rw [hleaf] at hchild
    simp at hchild
  · intro hnone
    change tree.children = []
    rw [List.eq_nil_iff_forall_not_mem]
    intro edge hmem
    rcases edge with ⟨t, child⟩
    have hstep :=
      (dfsFuel_isValid hdfs).step_of_mem_children hmem
    rw [dfsFuel_rootValue hdfs] at hstep
    exact hnone t child.rootValue hstep

/-- A successfully constructed DFS tree is a leaf exactly when its root node
is a duplicate or its ω-marking enables no transition. -/
theorem dfsFuel_isLeaf_iff_duplicate_or_terminal {P T : Type*}
    [FinEnum P] [FinEnum T]
    {net : WeightedNet P T} {fuel : ℕ}
    {src : KarpMillerNode P} {tree : KarpMillerTree P T}
    (hdfs : dfsFuel net fuel src = some tree) :
    tree.IsLeaf ↔
      src.IsDuplicate ∨ ∀ t, ¬ net.OmegaEnabled src.marking t :=
  (dfsFuel_isLeaf_iff_no_step hdfs).trans
    no_step_iff_duplicate_or_terminal

end KarpMiller

end PetriNet
