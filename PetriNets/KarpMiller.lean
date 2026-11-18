/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.OmegaMarking.Sequence
public import PetriNets.KarpMiller.LTS
public import Mathlib.Data.FinEnum

/-!
# The Karp–Miller construction

This module formalises the Karp–Miller algorithm for constructing a covering
graph of a weighted P/T net. The construction is implemented using a
depth-first search (DFS).

The local construction step is first defined declaratively, independently of
the DFS traversal. A construction node stores its current ω-marking
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

variable {P T : Type*}
variable {net : WeightedNet P T}

section FinitePlaces

variable [FinEnum P] [FinEnum T]

/-- Along an infinite Karp–Miller execution, the set of `ω`-places at an
earlier position is contained in the set at every later position. -/
theorem omegaPlaces_mono_of_omegaExecution {nodes : Cslib.ωSequence (Branch P)}
    {labels : Cslib.ωSequence T}
    (hexec : (dfsLTS net).OmegaExecution nodes labels)
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
          (omegaPlaces_mono_of_tr (hexec j))

end FinitePlaces

/-- If a node's ancestors contain no duplicates and the node is open,
then the node is not a duplicate and its complete history contains no duplicates. -/
theorem Branch.history_nodup {node : Branch P}
    (hancestors : node.ancestors.Nodup) (hopen : node.IsOpen) :
    node.history.Nodup := by
  change node.marking ∉ node.ancestors at hopen
  simp [Branch.history, List.nodup_append, hancestors]
  intro a ha heq
  apply hopen
  exact heq ▸ ha

section FinitePlaces

variable [FinEnum P] [FinEnum T]


/-- The ancestors of the target of a Karp–Miller DFS edge `src t tgt`
are exactly the complete history of `src`. -/
theorem ancestors_eq_history_of_tr {src tgt : Branch P} {t : T}
    (htr : (dfsLTS net).Tr src t tgt) :
    tgt.ancestors = src.history := by
  change (t, tgt) ∈ dfsSuccessors net src at htr
  rw [mem_dfsSuccessors_iff] at htr
  rw [← htr.2.2]
  rfl

/-- Every marking occurring earlier on an infinite Karp–Miller execution is
stored in the ancestor list of every later node.

For consecutive nodes this follows because a step places the source marking
at the head of the target history. For a more distant node, the existing
ancestor membership is carried forward by each subsequent step. -/
theorem marking_mem_ancestors_of_omegaExecution {nodes : Cslib.ωSequence (Branch P)}
    {labels : Cslib.ωSequence T}
    (hexec : (dfsLTS net).OmegaExecution nodes labels)
    {i j : ℕ} (hij : i < j) :
    (nodes i).marking ∈ (nodes j).ancestors := by
  induction j with
  | zero => omega
  | succ j ih =>
      rw [ancestors_eq_history_of_tr (hexec j)]
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hij) with (rfl | hij')
      · simp [Branch.history]
      · simp [Branch.history, ih hij']

/-- Every marking is contained in the complete history of every node at the
same or a later position of an infinite Karp–Miller execution. -/
theorem marking_mem_history_of_omegaExecution
    {nodes : Cslib.ωSequence (Branch P)}
    {labels : Cslib.ωSequence T}
    (hexec : (dfsLTS net).OmegaExecution nodes labels)
    {i j : ℕ} (hij : i ≤ j) :
    (nodes i).marking ∈ (nodes j).history := by
  rcases Nat.eq_or_lt_of_le hij with (rfl | hij')
  · simp [Branch.history]
  · simp [Branch.history,
      marking_mem_ancestors_of_omegaExecution hexec hij']

/-- On an infinite Karp–Miller execution, two distinct comparable markings
with the same ω-places would force a new ω-place in the later marking.

The earlier marking occurs in the history of the predecessor of the later
node. Stability of the ω-place set makes the later marking equal to its raw
firing result. Hence any strict component increase satisfies the acceleration
condition and is replaced by `ω`. -/
theorem exists_new_omegaPlace_of_lt_of_le_omegaExecution
    {nodes : Cslib.ωSequence (Branch P)}
    {labels : Cslib.ωSequence T}
    (hexec : (dfsLTS net).OmegaExecution nodes labels)
    {i j : ℕ} (hij : i < j)
    (hle : (nodes i).marking ≤ (nodes j).marking)
    (homega : OmegaMarking.omegaPlaces (nodes i).marking =
      OmegaMarking.omegaPlaces (nodes j).marking)
    (hne : (nodes i).marking ≠ (nodes j).marking) :
    ∃ p, p ∉ OmegaMarking.omegaPlaces (nodes i).marking ∧
      p ∈ OmegaMarking.omegaPlaces (nodes j).marking := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := by
    use j - 1
    omega
  have hik : i ≤ k := by omega
  have hhistory : (nodes i).marking ∈ (nodes k).history :=
    marking_mem_history_of_omegaExecution hexec hik
  have homegaPred : OmegaMarking.omegaPlaces (nodes k).marking =
      OmegaMarking.omegaPlaces (nodes (k + 1)).marking := by
    apply Finset.Subset.antisymm
    · exact omegaPlaces_mono_of_tr (hexec k)
    · intro p hp
      have hpEarlier : p ∈ OmegaMarking.omegaPlaces (nodes i).marking := by
        rw [homega]
        exact hp
      exact omegaPlaces_mono_of_omegaExecution hexec hik hpEarlier
  have htr := mem_dfsSuccessors_iff.mp (hexec k)
  have homegaSucc : OmegaMarking.omegaPlaces (nodes k).marking =
      OmegaMarking.omegaPlaces
        (succBranch net (nodes k) (labels k)).marking := by
    rw [htr.2.2]
    exact homegaPred
  have hraw : (nodes (k + 1)).marking =
      succMarking net (nodes k).marking (labels k) := by
    rw [← htr.2.2]
    exact succBranch_marking_eq_succMarking_of_omegaPlaces_eq
      (nodes k) (labels k) homegaSucc
  obtain ⟨p, hp⟩ : ∃ p,
      (nodes i).marking p < (nodes (k + 1)).marking p := by
    by_contra h
    push Not at h
    apply hne
    funext p
    exact le_antisymm (hle p) (h p)
  have hpAccelerated : p ∈ Branch.acceleratedPlaces
      (succMarking net (nodes k).marking (labels k)) (nodes k) := by
    simp only [Branch.acceleratedPlaces, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨(nodes i).marking, hhistory, ?_, ?_⟩
    · rw [← hraw]
      exact hle
    · rw [← hraw]
      exact hp
  have hpTop : (nodes (k + 1)).marking p = ⊤ := by
    rw [← htr.2.2]
    exact succBranch_eq_top_of_mem_acceleratedPlaces
      (nodes k) (labels k) hpAccelerated
  refine ⟨p, ?_, ?_⟩
  · rw [OmegaMarking.mem_omegaPlaces]
    intro hpOldTop
    rw [hpOldTop, hpTop] at hp
    exact (lt_self_iff_false ⊤).mp hp
  · rw [OmegaMarking.mem_omegaPlaces]
    exact hpTop

/-- The Karp–Miller LTS has no infinite execution.

The generic ω-marking sequence lemma supplies two equal markings on any
hypothetical infinite execution. The earlier marking is stored among the
ancestors of the later node, so that node is a duplicate. But every step has
an open source, contradicting the next step of the infinite execution. -/
theorem not_omegaExecution
    {nodes : Cslib.ωSequence (Branch P)}
    {labels : Cslib.ωSequence T} :
    ¬ (dfsLTS net).OmegaExecution nodes labels := by
  intro hexec
  obtain ⟨i, j, hij, heq⟩ :=
    OmegaMarking.exists_eq_pair_of_omegaPlaces_mono
      (fun n => (nodes n).marking)
      (fun hij => omegaPlaces_mono_of_omegaExecution hexec hij)
      (fun hij hle homega hne =>
        exists_new_omegaPlace_of_lt_of_le_omegaExecution
          hexec hij hle homega hne)
  have hancestor :=
    marking_mem_ancestors_of_omegaExecution hexec hij
  have hnotopen : ¬ (nodes j).IsOpen := by
    simp only [Branch.IsOpen, not_not]
    rw [← heq]
    exact hancestor
  exact hnotopen (mem_dfsSuccessors_iff.mp (hexec j)).1

/-- `Child net tgt src` means that `tgt` is an immediate Karp–Miller
successor of `src`, for some transition label. The argument order is chosen
for well-founded recursion: children are smaller than their parents. -/
def Child (net : WeightedNet P T)
    (tgt src : Branch P) : Prop :=
  ∃ t, (dfsLTS net).Tr src t tgt

/-- The Karp–Miller child relation is well-founded.

An infinite descending chain for `Child net` would select a transition label
at every position and therefore form an infinite execution of `dfsLTS net`,
contradicting `not_omegaExecution`. -/
theorem child_wellFounded : WellFounded (Child net) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  constructor
  rintro ⟨nodes, hchildren⟩
  let nodeSequence : Cslib.ωSequence (Branch P) := nodes
  let labels : Cslib.ωSequence T := fun n =>
    Classical.choose (hchildren n)
  apply not_omegaExecution (nodes := nodeSequence) (labels := labels)
  intro n
  change (dfsLTS net).Tr (nodes n) (Classical.choose (hchildren n))
    (nodes (n + 1))
  exact Classical.choose_spec (hchildren n)

/-- A Karp–Miller DFS edge preserves the invariant that the ancestor list has
no duplicates. -/
theorem ancestors_nodup_of_tr {src tgt : Branch P} {t : T}
    (htr : (dfsLTS net).Tr src t tgt) (hsrc : src.ancestors.Nodup) :
    tgt.ancestors.Nodup := by
  rw [ancestors_eq_history_of_tr htr]
  exact src.history_nodup hsrc (mem_dfsSuccessors_iff.mp htr).1

/-- Every node reachable from the initial Karp–Miller node has a
duplicate-free list of ancestors. -/
theorem reachable_ancestors_nodup {m₀ : Marking P} {node : Branch P}
    (hreach : (dfsLTS net).CanReach (Branch.initial m₀) node) :
    node.ancestors.Nodup := by
  obtain ⟨labels, hmtr⟩ := hreach
  have preserve {src tgt : Branch P} {labels : List T}
      (h : (dfsLTS net).MTr src labels tgt) (hsrc : src.ancestors.Nodup) :
      tgt.ancestors.Nodup := by
    induction h with
    | refl => exact hsrc
    | stepL htr _ ih => exact ih (ancestors_nodup_of_tr htr hsrc)
  exact preserve hmtr (by simp [Branch.initial, Branch.root])

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
inductive KarpMillerTree.IsValid (net : WeightedNet P T) : KarpMillerTree P T → Prop where
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

/-- Depth-first Karp–Miller exploration with a bound on the remaining branch
depth.

At zero fuel the computation returns `none`. With successor fuel,
`dfsSuccessors` checks whether the branch is open and returns no successors
when it is not. Every successor of an open branch is recursively explored
with one less unit of fuel. The result is `none` if any child needs more fuel,
and `some tree` when the complete subtree fits within the supplied bound. -/
def dfsFuel (net : WeightedNet P T) : ℕ → Branch P →
      Option (KarpMillerTree P T)
  | 0, _ => none
  | n + 1, src => do
      let children ← (dfsSuccessors net src).mapM fun (t, tgt) => do
        let tree ← dfsFuel net n tgt
        pure (t, tree)
      pure (.node src children)

/-- Increasing the available depth by one preserves a successful DFS result. -/
theorem dfsFuel_succ_of_eq_some
    {fuel : ℕ} {src : Branch P} {tree : KarpMillerTree P T}
    (hdfs : dfsFuel net fuel src = some tree) :
    dfsFuel net (fuel + 1) src = some tree := by
  induction fuel generalizing src tree with
  | zero => simp [dfsFuel] at hdfs
  | succ n ih =>
      unfold dfsFuel at hdfs ⊢
      cases hchildren : (dfsSuccessors net src).mapM (fun x =>
          (dfsFuel net n x.2).bind fun subtree => some (x.1, subtree)) with
      | none => simp [hchildren] at hdfs
      | some children =>
          simp [hchildren] at hdfs
          subst tree
          have mapM_succ {candidates : List (T × Branch P)}
              {trees : List (T × KarpMillerTree P T)}
              (hmap : candidates.mapM (fun x =>
                  (dfsFuel net n x.2).bind fun subtree =>
                    some (x.1, subtree)) = some trees) :
              candidates.mapM (fun x =>
                  (dfsFuel net (n + 1) x.2).bind fun subtree =>
                    some (x.1, subtree)) = some trees := by
            induction candidates generalizing trees with
            | nil => simpa using hmap
            | cons candidate candidates ihCandidates =>
                rw [List.mapM_cons] at hmap ⊢
                cases htree : dfsFuel net n candidate.2 with
                | none => simp [htree] at hmap
                | some child =>
                    cases hrest : candidates.mapM (fun x =>
                        (dfsFuel net n x.2).bind fun subtree =>
                          some (x.1, subtree)) with
                    | none => simp [htree, hrest] at hmap
                    | some rest =>
                        simp [htree, hrest] at hmap
                        subst trees
                        simp [ih htree, ihCandidates hrest]
          simp [mapM_succ hchildren]

/-- Any larger fuel bound preserves a successful DFS result. -/
theorem dfsFuel_mono
    {fuel fuel' : ℕ} (hle : fuel ≤ fuel')
    {src : Branch P} {tree : KarpMillerTree P T}
    (hdfs : dfsFuel net fuel src = some tree) :
    dfsFuel net fuel' src = some tree := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction extra with
  | zero => simpa
  | succ extra ih =>
      rw [Nat.add_succ]
      exact dfsFuel_succ_of_eq_some (ih (by omega))

/-- Increasing the common fuel bound preserves a successful traversal of a
list of candidate successors. -/
theorem mapM_dfsFuel_mono
    {fuel fuel' : ℕ} (hle : fuel ≤ fuel')
    {candidates : List (T × Branch P)}
    {trees : List (T × KarpMillerTree P T)}
    (hmap : candidates.mapM (fun x =>
        (dfsFuel net fuel x.2).bind fun tree => some (x.1, tree)) =
      some trees) :
    candidates.mapM (fun x =>
        (dfsFuel net fuel' x.2).bind fun tree => some (x.1, tree)) =
      some trees := by
  induction candidates generalizing trees with
  | nil => simpa using hmap
  | cons candidate candidates ih =>
      rw [List.mapM_cons] at hmap ⊢
      cases htree : dfsFuel net fuel candidate.2 with
      | none => simp [htree] at hmap
      | some tree =>
          cases htrees : candidates.mapM (fun x =>
              (dfsFuel net fuel x.2).bind fun subtree =>
                some (x.1, subtree)) with
          | none => simp [htree, htrees] at hmap
          | some rest =>
              simp [htree, htrees] at hmap
              subst trees
              simp [dfsFuel_mono hle htree, ih htrees]

/-- Some finite fuel bound is sufficient to construct the complete
Karp–Miller subtree below any node. -/
theorem exists_dfsFuel (src : Branch P) :
    ∃ fuel tree, dfsFuel net fuel src = some tree := by
  apply (child_wellFounded (net := net) (T := T)).induction src
  intro src smaller
  have buildChildren : ∀ candidates : List (T × Branch P),
      (∀ candidate ∈ candidates, Child net candidate.2 src) →
      ∃ fuel trees,
        candidates.mapM (fun x =>
          (dfsFuel net fuel x.2).bind fun tree => some (x.1, tree)) =
            some trees := by
    intro candidates
    induction candidates with
    | nil =>
        intro _
        exact ⟨0, [], by simp⟩
    | cons candidate candidates ihCandidates =>
        intro hchildren
        obtain ⟨childFuel, childTree, hchildTree⟩ :=
          smaller candidate.2 (hchildren candidate (by simp))
        obtain ⟨restFuel, restTrees, hrestTrees⟩ :=
          ihCandidates (fun child hmem =>
            hchildren child (by simp [hmem]))
        let fuel := max childFuel restFuel
        have hchildTree' : dfsFuel net fuel candidate.2 =
            some childTree :=
          dfsFuel_mono (Nat.le_max_left _ _) hchildTree
        have hrestTrees' : candidates.mapM (fun x =>
            (dfsFuel net fuel x.2).bind fun tree =>
              some (x.1, tree)) = some restTrees :=
          mapM_dfsFuel_mono (Nat.le_max_right _ _) hrestTrees
        refine ⟨fuel, (candidate.1, childTree) :: restTrees, ?_⟩
        simp [List.mapM_cons, hchildTree', hrestTrees']
  obtain ⟨fuel, trees, htrees⟩ := buildChildren (dfsSuccessors net src)
    (fun candidate hmem =>
      ⟨candidate.1, hmem⟩)
  refine ⟨fuel + 1, .node src trees, ?_⟩
  unfold dfsFuel
  simp [htrees]

/-- A tree returned by `dfsFuel` has the source node supplied to the search
as its root. -/
theorem dfsFuel_rootValue {fuel : ℕ}
    {src : Branch P} {tree : KarpMillerTree P T}
    (h : dfsFuel net fuel src = some tree) :
    tree.rootValue = src := by
  cases fuel with
  | zero => simp [dfsFuel] at h
  | succ n =>
      unfold dfsFuel at h
      cases hchildren : (dfsSuccessors net src).mapM (fun x =>
          (dfsFuel net n x.2).bind fun subtree => some (x.1, subtree)) with
      | none => simp [hchildren] at h
      | some children =>
          simp [hchildren] at h
          subst tree
          rfl

/-- A candidate occurring in a successful `mapM` traversal produces a
corresponding labelled child tree. -/
theorem exists_child_of_mem_mapM_dfsFuel {n : ℕ}
    {candidates : List (T × Branch P)}
    {children : List (T × KarpMillerTree P T)}
    {t : T} {tgt : Branch P}
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

/-- Every outgoing DFS edge occurs among the immediate children of a
successfully constructed tree. -/
theorem exists_child_of_dfsFuel {fuel : ℕ}
    {src tgt : Branch P} {t : T}
    {tree : KarpMillerTree P T}
    (hdfs : dfsFuel net fuel src = some tree)
    (htr : (dfsLTS net).Tr src t tgt) :
    ∃ child, (t, child) ∈ tree.children ∧ child.rootValue = tgt := by
  cases fuel with
  | zero => simp [dfsFuel] at hdfs
  | succ n =>
      unfold dfsFuel at hdfs
      cases hchildren : (dfsSuccessors net src).mapM (fun x =>
          (dfsFuel net n x.2).bind fun subtree => some (x.1, subtree)) with
      | none => simp [hchildren] at hdfs
      | some children =>
          simp [hchildren] at hdfs
          subst tree
          obtain ⟨child, hchild, hchildDfs⟩ :=
            exists_child_of_mem_mapM_dfsFuel hchildren
              htr
          refine ⟨child, hchild, ?_⟩
          exact dfsFuel_rootValue hchildDfs

/-- If a list of candidate edges is recursively explored successfully, the
resulting child trees are valid and remain connected to their parent by those
edges. This is the list-processing part of `dfsFuel_isValid`. -/
theorem validChildren_of_mapM_dfsFuel {n : ℕ} {src : Branch P}
    {candidates : List (T × Branch P)}
    {children : List (T × KarpMillerTree P T)}
    (hsteps : ∀ t tgt, (t, tgt) ∈ candidates → (dfsLTS net).Tr src t tgt)
    (hvalid : ∀ {tgt tree}, dfsFuel net n tgt = some tree → tree.IsValid net)
    (hmap : candidates.mapM (fun x =>
        (dfsFuel net n x.2).bind fun tree => some (x.1, tree)) =
      some children) :
    children.Forall fun (t, child) =>
      (dfsLTS net).Tr src t child.rootValue ∧ child.IsValid net := by
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

/-- Every tree successfully constructed by `dfsFuel` is valid: each labelled
edge belongs to the DFS LTS, recursively throughout the tree. -/
theorem dfsFuel_isValid {fuel : ℕ}
    {src : Branch P} {tree : KarpMillerTree P T}
    (h : dfsFuel net fuel src = some tree) :
    tree.IsValid net := by
  induction fuel generalizing src tree with
  | zero => simp [dfsFuel] at h
  | succ n ih =>
      unfold dfsFuel at h
      cases hchildren : (dfsSuccessors net src).mapM (fun x =>
          (dfsFuel net n x.2).bind fun subtree => some (x.1, subtree)) with
      | none => simp [hchildren] at h
      | some children =>
          simp [hchildren] at h
          subst tree
          have hvalidChildren := validChildren_of_mapM_dfsFuel
            (fun _ _ hmem => hmem)
            (fun hsubtree => ih hsubtree) hchildren
          apply KarpMillerTree.IsValid.node
          · intro t child hmem
            exact ((List.forall_iff_forall_mem.mp hvalidChildren)
              (t, child) hmem).1
          · intro t child hmem
            exact ((List.forall_iff_forall_mem.mp hvalidChildren)
              (t, child) hmem).2

/-- A successfully constructed DFS tree is a leaf exactly when its root has
no outgoing DFS edge. -/
theorem dfsFuel_isLeaf_iff_no_tr {fuel : ℕ}
    {src : Branch P} {tree : KarpMillerTree P T}
    (hdfs : dfsFuel net fuel src = some tree) :
    tree.IsLeaf ↔ ∀ t tgt, ¬ (dfsLTS net).Tr src t tgt := by
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
    have htr :=
      (dfsFuel_isValid hdfs).tr_of_mem_children hmem
    rw [dfsFuel_rootValue hdfs] at htr
    exact hnone t child.rootValue htr

/-- A successfully constructed DFS tree is a leaf exactly when its root
branch is not open or its ω-marking enables no transition. -/
theorem dfsFuel_isLeaf_iff_not_open_or_terminal {fuel : ℕ}
    {src : Branch P} {tree : KarpMillerTree P T}
    (hdfs : dfsFuel net fuel src = some tree) :
    tree.IsLeaf ↔
      ¬ src.IsOpen ∨ ∀ t, ¬ net.OmegaEnabled src.marking t :=
  (dfsFuel_isLeaf_iff_no_tr hdfs).trans
    no_tr_iff_not_open_or_terminal

end FinitePlaces

end KarpMiller

end PetriNet
