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
markings, and extend an open branch. These computed successors define the DFS
labelled transition system.

When the current marking already occurs among the ancestors, the branch is
not open and becomes a leaf. The completed finite DFS tree retains these
closed leaves.

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

/-- A Karp–Miller DFS edge preserves the invariant that the ancestor list has
no duplicates. -/
theorem ancestors_nodup_of_tr {src tgt : Branch P} {t : T}
    (htr : (dfsLTS net).Tr src t tgt) (hsrc : src.ancestors.Nodup) :
    tgt.ancestors.Nodup := by
  obtain ⟨hopen, _, rfl⟩ := mem_dfsSuccessors_iff.mp htr
  simpa [succBranch] using src.history_nodup hsrc hopen

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
