/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller

/-!
# Completeness of the Karp–Miller construction

This module proves that the finite Karp–Miller tree over-approximates every
execution of the net:

Every reachable marking `m` in the net is dominated by an ω-marking
occurring in the tree, i.e. there exists an ω-marking `mω` in the tree
such that `m ≤ mω`.

The proof first lifts one firing to the DFS transition system. A fresh branch
follows its computed successor; a non-fresh branch redirects to an earlier
fresh occurrence with the same marking. Induction extends this simulation to
firing sequences, and `karpMillerDFS_hasNode_of_mTr` transfers the resulting
DFS branch to the finite tree.
-/

@[expose] public section

namespace PetriNet.KarpMiller

variable {P T : Type*}
variable [FinEnum P] [FinEnum T]
variable (net : WeightedNet P T)

/-- The tree rooted at `src` covers every ordinary marking already covered by
`src.marking`. In particular, the initial Karp–Miller tree covers its initial
marking. -/
theorem karpMillerDFS_covers_root
    (src : Branch P) {m : Marking P} (hcover : m ≤ src.marking) :
    (karpMillerDFS net src).Covers m := by
  exact ⟨src.marking, karpMillerDFS_hasNode_root net src, hcover⟩

/-- The Karp–Miller tree constructed from an initial marking covers that
marking at its root. This is the base case of firing-sequence simulation. -/
theorem karpMillerDFS_covers_initial (m₀ : Marking P) :
    (karpMillerDFS net (Branch.initial m₀)).Covers m₀ := by
  apply karpMillerDFS_covers_root
  exact le_rfl

/-- Lift one ordinary firing step to the Karp–Miller tree rooted at a fresh
branch. If `src.marking` covers `m` and `m` fires `t` to `m'`, the computed
successor occurs in the tree and covers `m'`.

```text
                  Fires t
       m --------------------------> m'
       |                              |
       | ≤                            | ≤
       v                              v
src.marking ----------------> tgt.marking
              tree child t
```

Here `tgt` is `succBranch net src t`. Acceleration may replace finite target
components by `ω`, so the diagram commutes in the covering order rather than
by equality. -/
theorem lift_fires_to_karpMillerDFS
    {m m' : Marking P} {src : Branch P} {t : T}
    (hfresh : src.IsFresh) (hcover : m ≤ src.marking)
    (hfires : net.Fires m t m') :
    (karpMillerDFS net src).Covers m' := by
  obtain ⟨henabled, hle⟩ := fires_le_succBranch hcover hfires
  exact ⟨(succBranch net src t).marking,
    karpMillerDFS_hasNode_succBranch net src t hfresh henabled, hle⟩

/-- Lift one concrete firing from a fresh covering branch reachable in
`dfsLTS`. The target branch is the computed successor of `src`, reached by
appending the same transition `t` to the DFS path. -/
theorem lift_fires_to_dfsMTr_of_fresh
    {m₀ m m' : Marking P}
    {src : Branch P} {labels : List T} {t : T}
    (hexec : (dfsLTS net).MTr (Branch.initial m₀) labels src)
    (hfresh : src.IsFresh) (hcover : m ≤ src.marking)
    (hfires : net.Fires m t m') :
    ∃ nextLabels tgt,
      (dfsLTS net).MTr (Branch.initial m₀) nextLabels tgt ∧
      m' ≤ tgt.marking := by
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
    {m₀ m m' : Marking P}
    {src : Branch P} {labels : List T} {t : T}
    (hexec : (dfsLTS net).MTr (Branch.initial m₀) labels src)
    (hnotfresh : ¬ src.IsFresh) (hcover : m ≤ src.marking)
    (hfires : net.Fires m t m') :
    ∃ nextLabels tgt,
      (dfsLTS net).MTr (Branch.initial m₀) nextLabels tgt ∧
      m' ≤ tgt.marking := by
  obtain ⟨pre, ancestor, hpre, hancestorFresh, hmarking⟩ :=
    exists_fresh_predecessor_of_not_fresh hexec hnotfresh
  have hcoverAncestor : m ≤ ancestor.marking := by
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
    {m₀ m m' : Marking P}
    {src : Branch P} {labels : List T} {t : T}
    (hexec : (dfsLTS net).MTr (Branch.initial m₀) labels src)
    (hcover : m ≤ src.marking) (hfires : net.Fires m t m') :
    ∃ nextLabels tgt,
      (dfsLTS net).MTr (Branch.initial m₀) nextLabels tgt ∧
      m' ≤ tgt.marking := by
  by_cases hfresh : src.IsFresh
  · exact lift_fires_to_dfsMTr_of_fresh net hexec hfresh hcover hfires
  · exact lift_fires_to_dfsMTr_of_not_fresh net hexec hfresh hcover hfires

/-- Lift a concrete firing sequence to a reachable branch of `dfsLTS` whose
ω-marking covers the concrete target. At each step the proof uses either the
fresh-successor case or redirects a duplicate branch to an earlier fresh
occurrence with the same marking. -/
theorem lift_firesSequence_to_dfsMTr
    {m₀ src tgt : Marking P}
    {branch : Branch P} {labels : List T} {ts : List T}
    (hexec : (dfsLTS net).MTr (Branch.initial m₀) labels branch)
    (hcover : src ≤ branch.marking)
    (hseq : net.FiresSequence src ts tgt) :
    ∃ nextLabels next,
      (dfsLTS net).MTr (Branch.initial m₀) nextLabels next ∧
      tgt ≤ next.marking := by
  induction hseq generalizing branch labels with
  | nil => exact ⟨labels, branch, hexec, hcover⟩
  | cons head tail ih =>
      obtain ⟨nextLabels, next, hnext, hcoverNext⟩ :=
        lift_fires_to_dfsMTr net hexec hcover head
      exact ih hnext hcoverNext

/-- **Karp–Miller DFS over-approximation for reachability.** Every marking
`tgt` reachable from `m₀` is covered by the marking of some branch reachable
in `dfsLTS` from the initial branch.

```text
m₀ ──concrete firing sequence──▶ tgt

Branch.initial m₀ ──DFS path──▶ branch
                                      ▲
                                      │ tgt ≤ branch.marking
```

This is the transition-system form of Karp–Miller completeness. The finite
tree result below follows by transferring the reachable branch to a tree
node. -/
theorem dfsLTS_covers_of_reachable
    {m₀ tgt : Marking P} (hreach : net.Reachable m₀ tgt) :
    ∃ labels branch,
      (dfsLTS net).MTr (Branch.initial m₀) labels branch ∧
      tgt ≤ branch.marking := by
  obtain ⟨ts, hseq⟩ := hreach
  exact lift_firesSequence_to_dfsMTr net
    Cslib.LTS.MTr.refl le_rfl hseq

/-- **Karp–Miller over-approximation for reachability.** For every marking
`tgt` reachable from `m₀`, there exists an ω-marking `mω` occurring in the
finite Karp–Miller tree such that `tgt ≤ mω`.

Reachability supplies a firing sequence from `m₀` to `tgt`.
`lift_firesSequence_to_dfsMTr` produces a reachable DFS branch covering
`tgt`, and `karpMillerDFS_hasNode_of_mTr` places its ω-marking in the finite
tree. -/
theorem karpMillerDFS_covers_of_reachable
    {m₀ tgt : Marking P}
    (hreach : net.Reachable m₀ tgt) :
    ∃ mω,
      (karpMillerDFS net (Branch.initial m₀)).HasNode mω ∧
      tgt ≤ mω := by
  obtain ⟨labels, branch, hexec, hcover⟩ :=
    dfsLTS_covers_of_reachable net hreach
  exact ⟨branch.marking, karpMillerDFS_hasNode_of_mTr net hexec, hcover⟩

end PetriNet.KarpMiller
