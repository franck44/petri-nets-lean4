/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller

/-!
# Completeness of the Karp–Miller construction

This module proves that the finite Karp–Miller tree over-approximates (covers) every
execution of the net. The proof follows this chain of results:

- `dfsLTS_covers_of_fires`: coverage is preserved by one firing.
- `dfsLTS_covers_of_firesSequence`: coverage is preserved by a firing
  sequence.
- `dfsLTS_covers_of_reachable`: every marking reachable in the net is covered
  by a reachable DFS branch marking.
- `karpMillerDFS_covers_of_reachable`: every reachable marking is covered by marking of a node in the finite Karp–Miller tree.

```text
dfsLTS_covers_of_fires
        │
        ▼
dfsLTS_covers_of_firesSequence
        │
        ▼
dfsLTS_covers_of_reachable
        │
        ▼
karpMillerDFS_covers_of_reachable
```

-/

@[expose] public section

namespace PetriNet.KarpMiller

variable {P T : Type*}
variable [FinEnum P] [FinEnum T]
variable (net : WeightedNet P T)

/-- The DFS rooted at `m₀` covers a concrete marking `m` when some reachable
branch has an ω-marking greater than or equal to `m`. -/
def DFSCovers (m₀ m : Marking P) : Prop :=
  ∃ branch,
    (dfsLTS net).CanReach (Branch.initial m₀) branch ∧
    m ≤ branch.marking

/-- Lift coverage by an arbitrary reachable DFS branch across one concrete
firing.

If a reachable branch covers `m` and `m` fires `t` to `m'`, then some
reachable branch covers `m'`:

```text
                         m ──t──▶ m'
                         │        │
                         ≤        ≤
                         ▼        ▼
Branch.initial m₀ ──*──▶ branch    next
              └──────────*─────────▲
```
The proof first replaces the covering branch by a reachable first occurrence
with the same marking. `dfsLTS_tr_cover_of_fires` then supplies the covering
successor edge, which extends the path reaching that first occurrence.
-/
theorem dfsLTS_covers_of_fires
    {m₀ m m' : Marking P} {t : T}
    (hcover : DFSCovers net m₀ m) (hfires : net.Fires m t m') :
    DFSCovers net m₀ m' := by
  obtain ⟨branch, hreach, hcovered⟩ := hcover
  obtain ⟨first, hreachFirst, hfirst, hmarking⟩ :=
    exists_first_occurrence_of_canReach hreach
  have hcoverFirst : m ≤ first.marking := by
    rw [hmarking]
    exact hcovered
  obtain ⟨hstep, hcoverNext⟩ :=
    dfsLTS_tr_cover_of_fires hfirst hcoverFirst hfires
  exact ⟨succBranch net first t,
    Cslib.LTS.CanReach.stepR hreachFirst hstep, hcoverNext⟩

/-- Lift DFS coverage along a concrete firing sequence.

Coverage is preserved one firing at a time by `dfsLTS_covers_of_fires`; the
proof iterates that result along the sequence. -/
theorem dfsLTS_covers_of_firesSequence
    {m₀ src tgt : Marking P} {ts : List T}
    (hcover : DFSCovers net m₀ src)
    (hseq : net.FiresSequence src ts tgt) :
    DFSCovers net m₀ tgt := by
  induction hseq with
  | nil => exact hcover
  | cons head tail ih =>
      exact ih (dfsLTS_covers_of_fires net hcover head)

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
    DFSCovers net m₀ tgt := by
  obtain ⟨ts, hseq⟩ := hreach
  exact dfsLTS_covers_of_firesSequence net
    ⟨Branch.initial m₀,
      Cslib.LTS.CanReach.refl (dfsLTS net) (Branch.initial m₀), le_rfl⟩
    hseq

/-- **Karp–Miller over-approximation for reachability.** For every marking
`tgt` reachable from `m₀`, there exists an ω-marking `mω` occurring in the
finite Karp–Miller tree such that `tgt ≤ mω`.

`dfsLTS_covers_of_reachable` produces a reachable DFS branch covering `tgt`,
and `karpMillerDFS_hasNode_of_mTr` places its ω-marking in the finite tree. -/
theorem karpMillerDFS_covers_of_reachable
    {m₀ tgt : Marking P}
    (hreach : net.Reachable m₀ tgt) :
    ∃ mω,
      (karpMillerDFS net (Branch.initial m₀)).HasNode mω ∧
      tgt ≤ mω := by
  obtain ⟨branch, ⟨labels, hexec⟩, hcover⟩ :=
    dfsLTS_covers_of_reachable net hreach
  exact ⟨branch.marking, karpMillerDFS_hasNode_of_mTr net hexec, hcover⟩

end PetriNet.KarpMiller
