/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraph.Properties
public import PetriNets.LTS.Basic

/-!
# Completeness of the covering LTS

Provides the over-approximation property of the (algorithm-independent)
covering LTS: every concrete marking reachable from an initial marking is
covered by the marking of a reachable coveringLTS node.

The proof proceeds in three steps:

* `coveringLTS_covers_of_fires`: coverage is preserved by one firing;
* `coveringLTS_covers_of_firesSequence`: coverage is preserved by a firing
  sequence;
* `coveringLTS_covers_of_reachable`: every reachable concrete marking is
  covered by a reachable covering node.
-/

@[expose] public section

namespace PetriNet.CoveringGraph

variable {P T : Type*} [FinEnum P]
variable (net : WeightedNet P T)

/-- The covering LTS rooted at `m₀` covers a concrete marking `m` when a
reachable node has an `ω`-marking greater than or equal to `m`. -/
def CoveringLTSCovers (m₀ m : Marking P) : Prop :=
  ∃ node,
    (coveringLTS net).CanReach (Node.initial m₀) node ∧
    m ≤ node.marking

/-- Coverage is preserved across one concrete firing.

Starting from a reachable node covering `m`, first redirect it, if necessary,
to an earlier first-occurrence node with the same marking. The corresponding
covering-LTS successor then covers the concrete firing result `m'`:

```text
               Fires t
       m --------------------> m'
       |                        |
       | ≤                      | ≤
       v                        v
first.marking ──covering t──▶ successor.marking
```
-/
theorem coveringLTS_covers_of_fires
    {m₀ m m' : Marking P} {t : T}
    (hcover : CoveringLTSCovers net m₀ m)
    (hfires : net.Fires m t m') :
    CoveringLTSCovers net m₀ m' := by
  obtain ⟨node, hreach, hcovered⟩ := hcover
  obtain ⟨first, hreachFirst, hfirst, hmarking⟩ :=
    exists_first_occurrence_of_canReach hreach
  have hcoverFirst : m ≤ first.marking := by
    rw [hmarking]
    exact hcovered
  obtain ⟨hstep, hcoverNext⟩ :=
    coveringLTS_tr_cover_of_fires hfirst hcoverFirst hfires
  exact ⟨successor net first t,
    Cslib.LTS.CanReach.stepR hreachFirst hstep, hcoverNext⟩

/-- Coverage is preserved along a concrete firing sequence by applying
`coveringLTS_covers_of_fires` to each firing. -/
theorem coveringLTS_covers_of_firesSequence
    {m₀ src tgt : Marking P} {labels : List T}
    (hcover : CoveringLTSCovers net m₀ src)
    (hexec : net.FiresSequence src labels tgt) :
    CoveringLTSCovers net m₀ tgt := by
  induction hexec with
  | nil => exact hcover
  | cons head tail ih =>
      exact ih (coveringLTS_covers_of_fires net hcover head)

/-- **Covering-LTS completeness for reachability.**

Every concrete marking `tgt` reachable from `m₀` is covered by a reachable
node of the covering LTS rooted at `m₀`:

```text
m₀ ──concrete firing sequence──▶ tgt

Node.initial m₀ ──covering-LTS path──▶ node
                                              ▲
                                              │ tgt ≤ node.marking
```
-/
theorem coveringLTS_covers_of_reachable
    {m₀ tgt : Marking P} (hreach : net.Reachable m₀ tgt) :
    CoveringLTSCovers net m₀ tgt := by
  obtain ⟨labels, hexec⟩ := hreach
  exact coveringLTS_covers_of_firesSequence net
    ⟨Node.initial m₀,
      Cslib.LTS.CanReach.refl (coveringLTS net) (Node.initial m₀), le_rfl⟩
    hexec

end PetriNet.CoveringGraph
