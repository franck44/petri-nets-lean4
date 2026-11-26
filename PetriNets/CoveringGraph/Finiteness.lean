/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraph.Properties
public import PetriNets.OmegaMarking.Sequence

/-!
# Finiteness of covering-LTS branches

Provides a proof that the covering LTS has no infinite execution.

In a hypothetical infinite execution, the set of `ω`-places can only grow.
Since the net has finitely many places, this set eventually stabilises.
Dickson's lemma then gives an earlier marking that is pointwise at most
a later marking in the stable suffix.

If the inequality were strict, the acceleration rule would force a new
`ω`-place. The two markings are therefore equal. The later node repeats
an ancestor marking and is terminal, contradicting the next step of the
infinite execution.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, Chapter 14.
  DOI: 10.1007/978-3-642-33278-4.
-/

@[expose] public section

namespace PetriNet.CoveringGraph

variable {P T : Type*} [FinEnum P]
variable {net : WeightedNet P T}

/-! ## Strict growth introduces a new ω-place -/

/-- Two endpoints of a `coveringLTS` execution with the same `ω`-places
cannot be strictly ordered.

Suppose instead that `src.marking < tgt.marking`. Then some place `p`
satisfies `src.marking <[p] tgt.marking`. The proof exposes the final edge:

The local successor property rules out `src.marking <[p] tgt.marking`: acceleration
would make `p` equal to `ω` at `tgt`, and endpoint equality would make it
already `ω` at `src`, contradicting strict growth. -/
private theorem not_lt_of_omegaPlaces_eq_mTr
    {src tgt : Node P} {labels : List T}
    (hexec : (coveringLTS net).MTr src labels tgt)
    (homega : OmegaMarking.omegaPlaces src.marking =
      OmegaMarking.omegaPlaces tgt.marking) :
    ¬ src.marking < tgt.marking := by
  intro hlt
  obtain ⟨p, hp⟩ : ∃ p, src.marking p < tgt.marking p :=
    OmegaMarking.exists_place_lt_of_le_of_ne hlt.le hlt.ne
  rcases labels.eq_nil_or_concat with rfl | ⟨labels, t, rfl⟩
  · have : src = tgt := Cslib.LTS.MTr.nil_eq (coveringLTS net) hexec
    subst tgt
    exact (lt_irrefl _ hp).elim
  · rw [List.concat_eq_append] at hexec
    rw [Cslib.LTS.MTr.append_iff] at hexec
    obtain ⟨pred, hprefix, hlast⟩ := hexec
    have htr : (coveringLTS net).Tr pred t tgt := by simpa using hlast
    have homegaPred : OmegaMarking.omegaPlaces pred.marking =
        OmegaMarking.omegaPlaces tgt.marking :=
      omegaPlaces_eq_of_between_mTr hprefix
        (Cslib.LTS.MTr.single (coveringLTS net) htr) homega
    have hgrows : src.marking <[p] tgt.marking := ⟨hlt.le, hp⟩
    rw [htr.2.2] at homega homegaPred hgrows
    exact not_growsAt_successor_of_mem_history_of_omegaPlaces_eq
      (marking_mem_history_of_mTr hprefix) homega homegaPred hgrows

/-! ## Absence of infinite executions -/

/-- The covering LTS has no infinite execution.

Dickson's lemma and the strict-growth result yield two positions carrying the
same marking. The earlier marking occurs among the ancestors of the later
node, so that node is not a first occurrence and is terminal, contradicting
the next edge of the infinite execution. -/
theorem no_OmegaExecution
    {nodes : Cslib.ωSequence (Node P)} {labels : Cslib.ωSequence T} :
    ¬ (coveringLTS net).OmegaExecution nodes labels := by
  -- Assume an infinite execution and derive a terminal node with an outgoing
  -- transition.
  intro hexec
  -- Stabilisation of ω-places and Dickson's lemma provide two positions
  -- i < j carrying the same marking.
  obtain ⟨i, j, hij, heq⟩ :=
    OmegaMarking.exists_eq_pair_of_omegaPlaces_mono
      (fun n => (nodes n).marking)
      -- Existing ω-places are preserved along the execution.
      (fun hij => omegaPlaces_mono_of_omegaExecution hexec hij)
      -- On a stable set of ω-places, comparable markings must be equal:
      -- otherwise they would be strictly ordered, which would introduce a
      -- new ω-place.
      (fun hij hle homega => by
        by_contra hne
        exact not_lt_of_omegaPlaces_eq_mTr
          (hexec.extract_mTr hij.le) homega
          (lt_of_le_of_ne hle hne))
  -- The earlier marking is recorded among the ancestors of the later node.
  have hancestor :=
    marking_mem_ancestors_of_omegaExecution hexec hij
  -- Since the current markings at i and j are equal, node j repeats an
  -- ancestor and is not a first occurrence.
  have hnotfirst : ¬ (nodes j).IsFirstOccurrence := by
    simp only [Node.IsFirstOccurrence, not_not]
    rw [← heq]
    exact hancestor
  -- A repeated node is terminal, contradicting the edge at position j of
  -- the assumed infinite execution.
  exact coveringLTS_terminal_of_not_first_occurrence hnotfirst
    (labels j) (nodes (j + 1)) (hexec j)

end PetriNet.CoveringGraph
