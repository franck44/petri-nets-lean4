/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraph.Completeness
public import PetriNets.CoveringGraph.Soundness
public import PetriNets.MarkingGraph.Boundedness
import PetriNets.CoveringGraph.Finiteness
import PetriNets.LTS.Konig

/-!
# Unbounded places in the covering LTS

Provides characterisations of individual and simultaneous place unboundedness
by reachable ω-markings.
-/

@[expose] public section

namespace PetriNet.CoveringGraph

variable {P T : Type*} [FinEnum P]
variable {net : WeightedNet P T}

private theorem finite_reachable_nodes [Finite T] (m₀ : Marking P) :
    Finite {node : Node P // (coveringLTS net).CanReach (Node.initial m₀) node} := by
  by_contra hinfinite
  obtain ⟨_, _, hexec, _⟩ :=
    Cslib.LTS.konig_weak (coveringLTS net) (Node.initial m₀) hinfinite
  exact no_OmegaExecution hexec

/-- A set of places is simultaneously unbounded exactly when one reachable
covering-LTS node has ω at every place in the set. -/
theorem simultaneouslyUnboundedFrom_iff_exists_omega [Finite T]
    (m₀ : Marking P) (places : Set P) :
    net.SimultaneouslyUnboundedFrom m₀ places ↔
      ∃ node, (coveringLTS net).CanReach (Node.initial m₀) node ∧
        ∀ p ∈ places, node.marking p = ⊤ := by
  constructor
  · intro hunbounded
    classical
    let ReachableNode :=
      {node : Node P // (coveringLTS net).CanReach (Node.initial m₀) node}
    let _ : Finite ReachableNode := finite_reachable_nodes (net := net) m₀
    -- Bound every finite coordinate of every reachable covering node.
    obtain ⟨B, hB⟩ := Finite.bddAbove_range
      (fun np : ReachableNode × P => (np.1.val.marking np.2).toNat)
    obtain ⟨m, hreach, hlarge⟩ := hunbounded B
    obtain ⟨node, hnode, hcover⟩ := coveringLTS_covers_of_reachable net hreach
    refine ⟨node, hnode, fun p hp => ?_⟩
    by_contra hfinite
    have hle : m p ≤ (node.marking p).toNat := by
      apply ENat.natCast_le_natCast.mp
      rw [ENat.natCast_toNat hfinite]
      exact hcover p
    exact (Nat.not_le_of_lt (hlarge p hp))
      (hle.trans (hB ⟨(⟨node, hnode⟩, p), rfl⟩))
  · rintro ⟨node, hnode, homega⟩ B
    obtain ⟨m, hreach, hcover⟩ :=
      (omegaCoverableFrom_of_coveringLTS_canReach hnode).coverable_concretise
        (fun _ => B + 1)
    refine ⟨m, hreach, fun p hp => (Nat.lt_succ_self B).trans_le ?_⟩
    simpa [homega p hp] using hcover p

/-- A place is unbounded exactly when some reachable covering node has ω
at that place. This is simultaneous unboundedness for a singleton. -/
theorem placeUnboundedFrom_iff_exists_omega [Finite T]
    (m₀ : Marking P) (p : P) :
    net.PlaceUnboundedFrom m₀ p ↔
      ∃ node, (coveringLTS net).CanReach (Node.initial m₀) node ∧
        node.marking p = ⊤ := by
  simpa [WeightedNet.simultaneouslyUnboundedFrom_singleton] using
    simultaneouslyUnboundedFrom_iff_exists_omega (net := net) m₀ ({p} : Set P)

end PetriNet.CoveringGraph
