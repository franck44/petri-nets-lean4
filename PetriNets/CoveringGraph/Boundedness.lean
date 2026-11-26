/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraph.Completeness
public import PetriNets.CoveringGraph.Soundness
public import PetriNets.MarkingGraph.Boundedness
import PetriNets.KarpMiller.Finiteness

/-!
# Unbounded places in the covering LTS

Provides a characterisation of place unboundedness by reachable ω-markings.
-/

@[expose] public section

namespace PetriNet.CoveringGraph

variable {P T : Type*} [FinEnum P]
variable {net : WeightedNet P T}

/-- If a place is unbounded, some reachable covering node has ω there.
Otherwise the finitely many Karp–Miller tree labels give a common bound
at that place. Completeness and the correspondence between the tree and
the covering LTS transfer the bound to every reachable concrete marking. -/
theorem exists_omega_of_placeUnboundedFrom [Finite T]
    {m₀ : Marking P} {p : P} (hunbounded : net.PlaceUnboundedFrom m₀ p) :
    ∃ node, (coveringLTS net).CanReach (Node.initial m₀) node ∧
      node.marking p = ⊤ := by
  classical
  by_contra hnone
  let _ : Fintype T := Fintype.ofFinite T
  let _ : FinEnum T := FinEnum.ofEquiv _ (Fintype.equivFin T)
  let tree := KarpMiller.karpMillerDFS net (KarpMiller.Branch.initial m₀)
  let TreeMarking := {m : OmegaMarking P // tree.HasNode m}
  let _ : Finite TreeMarking := KarpMiller.KarpMillerTree.finite tree
  obtain ⟨B, hB⟩ := Finite.bddAbove_range
    (fun m : TreeMarking => (m.val p).toNat)
  obtain ⟨m, hm, hlt⟩ := hunbounded B
  obtain ⟨node, hnode, hcover⟩ := coveringLTS_covers_of_reachable net hm
  have hlabel : tree.HasNode node.marking :=
    (KarpMiller.karpMillerDFS_hasNode_iff_exists_coveringLTS_canReach
      net m₀ node.marking).mpr ⟨node, hnode, rfl⟩
  have hp : node.marking p ≠ ⊤ := fun h => hnone ⟨node, hnode, h⟩
  apply (lt_irrefl B)
  calc
    B < m p := hlt
    _ ≤ (node.marking p).toNat := by
      apply ENat.natCast_le_natCast.mp
      rw [ENat.natCast_toNat hp]
      exact hcover p
    _ ≤ B := hB ⟨⟨node.marking, hlabel⟩, rfl⟩

/-- An ω at a reachable covering node makes that place unbounded.
For any bound `B`, soundness gives a reachable marking covering the
concretisation with `B + 1` tokens at each ω-place, including `p`. -/
theorem placeUnboundedFrom_of_exists_omega
    {m₀ : Marking P} {p : P}
    (homega : ∃ node, (coveringLTS net).CanReach (Node.initial m₀) node ∧
      node.marking p = ⊤) :
    net.PlaceUnboundedFrom m₀ p := by
  /- get a bound to cover and a witness node from the ω-covering. -/
  intro B
  obtain ⟨node, hnode, hp⟩ := homega
  /- get a reachable concretisation covering the ω-marking of the witness node with B + 1 tokens at p. -/
  obtain ⟨witness, hreachable, hcover⟩ :=
    (omegaCoverableFrom_of_coveringLTS_canReach hnode).coverable_concretise
      (fun _ => B + 1)
  have hpCover : B + 1 ≤ witness p := by
    simpa [hp] using hcover p
  exact ⟨witness, hreachable, (Nat.lt_succ_self B).trans_le hpCover⟩

/-- A place is unbounded exactly when some reachable covering node has ω
at that place. -/
theorem placeUnboundedFrom_iff_exists_omega [Finite T]
    (m₀ : Marking P) (p : P) :
    net.PlaceUnboundedFrom m₀ p ↔
      ∃ node, (coveringLTS net).CanReach (Node.initial m₀) node ∧
        node.marking p = ⊤ :=
  ⟨exists_omega_of_placeUnboundedFrom, placeUnboundedFrom_of_exists_omega⟩

end PetriNet.CoveringGraph
