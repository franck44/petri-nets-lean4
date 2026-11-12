module

public import PetriNets.Basic

/-!
# Firing sequences and reachability

This module defines executions of transition sequences and the resulting
reachability relation for weighted P/T nets.
-/

@[expose] public section

namespace PetriNet

-- namespace WeightedNet

/-- `net.FiresSequence m transitions m'` means that firing the transitions in
order takes marking `m` to marking `m'`. -/
inductive WeightedNet.FiresSequence {P T : Type*} (net : WeightedNet P T) :
    Marking P → List T → Marking P → Prop where
  | nil (marking) : net.FiresSequence marking [] marking
  | cons {marking marking' marking'' : Marking P} {transition : T}
      {transitions : List T} (head : net.Fires marking transition marking')
      (tail : net.FiresSequence marking' transitions marking'') :
      net.FiresSequence marking (transition :: transitions) marking''

/-- A marking is reachable from another marking when some transition sequence
takes the first marking to the second. -/
def WeightedNet.Reachable {P T : Type*} (net : PetriNet.WeightedNet P T)
    (marking marking' : Marking P) : Prop :=
  ∃ transitions : List T, net.FiresSequence marking transitions marking'

-- end WeightedNet

end PetriNet
