/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller.TreeView
public meta import PetriNets.KarpMiller.TreeView

/-!
# Example: executing the Karp–Miller algorithm

This module defines a one-place net whose only transition creates one token:

```text
[create] ──▶ (buffer)
```

Starting from zero tokens, the first firing produces one token. Since this is
strictly greater than the ancestor marking zero, Karp–Miller acceleration
replaces the token count by `ω`. The next occurrence of the `ω`-marking is a
duplicate and therefore becomes a leaf.
-/

@[expose] public section

namespace PetriNet.KarpMillerExample

/-- The single place, `buffer`. -/
inductive P where
  | buffer
  deriving DecidableEq

instance : FinEnum P :=
  FinEnum.ofList [.buffer] (by intro p; cases p; simp)

instance : ToString P where
  toString
    | .buffer => "buffer"

/-- The single transition, `create`. -/
inductive T where
  | create
  deriving DecidableEq

instance : FinEnum T :=
  FinEnum.ofList [.create] (by intro t; cases t; simp)

instance : ToString T where
  toString
    | .create => "create"

/-- The transition `create` produces one token without consuming any. -/
def net : WeightedNet P T where
  pre _ _ := 0
  post _ _ := 1

/-- The empty initial marking. -/
def initial : Marking P := fun _ => 0

/-- Execute the fuelled DFS and convert its result to Graphviz DOT.

Three units of fuel suffice for this example: the root, the accelerated
`ω`-node, and its duplicate leaf. -/
def dot : String :=
  match KarpMiller.dfsFuel net 3 (KarpMiller.Node.initial initial) with
  | some tree => tree.toDot
  | none => "// Insufficient DFS fuel"

#eval IO.println dot

end PetriNet.KarpMillerExample
