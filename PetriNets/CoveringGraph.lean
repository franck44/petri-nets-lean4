/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.CoveringGraph.Finiteness
public import PetriNets.CoveringGraph.Completeness
public import PetriNets.CoveringGraph.Soundness
public import PetriNets.CoveringGraph.Boundedness
public import PetriNets.CoveringGraph.TransitionDead

/-!
# Covering graphs

Provides the covering transition system of a weighted place/transition net
and its finiteness, completeness, and soundness results.

A node records an ω-marking and the markings encountered on its path.
An edge fires an enabled transition and accelerates coordinates where the
raw successor grows relative to a marking in that history. A node whose
marking repeats an ancestor marking has no outgoing edges.

The covering LTS has no infinite execution. From a concrete initial marking,
every reachable concrete marking is covered by a reachable node label, and
every finite demand below a reachable node label is coverable in the net.
The Karp–Miller DFS uses these results through its correspondence with the
reachable node labels.
-/
