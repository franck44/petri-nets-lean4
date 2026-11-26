/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite sets of Karp–Miller markings

Provides finiteness of the set of markings labelling a Karp–Miller tree.
-/

public section

namespace PetriNet.KarpMiller

variable {P T : Type*}

/-- The set of distinct markings labelling nodes of a Karp–Miller tree is finite. -/
@[expose] def KarpMillerTree.Finite (tree : KarpMillerTree P T) : Prop :=
  {m | tree.HasNode m}.Finite

/-- Every Karp–Miller tree has finitely many distinct node markings. -/
theorem KarpMillerTree.finite (tree : KarpMillerTree P T) : tree.Finite := by
  cases tree with
  | node root children =>
    classical
    have hchildren : {child | child ∈ children}.Finite := by
      simp
    have hlabels := hchildren.biUnion
      (t := fun child => {m | child.2.HasNode m})
      (fun child hc => KarpMillerTree.finite child.2)
    refine (hlabels.insert root).subset ?_
    intro m hm
    cases hm with
    | root => exact Set.mem_insert _ _
    | child hc hn => exact Set.mem_insert_of_mem _ (Set.mem_iUnion₂.mpr ⟨_, hc, hn⟩)
termination_by sizeOf tree
decreasing_by
  have h := List.sizeOf_lt_of_mem hc
  cases child
  simp_wf
  simp at h
  omega

/-- The tree computed from `m₀` has finitely many distinct markings. -/
theorem karpMillerDFS_finite [FinEnum P] [FinEnum T]
    (net : WeightedNet P T) (m₀ : Marking P) :
    (karpMillerDFS net (Branch.initial m₀)).Finite :=
  KarpMillerTree.finite _

end PetriNet.KarpMiller
