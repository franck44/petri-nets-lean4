/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.KarpMiller

/-!
# Soundness of the Karp–Miller construction

This module proves that the ω-markings stored in a Karp–Miller tree do not
introduce false coverability claims. An ω-marking is sound from an initial
marking when every ordinary marking below it is covered by some reachable
marking.

The quantifiers are important: each finite marking may have a different
reachable witness. In particular, an ω component represents arbitrarily large
reachable token counts, not one ordinary marking containing ω tokens.

The proof will establish soundness first for the initial marking, then show
that it is preserved by ordinary successors and by acceleration.
-/

@[expose] public section

namespace PetriNet

/-- An ω-marking `mω` is omega coverable from `m₀` when every concrete (no omega)
marking below `mω` is coverable from `m₀`.

Equivalently, the downward closure of `mω` among concrete markings is
contained in the downward closure of a marking reachable from `m₀`:

```text
∀ concrete marking m, m.toOmega ≤ mω → ∃ m', Reachable m₀ m' ∧ m ≤ m'.
```
-/
def WeightedNet.OmegaCoverableFrom {P T : Type*} (net : WeightedNet P T)
    (m₀ : Marking P) (mω : OmegaMarking P) : Prop :=
  ∀ m, m.toOmega ≤ mω → net.CoverableFrom m₀ m

/-- The initial marking embedded as an ω-marking is coverable from itself.
Every ordinary marking below `m₀.toOmega` is covered by the reachable
marking `m₀`. -/
theorem WeightedNet.omegaCoverableFrom_initial
    {P T : Type*} (net : WeightedNet P T) (m₀ : Marking P) :
    net.OmegaCoverableFrom m₀ m₀.toOmega := by
  intro m hle
  refine ⟨m₀, WeightedNet.Reachable.refl net m₀, ?_⟩
  intro p
  exact ENat.natCast_le_natCast.mp (hle p)

end PetriNet
