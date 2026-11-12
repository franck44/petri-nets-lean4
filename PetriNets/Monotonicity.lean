/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Reachability

/-!
# Monotonicity of weighted P/T nets

This module develops monotonicity properties with respect to the pointwise
order on markings. In particular, adding tokens to a place cannot disable a transition.
-/

@[expose] public section

namespace PetriNet

/-- A transition enabled at a marking remains enabled at any (point-wise) larger marking.
The proof is to unfold the definition of `Enabled` and use the point-wise order on markings.
-/
theorem WeightedNet.Enabled.mono {P T : Type*} {net : WeightedNet P T}
    {m₁ m₂ : Marking P} {t : T} (h : net.Enabled m₁ t) (hle : m₁ ≤ m₂) :
    net.Enabled m₂ t := by
  intro p
  exact (h p).trans (hle p)

/-- If `t` fires from `m` to `m'`, then for any additional marking `d`, `t`
also fires from `m + d` to `m' + d`.
The proof splits the two conditions of `Fires`: first, the transition must be enabled at the new marking `m + d`, which follows from monotonicity; second, the resulting marking `m' + d` must satisfy the firing equation, which is verified by simple arithmetic.
-/
theorem WeightedNet.Fires.add {P T : Type*} {net : WeightedNet P T}
    {m m' : Marking P} {t : T} (h : net.Fires m t m') (d : Marking P) :
    net.Fires (m + d) t (m' + d) := by
  constructor
  · have hle: m ≤ m + d := by simp
    exact WeightedNet.Enabled.mono h.left hle
  · intro p
    have hfire := h.right p
    have henabled := h.left p
    /- use point-wise addition (m' + d) p = m' p + d p and (m + d) p = m p + d p -/
    change m' p + d p = (m p + d p) - net.pre p t + net.post p t
    omega

/-- Extend `WeightedNet.Fires.add` to firing sequences: if `ts` fires from
`src` to `tgt`, then for any additional marking `d`, `ts` also fires from
`src + d` to `tgt + d`.

The proof is: nil case, it must the case that tgt = src, and adding d to both sides preserves the equality; cons case, apply `WeightedNet.Fires.add` to the head and use the induction hypothesis on the tail.
-/
theorem WeightedNet.FiresSequence.add {P T : Type*} {net : WeightedNet P T}
    {src tgt : Marking P} {ts : List T}
    (h : net.FiresSequence src ts tgt) (d : Marking P) :
    net.FiresSequence (src + d) ts (tgt + d) := by
  induction h with
  | nil src =>
      exact WeightedNet.FiresSequence.nil (src + d)
  | cons head tail ih =>
      exact WeightedNet.FiresSequence.cons (WeightedNet.Fires.add head d) ih

/-- Extend `WeightedNet.FiresSequence.add` to reachability: if `tgt` is
reachable from `src`, then `tgt + d` is reachable from `src + d` for any
additional marking `d`.
The proof is to get a witness sequence of transitions `ts` that witnesses the reachability from `src` to `tgt`, and then apply `WeightedNet.FiresSequence.add` to show that the same sequence witnesses the reachability from `src + d` to `tgt + d`.
-/
theorem WeightedNet.Reachable.add {P T : Type*} {net : WeightedNet P T}
    {src tgt : Marking P} (h : net.Reachable src tgt) (d : Marking P) :
    net.Reachable (src + d) (tgt + d) := by
  rcases h with ⟨ts, hts⟩
  have hts_add := WeightedNet.FiresSequence.add hts d
  use ts

end PetriNet
