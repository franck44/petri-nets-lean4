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

variable {P T : Type*} {net : WeightedNet P T}

/-- A transition enabled at a marking remains enabled at any (point-wise) larger marking.
The proof is to unfold the definition of `Enabled` and use the point-wise order on markings.
-/
theorem WeightedNet.Enabled.mono {m₁ m₂ : Marking P} {t : T}
    (h : net.Enabled m₁ t) (hle : m₁ ≤ m₂) :
    net.Enabled m₂ t := by
  intro p
  exact (h p).trans (hle p)

/-- If `t` fires from `m` to `m'`, then for any additional marking `d`, `t`
also fires from `m + d` to `m' + d`.
The proof splits the two conditions of `Fires`: first, the transition must be enabled at the new marking `m + d`, which follows from monotonicity; second, the resulting marking `m' + d` must satisfy the firing equation, which is verified by simple arithmetic.
-/
theorem WeightedNet.Fires.add {m m' : Marking P} {t : T}
    (h : net.Fires m t m') (d : Marking P) :
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
theorem WeightedNet.FiresSequence.add {src tgt : Marking P} {ts : List T}
    (h : net.FiresSequence src ts tgt) (d : Marking P) :
    net.FiresSequence (src + d) ts (tgt + d) := by
  induction h with
  | nil src =>
      exact WeightedNet.FiresSequence.nil (src + d)
  | cons head tail ih =>
      exact WeightedNet.FiresSequence.cons (WeightedNet.Fires.add head d) ih

/-- A nondecreasing firing sequence can be fired again from its target, and
the second firing adds the same marking difference as the first.

If `ts` takes `src` to `tgt` and `src ≤ tgt`, the additional marking
`tgt - src` supplies the difference between the two markings. Monotonicity
therefore shifts the original execution from `src` to `tgt` and gives the
exact next target.

```text
src ──ts──▶ tgt ──ts──▶ tgt + (tgt - src)
``` -/
theorem WeightedNet.FiresSequence.fire_again
    {src tgt : Marking P} {ts : List T}
    (hseq : net.FiresSequence src ts tgt) (hle : src ≤ tgt) :
    net.FiresSequence tgt ts (tgt + (tgt - src)) := by
  let d : Marking P := tgt - src
  have htgt : tgt = src + d := by
    funext p
    change tgt p = src p + (tgt p - src p)
    exact (Nat.add_sub_of_le (hle p)).symm
  change net.FiresSequence tgt ts (tgt + d)
  convert hseq.add d using 1

/-- **Pumping a nondecreasing firing sequence.** Suppose `ts` takes `src` to
`tgt` and `src ≤ tgt`. Let `d = tgt - src` be the nonnegative effect of the
sequence. Repeating `ts` exactly `n` times takes `src` to `src + n • d`.

```text
src --ts--> src + d --ts--> src + 2d --ts--> ... --ts--> src + nd
```

Each repetition is enabled by `FiresSequence.add`, because it starts with the
tokens produced by the preceding repetitions. -/
theorem WeightedNet.FiresSequence.pump {src tgt : Marking P} {ts : List T}
    (hseq : net.FiresSequence src ts tgt) (hle : src ≤ tgt) (n : ℕ) :
    net.FiresSequence src (List.replicate n ts).flatten
      (src + n • (tgt - src)) := by
  induction n generalizing src tgt with
  | zero =>
      simp
      exact WeightedNet.FiresSequence.nil src
  | succ n ih =>
      let d : Marking P := tgt - src
      have hagain : net.FiresSequence tgt ts (tgt + d) := by
        exact hseq.fire_again hle
      have hle' : tgt ≤ tgt + d := by simp
      have htail := ih hagain hle'
      have hall := WeightedNet.FiresSequence.append hseq htail
      convert hall using 1
      · simp [List.replicate_succ]
      · funext p
        simp [d, Pi.add_apply, Nat.add_mul]
        rw [add_comm (n * (tgt p - src p)) (tgt p - src p),
          ← Nat.add_assoc, Nat.add_sub_of_le (hle p)]

/-- If a nondecreasing firing sequence strictly increases place `p`, then
markings with arbitrarily many tokens at `p` are reachable from its source.
The reachable witnesses are obtained by pumping the sequence. -/
theorem WeightedNet.FiresSequence.exists_reachable_ge_at
    {src tgt : Marking P} {ts : List T} {p : P}
    (hseq : net.FiresSequence src ts tgt) (hle : src ≤ tgt)
    (hlt : src p < tgt p) (k : ℕ) :
    ∃ m, net.Reachable src m ∧ k ≤ m p := by
  let d : Marking P := tgt - src
  let m := src + k • d
  have hpump := hseq.pump hle k
  have hdp : 0 < d p := by
    exact Nat.sub_pos_of_lt hlt
  have hk : k ≤ m p := by
    dsimp [m]
    exact (Nat.le_mul_of_pos_right k hdp).trans
      (Nat.le_add_left (k * d p) (src p))
  exact ⟨m, ⟨(List.replicate k ts).flatten, hpump⟩, hk⟩

/-- Extend `WeightedNet.FiresSequence.add` to reachability: if `tgt` is
reachable from `src`, then `tgt + d` is reachable from `src + d` for any
additional marking `d`.
The proof is to get a witness sequence of transitions `ts` that witnesses the reachability from `src` to `tgt`, and then apply `WeightedNet.FiresSequence.add` to show that the same sequence witnesses the reachability from `src + d` to `tgt + d`.
-/
theorem WeightedNet.Reachable.add {src tgt : Marking P}
    (h : net.Reachable src tgt) (d : Marking P) :
    net.Reachable (src + d) (tgt + d) := by
  rcases h with ⟨ts, hts⟩
  have hts_add := WeightedNet.FiresSequence.add hts d
  use ts

/-- Reachability is monotonic with respect to the pointwise order on markings:
if `m₁ ≤ m₂` and `m₁'` is reachable from `m₁`, then there is an `m₂'`
reachable from `m₂` such that `m₁' ≤ m₂'`.

For the proof, let `d = m₂ - m₁`. The assumption `m₁ ≤ m₂` gives
`m₁ + d = m₂` pointwise. By `WeightedNet.Reachable.add`, `m₁' + d` is
reachable from `m₁ + d = m₂`. Finally, `m₁' ≤ m₁' + d` pointwise, so take
`m₂' = m₁' + d`.
-/
theorem WeightedNet.Reachable.mono {m₁ m₂ m₁' : Marking P}
    (hreach : net.Reachable m₁ m₁')
    (hle : m₁ ≤ m₂) :
    ∃ m₂', net.Reachable m₂ m₂' ∧ m₁' ≤ m₂' := by
  let d : Marking P := m₂ - m₁
  have hsrc : m₁ + d = m₂ := by
    funext p
    change m₁ p + (m₂ p - m₁ p) = m₂ p
    exact Nat.add_sub_of_le (hle p)
  have hreach_add := WeightedNet.Reachable.add hreach d
  rw [hsrc] at hreach_add
  have htgt_le : m₁' ≤ m₁' + d := by
    intro p
    simp
  use m₁' + d

end PetriNet
