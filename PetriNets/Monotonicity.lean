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

/-- Combine two firing sequences by supplying each with the marking required
by the other.

If `ts₁` fires from `src₁` to `tgt₁` and `ts₂` fires from `src₂` to
`tgt₂`, adding `src₂` to the first execution makes it end at
`tgt₁ + src₂`. The second execution can then start there after adding
`tgt₁` to both its endpoints:

```text
src₁ + src₂ ──ts₁──▶ tgt₁ + src₂
                         = src₂ + tgt₁ ──ts₂──▶ tgt₂ + tgt₁
```

Thus the concatenated sequence has the sum of the two sources as its source
and the sum of the two targets as its target. No nondecreasing hypothesis is
required: the added markings act as reserves for the two executions. -/
theorem WeightedNet.FiresSequence.append_add
    {src₁ tgt₁ src₂ tgt₂ : Marking P} {ts₁ ts₂ : List T}
    (h₁ : net.FiresSequence src₁ ts₁ tgt₁)
    (h₂ : net.FiresSequence src₂ ts₂ tgt₂) :
    net.FiresSequence (src₁ + src₂) (ts₁ ++ ts₂) (tgt₁ + tgt₂) := by
  have hfirst := h₁.add src₂
  have hsecond := h₂.add tgt₁
  rw [add_comm src₂ tgt₁] at hsecond
  have hcombined := WeightedNet.FiresSequence.append hfirst hsecond
  simpa [add_comm tgt₂ tgt₁] using hcombined

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

/-- **Repeat a firing sequence with reserve.** An arbitrary firing sequence
can be repeated by supplying enough initial tokens at every place which it
decreases.

Let `loss = src - tgt` and `gain = tgt - src`, both pointwise. These are the
negative and positive parts of the effect of `ts`. Starting with `n` copies
of `loss` in reserve allows `n + 1` repetitions; the final marking contains
the original target plus `n` copies of `gain`:

```text
src + n·loss ─────────────ts^(n+1)────────────▶ tgt + n·gain

inductive step:
src + (n+1)·loss ──ts──▶ tgt + (n+1)·loss
                              = src + n·loss + gain
                        ──ts^(n+1)──▶ tgt + (n+1)·gain
```

At each place, either `loss` or `gain` is zero. This gives the pointwise
identity which joins the first firing to the remaining repetitions:

```text
tgt + (n+1)·loss = (src + n·loss) + gain.
```

Unlike `FiresSequence.pump`, no hypothesis `src ≤ tgt` is required. The price
is that the repeated execution starts at `src + n • loss`, not at `src`
itself. A later application must separately show that this enlarged source is
available or covered by a reachable marking. -/
theorem WeightedNet.FiresSequence.repeat_with_reserve
    {src tgt : Marking P} {ts : List T}
    (hseq : net.FiresSequence src ts tgt) (n : ℕ) :
    net.FiresSequence
      (src + n • (src - tgt))
      (List.replicate (n + 1) ts).flatten
      (tgt + n • (tgt - src)) := by
  induction n with
  | zero => simpa using hseq
  | succ n ih =>
      let loss : Marking P := src - tgt
      let gain : Marking P := tgt - src
      /- Pay for the first repetition with all `n + 1` remaining copies of
      the loss. -/
      have hfirst := hseq.add ((n + 1) • loss)
      /- Shift the induction hypothesis by one copy of the gain. -/
      have htail := ih.add gain
      have hjoin : tgt + (n + 1) • loss =
          (src + n • loss) + gain := by
        funext p
        by_cases hle : src p ≤ tgt p
        · have hloss : src p - tgt p = 0 := Nat.sub_eq_zero_of_le hle
          simp [loss, gain, Pi.add_apply, hloss]
          omega
        · have hle' : tgt p ≤ src p := Nat.le_of_not_ge hle
          have hgain : tgt p - src p = 0 := Nat.sub_eq_zero_of_le hle'
          simp [loss, gain, Pi.add_apply, hgain, Nat.add_mul]
          omega
      rw [hjoin] at hfirst
      have hall := WeightedNet.FiresSequence.append hfirst htail
      convert hall using 1
      · simp [List.replicate_succ]
      · funext p
        simp [gain, Pi.add_apply, Nat.add_mul, Nat.add_assoc]

/-- **Meet finitely many bounds by reserve-backed repetition.** Suppose `ts`
strictly increases every place in the finite set `A`. Then the execution
provided by `repeat_with_reserve` can simultaneously exceed an arbitrary
prescribed `bound` at all places in `A`.

The sequence may decrease at places outside `A`; the initial marking
`src + n • (src - tgt)` contains the reserve needed to pay for those losses.
At each `p ∈ A`, the gain `tgt p - src p` is at least one. Choosing

```text
n = ∑ p ∈ A, bound p
```

therefore makes `n` at least every individual bound and adds at least `n`
tokens at each growing place. The resulting marking is also pointwise above
`tgt`, because it is exactly `tgt + n • (tgt - src)`.

```text
src + n·(src - tgt)
          │
          │  ts repeated n + 1 times
          ▼
tgt + n·(tgt - src) = reached
          ▲
          │  tgt ≤ reached
          │  bound(p) ≤ reached(p)  for every p ∈ A
```

As with `repeat_with_reserve`, this theorem constructs a firing sequence from
an enlarged source; it does not by itself prove that this source is reachable.
In the Karp–Miller soundness proof, omega coverability will supply a reachable
marking covering the required reserve. -/
theorem WeightedNet.FiresSequence.repeat_with_reserve_ge_on
    {src tgt : Marking P} {ts : List T}
    (A : Finset P) (bound : P → ℕ)
    (hseq : net.FiresSequence src ts tgt)
    (hgrows : ∀ p ∈ A, src p < tgt p) :
    let n := ∑ p ∈ A, bound p
    net.FiresSequence
        (src + n • (src - tgt))
        (List.replicate (n + 1) ts).flatten
        (tgt + n • (tgt - src)) ∧
      tgt ≤ tgt + n • (tgt - src) ∧
      ∀ p ∈ A, bound p ≤ (tgt + n • (tgt - src)) p := by
  dsimp only
  let n := ∑ p ∈ A, bound p
  refine ⟨hseq.repeat_with_reserve n, by simp, ?_⟩
  intro p hp
  have hbound : bound p ≤ n := by
    dsimp [n]
    exact Finset.single_le_sum (fun q _ => Nat.zero_le (bound q)) hp
  have hgain : 0 < (tgt - src) p :=
    Nat.sub_pos_of_lt (hgrows p hp)
  have hn : n ≤ (tgt + n • (tgt - src)) p := by
    change n ≤ tgt p + n * (tgt p - src p)
    exact (Nat.le_mul_of_pos_right n hgain).trans
      (Nat.le_add_left (n * (tgt p - src p)) (tgt p))
  exact hbound.trans hn

/-- If a nondecreasing firing sequence strictly increases every place in a
finite set `A`, then one reachable marking can simultaneously exceed an
arbitrary prescribed `bound` at every place in `A`.

The resulting marking also remains above `src`; this is useful for places
outside `A`, for which no strict-growth hypothesis is available.

The proof chooses the number of repetitions to be the sum of all prescribed
bounds. This number is at least each individual bound. Since the sequence
adds at least one token at every place in `A` on each repetition, the marking
provided by `FiresSequence.pump` satisfies all the bounds at once. -/
theorem WeightedNet.FiresSequence.exists_reachable_ge_on
    {src tgt : Marking P} {ts : List T} (A : Finset P) (bound : P → ℕ)
    (hseq : net.FiresSequence src ts tgt) (hle : src ≤ tgt)
    (hgrows : ∀ p ∈ A, src p < tgt p) :
    ∃ m, net.Reachable src m ∧ src ≤ m ∧
      ∀ p ∈ A, bound p ≤ m p := by
  let n := ∑ p ∈ A, bound p
  let d : Marking P := tgt - src
  let m := src + n • d
  have hpump := hseq.pump hle n
  refine ⟨m, ⟨(List.replicate n ts).flatten, hpump⟩, by simp [m], ?_⟩
  intro p hp
  have hbound : bound p ≤ n := by
    dsimp [n]
    exact Finset.single_le_sum (fun q _ => Nat.zero_le (bound q)) hp
  have hdp : 0 < d p := Nat.sub_pos_of_lt (hgrows p hp)
  have hn : n ≤ m p := by
    dsimp [m]
    exact (Nat.le_mul_of_pos_right n hdp).trans
      (Nat.le_add_left (n * d p) (src p))
  exact hbound.trans hn

/-- **Shift finitely many growth paths to a common endpoint.**

Suppose every `p ∈ A` has a firing sequence with its own source and endpoint,
such that the sequence is nondecreasing and strictly increases place `p`:

```text
srcₚ ──tsₚ──▶ endₚ       srcₚ ≤ endₚ       srcₚ(p) < endₚ(p)
```

Then all paths can be shifted to a single endpoint `base` while preserving
their non-strict and strict growth properties:

```text
shiftedSrc₁ ──ts₁──▶ ┐
shiftedSrc₂ ──ts₂──▶ ├── base
        ⋮             │
shiftedSrcᵣ ──tsᵣ──▶ ┘

shiftedSrcₚ ≤ base       shiftedSrcₚ(p) < base(p)
```

The proof constructs `base` as the pointwise maximum of the finitely many
endpoints. If `endₚ ≤ base`, adding `base - endₚ` to both ends of the path
changes its endpoint to exactly `base`:

```text
srcₚ + (base - endₚ) ──tsₚ──▶ endₚ + (base - endₚ) = base.
```

Adding the same marking preserves both `≤` and strict growth at `p`. -/
theorem WeightedNet.FiresSequence.exists_common_endpoint_growth
    (A : Finset P)
    (hpaths : ∀ p ∈ A, ∃ src tgt ts,
      net.FiresSequence src ts tgt ∧ src ≤ tgt ∧ src p < tgt p) :
    ∃ base, ∀ p ∈ A, ∃ src ts,
      net.FiresSequence src ts base ∧ src ≤ base ∧ src p < base p := by
  classical
  induction A using Finset.induction with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert p A hp ih =>
      obtain ⟨srcP, endP, tsP, hseqP, hleP, hltP⟩ :=
        hpaths p (by simp)
      obtain ⟨baseA, hbaseA⟩ := ih (by
        intro q hq
        exact hpaths q (by simp [hq]))
      let base : Marking P := endP ⊔ baseA
      have hendP : endP ≤ base := le_sup_left
      have hbaseA_le : baseA ≤ base := le_sup_right
      have shift {q : P} {src end_ : Marking P} {ts : List T}
          (hseq : net.FiresSequence src ts end_)
          (hle : src ≤ end_) (hlt : src q < end_ q)
          (hend : end_ ≤ base) :
          ∃ shiftedSrc,
            net.FiresSequence shiftedSrc ts base ∧
            shiftedSrc ≤ base ∧ shiftedSrc q < base q := by
        let d : Marking P := base - end_
        have hendEq : end_ + d = base := by
          funext r
          exact Nat.add_sub_of_le (hend r)
        refine ⟨src + d, ?_, ?_, ?_⟩
        · rw [← hendEq]
          exact hseq.add d
        · rw [← hendEq]
          exact fun r => Nat.add_le_add_right (hle r) (d r)
        · rw [← hendEq]
          exact Nat.add_lt_add_right hlt (d q)
      refine ⟨base, ?_⟩
      intro q hq
      rw [Finset.mem_insert] at hq
      rcases hq with rfl | hq
      · obtain ⟨shiftedSrc, hseq, hle, hlt⟩ :=
          shift hseqP hleP hltP hendP
        exact ⟨shiftedSrc, tsP, hseq, hle, hlt⟩
      · obtain ⟨srcQ, tsQ, hseqQ, hleQ, hltQ⟩ := hbaseA q hq
        obtain ⟨shiftedSrc, hseq, hle, hlt⟩ :=
          shift hseqQ hleQ hltQ hbaseA_le
        exact ⟨shiftedSrc, tsQ, hseq, hle, hlt⟩

/-- Combine finitely many pumpable segments ending at the same marking.

Suppose that, for every `p ∈ A`, some sequence ts_p takes a marking `src_p` to a common endpoint
`base` with `src_p ≤ base` and `src_p < base p` (strict increase at `p`).

```text
src₁ ──ts₁──▶ base       src₁ ≤ base,  src₁(p₁) < base(p₁)
src₂ ──ts₂──▶ base       src₂ ≤ base,  src₂(p₂) < base(p₂)
       ⋮
srcᵣ ──tsᵣ──▶ base       srcᵣ ≤ base,  srcᵣ(pᵣ) < base(pᵣ)
```
Then we can concatenate the sequences ts_p to obtain a firing sequence from `base` to a marking `tgt` that strictly grows at every place `p ∈ A`.
```text
                         replay shifted copies
base ──ts₁──▶ base + d₁ ──ts₂──▶ base + d₁ + d₂ ── ... ──tsᵣ──▶ tgt
       where dᵢ = base - srcᵢ
```

Moreover
```text
base ≤ tgt       and       base(p) < tgt(p) for every p ∈ A
```

Each replay is enabled by monotonicity because its current source is at least
`base`, and `base >= srcᵢ`.

There is no specific order required for the concatenation of the sequences corresponding to different places in `A`. Any combination works.

The proof is by induction on the size of the set `A`.
-/
theorem WeightedNet.FiresSequence.exists_combined_growth
    (base : Marking P) (A : Finset P)
    (hsegments : ∀ p ∈ A, ∃ src ts,
      net.FiresSequence src ts base ∧ src ≤ base ∧ src p < base p) :
    ∃ ts tgt,
      net.FiresSequence base ts tgt ∧
      base ≤ tgt ∧
      ∀ p ∈ A, base p < tgt p := by
  classical
  induction A using Finset.induction with
  | empty =>
      /- base -[empty sequence]-> base -/
      simp
      use [], base
      simp
      exact WeightedNet.FiresSequence.nil base
  | @insert p A hp ih =>
      obtain ⟨src, ts, hseq, hle, hpLt⟩ := hsegments p (by simp)
      obtain ⟨combined, tgt, hcombined, hbaseTgt, hstrict⟩ := ih (by
        intro q hq
        exact hsegments q (by simp [hq]))
      let d : Marking P := base - src
      have hpAgain : net.FiresSequence base ts (base + d) := by
        exact hseq.fire_again hle
      have hcombinedShifted :
          net.FiresSequence (base + d) combined (tgt + d) := by
        exact hcombined.add d
      have hpGrowth : base p < (tgt + d) p := by
        have hdp : 0 < d p := Nat.sub_pos_of_lt hpLt
        change base p < tgt p + d p
        exact (Nat.lt_add_of_pos_right hdp).trans_le
          (Nat.add_le_add_right (hbaseTgt p) (d p))
      refine ⟨ts ++ combined, tgt + d, hpAgain.append hcombinedShifted,
        ?_, ?_⟩
      · intro q
        exact (hbaseTgt q).trans (by simp)
      · intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · exact hpGrowth
        · have hqLt := hstrict q hq
          change base q < tgt q + d q
          omega

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
