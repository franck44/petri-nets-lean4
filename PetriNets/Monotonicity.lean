/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Reachability

/-!
# Monotonicity of weighted P/T nets

Provides monotonicity results for enabled transitions, firings, firing
sequences, and reachability with respect to the pointwise order on markings.

For two markings, `m₁ ≤ m₂` means that `m₁ p ≤ m₂ p` for every place `p`.
Adding tokens cannot disable a transition. Consequently, an executable firing
sequence remains executable after adding the same marking to its source and
target.
-/

@[expose] public section

namespace PetriNet

variable {P T : Type*} {net : WeightedNet P T}

/-! ## One-step monotonicity -/

/-- A transition enabled at a marking remains enabled at any pointwise larger
marking. -/
theorem WeightedNet.Enabled.mono {m₁ m₂ : Marking P} {t : T}
    (h : net.Enabled m₁ t) (hle : m₁ ≤ m₂) :
    net.Enabled m₂ t := by
  intro p
  exact (h p).trans (hle p)

/-- If `t` fires from `m` to `m'`, then for any additional marking, or token
budget, `d`, the transition also fires from `m + d` to `m' + d`.

```text
m   ──t──▶ m'
│          │
+ d        + d
▼          ▼
m+d ──t──▶ m'+d
```

The proof uses enabledness monotonicity and checks the firing equation
pointwise. -/
theorem WeightedNet.Fires.add {m m' : Marking P} {t : T}
    (h : net.Fires m t m') (d : Marking P) :
    net.Fires (m + d) t (m' + d) := by
  constructor
  · have hle: m ≤ m + d := by simp
    exact WeightedNet.Enabled.mono h.left hle
  · intro p
    have hfire : m' p = m p - net.pre p t + net.post p t := by
      simpa using h.right p
    have henabled := h.left p
    /- Use pointwise addition at `p`. -/
    change m' p + d p = (m p + d p) - net.pre p t + net.post p t
    omega

/-! ## Firing-sequence monotonicity -/

/-- Extend `WeightedNet.Fires.add` to firing sequences: if `ts` fires from
`src` to `tgt`, then for any additional marking `d`, `ts` also fires from
`src + d` to `tgt + d`.

The empty case is immediate. In the nonempty case, apply
`WeightedNet.Fires.add` to the first firing and the induction hypothesis to
the remaining sequence. -/
theorem WeightedNet.FiresSequence.add {src tgt : Marking P} {ts : List T}
    (h : net.FiresSequence src ts tgt) (d : Marking P) :
    net.FiresSequence (src + d) ts (tgt + d) := by
  induction h with
  | nil src =>
      exact WeightedNet.FiresSequence.nil (src + d)
  | cons head tail ih =>
      exact WeightedNet.FiresSequence.cons (WeightedNet.Fires.add head d) ih

/-- A firing sequence can be replayed from any pointwise larger source. The
target is shifted by the additional marking `largerSrc - src`.

This follows directly from `WeightedNet.FiresSequence.add`: apply it with the
additional marking `largerSrc - src`, and use
`src + (largerSrc - src) = largerSrc`.

```text
src       ──ts──▶ tgt
│                   │
+ (largerSrc-src)   + (largerSrc-src)
▼                   ▼
largerSrc ──ts──▶ tgt + (largerSrc-src)
``` -/
theorem WeightedNet.FiresSequence.mono
    {src tgt largerSrc : Marking P} {ts : List T}
    (h : net.FiresSequence src ts tgt) (hle : src ≤ largerSrc) :
    net.FiresSequence largerSrc ts (tgt + (largerSrc - src)) := by
  have hsrc : src + (largerSrc - src) = largerSrc := by
    funext p
    exact Nat.add_sub_of_le (hle p)
  have hshifted := h.add (largerSrc - src)
  rw [hsrc] at hshifted
  exact hshifted

/-! ## Repeating and combining firing sequences -/

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
  exact hseq.mono hle

/-- The arithmetic identity joining consecutive budget-backed repetitions.
At every place, `src - tgt` is the loss and `tgt - src` is the gain of one
execution. -/
theorem Marking.budget_join (src tgt : Marking P) (n : ℕ) :
    tgt + (n + 1) • (src - tgt) =
      (src + n • (src - tgt)) + (tgt - src) := by
  funext p
  have hparts : tgt p + (src p - tgt p) =
      src p + (tgt p - src p) := by omega
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Nat.add_mul]
  omega

/-- **Repeat a firing sequence with a budget.** An arbitrary firing sequence
can be repeated an arbitrary number of times by supplying enough initial tokens
at every place which it decreases.

Let `loss = src - tgt` and `gain = tgt - src`, both pointwise. These are the
negative and positive parts of the effect of a sequence of transitions `ts`.
Starting with `n` copies of `loss` as a budget allows `n + 1` repetitions;
the final marking contains the original target plus `n` copies of `gain`:

```text
src + n·loss ─────────────ts^(n+1)────────────▶ tgt + n·gain

inductive step:
src + (n+1)·loss ──ts──▶ tgt + (n+1)·loss
                              = src + n·loss + gain
                        ──ts^(n+1)──▶ tgt + (n+1)·gain
```

The loss and gain are respectively the negative and positive parts of the
same marking change. Consequently,

```text
tgt + loss = src + gain.
```

Adding `n` further copies of `loss` to both sides gives the identity that
makes the target of the first shifted execution equal to the source of the
remaining shifted repetitions:

```text
tgt + (n+1)·loss = (src + n·loss) + gain.
```

No hypothesis `src ≤ tgt` is required. The repeated execution instead starts
at `src + n • loss`, rather than at `src` itself. An application must
separately show that this enlarged source is available or covered by a
reachable marking. -/
theorem WeightedNet.FiresSequence.repeat_with_budget
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
      have hfirst := hseq.add ((n + 1) • loss)
      have htail := ih.add gain
      have hjoin : tgt + (n + 1) • loss =
          (src + n • loss) + gain := by
        simpa [loss, gain] using Marking.budget_join src tgt n
      rw [hjoin] at hfirst
      have hall := WeightedNet.FiresSequence.append hfirst htail
      convert hall using 1
      · simp [List.replicate_succ]
      · funext p
        simp [gain, Pi.add_apply, Nat.add_mul, Nat.add_assoc]

/-- **Meet a common bound by budget-backed repetition.** Suppose `ts` strictly
increases every place in the finite set `A`. Repeating it with `bound` copies
of the loss as a budget produces a marking containing at least `bound` tokens
at every place in `A`.

The sequence may decrease at places outside `A`; the initial marking
`src + bound • (src - tgt)` contains the budget needed to pay for those
losses. At each `p ∈ A`, the gain `tgt p - src p` is at least one, so `bound`
repetitions add at least `bound` tokens there. The resulting marking is also
pointwise above `tgt`.

```text
src + bound·(src - tgt)
          │
          │  ts repeated bound + 1 times
          ▼
tgt + bound·(tgt - src) = reached
          ▲
          │  tgt ≤ reached
          │  bound ≤ reached(p)  for every p ∈ A
```

As with `repeat_with_budget`, this theorem constructs a firing sequence from
an enlarged source; it does not by itself prove that this source is reachable.
In the Karp–Miller soundness proof, omega coverability will supply a reachable
marking covering the required budget. -/
theorem WeightedNet.FiresSequence.repeat_with_budget_ge_on
    {src tgt : Marking P} {ts : List T}
    (A : Finset P) (bound : ℕ)
    (hseq : net.FiresSequence src ts tgt)
    (hgrows : ∀ p ∈ A, src p < tgt p) :
    net.FiresSequence
        (src + bound • (src - tgt))
        (List.replicate (bound + 1) ts).flatten
        (tgt + bound • (tgt - src)) ∧
      tgt ≤ tgt + bound • (tgt - src) ∧
      ∀ p ∈ A, bound ≤ (tgt + bound • (tgt - src)) p := by
  refine ⟨hseq.repeat_with_budget bound, by simp, ?_⟩
  intro p hp
  have hgain : 0 < (tgt - src) p :=
    Nat.sub_pos_of_lt (hgrows p hp)
  change bound ≤ tgt p + bound * (tgt p - src p)
  exact (Nat.le_mul_of_pos_right bound hgain).trans
    (Nat.le_add_left (bound * (tgt p - src p)) (tgt p))

/-- Meet a separate bound at each place by choosing their sum as a common
bound and applying `repeat_with_budget_ge_on`. -/
theorem WeightedNet.FiresSequence.repeat_with_budget_ge_on_each
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
  obtain ⟨hrepeated, hmono, hbound⟩ :=
    hseq.repeat_with_budget_ge_on A n hgrows
  refine ⟨hrepeated, hmono, ?_⟩
  intro p hp
  have hle : bound p ≤ n := by
    dsimp [n]
    exact Finset.single_le_sum (fun q _ => Nat.zero_le (bound q)) hp
  exact hle.trans (hbound p hp)

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

Suppose that, for every `p ∈ A`, some sequence `tsₚ` takes a marking `srcₚ`
to a common endpoint `base`, with `srcₚ ≤ base` and
`srcₚ p < base p` (strict increase at `p`).

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
`base`, and `srcᵢ ≤ base`.

The sequences associated with the different places may be concatenated in any
order.

The proof is by induction on the size of `A`. -/
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

/-! ## Reachability monotonicity -/

/-- Extend `WeightedNet.FiresSequence.add` to reachability: if `tgt` is
reachable from `src`, then `tgt + d` is reachable from `src + d` for any
additional marking `d`.

The same transition sequence witnesses both reachability statements. -/
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
