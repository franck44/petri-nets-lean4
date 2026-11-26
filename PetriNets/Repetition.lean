/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Monotonicity

/-!
# Budgeted repetition of firing sequences

Provides loss budgets for repeating firing sequences and meeting token
bounds at selected places.
-/

@[expose] public section

namespace PetriNet

variable {P T : Type*} {net : WeightedNet P T}

/-! ## Repetition with a loss budget -/

/-- `Marking.GrowsOnWithBudget src tgt budget A` compares two markings
place by place. Every place in `A` must gain tokens. At any place outside of A
where the token count may decrease, the decrease must be at most `budget p`, so
overall `src p ≤ tgt p + budget p`, i.e src ≤ tgt + budget.

For example, going from `(2, 5)` to `(3, 3)` grows the first place and
loses two tokens at the second. For `A` containing only the first place,
`(0, 2)` is a sufficient budget.

The canonical budget is `src - tgt`. A zero budget recovers `GrowsOn`. -/
def Marking.GrowsOnWithBudget
    (src tgt budget : Marking P) (A : Finset P) : Prop :=
  src ≤ tgt + budget ∧ ∀ p ∈ A, src p < tgt p

/-- A zero loss budget is equivalent to global non-decrease. -/
@[simp]
theorem Marking.growsOnWithBudget_zero
    (src tgt : Marking P) (A : Finset P) :
    Marking.GrowsOnWithBudget src tgt 0 A ↔
      Marking.GrowsOn src tgt A := by
  simp [Marking.GrowsOnWithBudget, Marking.GrowsOn]

/-- If every place in `A` gains tokens from `src` to `tgt`, then the
difference `src - tgt` is a sufficient loss budget.

At a place that loses tokens, the budget is exactly the number lost.
At a place that stays the same or gains tokens, natural-number subtraction
gives zero. Adding the budget to `tgt` therefore gives a marking at least
as large as `src`. -/
theorem Marking.growsOnWithBudget_sub
    (src tgt : Marking P) (A : Finset P)
    (hstrict : ∀ p ∈ A, src p < tgt p) :
    Marking.GrowsOnWithBudget src tgt (src - tgt) A := by
  refine ⟨?_, hstrict⟩
  intro p
  simp only [Pi.add_apply, Pi.sub_apply]
  omega

/-- The sequence `ts` fires from `src` to `tgt`. Every place in `A`
gains tokens, and any decrease at a place `p` is at most `budget p`.
The budget bounds the net loss between the endpoints of the sequence. -/
def WeightedNet.FiresSequence.GrowsOnWithBudget (net : WeightedNet P T)
    (src : Marking P) (ts : List T) (tgt budget : Marking P)
    (A : Finset P) : Prop :=
  net.FiresSequence src ts tgt ∧
    Marking.GrowsOnWithBudget src tgt budget A

/-- If firing `ts` from `src` to `tgt` increases the token count at every
place in `A`, then `src - tgt` is a sufficient loss budget for the sequence.
It records the number of tokens lost at each decreasing place. -/
theorem WeightedNet.FiresSequence.growsOnWithBudget_sub
    {src tgt : Marking P} {ts : List T} (A : Finset P)
    (hseq : net.FiresSequence src ts tgt)
    (hstrict : ∀ p ∈ A, src p < tgt p) :
    WeightedNet.FiresSequence.GrowsOnWithBudget
      net src ts tgt (src - tgt) A := by
  exact ⟨hseq, Marking.growsOnWithBudget_sub src tgt A hstrict⟩

/-- Let `loss = src - tgt` and `gain = tgt - src`, computed pointwise
using natural-number subtraction. At each place, `tgt + loss` and
`src + gain` both give the larger of the two original token counts.
Adding `n • loss` to both sides gives the stated identity. -/
private theorem Marking.repeat_add_budget (src tgt : Marking P) (n : ℕ) :
    tgt + (n + 1) • (src - tgt) =
      (src + n • (src - tgt)) + (tgt - src) := by
  funext p
  have hparts : tgt p + (src p - tgt p) =
      src p + (tgt p - src p) := by omega
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Nat.add_mul]
  omega

/-- If `ts` fires from `src` to `tgt`, it can fire `n + 1` times
from `src + n • loss` and reach `tgt + n • gain`, where
`loss = src - tgt` and `gain = tgt - src` are computed pointwise.

Every execution of `ts` has the same net effect. The original source
already enables one execution, so the extra budget only needs to cover
the losses of the other `n` executions. The original target already
includes the gain from one execution, so the final marking adds the
gain from the other `n`.

For example, suppose `ts` takes `(5, 2)` to `(3, 3)`. Each execution
loses two tokens at the first place and gains one at the second. To
fire `ts` three times, add four tokens at the first place:

```text
(9, 2) ──ts──▶ (7, 3) ──ts──▶ (5, 4) ──ts──▶ (3, 5)
```

After the first execution, `(7, 3) = (5, 2) + (2, 0) + (0, 1)`.
The marking consists of the original source, the remaining loss budget,
and the gain so far. The identity `repeat_add_budget` gives this
decomposition in general so the remaining executions can start there. -/
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
        simpa [loss, gain] using Marking.repeat_add_budget src tgt n
      rw [hjoin] at hfirst
      have hall := WeightedNet.FiresSequence.append hfirst htail
      convert hall using 1
      · simp [List.replicate_succ]
      · funext p
        simp [gain, Pi.add_apply, Nat.add_mul, Nat.add_assoc]

/-- If the effect from `src` to `tgt` gains at least one token at `p`,
then repeating that effect `n + 1` times gains at least `n + 1` tokens
at `p` relative to the budgeted source.

The loss `src p - tgt p` is zero, so the budgeted source starts with
`src p` tokens at `p`. The repeated effect ends with `tgt p` plus
`n` times the gain `tgt p - src p`. -/
theorem Marking.repeat_with_budget_gain_at
    {src tgt : Marking P} {p : P} (hp : src p < tgt p) (n : ℕ) :
    (src + n • (src - tgt)) p + (n + 1) ≤
      (tgt + n • (tgt - src)) p := by
  change src p + n * (src p - tgt p) + (n + 1) ≤
    tgt p + n * (tgt p - src p)
  have hgain := Nat.le_mul_of_pos_right n (Nat.sub_pos_of_lt hp)
  rw [Nat.sub_eq_zero_of_le hp.le, Nat.mul_zero, Nat.add_zero]
  omega

/-- If firing `ts` takes `src` to `tgt` and strictly increases every
place in `A`, firing it once and then repeating it `n` more times
reaches at least `n` tokens at each place in `A`.

The extra budget `n • (src - tgt)` pays for the losses of the `n`
repetitions. Each repetition gains at least one token at every place in
`A`, and the final marking `tgt + n • (tgt - src)` also covers `tgt`. -/
theorem WeightedNet.FiresSequence.repeat_with_budget_ge_on
    {src tgt : Marking P} {ts : List T}
    (A : Finset P) (n : ℕ)
    (hseq : net.FiresSequence src ts tgt)
    (hgrows : ∀ p ∈ A, src p < tgt p) :
    let repeatTs := (List.replicate (n + 1) ts).flatten
    let tgtAfterNPlusOne := tgt + n • (tgt - src)
    net.FiresSequence (src + n • (src - tgt)) repeatTs tgtAfterNPlusOne ∧
      tgt ≤ tgtAfterNPlusOne ∧
      ∀ p ∈ A, n ≤ tgtAfterNPlusOne p := by
  dsimp only
  refine ⟨hseq.repeat_with_budget n, by simp, ?_⟩
  intro p hp
  have hgain : 0 < (tgt - src) p :=
    Nat.sub_pos_of_lt (hgrows p hp)
  change n ≤ tgt p + n * (tgt p - src p)
  exact (Nat.le_mul_of_pos_right n hgain).trans
    (Nat.le_add_left (n * (tgt p - src p)) (tgt p))

/-- If firing `ts` strictly increases every place in `A`, we can repeat it
to meet a separate token bound `bound p` at each place `p ∈ A`.

Let `n` be the sum of these bounds, so `bound p ≤ n` for every `p ∈ A`.
With the extra loss budget `n • (src - tgt)`, fire `ts` once and then
repeat it `n` more times. The resulting sequence `repeatTs` reaches
`tgtAfterNPlusOne`, which covers `tgt` and has at least `bound p` tokens
at every place `p ∈ A`. -/
theorem WeightedNet.FiresSequence.repeat_with_budget_ge_on_each
    {src tgt : Marking P} {ts : List T}
    (A : Finset P) (bound : P → ℕ)
    (hseq : net.FiresSequence src ts tgt)
    (hgrows : ∀ p ∈ A, src p < tgt p) :
    let n := ∑ p ∈ A, bound p
    let repeatTs := (List.replicate (n + 1) ts).flatten
    let tgtAfterNPlusOne := tgt + n • (tgt - src)
    net.FiresSequence (src + n • (src - tgt)) repeatTs tgtAfterNPlusOne ∧
      tgt ≤ tgtAfterNPlusOne ∧
      ∀ p ∈ A, bound p ≤ tgtAfterNPlusOne p := by
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

end PetriNet
