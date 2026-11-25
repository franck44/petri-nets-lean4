/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.Reachability

/-!
# Monotonicity of weighted P/T nets

Provides monotonicity results for the pointwise order on markings.
Here `m₁ ≤ m₂` means `m₁ p ≤ m₂ p` for every place `p`.

* An enabled transition remains enabled at any larger marking.
* Adding the same tokens to both ends of a firing preserves that firing.
* A firing sequence can be replayed from a larger source, reaching a marking
  at least as large as its original target.
* Reachability is preserved when the same tokens are added to the source
  and target (`Reachable.add`).
* From a larger source, some reachable marking covers the original reachable
  target (`Reachable.mono`).

Later sections use these results to repeat firing sequences and combine
sequences that grow selected places.
-/

@[expose] public section

namespace PetriNet

variable {P T : Type*} {net : WeightedNet P T}

/-! ## One-step monotonicity -/

/-- A transition enabled at a marking remains enabled at any larger
marking. -/
theorem WeightedNet.Enabled.mono {m₁ m₂ : Marking P} {t : T}
    (h : net.Enabled m₁ t) (hle : m₁ ≤ m₂) :
    net.Enabled m₂ t := by
  intro p
  exact (h p).trans (hle p)

/-- If `t` fires from `m` to `m'`, then for any additional marking `d`,
the transition also fires from `m + d` to `m' + d`.

```text
m   ──t──▶ m'
│          │
+ d        + d
▼          ▼
m+d ──t──▶ m'+d
```
-/
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
 -/
theorem WeightedNet.FiresSequence.add {src tgt : Marking P} {ts : List T}
    (h : net.FiresSequence src ts tgt) (d : Marking P) :
    net.FiresSequence (src + d) ts (tgt + d) := by
  induction h with
  | nil src =>
      exact WeightedNet.FiresSequence.nil (src + d)
  | cons head tail ih =>
      exact WeightedNet.FiresSequence.cons (WeightedNet.Fires.add head d) ih

/-- A firing sequence can be replayed from any larger source. The
target is shifted by the additional marking `largerSrc - src`. -/
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

/-! ## Growth at places -/

/-- `src <[p] tgt` means that `tgt` is pointwise at least `src` and is
strictly larger at place `p`.

The value type is polymorphic, so the relation applies to any pointwise
ordered indexed family. In particular, it can be used with ordinary markings,
ω-markings, vectors represented by `Fin n → α`, and matrix rows. -/
def Marking.GrowsAt {α : Type*} [LE α] [LT α]
    (src tgt : P → α) (p : P) : Prop :=
  src ≤ tgt ∧ src p < tgt p

/-- Pointwise growth notation which is strict at the specified place. -/
notation:50 src " <[" p "] " tgt => Marking.GrowsAt src tgt p

/-- `Marking.GrowsOn src tgt A` means that `tgt` is pointwise at least
`src` and is strictly larger at every place in the finite set `A`.

Like `GrowsAt`, the relation is polymorphic in the value type. -/
def Marking.GrowsOn {α : Type*} [LE α] [LT α]
    (src tgt : P → α) (A : Finset P) : Prop :=
  src ≤ tgt ∧ ∀ p ∈ A, src p < tgt p

/-- Growth on a singleton set is growth at its unique place. -/
@[simp]
theorem Marking.growsOn_singleton {α : Type*} [LE α] [LT α]
    [DecidableEq P] (src tgt : P → α) (p : P) :
    Marking.GrowsOn src tgt {p} ↔ src <[p] tgt := by
  simp [Marking.GrowsOn, Marking.GrowsAt]

/-- A firing sequence which is nondecreasing and strictly grows every place
in `A`.

This packages the executable sequence together with the growth property used
when combining and repeating firing sequences. -/
def WeightedNet.FiresSequence.GrowsOn (net : WeightedNet P T)
    (src : Marking P) (ts : List T) (tgt : Marking P) (A : Finset P) : Prop :=
  net.FiresSequence src ts tgt ∧ Marking.GrowsOn src tgt A

/-! ## Replaying and repeating firing sequences -/

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

/-! ### Repetition with a loss budget -/

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

/-! ## Combining growth sequences -/

/-- Combine two firing sequences `σ₁` and `σ₂` starting at `src`.
Each leaves every place with at least its starting token count.
The sequence `σ₁` strictly increases every place in `A`, and
`σ₂` strictly increases the token count at `q`.

After firing `σ₁` to reach `grownA`, replay `σ₂` from `grownA`.
Since `src ≤ grownA`, monotonicity lets `σ₂` fire there and carry
the extra tokens `grownA - src` through to its target. The concatenation
`σ₁ ++ σ₂` thus strictly increases every place in `A ∪ {q}` and
leaves every place with at least its starting token count. -/
theorem WeightedNet.FiresSequence.combine_growth_firing_sequences
    [DecidableEq P] (A : Finset P) (q : P)
    {src grownA grownQ : Marking P} {labelsA labelsQ : List T}
    (hgrowsA : WeightedNet.FiresSequence.GrowsOn net src labelsA grownA A)
    (hgrowsQ : WeightedNet.FiresSequence.GrowsOn net src labelsQ grownQ {q}) :
    ∃ tgt,
      WeightedNet.FiresSequence.GrowsOn net src
        (labelsA ++ labelsQ) tgt (insert q A) := by
  let tgt := grownQ + (grownA - src)
  have hgrowsAtQ : src <[q] grownQ :=
    Marking.growsOn_singleton src grownQ q |>.mp hgrowsQ.2
  have hreplayed := hgrowsQ.1.mono hgrowsA.2.1
  refine ⟨tgt, hgrowsA.1.append hreplayed, ?_, ?_⟩
  · intro p
    exact (hgrowsAtQ.1 p).trans (by simp [tgt])
  · intro p hp
    rw [Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · exact hgrowsAtQ.2.trans_le (by simp [tgt])
    · have hgrowthAtP := hgrowsA.2.2 p hp
      have hmonoAtP := hgrowsAtQ.1 p
      change src p < grownQ p + (grownA p - src p)
      exact (Nat.lt_add_of_pos_right
        (Nat.sub_pos_of_lt hgrowthAtP)).trans_le
          (Nat.add_le_add_right hmonoAtP (grownA p - src p))

/-- Given, for each `p ∈ A`, a non-decreasing firing sequence from `src`
that strictly grows `p`, combine these sequences into a single non-decreasing
firing sequence from `src` that strictly grows every place in `A`.

For each `p ∈ A`, suppose a sequence `σₚ` fires from `src`, strictly
increases the token count at `p`, and leaves every place with at least
its starting token count. Replay each `σₚ` in turn from the marking reached
so far. The resulting sequence fires from `src`, strictly increases every
place in `A`, and leaves every place with at least its starting token count. -/
theorem WeightedNet.FiresSequence.exists_combined_growth_from
    (src : Marking P) (A : Finset P)
    (hsegments : ∀ p ∈ A, ∃ labels tgt,
      WeightedNet.FiresSequence.GrowsOn net src labels tgt {p}) :
    ∃ labels tgt,
      WeightedNet.FiresSequence.GrowsOn net src labels tgt A := by
  classical
  induction A using Finset.induction with
  | empty => exact ⟨[], src, WeightedNet.FiresSequence.nil src, le_rfl, by simp⟩
  | @insert q A hq ih =>
      obtain ⟨labelsA, grownA, hgrowsA⟩ :=
        ih (fun p hp => hsegments p (by simp [hp]))
      obtain ⟨labelsQ, grownQ, hgrowsQ⟩ :=
        hsegments q (by simp)
      obtain ⟨combined, hcombined⟩ :=
        WeightedNet.FiresSequence.combine_growth_firing_sequences A q hgrowsA hgrowsQ
      exact ⟨labelsA ++ labelsQ, combined, hcombined⟩

/-- Given, for each `p ∈ A`, a non-decreasing firing sequence `σₚ` that
ends at `base` and strictly grows `p`, combine them into a single
non-decreasing firing sequence from `base` that strictly grows every
place in `A`.

Each `σₚ` can fire again from `base` because its original source is
at most `base`. The replays now share the same source, so
`exists_combined_growth_from` combines them. -/
theorem WeightedNet.FiresSequence.exists_combined_growth
    (base : Marking P) (A : Finset P)
    (hsegments : ∀ p ∈ A, ∃ src ts,
      net.FiresSequence src ts base ∧ src <[p] base) :
    ∃ ts tgt,
      WeightedNet.FiresSequence.GrowsOn net base ts tgt A := by
  classical
  apply WeightedNet.FiresSequence.exists_combined_growth_from base A
  intro p hp
  obtain ⟨src, ts, hseq, hgrows⟩ := hsegments p hp
  refine ⟨ts, base + (base - src), hseq.fire_again hgrows.1, ?_⟩
  rw [Marking.growsOn_singleton]
  exact ⟨by simp, by simp [Nat.sub_pos_of_lt hgrows.2]⟩

end PetriNet
