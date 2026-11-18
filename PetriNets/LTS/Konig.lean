/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Mathlib.Data.List.Duplicate

/-!
# Simple paths and Kőnig's lemma for LTS

This module provides generic labelled-transition-system machinery used by the
Petri-net covering-graph development: simple reachability, cycle removal, the
LTS of finite simple paths, and Kőnig's infinity lemma for deterministic LTS.

The definitions and results are generic and may eventually be contributed to
CSLib.
-/

@[expose] public section

namespace Cslib.LTS

/-- A state `tgt` is *simply reachable* from `src` when there is a finite
execution from `src` to `tgt` whose list of visited states contains no
duplicates.

The transition-label list and complete state list are retained through
`Execution`; the `Nodup` condition makes the execution a simple path.

TODO: this is a generic LTS definition and may eventually be contributed
to CSLib and moved to the `Cslib.LTS` library itself. -/
def CanReachSimple {State Label : Type*} (lts : LTS State Label)
    (src tgt : State) : Prop :=
  ∃ labels states,
    lts.Execution src labels tgt states ∧ states.Nodup

end Cslib.LTS

namespace List

/-- A duplicated list element occurs at two ordered bounded indices in the list. -/
theorem Duplicate.exists_get_eq {α : Type*} {x : α} {l : List α}
    (h : Duplicate x l) :
    ∃ i j : Fin l.length,
      i < j ∧ l.get i = x ∧ l.get j = x := by
  induction h with
  | @cons_mem l hx =>
      obtain ⟨i, hi⟩ := List.get_of_mem hx
      refine ⟨⟨0, by simp⟩, ⟨i + 1, by simp⟩, ?_, by simp, ?_⟩
      · change (0 : ℕ) < i.val + 1
        omega
      · simpa using hi
  | @cons_duplicate y l _ ih =>
      obtain ⟨i, j, hij, hi, hj⟩ := ih
      refine ⟨⟨i + 1, by simp⟩, ⟨j + 1, by simp⟩, ?_, ?_, ?_⟩
      · simpa using hij
      · simpa using hi
      · simpa using hj

end List

namespace Cslib.LTS

/-- Remove a cycle from a finite execution containing a repeated state.

An execution with a duplicated state can be shortened by removing the segment
(cycle) between the first and second occurrences of the repeated state, resulting in a
strictly shorter execution with the same source and target.

For example, consider the execution

```text
a → b → c → b → d
```

in which `b` occurs twice. Removing the segment from the first occurrence of
`b` up to the second gives

```text
a → b → d
```

This remains a valid execution because the prefix and the suffix around the removed
cycle are themselves valid executions and can be concatenated. -/
theorem Execution.shorten_of_dup {State Label : Type*}
    {lts : LTS State Label} {src tgt : State}
    {labels : List Label} {states : List State}
    (hexec : lts.Execution src labels tgt states)
    (hdup : ∃ s, List.Duplicate s states) :
    ∃ labels' states',
      lts.Execution src labels' tgt states' ∧
      states'.length < states.length := by
  /- get a witness duplicated state. -/
  obtain ⟨state, hstate⟩ := hdup
  /- get two indices i < j where the duplicated state occurs. -/
  obtain ⟨i, j, hij, hi, hj⟩ := hstate.exists_get_eq
  /- the two occurrences of the duplicated state are equal. -/
  have heq : states.get i = states.get j := hi.trans hj.symm
  /- take the prefix up to the first occurrence and the suffix from the second occurrence. -/
  have hprefix := hexec.take i i.isLt
  have hsuffix := hexec.drop j j.isLt
 /- rewwrite to use state.get i and get j. -/
  change lts.Execution src (labels.take i) (states.get i)
    (states.take (i + 1)) at hprefix
  change lts.Execution (states.get j) (labels.drop j) tgt
    (states.drop j) at hsuffix
  /- show that sufix starts with the duplicated state. -/
  rw [← heq] at hsuffix
  refine ⟨labels.take i ++ labels.drop j,
    states.take (i + 1) ++ (states.drop j).tail,
    hprefix.comp hsuffix, ?_⟩
  simp
  omega

/-- Every finite execution can be shortened, without changing its endpoints,
to an execution whose state list contains no duplicates. -/
theorem Execution.exists_nodup {State Label : Type*}
    {lts : LTS State Label} {src tgt : State}
    {labels : List Label} {states : List State}
    (hexec : lts.Execution src labels tgt states) :
    ∃ labels' states',
      lts.Execution src labels' tgt states' ∧ states'.Nodup := by
  induction hlength : states.length using Nat.strong_induction_on
      generalizing labels states with
  | ind n ih =>
      by_cases hnodup : states.Nodup
      · exact ⟨labels, states, hexec, hnodup⟩
      · obtain ⟨labels', states', hexec', hshorter⟩ :=
          hexec.shorten_of_dup
            (List.exists_duplicate_iff_not_nodup.mpr hnodup)
        exact ih states'.length (hlength ▸ hshorter) hexec' rfl

/-- Reachability in an lts is equivalent to reachability by a simple path.

For the forward direction, convert a multistep transition into an execution
and repeatedly remove cycles until its state list is `Nodup`. The reverse
direction simply forgets the intermediate state list and its `Nodup` proof.

TODO: this generic result should eventually be contributed to CSLib. -/
theorem canReach_iff_canReachSimple {State Label : Type*}
    {lts : LTS State Label} {src tgt : State} :
    lts.CanReach src tgt ↔ lts.CanReachSimple src tgt := by
  constructor
  · rintro ⟨labels, hmtr⟩
    obtain ⟨states, hexec⟩ := Execution.of_mTr hmtr
    obtain ⟨labels', states', hexec', hnodup⟩ := hexec.exists_nodup
    exact ⟨labels', states', hexec', hnodup⟩
  · rintro ⟨labels, _, hexec, _⟩
    exact ⟨labels, hexec.to_mTr⟩

/-- A finite simple path represented by its nonempty list of pairwise
distinct states. -/
structure SimplePath (State : Type*) where
  states : List State
  nodup : states.Nodup
  nonempty : states ≠ []

namespace SimplePath

/-- Construct a simple path from a nonempty list containing no duplicate
states. -/
def ofList {State : Type*} (states : List State) (hnodup : states.Nodup)
    (hnonempty : states ≠ []) : SimplePath State where
  states := states
  nodup := hnodup
  nonempty := hnonempty

/-- The states of a simple path build from a list using `ofList` are exactly the original list. -/
@[simp]
theorem states_ofList {State : Type*} (states : List State)
    (hnodup : states.Nodup) (hnonempty : states ≠ []) :
    (ofList states hnodup hnonempty).states = states :=
  rfl

/-- The final state of a simple path. -/
def last {State : Type*} (path : SimplePath State) : State :=
  path.states.getLast path.nonempty

/-- The zero-step simple path rooted at `root`. -/
def root {State : Type*} (root : State) : SimplePath State :=
  ofList [root] (by simp) (by simp)

/-- The root of a simple path is its last state. -/
@[simp]
theorem last_root {State : Type*} (root : State) :
    (SimplePath.root root).last = root :=
  rfl

/-- Simple paths are equal when their state lists are equal; their remaining
fields are proofs. -/
@[ext]
theorem ext {State : Type*} {path path' : SimplePath State}
    (hstates : path.states = path'.states) : path = path' := by
  cases path
  cases path'
  simp_all

/-- Construct a `SimplePath State` from an initial segment of a list of states
with no duplicates.

Given a duplicate-free list `states` and a valid index `i`, the result contains
the states at positions `0` through `i`. The bound `hi : i < states.length`
ensures that this initial segment is nonempty and ends at `states[i]`. -/
def initialSegment {State : Type*} (states : List State) (hnodup : states.Nodup)
    (i : ℕ) (hi : i < states.length) : SimplePath State :=
  ofList (states.take (i + 1)) hnodup.take (by
    apply List.ne_nil_of_length_pos
    simp
    omega)

/-- The states of a simple path built from an initial segment of a list are exactly that segment. -/
@[simp]
theorem states_initialSegment {State : Type*} (states : List State)
    (hnodup : states.Nodup) (i : ℕ) (hi : i < states.length) :
    (initialSegment states hnodup i hi).states = states.take (i + 1) :=
  rfl

/-- The last state of a simple path built from an initial segment of a list is the state at the given index. -/
@[simp]
theorem last_initialSegment {State : Type*} (states : List State)
    (hnodup : states.Nodup) (i : ℕ) (hi : i < states.length) :
    (initialSegment states hnodup i hi).last = states[i] := by
  unfold initialSegment ofList last
  simp only [List.take_succ_eq_append_getElem hi,
    List.getLast_append_singleton]

end SimplePath

/-- The LTS whose states store finite simple paths of `lts`.

The states of `simplePathLTS lts` are paths, rather than merely states of the
`lts`. Consequently, two different paths in `simplePathLTS lts` cannot reach the same
state of `simplePathLTS lts`, even when they end in the same original state of the lts.
We denote ->_lts the transition relation of `lts`
An edge of `simplePathLTS lts`

```text
path --label -> path' iff path.last --label ->_lts next, next ∉ path and path' = path ++ [next],
```

The transition relation mirrors the transition relation of `lts`: it carries
the same label and appends the target of the original transition to the
stored path. Thus every edge extends a path by exactly one previously
unvisited state. -/
def simplePathLTS {State Label : Type*} (lts : LTS State Label) :
    LTS (SimplePath State) Label where
  Tr path label path' :=
    ∃ next,
      lts.Tr path.last label next ∧
      next ∉ path.states ∧
      path'.states = path.states ++ [next]

/-- Every transition path - label -> path' of `simplePathLTS lts` corresponds
to a transition of `lts` between the final states of path and path'. -/
theorem simplePathLTS_tr_projects {State Label : Type*}
    {lts : LTS State Label} {path path' : SimplePath State} {label : Label}
    (htr : (simplePathLTS lts).Tr path label path') :
    lts.Tr path.last label path'.last := by
  obtain ⟨next, hnext, _, hstates⟩ := htr
  have hlast : path'.last = next := by
    simp [SimplePath.last, hstates]
  rwa [hlast]

/-- If `lts` is deterministic, then `simplePathLTS lts` is deterministic. -/
instance simplePathLTS_deterministic {State Label : Type*}
    (lts : LTS State Label) [lts.Deterministic] :
    (simplePathLTS lts).Deterministic where
  deterministic path label path₁ path₂ h₁ h₂ := by
    obtain ⟨next₁, hnext₁, _, hstates₁⟩ := h₁
    obtain ⟨next₂, hnext₂, _, hstates₂⟩ := h₂
    have hnext : next₁ = next₂ := Deterministic.eq_of_tr hnext₁ hnext₂
    apply SimplePath.ext
    rw [hstates₁, hstates₂, hnext]

/-- Consecutive prefixes of a an execution of `lts` with no duplicate states
form a transition in the `simplePathLTS lts`.

For an execution in `lts`

```text
s₀ --a₀ -> s₁ --a₁ -> ⋯ --aᵢ -> sᵢ₊₁ -> ⋯,
```

a prefix is specified by a parameter `i` that selects the transition labelled `aᵢ`. The hypothesis
`hi : i < labels.length` states that this transition exists; it also ensures we can safely perform
the indexed accesses to `labels[i]` and `states[i + 1]` in the execution.

The result is the corresponding transition between path prefixes in `simplePathLTS lts`:

```text
[s₀, …, sᵢ] --aᵢ -> [s₀, …, sᵢ, sᵢ₊₁].
```

The `Nodup` hypothesis ensures that `sᵢ₊₁` is fresh in the first
prefix, as required by `simplePathLTS`. -/
theorem Execution.simplePrefix_tr {State Label : Type*}
    {lts : LTS State Label} {src tgt : State}
    {labels : List Label} {states : List State}
    (hexec : lts.Execution src labels tgt states)
    (hnodup : states.Nodup) (i : ℕ) (hi : i < labels.length) :
    (simplePathLTS lts).Tr
      (SimplePath.initialSegment states hnodup i (by rw [hexec.length]; omega))
      (labels.get ⟨i, hi⟩)
      (SimplePath.initialSegment states hnodup (i + 1) (by rw [hexec.length]; omega)) := by
  have hlen := hexec.length
  refine ⟨states[i + 1]'(by omega), ?_, ?_, ?_⟩
  · simpa using hexec.trans i hi
  · change states[i + 1] ∉ states.take (i + 1)
    intro hmem
    obtain ⟨j, hj⟩ := List.get_of_mem hmem
    have hjlt : j.val < i + 1 := by
      have := j.isLt
      simp only [List.length_take] at this
      omega
    have heq : states[j.val] = states[i + 1] := by
      rw [← List.getElem_take (h := j.isLt)]
      exact hj
    have hij := hnodup.getElem_inj_iff.mp heq
    omega
  · exact List.take_succ_eq_append_getElem (by omega : i + 1 < states.length)

/-- Every initial segment of an execution of `lts` from `src`, with no duplicate states
 is reachable in `simplePathLTS lts` from its one-state root `[src]`.

Suppose `hexec` describes an execution of the `lts`:

```text
s₀ --a₀→ s₁ --a₁→ ⋯ --aᵢ₋₁→ sᵢ → ⋯ --aₙ₋₁→ sₙ.
```

The parameter `i` selects the state `sᵢ`, and `hi : i ≤ labels.length`
ensures that this state occurs in the execution. Notice that `≤`, rather than
`<`, is used here because `i` may select the final state `sₙ`. The theorem
states that the corresponding simple path [s₀, …, sᵢ] (upto the state `sᵢ`) is reachable in
`simplePathLTS lts` from the root path `[s₀]`.


The proof proceeds by induction on `i`. The segment at position zero is the
root path itself. At a non-zero position `i + 1`, the induction hypothesis reaches
`[s₀, …, sᵢ]`, and `Execution.simplePrefix_tr` extends it with the next
transition to `[s₀, …, sᵢ, sᵢ₊₁]`. -/
theorem Execution.initialSegment_canReach {State Label : Type*}
    {lts : LTS State Label} {src tgt : State}
    {labels : List Label} {states : List State}
    (hexec : lts.Execution src labels tgt states)
    (hnodup : states.Nodup) (i : ℕ) (hi : i ≤ labels.length) :
    (simplePathLTS lts).CanReach (SimplePath.root src)
      (SimplePath.initialSegment states hnodup i (by rw [hexec.length]; omega)) := by
  induction i with
  | zero =>
      refine ⟨[], ?_⟩
      have hpath : SimplePath.initialSegment states hnodup 0
          (by rw [hexec.length]; omega) = SimplePath.root src := by
        apply SimplePath.ext
        simp only [SimplePath.states_initialSegment, SimplePath.root]
        rw [List.take_succ_eq_append_getElem (by rw [hexec.length]; omega)]
        simp [hexec.start]
      rw [hpath]
      exact MTr.refl
  | succ i ih =>
      have hi' : i ≤ labels.length := by omega
      obtain ⟨prefixLabels, hprefix⟩ := ih hi'
      have hilt : i < labels.length := by omega
      refine ⟨prefixLabels ++ [labels.get ⟨i, hilt⟩], ?_⟩
      exact MTr.stepR (simplePathLTS lts) hprefix
        (hexec.simplePrefix_tr hnodup i hilt)

/-- **Weak Kőnig infinity lemma for deterministic LTS.** Suppose the type of
labels is finite and the LTS is deterministic. If infinitely many states are
reachable from `root`, there is an infinite execution starting at `root`.
Note that this theorem does not imply that infinitely many different states
are visited on the infinite execution, which is why it is called the weak
Kőnig lemma.

TODO: this is a generic LTS result and should eventually be contributed to
CSLib and moved to the `Cslib.LTS` library itself.

Finite transition labels and determinism imply finite branching. The proof
maintains a state from which infinitely many states remain reachable. Such a
state must have a successor with the same property: otherwise its finitely
many successors would each have only finitely many descendants, making its
own set of descendants finite. Repeatedly choosing such a successor produces
the required infinite execution.

In a nutshell, for any depth `d`, if we unfold the execution tree of `lts`
from `root` up to depth `d`, we can only visit a finite number of states.
As there is an infinite number of reachable states, there must be a state with
infinitely many descendants, which allows us to construct the infinite execution.
-/
theorem konig_weak
    {State Label : Type*} [Finite Label]
    (lts : LTS State Label) [lts.Deterministic]
    (root : State) (hinfinite : {s | lts.CanReach root s}.Infinite) :
    ∃ states labels,
      lts.OmegaExecution states labels ∧ states 0 = root := by
  classical
  let descendants (s : State) := {s' | lts.CanReach s s'}
  have next_infinite {s : State} (hs : (descendants s).Infinite) :
      ∃ label s', lts.Tr s label s' ∧ (descendants s').Infinite := by
    by_contra! h
    let successors : Set State := {s' | ∃ label, lts.Tr s label s'}
    have hsuccessors : successors.Finite := by
      have hall : (⋃ label, lts.image s label).Finite :=
        Set.finite_iUnion fun label => Set.toFinite (lts.image s label)
      apply hall.subset
      rintro s' ⟨label, htr⟩
      exact Set.mem_iUnion.mpr ⟨label, htr⟩
    have hdesc : ∀ s' ∈ successors, (descendants s').Finite := by
      rintro s' ⟨label, htr⟩
      exact Set.finite_coe_iff.mp (h label s' htr)
    have hunion : (⋃ s' ∈ successors, descendants s').Finite :=
      hsuccessors.biUnion hdesc
    apply hs
    apply ((Set.finite_singleton s).union hunion).subset
    intro tgt htgt
    obtain ⟨ts, hts⟩ := htgt
    cases ts with
    | nil =>
        left
        have : s = tgt := by simpa using hts
        exact this.symm
    | cons label labels =>
        right
        obtain ⟨s', htr, htail⟩ := (MTr.cons_iff).mp hts
        exact Set.mem_iUnion₂.mpr ⟨s', ⟨label, htr⟩, ⟨labels, htail⟩⟩
  let good := {s : State // (descendants s).Infinite}
  let next (s : good) : good :=
    ⟨(next_infinite s.2).choose_spec.choose,
      (next_infinite s.2).choose_spec.choose_spec.2⟩
  let label (s : good) : Label := (next_infinite s.2).choose
  have next_tr (s : good) : lts.Tr s (label s) (next s) :=
    (next_infinite s.2).choose_spec.choose_spec.1
  let branch : ℕ → good := fun n => next^[n] ⟨root, hinfinite⟩
  refine ⟨fun n => (branch n).1, fun n => label (branch n), ?_, ?_⟩
  · intro n
    simpa [branch, Function.iterate_succ_apply'] using next_tr (branch n)
  · rfl

/-- If infinitely many states of `lts` are reachable from `root`, then
infinitely many states of `simplePathLTS lts` are reachable from the one-state
path `[root]`.

Recall that a state of `simplePathLTS lts` is itself a duplicate-free finite
path. For every original state `tgt` reachable from `root`, cycle removal gives
a simple execution from `root` to `tgt`. By
`Execution.initialSegment_canReach`, its complete state list is a reachable
state `path` of `simplePathLTS lts`, and

```text
path.last = tgt.
```

Consequently, taking the final state maps the reachable simple paths onto all
states reachable in the original LTS:

```text
reachable simple paths  --SimplePath.last→  reachable original states.
```

The proof argues by contradiction. If there were only finitely many reachable
states (paths) in `simplePathLTS lts`, their last states would form a finite set.
The construction above shows that this finite set contains every state reachable from `root`,
contradicting the hypothesis that the latter set is infinite. No determinism
or finiteness assumption on the transition labels is needed for this result. -/
theorem simplePathLTS_infinite_reachable {State Label : Type*}
    (lts : LTS State Label) (root : State)
    (hinfinite : {s | lts.CanReach root s}.Infinite) :
    {path | (simplePathLTS lts).CanReach (SimplePath.root root) path}.Infinite := by
  by_contra hfinite
  have hpaths : {path | (simplePathLTS lts).CanReach
      (SimplePath.root root) path}.Finite := Set.not_infinite.mp hfinite
  have hlasts := hpaths.image SimplePath.last
  apply hinfinite
  apply hlasts.subset
  intro tgt htgt
  obtain ⟨labels, states, hexec, hnodup⟩ :=
    canReach_iff_canReachSimple.mp htgt
  let path := SimplePath.initialSegment states hnodup labels.length
    (by rw [hexec.length]; omega)
  have hreach : (simplePathLTS lts).CanReach
      (SimplePath.root root) path :=
    hexec.initialSegment_canReach hnodup labels.length (by omega)
  refine ⟨path, hreach, ?_⟩
  simp only [path, SimplePath.last_initialSegment]
  exact hexec.last'

/-- The paths occurring later in an infinite execution of
`simplePathLTS lts` extend the paths occurring earlier.

Suppose `paths` is an infinite execution in `simplePathLTS lts`

```text
paths 0 → paths 1 → paths 2 → ⋯
```

and `i ≤ j`. The theorem states that the list of `lts` states stored
in `paths i` is a prefix of the list stored in `paths j`:

```text
(paths i).states <+: (paths j).states.
```

For example, the execution may contain

```text
[s₀, s₁] → [s₀, s₁, s₂] → [s₀, s₁, s₂, s₃].
```

This follows directly from the definition of `simplePathLTS`: every
transition preserves the existing list and appends exactly one fresh state.
The proof is by induction on the later index `j`, composing the prefix relation for
the preceding path with this one-state extension. -/
theorem OmegaExecution.simplePath_states_prefix {State Label : Type*}
    {lts : LTS State Label} {paths : ℕ → SimplePath State}
    {labels : ℕ → Label}
    (hexec : (simplePathLTS lts).OmegaExecution paths labels)
    {i j : ℕ} (hij : i ≤ j) :
    (paths i).states <+: (paths j).states := by
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact List.prefix_rfl
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with (rfl | hij')
      · exact List.prefix_rfl
      · have hprefix := ih (Nat.le_of_lt_succ hij')
        obtain ⟨next, _, _, hstates⟩ := hexec j
        exact hprefix.trans ⟨[next], hstates.symm⟩

/-- **Strict Kőnig infinity lemma for deterministic LTS.**

For a deterministic LTS with finitely many labels, and infinitely many reachable states
from `root`, there is an infinite execution of the LTS starting at `root`
with pairwise distinct states.

In other words, there exist two functions `states` and `labels` that
yield an infinite execution

```text
s₀ --a₀→ s₁ --a₁→ s₂ --a₂→ ⋯
```

starting at `root`, in which the state function is injective (in other words
the execution visits pairwise distinct states).

The proof applies the weak version `konig_weak` (Kőnig's lemma building an
infinite execution possibly with cycles) to `simplePathLTS lts`.

Because `simplePathLTS lts` only allows extensions by fresh states,
any infinite execution of it must consist of pairwise distinct states.-/
theorem konig_strict
    {State Label : Type*} [Finite Label]
    (lts : LTS State Label) [lts.Deterministic]
    (root : State) (hinfinite : {s | lts.CanReach root s}.Infinite) :
    ∃ states labels,
      lts.OmegaExecution states labels ∧
      states 0 = root ∧ Function.Injective states := by
  have hpaths := simplePathLTS_infinite_reachable lts root hinfinite
  obtain ⟨paths, labels, hexec, hroot⟩ :=
    konig_weak
      (simplePathLTS lts) (SimplePath.root root) hpaths
  refine ⟨fun n => (paths n).last, labels, ?_, ?_, ?_⟩
  · intro n
    exact simplePathLTS_tr_projects (hexec n)
  · simp [hroot]
  · intro i j hij
    have ordered {i k : ℕ} (hik : i < k + 1)
        (heq : (paths i).last = (paths (k + 1)).last) : False := by
      obtain ⟨next, _, hfresh, hstates⟩ := hexec k
      have hnext : (paths (k + 1)).last = next := by
        simp [SimplePath.last, hstates]
      have himem : (paths i).last ∈ (paths k).states := by
        have hpref := hexec.simplePath_states_prefix (show i ≤ k by omega)
        exact hpref.subset (List.getLast_mem (paths i).nonempty)
      apply hfresh
      rw [← hnext, ← heq]
      exact himem
    rcases Nat.lt_trichotomy i j with (hlt | rfl | hgt)
    · cases j with
      | zero => omega
      | succ k => exact (ordered hlt hij).elim
    · rfl
    · cases i with
      | zero => omega
      | succ k => exact (ordered hgt hij.symm).elim

end Cslib.LTS
