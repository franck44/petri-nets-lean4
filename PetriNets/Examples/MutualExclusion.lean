/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.PlaceInvariant

/-!
# Example: mutual exclusion

This module formalises the mutual-exclusion example from Reisig's symbolic
net in Fig. 3.8. Its places are labelled `A` through `G`, and its transitions
are labelled `a` through `f`:

The two process are simple cycles  entering and exiting their critical sections.
Entering and exiting their critical sections, the processes must acquire and release the lock, represented by place `D`:

```text
left:   (A •) ─▶ [a] ─▶ (B) ─▶ [b] ─▶ (C*) ─▶ [c] ─▶ (A) ...
                              ▲                  │
                               \                /
                                \              ▼
                                 ------------ (D •)
                                /              ▲
                               /                \
                              ▼                  │
right:  (E •) ─▶ [d] ─▶ (F) ─▶ [e] ─▶ (G*) ─▶ [f] ─▶ (E) ...

        * critical state       • initial token
```

Transitions `b` and `e` enter the critical section by acquiring the single token in `D`, which represents the lock to the critical section. Transitions `c` and `f`  exit the critical section by releasing the lock. The bullet • indicates a token.
The initial marking contains one token in each of `A`, `D`, and `E`.

To prove that the mutual exclusion property holds, we can identify a place invariant that captures this property:
`C + G ≤ 1`

To illustrate how we can use the algebra on invariants to derive the mutual exclusion property, consider the following place invariant.

`C + D + G = 1`

at every reachable marking. Since a marking contains a nonnegative number of
tokens in `D`, it follows that `C + G ≤ 1`: the left and right processes
cannot both be in their critical states.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, Section 12.2, p. 133; see also Figs. 3.2 and
  3.8. DOI: 10.1007/978-3-642-33278-4.
-/

@[expose] public section

namespace PetriNet.MutualExclusion

/-- The seven places `A`, `B`, `C`, `D`, `E`, `F`, and `G`. -/
abbrev P := Fin 7

/-- The six transitions `a`, `b`, `c`, `d`, `e`, and `f`. -/
abbrev T := Fin 6

def pA : P := 0
def pB : P := 1
def pC : P := 2
def pD : P := 3
def pE : P := 4
def pF : P := 5
def pG : P := 6

def ta : T := 0
def tb : T := 1
def tc : T := 2
def td : T := 3
def te : T := 4
def tf : T := 5

/-- Reisig's mutual-exclusion net. Transitions `tb` and `te` acquire the key
in `pD`; transitions `tc` and `tf` return it. -/
def net : WeightedNet P T where
  pre p t :=
    match p.val, t.val with
    | 0, 0 | 1, 1 | 3, 1 | 2, 2
    | 4, 3 | 5, 4 | 3, 4 | 6, 5 => 1
    | _, _ => 0
  post p t :=
    match p.val, t.val with
    | 1, 0 | 2, 1 | 0, 2 | 3, 2
    | 5, 3 | 6, 4 | 4, 5 | 3, 5 => 1
    | _, _ => 0

/-- The initial marking `ADE`: both processes are local and the key is
available. -/
def initial : Marking P := fun p =>
  if p = pA ∨ p = pD ∨ p = pE then 1 else 0

/-- The invariant with coefficient vector `(0, 0, 1, 1, 0, 0, 1)`, which
counts the two critical places and the available lock. -/
def criticalOrLock : WeightedNet.PlaceInvariant net where
  coeff p := if p = pC ∨ p = pD ∨ p = pG then 1 else 0
  condition := by
    intro t
    fin_cases t <;> decide

/-- At the initial marking `ADE`, the value of the invariant `C + D + G` is
one: only the lock place `D` is marked. -/
theorem criticalOrLock_value_initial :
    criticalOrLock.value initial = 1 := by
  simp [WeightedNet.PlaceInvariant.value]
  simp [criticalOrLock]
  simp [initial, pA, pC, pD, pE, pG]
  simp [Fin.sum_univ_succ]

/-- At every marking `m` reachable from `initial`, the invariant equation is
`m C + m D + m G = 1`.
We use `value_eq_of_reachable` to transfer the invariant value one from the
initial marking to `m`.
-/
theorem critical_lock_eq_one {m : Marking P}
    (hreach : net.Reachable initial m) :
    m pC + m pD + m pG = 1 := by
  have hvalue := criticalOrLock.value_eq_of_reachable hreach
  rw [criticalOrLock_value_initial] at hvalue
  simp [WeightedNet.PlaceInvariant.value, criticalOrLock, pC, pD, pG,
    Fin.sum_univ_succ] at hvalue
  change m 2 + m 3 + m 6 = 1
  omega

/-- Mutual exclusion: in every reachable marking, at most one of the two
critical places `C` and `G` contains a token. This is Reisig's inequality
`C + G ≤ 1`, obtained from `C + D + G = 1` and `D ≥ 0`. -/
theorem mutual_exclusion {m : Marking P}
    (hreach : net.Reachable initial m) :
    m pC + m pG ≤ 1 := by
  have hinv := critical_lock_eq_one hreach
  omega

end PetriNet.MutualExclusion
