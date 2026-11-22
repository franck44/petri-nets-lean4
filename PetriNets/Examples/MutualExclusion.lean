/-
Copyright (c) 2026 Franck Cassez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franck Cassez
-/

module

public import PetriNets.PlaceInvariant

/-!
# Example: mutual exclusion

Provides a formalisation of Reisig's mutual-exclusion net and proves that its
two processes cannot be in their critical sections simultaneously. The
places are labelled `A` through `G`, and the transitions `a` through `f`.

Each process follows a cycle through its local, waiting, and critical states.
To enter its critical section, a process must acquire the single lock token
stored in place `D`; leaving the critical section returns that token.

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

Transitions `b` and `e` acquire the token in `D`, while transitions `c` and
`f` release it. The bullet `•` indicates an initial token, so the initial
marking contains one token in each of `A`, `D`, and `E`.

The place invariant

```text
C + D + G = 1
```

holds at every reachable marking. Since `D` contains a nonnegative number of
tokens, it implies `C + G ≤ 1`; hence the left and right processes cannot both
be in their critical sections at the same time.

## References

* W. Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis Methods,
  Case Studies*, Springer, 2013, Section 12.2, p. 133; see also Figs. 3.2 and
  3.8. DOI: 10.1007/978-3-642-33278-4.
-/

@[expose] public section

namespace PetriNet.MutualExclusion

/-! ## The mutual-exclusion net -/

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

/-- Reisig's mutual-exclusion net. Transitions `tb` and `te` acquire the lock
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

/-- The initial marking `ADE`: both processes are local and the lock is
available. -/
def initial : Marking P := fun p =>
  if p = pA ∨ p = pD ∨ p = pE then 1 else 0

/-! ## The critical-section invariant -/

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

/-! ## Mutual exclusion -/

/-- Mutual exclusion: in every reachable marking, at most one of the two
critical places `C` and `G` contains a token. This is Reisig's inequality
`C + G ≤ 1`, obtained from `C + D + G = 1` and `D ≥ 0`. -/
theorem mutual_exclusion {m : Marking P}
    (hreach : net.Reachable initial m) :
    m pC + m pG ≤ 1 := by
  have hinv := critical_lock_eq_one hreach
  omega

end PetriNet.MutualExclusion
