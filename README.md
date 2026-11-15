# Petri Nets in Lean 4

[![Lean v4.36.0-rc2](https://img.shields.io/badge/Lean-v4.36.0--rc2-blue)](https://github.com/leanprover/lean4/releases/tag/v4.36.0-rc2)
[![Mathlib 079459b](https://img.shields.io/badge/Mathlib-079459b-blue)](https://github.com/leanprover-community/mathlib4/commit/079459b14868f2c41fe80848321a4f152c8739b3)
[![CSLib e37c15a](https://img.shields.io/badge/CSLib-e37c15a-blue)](https://github.com/leanprover/cslib/commit/e37c15a8320f4c6ece5750c1447ec499755ff00e)

This repository aims to develop a Lean 4 library for Petri nets, specifically weighted place/transition (P/T) nets. It currently formalises:

- weighted P/T nets and markings;
- enabling and firing;
- firing sequences and reachability;
- monotonicity properties;
- pre-incidence, post-incidence, and incidence matrices;
- firing counts and state equations; and
- place invariants, their preservation properties, and their basic algebra.

The project is under development. The definitions and proofs are kept
in small modules so that their mathematical formulation can be reviewed before
the library is extended further.

## Mathematical conventions

A weighted P/T net has place and transition types `P` and `T`, with

```lean
pre  : P → T → ℕ
post : P → T → ℕ
```

The value zero means that the corresponding arc is absent. Since
`Matrix P T ℕ` is definitionally a function `P → T → ℕ`, these
functions are also the pre- and post-incidence matrices. The integer incidence
matrix is oriented place-by-transition and is defined by

```text
C p t = post p t - pre p t.
```

A marking is a function `P → ℕ`.

## Building

Install the Lean toolchain through [elan](https://github.com/leanprover/elan),
then run:

```sh
lake update
lake build
```

The committed `lake-manifest.json` records the complete dependency graph.

## Versions

The project currently uses the following pinned versions:

- Lean: `v4.36.0-rc2`
- Mathlib commit:
  [`079459b14868f2c41fe80848321a4f152c8739b3`](https://github.com/leanprover-community/mathlib4/commit/079459b14868f2c41fe80848321a4f152c8739b3)
- CSLib commit:
  [`e37c15a8320f4c6ece5750c1447ec499755ff00e`](https://github.com/leanprover/cslib/commit/e37c15a8320f4c6ece5750c1447ec499755ff00e)

The Lean version is specified in `lean-toolchain`; the direct dependency
commits are specified in `lakefile.toml`.

## References

The definitions, terminology, and standard results are guided principally by:

- Wolfgang Reisig, *Understanding Petri Nets: Modeling Techniques, Analysis
  Methods, Case Studies*, Springer, 2013.
  [doi:10.1007/978-3-642-33278-4](https://doi.org/10.1007/978-3-642-33278-4)
  The version used for this project is the English translation made available
  by the author on
  [ResearchGate](https://www.researchgate.net/publication/266860206_Understanding_Petri_nets_Modeling_techniques_analysis_methods_case_studies_Translated_from_the_German_by_the_author).
- Tadao Murata, “Petri Nets: Properties, Analysis and Applications,”
  *Proceedings of the IEEE* **77**(4), 1989, pp. 541–580.
  [doi:10.1109/5.24143](https://doi.org/10.1109/5.24143)
  The version used for this project is available as a
  [PDF from Universidade Federal de Campina Grande](https://www.dsc.ufcg.edu.br/~abrantes/CursosAnteriores/MVSRP/murata89.pdf).

Individual Lean modules give more precise references where a definition or
result is introduced.

## License

Copyright © 2026 Franck Cassez.

Released under the Apache License 2.0. See [LICENSE](LICENSE).
