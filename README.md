# Goal : core deliverable for praktika

1. Implementation:
  - Huet/KB completion implementation 
  - LPO 
  - selection strategies(smallest rule first)

2. Evaluation:
  - Original KB paper examples.
  - Hand-written algebraic examples: nat, monoid, zero monoid, group, wiki monoid.
  - Small TPTP equational benchmark set.

3. Extensions if time permits:
  - KBO for problems where LPO fails to orient.
  - Profiling and optimization.


# Future work: proof reconstruction in Lean
Implementation of unfailing loop using metaprogramming API instead of self-defined inductive types


## Project Structure


| Layer | Module            | Depends on        |  TODO        |
|-------|-------------------|-------------------|--------------|
|8| `UnfailingKBC.hs`(unfailing version) | 0 - 6| implementation(possibly just directly in Lean)
|7| `Huet.hs`(classical completion) | 0 - 6| 
| 6| `CriticalPair.hs` | 0 - 5       | unfailing version |
| 5    | `Rewrite.hs`          | 0 - 4              | 
| 4     | `Unification.hs`  | Matching          | possible optimization: MM|
| 3     | `Matching.hs`     | Substitution      |
| 2     | `Substitution.hs` | Term              |
| 1     | `LPO.hs`          | Term              | optimization
| 0     | `Term.hs`         | — (foundation)    |


## References :

- [Simple Word Problems in Universal Algebra](https://www.cs.tufts.edu/~nr/cs257/archive/don-knuth/knuth-bendix.pdf): the original paper from Knuth&Bendix

- [Term Rewriting Systems](https://joerg.endrullis.de/trs/) : general theoretical background
- [Term Rewriting and All That](https://www.cambridge.org/core/books/term-rewriting-and-all-that/71768055278D0DEF4FFC74722DE0D707) : Chapter 7.2, for the implementation of Huet's completion loop
- [Twee: An Equational Theorem Prover (System Description) ](https://smallbone.se/papers/twee.pdf)
- [THINGS TO KNOW WHEN IMPLEMENTING LPO](https://www.worldscientific.com/doi/abs/10.1142/S0218213006002564) : implementation of naive LPO

