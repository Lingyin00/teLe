# Goal

1. Implementing the unfailing Knuth-Bendix completion in Haskell 
- 1.1: implement the classical KBC, test with group axioms
- 1.2: implement the unfailing version, test with abel group axioms

2. Doing proof reconstruction in Lean

I separate the completion algorithm from proof reconstruction. The algorithm is an untrusted oracle; the Lean kernel is the root of trust and checks the justification it produces. So the algorithm does not need to be written in Lean.
I wrote it in Haskell because working in a non-dependent typed language helps me to figure out how the algorithm itself, and also because I can reference the early versions of [Twee](https://github.com/nick8325/twee)

## Project Structure


| Layer | Module            | Depends on        |  TODO        |
|-------|-------------------|-------------------|--------------|
|8| `Completion.hs` | 0 - 6| unfailing completion
|7| `Huet.hs` | 0 - 6| interface with CP, classical KBC implementation
| 6| `CriticalPair.hs` | 0 - 5       | unfailing version |
| 5    | `Rewrite.hs`          | 0 - 4              | bidirectional orient
| 4     | `Unification.hs`  | Matching          | possible optimization: MM|
| 3     | `Matching.hs`     | Substitution      |
| 2     | `Substitution.hs` | Term              |
| 1     | `LPO.hs`          | Term              | optimization
| 0     | `Term.hs`         | — (foundation)    |


## References :

- [Term Rewriting Systems](https://joerg.endrullis.de/trs/) : general theoretical background
- [Term Rewriting and All That](https://www.cambridge.org/core/books/term-rewriting-and-all-that/71768055278D0DEF4FFC74722DE0D707) : Chapter 7.2, for the implementation of Huet's completion loop
- [Twee: An Equational Theorem Prover (System Description) ](https://smallbone.se/papers/twee.pdf)
- [THINGS TO KNOW WHEN IMPLEMENTING LPO](https://www.worldscientific.com/doi/abs/10.1142/S0218213006002564) : implementation of naive LPO

