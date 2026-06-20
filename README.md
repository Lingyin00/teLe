# Goal

1. Implementing the unfailing Knuth-Bendix completion in Haskell 


2. Doing proof reconstruction in Lean

I separate the completion algorithm from proof reconstruction. The algorithm is an untrusted oracle; the Lean kernel is the root of trust and checks the justification it produces. So the algorithm does not need to be written in Lean.
I wrote it in Haskell because working in a non-dependent typed language helps me to figure out how the algorithm itself, and also because I can reference the early versions of [Twee](https://github.com/nick8325/twee)

## Project Structure


| Layer | Module            | Depends on        |  TODO        |
|-------|-------------------|-------------------|--------------|
| 5| `CriticalPair.hs` | Unification, LPO       | unfailing    |
| 4     | `Unification.hs`  | Matching          | possible optimization: MM|
| 3     | `Matching.hs`     | Substitution      |
| 2     | `Substitution.hs` | Term              |
| 1     | `LPO.hs`          | Term              | optimization
| 0     | `Term.hs`         | — (foundation)    |


## References :

- [Term Rewriting Systems](https://joerg.endrullis.de/trs/)
- [Term Rewriting and All That](https://www.cambridge.org/core/books/term-rewriting-and-all-that/71768055278D0DEF4FFC74722DE0D707)
- [Twee: An Equational Theorem Prover (System Description) ](https://smallbone.se/papers/twee.pdf)