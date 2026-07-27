# teLe

teLe is a Haskell implementation of [Knuth–Bendix completion](https://en.wikipedia.org/wiki/Knuth–Bendix_completion_algorithm) (KBC) with the
[lexicographic path ordering](https://en.wikipedia.org/wiki/Path_ordering_(term_rewriting)) (LPO). Given a set of equational axioms, it attempts to derive a canonical rewrite system; when completion succeeds, equational reasoning becomes a decision procedure by normalization.


---

# Goal : core deliverable for praktika

1. Implementation(done)
  - Huet/KB completion implementation 
  - LPO 
  - selection strategies(smallest rule first)

2. Evaluation(done)
  - Original KB paper examples.
  - Hand-written algebraic examples: nat, monoid, zero monoid, group, wiki monoid.
  - Small TPTP equational benchmark set.

3. Extensions if time permits(TODO)
  - KBO for problems where LPO fails to orient.
  - Profiling and optimization.

4. Unfailing completion(TODO)
  - ordered rewriting with unorientable equations
  - test on TPTP examples, study the comparison with classical completion loop

---

## Example : Uniqueness of Inverses

Given the group axioms and an additional assumption that `a2` is a left inverse of `a`,

```haskell
leftinvPrime =
  Equation (app "f" [app "a2" [], app "a" []]) (app "e" [])

let Just rs =
  huetRules (huet groupPinv (groupAxiom ++ [leftinvPrime]))

decideEq rs $
  Equation (app "a2" []) (app "i" [app "a" []])
-- True
```

The completion procedure derives a canonical rewrite system from the axioms. Equality is then decided by normalization, automatically proving that the left inverse `a2` is equal to the inverse `i(a)`.

---

# Future work: proof reconstruction in Lean
 Reimplementation in Lean's metaprogramming framework

---

## Project Structure


| Layer | Module            | Depends on        |  TODO        |
|-------|-------------------|-------------------|--------------|
|8| `UnfailingKBC.hs`(unfailing version) | 0 - 6| implementation
|7| `Huet.hs`(classical completion) | 0 - 6| 
| 6| `CriticalPair.hs` | 0 - 5       | unfailing version |
| 5    | `Rewrite.hs`          | 0 - 4              | 
| 4     | `Unification.hs`  | Matching          | possible optimization: Martelli-Montanari|
| 3     | `Matching.hs`     | Substitution      |
| 2     | `Substitution.hs` | Term              |
| 1     | `LPO.hs`          | Term              | possible optimization
| 0     | `Term.hs`         | — (foundation)    |

---

## References :

- [Simple Word Problems in Universal Algebra](https://www.cs.tufts.edu/~nr/cs257/archive/don-knuth/knuth-bendix.pdf): the original paper from Knuth&Bendix

- [Term Rewriting Systems](https://joerg.endrullis.de/trs/) : general theoretical background
- [Term Rewriting and All That](https://www.cambridge.org/core/books/term-rewriting-and-all-that/71768055278D0DEF4FFC74722DE0D707) : Chapter 7.4, for the implementation of Huet's completion loop
- [Twee: An Equational Theorem Prover (System Description) ](https://smallbone.se/papers/twee.pdf)
- [THINGS TO KNOW WHEN IMPLEMENTING LPO](https://www.worldscientific.com/doi/abs/10.1142/S0218213006002564) : implementation of naive LPO

- [Completion without Failure](https://www.semanticscholar.org/paper/Completion-without-Failure-1-Bachmair-Plaisted/be28fac7cc04a6affd1b05997bb587600b98faf5): implementation reference for unfailing KBC

