# teLe

teLe is a Haskell implementation of [Knuth–Bendix completion](https://en.wikipedia.org/wiki/Knuth–Bendix_completion_algorithm) (KBC) with the
[lexicographic path ordering](https://en.wikipedia.org/wiki/Path_ordering_(term_rewriting)) (LPO). Given a set of equational axioms, it attempts to derive a canonical rewrite system; when completion succeeds, equational reasoning becomes a decision procedure by normalization.

# Goal : core deliverable for praktika

1. Implementation
  - Huet/KB completion implementation 
  - LPO 
  - selection strategies(smallest rule first)

2. Evaluation and analysis
  - Hand-written algebraic examples: nat, monoid, zero monoid, group, wiki monoid.
  - 18 examples from riginal KB paper.
  - 6 TPTP equational examples.

# Project Structure


| Layer | Module            | Depends on        |  TODO        |
|-------|-------------------|-------------------|--------------|
|7| `Huet.hs`(classical completion) | 0 - 6| 
| 6| `CriticalPair.hs` | 0 - 5       | unfailing version(future work) |
| 5    | `Rewrite.hs`          | 0 - 4              | 
| 4     | `Unification.hs`  | Matching          | possible optimization: Martelli-Montanari|
| 3     | `Matching.hs`     | Substitution      |
| 2     | `Substitution.hs` | Term              |
| 1     | `LPO.hs`          | Term              | possible optimization
| 0     | `Term.hs`         | — (foundation)    |


# Run
## Under the root folder:
1. build the project
```shell
cabal build
```
2. print the results of evaluation with the examples from knuth, and 2 uniqueness theorems
```shell
cabal run -v0 kbc-haskell 2>/dev/null 
```
## TPTP
The TPTP examples are translated into Haskell because there're very few pure equational examples.

Analysis are written as comment in each example

To check the result, enter each file and for example:
1. enter into ghci
```shell
cabal repl
```
2. type the name of the TPTP example file
```shell
:m + Assoc_syn0831
```
3. give the name of the result and print it in console
```shell
result0831
```

# Overview of result

```shell
#    Example                  Result       Expected     Knuth                    time
--------------------------------------------------------------------------------------
1    Group theory             10 rules     10 rules     10 rules, 30 s          0.00s
2    Group theory II          FAIL         FAIL         FAIL                    0.00s
3    Group theory III         10 rules     10 rules     24 rules, 40 s          0.00s
4    Inverse property         3 rules      3 rules      3 rules(per hand)       0.00s
5    Group theory IV          12 rules     12 rules     12 rules, 50 s          0.00s
6    Central groupoids I      3 rules      3 rules      3 rules(per hand)       0.00s
7    Random axiom             FAIL         FAIL         FAIL(degenerate)        0.00s
8    Random axiom II          FAIL         FAIL         FAIL (degenerate)       0.00s
9A   Cancellation             2 rules      2 rules      2 rules                 0.00s
9B   Cancellation + unit      8 rules      8 rules      8 rules                 0.00s
10   Loops                    14 rules     14 rules     10 rules, 20s           0.00s
11   Group theory V           12 rules     12 rules     12 rules, 2m15s         0.02s
12   (l,r) systems I          9 rules      9 rules      10 rules, 110s          0.00s
13   (r,l) systems            12 rules     12 rules     HALTED                  0.02s
14   (l,r) systems II         12 rules     12 rules     21 rules,2.5 min        0.00s
15   (l,r) systems III        15 rules     15 rules     FAIL(DIVERGED)          0.04s
16   Central groupoids II     FAIL         FAIL         13 rules, 9 min         0.00s
17   Central groupoids III    5 rules      5 rules      25 rules, 2 min         0.00s
18   Burnside groups          FAIL         FAIL         FAIL                    0.00s
--------------------------------------------------------------------------------------
19/19 matched

#    Theorem                      Result     Expected       time
----------------------------------------------------------------
1    identity is unique           yes        yes           0.00s
2    inverse is unique            yes        yes           0.00s
----------------------------------------------------------------
```
# Example : Uniqueness of Inverses

Given the group axioms and an additional assumption that `a2` is a left inverse of `a`,

the completion procedure derives a canonical rewrite system from the axioms. 

Equality is then decided by normalization, automatically proving that the left inverse `a2` is equal to the inverse `i(a)`.

```haskell
leftinvPrime =
  Equation (app "f" [app "a2" [], app "a" []]) (app "e" [])

let Just rs =
  huetRules (huet groupPinv (groupAxiom ++ [leftinvPrime]))

decideEq rs $
  Equation (app "a2" []) (app "i" [app "a" []])
-- True
```
# Analysis:
Please see: ```ExamplesFromKnuth.hs```, ```Decide.hs```, and each haskell file under ```TPTP``` folder.

# Future work
1. Reimplementation in Lean's metaprogramming framework, possibly the unfailing KBC
2. Optimizations in unification, LPO
3. Add and experimenting with KBO 

---

# References :

- [Simple Word Problems in Universal Algebra](https://www.cs.tufts.edu/~nr/cs257/archive/don-knuth/knuth-bendix.pdf): the original paper from Knuth&Bendix

- [Term Rewriting Systems](https://joerg.endrullis.de/trs/) : general theoretical background
- [Term Rewriting and All That](https://www.cambridge.org/core/books/term-rewriting-and-all-that/71768055278D0DEF4FFC74722DE0D707) : Chapter 7.4, for the implementation of Huet's completion loop
- [Twee: An Equational Theorem Prover (System Description) ](https://smallbone.se/papers/twee.pdf)
- [THINGS TO KNOW WHEN IMPLEMENTING LPO](https://www.worldscientific.com/doi/abs/10.1142/S0218213006002564) : implementation of naive LPO

- [Completion without Failure](https://www.semanticscholar.org/paper/Completion-without-Failure-1-Bachmair-Plaisted/be28fac7cc04a6affd1b05997bb587600b98faf5): implementation reference for unfailing KBC

