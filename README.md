# Goal

1. Implementing unfailing Knuth-Bendix completion in Haskell 

2. Doing proof reconstruction in Lean

I separate the completion algorithm from proof reconstruction. The algorithm is an untrusted oracle; the Lean kernel is the root of trust and checks the justification it produces. So the algorithm does not need to be written in Lean.
I wrote it in Haskell because the debugging is more transparent for me while working out the core logic, and because I can reference the early versions of twee.
