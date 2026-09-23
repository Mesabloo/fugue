---- MODULE RejectSynthesizedFunctionDomain ----
\* Expect: rejected, E0026, at the string index. `Sq[n \in 1..3] == n * n` carries no type
\* annotation; its domain comes from `1..3`, so `Sq : Int -> Int`. A string index must not be
\* accepted.

EXTENDS Naturals

Sq[n \in 1..3] == n * n

ASSUME Sq["a"] = 1

====
