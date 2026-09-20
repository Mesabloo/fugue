------------- MODULE Fibonacci ------------------
EXTENDS Naturals

CONSTANTS
  \* @type: Int;
  N,
  \* @type: Address;
  Comp
ASSUME N \in Nat

\* @type: Int -> Int;
Fib[n \in Nat] == CASE
     n = 0        -> 0
  [] n \in {1, 2} -> 1
  [] OTHER        -> Fib[n - 1]

(*--algorithm Fibonacci {
  process (comp = Comp)
    variables
      \* @type: Int;
      i = 1,
      \* @type: Int;
      res1 = 0,
      \* @type: Int;
      res2 = 1;
    {
    loop:
      while (i < N) {
        res1 := res2 || res2 := res1 + res2;
      };
      assert res2 = Fib[N];
    }
}*)

======================
