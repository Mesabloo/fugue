---- MODULE AcceptMkSeqGoCodegen ----
\* Expect: accepted, all the way to Go, and the emitted Go must compile. `Fugue!MkSeq(N, Op)` is the
\* total sequence constructor [i \in 1..N |-> Op(i)] -- safe, unlike FunAsSeq/SetAsFun, so it raises
\* no -Wunsafe. `Op` compiles like any other operator reference, a plain Go function value, so
\* `Network2Go` composes `IntRange`/`FnConstructor`/`FunAsSeq` around it rather than needing a
\* dedicated runtime function.

EXTENDS Fugue, Sequences

CONSTANTS
    \* @type: Address;
    PID

\* @type: (Int) => Int;
Sq(i) == i * i

(*--algorithm AcceptMkSeqGoCodegen {
    process (P = PID)
        variables
            \* @type: Seq(Int);
            s = <<>>;
    {
    p1: s := MkSeq(3, Sq);
        assert Len(s) = 3;
        goto Done;
    }
}*)

====
