---- MODULE AcceptFunctionDefinitionTuplePatternBinderGoCodegen ----
\* Expect: accepted, all the way through Go code generation. `f[<<x,y>> \in S] == e` -- a
\* tuple-pattern binder, real TLA+ (same footnote as `AcceptFunctionDefinitionSharedDomainBinderGoCodegen.tla`
\* -- "v is either a comma-separated list or a tuple of identifiers"). `Desugarer/TLAPlus.lean`'s
\* `flattenBound` collapses this to one fresh binder over `S`, rewriting the body to project `x`/`y`
\* back out (`z[1]`/`z[2]`) -- the same `CoreTLAPlus.Expression.subst`-based mechanism already
\* proven for `\A`/`\E`/set-builder/function-literal tuple patterns.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

\* @type: <<Int, Int>> -> Int;
f[<<x, y>> \in {<<1, 1>>, <<2, 2>>}] == x + y

(*--algorithm AcceptFunctionDefinitionTuplePatternBinderGoCodegen {
    process (P = PID)
        variables
            \* @type: Int;
            z = 0;
    {
    p1: z := f[<<1, 1>>];
        goto Done;
    }
}*)
====
