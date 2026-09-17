---- MODULE AcceptFunctionDefinitionSharedDomainBinderGoCodegen ----
\* Expect: accepted, all the way through Go code generation. `f[x, y \in S] == e` -- a shared-domain
\* binder, real TLA+ (Lamport's "Summary of TLA+", the `f[x \in S] == exp` entry's own footnote: "x
\* \in S may be replaced by a comma-separated list of items v \in S, where v is either a
\* comma-separated list or a tuple of identifiers"). `Desugarer/TLAPlus.lean`'s `flattenBound`
\* expands this to two ordinary flat binders sharing the same domain expression -- from
\* `Network2Go/Definition.lean` on, indistinguishable from `f[x \in S, y \in S] == e`.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

\* @type: <<Int, Int>> -> Int;
f[x, y \in {1, 2}] == x + y

(*--algorithm AcceptFunctionDefinitionSharedDomainBinderGoCodegen {
    process (P = PID)
        variables
            \* @type: Int;
            z = 0;
    {
    p1: z := f[1, 2];
        goto Done;
    }
}*)
====
