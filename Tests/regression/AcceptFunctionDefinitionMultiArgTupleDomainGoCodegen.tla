---- MODULE AcceptFunctionDefinitionMultiArgTupleDomainGoCodegen ----
\* Expect: accepted, all the way through Go code generation. `AcceptFunctionDefinitionMultiArgTupleDomain.tla`
\* has no embedded algorithm, so it never reaches `Network2Go` at all (`Driver/Pipeline.lean`'s
\* `let some algo := computable.pcalAlgorithm | return result` short-circuits before it) -- this
\* fixture pairs the same 2-binder function definition with a process that actually calls it, so
\* `Network2Go/Definition.lean`'s arity-2 domain-set construction (chained `SetProduct`, its pairing
\* closure repacking a flat 2-tuple) gets real coverage.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

\* @type: <<Int, Int>> -> Int;
f[x \in {1, 2}, y \in {1, 2}] == x + y

(*--algorithm AcceptFunctionDefinitionMultiArgTupleDomainGoCodegen {
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
