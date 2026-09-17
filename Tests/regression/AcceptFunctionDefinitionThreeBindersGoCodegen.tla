---- MODULE AcceptFunctionDefinitionThreeBindersGoCodegen ----
\* Expect: accepted, all the way through Go code generation. A 3-binder function definition --
\* `Network2Go/Definition.lean`'s `buildProductDomain` chains `SetProduct` twice, each step
\* repacking a flat, one-field-longer tuple, so the compiled domain is `Set(<<Int, Int, Int>>)`,
\* never a nested pair. No other fixture in this corpus exercises arity 3.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

\* @type: <<Int, Int, Int>> -> Int;
g[x \in {1, 2}, y \in {1, 2}, z \in {1, 2}] == x + y + z

(*--algorithm AcceptFunctionDefinitionThreeBindersGoCodegen {
    process (P = PID)
        variables
            \* @type: Int;
            w = 0;
    {
    p1: w := g[1, 2, 1];
        goto Done;
    }
}*)
====
