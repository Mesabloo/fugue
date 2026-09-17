---- MODULE AcceptFunctionDefinitionSingleBinderGoCodegen ----
\* Expect: accepted, all the way through Go code generation. A single-binder top-level function
\* definition -- `Parser_/TLAPlus.lean`'s `parseDeclaration` had no production for
\* `Declaration.function` at all until now, so this arity, the one most real specs would actually
\* write, had no coverage anywhere in this corpus despite every downstream stage (checker,
\* `Network2Go/Definition.lean`'s `FnConstructor`/`MkRecFn` path) already supporting it.

EXTENDS Naturals

CONSTANTS
    \* @type: Address;
    PID

\* @type: Int -> Int;
f[x \in {1, 2}] == x + 1

(*--algorithm AcceptFunctionDefinitionSingleBinderGoCodegen {
    process (P = PID)
        variables
            \* @type: Int;
            z = 0;
    {
    p1: z := f[1];
        goto Done;
    }
}*)
====
