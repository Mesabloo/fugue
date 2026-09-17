---- MODULE AcceptFunctionDefinitionMultiArgTupleDomain ----
\* Expect: accepted -- a well-typed 2-binder function definition. `f`'s domain is the 2-tuple
\* `<<Int, Int>>`, matching its 2 binders, per `Elaborator/Declarations.lean`'s `.function` rule.

EXTENDS Naturals

\* @type: <<Int, Int>> -> Int;
f[x \in {1, 2}, y \in {1, 2}] == x + y
====
