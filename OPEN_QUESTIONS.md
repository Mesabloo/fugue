# OPEN_QUESTIONS.md

Open questions and known issues. Ask before resolving any unilaterally. `PLAN.md` and other
docs cross-reference these as `§9.x`.

**Resolving one: delete it from this file** and write the decision into `PLAN.md` as settled
fact. No "resolved" markers, no strike-throughs. Gaps in the numbering are fine — don't
renumber.

---

### 9.1 Join Calculus: what happens after emission?
Committed scope (§2/§5.6) is "emit a syntactically well-formed `.join` file implementing the
thesis's compilation scheme." Open: (a) an interpreter for the guarded dialect (closest to
"formally verified compiler" in spirit — far easier to relate to a Lean model than real Go
concurrency), (b) a further lowering to something existing tooling runs (JoCaml-compatible
encoding, with the performance caveat the thesis flags), or (c) nothing, treating the output
purely as a verification artifact. Revisit once §5.6 exists.

### 9.2 Known parser gaps
Not blockers, none hit by §8's subset:
- Incomplete TLA⁺ reserved-word list (`TLAPlus.lean:62`); no binary/octal/hex number literals
  (`TLAPlus.lean:376`); no handling of junk before/after the module (`TLAPlus.lean:1135`).
- PlusCal `procedure`/`define` unsupported (`PlusCal.lean:423`) — `Core/SurfacePlusCal/Syntax.
  lean` has no AST nodes for them; `procedure` needs call-stack runtime semantics, `define` needs
  `Elaborator` scoping, neither is "pure syntax" the way `macro` was. `macro` itself is supported
  (`Desugarer/PlusCal.lean`'s `Algorithm.expandMacros`, a pre-desugar textual-substitution pass).
- `LET`/`IN` are lexed (`.let`/`.in` tokens exist) but have **no parser rule at all**. `CHOOSE`
  used to be in the same state; it now has one (`parseChoose`, bounded and unbounded both).
- `@type` supports only the Apalache-style syntax (`Channel({type: Str, agent: Address})`); the
  pre-Apalache dialect (`Channel[{type: string, agent: T}]`) is not.

### 9.3 CLI / UX — remaining details
Flag surface settled (§2), `-X<name>` included. One thing left open:
- **Join Calculus "flavors"** (`-t join[jocaml]`, `-t join[jerlang]`) — selecting between
  lowerings for different Join Calculus runtimes; ties into §9.1. Possibly not worth the
  complexity — don't build unless asked.

Resolved: the Go package name is `-Xgo-pkg:<name>`, defaulting to `main` — a property of the
output rather than of the compiler's behaviour, so `-X` rather than a `-p` of its own. `-o` names a
**file**: a compile emits one Go file, because everything lands in one package and Go compiles a
package as a unit, so splitting per process would buy nothing.

### 9.4 Join Calculus operational semantics — low priority
`Core/JoinCalculus/Semantics/` (RCHAM heating/cooling + reaction rules, thesis Fig.
8.4.2–8.4.3, local and distributed) isn't wanted now — getting `Network2JoinCalculus` to
compile is the near-term goal. Only matters once there's appetite to prove something about
that pass (prerequisite for §9.1).

### 9.5 Multicast compilation is undescribed for the Join Calculus backend
`multicast(x, [y ∈ e1 ↦ e2])` is in the v1 subset (§8). §5.6's Join Calculus scheme only shows a
single `send(c[α],e)` folded into a reaction body — unclear whether emitting to a filtered set
means one atom per recipient (which needs a bounded loop/comprehension inside a reaction body,
not obviously supported by the target calculus) or something else.

The Go side is settled and implemented (§5.2 for the filter collapse, §5.7 for the compiled
call), and does not constrain this: what it settles is that the *iteration* need not appear in
emitted code, which is an option the Go runtime library has and the target calculus may not.
What it does supply is the input shape — `CorePlusCal.Multicast` is a recipient set plus a
payload keyed by recipient, with no bind list left to destructure, so whatever this backend
emits starts from the same two pieces.

### 9.6 Runtime value representation in Go: channel capacity
TLA+ `Int`/`Nat` are unbounded and FIFOs uncapacitated; Go's types and channels are bounded.
The numeric side is resolved (§2, §5.7): arbitrary precision by default, machine integers
behind the `fugue_machint` build tag, no Fugue-level flag.

The channel-capacity side no longer belongs to the compiler at all (settled, §5.7): `send`
compiles to `Sender[τ]`'s `Send`, whose contract is "may block, no error result", so capacity
is a property of whichever endpoint implementation the person wiring the system supplies —
generated code neither picks it nor can observe it.

What remains is a hypothesis about *any* bounded implementation: because lock inference (§5.7)
already serializes atomic blocks touching shared state, a blocking `Send` shouldn't change
*which* transitions are enabled — at worst it slows execution. Holds for the Go-channel-backed
endpoints in the Ping-Pong end-to-end run (§5.7). Unconfirmed for a socket-backed endpoint,
where blocking comes out of the socket plus runtime buffering rather than a capacity anyone
chose; re-check whenever a reference transport gets written (§5.7's deferred-scope note).

**Known, accepted risk:** a block that blocks in `Send`/`Recv` *while holding its component's
lock* freezes every other block sharing that lock — potentially including the process's own
`T_rx` thread. Stays local to that one process; what unblocks it is the peer's own code
eventually receiving. Failure mode is "one process goes locally unresponsive," not a
system-wide deadlock.

### 9.10 `LAMBDA` — designed, not implemented
Thesis has typing rules (Fig. 3.1.4), but neither `SurfaceTLAPlus.Expression` nor
`CoreTLAPlus.Expression` has a constructor, and there's no `LAMBDA` lexer token. Out of scope;
implementing touches `Parser_/TLAPlus.lean`, both `Syntax.lean`s, `Desugarer/TLAPlus.lean`, not
just the checker.

Design, preserved:
- **Checking-only without an annotation** (thesis Fig. 3.1.4) — `Γ, x1:τ1, ..., xn:τn ⊢ e ⇓ τ ⟹
  Γ ⊢ LAMBDA x1,...,xn : e ⇓ (τ1,...,τn)⇒τ`, requiring the expected type already known.
- **Synthesis form once every binder carries `@type`** — mirroring unbounded quantification:
  `(LAMBDA (* @type: Int; *) x : x + 2)(3)` should synthesize. (The thesis's `LET`-`IN` rewrite
  workaround doesn't apply here — this AST has no `LET`-`IN` node either.)
- **AST work needed:** a `.lambda (binders : List (String × α)) (body : Expression α)`
  constructor on both expression types, a per-binder annotation slot so `tryParseAnnotations` can
  attach `@type` per binder (matching `parseQuantifierBound`), a lexer token, a parser rule, a
  pass-through desugarer case, both checking and conditional synthesis rules.

`Operator`-vs-`Operator` structural subtyping (`Elaborator/Subtyping.lean`, Fig. 3.1.8) only ever
produces an identity coercion precisely because there's no `LAMBDA`-equivalent way to eta-expand
into a new first-class operator value.

### 9.11 Most temporal/action operators aren't parsed; `WF_e(A)`/`SF_e(A)` have no parser rule
`UNCHANGED`/`ENABLED`/prime/`~>`/`-+>`/`[]`/`<>` have real surface syntax and desugar to plain
`opCall`s onto builtin `var`s, so the generic `OPERATOR CALL` rule already covers them. **Most
other temporal/action operators are not parsed.** `WF_e(A)`/`SF_e(A)` (thesis Fig. 3.1.5) lex
correctly — `WF_`/`SF_` are their own tokens (`Parser_/TLAPlus.lean`'s `identifierOrKeyword`
matches them ahead of the maximal-munch identifier scan, so `WF_e` lexes as `WF_` then `e`,
`RejectWeakFairnessNotParsed` pins it) — but `parseAtom` has no production for either: `WF_`/`SF_`
reach the parser as unexpected tokens.

`^+`/`^*`/`^#` (postfix action-closure) have **no documented typing rule anywhere** — not in the
thesis, not standard TLA⁺ as far as traced. Left unbound in `builtinContext`; referencing one
fails at `unboundVariable`. Their canonical names are in `WellFormedness/Restrictions.lean`'s
check-3 list for forward-compatibility, currently inert.

### 9.12 Regression fixtures parked as `xfail`
All run, all still fail as described, and an unexpected pass is reported as XPASS. They were
`skip_*` files until phase 4; skipping meant they could quietly start working and nobody would
know.

**Left this list.** `AcceptFunctionDefinitionMultiArgTupleDomain.tla` — `Parser_/TLAPlus.lean`'s
`parseDeclaration` had no production for `Declaration.function` at all, so no module-level
function definition of any arity could be written, whether or not its shape would type-check.
Fixed by adding `parseFunctionDefinition` (binder list = `sepBy1 comma parseQuantifierBound`,
reusing the same grammar `\A`/`\E`/set-builders already use rather than a narrower one) and
dispatching to it from `parseDeclaration` on a `[` peek past the leading identifier. Sidecar
dropped, fixture passes for real; a companion, `…GoCodegen.tla`, pairs the same definition with a
process that calls it and asserts `goBuild: true`, since this fixture's own module has no
algorithm and so never reaches `Network2Go` at all.

**Also left this list already:** `AcceptFunctionLiteralCartesianProductBinder.tla` — `\X` typed
(`(Set(a), Set(b)) => Set(<<a,b>>)`, `builtinContext`) but had no Go compilation: a product's
elements are pairs, and a tuple compiles to an *anonymous* struct only the site building it can
name, so a runtime `SetProduct` could not construct its own elements the way `SetUnion` does.
Fixed by taking the pair constructor as a callback, the way `SetMap` takes its mapping function —
`runtime/tlaplus/sets.go`'s `SetProduct`, called from `Network2Go/Expression.lean`'s `"\\X"` case.
No dictionary parameter or renormalizing pass needed there, unlike `SetMap`: the pair constructor
is always injective and row-major order over two sorted inputs is already ascending in the tuple's
own lexicographic order, so both invariants hold by construction. Sidecar dropped, fixture passes
for real (confirmed via a real `go build`, not just the in-process pipeline check).

**Three left this list by that last rule**, all rewritten as `Reject*` fixtures asserting the
rejection they actually produce, since each encodes a construct outside §8:
- `RejectUnboundedChooseWithExpectedType` (was `Accept*`) — `CHOOSE` parses now (§9.2's gap is
  closed), and the fixture type-checks through `Elaborator/Expressions.lean`'s checking-mode
  `[Unbounded choice]` rule, so what it really exercises is check 3's `unboundedQuantifier`
  (`E0054`, `wellformedness`). §8 has no unbounded quantifier.
- `RejectMulticastMultiComponent`, `RejectMulticastPartialAnnotation` (both were `Accept*`) — a
  multi-component multicast filter (§5.2) makes the recipients a tuple, so the channel's domain is
  one, and the `Network` struct holds `map[comm.Address]`; the Go backend rejects it with `E0061`
  at `go`, the same limit `compileSend` has for a channel indexed by more than one bracket group.
  §8's multicast is single-binder (`multicast(x, [y ∈ e1 ↦ e2])`), so the multi-component form is
  outside the v1 subset and the rejection is the expectation. The second of the two remains the
  only route to W0005 (`partial-multicast-annotation`); the warning fires and is asserted there,
  now alongside the error.

**`\X` is binary here**, with a precedence and left associativity, though
`Core/SurfaceTLAPlus/Syntax.lean` notes it is not really binary in TLA⁺'s grammar. So `A \X B \X
C` is `(A \X B) \X C`, whose elements are pairs holding a pair rather than the flat triples TLA⁺
means. Nothing accepts the wrong shape — `collapseToSingleBinder` projects component `i` as
`z[i]`, and `z[3]` on a pair is caught by the tuple-index bound — but a genuinely n-ary `\X`
(needed before three-component products of any kind work, including multicast filters) is
unwritten. Binary `\X` itself compiles to Go now (`SetProduct`, above); this paragraph is only
about the n≥3 shape.

### 9.13 Two well-formedness checks are currently unreachable
The rule is right in each case; the parser/type-checker just can't produce the triggering input:
- **Check 2(b)'s `nonEmptyLocalChannels`**: `Parser_/PlusCal.lean`'s `parseProcess` hardcodes
  `channels := []`/`fifos := []` — never parses process-level `channels`/`fifos` at all. No
  fixture can exercise the reject side; defense-in-depth only.
- **Check 1's `channelInExpression` via `receive`'s destination `r`** (not the check as a whole
  — `assert ch = ch;` exercises it directly). The only route to a Channel-shaped `r` past type
  checking was a channel-of-channels source (`Channel(Channel(τ))`, needed for `Channel`'s
  reflexivity-only subtyping to accept the `receive`), which `sendable` (§5.3) now rejects at
  declaration time.

Both confirmed correct via direct calls, just not end-to-end through a `.tla` fixture.
Revisit once: (a) the parser gains process-level `channels`/`fifos` (probably never worth it,
given 2(b) is explicitly defense-in-depth), or (b) another route to a channel-shaped `receive`
destination appears (none known; `Channel`'s reflexivity-only subtyping and the lack of another
channel-shaped type constructor make it look structurally unlikely, not proven impossible).

**Check 3's `unboundedQuantifier` is no longer on this list.** Unbounded `\A x : P`/`\E x : P`
still cannot trigger it — the binder's type can never reach an annotation (`parseQuantifier`'s
unbounded branch is bare `parseIdentifier`, no `tryParseAnnotations`), so it fails at
`TCError.expectedTypeAnnotation` first. Unbounded `CHOOSE x : P` in checking position does,
though: `Elaborator/Expressions.lean`'s `[Unbounded choice]` rule takes the type from the expected
type rather than an annotation, and `CHOOSE` now parses (§9.2). End-to-end fixture:
`RejectUnboundedChooseWithExpectedType`.

### 9.14 Should intrinsic operators get dedicated AST constructors instead of `opCall`?
Every builtin, intrinsic or stdlib, is `.opCall (.var name _ origin) args`. Keeps the checker's
op-call rule uniform (one generic rule plus a `Γ`/`builtinContext` lookup), but pushes every
downstream pass needing to special-case a builtin into re-deriving its own string/`Origin` match
— `WellFormedness/Restrictions.lean`'s `reservedTemporalActionNames`, `Typed2Computable`'s
computability classification, and both backends unconditionally (stdlib operators "get replaced
by backend-native implementations at code-generation time regardless of what their 'definition'
says"). The shared recognizer table (`Core/TypedTLAPlus/Builtins.lean`, §2) is the near-term
fix, in place — open is whether that's enough long-term.

Scope: intrinsics only — `builtinContext`'s ~14 `EXTENDS`-independent entries (`=`, `/=`, `/\`,
`\/`, `=>`, `<=>`, `\neg`, `\in`, `\notin`, `\subseteq`, `\cup`, `\cap`, `\`, `DOMAIN`, plus the
temporal ones in §9.11) — **not** vendored stdlib operators (`Naturals`/`Sequences`/`Bags`/
`FiniteSets`, §5.3's `builtinModules`). Intrinsics are a small closed permanent set baked into
every module; stdlib operators are open-ended declarations in an ordinary (if hardcoded)
`Module`, and giving those constructors would mean one per `Len`/`Head`/`+`/…, undermining the
point of representing them as ordinary declarations.

### 9.15 Infinite set used as a quantifier/set-builder domain
**Representation half resolved.** `Set[T]` (`runtime/tlaplus/sets.go`) is now a tagged struct —
finite `elems` slice xor an infinite `pred` predicate, never both — so `Nat`/`Int` compile to a
real value (`NatSet`/`IntSet`) instead of `compileBuiltinVar` rejecting them outright. `\A x \in
Nat : P`/`\E x \in Nat : P`/`CHOOSE x \in Nat : P`/`{e : x \in Nat}` still can't run — enumeration
needs a finite slice, `Nat` has none — but now panic cleanly instead of not terminating: real fix
over the old framing below, a panic is diagnosable and a hang isn't. `{x \in Nat : P}` is the
exception — restricting an infinite set never needs enumerating it, so `SetFilter`'s infinite
branch just works, no panic. Full accounting of what panics vs. what doesn't: `sets.go`'s own doc
comment, not repeated here.

**Was wrong, now fixed:** the "Settled, not part of this gap" paragraph here used to claim
`Typed2Computable`'s no-restriction behavior on `[x \in Nat |-> x * x]` was already correct as an
*implementation* fact. It wasn't — `LazyFunction.dom` (`runtime/tlaplus/functions.go`) is typed
`Set[T]`, and the old finite-only `Set[T]` had no way to hold `Nat`, so this actually failed at
`Network2Go` (the same `compileBuiltinVar` rejection above), not merely "unrestricted at the
type-checking layer" as the old wording had it. True now: the predicate branch lets
`LazyFunction.dom` hold `Nat`/`Int` for real, so `[x \in Nat |-> x * x]` compiles and runs.

**Not affected by the denotational semantics.** `Core/ComputableTLAPlus/Semantics/Interface.lean`
keeps evaluation abstract (`class ExprSemantics`), so `Core/*/Semantics/Denotational.lean` says
nothing about quantifier or set-builder domains either way. This stays a `Network2Go`/§5.7
question, and whichever `ExprSemantics` instance eventually models TLA⁺ inherits it unchanged.

**Still open: admission control.** Whether/how to *reject* an infinite domain at
`forall`/`exists`/`choose`/`collect`/`map'` (and PlusCal's `with x \in dom`) at compile time, ahead
of the runtime panic above — a separate, genuinely optional UX question the representation fix
does not settle. Two options, neither committed:
- **Narrow syntactic check**: reject a *direct* bare reference to a known-infinite builtin set
  (`Nat`/`Int`) at exactly these positions — misses derived cases (`Nat \ {0}`, `Nat \cup {1}`,
  an operator returning `Nat`).
- **Track possible-infiniteness with an invariant**: most infinite sets encountered (`Nat`,
  `STRING`, `[Nat -> Nat]`) denote "the universe of all values of some type", possibly
  summarizable rather than needing general finiteness inference. Weaker than it looks, though:
  a PlusCal `variable` reassigned from `Nat` (or a derived expression) on one branch needs a
  single static tag covering every value it's ever assigned, across every branch — the
  conservative join collapses to "possibly infinite" for that variable's entire remaining
  lifetime, not just at the assignment site. Catches the direct, unmutated case; buys nothing
  extra once `variables` are involved. Not worth building past the narrow check above for that
  reason, not merely "possibly."

Revisit once §9.14's recognizer-table shape settles (it determines how cheap a fix is). Less
urgent than before: the runtime panic is already a real backstop, not a hang.

### 9.17 No proof `subtype` and `Coercion.apply`/`.applyComputable` agree on type
`Coercion` is real closed data, not an opaque closure, which makes a real theorem statable; none
written. Checked only empirically — `tests/regression/` fixtures plus one hand-verified dump.

**Open:** what to prove, roughly `subtype τ τ' = .success c → ∀ e, Γ ⊢ e : τ → Γ ⊢ c.apply e :
τ'` — likely two statements, one per `apply`/`.applyComputable`, since they discharge against
different `Expression` types. Also open whether this falls under the well-scopedness-preservation
exception in `INSTRUCTIONS.md`'s verification-scope rule or is a separate ask;
`INSTRUCTIONS.md` names only well-scopedness preservation as in scope. Don't start without
check-in.

### 9.18 `lub` isn't a real join, so `IF`/`CASE`/set-literal *synthesis* over incomparable branches fails
`Elaborator/Subtyping.lean`'s `lub` returns the wider of its two arguments, or `none` when
neither is a subtype of the other — it can only ever return a type already handed to it, never
name a common upper bound that isn't one of the two inputs. `lubAll`
(`Elaborator/Expressions.lean`) folds it left across branches, so `IF`/`CASE`/`{e₁,…,eₙ}` in
*synthesis* position succeed only when the join happens to *be* one of the branch types;
otherwise `TCError.ambiguousType`.

Concretely: `IF c THEN "ab" ELSE <<1, 2>>` has branch types `Str` and `⟨Int,Int⟩`, whose common
upper bounds are `Seq(Int)` and `Int → Int` — neither producible by `lub`, so the fold fails on
the first pair. Order-sensitive for the same reason: the same branches with an `Int → Int` one
placed first succeed, since the join is then already in the accumulator. `lub` itself is
symmetric; the order-sensitivity is the fold's.

Distinct from `lub`'s *partiality*, which is correct and stays: `lub Int Str` is genuinely
`none` — `Int` has no axiom out of it, so no shared upper bound exists, and `ambiguousType` is
right. The gap is only pairs that do have a least upper bound and get rejected anyway.

**Not a blocker, by design.** §5.3 already commits to the matching trade on the metavariable side
("error and require an explicit annotation instead of implementing `lub`"), and thesis §3.1.3.6's
*checking* rules for `IF`/`CASE`, both implemented, make that escape hatch reachable: given an
expected type, each branch is checked against it directly and picks up its own coercion. The
example type-checks under an annotation
(`Tests/regression/AcceptIfCheckedHeterogeneousBranches.tla`,
`AcceptCaseCheckedHeterogeneousBranches.tla`). The limitation bites only in annotation-free
synthesis position.

**Open, quite possibly permanently:** whether to make `lub` a real join. Doing so means a
structural recursion mirroring `subtype`'s case split but producing a type rather than a
`Coercion` (`join (Set a) (Set b) = Set (join a b)`, records/tuples pointwise on matching shapes,
an axiom-widening fallback), plus a mutually-recursive `glb` for `function`'s contravariant
domain — roughly duplicating `subtype`'s ~90 lines for a case no fixture needs. Unchecked
prerequisite: folding a partial join pairwise is order-independent only if the subtype order is
**bounded-complete** (any two types with a common upper bound have a least one). Not verified;
`function`'s contravariant domain is where a counterexample would most likely hide. If it holds,
fixing `lub` suffices and `lubAll` stays a plain fold; if not, the join must become genuinely
n-ary and `lubAll` goes away. Don't start either without checking bounded-completeness first, and
don't start at all unless a real program hits this.

Cheap adjacent improvement, unclaimed: `TCError.ambiguousType`'s message
(`Elaborator/Errors.lean`) states the symptom without naming the fix. Pointing it at "annotate
the expected type" would make the workaround discoverable. Both throw sites are inside `lubAll`,
so no other caller's wording constrains it.

### 9.22 The module progress line ignores `-W`
`Driver/Modules.lean` reports `ModuleOutcome.built (hadWarnings : Bool)`, and `Fugue.lean` renders
it as a yellow `⚠ [1/1] Built <Module>` when the flag is set. `hadWarnings` counts warnings as
*reported by the pass*, before `-Wno-<name>` filtering, which happens later in
`PipelineResult.renderWarnings`. So `fugue compile -Wno-duplicate-parameter` on
`AcceptDuplicateParameterWarns.tla` correctly prints no warning, and still marks the module
yellow with a warning dingbat for a warning the user asked not to hear about.

Pre-existing; unrelated to the pipeline extraction that surfaced it.

**Open:** which of the two is wrong. Either the outcome should be computed after filtering (`-W`
then genuinely silences the diagnostic everywhere, and `hadWarnings` needs the `FlagsEnv` at the
point it is built), or the dingbat is deliberately reporting "this module produced warnings"
independently of whether they were displayed, and only the colour is misleading. Matters for the
regression runner once it asserts on progress lines rather than only on diagnostics.

### 9.23 Six fixtures asserted something they did not exercise
Found by phase 4's sidecars: every rejection now records the stage and code it must produce, and
six fixtures produced something else. All six passed `run.sh`, which only ever asked for a nonzero
exit.

**Three are fixed.** `RejectGlobalTlaplusVariableCrossModule` and `RejectTransitiveTemporal` failed
at `resolve` (`E0021`) because their `EXTENDS` could not be found: `Driver/Modules.lean`'s `locate`
looks for `<ModuleName>.tla`, and the corpus named files in snake_case. Renaming every fixture to
its module name — which TLA⁺ requires anyway, and which nothing had been checking — makes both
resolve, and both now produce exactly what their headers always claimed: `E0052`
(`globalTLAPlusVariable`, check 2(c)) and `E0053` (`bareTemporalOrAction`, check 3 transitive).
`RejectAssignThenReceiveSameVariable`, which did not parse at all, was repaired by hand and now
produces `E0018` (`conflictingAssignment`) at `desugar`, as its header always said.

**Three were parked**, renamed from `Reject*` to `Skip*` with a sidecar `reason` the runner prints
on every run. `Skip` rather than `xfail` because the fault is in the fixture, not the compiler:
each claims to test a pass it never reaches, and fixing the compiler would not make it start
testing that pass. **All three are back.**

`SkipUnboundedChooseSynthesisPosition` was parked for the `CHOOSE` parser gap; that gap is closed
(§9.2), so `print CHOOSE x : x = x` now reaches the type checker and produces the `E0028`
(`cannotInferType`) its header always claimed. Back as `RejectUnboundedChooseSynthesisPosition`,
`status: ok`.
`SkipOperatorParamArityMismatch` was parked because its `@type` annotation died at annotation
parsing (`E0005`): `Parser_/Annotations.lean`'s `parseType'` could not nest an operator-shaped
(`=>`) type inside another operator type's argument list. That gap is closed too, so
`((Int) => Int, Int) => Int` now parses and `Op(F(_,_), x) == x` reaches `checkParamArity`, which
produces the `E0039` (`paramArityMismatch`) its header always claimed. Back as
`RejectOperatorParamArityMismatch`, `status: ok`, `failsAt: typecheck`.
`SkipFunctionDefinitionDomainNotTuple` was parked for the function-definition parser gap (§9.12);
that gap is closed too, so its 2-binder function definition now reaches the type checker and
produces the `E0038` (`notATupleType`) its header always claimed. Back as
`RejectFunctionDefinitionDomainNotTuple`, `status: ok`, `failsAt: typecheck`.

All three un-parkings were noticed by hand, not by the suite, which is the point of tracking them
here rather than leaving them silently skipped.

### 9.33 Reachability walk recurses into builtin-module definition bodies
`WellFormedness/Reachability.lean`'s `walkReachable`, on a `.var _ (.module m name)` that resolves
to an `operator`/`function`, recurses into its body — including when `m` is a builtin module
(`Naturals`, `Sequences`, `Fugue`, …). Every such body is now self-referential (`Op(x) == Op(x)`,
`Driver/Builtins.lean`), so the walk takes one wasted step per builtin reference and then stops on
its memo (or on `resolveInModule`'s `currentModule == targetModule` branch resolving `name` against
the *caller's* `ownDecls`, where it is absent). Backends replace every builtin call regardless of
its body (`PLAN.md` §5.3), so the recursion re-reaches nothing.

Fix: when the resolved declaration's module is in `builtinModules`, record the `(module, name)`
pair and stop — never walk the body. Both consumers already want exactly that: `Typed2Computable`
drops every closure entry whose origin hits `builtinOpOf?`, and `Restrictions.lean`'s transitive
temporal/action check keys on the builtin origin directly. Check the elaborator's own use of the
walk for the same recursion, and confirm against §9.13's two already-unreachable checks that
nothing reachable becomes unreachable.

### 9.34 No type synthesis for an unannotated operator/function definition
`Elaborator/Declarations.lean`'s `[Operator definition]`/`[Function definition]` cases open with
`requireAnnotation`, so `X == 0` (or `Y == 0 - 0`, `Op(x) == x + 1`) is rejected with `E0027`
without ever looking at the body — no attempt to synthesize `X : Int` from `0 ⇒ Int`. This matches
thesis Fig. 3.1.9, whose rule conclusions carry the type in the syntax (`f(x⃗) ⦂ (τ⃗)⇒τ ≜ e`) and
check the body against it; §3.1.4 explicitly notes the non-recursive case *could* be inferred and
requires the annotation anyway, for uniformity with the recursive case (where inferring `f`'s type
needs `f`'s type).

Open: whether to add a synthesis path for the unannotated, non-`RECURSIVE` case — `inferExpr body`
(already implemented, used everywhere else), bind `f` at the synthesized type, keep
`requireAnnotation` only when the body is in checking-only position or `f` is recursive. Cheap
given the bidirectional machinery; a deliberate step past the thesis. `CONSTANT`/`VARIABLE`
annotations stay mandatory regardless — they have no body to synthesize from.
Item 7 §9.5 (thesis phase 10, P3): `Core/{Guarded,Network}PlusCal/Semantics/Denotational.lean`'s
`Statement.reducing`/`.aborting` still have `multicast = ∅` (four sites, `TODO(item 7)`). Prior
art left the same case `sorry` in both — no existing shape to port.

`ComputableTLAPlus.ExprSemantics.mem : V → V → Prop` is a bare membership *relation*; there is no
`enumerate : V → List V` (or similar) to pull a concrete recipient list out of a set value. A
`multicast`'s `reducing` is meant to be "a set-indexed family of `send`s, folded over the evaluated
address set" (plan §1 P3), which needs such a list to fold over.

Proposed, not yet implemented: characterize the recipient list *relationally* instead of
computing it — `∃ recipients : List V, (∀ r, r ∈ recipients ↔ ExprSemantics.mem r S) ∧
recipients.Nodup ∧ …` — matching `Eval`'s own relational style ("no derivation tree" already
*is* "no value", `Semantics/Interface.lean`'s module doc). `Nodup` rules out the degenerate
reading where the same recipient is sent to twice. Fold sends over `recipients` via a new
inductive relation (`MulticastFold` for `reducing`, `MulticastAborts` for "the fold gets stuck
partway"), each recipient keyed as `(c, [.inr r])` — the recipient value as the channel's one
index segment, matching an ordinary `chan[addr]` reference's own indexing convention.

Open: whether this relational-enumeration approach is right, or whether `ExprSemantics` should
instead grow an actual enumeration field (bigger surface, but avoids `Nodup`-as-a-proxy-for-
"this is really a set" and the resulting order-nondeterminism in `reducing`'s outcome set).
Blocks P3, and P6/D4 (whose generic action-statement lemma quantifies over every action
constructor, `multicast` included) until resolved.

### 9.31 `CorrectInstance` private-import workaround
`Guarded2Network.lean` imports `Guarded2Network.CorrectInstance` privately (bare `import`) so plain
`lake build` builds and checks the concrete-`Value` refinement proof (`correct''`,
`assert_no_sorry`). Must be private: `zflean`'s `ZFLean/Basic.lean:172` `notation " ε "` is global,
and a `public import` re-exports it into `Driver/Pipeline.lean` (`runStage {ε}`) and later passes,
where `ε` is a type variable.

Cost: a private import is not re-exported, so downstream code doing `import Guarded2Network` cannot
reach `correct''` — using it needs a direct `import Guarded2Network.CorrectInstance`, which
re-triggers the clash. Blocks further development on top of the correctness theorem.

`zflean` makes the `ε` notation scoped in its `v4.33.0` release. The lockfile pins
`zflean @ v{Lean.versionString}`, so this arrives with the toolchain bump to Lean 4.33. Revisit
then: `public import Guarded2Network.CorrectInstance` and drop the workaround.

### 9.35 `EvalBuiltin` has no rule for `Cardinality`/`IsFiniteSet`/`Address` order
`Core/ComputableTLAPlus/Semantics/Operational.lean:232-236` doc comment: these denote nothing in
the reference operational semantics — no `EvalBuiltin` arm, each already total and closed-form
elsewhere (`FiniteSets!IsFiniteSet`/`Cardinality`: every `Value` set is finite by construction; the
`Address` order: unspecified by design, `runtime/comm/address.go`). `Bags` (resolved — all 13
operators now have real rules, `PLAN.md`'s builtin-module section), `MkSeq` (resolved — real rule
now, same section), and `SetAsFun` (resolved — real rule now, same section) no longer belong in
this entry. `Cardinality`/`IsFiniteSet`/`Address` order stay, untouched, still open.

Cost: `Network2Go` already compiles `Cardinality`/`IsFiniteSet` and the `Address` order operators
proof-free — nothing shows compiled behavior matches spec for them.

To resolve: per operator, decide (a) add an `EvalBuiltin` rule — and, separately, whether to also
prove `Network2Go` sound against it, since no such proof exists for *any* operator yet, `Bags`
included — or (b) accept permanently proof-free codegen and record that choice here rather than
leaving it implicit in the doc comment.

### 9.36 `with x ∈ S` compiles for Go, against the thesis's own call

Deliberate divergence, not a gap. Thesis §7.2.3.1 rejects a set-valued `with` outright: "we
choose not to support such constructs as they do not necessarily carry much computational
meaning anyway." `Network2Go/PlusCal.lean`'s `compileGuard` used to match that, throwing
`E0061` (`Tests/regression/RejectWithSetBinderInGo.tla` pinned it). Compiles now instead,
through `Pick` (`runtime/tlaplus/sets.go`) — already there, used for a `variable x ∈ S`
initializer, just not wired to the statement form. `PLAN.md`'s §7 write-up (the "Guards"
bullet) has the mechanics; `Tests/regression/AcceptWithSetBinderInGo.tla` is the fixture
(renamed from the reject one).

Why diverge: the thesis's own objection is that no principled deterministic search exists —
true, and irrelevant here, since nothing about `Pick` searches. It draws once, uniformly,
from whatever `S` denotes at that attempt; if a guard after the `with` then rejects the
draw, the branch just fails the way any other unmet `await` does, and the block's retry
loop (already there for every atomic block, thesis §7.2.3.1's own scheduling model) draws
again next iteration. Every TLA⁺ behavior the spec allows for a satisfying draw is still
reachable — just not on every attempt, same as `either`/`or` branch selection already
isn't.

Cost: no proof obligation crosses this — `Network2Go` is unverified/informal throughout
(§7.4, §5.7), same footing as multicast, lock inference, and everything else this pass
does. `AcceptMultiBinderWithDesugarsToChain.tla` still uses only `=` binders; that's
unrelated now (it isolates multi-binder-desugars-to-a-chain from set-binder Go
compilation, not a workaround for this).

Still open: whether `Pick`'s uniform distribution is worth documenting as part of the
compiled program's *meaning* (a spec that happens to depend on a fair distribution over `S`
— e.g. probabilistic liveness — would silently get one from this compilation, never
promised by the TLA⁺ source) or should stay an implementation detail nobody should rely on.
Leaning the latter (TLA⁺'s `with` promises no distribution, only "some" outcome across
behaviors) but nothing pins it down in writing yet.

### 9.37 `RECURSIVE` operators out of scope — revisit criteria and design not pinned down

`RECURSIVE` out of scope for now, `PLAN.md` §2/§8 (its language-subset-exclusions row) and
§9's syntax-coverage list. No prior-art checkout (`distpcal-compiler`, `mesabloo/fugue`)
parses it either, so no existing shape to port. Only `RECURSIVE` *operators* — recursive
*functions* (`f[x ∈ S] == ...` referencing `f` in its own body) already work via the
`MkRecFn` tie-the-knot bootstrap, `PLAN.md`'s operator/function-definitions section — a
different mechanism, unaffected by this entry.

`PLAN.md`'s exclusions row already sketches a fallback if picked up: explicit type
annotation required on every operator in a `RECURSIVE` group's declaration, `Γ` extended
with all declared sibling types up front, each body checked against its own annotation
independently — breaks the circularity a mutually-recursive group creates for a
bidirectional checker (standard precedent: mutual `def`/`def` in Coq/Agda/Lean always carry
signatures), near-necessary for decidability under rank-1 polymorphism if any operator in
the group is polymorphic. That sketch stops at the checker; nothing designs the parser side
(TLA⁺ syntax lets `RECURSIVE f, g` predeclare a group, then separate `==` definitions bind
each — needs a two-pass elaboration: collect the group's names/annotations first, check
bodies after) or either backend (Go: same `MkRecFn`-style bootstrap as recursive functions,
but for an operator, which compiles to a Go func rather than a `LazyFunction` value —
ordinary Go function definitions already support mutual recursion natively, so this may be
free; Join Calculus backend not examined at all).

Open: whether to design and implement this, or leave `RECURSIVE` permanently excluded. No
known example program in this project's fixtures or thesis chapters needs it yet — revisit
if one does.

### 9.38 `channels` compile with FIFO (sequence) semantics; thesis wants `Set`/multiset

`reference/thesis.txt:1674` (§3.1.1): intended encoding is `Set(τ)` for `channels`,
`Seq(τ)` for `fifos` — kept as one `Channel(τ)` type only because "the distinction is only
meaningful when emitting code or when describing the semantics" (line 1688-1689), not at the
type level. §3.1.5's subtyping rule (line 2304-2305) allows either a multiset/bag or sequence
encoding for `Channel(τ)` — covariant either way — so the type theory doesn't force the
choice; codegen does, and codegen hasn't made it.

Compiler picks one encoding for both. `GuardedPlusCal.FIFOs`
(`Core/GuardedPlusCal/Semantics/Denotational.lean:106`) is `Finmap λ _ : ChanKey V ↦ List V`
— push-right/pop-left queue — and every `ChanKey` uses it, whether the source declared the
name under `channels` or `fifos` (`Declarations.channels`/`.fifos`,
`Core/GuardedPlusCal/Syntax.lean:208-209`: same `String × Typ × List Expr` shape, no tag
past which field it sits in). `Guarded2Network` (§5.5) compiles a receiving process's mailbox
to one shared `inbox` sequence fed by per-channel `.rx` threads — same `List`-backed queue,
so a `channels`-declared mailbox still gets strict FIFO delivery order. `PLAN.md:1642-1643`'s
own characterization of the state space (`LState = (Var → Value) × (Var → Value*)`) shows the
operational-semantics side collapses to one sequence-valued component too — the
`channels`/`fifos` split lives only in the surface syntax and the frontend typing chapter,
never reaches `GuardedPlusCal`/`Guarded2Network`.

Consequence: a spec whose correctness argument depends on `channels` reordering
(out-of-order delivery, no FIFO guarantee) compiles to something *stricter* than the source
permits — fewer reachable behaviors, not more, so nothing unsound, but a real gap between
what the source declares and what the target guarantees, silently resolved by picking
sequence order for everyone.

Fix shape: `Guarded2Network`'s inbox for a `channels`-declared `ChanKey` would need a finite
multiset (bag over `V`) instead of `List V`; `fifos`-declared keys keep `List`. `FIFOs` would
need that distinction carried per-key — derived once at `Declarations` construction, not
guessed downstream from naming ([[feedback_derive_dont_let_sites_choose]]'s rule) — likely a
split into two payload kinds rather than a flag. Needs a pop-any-element rule
(`Finset.erase`-then-insert or similar) replacing list-append/`Head` for the multiset case,
and the refinement proof (§6.2) would gain a second delivery-order relation alongside the
FIFO one it already has.

Open: implement now, or leave documented. No fixture exercises `channels` reordering today —
process-level `channels`/`fifos` don't even parse yet (§9.13) — so nothing currently breaks
silently; revisit once one does.

### 9.27 `multicast`'s denotational semantics has no enumeration primitive to fold over
Guarded→Network's refinement proof (§5.5) re-derives `GuardedPlusCal`/`NetworkPlusCal`'s
denotational semantics against the fresh `Core/GuardedPlusCal/Syntax.lean` AST — the proof's
mathematical content transfers from prior art, but `multicast`'s own semantics doesn't: folding
a `send` over a set value's members needs an enumeration primitive over `Set(τ)`, and neither
the fresh AST nor prior art supplies a shape for one. Open until Guarded→Network's proof reaches
the `multicast` case.

### 9.39 Type aliases in annotations (Apalache `@typeAlias`) — Lean representation not picked
Apalache lets a spec name a type once, reuse it elsewhere in `@type` annotations. Nothing here
supports this — `Annotation` (`Parser_/Annotations.lean:53`) has only
`@type`/`@mailbox`/`@parameter`; `Typ` (`Core/SurfaceTLAPlus/Syntax.lean:235`) has no
alias-reference case.

**Reference syntax settled: `$name`**, Apalache's own sigil. Rejected alternative: reusing a bare
identifier (same production as `.var`, a rigid type variable) and resolving the alias in a
post-pass — risks a real type variable silently colliding with an alias of the same name, a
distinction a future correctness proof would then have to carry rather than one dissolved at
parse time for free.

**Alias polymorphism settled as an explicit parameter list on the alias**, e.g. `@typeAlias:
msg(a) = Ok(a) | Err(Str);`, instantiated at each use as `$msg(Int)` — a deliberate divergence
from Apalache, whose aliases take no parameters and get polymorphism only indirectly, from a free
`.var` in the body resolved by unification at each use site. Chosen because the call site names
the intended instance directly instead of relying on unification to recover it. Not implemented
now — `Typ`/`parseType'` have no alias case at all yet — but the reference syntax above must keep
this addable without redesign: `$name` extends to `$name(τ₁, …, τₙ)` without ambiguity.

**Settled: a type alias is its own (virtual) TLA⁺ declaration, not a name→`Typ` side table**, and
may not appear inside a PlusCal algorithm. Falls out by construction once represented this way,
no separate check needed: `Module` (`Core/Declaration.lean:69-75`) holds `declarations₁`/
`declarations₂ : List (Declaration E β)` either side of `pcalAlgorithm : Option α` — a field of an
unrelated type — so a `Declaration`-shaped alias is structurally excluded from the algorithm
body. "Virtual" because, unlike `.constants`/`.variables`/`.operator`/`.function`
(`Core/Declaration.lean:22-32`), it carries no real TLA⁺ syntax of its own — synthesized entirely
from a comment.

**Open: how that declaration case is represented.** A standalone comment block containing only
`@typeAlias: name(...) = Typ;` with nothing else following is new grammar either way — today
every annotation decorates a declaration already being parsed for some other reason; nothing
produces a `Declaration` from a comment alone. Two shapes floated, not decided:
- A dedicated `Declaration.typeAlias` constructor.
- A generic `Declaration.annotation (_ : Annotation)` — a declaration that's just a standalone
  resolved annotation, so any future free-standing annotation reuses the same grammar case
  instead of earning its own `Declaration` constructor; what a `.annotation` value *means* (alias
  expansion, or rejected as meaningless anywhere else) is a later pass's job, not the parser's.

Either way, open whether it needs to live in the shared `Core/Declaration.lean` (touching
`SurfaceTLAPlus`/`CoreTLAPlus`/`TypedTLAPlus` alike, per that file's own doc comment) or can stay
`SurfaceTLAPlus`-only, fully expanded away by `SurfaceTLAPlus.Module.desugar` before `CoreTLAPlus`
— matching how §5.2's four surface-only expression transformations already disappear at Core
(`PLAN.md` §5.2). Aliases are pure notation with no runtime content of their own, so the latter
looks like the better fit, but not decided.

**Settled, diverging from Apalache: alias scope follows ordinary declaration order.**
`checkDeclarations` (`Elaborator/Declarations.lean:178-182`) folds `declarations₁ ++
declarations₂` left to right, extending `Γ` as it goes — each declaration sees only bindings
from declarations before it. A type alias represented as an ordinary `Declaration` inherits this:
`$msg` is in scope only for declarations textually after `@typeAlias: msg = …`, no forward
reference. Apalache itself has no such restriction — every `@typeAlias` comment in the module is
collected up front, module-wide, order-independent. Deliberate here: matches how every other TLA⁺
declaration already behaves, rather than carving out an exception for this one kind.

This also resolves the earlier worry about `PLAN.md`'s deferred `ParserWarning.unusedAnnotation`
(§5.1, lines 249-258): that detection is scoped to annotations inside a PlusCal algorithm body
(`parseUnlabeledStatement` calling `tryParseAnnotations`), and a type alias can no longer appear
there at all — so it can never reach that check, no carve-out needed.

Open: `Declaration.typeAlias` vs. generic `Declaration.annotation`, and which stage(s) own the new
case. Don't start without check-in.

