module

import Common.Position
public import Common.Errors

public section

/-- Errors produced while desugaring `SurfaceTLAPlus`/`SurfacePlusCal` into `CoreTLAPlus`/`CorePlusCal`. -/
inductive DesugarError : Type
  /-- `@` used outside of an `EXCEPT` update. -/
  | misplacedAt (pos : SourceSpan)
  /-- A `goto` is followed by more unlabelled statements — unreachable dead code (a `goto`
  followed by a label is fine). -/
  | gotoNotInTailPosition (pos : SourceSpan)
  /-- A statement appears before the first label of its enclosing thread — there is no label to
  attach it (or the block it starts) to. -/
  | unlabelledStatement (pos : SourceSpan)
  /-- A label appears inside a `with` body — never allowed, since a `with` binding only makes
  sense within one atomic step. -/
  | nestedLabel (pos : SourceSpan)
  /-- A `while` statement appears inside a `with` body, at any nesting depth. -/
  | whileInWith (pos : SourceSpan)
  /-- A `while` statement is not immediately preceded by a real, user-written label; none is
  auto-inserted. -/
  | whileNotLabelled (pos : SourceSpan)
  /-- A statement following an `if`/`either` that contains a labelled statement or a `goto`
  anywhere within it is not itself labelled. -/
  | notFollowedByLabel (pos : SourceSpan)
  /-- A statement writes into a variable currently bound by an enclosing `with` — an `assign`
  target or a `receive`'s target `Ref`. A `with`-bound name is a fixed local binding, not a
  process variable, so writing to it is meaningless. -/
  | withBoundVarWritten (pos : SourceSpan) (name : String)
  /-- An annotation-carrying slot only accepts specific kinds of annotation, but a different kind
  was found there. -/
  | wrongAnnotationKindAtSite (pos : SourceSpan) (found : String) (expected : String)
  /-- Two or more annotations of the same kind found at one slot, for a kind whose content can
  actually differ between instances (`@type`, `@mailbox`). Content-free markers (`@parameter`)
  get a warning instead (`DesugarWarning.duplicateParameterAnnotation`). -/
  | duplicateAnnotation (pos : SourceSpan) (kind : String)
  /-- The same bare variable (no index — `x`, not `x[…]`) is written more than once within one
  atomic step (`assign`/`receive`, any combination), on the same control path. Indexed writes
  (`x[0] := …`) aren't tracked by this check. -/
  | conflictingAssignment (pos : SourceSpan) (name : String)
  /-- The right-hand side of a record-access `.` is not a bare field-name identifier (e.g. `r.1`,
  `r.(f)`). -/
  | invalidRecordFieldAccess (pos : SourceSpan)
  /-- Two `macro` declarations share a name. `firstPos` is the earlier one's own span. -/
  | duplicateMacroDecl (pos : SourceSpan) (name : String) (firstPos : SourceSpan)
  /-- A label appears inside a `macro` body — never allowed, same restriction as `with`. -/
  | labelInMacroBody (pos : SourceSpan)
  /-- The macro call-graph (which macro name each declared macro's own body calls) has a cycle.
  `pos` is the flagged declaration's own span; `cycle` is the chain of calls closing the loop,
  outermost first, each entry the callee name and the call site inside its caller's body. -/
  | recursiveMacro (pos : SourceSpan) (cycle : List (String × SourceSpan))
  /-- A `Name(…)` call names no declared macro. -/
  | undefinedMacro (pos : SourceSpan) (name : String)
  /-- A macro call's argument count doesn't match its declaration's parameter count. `declPos` is
  the declaration's own span. -/
  | macroArityMismatch (pos : SourceSpan) (name : String) (expected got : Nat) (declPos : SourceSpan)
  /-- A macro call's argument is substituted into a parameter that the macro body writes to
  (`assign`/`receive`'s target, `send`'s channel), but the argument itself is not a reference
  (variable, possibly indexed/field-accessed) that can be written to. `writePos` is the span of
  the statement inside the macro body that writes to the parameter. -/
  | macroArgumentNotAssignable (pos : SourceSpan) (macroName paramName : String) (writePos : SourceSpan)
  /-- A `.macroCall` reached statement desugaring — every one should have been rewritten away by
  `Desugarer/PlusCalMacros.lean`'s expansion pass, which runs first in `runDesugarer`. Reported as
  a diagnostic rather than `panic!`/`unreachable!`, matching this compiler's own instinct of never
  taking the process down on a "should be impossible" path. -/
  | internalUnexpandedMacroCall (pos : SourceSpan)

instance : CompilerDiagnostic DesugarError String where
  isError := true
  code
    | .misplacedAt _ => Diagnostics.misplacedAt.code
    | .gotoNotInTailPosition _ => Diagnostics.gotoNotInTailPosition.code
    | .unlabelledStatement _ => Diagnostics.unlabelledStatement.code
    | .nestedLabel _ => Diagnostics.nestedLabel.code
    | .whileInWith _ => Diagnostics.whileInWith.code
    | .whileNotLabelled _ => Diagnostics.whileNotLabelled.code
    | .notFollowedByLabel _ => Diagnostics.notFollowedByLabel.code
    | .withBoundVarWritten .. => Diagnostics.withBoundVarWritten.code
    | .wrongAnnotationKindAtSite .. => Diagnostics.wrongAnnotationKind.code
    | .duplicateAnnotation .. => Diagnostics.duplicateAnnotation.code
    | .conflictingAssignment .. => Diagnostics.conflictingAssignment.code
    | .invalidRecordFieldAccess _ => Diagnostics.invalidRecordFieldAccess.code
    | .duplicateMacroDecl .. => Diagnostics.duplicateMacroDecl.code
    | .labelInMacroBody _ => Diagnostics.labelInMacroBody.code
    | .recursiveMacro .. => Diagnostics.recursiveMacro.code
    | .undefinedMacro .. => Diagnostics.undefinedMacro.code
    | .macroArityMismatch .. => Diagnostics.macroArityMismatch.code
    | .macroArgumentNotAssignable .. => Diagnostics.macroArgumentNotAssignable.code
    | .internalUnexpandedMacroCall _ => Diagnostics.internalUnexpandedMacroCall.code
  posOf
    | .misplacedAt pos
    | .gotoNotInTailPosition pos
    | .unlabelledStatement pos
    | .nestedLabel pos
    | .whileInWith pos
    | .whileNotLabelled pos
    | .notFollowedByLabel pos
    | .withBoundVarWritten pos _
    | .wrongAnnotationKindAtSite pos _ _
    | .duplicateAnnotation pos _
    | .conflictingAssignment pos _
    | .invalidRecordFieldAccess pos
    | .duplicateMacroDecl pos ..
    | .labelInMacroBody pos
    | .recursiveMacro pos _
    | .undefinedMacro pos _
    | .macroArityMismatch pos ..
    | .macroArgumentNotAssignable pos ..
    | .internalUnexpandedMacroCall pos => pos
  msgOf
    | .misplacedAt _ => "Unexpected '@' outside 'EXCEPT' construct."
    | .gotoNotInTailPosition _ => "'goto' may not be followed by further unlabelled statements."
    | .unlabelledStatement _ => "Statement is not preceded by a label."
    | .nestedLabel _ => "A label may not appear inside a 'with' block."
    | .whileInWith _ => "A 'while' statement may not appear inside a 'with' block."
    | .whileNotLabelled _ => "A 'while' statement must be immediately preceded by a label."
    | .notFollowedByLabel _ => "This statement must be labelled, since it follows an 'if'/'either' containing a label or 'goto'."
    | .withBoundVarWritten _ name => s!"'{name}' is bound by an enclosing 'with' and cannot be written to."
    | .wrongAnnotationKindAtSite _ found expected => s!"'{found}' is not valid here; only '{expected}' is expected at this position."
    | .duplicateAnnotation _ kind => s!"Only one '{kind}' annotation is allowed per binder."
    | .conflictingAssignment _ name => s!"'{name}' is written to more than once within the same atomic step."
    | .invalidRecordFieldAccess _ => "The right-hand side of '.' must be a field name."
    | .duplicateMacroDecl _ name _ => s!"Macro '{name}' is declared more than once."
    | .labelInMacroBody _ => "A label may not appear inside a 'macro' body."
    | .recursiveMacro .. => "Macro declarations may not be recursive."
    | .undefinedMacro _ name => s!"'{name}' is not a declared macro."
    | .macroArityMismatch _ name expected got _ =>
      s!"Macro '{name}' expects {expected} argument(s), but was called with {got}."
    | .macroArgumentNotAssignable _ macroName paramName _ =>
      s!"This argument cannot be written to, but macro '{macroName}''s parameter '{paramName}' is assigned to in its body."
    | .internalUnexpandedMacroCall _ =>
      "Internal error: a macro call reached statement desugaring without being expanded."
  notesOf
    | .duplicateMacroDecl _ name firstPos => [(firstPos, s!"'{name}' first declared here")]
    | .recursiveMacro _ cycle => cycle.map λ (name, callPos) ↦ (callPos, s!"recursively calls macro '{name}' here")
    | .macroArityMismatch _ name _ _ declPos => [(declPos, s!"macro '{name}' declared here")]
    | .macroArgumentNotAssignable _ _ paramName writePos =>
      [(writePos, s!"'{paramName}' is assigned to here")]
    | _ => []

/-- Non-fatal issues found while desugaring — collected out-of-band and filtered/printed once
desugaring returns (`Driver/Modules.lean`'s `compileModule`). -/
inductive DesugarWarning : Type
  /-- A `@parameter` marker repeated on the same variable — content-free, so a warning rather
  than `DesugarError.duplicateAnnotation`. -/
  | duplicateParameterAnnotation (pos : SourceSpan)
  /-- A `multicast` filter whose components carry `@type` annotations on some binds but not all.
  The desugarer collapses the components into one binder over their Cartesian product, whose
  declared type is the tuple of theirs — which it can only build when every component supplies
  one. The annotations that were written are dropped, and the recipient's type comes from the
  channel's own declared domain instead. -/
  | partialMulticastAnnotation (pos : SourceSpan)
  deriving Repr, Inhabited, BEq

/-- The `-W<name>`/`-Wno-<name>` name a given warning is filtered under. -/
def DesugarWarning.name : DesugarWarning → String
  | .duplicateParameterAnnotation _ => "duplicate-parameter"
  | .partialMulticastAnnotation _ => "partial-multicast-annotation"

instance : CompilerDiagnostic DesugarWarning String where
  isError := false
  code
    | .duplicateParameterAnnotation _ => Diagnostics.duplicateParameterAnnotation.code
    | .partialMulticastAnnotation _ => Diagnostics.partialMulticastAnnotation.code
  name := DesugarWarning.name
  posOf
    | .duplicateParameterAnnotation pos => pos
    | .partialMulticastAnnotation pos => pos
  msgOf
    | .duplicateParameterAnnotation _ => "Only one '@parameter' is needed per variable; the extra one(s) have no additional effect."
    | .partialMulticastAnnotation _ => "This multicast's recipients are a tuple, so a declared type for them can only be built when every component is annotated; the annotations given here are ignored."

end
