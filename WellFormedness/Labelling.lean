module

public import WellFormedness.Errors
public import Core.TypedPlusCal.Syntax

public section

/-!
  Well-labelledness: every `goto` targets a label its process actually defines, or the reserved
  `"Done"`; `"Done"` itself is never a real, user-defined label.

  Assignment-conflict checking is **not** duplicated here — it already runs in
  `Desugarer/PlusCal.lean`'s `CorePlusCal.Algorithm.checkAssignConflicts`.
-/

variable {m : Type → Type} [Monad m] [MonadDiagnostic WellFormednessWarning WellFormednessError m]

/-- Collect every label a process defines across all its threads (`Process.threads`, the label
of every atomic block), paired with that block's own terminal-statement position — needed both
to check `goto` targets and, concatenated across every process (`checkLabelling` below), to check
for a repeated label. Rejects a literal `"Done"` entry along the way — `"Done"` is a reserved
fallthrough target, never itself a real label. No better position exists for a `redefinedDone`
error than the labelled block's own terminal statement: labels are bare strings paired with a
block, not positioned nodes in their own right. -/
def TypedPlusCal.Process.labels (p : TypedPlusCal.Process) : m (List (String × SourceSpan)) := do
  let perThread ← p.threads.mapM λ thread ↦
    thread.mapM λ (label, blk) ↦ do
      if label = "Done" then throw (.redefinedDone (posOf blk.end))
      else pure (label, posOf blk.end)
  return perThread.flatten

/-- Rejects the first repeated label among `labels`, at that repeat's own position. Labels are one
flat namespace across the *whole algorithm*, not scoped per process — matching the original
PlusCal-to-TLA⁺ translator, whose labels each become their own top-level TLA⁺ definition and so
cannot collide regardless of which process they sit in. A same-process duplicate is additionally
an operational hazard on top of that: `Process.codeTable` (both later languages) treats a label as
denoting the *union* of every block carrying it, so it would otherwise make a `goto` to it
silently non-deterministic. -/
private def checkNoDuplicateLabels : List (String × SourceSpan) → m Unit
  | [] => pure ()
  | (l, _) :: rest =>
    match rest.find? (·.1 == l) with
    | some (_, pos) => throw (.duplicateLabel pos l)
    | none => checkNoDuplicateLabels rest

/-- Checks one `goto l`, within its own process, against that process's own `labels ∪ {"Done"}` —
a `goto` can only ever reach a label in its own process's control flow (`Process.codeTable` is
built per process), even though labels are drawn from one algorithm-wide namespace. A per-node
check with no context of its own beyond `labels`, so it does no recursing —
`ElaboratedPlusCal.Statement.forEachNode` (`Core/TypedPlusCal/Syntax.lean`) supplies that. Every
non-`goto` statement is vacuously fine. -/
def TypedPlusCal.Statement.checkGotoTarget {b} (labels : List String)
    (s : TypedPlusCal.Statement b) : m Unit :=
  match_source s with
  | .goto l, pos => unless labels.contains l ∨ l = "Done" do throw (.unknownLabel pos l)
  | _, _ => pure ()

/-- Well-labelledness over a whole algorithm: labels form one flat namespace across every process,
checked for uniqueness once, algorithm-wide; then, per process, every `goto` in every one of its
threads must target one of that same process's own labels or `"Done"`. -/
def TypedPlusCal.Algorithm.checkLabelling (algo : TypedPlusCal.Algorithm) : m Unit := do
  let labelsByProcess ← algo.processes.mapM TypedPlusCal.Process.labels
  checkNoDuplicateLabels labelsByProcess.flatten
  (algo.processes.zip labelsByProcess).forM λ (p, labels) ↦
    ElaboratedPlusCal.Process.forStatements
      (ElaboratedPlusCal.Statement.forEachNode
        (TypedPlusCal.Statement.checkGotoTarget (labels.map Prod.fst))) p

end
