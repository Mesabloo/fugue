module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.firstVsSolve`

A `first | …` in terminal position — the last tactic of a `by` / `·` / `{ }` / `case` arm — must
have closed the goal in a compiling proof, so it is a `solve | …`: `solve` errors if a branch
succeeds without closing, `first` does not.

`<;> first` and blanket-selector forms are `seqFocusPipe` / `selectorFirst`'s, not this one.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Every `first` that ends a multi-step tactic sequence. -/
def firstVsSolveCore : Syntax → Array Finding :=
  scan λ seq ↦
    if seq.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
      let tacs := seqTactics seq
      match tacs.back? with
      | some last =>
        if tacs.size ≥ 2 && last.isOfKind ``Lean.Parser.Tactic.first then
          hit last m!"terminal `first | …` closes the goal → `solve | …`"
        else #[]
      | none => #[]
    else #[]

/-- Terminal `first | …` → `solve | …`. -/
fugue_linter firstVsSolve
  "flag a `first` that is the last tactic of a proof block — use `solve`" := firstVsSolveCore

end CustomPrelude.Linter
