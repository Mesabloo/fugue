module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.byClassical`

`by classical` goes on one line, not `by` then `classical` on the next.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Every `by` whose sequence opens with `classical` on a later line than the `by`. -/
def byClassicalCore : Syntax → Array Finding :=
  scan λ s ↦
    if s.isOfKind ``Lean.Parser.Term.byTactic || s.isOfKind ``Lean.Parser.Term.byTactic' then
      match (seqTactics s[1])[0]? with
      | some t =>
        if t.isOfKind ``Lean.Parser.Tactic.classical && crossesLine s[0] then
          hit s[0] m!"put `by classical` on one line"
        else #[]
      | none => #[]
    else #[]

/-- `by classical` on one line. -/
fugue_linter byClassical
  "flag `by` and a leading `classical` split across two lines" := byClassicalCore

end CustomPrelude.Linter
