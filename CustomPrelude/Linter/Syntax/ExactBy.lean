module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.exactBy`

`exact by tac` opens a tactic block to prove a term inside the `exact` tactic — a tactic proving
a term proving a tactic. Drop the wrapper and run `tac` directly.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Every `exact` whose term (through one `( … )`) is a `by` block. -/
def exactByCore : Syntax → Array Finding :=
  scan λ s ↦
    if s.isOfKind ``Lean.Parser.Tactic.exact then
      let t := if s[1].isOfKind ``Lean.Parser.Term.paren then s[1][1] else s[1]
      if t.isOfKind ``Lean.Parser.Term.byTactic then
        hit s m!"`exact by …` — drop the `exact by` and run the tactics directly"
      else #[]
    else #[]

/-- `exact by tac` → `tac`. -/
fugue_linter exactBy
  "flag `exact by …` — run the tactics directly" := exactByCore

end CustomPrelude.Linter
