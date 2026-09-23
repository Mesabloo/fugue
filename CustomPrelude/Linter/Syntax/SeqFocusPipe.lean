module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.seqFocusPipe`

Batteries' `seq_focus` notation is `t <;> [t₁; t₂; …]` (`;`-separated). `CustomPrelude` respells
it `t <;> [t₁ | t₂ | …]` (`|`-separated) to pair with the project's other bracketed tactic
lists. Deterministic — one right spelling.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Every Batteries `seq_focus` node. -/
def seqFocusPipeCore : Syntax → Array Finding :=
  scan λ s ↦
    if s.getKind == `Batteries.Tactic.seq_focus then
      hit s m!"`t <;> [a; b]` → `t <;> [a | b]` (the project's spelling)"
    else #[]

/-- `t <;> [a; b]` → `t <;> [a | b]`. -/
fugue_linter seqFocusPipe
  "flag Batteries' `;`-separated `<;> [ … ]` — use the project's `|`-separated form"
  := seqFocusPipeCore

end CustomPrelude.Linter
