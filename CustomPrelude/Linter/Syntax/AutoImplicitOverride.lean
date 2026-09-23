module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.autoImplicitOverride`

`autoImplicit` is off project-wide (`lakefile.lean`). A per-file `set_option autoImplicit true`
opts back in — never right; write every implicit explicitly. (The one-command
`set_option autoImplicit true in …` form is peeled off before linters run and is not flagged.)
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Every `set_option autoImplicit true`. -/
def autoImplicitOverrideCore : Syntax → Array Finding :=
  scan λ s ↦
    if isSetOption "autoImplicit" "true" s then
      hit s m!"`autoImplicit` is off project-wide — write every implicit explicitly"
    else #[]

/-- `autoImplicit` stays off. -/
fugue_linter autoImplicitOverride
  "flag `set_option autoImplicit true`" := autoImplicitOverrideCore

end CustomPrelude.Linter
