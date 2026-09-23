module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.renameI`

`rename_i` and `expose_names` reach for a hypothesis by its position in the context — the one
thing every edit above them changes, silently. Name it where it is bound (`rintro`/`obtain`
pattern, `case`/`with` alternative), or with `next x y => …`, or do not name it at all.

Syntax quotations are exempt — `split … using` and `injections with` build `rename_i` into
themselves so no proof has to write it.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Every `rename_i` / `expose_names` outside a quotation. -/
def renameICore : Syntax → Array Finding :=
  scan λ s ↦
    if s.isOfKind ``Lean.Parser.Tactic.renameI then
      hit s m!"never `rename_i` — use `next x y => …`, or name it where it is bound"
    else if s.isOfKind ``Lean.Parser.Tactic.exposeNames then
      hit s m!"never `expose_names` — name the hypotheses where they are bound"
    else #[]

/-- Never `rename_i` / `expose_names`. -/
fugue_linter renameI
  "flag `rename_i` / `expose_names` — name the hypothesis where it is bound" := renameICore

end CustomPrelude.Linter
