module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.rwBeforeSimp`

A `rw […]` immediately before a `simp only […]` / `grind` is two traversals where one would do,
and `rw`'s closing `rfl` attempt is dead work when a `simp`/`grind` follows. Fold the lemmas into
the `simp only` set, or — where that overshoots — use `rewrite`.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Every `rw` on its own line whose next sibling tactic, on the following line, is `simp` or
`grind`. A `;`-joined one-liner (`rw […]; simp only […]`) is left alone — matching the text rule,
which keys on `simp`/`grind` starting the *next* line. -/
def rwBeforeSimpCore : Syntax → Array Finding :=
  scan λ seq ↦
    if seq.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
      let tacs := seqTactics seq
      tacs.zipIdx.foldl (init := #[]) λ out (t, i) ↦
        if t.getKind == ``Lean.Parser.Tactic.rwSeq && crossesLine t then
          match tacs[i + 1]? with
          | some n =>
            if n.getKind == ``Lean.Parser.Tactic.simp || n.getKind == ``Lean.Parser.Tactic.grind then
              out.push ⟨t, m!"merge this `rw` into the following `{n.getKind.components.getLast!}`, or use `rewrite`"⟩
            else out
          | none => out
        else out
    else #[]

/-- Merge `rw` into a following `simp only` / `grind`. -/
fugue_linter rwBeforeSimp
  "flag `rw` immediately before `simp`/`grind` — merge it in, or use `rewrite`" := rwBeforeSimpCore

end CustomPrelude.Linter
