module

public meta import CustomPrelude.Linter.Basic

/-!
# `linter.fugue.subscriptSuffix`

An identifier's trailing digits read as an index — write them as Unicode subscript digits
(`B₁`, `hf₂`), not ASCII digits (`B1`, `hf2`). Matches the project's own naming
(`ref₁`/`ref₂`/`ref₃`, `LEAN_STYLE.md`'s "Name introduced hypotheses in signature order").

`fixedWidthNames` excepts the standard fixed-width numeric type names, whose trailing digit is
part of the name itself (a bit width), not an index — `UInt64` stays `UInt64`.

`default := false`: the backlog is the whole tree (`vc1`…`vc14`, `hself0`, `b1`/`b2`, …) — opt in
per file with `set_option linter.fugue.subscriptSuffix true`, same reasoning `sigIndent` gives.
-/

meta section

open Lean Elab Command Linter

namespace CustomPrelude.Linter

/-- Write an index suffix as a Unicode subscript (`x₁`), not ASCII digits (`x1`). -/
register_option linter.fugue.subscriptSuffix : Bool := {
  defValue := false
  descr := "flag an identifier ending in ASCII digits — write the suffix as a Unicode subscript"
}

/-- `c` (an ASCII digit) as the matching Unicode subscript digit. -/
def subscriptDigit (c : Char) : Char :=
  Char.ofNat (c.toNat - '0'.toNat + '₀'.toNat)

/-- `s` with every ASCII digit replaced by its Unicode subscript form. -/
def toSubscript (s : String) : String :=
  String.ofList (s.toList.map λ c ↦ if c.isDigit then subscriptDigit c else c)

/-- Whether `s` ends in at least one ASCII digit, with a non-digit character before it (so a
name that is entirely digits — never a legal identifier — is not miscounted). -/
def endsInAsciiDigit (s : String) : Bool :=
  match s.toList.reverse with
  | c :: _ => c.isDigit
  | [] => false

/-- Standard fixed-width numeric type names — their trailing digit is a bit width, not an index.
Full last-component names only (`UInt64.toNat`'s last component is `toNat`, not `UInt64`; a bare
reference to the type itself is what needs excepting). -/
def fixedWidthNames : Array String :=
  #["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Int8", "Int16", "Int32", "Int64",
    "Float32", "Float64"]

/-- Every identifier whose last name component ends in an ASCII digit, `fixedWidthNames`
excepted. -/
def subscriptSuffixCore : Syntax → Array Finding :=
  scan λ s ↦
    match identLast? s with
    | some name =>
      if endsInAsciiDigit name && !fixedWidthNames.contains name then
        hit s m!"write `{toSubscript name}`, not `{name}` — index suffix should be a Unicode subscript"
      else #[]
    | none => #[]

/-- The `linter.fugue.subscriptSuffix` linter. -/
def subscriptSuffix : Linter where
  run := mkFugueLinter linter.fugue.subscriptSuffix subscriptSuffixCore

initialize addLinter subscriptSuffix

end CustomPrelude.Linter
