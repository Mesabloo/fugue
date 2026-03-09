import CustomPrelude
import Common.Pretty
import Core.SurfaceTLAPlus.Syntax

namespace SurfaceTLAPlus
  partial def Typ.pretty : Typ → Std.Format
    | .bool => "Bool"
    | .int => "Int"
    | .str => "Str"
    | .address => "Address"
    | .function dom@(.function _ _) rng
    | .function dom@(.operator _ _) rng => .paren (pretty dom) ++ " → " ++ pretty rng
    | .function dom rng => pretty dom ++ " → " ++ pretty rng
    | .set τ => "Set" ++ .paren (pretty τ)
    | .seq τ => "Seq" ++ .paren (pretty τ)
    | .tuple τs => .bracket "<<" (.joinSep (τs.map pretty) ", ") ">>"
    | .operator dom rng => .paren (.joinSep (dom.map pretty) ", ") ++ " ⇒ " ++ pretty rng
    | .var v => v
    | .const v => v
    | .record fs => .bracket "{" (.joinSep (fs.map λ ⟨name, τ⟩ ↦ name ++ " : " ++ pretty τ) ", ") "}"
    | .channel τ => "Channel" ++ .paren (pretty τ)
  instance : Std.ToFormat Typ := ⟨Typ.pretty⟩

  instance : Std.ToFormat PrefixOperator := ⟨.text ∘ toString⟩
  instance : Std.ToFormat InfixOperator := ⟨.text ∘ toString⟩
  instance : Std.ToFormat PostfixOperator := ⟨.text ∘ toString⟩

  instance {α} [Std.ToFormat α] : Std.ToFormat (IdentifierOrTuple α) where
    format
      | .inl x => Std.format x
      | .inr xs => .bracket "<<" (.joinSep xs ",") ">>"

  partial def QuantifierBound.pretty {α β} [Std.ToFormat α] (f : β → Std.Format) : QuantifierBound α β → Std.Format
    | .var ann x e => Std.format ann ++ f!" {x} \\in " ++ f e
    | .varTuple xs e => .bracket "<<" (.joinSep (xs <&> λ ⟨ann, x⟩ ↦ Std.format ann ++ f!" {x}") ", ") ">>" ++ " \\in " ++ f e
    | .vars xs e => .joinSep (xs <&> λ ⟨ann, x⟩ ↦ Std.format ann ++ f!" {x}") ", " ++ " \\in " ++ f e

  partial def Expression.pretty {α} [Std.ToFormat α] (e : Expression α) : Std.Format :=
    formatPos (posOf e) ++ match e with
      | .var x => x
      | .opCall e es => e.pretty ++ .paren (.joinSep (Expression.pretty <$> es) ", ")
      | .prefixCall op e => f!"{op} " ++ e.pretty
      | .infixCall e₁ op e₂ => e₁.pretty ++ f!" {op} " ++ e₂.pretty
      | .postfixCall e op => e.pretty ++ f!" {op}"
      | .parens e => .paren e.pretty
      | .bforall qs e => "\\A " ++ .joinSep (qs <&> λ q ↦ q.pretty Expression.pretty) ", " ++ " : " ++ e.pretty
      | .bexists qs e => "\\E " ++ .joinSep (qs <&> λ q ↦ q.pretty Expression.pretty) ", " ++ " : " ++ e.pretty
      | .forall vs e => "\\A " ++ .joinSep vs ", " ++ " : " ++ e.pretty
      | .exists vs e => "\\E " ++ .joinSep vs ", " ++ " : " ++ e.pretty
      | .fforall vs e => "\\AA " ++ .joinSep vs ", " ++ " : " ++ e.pretty
      | .eexists vs e => "\\EE " ++ .joinSep vs ", " ++ " : " ++ e.pretty
      | .choose x e₁ e₂ => "CHOOSE " ++ Std.format x ++ (e₁.elim .nil λ e ↦ " \\in " ++ e.pretty) ++ " : " ++ e₂.pretty
      | .set es => .cbracket (.joinSep (Expression.pretty <$> es) ", ")
      | .collect x e₁ e₂ => .cbracket (Std.format x ++ " \\in " ++ e₁.pretty ++ " : " ++ e₂.pretty)
      | .map' e qs => .cbracket (e.pretty ++ " : " ++ .joinSep (qs <&> λ q ↦ q.pretty Expression.pretty) ", ")
      | .fnCall e es => e.pretty ++ .sbracket (.joinSep (Expression.pretty <$> es) ", ")
      | .fn qs e => .sbracket (.joinSep (qs <&> λ q ↦ q.pretty Expression.pretty) ", " ++ " |-> " ++ e.pretty)
      | .fnSet e₁ e₂ => .sbracket (e₁.pretty ++ " -> " ++ e₂.pretty)
      | .record fs => .sbracket (.joinSep (fs <&> λ ⟨ann, x, e⟩ ↦ Std.format ann ++ f!" {x} |-> " ++ e.pretty) ",")
      | .recordSet fs => .sbracket (.joinSep (fs <&> λ ⟨ann, x, e⟩ ↦ Std.format ann ++ f!" {x} : " ++ e.pretty) ",")
      | .except e upds => .sbracket <| e.pretty ++ " EXCEPT " ++ .joinSep (upds <&> λ ⟨upd, e⟩ ↦
        let rec formatIndex : List (String ⊕ List (Expression α)) → Std.Format
          | [] => .nil
          | .inl x :: upd => f!".{x}" ++ formatIndex upd
          | .inr es :: upd => Std.Format.sbracket (.joinSep (Expression.pretty <$> es) ",") ++ formatIndex upd
        "!" ++ formatIndex upd ++ " = " ++ e.pretty) ","
      | .recordAccess e x => e.pretty ++ f!".{x}"
      | .tuple es => .bracket "<<" (.joinSep (Expression.pretty <$> es) ", ") ">>"
      | .if e₁ e₂ e₃ => "IF " ++ e₁.pretty ++ .nest 2 (.line ++ "THEN " ++ e₂.pretty ++ .line ++ "ELSE " ++ e₃.pretty)
      | .case bs other => "CASE " ++ .align .true ++ .joinSep (bs <&> λ ⟨e₁, e₂⟩ ↦ e₁.pretty ++ " -> " ++ e₂.pretty) (.line ++ "[] ") ++ match other with
        | .none => .nil
        | .some e => .line ++ "[] OTHER -> " ++ e.pretty
      | .conj es => .align .true ++ .joinSep (es <&> λ e ↦ "/\\ " ++ e.pretty) .line
      | .disj es => .align .true ++ .joinSep (es <&> λ e ↦ "\\/ " ++ e.pretty) .line
      | .nat n => n
      | .str s => f!"\"{s}\""
      | .at => "@"
      | .true => "TRUE"
      | .false => "FALSE"
      | .stutter e₁ e₂ => .sbracket e₁.pretty ++ "_" ++ e₂.pretty
  where
    formatPos (pos : SourceSpan) : Std.Format := .bracket "(* " (Std.format pos) " *)"

  instance {α} [Std.ToFormat α] : Std.ToFormat (Expression α) := ⟨Expression.pretty⟩

  instance {α} [Std.ToFormat α] : Std.ToFormat (Declaration α) where
    format
      | .constants vs => "CONSTANTS " ++ .joinSep (vs <&> λ ⟨v, ann⟩ ↦ Std.format ann ++ f!" {v}") ", "
      | .variables vs => "VARIABLES " ++ .joinSep (vs <&> λ ⟨v, ann⟩ ↦ Std.format ann ++ f!" {v}") ", "
      | .assume e => "ASSUME " ++ Std.format e
      | .operator ann x ps e =>
        Std.format ann ++ f!" {x}" ++ .paren (.joinSep (ps <&> λ ⟨p, n⟩ ↦ p ++ if n > 0 then Std.Format.paren (.joinSep (List.replicate n "_") ", ") else Std.Format.nil) ",") ++
        " == " ++ Std.format e
      | .function ann x ps e =>
        Std.format ann ++ f!" {x}" ++ .sbracket (.joinSep (ps <&> λ ⟨x, e⟩ ↦ f!"{x} \\in " ++ Std.format e) ", ") ++ " == " ++ Std.format e

  instance {α β} [Std.ToFormat α] [Std.ToFormat β] : Std.ToFormat (Module α β) where
    format mod :=
      .align true ++
      f!"---- {mod.name} ----" ++ .line ++
      (if mod.extends.isEmpty then Std.Format.nil else "EXTENDS " ++ .joinSep mod.extends ", ") ++ .line ++
      .joinSep mod.declarations₁ .line ++ .line ++
      (match mod.pcalAlgorithm with | .none => .nil | .some alg => Std.format alg) ++ .line ++
      .joinSep mod.declarations₂ .line ++ .line ++
      "===="
