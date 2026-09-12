module

meta import CustomPrelude
public import Guarded2Network.Lemmas.Correctness
public import Core.ComputableTLAPlus.Semantics.Operational
public import Std.Data.String.ToNat
import all Guarded2Network.PlusCal

@[expose] public section

/-!
  `Guarded2Network.correct'` at this development's concrete value type.

  Everything below `Guarded2Network` is proved against abstract `[ExprSemantics V] [SeqBuiltins V]`.
  This file discharges both classes at `V := ComputableTLAPlus.Value` (`ZFSet`): the `ExprSemantics`
  instance is `Core/ComputableTLAPlus/Semantics/Operational.lean`'s operational evaluator, and
  `SeqBuiltins Value` is proved here from that evaluator's `Sequences`/`Naturals` builtin rules.
  `correct''` is `correct'` at that instance, and `assert_no_sorry` then checks the whole
  correctness proof carries no `sorry` once every class is concrete.
-/

namespace Guarded2Network

open ComputableTLAPlus ComputableTLAPlus.Operational

/-- `Head` denotes only on a non-empty sequence — the `EvalBuiltin` rule, inverted. -/
private theorem evalBuiltin_head_inv {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {a : Expression Typ} {b : Value} (h : EvalBuiltin Ξ Ω M .head [a] b) :
    ∃ vs, Eval Ξ Ω M a (Value.ofSeq (b :: vs)) := by
  cases h with
  | head h => exact ⟨_, h⟩

/-- `Tail` denotes only on a non-empty sequence — the `EvalBuiltin` rule, inverted. -/
private theorem evalBuiltin_tail_inv {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {a : Expression Typ} {b : Value} (h : EvalBuiltin Ξ Ω M .tail [a] b) :
    ∃ v vs, Eval Ξ Ω M a (Value.ofSeq (v :: vs)) ∧ b = Value.ofSeq vs := by
  cases h with
  | tail h => exact ⟨_, _, h, rfl⟩

private theorem builtinOpOf?_head :
    TypedTLAPlus.builtinOpOf? (.module "Sequences" "Head") = some .head := rfl

private theorem builtinOpOf?_tail :
    TypedTLAPlus.builtinOpOf? (.module "Sequences" "Tail") = some .tail := rfl

private theorem builtinOpOf?_len :
    TypedTLAPlus.builtinOpOf? (.module "Sequences" "Len") = some .len := rfl

private theorem builtinOpOf?_gt :
    TypedTLAPlus.builtinOpOf? (.module "Naturals" ">") = some .gt := rfl

/-- `Head(e)` evaluates exactly to the first element of the sequence `e` denotes. -/
theorem eval_head_iff' {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {e : ComputablePlusCal.Expression} {τ : Typ} {v : Value} :
    Eval Ξ Ω M (Guarded2Network.head τ e) v ↔
      ∃ s vs, Eval Ξ Ω M e s ∧ IsSeq s (v :: vs) := by
  rw [Guarded2Network.head]
  iff_rintro h ⟨s, vs, hes, hseq⟩
  · have hb := evalOpCall1_inv builtinOpOf?_head h
    obtain ⟨vs, hea⟩ := evalBuiltin_head_inv hb
    exact ⟨_, vs, hea, isSeq_ofSeq _⟩
  · obtain rfl := isSeq_iff_ofSeq.mp hseq
    exact .opCall_builtin builtinOpOf?_head (.head hes)

/-- `Tail(e)` evaluates exactly to the sequence of everything but the first element. -/
theorem eval_tail_iff' {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {e : ComputablePlusCal.Expression} {τ : Typ} {t : Value} :
    Eval Ξ Ω M (Guarded2Network.tail τ e) t ↔
      ∃ s v vs, Eval Ξ Ω M e s ∧ IsSeq s (v :: vs) ∧ IsSeq t vs := by
  rw [Guarded2Network.tail]
  iff_rintro h ⟨s, v, vs, hes, hseq, htseq⟩
  · have hb := evalOpCall1_inv builtinOpOf?_tail h
    obtain ⟨v, vs, hea, rfl⟩ := evalBuiltin_tail_inv hb
    exact ⟨_, v, vs, hea, isSeq_ofSeq _, isSeq_ofSeq _⟩
  · obtain rfl := isSeq_iff_ofSeq.mp hseq
    obtain rfl := isSeq_iff_ofSeq.mp htseq
    exact .opCall_builtin builtinOpOf?_tail (.tail hes)

/-- `Len(e) > n` evaluates to a boolean whenever `e` is a sequence, `TRUE` exactly when that
sequence is longer than `n`. -/
theorem eval_lenGt' {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value}
    {e : ComputablePlusCal.Expression} {τ : Typ} {n : Nat} {s : Value} {vs : List Value}
    (hes : Eval Ξ Ω M e s) (hseq : IsSeq s vs) :
    ∃ b, Eval Ξ Ω M (Guarded2Network.lenGt τ e n) b ∧ IsBool b ∧
      (b = Value.tru ↔ n < vs.length) := by
  obtain rfl := isSeq_iff_ofSeq.mp hseq
  rw [Guarded2Network.lenGt]
  have hLen : Eval Ξ Ω M
      (Expression.opCall (.var (.operator [.seq τ] .int) (.module "Sequences" "Len")) [e])
      (Value.ofNat vs.length) :=
    .opCall_builtin builtinOpOf?_len (.len hes)
  have hNat : Eval Ξ Ω M (Expression.nat (toString n)) (Value.ofNat n) :=
    .nat (Nat.toNat?_repr n)
  by_cases hlt : n < vs.length
  · exact ⟨Value.tru, .opCall_builtin builtinOpOf?_gt (.gt_pos hLen hNat (Int.ofNat_lt.mpr hlt)),
      .inl rfl, iff_of_true rfl hlt⟩
  · exact ⟨Value.fls,
      .opCall_builtin builtinOpOf?_gt (.gt_neg hLen hNat (λ hc ↦ hlt (Int.ofNat_lt.mp hc))),
      .inr rfl, iff_of_false Value.tru_ne_fls.symm hlt⟩

/-- `<<>>` evaluates to the empty sequence, and only that. -/
theorem eval_seq_nil_iff' {Ξ : OperatorEnv} {Ω : Model Value} {M : Memory Value} {τ : Typ}
    {s : Value} :
    Eval Ξ Ω M (.seq [] τ) s ↔ IsSeq s [] := by
  iff_rintro h hseq
  · cases h with
    | seq hes => cases hes; exact isSeq_ofSeq []
  · obtain rfl := isSeq_iff_ofSeq.mp hseq
    exact .seq .nil

/-- The operational evaluator satisfies `Guarded2Network`'s sequence-expression laws. -/
noncomputable instance instSeqBuiltinsValue : SeqBuiltins Value where
  evalHead := eval_head_iff'
  evalTail := eval_tail_iff'
  evalLenGt := eval_lenGt'
  evalSeqNil := eval_seq_nil_iff'

/-- `Guarded2Network.correct'` at this development's concrete value type `Value` (`ZFSet`), with the
operational `ExprSemantics Value` instance (whose `evalVar`/`evalSubst` fields are `evalVar'`/
`evalSubst'`) and the `SeqBuiltins Value` instance above. `Ξ`/`Ω` stay universally quantified — the
statement holds for every operator environment and model. -/
theorem correct'' {Ξ : OperatorEnv} {Ω : Model Value} :
    Compiler.Correct compile
      (λ s : SourceProgram Value Ξ Ω ↦ GuardedPlusCal.Algorithm.init Ξ Ω s.algo)
      (NetworkPlusCal.Algorithm.init Ξ Ω) :=
  correct'

assert_no_sorry correct''

end Guarded2Network

end
