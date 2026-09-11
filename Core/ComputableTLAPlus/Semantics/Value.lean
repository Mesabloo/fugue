module

meta import CustomPrelude
public import ZFLean
public import Core.ComputableTLAPlus.Semantics.ZFSet

@[expose] public section

/-!
  The value domain for the concrete TLA⁺ expression evaluator: `Value := ZFSet`, one uniform
  representation for every kind of TLA⁺ value.

  TLA⁺ is untyped set theory, so a value — a number, a string, a set, a function, a tuple, a
  record — is always a set. This development represents that directly: `Value` is mathlib's
  `ZFSet`, set membership is `ZFSet`'s own `∈`, and the encodings below place each syntactic kind
  of literal into that one universe. Integers land in `vtrelat/zflean`'s `ZFSet.Int` (via the
  `ZFInt ≃+* ℤ` equivalence and `ZFInt.into`), the booleans use its `zftrue`/`zffalse`, and
  functions, tuples, records and sequences are ordinary sets of ordered pairs.

  Distinct kinds of value are not kept provably disjoint: `FALSE` and the empty set share an
  encoding, a string and the tuple of its code points share an encoding, and so on. TLA⁺ leaves
  such cross-kind comparisons unspecified, and this compiler's type checker keeps them from ever
  being asked — an expression of set type only evaluates against the set encodings, one of string
  type only against the string encoding. Only within a kind are the encodings injective.

  Equality of values is not decidable — `ZFSet` extensionality is a `∀` — so `DecidableEq`/`BEq`
  are classical and noncomputable, which costs nothing here: evaluation is a `Prop` relation.
-/

namespace ComputableTLAPlus

/-- A TLA⁺ value: an element of the cumulative set hierarchy. Every kind of TLA⁺ value — scalar,
set, function, tuple, record — is one of these. `ZFSet` is `Type 1` (its underlying `PSet` is
`Type`), so `Value` is `Type 1`. -/
abbrev Value : Type 1 := ZFSet

namespace Value

/-- The integer `z`, as the corresponding element of `zflean`'s `ZFSet.Int` encoding. `z` crosses
into the quotient integers `ZFInt` along the canonical ring equivalence `ZFInt ≃+* ℤ`
(`ZFInt.equivInt`), then into `ZFSet.Int` along `ZFInt.into`. Both legs are injective with public
injectivity lemmas, so `ofInt` is too (`ofInt_inj`). -/
noncomputable def ofInt (z : ℤ) : Value :=
  (ZFSet.ZFInt.into (ZFSet.ZFInt.equivInt.symm z)).val

/-- The natural number `n`, as the integer `n`. TLA⁺ has one numeric type; `Nat` is a subset of
`Int`, not a separate encoding. -/
noncomputable def ofNat (n : ℕ) : Value := ofInt n

/-- `TRUE`. -/
def tru : Value := ZFSet.zftrue

/-- `FALSE`. -/
def fls : Value := ZFSet.zffalse

/-- The boolean `b`. -/
def ofBool (b : Bool) : Value := bif b then tru else fls

/-- The graph `{(start, v₁), (start + 1, v₂), …}` of a list of values indexed by consecutive
integers from `start`. The shape every TLA⁺ sequence and tuple value takes. -/
noncomputable def seqGraphFrom (start : ℕ) : List Value → Value
  | [] => ∅
  | v :: vs => insert (ZFSet.pair (ofNat start) v) (seqGraphFrom (start + 1) vs)

/-- A TLA⁺ sequence or tuple `⟨v₁, …, vₙ⟩`: the function `{1 ↦ v₁, …, n ↦ vₙ}`. Sequences and
tuples are the same kind of value; their two syntactic forms differ only in how they are checked. -/
noncomputable def ofSeq (vs : List Value) : Value := seqGraphFrom 1 vs

/-- A TLA⁺ tuple `⟨v₁, …, vₙ⟩`. Identical to `ofSeq`. -/
noncomputable def ofTuple : List Value → Value := ofSeq

/-- A TLA⁺ string: the sequence of its Unicode code points. `"abc"` is the tuple `⟨97, 98, 99⟩`,
matching TLA⁺'s treatment of a string as a tuple of characters. -/
noncomputable def ofString (s : String) : Value := ofSeq (s.toList.map λ c ↦ ofNat c.toNat)

/-- The graph `{(k₁, v₁), …}` of a record's fields, keyed by the string encodings of the field
names. -/
noncomputable def recordGraph : List (String × Value) → Value
  | [] => ∅
  | f :: fs => insert (ZFSet.pair (ofString f.1) f.2) (recordGraph fs)

/-- A TLA⁺ record `[a₁ ↦ v₁, …]`: the function from field-name strings to values. -/
noncomputable def ofRecord (fs : List (String × Value)) : Value := recordGraph fs

/-- A finite set literal `{v₁, …, vₙ}`. -/
def ofFinSet (vs : List Value) : Value := vs.foldr insert ∅

instance : Inhabited Value := ⟨(∅ : ZFSet)⟩

/-- `TRUE` and `FALSE` are distinct values. -/
@[simp] theorem tru_ne_fls : tru ≠ fls := by
  unfold tru fls; exact ZFSet.zftrue_ne_zffalse

/-- `FALSE` and `TRUE` are distinct values — the flipped orientation, for rewriting. -/
@[simp] theorem fls_ne_tru : fls ≠ tru := tru_ne_fls.symm

/-- The boolean encoding is injective. -/
@[simp] theorem ofBool_inj {a b : Bool} : ofBool a = ofBool b ↔ a = b := by
  cases a <;> cases b <;>
    simp [ofBool, tru_ne_fls, tru_ne_fls.symm]

/-- The integer encoding is injective — both legs of `ofInt` are. -/
@[simp] theorem ofInt_inj {a b : ℤ} : ofInt a = ofInt b ↔ a = b := by
  refine ⟨λ h ↦ ?_, λ h ↦ h ▸ rfl⟩
  exact ZFSet.ZFInt.equivInt.symm.injective (ZFSet.ZFInt.into.injective (Subtype.ext h))

/-- The natural-number encoding is injective. -/
@[simp] theorem ofNat_inj {m n : ℕ} : ofNat m = ofNat n ↔ m = n := by
  rw [ofNat, ofNat, ofInt_inj, Int.natCast_inj]

/-- Membership in a finite set literal is list membership of the elements. -/
@[simp] theorem mem_ofFinSet {z : Value} {vs : List Value} : z ∈ ofFinSet vs ↔ z ∈ vs := by
  unfold ofFinSet
  induction vs with
  | nil => simp [ZFSet.notMem_empty]
  | cons v vs ih => simp [List.foldr, ZFSet.mem_insert_iff, ih, List.mem_cons]

/-- Every integer encoding is a member of `zflean`'s `ZFSet.Int`. -/
theorem ofInt_mem_int {k : ℤ} : ofInt k ∈ ZFSet.Int :=
  (ZFSet.ZFInt.into (ZFSet.ZFInt.equivInt.symm k)).property

/-- TLA⁺'s `Nat`: the non-negative integers, `{i ∈ Int : i ≥ 0}`. -/
noncomputable def natSet : Value :=
  ZFSet.sep (λ z ↦ ∃ k : ℤ, 0 ≤ k ∧ z = ofInt k) ZFSet.Int

/-- `Nat` holds exactly the non-negative integer encodings. -/
@[simp] theorem mem_natSet {z : Value} : z ∈ natSet ↔ ∃ k : ℤ, 0 ≤ k ∧ z = ofInt k := by
  rw [natSet, ZFSet.mem_sep, and_iff_right_iff_imp]
  rintro ⟨k, -, rfl⟩
  exact ofInt_mem_int

/-- The integer interval `a .. b` — what TLA⁺'s `..` denotes. Empty when `b < a`. Given as an
explicit finite-set literal over the enumerated integers so that it is a closed-form function of
its bounds, not merely a set characterised up to extensionality. -/
noncomputable def intRange (a b : ℤ) : Value :=
  ofFinSet ((List.range (b + 1 - a).toNat).map (λ i : ℕ ↦ ofInt (a + i)))

/-- `a .. b` holds exactly the integers from `a` to `b` inclusive. -/
@[simp] theorem mem_intRange {z : Value} {a b : ℤ} :
    z ∈ intRange a b ↔ ∃ k : ℤ, a ≤ k ∧ k ≤ b ∧ z = ofInt k := by
  simp only [intRange, mem_ofFinSet, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨a + i, by omega, by omega, rfl⟩
  · rintro ⟨k, hka, hkb, rfl⟩
    exact ⟨(k - a).toNat, by omega, by rw [ofInt_inj]; omega⟩

/-- The pairs of a `seqGraphFrom`: one per list position, keyed by its index. -/
theorem mem_seqGraphFrom {z : Value} {start : ℕ} {vs : List Value} :
    z ∈ seqGraphFrom start vs ↔
      ∃ i, ∃ h : i < vs.length, z = ZFSet.pair (ofNat (start + i)) vs[i] := by
  induction vs generalizing start with
  | nil => simp [seqGraphFrom, ZFSet.notMem_empty]
  | cons v vs ih =>
    rw [seqGraphFrom, ZFSet.mem_insert_iff, ih]
    iff_rintro (rfl | ⟨i, hi, rfl⟩) ⟨i, hi, rfl⟩
    · exact ⟨0, by simp, by simp⟩
    · exists i + 1, by simpa using hi
      have h : start + 1 + i = start + (i + 1) := by omega
      rw [h, List.getElem_cons_succ]
    · cases i with
      | zero => exact Or.inl (by simp)
      | succ k =>
        refine Or.inr ⟨k, by simpa using hi, ?_⟩
        have h : start + (k + 1) = start + 1 + k := by omega
        rw [h, List.getElem_cons_succ]

/-- The pairs of a `seqGraphFrom` starting at `1`, the sequence/tuple encoding. -/
theorem mem_ofSeq {z : Value} {vs : List Value} :
    z ∈ ofSeq vs ↔ ∃ i, ∃ h : i < vs.length, z = ZFSet.pair (ofNat (i + 1)) vs[i] := by
  rewrite [ofSeq, mem_seqGraphFrom]
  simp only [Nat.add_comm]

/-- The sequence/tuple encoding is injective. -/
theorem ofSeq_inj {vs ws : List Value} : ofSeq vs = ofSeq ws ↔ vs = ws := by
  refine ⟨λ h ↦ ?_, λ h ↦ h ▸ rfl⟩
  have key : ∀ (as bs : List Value), ofSeq as = ofSeq bs →
      ∀ i, ∀ hi : i < as.length, ∃ _ : i < bs.length, as[i] = bs[i] := by
    intro as bs hab i hi
    have hmem : ZFSet.pair (ofNat (i + 1)) as[i] ∈ ofSeq bs := by
      rw [← hab]; exact mem_ofSeq.mpr ⟨i, hi, rfl⟩
    obtain ⟨j, hj, he⟩ := mem_ofSeq.mp hmem
    rw [ZFSet.pair_inj, ofNat_inj] at he
    obtain ⟨hij, hv⟩ := he
    obtain rfl : i = j := by omega
    exact ⟨hj, hv⟩
  have hle : ∀ (as bs : List Value), ofSeq as = ofSeq bs → as.length ≤ bs.length := by
    intro as bs hab
    by_contra! hc
    obtain ⟨hj, _⟩ := key as bs hab bs.length (by omega)
    omega
  exact List.ext_getElem (Nat.le_antisymm (hle vs ws h) (hle ws vs h.symm))
    (λ i h1 _ ↦ (key vs ws h i h1).2)

/-- A sequence/tuple value is a partial function: `{1 ↦ v₁, …, n ↦ vₙ}` over the interval `1 .. n`
into its own elements. This is the `IsPFunc` witness `fnApply`/`ZFSet.fapply` needs to read a
sequence at an index. -/
theorem ofSeq_isPFunc (vs : List Value) :
    (ofSeq vs).IsPFunc (intRange 1 vs.length) (ofFinSet vs) := by
  refine ⟨λ z hz ↦ ?_, λ x y hxy z hxz ↦ ?_⟩
  · obtain ⟨i, hi, rfl⟩ := mem_ofSeq.mp hz
    refine ZFSet.pair_mem_prod.mpr ⟨?_, mem_ofFinSet.mpr (List.getElem_mem hi)⟩
    rw [mem_intRange]
    exact ⟨(i : ℤ) + 1, by omega, by omega, by rw [ofNat, Nat.cast_add, Nat.cast_one]⟩
  · obtain ⟨i, hi, hei⟩ := mem_ofSeq.mp hxy
    obtain ⟨j, hj, hej⟩ := mem_ofSeq.mp hxz
    rw [ZFSet.pair_inj] at hei hej
    obtain ⟨hxi, rfl⟩ := hei
    obtain ⟨hxj, rfl⟩ := hej
    rw [hxi, ofNat_inj] at hxj
    obtain rfl : i = j := by omega
    rfl

/-- A sequence/tuple value is a total function from the interval `1 .. n` — the `IsFunc`
strengthening of `ofSeq_isPFunc`, adding that every index in range has an entry. -/
theorem ofSeq_isFunc (vs : List Value) :
    (intRange 1 vs.length).IsFunc (ofFinSet vs) (ofSeq vs) := by
  refine ⟨(ofSeq_isPFunc vs).1, λ z hz ↦ ?_⟩
  obtain ⟨k, hk1, hk2, rfl⟩ := mem_intRange.mp hz
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = (j : ℤ) + 1 := ⟨k.toNat - 1, by omega⟩
  have hj : j < vs.length := by omega
  have hcast : ofInt ((j : ℤ) + 1) = ofNat (j + 1) := by rw [ofNat, Nat.cast_add, Nat.cast_one]
  have hmem : ZFSet.pair (ofInt ((j : ℤ) + 1)) vs[j] ∈ ofSeq vs := by
    rw [hcast]; exact mem_ofSeq.mpr ⟨j, hj, rfl⟩
  exact ⟨vs[j], hmem, λ y hy ↦ ((ofSeq_isPFunc vs).2 _ _ hmem _ hy).symm⟩

/-- `s` is a sequence value: a total function over some interval `1 .. n`. TLA⁺'s
`s ∈ Seq(S)` with the codomain left to `∃`. -/
def IsSeqVal (s : Value) : Prop := ∃ (n : ℕ) (A : Value), (intRange 1 n).IsFunc A s

/-- The length of a sequence value: the `n` for which its domain is `1 .. n`. TLA⁺'s
`Len(s) == CHOOSE n ∈ Nat : DOMAIN s = 1 .. n`. Junk off sequence values. -/
noncomputable def lenOf (s : Value) : ℕ :=
  Classical.epsilon (λ n ↦ ∃ A : Value, (intRange 1 n).IsFunc A s)

/-- `ofSeq vs` is a sequence value. -/
theorem isSeqVal_ofSeq (vs : List Value) : IsSeqVal (ofSeq vs) :=
  ⟨vs.length, _, ofSeq_isFunc vs⟩

/-- Distinct lengths give distinct index intervals over `ℕ`. -/
theorem intRange_one_inj {m n : ℕ} (h : intRange 1 (m : ℤ) = intRange 1 (n : ℤ)) : m = n := by
  have key : ∀ a b : ℕ, intRange 1 (a : ℤ) = intRange 1 (b : ℤ) → a ≤ b := by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · omega
    · have hmem : ofInt (a : ℤ) ∈ intRange 1 (b : ℤ) := by
        rw [← hab]; exact mem_intRange.mpr ⟨a, by omega, le_refl _, rfl⟩
      obtain ⟨k, -, hk2, hk⟩ := mem_intRange.mp hmem
      rw [ofInt_inj] at hk; omega
  exact Nat.le_antisymm (key m n h) (key n m h.symm)

/-- Two index intervals over which the same value is a total function have the same length: the
value's own set of first coordinates pins the interval. -/
theorem isFunc_intRange_length_inj {s A B : Value} {m n : ℕ}
    (hm : (intRange 1 (m : ℤ)).IsFunc A s) (hn : (intRange 1 (n : ℤ)).IsFunc B s) : m = n := by
  refine intRange_one_inj (ZFSet.ext λ z ↦ ⟨λ hz ↦ ?_, λ hz ↦ ?_⟩)
  · obtain ⟨w, hw, -⟩ := hm.2 z hz
    exact (ZFSet.pair_mem_prod.mp (hn.1 hw)).1
  · obtain ⟨w, hw, -⟩ := hn.2 z hz
    exact (ZFSet.pair_mem_prod.mp (hm.1 hw)).1

/-- `lenOf (ofSeq vs)` is `vs.length`. -/
theorem lenOf_ofSeq (vs : List Value) : lenOf (ofSeq vs) = vs.length := by
  have hp : ∃ n : ℕ, ∃ A : Value, (intRange 1 (n : ℤ)).IsFunc A (ofSeq vs) :=
    ⟨vs.length, _, ofSeq_isFunc vs⟩
  obtain ⟨A, hA⟩ := Classical.epsilon_spec hp
  exact isFunc_intRange_length_inj hA (ofSeq_isFunc vs)

/-- The TLA⁺ cartesian product `A \X B`: every pair `<<a, b>>` with `a ∈ A` and `b ∈ B`. Carved
by `ZFSet.sep` out of the powerset that bounds the two-element tuple encodings, so it is a
closed-form function of `A` and `B`, not a set fixed only up to extensionality. -/
noncomputable def cartesian (A B : Value) : Value :=
  ZFSet.sep (λ z ↦ ∃ a ∈ A, ∃ b ∈ B, z = ofTuple [a, b])
    (ofFinSet [ofNat 1, ofNat 2] |>.prod (A ∪ B)).powerset

/-- `A \X B` holds exactly the pairs `<<a, b>>` with `a ∈ A` and `b ∈ B`. -/
@[simp] theorem mem_cartesian {z A B : Value} :
    z ∈ cartesian A B ↔ ∃ a ∈ A, ∃ b ∈ B, z = ofTuple [a, b] := by
  rw [cartesian, ZFSet.mem_sep, and_iff_right_iff_imp]
  rintro ⟨a, ha, b, hb, rfl⟩
  rw [ZFSet.mem_powerset]
  intro w hw
  simp only [ofTuple, mem_ofSeq] at hw
  obtain ⟨i, hi, rfl⟩ := hw
  rw [ZFSet.pair_mem_prod, mem_ofFinSet, ZFSet.mem_union]
  match i, hi with
  | 0, _ => exact ⟨by simp, .inl ha⟩
  | 1, _ => exact ⟨by simp, .inr hb⟩

/-- The pairs of a `recordGraph`: one per field, keyed by the string encoding of its name. -/
theorem mem_recordGraph {z : Value} {fs : List (String × Value)} :
    z ∈ recordGraph fs ↔ ∃ (k : String) (v : Value), (k, v) ∈ fs ∧ z = ZFSet.pair (ofString k) v := by
  induction fs with
  | nil => simp [recordGraph]
  | cons f fs ih =>
    obtain ⟨k, v⟩ := f
    rw [recordGraph, ZFSet.mem_insert_iff, ih]
    iff_rintro (rfl | ⟨k', v', hmem, rfl⟩) ⟨k', v', hmem, rfl⟩
    · exact ⟨k, v, by simp, rfl⟩
    · exact ⟨k', v', by simp [hmem], rfl⟩
    · rw [List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. |>.mp heq
        exact Or.inl rfl
      · exact Or.inr ⟨k', v', hmem, rfl⟩

/-- TLA⁺'s `{n ∈ Nat : n > 0}` — the strictly positive integers, `Bags`' codomain
(`Bags!IsABag`'s `[DOMAIN B -> {n ∈ Nat : n > 0}]`). -/
noncomputable def posNatSet : Value :=
  ZFSet.sep (λ z ↦ ∃ k : ℤ, 0 < k ∧ z = ofInt k) ZFSet.Int

/-- `{n ∈ Nat : n > 0}` holds exactly the strictly positive integer encodings. -/
@[simp] theorem mem_posNatSet {z : Value} : z ∈ posNatSet ↔ ∃ k : ℤ, 0 < k ∧ z = ofInt k := by
  rw [posNatSet, ZFSet.mem_sep, and_iff_right_iff_imp]
  rintro ⟨k, -, rfl⟩
  exact ofInt_mem_int

/-- `B` is a bag value: a total function from some carrier set into the strictly positive
integers — `Bags!IsABag`'s own defining condition, `B ∈ [DOMAIN B -> {n ∈ Nat : n > 0}]`. -/
def IsBagVal (B : Value) : Prop := ∃ A : Value, ZFSet.IsFunc A posNatSet B

/-- `Bags!SetToBag(S)`: the bag containing exactly one copy of every element of `S`,
`[e ∈ S ↦ 1]`. Its graph is the product of `S` with the singleton `{1}` directly —
`ZFSet.prod`'s own membership characterisation already is the graph, no `sep` needed. -/
noncomputable def setToBag (S : Value) : Value := S.prod ({ofNat 1} : Value)

/-- `SetToBag S` holds exactly the pairs `⟨w, 1⟩` with `w ∈ S`. -/
@[simp] theorem mem_setToBag {z S : Value} :
    z ∈ setToBag S ↔ ∃ w ∈ S, z = ZFSet.pair w (ofNat 1) := by
  simp only [setToBag, ZFSet.mem_prod, ZFSet.mem_singleton]
  grind

/-- The first coordinate of any pair of `f` is reachable through `⋃₀ ⋃₀ f` — symmetric to
`Operational.lean`'s (private) `snd_mem_sUsU` for the second. -/
private theorem fst_mem_sUsU {f k w : Value} (h : ZFSet.pair k w ∈ f) :
    k ∈ ZFSet.sUnion (ZFSet.sUnion f) := by
  have h1 : ({k} : ZFSet) ∈ ZFSet.pair k w := by
    rw [ZFSet.pair, ZFSet.mem_insert_iff]; left; rfl
  exact ZFSet.mem_sUnion.mpr ⟨{k}, ZFSet.mem_sUnion.mpr ⟨_, h, h1⟩, ZFSet.mem_singleton.mpr rfl⟩

/-- The set of first coordinates among `f`'s pairs — `DOMAIN f` without needing an `IsPFunc`
witness first. Bounded the same way `fnRead` is (`⋃₀ ⋃₀ f` reaches every coordinate of every pair
of `f`), so it is total on any `Value`, not just a genuine function graph. `bagAdd`/`bagSub` build
on this rather than `Value.Dom` so they need no well-formedness proof to construct. -/
noncomputable def rawDom (f : Value) : Value :=
  ZFSet.sep (λ e ↦ ∃ c, ZFSet.pair e c ∈ f) (ZFSet.sUnion (ZFSet.sUnion f))

/-- `rawDom f` holds exactly the keys `f` pairs something with. -/
@[simp] theorem mem_rawDom {e f : Value} : e ∈ rawDom f ↔ ∃ c, ZFSet.pair e c ∈ f := by
  rw [rawDom, ZFSet.mem_sep, and_iff_right_iff_imp]
  rintro ⟨c, hc⟩
  exact fst_mem_sUsU hc

/-- The multiplicity `f` assigns `e`, or `0` when `f` has no pair at `e` — `CopiesIn`'s own
"else 0" branch, as a value-level function so a `sep` predicate can use it directly instead of an
existential disjunction. Junk (an unspecified count) only if `f` pairs `e` with something other
than a single `ofNat`-shaped value; every genuine bag graph does not, so this only matters off
`IsBagVal`, same convention as `lenOf`. -/
noncomputable def copiesInRaw (e f : Value) : ℕ :=
  Classical.epsilon (λ n ↦ ZFSet.pair e (ofNat n) ∈ f ∨ (n = 0 ∧ e ∉ rawDom f))

/-- Off `rawDom f`, `copiesInRaw` is exactly `0` — the only `n` satisfying its defining
disjunction's second arm, and the first is unreachable. -/
theorem copiesInRaw_eq_zero {e f : Value} (he : e ∉ rawDom f) : copiesInRaw e f = 0 := by
  have hp : ∃ n, ZFSet.pair e (ofNat n) ∈ f ∨ (n = 0 ∧ e ∉ rawDom f) := ⟨0, Or.inr ⟨rfl, he⟩⟩
  rcases Classical.epsilon_spec hp with h | ⟨h, -⟩
  · absurd (mem_rawDom.mpr ⟨_, h⟩); exact he
  · exact h

/-- A genuine bag's own stored count at `e` is exactly what `copiesInRaw` computes — the
`IsFunc`-uniqueness half of the graph-reconstruction fact `bagToFun`'s coercion proof needs
(`Bag(τ) <: τ → Int` is discharged as an eta-expansion through `BagToSet`/`CopiesIn`, so proving
it correct means showing the eta-expanded graph reproduces the bag exactly). -/
theorem IsBagVal.eq_ofNat_copiesInRaw {f : Value} (hf : IsBagVal f) {e c : Value}
    (h : ZFSet.pair e c ∈ f) : c = ofNat (copiesInRaw e f) := by
  obtain ⟨A, hA⟩ := hf
  have he : e ∈ rawDom f := mem_rawDom.mpr ⟨c, h⟩
  obtain ⟨heA, hcPos⟩ := ZFSet.pair_mem_prod.mp (hA.1 h)
  obtain ⟨k, hk, hck⟩ := mem_posNatSet.mp hcPos
  have hc0 : c = ofNat k.toNat := by rw [hck, ofNat]; congr 1; omega
  have hp : ∃ n, ZFSet.pair e (ofNat n) ∈ f ∨ (n = 0 ∧ e ∉ rawDom f) :=
    ⟨k.toNat, Or.inl (hc0 ▸ h)⟩
  rcases Classical.epsilon_spec hp with hev | ⟨-, hne⟩
  · exact (hA.2 e heA).unique h hev
  · absurd he; exact hne

/-- The other half: a genuine bag actually *has* a stored pair at every key of its domain, at
exactly the count `copiesInRaw` computes. -/
theorem IsBagVal.mem_copiesInRaw {f : Value} (hf : IsBagVal f) {w : Value} (hw : w ∈ rawDom f) :
    ZFSet.pair w (ofNat (copiesInRaw w f)) ∈ f := by
  obtain ⟨c, hc⟩ := mem_rawDom.mp hw
  rwa [hf.eq_ofNat_copiesInRaw hc] at hc

/-- A genuine bag's graph is exactly the graph `copiesInRaw` characterises — the
self-reconstruction fact underlying `bagToFun`'s coercion correctness (`evalCoerce'`'s
`.bagToFun` case): the `.fn` the coercion eta-expands to reproduces `f` exactly because `f`
already *is* this graph. -/
theorem IsBagVal.mem_iff {f : Value} (hf : IsBagVal f) {z : Value} :
    z ∈ f ↔ ∃ w ∈ rawDom f, z = ZFSet.pair w (ofNat (copiesInRaw w f)) := by
  obtain ⟨A, hA⟩ := hf
  constructor
  · intro hz
    obtain ⟨w, -, c, -, rfl⟩ := ZFSet.mem_prod.mp (hA.1 hz)
    exact ⟨w, mem_rawDom.mpr ⟨c, hz⟩,
      congrArg (ZFSet.pair w) (IsBagVal.eq_ofNat_copiesInRaw ⟨A, hA⟩ hz)⟩
  · rintro ⟨w, hw, rfl⟩
    exact IsBagVal.mem_copiesInRaw ⟨A, hA⟩ hw

/-- `Bags!(+)`: multiset sum, `[e ∈ (DOMAIN B1) ∪ (DOMAIN B2) ↦ CopiesIn(e,B1) + CopiesIn(e,B2)]`.
Total on any two `Value`s — `rawDom`/`copiesInRaw`, not `Value.Dom`, so no well-formedness proof
is needed to build it. `e ∈ rawDom B1 ∪ rawDom B2` sits inside the existential (not just the
bound) so the predicate can't be satisfied by an `e` outside both domains with count `0` — that
`z` genuinely is not a member, and a membership lemma stating otherwise would be false. -/
noncomputable def bagAdd (B1 B2 : Value) : Value :=
  ZFSet.sep
    (λ z ↦ ∃ e ∈ rawDom B1 ∪ rawDom B2,
      z = ZFSet.pair e (ofNat (copiesInRaw e B1 + copiesInRaw e B2)))
    ((rawDom B1 ∪ rawDom B2).prod posNatSet)

/-- `bagAdd B1 B2` holds exactly the pairs `⟨e, c1 + c2⟩` where `c1`/`c2` are `e`'s count in
`B1`/`B2`, `e` in at least one of the two domains and the sum strictly positive (`sep`'s bound —
matters only for garbage input where a stored count is itself `0`; a genuine `IsBagVal` bag never
stores one). -/
theorem mem_bagAdd {z B1 B2 : Value} :
    z ∈ bagAdd B1 B2 ↔ ∃ e ∈ rawDom B1 ∪ rawDom B2,
      0 < copiesInRaw e B1 + copiesInRaw e B2 ∧
      z = ZFSet.pair e (ofNat (copiesInRaw e B1 + copiesInRaw e B2)) := by
  rw [bagAdd, ZFSet.mem_sep]
  constructor
  · rintro ⟨hbound, e, he, rfl⟩
    obtain ⟨-, hc⟩ := ZFSet.pair_mem_prod.mp hbound
    obtain ⟨k, hk, hke⟩ := mem_posNatSet.mp hc
    rw [ofNat] at hke
    have hnk : (copiesInRaw e B1 + copiesInRaw e B2 : ℤ) = k := ofInt_inj.mp hke
    exact ⟨e, he, by omega, rfl⟩
  · rintro ⟨e, he, hpos, rfl⟩
    refine ⟨ZFSet.pair_mem_prod.mpr ⟨he, mem_posNatSet.mpr
      ⟨(copiesInRaw e B1 + copiesInRaw e B2 : ℕ), ?_, ?_⟩⟩, e, he, rfl⟩
    · exact_mod_cast hpos
    · rw [ofNat, Nat.cast_add]

/-- `Bags!(-)`: multiset difference, domain restricted to `B1`'s, each count clamped to `0` and
dropped there (ℕ's `-` is already truncated, so `copiesInRaw e B1 - copiesInRaw e B2` *is*
`max(c1 - c2, 0)`; `sep`'s codomain bound then drops the zero-count keys). Total on any two
`Value`s, same reason `bagAdd` is. -/
noncomputable def bagSub (B1 B2 : Value) : Value :=
  ZFSet.sep
    (λ z ↦ ∃ e ∈ rawDom B1, z = ZFSet.pair e (ofNat (copiesInRaw e B1 - copiesInRaw e B2)))
    ((rawDom B1).prod posNatSet)

/-- `bagSub B1 B2` holds exactly the pairs `⟨e, c1 - c2⟩` (ℕ-truncated) with `e ∈ rawDom B1` and
the difference strictly positive. -/
theorem mem_bagSub {z B1 B2 : Value} :
    z ∈ bagSub B1 B2 ↔ ∃ e ∈ rawDom B1,
      0 < copiesInRaw e B1 - copiesInRaw e B2 ∧
      z = ZFSet.pair e (ofNat (copiesInRaw e B1 - copiesInRaw e B2)) := by
  rw [bagSub, ZFSet.mem_sep]
  constructor
  · rintro ⟨hbound, e, he, rfl⟩
    obtain ⟨-, hc⟩ := ZFSet.pair_mem_prod.mp hbound
    obtain ⟨k, hk, hke⟩ := mem_posNatSet.mp hc
    rw [ofNat] at hke
    have hnk : ((copiesInRaw e B1 - copiesInRaw e B2 : ℕ) : ℤ) = k := ofInt_inj.mp hke
    exact ⟨e, he, by omega, rfl⟩
  · rintro ⟨e, he, hpos, rfl⟩
    refine ⟨ZFSet.pair_mem_prod.mpr ⟨he, mem_posNatSet.mpr
      ⟨(copiesInRaw e B1 - copiesInRaw e B2 : ℕ), ?_, ?_⟩⟩, e, he, rfl⟩
    · exact_mod_cast hpos
    · rw [ofNat]

/-- `Bags!SubBag(B)`'s `AllBagsOfSubset` (TLA⁺ book definition, not `Bags.tla`'s own recursive
one): every bag graph whose carrier is some subset of `B`'s domain — `UNION {[SB -> {n ∈ Nat : n >
0}] : SB ∈ SUBSET BagToSet(B)}`. One `powerset` layer bounds it, since each element is itself a
graph (`⊆ T.prod posNatSet ⊆ (rawDom B).prod posNatSet` for its own carrier `T ⊆ rawDom B`). -/
noncomputable def allBagsOfSubset (B : Value) : Value :=
  ZFSet.sep (λ z ↦ ∃ T ⊆ rawDom B, ZFSet.IsFunc T posNatSet z)
    (ZFSet.powerset ((rawDom B).prod posNatSet))

/-- `AllBagsOfSubset B` holds exactly the total functions from some subset of `rawDom B` into the
strictly positive integers. -/
theorem mem_allBagsOfSubset {z B : Value} :
    z ∈ allBagsOfSubset B ↔ ∃ T ⊆ rawDom B, ZFSet.IsFunc T posNatSet z := by
  rw [allBagsOfSubset, ZFSet.mem_sep, and_iff_right_iff_imp]
  rintro ⟨T, hT, hf⟩
  rw [ZFSet.mem_powerset]
  intro w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp ((ZFSet.is_func_is_pfunc hf).1 hw)
  exact ZFSet.mem_prod.mpr ⟨a, hT ha, b, hb, rfl⟩

/-- `Bags!SubBag(B)`: every sub-bag of `B` — `AllBagsOfSubset B` filtered to the graphs whose
count at each of its own keys is at most `B`'s. `copiesInRaw`, not `Value.Dom`/`fnApply`, so no
well-formedness proof is needed for `B` either. -/
noncomputable def subBag (B : Value) : Value :=
  ZFSet.sep (λ SB ↦ ∀ e ∈ rawDom SB, copiesInRaw e SB ≤ copiesInRaw e B) (allBagsOfSubset B)

/-- `SubBag B` holds exactly the bag graphs in `AllBagsOfSubset B` whose count nowhere exceeds
`B`'s own. -/
theorem mem_subBag {SB B : Value} :
    SB ∈ subBag B ↔ (∃ T ⊆ rawDom B, ZFSet.IsFunc T posNatSet SB) ∧
      ∀ e ∈ rawDom SB, copiesInRaw e SB ≤ copiesInRaw e B := by
  rw [subBag, ZFSet.mem_sep, mem_allBagsOfSubset]

open Classical in
/-- `Bags!BagUnion(S)`: multiset sum across every bag of `S`, `[e ∈ ⋃{BagToSet(B) : B ∈ S} ↦
Sum({CopiesIn(e,B) : B ∈ S})]`. `⋃₀ S` is already exactly "every pair from every bag of `S`", so
its `rawDom` is `S`'s combined domain directly — no separate bound construction needed. The count
needs `S` itself finite (`hS`, `ZFSet.IsFinite` — proven correct via `ZFSet.sumUpTo_insert`, not
a bespoke fold) to sum over; every other `Bags` builder is total precisely because none of the
rest needs to sum across a *set* of bags. -/
noncomputable def bagUnion (S : Value) (hS : S.IsFinite) : Value :=
  ZFSet.sep
    (λ z ↦ ∃ e ∈ rawDom (ZFSet.sUnion S), z = ZFSet.pair e (ofNat (hS.sum (copiesInRaw e))))
    ((rawDom (ZFSet.sUnion S)).prod posNatSet)

/-- `bagUnion S hS` holds exactly the pairs `⟨e, Σ⟩` where `Σ` sums `e`'s count across every bag
of `S`, `e` a key of some bag of `S` and the sum strictly positive. -/
theorem mem_bagUnion {z S : Value} {hS : S.IsFinite} :
    z ∈ bagUnion S hS ↔ ∃ e ∈ rawDom (ZFSet.sUnion S),
      0 < hS.sum (copiesInRaw e) ∧ z = ZFSet.pair e (ofNat (hS.sum (copiesInRaw e))) := by
  rw [bagUnion, ZFSet.mem_sep]
  constructor
  · rintro ⟨hbound, e, he, rfl⟩
    obtain ⟨-, hc⟩ := ZFSet.pair_mem_prod.mp hbound
    obtain ⟨k, hk, hke⟩ := mem_posNatSet.mp hc
    rw [ofNat] at hke
    have hnk : ((hS.sum (copiesInRaw e) : ℕ) : ℤ) = k := ofInt_inj.mp hke
    exact ⟨e, he, by omega, rfl⟩
  · rintro ⟨e, he, hpos, rfl⟩
    refine ⟨ZFSet.pair_mem_prod.mpr ⟨he, mem_posNatSet.mpr
      ⟨hS.sum (copiesInRaw e), ?_, ?_⟩⟩, e, he, rfl⟩
    · exact_mod_cast hpos
    · rw [ofNat]

/-- `Bags!BagCardinality(B) == Sum(B)`: the sum of `B`'s own multiplicities. Same
`ZFSet.IsFinite.sum` `bagUnion`'s count uses, applied to one bag instead of a set of them. -/
noncomputable def bagCardinality (B : Value) (hB : (rawDom B).IsFinite) : ℕ :=
  hB.sum (copiesInRaw · B)

/-- `ZFSet` carries no canonical structural pretty-printer; a value prints as an opaque
placeholder. Present only so that a structure carrying a `Value` can still derive `Repr`. -/
instance : Repr Value := ⟨λ _ _ ↦ "(value : ZFSet)"⟩

/-- Value equality, classically. `ZFSet` equality is a universally quantified statement, so this
is noncomputable — harmless, since evaluation is a `Prop` relation. -/
noncomputable instance : DecidableEq Value := λ a b ↦ Classical.propDecidable (a = b)

noncomputable instance : BEq Value := ⟨λ a b ↦ decide (a = b)⟩

end Value

end ComputableTLAPlus

end
