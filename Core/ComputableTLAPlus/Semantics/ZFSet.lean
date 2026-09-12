module

meta import CustomPrelude
public import ZFLean.Functions
public import ZFLean.Naturals
import all ZFLean.Functions

/-!
  `ZFSet.IsFinite` carries no `@[expose]` upstream (`ZFLean.Functions`), so a downstream
  `obtain`/`cases` on an `IsFinite` hypothesis fails ("not an inductive datatype") — the same
  problem `Value.ofInt` has with the private-bodied `ZFSet.ZFInt`, same escape hatch: `import all`
  exposes the body privately. Kept to this one small file rather than reaching for `import all`
  inside `Value.lean` directly, so the exposure's blast radius (every private declaration of
  `ZFLean.Functions`, not just `IsFinite`) stays contained — `Value.lean` and everything downstream
  only ever sees the ordinary, already-exposed conclusion below.
-/

@[expose] public section

/-- Unpacks `x.IsFinite` into its witnesses directly — same content `IsFinite` already carries,
just through a statement whose own head is a plain `∃` (not a private-bodied `def`), so callers
outside this file can `obtain` it normally. -/
theorem ZFSet.IsFinite.exists_witness {x : ZFSet} (h : x.IsFinite) :
    ∃ (n : ZFNat) (f : ZFSet) (hf : f ∈ x.funs n.val), f.IsInjective (ZFSet.mem_funs.mp hf) := by
  obtain ⟨n, f, hn, hf, hinj⟩ := h
  exact ⟨⟨n, hn⟩, f, hf, hinj⟩

open Classical in
/-- Sums `g` across the (at most) `n`-many elements of `x` that `f` (an injective total function
into the ordinal `n`) accounts for, by recursion on `n` — `Bags.tla`'s own `DSum` algorithm,
adapted so `f` never gets restricted to a smaller domain: it stays fixed, and the recursion
instead sweeps through which part of the *codomain* has been accounted for so far, adding `g` of
whichever element of `x` (unique, by injectivity) `f` sends to the ordinal being peeled off. -/
noncomputable def ZFSet.sumUpTo (x f : ZFSet) (g : ZFSet → ℕ) (n : ZFNat) : ℕ :=
  ZFNat.rec n 0
    (λ (k : ZFNat) ih ↦
      if h : ∃ a ∈ x, ZFSet.pair a k.val ∈ f then ih + g h.choose else ih)

/-- `sumUpTo _ _ _ 0 = 0` — nothing has been swept yet. -/
theorem ZFSet.sumUpTo_zero {x f : ZFSet} {g : ZFSet → ℕ} : ZFSet.sumUpTo x f g 0 = 0 :=
  ZFNat.rec_zero _ _

open Classical in
/-- `sumUpTo`'s defining unfold at a successor: one more step of the codomain sweep. -/
theorem ZFSet.sumUpTo_succ {x f : ZFSet} {g : ZFSet → ℕ} {k : ZFNat} :
    ZFSet.sumUpTo x f g (ZFNat.succ k) =
      if h : ∃ a ∈ x, ZFSet.pair a k.val ∈ f then ZFSet.sumUpTo x f g k + g h.choose
      else ZFSet.sumUpTo x f g k :=
  ZFNat.rec_succ k _ _

open Classical in
/-- Auxiliary form of `sumUpTo_insert`: tracks whether the sweep up to `n` has reached `a`'s own
slot yet, rather than assuming it has — the base case (`n = 0`) then needs no contradiction, and
the successor case's two sub-cases (`a`'s slot is the one just swept, or isn't) both reduce to
this same statement one step down, rather than needing a separate "hasn't reached yet" lemma.

Takes plain pairwise injectivity and single-valuedness on `insert a x`, not an `IsFunc`-into-`n`
witness — totality into a *specific* `n` doesn't carry from `n + 1` down to `n` (an element could
map to exactly the top slot `n`, so `f` restricted need not still be total into `n`), but neither
of these depends on `n` at all, so the induction's `ih` applies unconditionally.
Single-valuedness matters here specifically: without it `a` could pair with more than one `b`,
and its `g`-value would get counted once per such `b` instead of exactly once. -/
theorem ZFSet.sumUpTo_insert_aux {x a f : ZFSet} {g : ZFSet → ℕ} (ha : a ∉ x)
    (hfunc : ∀ a' ∈ insert a x, ∀ b1 b2, ZFSet.pair a' b1 ∈ f → ZFSet.pair a' b2 ∈ f → b1 = b2)
    (hinj : ∀ a1 ∈ insert a x, ∀ a2 ∈ insert a x, ∀ b,
      ZFSet.pair a1 b ∈ f → ZFSet.pair a2 b ∈ f → a1 = a2) :
    ∀ n : ZFNat, ZFSet.sumUpTo (insert a x) f g n =
      ZFSet.sumUpTo x f g n + (if ∃ b ∈ n.val, ZFSet.pair a b ∈ f then g a else 0) := by
  intro n
  induction n with
  | zero =>
    rw [ZFSet.sumUpTo_zero, ZFSet.sumUpTo_zero, zero_add, if_neg]
    rintro ⟨b, hb, -⟩
    exact ZFSet.notMem_empty b hb
  | succ k ih =>
    simp only [ZFNat.add_one_eq_succ, ZFSet.sumUpTo_succ, ih]
    by_cases hak : ZFSet.pair a k.val ∈ f
    · have hnx : ¬∃ a' ∈ x, ZFSet.pair a' k.val ∈ f := by
        rintro ⟨a', ha', hp⟩
        exact ha (hinj a' (ZFSet.mem_insert_iff.mpr (Or.inr ha')) a
          (ZFSet.mem_insert_iff.mpr (Or.inl rfl)) k.val hp hak ▸ ha')
      have hnbelow : ¬∃ b ∈ k.val, ZFSet.pair a b ∈ f := by
        rintro ⟨b, hb, hp⟩
        exact ZFSet.mem_irrefl k.val
          (hfunc a (ZFSet.mem_insert_iff.mpr (Or.inl rfl)) k.val b hak hp ▸ hb)
      have hins : ∃ a1 ∈ insert a x, ZFSet.pair a1 k.val ∈ f :=
        ⟨a, ZFSet.mem_insert_iff.mpr (Or.inl rfl), hak⟩
      have hsucc_val : (ZFNat.succ k).val = insert k.val k.val := rfl
      have hbelow : ∃ b ∈ (ZFNat.succ k).val, ZFSet.pair a b ∈ f :=
        ⟨k.val, hsucc_val ▸ ZFSet.mem_insert_iff.mpr (Or.inl rfl), hak⟩
      rw [dif_pos hins, if_neg hnbelow, dif_neg hnx, if_pos hbelow]
      have hceq := hinj hins.choose hins.choose_spec.1 a
        (ZFSet.mem_insert_iff.mpr (Or.inl rfl)) k.val hins.choose_spec.2 hak
      rw [hceq]
      omega
    · have hins_iff_x : (∃ a1 ∈ insert a x, ZFSet.pair a1 k.val ∈ f) ↔
          (∃ a' ∈ x, ZFSet.pair a' k.val ∈ f) := by
        constructor
        · rintro ⟨a1, ha1, hp⟩
          rcases ZFSet.mem_insert_iff.mp ha1 with rfl | ha1x
          · nomatch hak hp
          · exact ⟨a1, ha1x, hp⟩
        · rintro ⟨a', ha', hp⟩
          exact ⟨a', ZFSet.mem_insert_iff.mpr (Or.inr ha'), hp⟩
      have hsucc_val : (ZFNat.succ k).val = insert k.val k.val := rfl
      have hsucc_iff_below : (∃ b ∈ (ZFNat.succ k).val, ZFSet.pair a b ∈ f) ↔
          (∃ b ∈ k.val, ZFSet.pair a b ∈ f) := by
        rw [hsucc_val]
        constructor
        · rintro ⟨b, hb, hp⟩
          rcases ZFSet.mem_insert_iff.mp hb with rfl | hb
          · nomatch hak hp
          · exact ⟨b, hb, hp⟩
        · rintro ⟨b, hb, hp⟩
          exact ⟨b, ZFSet.mem_insert_iff.mpr (Or.inr hb), hp⟩
      simp only [hsucc_iff_below]
      split_ifs with h1 h2 h3 h4 h5 h6 h7
      · have hw1 := h1.choose_spec
        have hw2 := h3.choose_spec
        rw [hinj h1.choose hw1.1 h3.choose (ZFSet.mem_insert_iff.mpr (Or.inr hw2.1)) k.val
          hw1.2 hw2.2]
        omega
      · exfalso
        obtain ⟨a1, ha1, hp⟩ := h1
        rcases ZFSet.mem_insert_iff.mp ha1 with rfl | ha1x
        · exact hak hp
        · exact h3 ⟨a1, ha1x, hp⟩
      · have hw1 := h1.choose_spec
        have hw2 := h4.choose_spec
        rw [hinj h1.choose hw1.1 h4.choose (ZFSet.mem_insert_iff.mpr (Or.inr hw2.1)) k.val
          hw1.2 hw2.2]
        omega
      · exfalso
        obtain ⟨a1, ha1, hp⟩ := h1
        rcases ZFSet.mem_insert_iff.mp ha1 with rfl | ha1x
        · exact hak hp
        · exact h4 ⟨a1, ha1x, hp⟩
      · exfalso
        obtain ⟨a2, ha2, hp⟩ := h6
        exact h1 ⟨a2, ZFSet.mem_insert_iff.mpr (Or.inr ha2), hp⟩
      · rfl
      · exfalso
        obtain ⟨a2, ha2, hp⟩ := h7
        exact h1 ⟨a2, ZFSet.mem_insert_iff.mpr (Or.inr ha2), hp⟩
      · rfl

/-- `sumUpTo_insert_aux` without the "has the sweep reached `a` yet" guard: given `f` genuinely
*total* on `insert a x` into `n` (not just injective), `a`'s slot is always reached by the time
the sweep finishes, so the `if` always resolves true. This is `sumUpTo`'s actual correctness
statement — matches what a caller building an `EvalBuiltin` rule from an `IsFinite` witness
(`exists_witness`, always total) will have in hand, without needing to separately show `a`'s slot
falls within range. -/
theorem ZFSet.sumUpTo_insert {x a f : ZFSet} {g : ZFSet → ℕ} {n : ZFNat} (ha : a ∉ x)
    (hf : f ∈ (insert a x).funs n.val) (hfinj : f.IsInjective (ZFSet.mem_funs.mp hf)) :
    ZFSet.sumUpTo (insert a x) f g n = g a + ZFSet.sumUpTo x f g n := by
  have hIsFunc := ZFSet.mem_funs.mp hf
  have hfunc : ∀ a' ∈ insert a x, ∀ b1 b2, ZFSet.pair a' b1 ∈ f → ZFSet.pair a' b2 ∈ f → b1 = b2 :=
    λ a' ha' b1 b2 hb1 hb2 ↦ (hIsFunc.2 a' ha').unique hb1 hb2
  have hinjRaw : ∀ a1 ∈ insert a x, ∀ a2 ∈ insert a x, ∀ b,
      ZFSet.pair a1 b ∈ f → ZFSet.pair a2 b ∈ f → a1 = a2 := by
    intro a1 ha1 a2 ha2 b hb1 hb2
    obtain ⟨-, hb⟩ := ZFSet.pair_mem_prod.mp (hIsFunc.1 hb1)
    exact hfinj a1 a2 b ha1 ha2 hb hb1 hb2
  obtain ⟨w, hw, -⟩ := hIsFunc.2 a (ZFSet.mem_insert_iff.mpr (Or.inl rfl))
  have haw : ∃ b ∈ n.val, ZFSet.pair a b ∈ f :=
    ⟨w, (ZFSet.pair_mem_prod.mp (hIsFunc.1 hw)).2, hw⟩
  have heq := ZFSet.sumUpTo_insert_aux (g := g) ha hfunc hinjRaw n
  rw [if_pos haw] at heq
  omega

/-- The sum of `g` across every element of `x`, given `x` finite. `IsFinite` erases its witness
(a bare `∃`), so `n`/`f` come out via `Classical.choose`, not `obtain` — destructuring a `Prop`
to build `ℕ` data is exactly what `Exists.casesOn` refuses. -/
noncomputable def ZFSet.IsFinite.sum {x : ZFSet} (h : x.IsFinite) (g : ZFSet → ℕ) : ℕ :=
  ZFSet.sumUpTo x h.exists_witness.choose_spec.choose g h.exists_witness.choose

/-- `sumUpTo` only ever calls `g` at elements of `x` (`sumUpTo_succ`'s own `h.choose ∈ x`), so two
`g`s agreeing there sum the same — the sweep itself (`x`/`f`/`n`) is untouched. -/
theorem ZFSet.sumUpTo_congr {x f : ZFSet} {g₁ g₂ : ZFSet → ℕ} {n : ZFNat}
    (h : ∀ a ∈ x, g₁ a = g₂ a) : ZFSet.sumUpTo x f g₁ n = ZFSet.sumUpTo x f g₂ n := by
  induction n with
  | zero => rw [ZFSet.sumUpTo_zero, ZFSet.sumUpTo_zero]
  | succ k ih =>
    rw [ZFNat.add_one_eq_succ, ZFSet.sumUpTo_succ, ZFSet.sumUpTo_succ, ih]
    split_ifs with hex
    · rw [h hex.choose hex.choose_spec.1]
    · rfl

/-- `IsFinite.sum` at two `g`s agreeing on `x` — `sumUpTo_congr` through the fixed witness
enumeration `IsFinite.sum` itself uses. -/
theorem ZFSet.IsFinite.sum_congr {x : ZFSet} (hx : x.IsFinite) {g₁ g₂ : ZFSet → ℕ}
    (h : ∀ a ∈ x, g₁ a = g₂ a) : hx.sum g₁ = hx.sum g₂ :=
  ZFSet.sumUpTo_congr h
