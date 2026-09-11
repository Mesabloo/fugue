module

import CustomPrelude

/-! Tests for `linter.fugue.subscriptSuffix` (opt-in — `default := false`). -/

-- Off by default: the backlog is the whole tree, same reasoning `sigIndent` gives.
#guard_msgs in
example (hf1 hf2 : Nat) : Nat := hf1 + hf2

-- Flags every occurrence, binder and each reference alike — same as `linter.fugue.exactAbsurd`
-- flagging every `exact absurd` call site, not just the first; one rename clears all of them.
/--
warning: write `hf₁`, not `hf1` — index suffix should be a Unicode subscript

Note: This linter can be disabled with `set_option linter.fugue.subscriptSuffix false`
---
warning: write `hf₂`, not `hf2` — index suffix should be a Unicode subscript

Note: This linter can be disabled with `set_option linter.fugue.subscriptSuffix false`
---
warning: write `hf₁`, not `hf1` — index suffix should be a Unicode subscript

Note: This linter can be disabled with `set_option linter.fugue.subscriptSuffix false`
---
warning: write `hf₂`, not `hf2` — index suffix should be a Unicode subscript

Note: This linter can be disabled with `set_option linter.fugue.subscriptSuffix false`
-/
#guard_msgs in
set_option linter.fugue.subscriptSuffix true in
example (hf1 hf2 : Nat) : Nat := hf1 + hf2

-- Already a Unicode subscript — not flagged.
#guard_msgs in
set_option linter.fugue.subscriptSuffix true in
example (hf₁ hf₂ : Nat) : Nat := hf₁ + hf₂

-- Fixed-width numeric type names are not index suffixes.
#guard_msgs in
set_option linter.fugue.subscriptSuffix true in
example (n : UInt64) : UInt64 := n
