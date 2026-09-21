import CubeToSU3.Hexagram64

/-!
# 京房八宮卦序是 Q₆ 的一個陪集分解

`Hexagram.lean` showed that the difference map

    δ : Q₆ → Q₃,   δ(下卦, 上卦) = 下 ⊕ 上

is a group homomorphism whose kernel is the diagonal — the eight hexagrams whose
two trigrams agree.  Those eight are exactly the 八純卦, the 本宮 of the eight
palaces.

京房's arrangement turns out to be precisely the coset decomposition that
homomorphism defines.

**The construction.**  Within a palace the eight hexagrams are obtained from the
本宮 by flipping a fixed pattern of yao, the same pattern in every palace:

| 位   | 變爻                  | 遮罩 |
|------|----------------------|------|
| 本宮 | —                    | `0`  |
| 一世 | 初                    | `32` |
| 二世 | 初二                  | `48` |
| 三世 | 初二三                | `56` |
| 四世 | 初二三四              | `60` |
| 五世 | 初二三四五            | `62` |
| 遊魂 | 四爻復原              | `58` |
| 歸魂 | 下卦復原              | `2`  |

Checked against the 乾宮: `63, 31, 15, 7, 3, 1, 5, 61` — 乾姤遯否觀剝晉大有.

**Why it covers all sixty-four exactly once.**  Not by construction or by
tradition: the eight masks land in eight *different* fibres of `δ`.  Their
`δ`-images are `0, 4, 6, 7, 3, 1, 5, 2` — the eight trigrams, each once.  So the
masks are a complete transversal of `ker δ`, the palaces are `ker δ` itself, and
`八宮 × 八世` is the coset decomposition `Q₆ = ker δ ⊕ transversal`.  Sixty-four
cells, no repeat, no gap.

**The walk.**  Consecutive positions differ by exactly one yao — seven times.
The single exception is 遊魂 → 歸魂, which changes three at once, because
restoring the lower trigram reverts 初二三 together.  So the palace sequence is
a Gray-code path with one jump, not a full Gray cycle.  That is a structural
fact about the received order, not a defect: 歸魂 is defined by restoring a
trigram, and a trigram is three yao.

**What this does not claim.**  Nothing about divination, and nothing about
physics.  `Q₆` corresponds to no root system (see `Hexagram.lean`), so this is
structure on the 易 side alone.
-/

namespace CubeToSU3.JingFang

open CubeToSU3.Hexagram64

/-! ## The eight positions -/

/-- The yao-flip mask of each of the eight positions in a palace. -/
def mask : Nat → Nat
  | 0 => 0   | 1 => 32  | 2 => 48  | 3 => 56
  | 4 => 60  | 5 => 62  | 6 => 58  | 7 => 2
  | _ => 0

/-- The 本宮 of palace `t` is the pure hexagram `(t, t)`. -/
def pureHex (t : Nat) : Nat := 9 * t

/-- The hexagram at position `p` of palace `t`. -/
def hex (t p : Nat) : Nat := pureHex t ^^^ mask p

/-- The difference map of `Hexagram.lean`, on `Nat`. -/
def delta (v : Nat) : Nat := (v / 8) ^^^ (v % 8)

/-! ## The 乾宮, against the received text -/

theorem qian_palace :
    hex 7 0 = 63 ∧ hex 7 1 = 31 ∧ hex 7 2 = 15 ∧ hex 7 3 = 7 ∧
    hex 7 4 = 3 ∧ hex 7 5 = 1 ∧ hex 7 6 = 5 ∧ hex 7 7 = 61 := by
  decide

/-! ## The palaces are the kernel -/

/-- The eight 本宮 are exactly the hexagrams killed by `δ`: the two trigrams
    agree, so their XOR is zero. -/
theorem pureHex_mem_kernel : ∀ t ∈ List.range 8, delta (pureHex t) = 0 := by
  decide

/-- And conversely — the kernel contains nothing else. -/
theorem kernel_eq_pureHex : ∀ v ∈ List.range 64,
    (delta v = 0 ↔ v = 0 ∨ v = 9 ∨ v = 18 ∨ v = 27 ∨
                   v = 36 ∨ v = 45 ∨ v = 54 ∨ v = 63) := by
  decide

/-! ## The masks are a transversal -/

/-- **The eight positions land in eight different fibres of `δ`.**  Their images
    are the eight trigrams, each exactly once, so the masks form a complete set
    of coset representatives for `ker δ`. -/
theorem mask_delta_values :
    delta (mask 0) = 0 ∧ delta (mask 1) = 4 ∧ delta (mask 2) = 6 ∧
    delta (mask 3) = 7 ∧ delta (mask 4) = 3 ∧ delta (mask 5) = 1 ∧
    delta (mask 6) = 5 ∧ delta (mask 7) = 2 := by
  decide

/-- Distinct positions give distinct fibres. -/
theorem mask_delta_injective : ∀ p ∈ List.range 8, ∀ q ∈ List.range 8,
    delta (mask p) = delta (mask q) → p = q := by
  decide

/-- The 世 of a hexagram is read off by `δ`, independently of the palace. -/
theorem delta_hex : ∀ t ∈ List.range 8, ∀ p ∈ List.range 8,
    delta (hex t p) = delta (mask p) := by
  decide

/-! ## Hence it covers the sixty-four exactly once -/

/-- All sixty-four cells of the eight-by-eight palace table. -/
def all64 : List Nat :=
  (List.range 8).flatMap fun t => (List.range 8).map fun p => hex t p

theorem all64_length : all64.length = 64 := by decide

/-- **Every hexagram appears.**  With sixty-four cells and sixty-four distinct
    hexagrams covered, the arrangement is a bijection — a consequence of the
    coset decomposition, not of the tradition having checked. -/
theorem all64_covers : ∀ v ∈ List.range 64, v ∈ all64 := by decide

/-! ## The walk -/

/-- Seven of the eight steps change exactly one yao. -/
theorem steps_single_yao :
    yangCount (mask 0 ^^^ mask 1) = 1 ∧
    yangCount (mask 1 ^^^ mask 2) = 1 ∧
    yangCount (mask 2 ^^^ mask 3) = 1 ∧
    yangCount (mask 3 ^^^ mask 4) = 1 ∧
    yangCount (mask 4 ^^^ mask 5) = 1 ∧
    yangCount (mask 5 ^^^ mask 6) = 1 ∧
    yangCount (mask 7 ^^^ mask 0) = 1 := by
  decide

/-- The exception is 遊魂 → 歸魂, which restores the lower trigram and so
    changes three yao at once. -/
theorem step_gui_hun : yangCount (mask 6 ^^^ mask 7) = 3 := by decide

/-! ## Axiom audit -/

#print axioms qian_palace
#print axioms pureHex_mem_kernel
#print axioms kernel_eq_pureHex
#print axioms mask_delta_injective
#print axioms delta_hex
#print axioms all64_covers
#print axioms steps_single_yao
#print axioms step_gui_hun

end CubeToSU3.JingFang
