import CubeToSU3.Hexagram

/-!
# 先天六十四卦圖就是 Q₆

The familiar diagram of the sixty-four hexagrams drawn as nested cubes is not a
mnemonic device: it **is** the six-dimensional hypercube `Q₆`, drawn by
projection.  Sixty-four vertices, one per hexagram; an edge joins two hexagrams
differing in exactly one yao; 乾 (`63`) and 坤 (`0`) sit at opposite ends of the
main diagonal.

The 先天 numbering on such diagrams is the binary value of the hexagram with the
**下爻 as the most significant bit**.  Checking against the picture: 乾 `= 63`,
坤 `= 0`, 師 `= 16`, 復 `= 32`, 比 `= 2`.  Since a hexagram is a lower trigram
under an upper one, the value splits as `8 · lower + upper`, which is the
factorisation `Q₆ = Q₃ × Q₃` that `Hexagram.lean` uses.

Three structures that the picture makes visible, all checked here:

* **錯卦** — flipping all six yao — is XOR with `63`, the antipodal map of the
  cube.  It is an involution with no fixed point, and it exchanges 乾 with 坤.
  On the two trigrams it acts componentwise, so it is the antipodal map of each
  `Q₃` factor at once.
* **綜卦** — turning the hexagram upside down — is reversal of the six bits.  It
  is also an involution, but it has **eight** fixed points: those hexagrams that
  read the same either way up.
* **三十六宮** — the fifty-six non-self-reversing hexagrams fall into twenty-eight
   綜 pairs, and with the eight self-reversing ones that makes thirty-six.  The
  traditional count is a consequence of the involution's fixed-point structure.

And one that the picture makes visible but is pure combinatorics: the hexagrams
sort by yang count into layers of sizes `1, 6, 15, 20, 15, 6, 1` — the binomial
coefficients `C(6,k)`, which are also the eigenvalue multiplicities of `Q₆`'s
adjacency operator.

Everything is stated on `Nat` restricted to `List.range 64`, so that bound
proofs never appear and `decide` sees plain arithmetic.

**What this does not do.**  `Q₆` does not correspond to a root system the way
`Q₃` does — see `Hexagram.lean` for the arithmetic.  This file adds structure to
the 易 side only.

Nothing here is a physical claim, and nothing here bears on the traditional uses
of these diagrams.
-/

namespace CubeToSU3.Hexagram64

/-! ## The numbering -/

/-- 錯卦: flip all six yao. -/
def cuo (v : Nat) : Nat := v ^^^ 63

/-- The `b`-th yao of a hexagram, `b = 0` being the 上爻. -/
def yao (v b : Nat) : Nat := v / 2 ^ b % 2

/-- 綜卦: turn the hexagram upside down, i.e. reverse the six yao. -/
def zong (v : Nat) : Nat :=
  yao v 0 * 32 + yao v 1 * 16 + yao v 2 * 8 + yao v 3 * 4 + yao v 4 * 2 + yao v 5

/-- Number of yang yao. -/
def yangCount (v : Nat) : Nat :=
  yao v 0 + yao v 1 + yao v 2 + yao v 3 + yao v 4 + yao v 5

/-- A hexagram splits into its lower and upper trigrams, the `Q₆ = Q₃ × Q₃` of
    `Hexagram.lean`: `v / 8` is the lower, `v % 8` the upper. -/
theorem hex_split : ∀ v ∈ List.range 64, v = 8 * (v / 8) + v % 8 := by decide

/-- The 先天 numbering against the picture. -/
theorem numbering_checks :
    8 * 7 + 7 = 63 ∧    -- 乾:下乾 上乾
    8 * 0 + 0 = 0 ∧     -- 坤
    8 * 2 + 0 = 16 ∧    -- 師:下坎 上坤
    8 * 4 + 0 = 32 ∧    -- 復:下震 上坤
    8 * 0 + 2 = 2 := by  -- 比:下坤 上坎
  decide

/-! ## 錯卦 is the antipodal map -/

theorem cuo_involutive : ∀ v ∈ List.range 64, cuo (cuo v) = v := by decide

theorem cuo_no_fixed : ∀ v ∈ List.range 64, cuo v ≠ v := by decide

theorem cuo_qian_kun : cuo 63 = 0 ∧ cuo 0 = 63 := by decide

/-- 錯 acts on the two trigrams componentwise: it is the antipodal map of each
    `Q₃` factor simultaneously. -/
theorem cuo_componentwise : ∀ v ∈ List.range 64,
    cuo v = 8 * (7 - v / 8) + (7 - v % 8) := by decide

/-- Every hexagram is at yao-distance six from its 錯卦 — the two ends of a main
    diagonal of `Q₆`. -/
theorem cuo_flips_all : ∀ v ∈ List.range 64,
    yangCount v + yangCount (cuo v) = 6 := by decide

/-! ## 綜卦 is bit reversal -/

theorem zong_involutive : ∀ v ∈ List.range 64, zong (zong v) = v := by decide

/-- 綜 preserves the number of yang yao — it permutes the layers of the cube
    within themselves. -/
theorem zong_preserves_yang : ∀ v ∈ List.range 64,
    yangCount (zong v) = yangCount v := by decide

/-- **The eight self-reversing hexagrams**, listed explicitly. -/
theorem zong_fixed_iff : ∀ v ∈ List.range 64,
    (zong v = v ↔
      v = 0 ∨ v = 12 ∨ v = 18 ∨ v = 30 ∨ v = 33 ∨ v = 45 ∨ v = 51 ∨ v = 63) := by
  decide

theorem zong_fixed_count :
    ((List.range 64).filter (fun v => zong v == v)).length = 8 := by decide

/-! ## 三十六宮 -/

/-- Fifty-six hexagrams are not self-reversing, so they form twenty-eight 綜
    pairs; with the eight self-reversing ones that is thirty-six.  The count is
    a consequence of the fixed-point structure of an involution. -/
theorem thirtysix_palaces :
    ((List.range 64).filter (fun v => zong v == v)).length = 8 ∧
    (64 - 8) / 2 = 28 ∧
    (64 - 8) / 2 + 8 = 36 := by
  decide

/-! ## Layers -/

/-- The hexagrams sort by yang count into layers of sizes `1, 6, 15, 20, 15, 6,
    1` — the binomial coefficients `C(6,k)`, and also the eigenvalue
    multiplicities of the adjacency operator of `Q₆`. -/
theorem layer_sizes :
    ((List.range 64).filter (fun v => yangCount v == 0)).length = 1 ∧
    ((List.range 64).filter (fun v => yangCount v == 1)).length = 6 ∧
    ((List.range 64).filter (fun v => yangCount v == 2)).length = 15 ∧
    ((List.range 64).filter (fun v => yangCount v == 3)).length = 20 ∧
    ((List.range 64).filter (fun v => yangCount v == 4)).length = 15 ∧
    ((List.range 64).filter (fun v => yangCount v == 5)).length = 6 ∧
    ((List.range 64).filter (fun v => yangCount v == 6)).length = 1 := by
  decide

/-! ## Edges of the cube -/

/-- Two hexagrams are joined in the picture when exactly one yao differs; the
    six neighbours of a hexagram are its six single-yao changes. -/
def adjacent (v w : Nat) : Bool :=
  (v ^^^ w == 1) || (v ^^^ w == 2) || (v ^^^ w == 4) ||
  (v ^^^ w == 8) || (v ^^^ w == 16) || (v ^^^ w == 32)

-- 4096 nested bounded quantifiers; `degree_six` below has only 64 at the outer
-- level and fits within the default recursion depth, this one does not.
set_option maxRecDepth 20000 in
theorem adjacent_symm : ∀ v ∈ List.range 64, ∀ w ∈ List.range 64,
    adjacent v w = adjacent w v := by decide

theorem degree_six : ∀ v ∈ List.range 64,
    ((List.range 64).filter (fun w => adjacent v w)).length = 6 := by decide

/-! ## Axiom audit -/

#print axioms hex_split
#print axioms cuo_involutive
#print axioms cuo_componentwise
#print axioms zong_involutive
#print axioms zong_fixed_iff
#print axioms thirtysix_palaces
#print axioms layer_sizes
#print axioms degree_six

end CubeToSU3.Hexagram64
