import CubeToSU3.YouNianGray

/-!
# 天父卦、地母卦、壺中鬼卦:一條迴路,三種走法

`YouNian.lean` transcribed two tables from 中華象數大成 ch. 8.  This module adds
the third system of the same chapter, 天父卦 and 地母卦, transcribed from the
same source (走進伏羲, 中華象數大成, pp. 183-188, all eight palaces), and records
what the three have in common.

The result is sharper than for two tables alone.

* All three systems are XOR-only: 192 cells collapse to 3 × 8 values.
* All three star orders are cyclic Gray codes on `Q₃`.
* **天父卦 and 大遊年 are the same rule.**  Not similar — identical on all 64
  cells (`tianfu_eq_dayounian`).
* **地母卦 is 天父卦 walked backwards.**  `dimuOrder i = tianfuOrder (-i)`
  exactly, with no shift (`dimu_is_tianfu_reversed`).
* 壺中鬼卦 is the mirror: the same construction after swapping 上爻 and 下爻,
  which as an undirected cycle is a *different* Hamiltonian cycle of `Q₃`.

So the three received systems use only two of the six Hamiltonian cycles of the
cube, one of them in both directions.

The yao-flip sequences make the relationship visible:

    天父    上 中 下 中 上 中 下 中
    地母    中 下 中 上 中 下 中 上     (天父 read backwards)
    壺中鬼  下 中 上 中 下 中 上 中     (天父 with 上/下 exchanged)

Nothing here is a physical claim, and nothing here bears on whether the
traditional use of these tables is sound.  It is a structural audit of received
text, and every statement is an exact finite identity checked by kernel
reduction.
-/

namespace CubeToSU3.YouNian

/-! ## 天父卦 -/

/-- 天父卦 star order: `tianfuOrder i` is the XOR value carrying star `i`,
    counting 輔弼 as 0 and 貪狼 as 1. -/
def tianfuOrder : Fin 8 → Fin 8
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 7
  | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 2

/-- **天父卦 is 大遊年.**  The two received systems, with different star names,
    put the same star number on every one of the 64 cells. -/
theorem tianfu_eq_dayounian : ∀ i : Fin 8, tianfuOrder i = grayOrder i := by
  decide

theorem tianfuOrder_adjacent : ∀ i : Fin 8,
    A (tianfuOrder i) (tianfuOrder ⟨(i.val + 1) % 8, by omega⟩) = 1 := by decide

/-! ## 地母卦 -/

/-- 地母卦 star order, 輔弼 as 0 and 武曲 as 1. -/
def dimuOrder : Fin 8 → Fin 8
  | 0 => 0 | 1 => 2 | 2 => 6 | 3 => 4
  | 4 => 5 | 5 => 7 | 6 => 3 | 7 => 1

theorem dimuOrder_adjacent : ∀ i : Fin 8,
    A (dimuOrder i) (dimuOrder ⟨(i.val + 1) % 8, by omega⟩) = 1 := by decide

/-- **地母卦 is 天父卦 traversed backwards.**  Step `i` of 地母 lands where step
    `8 - i` of 天父 lands; the two systems share one closed circuit and differ
    only in direction. -/
theorem dimu_is_tianfu_reversed : ∀ i : Fin 8,
    dimuOrder i = tianfuOrder ⟨(8 - i.val) % 8, by omega⟩ := by decide

/-! ## The three circuits together -/

/-- 壺中鬼 is 天父 after exchanging 上爻 and 下爻.  `revYao` is that exchange, so
    this states that the third system is the mirror of the first. -/
theorem huzhong_is_tianfu_mirrored : ∀ i : Fin 8,
    (hzRule (revYao (tianfuOrder i).val)) = i.val := by decide

/-! ## 吉凶

For the 八宅 star names the four auspicious stars form an index-two subgroup in
both systems, but *not the same one*:

* 大遊年 / 天父 circuit: 吉 = `{0,1,6,7}`, the kernel of 中爻 ⊕ 下爻, so 上爻 is
  the yao that does not enter 吉凶 (`auspicious_upper_yao_irrelevant`).
* 壺中鬼 circuit: 吉 = `{0,2,5,7}`, the kernel of 上爻 ⊕ 下爻, so there the
  irrelevant yao is the 中爻.

`hz_auspicious_subgroup` records the second of these. -/

/-- 吉 for 壺中鬼, by star number: 伏位 0, 天醫 3, 生氣 4, 福德 7. -/
def hzAuspicious (star : Nat) : Bool :=
  star = 0 || star = 3 || star = 4 || star = 7

def hzAuspiciousXor (x : Nat) : Bool := hzAuspicious (hzRule x)

theorem hz_auspicious_subgroup : ∀ a b : Fin 8,
    hzAuspiciousXor a.val = true → hzAuspiciousXor b.val = true →
      hzAuspiciousXor (a.val ^^^ b.val) = true := by decide

/-- 壺中鬼's 吉凶 ignores the 中爻. -/
theorem hz_auspicious_middle_yao_irrelevant : ∀ x : Fin 8,
    hzAuspiciousXor x.val = hzAuspiciousXor (x.val ^^^ 2) := by decide

/-! ## Axiom audit -/

#print axioms tianfu_eq_dayounian
#print axioms tianfuOrder_adjacent
#print axioms dimuOrder_adjacent
#print axioms dimu_is_tianfu_reversed
#print axioms huzhong_is_tianfu_mirrored
#print axioms hz_auspicious_subgroup
#print axioms hz_auspicious_middle_yao_irrelevant

end CubeToSU3.YouNian
