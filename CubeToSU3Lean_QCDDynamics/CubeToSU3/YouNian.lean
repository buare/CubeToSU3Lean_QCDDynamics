import CubeToSU3.Cube
import CubeToSU3.CrossProduct

/-!
# 遊年: the one place where the group `(Z₂)³` is load-bearing

Elsewhere in this project the eight cube vertices are used only as a source of
six vectors, and `D` is `R`-linear, so it does not respect the group law on
`(Z₂)³` at all (`D_not_group_hom` below). The group has been decorative.

The 遊年 tables of 八宅 feng shui are the exception. Both systems recorded in
中華象數大成 ch. 8 -- 大遊年變卦法 for 陽宅 and 壺中鬼卦 for 陰宅 -- are
functions of the XOR of the two trigrams, and of nothing else. Their eight-by-
eight tables are the Cayley table of `(Z₂)³` with star names written in the
cells. Every one of the 64 entries of each table is checked below against the
rule, by kernel reduction.

Encoding: a trigram is three yao read 上中下 as bits, yang = 1. So
坤 = 0, 艮 = 1, 坎 = 2, 巽 = 3, 震 = 4, 離 = 5, 兌 = 6, 乾 = 7. This is the same
`Fin 8` that indexes the cube vertices in `Cube.lean`, and one yao changing is
one cube edge.

Nothing here is a physical claim. It is a structural audit of a traditional
table, kept in the project because it settles a question the rest of the files
raise: whether the cube's group structure ever does work. It does, here, and
only here.
-/

namespace CubeToSU3.YouNian

/-! ## The tables, transcribed -/

/-- 大遊年變卦法 (陽宅). `dyTable p q` is the star number of trigram `q` seen
from palace `p`. Transcribed cell by cell from the source. -/
def dyTable : Fin 8 → Fin 8 → Nat
  | 0, 0 => 0   -- 坤宮 坤
  | 0, 1 => 1   -- 坤宮 艮
  | 0, 2 => 7   -- 坤宮 坎
  | 0, 3 => 2   -- 坤宮 巽
  | 0, 4 => 5   -- 坤宮 震
  | 0, 5 => 4   -- 坤宮 離
  | 0, 6 => 6   -- 坤宮 兌
  | 0, 7 => 3   -- 坤宮 乾
  | 1, 0 => 1   -- 艮宮 坤
  | 1, 1 => 0   -- 艮宮 艮
  | 1, 2 => 2   -- 艮宮 坎
  | 1, 3 => 7   -- 艮宮 巽
  | 1, 4 => 4   -- 艮宮 震
  | 1, 5 => 5   -- 艮宮 離
  | 1, 6 => 3   -- 艮宮 兌
  | 1, 7 => 6   -- 艮宮 乾
  | 2, 0 => 7   -- 坎宮 坤
  | 2, 1 => 2   -- 坎宮 艮
  | 2, 2 => 0   -- 坎宮 坎
  | 2, 3 => 1   -- 坎宮 巽
  | 2, 4 => 6   -- 坎宮 震
  | 2, 5 => 3   -- 坎宮 離
  | 2, 6 => 5   -- 坎宮 兌
  | 2, 7 => 4   -- 坎宮 乾
  | 3, 0 => 2   -- 巽宮 坤
  | 3, 1 => 7   -- 巽宮 艮
  | 3, 2 => 1   -- 巽宮 坎
  | 3, 3 => 0   -- 巽宮 巽
  | 3, 4 => 3   -- 巽宮 震
  | 3, 5 => 6   -- 巽宮 離
  | 3, 6 => 4   -- 巽宮 兌
  | 3, 7 => 5   -- 巽宮 乾
  | 4, 0 => 5   -- 震宮 坤
  | 4, 1 => 4   -- 震宮 艮
  | 4, 2 => 6   -- 震宮 坎
  | 4, 3 => 3   -- 震宮 巽
  | 4, 4 => 0   -- 震宮 震
  | 4, 5 => 1   -- 震宮 離
  | 4, 6 => 7   -- 震宮 兌
  | 4, 7 => 2   -- 震宮 乾
  | 5, 0 => 4   -- 離宮 坤
  | 5, 1 => 5   -- 離宮 艮
  | 5, 2 => 3   -- 離宮 坎
  | 5, 3 => 6   -- 離宮 巽
  | 5, 4 => 1   -- 離宮 震
  | 5, 5 => 0   -- 離宮 離
  | 5, 6 => 2   -- 離宮 兌
  | 5, 7 => 7   -- 離宮 乾
  | 6, 0 => 6   -- 兌宮 坤
  | 6, 1 => 3   -- 兌宮 艮
  | 6, 2 => 5   -- 兌宮 坎
  | 6, 3 => 4   -- 兌宮 巽
  | 6, 4 => 7   -- 兌宮 震
  | 6, 5 => 2   -- 兌宮 離
  | 6, 6 => 0   -- 兌宮 兌
  | 6, 7 => 1   -- 兌宮 乾
  | 7, 0 => 3   -- 乾宮 坤
  | 7, 1 => 6   -- 乾宮 艮
  | 7, 2 => 4   -- 乾宮 坎
  | 7, 3 => 5   -- 乾宮 巽
  | 7, 4 => 2   -- 乾宮 震
  | 7, 5 => 7   -- 乾宮 離
  | 7, 6 => 1   -- 乾宮 兌
  | 7, 7 => 0   -- 乾宮 乾
  | _, _ => 99

/-- 壺中鬼卦 (陰宅), likewise. -/
def hzTable : Fin 8 → Fin 8 → Nat
  | 0, 0 => 0   -- 坤宮 坤
  | 0, 1 => 5   -- 坤宮 艮
  | 0, 2 => 7   -- 坤宮 坎
  | 0, 3 => 6   -- 坤宮 巽
  | 0, 4 => 1   -- 坤宮 震
  | 0, 5 => 4   -- 坤宮 離
  | 0, 6 => 2   -- 坤宮 兌
  | 0, 7 => 3   -- 坤宮 乾
  | 1, 0 => 5   -- 艮宮 坤
  | 1, 1 => 0   -- 艮宮 艮
  | 1, 2 => 6   -- 艮宮 坎
  | 1, 3 => 7   -- 艮宮 巽
  | 1, 4 => 4   -- 艮宮 震
  | 1, 5 => 1   -- 艮宮 離
  | 1, 6 => 3   -- 艮宮 兌
  | 1, 7 => 2   -- 艮宮 乾
  | 2, 0 => 7   -- 坎宮 坤
  | 2, 1 => 6   -- 坎宮 艮
  | 2, 2 => 0   -- 坎宮 坎
  | 2, 3 => 5   -- 坎宮 巽
  | 2, 4 => 2   -- 坎宮 震
  | 2, 5 => 3   -- 坎宮 離
  | 2, 6 => 1   -- 坎宮 兌
  | 2, 7 => 4   -- 坎宮 乾
  | 3, 0 => 6   -- 巽宮 坤
  | 3, 1 => 7   -- 巽宮 艮
  | 3, 2 => 5   -- 巽宮 坎
  | 3, 3 => 0   -- 巽宮 巽
  | 3, 4 => 3   -- 巽宮 震
  | 3, 5 => 2   -- 巽宮 離
  | 3, 6 => 4   -- 巽宮 兌
  | 3, 7 => 1   -- 巽宮 乾
  | 4, 0 => 1   -- 震宮 坤
  | 4, 1 => 4   -- 震宮 艮
  | 4, 2 => 2   -- 震宮 坎
  | 4, 3 => 3   -- 震宮 巽
  | 4, 4 => 0   -- 震宮 震
  | 4, 5 => 5   -- 震宮 離
  | 4, 6 => 7   -- 震宮 兌
  | 4, 7 => 6   -- 震宮 乾
  | 5, 0 => 4   -- 離宮 坤
  | 5, 1 => 1   -- 離宮 艮
  | 5, 2 => 3   -- 離宮 坎
  | 5, 3 => 2   -- 離宮 巽
  | 5, 4 => 5   -- 離宮 震
  | 5, 5 => 0   -- 離宮 離
  | 5, 6 => 6   -- 離宮 兌
  | 5, 7 => 7   -- 離宮 乾
  | 6, 0 => 2   -- 兌宮 坤
  | 6, 1 => 3   -- 兌宮 艮
  | 6, 2 => 1   -- 兌宮 坎
  | 6, 3 => 4   -- 兌宮 巽
  | 6, 4 => 7   -- 兌宮 震
  | 6, 5 => 6   -- 兌宮 離
  | 6, 6 => 0   -- 兌宮 兌
  | 6, 7 => 5   -- 兌宮 乾
  | 7, 0 => 3   -- 乾宮 坤
  | 7, 1 => 2   -- 乾宮 艮
  | 7, 2 => 4   -- 乾宮 坎
  | 7, 3 => 1   -- 乾宮 巽
  | 7, 4 => 6   -- 乾宮 震
  | 7, 5 => 7   -- 乾宮 離
  | 7, 6 => 5   -- 乾宮 兌
  | 7, 7 => 0   -- 乾宮 乾
  | _, _ => 99

/-! ## The rule -/

/-- 大遊年: star as a function of the XOR alone.
`0 伏吟, 1 生氣, 2 五鬼, 3 延年, 4 六煞, 5 禍害, 6 天乙, 7 絕命`. -/
def dyRule : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 7 | 3 => 2
  | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 3
  | _ => 99

/-- 壺中鬼: same shape, different labelling.
`0 伏位, 1 五鬼, 2 絕命, 3 天醫, 4 生氣, 5 遊魂, 6 絕體, 7 福德`. -/
def hzRule : Nat → Nat
  | 0 => 0 | 1 => 5 | 2 => 7 | 3 => 6
  | 4 => 1 | 5 => 4 | 6 => 2 | 7 => 3
  | _ => 99

/-- **All 64 cells of the 陽宅 table are the XOR rule.** -/
theorem dy_is_xor : ∀ p q : Fin 8, dyTable p q = dyRule (p.val ^^^ q.val) := by
  decide

/-- **All 64 cells of the 陰宅 table are the XOR rule.** -/
theorem hz_is_xor : ∀ p q : Fin 8, hzTable p q = hzRule (p.val ^^^ q.val) := by
  decide

/-! ## The two systems differ by one reflection

`大遊年` starts the count from the 上爻; `壺中鬼` starts from the 下爻. In the
bit encoding that is exactly reversing the three bits, an odd permutation with
`det = -1`. So 陽宅 and 陰宅 are related by an orientation reversal, the same
sign that `CrossProduct.refl_reverses_cross` tracks on the geometric side.

One bit of information, so this is a structural match and not evidence of
anything further. It is recorded because it is exact.
-/

/-- Reversing 上爻 and 下爻. -/
def revYao : Nat → Nat
  | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 6
  | 4 => 1 | 5 => 5 | 6 => 3 | 7 => 7
  | _ => 99

theorem hz_is_dy_reflected : ∀ x : Fin 8, hzRule x.val = dyRule (revYao x.val) := by
  decide

theorem revYao_involutive : ∀ x : Fin 8, revYao (revYao x.val) = x.val := by
  decide

/-! ## 吉凶 is a subgroup and its coset

The four 吉星 of 大遊年 are 伏吟, 生氣, 天乙, 延年, at XOR values
`000, 001, 110, 111`. That set is closed under XOR: it is an index-two subgroup
of `(Z₂)³`, and the four 凶星 are its nontrivial coset.

An index-two subgroup is the kernel of a character, so 吉凶 is decided by one
linear functional. Reading it off: `λ(x) = 上爻 ⊕ 中爻`, and the 下爻 does not
enter at all.

This is a statement about the table, not a traditional formulation.
-/

/-- 吉 for 大遊年, by star number: 伏吟 0, 生氣 1, 延年 3, 天乙 6. -/
def dyAuspicious (star : Nat) : Bool :=
  star = 0 || star = 1 || star = 3 || star = 6

/-- The XOR values carrying an auspicious star. -/
def auspiciousXor (x : Nat) : Bool := dyAuspicious (dyRule x)

/-- **Closed under the group law**: an index-two subgroup of `(Z₂)³`. -/
theorem auspicious_subgroup : ∀ a b : Fin 8,
    auspiciousXor a.val = true → auspiciousXor b.val = true →
      auspiciousXor (a.val ^^^ b.val) = true := by
  decide

/-- The inauspicious set is the coset: two 凶 compose to a 吉. -/
theorem inauspicious_coset : ∀ a b : Fin 8,
    auspiciousXor a.val = false → auspiciousXor b.val = false →
      auspiciousXor (a.val ^^^ b.val) = true := by
  decide

/-- The character. Bit 2 is 上爻, bit 1 is 中爻, bit 0 is 下爻. -/
def lam (x : Nat) : Nat := ((x / 4) % 2 + (x / 2) % 2) % 2

/-- **吉 iff 上爻 and 中爻 change with the same parity.** The 下爻 is irrelevant
to 吉凶. -/
theorem auspicious_iff_character : ∀ x : Fin 8,
    auspiciousXor x.val = (lam x.val == 0) := by
  decide

/-! ## The 翻卦 path is a Gray code on the cube

Listing the trigrams in star order `0, 1, ..., 7` from a fixed palace gives
乾 兌 震 坤 坎 巽 艮 離, and every consecutive pair differs in exactly one yao.
So the zigzag drawn in the source diagrams is a Hamiltonian cycle on `Q₃`.

Note the contrast with an Eulerian one-stroke path, which does not exist here:
all eight vertices of `Q₃` have degree three, and Euler's condition allows at
most two odd vertices.
-/

/-- Trigrams in 大遊年 star order, starting from 乾宮. -/
def dyCycle : Fin 8 → Fin 8
  | 0 => 7 | 1 => 6 | 2 => 4 | 3 => 0
  | 4 => 2 | 5 => 3 | 6 => 1 | 7 => 5

/-- Each step of the star order flips exactly one yao, and the last step closes
the loop. Stated through `CubeToSU3.A`, the cube's own adjacency operator, so
this is a claim about the cube and not about a private copy of it. -/
theorem dyCycle_is_hamiltonian : ∀ i : Fin 8,
    A (dyCycle i) (dyCycle ⟨(i.val + 1) % 8, by omega⟩) = 1 := by
  decide

/-- The inverse listing: which star number carries a given trigram. -/
def dyCycleInv : Fin 8 → Fin 8
  | 0 => 3 | 1 => 6 | 2 => 4 | 3 => 5
  | 4 => 2 | 5 => 7 | 6 => 1 | 7 => 0

/-- The cycle really does visit all eight trigrams, once each. -/
theorem dyCycle_bijective :
    (∀ i : Fin 8, dyCycleInv (dyCycle i) = i) ∧
    (∀ q : Fin 8, dyCycle (dyCycleInv q) = q) := by
  constructor <;> decide

/-- No Eulerian one-stroke path exists on the cube: every vertex has odd
degree, and there are eight of them. -/
theorem all_degrees_odd : ∀ i : Fin 8,
    (A i 0 + A i 1 + A i 2 + A i 3 + A i 4 + A i 5 + A i 6 + A i 7) = 3 := by
  decide

/-! ## Why this does not connect to the algebra

`D` is `R`-linear on `R³`. The group law on `(Z₂)³` is addition mod two. These
are incompatible: `100 ⊕ 100 = 000` in the group, but `D` doubles instead of
cancelling. So the structure the 遊年 tables run on is destroyed the moment `D`
is applied, and the structure `D` runs on -- the cross product with the pole --
is invisible to the 遊年 tables, which never ask which vertices are near which.

Two real structures on the same eight points, each complete, and disjoint.
-/

/-- **The incompatibility.** `D` is not a homomorphism of `(Z₂)³`: in the group
`e₁ ⊕ e₁ = 0`, but `D e₁ + D e₁ ≠ D 0`. -/
theorem D_not_group_hom :
    Vec3.add (Mat3.mulVec D ⟨1, 0, 0⟩) (Mat3.mulVec D ⟨1, 0, 0⟩) ≠
      Mat3.mulVec D ⟨0, 0, 0⟩ := by
  decide

end CubeToSU3.YouNian
