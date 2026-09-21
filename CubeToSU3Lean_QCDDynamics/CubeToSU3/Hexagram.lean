import CubeToSU3.YouNianGray

/-!
# 六十四卦是 Q₆,遊年表是它到 Q₃ 的商

`YouNian.lean` proves that every cell of the eight-by-eight table depends only
on the XOR of the two trigrams, and `YouNianGray.lean` identifies the resulting
eight values as positions in a Gray circuit.  Both treat the collapse from 64
cells to 8 values as a computational fact, checked cell by cell.

It is a group-theoretic fact.

A hexagram is an upper trigram on a lower one, so the 64 hexagrams are
`Q₃ × Q₃`, which is the six-dimensional hypercube `Q₆ = (Z/2)⁶` — six yao, six
dimensions.  The eight-by-eight table is a function on `Q₆`.

The map taking a hexagram to the XOR of its two trigrams,

    δ : Q₆ → Q₃,   δ(p, q) = p ⊕ q

is a **group homomorphism**.  Its kernel is the diagonal `{(p,p)}`, of size
eight, so `64 / 8 = 8` and there are eight fibres of eight cells each.  Saying
that the star depends only on the XOR is exactly saying that the star function
**factors through δ**: it is constant on each fibre, hence descends to the
quotient `Q₆ / diagonal ≅ Q₃`.

That is what this file records.  Nothing new is computed — the numbers were
already in `YouNian` — but the reason the table collapses is now a statement
about a homomorphism rather than a coincidence of 64 entries.

The same holds for 壺中鬼, and 吉凶 descends further: it is constant on the
fibres of `δ` and then takes only two values, so the auspicious hexagrams form a
subgroup of index two in `Q₆`, of size 32.

**A limit worth recording.**  `Q₆` does not correspond to any root system the
way `Q₃` does.  Projecting `Q_n` along its main diagonal leaves `2ⁿ - 2`
vertices, while `A_{n-1}` has `n(n-1)` roots; these agree only for `n = 2` and
`n = 3` (`6 = 6`, but `62 ≠ 30`).  No other rank-six system fits either —
`D₆` has 60 roots, `B₆`, `C₆` and `E₆` have 72.  The cube's fit with `A₂` is a
genuine coincidence of small numbers, not an instance of a pattern, so this
file adds structure to the 遊年 side and nothing to the `su(3)` side.

Nothing here is a physical claim, and nothing here bears on whether the
traditional use of these tables is sound.
-/

namespace CubeToSU3.YouNian

open CubeToSU3

/-! ## Hexagrams

`Hexagram` is kept as a name for the reader, but every theorem below quantifies
over the two trigram components separately.  This branch has no Mathlib, and
Lean's core supplies a decidable bounded quantifier for `Fin n` but not for a
product of two, so `∀ a : Fin 8 × Fin 8` has no `Decidable` instance while
`∀ p q : Fin 8` does. -/

/-- A hexagram: an upper trigram and a lower one.  As a set this is
    `Q₃ × Q₃ ≅ Q₆`, the six-dimensional hypercube — six yao, six dimensions. -/
abbrev Hexagram := Fin 8 × Fin 8

/-- XOR on trigrams, the group operation of `Q₃`.  Applied componentwise it is
    the group operation of `Q₆`. -/
def xor8 (a b : Fin 8) : Fin 8 := ⟨(a.val ^^^ b.val) % 8, by omega⟩

/-- The difference map `δ(p, q) = p ⊕ q`, from `Q₆` to `Q₃`. -/
def delta (p q : Fin 8) : Fin 8 := xor8 p q

/-! ## It is a homomorphism -/

/-- **`δ` is a group homomorphism `Q₆ → Q₃`.**  The group operation upstairs is
    componentwise XOR, downstairs it is XOR. -/
theorem delta_hom : ∀ p q r s : Fin 8,
    delta (xor8 p r) (xor8 q s) = xor8 (delta p q) (delta r s) := by decide

/-- Its kernel is exactly the diagonal `{(p,p)}`, of size eight — whence
    `64 / 8 = 8`. -/
theorem delta_eq_zero_iff : ∀ p q : Fin 8, delta p q = 0 ↔ p = q := by decide

/-- Every fibre has eight elements: the hexagrams with a given XOR `x` are
    `(p, p ⊕ x)` as `p` ranges over the eight trigrams. -/
theorem delta_fibre : ∀ x p : Fin 8, delta p (xor8 p x) = x := by decide

/-! ## The table factors through it -/

/-- **The 遊年 star factors through `δ`.**  This is `dy_is_xor` restated: the
    star is constant on each fibre, so the eight-by-eight table is a function of
    eight values on the quotient `Q₆ / diagonal ≅ Q₃`. -/
theorem dyStar_factors : ∀ p q r s : Fin 8,
    delta p q = delta r s → dyTable p q = dyTable r s := by decide

/-- The same for 壺中鬼. -/
theorem hzStar_factors : ∀ p q r s : Fin 8,
    delta p q = delta r s → hzTable p q = hzTable r s := by decide

/-- 吉凶 descends too. -/
theorem auspicious_factors : ∀ p q r s : Fin 8,
    delta p q = delta r s →
      auspiciousXor (delta p q).val = auspiciousXor (delta r s).val := by decide

/-- The auspicious hexagrams are closed under the group operation, hence a
    subgroup of index two in `Q₆` — the preimage under `δ` of the auspicious
    subgroup of `Q₃`.  Thirty-two of the sixty-four. -/
theorem auspicious_hexagram_subgroup : ∀ p q r s : Fin 8,
    auspiciousXor (delta p q).val = true → auspiciousXor (delta r s).val = true →
      auspiciousXor (delta (xor8 p r) (xor8 q s)).val = true := by decide

/-! ## Axiom audit -/

#print axioms delta_hom
#print axioms delta_eq_zero_iff
#print axioms delta_fibre
#print axioms dyStar_factors
#print axioms hzStar_factors
#print axioms auspicious_hexagram_subgroup

end CubeToSU3.YouNian
