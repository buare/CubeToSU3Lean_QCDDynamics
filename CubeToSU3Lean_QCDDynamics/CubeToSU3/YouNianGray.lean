import CubeToSU3.YouNian

/-!
# 遊年 is a Gray-code rank function

`YouNian.lean` proves that every cell of both eight-by-eight tables depends only
on the XOR of the two trigrams.  That collapses 64 cells to 8 values, but it
leaves the eight star names looking arbitrary.  They are not.

Order the eight XOR values as

    0, 1, 3, 7, 5, 4, 6, 2

Consecutive entries differ in exactly one bit, and the list closes back to the
start, so this is a cyclic Gray code — a Hamiltonian cycle on `Q₃`.  The content
of this file is that the star number of `q` seen from palace `p` is exactly the
**position of `p ⊕ q` in that cycle**:

    dyTable p q = grayRank (p ⊕ q)

So the whole system is one sentence: *walk the cube one yao at a time along a
fixed closed circuit, and the star is how many steps you have taken.*  The eight
star names are the eight positions, nothing more.

Three further exact facts are recorded.

* The 上爻 does not affect 吉凶 at all (`auspicious_upper_yao_irrelevant`), and
  the four auspicious XOR values `{0,1,6,7}` form two antipodal edges of the
  cube, the two edges running in the 上爻 direction at opposite corners.
  Note that `YouNian.lean`'s comment on `lam` names the bits the other way
  round; the trigram assignment `艮 = 1` fixes 上爻 as bit 0, so the character
  `lam = bit2 ⊕ bit1` is 下爻 ⊕ 中爻 and the yao it ignores is the 上爻.
* 壺中鬼 is the same construction read from the other end of the trigram, so it
  is the same Gray code after the bit-reversal automorphism.
* The circuit is **not** canonical.  `Q₃` has exactly six Hamiltonian cycles and
  `Aut(Q₃)`, of order 48, permutes them transitively; `phi_maps_to_standard`
  exhibits an explicit automorphism carrying the 遊年 circuit to the textbook
  reflected binary Gray code.  So no information is carried by *which* circuit
  the tradition chose.  What is non-trivial, and could have failed, is that the
  received star order is a Gray code at all.

The counts 6 and 48 were obtained by exhaustive search outside Lean and are
stated here as commentary, not as theorems.  Everything asserted below is an
exact finite identity checked by kernel reduction.

Nothing here is a physical claim.
-/

namespace CubeToSU3.YouNian

/-! ## The circuit and its rank function -/

/-- The 遊年 circuit: `grayOrder i` is the XOR value carrying star number `i`. -/
def grayOrder : Fin 8 → Fin 8
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 7
  | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 2

/-- Position of an XOR value in the circuit.  This is `dyRule` seen for what it
    is, so the two agree by construction and `dyRule_eq_grayRank` checks it. -/
def grayRank : Fin 8 → Fin 8
  | 0 => 0 | 1 => 1 | 2 => 7 | 3 => 2
  | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 3

theorem grayOrder_rank : ∀ i : Fin 8, grayRank (grayOrder i) = i := by decide

theorem grayRank_order : ∀ x : Fin 8, grayOrder (grayRank x) = x := by decide

/-- **The circuit is a Hamiltonian cycle**, stated through the cube's own
    adjacency operator: each step flips exactly one yao, and step eight closes
    the loop. -/
theorem grayOrder_adjacent : ∀ i : Fin 8,
    A (grayOrder i) (grayOrder ⟨(i.val + 1) % 8, by omega⟩) = 1 := by decide

/-- `dyRule` *is* the rank function. -/
theorem dyRule_eq_grayRank : ∀ x : Fin 8, dyRule x.val = (grayRank x).val := by
  decide

/-- **The table in one line.**  The star of `q` seen from palace `p` is the
    number of steps from the start of the circuit to `p ⊕ q`. -/
theorem dyTable_eq_grayRank : ∀ p q : Fin 8,
    dyTable p q = (grayRank ⟨(p.val ^^^ q.val) % 8, by omega⟩).val := by
  decide

/-! ## 吉凶 ignores the 下爻 -/

/-- Changing only the 上爻 never changes 吉凶. -/
theorem auspicious_upper_yao_irrelevant : ∀ x : Fin 8,
    auspiciousXor x.val = auspiciousXor (x.val ^^^ 1) := by decide

/-- The four auspicious XOR values are exactly `{0,1,6,7}`: two antipodal edges
    of the cube, both running in the 上爻 direction. -/
theorem auspicious_is_two_antipodal_edges : ∀ x : Fin 8,
    auspiciousXor x.val = (x.val == 0 || x.val == 1 || x.val == 6 || x.val == 7) := by
  decide

/-! ## The circuit is not canonical

`phi` swaps 上爻 with 中爻 and then flips the 上爻.  It is an automorphism of the
cube, and it carries the 遊年 circuit onto the textbook reflected binary Gray
code `0,1,3,2,6,7,5,4`, rotated by one step.

The swap and the flip do not commute, so `phi` is *not* an involution: it has
order four, acting as `(0 1 3 2)(4 5 7 6)`.  Only the equivalence of the two
circuits is needed below, so the order plays no role in the argument. -/

def phi : Fin 8 → Fin 8
  | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2
  | 4 => 5 | 5 => 7 | 6 => 4 | 7 => 6

/-- The standard reflected binary Gray code. -/
def stdGray : Fin 8 → Fin 8
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2
  | 4 => 6 | 5 => 7 | 6 => 5 | 7 => 4

theorem phi_is_automorphism : ∀ i j : Fin 8, A (phi i) (phi j) = A i j := by
  decide

/-- `phi` has order four, not two: as a permutation of the eight trigrams it is
    the pair of four-cycles `(0 1 3 2)(4 5 7 6)`.  The bit swap and the bit flip
    do not commute, so composing `phi` with itself flips the 中爻 instead of
    returning to the identity. -/
theorem phi_order_four : ∀ i : Fin 8, phi (phi (phi (phi i))) = i := by decide

/-- **The received circuit is the textbook one in disguise.** -/
theorem phi_maps_to_standard : ∀ i : Fin 8,
    phi (grayOrder i) = stdGray ⟨(i.val + 1) % 8, by omega⟩ := by decide

/-! ## Axiom audit -/

#print axioms grayOrder_rank
#print axioms grayOrder_adjacent
#print axioms dyRule_eq_grayRank
#print axioms dyTable_eq_grayRank
#print axioms auspicious_upper_yao_irrelevant
#print axioms auspicious_is_two_antipodal_edges
#print axioms phi_order_four
#print axioms phi_is_automorphism
#print axioms phi_maps_to_standard

end CubeToSU3.YouNian
