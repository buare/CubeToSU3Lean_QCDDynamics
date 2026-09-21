import CubeToSU3.QianKunAxis

/-!
# 從幾何到反常自由:一條完整的鏈

This file is the formal counterpart of §9–§11 of the original notes.  It is
written as a single chain with a head, a body and a tail, and with the physics
inputs declared where they enter rather than folded silently into definitions.

```
  幾何內生          物理輸入            樸素解              檢驗
  ker D ⊕ im D  →  三個字典公理   →   X_Q 譜唯一   →   五項反常歸零
   = 1 + 2                              2:1 分解         (n_Q,n_L) 唯一
```

**頭 — 幾何內生, already machine-checked elsewhere.**  `Core.lean` proves
`kernel_D`, `image_D` and `kernel_meets_image_trivially`, i.e. that the cyclic
difference splits the three coordinate directions as `1 + 2`.
`QianKunAxis.lean` proves that the 乾-坤 diagonal is the kernel direction and
that the other six vertices form the `A₂` hexagon.  Nothing in this file
re-derives that; it starts where those leave off.

**軀幹 — 物理輸入.**  Three dictionary statements are needed to turn the `1 + 2`
splitting into a fermion assignment.  They are declared as `axiom` in the
section below so that `#print axioms` shows exactly which results lean on them.
They are *not* consequences of the cube, and the notes were right to flag them.

**尾 — 樸素解與檢驗.**  Everything after that is integer arithmetic and uses no
axioms at all.  `xQ_spectrum_unique` shows the `(-1/3, -1/3, 2/3)` spectrum is
forced; `family_split_unique` shows `2 + 1` is the only anomaly-free family
split; `anomalies_all_vanish` checks all six coefficients for the explicit
fifteen-field content.

Charges are carried as `3X` so that everything stays in `Int` and `decide`
can run in the kernel.  A cubic anomaly vanishes iff its `3X`-scaled version
does, so nothing is lost.

**What is still not proved.**  That the six hexagon vertices *are* the six roots
(a shape match, not a structure match — see `QianKunAxis`), that chirality can
arise at all (`Cube.lean`'s `cube_index_zero` says it cannot, so the `Γ□` rule
below is unavoidable rather than merely convenient), and anything numerical:
`sin²θ_W = 1/4` and `f/v = 6√6` are not touched here.

Nothing here is a claim that this model describes nature.
-/

namespace CubeToSU3.Anomaly

/-! ## 軀幹:物理輸入,顯式記帳

These three are the dictionary.  They are assumptions, not theorems. -/

/-- P1.  The three coordinate directions of the cube are read as the three
    fermion families.  Nothing in the cube says "family". -/
axiom family_dictionary : Prop

/-- P2.  The sign of `Γ□ = P₂ - P₁` selects `3_L` versus `3̄_L`.  This is where
    chirality is inserted; `cube_index_zero` proves it cannot be derived. -/
axiom chirality_dictionary : Prop

/-- P3.  The relative phase of the two coincident centres is kept as a
    `U(1)_X`.  The notes list this as candidate axiom A5. -/
axiom center_phase_dictionary : Prop

/-! ## 尾一:`X_Q` 的譜是被逼出來的

Write `X_Q = a P₁ + b P₂`.  Tracelessness over three families gives
`a + 2b = 0`; normalising the gap between the two eigenvalues to one gives
`a - b = 1`.  Carrying `3a` and `3b` keeps this in `Int`. -/

/-- With `A = 3a` and `B = 3b`, the two conditions force `A = 2`, `B = -1`,
    that is `a = 2/3` and `b = -1/3`.  The spectrum of `X_Q` is therefore
    `{-1/3, -1/3, 2/3}` — one eigenvalue from the diagonal, two from the root
    plane — and is not chosen family by family. -/
theorem xQ_spectrum_unique (A B : Int) (htrace : A + 2 * B = 0)
    (hgap : A - B = 3) : A = 2 ∧ B = -1 := by
  omega

/-! ## 尾二:只有 2 + 1 能消反常

With `n_Q` quark families in `3_L` and `n_L` lepton families in `3_L`, the cubic
`SU(3)_L` anomaly is `3(2n_Q - 3) + (2n_L - 3)`, the factor three being colour.
Clearing it and moving the constants gives `6 n_Q + 2 n_L = 12`. -/

theorem family_split_unique (nQ nL : Nat) (hQ : nQ ≤ 3) (hL : nL ≤ 3)
    (h : 6 * nQ + 2 * nL = 12) :
    (nQ = 2 ∧ nL = 0) ∨ (nQ = 1 ∧ nL = 3) := by
  omega

/-! ## 尾三:顯式場內容與六項反常 -/

/-- One left-handed Weyl field.  `nc`, `nl` are the cubic anomaly indices
    (`+1` for a triplet, `-1` for an antitriplet, `0` for a singlet); `dc`,
    `dl` are the dimensions; `x3` is three times the `U(1)_X` charge. -/
structure Weyl where
  nc : Int
  dc : Int
  nl : Int
  dl : Int
  x3 : Int
deriving DecidableEq

/-- `1` on a (anti)triplet, `0` on a singlet — the quadratic index up to the
    common factor one half, which drops out of a vanishing condition. -/
def tri (n : Int) : Int := if n = 0 then 0 else 1

/-- The fifteen left-handed Weyl fields of the minimal candidate.  Right-handed
    quarks appear as left-handed conjugates, hence colour antitriplets. -/
def content : List Weyl :=
  -- 前兩代:Q ~ (3, 3, X = -1/3),右手共軛 3X = -2, 1, 4
  [ ⟨ 1, 3,  1, 3, -1⟩,
    ⟨-1, 3,  0, 1, -2⟩, ⟨-1, 3, 0, 1,  1⟩, ⟨-1, 3, 0, 1, 4⟩,
    ⟨ 1, 3,  1, 3, -1⟩,
    ⟨-1, 3,  0, 1, -2⟩, ⟨-1, 3, 0, 1,  1⟩, ⟨-1, 3, 0, 1, 4⟩,
  -- 第三代:Q ~ (3, 3̄, X = 2/3),右手共軛 3X = 1, -2, -5
    ⟨ 1, 3, -1, 3,  2⟩,
    ⟨-1, 3,  0, 1,  1⟩, ⟨-1, 3, 0, 1, -2⟩, ⟨-1, 3, 0, 1, -5⟩,
  -- 三代輕子:L ~ (1, 3̄, X = 0)
    ⟨ 0, 1, -1, 3,  0⟩, ⟨0, 1, -1, 3, 0⟩, ⟨0, 1, -1, 3, 0⟩ ]

def anomL3   (W : List Weyl) : Int := (W.map fun f => f.dc * f.nl).sum
def anomC3   (W : List Weyl) : Int := (W.map fun f => f.dl * f.nc).sum
def anomL2X  (W : List Weyl) : Int := (W.map fun f => f.dc * tri f.nl * f.x3).sum
def anomC2X  (W : List Weyl) : Int := (W.map fun f => f.dl * tri f.nc * f.x3).sum
def anomGrav (W : List Weyl) : Int := (W.map fun f => f.dc * f.dl * f.x3).sum
def anomX3   (W : List Weyl) : Int :=
  (W.map fun f => f.dc * f.dl * f.x3 * f.x3 * f.x3).sum

theorem content_length : content.length = 15 := by decide

/-- **The ledger.**  All six local gauge and mixed gravitational anomalies of
    the candidate vanish. -/
theorem anomalies_all_vanish :
    anomL3 content = 0 ∧ anomC3 content = 0 ∧
    anomL2X content = 0 ∧ anomC2X content = 0 ∧
    anomGrav content = 0 ∧ anomX3 content = 0 := by
  decide

/-- The colour anomaly vanishes field by field within each family, which is the
    statement that `SU(3)_c` is vector-like: the cube contributes nothing
    chiral to colour. -/
theorem colour_vector_like :
    anomC3 (content.take 4) = 0 ∧
    anomC3 ((content.drop 4).take 4) = 0 ∧
    anomC3 ((content.drop 8).take 4) = 0 := by
  decide

/-- The cubic `U(1)_X` anomaly is `+6, +6, -12` family by family, in units of
    `1/27` from the `3X` scaling.  The cancellation is between families, not
    within one — this is the arithmetic form of "two generations plus one". -/
theorem xCubed_by_family :
    anomX3 (content.take 4) = 162 ∧
    anomX3 ((content.drop 4).take 4) = 162 ∧
    anomX3 ((content.drop 8).take 4) = -324 := by
  decide

/-! ## 記帳

`#print axioms` below is the point of the file: the three dictionary axioms are
declared, and none of the results uses them.  What the cube plus arithmetic buys
you is the *consistency* of the candidate, not its *derivation*. -/

#print axioms xQ_spectrum_unique
#print axioms family_split_unique
#print axioms anomalies_all_vanish
#print axioms colour_vector_like
#print axioms xCubed_by_family

end CubeToSU3.Anomaly
