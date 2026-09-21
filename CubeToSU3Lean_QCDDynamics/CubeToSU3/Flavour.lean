import CubeToSU3.Cube

/-!
# From `1 + 2` to flavour physics

This module records the sharpest link found so far between the group-algebra
core and a measured quantity. It is still a no-go — it closes the option "both
quark sectors fully aligned" — but unlike everything in `Rejected.lean` it does
not kill a candidate model. It points outward: closing that escape forces the
model to hand over an observable.

## The chain

    Z/3 group algebra: integral ker/image/intersection facts  [theorem, Core.lean]
              ↓  scalar extension gives ker D ⊕ im D = 1 ⊕ 2 [not formalised here]
              ↓  family dictionary: the 3-space is generation space   [input]
              ↓  the 1 and the 2 carry different SU(3)_L reps         [input]
    Z' coupling matrix: G = g₂ I + Δg · P₁                            [group theory]
              ↓  measured CKM is not block diagonal                   [data]
    at least one quark sector has tree-level Z' FCNC                  [conclusion]

`P₁` is the rank-one projector onto `ker D`, the "special generation" direction.

## Theorem A (alignment forces a block CKM)

Let `P₁ = |n⟩⟨n|`, `H_u = M_u M_u†`, `H_d = M_d M_d†`. Suppose both sectors are
aligned with the special direction:

    [P₁, H_u] = 0   and   [P₁, H_d] = 0.

Then `|n⟩` is an eigenvector of both `H_u` and `H_d`, so (in the non-degenerate
case) `|n⟩` is a column of `U_L` and a column of `D_L`. Say `U_L e_k = |n⟩` and
`D_L e_l = |n⟩`. Then

    V e_l = U_L† D_L e_l = U_L† |n⟩ = e_k,

so column `l` of `V` is `e_k`; unitarity then forces row `k` to be `e_l`, and
`V` is block diagonal with respect to the `1 ⊕ 2` split.

The contrapositive is the useful direction:

    V not block diagonal  ⟹  [P₁, H_u] ≠ 0  or  [P₁, H_d] ≠ 0.

**This half is not formalised here, and the gap is larger than an ordered
field.** A faithful statement needs `ℂ`, conjugate transpose, unitarity,
Hermitian mass-squared matrices, non-degenerate eigenvalues, and a spectral
theorem — none of which exist in plain Lean (which has no `Rat` multiplication
either). The sensible Phase 2 split is:

* **A1, pure matrix lemma.** Given `U_L e_k = n` and `D_L e_l = n`, show
  `V e_l = e_k`, then use unitarity to zero the rest of row `k` and column `l`.
* **A2, spectral bridge.** Given non-degenerate masses, show
  `[P₁, H_q] = 0 ⟹ n` is an eigenvector of `H_q`, hence a column of `U_L`
  up to phase.

Nothing below depends on A1 or A2. **What this module machine-checks is Theorem
B alone**: a statement about nine hard-coded integers. `Cube` is imported for
context, not used in any proof here.

## Theorem B (the premise fails, decisively)

What *is* formalised is the empirical half: the measured CKM matrix is not
block diagonal, under any labelling of which generation is the special one.

Entries are `|V_ij|` scaled by `10^5` so everything stays in `Int`. For each
candidate pair `(k, l)` — meaning "generation `k` decouples, matching column
`l`" — the block defect is the sum of squared off-entries in row `k` and column
`l`. Block structure requires this to vanish; the theorem below shows every one
of the nine possibilities is far from vanishing.

## What this does and does not establish

It does **not** predict a `Z'` mass. The residual freedom is real: with
`ξ_d = V† ξ_u`, the FCNC can be moved between the up and down sectors, and
published bounds range over orders of magnitude depending on that choice.

It does establish that the FCNC cannot be moved away *entirely* — the option
"no tree-level flavour violation anywhere" is closed by the CKM data. That is a
genuine, if modest, consequence of the `1 + 2` structure.
-/

namespace CubeToSU3.Flavour

/-- `|V_ij|` scaled by `10^5`. These are central values from a global CKM fit
that **imposes three-generation unitarity**, so `ckm_rows_normalised` below is a
transcription check, not independent experimental evidence for unitarity. Only
magnitudes are needed: block structure is a statement about which entries
vanish. The interval version further down is the one that carries weight. -/
def ckm : Fin 3 → Fin 3 → Int
  | 0, 0 =>  97435 | 0, 1 =>  22500 | 0, 2 =>    369
  | 1, 0 =>  22486 | 1, 1 =>  97349 | 1, 2 =>   4182
  | 2, 0 =>    857 | 2, 1 =>   4110 | 2, 2 =>  99912

/-- Transcription check only. Each row has squared norm `10^10` to within
rounding — which it must, since the source fit imposed unitarity. This catches
typos; it is not evidence. -/
def rowNormSq (k : Fin 3) : Int :=
  ckm k 0 * ckm k 0 + ckm k 1 * ckm k 1 + ckm k 2 * ckm k 2

theorem ckm_rows_normalised : ∀ k : Fin 3,
    10000000000 - 2000000 ≤ rowNormSq k ∧ rowNormSq k ≤ 10000000000 + 2000000 := by
  decide

/-- The block defect for the labelling "generation `k` decouples, matching
column `l`": the sum of squared entries that block structure requires to be
zero, namely the rest of row `k` and the rest of column `l`. -/
def blockDefect (k l : Fin 3) : Int :=
  (List.finRange 3).foldl
      (fun acc j => acc + (if j = l then 0 else ckm k j * ckm k j)) 0
  + (List.finRange 3).foldl
      (fun acc i => acc + (if i = k then 0 else ckm i l * ckm i l)) 0

/-- **Theorem B.** No labelling makes the CKM matrix block diagonal. Every one
of the nine candidate pairs has a block defect above `10^7`, i.e. above
`0.001` in units where the matrix is unitary. -/
theorem ckm_not_block_diagonal : ∀ k l : Fin 3, blockDefect k l ≥ 10000000 := by
  decide

/-- The best case — third generation matched to third column — still misses by
a wide margin: `35251834 / 10^10 = 0.003525`, so the defect is `0.0594`.

Deliberately *not* quoted as a significance in sigma. The defect is a quadrature
sum over four matrix elements, so dividing it by the uncertainty on any single
element (`V_cb`) is not a legitimate statistical statement. The interval theorem
below is the honest way to make the claim robust. -/
theorem best_case_still_fails : blockDefect 2 2 = 35251834 := by decide

/-- And it really is the best case. The next closest labellings (the other two
diagonal ones) are worse by a factor of about 29, i.e. 1.5 orders of magnitude;
the six off-diagonal labellings by a factor of about 570. -/
theorem third_generation_is_the_closest : ∀ k l : Fin 3,
    blockDefect 2 2 ≤ blockDefect k l := by decide

/-! ### The interval version

Central values alone only show that *one particular table* is not block
diagonal. What is wanted is that the whole experimentally allowed region is.
Below, each magnitude is replaced by a deliberately generous lower bound (well
outside the quoted uncertainties), and the defect is recomputed. Since the
defect is a sum of squares of magnitudes, taking every entry at its minimum
gives the minimum possible defect for that labelling.
-/

/-- Generous lower bounds on `|V_ij| × 10^5`.

Chosen well below the quoted uncertainties, so the conclusion is **insensitive
to variation within these declared bounds**. Note the weaker phrasing: how the
bounds are obtained from experimental intervals still involves error modelling.
What Lean proves is conditional on this table; that the true CKM lies above it
is an external experimental input, on the same footing as any other entry in
`PhysicsInputs`.

TODO for a publication version — attach to each entry:
* the PDG edition and table number;
* whether the value comes from direct measurement or a unitarity-constrained
  global fit (the central-value table above is the latter);
* the confidence level at which the lower bound is taken;
* how the bound was derived from the quoted interval. -/
def ckmMin : Fin 3 → Fin 3 → Int
  | 0, 0 =>  97300 | 0, 1 =>  22000 | 0, 2 =>    300
  | 1, 0 =>  21500 | 1, 1 =>  97200 | 1, 2 =>   3500
  | 2, 0 =>    700 | 2, 1 =>   3400 | 2, 2 =>  99800

def minBlockDefect (k l : Fin 3) : Int :=
  (List.finRange 3).foldl
      (fun acc j => acc + (if j = l then 0 else ckmMin k j * ckmMin k j)) 0
  + (List.finRange 3).foldl
      (fun acc i => acc + (if i = k then 0 else ckmMin i l * ckmMin i l)) 0

/-- The lower-bound table itself is far from block diagonal: the minimum over
all nine labellings is `24390000`, a defect of `0.0494`. Named for what it is —
a statement about one table. The universally quantified version is below. -/
theorem ckm_lower_bound_table_nonblock :
    (∀ k l : Fin 3, minBlockDefect k l ≥ 20000000) ∧
    minBlockDefect 2 2 = 24390000 := by
  constructor <;> decide

/-! ### From one table to every admissible matrix

The theorem above still only computes a fixed table. To cover the whole allowed
region one needs a *variable* matrix, the predicate that it dominates the lower
bounds, and monotonicity of the defect. Working in `Nat` avoids having to prove
non-negativity before using monotonicity of squaring.
-/

/-- The lower bounds again, as naturals. -/
def ckmMinN : Fin 3 → Fin 3 → Nat
  | 0, 0 =>  97300 | 0, 1 =>  22000 | 0, 2 =>    300
  | 1, 0 =>  21500 | 1, 1 =>  97200 | 1, 2 =>   3500
  | 2, 0 =>    700 | 2, 1 =>   3400 | 2, 2 =>  99800

/-- The block defect of an arbitrary matrix of magnitudes, written as an
explicit sum so that monotonicity is term by term. -/
def blockDefectOf (V : Fin 3 → Fin 3 → Nat) (k l : Fin 3) : Nat :=
  (if (0 : Fin 3) = l then 0 else V k 0 * V k 0)
  + (if (1 : Fin 3) = l then 0 else V k 1 * V k 1)
  + (if (2 : Fin 3) = l then 0 else V k 2 * V k 2)
  + (if (0 : Fin 3) = k then 0 else V 0 l * V 0 l)
  + (if (1 : Fin 3) = k then 0 else V 1 l * V 1 l)
  + (if (2 : Fin 3) = k then 0 else V 2 l * V 2 l)

/-- `V` is admissible: every magnitude is at least the corresponding lower
bound. This is the predicate the previous version was missing. -/
def DominatesMin (V : Fin 3 → Fin 3 → Nat) : Prop := ∀ i j, ckmMinN i j ≤ V i j

private theorem term_mono (c : Prop) [Decidable c] {a b : Nat} (h : a ≤ b) :
    (if c then 0 else a * a) ≤ (if c then 0 else b * b) := by
  split
  · exact Nat.le_refl 0
  · exact Nat.mul_le_mul h h

/-- **Monotonicity.** Raising any magnitude cannot lower the defect. -/
theorem blockDefect_mono (V : Fin 3 → Fin 3 → Nat) (h : DominatesMin V)
    (k l : Fin 3) : blockDefectOf ckmMinN k l ≤ blockDefectOf V k l := by
  unfold blockDefectOf
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (term_mono _ (h k 0)) (term_mono _ (h k 1)))
    (term_mono _ (h k 2))) (term_mono _ (h 0 l))) (term_mono _ (h 1 l)))
    (term_mono _ (h 2 l))

theorem lower_bound_defects : ∀ k l : Fin 3,
    blockDefectOf ckmMinN k l ≥ 20000000 := by decide

/-- **The statement that was claimed before it was proved.** Every matrix of
magnitudes lying at or above the experimental lower bounds has a block defect
above `2 × 10^7` for every labelling. So the conclusion covers the whole
admissible region, not one table of numbers. -/
theorem every_admissible_matrix_is_nonblock (V : Fin 3 → Fin 3 → Nat)
    (h : DominatesMin V) : ∀ k l : Fin 3, blockDefectOf V k l ≥ 20000000 :=
  fun k l => Nat.le_trans (lower_bound_defects k l) (blockDefect_mono V h k l)

/-- **What is actually machine-checked here**, named to match its content.

This is a statement about a table of integers and nothing else. It does not
mention `P₁`, `H_u`, `H_d`, `U_L`, `D_L`, alignment, or the cube. The physical
conclusion — that at least one quark sector carries tree-level `Z'` FCNC —
follows only after Theorems A1 and A2 (not formalised) and the family
dictionary (an input, see `PhysicsInputs`).

The name `alignment_cannot_be_universal` is reserved for the day the full chain
is machine-checked. -/
theorem ckm_dataset_decisively_nonblock :
    (∀ k l : Fin 3, blockDefect k l ≥ 10000000) ∧
    blockDefect 2 2 = 35251834 ∧
    (∀ k l : Fin 3, minBlockDefect k l ≥ 20000000) := by
  exact ⟨ckm_not_block_diagonal, best_case_still_fails,
         ckm_lower_bound_table_nonblock.1⟩

end CubeToSU3.Flavour
