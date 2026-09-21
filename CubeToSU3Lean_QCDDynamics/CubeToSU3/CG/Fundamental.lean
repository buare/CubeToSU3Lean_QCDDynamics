import CubeToSU3.CG.Convention

/-!
# `3 ⊗ 3 = 6 ⊕ 3̄`

Unnormalised integer states:

* `sym m n = |mn⟩ + |nm⟩`.  Normalised six-plet states are `sym m n / √2`
  for `m ≠ n` and `sym m m / 2` on the diagonal.
* `anti k = Σ_ij ε_kij |ij⟩`.  Normalised anti-triplet state `|k̄⟩ = anti k / √2`.
  With `ε_uds = +1` this gives `|ū⟩ = (|ds⟩ - |sd⟩)/√2`,
  `|d̄⟩ = (|su⟩ - |us⟩)/√2`, `|s̄⟩ = (|ud⟩ - |du⟩)/√2`.

What is proved, all by kernel evaluation over `Fin 3`:

1. `anti k` transforms as `3̄ ⊗ det`; on traceless generators, exactly as `3̄`.
2. The `sym` states span an invariant subspace.
3. `sym` and `anti` are orthogonal, with integer norms `2(δδ + δδ)` and `2`.
4. Completeness: `2 |mn⟩ = sym m n + Σ_k ε_kmn · anti k`.
5. Weights: `anti k` sits at `-w_k`. On the cube: two distinct weight-one
   vertices add up to the opposite of the third.
-/

namespace CubeToSU3.CG

/-- Symmetric (six-plet) state, unnormalised. -/
def sym (m n : Idx) : Ten := fun i j => ket m n i j + ket n m i j

/-- Antisymmetric (anti-triplet) state, unnormalised: `√2 · |k̄⟩`. -/
def anti (k : Idx) : Ten := fun i j => eps k i j

/-! ## Explicit phase check -/

theorem anti_u : ∀ i j : Idx, anti u i j = ket d s i j - ket s d i j := by decide
theorem anti_d : ∀ i j : Idx, anti d i j = ket s u i j - ket u s i j := by decide
theorem anti_s : ∀ i j : Idx, anti s i j = ket u d i j - ket d u i j := by decide

/-! ## 1. The antisymmetric part is `3̄`

For every matrix unit, hence every `T ∈ gl(3)`:

  `(T⊗1 + 1⊗T) anti k = Σ_l (tr T · δ_kl - T_kl) · anti l`.

The `tr T` term is the determinant factor in `Λ²(3) ≅ 3̄ ⊗ det`; it vanishes on
`su(3)`, leaving the contragredient action `-Tᵀ`. -/
theorem anti_transforms :
    ∀ a b k i j : Idx,
      act33 (E a b) (anti k) i j
        = sum3 (fun l => (delta k l * trace (E a b) - E a b k l) * anti l i j) := by
  decide

/-- On the six off-diagonal generators (the six roots) the action is exactly `-Tᵀ`. -/
theorem anti_is_3bar_offdiag :
    ∀ a b k i j : Idx, a ≠ b →
      act33 (E a b) (anti k) i j = sum3 (fun l => (- E a b k l) * anti l i j) := by
  decide

/-- The two Cartan generators `H₁ = E₀₀ - E₁₁`, `H₂ = E₁₁ - E₂₂`. -/
def H1 : Mat := fun i j => E 0 0 i j - E 1 1 i j
def H2 : Mat := fun i j => E 1 1 i j - E 2 2 i j

theorem anti_is_3bar_H1 :
    ∀ k i j : Idx, act33 H1 (anti k) i j = sum3 (fun l => (- H1 k l) * anti l i j) := by
  decide

theorem anti_is_3bar_H2 :
    ∀ k i j : Idx, act33 H2 (anti k) i j = sum3 (fun l => (- H2 k l) * anti l i j) := by
  decide

/-! ## 2. The symmetric part is invariant

`(T⊗1 + 1⊗T) sym m n = Σ_p T_pm · sym p n + Σ_p T_pn · sym m p`. -/
theorem sym_closed :
    ∀ a b m n i j : Idx,
      act33 (E a b) (sym m n) i j
        = sum3 (fun p => E a b p m * sym p n i j)
          + sum3 (fun p => E a b p n * sym m p i j) := by
  decide

/-- Relabelling symmetry: only unordered pairs matter, giving six states. -/
theorem sym_comm : ∀ m n i j : Idx, sym m n i j = sym n m i j := by decide

/-- The symmetric states are symmetric tensors. -/
theorem sym_is_symmetric : ∀ m n i j : Idx, sym m n i j = sym m n j i := by decide

/-- The antisymmetric states are antisymmetric tensors. -/
theorem anti_is_antisymmetric : ∀ k i j : Idx, anti k i j = - anti k j i := by decide

/-! ## 3. Orthogonality and norms -/

theorem sym_perp_anti : ∀ m n k : Idx, dot (sym m n) (anti k) = 0 := by decide

theorem anti_gram : ∀ k l : Idx, dot (anti k) (anti l) = 2 * delta k l := by decide

/-- `⟨sym mn, sym pq⟩ = 2(δ_mp δ_nq + δ_mq δ_np)`. Distinct unordered pairs are
orthogonal; norms are `2` off the diagonal and `4` on it. -/
theorem sym_gram :
    ∀ m n p q : Idx,
      dot (sym m n) (sym p q)
        = 2 * (delta m p * delta n q + delta m q * delta n p) := by
  decide

/-! ## 4. Completeness

Every basis tensor splits into its six-plet and anti-triplet parts:

  `2 |mn⟩ = sym m n + Σ_k ε_kmn · anti k`.

With `3 × 3 = 9 = 6 + 3`, this is the full decomposition `3 ⊗ 3 = 6 ⊕ 3̄`. -/
theorem completeness :
    ∀ m n i j : Idx,
      2 * ket m n i j = sym m n i j + sum3 (fun k => eps k m n * anti k i j) := by
  decide

/-! ## 5. Weights -/

/-- The weight of `|ij⟩` is `w_i + w_j`. Every component of `anti k` has weight
`-w_k`: two distinct weight-one cube vertices add to the opposite of the third. -/
theorem anti_weight :
    ∀ k i j : Idx, eps k i j ≠ 0 → (w i).add (w j) = (w k).neg := by
  decide

/-- The diagonal six-plet states sit at twice a fundamental weight: the three
corners of the six-plet triangle. -/
theorem sym_corner_weight : ∀ i : Idx, (w i).add (w i) = ⟨2 * (w i).x, 2 * (w i).y, 2 * (w i).z⟩ := by
  decide

end CubeToSU3.CG
