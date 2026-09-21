import CubeToSU3.SU3Surjectivity

/-!
# Removing `UnitarySpectralTheorem3`, stage 1: the phase shift

`SU3Surjectivity.lean` leaves `expSU3_surjective_of_unitarySpectralTheorem3`
depending on an unproved hypothesis, because Mathlib at the pinned revision
`a6276f4c` has no spectral theorem for normal or unitary matrices.  A grep of
that revision confirms what is and is not available:

* `Matrix.IsHermitian.spectral_theorem` — present.
* Schur triangulation — absent (`Mathlib/LinearAlgebra/Matrix/` has
  `SchurComplement.lean`, a different Schur).
* simultaneous diagonalisation of commuting Hermitians — absent.
* any `IsStarNormal` diagonalisation — absent.

So the hypothesis has to be built from the Hermitian theorem.  The route that
avoids simultaneous diagonalisation entirely is the **Cayley transform**.  For a
unitary `B` with `1 + B` invertible, `H = I * (1 - B) * (1 + B)⁻¹` is Hermitian
and `B` is a rational function of `H`; diagonalising `H` by the Hermitian
spectral theorem therefore diagonalises `B` in the *same* basis, with no
commuting-family argument needed.

The transform needs `1 + B` invertible, i.e. `-1` not an eigenvalue.  That is
arranged by rotating: replace `A` by `μ • A` for a suitable unit phase `μ`.
This file supplies exactly that step, and nothing else.

`exists_unit_phase_add_det_ne_zero` says: for any `3 × 3` complex matrix there
is a unit phase `μ` with `det (μ • 1 + A) ≠ 0`.  The proof is degree counting —
`λ ↦ det (λ • 1 + A)` is the characteristic polynomial of `-A`, monic of degree
three, so it has at most three roots, while `{1, i, -1, -i}` has four elements.

Remaining stages, in order:

2. `1 + B` invertible and `B` unitary ⟹ the Cayley transform is Hermitian.
3. `B` recovered as `(1 - i H) * (1 + i H)⁻¹`, hence diagonal in `H`'s
   eigenbasis, with unit-modulus diagonal entries.
4. Assemble into `UnitarySpectralTheorem3` and discharge the hypothesis.

Stage 2 is the one with real risk: it needs `star` of an inverse, and that
`(1 - B)` commutes with `(1 + B)⁻¹`.
-/

noncomputable section

open Matrix Complex Polynomial BigOperators

namespace CubeToSU3.Continuous

/-- The characteristic polynomial evaluated at a scalar is the determinant of
    the shifted matrix.  This is `Matrix.eval_det` combined with
    `Matrix.matPolyEquiv_charmatrix`. -/
theorem eval_charpoly_eq_det (M : M3C) (μ : ℂ) :
    M.charpoly.eval μ = (Matrix.scalar (Fin 3) μ - M).det := by
  rw [Matrix.charpoly, Matrix.eval_det, Matrix.matPolyEquiv_charmatrix]
  simp

/-- The four candidate phases. -/
def phases : Fin 4 → ℂ := ![1, Complex.I, -1, -Complex.I]

theorem phases_injective : Function.Injective phases := by
  intro a b hab
  have hre := congrArg Complex.re hab
  have him := congrArg Complex.im hab
  fin_cases a <;> fin_cases b <;> revert hre him <;> norm_num [phases]

theorem phases_norm (i : Fin 4) : ‖phases i‖ = 1 := by
  fin_cases i <;> simp [phases, Complex.norm_I]

/-- **Stage 1.**  Some unit phase makes `μ • 1 + A` nonsingular.

    `λ ↦ det (λ • 1 + A)` is the characteristic polynomial of `-A`: monic of
    degree three, hence nonzero, hence with at most three roots.  Four candidate
    phases cannot all be roots. -/
theorem exists_unit_phase_add_det_ne_zero (A : M3C) :
    ∃ μ : ℂ, ‖μ‖ = 1 ∧ (Matrix.scalar (Fin 3) μ + A).det ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ i : Fin 4,
      (-A).charpoly.eval (phases i) = 0 := by
    intro i
    rw [eval_charpoly_eq_det, sub_neg_eq_add]
    exact hcon (phases i) (phases_norm i)
  have hdeg : (-A).charpoly.natDegree = 3 := by
    rw [Matrix.charpoly_natDegree_eq_dim]
    simp
  have hlt : (-A).charpoly.natDegree < Fintype.card (Fin 4) := by
    rw [hdeg, Fintype.card_fin]
    norm_num
  have : (-A).charpoly = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (-A).charpoly phases_injective hzero hlt
  exact (Matrix.charpoly_monic (-A)).ne_zero this

/-! ## Axiom audit -/

#print axioms eval_charpoly_eq_det
#print axioms phases_injective
#print axioms exists_unit_phase_add_det_ne_zero

end CubeToSU3.Continuous
