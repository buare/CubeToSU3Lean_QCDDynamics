import CubeToSU3.SU3SpectralStage3

/-!
# Removing `UnitarySpectralTheorem3`, stage 4: transporting the diagonalisation

Stage 2 made `H = cayley B` Hermitian; stage 3 recovered `B = (1 + iH)(1 - iH)⁻¹`.
Mathlib diagonalises `H`, so what remains is to push that diagonalisation
through the rational expression.  That is what this file does, ending in

    unitary_diagonalizable_of_one_add_isUnit :
      Bᴴ * B = 1 → IsUnit (1 + B).det → ∃ U w, B = U * diagonal w * Uᴴ

The mechanism is a small toolkit: conjugation by a fixed unitary `U`,
`M ↦ U * M * Uᴴ`, preserves sums, products, scalar multiples and the identity,
and therefore also inverses.  `1 ± iH` are conjugates of `1 ± iD`, which are
diagonal, so the whole expression stays inside the conjugated copy.

The one analytic input is that `1 - i d` never vanishes for real `d`: its real
part is `1`.  This is exactly where the Cayley transform earns its keep — the
denominators cannot blow up, because the eigenvalues of a Hermitian matrix are
real and `-1` is not in the image of the transform.

Stage 5 will absorb the phase from stage 1, check that the diagonal entries have
modulus one, and discharge `UnitarySpectralTheorem3`.
-/

noncomputable section

open Matrix Complex

namespace CubeToSU3.Continuous

/-! ## Conjugation by a unitary is a ring homomorphism onto its image -/

/-- Conjugation by a unitary fixes the identity. -/
theorem conj_one {U : M3C} (hU : U * Uᴴ = 1) : U * 1 * Uᴴ = 1 := by
  rw [mul_one, hU]

theorem conj_mul {U : M3C} (hU' : Uᴴ * U = 1) (M N : M3C) :
    U * M * Uᴴ * (U * N * Uᴴ) = U * (M * N) * Uᴴ := by
  calc U * M * Uᴴ * (U * N * Uᴴ) = U * M * (Uᴴ * U) * N * Uᴴ := by noncomm_ring
    _ = U * M * 1 * N * Uᴴ := by rw [hU']
    _ = U * (M * N) * Uᴴ := by noncomm_ring

theorem conj_add (U M N : M3C) :
    U * M * Uᴴ + U * N * Uᴴ = U * (M + N) * Uᴴ := by noncomm_ring

theorem conj_smul (U : M3C) (c : ℂ) (M : M3C) :
    c • (U * M * Uᴴ) = U * (c • M) * Uᴴ := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Conjugation commutes with inversion, in the form we need: an explicit right
    inverse downstairs gives an explicit right inverse upstairs. -/
theorem conj_inv_of_right_inv {U : M3C} (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1)
    {M N : M3C} (h : M * N = 1) :
    (U * M * Uᴴ)⁻¹ = U * N * Uᴴ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [conj_mul hU', h, conj_one hU]

/-! ## The Cayley denominator never vanishes -/

/-- For real `r`, `1 - i r` has real part one, hence is nonzero. -/
theorem one_sub_I_mul_ofReal_ne_zero (r : ℝ) :
    (1 : ℂ) - Complex.I * (r : ℂ) ≠ 0 := by
  intro hcon
  have hre : ((1 : ℂ) - Complex.I * (r : ℂ)).re = 0 := by rw [hcon]; rfl
  simp at hre

/-! ## `1 ± i H` are conjugates of diagonal matrices -/

theorem one_add_I_smul_conj_diagonal (U : M3C) (hU : U * Uᴴ = 1)
    (d : Fin 3 → ℝ) (c : ℂ) :
    1 + c • (U * Matrix.diagonal (fun k => ((d k : ℂ))) * Uᴴ) =
      U * Matrix.diagonal (fun k => 1 + c * (d k : ℂ)) * Uᴴ := by
  have hdiag : (1 : M3C) + c • Matrix.diagonal (fun k => ((d k : ℂ)))
      = Matrix.diagonal (fun k => 1 + c * (d k : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
    · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij, hij]
  rw [conj_smul, ← conj_one hU, conj_add, hdiag]

/-! ## Main statement of this stage -/

/-- **Stage 4.**  A unitary `B` with `1 + B` invertible is unitarily
    diagonalisable.  The unitary is the eigenvector unitary of the Cayley
    transform, and the diagonal entries are the images of the Hermitian
    eigenvalues under the inverse transform. -/
theorem unitary_diagonalizable_of_one_add_isUnit (B : M3C) (hB : Bᴴ * B = 1)
    (h : IsUnit ((1 : M3C) + B).det) :
    ∃ (U : M3C) (w : Fin 3 → ℂ),
      U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧ B = U * Matrix.diagonal w * Uᴴ := by
  have hH : (cayley B).IsHermitian := cayley_isHermitian B hB h
  set U : M3C := (hH.eigenvectorUnitary : M3C) with hUdef
  set d : Fin 3 → ℝ := hH.eigenvalues with hddef
  have hU : U * Uᴴ = 1 := by
    rw [hUdef, ← Matrix.star_eq_conjTranspose]
    exact (Matrix.mem_unitaryGroup_iff).mp (hH.eigenvectorUnitary).2
  have hU' : Uᴴ * U = 1 := by
    rw [hUdef, ← Matrix.star_eq_conjTranspose]
    exact (Matrix.mem_unitaryGroup_iff').mp (hH.eigenvectorUnitary).2
  have hcoe : (RCLike.ofReal ∘ hH.eigenvalues : Fin 3 → ℂ)
      = fun k => ((d k : ℝ) : ℂ) := rfl
  have hspec : cayley B = U * Matrix.diagonal (fun k => ((d k : ℂ))) * Uᴴ := by
    rw [hUdef, hddef, ← Matrix.star_eq_conjTranspose, ← hcoe]
    exact hH.spectral_theorem
  -- the two halves
  have hplus : 1 + Complex.I • cayley B =
      U * Matrix.diagonal (fun k => 1 + Complex.I * (d k : ℂ)) * Uᴴ := by
    rw [hspec]; exact one_add_I_smul_conj_diagonal U hU d Complex.I
  have hminus : 1 - Complex.I • cayley B =
      U * Matrix.diagonal (fun k => 1 - Complex.I * (d k : ℂ)) * Uᴴ := by
    rw [sub_eq_add_neg, ← neg_smul, hspec]
    have := one_add_I_smul_conj_diagonal U hU d (-Complex.I)
    simpa [sub_eq_add_neg, neg_mul] using this
  -- invert the diagonal half
  have hdiagInv :
      Matrix.diagonal (fun k => 1 - Complex.I * (d k : ℂ)) *
        Matrix.diagonal (fun k => (1 - Complex.I * (d k : ℂ))⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    rw [show (fun k => (1 - Complex.I * (d k : ℂ)) * (1 - Complex.I * (d k : ℂ))⁻¹)
        = (fun _ => (1 : ℂ)) from funext fun k =>
          mul_inv_cancel₀ (one_sub_I_mul_ofReal_ne_zero (d k))]
    exact Matrix.diagonal_one
  have hinv : (1 - Complex.I • cayley B)⁻¹ =
      U * Matrix.diagonal (fun k => (1 - Complex.I * (d k : ℂ))⁻¹) * Uᴴ := by
    rw [hminus]
    exact conj_inv_of_right_inv hU hU' hdiagInv
  refine ⟨U, fun k => (1 + Complex.I * (d k : ℂ)) * (1 - Complex.I * (d k : ℂ))⁻¹,
    hU, hU', ?_⟩
  rw [← cayley_recover B h, hplus, hinv, conj_mul hU', Matrix.diagonal_mul_diagonal]

/-! ## Axiom audit -/

#print axioms conj_mul
#print axioms conj_inv_of_right_inv
#print axioms one_sub_I_mul_ofReal_ne_zero
#print axioms one_add_I_smul_conj_diagonal
#print axioms unitary_diagonalizable_of_one_add_isUnit

end CubeToSU3.Continuous
