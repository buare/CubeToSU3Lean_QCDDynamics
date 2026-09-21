import CubeToSU3.SU3SpectralStage2

/-!
# Removing `UnitarySpectralTheorem3`, stage 3: inverting the Cayley transform

Stage 2 produced a Hermitian `H = cayley B`.  For that to be useful, `B` has to
be recoverable from `H`, and recoverable by an expression that is *diagonal
whenever `H` is diagonal*.  This file supplies the inverse transform

    B = (1 + i H) (1 - i H)⁻¹

The computation is short once the two halves are evaluated.  Since
`i • cayley B = -((1 - B)(1 + B)⁻¹)` and `1 = (1 + B)(1 + B)⁻¹`,

    1 - i H = ((1 + B) + (1 - B)) (1 + B)⁻¹ = 2 • (1 + B)⁻¹
    1 + i H = ((1 + B) - (1 - B)) (1 + B)⁻¹ = 2 • (B (1 + B)⁻¹)

so `1 - i H` is invertible with inverse `2⁻¹ • (1 + B)`, and multiplying the two
gives `B` with the factors of two cancelling.

Note the orientation: it is `(1 + iH)(1 - iH)⁻¹` that returns `B`.  The other
order returns `B⁻¹`, since the two halves are exchanged.

Everything here is algebra over the ring `M3C`; unitarity is not used, only
invertibility of `1 + B`.  Unitarity was already spent in stage 2 to make `H`
Hermitian, and will be spent again in stage 4 to put the eigenvalues on the unit
circle.

Stage 4 then diagonalises `H` by `Matrix.IsHermitian.spectral_theorem`, pushes
the diagonalisation through this rational expression, and assembles
`UnitarySpectralTheorem3`.
-/

noncomputable section

open Matrix Complex

namespace CubeToSU3.Continuous

/-- Multiplying the Cayley transform by `i` clears the `i` in its definition. -/
theorem I_smul_cayley (B : M3C) :
    Complex.I • cayley B = -((1 - B) * (1 + B)⁻¹) := by
  unfold cayley
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]

theorem one_sub_I_smul_cayley (B : M3C) (h : IsUnit ((1 : M3C) + B).det) :
    1 - Complex.I • cayley B = (2 : ℂ) • (1 + B)⁻¹ := by
  have hinv : ((1 : M3C) + B) * (1 + B)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  rw [I_smul_cayley, sub_neg_eq_add, two_smul]
  calc (1 : M3C) + (1 - B) * (1 + B)⁻¹
      = ((1 : M3C) + B) * (1 + B)⁻¹ + (1 - B) * (1 + B)⁻¹ := by rw [hinv]
    _ = (1 + B)⁻¹ + (1 + B)⁻¹ := by noncomm_ring

theorem one_add_I_smul_cayley (B : M3C) (h : IsUnit ((1 : M3C) + B).det) :
    1 + Complex.I • cayley B = (2 : ℂ) • (B * (1 + B)⁻¹) := by
  have hinv : ((1 : M3C) + B) * (1 + B)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  rw [I_smul_cayley, ← sub_eq_add_neg, two_smul]
  calc (1 : M3C) - (1 - B) * (1 + B)⁻¹
      = ((1 : M3C) + B) * (1 + B)⁻¹ - (1 - B) * (1 + B)⁻¹ := by rw [hinv]
    _ = B * (1 + B)⁻¹ + B * (1 + B)⁻¹ := by noncomm_ring

/-- `1 - i H` is invertible, with an explicit inverse. -/
theorem inv_one_sub_I_smul_cayley (B : M3C) (h : IsUnit ((1 : M3C) + B).det) :
    (1 - Complex.I • cayley B)⁻¹ = (2 : ℂ)⁻¹ • (1 + B) := by
  apply Matrix.inv_eq_right_inv
  rw [one_sub_I_smul_cayley B h, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.nonsing_inv_mul _ h, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

theorem isUnit_det_one_sub_I_smul_cayley (B : M3C)
    (h : IsUnit ((1 : M3C) + B).det) :
    IsUnit (1 - Complex.I • cayley B).det := by
  rw [one_sub_I_smul_cayley B h, Matrix.det_smul]
  refine IsUnit.mul ?_ (Matrix.isUnit_nonsing_inv_det _ h)
  refine isUnit_iff_ne_zero.2 ?_
  simp only [Fintype.card_fin]
  norm_num

/-- **Stage 3.**  The Cayley transform is invertible as a map: `B` is recovered
    from `H = cayley B` by a rational expression that will stay diagonal when
    `H` is diagonalised. -/
theorem cayley_recover (B : M3C) (h : IsUnit ((1 : M3C) + B).det) :
    (1 + Complex.I • cayley B) * (1 - Complex.I • cayley B)⁻¹ = B := by
  rw [one_add_I_smul_cayley B h, inv_one_sub_I_smul_cayley B h,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul, mul_assoc,
    Matrix.nonsing_inv_mul _ h, mul_one]

/-! ## Axiom audit -/

#print axioms I_smul_cayley
#print axioms one_sub_I_smul_cayley
#print axioms one_add_I_smul_cayley
#print axioms inv_one_sub_I_smul_cayley
#print axioms isUnit_det_one_sub_I_smul_cayley
#print axioms cayley_recover

end CubeToSU3.Continuous
