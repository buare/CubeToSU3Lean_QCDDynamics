import CubeToSU3.SU3SpectralStage1

/-!
# Removing `UnitarySpectralTheorem3`, stage 2: the Cayley transform

Stage 1 produced a unit phase making `μ • 1 + A` nonsingular, so we may assume
from here on that the unitary matrix `B` under consideration has `1 + B`
invertible.  This file builds the Cayley transform

    cayley B = i • ((1 - B) * (1 + B)⁻¹)

and proves it Hermitian.  That is the whole point of the route: `B` is a
rational function of `cayley B`, so diagonalising the *Hermitian* matrix — which
Mathlib can do — diagonalises `B` in the same basis, with no simultaneous
diagonalisation of a commuting family required.

Two design choices keep the matrix-inverse algebra survivable.

* Everything is phrased with `ᴴ` rather than `star`, so the `conjTranspose`
  simp set applies without translation steps.
* Unitarity enters only as the single equation `Bᴴ * B = 1`.  `B⁻¹` never
  appears; the one inverse in play is `(1 + B)⁻¹`, and it is only ever removed
  by `Matrix.mul_nonsing_inv` / `Matrix.nonsing_inv_mul`.

The computation behind `conjTranspose_cayley_core` is

    (1 + Bᴴ)⁻¹ (1 - Bᴴ) = (1 + B)⁻¹ (B - 1)

which holds because `1 + Bᴴ = Bᴴ (1 + B)`, so the `Bᴴ` cancels against
`Bᴴ B = 1` after the `(1 + B)` is absorbed by its inverse.  Combined with
`star i = -i` and the commutation of `1 - B` with `(1 + B)⁻¹`, the two sign
flips cancel and `(cayley B)ᴴ = cayley B`.

Stage 3 will recover `B` from `H = cayley B` as `(1 - i H) (1 + i H)⁻¹` and read
off the diagonalisation.
-/

noncomputable section

open Matrix Complex

namespace CubeToSU3.Continuous

/-! ## Inverses commute with whatever the matrix commutes with -/

/-- If `A` is invertible and commutes with `C`, so does `A⁻¹`. -/
theorem inv_mul_comm_of_comm {A C : M3C} (hA : IsUnit A.det) (h : A * C = C * A) :
    A⁻¹ * C = C * A⁻¹ := by
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  calc A⁻¹ * C = A⁻¹ * C * (A * A⁻¹) := by rw [h1, mul_one]
    _ = A⁻¹ * (C * A) * A⁻¹ := by noncomm_ring
    _ = A⁻¹ * (A * C) * A⁻¹ := by rw [h]
    _ = A⁻¹ * A * C * A⁻¹ := by noncomm_ring
    _ = C * A⁻¹ := by rw [h2, one_mul]

/-- `1 - B` and `(1 + B)⁻¹` commute. -/
theorem one_sub_mul_one_add_inv_comm (B : M3C) (h : IsUnit ((1 : M3C) + B).det) :
    (1 - B) * (1 + B)⁻¹ = (1 + B)⁻¹ * (1 - B) :=
  (inv_mul_comm_of_comm h (by noncomm_ring)).symm

/-! ## The conjugate transpose of the core factor -/

/-- `1 + Bᴴ` is invertible whenever `1 + B` is, for `B` unitary. -/
theorem isUnit_det_one_add_conjTranspose (B : M3C) (hB : Bᴴ * B = 1)
    (h : IsUnit ((1 : M3C) + B).det) : IsUnit ((1 : M3C) + Bᴴ).det := by
  have hfac : Bᴴ * (1 + B) = 1 + Bᴴ := by
    rw [mul_add, mul_one, hB]
    exact add_comm _ _
  have hdetStar : IsUnit (Bᴴ).det := by
    refine isUnit_of_mul_eq_one _ B.det ?_
    rw [← Matrix.det_mul, hB, Matrix.det_one]
  rw [← hfac, Matrix.det_mul]
  exact hdetStar.mul h

/-- The identity that makes the Cayley transform Hermitian. -/
theorem conjTranspose_cayley_core (B : M3C) (hB : Bᴴ * B = 1)
    (h : IsUnit ((1 : M3C) + B).det) :
    ((1 : M3C) + Bᴴ)⁻¹ * (1 - Bᴴ) = (1 + B)⁻¹ * (B - 1) := by
  have hinv : ((1 : M3C) + B) * (1 + B)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have hfac : (1 : M3C) + Bᴴ = Bᴴ * (1 + B) := by
    rw [mul_add, mul_one, hB]
    exact (add_comm _ _).symm
  have hclaim : ((1 : M3C) + Bᴴ) * ((1 + B)⁻¹ * (B - 1)) = 1 - Bᴴ := by
    rw [hfac]
    calc Bᴴ * (1 + B) * ((1 + B)⁻¹ * (B - 1))
        = Bᴴ * ((1 + B) * (1 + B)⁻¹ * (B - 1)) := by noncomm_ring
      _ = Bᴴ * (B - 1) := by rw [hinv, one_mul]
      _ = Bᴴ * B - Bᴴ := by noncomm_ring
      _ = 1 - Bᴴ := by rw [hB]
  have hU : IsUnit ((1 : M3C) + Bᴴ).det :=
    isUnit_det_one_add_conjTranspose B hB h
  calc ((1 : M3C) + Bᴴ)⁻¹ * (1 - Bᴴ)
      = ((1 : M3C) + Bᴴ)⁻¹ * (((1 : M3C) + Bᴴ) * ((1 + B)⁻¹ * (B - 1))) := by
        rw [hclaim]
    _ = ((1 : M3C) + Bᴴ)⁻¹ * ((1 : M3C) + Bᴴ) * ((1 + B)⁻¹ * (B - 1)) := by
        noncomm_ring
    _ = (1 + B)⁻¹ * (B - 1) := by rw [Matrix.nonsing_inv_mul _ hU, one_mul]

/-! ## The transform itself -/

/-- The Cayley transform of `B`. -/
def cayley (B : M3C) : M3C := Complex.I • ((1 - B) * (1 + B)⁻¹)

theorem star_I : star Complex.I = -Complex.I := by
  rw [Complex.star_def]
  exact Complex.conj_I

/-- **Stage 2.**  The Cayley transform of a unitary matrix with `1 + B`
    invertible is Hermitian. -/
theorem cayley_isHermitian (B : M3C) (hB : Bᴴ * B = 1)
    (h : IsUnit ((1 : M3C) + B).det) : (cayley B).IsHermitian := by
  have hcomm : (1 - B) * (1 + B)⁻¹ = (1 + B)⁻¹ * (1 - B) :=
    one_sub_mul_one_add_inv_comm B h
  have hcore : ((1 : M3C) + Bᴴ)⁻¹ * (1 - Bᴴ) = (1 + B)⁻¹ * (B - 1) :=
    conjTranspose_cayley_core B hB h
  show (cayley B)ᴴ = cayley B
  unfold cayley
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, Matrix.conjTranspose_sub, star_I]
  rw [hcore, hcomm,
    show ((1 : M3C) + B)⁻¹ * (B - 1) = -(((1 : M3C) + B)⁻¹ * (1 - B)) by
      noncomm_ring,
    smul_neg, neg_smul, neg_neg]

/-! ## Axiom audit -/

#print axioms inv_mul_comm_of_comm
#print axioms one_sub_mul_one_add_inv_comm
#print axioms isUnit_det_one_add_conjTranspose
#print axioms conjTranspose_cayley_core
#print axioms cayley_isHermitian

end CubeToSU3.Continuous
