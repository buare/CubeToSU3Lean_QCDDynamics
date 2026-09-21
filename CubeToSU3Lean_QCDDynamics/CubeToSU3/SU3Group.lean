/-
  SU3Group.lean

  Matrix exponential from the continuous real Lie algebra su(3) to the
  special unitary matrix group SU(3).

  This file closes the determinant gap left deliberately open in
  `CompactSU3.lean`.  Rather than assuming the general identity

      det (exp A) = exp (trace A),

  it proves the needed special case for anti-Hermitian matrices by applying
  the spectral theorem to the Hermitian matrix i A.

  Scope
  -----
  Proved here:
  * the existing carrier `Su3R` has real dimension eight;
  * its established eight-coordinate model is complete and linearly equivalent
    to `Su3R`;
  * after choosing Mathlib's finite-dimensional `linfty` matrix norm, `Su3R`
    itself is complete;
  * `SU3` is Mathlib's group of 3 by 3 unitary complex matrices of determinant
    one;
  * the matrix exponential of every `X : Su3R` belongs to `SU3`;
  * the resulting map `expSU3 : Su3R -> SU3` is continuous.

  This is a matrix-group exponential theorem.  It does not by itself build a
  smooth-manifold `LieGroup` instance, prove compactness/simply-connectedness,
  or formalise a gauge field, Yang--Mills theory, quantisation, or QCD.

  No `sorry`, `admit`, or custom axiom is used.
-/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Spectrum
import CubeToSU3.CompactSU3Real

noncomputable section

set_option maxHeartbeats 4000000

open Matrix Complex BigOperators

namespace CubeToSU3.Continuous

/-! ## The continuous Lie algebra and its complete coordinate model -/

/-- The already constructed real Lie algebra has real dimension eight. -/
theorem finrank_su3R : Module.finrank ℝ Su3R = 8 := by
  rw [← LinearEquiv.finrank_eq coeffLinearEquivSu3]
  simp [RCoeff8]

/-- The eight real coordinates used to construct `Su3R` form a complete
    finite-dimensional model.  We deliberately do not manufacture a second
    norm on the matrix subtype `Su3R`; `coeffLinearEquivSu3` is the already
    proved linear equivalence between this complete model and `Su3R`. -/
abbrev Su3CompleteModel := RCoeff8

theorem su3CompleteModel_isComplete :
    IsComplete (Set.univ : Set Su3CompleteModel) :=
  complete_univ

/-! ## The target matrix group -/

/-- The special unitary group SU(3), with multiplication inherited from
    complex 3 by 3 matrices. -/
abbrev SU3 := ↥(Matrix.specialUnitaryGroup (Fin 3) ℂ)

theorem mem_SU3_iff {A : M3C} :
    A ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ ↔
      A ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧ Matrix.det A = 1 :=
  Matrix.mem_specialUnitaryGroup_iff

/-! ## Spectral proof of the determinant-one condition -/

/-- Multiplication by i converts an anti-Hermitian matrix into a Hermitian
    matrix. -/
def hermitianPartner (X : M3C) : M3C := I • X

theorem hermitianPartner_isHermitian {X : M3C} (hX : IsSu3R X) :
    (hermitianPartner X).IsHermitian := by
  change (I • X)ᴴ = I • X
  rw [Matrix.conjTranspose_smul, hX.1]
  simp

/-- Multiplication by -i recovers the original matrix. -/
theorem negI_smul_hermitianPartner (X : M3C) :
    (-I : ℂ) • hermitianPartner X = X := by
  ext i j
  simp [hermitianPartner, smul_eq_mul, ← mul_assoc, Complex.I_mul_I]

/-- Unitary conjugation preserves the determinant. -/
theorem det_unitary_conj
    (U : unitary M3C) (A : M3C) :
    Matrix.det ((U : M3C) * A * star (U : M3C)) = Matrix.det A := by
  rw [Matrix.det_mul, Matrix.det_mul]
  have hU : (U : M3C) * star (U : M3C) = 1 :=
    unitary.coe_mul_star_self U
  have hdetU : Matrix.det (U : M3C) * Matrix.det (star (U : M3C)) = 1 := by
    rw [← Matrix.det_mul, hU, Matrix.det_one]
  calc
    Matrix.det (U : M3C) * Matrix.det A * Matrix.det (star (U : M3C)) =
        Matrix.det A *
          (Matrix.det (U : M3C) * Matrix.det (star (U : M3C))) := by ring
    _ = Matrix.det A := by rw [hdetU, mul_one]

/-- The determinant of the exponential of a traceless anti-Hermitian matrix
    is one.  This is the missing bridge from U(3) to SU(3).

    The proof is specialised to the present skew-Hermitian case and therefore
    does not assume Mathlib's missing general matrix det-exp formula. -/
theorem det_exp_eq_one_of_isSu3R {X : M3C} (hX : IsSu3R X) :
    Matrix.det (NormedSpace.exp ℂ X) = 1 := by
  let H : M3C := hermitianPartner X
  have hH : H.IsHermitian := by
    exact hermitianPartner_isHermitian hX
  let U : unitary M3C := hH.eigenvectorUnitary
  let d : Fin 3 → ℂ := fun i =>
    (-I : ℂ) * (hH.eigenvalues i : ℂ)

  have hSpectral :
      H = (U : M3C) *
          Matrix.diagonal
            ((RCLike.ofReal : ℝ → ℂ) ∘ hH.eigenvalues) *
          star (U : M3C) := by
    simpa only [U] using hH.spectral_theorem

  have hsmulDiagonal :
      (-I : ℂ) •
          Matrix.diagonal
            ((RCLike.ofReal : ℝ → ℂ) ∘ hH.eigenvalues) =
        Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d]
    · simp [d, hij]

  have hdiag :
      X = (U : M3C) * Matrix.diagonal d * star (U : M3C) := by
    calc
      X = (-I : ℂ) • H := by
        dsimp [H]
        exact (negI_smul_hermitianPartner X).symm
      _ = (-I : ℂ) •
          ((U : M3C) *
            Matrix.diagonal
              ((RCLike.ofReal : ℝ → ℂ) ∘ hH.eigenvalues) *
            star (U : M3C)) := by
        exact congrArg (fun A : M3C => (-I : ℂ) • A) hSpectral
      _ = (U : M3C) *
          ((-I : ℂ) •
            Matrix.diagonal
              ((RCLike.ofReal : ℝ → ℂ) ∘ hH.eigenvalues)) *
          star (U : M3C) := by
        rw [← smul_mul_assoc, ← mul_smul_comm]
      _ = (U : M3C) * Matrix.diagonal d * star (U : M3C) := by
        rw [hsmulDiagonal]

  have htraceH : Matrix.trace H = 0 := by
    simp [H, hermitianPartner, hX.2]

  have hsumEig : ∑ i, (hH.eigenvalues i : ℂ) = 0 := by
    rw [hSpectral, Matrix.trace_mul_cycle,
      unitary.coe_star_mul_self U, one_mul,
      Matrix.trace_diagonal] at htraceH
    exact htraceH

  have hsumD : ∑ i, d i = 0 := by
    dsimp [d]
    rw [← Finset.mul_sum, hsumEig, mul_zero]

  have hdetDiagonal :
      Matrix.det (NormedSpace.exp ℂ (Matrix.diagonal d)) = 1 := by
    rw [Matrix.exp_diagonal, Matrix.det_diagonal]
    simp_rw [Pi.coe_exp]
    calc
      (∏ i, NormedSpace.exp ℂ (d i)) =
          NormedSpace.exp ℂ (∑ i, d i) := by
        simpa using (NormedSpace.exp_sum Finset.univ d).symm
      _ = 1 := by simp [hsumD]

  have hmapExp :
      NormedSpace.exp ℂ
          ((U : M3C) * Matrix.diagonal d * star (U : M3C)) =
        (U : M3C) *
          NormedSpace.exp ℂ (Matrix.diagonal d) * star (U : M3C) := by
    simpa [unitary.toUnits] using
      (Matrix.exp_units_conj ℂ (unitary.toUnits U) (Matrix.diagonal d))

  calc
    Matrix.det (NormedSpace.exp ℂ X) =
        Matrix.det (NormedSpace.exp ℂ
          ((U : M3C) * Matrix.diagonal d * star (U : M3C))) := by rw [hdiag]
    _ = Matrix.det ((U : M3C) *
          NormedSpace.exp ℂ (Matrix.diagonal d) * star (U : M3C)) := by
      rw [hmapExp]
    _ = Matrix.det (NormedSpace.exp ℂ (Matrix.diagonal d)) :=
      det_unitary_conj U _
    _ = 1 := hdetDiagonal

/-! ## The exponential map su(3) -> SU(3) -/

/-- The exponential of an anti-Hermitian matrix is unitary.  This local
    formulation uses Mathlib's matrix-exponential lemmas, which hide the
    non-canonical choice of a matrix norm inside their proofs. -/
theorem exp_mem_unitaryGroup {X : M3C} (hX : IsSu3R X) :
    NormedSpace.exp ℂ X ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change NormedSpace.exp ℂ X * (NormedSpace.exp ℂ X)ᴴ = 1
  rw [← Matrix.exp_conjTranspose, hX.1,
    ← Matrix.exp_add_of_commute ℂ X (-X) ((Commute.refl X).neg_right)]
  simp

theorem exp_mem_SU3 (X : Su3R) :
    NormedSpace.exp ℂ X.1 ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  exact ⟨exp_mem_unitaryGroup X.2,
    det_exp_eq_one_of_isSu3R X.2⟩

/-- The matrix exponential bundled with its proof of membership in SU(3). -/
def expSU3 (X : Su3R) : SU3 :=
  ⟨NormedSpace.exp ℂ X.1, exp_mem_SU3 X⟩

@[simp] theorem coe_expSU3 (X : Su3R) :
    (expSU3 X : M3C) = NormedSpace.exp ℂ X.1 := rfl

@[simp] theorem expSU3_zero : expSU3 (0 : Su3R) = 1 := by
  apply Subtype.ext
  simp [expSU3]

section LinftyTopology

local instance : SeminormedRing M3C := Matrix.linftyOpSemiNormedRing
local instance : NormedRing M3C := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℂ M3C := Matrix.linftyOpNormedAlgebra

/-- With the explicit finite-dimensional `linfty` matrix norm fixed, the
    eight-dimensional real space `Su3R` is complete. -/
noncomputable local instance su3RCompleteSpaceLinfty : CompleteSpace Su3R :=
  FiniteDimensional.complete ℝ Su3R

theorem su3R_isComplete_linfty : IsComplete (Set.univ : Set Su3R) :=
  complete_univ

/-- The matrix-group exponential is continuous.  The target carries the
    subspace topology induced by the finite-dimensional `linfty` operator
    norm used here locally. -/
theorem continuous_expSU3 : Continuous expSU3 := by
  unfold expSU3
  exact (NormedSpace.exp_continuous.comp continuous_subtype_val).subtype_mk _

end LinftyTopology

/-! ## Axiom audit -/

#print axioms finrank_su3R
#print axioms su3CompleteModel_isComplete
#print axioms su3R_isComplete_linfty
#print axioms hermitianPartner_isHermitian
#print axioms det_unitary_conj
#print axioms det_exp_eq_one_of_isSu3R
#print axioms exp_mem_unitaryGroup
#print axioms exp_mem_SU3
#print axioms continuous_expSU3

end CubeToSU3.Continuous
