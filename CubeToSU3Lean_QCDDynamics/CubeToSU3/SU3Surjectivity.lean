/-
  SU3Surjectivity.lean

  Reduction of global exponential surjectivity for SU(3) to the missing
  unitary spectral theorem in Mathlib 4.16.

  The substantial part proved here is the logarithm construction: assuming a
  unitary diagonalisation A = U diag(z) U*, the principal logarithms of the
  three unit phases are adjusted by one integral multiple of 2*pi*i.  This
  preserves their exponentials and makes their sum exactly zero.  Conjugating
  the resulting diagonal matrix gives an element of su(3) whose exponential
  is A.

  No `sorry`, `admit`, or custom axiom is used.  The one explicit hypothesis
  in the final theorem is stated as a proposition, not installed as an axiom.
-/

import CubeToSU3.SU3Global
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section

set_option maxHeartbeats 4000000

open Matrix Complex BigOperators

namespace CubeToSU3.Continuous

section LinftyTopology

local instance : SeminormedRing M3C := Matrix.linftyOpSemiNormedRing
local instance : NormedRing M3C := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℂ M3C := Matrix.linftyOpNormedAlgebra

/-- A unitary diagonalisation with the diagonal entries bundled as unit
    complex numbers. -/
def HasUnitaryDiagonalization (A : M3C) : Prop :=
  ∃ (U : unitary M3C) (z : Fin 3 → unitary ℂ),
    A = (U : M3C) * Matrix.diagonal (fun i => (z i : ℂ)) * star (U : M3C)

/-- The exact normal/unitary spectral theorem needed by the global logarithm
    construction. -/
def UnitarySpectralTheorem3 : Prop :=
  ∀ A : M3C, A ∈ Matrix.unitaryGroup (Fin 3) ℂ →
    HasUnitaryDiagonalization A

theorem unitary_complex_ne_zero (z : unitary ℂ) : (z : ℂ) ≠ 0 := by
  intro hz
  have h := z.2.1
  rw [hz] at h
  simp at h

theorem log_unitary_re (z : unitary ℂ) : (Complex.log (z : ℂ)).re = 0 := by
  rw [Complex.log_re]
  have hzabs : Complex.abs (z : ℂ) = 1 := by
    rw [← Complex.norm_eq_abs]
    exact CStarRing.norm_coe_unitary z
  rw [hzabs, Real.log_one]

theorem conj_eq_neg_of_re_eq_zero {z : ℂ} (hz : z.re = 0) :
    star z = -z := by
  apply Complex.ext
  · simp [hz]
  · simp

/-- A diagonalisation of an SU(3) matrix yields a trace-adjusted diagonal
    logarithm. -/
theorem exists_trace_zero_diagonal_log
    (A : SU3) (hdiag : HasUnitaryDiagonalization A.1) :
    ∃ (U : unitary M3C) (d : Fin 3 → ℂ),
      A.1 = (U : M3C) * Matrix.diagonal (fun i => Complex.exp (d i)) *
          star (U : M3C) ∧
      (∀ i, star (d i) = -d i) ∧
      ∑ i, d i = 0 := by
  rcases hdiag with ⟨U, z, hA⟩
  let L : Fin 3 → ℂ := fun i => Complex.log (z i : ℂ)

  have hprod : ∏ i, (z i : ℂ) = 1 := by
    have hdet : Matrix.det A.1 = 1 := A.2.2
    rw [hA, det_unitary_conj U, Matrix.det_diagonal] at hdet
    exact hdet

  have hexpL (i : Fin 3) : Complex.exp (L i) = (z i : ℂ) := by
    exact Complex.exp_log (unitary_complex_ne_zero (z i))

  have hexpSum : Complex.exp (∑ i, L i) = 1 := by
    calc
      Complex.exp (∑ i, L i) =
          Complex.exp (L 0) * (Complex.exp (L 1) * Complex.exp (L 2)) := by
        rw [show (∑ i, L i) = L 0 + (L 1 + L 2) by
          simp [Fin.sum_univ_succ], Complex.exp_add, Complex.exp_add]
      _ = (z 0 : ℂ) * ((z 1 : ℂ) * (z 2 : ℂ)) := by
        rw [hexpL, hexpL, hexpL]
      _ = ∏ i, (z i : ℂ) := by simp [Fin.prod_univ_succ]
      _ = 1 := hprod

  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexpSum
  let period : ℂ := (n : ℂ) * (2 * (Real.pi : ℂ) * I)
  let d : Fin 3 → ℂ :=
    ![L 0 - period, L 1, L 2]

  have hsumL : L 0 + (L 1 + L 2) = period := by
    simpa [Fin.sum_univ_succ, period] using hn

  have hsumD : ∑ i, d i = 0 := by
    simp [d, Fin.sum_univ_succ]
    linear_combination hsumL

  have hperiodExp : Complex.exp period = 1 := by
    apply Complex.exp_eq_one_iff.mpr
    exact ⟨n, rfl⟩

  have hexpD (i : Fin 3) : Complex.exp (d i) = (z i : ℂ) := by
    fin_cases i
    · change Complex.exp (L 0 - period) = (z 0 : ℂ)
      rw [Complex.exp_sub, hperiodExp, div_one, hexpL]
    · change Complex.exp (L 1) = (z 1 : ℂ)
      exact hexpL 1
    · change Complex.exp (L 2) = (z 2 : ℂ)
      exact hexpL 2

  have hperiodRe : period.re = 0 := by
    simp [period]

  have hdRe (i : Fin 3) : (d i).re = 0 := by
    fin_cases i
    · change (L 0 - period).re = 0
      simp [L, log_unitary_re, hperiodRe]
    · change (L 1).re = 0
      exact log_unitary_re (z 1)
    · change (L 2).re = 0
      exact log_unitary_re (z 2)

  refine ⟨U, d, ?_, ?_, hsumD⟩
  · rw [hA]
    congr 2
    ext i j
    by_cases hij : i = j
    · subst j
      simp [hexpD]
    · simp [hij]
  · intro i
    exact conj_eq_neg_of_re_eq_zero (hdRe i)

/-- A trace-adjusted diagonal logarithm conjugates to an actual element of
    su(3), and its exponential is the original matrix. -/
theorem exists_su3_log_of_diagonalization
    (A : SU3) (hdiag : HasUnitaryDiagonalization A.1) :
    ∃ X : Su3R, expSU3 X = A := by
  obtain ⟨U, d, hA, hdStar, hsumD⟩ :=
    exists_trace_zero_diagonal_log A hdiag
  let X0 : M3C :=
    (U : M3C) * Matrix.diagonal d * star (U : M3C)

  have hXstar : X0ᴴ = -X0 := by
    have hdiagStar : (Matrix.diagonal d)ᴴ = -Matrix.diagonal d := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [Matrix.conjTranspose_apply, hdStar]
      · simp [Matrix.conjTranspose_apply, hij, Ne.symm hij]
    dsimp [X0]
    change
      (((U : M3C) * Matrix.diagonal d * (U : M3C)ᴴ)ᴴ) =
        -((U : M3C) * Matrix.diagonal d * (U : M3C)ᴴ)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hdiagStar]
    noncomm_ring

  have hXtrace : Matrix.trace X0 = 0 := by
    dsimp [X0]
    rw [Matrix.trace_mul_cycle, unitary.coe_star_mul_self U, one_mul,
      Matrix.trace_diagonal, hsumD]

  let X : Su3R := ⟨X0, hXstar, hXtrace⟩
  refine ⟨X, ?_⟩
  apply Subtype.ext
  change NormedSpace.exp ℂ X0 = A.1
  have hmapExp :
      NormedSpace.exp ℂ X0 =
        (U : M3C) * NormedSpace.exp ℂ (Matrix.diagonal d) *
          star (U : M3C) := by
    dsimp [X0]
    simpa [unitary.toUnits] using
      (Matrix.exp_units_conj ℂ (unitary.toUnits U) (Matrix.diagonal d))
  rw [hmapExp, Matrix.exp_diagonal]
  have hfun : NormedSpace.exp ℂ d = fun i => Complex.exp (d i) := by
    funext i
    rw [Pi.coe_exp]
    exact (congrFun Complex.exp_eq_exp_ℂ (d i)).symm
  rw [hfun]
  exact hA.symm

/-- Once the standard unitary spectral theorem is supplied, the exponential
    map su(3) -> SU(3) is surjective.  All branch and trace adjustments are
    discharged above. -/
theorem expSU3_surjective_of_unitarySpectralTheorem3
    (hspec : UnitarySpectralTheorem3) : ExponentialSurjective := by
  intro A
  exact exists_su3_log_of_diagonalization A (hspec A.1 A.2.1)

/-! ## Axiom audit -/

#print axioms log_unitary_re
#print axioms exists_trace_zero_diagonal_log
#print axioms exists_su3_log_of_diagonalization
#print axioms expSU3_surjective_of_unitarySpectralTheorem3

end LinftyTopology

end CubeToSU3.Continuous
