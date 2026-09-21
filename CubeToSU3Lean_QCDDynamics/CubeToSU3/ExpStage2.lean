import CubeToSU3.ExpStage1

/-!
# `exp (θ D) = P`,第二階段:指數化

Stage 1 gave `D = V Λ V⁻¹` with `Λ = diag(0, -i√3, i√3)`.  This file applies
`Matrix.exp_conj` and `Matrix.exp_diagonal`, evaluates the two scalar
exponentials, and lands on `PmatM`:

    θ = 2π/(3√3)        so   θ·√3 = 2π/3
    exp(θ Λ) = diag(1, e^{-2πi/3}, e^{2πi/3}) = diag(1, ω², ω) =: E
    exp(θ D) = V · E · V⁻¹ = V · E · (Vᴴ/3) = P

The two eigenvalue exponentials come back as `ω` and `ω²` — the same two cube
roots of unity stage 1 used to build `V`.

Revision notes: the matrix exponential is `NormedSpace.exp ℂ`,
`Complex.exp_eq_exp_ℂ` reads `Complex.exp = NormedSpace.exp ℂ`, and the
pointwise exponential on a Pi type is `Pi.exp_def`.

Performance notes (v3): the final product is done in two steps with the factor
`1/3` pulled out (`V·E` first, then `·Vᴴ`), so no complex division appears
inside a nine-entry `simp`; and the scalar exponentials are also stated in the
cast-pushed form `2 * (π : ℂ) / 3` that `simp` produces.

Nothing here is a physical claim.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Matrix

namespace CubeToSU3.Lattice

open CubeToSU3 CubeToSU3.Continuous

/-! ## The angle -/

/-- `θ = 2π/(3√3)`: the parameter at which the one-parameter subgroup generated
    by `D` reaches the 120° rotation. -/
def theta : ℝ := 2 * Real.pi / (3 * Real.sqrt 3)

theorem sqrt3_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

theorem sqrt3_ne_zero : Real.sqrt 3 ≠ 0 := ne_of_gt sqrt3_pos

/-- `θ · √3 = 2π/3`: the rotation angle, since `|(1,1,1)| = √3`. -/
theorem theta_mul_sqrt3 : theta * Real.sqrt 3 = 2 * Real.pi / 3 := by
  unfold theta
  field_simp
  ring

/-! ## The two scalar exponentials -/

theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -(1/2) := by
  have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]

theorem sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.sin_pi_sub, Real.sin_pi_div_three]

/-- `e^{2πi/3} = ω`. -/
theorem cexp_pos : Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) = om := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    cos_two_pi_div_three, sin_two_pi_div_three]
  apply Complex.ext <;> simp [om]

/-- `e^{-2πi/3} = ω²`. -/
theorem cexp_neg : Complex.exp (-(((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I)) = om2 := by
  have h : -(((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I)
      = (-((2 * Real.pi / 3 : ℝ) : ℂ)) * Complex.I := by ring
  rw [h, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    cos_two_pi_div_three, sin_two_pi_div_three]
  apply Complex.ext <;> simp [om2]

/-- The same two facts in the cast-pushed shape that `simp` produces. -/
theorem cexp_pos' : Complex.exp (2 * (Real.pi : ℂ) / 3 * Complex.I) = om := by
  have h : 2 * (Real.pi : ℂ) / 3 = ((2 * Real.pi / 3 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h]; exact cexp_pos

theorem cexp_neg' : Complex.exp (-(2 * (Real.pi : ℂ) / 3 * Complex.I)) = om2 := by
  have h : 2 * (Real.pi : ℂ) / 3 = ((2 * Real.pi / 3 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h]; exact cexp_neg

/-- `NormedSpace.exp ℂ` on scalars is `Complex.exp`. -/
theorem exp_scalar (z : ℂ) : NormedSpace.exp ℂ z = Complex.exp z := by
  rw [← Complex.exp_eq_exp_ℂ]

/-! ## The diagonal exponential -/

/-- `exp(θΛ)`, written out. -/
def Emat : M3C := !![1, 0, 0; 0, om2, 0; 0, 0, om]

/-- `θ Λ` as a diagonal matrix of angles. -/
theorem theta_smul_Lam :
    (theta : ℂ) • Lam
      = Matrix.diagonal
          ![0, -(((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I),
            ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I] := by
  have h : ((theta : ℂ)) * ((Real.sqrt 3 : ℝ) : ℂ) = ((2 * Real.pi / 3 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, theta_mul_sqrt3]
  unfold Lam
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.diagonal_apply, ← h] <;> ring

/-- `exp(θΛ) = diag(1, ω², ω)`. -/
theorem exp_theta_Lam : NormedSpace.exp ℂ ((theta : ℂ) • Lam) = Emat := by
  rw [theta_smul_Lam, Matrix.exp_diagonal]
  unfold Emat
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_apply, Pi.exp_def, exp_scalar, cexp_pos, cexp_neg,
      cexp_pos', cexp_neg']

/-! ## The product, done in two light steps -/

/-- `ω² · ω² = ω`. -/
theorem om2_sq : om2 * om2 = om := by
  have h := sqrt3_mul_self
  apply Complex.ext <;>
    simp [om, om2, Complex.mul_re, Complex.mul_im] <;> nlinarith [h]

/-- `Vᴴ`, written out. -/
def VHmat : M3C := !![1, 1, 1; 1, om2, om; 1, om, om2]

theorem Vmat_conjTranspose : Vmatᴴ = VHmat := by
  unfold Vmat VHmat
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, om_conj, om2_conj]

theorem Wmat_eq_smul_VH : Wmat = (3 : ℂ)⁻¹ • VHmat := by
  rw [Wmat_eq_conjTranspose, Vmat_conjTranspose]

/-- First step: `V · E` is `V` with its rows cyclically rearranged.  Uses only
    `ω·ω² = 1`, `ω² = ω·ω` and `ω²·ω² = ω`; no division. -/
theorem Vmat_mul_Emat :
    Vmat * Emat = !![1, om2, om; 1, 1, 1; 1, om, om2] := by
  have h1 := om_mul_om2
  have h2 := om_sq
  have h3 := om2_sq
  unfold Vmat Emat
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    simp [h1, h2, h3, mul_comm]

/-- Second step: `(V·E) · Vᴴ = 3 P`. -/
theorem VEVH : (Vmat * Emat) * VHmat = (3 : ℂ) • PmatM := by
  have h := sqrt3_mul_self
  rw [Vmat_mul_Emat]
  unfold VHmat PmatM
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.smul_apply, om, om2,
        Complex.mul_re, Complex.mul_im] <;>
      nlinarith [h]

/-! ## The exponential of `D` -/

theorem Vmat_isUnit : IsUnit Vmat := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact Matrix.isUnit_det_of_right_inverse Vmat_mul_Wmat

/-- **The bridge, completed.**  The link variable of `WilsonAction` is the
    exponential of the fibre-side generator `D`. -/
theorem exp_theta_DmatM : NormedSpace.exp ℂ ((theta : ℂ) • DmatM) = PmatM := by
  have h : (theta : ℂ) • DmatM = Vmat * ((theta : ℂ) • Lam) * Vmat⁻¹ := by
    rw [DmatM_conj, Matrix.mul_smul, Matrix.smul_mul]
  rw [h, Matrix.exp_conj ℂ _ _ Vmat_isUnit, exp_theta_Lam, Vmat_inv,
    Wmat_eq_smul_VH, Matrix.mul_smul, VEVH, smul_smul]
  norm_num

/-! ## Axiom audit -/

#print axioms theta_mul_sqrt3
#print axioms cexp_pos
#print axioms cexp_neg
#print axioms theta_smul_Lam
#print axioms exp_theta_Lam
#print axioms Vmat_mul_Emat
#print axioms VEVH
#print axioms Vmat_isUnit
#print axioms exp_theta_DmatM

end CubeToSU3.Lattice
