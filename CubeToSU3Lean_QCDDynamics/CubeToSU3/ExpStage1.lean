import CubeToSU3.LinkFromD

/-!
# `exp (θ D) = P`,第一階段:Fourier 對角化(純代數)

Splitting the analytic step the way `SU3SpectralStage1`–`5` split the unitary
spectral theorem.  **This file contains no analysis**: it exhibits the Fourier
matrix `V`, its inverse, and the diagonalisation of `D`.

The eigenvectors are the three `ℤ/3` Fourier vectors — the same ones that make
`a·1 + b·P + c·P²` simultaneously diagonalisable — with no `√3` normalisation,
so that `V⁻¹ = Vᴴ/3` and no square root appears in the matrices:

    V = !![1, 1,  1;
           1, ω,  ω²;
           1, ω², ω ]

    V · (Vᴴ/3) = 1                        (`Vmat_mul_Wmat`)
    D · V = V · diag(0, -i√3, i√3)        (`DmatM_mul_Vmat`)
    D = V · Λ · V⁻¹                       (`DmatM_conj`)

**Design note (v2).**  Both `ω` and `ω²` are given by their coordinates, and the
matrices are built from those two literals rather than from products.  Every
entry identity is then plain arithmetic on `re`/`im`, closed by `Complex.ext`
and `√3 · √3 = 3`; no rewriting with `ω³ = 1` is needed inside the matrix
proofs, which is what stalled v1.

Stage 2 will apply `Matrix.exp_conj` and `Matrix.exp_diagonal` to the last two
facts, evaluate `exp(∓2πi/3)`, and land on `PmatM` — where those two values are
exactly `ω` and `ω²` again.

Nothing here is a physical claim.
-/

noncomputable section

open Matrix

namespace CubeToSU3.Lattice

open CubeToSU3 CubeToSU3.Continuous

/-! ## The two primitive cube roots of unity, as literals -/

/-- `ω = exp(2πi/3)`. -/
def om : ℂ := ⟨-(1/2), Real.sqrt 3 / 2⟩

/-- `ω² = exp(-2πi/3) = conj ω`. -/
def om2 : ℂ := ⟨-(1/2), -(Real.sqrt 3 / 2)⟩

/-- `√3 · √3 = 3`: the only fact about the square root used anywhere below. -/
theorem sqrt3_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

theorem sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := by
  rw [pow_two]; exact sqrt3_mul_self

/-- The literal `om2` really is `ω²`. -/
theorem om_sq : om * om = om2 := by
  have h := sqrt3_mul_self
  apply Complex.ext <;>
    simp [om, om2, Complex.mul_re, Complex.mul_im] <;> nlinarith [h]

/-- `ω · ω² = 1`, i.e. `ω³ = 1`. -/
theorem om_mul_om2 : om * om2 = 1 := by
  have h := sqrt3_mul_self
  apply Complex.ext <;>
    simp [om, om2, Complex.mul_re, Complex.mul_im] <;> nlinarith [h]

/-- `1 + ω + ω² = 0`: the algebraic form of "the projection kills the body
    diagonal". -/
theorem one_add_om_add_om2 : 1 + om + om2 = 0 := by
  apply Complex.ext <;> simp [om, om2] <;> ring

theorem om_conj : (starRingEnd ℂ) om = om2 := by
  apply Complex.ext <;> simp [om, om2]

theorem om2_conj : (starRingEnd ℂ) om2 = om := by
  apply Complex.ext <;> simp [om, om2]

/-! ## The Fourier matrix -/

/-- The unnormalised Fourier matrix: columns `(1,1,1)`, `(1,ω,ω²)`, `(1,ω²,ω)`. -/
def Vmat : M3C := !![1, 1, 1; 1, om, om2; 1, om2, om]

/-- Its inverse, `Vᴴ/3`, written out. -/
def Wmat : M3C :=
  !![(3 : ℂ)⁻¹, (3 : ℂ)⁻¹, (3 : ℂ)⁻¹;
     (3 : ℂ)⁻¹, om2 / 3, om / 3;
     (3 : ℂ)⁻¹, om / 3, om2 / 3]

/-- `Wmat` is the scaled conjugate transpose of `Vmat`. -/
theorem Wmat_eq_conjTranspose : Wmat = (3 : ℂ)⁻¹ • Vmatᴴ := by
  unfold Wmat Vmat
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.smul_apply, om_conj, om2_conj,
      div_eq_inv_mul] <;>
    ring

/-- `V · (Vᴴ/3) = 1`: the Fourier vectors are orthogonal. -/
theorem Vmat_mul_Wmat : Vmat * Wmat = 1 := by
  have h := sqrt3_mul_self
  unfold Vmat Wmat
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, om, om2,
        Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
        Complex.normSq_apply] <;>
      nlinarith [h]

/-- Hence `V⁻¹ = Vᴴ/3`. -/
theorem Vmat_inv : Vmat⁻¹ = Wmat :=
  Matrix.inv_eq_right_inv Vmat_mul_Wmat

/-! ## The diagonalisation -/

/-- The eigenvalues of `D`: `0` along the 乾-坤 diagonal, `∓i√3` on the plane
    orthogonal to it.  The `√3` is `|(1,1,1)|`. -/
def Lam : M3C :=
  Matrix.diagonal ![0, -((Real.sqrt 3 : ℂ) * Complex.I), (Real.sqrt 3 : ℂ) * Complex.I]

/-- **The diagonalisation, in product form**: each Fourier vector is an
    eigenvector of `D`. -/
theorem DmatM_mul_Vmat : DmatM * Vmat = Vmat * Lam := by
  have h := sqrt3_mul_self
  rw [DmatM_eq]
  unfold Vmat Lam
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, om, om2,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im] <;>
      nlinarith [h]

/-- **The diagonalisation, in conjugation form**: the shape `Matrix.exp_conj`
    consumes in stage 2. -/
theorem DmatM_conj : DmatM = Vmat * Lam * Vmat⁻¹ := by
  rw [Vmat_inv, ← DmatM_mul_Vmat, Matrix.mul_assoc, Vmat_mul_Wmat,
    Matrix.mul_one]

/-! ## Axiom audit -/

#print axioms om_sq
#print axioms om_mul_om2
#print axioms one_add_om_add_om2
#print axioms om_conj
#print axioms Wmat_eq_conjTranspose
#print axioms Vmat_mul_Wmat
#print axioms Vmat_inv
#print axioms DmatM_mul_Vmat
#print axioms DmatM_conj

end CubeToSU3.Lattice
