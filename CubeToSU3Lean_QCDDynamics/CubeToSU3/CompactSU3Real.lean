/-
  CompactSU3Real.lean

  Mathlib companion to CubeToSU3.CompactSU3 (v11).

  Scope
  -----
  This file performs the two scalar-extension steps deliberately omitted from
  the Std-only core:

  1. The Gaussian-integer lattice is embedded entrywise into complex matrices.
  2. Eight real coordinates are proved linearly equivalent to the full real
     vector space of 3 by 3 complex, anti-Hermitian, traceless matrices.
  3. The integer vector field adD is extended to a real linear vector field,
     and the naive equation dX/dt = kappa [D,X] is stated as an actual ODE.

  This is still an algebra/ODE companion, not QCD.  No Lorentz spacetime,
  gauge connection, Yang-Mills action, quark field, quantisation, confinement,
  or experimental identification is claimed here.

  Target use
  ----------
  Add a Mathlib release compatible with the project's Lean toolchain, place
  this file at CubeToSU3/CompactSU3Real.lean, and run

    lake env lean CubeToSU3/CompactSU3Real.lean

  No `sorry`, `admit`, or custom axiom is used.
-/

import Mathlib
import CubeToSU3.CompactSU3

noncomputable section

set_option maxHeartbeats 1000000

open Matrix Complex BigOperators

namespace CubeToSU3.Continuous

abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ
abbrev RCoeff8 := Fin 8 → ℝ

/- Lean 4.16's vector-literal simplifier has direct numeral support only up to
   index four.  These three local lemmas complete the eight-coordinate case. -/
@[simp] theorem vec8_apply_five {α : Type*}
    (a0 a1 a2 a3 a4 a5 a6 a7 : α) :
    (![a0, a1, a2, a3, a4, a5, a6, a7] : Fin 8 → α) (5 : Fin 8) = a5 := by
  rfl

@[simp] theorem vec8_apply_six {α : Type*}
    (a0 a1 a2 a3 a4 a5 a6 a7 : α) :
    (![a0, a1, a2, a3, a4, a5, a6, a7] : Fin 8 → α) (6 : Fin 8) = a6 := by
  rfl

@[simp] theorem vec8_apply_seven {α : Type*}
    (a0 a1 a2 a3 a4 a5 a6 a7 : α) :
    (![a0, a1, a2, a3, a4, a5, a6, a7] : Fin 8 → α) (7 : Fin 8) = a7 := by
  rfl

/-- The standard mathematical carrier of the real Lie algebra su(3). -/
def IsSu3R (X : M3C) : Prop :=
  Xᴴ = -X ∧ Matrix.trace X = 0

/-- The full real vector subspace of anti-Hermitian traceless matrices. -/
def su3Submodule : Submodule ℝ M3C where
  carrier := {X | IsSu3R X}
  zero_mem' := by
    simp [IsSu3R]
  add_mem' := by
    intro A B hA hB
    constructor
    · simp [hA.1, hB.1, add_comm]
    · rw [Matrix.trace_add, hA.2, hB.2, add_zero]
  smul_mem' := by
    intro r A hA
    constructor
    · rw [Matrix.conjTranspose_smul, hA.1]
      simp
    · rw [Matrix.trace_smul, hA.2, smul_zero]

abbrev Su3R := ↥su3Submodule

/-! ## Eight real coordinates -/

/-- Order of coordinates:
    p, q, u12, v12, u13, v13, u23, v23. -/
def compactMatrixR (c : RCoeff8) : M3C :=
  !![ (c 0 : ℂ) * I,
      (c 2 : ℂ) + (c 3 : ℂ) * I,
      (c 4 : ℂ) + (c 5 : ℂ) * I ;
      -(c 2 : ℂ) + (c 3 : ℂ) * I,
      ((-c 0 + c 1 : ℝ) : ℂ) * I,
      (c 6 : ℂ) + (c 7 : ℂ) * I ;
      -(c 4 : ℂ) + (c 5 : ℂ) * I,
      -(c 6 : ℂ) + (c 7 : ℂ) * I,
      -(c 1 : ℂ) * I ]

theorem compactMatrixR_mem (c : RCoeff8) : IsSu3R (compactMatrixR c) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [compactMatrixR, Matrix.conjTranspose_apply, Complex.ext_iff]
  · simp [compactMatrixR, Matrix.trace, Fin.sum_univ_succ, Complex.ext_iff]

/-- Read the eight real coordinates from an arbitrary complex matrix. -/
def coordinatesR (X : M3C) : RCoeff8 :=
  ![(X 0 0).im, -(X 2 2).im,
    (X 0 1).re, (X 0 1).im,
    (X 0 2).re, (X 0 2).im,
    (X 1 2).re, (X 1 2).im]

theorem coordinatesR_compactMatrixR (c : RCoeff8) :
    coordinatesR (compactMatrixR c) = c := by
  funext i
  fin_cases i <;> simp [coordinatesR, compactMatrixR]

theorem entry_conj {X : M3C} (hX : IsSu3R X) (i j : Fin 3) :
    (starRingEnd ℂ) (X j i) = -(X i j) := by
  have h := congrArg (fun M : M3C => M i j) hX.1
  simpa [Matrix.conjTranspose_apply] using h

theorem diag_re_eq_zero {X : M3C} (hX : IsSu3R X) (i : Fin 3) :
    (X i i).re = 0 := by
  have h := entry_conj hX i i
  have hre := congrArg Complex.re h
  simp at hre
  linarith

theorem lower_of_upper {X : M3C} (hX : IsSu3R X) (i j : Fin 3) :
    X j i = -(starRingEnd ℂ) (X i j) := by
  have h := entry_conj hX j i
  rw [h]
  simp

theorem mid_diag_im {X : M3C} (hX : IsSu3R X) :
    (X 1 1).im = -(X 0 0).im - (X 2 2).im := by
  have h := congrArg Complex.im hX.2
  simp [Matrix.trace, Fin.sum_univ_succ] at h
  linarith

/-- Surjectivity: every element of the continuous real su(3) carrier has the
    displayed eight-coordinate form. -/
theorem compactMatrixR_coordinatesR {X : M3C} (hX : IsSu3R X) :
    compactMatrixR (coordinatesR X) = X := by
  have hd0 := diag_re_eq_zero hX 0
  have hd1 := diag_re_eq_zero hX 1
  have hd2 := diag_re_eq_zero hX 2
  have hmid := mid_diag_im hX
  have h10 := lower_of_upper hX 0 1
  have h20 := lower_of_upper hX 0 2
  have h21 := lower_of_upper hX 1 2
  have h10re := congrArg Complex.re h10
  have h10im := congrArg Complex.im h10
  have h20re := congrArg Complex.re h20
  have h20im := congrArg Complex.im h20
  have h21re := congrArg Complex.re h21
  have h21im := congrArg Complex.im h21
  simp at h10re h10im h20re h20im h21re h21im
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [compactMatrixR, coordinatesR] <;>
    linarith

/-- The coordinate map bundled as a real-linear map into the su(3) subspace. -/
def coeffLinearMap : RCoeff8 →ₗ[ℝ] Su3R where
  toFun c := ⟨compactMatrixR c, compactMatrixR_mem c⟩
  map_add' a b := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [compactMatrixR, Complex.ext_iff] <;>
      ring
  map_smul' r a := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [compactMatrixR, Complex.ext_iff, smul_eq_mul] <;>
      ring

theorem coeffLinearMap_injective : Function.Injective coeffLinearMap := by
  intro a b h
  have hval : compactMatrixR a = compactMatrixR b := congrArg Subtype.val h
  calc
    a = coordinatesR (compactMatrixR a) := (coordinatesR_compactMatrixR a).symm
    _ = coordinatesR (compactMatrixR b) := congrArg coordinatesR hval
    _ = b := coordinatesR_compactMatrixR b

theorem coeffLinearMap_surjective : Function.Surjective coeffLinearMap := by
  intro X
  refine ⟨coordinatesR X.1, ?_⟩
  apply Subtype.ext
  exact compactMatrixR_coordinatesR X.2

/-- Main continuous result: the full real su(3) carrier is linearly equivalent
    to eight real coordinates. -/
noncomputable def coeffLinearEquivSu3 : RCoeff8 ≃ₗ[ℝ] Su3R :=
  LinearEquiv.ofBijective coeffLinearMap
    ⟨coeffLinearMap_injective, coeffLinearMap_surjective⟩

/-! ## Lie bracket -/

def bracketR (A B : M3C) : M3C := A * B - B * A

theorem bracketR_mem {A B : M3C} (hA : IsSu3R A) (hB : IsSu3R B) :
    IsSu3R (bracketR A B) := by
  constructor
  · simp only [bracketR, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, hA.1, hB.1]
    noncomm_ring
  · rw [bracketR, Matrix.trace_sub, Matrix.trace_mul_comm A B, sub_self]

/-- The matrix commutator transported to the eight real coordinates. -/
def coeffBracket (a b : RCoeff8) : RCoeff8 :=
  coordinatesR (bracketR (compactMatrixR a) (compactMatrixR b))

theorem compactMatrixR_coeffBracket (a b : RCoeff8) :
    compactMatrixR (coeffBracket a b) =
      bracketR (compactMatrixR a) (compactMatrixR b) := by
  apply compactMatrixR_coordinatesR
  exact bracketR_mem (compactMatrixR_mem a) (compactMatrixR_mem b)

/-! ## The v11 Gaussian lattice embeds into the continuous carrier -/

def ofGInt (z : GInt) : ℂ := (z.re : ℂ) + (z.im : ℂ) * I

def complexifyMatG3 (A : MatG3) : M3C :=
  !![ofGInt A.a00, ofGInt A.a01, ofGInt A.a02;
     ofGInt A.a10, ofGInt A.a11, ofGInt A.a12;
     ofGInt A.a20, ofGInt A.a21, ofGInt A.a22]

def intCoordsToReal (c : Coeff8) : RCoeff8 :=
  ![(c.p : ℝ), (c.q : ℝ),
    (c.u12 : ℝ), (c.v12 : ℝ),
    (c.u13 : ℝ), (c.v13 : ℝ),
    (c.u23 : ℝ), (c.v23 : ℝ)]

theorem complexify_compactMatrix
    (p q u12 v12 u13 v13 u23 v23 : Int) :
    complexifyMatG3 (compactMatrix p q u12 v12 u13 v13 u23 v23) =
      compactMatrixR
        ![(p : ℝ), (q : ℝ),
          (u12 : ℝ), (v12 : ℝ),
          (u13 : ℝ), (v13 : ℝ),
          (u23 : ℝ), (v23 : ℝ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexifyMatG3, ofGInt, compactMatrix, compactMatrixR,
      Complex.ext_iff]

theorem complexify_toMatrix (c : Coeff8) :
    complexifyMatG3 c.toMatrix = compactMatrixR (intCoordsToReal c) := by
  rcases c with ⟨p, q, u12, v12, u13, v13, u23, v23⟩
  simpa [Coeff8.toMatrix, intCoordsToReal] using
    complexify_compactMatrix p q u12 v12 u13 v13 u23 v23

theorem complexify_mem {A : MatG3} (hA : IsSu3Alg A) :
    IsSu3R (complexifyMatG3 A) := by
  obtain ⟨p, q, u12, v12, u13, v13, u23, v23, h⟩ := exists_coords hA
  rw [h, complexify_compactMatrix]
  exact compactMatrixR_mem _

/-! ## Real vector field and actual ODE -/

/-- The real scalar extension of v11's integer coefficient vector field. -/
def adDVec (c : RCoeff8) : RCoeff8 :=
  ![2 * (c 3 - c 5),
    2 * (c 7 - c 5),
    c 4 + c 6,
    -2 * c 0 + c 1 + c 5 - c 7,
    -c 2 + c 6,
    c 0 + c 1 - c 3 + c 7,
    -c 2 - c 4,
    c 0 - 2 * c 1 + c 3 - c 5]

def adDLinear : RCoeff8 →ₗ[ℝ] RCoeff8 where
  toFun := adDVec
  map_add' a b := by
    funext i
    fin_cases i <;> simp [adDVec] <;> ring
  map_smul' r a := by
    funext i
    fin_cases i <;> simp [adDVec] <;> ring

def Dreal : M3C :=
  compactMatrixR ![0, 0, 1, 0, -1, 0, 1, 0]

/-- Independent continuous reconstruction of all eight coefficient equations. -/
theorem bracket_Dreal_coefficients (c : RCoeff8) :
    bracketR Dreal (compactMatrixR c) = compactMatrixR (adDVec c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bracketR, Dreal, compactMatrixR, adDVec,
      Matrix.mul_apply, Fin.sum_univ_succ, Complex.ext_iff] <;>
    ring_nf <;>
    simp

theorem integer_adD_scalar_extension (c : Coeff8) :
    intCoordsToReal (Coeff8.adD c) = adDVec (intCoordsToReal c) := by
  rcases c with ⟨p, q, u12, v12, u13, v13, u23, v23⟩
  funext i
  fin_cases i <;> simp [intCoordsToReal, Coeff8.adD, adDVec]

/-- The three complex off-diagonal coordinates. -/
def z12R (c : RCoeff8) : ℂ := (c 2 : ℂ) + (c 3 : ℂ) * I
def z13R (c : RCoeff8) : ℂ := (c 4 : ℂ) + (c 5 : ℂ) * I
def z23R (c : RCoeff8) : ℂ := (c 6 : ℂ) + (c 7 : ℂ) * I

theorem adDVec_z12R (c : RCoeff8) :
    z12R (adDVec c) =
      z13R c + starRingEnd ℂ (z23R c) + ((-2 * c 0 + c 1 : ℝ) : ℂ) * I := by
  simp [z12R, z13R, z23R, adDVec, Complex.ext_iff]
  ring

theorem adDVec_z13R (c : RCoeff8) :
    z13R (adDVec c) =
      -z12R c + z23R c + ((c 0 + c 1 : ℝ) : ℂ) * I := by
  simp [z12R, z13R, z23R, adDVec, Complex.ext_iff]
  ring

theorem adDVec_z23R (c : RCoeff8) :
    z23R (adDVec c) =
      -starRingEnd ℂ (z12R c) - z13R c + ((c 0 - 2 * c 1 : ℝ) : ℂ) * I := by
  simp [z12R, z13R, z23R, adDVec, Complex.ext_iff]
  ring

/-- Genuine real ODE on the eight-dimensional coefficient space:

      c'(t) = kappa * adDVec(c(t)).

    `HasDerivAt` makes this a calculus statement, unlike the integer vector
    field in the Std-only file. -/
def SolvesNaiveODE (kappa : ℝ) (c : ℝ → RCoeff8) : Prop :=
  ∀ t : ℝ, HasDerivAt c (kappa • adDVec (c t)) t

/-- Equivalent matrix RHS: the coefficient vector field is precisely the
    commutator with the complex anti-Hermitian matrix D. -/
theorem naiveODE_matrix_rhs (kappa : ℝ) (c : RCoeff8) :
    compactMatrixR (kappa • adDVec c) =
      kappa • bracketR Dreal (compactMatrixR c) := by
  rw [bracket_Dreal_coefficients]
  have h := congrArg Subtype.val
    (coeffLinearMap.map_smul kappa (adDVec c))
  change compactMatrixR (kappa • adDVec c) =
    kappa • compactMatrixR (adDVec c) at h
  exact h

#print axioms compactMatrixR_mem
#print axioms compactMatrixR_coordinatesR
#print axioms coeffLinearEquivSu3
#print axioms bracketR_mem
#print axioms complexify_mem
#print axioms bracket_Dreal_coefficients
#print axioms integer_adD_scalar_extension
#print axioms adDVec_z12R
#print axioms adDVec_z13R
#print axioms adDVec_z23R
#print axioms naiveODE_matrix_rhs

end CubeToSU3.Continuous
