import Std
import Lean.Elab.Tactic.Omega

/-!
# Cube → traceless 3×3 algebra: a checked finite core

This module deliberately starts without Mathlib. The 3×3 matrices and
three-vectors are explicit integer objects, so the first layer can be checked
with stock Lean alone. This is sufficient for the exact finite identities
behind the construction.

It proves only mathematical claims. The physical dictionary lives separately
in CubeToSU3.PhysicsInputs.
-/

namespace CubeToSU3

/-- An exact three-component integer vector. -/
structure Vec3 where
  x : Int
  y : Int
  z : Int
deriving Repr, DecidableEq

namespace Vec3

/-- Integer scalar multiplication of a three-vector. -/
def scale (c : Int) (v : Vec3) : Vec3 :=
  ⟨c * v.x, c * v.y, c * v.z⟩

end Vec3

/-- An exact 3×3 integer matrix, written in row-major coordinates. -/
structure Mat3 where
  a00 : Int
  a01 : Int
  a02 : Int
  a10 : Int
  a11 : Int
  a12 : Int
  a20 : Int
  a21 : Int
  a22 : Int
deriving Repr, DecidableEq

namespace Mat3

def zero : Mat3 :=
  ⟨0, 0, 0,
   0, 0, 0,
   0, 0, 0⟩

def add (A B : Mat3) : Mat3 :=
  ⟨A.a00 + B.a00, A.a01 + B.a01, A.a02 + B.a02,
   A.a10 + B.a10, A.a11 + B.a11, A.a12 + B.a12,
   A.a20 + B.a20, A.a21 + B.a21, A.a22 + B.a22⟩

def neg (A : Mat3) : Mat3 :=
  ⟨-A.a00, -A.a01, -A.a02,
   -A.a10, -A.a11, -A.a12,
   -A.a20, -A.a21, -A.a22⟩

def sub (A B : Mat3) : Mat3 :=
  add A (neg B)

def smul (c : Int) (A : Mat3) : Mat3 :=
  ⟨c * A.a00, c * A.a01, c * A.a02,
   c * A.a10, c * A.a11, c * A.a12,
   c * A.a20, c * A.a21, c * A.a22⟩

/-- Ordinary 3×3 matrix multiplication. -/
def mul (A B : Mat3) : Mat3 :=
  ⟨A.a00 * B.a00 + A.a01 * B.a10 + A.a02 * B.a20,
   A.a00 * B.a01 + A.a01 * B.a11 + A.a02 * B.a21,
   A.a00 * B.a02 + A.a01 * B.a12 + A.a02 * B.a22,
   A.a10 * B.a00 + A.a11 * B.a10 + A.a12 * B.a20,
   A.a10 * B.a01 + A.a11 * B.a11 + A.a12 * B.a21,
   A.a10 * B.a02 + A.a11 * B.a12 + A.a12 * B.a22,
   A.a20 * B.a00 + A.a21 * B.a10 + A.a22 * B.a20,
   A.a20 * B.a01 + A.a21 * B.a11 + A.a22 * B.a21,
   A.a20 * B.a02 + A.a21 * B.a12 + A.a22 * B.a22⟩

def mulVec (A : Mat3) (v : Vec3) : Vec3 :=
  ⟨A.a00 * v.x + A.a01 * v.y + A.a02 * v.z,
   A.a10 * v.x + A.a11 * v.y + A.a12 * v.z,
   A.a20 * v.x + A.a21 * v.y + A.a22 * v.z⟩

def trace (A : Mat3) : Int :=
  A.a00 + A.a11 + A.a22

/-- The associative-algebra commutator, the concrete Lie bracket. -/
def commutator (A B : Mat3) : Mat3 :=
  sub (mul A B) (mul B A)

def sum (matrices : List Mat3) : Mat3 :=
  matrices.foldl add zero

end Mat3

/-- The 3×3 identity matrix. -/
def I3 : Mat3 :=
  ⟨1, 0, 0,
   0, 1, 0,
   0, 0, 1⟩

/-- The all-one matrix. -/
def J : Mat3 :=
  ⟨1, 1, 1,
   1, 1, 1,
   1, 1, 1⟩

/-- The cyclic difference matrix. -/
def D : Mat3 :=
  ⟨ 0,  1, -1,
    -1, 0,  1,
     1, -1, 0⟩

/-- The plane x + y + z = 0. -/
def zeroSum (v : Vec3) : Prop :=
  v.x + v.y + v.z = 0

/-- Mathematical core: D² = -3I + J, with no floating-point arithmetic. -/
theorem D_squared :
    Mat3.mul D D = Mat3.add (Mat3.smul (-3) I3) J := by
  decide

/-- D maps the zero-sum plane to itself. -/
theorem D_preserves_zero_sum (v : Vec3) (h : zeroSum v) :
    zeroSum (Mat3.mulVec D v) := by
  cases v with
  | mk x y z =>
    simp [zeroSum, Mat3.mulVec, D] at h ⊢
    omega

/-- On x + y + z = 0, the J term vanishes and D² = -3I. -/
theorem D_squared_on_zero_sum (v : Vec3) (h : zeroSum v) :
    Mat3.mulVec D (Mat3.mulVec D v) = Vec3.scale (-3) v := by
  cases v with
  | mk x y z =>
    simp [zeroSum, Mat3.mulVec, Vec3.scale, D] at h ⊢
    omega

/-!
## Explicit traceless 3×3 seed

The six directed paths Eᵢⱼ, together with the two diagonal commutators H₀₁
and H₁₂, are the eight usual coordinate directions of the traceless 3×3
matrix algebra. At this stage the coefficients are integers; this is the
integral lattice underlying the usual rational, real, or complex version.
-/

def E01 : Mat3 :=
  ⟨0, 1, 0,
   0, 0, 0,
   0, 0, 0⟩

def E02 : Mat3 :=
  ⟨0, 0, 1,
   0, 0, 0,
   0, 0, 0⟩

def E10 : Mat3 :=
  ⟨0, 0, 0,
   1, 0, 0,
   0, 0, 0⟩

def E12 : Mat3 :=
  ⟨0, 0, 0,
   0, 0, 1,
   0, 0, 0⟩

def E20 : Mat3 :=
  ⟨0, 0, 0,
   0, 0, 0,
   1, 0, 0⟩

def E21 : Mat3 :=
  ⟨0, 0, 0,
   0, 0, 0,
   0, 1, 0⟩

def H01 : Mat3 :=
  ⟨1,  0, 0,
   0, -1, 0,
   0,  0, 0⟩

def H12 : Mat3 :=
  ⟨0, 0,  0,
   0, 1,  0,
   0, 0, -1⟩

/-- The two Cartan directions arise from opposite directed paths. -/
theorem H01_from_paths :
    Mat3.commutator E01 E10 = H01 := by
  decide

theorem H12_from_paths :
    Mat3.commutator E12 E21 = H12 := by
  decide

/-- A sample of the A₂ root-path commutators. -/
theorem E01_E12 :
    Mat3.commutator E01 E12 = E02 := by
  decide

theorem E12_E20 :
    Mat3.commutator E12 E20 = E10 := by
  decide

theorem E20_E01 :
    Mat3.commutator E20 E01 = E21 := by
  decide

/-- The two diagonal directions commute. -/
theorem cartan_commutes :
    Mat3.commutator H01 H12 = Mat3.zero := by
  decide

/-- Selected root weights. -/
theorem H01_on_E01 :
    Mat3.commutator H01 E01 = Mat3.smul 2 E01 := by
  decide

theorem H12_on_E12 :
    Mat3.commutator H12 E12 = Mat3.smul 2 E12 := by
  decide

theorem H01_on_E12 :
    Mat3.commutator H01 E12 = Mat3.smul (-1) E12 := by
  decide

theorem H12_on_E01 :
    Mat3.commutator H12 E01 = Mat3.smul (-1) E01 := by
  decide

/-- All eight coordinate matrices have zero trace. -/
theorem basis_trace_zero :
    Mat3.trace H01 = 0 ∧ Mat3.trace H12 = 0 ∧
    Mat3.trace E01 = 0 ∧ Mat3.trace E02 = 0 ∧
    Mat3.trace E10 = 0 ∧ Mat3.trace E12 = 0 ∧
    Mat3.trace E20 = 0 ∧ Mat3.trace E21 = 0 := by
  decide

/-- The explicit eight-coordinate reconstruction of a traceless matrix. -/
def reconstruct (A : Mat3) : Mat3 :=
  Mat3.sum [
    Mat3.smul A.a00 H01,
    Mat3.smul (-A.a22) H12,
    Mat3.smul A.a01 E01,
    Mat3.smul A.a02 E02,
    Mat3.smul A.a10 E10,
    Mat3.smul A.a12 E12,
    Mat3.smul A.a20 E20,
    Mat3.smul A.a21 E21
  ]

/-- Every integer traceless 3×3 matrix has the stated eight coordinates. -/
theorem traceless_coordinate_formula (A : Mat3) (h : Mat3.trace A = 0) :
    reconstruct A = A := by
  cases A with
  | mk a00 a01 a02 a10 a11 a12 a20 a21 a22 =>
    simp [reconstruct, Mat3.sum, Mat3.add, Mat3.smul, Mat3.zero,
      Mat3.trace, H01, H12, E01, E02, E10, E12, E20, E21] at h ⊢
    omega

/-! ## The `1 + 2` decomposition, stated properly

Earlier files refer to `ker D ⊕ im D = 1 ⊕ 2` as though it were a theorem here.
It was not: only `D_preserves_zero_sum` and `D_squared_on_zero_sum` existed, and
the decomposition was left as "easily derived". Here it is, derived.

Over the integers both pieces are characterised exactly. The *direct sum* needs
division by three (splitting `v` into `(s/3)(1,1,1)` plus a zero-sum part), so it
holds over `ℚ` but not over `ℤ`; what is proved integrally is that the two
pieces meet only at zero.
-/

/-- **The kernel is the pole line.** `D v = 0` exactly when all three
coordinates agree, i.e. `v` lies on the `(1,1,1)` axis. -/
theorem kernel_D (v : Vec3) :
    Mat3.mulVec D v = ⟨0, 0, 0⟩ ↔ (v.x = v.y ∧ v.y = v.z) := by
  cases v with
  | mk x y z =>
    constructor <;> intro h <;>
      simp [Mat3.mulVec, D, Vec3.mk.injEq] at h ⊢ <;> omega

/-- **The image is the zero-sum plane**, exactly, over the integers. The witness
for a zero-sum `w` is `(-w.y, w.x, 0)`. -/
theorem image_D (w : Vec3) :
    zeroSum w ↔ ∃ v : Vec3, Mat3.mulVec D v = w := by
  constructor
  · intro h
    refine ⟨⟨-w.y, w.x, 0⟩, ?_⟩
    cases w with
    | mk x y z => simp [zeroSum] at h; simp [Mat3.mulVec, D, Vec3.mk.injEq]; omega
  · rintro ⟨v, rfl⟩
    cases v with
    | mk a b c => simp [zeroSum, Mat3.mulVec, D]; omega

/-- **The two pieces meet only at zero.** A vector on the pole line with zero
coordinate sum must vanish, since `3x = 0`. -/
theorem kernel_meets_image_trivially (v : Vec3)
    (hk : v.x = v.y ∧ v.y = v.z) (hi : zeroSum v) : v = ⟨0, 0, 0⟩ := by
  obtain ⟨h1, h2⟩ := hk
  cases v with
  | mk x y z => simp [zeroSum] at hi; simp [Vec3.mk.injEq] at h1 h2 ⊢; omega

/-- The three integral facts together. Named for what it proves: the kernel is
the diagonal lattice, the image is the zero-sum lattice, and they meet only at
zero.

It is **not** the direct sum statement. Over `ℤ` the two sublattices span only
the index-three sublattice `{v : v.x + v.y + v.z ≡ 0 mod 3}`, since splitting
off the diagonal part needs division by three. The genuine
`ℚ³ = ker D ⊕ im D` with `dim = 1 + 2` needs scalar extension and Mathlib's
`Submodule.IsCompl` and `finrank`; the name `one_plus_two_decomposition` is
reserved for that. -/
theorem integral_kernel_image_structure :
    (∀ v : Vec3, Mat3.mulVec D v = ⟨0,0,0⟩ ↔ (v.x = v.y ∧ v.y = v.z)) ∧
    (∀ w : Vec3, zeroSum w ↔ ∃ v : Vec3, Mat3.mulVec D v = w) ∧
    (∀ v : Vec3, (v.x = v.y ∧ v.y = v.z) → zeroSum v → v = ⟨0,0,0⟩) :=
  ⟨kernel_D, image_D, kernel_meets_image_trivially⟩

end CubeToSU3
