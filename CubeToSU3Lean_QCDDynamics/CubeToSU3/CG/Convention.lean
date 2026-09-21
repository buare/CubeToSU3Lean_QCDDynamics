/-!
# SU(3) Clebsch–Gordan layer: conventions

Everything in this module is exact integer arithmetic over `Fin 3`.
No Mathlib, no square roots.

## Conventions fixed here

* Basis of the fundamental representation `3`: `u = 0`, `d = 1`, `s = 2`.
  These are the three weight-one vertices of the unit cube.
* Levi-Civita symbol with `ε(u,d,s) = +1`.
* States are kept **unnormalised** as integer vectors. A normalised state is
  the integer vector divided by the square root of its (integer) norm, so every
  structural statement (invariance, orthogonality, symmetry) is already
  decided at the integer level.
* Weights are the cube vertices projected along the body diagonal, scaled by 3:
  `w_u = (2,-1,-1)`, `w_d = (-1,2,-1)`, `w_s = (-1,-1,2)`.
-/

namespace CubeToSU3.CG

/-- Flavour index: `0 = u`, `1 = d`, `2 = s`. -/
abbrev Idx := Fin 3

def u : Idx := 0
def d : Idx := 1
def s : Idx := 2

/-- Explicit sum over the three indices, kept literal for cheap kernel reduction. -/
def sum3 (f : Idx → Int) : Int := f 0 + f 1 + f 2

/-- Kronecker delta. -/
def delta (i j : Idx) : Int := if i = j then 1 else 0

/-! ## Levi-Civita symbol -/

/-- `ε(i,j,k)`: `+1` on even permutations of `(0,1,2)`, `-1` on odd ones, `0` otherwise. -/
def eps (i j k : Idx) : Int :=
  match i.val, j.val, k.val with
  | 0, 1, 2 => 1
  | 1, 2, 0 => 1
  | 2, 0, 1 => 1
  | 0, 2, 1 => -1
  | 2, 1, 0 => -1
  | 1, 0, 2 => -1
  | _, _, _ => 0

/-- The phase convention. -/
theorem eps_uds : eps u d s = 1 := by decide

/-- Antisymmetry in the last two slots. -/
theorem eps_antisymm_23 : ∀ i j k : Idx, eps i j k = - eps i k j := by decide

/-- Antisymmetry in the first two slots. -/
theorem eps_antisymm_12 : ∀ i j k : Idx, eps i j k = - eps j i k := by decide

/-- Cyclic invariance. -/
theorem eps_cyclic : ∀ i j k : Idx, eps i j k = eps j k i := by decide

/-- The contraction identity `Σ_k ε_kij ε_kmn = δ_im δ_jn - δ_in δ_jm`.
This single identity is what makes the antisymmetric part of `3 ⊗ 3`
a copy of `3̄`. -/
theorem eps_contract :
    ∀ i j m n : Idx,
      sum3 (fun k => eps k i j * eps k m n)
        = delta i m * delta j n - delta i n * delta j m := by decide

/-! ## Matrices and generators

`gl(3)` is spanned by the nine matrix units `E a b`. Every statement below is
proved for all nine, hence by linearity for every integer matrix, and in
particular for the eight traceless generators of `su(3)`. -/

/-- A 3×3 integer matrix. -/
abbrev Mat := Idx → Idx → Int

/-- Matrix unit: the directed path that moves the occupied coordinate `b` to `a`. -/
def E (a b : Idx) : Mat := fun i j => delta i a * delta j b

def trace (T : Mat) : Int := sum3 (fun i => T i i)

theorem trace_E : ∀ a b : Idx, trace (E a b) = delta a b := by decide

/-! ## Representation spaces -/

/-- A vector in `3` (or `3̄`). -/
abbrev Vec := Idx → Int

/-- A vector in `3 ⊗ 3` or `3 ⊗ 3̄`: `t i j` is the coefficient of `|i⟩ ⊗ |j⟩`. -/
abbrev Ten := Idx → Idx → Int

/-- Basis tensor `|m n⟩`. -/
def ket (m n : Idx) : Ten := fun i j => delta i m * delta j n

/-- Integer inner product on `3 ⊗ 3`. -/
def dot (x y : Ten) : Int := sum3 (fun i => sum3 (fun j => x i j * y i j))

def Ten.add (x y : Ten) : Ten := fun i j => x i j + y i j
def Ten.smul (c : Int) (x : Ten) : Ten := fun i j => c * x i j
def Ten.zero : Ten := fun _ _ => 0

/-- Action of `T` on the fundamental: `(T v)_i = Σ_j T_ij v_j`. -/
def act3 (T : Mat) (v : Vec) : Vec := fun i => sum3 (fun j => T i j * v j)

/-- Action of `T` on `3 ⊗ 3`: `T ⊗ 1 + 1 ⊗ T`. -/
def act33 (T : Mat) (t : Ten) : Ten :=
  fun i j => sum3 (fun m => T i m * t m j) + sum3 (fun n => T j n * t i n)

/-- Action of `T` on `3 ⊗ 3̄`: `T ⊗ 1 + 1 ⊗ (-Tᵀ)`. -/
def act33bar (T : Mat) (t : Ten) : Ten :=
  fun i j => sum3 (fun m => T i m * t m j) - sum3 (fun n => T n j * t i n)

/-! ## Weights

A weight is stored as an integer triple with zero sum. -/

structure Wt where
  x : Int
  y : Int
  z : Int
deriving DecidableEq, Repr

def Wt.add (p q : Wt) : Wt := ⟨p.x + q.x, p.y + q.y, p.z + q.z⟩
def Wt.neg (p : Wt) : Wt := ⟨-p.x, -p.y, -p.z⟩
def Wt.zero : Wt := ⟨0, 0, 0⟩

/-- The three weights of `3`, i.e. the projected weight-one cube vertices (×3). -/
def w : Idx → Wt
  | ⟨0, _⟩ => ⟨2, -1, -1⟩
  | ⟨1, _⟩ => ⟨-1, 2, -1⟩
  | ⟨2, _⟩ => ⟨-1, -1, 2⟩

/-- The three weights sum to zero: the projection kills the body diagonal. -/
theorem weights_sum_zero : ((w u).add (w d)).add (w s) = Wt.zero := by decide

/-- Every weight has zero coordinate sum, i.e. lies on the plane `x + y + z = 0`. -/
theorem weights_traceless : ∀ i : Idx, (w i).x + (w i).y + (w i).z = 0 := by decide

end CubeToSU3.CG
