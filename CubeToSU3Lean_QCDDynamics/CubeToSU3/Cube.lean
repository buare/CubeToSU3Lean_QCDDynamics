import CubeToSU3.Core

/-!
# The cube itself: group algebra, chirality, and a checked no-go

Core.lean proved facts about `D` as a bare 3×3 integer matrix. This module
adds three things that were missing from the ledger:

1. `D` is not an arbitrary matrix. It is the unique (up to scale) real
   antisymmetric element of the group algebra of the cyclic group of order 3.
   Everything downstream of `D` therefore descends from that cyclic group, not
   from the eight vertices.

2. The cube graph carries an intrinsic chirality operator `S`, the parity of
   the Hamming weight, which anticommutes with the hopping operator `A`.

3. That chirality operator has vanishing index: `A` has trivial kernel, so
   there are no zero modes of either chirality. This is a no-go, not a gap.

All statements are exact integer identities, checked by kernel reduction.
-/

namespace CubeToSU3

/-! ## Part 1: the cyclic group of order three -/

/-- The cyclic shift of the three coordinates. -/
def P : Mat3 :=
  ⟨0, 1, 0,
   0, 0, 1,
   1, 0, 0⟩

theorem P_cubed : Mat3.mul P (Mat3.mul P P) = I3 := by decide

/-- The cyclic difference matrix is an element of the group algebra of Z/3. -/
theorem D_eq_P_sub_P_sq : D = Mat3.sub P (Mat3.mul P P) := by decide

/-- Transpose, needed to state antisymmetry. -/
def Mat3.transpose (A : Mat3) : Mat3 :=
  ⟨A.a00, A.a10, A.a20,
   A.a01, A.a11, A.a21,
   A.a02, A.a12, A.a22⟩

/-- A general element `a·I + b·P + c·P²` of the integral group algebra. -/
def groupAlgebra (a b c : Int) : Mat3 :=
  Mat3.add (Mat3.smul a I3)
    (Mat3.add (Mat3.smul b P) (Mat3.smul c (Mat3.mul P P)))

/-- `D` is the group-algebra element with coefficients `(0, 1, -1)`. -/
theorem D_as_group_algebra : groupAlgebra 0 1 (-1) = D := by decide

/-- **Uniqueness.** Inside the group algebra of Z/3 the antisymmetry condition
forces `a = 0` and `b = -c`. So `D` is the unique antisymmetric element up to
an integer scale: it is canonical, not a choice. -/
theorem antisymmetric_group_algebra_unique (a b c : Int)
    (h : Mat3.transpose (groupAlgebra a b c) = Mat3.neg (groupAlgebra a b c)) :
    a = 0 ∧ b = -c := by
  simp [Mat3.transpose, groupAlgebra, Mat3.add, Mat3.smul, Mat3.neg,
    Mat3.mul, I3, P, Mat3.mk.injEq] at h
  omega

/-- Consequently every antisymmetric group-algebra element is a multiple of `D`. -/
theorem antisymmetric_is_multiple_of_D (a b c : Int)
    (h : Mat3.transpose (groupAlgebra a b c) = Mat3.neg (groupAlgebra a b c)) :
    groupAlgebra a b c = Mat3.smul b D := by
  obtain ⟨ha, hbc⟩ := antisymmetric_group_algebra_unique a b c h
  subst ha
  have hc : c = -b := by omega
  subst hc
  simp [groupAlgebra, Mat3.add, Mat3.smul, Mat3.mul, I3, P, D, Mat3.mk.injEq]

/-! ## Part 2: the cube graph and its chirality operator

Vertices are the eight three-bit patterns, encoded as `Fin 8`. Two vertices are
adjacent exactly when they differ in one bit, which is axiom G2.
-/

/-- Hamming weight of a three-bit vertex label. -/
def weight (i : Fin 8) : Nat :=
  i.val % 2 + (i.val / 2) % 2 + (i.val / 4) % 2

/-- The adjacency (hopping) operator of the cube. -/
def A (i j : Fin 8) : Int :=
  let d := i.val ^^^ j.val
  if d = 1 ∨ d = 2 ∨ d = 4 then 1 else 0

/-- The chirality operator: the sign of the Hamming-weight parity. -/
def S (i : Fin 8) : Int :=
  if weight i % 2 = 0 then 1 else -1

/-- The cube is bipartite, so its hopping operator anticommutes with `S`.
This is the discrete form of `{γ⁵, γ^μ ∂_μ} = 0`. -/
theorem S_anticommutes_A : ∀ i j : Fin 8, S i * A i j + A i j * S j = 0 := by
  decide

/-- The two chirality sectors of the cube have four vertices each. -/
theorem sectors_balanced :
    (List.finRange 8).countP (fun i => S i == 1) = 4 ∧
    (List.finRange 8).countP (fun i => S i == -1) = 4 := by
  decide

/-! ## Part 3: the index vanishes

The characteristic identity `A⁴ = 10 A² - 9 I` says the spectrum of `A` lies in
`{±1, ±3}`, so zero is not an eigenvalue. Every zero mode is therefore zero,
and both chiral kernels are trivial: the index is `0 - 0 = 0`.
-/

/-- Matrix product on `Fin 8 → Fin 8 → Int`, written out to keep kernel
reduction cheap. -/
def mul8 (M N : Fin 8 → Fin 8 → Int) (i j : Fin 8) : Int :=
  M i 0 * N 0 j + M i 1 * N 1 j + M i 2 * N 2 j + M i 3 * N 3 j +
  M i 4 * N 4 j + M i 5 * N 5 j + M i 6 * N 6 j + M i 7 * N 7 j

def mulVec8 (M : Fin 8 → Fin 8 → Int) (v : Fin 8 → Int) (i : Fin 8) : Int :=
  M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 + M i 3 * v 3 +
  M i 4 * v 4 + M i 5 * v 5 + M i 6 * v 6 + M i 7 * v 7

def id8 (i j : Fin 8) : Int := if i = j then 1 else 0

/-- An explicit eight-component integer vector, so that the kernel statement
can be discharged by linear integer arithmetic without Mathlib. -/
structure Vec8 where
  v0 : Int
  v1 : Int
  v2 : Int
  v3 : Int
  v4 : Int
  v5 : Int
  v6 : Int
  v7 : Int
deriving Repr, DecidableEq

/-- The hopping operator acting on a vector, written out from the cube's
neighbour lists: vertex `i` is joined to the three vertices differing in one
bit. -/
def hop (v : Vec8) : Vec8 :=
  ⟨v.v1 + v.v2 + v.v4,
   v.v0 + v.v3 + v.v5,
   v.v0 + v.v3 + v.v6,
   v.v1 + v.v2 + v.v7,
   v.v0 + v.v5 + v.v6,
   v.v1 + v.v4 + v.v7,
   v.v2 + v.v4 + v.v7,
   v.v3 + v.v5 + v.v6⟩

/-- Reading a `Vec8` as a function on the eight vertices. -/
def ofVec8 (v : Vec8) : Fin 8 → Int
  | 0 => v.v0 | 1 => v.v1 | 2 => v.v2 | 3 => v.v3
  | 4 => v.v4 | 5 => v.v5 | 6 => v.v6 | 7 => v.v7

/-- `hop` really is the action of the adjacency matrix `A`, so the kernel
statement below is a statement about `A` and not about a hand-written stand-in. -/
theorem hop_is_A (v : Vec8) : ofVec8 (hop v) = mulVec8 A (ofVec8 v) := by
  funext i
  match i with
  | 0 => simp (config := {decide := true}) [ofVec8, hop, mulVec8, A]
  | 1 => simp (config := {decide := true}) [ofVec8, hop, mulVec8, A]
  | 2 => simp (config := {decide := true}) [ofVec8, hop, mulVec8, A]
  | 3 => simp (config := {decide := true}) [ofVec8, hop, mulVec8, A]
  | 4 => simp (config := {decide := true}) [ofVec8, hop, mulVec8, A]
  | 5 => simp (config := {decide := true}) [ofVec8, hop, mulVec8, A]
  | 6 => simp (config := {decide := true}) [ofVec8, hop, mulVec8, A]
  | 7 => simp (config := {decide := true}) [ofVec8, hop, mulVec8, A]

def Vec8.zero : Vec8 := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- **No zero modes.** The cube's hopping operator has trivial kernel, so the
spectrum misses zero entirely. -/
theorem cube_kernel_trivial (v : Vec8) (h : hop v = Vec8.zero) :
    v = Vec8.zero := by
  cases v with
  | mk v0 v1 v2 v3 v4 v5 v6 v7 =>
    simp [hop, Vec8.zero, Vec8.mk.injEq] at h ⊢
    omega

/-- **The index no-go.** Both chiral sectors contain only the zero vector, so
the chiral index of the cube is `0 - 0 = 0`.

By the bipartite index theorem the index of any hopping operator on a bipartite
graph equals the difference of the two sector sizes, independently of the edge
weights or phases; `sectors_balanced` shows that difference is zero here. So no
choice of phases -- in particular nothing licensed by axiom A4 -- can make the
cube chiral. -/
theorem cube_index_zero (v : Vec8) (h : hop v = Vec8.zero) :
    v.v0 = 0 ∧ v.v1 = 0 ∧ v.v2 = 0 ∧ v.v3 = 0 ∧
    v.v4 = 0 ∧ v.v5 = 0 ∧ v.v6 = 0 ∧ v.v7 = 0 := by
  have := cube_kernel_trivial v h
  subst this
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part 4: the weight criterion

Appendix E's filter says any claimed dimensionless prediction must be invariant
under a common rescaling of every cube-derived matrix. The candidate
`rho(A) * sqrt(Tr A^2)` is not: it is homogeneous of degree two. A single
integer witness settles it.
-/

def trace8 (M : Fin 8 → Fin 8 → Int) : Int :=
  M 0 0 + M 1 1 + M 2 2 + M 3 3 + M 4 4 + M 5 5 + M 6 6 + M 7 7

def smul8 (c : Int) (M : Fin 8 → Fin 8 → Int) (i j : Fin 8) : Int := c * M i j

theorem trace_A_sq : trace8 (mul8 A A) = 24 := by decide

theorem trace_A_four : trace8 (mul8 (mul8 A A) (mul8 A A)) = 168 := by decide

/-- Doubling the matrix quadruples `Tr A^2`, so `sqrt(Tr A^2)` has weight one.
Together with the linear scaling of the spectral radius, the candidate
`rho(A) * sqrt(Tr A^2) = 6 * sqrt 6` has weight two, and therefore cannot be a
ratio of two vacuum expectation values, which must have weight zero. -/
theorem trace_sq_has_weight_two :
    trace8 (mul8 (smul8 2 A) (smul8 2 A)) = 4 * trace8 (mul8 A A) := by
  decide

/-- A weight-zero invariant, by contrast, is unchanged by the same rescaling.
Here `Tr A^4 / (Tr A^2)^2 = 168 / 576 = 7 / 24`, stated without division. -/
theorem weight_zero_invariant :
    24 * trace8 (mul8 (mul8 A A) (mul8 A A)) =
      7 * (trace8 (mul8 A A) * trace8 (mul8 A A)) := by
  decide

theorem weight_zero_is_scale_invariant :
    24 * trace8 (mul8 (mul8 (smul8 2 A) (smul8 2 A)) (mul8 (smul8 2 A) (smul8 2 A))) =
      7 * (trace8 (mul8 (smul8 2 A) (smul8 2 A)) *
           trace8 (mul8 (smul8 2 A) (smul8 2 A))) := by
  decide

end CubeToSU3
