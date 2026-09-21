import CubeToSU3.Core

/-!
# `D` is a cross product, and `D²` follows from BAC-CAB

`Core.lean` proves `D² = -3I + J` by `decide`: the kernel multiplies the
matrices out and checks nine integers. That verifies the identity without
explaining it.

Here the same identity is *derived*. The key fact is

  `D v = v × 1`,   where `1 = (1,1,1)` is the pole of the cube,

so `D` is not a matrix that happens to square to `-3I + J`. It is the cross
product with a fixed vector, and `D² = -3I + J` is the ordinary BAC-CAB
identity written in matrix form. Three things that were separate observations
in the notes collapse into one:

* `ker D` is the pole axis, because `v × 1 = 0` exactly when `v` is parallel
  to `1`;
* the `J` term is the component along `1`, which is what BAC-CAB leaves behind;
* the amplification factor is `√3` because `|1| = √3`. Not `2 sin 60°`, which
  is a true but roundabout description via the cyclic group.

The cross product needs three dimensions, a metric, and an orientation. None of
those comes from the group algebra of `Z/3`, so this module records the one
place where the ambient `R³` is genuinely doing work.
-/

namespace CubeToSU3

namespace Vec3

def add (u v : Vec3) : Vec3 := ⟨u.x + v.x, u.y + v.y, u.z + v.z⟩

def sub (u v : Vec3) : Vec3 := ⟨u.x - v.x, u.y - v.y, u.z - v.z⟩

/-- The Euclidean inner product. -/
def dot (u v : Vec3) : Int := u.x * v.x + u.y * v.y + u.z * v.z

/-- The cross product. This is where the ambient three-dimensional space, its
metric, and its orientation enter; there is no analogue in the abstract group
algebra. -/
def cross (u v : Vec3) : Vec3 :=
  ⟨u.y * v.z - u.z * v.y,
   u.z * v.x - u.x * v.z,
   u.x * v.y - u.y * v.x⟩

end Vec3

/-- The pole of the cube: the vector fixed by the cyclic shift, the image of the
two vertices that project to the centre. -/
def one3 : Vec3 := ⟨1, 1, 1⟩

/-- **The reformulation.** `D` acts as the cross product with the pole. -/
theorem D_is_cross (v : Vec3) : Mat3.mulVec D v = Vec3.cross v one3 := by
  cases v with
  | mk x y z => simp [Mat3.mulVec, Vec3.cross, D, one3, Vec3.mk.injEq]; omega

/-- The pole has squared length three. This single integer is the source of
every `√3` in the construction. -/
theorem pole_norm_sq : Vec3.dot one3 one3 = 3 := by decide

/-- The all-ones matrix acts as projection onto the pole direction, unnormalised. -/
theorem J_is_pole_component (v : Vec3) :
    Mat3.mulVec J v = Vec3.scale (Vec3.dot one3 v) one3 := by
  cases v with
  | mk x y z => simp [Mat3.mulVec, Vec3.scale, Vec3.dot, J, one3, Vec3.mk.injEq]

/-- **BAC-CAB**, in the bracketed-on-the-left form. Proved for arbitrary
vectors, not just for the ones used below. -/
theorem cross_cross (x y z : Vec3) :
    Vec3.cross (Vec3.cross x y) z =
      Vec3.sub (Vec3.scale (Vec3.dot z x) y) (Vec3.scale (Vec3.dot z y) x) := by
  cases x with
  | mk x1 x2 x3 => cases y with
    | mk y1 y2 y3 => cases z with
      | mk z1 z2 z3 =>
        simp only [Vec3.cross, Vec3.sub, Vec3.scale, Vec3.dot, Vec3.mk.injEq]
        refine ⟨?_, ?_, ?_⟩ <;>
          simp [Int.sub_eq_add_neg, Int.neg_mul, Int.mul_neg, Int.mul_add, Int.add_mul,
            Int.mul_assoc, Int.mul_left_comm, Int.mul_comm,
            Int.add_left_comm, Int.add_comm] <;> omega

/-- Matrix product acts as composition on vectors. -/
theorem mulVec_mul (A B : Mat3) (v : Vec3) :
    Mat3.mulVec (Mat3.mul A B) v = Mat3.mulVec A (Mat3.mulVec B v) := by
  cases A with
  | mk _ _ _ _ _ _ _ _ _ => cases B with
    | mk _ _ _ _ _ _ _ _ _ => cases v with
      | mk _ _ _ =>
        simp only [Mat3.mulVec, Mat3.mul, Vec3.mk.injEq]
        refine ⟨?_, ?_, ?_⟩ <;>
          simp [Int.sub_eq_add_neg, Int.neg_mul, Int.mul_neg, Int.mul_add, Int.add_mul,
            Int.mul_assoc, Int.mul_left_comm, Int.mul_comm,
            Int.add_left_comm, Int.add_comm] <;> omega

/-- **The derivation.** `D² v = J v - 3 v` follows from BAC-CAB and
`|1|² = 3`. No matrix entries are multiplied out; this is the same identity
`Core.D_squared` checks numerically, obtained instead by reasoning. -/
theorem D_squared_from_cross (v : Vec3) :
    Mat3.mulVec (Mat3.mul D D) v =
      Vec3.sub (Mat3.mulVec J v) (Vec3.scale 3 v) := by
  rw [mulVec_mul, D_is_cross, D_is_cross, cross_cross, J_is_pole_component]
  cases v with
  | mk x y z => simp [Vec3.sub, Vec3.scale, Vec3.dot, one3, Vec3.mk.injEq]

/-- On the plane through the pole's orthogonal complement the `J` term drops
out, leaving `D² = -3`. The `-3` is `-|1|²`. -/
theorem D_squared_on_plane_from_cross (v : Vec3) (h : Vec3.dot one3 v = 0) :
    Mat3.mulVec (Mat3.mul D D) v = Vec3.scale (-3) v := by
  rw [D_squared_from_cross, J_is_pole_component, h]
  cases v with
  | mk x y z => simp [Vec3.sub, Vec3.scale, one3, Vec3.mk.injEq]

/-- The kernel is the pole axis, because a cross product vanishes exactly on
parallel vectors. Stated concretely for the pole itself. -/
theorem pole_in_kernel : Mat3.mulVec D one3 = ⟨0, 0, 0⟩ := by decide

/-! ## The orientation `Z₂`

A cross product depends on a choice of orientation. Under a reflection it picks
up a sign, and so therefore does `D`, and so does the chirality operator
`Γ₅ = iD/√3` of `Cube.lean`.

This locates something the graph-theoretic picture cannot see. Bipartiteness
explains why a chirality operator *exists*; only the ambient orientation
explains where its *sign* comes from. The `C₆` replacement test in
`Hexagon.lean` compares graphs, and a graph has forgotten its embedding, so
that test is blind to this.

It remains true that the index is zero either way. An orientation supplies a
sign, not an index.
-/

/-- The reflection swapping the first two coordinates. -/
def refl : Mat3 :=
  ⟨0, 1, 0,
   1, 0, 0,
   0, 0, 1⟩

theorem refl_involutive : Mat3.mul refl refl = I3 := by decide

/-- A reflection reverses the cross product: `R u × R v = -R(u × v)`. This is
the `det R = -1` factor, and it is the origin of the sign of the chirality
operator. -/
theorem refl_reverses_cross (u v : Vec3) :
    Vec3.cross (Mat3.mulVec refl u) (Mat3.mulVec refl v) =
      Mat3.mulVec refl (Vec3.scale (-1) (Vec3.cross u v)) := by
  cases u with
  | mk u1 u2 u3 => cases v with
    | mk v1 v2 v3 =>
      simp only [Vec3.cross, Vec3.scale, Mat3.mulVec, refl, Vec3.mk.injEq]
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [Int.sub_eq_add_neg, Int.neg_mul, Int.mul_neg, Int.mul_add, Int.add_mul,
            Int.mul_assoc, Int.mul_left_comm, Int.mul_comm,
            Int.add_left_comm, Int.add_comm] <;> omega

/-- Consequently the reflection conjugates `D` into `-D`, which is why parity
flips chirality. -/
theorem refl_conjugates_D : Mat3.mul refl (Mat3.mul D refl) = Mat3.neg D := by
  decide

end CubeToSU3
