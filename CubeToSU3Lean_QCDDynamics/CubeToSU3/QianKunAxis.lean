import CubeToSU3.Cube

/-!
# 乾-坤 軸:立方體與 su(3) 的第一道橋

Up to now the project has had two branches that never met.  The algebraic
branch — `Core → CompactSU3 → CompactSU3Real → SU3Group` — is built entirely on
the `3 × 3` matrix `D = P - P²`, a cyclic object living on `Z/3`.  The discrete
branch — `Cube → ClosedWalks / Flavour / YouNian` — is built on the eight-vertex
hypercube `Q₃`.  No file on the algebraic branch imports `Cube.lean`, so nothing
in the `su(3)` construction has ever depended on the cube.

This file supplies the missing geometric link, and it is entirely elementary:
**project the cube along its 乾-坤 body diagonal.**

Put the cube in centred coordinates, each yao contributing `+1` for 陽 and `-1`
for 陰, so 乾 is `(1,1,1)` and 坤 is `(-1,-1,-1)`.  The body diagonal through
them is the direction `d = (1,1,1)`.  Orthogonal projection onto the plane
`x + y + z = 0` — the very plane `Core.lean` already singles out as `zeroSum` —
sends

* 乾 and 坤 to the origin, and
* the remaining six vertices to a regular hexagon.

Scaling by three keeps everything in `Int`: `proj v = 3 v - ⟨v,d⟩ d`.  Then
every hexagon vertex has `‖proj v‖² = 24`, adjacent ones have inner product
`12` (that is `24 cos 60°`), next-nearest `-12` (`120°`), antipodal `-24`.

Three further facts make the identification with `A₂` more than a shape match.

* The cyclic order `1, 3, 2, 6, 4, 5` alternates between vertices of yao-weight
  one and two.  The two alternating triangles are the pictures of the `3` and
  the `3̄`.
* `P`, the cyclic permutation of coordinates, is the 120° rotation about the
  乾-坤 axis.  It fixes 乾 and 坤 and splits the hexagon into exactly those two
  triangles: `(1 2 4)` and `(3 6 5)`.
* `D = P - P²` is the infinitesimal generator of that rotation:
  `D v = v × d`.  This is where `Core.lean`'s seed matrix comes from.

So the `Z/3` that generates `su(3)` is not imported from outside — it is the
rotation about the 乾-坤 diagonal of the cube, and the plane `zeroSum` is the
root plane of `A₂`.

**What this file does not claim.**  A regular hexagon carrying a `Z/3` action is
necessary for `A₂`, not sufficient.  Showing that the six vertices *are* the six
roots requires a map intertwining the cube's symmetry action with the adjoint
action of `su(3)`, and that is not proved here.  Until that is done this is a
match of shapes, not of structures.  `WeylReal.lean`'s `cubeActSu3LinearEquiv`
is the natural place to attempt it.

Nothing here is a physical claim.
-/

namespace CubeToSU3.Axis

open CubeToSU3

/-! ## Centred coordinates -/

/-- The cube vertex `i` in centred coordinates: bit `0` is 上爻, bit `1` is
    中爻, bit `2` is 下爻, with 陽 contributing `+1` and 陰 `-1`. -/
def vtx (i : Fin 8) : Vec3 :=
  ⟨2 * ((i.val) % 2) - 1,
   2 * ((i.val / 2) % 2) - 1,
   2 * ((i.val / 4) % 2) - 1⟩

/-- 坤, all yin. -/
theorem vtx_kun : vtx 0 = ⟨-1, -1, -1⟩ := by decide

/-- 乾, all yang. -/
theorem vtx_qian : vtx 7 = ⟨1, 1, 1⟩ := by decide

/-- The 乾-坤 body diagonal. -/
def axisD : Vec3 := ⟨1, 1, 1⟩

def dot (v w : Vec3) : Int := v.x * w.x + v.y * w.y + v.z * w.z

/-- Orthogonal projection onto the plane `x + y + z = 0`, scaled by three so
    that it stays inside `Int`. -/
def proj (v : Vec3) : Vec3 :=
  ⟨3 * v.x - dot v axisD, 3 * v.y - dot v axisD, 3 * v.z - dot v axisD⟩

/-- The projected coordinates sum to zero.  Stated on the bare `Int` equation
    so that `decide` can find a `Decidable` instance: `zeroSum` is a plain
    `def ... : Prop`, and instance search does not unfold it. -/
theorem proj_sum_zero : ∀ i : Fin 8,
    (proj (vtx i)).x + (proj (vtx i)).y + (proj (vtx i)).z = 0 := by decide

/-- The projection does land in `Core.lean`'s zero-sum plane.  `zeroSum` is by
    definition that same equation, so this is a definitional restatement. -/
theorem proj_zeroSum (i : Fin 8) : zeroSum (proj (vtx i)) := proj_sum_zero i

/-! ## 乾 and 坤 are the axis; the other six form a hexagon -/

theorem proj_kun : proj (vtx 0) = ⟨0, 0, 0⟩ := by decide

theorem proj_qian : proj (vtx 7) = ⟨0, 0, 0⟩ := by decide

/-- Exactly 乾 and 坤 collapse to the origin. -/
theorem proj_eq_zero_iff : ∀ i : Fin 8,
    proj (vtx i) = ⟨0, 0, 0⟩ ↔ (i = 0 ∨ i = 7) := by decide

/-- The hexagon, in cyclic order. -/
def hex : Fin 6 → Fin 8
  | 0 => 1 | 1 => 3 | 2 => 2
  | 3 => 6 | 4 => 4 | 5 => 5

/-- All six lie on one circle. -/
theorem hex_equidistant : ∀ k : Fin 6,
    dot (proj (vtx (hex k))) (proj (vtx (hex k))) = 24 := by decide

/-- Adjacent vertices subtend 60°: the inner product is `24 · cos 60° = 12`. -/
theorem hex_adjacent : ∀ k : Fin 6,
    dot (proj (vtx (hex k))) (proj (vtx (hex ⟨(k.val + 1) % 6, by omega⟩))) = 12 := by
  decide

/-- Next-nearest subtend 120°. -/
theorem hex_next_nearest : ∀ k : Fin 6,
    dot (proj (vtx (hex k))) (proj (vtx (hex ⟨(k.val + 2) % 6, by omega⟩))) = -12 := by
  decide

/-- Opposite vertices are antipodal. -/
theorem hex_antipodal : ∀ k : Fin 6,
    dot (proj (vtx (hex k))) (proj (vtx (hex ⟨(k.val + 3) % 6, by omega⟩))) = -24 := by
  decide

/-- Number of yang yao in a vertex. -/
def yaoWeight (i : Fin 8) : Nat :=
  i.val % 2 + (i.val / 2) % 2 + (i.val / 4) % 2

/-- Going round the hexagon, yao-weight alternates between one and two.  The
    two alternating triangles are the pictures of the `3` and the `3̄`. -/
theorem hex_weight_alternates : ∀ k : Fin 6,
    yaoWeight (hex k) % 2 ≠ yaoWeight (hex ⟨(k.val + 1) % 6, by omega⟩) % 2 := by
  decide

theorem hex_weight_one_or_two : ∀ k : Fin 6,
    yaoWeight (hex k) = 1 ∨ yaoWeight (hex k) = 2 := by decide

/-! ## The rotation about the axis, and where `D` comes from -/

/-- Cyclic permutation of the coordinates: the 120° rotation about 乾-坤. -/
def rotP : Fin 8 → Fin 8
  | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 6
  | 4 => 1 | 5 => 3 | 6 => 5 | 7 => 7

/-- The rotation fixes both ends of the axis. -/
theorem rotP_fixes_axis : rotP 0 = 0 ∧ rotP 7 = 7 := by decide

/-- It is a rotation of order three. -/
theorem rotP_order_three : ∀ i : Fin 8, rotP (rotP (rotP i)) = i := by decide

/-- On coordinates, `rotP` really is the cyclic shift. -/
theorem rotP_cycles_coords : ∀ i : Fin 8,
    vtx (rotP i) = ⟨(vtx i).z, (vtx i).x, (vtx i).y⟩ := by decide

/-- The hexagon splits into the two triangles `(1 2 4)` and `(3 6 5)` — the
    yao-weight-one and yao-weight-two vertices. -/
theorem rotP_triangles :
    rotP 1 = 2 ∧ rotP 2 = 4 ∧ rotP 4 = 1 ∧
    rotP 3 = 6 ∧ rotP 6 = 5 ∧ rotP 5 = 3 := by decide

/-- **The seed matrix is the generator of the axial rotation.**  `Core.lean`
    writes `D` down by hand; this identifies it as the infinitesimal rotation
    about the 乾-坤 diagonal, since `D v = v × (1,1,1)`. -/
theorem D_is_cross_with_axis (v : Vec3) :
    Mat3.mulVec D v =
      ⟨v.y * axisD.z - v.z * axisD.y,
       v.z * axisD.x - v.x * axisD.z,
       v.x * axisD.y - v.y * axisD.x⟩ := by
  cases v with
  | mk x y z => simp [Mat3.mulVec, D, axisD, Vec3.mk.injEq]; omega

/-! ## Axiom audit -/

#print axioms proj_sum_zero
#print axioms proj_zeroSum
#print axioms proj_eq_zero_iff
#print axioms hex_equidistant
#print axioms hex_adjacent
#print axioms hex_antipodal
#print axioms hex_weight_alternates
#print axioms hex_weight_one_or_two
#print axioms rotP_cycles_coords
#print axioms rotP_triangles
#print axioms D_is_cross_with_axis

end CubeToSU3.Axis
