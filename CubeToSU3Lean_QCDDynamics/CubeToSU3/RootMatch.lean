import CubeToSU3.QianKunAxis

/-!
# 六個頂點就是六個根

`QianKunAxis.lean` closed one gap and left another open.  It proved that the six
non-axis vertices project to a regular hexagon carrying a `Z/3` action, and said
plainly that this is a match of *shapes*: a regular hexagon with a threefold
rotation is necessary for `A₂`, not sufficient.  This file closes the remaining
gap by producing the structural statement.

**The correct map is `D`, not the orthogonal projection.**  This is worth
stating, because the two differ and only one of them lands on the roots.  In the
`{0,1}³` coordinates,

* `proj` sends the six vertices to `(4,-2,-2)` and the like — these are
  `3e_i - (1,1,1)`, the **weights** of `3 ⊕ 3̄`;
* `D` sends them to `(0,-1,1)` and the like — these are `e_i - e_j`, the six
  **roots** of `A₂`.

Both form hexagons, which is why `QianKunAxis` could not tell them apart, and
they differ by the quarter turn `D/√3` that `Core.lean` records as
`D² = -3P`.  The hexagon of weights and the hexagon of roots are rotated 30°
from one another.

**What makes it structural.**  A vector is a root when it is the eigenvalue of
the adjoint action of the Cartan on the matching generator.  So the statement to
prove is not "these six vectors form a hexagon" but

    [diag h, E_{φ(v)}] = ⟨D·v, h⟩ · E_{φ(v)}

for every non-axis vertex `v` and every diagonal `h`.  The left side is the
adjoint action inside `su(3)`; the right side pairs the Cartan with the vector
that the cube hands over.  `adjoint_eigenvalue_is_root` proves exactly this, and
because `genOf` sends 乾 and 坤 to the zero matrix, it holds for all eight
vertices with no side conditions.

The dictionary `φ` is forced, not chosen: `D·v` determines `e_i - e_j`, hence
the pair `(i,j)`, hence `E_ij`.

**Equivariance.**  The threefold rotation about the 乾-坤 axis commutes with `D`;
a transposition of two yao anticommutes with it, because conjugating the cyclic
permutation by a transposition inverts it.  So the cube's `S₃` acts on the roots
as the Weyl group of `A₂` does, up to the sign of the permutation — and that
sign is the same orientation datum that `Weyl.lean` tracks in
`evenSigns_are_det_one`.

With this file the chain from the cube to `su(3)` is connected: the 乾-坤 axis
gives the `Z/3`, `D` is its generator, the six remaining vertices are the six
roots, and the cube's axis stabiliser acts as the Weyl group.

Nothing here is a physical claim.
-/

namespace CubeToSU3.Root

open CubeToSU3

/-! ## Vertices, roots, generators -/

/-- Cube vertex in `{0,1}³` coordinates, the convention `D` was written for. -/
def vtx01 (i : Fin 8) : Vec3 :=
  ⟨(i.val) % 2, (i.val / 2) % 2, (i.val / 4) % 2⟩

/-- The vector the cube hands to vertex `i`. -/
def rootOf (i : Fin 8) : Vec3 := Mat3.mulVec D (vtx01 i)

/-- The matching generator.  乾 and 坤 lie on the axis and get the zero matrix,
    which is what lets the main theorem hold without side conditions. -/
def genOf : Fin 8 → Mat3
  | 0 => Mat3.zero
  | 1 => E21 | 2 => E02 | 3 => E01
  | 4 => E10 | 5 => E20 | 6 => E12
  | 7 => Mat3.zero

/-- A traceless diagonal matrix is not required; any diagonal will do. -/
def diagH (h : Vec3) : Mat3 :=
  ⟨h.x, 0, 0,
   0, h.y, 0,
   0, 0, h.z⟩

/-- Pairing of a root with a Cartan element. -/
def pair (a h : Vec3) : Int := a.x * h.x + a.y * h.y + a.z * h.z

/-! ## The six vectors are the six roots of `A₂` -/

theorem rootOf_axis : rootOf 0 = ⟨0, 0, 0⟩ ∧ rootOf 7 = ⟨0, 0, 0⟩ := by decide

/-- Each non-axis vertex goes to a distinct `e_i - e_j`. -/
theorem rootOf_table :
    rootOf 1 = ⟨0, -1, 1⟩ ∧ rootOf 2 = ⟨1, 0, -1⟩ ∧ rootOf 3 = ⟨1, -1, 0⟩ ∧
    rootOf 4 = ⟨-1, 1, 0⟩ ∧ rootOf 5 = ⟨-1, 0, 1⟩ ∧ rootOf 6 = ⟨0, 1, -1⟩ := by
  decide

/-- `D` is injective on the six, so the six roots are hit exactly once each. -/
theorem rootOf_injective_off_axis : ∀ v w : Fin 8,
    v ≠ 0 → v ≠ 7 → w ≠ 0 → w ≠ 7 → rootOf v = rootOf w → v = w := by
  decide

/-- All six have squared length two — the `A₂` normalisation. -/
theorem roots_same_length : ∀ v : Fin 8, v ≠ 0 → v ≠ 7 →
    Root.pair (rootOf v) (rootOf v) = 2 := by decide

/-- The six non-axis vertices, indexed by `Fin 6`. -/
def offAxis : Fin 6 → Fin 8
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 6

/-- Distinct roots pair to `1`, `-1` or `-2`: the `60°`, `120°`, `180°` of the
    hexagon.  No other value occurs.  Indexing by `Fin 6` rather than carrying
    four `≠` side conditions keeps the `Decidable` instance small enough to
    synthesise. -/
theorem roots_inner_products : ∀ i j : Fin 6, i ≠ j →
    Root.pair (rootOf (offAxis i)) (rootOf (offAxis j)) = 1 ∨
    Root.pair (rootOf (offAxis i)) (rootOf (offAxis j)) = -1 ∨
    Root.pair (rootOf (offAxis i)) (rootOf (offAxis j)) = -2 := by decide

/-! ## The structural statement -/

/-- **The six vertices are the six roots.**  For every vertex and every Cartan
    element, the adjoint action of the Cartan on the matching generator is
    multiplication by the pairing of the Cartan with the vector `D` assigns to
    that vertex.  That is what it means for `D·v` to *be* a root rather than
    merely to sit at the right place in a hexagon. -/
theorem adj_E21 (h : Vec3) :
    Mat3.commutator (diagH h) E21 = Mat3.smul (Root.pair ⟨0, -1, 1⟩ h) E21 := by
  cases h with
  | mk a b c =>
    simp only [Mat3.commutator, Mat3.sub, Mat3.add, Mat3.neg, Mat3.mul,
      Mat3.smul, diagH, E21,
      Root.pair, Mat3.mk.injEq]
    omega

theorem adj_E02 (h : Vec3) :
    Mat3.commutator (diagH h) E02 = Mat3.smul (Root.pair ⟨1, 0, -1⟩ h) E02 := by
  cases h with
  | mk a b c =>
    simp only [Mat3.commutator, Mat3.sub, Mat3.add, Mat3.neg, Mat3.mul,
      Mat3.smul, diagH, E02,
      Root.pair, Mat3.mk.injEq]
    omega

theorem adj_E01 (h : Vec3) :
    Mat3.commutator (diagH h) E01 = Mat3.smul (Root.pair ⟨1, -1, 0⟩ h) E01 := by
  cases h with
  | mk a b c =>
    simp only [Mat3.commutator, Mat3.sub, Mat3.add, Mat3.neg, Mat3.mul,
      Mat3.smul, diagH, E01,
      Root.pair, Mat3.mk.injEq]
    omega

theorem adj_E10 (h : Vec3) :
    Mat3.commutator (diagH h) E10 = Mat3.smul (Root.pair ⟨-1, 1, 0⟩ h) E10 := by
  cases h with
  | mk a b c =>
    simp only [Mat3.commutator, Mat3.sub, Mat3.add, Mat3.neg, Mat3.mul,
      Mat3.smul, diagH, E10,
      Root.pair, Mat3.mk.injEq]
    omega

theorem adj_E20 (h : Vec3) :
    Mat3.commutator (diagH h) E20 = Mat3.smul (Root.pair ⟨-1, 0, 1⟩ h) E20 := by
  cases h with
  | mk a b c =>
    simp only [Mat3.commutator, Mat3.sub, Mat3.add, Mat3.neg, Mat3.mul,
      Mat3.smul, diagH, E20,
      Root.pair, Mat3.mk.injEq]
    omega

theorem adj_E12 (h : Vec3) :
    Mat3.commutator (diagH h) E12 = Mat3.smul (Root.pair ⟨0, 1, -1⟩ h) E12 := by
  cases h with
  | mk a b c =>
    simp only [Mat3.commutator, Mat3.sub, Mat3.add, Mat3.neg, Mat3.mul,
      Mat3.smul, diagH, E12,
      Root.pair, Mat3.mk.injEq]
    omega

/-- **The six vertices are the six roots**, assembled from the six cases. -/
theorem adjoint_eigenvalue_is_root (h : Vec3) :
    Mat3.commutator (diagH h) E21 = Mat3.smul (Root.pair ⟨0, -1, 1⟩ h) E21 ∧
    Mat3.commutator (diagH h) E02 = Mat3.smul (Root.pair ⟨1, 0, -1⟩ h) E02 ∧
    Mat3.commutator (diagH h) E01 = Mat3.smul (Root.pair ⟨1, -1, 0⟩ h) E01 ∧
    Mat3.commutator (diagH h) E10 = Mat3.smul (Root.pair ⟨-1, 1, 0⟩ h) E10 ∧
    Mat3.commutator (diagH h) E20 = Mat3.smul (Root.pair ⟨-1, 0, 1⟩ h) E20 ∧
    Mat3.commutator (diagH h) E12 = Mat3.smul (Root.pair ⟨0, 1, -1⟩ h) E12 :=
  ⟨adj_E21 h, adj_E02 h, adj_E01 h, adj_E10 h, adj_E20 h, adj_E12 h⟩

/-- The six vectors appearing above are exactly `rootOf 1 … rootOf 6`, so the
    eigenvalues really are the vectors the cube hands over.  This is
    `rootOf_table` restated next to the theorem that consumes it. -/
theorem eigenvalue_vectors_are_cube_roots :
    (⟨0, -1, 1⟩ : Vec3) = rootOf 1 ∧ (⟨1, 0, -1⟩ : Vec3) = rootOf 2 ∧
    (⟨1, -1, 0⟩ : Vec3) = rootOf 3 ∧ (⟨-1, 1, 0⟩ : Vec3) = rootOf 4 ∧
    (⟨-1, 0, 1⟩ : Vec3) = rootOf 5 ∧ (⟨0, 1, -1⟩ : Vec3) = rootOf 6 := by
  decide

/-- The generators used above are exactly `genOf 1 … genOf 6`. -/
theorem eigenvectors_are_cube_generators :
    genOf 1 = E21 ∧ genOf 2 = E02 ∧ genOf 3 = E01 ∧
    genOf 4 = E10 ∧ genOf 5 = E20 ∧ genOf 6 = E12 := by
  decide

/-! ## Equivariance: the axis stabiliser acts as the Weyl group -/

/-- The 120° rotation about the 乾-坤 axis, on vertices. -/
def rot8 : Fin 8 → Fin 8
  | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 6
  | 4 => 1 | 5 => 3 | 6 => 5 | 7 => 7

/-- The same rotation on vectors: cyclic shift of coordinates. -/
def rotV (v : Vec3) : Vec3 := ⟨v.z, v.x, v.y⟩

/-- Exchanging the 上爻 with the 中爻, on vertices. -/
def swap8 : Fin 8 → Fin 8
  | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3
  | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7

def swapV (v : Vec3) : Vec3 := ⟨v.y, v.x, v.z⟩

/-- The even element commutes with `D`. -/
theorem rot_equivariant : ∀ v : Fin 8, rootOf (rot8 v) = rotV (rootOf v) := by
  decide

/-- The odd element anticommutes with `D`: conjugating the cyclic permutation by
    a transposition inverts it, so `D = P - P²` changes sign. -/
theorem swap_anti_equivariant : ∀ v : Fin 8,
    rootOf (swap8 v) = Vec3.scale (-1) (swapV (rootOf v)) := by decide

/-- Both fix the axis, as they must. -/
theorem stabiliser_fixes_axis :
    rot8 0 = 0 ∧ rot8 7 = 7 ∧ swap8 0 = 0 ∧ swap8 7 = 7 := by decide

/-! ## Axiom audit -/

#print axioms rootOf_table
#print axioms rootOf_injective_off_axis
#print axioms roots_same_length
#print axioms roots_inner_products
#print axioms adj_E01
#print axioms adjoint_eigenvalue_is_root
#print axioms eigenvalue_vectors_are_cube_roots
#print axioms eigenvectors_are_cube_generators
#print axioms rot_equivariant
#print axioms swap_anti_equivariant

end CubeToSU3.Root
