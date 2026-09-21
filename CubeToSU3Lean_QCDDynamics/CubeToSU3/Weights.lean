import CubeToSU3.RootMatch

/-!
# 權圖:從立方體的幾何讀出 3 ⊗ 3 ⊗ 3 = 10 ⊕ 8 ⊕ 8 ⊕ 1

Gell-Mann arrived at the decuplet by algebra on the `SU(3)` generators.  This
file takes the other route: the weights are **points**, the tensor product is
**addition of points**, and the decomposition is read off the resulting picture.
Every statement is an integer-vector identity, checked by kernel reduction.

**Where the weights come from.**  Not postulated — they are already on the cube.
`QianKunAxis` projects the eight vertices along the 乾-坤 diagonal; the six
non-axis ones land on a hexagon, alternating by yao-weight.  The three of
yao-weight one are the weights of the fundamental `3`, the three of yao-weight
two are the weights of `3̄`.  `fund_eq_cube_projection` records this: the
projection is exactly twice `fund`.

Coordinates are scaled by three so that everything is an integer:
`fund i = 3 e_i - (1,1,1)`, which sums to zero over `i`, as tracelessness
requires.

**The picture.**  The 27 weights of `3 ⊗ 3 ⊗ 3` occupy only ten distinct points:

* three outer corners, each once — `(6,-3,-3)` and its permutations;
* six hexagon points, each three times;
* the centre, six times.

Those ten points with those multiplicities are exactly

    10 ⊕ 8 ⊕ 8 ⊕ 1

with the decuplet the symmetric combinations `w_i + w_j + w_k` for `i ≤ j ≤ k`,
each octet the six roots plus two copies of the centre, and the singlet the
centre once more.  `tensor_cube_decomposition` checks the multiplicity of every
point, and `dimension_count` checks `27 = 10 + 8 + 8 + 1`.

**The second bridge.**  The non-zero weights of the octet are the roots, and
`RootMatch` already identified those with the six non-axis cube vertices under
`D`.  `octet_roots_eq_cube_roots` records that the two agree up to the factor of
three carried by this file's scaling.  So both the fundamental and the adjoint
weight diagrams are the cube's own geometry, at different scales.

**What this is not.**  The decomposition holds for any `su(3)`; it is standard
representation theory, not a consequence of the cube.  What the cube supplies is
the *picture* — a specific realisation of the weight lattice in which the
fundamental weights are vertices of a cube seen down its diagonal.  And the
decuplet is a flavour statement: it classifies baryons made of three light
quarks, not anything about the gauge group.

Nothing here is a physical claim.
-/

namespace CubeToSU3.Weight

open CubeToSU3

/-! ## The fundamental weights -/

/-- The three weights of `3`, scaled by three to stay in `Int`:
    `fund i = 3 e_i - (1,1,1)`. -/
def fund : Fin 3 → Vec3
  | 0 => ⟨2, -1, -1⟩
  | 1 => ⟨-1, 2, -1⟩
  | 2 => ⟨-1, -1, 2⟩

/-- The three weights of `3̄`. -/
def antifund (i : Fin 3) : Vec3 := Vec3.scale (-1) (fund i)

def vadd (v w : Vec3) : Vec3 := ⟨v.x + w.x, v.y + w.y, v.z + w.z⟩

def vsub (v w : Vec3) : Vec3 := ⟨v.x - w.x, v.y - w.y, v.z - w.z⟩

/-- Tracelessness: the fundamental weights sum to zero. -/
theorem fund_sum_zero : vadd (vadd (fund 0) (fund 1)) (fund 2) = ⟨0, 0, 0⟩ := by
  decide

/-- **First bridge.**  The fundamental weights are the cube's own vertices seen
    down the 乾-坤 diagonal: vertices `1`, `2`, `4` are the three of yao-weight
    one, and their projection is twice `fund`. -/
theorem fund_eq_cube_projection :
    Axis.proj (Axis.vtx 1) = Vec3.scale 2 (fund 0) ∧
    Axis.proj (Axis.vtx 2) = Vec3.scale 2 (fund 1) ∧
    Axis.proj (Axis.vtx 4) = Vec3.scale 2 (fund 2) := by
  decide

/-- And the three of yao-weight two give `3̄`. -/
theorem antifund_eq_cube_projection :
    Axis.proj (Axis.vtx 6) = Vec3.scale 2 (antifund 0) ∧
    Axis.proj (Axis.vtx 5) = Vec3.scale 2 (antifund 1) ∧
    Axis.proj (Axis.vtx 3) = Vec3.scale 2 (antifund 2) := by
  decide

/-! ## The three pieces -/

/-- The ten weights of the decuplet: `w_i + w_j + w_k` for `i ≤ j ≤ k`. -/
def decupletWeights : List Vec3 :=
  [ vadd (vadd (fund 0) (fund 0)) (fund 0),
    vadd (vadd (fund 0) (fund 0)) (fund 1),
    vadd (vadd (fund 0) (fund 0)) (fund 2),
    vadd (vadd (fund 0) (fund 1)) (fund 1),
    vadd (vadd (fund 0) (fund 1)) (fund 2),
    vadd (vadd (fund 0) (fund 2)) (fund 2),
    vadd (vadd (fund 1) (fund 1)) (fund 1),
    vadd (vadd (fund 1) (fund 1)) (fund 2),
    vadd (vadd (fund 1) (fund 2)) (fund 2),
    vadd (vadd (fund 2) (fund 2)) (fund 2) ]

/-- The eight weights of the adjoint: the six roots `w_i - w_j` and the centre
    twice, the rank of `su(3)` being two. -/
def octetWeights : List Vec3 :=
  [ vsub (fund 0) (fund 1), vsub (fund 0) (fund 2),
    vsub (fund 1) (fund 0), vsub (fund 1) (fund 2),
    vsub (fund 2) (fund 0), vsub (fund 2) (fund 1),
    ⟨0, 0, 0⟩, ⟨0, 0, 0⟩ ]

def singletWeights : List Vec3 := [⟨0, 0, 0⟩]

/-- All 27 weights of `3 ⊗ 3 ⊗ 3`. -/
def tensorWeights : List Vec3 :=
  (List.range 3).flatMap fun i =>
    (List.range 3).flatMap fun j =>
      (List.range 3).map fun k =>
        vadd (vadd (fund ⟨i % 3, by omega⟩) (fund ⟨j % 3, by omega⟩))
          (fund ⟨k % 3, by omega⟩)

/-! ## The decomposition -/

theorem dimension_count :
    tensorWeights.length = 27 ∧ decupletWeights.length = 10 ∧
    octetWeights.length = 8 ∧ singletWeights.length = 1 := by
  decide

theorem dimension_sum : 10 + 8 + 8 + 1 = 27 := by decide

/-- Only ten distinct points occur, with multiplicities `1`, `3` and `6`. -/
theorem tensor_multiplicities :
    tensorWeights.count ⟨6, -3, -3⟩ = 1 ∧
    tensorWeights.count ⟨-3, 6, -3⟩ = 1 ∧
    tensorWeights.count ⟨-3, -3, 6⟩ = 1 ∧
    tensorWeights.count ⟨3, -3, 0⟩ = 3 ∧
    tensorWeights.count ⟨3, 0, -3⟩ = 3 ∧
    tensorWeights.count ⟨-3, 3, 0⟩ = 3 ∧
    tensorWeights.count ⟨0, 3, -3⟩ = 3 ∧
    tensorWeights.count ⟨-3, 0, 3⟩ = 3 ∧
    tensorWeights.count ⟨0, -3, 3⟩ = 3 ∧
    tensorWeights.count ⟨0, 0, 0⟩ = 6 := by
  decide

/-- **The decomposition.**  Every weight of `3 ⊗ 3 ⊗ 3` occurs exactly as often
    as it does in `10 ⊕ 8 ⊕ 8 ⊕ 1`. -/
theorem tensor_cube_decomposition : ∀ w ∈ tensorWeights,
    tensorWeights.count w
      = decupletWeights.count w + 2 * octetWeights.count w
        + singletWeights.count w := by
  decide

/-- Nothing outside the tensor product's support is claimed by the right-hand
    side either, so the two multisets agree everywhere. -/
theorem decomposition_support : ∀ w ∈ decupletWeights ++ octetWeights ++ singletWeights,
    w ∈ tensorWeights := by
  decide

/-! ## The second bridge -/

/-- **The octet's non-zero weights are the cube's roots.**  `RootMatch` sends the
    six non-axis vertices to `e_i - e_j`; here the same six appear as
    `w_i - w_j`, three times as large because of this file's scaling. -/
theorem octet_roots_eq_cube_roots :
    vsub (fund 0) (fund 1) = Vec3.scale 3 (Root.rootOf 3) ∧
    vsub (fund 0) (fund 2) = Vec3.scale 3 (Root.rootOf 2) ∧
    vsub (fund 1) (fund 0) = Vec3.scale 3 (Root.rootOf 4) ∧
    vsub (fund 1) (fund 2) = Vec3.scale 3 (Root.rootOf 6) ∧
    vsub (fund 2) (fund 0) = Vec3.scale 3 (Root.rootOf 5) ∧
    vsub (fund 2) (fund 1) = Vec3.scale 3 (Root.rootOf 1) := by
  decide

/-! ## Axiom audit -/

#print axioms fund_sum_zero
#print axioms fund_eq_cube_projection
#print axioms antifund_eq_cube_projection
#print axioms dimension_count
#print axioms tensor_multiplicities
#print axioms tensor_cube_decomposition
#print axioms octet_roots_eq_cube_roots

end CubeToSU3.Weight
