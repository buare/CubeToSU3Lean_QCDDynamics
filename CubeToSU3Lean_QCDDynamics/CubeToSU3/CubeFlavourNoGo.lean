import CubeToSU3.Cube

/-!
# The cube's rotation group as a candidate flavour symmetry, and why it fails

`WeylReal.lean` computes the hand-built signed-permutation group: order 48,
kernel 2, image 24.  That order-24 image is the rotation group of the cube,
abstractly `S₄`, and `S₄` really is a finite subgroup of `SO(3) ⊂ SU(3)`.
Finite subgroups of `SU(3)` — `A₄`, `S₄`, `Δ(27)` — are used in the published
discrete-flavour-symmetry literature to constrain fermion mass matrices, so
asking whether the cube's own copy of `S₄` does the same is a fair question.

This module answers it, negatively, for the unbroken symmetry.

The candidate mechanism is the standard one: let the three generations carry
the three-dimensional irreducible representation of `S₄`, here realised by
integer matrices, and require the mass matrix `M` to be invariant, i.e. to
commute with the whole group.  `S4_commutant_scalar` below shows that the two
generators already force

    M = c • I₃

for a single integer `c`.  By Schur's lemma this is exactly what had to happen:
the three-dimensional representation is irreducible, so its commutant is
one-dimensional.  The physical reading is that an *unbroken* `S₄` acting this
way predicts three exactly degenerate generations.

That is a no-go, not a gap.  The observed hierarchy is enormous —
`m_τ/m_e ≈ 3477`, `m_t/m_u ≈ 8·10⁴` — so no amount of tuning inside the
invariant ansatz can reproduce it.  Any flavour model built on this group must
therefore *break* it, and every prediction then comes from the chosen breaking
pattern and vacuum alignment, not from the cube.  The cube supplies the group;
the group alone supplies degeneracy.

What is *not* ruled out: broken `S₄`, where the symmetry constrains mixing
angles rather than mass ratios.  That route is open, but it is the generic
discrete-flavour route and owes nothing to the cube beyond the group itself,
which any cube — or any octahedron — would have supplied.

All statements are exact integer identities.
-/

namespace CubeToSU3.FlavourNoGo

/-! ## Two generators of the cube's rotation group

`rot3` is the 3-cycle of the coordinate axes (a 120° rotation about a body
diagonal); `rot4` is a 90° rotation about the `z` axis.  Together they generate
the full order-24 rotation group, and each has determinant `+1`. -/

/-- 120° rotation about the body diagonal: cyclic permutation of the axes. -/
def rot3 : Mat3 :=
  ⟨0, 1, 0,
   0, 0, 1,
   1, 0, 0⟩

/-- 90° rotation about the `z` axis: swap `x` and `y` with one sign flip. -/
def rot4 : Mat3 :=
  ⟨0, -1, 0,
   1,  0, 0,
   0,  0, 1⟩

theorem rot3_order_three : Mat3.mul rot3 (Mat3.mul rot3 rot3) = I3 := by decide

theorem rot4_order_four :
    Mat3.mul rot4 (Mat3.mul rot4 (Mat3.mul rot4 rot4)) = I3 := by decide

/-- The two generators do not commute, so the group they generate is nonabelian
    and in particular is not a product of cyclic factors. -/
theorem generators_noncommuting :
    Mat3.mul rot3 rot4 ≠ Mat3.mul rot4 rot3 := by decide

/-! ## The commutant is one-dimensional -/

/-- Invariance of a mass matrix under the flavour group. -/
def Invariant (M : Mat3) : Prop :=
  Mat3.mul rot3 M = Mat3.mul M rot3 ∧ Mat3.mul rot4 M = Mat3.mul M rot4

/-- **The flavour no-go.**  A mass matrix invariant under the cube's rotation
group is a scalar.  Only the two generators are used, so the conclusion holds a
fortiori for the full order-24 group. -/
theorem S4_commutant_scalar (M : Mat3) (h : Invariant M) :
    M = Mat3.smul M.a00 I3 := by
  obtain ⟨h3, h4⟩ := h
  cases M with
  | mk a00 a01 a02 a10 a11 a12 a20 a21 a22 =>
    simp [Mat3.mul, rot3, rot4, Mat3.smul, I3, Mat3.mk.injEq] at h3 h4 ⊢
    omega

/-- Restated as exact degeneracy of the three diagonal entries: an invariant
mass matrix assigns the same mass to all three generations. -/
theorem invariant_forces_degeneracy (M : Mat3) (h : Invariant M) :
    M.a11 = M.a00 ∧ M.a22 = M.a00 ∧
    M.a01 = 0 ∧ M.a02 = 0 ∧ M.a10 = 0 ∧
    M.a12 = 0 ∧ M.a20 = 0 ∧ M.a21 = 0 := by
  obtain ⟨h3, h4⟩ := h
  cases M with
  | mk a00 a01 a02 a10 a11 a12 a20 a21 a22 =>
    simp [Mat3.mul, rot3, rot4, Mat3.mk.injEq] at h3 h4 ⊢
    omega

/-! ## Axiom audit -/

#print axioms rot3_order_three
#print axioms rot4_order_four
#print axioms generators_noncommuting
#print axioms S4_commutant_scalar
#print axioms invariant_forces_degeneracy

end CubeToSU3.FlavourNoGo
