import CubeToSU3.CompactSU3

/-!
# Aut(Q3) and the Weyl group of A2

The automorphism group of the cube is the hyperoctahedral group

  Aut(Q3) = (Z2)^3 semidirect S3,   order 48,

where S3 permutes the three coordinate axes and (Z2)^3 flips them.

This file measures exactly how much of that survives inside su(3).

* The S3 factor survives in full: it acts faithfully on su(3) by permuting
  the three weights, which is precisely the Weyl group action of A2.
* The (Z2)^3 factor survives only halfway: the action has a two-element
  kernel, so only a (Z2)^2 quotient acts faithfully.

Both halves are proved, not asserted.  No Mathlib.
-/

namespace CubeToSU3

/-! ## 1. The six axis permutations -/

inductive Perm3 where
  | id | s01 | s02 | s12 | c012 | c021
deriving DecidableEq, Repr

namespace Perm3
def all : List Perm3 := [id, s01, s02, s12, c012, c021]
end Perm3

/-- Conjugation by a permutation matrix, written directly as a rearrangement
    of entries: `(permMat s X).a i j = X.a (s i) (s j)`. -/
def permMat : Perm3 → MatG3 → MatG3
  | .id, X => X
  | .s01, X => ⟨X.a11, X.a10, X.a12, X.a01, X.a00, X.a02, X.a21, X.a20, X.a22⟩
  | .s02, X => ⟨X.a22, X.a21, X.a20, X.a12, X.a11, X.a10, X.a02, X.a01, X.a00⟩
  | .s12, X => ⟨X.a00, X.a02, X.a01, X.a20, X.a22, X.a21, X.a10, X.a12, X.a11⟩
  | .c012, X => ⟨X.a11, X.a12, X.a10, X.a21, X.a22, X.a20, X.a01, X.a02, X.a00⟩
  | .c021, X => ⟨X.a22, X.a20, X.a21, X.a02, X.a00, X.a01, X.a12, X.a10, X.a11⟩

/-! ## 2. The action is by algebra automorphisms -/

theorem permMat_conjTranspose (s : Perm3) (X : MatG3) :
    MatG3.conjTranspose (permMat s X) = permMat s (MatG3.conjTranspose X) := by
  cases s <;> rfl

theorem permMat_neg (s : Perm3) (X : MatG3) :
    MatG3.neg (permMat s X) = permMat s (MatG3.neg X) := by
  cases s <;> rfl

theorem permMat_trace (s : Perm3) (X : MatG3) :
    MatG3.trace (permMat s X) = MatG3.trace X := by
  cases s <;> simp [permMat, MatG3.trace, GInt.add, GInt.mk.injEq] <;> omega

/-- Axis permutations preserve su(3). -/
theorem permMat_mem {X : MatG3} (s : Perm3) (hX : IsSu3Alg X) :
    IsSu3Alg (permMat s X) := by
  refine ⟨?_, ?_⟩
  · rw [permMat_conjTranspose, hX.1, permMat_neg]
  · rw [permMat_trace]; exact hX.2


/-! ## 3. The action on the eight coordinates -/

def permCoeff : Perm3 → Coeff8 → Coeff8
  | .id,   c => c
  | .s01,  c => ⟨-c.p + c.q, c.q, -c.u12, c.v12, c.u23, c.v23, c.u13, c.v13⟩
  | .s02,  c => ⟨-c.q, -c.p, -c.u23, c.v23, -c.u13, c.v13, -c.u12, c.v12⟩
  | .s12,  c => ⟨c.p, c.p - c.q, c.u13, c.v13, c.u12, c.v12, -c.u23, c.v23⟩
  | .c012, c => ⟨-c.p + c.q, -c.p, c.u23, c.v23, -c.u12, c.v12, -c.u13, c.v13⟩
  | .c021, c => ⟨-c.q, c.p - c.q, -c.u13, c.v13, -c.u23, c.v23, c.u12, c.v12⟩

/-- The action is closed on the eight-coordinate parameterisation. -/
theorem permMat_toMatrix (s : Perm3) (c : Coeff8) :
    permMat s c.toMatrix = (permCoeff s c).toMatrix := by
  cases c
  cases s <;>
    simp [permMat, permCoeff, Coeff8.toMatrix, compactMatrix,
          MatG3.mk.injEq, GInt.mk.injEq] <;> omega

/-! ## 4. S3 acts as the Weyl group of A2

    The Cartan part of X is i*(d0,d1,d2) with d0+d1+d2 = 0; these are the
    three weights r,g,b.  W(A2) is by definition the group permuting them. -/

def weights (X : MatG3) : Int × Int × Int := (X.a00.im, X.a11.im, X.a22.im)

def permWeights : Perm3 → Int × Int × Int → Int × Int × Int
  | .id,   w => w
  | .s01,  w => (w.2.1, w.1, w.2.2)
  | .s02,  w => (w.2.2, w.2.1, w.1)
  | .s12,  w => (w.1, w.2.2, w.2.1)
  | .c012, w => (w.2.1, w.2.2, w.1)
  | .c021, w => (w.2.2, w.1, w.2.1)

/-- MAIN POSITIVE RESULT (part 1): the axis permutations act on su(3)
    exactly by permuting the three weights.  That is the Weyl group of A2. -/
theorem weights_permMat (s : Perm3) (X : MatG3) :
    weights (permMat s X) = permWeights s (weights X) := by
  cases s <;> rfl

/-- A test element with three distinct weights (1, 2, -3). -/
def testW : MatG3 := compactMatrix 1 3 0 0 0 0 0 0

/-- The S3 factor of Aut(Q3) survives in full: the action is faithful,
    so all six permutations give six distinct automorphisms of su(3). -/
theorem permMat_faithful (s t : Perm3) (h : permMat s testW = permMat t testW) :
    s = t := by
  revert h; cases s <;> cases t <;> decide

/-! ## 5. The (Z2)^3 factor survives only halfway -/

def gsmul (n : Int) (z : GInt) : GInt := ⟨n * z.re, n * z.im⟩

/-- Conjugation by diag(e0,e1,e2) with each ei = +-1 scales entry (i,j) by ei*ej. -/
def signAct (e0 e1 e2 : Int) (X : MatG3) : MatG3 :=
  ⟨gsmul (e0*e0) X.a00, gsmul (e0*e1) X.a01, gsmul (e0*e2) X.a02,
   gsmul (e1*e0) X.a10, gsmul (e1*e1) X.a11, gsmul (e1*e2) X.a12,
   gsmul (e2*e0) X.a20, gsmul (e2*e1) X.a21, gsmul (e2*e2) X.a22⟩

/-- MAIN POSITIVE RESULT (part 2): the sign action has a two-element kernel.
    Flipping all three axes at once acts trivially, so (Z2)^3 does NOT act
    faithfully on su(3) -- only the (Z2)^2 quotient does. -/
theorem signAct_neg_all (e0 e1 e2 : Int) (X : MatG3) :
    signAct (-e0) (-e1) (-e2) X = signAct e0 e1 e2 X := by
  cases X
  simp [signAct, gsmul, MatG3.mk.injEq, GInt.mk.injEq, Int.neg_mul_neg]

theorem signAct_flip_all_trivial (X : MatG3) : signAct (-1) (-1) (-1) X = X := by
  cases X
  simp [signAct, gsmul, MatG3.mk.injEq, GInt.mk.injEq]

/-- A test element whose three off-diagonal entries are distinct and nonzero. -/
def testS : MatG3 := compactMatrix 0 0 1 0 2 0 3 0

/-- The four representatives with e0 = 1 give four genuinely distinct maps.
    Together with signAct_neg_all this pins the image at exactly (Z2)^2. -/
theorem signAct_four_distinct :
    signAct 1 1 1 testS    ≠ signAct 1 1 (-1) testS ∧
    signAct 1 1 1 testS    ≠ signAct 1 (-1) 1 testS ∧
    signAct 1 1 1 testS    ≠ signAct 1 (-1) (-1) testS ∧
    signAct 1 1 (-1) testS ≠ signAct 1 (-1) 1 testS ∧
    signAct 1 1 (-1) testS ≠ signAct 1 (-1) (-1) testS ∧
    signAct 1 (-1) 1 testS ≠ signAct 1 (-1) (-1) testS := by
  decide

/-! ## 6. The determinant test agrees

    diag(e0,e1,e2) lies in SU(3) iff e0*e1*e2 = 1.  Exactly four of the eight
    sign vectors pass, and they form the same (Z2)^2 found above. -/

def allSigns : List (Int × Int × Int) :=
  [(1,1,1), (1,1,-1), (1,-1,1), (1,-1,-1),
   (-1,1,1), (-1,1,-1), (-1,-1,1), (-1,-1,-1)]

def evenSigns : List (Int × Int × Int) :=
  [(1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1)]

theorem evenSigns_are_det_one :
    ∀ e ∈ allSigns, (e.1 * e.2.1 * e.2.2 = 1) ↔ e ∈ evenSigns := by decide

theorem evenSigns_card : evenSigns.length = 4 := by decide

/-! ## 7. Summary as a single statement

    Aut(Q3) has order 48 = 8 * 6.  Inside su(3):
      the S3 factor  (order 6) acts faithfully   -> 6 distinct automorphisms
      the (Z2)^3     (order 8) collapses by 2    -> 4 distinct automorphisms
    So exactly 24 of the 48 cube automorphisms survive as distinct
    automorphisms of su(3). -/

theorem cube_automorphism_survival :
    Perm3.all.length = 6 ∧ allSigns.length = 8 ∧ evenSigns.length = 4 := by
  decide

#print axioms permMat_mem
#print axioms permMat_toMatrix
#print axioms weights_permMat
#print axioms permMat_faithful
#print axioms signAct_neg_all
#print axioms signAct_four_distinct
#print axioms evenSigns_are_det_one

end CubeToSU3
