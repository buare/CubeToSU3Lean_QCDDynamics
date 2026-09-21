/-
  SU3Global.lean

  Global topological-group structure and one-parameter subgroups for SU(3).

  Scope
  -----
  Proved here, without `sorry`, `admit`, or custom axioms:
  * the matrix carrier called `SU3` in `SU3Group.lean` is an actual group;
  * inversion is conjugate transpose and is continuous;
  * hence `SU3` is a Hausdorff topological group;
  * the ambient matrix exponential is complex analytic and real smooth;
  * every X in su(3) gives a continuous one-parameter subgroup of SU(3).

  Not proved here:
  * a smooth-manifold structure on the subtype `SU3`;
  * surjectivity of `expSU3`;
  * compactness or simple connectedness;
  * gauge fields, Yang--Mills dynamics, quantisation, or QCD.

  The surjectivity theorem needs a unitary spectral theorem plus a branch-adjusted
  logarithm whose three eigenangles sum to zero.  Mathlib 4.16 contains the
  Hermitian spectral theorem used in `SU3Group.lean`, but not that normal/unitary
  spectral theorem in a directly reusable matrix form.
-/

import CubeToSU3.SU3Group
import Mathlib.Geometry.Manifold.Algebra.LieGroup

noncomputable section

set_option maxHeartbeats 4000000

open Matrix Complex BigOperators
open scoped ContDiff

namespace CubeToSU3.Continuous

section LinftyTopology

local instance : SeminormedRing M3C := Matrix.linftyOpSemiNormedRing
local instance : NormedRing M3C := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℂ M3C := Matrix.linftyOpNormedAlgebra

/-! ## The actual group structure -/

/-- Inversion in SU(3) is conjugate transpose. -/
def su3Inv (A : SU3) : SU3 :=
  ⟨star A.1, by
    refine ⟨unitary.star_mem A.2.1, ?_⟩
    change Matrix.det A.1ᴴ = 1
    rw [Matrix.det_conjTranspose]
    have hdet : Matrix.det A.1 = 1 := A.2.2
    rw [hdet]
    simp⟩

/-- Mathlib 4.16 represents `specialUnitaryGroup` as a submonoid of the
    matrix monoid.  This instance supplies the inverse and proves the group
    law using unitarity. -/
instance su3Group : Group SU3 :=
  { inferInstanceAs (Monoid SU3) with
    inv := su3Inv
    inv_mul_cancel := fun A => by
      apply Subtype.ext
      exact A.2.1.1 }

@[simp] theorem coe_su3_inv (A : SU3) :
    ((A⁻¹ : SU3) : M3C) = star (A : M3C) := rfl

/-- Inversion is continuous because conjugate transpose is continuous. -/
instance su3ContinuousInv : ContinuousInv SU3 where
  continuous_inv := by
    change Continuous su3Inv
    exact (continuous_star.comp continuous_subtype_val).subtype_mk _

/-- SU(3), with the subtype topology inherited from complex matrices, is a
    topological group. -/
instance su3TopologicalGroup : TopologicalGroup SU3 where
  continuous_mul := continuous_mul
  continuous_inv := continuous_inv

theorem su3_isHausdorff : T2Space SU3 := inferInstance

/-! ## Analyticity and smoothness in the ambient matrix space -/

/-- The matrix exponential is complex analytic on all complex 3 by 3
    matrices. -/
theorem analytic_exp_ambient_complex :
    AnalyticOnNhd ℂ (NormedSpace.exp ℂ : M3C → M3C) Set.univ :=
  fun X _ => NormedSpace.exp_analytic X

/-- After restriction of scalars, the ambient matrix exponential is infinitely
    differentiable as a real map.  This is an ambient statement; it is not yet
    a manifold-smoothness statement about the subtype `SU3`. -/
theorem smooth_exp_ambient_real :
    ContDiff ℝ ∞ (NormedSpace.exp ℂ : M3C → M3C) :=
  analytic_exp_ambient_complex.restrictScalars.contDiff

/-! ## Exponential identities inside SU(3) -/

theorem expSU3_add_of_commute (X Y : Su3R)
    (hXY : Commute (X.1 : M3C) Y.1) :
    expSU3 (X + Y) = expSU3 X * expSU3 Y := by
  apply Subtype.ext
  exact NormedSpace.exp_add_of_commute hXY

@[simp] theorem expSU3_neg (X : Su3R) :
    expSU3 (-X) = (expSU3 X)⁻¹ := by
  apply Subtype.ext
  change NormedSpace.exp ℂ (-X.1) = (NormedSpace.exp ℂ X.1)ᴴ
  rw [← Matrix.exp_conjTranspose ℂ X.1, X.2.1]

theorem smul_commute_self (a b : ℝ) (X : Su3R) :
    Commute (((a : ℂ) • X.1) : M3C) ((b : ℂ) • X.1) := by
  rw [Commute]
  calc
    ((a : ℂ) • X.1) * ((b : ℂ) • X.1) =
        ((a : ℂ) * b) • (X.1 * X.1) := by rw [smul_mul_smul_comm]
    _ = ((b : ℂ) * a) • (X.1 * X.1) := by rw [mul_comm (a : ℂ) b]
    _ = ((b : ℂ) • X.1) * ((a : ℂ) • X.1) := by rw [smul_mul_smul_comm]

/-- The exponential curve associated with X. -/
def expLine (X : Su3R) (t : ℝ) : SU3 := expSU3 (t • X)

@[simp] theorem expLine_zero (X : Su3R) : expLine X 0 = 1 := by
  simp [expLine]

theorem expLine_add (X : Su3R) (s t : ℝ) :
    expLine X (s + t) = expLine X s * expLine X t := by
  unfold expLine
  rw [add_smul]
  apply expSU3_add_of_commute
  exact smul_commute_self s t X

/-- The additive real line maps homomorphically to SU(3).  `Multiplicative ℝ`
    is used only to present addition as the source multiplication expected by
    `MonoidHom`. -/
def oneParameterSubgroup (X : Su3R) : Multiplicative ℝ →* SU3 where
  toFun t := expLine X t.toAdd
  map_one' := expLine_zero X
  map_mul' s t := expLine_add X s.toAdd t.toAdd

@[simp] theorem oneParameterSubgroup_apply (X : Su3R) (t : Multiplicative ℝ) :
    oneParameterSubgroup X t = expLine X t.toAdd := rfl

/-- Every Lie-algebra element gives a continuous one-parameter subgroup. -/
theorem continuous_expLine (X : Su3R) : Continuous (expLine X) := by
  unfold expLine
  exact continuous_expSU3.comp (continuous_id.smul continuous_const)

/-! ## Precise statements of the next two global gaps -/

/-- The exact global exponential-surjectivity statement still to be proved. -/
def ExponentialSurjective : Prop := Function.Surjective expSU3

/-- Data that would witness the requested eight-dimensional smooth Lie-group
    structure.  It is a specification, not an asserted instance. -/
structure SmoothLieGroupWitness where
  I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 8))
        (EuclideanSpace ℝ (Fin 8))
  charted : ChartedSpace (EuclideanSpace ℝ (Fin 8)) SU3
  lie : letI := charted; LieGroup I ∞ SU3

/-- The exact smooth-Lie-group existence proposition still to be proved. -/
def HasSmoothLieGroupStructure : Prop := Nonempty SmoothLieGroupWitness

/-! ## Axiom audit -/

#print axioms coe_su3_inv
#print axioms su3_isHausdorff
#print axioms analytic_exp_ambient_complex
#print axioms smooth_exp_ambient_real
#print axioms expSU3_add_of_commute
#print axioms expSU3_neg
#print axioms expLine_add
#print axioms continuous_expLine

end LinftyTopology

end CubeToSU3.Continuous
