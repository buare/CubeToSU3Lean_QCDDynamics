import CubeToSU3.QCDDynamics

/-!
# Dimensionless toy flow versus physically calibrated dynamics

This module keeps two logically different insertions separate.

1. A single nonzero scale `kappa` multiplying the homogeneous eight-component
   toy flow can be divided out.  It calibrates the time/energy unit but does
   not change the dimensionless vector-field direction.
2. The QCD coupling `g_s` changes the relative coefficient of the derivative
   and commutator pieces of the curvature.  It therefore cannot in general be
   removed by one global rescaling once the full field equation is present.

The PDG number below is deliberately encoded as declared data, not as a
theorem derived from the cube.  The exact Lean theorem uses the central value
`alpha_s(M_Z^2)=0.1180`; provenance and uncertainty remain documentary data.

No `sorry`, `admit`, or new custom axiom is used.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Matrix Complex BigOperators

namespace CubeToSU3.Calibration

open CubeToSU3.Continuous
open CubeToSU3.QCD

/-! ## Pure scale calibration of the eight-component toy flow -/

/-- The dimensionless direction field supplied by the `D` commutator. -/
def naiveRHS (c : RCoeff8) : RCoeff8 := adDVec c

/-- The same direction field after one external inverse-time scale is added. -/
def calibratedRHS (kappa : ℝ) (c : RCoeff8) : RCoeff8 :=
  kappa • naiveRHS c

@[simp] theorem calibratedRHS_one (c : RCoeff8) :
    calibratedRHS 1 c = naiveRHS c := by
  simp [calibratedRHS]

/-- Exact difference between the calibrated and unit-normalised flows. -/
theorem calibratedRHS_sub_naive (kappa : ℝ) (c : RCoeff8) :
    calibratedRHS kappa c - naiveRHS c =
      (kappa - 1) • naiveRHS c := by
  simp [calibratedRHS, sub_smul]

/-- A nonzero single scale can be divided out of the isolated homogeneous
    toy vector field.  This is the precise sense in which `kappa` calibrates
    the clock but supplies no new dimensionless orbit shape. -/
theorem recover_naiveRHS (kappa : ℝ) (hk : kappa ≠ 0) (c : RCoeff8) :
    kappa⁻¹ • calibratedRHS kappa c = naiveRHS c := by
  simp [calibratedRHS, hk]

/-! ## Experimental coupling data and the irreducible QCD gap -/

/-- PDG 2025 central value at the Z-mass reference scale.
    This is an input datum, not a cube theorem. -/
def alphaS_MZ_central : ℝ := 118 / 1000

/-- Symmetric quoted one-standard-uncertainty half-width, `0.0009`. -/
def alphaS_MZ_uncertainty : ℝ := 9 / 10000

/-- Conversion of the conventional `alpha_s` to `g_s`. -/
def gFromAlpha (alpha : ℝ) : ℝ := Real.sqrt (4 * Real.pi * alpha)

def gS_MZ_central : ℝ := gFromAlpha alphaS_MZ_central

theorem alphaS_MZ_central_nonneg : 0 ≤ alphaS_MZ_central := by
  norm_num [alphaS_MZ_central]

theorem gS_MZ_central_sq :
    gS_MZ_central ^ 2 = 4 * Real.pi * alphaS_MZ_central := by
  change (Real.sqrt (4 * Real.pi * alphaS_MZ_central)) ^ 2 =
    4 * Real.pi * alphaS_MZ_central
  refine Real.sq_sqrt ?_
  unfold alphaS_MZ_central
  positivity

/-- The measured central coupling is not the unit normalisation hidden in the
    original toy curvature.  We prove the robust squared statement without
    decimal approximation. -/
theorem gS_MZ_central_sq_gt_one : 1 < gS_MZ_central ^ 2 := by
  rw [gS_MZ_central_sq]
  unfold alphaS_MZ_central
  have hpi : 3 < Real.pi := Real.pi_gt_three
  nlinarith

/-- The exact field-level discrepancy after inserting the PDG-calibrated
    coupling.  The numerical evaluation `g_s ≈ 1.2177` is documentary; the
    identity itself is exact. -/
theorem calibrated_fieldStrength_gap (A : GaugePotential)
    (μ ν : LorentzIndex) (x : Spacetime) :
    fieldStrengthG gS_MZ_central A μ ν x - fieldStrength A μ ν x =
      (gS_MZ_central - 1) • su3Bracket (A μ x) (A ν x) :=
  fieldStrengthG_sub_naive gS_MZ_central A μ ν x

/-! ## Ledger: which quantities are structural and which are inserted -/

/-- A calibration package needed before a classical field problem has
    dimensionful predictions.  Units are documentary in the present project;
    a future units-of-measure layer should refine the three real fields. -/
structure DynamicalCalibration where
  g_s : ℝ
  energyScaleGeV : ℝ
  quarkMassGeV : ℝ

/-- The dimensionless core and one measured coupling still do not select a
    solution: a background/current plus initial and boundary data are needed. -/
structure CalibratedQCDProblem extends DynamicalCalibration where
  gamma : GammaSystem
  quarkCurrent : QuarkField → ColorCurrent
  initial : InitialData
  boundary : BoundaryData

/-! ## Axiom audit -/

#print axioms calibratedRHS_sub_naive
#print axioms recover_naiveRHS
#print axioms gS_MZ_central_sq
#print axioms gS_MZ_central_sq_gt_one
#print axioms calibrated_fieldStrength_gap

end CubeToSU3.Calibration
