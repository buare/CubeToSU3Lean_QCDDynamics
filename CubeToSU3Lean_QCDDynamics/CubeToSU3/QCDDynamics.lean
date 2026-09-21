import CubeToSU3.QCDKinematics

/-!
# Classical QCD dynamics: explicit external parameters

This module adds the first *dynamical dictionary* on top of
`QCDKinematics.lean`.  In particular it no longer hides the convention
`g_s = 1`:

* `fieldStrengthG` contains an explicit strong coupling `g_s`;
* `covariantDerivativeAdjoint` and `quarkCovariantDerivative` contain the
  same coupling;
* `YangMillsEquation` and `DiracEquation` state the classical residual
  equations;
* `InitialData` and `BoundaryData` record the information required to select
  a solution;
* `euclideanQCDDensity` is a pointwise classical prototype containing a gauge
  term and a quark--Dirac term.

Convention: the Lie algebra carrier consists of anti-Hermitian matrices, so
the connection is written `partial + g_s A` rather than `partial - i g_s A`.
Changing to Hermitian generators moves the factor `i`; it does not change the
content.

Important boundary: this module *defines* the field equations and proves
their algebraic consistency with the earlier normalisation.  It does not
derive them from the cube, from a variational theorem, or from quantisation.
Gamma-matrix Clifford relations, Grassmann-valued quantum fields,
gauge-fixing, ghosts, renormalisation and confinement remain outside scope.

No `sorry`, `admit`, or new custom axiom is used.
-/

noncomputable section

set_option maxHeartbeats 4000000

open Matrix Complex BigOperators

namespace CubeToSU3.QCD

open CubeToSU3.Continuous

section LinftyTopology

local instance : SeminormedRing M3C := Matrix.linftyOpSemiNormedRing
local instance : NormedRing M3C := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℂ M3C := Matrix.linftyOpNormedAlgebra

/-- Re-activation of the `l^infty` completeness instance inside this file.

    `local instance` only restricts the *attribute* to the current file; the
    constant itself is exported.  `QCDKinematics` already declares
    `CubeToSU3.QCD.su3RCompleteSpace`, so this file must use a fresh name
    instead of repeating it (compare `su3RCompleteSpaceLinfty` in
    `SU3Group.lean`). -/
noncomputable local instance su3RCompleteSpaceDynamics : CompleteSpace Su3R :=
  FiniteDimensional.complete ℝ Su3R

/-! ## The strong coupling is no longer hidden -/

/-- Non-abelian curvature with an explicit dimensionless coupling.

    `F_g = dA + g_s [A,A]` in the anti-Hermitian convention. -/
def fieldStrengthG (g_s : ℝ) (A : GaugePotential) (μ ν : LorentzIndex)
    (x : Spacetime) : Su3R :=
  partialDerivative A μ ν x - partialDerivative A ν μ x +
    g_s • su3Bracket (A μ x) (A ν x)

theorem fieldStrengthG_mem_su3 (g_s : ℝ) (A : GaugePotential)
    (μ ν : LorentzIndex) (x : Spacetime) :
    IsSu3R (fieldStrengthG g_s A μ ν x).1 :=
  (fieldStrengthG g_s A μ ν x).2

/-- The old kinematic field strength was exactly the normalisation `g_s=1`. -/
@[simp] theorem fieldStrengthG_one (A : GaugePotential) (μ ν : LorentzIndex)
    (x : Spacetime) :
    fieldStrengthG 1 A μ ν x = fieldStrength A μ ν x := by
  simp [fieldStrengthG, fieldStrength]

/-- At `g_s=0`, only the abelian derivative part remains. -/
@[simp] theorem fieldStrengthG_zero (A : GaugePotential) (μ ν : LorentzIndex)
    (x : Spacetime) :
    fieldStrengthG 0 A μ ν x =
      partialDerivative A μ ν x - partialDerivative A ν μ x := by
  simp [fieldStrengthG]

/-- Exact gap between a physical coupling and the dimensionless `g_s=1`
    prototype.  The derivative part is unchanged; only the non-abelian term
    is rescaled. -/
theorem fieldStrengthG_sub_naive (g_s : ℝ) (A : GaugePotential)
    (μ ν : LorentzIndex) (x : Spacetime) :
    fieldStrengthG g_s A μ ν x - fieldStrength A μ ν x =
      (g_s - 1) • su3Bracket (A μ x) (A ν x) := by
  unfold fieldStrengthG fieldStrength
  rw [sub_smul g_s 1 (su3Bracket (A μ x) (A ν x)),
      one_smul ℝ (su3Bracket (A μ x) (A ν x))]
  generalize g_s • su3Bracket (A μ x) (A ν x) = X
  generalize su3Bracket (A μ x) (A ν x) = B
  abel

theorem fieldStrengthG_swap (g_s : ℝ) (A : GaugePotential)
    (μ ν : LorentzIndex) (x : Spacetime) :
    fieldStrengthG g_s A μ ν x = -fieldStrengthG g_s A ν μ x := by
  unfold fieldStrengthG
  rw [su3Bracket_swap]
  simp only [smul_neg]
  abel

@[simp] theorem fieldStrengthG_self (g_s : ℝ) (A : GaugePotential)
    (μ : LorentzIndex) (x : Spacetime) :
    fieldStrengthG g_s A μ μ x = 0 := by
  simp [fieldStrengthG]

/-- Pointwise Euclidean pure-gauge density with explicit coupling. -/
def yangMillsDensityG (g_s : ℝ) (A : GaugePotential) (x : Spacetime) : ℝ :=
  (1 / 4 : ℝ) * ∑ μ : LorentzIndex, ∑ ν : LorentzIndex,
    ‖fieldStrengthG g_s A μ ν x‖ ^ 2

theorem yangMillsDensityG_nonneg (g_s : ℝ) (A : GaugePotential)
    (x : Spacetime) : 0 ≤ yangMillsDensityG g_s A x := by
  unfold yangMillsDensityG
  positivity

@[simp] theorem yangMillsDensityG_one (A : GaugePotential) (x : Spacetime) :
    yangMillsDensityG 1 A x = yangMillsDensity A x := by
  simp [yangMillsDensityG, yangMillsDensity]

/-! ## Adjoint covariant derivative and Yang--Mills equation -/

abbrev AdjointField := Spacetime → Su3R

def partialAdjoint (φ : AdjointField) (μ : LorentzIndex)
    (x : Spacetime) : Su3R :=
  fderiv ℝ φ x (coordinateDirection μ)

/-- `D_mu φ = partial_mu φ + g_s [A_mu,φ]`. -/
def covariantDerivativeAdjoint (g_s : ℝ) (A : GaugePotential)
    (φ : AdjointField) (μ : LorentzIndex) (x : Spacetime) : Su3R :=
  partialAdjoint φ μ x + g_s • su3Bracket (A μ x) (φ x)

abbrev ColorCurrent := LorentzIndex → Spacetime → Su3R

/-- The residual `D^mu F_{mu,nu}` in the present Euclidean-coordinate
    prototype.  Raising/lowering with a Minkowski metric is deliberately not
    smuggled into this definition. -/
def yangMillsResidual (g_s : ℝ) (A : GaugePotential)
    (ν : LorentzIndex) (x : Spacetime) : Su3R :=
  ∑ μ : LorentzIndex,
    covariantDerivativeAdjoint g_s A
      (fun y => fieldStrengthG g_s A μ ν y) μ x

/-- Classical Yang--Mills equation with a supplied colour current. -/
def YangMillsEquation (g_s : ℝ) (A : GaugePotential)
    (J : ColorCurrent) : Prop :=
  ∀ ν x, yangMillsResidual g_s A ν x = J ν x

/-! ## Quark colour--spin fields and the Dirac residual -/

abbrev SpinIndex := Fin 4
abbrev ColorIndex := Fin 3
abbrev SpinColor := SpinIndex → ColorIndex → ℂ
abbrev QuarkField := Spacetime → SpinColor
abbrev GammaMatrix := Matrix SpinIndex SpinIndex ℂ
abbrev GammaSystem := LorentzIndex → GammaMatrix

/-- The Lie-algebra action on one colour triplet. -/
def algebraColorAction (X : Su3R) (v : ColorVector) : ColorVector :=
  (X : M3C) *ᵥ v

/-- Colour acts independently on each spin component. -/
def spinColorGaugeAction (X : Su3R) (ψ : SpinColor) : SpinColor :=
  fun s => algebraColorAction X (ψ s)

def quarkPartialDerivative (ψ : QuarkField) (μ : LorentzIndex)
    (x : Spacetime) : SpinColor :=
  fderiv ℝ ψ x (coordinateDirection μ)

/-- `D_mu ψ = partial_mu ψ + g_s A_mu ψ`. -/
def quarkCovariantDerivative (g_s : ℝ) (A : GaugePotential)
    (ψ : QuarkField) (μ : LorentzIndex) (x : Spacetime) : SpinColor :=
  quarkPartialDerivative ψ μ x +
    g_s • spinColorGaugeAction (A μ x) (ψ x)

/-- A gamma matrix acts on spin and leaves colour untouched. -/
def gammaAction (γ : GammaMatrix) (ψ : SpinColor) : SpinColor :=
  fun s c => ∑ r : SpinIndex, γ s r * ψ r c

/-- Residual of `(i gamma^mu D_mu - m) ψ = 0`.

    The Clifford relations of the supplied `gamma` matrices are not asserted
    by this definition; they are part of the spacetime/Dirac dictionary. -/
def diracResidual (gamma : GammaSystem) (g_s m : ℝ)
    (A : GaugePotential) (ψ : QuarkField) (x : Spacetime) : SpinColor :=
  Complex.I • (∑ μ : LorentzIndex,
    gammaAction (gamma μ) (quarkCovariantDerivative g_s A ψ μ x)) -
    (m : ℂ) • ψ x

def DiracEquation (gamma : GammaSystem) (g_s m : ℝ)
    (A : GaugePotential) (ψ : QuarkField) : Prop :=
  ∀ x, diracResidual gamma g_s m A ψ x = 0

/-! ## Pointwise QCD density and solution-selecting data -/

def spinColorPairing (ψ χ : SpinColor) : ℂ :=
  ∑ s : SpinIndex, ∑ c : ColorIndex, starRingEnd ℂ (ψ s c) * χ s c

/-- A pointwise Euclidean classical prototype.  This is intentionally named
    a density, not an integrated action and not a quantum path integral. -/
def euclideanQCDDensity (gamma : GammaSystem) (g_s m : ℝ)
    (A : GaugePotential) (ψ : QuarkField) (x : Spacetime) : ℝ :=
  yangMillsDensityG g_s A x +
    (spinColorPairing (ψ x) (diracResidual gamma g_s m A ψ x)).re

/-- Initial values on the coordinate hyperplane `x 0 = 0`. -/
structure InitialData where
  gauge : LorentzIndex → Spacetime → Su3R
  quark : Spacetime → SpinColor

def OnInitialSlice (x : Spacetime) : Prop := x 0 = 0

def SatisfiesInitialData (A : GaugePotential) (ψ : QuarkField)
    (data : InitialData) : Prop :=
  (∀ μ x, OnInitialSlice x → A μ x = data.gauge μ x) ∧
  (∀ x, OnInitialSlice x → ψ x = data.quark x)

/-- General boundary data on an explicitly supplied spacetime set. -/
structure BoundaryData where
  region : Set Spacetime
  gauge : LorentzIndex → Spacetime → Su3R
  quark : Spacetime → SpinColor

def SatisfiesBoundaryData (A : GaugePotential) (ψ : QuarkField)
    (data : BoundaryData) : Prop :=
  (∀ μ x, x ∈ data.region → A μ x = data.gauge μ x) ∧
  (∀ x, x ∈ data.region → ψ x = data.quark x)

/-- One explicit classical initial/boundary-value problem. -/
structure ClassicalQCDProblem where
  g_s : ℝ
  mass : ℝ
  gamma : GammaSystem
  /-- The map from a quark field to its colour current.  Its detailed
      gamma/generator formula belongs to the Dirac and representation
      dictionary and is therefore explicit data at this stage. -/
  quarkCurrent : QuarkField → ColorCurrent
  initial : InitialData
  boundary : BoundaryData

def SolvesClassicalQCDProblem (problem : ClassicalQCDProblem)
    (A : GaugePotential) (ψ : QuarkField) : Prop :=
  YangMillsEquation problem.g_s A (problem.quarkCurrent ψ) ∧
  DiracEquation problem.gamma problem.g_s problem.mass A ψ ∧
  SatisfiesInitialData A ψ problem.initial ∧
  SatisfiesBoundaryData A ψ problem.boundary

/-! ## Axiom audit -/

#print axioms fieldStrengthG_sub_naive
#print axioms fieldStrengthG_swap
#print axioms yangMillsDensityG_nonneg
#print axioms YangMillsEquation
#print axioms DiracEquation
#print axioms SolvesClassicalQCDProblem

end LinftyTopology

end CubeToSU3.QCD
