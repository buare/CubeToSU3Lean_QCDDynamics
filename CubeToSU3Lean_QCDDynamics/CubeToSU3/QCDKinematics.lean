/-
  QCDKinematics.lean

  A deliberately scoped first classical gauge-theory layer built on the
  continuous real Lie algebra su(3).

  Proved here:
  * a bundled su(3)-valued commutator;
  * smooth gauge potentials on four-dimensional real coordinate space;
  * directional partial derivatives and the non-abelian field strength;
  * the field strength remains su(3)-valued by construction;
  * F_{mu,nu} = -F_{nu,mu}, hence F_{mu,mu} = 0;
  * a nonnegative Euclidean Yang--Mills density;
  * the fundamental colour action of SU(3) respects identity and products.

  This is classical kinematics.  It does not yet define a principal bundle,
  local gauge transformations, covariant derivatives of quarks, the Dirac
  operator, spacetime integration, equations of motion, path integrals,
  renormalisation, confinement, or quantum QCD.

  No `sorry`, `admit`, or custom axiom is used.
-/

import CubeToSU3.SU3Global

noncomputable section

set_option maxHeartbeats 4000000

open Matrix Complex BigOperators
open scoped ContDiff

namespace CubeToSU3.QCD

open CubeToSU3.Continuous

section LinftyTopology

local instance : SeminormedRing M3C := Matrix.linftyOpSemiNormedRing
local instance : NormedRing M3C := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℂ M3C := Matrix.linftyOpNormedAlgebra

noncomputable local instance su3RCompleteSpace : CompleteSpace Su3R :=
  FiniteDimensional.complete ℝ Su3R

/-! ## The Lie bracket as a bundled su(3) value -/

/-- The matrix commutator, bundled with the proof that it stays in su(3). -/
def su3Bracket (X Y : Su3R) : Su3R :=
  ⟨bracketR X.1 Y.1, bracketR_mem X.2 Y.2⟩

@[simp] theorem coe_su3Bracket (X Y : Su3R) :
    (su3Bracket X Y : M3C) = bracketR X.1 Y.1 := rfl

theorem su3Bracket_swap (X Y : Su3R) :
    su3Bracket X Y = -su3Bracket Y X := by
  apply Subtype.ext
  simp only [coe_su3Bracket, Submodule.coe_neg]
  unfold bracketR
  noncomm_ring

@[simp] theorem su3Bracket_self (X : Su3R) : su3Bracket X X = 0 := by
  apply Subtype.ext
  simp [su3Bracket, bracketR]

/-! ## Four-dimensional gauge potentials -/

/-- Four real coordinates.  The finite product norm induces the usual
    finite-dimensional topology; no Lorentzian metric is chosen here. -/
abbrev Spacetime := Fin 4 → ℝ

abbrev LorentzIndex := Fin 4

/-- A classical su(3)-valued gauge potential A_mu(x). -/
abbrev GaugePotential := LorentzIndex → Spacetime → Su3R

/-- A gauge potential whose four components are infinitely differentiable. -/
structure SmoothGaugePotential where
  toFun : GaugePotential
  smooth : ∀ μ, ContDiff ℝ ∞ (toFun μ)

instance : CoeFun SmoothGaugePotential (fun _ => GaugePotential) :=
  ⟨SmoothGaugePotential.toFun⟩

/-- The mu-th coordinate direction in spacetime. -/
def coordinateDirection (μ : LorentzIndex) : Spacetime := Pi.single μ 1

/-- Partial derivative of component A_nu in coordinate direction mu. -/
def partialDerivative (A : GaugePotential) (μ ν : LorentzIndex) (x : Spacetime) : Su3R :=
  fderiv ℝ (A ν) x (coordinateDirection μ)

/-- Non-abelian field strength

      F_{mu,nu} = partial_mu A_nu - partial_nu A_mu + [A_mu,A_nu].
-/
def fieldStrength (A : GaugePotential) (μ ν : LorentzIndex)
    (x : Spacetime) : Su3R :=
  partialDerivative A μ ν x - partialDerivative A ν μ x +
    su3Bracket (A μ x) (A ν x)

/-- The field strength is su(3)-valued.  This is a type-level closure result,
    not an external side condition. -/
theorem fieldStrength_mem_su3 (A : GaugePotential) (μ ν : LorentzIndex)
    (x : Spacetime) : IsSu3R (fieldStrength A μ ν x).1 :=
  (fieldStrength A μ ν x).2

/-- Antisymmetry in the spacetime indices. -/
theorem fieldStrength_swap (A : GaugePotential) (μ ν : LorentzIndex)
    (x : Spacetime) :
    fieldStrength A μ ν x = -fieldStrength A ν μ x := by
  unfold fieldStrength
  rw [su3Bracket_swap]
  abel

@[simp] theorem fieldStrength_self (A : GaugePotential) (μ : LorentzIndex)
    (x : Spacetime) : fieldStrength A μ μ x = 0 := by
  unfold fieldStrength
  simp

/-! ## A first Euclidean Yang--Mills scalar -/

/-- Pointwise Euclidean pure-gauge density.  This is not yet the Minkowski
    Lagrangian and is not integrated over spacetime. -/
def yangMillsDensity (A : GaugePotential) (x : Spacetime) : ℝ :=
  (1 / 4 : ℝ) * ∑ μ : LorentzIndex, ∑ ν : LorentzIndex,
    ‖fieldStrength A μ ν x‖ ^ 2

theorem yangMillsDensity_nonneg (A : GaugePotential) (x : Spacetime) :
    0 ≤ yangMillsDensity A x := by
  unfold yangMillsDensity
  positivity

/-! ## Fundamental colour representation -/

abbrev ColorVector := Fin 3 → ℂ

/-- The defining action of SU(3) on a three-component colour vector. -/
def colorAction (g : SU3) (v : ColorVector) : ColorVector :=
  (g : M3C) *ᵥ v

@[simp] theorem colorAction_one (v : ColorVector) :
    colorAction (1 : SU3) v = v := by
  simp [colorAction]

theorem colorAction_mul (g h : SU3) (v : ColorVector) :
    colorAction (g * h) v = colorAction g (colorAction h v) := by
  simp [colorAction, Matrix.mulVec_mulVec]

/-! ## Axiom audit -/

#print axioms su3Bracket_swap
#print axioms fieldStrength_mem_su3
#print axioms fieldStrength_swap
#print axioms fieldStrength_self
#print axioms yangMillsDensity_nonneg
#print axioms colorAction_mul

end LinftyTopology

end CubeToSU3.QCD
