import CubeToSU3.GaugeTheory
import CubeToSU3.QCDDynamics

/-!
# 規範模組之二:全域規範協變性

The first block proved that `Ad g` is a Lie-algebra automorphism, using nothing
but algebra.  This block takes the smallest step that involves a base space: a
**constant** `g`, so that `∂ g = 0` and the transformation law collapses to

    A ↦ Ad g ∘ A

The payoff is the statement that makes `fieldStrength` deserve its name:

    F (Ad g ∘ A) = Ad g (F A)

Splitting the work this way keeps algebra and analysis apart.  Here the only
analytic input is that `fderiv` commutes with a fixed continuous linear
equivalence — `ContinuousLinearEquiv.comp_fderiv`, which holds with **no
differentiability hypothesis** because a linear equivalence sends
non-differentiable points to non-differentiable points and `fderiv` is zero at
both.  That is why `Ad g` is packaged as an equivalence rather than a plain
linear map: `Ad g⁻¹` is its inverse, by `Ad_mul` and `Ad_one`.

The local case, where `g` varies over the base, adds exactly one thing: the
inhomogeneous term `(1/g_s) g ∂g†`, together with the work of showing it lands
in `su(3)` (differentiate the constraints `g g† = 1` and `det g = 1`).  Nothing
in this file will change when that is added; the homogeneous part of the local
computation is precisely what is proved here.

Gauge freedom having no physical content is the conjunction of two statements:
`Ad_bracket` from block one says the algebra inside a fibre is untouched, and
`fieldStrength_gauge_covariant` below says the curvature only turns rigidly.

Nothing here is a physical claim.
-/

noncomputable section

namespace CubeToSU3.Gauge

open CubeToSU3 CubeToSU3.Continuous CubeToSU3.QCD

section LinftyTopology

local instance : SeminormedRing M3C := Matrix.linftyOpSemiNormedRing
local instance : NormedRing M3C := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℂ M3C := Matrix.linftyOpNormedAlgebra

/-! ## The bracket, re-stated for the bundled `Su3R`

`GaugeTheory` proves this at the matrix level; here it is wrapped, now that
`su3Bracket` is in scope. -/

theorem Ad_bracket (g : SU3) (X Y : Su3R) :
    Ad g (su3Bracket X Y) = su3Bracket (Ad g X) (Ad g Y) := by
  apply Subtype.ext
  exact Ad_bracketR g (X : M3C) (Y : M3C)

theorem Ad_bracket_inv (g : SU3) (X Y : Su3R) :
    su3Bracket X Y = Ad g⁻¹ (su3Bracket (Ad g X) (Ad g Y)) := by
  rw [← Ad_bracket, ← Ad_mul, inv_mul_cancel, Ad_one]

/-! ## `Ad g` as a linear equivalence -/

/-- `Ad g` with `Ad g⁻¹` as its inverse. -/
def AdEquiv (g : SU3) : Su3R ≃ₗ[ℝ] Su3R where
  toFun := Ad g
  map_add' := Ad_add g
  map_smul' := Ad_smul g
  invFun := Ad g⁻¹
  left_inv := by
    intro X
    -- the anonymous-constructor projection does not reduce on its own, so the
    -- `rw` pattern `Ad ?g (Ad ?h ?X)` is not visible until we `show` it
    show Ad g⁻¹ (Ad g X) = X
    rw [← Ad_mul, inv_mul_cancel, Ad_one]
  right_inv := by
    intro X
    show Ad g (Ad g⁻¹ X) = X
    rw [← Ad_mul, mul_inv_cancel, Ad_one]

@[simp] theorem coe_AdEquiv (g : SU3) : ⇑(AdEquiv g) = Ad g := rfl

/-- Upgraded to a continuous linear equivalence.  `Su3R` is finite dimensional,
    so no continuity argument is needed. -/
def AdCLE (g : SU3) : Su3R ≃L[ℝ] Su3R := (AdEquiv g).toContinuousLinearEquiv

@[simp] theorem coe_AdCLE (g : SU3) : ⇑(AdCLE g) = Ad g := rfl

/-! ## Global gauge transformation -/

/-- A constant gauge transformation acts on the potential by conjugation. -/
def gaugeActGlobal (g : SU3) (A : GaugePotential) : GaugePotential :=
  fun μ x => Ad g (A μ x)

/-- The derivative commutes with a constant conjugation.  No differentiability
    hypothesis is needed: `AdCLE g` is an equivalence, so it preserves both
    differentiability and its failure. -/
theorem partialDerivative_gaugeActGlobal (g : SU3) (A : GaugePotential)
    (μ ν : LorentzIndex) (x : Spacetime) :
    partialDerivative (gaugeActGlobal g A) μ ν x
      = Ad g (partialDerivative A μ ν x) := by
  show fderiv ℝ (fun y => Ad g (A ν y)) x (coordinateDirection μ)
      = Ad g (fderiv ℝ (A ν) x (coordinateDirection μ))
  have h : fderiv ℝ ((AdCLE g) ∘ (A ν)) x
      = ((AdCLE g : Su3R →L[ℝ] Su3R)).comp (fderiv ℝ (A ν) x) :=
    (AdCLE g).comp_fderiv
  have hfun : ((AdCLE g) ∘ (A ν)) = fun y => Ad g (A ν y) := rfl
  rw [hfun] at h
  rw [h]
  rfl

/-! ## The field strength is covariant -/

/-- **Global gauge covariance.**  Conjugating the potential by a constant group
    element conjugates the field strength by the same element: the curvature
    turns rigidly and every invariant built from it is untouched. -/
theorem fieldStrength_gauge_covariant (g : SU3) (A : GaugePotential)
    (μ ν : LorentzIndex) (x : Spacetime) :
    fieldStrength (gaugeActGlobal g A) μ ν x = Ad g (fieldStrength A μ ν x) := by
  show partialDerivative (gaugeActGlobal g A) μ ν x
        - partialDerivative (gaugeActGlobal g A) ν μ x
        + su3Bracket (gaugeActGlobal g A μ x) (gaugeActGlobal g A ν x)
      = Ad g (partialDerivative A μ ν x - partialDerivative A ν μ x
        + su3Bracket (A μ x) (A ν x))
  rw [partialDerivative_gaugeActGlobal, partialDerivative_gaugeActGlobal]
  show Ad g (partialDerivative A μ ν x) - Ad g (partialDerivative A ν μ x)
      + su3Bracket (Ad g (A μ x)) (Ad g (A ν x))
    = Ad g (partialDerivative A μ ν x - partialDerivative A ν μ x
        + su3Bracket (A μ x) (A ν x))
  rw [← Ad_bracket, ← Ad_sub, ← Ad_add]

/-- The same for the `g_s`-carrying field strength of `QCDDynamics`. -/
theorem fieldStrengthG_gauge_covariant (g_s : ℝ) (g : SU3) (A : GaugePotential)
    (μ ν : LorentzIndex) (x : Spacetime) :
    fieldStrengthG g_s (gaugeActGlobal g A) μ ν x
      = Ad g (fieldStrengthG g_s A μ ν x) := by
  show partialDerivative (gaugeActGlobal g A) μ ν x
        - partialDerivative (gaugeActGlobal g A) ν μ x
        + g_s • su3Bracket (gaugeActGlobal g A μ x) (gaugeActGlobal g A ν x)
      = Ad g (partialDerivative A μ ν x - partialDerivative A ν μ x
        + g_s • su3Bracket (A μ x) (A ν x))
  rw [partialDerivative_gaugeActGlobal, partialDerivative_gaugeActGlobal]
  show Ad g (partialDerivative A μ ν x) - Ad g (partialDerivative A ν μ x)
      + g_s • su3Bracket (Ad g (A μ x)) (Ad g (A ν x))
    = Ad g (partialDerivative A μ ν x - partialDerivative A ν μ x
        + g_s • su3Bracket (A μ x) (A ν x))
  rw [← Ad_bracket, ← Ad_smul, ← Ad_sub, ← Ad_add]

end LinftyTopology

/-! ## Axiom audit -/

#print axioms Ad_bracket
#print axioms AdEquiv
#print axioms partialDerivative_gaugeActGlobal
#print axioms fieldStrength_gauge_covariant
#print axioms fieldStrengthG_gauge_covariant

end CubeToSU3.Gauge
