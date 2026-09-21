import CubeToSU3.GaugeGlobal

/-!
# 規範模組之三:局部規範變換,第一步

`GaugeGlobal` handled a constant `g`.  Letting `g` vary over the base is where
the gauge field becomes *necessary* rather than merely allowed: differentiating
`g A g†` leaves two extra pieces,

    ∂(g A g†) = g (∂A) g† + (∂g) A g† + g A (∂g†)
                └ covariant ┘ └──── residue ────┘

and the inhomogeneous term in the transformation law exists precisely to cancel
that residue.  The object that carries it is the Maurer–Cartan form

    θ_μ = u ∂_μ u†      (u = g as a matrix)

This file establishes what `θ` is, and nothing more.  Covariance comes next.

**What is proved.**  `θ` is anti-Hermitian.  Only unitarity is used: differentiate
`u u† = 1` to get `(∂u)u† + u(∂u†) = 0`, and note `(u ∂u†)† = (∂u) u†`.

**What is assumed, and why.**  `θ` is also traceless, because `det u = 1`.  That
step needs the derivative of the determinant — Jacobi's formula — and Mathlib at
the pinned revision `a6276f4c` **does not have it**: `Matrix.det` appears nowhere
in `Mathlib/Analysis/Calculus/`, only `Continuous.matrix_det` in the topology
files.  The nearest material is the polynomial identity
`Matrix.det_one_add_X_smul`, giving `det (1 + XM) = 1 + (tr M)X + O(X²)`; turning
that into an analytic derivative and composing it along a curve is a separate
piece of work.

So `traceless` enters as an explicit field of `LocalGauge` below, flagged here
rather than hidden.  This is the same device that carried
`UnitarySpectralTheorem3` for a long time before it was discharged in
`SU3SpectralStage1`–`5`; the intention is the same, and the hypothesis is a
standard fact, not a gap in the mathematics.

**Risk note.**  This is the first file in the gauge module that does real
analysis rather than algebra — product rule, derivative of the star operation,
derivative of a constant.  It is correspondingly more likely to need adjustment
than the two before it.

Nothing here is a physical claim.
-/

noncomputable section

-- `ᴴ` is scoped notation in the `Matrix` namespace; without this every use of
-- it below is a parse error.
open Matrix

namespace CubeToSU3.Gauge

open CubeToSU3 CubeToSU3.Continuous CubeToSU3.QCD

section LinftyTopology

-- Only `NormedRing` is declared here.  `NormedRing.toSeminormedRing` supplies
-- the seminormed structure, and declaring both creates two paths to `Ring M3C`;
-- that diamond is harmless until instance search has to backtrack, which it
-- does for the scalar action on `Spacetime →L[ℝ] M3C` used by the product rule.
local instance : NormedRing M3C := Matrix.linftyOpNormedRing
local instance : NormedAlgebra ℂ M3C := Matrix.linftyOpNormedAlgebra

/-! ## The derivative commutes with the conjugate transpose -/

/-- `ᴴ` is `ℝ`-linear and continuous, so it passes through `fderiv`.  Like
    `ContinuousLinearEquiv.comp_fderiv`, this needs no differentiability
    hypothesis. -/
theorem fderiv_conjTranspose (u : Spacetime → M3C) (x v : Spacetime) :
    fderiv ℝ (fun y => (u y)ᴴ) x v = (fderiv ℝ u x v)ᴴ := by
  have h : fderiv ℝ (fun y => star (u y)) x
      = ((starL' ℝ : M3C ≃L[ℝ] M3C) : M3C →L[ℝ] M3C) ∘L (fderiv ℝ u x) :=
    fderiv_star
  -- `star` and `ᴴ` are definitionally equal on matrices, as is applying
  -- `starL'`, so `exact` closes this without any simp normalisation.
  exact congrArg (fun L : Spacetime →L[ℝ] M3C => L v) h

/-! ## The Maurer–Cartan form -/

/-- `θ_μ = u ∂_μ u†`.  Defined on a raw matrix-valued map so that the
    differentiability and unitarity hypotheses can be supplied separately. -/
def mc (u : Spacetime → M3C) (μ : LorentzIndex) (x : Spacetime) : M3C :=
  u x * fderiv ℝ (fun y => (u y)ᴴ) x (coordinateDirection μ)

/-- Differentiating `u u† = 1`. -/
theorem unitary_deriv_relation (u : Spacetime → M3C) (hd : Differentiable ℝ u)
    (hu : ∀ y, u y * (u y)ᴴ = 1) (x v : Spacetime) :
    u x * (fderiv ℝ u x v)ᴴ + fderiv ℝ u x v * (u x)ᴴ = 0 := by
  have h1 : HasFDerivAt u (fderiv ℝ u x) x := (hd x).hasFDerivAt
  have h2 : HasFDerivAt (fun y => (u y)ᴴ)
      (((starL' ℝ : M3C ≃L[ℝ] M3C) : M3C →L[ℝ] M3C) ∘L (fderiv ℝ u x)) x :=
    h1.star
  -- the `0` must be ascribed: as a bare `0` the scalar field of
  -- `Spacetime →L[?] M3C` is a metavariable and `Module ? M3C` stalls.
  have hconst : HasFDerivAt (fun y => u y * (u y)ᴴ)
      (0 : Spacetime →L[ℝ] M3C) x := by
    have hfun : (fun y => u y * (u y)ᴴ) = fun _ => (1 : M3C) := funext hu
    rw [hfun]
    exact hasFDerivAt_const _ _
  have hprod := HasFDerivAt.mul' (𝕜 := ℝ) h1 h2
  have heq := hprod.unique hconst
  have happ := congrArg (fun L : Spacetime →L[ℝ] M3C => L v) heq
  simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_comp',
    smul_eq_mul, add_comm] using happ

/-- **The Maurer–Cartan form is anti-Hermitian.**  Only `u u† = 1` is used. -/
theorem mc_antiHermitian (u : Spacetime → M3C) (hd : Differentiable ℝ u)
    (hu : ∀ y, u y * (u y)ᴴ = 1) (μ : LorentzIndex) (x : Spacetime) :
    (mc u μ x)ᴴ = -(mc u μ x) := by
  have hrel := unitary_deriv_relation u hd hu x (coordinateDirection μ)
  have hstar := fderiv_conjTranspose u x (coordinateDirection μ)
  unfold mc
  rw [hstar, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hneg : fderiv ℝ u x (coordinateDirection μ) * (u x)ᴴ
      = -(u x * (fderiv ℝ u x (coordinateDirection μ))ᴴ) := by
    have h := hrel
    rw [add_eq_zero_iff_eq_neg] at h
    rw [h, neg_neg]
  rw [hneg]

/-! ## Bundled local gauge transformations -/

/-- A local gauge transformation, carrying its differentiability and — as an
    explicit hypothesis — the tracelessness of its Maurer–Cartan form.  See the
    module docstring: tracelessness follows from `det g = 1` by Jacobi's
    formula, which the pinned Mathlib lacks. -/
structure LocalGauge where
  /-- the group-valued map -/
  map : Spacetime → SU3
  /-- differentiability of the underlying matrix-valued map -/
  diff : Differentiable ℝ (fun y => ((map y : M3C)))
  /-- **assumed**: the Maurer–Cartan form is traceless -/
  traceless : ∀ (μ : LorentzIndex) (x : Spacetime),
    Matrix.trace (mc (fun y => ((map y : M3C))) μ x) = 0

namespace LocalGauge

variable (G : LocalGauge)

/-- The underlying matrix-valued map. -/
def mat : Spacetime → M3C := fun y => ((G.map y : M3C))

theorem mat_unitary (y : Spacetime) : G.mat y * (G.mat y)ᴴ = 1 :=
  (G.map y).2.1.2

/-- The Maurer–Cartan form of a local gauge transformation lands in `su(3)`:
    anti-Hermitian by `mc_antiHermitian`, traceless by hypothesis. -/
theorem mc_mem (μ : LorentzIndex) (x : Spacetime) :
    IsSu3R (mc G.mat μ x) :=
  ⟨mc_antiHermitian G.mat G.diff G.mat_unitary μ x, G.traceless μ x⟩

/-- The Maurer–Cartan form, valued in `su(3)`. -/
def theta (μ : LorentzIndex) (x : Spacetime) : Su3R :=
  ⟨mc G.mat μ x, G.mc_mem μ x⟩

@[simp] theorem coe_theta (μ : LorentzIndex) (x : Spacetime) :
    (G.theta μ x : M3C) = mc G.mat μ x := rfl

end LocalGauge

end LinftyTopology

/-! ## Axiom audit -/

#print axioms fderiv_conjTranspose
#print axioms unitary_deriv_relation
#print axioms mc_antiHermitian
#print axioms LocalGauge.mc_mem

end CubeToSU3.Gauge
