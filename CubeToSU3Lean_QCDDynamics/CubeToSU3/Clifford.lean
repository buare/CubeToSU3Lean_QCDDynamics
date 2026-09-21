import CubeToSU3.QCDDynamics

/-!
# Clifford 關係:補上 Dirac 方程的一個實質漏洞

`QCDDynamics.DiracEquation` takes a `GammaSystem` — four arbitrary `4 × 4`
complex matrices — and asserts nothing about them.  Its own docstring says so.
That makes the statement weaker than it looks: substitute four arbitrary
matrices and the equation is not the Dirac equation, it is an arbitrary
first-order system that happens to have the same shape.

This file supplies what was missing, in two parts.

**The condition.**  `IsCliffordSystem γ` requires the Euclidean Clifford
relation

    γ^μ γ^ν + γ^ν γ^μ = 2 δ^{μν} · 1

Anything called a gamma system should satisfy it; `DiracEquation` should be
read as carrying this as a side condition.

**A witness.**  `euclideanGamma` is an explicit chiral-basis solution, built
from the Pauli matrices as `γ_j = [[0, -i σ_j], [i σ_j, 0]]` for `j = 1,2,3` and
`γ_4 = [[0, 1], [1, 0]]` in `2 × 2` blocks.  `euclideanGamma_isClifford` checks
all sixteen anticommutators.  Without a witness the condition could be vacuous;
with one, `IsCliffordSystem` is known to be satisfiable.

Two further properties are recorded because they are what the Clifford relation
is usually used through: each `γ^μ` is Hermitian, and each squares to the
identity (the diagonal case of the relation).

**Where this sits.**  The Clifford algebra belongs to the *spacetime* side of
the dictionary, not the colour side.  The index `μ` is a spacetime index and
`δ^{μν}` is the Euclidean metric; `SU(3)` says nothing about any of it.  So
unlike the gauge modules, this is genuinely an external constraint — one of the
"other" constraints that the `SU(3)` block gets plugged into.  The signature is
Euclidean, matching `QCDKinematics`'s deliberate choice not to fix a Minkowski
metric.

Nothing here is a physical claim.
-/

noncomputable section

open Matrix

namespace CubeToSU3.QCD

/-! ## The condition -/

/-- The Euclidean Clifford relation, split into its diagonal and off-diagonal
    halves.  This is equivalent to `{γ^μ, γ^ν} = 2 δ^{μν}` — the diagonal case
    of that relation is `2 γ^μ γ^μ = 2`, i.e. `γ^μ γ^μ = 1` — and it avoids an
    `if` in the statement, which keeps the proofs from having to discharge a
    `Fin` equality inside every one of the sixteen cases. -/
def IsCliffordSystem (γ : GammaSystem) : Prop :=
  (∀ μ : LorentzIndex, γ μ * γ μ = 1) ∧
  (∀ μ ν : LorentzIndex, μ ≠ ν → γ μ * γ ν + γ ν * γ μ = 0)

/-! ## An explicit witness -/

/-- The chiral-basis Euclidean gamma matrices. -/
def euclideanGamma : GammaSystem
  | 0 => !![0, 0, 0, -Complex.I;
            0, 0, -Complex.I, 0;
            0, Complex.I, 0, 0;
            Complex.I, 0, 0, 0]
  | 1 => !![0, 0, 0, -1;
            0, 0, 1, 0;
            0, 1, 0, 0;
            -1, 0, 0, 0]
  | 2 => !![0, 0, -Complex.I, 0;
            0, 0, 0, Complex.I;
            Complex.I, 0, 0, 0;
            0, -Complex.I, 0, 0]
  | 3 => !![0, 0, 1, 0;
            0, 0, 0, 1;
            1, 0, 0, 0;
            0, 1, 0, 0]

/-! ## The six independent anticommutators

Each is its own declaration.  `maxHeartbeats` is counted **per declaration**, so
sixteen matrix computations inside one theorem share a single budget and time
out, while six separate ones each get a fresh budget and finish easily.  The
reversed six follow by `add_comm` at no cost. -/

theorem gamma_anticomm_01 :
    euclideanGamma 0 * euclideanGamma 1 + euclideanGamma 1 * euclideanGamma 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [euclideanGamma, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

theorem gamma_anticomm_02 :
    euclideanGamma 0 * euclideanGamma 2 + euclideanGamma 2 * euclideanGamma 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [euclideanGamma, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

theorem gamma_anticomm_03 :
    euclideanGamma 0 * euclideanGamma 3 + euclideanGamma 3 * euclideanGamma 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [euclideanGamma, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

theorem gamma_anticomm_12 :
    euclideanGamma 1 * euclideanGamma 2 + euclideanGamma 2 * euclideanGamma 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [euclideanGamma, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

theorem gamma_anticomm_13 :
    euclideanGamma 1 * euclideanGamma 3 + euclideanGamma 3 * euclideanGamma 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [euclideanGamma, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

theorem gamma_anticomm_23 :
    euclideanGamma 2 * euclideanGamma 3 + euclideanGamma 3 * euclideanGamma 2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [euclideanGamma, Matrix.mul_apply, Fin.sum_univ_four, Complex.I_mul_I]

theorem gamma_anticomm_10 :
    euclideanGamma 1 * euclideanGamma 0 + euclideanGamma 0 * euclideanGamma 1 = 0 := by
  rw [add_comm]; exact gamma_anticomm_01

theorem gamma_anticomm_20 :
    euclideanGamma 2 * euclideanGamma 0 + euclideanGamma 0 * euclideanGamma 2 = 0 := by
  rw [add_comm]; exact gamma_anticomm_02

theorem gamma_anticomm_30 :
    euclideanGamma 3 * euclideanGamma 0 + euclideanGamma 0 * euclideanGamma 3 = 0 := by
  rw [add_comm]; exact gamma_anticomm_03

theorem gamma_anticomm_21 :
    euclideanGamma 2 * euclideanGamma 1 + euclideanGamma 1 * euclideanGamma 2 = 0 := by
  rw [add_comm]; exact gamma_anticomm_12

theorem gamma_anticomm_31 :
    euclideanGamma 3 * euclideanGamma 1 + euclideanGamma 1 * euclideanGamma 3 = 0 := by
  rw [add_comm]; exact gamma_anticomm_13

theorem gamma_anticomm_32 :
    euclideanGamma 3 * euclideanGamma 2 + euclideanGamma 2 * euclideanGamma 3 = 0 := by
  rw [add_comm]; exact gamma_anticomm_23

/-- Each gamma squares to the identity. -/
theorem euclideanGamma_sq (μ : LorentzIndex) :
    euclideanGamma μ * euclideanGamma μ = (1 : GammaMatrix) := by
  fin_cases μ <;>
    (ext i j;
     fin_cases i <;> fin_cases j <;>
       simp [euclideanGamma, Matrix.mul_apply, Fin.sum_univ_four,
         Matrix.one_apply, Complex.I_mul_I])

/-- **The witness works.**  Assembled from the twelve lemmas above; no matrix
    arithmetic happens here. -/
theorem euclideanGamma_isClifford : IsCliffordSystem euclideanGamma := by
  refine ⟨euclideanGamma_sq, ?_⟩
  intro μ ν hμν
  fin_cases μ <;> fin_cases ν <;>
    simp_all [gamma_anticomm_01, gamma_anticomm_02, gamma_anticomm_03,
      gamma_anticomm_12, gamma_anticomm_13, gamma_anticomm_23,
      gamma_anticomm_10, gamma_anticomm_20, gamma_anticomm_30,
      gamma_anticomm_21, gamma_anticomm_31, gamma_anticomm_32]

/-- Each gamma is Hermitian. -/
theorem euclideanGamma_isHermitian (μ : LorentzIndex) :
    (euclideanGamma μ)ᴴ = euclideanGamma μ := by
  fin_cases μ <;>
    (ext i j;
     fin_cases i <;> fin_cases j <;>
       simp [euclideanGamma, Matrix.conjTranspose_apply])

/-! ## Restated for `DiracEquation`

`DiracEquation` is written for an arbitrary `GammaSystem`.  The intended reading
is with the side condition below; `euclideanGamma_isClifford` shows the
condition is satisfiable, so the restricted statement is not vacuous. -/

/-- The Dirac equation together with the side condition its gamma system was
    always meant to carry. -/
def IsDiracProblem (gamma : GammaSystem) (g_s m : ℝ)
    (A : GaugePotential) (ψ : QuarkField) : Prop :=
  IsCliffordSystem gamma ∧ DiracEquation gamma g_s m A ψ

/-- For the explicit system the side condition is free, so the strengthened
    statement is not vacuous. -/
theorem isDiracProblem_euclideanGamma (g_s m : ℝ) (A : GaugePotential)
    (ψ : QuarkField) :
    IsDiracProblem euclideanGamma g_s m A ψ
      ↔ DiracEquation euclideanGamma g_s m A ψ :=
  ⟨fun h => h.2, fun h => ⟨euclideanGamma_isClifford, h⟩⟩

/-! ## Axiom audit -/

#print axioms gamma_anticomm_01
#print axioms euclideanGamma_isClifford
#print axioms euclideanGamma_sq
#print axioms euclideanGamma_isHermitian
#print axioms isDiracProblem_euclideanGamma

end CubeToSU3.QCD
