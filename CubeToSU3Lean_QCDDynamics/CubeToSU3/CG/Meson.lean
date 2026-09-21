import CubeToSU3.CG.Fundamental

/-!
# `3 ⊗ 3̄ = 8 ⊕ 1`

Here `t i j` is the coefficient of `|q_i q̄_j⟩`, and the action is
`T ⊗ 1 + 1 ⊗ (-Tᵀ)` (`act33bar`).

Unnormalised integer states:

* `singlet = Σ_i |i ī⟩`, norm 3. Normalised: `(uū + dd̄ + ss̄)/√3`.
* `pi0     = uū - dd̄`,  norm 2. Normalised: `(uū - dd̄)/√2`.
* `eta8    = uū + dd̄ - 2 ss̄`, norm 6. Normalised: `(uū + dd̄ - 2ss̄)/√6`.
* the six off-diagonal kets `|i j̄⟩`, `i ≠ j`, norm 1:
  `π⁺ = ud̄`, `π⁻ = dū`, `K⁺ = us̄`, `K⁰ = ds̄`, `K̄⁰ = sd̄`, `K⁻ = sū`.

**Phase caveat.** This file uses the plain tensor phases above. When these
states are later combined with SU(2) Clebsch–Gordan coefficients (isospin
amplitudes), the anti-quark isospin doublet must be taken as `(d̄, -ū)` to match
Condon–Shortley; some meson states then acquire an overall sign. Norms,
orthogonality and invariance proved here are unaffected.
-/

namespace CubeToSU3.CG

def singlet : Ten := fun i j => delta i j
def pi0 : Ten := fun i j => ket u u i j - ket d d i j
def eta8 : Ten := fun i j => ket u u i j + ket d d i j - 2 * ket s s i j

def piPlus  : Ten := ket u d
def piMinus : Ten := ket d u
def KPlus   : Ten := ket u s
def KZero   : Ten := ket d s
def KZeroBar : Ten := ket s d
def KMinus  : Ten := ket s u

/-- Trace of a `3 ⊗ 3̄` tensor: its overlap with the singlet. -/
def ttrace (t : Ten) : Int := sum3 (fun i => t i i)

/-! ## The singlet -/

/-- The singlet is annihilated by every `T ∈ gl(3)`, hence it is invariant. -/
theorem singlet_invariant :
    ∀ a b i j : Idx, act33bar (E a b) singlet i j = 0 := by decide

theorem singlet_norm : dot singlet singlet = 3 := by decide

/-! ## The two zero-weight octet states -/

theorem pi0_norm : dot pi0 pi0 = 2 := by decide
theorem eta8_norm : dot eta8 eta8 = 6 := by decide

theorem singlet_perp_pi0 : dot singlet pi0 = 0 := by decide
theorem singlet_perp_eta8 : dot singlet eta8 = 0 := by decide
theorem pi0_perp_eta8 : dot pi0 eta8 = 0 := by decide

/-! ## The octet as the traceless part

For each basis ket define its octet projection `oct m n = 3|m n̄⟩ - δ_mn · singlet`. -/

def oct (m n : Idx) : Ten := fun i j => 3 * ket m n i j - delta m n * singlet i j

/-- Completeness: `3 |m n̄⟩ = oct m n + δ_mn · singlet`. With `9 = 8 + 1`,
this is `3 ⊗ 3̄ = 8 ⊕ 1`. -/
theorem meson_completeness :
    ∀ m n i j : Idx, 3 * ket m n i j = oct m n i j + delta m n * singlet i j := by decide

/-- Every octet projection is traceless, i.e. orthogonal to the singlet. -/
theorem oct_traceless : ∀ m n : Idx, ttrace (oct m n) = 0 := by decide

theorem oct_perp_singlet : ∀ m n : Idx, dot (oct m n) singlet = 0 := by decide

/-- The traceless subspace is invariant: acting with any generator keeps the
octet orthogonal to the singlet. -/
theorem oct_invariant :
    ∀ a b m n : Idx, ttrace (act33bar (E a b) (oct m n)) = 0 := by decide

/-- `pi0` and `eta8` are octet states (traceless). -/
theorem pi0_traceless : ttrace pi0 = 0 := by decide
theorem eta8_traceless : ttrace eta8 = 0 := by decide

/-! ## Weights: the octet is the root hexagon plus two zero weights

A diagonal generator `E a a` measures `δ_ai - δ_aj` on `|i j̄⟩`, so the ket
`|i j̄⟩` has weight `w_i - w_j`: a difference of two cube vertices. -/

theorem ket_cartan_eigen :
    ∀ a i j p q : Idx,
      act33bar (E a a) (ket i j) p q = (delta a i - delta a j) * ket i j p q := by
  decide

/-- The six off-diagonal kets sit at nonzero weights (the six roots). -/
theorem offdiag_weight_nonzero :
    ∀ i j : Idx, i ≠ j → (w i).add (w j).neg ≠ Wt.zero := by decide

/-- The three diagonal kets all sit at weight zero; after removing the singlet
they leave exactly the two Cartan states `pi0`, `eta8`. -/
theorem diag_weight_zero : ∀ i : Idx, (w i).add (w i).neg = Wt.zero := by decide

/-- `pi0` and `eta8` are annihilated by both Cartan generators: zero weight. -/
theorem pi0_zero_weight :
    ∀ p q : Idx, act33bar H1 pi0 p q = 0 ∧ act33bar H2 pi0 p q = 0 := by decide

theorem eta8_zero_weight :
    ∀ p q : Idx, act33bar H1 eta8 p q = 0 ∧ act33bar H2 eta8 p q = 0 := by decide

end CubeToSU3.CG
