import CubeToSU3.CG.Fundamental
import CubeToSU3.CG.BCJ

/-!
# 八膠子,與味質量的破缺

Two things that belong together: why the gauge bosons of colour are eight and
not nine, and what happens when the analogous *flavour* symmetry is broken by
unequal quark masses.  Colour is never broken; flavour always is.  The same
algebra describes both, and the difference shows up as one integer coefficient
being zero or not.

## Part 1 — eight gluons

* `E i j` with `i ≠ j` are the six colour-changing directions (the six roots,
  i.e. the six non-axial cube vertices of `RootMatch`), each traceless.
* `H1 = E₀₀ - E₁₁`, `H2 = E₁₁ - E₂₂` are the two Cartan directions, the
  colour-preserving gluons `g₇`, `g₈`.
* The ninth direction is the identity; `idm_trace` shows it has trace `3`, and
  `no_ninth_gluon` that no nonzero multiple of it is traceless.  That is the
  colour singlet removed along the body diagonal: **9 - 1 = 8**.
* `gluon_completeness` shows the eight span everything traceless: any integer
  matrix of trace zero is the stated combination of them.

## Part 2 — flavour breaking

With `M = diag(mu, md, ms)` the quark mass matrix,

    6·M = 2(mu+md+ms)·1 + 3(mu-md)·T₃ + (mu+md-2ms)·T₈

(`mass_decomposition`).  The first term is the symmetric part, invariant under
everything; the other two are the breaking, and each has a direct reading:

| coefficient | vanishes iff | symmetry |
|---|---|---|
| `mu - md` | `mu = md` | isospin SU(2) |
| `mu + md - 2ms` | `mu = md = ms` (with the first) | flavour SU(3) |

* `su3_exact_iff` — both coefficients vanish exactly when all three masses agree.
* `isospin_survives` — if `mu = md`, the mass matrix still commutes with the
  isospin generators `E₀₁`, `E₁₀`, `H1`, whatever `ms` is.
* `strangeness_breaks` — but it fails to commute with `E₀₂` as soon as
  `ms ≠ mu`.  This is why isospin is a far better symmetry than flavour SU(3):
  the residual symmetry of the physical mass matrix is SU(2) × U(1), not SU(3).

For colour the analogous matrix is a multiple of the identity — the three
colours of a quark have exactly equal mass — so both breaking coefficients are
identically zero and the symmetry is exact.  That single fact is the whole
difference between colour and flavour in this framework.

Exact integer arithmetic, no Mathlib.  Nothing here is a new physical claim.
-/

namespace CubeToSU3.CG

/-- The identity matrix. -/
def idm : Mat := fun i j => delta i j

/-! ## Part 1 — eight gluons -/

/-- The six colour-changing directions are traceless. -/
theorem offdiag_traceless : ∀ i j : Idx, i ≠ j → trace (E i j) = 0 := by decide

/-- The two Cartan directions are traceless. -/
theorem H1_traceless : trace H1 = 0 := by decide
theorem H2_traceless : trace H2 = 0 := by decide

/-- The ninth direction, the identity, has trace `3`. -/
theorem idm_trace : trace idm = 3 := by decide

/-- **Nine minus one.**  No nonzero multiple of the identity is traceless, so
the colour-singlet direction cannot be a gluon: there are eight, not nine. -/
theorem no_ninth_gluon (a : Int) (h : trace (fun i j => a * idm i j) = 0) : a = 0 := by
  simp [trace, idm, delta, sum3] at h
  omega

/-- The eight directions span all traceless matrices: with
`a = M 0 0` and `b = M 0 0 + M 1 1`,

  `M = Σ_{i≠j} M i j · E i j + a · H1 + b · H2`. -/
def gluonExp (M : Mat) : Mat := fun i j =>
  M 0 1 * E 0 1 i j + M 0 2 * E 0 2 i j
    + M 1 0 * E 1 0 i j + M 1 2 * E 1 2 i j
    + M 2 0 * E 2 0 i j + M 2 1 * E 2 1 i j
    + (M 0 0) * H1 i j + (M 0 0 + M 1 1) * H2 i j

/-- **Completeness of the eight gluons.**  Every traceless integer matrix is the
above combination; the eight directions are a basis of the colour algebra. -/
theorem gluon_completeness (M : Mat) (h : trace M = 0) :
    M 0 0 = gluonExp M 0 0 ∧ M 0 1 = gluonExp M 0 1 ∧ M 0 2 = gluonExp M 0 2
    ∧ M 1 0 = gluonExp M 1 0 ∧ M 1 1 = gluonExp M 1 1 ∧ M 1 2 = gluonExp M 1 2
    ∧ M 2 0 = gluonExp M 2 0 ∧ M 2 1 = gluonExp M 2 1 ∧ M 2 2 = gluonExp M 2 2 := by
  simp [trace, sum3] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [gluonExp, E, H1, H2, delta] <;> omega

/-! ## Part 2 — flavour breaking -/

/-- The quark mass matrix `diag(mu, md, ms)`. -/
def massM (mu md ms : Int) : Mat := fun i j =>
  match i.val, j.val with
  | 0, 0 => mu
  | 1, 1 => md
  | 2, 2 => ms
  | _, _ => 0

/-- `T₃ = diag(1,-1,0)`, the isospin direction. -/
def T3 : Mat := fun i j =>
  match i.val, j.val with | 0, 0 => 1 | 1, 1 => -1 | _, _ => 0

/-- `T₈ = diag(1,1,-2)`, the strangeness direction. -/
def T8 : Mat := fun i j =>
  match i.val, j.val with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => -2 | _, _ => 0

/-- **The decomposition.**  Symmetric part plus two breaking terms:

  `6·M = 2(mu+md+ms)·1 + 3(mu-md)·T₃ + (mu+md-2ms)·T₈`. -/
theorem mass_decomposition (mu md ms : Int) :
    (∀ i j : Idx,
      6 * massM mu md ms i j
        = 2 * (mu + md + ms) * idm i j
          + 3 * (mu - md) * T3 i j
          + (mu + md - 2 * ms) * T8 i j) := by
  intro i j
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨1, _⟩ | ⟨0, _⟩, ⟨2, _⟩
  | ⟨1, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨2, _⟩
  | ⟨2, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨2, _⟩ =>
      simp [massM, idm, T3, T8, delta] <;> omega

/-- Isospin is exact exactly when the first breaking coefficient vanishes. -/
theorem isospin_exact_iff (mu md : Int) : mu - md = 0 ↔ mu = md := by
  constructor <;> intro h <;> omega

/-- Flavour SU(3) is exact exactly when both breaking coefficients vanish. -/
theorem su3_exact_iff (mu md ms : Int) :
    (mu - md = 0 ∧ mu + md - 2 * ms = 0) ↔ (mu = md ∧ md = ms) := by
  constructor
  · intro h; exact ⟨by omega, by omega⟩
  · intro h; exact ⟨by omega, by omega⟩

/-- **Residual symmetry.**  If `mu = md`, the mass matrix still commutes with the
isospin generators, whatever `ms` is: isospin survives the breaking of SU(3). -/
theorem isospin_survives (m ms : Int) :
    (∀ i j : Idx, br (massM m m ms) (E 0 1) i j = 0)
    ∧ (∀ i j : Idx, br (massM m m ms) (E 1 0) i j = 0)
    ∧ (∀ i j : Idx, br (massM m m ms) H1 i j = 0) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro i j <;>
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨1, _⟩ | ⟨0, _⟩, ⟨2, _⟩
    | ⟨1, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨2, _⟩
    | ⟨2, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨2, _⟩ =>
        simp [br, mmul, massM, E, H1, delta, sum3] <;> omega

/-- But the strange direction is broken: the commutator with `E₀₂` is nonzero as
soon as `ms ≠ mu`.  Hence the residual symmetry is SU(2) × U(1), not SU(3). -/
theorem strangeness_breaks (mu md ms : Int) :
    br (massM mu md ms) (E 0 2) 0 2 = mu - ms := by
  simp [br, mmul, massM, E, delta, sum3]

/-- Colour, by contrast, has all three masses equal, so both breaking
coefficients vanish identically and the symmetry is exact. -/
theorem colour_unbroken (m : Int) :
    m - m = 0 ∧ m + m - 2 * m = 0 := by
  constructor <;> omega

end CubeToSU3.CG
