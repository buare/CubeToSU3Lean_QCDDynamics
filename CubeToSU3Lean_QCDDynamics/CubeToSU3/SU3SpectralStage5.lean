import CubeToSU3.SU3SpectralStage4

/-!
# Removing `UnitarySpectralTheorem3`, stage 5: assembly

Stage 4 diagonalises a unitary `B` *provided* `1 + B` is invertible.  Stage 1
supplies a unit phase `μ` making `μ • 1 + A` nonsingular for an arbitrary `A`.
This file glues the two together and packages the result in the shape
`SU3Surjectivity.lean` asks for, then discharges the standing hypothesis.

Three things happen here, none of them new mathematics.

* **Phase algebra.**  With `ν = μ⁻¹`, the matrix `B = ν • A` is unitary and
  satisfies `μ • 1 + A = μ • (1 + B)`, so `det (1 + B) = μ⁻³ det (μ • 1 + A) ≠ 0`
  and stage 4 applies.  Multiplying back by `μ` scales the diagonal.

* **Unit modulus.**  The target type wants `Fin 3 → unitary ℂ`, so the diagonal
  entries must lie on the circle.  Rather than tracing the Cayley formula, we
  read it off structurally: conjugating `Aᴴ A = 1` through the diagonalisation
  gives `Dᴴ D = 1`, and a diagonal matrix is unitary exactly when each entry is.

* **Subtype transport.**  `U : M3C` into `unitary M3C`, each entry into
  `unitary ℂ`, and `ᴴ` into `star`.

The final theorem `expSU3_surjective` has no hypotheses left.
-/

noncomputable section

open Matrix Complex

namespace CubeToSU3.Continuous

/-! ## Cancelling a unitary conjugation -/

theorem conj_cancel {U : M3C} (hU' : Uᴴ * U = 1) {X Y : M3C}
    (h : U * X * Uᴴ = U * Y * Uᴴ) : X = Y := by
  calc X = Uᴴ * U * X * (Uᴴ * U) := by rw [hU', one_mul, mul_one]
    _ = Uᴴ * (U * X * Uᴴ) * U := by noncomm_ring
    _ = Uᴴ * (U * Y * Uᴴ) * U := by rw [h]
    _ = Uᴴ * U * Y * (Uᴴ * U) := by noncomm_ring
    _ = Y := by rw [hU', one_mul, mul_one]

/-! ## A unitary diagonal matrix has unit entries -/

theorem diagonal_entries_unit_of_unitary (w : Fin 3 → ℂ)
    (h : (Matrix.diagonal w)ᴴ * Matrix.diagonal w = 1) (k : Fin 3) :
    star (w k) * w k = 1 ∧ w k * star (w k) = 1 := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal] at h
  have hk : star (w k) * w k = 1 := by
    have := congrFun (congrFun (congrArg (fun M : M3C => M) h) k) k
    simpa [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using this
  exact ⟨hk, by rw [mul_comm]; exact hk⟩

/-! ## The spectral theorem, unconditionally -/

/-- **Stage 5.**  Every `3 × 3` unitary matrix is unitarily diagonalisable with
    unit-modulus diagonal entries. -/
theorem unitarySpectralTheorem3 : UnitarySpectralTheorem3 := by
  intro A hA
  have hAA : Aᴴ * A = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').mp hA
    rwa [Matrix.star_eq_conjTranspose] at this
  -- stage 1: a phase clearing the eigenvalue `-1`
  obtain ⟨μ, hμnorm, hμdet⟩ := exists_unit_phase_add_det_ne_zero A
  have hμ0 : μ ≠ 0 := by
    intro hc
    rw [hc] at hμnorm
    simp at hμnorm
  set ν : ℂ := μ⁻¹ with hνdef
  have hν0 : ν ≠ 0 := inv_ne_zero hμ0
  have hstarν : star ν * ν = 1 := by
    have : Complex.abs ν = 1 := by
      have hμabs : Complex.abs μ = 1 := by
        rw [← Complex.norm_eq_abs]; exact hμnorm
      rw [hνdef, map_inv₀, hμabs, inv_one]
    have h2 : star ν * ν = ((Complex.normSq ν : ℝ) : ℂ) := by
      rw [mul_comm]; exact Complex.mul_conj ν
    rw [h2, Complex.normSq_eq_abs, this]
    norm_num
  -- the rotated matrix
  set B : M3C := ν • A with hBdef
  have hBB : Bᴴ * B = 1 := by
    rw [hBdef, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hAA, hstarν, one_smul]
  have hBdet : IsUnit ((1 : M3C) + B).det := by
    have hfac : Matrix.scalar (Fin 3) μ + A = μ • ((1 : M3C) + B) := by
      rw [hBdef, smul_add, smul_smul, hνdef, mul_inv_cancel₀ hμ0, one_smul]
      congr 1
      ext i j
      by_cases hij : i = j
      · subst hij; simp [Matrix.scalar_apply, Matrix.one_apply_eq]
      · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij,
          Matrix.one_apply_ne hij, hij]
    rw [hfac, Matrix.det_smul] at hμdet
    refine isUnit_iff_ne_zero.2 ?_
    intro hc
    rw [hc, mul_zero] at hμdet
    exact hμdet rfl
  -- stage 4
  obtain ⟨U, w, hU, hU', hBeq⟩ := unitary_diagonalizable_of_one_add_isUnit B hBB hBdet
  set v : Fin 3 → ℂ := fun k => μ * w k with hvdef
  have hAsmul : A = μ • B := by
    rw [hBdef, smul_smul, hνdef, mul_inv_cancel₀ hμ0, one_smul]
  have hsmuldiag : μ • Matrix.diagonal w = Matrix.diagonal v := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hvdef, Matrix.diagonal_apply_eq]
    · simp [Matrix.diagonal_apply_ne _ hij, hij]
  have hAeq : A = U * Matrix.diagonal v * Uᴴ := by
    rw [hAsmul, hBeq, conj_smul, hsmuldiag]
  have hDD : (Matrix.diagonal v)ᴴ * Matrix.diagonal v = 1 := by
    refine conj_cancel hU' ?_
    rw [← conj_mul hU', conj_one hU]
    calc U * (Matrix.diagonal v)ᴴ * Uᴴ * (U * Matrix.diagonal v * Uᴴ)
        = Aᴴ * A := by
          rw [hAeq]
          simp only [Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose]
          noncomm_ring
      _ = 1 := hAA
  refine ⟨⟨U, ?_⟩, fun k => ⟨v k, ?_⟩, ?_⟩
  · rw [unitary.mem_iff, Matrix.star_eq_conjTranspose]
    exact ⟨hU', hU⟩
  · exact unitary.mem_iff.2 (diagonal_entries_unit_of_unitary v hDD k)
  · -- `star` on matrices is `conjTranspose` by `rfl`, and the subtype coercions
    -- reduce definitionally, so no rewriting is needed (and none is possible:
    -- rewriting `star U` would break the membership proof carried by `⟨U, _⟩`).
    exact hAeq

/-- **The standing hypothesis is discharged.**  `exp : su(3) → SU(3)` is
    surjective, with no assumptions. -/
theorem expSU3_surjective : ExponentialSurjective :=
  expSU3_surjective_of_unitarySpectralTheorem3 unitarySpectralTheorem3

/-! ## Axiom audit -/

#print axioms conj_cancel
#print axioms diagonal_entries_unit_of_unitary
#print axioms unitarySpectralTheorem3
#print axioms expSU3_surjective

end CubeToSU3.Continuous
