import CubeToSU3.SU3Global

/-!
# 規範模組之一:SU(3) 在 su(3) 上的伴隨作用

This is the first block of a gauge-theory module that is deliberately kept
**independent of any base space**.  Everything here is pure algebra inside
`SU(3)` and `su(3)`; no spacetime, no metric, no differentiation appears.  That
is the point: the same block serves a four-dimensional Lorentzian theory, a
lattice, a Riemannian four-manifold, or a flavour `SU(3)` with no space at all.
What differs between those is the *other* constraint set — Clifford relations,
a metric, a self-duality condition — not this.

The content is that conjugation

    Ad g X = g X g†

is a Lie-algebra automorphism of `su(3)`:

* it lands back in `su(3)` (`isSu3R_conj`),
* it is `ℝ`-linear (`AdLinear`),
* it preserves the bracket (`Ad_bracket`),
* and `g ↦ Ad g` is a group action (`Ad_one`, `Ad_mul`).

Two facts about `SU(3)` carry the whole file: `g† g = 1` supplies the
cancellation in the middle of every product, and `g g† = 1` supplies the other
side.  Tracelessness survives because the trace is cyclic.

Everything downstream in the gauge module rests on this block.  The local gauge
transformation law `A ↦ Ad g A + (1/g_s) g dg†` needs `Ad` to be a Lie-algebra
map for the field strength to transform covariantly; the covariant derivative
needs the same for its Leibniz rule.

Nothing here is a physical claim.
-/

noncomputable section

open Matrix

namespace CubeToSU3.Gauge

open CubeToSU3 CubeToSU3.Continuous

/-! ## Conjugation stays inside su(3) -/

/-- Conjugating an anti-Hermitian traceless matrix by a unitary keeps it
    anti-Hermitian and traceless.  Anti-Hermiticity is `(gXg†)† = gX†g†`;
    tracelessness is cyclicity of the trace together with `g† g = 1`. -/
theorem isSu3R_conj (g : SU3) {X : M3C} (hX : IsSu3R X) :
    IsSu3R ((g : M3C) * X * (g : M3C)ᴴ) := by
  obtain ⟨hanti, htr⟩ := hX
  have hgg : (g : M3C)ᴴ * (g : M3C) = 1 := g.2.1.1
  constructor
  · calc ((g : M3C) * X * (g : M3C)ᴴ)ᴴ
        = (g : M3C) * Xᴴ * (g : M3C)ᴴ := by
          simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (g : M3C) * (-X) * (g : M3C)ᴴ := by rw [hanti]
      _ = -((g : M3C) * X * (g : M3C)ᴴ) := by noncomm_ring
  · calc Matrix.trace ((g : M3C) * X * (g : M3C)ᴴ)
        = Matrix.trace ((g : M3C)ᴴ * ((g : M3C) * X)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((g : M3C)ᴴ * (g : M3C) * X) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace X := by rw [hgg, Matrix.one_mul]
      _ = 0 := htr

/-! ## The adjoint action -/

/-- `Ad g X = g X g†`, bundled with the proof that it stays in `su(3)`. -/
def Ad (g : SU3) (X : Su3R) : Su3R :=
  ⟨(g : M3C) * (X : M3C) * (g : M3C)ᴴ, isSu3R_conj g X.2⟩

@[simp] theorem coe_Ad (g : SU3) (X : Su3R) :
    (Ad g X : M3C) = (g : M3C) * (X : M3C) * (g : M3C)ᴴ := rfl

/-- The cancellation that every proof below uses: conjugation is
    multiplicative, because the inner `g† g` collapses. -/
theorem conj_mul_conj (g : SU3) (Z W : M3C) :
    (g : M3C) * Z * (g : M3C)ᴴ * ((g : M3C) * W * (g : M3C)ᴴ)
      = (g : M3C) * (Z * W) * (g : M3C)ᴴ := by
  have hgg : (g : M3C)ᴴ * (g : M3C) = 1 := g.2.1.1
  calc (g : M3C) * Z * (g : M3C)ᴴ * ((g : M3C) * W * (g : M3C)ᴴ)
      = (g : M3C) * Z * ((g : M3C)ᴴ * (g : M3C)) * W * (g : M3C)ᴴ := by
        noncomm_ring
    _ = (g : M3C) * Z * 1 * W * (g : M3C)ᴴ := by rw [hgg]
    _ = (g : M3C) * (Z * W) * (g : M3C)ᴴ := by noncomm_ring

/-! ## Group action -/

theorem Ad_one (X : Su3R) : Ad 1 X = X := by
  apply Subtype.ext
  show ((1 : SU3) : M3C) * (X : M3C) * ((1 : SU3) : M3C)ᴴ = (X : M3C)
  simp

theorem Ad_mul (g h : SU3) (X : Su3R) : Ad (g * h) X = Ad g (Ad h X) := by
  apply Subtype.ext
  show ((g * h : SU3) : M3C) * (X : M3C) * ((g * h : SU3) : M3C)ᴴ
      = (g : M3C) * ((h : M3C) * (X : M3C) * (h : M3C)ᴴ) * (g : M3C)ᴴ
  have hc : ((g * h : SU3) : M3C) = (g : M3C) * (h : M3C) := rfl
  rw [hc, Matrix.conjTranspose_mul]
  noncomm_ring

/-! ## Linearity -/

theorem Ad_add (g : SU3) (X Y : Su3R) : Ad g (X + Y) = Ad g X + Ad g Y := by
  apply Subtype.ext
  show (g : M3C) * ((X : M3C) + (Y : M3C)) * (g : M3C)ᴴ
      = (g : M3C) * (X : M3C) * (g : M3C)ᴴ
        + (g : M3C) * (Y : M3C) * (g : M3C)ᴴ
  noncomm_ring

theorem Ad_smul (g : SU3) (r : ℝ) (X : Su3R) : Ad g (r • X) = r • Ad g X := by
  apply Subtype.ext
  show (g : M3C) * (r • (X : M3C)) * (g : M3C)ᴴ
      = r • ((g : M3C) * (X : M3C) * (g : M3C)ᴴ)
  simp [Matrix.mul_smul, Matrix.smul_mul]

theorem Ad_sub (g : SU3) (X Y : Su3R) : Ad g (X - Y) = Ad g X - Ad g Y := by
  apply Subtype.ext
  show (g : M3C) * ((X : M3C) - (Y : M3C)) * (g : M3C)ᴴ
      = (g : M3C) * (X : M3C) * (g : M3C)ᴴ
        - (g : M3C) * (Y : M3C) * (g : M3C)ᴴ
  noncomm_ring

theorem Ad_zero (g : SU3) : Ad g 0 = 0 := by
  apply Subtype.ext
  show (g : M3C) * (0 : M3C) * (g : M3C)ᴴ = (0 : M3C)
  simp

/-- The adjoint action bundled as an `ℝ`-linear map. -/
def AdLinear (g : SU3) : Su3R →ₗ[ℝ] Su3R where
  toFun := Ad g
  map_add' := Ad_add g
  map_smul' := Ad_smul g

/-! ## The main property: the bracket is preserved

Stated at the matrix level with `bracketR`, because the bundled `su3Bracket`
lives in `QCDKinematics` and importing that would drag a base space into this
file.  `GaugeGlobal` re-states it for `Su3R` in one line. -/

/-- **`Ad g` is a Lie-algebra automorphism.**  This is the fact the whole gauge
    module rests on: it is what makes the field strength transform covariantly
    and what gives the covariant derivative its Leibniz rule.  Note that mere
    linearity is not enough — an arbitrary linear map does not commute with the
    bracket, and covariance would fail. -/
theorem Ad_bracketR (g : SU3) (X Y : M3C) :
    (g : M3C) * bracketR X Y * (g : M3C)ᴴ
      = bracketR ((g : M3C) * X * (g : M3C)ᴴ)
          ((g : M3C) * Y * (g : M3C)ᴴ) := by
  unfold bracketR
  rw [conj_mul_conj, conj_mul_conj]
  noncomm_ring

/-! ## Axiom audit -/

#print axioms isSu3R_conj
#print axioms conj_mul_conj
#print axioms Ad_one
#print axioms Ad_mul
#print axioms Ad_add
#print axioms Ad_smul
#print axioms Ad_sub
#print axioms Ad_bracketR

end CubeToSU3.Gauge
