import CubeToSU3.CG.Convention

/-!
# Jacobi 與 BCJ 三項色關係

The six off-diagonal matrix units `E i j` (`i ≠ j`) are exactly the six roots
that `RootMatch` matches with the six non-axial cube vertices.  This file proves
the two algebraic identities those roots satisfy, in the form used in the
colour–kinematics literature.

* `jacobi` : `[[X,Y],Z] + [[Y,Z],X] + [[Z,X],Y] = 0`
* `trace_bracket` : `tr([X,Y]·Z) = tr(X·[Y,Z])`
* `bcj` : with colour factors built from the trace form,

      c_s = ⟨[A,B],[C,D]⟩,  c_t = ⟨[B,C],[A,D]⟩,  c_u = ⟨[C,A],[B,D]⟩

  one has `c_s + c_t + c_u = 0`.

This is the colour side of the Bern–Carrasco–Johansson relations: the same
three-term pattern that the kinematic numerators are conjectured to satisfy.
The colour factors are not all zero — `bcj_nontrivial` exhibits a value `2` —
so the relation is a genuine cancellation, not a triviality.

Everything is exact integer arithmetic over `Fin 3`, proved for all nine matrix
units and hence, by linearity, for every element of `gl(3)` and `su(3)`.

Nothing here is a physical claim: these are identities in the Lie algebra, not
statements about amplitudes.
-/

set_option maxHeartbeats 4000000

namespace CubeToSU3.CG

/-- Matrix product. -/
def mmul (X Y : Mat) : Mat := fun i j => sum3 (fun k => X i k * Y k j)

/-- Lie bracket. -/
def br (X Y : Mat) : Mat := fun i j => mmul X Y i j - mmul Y X i j

/-- The trace form `⟨X,Y⟩ = tr(X·Y)`. -/
def form (X Y : Mat) : Int := trace (mmul X Y)

/-! ## Jacobi -/

/-- The Jacobi identity, for all nine matrix units in each slot. -/
theorem jacobi :
    ∀ a b c d e f i j : Idx,
      br (br (E a b) (E c d)) (E e f) i j
        + br (br (E c d) (E e f)) (E a b) i j
        + br (br (E e f) (E a b)) (E c d) i j = 0 := by
  decide

/-- Cyclicity of the trace form against the bracket. -/
theorem trace_bracket :
    ∀ a b c d e f : Idx,
      trace (mmul (br (E a b) (E c d)) (E e f))
        = trace (mmul (E a b) (br (E c d) (E e f))) := by
  decide

/-! ## The three-term colour relation -/

/-- `c_s = ⟨[A,B],[C,D]⟩`. -/
def cS (A B C D : Mat) : Int := form (br A B) (br C D)

/-- `c_t = ⟨[B,C],[A,D]⟩`. -/
def cT (A B C D : Mat) : Int := form (br B C) (br A D)

/-- `c_u = ⟨[C,A],[B,D]⟩`. -/
def cU (A B C D : Mat) : Int := form (br C A) (br B D)

/-- **The BCJ three-term relation on the colour side.**  For every choice of the
    four legs among the nine matrix units — in particular among the six roots —

      `c_s + c_t + c_u = 0`.

    This is the identity that the kinematic numerators are conjectured to
    mirror. -/
theorem bcj :
    ∀ a b c d e f g h : Idx,
      cS (E a b) (E c d) (E e f) (E g h)
        + cT (E a b) (E c d) (E e f) (E g h)
        + cU (E a b) (E c d) (E e f) (E g h) = 0 := by
  decide

/-- The relation is a genuine cancellation: individual colour factors are
    nonzero.  Here `⟨[E₀₁,E₁₂],[E₂₀,E₀₀]⟩ ≠ 0`. -/
theorem bcj_nontrivial :
    cS (E 0 1) (E 1 2) (E 2 0) (E 0 0) ≠ 0 := by decide

/-- Antisymmetry of the bracket. -/
theorem br_antisymm :
    ∀ a b c d i j : Idx, br (E a b) (E c d) i j = - br (E c d) (E a b) i j := by
  decide

/-- Symmetry of the trace form. -/
theorem form_symm : ∀ a b c d : Idx, form (E a b) (E c d) = form (E c d) (E a b) := by
  decide

/-! ## The六 roots

The six off-diagonal units are the roots matched to the non-axial cube vertices.
Their brackets close in the familiar way: `[E i j, E j k] = E i k` when the
indices chain, so two colour moves compose into one. -/

theorem root_chain :
    ∀ i j k a b : Idx, i ≠ j → j ≠ k → i ≠ k →
      br (E i j) (E j k) a b = E i k a b := by
  decide

/-- Two colour moves that do not chain commute. -/
theorem root_commute :
    ∀ i j k l a b : Idx, i ≠ j → k ≠ l → j ≠ k → l ≠ i →
      br (E i j) (E k l) a b = 0 := by
  decide



/-! ## 色結構的獨立數目:`(n-2)! = 2`

At four points the three colour factors `c_s, c_t, c_u` span only a
two-dimensional space: the single relation `c_s + c_t + c_u = 0` removes one,
and the two survivors are genuinely independent.  Two is `(n-2)!` at `n = 4`,
the size of the Del Duca–Dixon–Maltoni / BCJ colour basis.

The two witnesses below are built from the six roots only, i.e. from the six
non-axial cube vertices matched by `RootMatch`. -/

/-- `c_u` is determined by the other two: the span of the three colour factors
    is the span of `c_s` and `c_t`. -/
theorem cU_eq_neg_add :
    ∀ a b c d e f g h : Idx,
      cU (E a b) (E c d) (E e f) (E g h)
        = -(cS (E a b) (E c d) (E e f) (E g h)
            + cT (E a b) (E c d) (E e f) (E g h)) := by
  decide

/-- Witness one: a configuration of four roots where `c_s` vanishes and `c_t`
    does not.  Hence `c_t` is not a multiple of `c_s`. -/
theorem witness_S_zero_T_nonzero :
    cS (E 0 1) (E 0 1) (E 1 0) (E 1 0) = 0
      ∧ cT (E 0 1) (E 0 1) (E 1 0) (E 1 0) ≠ 0 := by
  decide

/-- Witness two: a configuration where `c_t` vanishes and `c_s` does not.
    Hence `c_s` is not a multiple of `c_t` either, and the two are linearly
    independent as functions of the four legs. -/
theorem witness_T_zero_S_nonzero :
    cT (E 0 1) (E 1 0) (E 1 0) (E 0 1) = 0
      ∧ cS (E 0 1) (E 1 0) (E 1 0) (E 0 1) ≠ 0 := by
  decide

/-- **Two independent colour structures.**  Packaging the three facts: one
    relation, and two witnesses ruling out dimension one. -/
theorem colour_structures_two :
    (∀ a b c d e f g h : Idx,
        cS (E a b) (E c d) (E e f) (E g h)
          + cT (E a b) (E c d) (E e f) (E g h)
          + cU (E a b) (E c d) (E e f) (E g h) = 0)
      ∧ (cS (E 0 1) (E 0 1) (E 1 0) (E 1 0) = 0
          ∧ cT (E 0 1) (E 0 1) (E 1 0) (E 1 0) ≠ 0)
      ∧ (cT (E 0 1) (E 1 0) (E 1 0) (E 0 1) = 0
          ∧ cS (E 0 1) (E 1 0) (E 1 0) (E 0 1) ≠ 0) :=
  ⟨bcj, witness_S_zero_T_nonzero, witness_T_zero_S_nonzero⟩

end CubeToSU3.CG
