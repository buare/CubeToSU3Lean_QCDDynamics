import CubeToSU3.CG.BCJ

/-!
# 三彈簧環:物理方程的係數矩陣與群代數

A classical, pre-quantum example of the framework.  Three equal masses on a
ring, each pair joined by a spring of stiffness `k`, moving tangentially:

    m ẍᵢ = k (xᵢ₊₁ + xᵢ₋₁ - 2xᵢ)

After `τ = t √(k/m)` the masses and stiffnesses disappear and

    ẍ = -K x,      K = 2·1 - P - P²  =  -D²

so the coefficient matrix of the physical equations *is* `-D²`, with
`D = P - P²` the unique antisymmetric element of the group algebra of `ℤ/3`.

## Contents

1. `commutes_iff_circulant` — **the criterion**: a matrix commutes with the
   cyclic shift `P` iff its entries depend only on `i - j`, i.e. iff it lies in
   the group algebra.  This upgrades "the coefficients happen to lie in the
   group algebra" to an equivalence.
2. `circulant_eq_circ` — such a matrix is exactly `a·1 + b·P + c·P²`.
3. `Kspring_eq_negDsq` — the spring matrix equals `-D²`.
4. Normal modes of the symmetric ring: `0` (rigid rotation) and `3` (doubly
   degenerate).  In physical units the frequency ratio is `√3`, the `3` being
   `|(1,1,1)|²`; it does not depend on `m` or `k`.
5. The broken ring `Ks e` (one spring scaled by `1 + e`):
   * `Ks_commutes_iff` — it lies in the group algebra **iff** `e = 0`;
   * the three eigenvectors are unchanged and integral, with eigenvalues
     `0`, `3`, `3 + 2e`: the degeneracy splits by exactly `2e`, linearly, with
     no higher-order corrections;
   * the zero mode survives: rigid rotation costs nothing whatever the springs.

Statements are entrywise so that no case-splitting tactic is needed; everything
is exact integer arithmetic with no Mathlib.  Nothing here is a new physical
claim: it is the classical normal-mode calculation, arranged so that the
symmetric part and the breaking are separated.
-/

namespace CubeToSU3.CG

/-! ## The cyclic shift and the group algebra -/

/-- Cyclic shift `P`: `P i j = 1` exactly when `i = j + 1`. -/
def Pm : Mat := fun i j => delta i (j + 1)

/-- `P²`. -/
def Pm2 : Mat := mmul Pm Pm

/-- `D = P - P²`. -/
def Dm : Mat := fun i j => Pm i j - Pm2 i j

/-- A general element `a·1 + b·P + c·P²` of the group algebra of `ℤ/3`. -/
def circ (a b c : Int) : Mat :=
  fun i j => a * delta i j + b * Pm i j + c * Pm2 i j

theorem Pm_cubed : ∀ i j : Idx, mmul Pm Pm2 i j = delta i j := by decide

/-- `D² = -2·1 + P + P²`, the group-algebra form of `D² = -3·1 + J`. -/
theorem Dm_sq : ∀ i j : Idx, mmul Dm Dm i j = circ (-2) 1 1 i j := by decide

/-! ## The criterion -/

/-- Every element of the group algebra commutes with `P`. -/
theorem circ_commutes (a b c : Int) :
    mmul (circ a b c) Pm 0 0 = mmul Pm (circ a b c) 0 0
    ∧ mmul (circ a b c) Pm 0 1 = mmul Pm (circ a b c) 0 1
    ∧ mmul (circ a b c) Pm 0 2 = mmul Pm (circ a b c) 0 2
    ∧ mmul (circ a b c) Pm 1 0 = mmul Pm (circ a b c) 1 0
    ∧ mmul (circ a b c) Pm 1 1 = mmul Pm (circ a b c) 1 1
    ∧ mmul (circ a b c) Pm 1 2 = mmul Pm (circ a b c) 1 2
    ∧ mmul (circ a b c) Pm 2 0 = mmul Pm (circ a b c) 2 0
    ∧ mmul (circ a b c) Pm 2 1 = mmul Pm (circ a b c) 2 1
    ∧ mmul (circ a b c) Pm 2 2 = mmul Pm (circ a b c) 2 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [mmul, circ, Pm, Pm2, delta, sum3] <;> omega

/-- **The criterion.**  Commuting with `P` is equivalent to being circulant:
the entries depend only on `i - j`.  Together with `circ_commutes` this says
that the coefficient matrix of a `ℤ/3`-symmetric linear system lies in the
group algebra, and that nothing else does. -/
theorem commutes_iff_circulant (M : Mat) :
    (mmul M Pm 0 0 = mmul Pm M 0 0
      ∧ mmul M Pm 0 1 = mmul Pm M 0 1
      ∧ mmul M Pm 0 2 = mmul Pm M 0 2
      ∧ mmul M Pm 1 0 = mmul Pm M 1 0
      ∧ mmul M Pm 1 1 = mmul Pm M 1 1
      ∧ mmul M Pm 1 2 = mmul Pm M 1 2
      ∧ mmul M Pm 2 0 = mmul Pm M 2 0
      ∧ mmul M Pm 2 1 = mmul Pm M 2 1
      ∧ mmul M Pm 2 2 = mmul Pm M 2 2)
    ↔ (M 0 0 = M 1 1 ∧ M 1 1 = M 2 2
        ∧ M 1 0 = M 2 1 ∧ M 2 1 = M 0 2
        ∧ M 2 0 = M 0 1 ∧ M 0 1 = M 1 2) := by
  constructor
  · intro h
    obtain ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := h
    simp [mmul, Pm, delta, sum3] at h00 h01 h02 h10 h11 h12 h20 h21 h22
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · intro h
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [mmul, Pm, delta, sum3] <;> omega

/-- A circulant matrix is exactly `a·1 + b·P + c·P²` with `a = M 0 0`,
`b = M 1 0`, `c = M 2 0`. -/
theorem circulant_eq_circ (M : Mat)
    (h : M 0 0 = M 1 1 ∧ M 1 1 = M 2 2
        ∧ M 1 0 = M 2 1 ∧ M 2 1 = M 0 2
        ∧ M 2 0 = M 0 1 ∧ M 0 1 = M 1 2) :
    M 0 0 = circ (M 0 0) (M 1 0) (M 2 0) 0 0
    ∧ M 0 1 = circ (M 0 0) (M 1 0) (M 2 0) 0 1
    ∧ M 0 2 = circ (M 0 0) (M 1 0) (M 2 0) 0 2
    ∧ M 1 0 = circ (M 0 0) (M 1 0) (M 2 0) 1 0
    ∧ M 1 1 = circ (M 0 0) (M 1 0) (M 2 0) 1 1
    ∧ M 1 2 = circ (M 0 0) (M 1 0) (M 2 0) 1 2
    ∧ M 2 0 = circ (M 0 0) (M 1 0) (M 2 0) 2 0
    ∧ M 2 1 = circ (M 0 0) (M 1 0) (M 2 0) 2 1
    ∧ M 2 2 = circ (M 0 0) (M 1 0) (M 2 0) 2 2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [circ, Pm, Pm2, mmul, sum3, delta] <;> omega

/-! ## The symmetric ring -/

/-- The spring matrix, read off from the equations of motion. -/
def Kspring : Mat := circ 2 (-1) (-1)

/-- The physical coefficient matrix is minus the square of `D`. -/
theorem Kspring_eq_negDsq : ∀ i j : Idx, Kspring i j = - mmul Dm Dm i j := by
  decide

/-! ## Normal modes -/

def vec3 (x y z : Int) : Vec :=
  fun i => match i.val with | 0 => x | 1 => y | _ => z

def mv (M : Mat) (v : Vec) : Vec := fun i => sum3 (fun j => M i j * v j)

/-- Rigid rotation: eigenvalue `0`. -/
theorem mode_zero : ∀ i : Idx, mv Kspring (vec3 1 1 1) i = 0 := by decide

/-- Eigenvalue `3`, first mode. -/
theorem mode_three_a :
    ∀ i : Idx, mv Kspring (vec3 1 (-2) 1) i = 3 * vec3 1 (-2) 1 i := by decide

/-- Eigenvalue `3`, second mode: the pair is degenerate. -/
theorem mode_three_b :
    ∀ i : Idx, mv Kspring (vec3 1 0 (-1)) i = 3 * vec3 1 0 (-1) i := by decide

/-! ## The broken ring -/

/-- Coefficient matrix with the third spring scaled by `1 + e`. -/
def Ks (e : Int) : Mat := fun i j =>
  match i.val, j.val with
  | 0, 0 => 2 + e
  | 0, 1 => -1
  | 0, 2 => -(1 + e)
  | 1, 0 => -1
  | 1, 1 => 2
  | 1, 2 => -1
  | 2, 0 => -(1 + e)
  | 2, 1 => -1
  | 2, 2 => 2 + e
  | _, _ => 0

/-- At `e = 0` the broken matrix is the symmetric one. -/
theorem Ks_zero : ∀ i j : Idx, Ks 0 i j = Kspring i j := by decide

/-- **The criterion applied.**  The broken ring is circulant — hence lies in the
group algebra — exactly when the springs are equal. -/
theorem Ks_commutes_iff (e : Int) :
    (Ks e 0 0 = Ks e 1 1 ∧ Ks e 1 1 = Ks e 2 2
      ∧ Ks e 1 0 = Ks e 2 1 ∧ Ks e 2 1 = Ks e 0 2
      ∧ Ks e 2 0 = Ks e 0 1 ∧ Ks e 0 1 = Ks e 1 2) ↔ e = 0 := by
  constructor
  · intro h
    obtain ⟨e1, _, _, _, _, _⟩ := h
    simp [Ks] at e1
    omega
  · intro he
    subst he
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Ks]

/-- The rigid rotation survives the breaking: still eigenvalue `0`. -/
theorem broken_mode_zero (e : Int) :
    mv (Ks e) (vec3 1 1 1) 0 = 0
    ∧ mv (Ks e) (vec3 1 1 1) 1 = 0
    ∧ mv (Ks e) (vec3 1 1 1) 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mv, Ks, vec3, sum3] <;> omega

/-- One partner of the degenerate pair keeps eigenvalue `3`. -/
theorem broken_mode_three (e : Int) :
    mv (Ks e) (vec3 1 (-2) 1) 0 = 3 * vec3 1 (-2) 1 0
    ∧ mv (Ks e) (vec3 1 (-2) 1) 1 = 3 * vec3 1 (-2) 1 1
    ∧ mv (Ks e) (vec3 1 (-2) 1) 2 = 3 * vec3 1 (-2) 1 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mv, Ks, vec3, sum3] <;> omega

/-- The other partner moves to `3 + 2e`: the degeneracy splits by exactly `2e`,
linearly, with no higher-order corrections. -/
theorem broken_mode_split (e : Int) :
    mv (Ks e) (vec3 1 0 (-1)) 0 = (3 + 2 * e) * vec3 1 0 (-1) 0
    ∧ mv (Ks e) (vec3 1 0 (-1)) 1 = (3 + 2 * e) * vec3 1 0 (-1) 1
    ∧ mv (Ks e) (vec3 1 0 (-1)) 2 = (3 + 2 * e) * vec3 1 0 (-1) 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mv, Ks, vec3, sum3] <;> omega

/-- Degeneracy holds exactly when the symmetry does. -/
theorem degenerate_iff (e : Int) : (3 : Int) = 3 + 2 * e ↔ e = 0 := by
  constructor <;> intro h <;> omega

end CubeToSU3.CG
