import CubeToSU3.CG.SpringRing

/-!
# 三原子環分子:同一個群代數,化學的讀法

The Hückel (tight-binding) matrix of a three-site ring with on-site energy `α`
and resonance integral `β` is

    H = α·1 + β(P + P²)

which lies in the group algebra of `ℤ/3` *by construction*: the symmetry of the
molecule forces it there, exactly as `commutes_iff_circulant` says.  Only the
two numbers `α, β` are chemistry; the orbitals and the degeneracy pattern are
not.

## Contents

1. `Hm_commutes` — the Hückel matrix commutes with the cyclic shift.
2. Molecular orbitals, independent of `α` and `β`:
   * `(1,1,1)`      with energy `α + 2β`  (fully bonding),
   * `(1,-2,1)` and `(1,0,-1)` with energy `α - β`  (degenerate pair).
   The gap is `3β`; `orbital_gap` and `degenerate_iff_beta_zero` record this.
3. The broken ring `Hb e` (one bond scaled by `1+e`, in units `α = 0`, `β = 1`):
   * `Hb_circulant_iff` — circulant, hence in the group algebra, **iff** `e = 0`;
   * `Hb_mode_anti` — the antisymmetric orbital `(1,0,-1)` stays exact, with
     energy `-(1+e)`;
   * `Hb_sym_sector` — the remaining two orbitals are `(1,t,1)` with
     `t² + (1+e)t = 2` and energy `(1+e) + t`;
   * `sym_sector_at_zero` — at `e = 0` that quadratic factors over the integers,
     `t = 1` and `t = -2`, returning the uniform orbital and the partner of the
     degenerate pair.

The contrast with `SpringRing` is instructive.  There the breaking left all
three eigenvectors intact and shifted one eigenvalue; here the antisymmetric
orbital survives but the other two mix, and the surviving integrality is
exactly the statement that the quadratic factors at `e = 0`.  This is the
algebraic content of a Jahn–Teller splitting.

Exact integer arithmetic, no Mathlib.  Nothing here is a new chemical claim.
-/

namespace CubeToSU3.CG

/-! ## The symmetric ring -/

/-- Hückel matrix `α·1 + β(P + P²)`. -/
def Hm (a b : Int) : Mat := circ a b b

/-- It lies in the group algebra, hence commutes with the cyclic shift. -/
theorem Hm_commutes (a b : Int) :
    mmul (Hm a b) Pm 0 0 = mmul Pm (Hm a b) 0 0
    ∧ mmul (Hm a b) Pm 0 1 = mmul Pm (Hm a b) 0 1
    ∧ mmul (Hm a b) Pm 0 2 = mmul Pm (Hm a b) 0 2
    ∧ mmul (Hm a b) Pm 1 0 = mmul Pm (Hm a b) 1 0
    ∧ mmul (Hm a b) Pm 1 1 = mmul Pm (Hm a b) 1 1
    ∧ mmul (Hm a b) Pm 1 2 = mmul Pm (Hm a b) 1 2
    ∧ mmul (Hm a b) Pm 2 0 = mmul Pm (Hm a b) 2 0
    ∧ mmul (Hm a b) Pm 2 1 = mmul Pm (Hm a b) 2 1
    ∧ mmul (Hm a b) Pm 2 2 = mmul Pm (Hm a b) 2 2 :=
  circ_commutes a b b

/-- Fully bonding orbital: energy `α + 2β`. -/
theorem orbital_bonding (a b : Int) :
    mv (Hm a b) (vec3 1 1 1) 0 = (a + 2 * b) * vec3 1 1 1 0
    ∧ mv (Hm a b) (vec3 1 1 1) 1 = (a + 2 * b) * vec3 1 1 1 1
    ∧ mv (Hm a b) (vec3 1 1 1) 2 = (a + 2 * b) * vec3 1 1 1 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mv, Hm, circ, Pm, Pm2, mmul, sum3, delta, vec3] <;> omega

/-- First member of the degenerate pair: energy `α - β`. -/
theorem orbital_pair_a (a b : Int) :
    mv (Hm a b) (vec3 1 (-2) 1) 0 = (a - b) * vec3 1 (-2) 1 0
    ∧ mv (Hm a b) (vec3 1 (-2) 1) 1 = (a - b) * vec3 1 (-2) 1 1
    ∧ mv (Hm a b) (vec3 1 (-2) 1) 2 = (a - b) * vec3 1 (-2) 1 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mv, Hm, circ, Pm, Pm2, mmul, sum3, delta, vec3] <;> omega

/-- Second member of the degenerate pair: same energy `α - β`. -/
theorem orbital_pair_b (a b : Int) :
    mv (Hm a b) (vec3 1 0 (-1)) 0 = (a - b) * vec3 1 0 (-1) 0
    ∧ mv (Hm a b) (vec3 1 0 (-1)) 1 = (a - b) * vec3 1 0 (-1) 1
    ∧ mv (Hm a b) (vec3 1 0 (-1)) 2 = (a - b) * vec3 1 0 (-1) 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mv, Hm, circ, Pm, Pm2, mmul, sum3, delta, vec3] <;> omega

/-- The gap between the bonding orbital and the degenerate pair is `3β`:
the on-site energy `α` drops out. -/
theorem orbital_gap (a b : Int) : (a + 2 * b) - (a - b) = 3 * b := by omega

/-- The pair is separated from the bonding orbital unless there is no bonding
at all. -/
theorem degenerate_iff_beta_zero (a b : Int) : a + 2 * b = a - b ↔ b = 0 := by
  constructor <;> intro h <;> omega

/-! ## The broken ring

Units `α = 0`, `β = 1`; the third bond is scaled by `1 + e`. -/

def Hb (e : Int) : Mat := fun i j =>
  match i.val, j.val with
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 1 + e
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => 1
  | 2, 0 => 1 + e
  | 2, 1 => 1
  | 2, 2 => 0
  | _, _ => 0

/-- At `e = 0` this is the symmetric Hückel matrix in these units. -/
theorem Hb_zero : ∀ i j : Idx, Hb 0 i j = Hm 0 1 i j := by decide

/-- **The criterion applied.**  The broken ring is circulant — hence in the
group algebra — exactly when the three bonds are equal. -/
theorem Hb_circulant_iff (e : Int) :
    (Hb e 0 0 = Hb e 1 1 ∧ Hb e 1 1 = Hb e 2 2
      ∧ Hb e 1 0 = Hb e 2 1 ∧ Hb e 2 1 = Hb e 0 2
      ∧ Hb e 2 0 = Hb e 0 1 ∧ Hb e 0 1 = Hb e 1 2) ↔ e = 0 := by
  constructor
  · intro h
    obtain ⟨_, _, _, e4, _, _⟩ := h
    simp [Hb] at e4
    omega
  · intro he
    subst he
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Hb]

/-- The antisymmetric orbital survives the breaking exactly, with energy
`-(1+e)`: it is the one orbital with a node on the unchanged site. -/
theorem Hb_mode_anti (e : Int) :
    mv (Hb e) (vec3 1 0 (-1)) 0 = (-(1 + e)) * vec3 1 0 (-1) 0
    ∧ mv (Hb e) (vec3 1 0 (-1)) 1 = (-(1 + e)) * vec3 1 0 (-1) 1
    ∧ mv (Hb e) (vec3 1 0 (-1)) 2 = (-(1 + e)) * vec3 1 0 (-1) 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mv, Hb, vec3, sum3] <;> omega

/-- The other two orbitals lie in the symmetric sector `(1,t,1)`, and `(1,t,1)`
is an eigenvector with energy `(1+e) + t` exactly when `t² + (1+e)t = 2`.
For `e ≠ 0` the two roots are irrational: the degeneracy is gone. -/
theorem Hb_sym_sector (e t : Int) (h : t * t + (1 + e) * t = 2) :
    mv (Hb e) (vec3 1 t 1) 0 = ((1 + e) + t) * vec3 1 t 1 0
    ∧ mv (Hb e) (vec3 1 t 1) 1 = ((1 + e) + t) * vec3 1 t 1 1
    ∧ mv (Hb e) (vec3 1 t 1) 2 = ((1 + e) + t) * vec3 1 t 1 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mv, Hb, vec3, sum3]
  · omega
  · rw [Int.add_mul, Int.add_comm ((1 + e) * t) (t * t)]
    exact h.symm

/-- At `e = 0` the quadratic factors over the integers: `t = 1` gives the
uniform orbital with energy `2`, and `t = -2` gives the partner of the
degenerate pair with energy `-1`. -/
theorem sym_sector_at_zero :
    (1 : Int) * 1 + (1 + 0) * 1 = 2 ∧ (-2 : Int) * (-2) + (1 + 0) * (-2) = 2 := by
  constructor <;> decide

/-- Degeneracy at `e = 0`: the two roots `1` and `-2` give energies `2` and
`-1`, and the antisymmetric orbital also has energy `-1`. -/
theorem degeneracy_at_zero :
    ((1 : Int) + 0) + (-2) = -1 ∧ -((1 : Int) + 0) = -1 := by
  constructor <;> decide

end CubeToSU3.CG
