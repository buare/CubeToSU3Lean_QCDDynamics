import CubeToSU3.Cube

/-!
# The replacement test

Claim under test: is the cube load-bearing, or is it scaffolding?

Method: swap `Q₃` for the hexagon `C₆` and recompile. Whatever still holds was
never about the cube. Whatever breaks is the cube's actual contribution.

`C₆` is not an arbitrary choice. Deleting the two poles `000` and `111` from
`Q₃` leaves six vertices of degree two each, joined in the cycle

  001 - 011 - 010 - 110 - 100 - 101 - 001

so the cube's hexagonal cross-section and the abstract planar hexagon are the
*same graph*. The two candidates one might have argued about are one candidate.
-/

namespace CubeToSU3.Hexagon

/-- Adjacency of the six-cycle: `i` and `j` are joined when they differ by one
step around the ring. -/
def H (i j : Fin 6) : Int :=
  if (i.val + 1) % 6 = j.val ∨ (j.val + 1) % 6 = i.val then 1 else 0

/-- Chirality: the hexagon is bipartite, so parity of the position works. -/
def Sh (i : Fin 6) : Int := if i.val % 2 = 0 then 1 else -1

/-! ## Part A: what survives

Every structural statement carries over unchanged. None of them was about the
cube.
-/

/-- SURVIVES. Bipartite, so a chirality operator exists here too. -/
theorem hex_S_anticommutes : ∀ i j : Fin 6, Sh i * H i j + H i j * Sh j = 0 := by
  decide

/-- SURVIVES, with different numbers. Three and three instead of four and four,
but still balanced, so the index still vanishes. -/
theorem hex_sectors_balanced :
    (List.finRange 6).countP (fun i => Sh i == 1) = 3 ∧
    (List.finRange 6).countP (fun i => Sh i == -1) = 3 := by
  decide

structure Vec6 where
  v0 : Int
  v1 : Int
  v2 : Int
  v3 : Int
  v4 : Int
  v5 : Int
deriving Repr, DecidableEq

def Vec6.zero : Vec6 := ⟨0, 0, 0, 0, 0, 0⟩

def hopH (v : Vec6) : Vec6 :=
  ⟨v.v1 + v.v5, v.v0 + v.v2, v.v1 + v.v3,
   v.v2 + v.v4, v.v3 + v.v5, v.v4 + v.v0⟩

/-- SURVIVES. The hexagon's determinant is `-4`, also nonzero, so its kernel is
trivial too and its index is likewise `0 - 0 = 0`. The chirality no-go is not a
fact about the cube; it is a fact about balanced bipartite graphs. -/
theorem hex_kernel_trivial (v : Vec6) (h : hopH v = Vec6.zero) :
    v = Vec6.zero := by
  cases v with
  | mk v0 v1 v2 v3 v4 v5 =>
    simp [hopH, Vec6.zero, Vec6.mk.injEq] at h ⊢
    omega

/-! ## Part B: what breaks

Only the spectral invariants change. These are exactly the two quantities the
cube was ever asked to supply.
-/

def mul6 (M N : Fin 6 → Fin 6 → Int) (i j : Fin 6) : Int :=
  M i 0 * N 0 j + M i 1 * N 1 j + M i 2 * N 2 j +
  M i 3 * N 3 j + M i 4 * N 4 j + M i 5 * N 5 j

def trace6 (M : Fin 6 → Fin 6 → Int) : Int :=
  M 0 0 + M 1 1 + M 2 2 + M 3 3 + M 4 4 + M 5 5

/-- BREAKS. The cube gives `24`; the hexagon gives `12`. -/
theorem hex_trace_sq : trace6 (mul6 H H) = 12 := by decide

/-- BREAKS. The cube gives `168`; the hexagon gives `36`. -/
theorem hex_trace_four : trace6 (mul6 (mul6 H H) (mul6 H H)) = 36 := by decide

/-- BREAKS. The weight-zero invariant `Tr A⁴ / (Tr A²)²` is `7/24` on the cube
and `1/4` on the hexagon. Stated without division. -/
theorem hex_weight_zero_invariant :
    4 * trace6 (mul6 (mul6 H H) (mul6 H H)) =
      1 * (trace6 (mul6 H H) * trace6 (mul6 H H)) := by
  decide

/-- BREAKS. The squared `f/v` candidate `ρ² · Tr A²` is `216` on the cube and
`4 · 12 = 48` on the hexagon. So `6√6` really was a fact about `Q₃` and about
nothing else. -/
theorem hex_candidate_value : 4 * trace6 (mul6 H H) = 48 := by decide

theorem hex_candidate_differs : (48 : Int) ≠ 216 := by decide

/-! ## Verdict

Survived the swap: bipartiteness, the chirality operator, sector balance,
trivial kernel, index zero. Also everything in `Core.lean` and
`Anomalies.lean`, neither of which mentions a graph at all -- and everything in
`Cube.lean` Part 1, since `D = P - P²` is a statement about `Z/3`, not about
eight vertices.

Broke under the swap: `Tr A²`, `Tr A⁴`, the weight-zero ratio, and the `f/v`
candidate.

So the cube's entire contribution to this project is a short list of spectral
invariants -- and both places those invariants were used have already been
closed: `6√6` by the weight criterion in `Rejected.lean`, and chirality by
`cube_index_zero`, which the hexagon reproduces anyway.

A component you can swap out without changing the conclusions is not a
load-bearing component.
-/

end CubeToSU3.Hexagon
