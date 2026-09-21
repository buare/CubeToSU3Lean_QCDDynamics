import CubeToSU3.Cube

/-!
# The closed-walk route, done in the prescribed order

Appendix E.7 laid down an order and a warning: write the axioms, see what
weight-zero invariants they produce, and only then look for a physical
quantity. Doing it the other way round -- starting from a target number and
hunting for a formula -- is numerology.

This module follows the prescribed order. The result is negative and complete.

## The axioms

* **W1** state space: a finite graph `G = (V, E)` with hopping operator `A`.
* **W2** closed walks: observables are built only from `Tr Aᵏ`, the number of
  closed walks of length `k`.
* **W3** isospectrality: isospectral graphs give identical physics. Equivalently
  only the spectral measure is available.
* **W4** weight zero: a dimensionless prediction must be invariant under
  `A → λA`.

None of the four mentions a cube. That is the point: the axioms are written
first.

## What they output, for the hypercube

The spectrum of `Qₙ` is

    eigenvalue n - 2j   with multiplicity   C(n, j),   j = 0 … n

which is a binomial distribution and **contains exactly one parameter, `n`**.
By W3 nothing outside the spectrum is available, so:

> Every invariant permitted by W1-W4 is a function of `n` alone.

There is no second degree of freedom to discover. The route can emit at most
one independent number, and that number is the dimension, which was an input.

Concretely, the normalised moments `mₖ = Tr Aᵏ / |V|` are polynomials in `n`:

    m₂ = n,   m₄ = 3n² - 2n,   m₆ = 15n³ - 30n² + 16n

and the leading weight-zero invariant is the kurtosis

    κ = m₄ / m₂² = 3 - 2/n

which is invertible: `n = 2/(3 - κ)`. One number in, the same number out.
Verified below for `Q₃`, where `κ = 7/3` and the inversion returns `3`.

## Verdict

The closed-walk route is closed, and not for want of effort. It cannot produce
a new number, because the object it is allowed to look at has no new number in
it. Any formula built this way that appears to yield an interesting constant is
a function of `3` in disguise.

This is stronger than the weight criterion of `Rejected.lean`, which rules out
particular candidates. This rules out the whole family.

## What is *not* ruled out

W3 is doing heavy lifting. Structure beyond the spectrum survives: the group
law used by `YouNian.lean`, Hamiltonian paths, and the embedding used by
`CrossProduct.lean` are all invisible to `Tr Aᵏ` and are untouched by this
no-go. The closed-walk route specifically is dead; combinatorics in general is
not.
-/

namespace CubeToSU3.ClosedWalks

/-- Closed walks of length two: twice the number of edges. -/
def T2 : Int := trace8 (mul8 A A)

/-- Closed walks of length four. -/
def T4 : Int := trace8 (mul8 (mul8 A A) (mul8 A A))

/-- Closed walks of length six. -/
def T6 : Int := trace8 (mul8 (mul8 A A) (mul8 (mul8 A A) (mul8 A A)))

theorem T2_value : T2 = 24 := by decide
theorem T4_value : T4 = 168 := by decide
theorem T6_value : T6 = 1464 := by decide

/-- Odd closed walks vanish: the cube is bipartite, so there are no odd cycles.
W2 therefore sees only even moments. -/
theorem odd_walks_vanish : trace8 (mul8 A (mul8 A A)) = 0 := by decide

/-! ## The moments match the binomial formula

With `|V| = 8`: `m₂ = T2/8 = 3`, `m₄ = T4/8 = 21`, `m₆ = T6/8 = 183`. Compared
with `m₂ = n`, `m₄ = 3n² - 2n`, `m₆ = 15n³ - 30n² + 16n` at `n = 3`, which give
`3`, `21`, `183`. Stated without division.
-/

theorem m2_matches : T2 = 8 * 3 := by decide

theorem m4_matches : T4 = 8 * (3 * 3 * 3 - 2 * 3) := by decide

theorem m6_matches : T6 = 8 * (15 * 3 * 3 * 3 - 30 * 3 * 3 + 16 * 3) := by decide

/-! ## The kurtosis, and the fact that it returns the input

`κ = m₄/m₂² = 21/9 = 7/3`. Cleared of denominators, `3 · 8 · T4 = 7 · T2²`.
-/

/-- The leading weight-zero invariant of the cube is `7/3`. -/
theorem kurtosis_is_seven_thirds : 3 * (8 * T4) = 7 * (T2 * T2) := by decide

/-- It is genuinely weight zero: doubling the hopping operator leaves the same
relation standing. -/
theorem kurtosis_scale_invariant :
    3 * (8 * trace8 (mul8 (mul8 (smul8 2 A) (smul8 2 A))
                          (mul8 (smul8 2 A) (smul8 2 A)))) =
      7 * (trace8 (mul8 (smul8 2 A) (smul8 2 A)) *
           trace8 (mul8 (smul8 2 A) (smul8 2 A))) := by
  decide

/-- **The whole output of the route.** Inverting `κ = 3 - 2/n` gives
`n · (3 m₂² - m₄) = 2 m₂²`; cleared of denominators with `|V| = 8`, this reads
`n · (3 T2² - 8 T4) = 2 T2²`, and it holds precisely at `n = 3`.

The single number the closed-walk axioms emit for the cube is the dimension,
which was put in by choosing the cube. Nothing else is available. -/
theorem dimension_recovered : 3 * (3 * (T2 * T2) - 8 * T4) = 2 * (T2 * T2) := by
  decide

/-- And it is the *only* solution: no other integer dimension satisfies the
relation, so the inversion is unambiguous. -/
theorem dimension_unique : ∀ n : Fin 10,
    (n.val : Int) * (3 * (T2 * T2) - 8 * T4) = 2 * (T2 * T2) ↔ n.val = 3 := by
  decide

/-! ## The comparison that makes the point

`Hexagon.lean` swapped `Q₃` for `C₆`. Under the closed-walk axioms the hexagon
gives `m₂ = 2`, `m₄ = 6`, hence `κ = 3/2`. Different number, same situation:
one parameter in, one parameter out. Neither graph has a second invariant to
give.
-/

theorem hexagon_kurtosis : 2 * (6 * 36) = 3 * (12 * 12) := by decide

end CubeToSU3.ClosedWalks
