# Cube → traceless 3×3 algebra, Lean kernel

A compact, executable Lean project for the mathematical core of the cube
construction. The point is not to prove that the construction is right. It is
to make the boundary between "proved" and "assumed" machine-enforced, so that
no assumption can be used silently.

Four files:

- `CubeToSU3/Core.lean` — the 3×3 identities behind `D` and the traceless basis.
- `CubeToSU3/Cube.lean` — the cyclic group of order three, the cube graph, its
  chirality operator, and the index no-go.
- `CubeToSU3/Anomalies.lean` — the five anomaly sums, in exact integer
  arithmetic, plus an exhaustive search.
- `CubeToSU3/CrossProduct.lean` — `D v = v × 1`, and `D²` derived from BAC-CAB
  rather than computed.
- `CubeToSU3/Hexagon.lean` — the replacement test: swap `Q₃` for `C₆` and see
  what survives.
- `CubeToSU3/YouNian.lean` — the 遊年 tables as the Cayley table of `(Z₂)³`, the
  one place the group law is load-bearing.
- `CubeToSU3/ClosedWalks.lean` — the closed-walk route done axioms-first, and
  the no-go it reaches.
- `CubeToSU3/CompactSU3.lean` — the Gaussian-integer lattice inside `su(3)`:
  `{A ∈ M₃(ℤ[i]) : A† = -A, tr A = 0} ↔ ℤ⁸`, a rank-8 Lie ring closed under
  bracket, containing `D`. Gets the compact form's *lattice* without Mathlib;
  the real Lie algebra still needs scalar extension.
- `CubeToSU3/Flavour.lean` — the `1 + 2` structure meets the measured CKM
  matrix. Still a no-go, but one that points outward: it closes an escape route
  rather than killing a candidate, and thereby forces an observable.
- `CubeToSU3/Rejected.lean` — the other half of the ledger: candidates that
  were tried and ruled out, each paired with the theorem that rules it out.
- `CubeToSU3/PhysicsInputs.lean` — an explicit ledger of the eight external
  inputs. Nothing in the mathematical files imports it.

## What Lean proves

All arithmetic is exact integer arithmetic. No floating point, no Mathlib.

**Core**

1. `D² = -3 I + J`, and on the plane `x + y + z = 0` this reduces to `D² v = -3 v`.
2. Six directed paths `Eᵢⱼ` produce the two Cartan directions through
   commutators; several `A₂` root relations hold by exact finite calculation.
3. The eight coordinate matrices reconstruct every traceless integer 3×3 matrix.
   This is the integral lattice under the usual `sl(3)` over ℚ, ℝ, or ℂ.

**Cube**

4. `D = P - P²`, where `P` is the cyclic shift. So `D` lives in the group
   algebra of `Z/3`.
5. `D` is the *unique* antisymmetric element of that group algebra, up to an
   integer scale. It is canonical, not a choice.
6. The cube is bipartite: the Hamming-weight sign `S` anticommutes with the
   hopping operator `A`. This is the discrete `{γ⁵, D̸} = 0`.
7. The two chirality sectors have four vertices each.
8. `hop` is the action of `A`, and its kernel is trivial. Hence both chiral
   kernels vanish and the index is `0 - 0 = 0`. **This is a no-go, not a gap.**
9. Doubling the matrix quadruples `Tr A²`, so `ρ(A)·√(Tr A²)` has weight two.
   A ratio of two vacuum expectation values must have weight zero, so that
   candidate cannot be `f/v`. By contrast `Tr A⁴ / (Tr A²)² = 7/24` is
   weight-zero and is invariant under the same rescaling.

**Anomalies**

10. All five local gauge anomalies and the mixed gravitational anomaly of the
    candidate 331-type spectrum vanish, as integer identities (charges stored
    as `3X`).
11. Over the sixteen admissible pairs, the cubic `SU(3)_L` condition
    `3(2 nQ - 3) + (2 nL - 3) = 0` has exactly the two solutions `(2,0)` and
    `(1,3)`, which are conjugate. Checked exhaustively by the kernel.

**Rejected**

12. `f/v = ρ(A)·√(Tr A²) = 6√6` is homogeneous of degree two, so it cannot be a
    ratio of two vacuum expectation values, which must have degree zero.
    Squared, the candidate is the integer `216`.
13. The rewrite `(hexagon area)·√|Q₃| = 3√3·√8` is the *same number*: squared,
    `27 · 8 = 216`. Same rejection.
14. Chirality cannot come from edge phases: the index is fixed by the sector
    sizes, which are four and four.
15. `Γ_□` cannot be applied to leptons as well: that gives `n_L = 2` and a
    cubic anomaly of `+4`.

Entry 5 of the rejection ledger — free parameters as prediction targets — has
no theorem, deliberately. It is a methodological rejection, and dressing it as
an axiom would misrepresent a refusal as an assumption.

**遊年**

16. Both traditional systems, 大遊年變卦法 and 壺中鬼卦, are functions of the XOR
    of the two trigrams and nothing else. All 64 cells of each 8×8 table are
    checked against the rule.
17. The two systems differ exactly by reversing 上爻 and 下爻, an odd
    permutation. 陽宅 and 陰宅 are related by an orientation reversal.
18. The four 吉星 form an index-two subgroup of `(Z₂)³`; the 凶星 are its coset.
    Equivalently 吉 iff 上爻 and 中爻 change with the same parity, the 下爻 being
    irrelevant.
19. Listing trigrams in star order gives a Hamiltonian cycle on `Q₃` — a Gray
    code — stated through the cube's own adjacency operator. No *Eulerian*
    one-stroke path exists: all eight vertices have degree three.
20. `D` is not a homomorphism of `(Z₂)³`. So the structure 遊年 runs on is
    destroyed by `D`, and the structure `D` runs on is invisible to 遊年. Two
    complete, disjoint structures on the same eight points.

**Closed walks**

21. Written axioms-first, as Appendix E.7 requires. Observables may use only
    `Tr Aᵏ`; isospectral graphs are identified; predictions must be weight zero.
22. The spectrum of `Qₙ` is binomial — eigenvalue `n - 2j` with multiplicity
    `C(n,j)` — so it carries exactly **one** parameter. Every invariant the
    axioms permit is therefore a function of `n` alone.
23. Concretely `m₂ = 3`, `m₄ = 21`, `m₆ = 183`, matching `n`, `3n²-2n`,
    `15n³-30n²+16n` at `n = 3`. The leading weight-zero invariant is the
    kurtosis `κ = m₄/m₂² = 7/3 = 3 - 2/n`, and inverting it returns `n = 3`,
    uniquely.
24. So the route emits one number and that number is the dimension, which was
    an input by choosing the cube. This closes a family, not a candidate: any
    formula built from `Tr Aᵏ` that appears to give an interesting constant is
    a function of `3` in disguise.
25. Scope: the isospectrality axiom is what does the work. The group law
    (`YouNian`), Hamiltonian paths, and the embedding (`CrossProduct`) are
    invisible to `Tr Aᵏ` and are untouched by this no-go.

**Flavour**

26. If the `1 + 2` decomposition is used as a family structure with different
    `SU(3)_L` representations for the two blocks, the `Z'` coupling matrix takes
    the form `G = g₂ I + Δg · P₁`, which is family non-universal.
27. Alignment of *both* quark sectors with the special direction would force the
    CKM matrix to be block diagonal with respect to the same `1 ⊕ 2` split.
    (Hand proof in the module docstring; the ordered-field step needs Mathlib.)
28. The measured CKM is not block diagonal under *any* labelling of which
    generation decouples. All nine block defects exceed `10^7` in units where
    unitarity means `10^10`; the best case, third generation to third column, is
    `3.5 × 10^7`, a defect of `0.0594`. The next closest labellings are worse by
    a factor of about 29, the rest by about 570. Machine-checked.
    Deliberately not quoted in sigma: the defect is a quadrature sum over four
    matrix elements, so dividing by one element's uncertainty is not a
    statistical statement.
    The robust form quantifies over a *variable* matrix: `blockDefect_mono` shows
    the defect is monotone in each magnitude, so any matrix dominating the lower
    bounds inherits the bound. `every_admissible_matrix_is_nonblock` then covers
    the whole admissible region, not one table of numbers.
29. **Scope, stated precisely.** What Lean checks in `Flavour.lean` is a
    statement about nine hard-coded integers, and nothing else — no `P₁`, no
    mass matrices, no alignment, no cube. Theorems A1 (matrix lemma) and A2
    (spectral bridge) that connect alignment to CKM block structure are hand
    proofs in the module docstring and need Mathlib. So the honest label is
    *machine-checked data + hand-proved algebra + a declared dictionary*, not a
    machine-checked chain. With that caveat: at least one quark sector carries
    tree-level `Z'` FCNC. This does
    *not* fix a `Z'` mass: with `ξ_d = V† ξ_u` the violation can be moved
    between sectors, and published bounds span orders of magnitude. What is
    closed is the option "no tree-level flavour violation anywhere".

## Why there are two ledgers

A ledger that only lists surviving assumptions makes a project look cleaner
than it is. Dead ends leave no trace, so they get re-proposed later by someone
who has forgotten them, including the person who proposed them the first time.
That is not hypothetical: `6√6` survived several rounds of review precisely
because the checked core did not contain any of the quantities it was built
from. The rejection ledger exists so that the kernel now refuses to let those
candidates back in silently.

## What is deliberately not claimed

- The core does not identify this lattice with physical flavour or colour.
- `D / √3`, the complex anti-Hermitian real form `su(3)`, and the Hermitian
  structure need scalar extension to ℝ or ℂ. Phase 2, with Mathlib.
- The bipartite index theorem is stated in general in the comments but proved
  here only for the cube, since the general form needs rank-nullity over a
  field. The concrete instance is what the no-go actually uses.
- **The anomaly theorems are conditional on chirality.** A vectorlike
  assignment cancels every anomaly automatically, so item 10 constrains nothing
  until axiom `chirality` is assumed. This is the honest reading of the
  `1 + 2` family structure: it is forced *given* chirality, not evidence for it.
- π-holonomy, the flavour dictionary, the Born rule, the `p³` phase-space
  factor, chirality, the colour factor, and the weak-direction choice are not
  theorems of finite linear algebra. They are the eight named axioms.

## Build

~~~bash
lake build
lake env lean CubeToSU3/Check.lean
~~~

`Check.lean` prints the axioms each representative declaration depends on. The
mathematical theorems stay independent of the ledger; `physical_ledger`
explicitly depends on its eight axioms. If a later "result" quietly leans on a
postulate, it appears in that report.
