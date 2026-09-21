# CubeToSU3: Symmetries of the Unit Cube {0,1}³ and SU(3)

A Lean 4 formalization of how the eight vertices of the unit cube {0,1}³,
read as fermionic occupation states, give a concrete and fully verified
construction of the Lie algebra su(3), the group SU(3), its representations,
and a lattice gauge structure.

> **Positioning.** All mathematical and physical results in this repository are
> known. The contribution is (1) the organization — a single concrete object,
> the unit cube, from which the SU(3) structure is read off — and (2) machine
> verification of the core chain in Lean 4 with Mathlib.

中文摘要：本專案以 Lean 4 形式化驗證「單位立方體 {0,1}³ 的八個頂點座標」如何具體生成
李代數 su(3)、李群 SU(3)、其表示論與格點規範結構。所有數學與物理結果皆為已知，
貢獻在於組織方式與形式化驗證。

---

## The bridge: vertices are fermion states

Read each coordinate of a vertex as the occupation number of one fermionic mode
(r, g, b). The eight vertices then form a basis of the exterior algebra Λ*ℂ³,
and the coordinate sum is the particle number N. Since U(3) preserves N, the
layers are SU(3) representations:

| Coordinate sum | Vertices | Count | Representation |
|---|---|---|---|
| 0 | (0,0,0) | 1 | **1** |
| 1 | (1,0,0), (0,1,0), (0,0,1) | 3 | **3** |
| 2 | (0,1,1), (1,0,1), (1,1,0) | 3 | **3̄** |
| 3 | (1,1,1) | 1 | **1** (ε_rgb) |

The complement map x ↦ (1,1,1) − x is the Hodge dual Λᵏ → Λ³⁻ᵏ, i.e. charge
conjugation **3** ↔ **3̄**.

## Verified main line

```
cyclic difference D = P − P²  →  su(3)  →  SU(3)  →  representations / Clebsch–Gordan  →  gauge fields / Wilson action
```

Selected results (see the modules for exact statements):

| Result | Statement |
|---|---|
| Root chain | `[E_ij, E_jk] = E_ik` for distinct i, j, k |
| Real form | the six off-diagonal paths and two traceless diagonals close to ℝ⁸ ≅ su(3) |
| Exponential map | `exp : su(3) → SU(3)` is surjective |
| Adjoint action | `Ad g [X, Y] = [Ad g X, Ad g Y]` |
| Lattice holonomy | plaquette holonomy transforms by conjugation; its trace is gauge invariant |
| Flat control | a pure-gauge connection has trivial holonomy on every face |
| Non-flat example | with P (120° rotation about (1,1,1)) and S = diag(1,−1,−1), the holonomy has trace −1 |
| Symmetry breaking | `broken_mode_split`: a degenerate eigenvalue 3 splits linearly to 3 and 3 + 2e |
| Scale weight | `candidate_has_weight_two`: rejects a proposed dimensionful ratio (recorded in `Rejected.lean`) |

**Build status:** <!-- TODO: fill in --> XX modules, XXXX build jobs,
zero `sorry`, zero `native_decide`.

## Status of extensions

The following were computed in the project but are **not all part of the green
main line yet**:

| Item | Content | Status |
|---|---|---|
| Naive dynamics | dv/dt = Dv (ω = √3); one-loop running; group factors in β₀ = 11 − 2n_f/3 | computed, to be formalized |
| Algebra embedding | su(2)_L ⊕ u(1) ⊂ su(3)_L; Q = T₃ + βT₈ + X | computed, to be formalized |
| Chiral content | 6n_Q + 2n_L = 12; 15 Weyl fields per generation, all six anomalies vanish | computed, to be formalized |
| Symmetry breaking | SU(2) × U(1) → U(1)_EM from a triplet VEV | not yet done |
| 331 mass scales | f ≈ 3.626 TeV; M ≈ 1.985 / 1.146 TeV | under review |
| Yukawa / CKM | continuous parameters | external input |

## Scope and limitations

- The cube supplies the discrete skeleton (weights, roots, Weyl group).
  Real parameters and the exponential map are introduced separately.
- Higher representations (e.g. **27**) require tensor products of cubes.
- The form of the running equations and the group factors come from the
  framework; loop structure comes from quantum field theory. Confinement is
  outside the framework.
- A finite combinatorial structure can only produce dimensionless ratios;
  every dimensionful number requires at least one external scale.

## Building

Requirements: <!-- TODO --> Lean `v4.X.X` (see `lean-toolchain`), Mathlib at the
commit pinned in `lake-manifest.json`.

```bash
git clone <!-- TODO: repository URL -->
cd CubeToSU3
lake exe cache get   # download prebuilt Mathlib
lake build
```

## Checking axioms

Every main theorem depends only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). To check:

```lean
#print axioms <!-- TODO: theorem name -->
```

<!-- TODO: paste the actual #print axioms output here -->

## Repository layout

<!-- TODO: adjust to the actual file list -->

| Module | Content |
|---|---|
| `Cube.lean` | the unit cube, layers, complement map |
| `Core.lean` | cyclic permutation P, difference D |
| `CrossProduct.lean` | D v = v × n, D² = −3I + J |
| `CompactSU3Real.lean` | real form su(3), bracket |
| `WeylReal.lean` | Weyl group action preserving the bracket |
| `SU3Group.lean`, `SU3Global.lean` | the group SU(3), surjectivity of exp |
| `QCDKinematics.lean` | su3Bracket, structure constants |
| `GaugeTheory.lean` | adjoint action, gauge covariance, lattice holonomy |
| `Anomalies.lean` | anomaly conditions |
| `PhysicsInputs.lean` | explicitly labelled external inputs |
| `Rejected.lean` | rejected candidates and why |
| `Check.lean` | top-level checks |

## Citation

If you use this work, please cite it via the "Cite this repository" button
(generated from `CITATION.cff`) or the Zenodo DOI:
<!-- TODO: add DOI badge after the first Zenodo release -->

## License

Apache License 2.0. See `LICENSE`.
