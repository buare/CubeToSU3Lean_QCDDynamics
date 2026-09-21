# Verification status

## QCD-dynamics extension — 2026-09-11

Two new source modules are included by the root import and sampled by the
central axiom audit:

- `CubeToSU3/QCDDynamics.lean`
- `CubeToSU3/DimensionlessComparison.lean`

Static checks performed in the packaging environment:

- both files are UTF-8 and contain no hidden control characters;
- no new `axiom`, executable `sorry`, or executable `admit` was added;
- `CubeToSU3.lean` imports both modules;
- `CubeToSU3/Check.lean` prints the axioms of eleven representative new
  declarations;
- the companion HTML has balanced MathJax delimiters and parses as HTML.
- the root module documentation occurs after all imports, as required by Lean
  4.16 (`/-! ... -/` is a command, not an inert pre-import comment).

The packaging environment does not contain a Lean executable. Therefore the
new extension is **not labelled freshly compiled here**. Run `lake build` and
`lake env lean CubeToSU3/Check.lean` in the pinned Lean/Mathlib 4.16
environment, and inspect their complete unfiltered output, before promoting
this extension to build-verified status.

## Assembly audit — 2026-09-11

This directory is a complete Lake project assembled from the supplied module
archive and project metadata.

Static checks performed during assembly:

- 21 source modules under `CubeToSU3/` plus the root `CubeToSU3.lean`;
- every source module is imported by the root;
- `CubeToSU3/Check.lean` covers every conceptual layer;
- no executable `sorry` or `admit` occurs in the source;
- the only eight project-defined axioms are the deliberately isolated entries
  in `PhysicsInputs.lean`;
- `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `.gitignore`, README
  and historical verification evidence are present.

The supplied `verification/build-weyl-real-v8.log` ends with
`Build completed successfully` and confirms the build through `WeylReal`.
It also records ordinary linter warnings and the expected logical dependencies
`propext`, `Classical.choice`, `Quot.sound`, and for `native_decide` results,
`Lean.ofReduceBool`.

## Fresh certification command

Run from the project root:

```bash
lake update
lake exe cache get
lake build
lake env lean CubeToSU3/Check.lean
```

The project is certified only when both commands exit successfully and the
complete output contains no error. The central audit must be read as follows:

- mathematical declarations may depend on Lean/Mathlib logical axioms;
- no mathematical declaration may depend on a name from `PhysicsInputs`;
- `physical_ledger` must list exactly the eight declared physics inputs;
- `expSU3_surjective_of_unitarySpectralTheorem3` is conditional even though
  its premise is not a project axiom;
- `Lean.ofReduceBool` marks finite results discharged through `native_decide`,
  not a physical assumption.

## Scope caveat

This assembly step does not manufacture new mathematical proofs. It makes the
module graph reproducible and the audit comprehensive. In particular it does
not prove:

- eight cube vertices are eight gluons;
- the constructed `SU(3)` is necessarily colour;
- the rational `1+2` direct sum;
- the alignment-to-block-CKM theorem;
- unconditional exponential surjectivity;
- a smooth Lie-group manifold;
- a variationally derived, full classical or quantum QCD theory.

Those remain named gaps rather than silently assumed results.
