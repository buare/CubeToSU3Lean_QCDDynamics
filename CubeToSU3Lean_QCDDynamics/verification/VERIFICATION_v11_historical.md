# Local verification record

Built and audited with Lean 4.16.0 (no Mathlib), most recently on 2026-09-06 (v11: + CompactSU3, the Gaussian-integer lattice in su(3); 8 axioms, 6 rejections; 52 audit lines).

~~~text
'CubeToSU3.D_squared' does not depend on any axioms
'CubeToSU3.D_squared_on_zero_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'CubeToSU3.integral_kernel_image_structure' depends on axioms: [propext, Classical.choice, Quot.sound]
'CubeToSU3.traceless_coordinate_formula' depends on axioms: [propext, Quot.sound]
'CubeToSU3.D_is_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'CubeToSU3.cross_cross' depends on axioms: [propext, Quot.sound]
'CubeToSU3.D_squared_from_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'CubeToSU3.refl_reverses_cross' depends on axioms: [propext, Quot.sound]
'CubeToSU3.D_eq_P_sub_P_sq' does not depend on any axioms
'CubeToSU3.antisymmetric_group_algebra_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'CubeToSU3.S_anticommutes_A' depends on axioms: [propext]
'CubeToSU3.sectors_balanced' does not depend on any axioms
'CubeToSU3.hop_is_A' depends on axioms: [propext, Quot.sound]
'CubeToSU3.cube_index_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'CubeToSU3.trace_sq_has_weight_two' depends on axioms: [propext]
'CubeToSU3.Anomalies.all_anomalies_vanish' does not depend on any axioms
'CubeToSU3.Anomalies.cubic_solutions_exhaustive' does not depend on any axioms
'CubeToSU3.Rejected.candidate_has_weight_two' depends on axioms: [propext]
'CubeToSU3.Rejected.traceSq_not_scale_invariant' depends on axioms: [propext]
'CubeToSU3.Rejected.chirality_from_phases_rejected' depends on axioms: [propext, Classical.choice, Quot.sound]
'CubeToSU3.Rejected.gamma_rule_not_universal' does not depend on any axioms
'CubeToSU3.ClosedWalks.kurtosis_is_seven_thirds' depends on axioms: [propext]
'CubeToSU3.ClosedWalks.dimension_recovered' depends on axioms: [propext]
'CubeToSU3.ClosedWalks.dimension_unique' depends on axioms: [propext]
'CubeToSU3.YouNian.dy_is_xor' depends on axioms: [propext]
'CubeToSU3.YouNian.hz_is_xor' depends on axioms: [propext]
'CubeToSU3.YouNian.auspicious_subgroup' depends on axioms: [propext]
'CubeToSU3.YouNian.auspicious_iff_character' does not depend on any axioms
'CubeToSU3.YouNian.dyCycle_is_hamiltonian' depends on axioms: [propext, Quot.sound]
'CubeToSU3.YouNian.D_not_group_hom' does not depend on any axioms
'CubeToSU3.compactMatrix_mem_su3' depends on axioms: [propext, Quot.sound]
'CubeToSU3.compactMatrix_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'CubeToSU3.compactMatrix_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'CubeToSU3.coeff_lattice_bijection' depends on axioms: [propext, Classical.choice, Quot.sound]
'CubeToSU3.no_phi_is_lie_hom' does not depend on any axioms
'CubeToSU3.Dg_squared' does not depend on any axioms
'CubeToSU3.Dg_eq_image_of_core_D' does not depend on any axioms
'CubeToSU3.bracket_Dg_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound]
'CubeToSU3.bracket_Dg_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'CubeToSU3.Rejected.ledger_size' does not depend on any axioms
'CubeToSU3.PhysicsInputs.physical_ledger' depends on axioms: [CubeToSU3.PhysicsInputs.born_rule,
 CubeToSU3.PhysicsInputs.chirality,
 CubeToSU3.PhysicsInputs.color_factor,
 CubeToSU3.PhysicsInputs.discretization,
 CubeToSU3.PhysicsInputs.flavor_dictionary,
 CubeToSU3.PhysicsInputs.p_wave_phase_space,
 CubeToSU3.PhysicsInputs.pi_holonomy,
 CubeToSU3.PhysicsInputs.weak_direction]
["f/v = ρ(A)·√(Tr A²) = 6√6", "f/v = (hexagon area)·√|Q₃| = 3√3·√8", "chirality from edge phases (axiom A4)",
  "Γ_□ applied universally, including leptons", "f/v, v, m_H, Yukawa ratios as prediction targets",
  "the closed-walk route in general (any function of Tr A^k)"]
'CubeToSU3.Hexagon.hex_S_anticommutes' does not depend on any axioms
'CubeToSU3.Hexagon.hex_sectors_balanced' does not depend on any axioms
'CubeToSU3.Hexagon.hex_kernel_trivial' depends on axioms: [propext, Classical.choice, Quot.sound]
'CubeToSU3.Hexagon.hex_candidate_differs' does not depend on any axioms
'CubeToSU3.Flavour.ckm_rows_normalised' depends on axioms: [propext, Quot.sound]
'CubeToSU3.Flavour.ckm_not_block_diagonal' depends on axioms: [propext, Quot.sound]
'CubeToSU3.Flavour.third_generation_is_the_closest' depends on axioms: [propext, Quot.sound]
'CubeToSU3.Flavour.ckm_dataset_decisively_nonblock' depends on axioms: [propext, Quot.sound]
'CubeToSU3.Flavour.ckm_lower_bound_table_nonblock' depends on axioms: [propext, Quot.sound]
'CubeToSU3.Flavour.blockDefect_mono' depends on axioms: [propext, Quot.sound]
'CubeToSU3.Flavour.every_admissible_matrix_is_nonblock' depends on axioms: [propext, Quot.sound]
~~~

Reading the report:

- `propext`, `Classical.choice`, `Quot.sound` are part of Lean's ordinary
  logical environment. They are not claims about the cube or about physics.
- No mathematical declaration lists any name from `CubeToSU3.PhysicsInputs`.
- `physical_ledger` lists exactly eight, which is the whole point of the file.

The count went from four axioms to eight on 2026-09-06. The four additions
(`chirality`, `color_factor`, `weak_direction`, `discretization`) were not new assumptions
smuggled in; they were assumptions already being used informally. `chirality`
in particular was promoted to an axiom *because* `CubeToSU3.cube_index_zero`
proves it cannot be derived from the finite core.
