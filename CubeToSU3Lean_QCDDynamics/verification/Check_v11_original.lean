import CubeToSU3

/-!
Run with:

  lake env lean CubeToSU3/Check.lean

Every report below except the last must be free of any declaration from
CubeToSU3.PhysicsInputs. The last one deliberately lists all eight inputs.

The point of this file is that the separation is machine-enforced. If someone
later proves a "result" by quietly leaning on a physical postulate, it shows up
here as a new name in the report, not as a footnote nobody reads.
-/

-- Core: the 3x3 identities
#print axioms CubeToSU3.D_squared
#print axioms CubeToSU3.D_squared_on_zero_sum
#print axioms CubeToSU3.integral_kernel_image_structure
#print axioms CubeToSU3.traceless_coordinate_formula

-- CrossProduct: D as a cross product, D-squared derived not computed
#print axioms CubeToSU3.D_is_cross
#print axioms CubeToSU3.cross_cross
#print axioms CubeToSU3.D_squared_from_cross
#print axioms CubeToSU3.refl_reverses_cross

-- Cube: group algebra, chirality, and the index no-go
#print axioms CubeToSU3.D_eq_P_sub_P_sq
#print axioms CubeToSU3.antisymmetric_group_algebra_unique
#print axioms CubeToSU3.S_anticommutes_A
#print axioms CubeToSU3.sectors_balanced
#print axioms CubeToSU3.hop_is_A
#print axioms CubeToSU3.cube_index_zero
#print axioms CubeToSU3.trace_sq_has_weight_two

-- Anomalies: finite integer arithmetic, independent of the cube
#print axioms CubeToSU3.Anomalies.all_anomalies_vanish
#print axioms CubeToSU3.Anomalies.cubic_solutions_exhaustive

-- Rejected: candidates that were tried and ruled out
#print axioms CubeToSU3.Rejected.candidate_has_weight_two
#print axioms CubeToSU3.Rejected.traceSq_not_scale_invariant
#print axioms CubeToSU3.Rejected.chirality_from_phases_rejected
#print axioms CubeToSU3.Rejected.gamma_rule_not_universal

-- ClosedWalks: the route done axioms-first, and its negative result
#print axioms CubeToSU3.ClosedWalks.kurtosis_is_seven_thirds
#print axioms CubeToSU3.ClosedWalks.dimension_recovered
#print axioms CubeToSU3.ClosedWalks.dimension_unique

-- YouNian: the one module that uses the group law on (Z2)^3
#print axioms CubeToSU3.YouNian.dy_is_xor
#print axioms CubeToSU3.YouNian.hz_is_xor
#print axioms CubeToSU3.YouNian.auspicious_subgroup
#print axioms CubeToSU3.YouNian.auspicious_iff_character
#print axioms CubeToSU3.YouNian.dyCycle_is_hamiltonian
#print axioms CubeToSU3.YouNian.D_not_group_hom

-- CompactSU3: the Gaussian-integer lattice in su(3)
#print axioms CubeToSU3.compactMatrix_mem_su3
#print axioms CubeToSU3.compactMatrix_injective
#print axioms CubeToSU3.compactMatrix_surjective
#print axioms CubeToSU3.coeff_lattice_bijection
#print axioms CubeToSU3.no_phi_is_lie_hom
#print axioms CubeToSU3.Dg_squared
#print axioms CubeToSU3.Dg_eq_image_of_core_D
#print axioms CubeToSU3.bracket_Dg_coefficients
#print axioms CubeToSU3.bracket_Dg_mem

-- The two ledgers
#print axioms CubeToSU3.Rejected.ledger_size
#print axioms CubeToSU3.PhysicsInputs.physical_ledger

#eval CubeToSU3.Rejected.rejectionLedger.map (fun e => e.candidate)

-- Replacement test: which theorems survive swapping Q3 for the hexagon
#print axioms CubeToSU3.Hexagon.hex_S_anticommutes
#print axioms CubeToSU3.Hexagon.hex_sectors_balanced
#print axioms CubeToSU3.Hexagon.hex_kernel_trivial
#print axioms CubeToSU3.Hexagon.hex_candidate_differs

-- Flavour: the 1+2 structure meets measured CKM
#print axioms CubeToSU3.Flavour.ckm_rows_normalised
#print axioms CubeToSU3.Flavour.ckm_not_block_diagonal
#print axioms CubeToSU3.Flavour.third_generation_is_the_closest
#print axioms CubeToSU3.Flavour.ckm_dataset_decisively_nonblock
#print axioms CubeToSU3.Flavour.ckm_lower_bound_table_nonblock
#print axioms CubeToSU3.Flavour.blockDefect_mono
#print axioms CubeToSU3.Flavour.every_admissible_matrix_is_nonblock
