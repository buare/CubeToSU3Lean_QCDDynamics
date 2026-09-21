import CubeToSU3

/-!
# Central axiom audit

Run with:

    lake env lean CubeToSU3/Check.lean

This file samples every shipped layer. All reports before the final
`physical_ledger` must remain free of declarations from
`CubeToSU3.PhysicsInputs`.

Important reading rule: the surjectivity theorem below has
`UnitarySpectralTheorem3` as an explicit premise. A custom-axiom-free
`#print axioms` report does not remove that premise.
-/

-- Finite core and the precise integral kernel/image statement
#print axioms CubeToSU3.D_squared
#print axioms CubeToSU3.D_squared_on_zero_sum
#print axioms CubeToSU3.integral_kernel_image_structure
#print axioms CubeToSU3.traceless_coordinate_formula

-- Cross-product reformulation
#print axioms CubeToSU3.D_is_cross
#print axioms CubeToSU3.cross_cross
#print axioms CubeToSU3.D_squared_from_cross
#print axioms CubeToSU3.refl_reverses_cross

-- Cube and Z/3 group algebra
#print axioms CubeToSU3.D_eq_P_sub_P_sq
#print axioms CubeToSU3.antisymmetric_group_algebra_unique
#print axioms CubeToSU3.S_anticommutes_A
#print axioms CubeToSU3.sectors_balanced
#print axioms CubeToSU3.hop_is_A
#print axioms CubeToSU3.cube_index_zero
#print axioms CubeToSU3.trace_sq_has_weight_two

-- Candidate 331 anomaly arithmetic (independent of the cube core)
#print axioms CubeToSU3.Anomalies.all_anomalies_vanish
#print axioms CubeToSU3.Anomalies.cubic_solutions_exhaustive
#print axioms CubeToSU3.Anomalies.two_plus_one_forced

-- Rejected routes
#print axioms CubeToSU3.Rejected.candidate_has_weight_two
#print axioms CubeToSU3.Rejected.traceSq_not_scale_invariant
#print axioms CubeToSU3.Rejected.chirality_from_phases_rejected
#print axioms CubeToSU3.Rejected.gamma_rule_not_universal
#print axioms CubeToSU3.Rejected.ledger_size

-- Closed-walk no-go
#print axioms CubeToSU3.ClosedWalks.kurtosis_is_seven_thirds
#print axioms CubeToSU3.ClosedWalks.dimension_recovered
#print axioms CubeToSU3.ClosedWalks.dimension_unique

-- YouNian and the (Z/2)^3 group law
#print axioms CubeToSU3.YouNian.dy_is_xor
#print axioms CubeToSU3.YouNian.hz_is_xor
#print axioms CubeToSU3.YouNian.auspicious_subgroup
#print axioms CubeToSU3.YouNian.auspicious_iff_character
#print axioms CubeToSU3.YouNian.dyCycle_is_hamiltonian
#print axioms CubeToSU3.YouNian.D_not_group_hom

-- Replacement test
#print axioms CubeToSU3.Hexagon.hex_S_anticommutes
#print axioms CubeToSU3.Hexagon.hex_sectors_balanced
#print axioms CubeToSU3.Hexagon.hex_kernel_trivial
#print axioms CubeToSU3.Hexagon.hex_candidate_differs

-- Flavour data theorem only; the alignment bridge is not formalised
#print axioms CubeToSU3.Flavour.ckm_rows_normalised
#print axioms CubeToSU3.Flavour.ckm_not_block_diagonal
#print axioms CubeToSU3.Flavour.third_generation_is_the_closest
#print axioms CubeToSU3.Flavour.ckm_lower_bound_table_nonblock
#print axioms CubeToSU3.Flavour.blockDefect_mono
#print axioms CubeToSU3.Flavour.every_admissible_matrix_is_nonblock
#print axioms CubeToSU3.Flavour.ckm_dataset_decisively_nonblock

-- Gaussian-integer lattice in su(3), and the exact bridge from Core.D
#print axioms CubeToSU3.compactMatrix_mem_su3
#print axioms CubeToSU3.compactMatrix_injective
#print axioms CubeToSU3.compactMatrix_surjective
#print axioms CubeToSU3.coeff_lattice_bijection
#print axioms CubeToSU3.no_phi_is_lie_hom
#print axioms CubeToSU3.Dg_squared
#print axioms CubeToSU3.Dg_eq_image_of_core_D
#print axioms CubeToSU3.bracket_Dg_coefficients
#print axioms CubeToSU3.bracket_Dg_mem

-- Scalar extension to the full real Lie algebra su(3)
#print axioms CubeToSU3.Continuous.compactMatrixR_mem
#print axioms CubeToSU3.Continuous.compactMatrixR_coordinatesR
#print axioms CubeToSU3.Continuous.coeffLinearEquivSu3
#print axioms CubeToSU3.Continuous.bracketR_mem
#print axioms CubeToSU3.Continuous.complexify_mem
#print axioms CubeToSU3.Continuous.bracket_Dreal_coefficients
#print axioms CubeToSU3.Continuous.integer_adD_scalar_extension
#print axioms CubeToSU3.Continuous.naiveODE_matrix_rhs

-- Finite signed-permutation/Weyl candidate and its real action
#print axioms CubeToSU3.Perm3.equivS3
#print axioms CubeToSU3.cubeSym_card
#print axioms CubeToSU3.cubeAct_bracket
#print axioms CubeToSU3.cube_kernel_iff
#print axioms CubeToSU3.signature_complete
#print axioms CubeToSU3.actionImage_card
#print axioms CubeToSU3.Continuous.cubeActR_mem
#print axioms CubeToSU3.Continuous.cubeActR_bracket
#print axioms CubeToSU3.Continuous.cubeActSu3LinearEquiv
#print axioms CubeToSU3.Continuous.complexify_cubeAct

-- Continuous su(3) and the matrix group SU(3)
#print axioms CubeToSU3.Continuous.finrank_su3R
#print axioms CubeToSU3.Continuous.det_exp_eq_one_of_isSu3R
#print axioms CubeToSU3.Continuous.exp_mem_SU3
#print axioms CubeToSU3.Continuous.continuous_expSU3

-- Global topological-group and one-parameter-subgroup layer
#print axioms CubeToSU3.Continuous.coe_su3_inv
#print axioms CubeToSU3.Continuous.su3_isHausdorff
#print axioms CubeToSU3.Continuous.smooth_exp_ambient_real
#print axioms CubeToSU3.Continuous.expLine_add
#print axioms CubeToSU3.Continuous.continuous_expLine

-- Conditional global exponential-surjectivity chain
#print axioms CubeToSU3.Continuous.exists_trace_zero_diagonal_log
#print axioms CubeToSU3.Continuous.exists_su3_log_of_diagonalization
#print axioms CubeToSU3.Continuous.expSU3_surjective_of_unitarySpectralTheorem3
#check CubeToSU3.Continuous.ExponentialSurjective
#check CubeToSU3.Continuous.HasSmoothLieGroupStructure

-- Classical QCD kinematics only
#print axioms CubeToSU3.QCD.su3Bracket_swap
#print axioms CubeToSU3.QCD.fieldStrength_mem_su3
#print axioms CubeToSU3.QCD.fieldStrength_swap
#print axioms CubeToSU3.QCD.fieldStrength_self
#print axioms CubeToSU3.QCD.yangMillsDensity_nonneg
#print axioms CubeToSU3.QCD.colorAction_mul

-- Explicit classical dynamics and the exact g_s-versus-unit gap
#print axioms CubeToSU3.QCD.fieldStrengthG_sub_naive
#print axioms CubeToSU3.QCD.fieldStrengthG_swap
#print axioms CubeToSU3.QCD.yangMillsDensityG_nonneg
#print axioms CubeToSU3.QCD.YangMillsEquation
#print axioms CubeToSU3.QCD.DiracEquation
#print axioms CubeToSU3.QCD.SolvesClassicalQCDProblem

-- Dimensionless scale calibration versus measured QCD coupling
#print axioms CubeToSU3.Calibration.calibratedRHS_sub_naive
#print axioms CubeToSU3.Calibration.recover_naiveRHS
#print axioms CubeToSU3.Calibration.gS_MZ_central_sq
#print axioms CubeToSU3.Calibration.gS_MZ_central_sq_gt_one
#print axioms CubeToSU3.Calibration.calibrated_fieldStrength_gap

-- Inspect the six recorded rejected proposals.
#eval CubeToSU3.Rejected.rejectionLedger.map (fun e => e.candidate)

-- Deliberately last: this declaration must list exactly the eight external
-- physics assumptions and is the only report allowed to do so.
#print axioms CubeToSU3.PhysicsInputs.physical_ledger
