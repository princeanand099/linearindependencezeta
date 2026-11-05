import Mathlib.Data.Nat.Defs
import Formalization.ZetaPreliminaries
import Formalization.CentralFactorial
import Formalization.WindowedKernel
import Formalization.JetSeparation
import Formalization.SchurAndValuation
import Formalization.MainResults

/-!
# Main Entry Point and Axiom Audit
("All Odd Zeta Values Are Linearly Independent Over Q" by Prince Anand)

This root module imports the complete formalization hierarchy:
* `Formalization.ZetaPreliminaries` — Section 1 definitions (`ζ(2n+1)`, `oddZetaTuple`, `oddZetaSeq`) and classical preliminaries (Apéry, Lindemann, Euler).
* `Formalization.CentralFactorial` — Section 2 central factorial basis `ℰ_m(u)`, shifted Legendre step identity, `1/ℰ'_m(r²) ∈ ℤ`, harmonic telescoping `T_{m,r}`, Newton-Girard closed form, and totally positive matrix factorization.
* `Formalization.WindowedKernel` — Section 3 windowed rational kernel `G_k(z)`, Taylor jet `g_{k,t}`, Laurent coefficients `c_{r,m}`, parity vanishing, shifted-kernel expansion (`R₀(z)`, `W_K(m)`), and tail remainder `Ω_B(z)`.
* `Formalization.JetSeparation` — Section 4 jet functional `S_{2n+1}`, Hermite basis `(H_{0,s}, ℓ_{r,j})`, upper-triangular divisor cascade, and Vandermonde-product tail submatrix determinant.
* `Formalization.SchurAndValuation` — Sections 5 & 6 finite-step Schur complement `L_n`, outer-pole cancellation, 2-adic valuation exponent `∑ v_p(m) = n A₀K`, centered harmonic numbers `H_m^{(c)}`, and pure rational proof of `H'_n(A₀, A) < 0`.
* `Formalization.MainResults` — Section 7 Euler sine-product square identity (`C_m ≠ 0`), Theorem 1.1 (All odd zeta values are linearly independent over `ℚ`), Corollary 1.2, and Corollary 1.3.
-/

-- Verify that the principal theorems typecheck with exact manuscript signatures:
#check OddZetaFormalization.theorem_1_1_odd_zeta_linear_independent
#check OddZetaFormalization.theorem_1_1_eq_1_7
#check OddZetaFormalization.theorem_1_1_eq_1_8
#check OddZetaFormalization.corollary_1_2_infinite
#check OddZetaFormalization.corollary_1_2_i_irrational
#check OddZetaFormalization.corollary_1_2_i_ratio_irrational
#check OddZetaFormalization.corollary_1_2_ii
#check OddZetaFormalization.corollary_1_2_iii
#check OddZetaFormalization.corollary_1_3_i
#check OddZetaFormalization.corollary_1_3_ii
#check OddZetaFormalization.corollary_1_3_iii

-- Axiom audit for the principal theorems across Sections 1–7:
-- Section 2 (CentralFactorial.lean):
#print axioms OddZetaFormalization.natDegree_centralFactorialPoly
#print axioms OddZetaFormalization.prop_2_2_i_vanishing
#print axioms OddZetaFormalization.prop_2_3_derivative_eval_eq_EPrimeForm1
#print axioms OddZetaFormalization.prop_2_4_harmonic_telescoping
#print axioms OddZetaFormalization.prop_2_4_asymptotic
#print axioms OddZetaFormalization.prop_2_2_binomial_identity
#print axioms OddZetaFormalization.prop_2_2_binomial_identity_int
#print axioms OddZetaFormalization.prop_2_2_eval_sq_int
#print axioms OddZetaFormalization.prop_2_2_i_diag
#print axioms OddZetaFormalization.prop_2_2_ii_taylor_lcm_int
#print axioms OddZetaFormalization.prop_2_3_three_forms_eq
#print axioms OddZetaFormalization.prop_2_3_reciprocal_int
#print axioms OddZetaFormalization.prop_2_4_table_1_formula
#print axioms OddZetaFormalization.prop_2_4_second_derivative_eq
#print axioms OddZetaFormalization.prop_2_4_harmonic_telescoping_verified
#print axioms OddZetaFormalization.theorem_2_5_eq_2_20_linear_w_factorization
#print axioms OddZetaFormalization.theorem_2_5_taylor_shift_factorization
#print axioms OddZetaFormalization.theorem_2_5_arbitrary_order_derivative
#print axioms OddZetaFormalization.elemSymmDeletedSq_eq_elemSymmNewton
#print axioms OddZetaFormalization.theorem_2_5_lcm_elemSymm_int
#print axioms OddZetaFormalization.theorem_2_5_linear_shift_product
#print axioms OddZetaFormalization.theorem_2_5_vandermonde_poly_eq
#print axioms OddZetaFormalization.theorem_2_5_linear_shift_lcm_int
#print axioms OddZetaFormalization.theorem_2_6_strict_total_positivity
#print axioms OddZetaFormalization.theorem_2_6_matrix_factorization
#print axioms OddZetaFormalization.theorem_2_6_lattice_path_minor_pos
-- Section 3 (WindowedKernel.lean):
#print axioms OddZetaFormalization.lemma_3_1_total_pole_multiplicity
#print axioms OddZetaFormalization.lemma_3_1_degree_margin
#print axioms OddZetaFormalization.lemma_3_2_gkZero_ne_zero
#print axioms OddZetaFormalization.lemma_3_2_eq_3_6_product_eq_closed
#print axioms OddZetaFormalization.lemma_3_2_outer_binomial_identity
#print axioms OddZetaFormalization.lemma_3_2_poly_quadratic_shift_coeff
#print axioms OddZetaFormalization.lemma_3_2_poly_quadratic_add_shift_coeff
#print axioms OddZetaFormalization.lemma_3_2_laurentCoeffAt_eq_cauchy_coeff
#print axioms OddZetaFormalization.theorem_3_3_i_kernel_odd_reflection
#print axioms OddZetaFormalization.theorem_3_3_i_laurentCoeff_reflect
#print axioms OddZetaFormalization.theorem_3_3_i_laurent_even_pole_sum_zero
#print axioms OddZetaFormalization.theorem_3_3_i_simple_pole_sum_zero_from_degree
#print axioms OddZetaFormalization.theorem_3_3_ii_inner_support_compression
#print axioms OddZetaFormalization.theorem_3_4_WKWeight_pos
#print axioms OddZetaFormalization.theorem_3_4_simple_pole_telescoping
#print axioms OddZetaFormalization.theorem_3_4_eq_3_18_simple_pole_limit
#print axioms OddZetaFormalization.theorem_3_4_eq_3_19_higher_pole_limit
#print axioms OddZetaFormalization.theorem_3_4_eq_3_16_full_series_limit
#print axioms OddZetaFormalization.theorem_3_4_moment_decomposition
#print axioms OddZetaFormalization.theorem_3_5_OmegaBPoly_eval_and_natDegree
#print axioms OddZetaFormalization.theorem_3_5_ii_vanishes_on_buffer
#print axioms OddZetaFormalization.theorem_3_5_ii_pos_beyond_buffer
#print axioms OddZetaFormalization.theorem_3_5_binomial_identity
#print axioms OddZetaFormalization.theorem_3_5_ii_WKBWeight_eq_and_pos
#print axioms OddZetaFormalization.theorem_3_5_ii_shifted_series_truncation
#print axioms OddZetaFormalization.theorem_3_5_iii_pole_shift_factorization
-- Section 4 (JetSeparation.lean):
#print axioms OddZetaFormalization.prop_4_1_eq_4_7_inner_pole_pairing
#print axioms OddZetaFormalization.prop_4_1_i_poleSum_eq_S2nPlus1Functional
#print axioms OddZetaFormalization.prop_4_1_ii_central_pole_jet
#print axioms OddZetaFormalization.prop_4_1_ii_off_center_pole_jet
#print axioms OddZetaFormalization.prop_4_1_ii_poleSum_eq_jet_expansion
#print axioms OddZetaFormalization.prop_4_1_ii_leading_jet_weights
#print axioms OddZetaFormalization.prop_4_1_iii_tail_vanishing
#print axioms OddZetaFormalization.HermiteOmega_at_zero_eq_factorial_pow_four
#print axioms OddZetaFormalization.lemma_4_2_i_H0Poly_full
#print axioms OddZetaFormalization.lemma_4_2_ii_iii_HrPoly_full
#print axioms OddZetaFormalization.lemma_4_2_hermite_natDegree_bounds
#print axioms OddZetaFormalization.lemma_4_2_hermite_interpolation_reconstruction
#print axioms OddZetaFormalization.lemma_4_2_ell_deriv_at_node
#print axioms OddZetaFormalization.lemma_4_2_hermite_uniqueness
#print axioms OddZetaFormalization.lemma_4_2_hermite_basis_expansion_unique
#print axioms OddZetaFormalization.theorem_4_3_EHead_det_eq_one
#print axioms OddZetaFormalization.theorem_4_3_ii_head_det
#print axioms OddZetaFormalization.theorem_4_3_leibniz_jet_reduction
#print axioms OddZetaFormalization.theorem_4_3_step2_hermite_testing
#print axioms OddZetaFormalization.theorem_4_3_backward_hermite_divisibility_zero
#print axioms OddZetaFormalization.theorem_4_3_iii_block_triangular_det
#print axioms OddZetaFormalization.theorem_4_4_exponent_identities
#print axioms OddZetaFormalization.theorem_4_4_four_step_product_eq_closed_form
#print axioms OddZetaFormalization.theorem_4_4_tail_det_pos
#print axioms OddZetaFormalization.innerNodeWeight_int
#print axioms OddZetaFormalization.theorem_4_4_monic_tail_det_int
#print axioms OddZetaFormalization.remark_4_5_odd_inner_multiplicity
-- Sections 5–7 & Section 1:
#print axioms OddZetaFormalization.prop_5_2_schur_row_identity
#print axioms OddZetaFormalization.prop_5_2_block_row_elimination_det
#print axioms OddZetaFormalization.theorem_5_3_i_schur_complement_det
#print axioms OddZetaFormalization.theorem_5_3_ii_scalar_cancellation
#print axioms OddZetaFormalization.theorem_6_3_i_centering_row_identity
#print axioms OddZetaFormalization.prop_6_4_i_link_to_first_tail_poly
#print axioms OddZetaFormalization.theorem_6_5_ii_pure_rational_negativity_proof
#print axioms OddZetaFormalization.theorem_7_1_euler_constant_nonzero
#print axioms OddZetaFormalization.liouville_integrality_contradiction
#print axioms OddZetaFormalization.theorem_1_1_odd_zeta_linear_independent
#print axioms OddZetaFormalization.theorem_1_1_eq_1_7
#print axioms OddZetaFormalization.theorem_1_1_eq_1_8
#print axioms OddZetaFormalization.corollary_1_2_infinite
#print axioms OddZetaFormalization.corollary_1_2_i_irrational
#print axioms OddZetaFormalization.corollary_1_2_i_ratio_irrational
#print axioms OddZetaFormalization.corollary_1_2_ii
#print axioms OddZetaFormalization.corollary_1_2_iii
#print axioms OddZetaFormalization.corollary_1_3_i
#print axioms OddZetaFormalization.corollary_1_3_ii
#print axioms OddZetaFormalization.corollary_1_3_iii
#print axioms OddZetaFormalization.euler_even_zeta_rational_multiple
#print axioms OddZetaFormalization.even_zeta_tuple_linearIndependent
