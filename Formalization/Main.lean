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
#print axioms OddZetaFormalization.lemma_2_1_poly_vanishing
#print axioms OddZetaFormalization.lemma_2_1_poly_deriv
#print axioms OddZetaFormalization.degree_centralFactorialPoly
#print axioms OddZetaFormalization.prop_2_2_binomial_identity
#print axioms OddZetaFormalization.prop_2_2_i_diag
#print axioms OddZetaFormalization.prop_2_2_ii_taylor_lcm_int
#print axioms OddZetaFormalization.prop_2_3_three_forms_eq
#print axioms OddZetaFormalization.prop_2_3_reciprocal_int
#print axioms OddZetaFormalization.prop_2_4_table_1_formula
#print axioms OddZetaFormalization.prop_2_4_poly_newton_expansion
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
#print axioms OddZetaFormalization.lemma_3_2_poly_quadratic_shift_coeff
#print axioms OddZetaFormalization.theorem_3_3_i_kernel_odd_reflection
#print axioms OddZetaFormalization.theorem_3_3_i_laurentCoeff_reflect
#print axioms OddZetaFormalization.theorem_3_3_i_laurent_even_pole_sum_zero
#print axioms OddZetaFormalization.theorem_3_3_ii_inner_support_compression
#print axioms OddZetaFormalization.theorem_3_4_WKWeight_pos
#print axioms OddZetaFormalization.theorem_3_4_simple_pole_telescoping
#print axioms OddZetaFormalization.theorem_3_4_moment_decomposition
#print axioms OddZetaFormalization.theorem_3_5_OmegaBPoly_eval_and_natDegree
#print axioms OddZetaFormalization.theorem_3_5_ii_vanishes_on_buffer
#print axioms OddZetaFormalization.theorem_3_5_ii_pos_beyond_buffer
#print axioms OddZetaFormalization.theorem_3_5_binomial_identity
#print axioms OddZetaFormalization.theorem_3_5_ii_shifted_series_truncation
-- Sections 4–7 & Section 1:
#print axioms OddZetaFormalization.theorem_4_3_EHead_det_eq_one
#print axioms OddZetaFormalization.theorem_4_3_ii_head_det
#print axioms OddZetaFormalization.theorem_4_3_iii_block_triangular_det
#print axioms OddZetaFormalization.theorem_4_4_tail_det_pos
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
