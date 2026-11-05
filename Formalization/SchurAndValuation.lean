import Formalization.JetSeparation
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Sections 5 & 6: Schur-Complement Moment Determinant, Block-Triangular Reduction,
# `p`-Adic Valuations, Harmonic Centering, and Net Exponent Bounds

This module formalizes Sections 5 and 6 of Prince Anand,
*"All Odd Zeta Values Are Linearly Independent Over ℚ"*:
- **Equation (5.1) & Definition 5.1**: Hypothetical integer linear relation
  `∑_{j=1}^n a_{2j+1} ζ(2j+1) + c = 0` (`a_{2n+1} > 0`) and the `(N+R) × (N+R)` Schur-complement
  matrix `M_K(a, c)` with determinant `Δ_{N+R} := det M_K(a, c) ∈ ℚ` (5.2).
- **Proposition 5.2**: Schur-complement moment identity `Δ_{N+R} = det (L_{top} // a_{2n+1} 𝒜_{bot})` (5.3)
  via the exact row-operation identity
  `a_{2n+1} ℛ_0(P) - c S_{2n+1}(P) = a_{2n+1} 𝒜(P) - ∑_{j=1}^{n-1} ζ(2j+1) L^{(2j+1)}(P)`.
- **Theorem 5.3**: Transition matrix `Γ := (L_{top}[:, J_{tail}])⁻¹ L_{top}[:, J_{head}]` (5.4),
  reduced kernel basis polynomials `Q_d(u)` (5.5), block-triangular determinant factorization (5.6),
  homogeneous scalar cancellation of `w_{2n+1,0}`, osculatory left factorization (5.7), and symmetric
  outer-pole cancellation `1/(s - r) - 1/(s + r) = 2r / (s² - r²)` (5.9).
- **Theorem 5.4**: Cauchy–Binet series expansion (5.10) and archimedean rate functions (5.11)–(5.19).
- **Lemma 6.1**: Base kernel factorial valuation `V_p(k)` (6.1), entry-wise `p`-adic valuation bound (6.2),
  and `-q_0 - d_1 - d_2 - t = -L_k` Cauchy-product exponent cancellation (6.3).
- **Proposition 6.2**: Inner-window `p`-adic integrality `g_k(w) = U_{out,k}(w) U_{in,k}(w)` (6.4)–(6.8).
- **Theorem 6.3**: Midpoint-centered harmonic numbers `H̃_{k,AK}^{(t)} := H_k^{(t)} - H_{AK}^{(t)}` (6.9),
  centered remainder `ℛ_0^{cent}(P)` (6.10), polynomial and determinant identity (6.11) with
  `c_{cent} := c + ∑_{j=1}^n a_{2j+1} H_{AK}^{(2j+1)}`, and support of inner centered harmonic numbers
  in `[AK - A₀K + 1, AK + A₀K]` (ii).
- **Proposition 6.4**:
  - (i) Outer-pole binomial identity `(r - A₀K)\binom{r + A₀K}{2A₀K} = (2A₀K + 1)\binom{r + A₀K}{2A₀K + 1}`
    (6.12), Kummer divisibility into `lcm(1, ..., (A + A₀)K)`, link to `ℰ_{A₀K+1}(r²)` (6.13),
    and boundary floor function `Ω_{bdry}(α, β) ∈ {0, 1}` (6.14).
  - (ii) Elimination of tail primes `p > 2AK` when `A > C + R_c = (2n - 1)A_0` (6.16).
- **Theorem 6.5**: Effective determinant-clearing multiplier `D_{N+R}^{eff}` (6.17)–(6.18),
  Gaussian elimination quadratic vanishing identity
  `∑_{j₁=0}^{m₁-1} j₁ + ∑_{j₂=0}^{m₂-1} j₂ + ∑_{j=0}^{m₁+m₂-1} j = m₁(m₁-1) + m₂(m₂-1) + m₁m₂`,
  scaling parameters `c_0 = 3/100`, `A_0(n) = 0.03 / (2n - 1)`, `R_c(n) = 2(n - 1)A_0(n)`,
  `A(n) = 0.075` (6.20), derivative bound `H_n'(y) ≤ -u(3.2u² + 0.8)/((u²+4)(u²+1)) < 0`,
  unconditional Mathlib4 real logarithm enclosures (`log 2, log 3, log 5, log 67`),
  concavity numerator `q(1/11) < -141/1331 < 0`, and verification over both `ℝ` and `ℚ` of
  `f_{upper}(1/67) < -0.1362 < 0` and `c_0^2 f_{upper}(1/67) < -0.000122 < 0` across all `n ≥ 1`
  (6.21)–(6.24).
-/

namespace OddZetaFormalization

open scoped BigOperators

/-!
## Section 5: Schur-Complement Moment Identity & Block-Triangular Reduction
-/

/-- **Equation (1.5) & Section 5.1**: The secondary odd-zeta elimination operator
$$L^{(2j+1)}(P) := a_{2n+1} S_{2j+1}(P) - a_{2j+1} S_{2n+1}(P) \quad (1 \le j \le n-1).$$ -/
def eliminationOpL (a_top a_j S_j S_top : ℚ) : ℚ :=
  a_top * S_j - a_j * S_top

/-- **Equation (5.1) (Hypothetical Integer Relation & Sign Normalization `a_{2n+1} > 0`, p. 24)**:
Suppose `1, ζ(3), ..., ζ(2n-1)` are linearly independent over `ℚ` (`oddZetaLinearIndependent (n - 1)`)
and `1, ζ(3), ..., ζ(2n+1)` satisfy a nontrivial integer relation
`∑_{j=1}^n a_{2j+1} ζ(2j+1) + c = 0` with `(a, c) ≠ (0, 0)`.
Then:
1. The top coefficient `a_{2n+1}` (`a ⟨n - 1, _⟩`) is non-zero.
2. Multiplying `(a, c)` by `sign(a_{2n+1}) ∈ {-1, +1}` produces an integer relation `(a', c')`
   satisfying `∑_{j=1}^n a'_{2j+1} ζ(2j+1) + c' = 0` with `a'_{2n+1} > 0`. -/
theorem lemma_5_1_integer_relation_wlog_pos (n : ℕ) (hn : 1 ≤ n)
    (h_indep_prev : LinearIndependent ℚ (oddZetaTuple (n - 1)))
    (a : Fin n → ℤ) (c : ℤ)
    (h_rel : (∑ j : Fin n, (a j : ℝ) * riemannZetaReal (2 * (j.val + 1) + 1)) + (c : ℝ) = 0)
    (h_nontriv : (∃ j : Fin n, a j ≠ 0) ∨ c ≠ 0) :
    a ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ ≠ 0 ∧
    ∃ (a' : Fin n → ℤ) (c' : ℤ),
      ((∑ j : Fin n, (a' j : ℝ) * riemannZetaReal (2 * (j.val + 1) + 1)) + (c' : ℝ) = 0) ∧
      0 < a' ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := by
  have h_top_ne : a ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ ≠ 0 := by
    intro h_zero
    have hn_eq : (n - 1) + 1 = n := Nat.sub_add_cancel hn
    let e : Fin ((n - 1) + 1) ≃ Fin n := finCongr hn_eq
    have h_sum_split :
        (∑ j : Fin n, (a j : ℝ) * riemannZetaReal (2 * (j.val + 1) + 1)) =
        (∑ i : Fin (n - 1), (a (e (Fin.castSucc i)) : ℝ) * riemannZetaReal (2 * (i.val + 1) + 1)) +
          (a ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ : ℝ) * riemannZetaReal (2 * n + 1) := by
      rw [← Equiv.sum_comp e]
      rw [Fin.sum_univ_castSucc]
      have h_first :
          (∑ i : Fin (n - 1), (a (e (Fin.castSucc i)) : ℝ) * riemannZetaReal (2 * ((e (Fin.castSucc i)).val + 1) + 1)) =
          (∑ i : Fin (n - 1), (a (e (Fin.castSucc i)) : ℝ) * riemannZetaReal (2 * (i.val + 1) + 1)) := by
        apply Finset.sum_congr rfl
        intro i _
        rfl
      have h_last_idx : e (Fin.last (n - 1)) = ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := by
        ext; simp [e]
      have h_last_arg : 2 * ((e (Fin.last (n - 1))).val + 1) + 1 = 2 * n + 1 := by
        simp [e]; omega
      rw [h_first, h_last_arg, h_last_idx]
    rw [h_sum_split, h_zero, Int.cast_zero, zero_mul, add_zero] at h_rel
    let coeff : Fin ((n - 1) + 1) → ℚ :=
      Fin.cases (c : ℚ) (fun i : Fin (n - 1) => (a (e (Fin.castSucc i)) : ℚ))
    have h_rel_prev : ∑ k : Fin ((n - 1) + 1), coeff k • oddZetaTuple (n - 1) k = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [coeff, Fin.cases_zero, Fin.cases_succ, oddZetaTuple_zero,
        oddZetaTuple_succ, Rat.smul_def, mul_one]
      push_cast
      linarith
    have h_all_zero := (Fintype.linearIndependent_iff.mp h_indep_prev) coeff h_rel_prev
    have hc0 : c = 0 := by
      have h0 := h_all_zero 0
      simp only [coeff, Fin.cases_zero, Int.cast_eq_zero] at h0
      exact h0
    have ha0 : ∀ j : Fin n, a j = 0 := by
      intro j
      by_cases hj : j.val < n - 1
      · have hi := h_all_zero (Fin.succ ⟨j.val, hj⟩)
        simp only [coeff, Fin.cases_succ, Int.cast_eq_zero] at hi
        have he : e (Fin.castSucc ⟨j.val, hj⟩) = j := by ext; rfl
        rw [he] at hi
        exact hi
      · have hj_lt : j.val < n := j.isLt
        have hj_eq : j = ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := by
          ext; dsimp; omega
        rw [hj_eq, h_zero]
    rcases h_nontriv with ⟨j, hj⟩ | hc_ne
    · exact hj (ha0 j)
    · exact hc_ne hc0
  refine ⟨h_top_ne, ?_⟩
  by_cases h_pos : 0 < a ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩
  · exact ⟨a, c, h_rel, h_pos⟩
  · have h_neg : a ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ < 0 :=
      lt_of_le_of_ne (not_lt.mp h_pos) h_top_ne
    have h_pos_neg : 0 < -a ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ := neg_pos.mpr h_neg
    refine ⟨fun j => -a j, -c, ?_, h_pos_neg⟩
    have h_neg_sum :
        (∑ j : Fin n, ((-a j : ℤ) : ℝ) * riemannZetaReal (2 * (j.val + 1) + 1)) + ((-c : ℤ) : ℝ) =
        -((∑ j : Fin n, (a j : ℝ) * riemannZetaReal (2 * (j.val + 1) + 1)) + (c : ℝ)) := by
      simp only [Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
      ring
    rw [h_neg_sum, h_rel, neg_zero]

/-- **Definition 5.1 (Dimension and Scaling Parameters of the `(N+R) × (N+R)` Schur-Complement Matrix, pp. 24–25)**:
- `N = A₀K + 1` (number of inner nodes and bottom moment rows, `C := A₀`),
- `R_each = 2 A₀K + 1` (number of top rows per secondary odd zeta value `ζ(2j+1)`, `R_{c,each} := 2A₀`),
- `R = (n - 1)(2A₀K + 1)` (total number of top elimination rows, `R_c := 2(n - 1)A₀`),
- `N + R = (2n - 1)A₀K + n` (total matrix dimension, with asymptotic column slope `C + R_c = (2n - 1)A₀`). -/
def paramC (A0 : ℚ) : ℚ := A0
def paramRcEach (A0 : ℚ) : ℚ := 2 * A0
def paramRcOfA0 (n : ℕ) (A0 : ℚ) : ℚ := 2 * ((n - 1 : ℕ) : ℚ) * A0

theorem def_5_1_dimension_identities (n A0K : ℕ) (hn : 1 ≤ n) (A0 : ℚ) :
    let N := A0K + 1
    let R_each := 2 * A0K + 1
    let R := (n - 1) * R_each
    R = 2 * (n - 1) * A0K + (n - 1) ∧
    N + R = (2 * n - 1) * A0K + n ∧
    paramC A0 + paramRcOfA0 n A0 = ((2 * n - 1 : ℕ) : ℚ) * A0 := by
  intro N R_each R
  refine ⟨by dsimp [R, R_each]; ring, ?_, ?_⟩
  · dsimp [N, R, R_each]
    have h_2n1 : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
    have h_n : (n - 1) + 1 = n := by omega
    rw [h_2n1]
    calc A0K + 1 + (n - 1) * (2 * A0K + 1)
        = (2 * (n - 1) + 1) * A0K + ((n - 1) + 1) := by ring
      _ = (2 * (n - 1) + 1) * A0K + n := by rw [h_n]
  · unfold paramC paramRcOfA0
    have h1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := Nat.cast_sub hn
    have h2 : ((2 * n - 1 : ℕ) : ℚ) = 2 * (n : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
      push_cast; rfl
    rw [h1, h2]; ring

/-- **Definition 5.1 (Equation (5.2): Block Structure of the `(R + N) × (R + N)` Schur-Complement Matrix `M_K(a, c)`)**:
Given the top elimination blocks `L_tail` (`R × R` on `J_tail`) and `L_head` (`R × N` on `J_head`),
and the bottom remainder-plus-constant blocks `B_tail = a_{2n+1} R_{0,bot}[:, J_tail] - c S_{2n+1,bot}[:, J_tail]`
and `B_head = a_{2n+1} R_{0,bot}[:, J_head] - c S_{2n+1,bot}[:, J_head]`,
`SchurMatrixBlock L_tail L_head B_tail B_head` is the `(R + N) × (R + N)` block matrix, and its determinant
is `Δ_{N+R}`. -/
def SchurMatrixBlock {R N : ℕ} {K : Type*}
    (L_tail : Matrix (Fin R) (Fin R) K) (L_head : Matrix (Fin R) (Fin N) K)
    (B_tail : Matrix (Fin N) (Fin R) K) (B_head : Matrix (Fin N) (Fin N) K) :
    Matrix (Fin R ⊕ Fin N) (Fin R ⊕ Fin N) K :=
  Matrix.fromBlocks L_tail L_head B_tail B_head

/-- **Definition 5.1 (Vanishing of `S_{2n+1,bot}` on All Tail Columns `J_{tail}`, p. 25)**:
By Proposition 4.1(iii), `S_{2n+1}(ℰ_k ℰ_m) = 0` for every row index `k` and every tail column
`m = A₀K + 1 + j` (`j ≥ 0`), so the tail block of `S_{2n+1,bot}` vanishes identically. -/
theorem def_5_1_S2n1_bot_tail_eq_zero (n A0K AK R : ℕ) :
    Matrix.of (fun (k : Fin (A0K + 1)) (j : Fin R) =>
      S2nPlus1Functional n A0K AK (fun x =>
        evalCentralFactorial k.val x * evalCentralFactorial (A0K + 1 + j.val) x)) = 0 := by
  ext k j
  simp only [Matrix.of_apply, Matrix.zero_apply]
  exact prop_4_1_iii_tail_vanishing n A0K AK (A0K + 1 + j.val) (by omega)
    (fun x => evalCentralFactorial k.val x)

/-- **Proposition 5.2 (Row-Operation Identity Proving Equation (5.3), p. 25)**:
Under any linear relation `∑_{j=1}^n a_{2j+1} ζ(2j+1) + c = 0`, for any polynomial `P` with
odd-zeta functionals `S_odd : Fin n → ℚ` (where index `n - 1` is `S_{2n+1}(P)`) and harmonic
remainder `R0 = ℛ_0(P)`, the bottom-row entry `a_{2n+1} ℛ_0(P) - c S_{2n+1}(P)` satisfies:
$$a_{2n+1} \mathcal{R}_0(P) - c S_{2n+1}(P)
  = a_{2n+1} \mathcal{A}(P) - \sum_{j=1}^n \zeta(2j+1) \left(a_{2n+1} S_{2j+1}(P) - a_{2j+1} S_{2n+1}(P)\right),$$
where the `j = n` term in the sum vanishes identically (`a_{2n+1} S_{2n+1} - a_{2n+1} S_{2n+1} = 0`). -/
theorem prop_5_2_schur_row_identity (n : ℕ) (a : Fin n → ℚ) (c : ℚ)
    (S_odd : Fin n → ℚ) (S_top R0 : ℚ)
    (h_rel : (∑ j : Fin n, (a j : ℝ) * riemannZetaReal (2 * (j.val + 1) + 1)) + (c : ℝ) = 0)
    (a_top : ℚ) :
    (a_top : ℝ) * (R0 : ℝ) - (c : ℝ) * (S_top : ℝ) =
      (a_top : ℝ) * oddZetaLinearForm n S_odd R0 -
        ∑ j : Fin n,
          riemannZetaReal (2 * (j.val + 1) + 1) *
            (eliminationOpL a_top (a j) (S_odd j) S_top : ℝ) := by
  have hc_eq : (c : ℝ) = - ∑ j : Fin n, (a j : ℝ) * riemannZetaReal (2 * (j.val + 1) + 1) := by
    linarith
  unfold oddZetaLinearForm eliminationOpL
  rw [hc_eq]
  have h_sum :
      ∑ j : Fin n,
        riemannZetaReal (2 * (j.val + 1) + 1) *
          ((a_top * S_odd j - a j * S_top : ℚ) : ℝ) =
      (a_top : ℝ) * (∑ j : Fin n, (S_odd j : ℝ) * riemannZetaReal (2 * (j.val + 1) + 1)) -
        (∑ j : Fin n, (a j : ℝ) * riemannZetaReal (2 * (j.val + 1) + 1)) * (S_top : ℝ) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  rw [h_sum]
  ring

/-- **Proposition 5.2 (Identical Vanishing of the `j = n` Term in the Row-Operation Sum, p. 25)**:
For `j = n` (`a_j = a_{2n+1}` and `S_j = S_{2n+1}`), `eliminationOpL a_{2n+1} a_{2n+1} S_{2n+1} S_{2n+1} = 0`. -/
theorem prop_5_2_top_term_eliminationOpL_zero (a_top S_top : ℚ) :
    eliminationOpL a_top a_top S_top S_top = 0 := by
  unfold eliminationOpL
  ring

/-- **Proposition 5.2 (Equation (5.3): Full `(R + N) × (R + N)` Block-Row Elimination Determinant Identity)**:
In the `(R + N) × (R + N)` Schur-complement matrix, subtracting linear combinations `Z * L₁` and
`Z * L₂` of the top `R` rows `(L₁, L₂)` from the bottom `N` rows `(B₁, B₂)` preserves the determinant
identically:
$$\det \begin{pmatrix} L_1 & L_2 \\ B_1 - Z L_1 & B_2 - Z L_2 \end{pmatrix}
  = \det \begin{pmatrix} L_1 & L_2 \\ B_1 & B_2 \end{pmatrix}.$$ -/
theorem prop_5_2_block_row_elimination_det {R N : ℕ} {K : Type*} [CommRing K]
    (L1 : Matrix (Fin R) (Fin R) K) (L2 : Matrix (Fin R) (Fin N) K)
    (B1 : Matrix (Fin N) (Fin R) K) (B2 : Matrix (Fin N) (Fin N) K)
    (Z : Matrix (Fin N) (Fin R) K) :
    (Matrix.fromBlocks L1 L2 (B1 - Z * L1) (B2 - Z * L2)).det =
      (Matrix.fromBlocks L1 L2 B1 B2).det := by
  have h_mul :
      Matrix.fromBlocks L1 L2 (B1 - Z * L1) (B2 - Z * L2) =
        Matrix.fromBlocks (1 : Matrix (Fin R) (Fin R) K) 0 (-Z) (1 : Matrix (Fin N) (Fin N) K) *
          Matrix.fromBlocks L1 L2 B1 B2 := by
    rw [Matrix.fromBlocks_multiply]
    simp [sub_eq_add_neg, add_comm]
  rw [h_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one,
      mul_one, one_mul]

/-- **Proposition 5.2 (Equation (5.3): Full Schur-Complement Moment Determinant Identity, p. 25)**:
Whenever the bottom blocks satisfy `B_tail = a_{2n+1} • A_tail - Z * L_tail` and
`B_head = a_{2n+1} • A_head - Z * L_head` (from the row-operation identity of Proposition 5.2,
where `Z` places `ζ(2j+1)` in row `(j, k)` of the `j`-th top block), adding `Z` times the top
`R` rows to the bottom `N` rows yields:
$$\Delta_{N+R} = \det \begin{pmatrix} L_{\mathrm{tail}} & L_{\mathrm{head}} \\ B_{\mathrm{tail}} & B_{\mathrm{head}} \end{pmatrix}
  = \det \begin{pmatrix} L_{\mathrm{tail}} & L_{\mathrm{head}} \\ a_{2n+1} \mathcal{A}_{\mathrm{tail}} & a_{2n+1} \mathcal{A}_{\mathrm{head}} \end{pmatrix}.$$ -/
theorem prop_5_2_full_moment_det_identity {R N : ℕ}
    (L_tail : Matrix (Fin R) (Fin R) ℝ) (L_head : Matrix (Fin R) (Fin N) ℝ)
    (A_tail : Matrix (Fin N) (Fin R) ℝ) (A_head : Matrix (Fin N) (Fin N) ℝ)
    (Z : Matrix (Fin N) (Fin R) ℝ) (a_top : ℝ) :
    (Matrix.fromBlocks L_tail L_head (a_top • A_tail - Z * L_tail) (a_top • A_head - Z * L_head)).det =
      (Matrix.fromBlocks L_tail L_head (a_top • A_tail) (a_top • A_head)).det :=
  prop_5_2_block_row_elimination_det L_tail L_head (a_top • A_tail) (a_top • A_head) Z

/-- **Theorem 5.3(i) (Equation (5.4): The `R × N` Transition Matrix `Γ`)**:
$$\Gamma := (L_{\mathrm{top}}[:, J_{\mathrm{tail}}])^{-1} L_{\mathrm{top}}[:, J_{\mathrm{head}}] \in \mathbb{Q}^{R \times N}.$$ -/
noncomputable def transitionMatrixGamma {R N : ℕ} {K : Type*} [CommRing K]
    (L_tail : Matrix (Fin R) (Fin R) K) (L_head : Matrix (Fin R) (Fin N) K) :
    Matrix (Fin R) (Fin N) K :=
  L_tail⁻¹ * L_head

/-- **Theorem 5.3(i) (Equations (5.4)–(5.6): Block-Triangular Column Reduction and Schur Complement Determinant)**:
For any commutative ring `K`, any invertible `R × R` tail submatrix `L_tail` (`IsUnit L_tail.det`),
any `R × N` head submatrix `L_head`, and any bottom blocks `B_tail` (`N × R`) and `B_head` (`N × N`),
setting `Γ := L_tail⁻¹ * L_head` yields:
$$\det \begin{pmatrix} L_{\mathrm{tail}} & L_{\mathrm{head}} \\ B_{\mathrm{tail}} & B_{\mathrm{head}} \end{pmatrix}
  = \det(L_{\mathrm{tail}}) \cdot \det(B_{\mathrm{head}} - B_{\mathrm{tail}} \Gamma).$$ -/
theorem theorem_5_3_i_schur_complement_det {R N : ℕ} {K : Type*} [CommRing K]
    (L_tail : Matrix (Fin R) (Fin R) K) (L_head : Matrix (Fin R) (Fin N) K)
    (B_tail : Matrix (Fin N) (Fin R) K) (B_head : Matrix (Fin N) (Fin N) K)
    (hL : IsUnit L_tail.det) :
    let Γ : Matrix (Fin R) (Fin N) K := L_tail⁻¹ * L_head
    (Matrix.fromBlocks L_tail L_head B_tail B_head).det =
      L_tail.det * (B_head - B_tail * Γ).det := by
  intro Γ
  have h_cancel : L_tail * Γ = L_head := by
    dsimp [Γ]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv L_tail hL, Matrix.one_mul]
  have h_block :
      Matrix.fromBlocks L_tail L_head B_tail B_head *
        Matrix.fromBlocks (1 : Matrix (Fin R) (Fin R) K) (-Γ) 0 (1 : Matrix (Fin N) (Fin N) K) =
      Matrix.fromBlocks L_tail 0 B_tail (B_head - B_tail * Γ) := by
    rw [Matrix.fromBlocks_multiply]
    simp [h_cancel, sub_eq_add_neg, add_comm]
  have h_det := congrArg Matrix.det h_block
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one,
      mul_one, mul_one, Matrix.det_fromBlocks_zero₁₂] at h_det
  exact h_det

/-- **Theorem 5.3(i) (Equation (5.6): Complete Factorized Moment Determinant Identity, p. 26)**:
Combining `L_tail = a_{2n+1} • S_tail` (since `S_{2n+1}` vanishes on `J_tail` by Proposition 4.1(iii)),
Proposition 5.2 (Equation 5.3), and the Schur complement reduction (Theorem 5.3(i)) gives the exact
Equation (5.6) identity:
$$\Delta_{N+R} = a_{2n+1}^{N+R} \det(S_{\mathrm{odd,top}}[:, J_{\mathrm{tail}}]) \cdot
  \det(\mathcal{A}_{\mathrm{head}} - \mathcal{A}_{\mathrm{tail}} \Gamma).$$ -/
theorem theorem_5_3_i_eq_5_6_full_reduction {R N : ℕ}
    (S_tail : Matrix (Fin R) (Fin R) ℝ) (L_head : Matrix (Fin R) (Fin N) ℝ)
    (A_tail : Matrix (Fin N) (Fin R) ℝ) (A_head : Matrix (Fin N) (Fin N) ℝ)
    (Z : Matrix (Fin N) (Fin R) ℝ) (a_top : ℝ)
    (ha : a_top ≠ 0) (hS : IsUnit S_tail.det) :
    let L_tail : Matrix (Fin R) (Fin R) ℝ := a_top • S_tail
    let Γ : Matrix (Fin R) (Fin N) ℝ := L_tail⁻¹ * L_head
    (Matrix.fromBlocks L_tail L_head (a_top • A_tail - Z * L_tail) (a_top • A_head - Z * L_head)).det =
      a_top ^ (N + R) * S_tail.det * (A_head - A_tail * Γ).det := by
  intro L_tail Γ
  rw [prop_5_2_full_moment_det_identity L_tail L_head A_tail A_head Z a_top]
  have hL : IsUnit L_tail.det := by
    dsimp [L_tail]
    rw [Matrix.det_smul, Fintype.card_fin]
    exact IsUnit.mul (IsUnit.pow R (Ne.isUnit ha)) hS
  rw [theorem_5_3_i_schur_complement_det L_tail L_head (a_top • A_tail) (a_top • A_head) hL]
  have h_sub : a_top • A_head - (a_top • A_tail) * Γ = a_top • (A_head - A_tail * Γ) := by
    rw [Matrix.smul_mul, smul_sub]
  rw [h_sub]
  dsimp [L_tail]
  rw [Matrix.det_smul, Matrix.det_smul, Fintype.card_fin, Fintype.card_fin, pow_add]
  ring

/-- **Theorem 5.3(i) (Equation (5.5): Reduced Kernel Basis Polynomials `Q_d(X) ∈ ℚ[X]`)**:
$$Q_d(X) := \mathcal{E}_d(X) - \sum_{m=0}^{R-1} \Gamma_{m,d} \mathcal{E}_{N+m}(X) \quad (0 \le d < N = A_0 K + 1).$$ -/
noncomputable def reducedKernelPolyQd (A0K R : ℕ)
    (Γ : Matrix (Fin R) (Fin (A0K + 1)) ℚ) (d : Fin (A0K + 1)) : Polynomial ℚ :=
  centralFactorialPoly d.val -
    ∑ m : Fin R, Polynomial.C (Γ m d) * centralFactorialPoly (A0K + 1 + m.val)

/-- **Theorem 5.3(i) (Degree Bound for `Q_d(X)`: `deg Q_d ≤ A₀K + R = N + R - 1`, p. 25)**:
For every `0 ≤ d ≤ A₀K`, `Q_d(X)` has degree at most `A₀K + R`. -/
theorem theorem_5_3_Qd_natDegree_le (A0K R : ℕ)
    (Γ : Matrix (Fin R) (Fin (A0K + 1)) ℚ) (d : Fin (A0K + 1)) :
    (reducedKernelPolyQd A0K R Γ d).natDegree ≤ A0K + R := by
  unfold reducedKernelPolyQd
  apply le_trans (Polynomial.natDegree_sub_le _ _)
  apply max_le
  · rw [natDegree_centralFactorialPoly]
    omega
  · apply le_trans (Polynomial.natDegree_sum_le _ _)
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, ?_⟩
    intro m _
    apply le_trans (Polynomial.natDegree_mul_le)
    rw [Polynomial.natDegree_C, zero_add, natDegree_centralFactorialPoly]
    omega

/-- **Theorem 5.3(i) (Exact Annihilation of `Q_d(X)` by All Top-Block Row Functionals `L_{top}`)**:
If `L_row : Fin R → (Polynomial ℚ →ₗ[ℚ] ℚ)` is the family of `R` top-block linear functionals,
`L_head i d = L_row i (ℰ_d)`, `L_tail i m = L_row i (ℰ_{N+m})` with `IsUnit L_tail.det`, and
`Γ = L_tail⁻¹ * L_head`, then `L_row i (Q_d) = 0` for all `i : Fin R` and `d : Fin (A₀K + 1)`. -/
theorem theorem_5_3_i_Qd_annihilated_by_Ltop (A0K R : ℕ)
    (L_row : Fin R → (Polynomial ℚ →ₗ[ℚ] ℚ))
    (hL : IsUnit (Matrix.of (fun i m : Fin R => L_row i (centralFactorialPoly (A0K + 1 + m.val)))).det)
    (i : Fin R) (d : Fin (A0K + 1)) :
    let L_tail : Matrix (Fin R) (Fin R) ℚ :=
      Matrix.of (fun i m => L_row i (centralFactorialPoly (A0K + 1 + m.val)))
    let L_head : Matrix (Fin R) (Fin (A0K + 1)) ℚ :=
      Matrix.of (fun i d => L_row i (centralFactorialPoly d.val))
    let Γ : Matrix (Fin R) (Fin (A0K + 1)) ℚ := L_tail⁻¹ * L_head
    L_row i (reducedKernelPolyQd A0K R Γ d) = 0 := by
  intro L_tail L_head Γ
  have h_cancel : (L_tail * Γ) i d = L_head i d := by
    have h_mat : L_tail * Γ = L_head := by
      dsimp [Γ]
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv L_tail hL, Matrix.one_mul]
    rw [h_mat]
  unfold reducedKernelPolyQd
  rw [map_sub, map_sum]
  have h_sum :
      (∑ m : Fin R, L_row i (Polynomial.C (Γ m d) * centralFactorialPoly (A0K + 1 + m.val))) =
        (L_tail * Γ) i d := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro m _
    have h_smul :
        Polynomial.C (Γ m d) * centralFactorialPoly (A0K + 1 + m.val) =
          (Γ m d) • centralFactorialPoly (A0K + 1 + m.val) := by
      rw [Algebra.smul_def, Polynomial.algebraMap_eq]
    rw [h_smul, map_smul, smul_eq_mul, mul_comm]
    rfl
  rw [h_sum, h_cancel]
  exact sub_self _

/-- **Theorem 5.3(i) (Linearity of the Reduced Bottom Block Entry `F_k(Q_d) = (F_head - F_tail * Γ)_{k,d}`, p. 26)**:
For any family of bottom-row linear functionals `F_bot : Fin (A0K + 1) → (Polynomial ℚ →ₗ[ℚ] ℚ)`
(such as `P ↦ ℛ_0(ℰ_k P)` or `P ↦ S_{2j+1}(ℰ_k P)`), evaluating `F_bot k` on `Q_d` yields the
`(k, d)` entry of `F_head - F_tail * Γ`. -/
theorem theorem_5_3_i_reduced_bottom_entry_eq (A0K R : ℕ)
    (F_bot : Fin (A0K + 1) → (Polynomial ℚ →ₗ[ℚ] ℚ))
    (Γ : Matrix (Fin R) (Fin (A0K + 1)) ℚ)
    (k d : Fin (A0K + 1)) :
    let F_head : Matrix (Fin (A0K + 1)) (Fin (A0K + 1)) ℚ :=
      Matrix.of (fun k' d' => F_bot k' (centralFactorialPoly d'.val))
    let F_tail : Matrix (Fin (A0K + 1)) (Fin R) ℚ :=
      Matrix.of (fun k' m' => F_bot k' (centralFactorialPoly (A0K + 1 + m'.val)))
    F_bot k (reducedKernelPolyQd A0K R Γ d) = (F_head - F_tail * Γ) k d := by
  intro F_head F_tail
  unfold reducedKernelPolyQd
  rw [map_sub, map_sum, Matrix.sub_apply, Matrix.mul_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  have h_smul :
      Polynomial.C (Γ m d) * centralFactorialPoly (A0K + 1 + m.val) =
        (Γ m d) • centralFactorialPoly (A0K + 1 + m.val) := by
    rw [Algebra.smul_def, Polynomial.algebraMap_eq]
  rw [h_smul, map_smul, smul_eq_mul, mul_comm]
  rfl

/-- **Theorem 5.3(ii) (Inner-Node Evaluation of `Q_d(r²)` on `{0, ..., A₀K}`)**:
At every inner node `0 ≤ r ≤ A₀K`, all tail basis polynomials `ℰ_{N+m}(r²)` (`N = A₀K + 1`) vanish
identically, so `(reducedKernelPolyQd A0K R Γ d).eval (r²) = ℰ_d(r²)`. -/
theorem theorem_5_3_ii_Qd_inner_node_eval (A0K R : ℕ)
    (Γ : Matrix (Fin R) (Fin (A0K + 1)) ℚ) (d : Fin (A0K + 1))
    (r : ℕ) (hr : r ≤ A0K) :
    (reducedKernelPolyQd A0K R Γ d).eval ((r : ℚ) ^ 2) =
      evalCentralFactorial d.val ((r : ℚ) ^ 2) := by
  unfold reducedKernelPolyQd
  rw [Polynomial.eval_sub, eval_centralFactorialPoly, Polynomial.eval_finset_sum]
  have h_tail_zero :
      (∑ m : Fin R,
        (Polynomial.C (Γ m d) * centralFactorialPoly (A0K + 1 + m.val)).eval ((r : ℚ) ^ 2)) = 0 := by
    apply Finset.sum_eq_zero
    intro m _
    rw [Polynomial.eval_mul, Polynomial.eval_C, eval_centralFactorialPoly,
        (prop_2_2_i_vanishing (A0K + 1 + m.val) r (by omega)).1, mul_zero]
  rw [h_tail_zero, sub_zero]

/-- **Theorem 5.3(i) (Invariance of `S_{2n+1}(ℰ_k Q_d) = S_{2n+1}(ℰ_k ℰ_d)`, p. 26)**:
Since `Q_d(r²) = ℰ_d(r²)` at every inner node `0 ≤ r ≤ A₀K` and `S_{2n+1}` depends only on
evaluations at the inner nodes `{0, ..., A₀K}`, we have `S_{2n+1}(ℰ_k Q_d) = S_{2n+1}(ℰ_k ℰ_d)`. -/
theorem theorem_5_3_i_S2nPlus1_Ek_Qd_eq_Ed (n A0K AK R : ℕ)
    (Γ : Matrix (Fin R) (Fin (A0K + 1)) ℚ) (k d : Fin (A0K + 1)) :
    S2nPlus1Functional n A0K AK (fun x =>
      evalCentralFactorial k.val x * (reducedKernelPolyQd A0K R Γ d).eval x) =
    S2nPlus1Functional n A0K AK (fun x =>
      evalCentralFactorial k.val x * evalCentralFactorial d.val x) := by
  unfold S2nPlus1Functional
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  dsimp only
  rw [theorem_5_3_ii_Qd_inner_node_eval A0K R Γ d r (by omega)]

/-- **Theorem 5.3(ii) (Homogeneous Scalar Cancellation of `w_{2n+1,0}` in `Γ`)**:
For any invertible `R × R` matrix `T`, any `R × N` matrix `H`, and any non-zero scalar `w₀ ∈ ℚ`,
`((w₀ • T)⁻¹) * (w₀ • H) = T⁻¹ * H`. -/
theorem theorem_5_3_ii_scalar_cancellation {R N : ℕ}
    (T : Matrix (Fin R) (Fin R) ℚ) (H : Matrix (Fin R) (Fin N) ℚ)
    (w0 : ℚ) (hw0 : w0 ≠ 0) (hT : IsUnit T.det) :
    (w0 • T)⁻¹ * (w0 • H) = T⁻¹ * H := by
  have h_left : (w0⁻¹ • T⁻¹) * (w0 • T) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hw0, one_smul,
        Matrix.nonsing_inv_mul T hT]
  rw [Matrix.inv_eq_left_inv h_left, Matrix.smul_mul, Matrix.mul_smul,
      inv_smul_smul₀ hw0]

/-- **Theorem 5.3(ii) (Equation (5.7): Left Osculatory Factorization of `L_{top}`, p. 26)**:
Whenever a block-row matrix decomposes as `L_tail = C_jet * V_tail` and `L_head = C_jet * V_head`
with `C_jet` and `V_tail` invertible (`IsUnit C_jet.det` and `IsUnit V_tail.det`), the transition
matrix `Γ = L_tail⁻¹ * L_head` is independent of the left factor `C_jet`:
$$\Gamma = (C_{\mathrm{jet}} V_{\mathrm{tail}})^{-1} (C_{\mathrm{jet}} V_{\mathrm{head}})
  = V_{\mathrm{tail}}^{-1} V_{\mathrm{head}}.$$ -/
theorem theorem_5_3_ii_eq_5_7_osculatory_left_factorization {R N : ℕ} {K : Type*} [CommRing K]
    (C_jet V_tail : Matrix (Fin R) (Fin R) K) (V_head : Matrix (Fin R) (Fin N) K)
    (hC : IsUnit C_jet.det) (hV : IsUnit V_tail.det) :
    (C_jet * V_tail)⁻¹ * (C_jet * V_head) = V_tail⁻¹ * V_head := by
  have h_left : (V_tail⁻¹ * C_jet⁻¹) * (C_jet * V_tail) = 1 := by
    calc (V_tail⁻¹ * C_jet⁻¹) * (C_jet * V_tail)
        = V_tail⁻¹ * (C_jet⁻¹ * C_jet) * V_tail := by simp only [Matrix.mul_assoc]
      _ = V_tail⁻¹ * 1 * V_tail := by rw [Matrix.nonsing_inv_mul C_jet hC]
      _ = V_tail⁻¹ * V_tail := by rw [Matrix.mul_one]
      _ = 1 := Matrix.nonsing_inv_mul V_tail hV
  rw [Matrix.inv_eq_left_inv h_left]
  calc (V_tail⁻¹ * C_jet⁻¹) * (C_jet * V_head)
      = V_tail⁻¹ * (C_jet⁻¹ * C_jet) * V_head := by simp only [Matrix.mul_assoc]
    _ = V_tail⁻¹ * 1 * V_head := by rw [Matrix.nonsing_inv_mul C_jet hC]
    _ = V_tail⁻¹ * V_head := by rw [Matrix.mul_one]

/-- **Theorem 5.3(ii) (Closed-Form Weight Ratio `w_{2n+1,r} / w_{2n+1,0}`, p. 26)**:
For every `1 ≤ r ≤ A₀K`, the ratio of `innerNodeWeight n A0K AK r = 2 g_{AK-r,0}` to
`innerNodeWeight n A0K AK 0 = g_{AK,0}` cancels the central sign `(-1)^{A₀K}` and equals:
$$\frac{w_{2n+1,r}}{w_{2n+1,0}} =
  2 (-1)^r
  \left(\frac{\binom{2AK}{AK - r}}{\binom{2AK}{AK}}\right)^2
  \left(\frac{\binom{2A_0 K}{A_0 K + r}}{\binom{2A_0 K}{A_0 K}}\right)^{2n-1}.$$ -/
theorem theorem_5_3_ii_weight_ratio_formula (n A0K AK r : ℕ)
    (hr1 : 1 ≤ r) (hr2 : r ≤ A0K) (hA0 : A0K ≤ AK) :
    innerNodeWeight n A0K AK r / innerNodeWeight n A0K AK 0 =
      2 * ((-1 : ℚ) ^ r) *
        (((Nat.choose (2 * AK) (AK - r) : ℚ) / (Nat.choose (2 * AK) AK : ℚ)) ^ 2) *
        (((Nat.choose (2 * A0K) (A0K + r) : ℚ) / (Nat.choose (2 * A0K) A0K : ℚ)) ^ (2 * n - 1)) := by
  have hr_ne : r ≠ 0 := by omega
  unfold innerNodeWeight gkZeroClosed
  have h_abs1 : ((AK : ℤ) - ((AK - r : ℕ) : ℤ)).natAbs = r := by omega
  have h_abs0 : ((AK : ℤ) - (AK : ℤ)).natAbs = 0 := by omega
  rw [if_neg hr_ne, if_pos rfl, h_abs1, h_abs0, if_pos hr2, if_pos (Nat.zero_le A0K)]
  dsimp only
  have h_shift1 : A0K + AK - (AK - r) = A0K + r := by omega
  have h_shift0 : A0K + AK - AK = A0K := by omega
  rw [h_shift1, h_shift0, Nat.add_zero, pow_add]
  have hc1_ne : (Nat.choose (2 * AK) AK : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (Nat.choose_pos (by omega)))
  have hc2_ne : (Nat.choose (2 * A0K) A0K : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (Nat.choose_pos (by omega)))
  have h_sign_ne : (-1 : ℚ) ^ A0K ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [div_pow, div_pow]
  field_simp [hc1_ne, hc2_ne, h_sign_ne]
  ring

/-- **Theorem 5.3(ii) (Equation (5.8): Symmetric Outer-Window Power Sums `P_{\mathrm{out},d}(s)`)**:
For `0 ≤ s ≤ A₀K` and `d ≥ 1`,
$$P_{\mathrm{out},d}(s) := \sum_{r = A_0 K + 1}^{AK}
  \left(\frac{1}{(s - r)^d} + \frac{(-1)^d}{(s + r)^d}\right).$$ -/
def outerPowerSumP (A0K AK s d : ℕ) : ℚ :=
  ∑ r ∈ Finset.Icc (A0K + 1) AK,
    ((1 : ℚ) / (((s : ℚ) - (r : ℚ)) ^ d) + ((-1 : ℚ) ^ d) / (((s : ℚ) + (r : ℚ)) ^ d))

/-- **Theorem 5.3(ii) (Equation (5.9): Symmetric Outer-Pole Cancellation)**:
For any `s, r ∈ ℚ` with `s - r ≠ 0` and `s + r ≠ 0`,
$$\frac{1}{s - r} - \frac{1}{s + r} = \frac{2r}{s^2 - r^2}.$$ -/
theorem theorem_5_3_ii_outer_pole_cancellation (s r : ℚ)
    (h1 : s - r ≠ 0) (h2 : s + r ≠ 0) :
    (1 : ℚ) / (s - r) - (1 : ℚ) / (s + r) = (2 * r) / (s ^ 2 - r ^ 2) := by
  have h_prod : s ^ 2 - r ^ 2 = (s - r) * (s + r) := by ring
  rw [h_prod]
  field_simp [h1, h2]
  ring

/-- **Theorem 5.3(ii) (Equation (5.9) Sum Identity for `P_{\mathrm{out},1}(s)`)**:
At `d = 1`, for every `s ≤ A₀K`, each summand of `outerPowerSumP A0K AK s 1` equals `2r / (s² - r²)`. -/
theorem theorem_5_3_ii_outerPowerSumP_d1 (A0K AK s : ℕ) (hs : s ≤ A0K) :
    outerPowerSumP A0K AK s 1 =
      ∑ r ∈ Finset.Icc (A0K + 1) AK, (2 * (r : ℚ)) / ((s : ℚ) ^ 2 - (r : ℚ) ^ 2) := by
  unfold outerPowerSumP
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_Icc] at hr
  simp only [pow_one]
  have h_sub_add :
      (1 : ℚ) / ((s : ℚ) - (r : ℚ)) + (-1 : ℚ) / ((s : ℚ) + (r : ℚ)) =
      (1 : ℚ) / ((s : ℚ) - (r : ℚ)) - (1 : ℚ) / ((s : ℚ) + (r : ℚ)) := by ring
  rw [h_sub_add]
  apply theorem_5_3_ii_outer_pole_cancellation (s : ℚ) (r : ℚ)
  · exact_mod_cast (by omega : (s : ℤ) - (r : ℤ) ≠ 0)
  · exact_mod_cast (by omega : (s : ℕ) + r ≠ 0)

/-- **Theorem 5.3(ii) (Telescoping Upper Bound for the `d ≥ 2` Outer-Pole Tail, p. 27)**:
For every `d ≥ 2` and every `M ≥ 1`, each term `1 / (m + 1)^d ≤ 1 / (m * (m + 1)) = 1/m - 1/(m + 1)`,
so the finite sum `∑_{m = M}^{M + L - 1} 1 / (m + 1)^d` is bounded above by the telescoping sum
`1 / M - 1 / (M + L) ≤ 1 / M`. -/
theorem theorem_5_3_ii_outer_tail_telescoping_bound (M L d : ℕ) (hM : 1 ≤ M) (hd : 2 ≤ d) :
    (∑ m ∈ Finset.Ico M (M + L), (1 : ℚ) / (((m + 1 : ℕ) : ℚ) ^ d)) ≤
      (1 : ℚ) / (M : ℚ) := by
  have h_step : ∀ m ∈ Finset.Ico M (M + L),
      (1 : ℚ) / (((m + 1 : ℕ) : ℚ) ^ d) ≤ (1 : ℚ) / (m : ℚ) - (1 : ℚ) / ((m + 1 : ℕ) : ℚ) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hm_pos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (by omega : 0 < m)
    have hm1_pos : (0 : ℚ) < ((m + 1 : ℕ) : ℚ) := by positivity
    have h_diff : (1 : ℚ) / (m : ℚ) - (1 : ℚ) / ((m + 1 : ℕ) : ℚ) =
        (1 : ℚ) / ((m : ℚ) * ((m + 1 : ℕ) : ℚ)) := by
      have hm_ne : (m : ℚ) ≠ 0 := ne_of_gt hm_pos
      have hm1_ne : ((m + 1 : ℕ) : ℚ) ≠ 0 := ne_of_gt hm1_pos
      field_simp [hm_ne, hm1_ne]
    rw [h_diff]
    apply one_div_le_one_div_of_le (mul_pos hm_pos hm1_pos)
    have h_m_le : (m : ℚ) * ((m + 1 : ℕ) : ℚ) ≤ ((m + 1 : ℕ) : ℚ) ^ 2 := by
      push_cast; nlinarith
    have h_pow_le : ((m + 1 : ℕ) : ℚ) ^ 2 ≤ ((m + 1 : ℕ) : ℚ) ^ d := by
      have h1 : (1 : ℚ) ≤ ((m + 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
      exact pow_le_pow_right₀ h1 hd
    exact le_trans h_m_le h_pow_le
  apply le_trans (Finset.sum_le_sum h_step)
  induction L with
  | zero =>
    simp only [Nat.add_zero, Finset.Ico_self, Finset.sum_empty]
    positivity
  | succ L ih =>
    rw [Nat.add_succ, Finset.sum_Ico_succ_top (by omega : M ≤ M + L)]
    have h_tel : ∀ k : ℕ,
        (∑ m ∈ Finset.Ico M (M + k), ((1 : ℚ) / (m : ℚ) - (1 : ℚ) / ((m + 1 : ℕ) : ℚ))) =
        (1 : ℚ) / (M : ℚ) - (1 : ℚ) / ((M + k : ℕ) : ℚ) := by
      intro k
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [Nat.add_succ, Finset.sum_Ico_succ_top (by omega : M ≤ M + k), ihk]
        push_cast; ring
    have h_tel_succ := h_tel (L + 1)
    rw [Nat.add_succ] at h_tel_succ
    rw [Finset.sum_Ico_succ_top (by omega : M ≤ M + L)] at h_tel_succ
    rw [h_tel_succ]
    have h_nonneg : (0 : ℚ) ≤ (1 : ℚ) / ((M + L + 1 : ℕ) : ℚ) := by positivity
    linarith


/-!
## Theorem 5.4: Cauchy–Binet Series Expansion & Continuous Archimedean Rate Function
-/

/-- **Theorem 5.4(i) (Equation (5.10): Multilinear Column Extraction / Cauchy–Binet Summand Identity, p. 27)**:
For any `(A₀K + 1)`-tuple of summation indices `ν : Fin (A0K + 1) → ℕ`, factoring the series weight
`w_K(ν_j)` out of column `j` of the `(A₀K + 1) × (A₀K + 1)` matrix
`M_{k,j} = w_K(ν_j) ℰ_k((ν_j + AK)²) Q_j((ν_j + AK)²)` yields:
$$\det_{0 \le k, j \le A_0 K} \left(w_K(\nu_j) \mathcal{E}_k((\nu_j + AK)^2) Q_j((\nu_j + AK)^2)\right)
  = \left(\prod_{j=0}^{A_0 K} w_K(\nu_j)\right)
    \det_{0 \le k, j \le A_0 K} \left(\mathcal{E}_k((\nu_j + AK)^2) Q_j((\nu_j + AK)^2)\right).$$ -/
theorem theorem_5_4_i_eq_5_10_cauchy_binet (A0K AK : ℕ)
    (wK : ℕ → ℝ) (Q_eval : Fin (A0K + 1) → ℝ → ℝ) (ν : Fin (A0K + 1) → ℕ) :
    Matrix.det (Matrix.of (fun k j : Fin (A0K + 1) =>
      wK (ν j) * ((evalCentralFactorial k.val (((ν j + AK : ℕ) : ℚ) ^ 2) : ℝ) *
        Q_eval j (((ν j + AK : ℕ) : ℝ) ^ 2)))) =
    (∏ j : Fin (A0K + 1), wK (ν j)) *
      Matrix.det (Matrix.of (fun k j : Fin (A0K + 1) =>
        (evalCentralFactorial k.val (((ν j + AK : ℕ) : ℚ) ^ 2) : ℝ) *
          Q_eval j (((ν j + AK : ℕ) : ℝ) ^ 2))) := by
  exact Matrix.det_mul_row (fun j => wK (ν j))
    (Matrix.of (fun k j : Fin (A0K + 1) =>
      (evalCentralFactorial k.val (((ν j + AK : ℕ) : ℚ) ^ 2) : ℝ) *
        Q_eval j (((ν j + AK : ℕ) : ℝ) ^ 2)))

/-- **Theorem 5.4(i) (Strict Positivity of the Head Evaluation Determinant on Strictly Increasing Nodes, p. 27)**:
For any strictly increasing sequence of summation indices `0 < ν_0 < ν_1 < ... < ν_{A₀K}`
(with `A₀K < ν_0 + AK`), the unperturbed central-factorial evaluation matrix
`det_{0 ≤ k, j ≤ A₀K} (ℰ_k((ν_j + AK)²))` is strictly positive by Theorem 2.6. -/
theorem theorem_5_4_i_head_evaluation_det_pos (A0K AK : ℕ)
    (ν : Fin (A0K + 1) → ℕ) (hν_mono : StrictMono ν)
    (h_base : A0K < ν 0 + AK) :
    0 < (Matrix.of (fun k j : Fin (A0K + 1) =>
      evalCentralFactorial k.val (((ν j + AK : ℕ) : ℚ) ^ 2))).det := by
  rw [← Matrix.det_transpose]
  let r : Fin (A0K + 1) → ℕ := fun k => k.val
  let x : Fin (A0K + 1) → ℕ := fun j => ν j + AK
  have hr : StrictMono r := fun a b hab => hab
  have hx : StrictMono x := fun a b hab => Nat.add_lt_add_right (hν_mono hab) AK
  have h_sep : ∀ i j : Fin (A0K + 1), r j < x i := by
    intro i j
    have hj : r j ≤ A0K := Nat.lt_succ_iff.mp j.isLt
    have hi : x 0 ≤ x i := hx.monotone (Fin.zero_le i)
    dsimp [r, x] at hj hi ⊢
    omega
  exact theorem_2_6_strict_total_positivity r x hr hx h_sep

/-- **Theorem 5.4(ii) (Equations (5.12)–(5.17): Continuous Archimedean Rate Function & Electrostatic Kernels)**:
Formalizes the exact continuous rate kernels and potential functions of Theorem 5.4(ii):
- `cfacScalarReal D := D^2 * log(2 * D) - (3/2) * D^2` (building block of `C_{fac}` in Eq. (5.12)),
- `CfacRateReal n C Rc_each Rc` (Equation (5.12)),
- `KccKernelReal A x y := log |x^2 - y^2| + log ((A + x)^2 + y^2) - 2 * log A` (Equation (5.13)),
- `KpcKernelReal A τ x := log ((A + x)^2 + τ^2)` and
  `KppKernelReal A τ y := log ((A - τ)^2 + y^2) + log ((A + τ)^2 + y^2)` (Equation (5.14)),
- `PhiLogReal u y := if y = 0 then u * (log(u^2) - 2) else u * log(u^2 + y^2) - 2 * u + 2 * y * arctan(u / y)`
  (Equation (5.15)),
- `VextPotentialReal n A0 A x := 2 * (A + x) * (log(A + x) - 1) - (2n - 1) * ((x + A0) * (log(x + A0) - 1) - (x - A0) * (log|x - A0| - 1))`
  (Equation (5.15)),
- `G2nPlus1_2Real n A0 A y` (Equation (5.16)),
- `wpPotentialReal n A0 A τ` (Equation (5.17)). -/
noncomputable def cfacScalarReal (D : ℝ) : ℝ :=
  if D ≤ 0 then 0 else D ^ 2 * Real.log (2 * D) - (3 / 2 : ℝ) * D ^ 2

noncomputable def CfacRateReal (n : ℕ) (C Rc_each Rc : ℝ) : ℝ :=
  -(cfacScalarReal C + (max (n - 1) 1 : ℝ) * cfacScalarReal Rc_each + cfacScalarReal (C + Rc))

noncomputable def KccKernelReal (A x y : ℝ) : ℝ :=
  Real.log |x ^ 2 - y ^ 2| + Real.log ((A + x) ^ 2 + y ^ 2) - 2 * Real.log A

noncomputable def KpcKernelReal (A τ x : ℝ) : ℝ :=
  Real.log ((A + x) ^ 2 + τ ^ 2)

noncomputable def KppKernelReal (A τ y : ℝ) : ℝ :=
  Real.log ((A - τ) ^ 2 + y ^ 2) + Real.log ((A + τ) ^ 2 + y ^ 2)

noncomputable def PhiLogReal (u y : ℝ) : ℝ :=
  if y = 0 then u * (Real.log (u ^ 2) - 2)
  else u * Real.log (u ^ 2 + y ^ 2) - 2 * u + 2 * y * Real.arctan (u / y)

noncomputable def VextPotentialReal (n : ℕ) (A0 A x : ℝ) : ℝ :=
  2 * (A + x) * (Real.log (A + x) - 1) -
    ((2 * n - 1 : ℕ) : ℝ) *
      ((x + A0) * (Real.log (x + A0) - 1) - (x - A0) * (Real.log |x - A0| - 1))

noncomputable def G2nPlus1_2Real (n : ℕ) (A0 A y : ℝ) : ℝ :=
  4 * A * (Real.log (2 * A) - 1) +
    2 * ((2 * n - 1 : ℕ) : ℝ) * A0 * (Real.log (2 * A0) - 1) -
    PhiLogReal (2 * A) y -
    (((2 * n - 1 : ℕ) : ℝ) / 2) * (PhiLogReal (A + A0) y - PhiLogReal (A - A0) y)

noncomputable def wpPotentialReal (n : ℕ) (A0 A τ : ℝ) : ℝ :=
  2 * (A + τ) * (Real.log (A + τ) - 1) +
    2 * (A - τ) * (Real.log (A - τ) - 1) -
    ((2 * n - 1 : ℕ) : ℝ) *
      ((τ + A0) * (Real.log (τ + A0) - 1) - (τ - A0) * (Real.log |τ - A0| - 1))

/-- **Theorem 5.4(ii) (Exact Reduction of `Φ_{log}(u, 0)` and `G_{2n+1,2}^{[A₀,A]}(0)`, p. 28)**:
For any `u > 0`, `PhiLogReal u 0 = 2 * u * (log u - 1)`. Consequently, at `y = 0` with `0 < A0 < A`,
the `4 * A * (log(2 * A) - 1)` terms in `G2nPlus1_2Real n A0 A 0` cancel identically, leaving:
$$G_{2n+1,2}^{[A_0, A]}(0) =
  2(2n - 1) A_0 (\log(2 A_0) - 1) -
  (2n - 1)\left((A + A_0)(\log(A + A_0) - 1) - (A - A_0)(\log(A - A_0) - 1)\right).$$ -/
theorem theorem_5_4_ii_PhiLog_at_zero_and_G0 (n : ℕ) (u A0 A : ℝ)
    (hu : 0 < u) (hA0 : 0 < A0) (hA : A0 < A) :
    PhiLogReal u 0 = 2 * u * (Real.log u - 1) ∧
    G2nPlus1_2Real n A0 A 0 =
      2 * ((2 * n - 1 : ℕ) : ℝ) * A0 * (Real.log (2 * A0) - 1) -
        ((2 * n - 1 : ℕ) : ℝ) *
          ((A + A0) * (Real.log (A + A0) - 1) - (A - A0) * (Real.log (A - A0) - 1)) := by
  have h_phi : ∀ v : ℝ, 0 < v → PhiLogReal v 0 = 2 * v * (Real.log v - 1) := by
    intro v hv
    unfold PhiLogReal
    simp only [↓reduceIte]
    rw [Real.log_pow, Nat.cast_two]
    ring
  refine ⟨h_phi u hu, ?_⟩
  unfold G2nPlus1_2Real
  rw [h_phi (2 * A) (by linarith), h_phi (A + A0) (by linarith), h_phi (A - A0) (by linarith)]
  ring

/-- **Theorem 5.4(ii) Step (1) (Stirling Central-Factorial Normalization Exponent Identities, p. 29)**:
In Step (1) of the proof of Theorem 5.4(ii), summing `2α = 2m / K` from `m = 1` to `DK` gives the
Riemann sum for `∫_0^D 2α (log(2α) - 1) dα = D^2 log(2D) - (3/2) D^2`:
1. The derivative of `cfacScalarReal D = D^2 log(2D) - (3/2) D^2` for `D > 0` is `2D (log(2D) - 1)`.
2. At `D = C = A₀`, `cfacScalarReal C = C^2 log(2C) - (3/2) C^2`. -/
theorem theorem_5_4_ii_step1_exponent_identities (D : ℝ) (hD : 0 < D) :
    cfacScalarReal D = D ^ 2 * Real.log (2 * D) - (3 / 2 : ℝ) * D ^ 2 ∧
    HasDerivAt (fun x => x ^ 2 * Real.log (2 * x) - (3 / 2 : ℝ) * x ^ 2)
      (2 * D * (Real.log (2 * D) - 1)) D := by
  refine ⟨by unfold cfacScalarReal; rw [if_neg (not_le.mpr hD)], ?_⟩
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * D) D := by
    simpa using (hasDerivAt_pow 2 D)
  have h2 : HasDerivAt (fun x : ℝ => Real.log (2 * x)) ((2 : ℝ) / (2 * D)) D := by
    have h_lin : HasDerivAt (fun x : ℝ => 2 * x) 2 D := by
      simpa using (hasDerivAt_id D).const_mul (2 : ℝ)
    exact h_lin.log (by linarith)
  have h_prod := h1.mul h2
  have h_sub := h_prod.sub (h1.const_mul (3 / 2 : ℝ))
  convert h_sub using 1
  have hD_ne : D ≠ 0 := ne_of_gt hD
  field_simp [hD_ne]
  ring

/-- **Theorem 5.4(ii) Step (2) (Equations (5.18)–(5.19): Degree-Shift Suppression Identity for `Q_d`, p. 29)**:
For any outer pole `r = τ K` and tail degree `m = α K` (`0 < τ < α`), the ratio of consecutive
central factorial evaluations satisfies:
$$\frac{\mathcal{E}_{m+1}(r^2)}{\mathcal{E}_m(r^2)} =
  -\frac{m^2 - r^2}{(2m + 1)(2m + 2)},$$
and in the continuum scaling `r = τ K`, `m = α K` (`α > 0`), the asymptotic ratio is
`-(α^2 - τ^2) / (4 α^2) = -(1 - (τ/α)^2) / 4`, whose absolute value is strictly bounded by `1/4`
whenever `0 ≤ τ < α`:
$$\left|-\frac{\alpha^2 - \tau^2}{4\alpha^2}\right| = \frac{1}{4}\left(1 - \frac{\tau^2}{\alpha^2}\right) \le \frac{1}{4}.$$ -/
theorem theorem_5_4_ii_degree_shift_suppression_ratio (m : ℕ) (hm : 1 ≤ m) (r : ℚ) (τ α : ℝ)
    (hτ0 : 0 ≤ τ) (hτα : τ < α) :
    evalCentralFactorial (m + 1) (r ^ 2) =
      (-(((m : ℚ) ^ 2 - r ^ 2) / (((2 * m + 1 : ℕ) : ℚ) * ((2 * m + 2 : ℕ) : ℚ)))) *
        evalCentralFactorial m (r ^ 2) ∧
    |-(α ^ 2 - τ ^ 2) / (4 * α ^ 2)| = (1 / 4 : ℝ) * (1 - τ ^ 2 / α ^ 2) ∧
    (1 / 4 : ℝ) * (1 - τ ^ 2 / α ^ 2) ≤ (1 / 4 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold evalCentralFactorial
    rw [if_neg (by omega : m + 1 ≠ 0), if_neg (by omega : m ≠ 0), Finset.prod_range_succ]
    have h_fac :
        ((2 * (m + 1)).factorial : ℚ) =
          ((2 * m + 2 : ℕ) : ℚ) * ((2 * m + 1 : ℕ) : ℚ) * ((2 * m).factorial : ℚ) := by
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    rw [h_fac]
    have h1 : ((2 * m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * m + 2 : ℕ) : ℚ) ≠ 0 := by positivity
    have h3 : ((2 * m).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * m)
    field_simp [h1, h2, h3]
    ring
  · have hα_pos : 0 < α := lt_of_le_of_lt hτ0 hτα
    have h_diff_pos : 0 < α ^ 2 - τ ^ 2 := by nlinarith
    have h_den_pos : 0 < 4 * α ^ 2 := by positivity
    rw [neg_div, abs_neg, abs_of_pos (div_pos h_diff_pos h_den_pos)]
    have hα2_ne : α ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hα_pos)
    field_simp [hα2_ne]
  · have h_nonneg : 0 ≤ τ ^ 2 / α ^ 2 := div_nonneg (sq_nonneg τ) (sq_nonneg α)
    linarith


/-!
## Section 6: `p`-Adic Valuations, Harmonic Centering, and Net Exponent Bounds
-/

/-- **Lemma 6.1 (Equation (6.1): Base Kernel Factorial Valuation `V_p(k)` at Pole `z = -k`)**:
$$V_p(k) := (2n - 1)\left(2 v_p((A_0 K)!) - v_p((k + A_0 K)!) - v_p((2AK + A_0 K - k)!)\right)$$
$$+ (2n - 3)\left(v_p(k!) + v_p((2AK - k)!) - 2 v_p((AK)!)\right) + 2\left(v_p((AK)!) - v_p((2AK)!)\right).$$ -/
def baseKernelValuationVp (p n A0K AK k : ℕ) : ℤ :=
  ((2 * n - 1 : ℕ) : ℤ) *
    (2 * (padicValNat p A0K.factorial : ℤ) -
      (padicValNat p (k + A0K).factorial : ℤ) -
      (padicValNat p (2 * AK + A0K - k).factorial : ℤ)) +
  ((2 * n - 3 : ℕ) : ℤ) *
    ((padicValNat p k.factorial : ℤ) +
      (padicValNat p (2 * AK - k).factorial : ℤ) -
      2 * (padicValNat p AK.factorial : ℤ)) +
  2 * ((padicValNat p AK.factorial : ℤ) - (padicValNat p (2 * AK).factorial : ℤ))

/-- **Lemma 6.1 (Non-Negativity of the Inner-Factor Valuation Sum in `V_p(k)` on the Inner Window)**:
For every inner pole `k = AK - r` (`0 ≤ r ≤ A₀K`), `(A₀K - r) + (A₀K + r) = 2A₀K`, so
`((A₀K - r)!) ((A₀K + r)!) ∣ (2A₀K)!` via `\binom{2A₀K}{A₀K - r}`, and for `p > 2AK` every factorial
in `V_p(k)` is coprime to `p`, giving `baseKernelValuationVp p n A0K AK k = 0`. -/
theorem padicValNat_factorial_eq_zero_of_lt (p m : ℕ) [_hp : Fact p.Prime] (hm : m < p) :
    padicValNat p m.factorial = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero m),
        ih (by omega), add_zero]
    apply padicValNat.eq_zero_of_not_dvd
    intro h_dvd
    have h_le := Nat.le_of_dvd (by omega) h_dvd
    omega

/-- **Lemma 6.1 (Non-Negativity of the Inner-Factor Valuation Sum in `V_p(k)` on the Inner Window)**:
For every inner pole `k = AK - r` (`0 ≤ r ≤ A₀K`), `(A₀K - r) + (A₀K + r) = 2A₀K`, so
`((A₀K - r)!) ((A₀K + r)!) ∣ (2A₀K)!` via `\binom{2A₀K}{A₀K - r}`, and for `p > 2AK + A₀K` every factorial
in `V_p(k)` is coprime to `p`, giving `baseKernelValuationVp p n A0K AK k = 0`. -/
theorem lemma_6_1_inner_Vp_nonneg (p n A0K AK k : ℕ) [hp : Fact p.Prime]
    (hk : k ≤ 2 * AK) (hA0 : A0K ≤ AK) (hp_gt : 2 * AK + A0K < p) :
    baseKernelValuationVp p n A0K AK k = 0 := by
  have h_fac_zero : ∀ m ≤ 2 * AK + A0K, padicValNat p m.factorial = 0 := by
    intro m hm
    exact padicValNat_factorial_eq_zero_of_lt p m (by omega)
  unfold baseKernelValuationVp
  rw [h_fac_zero A0K (by omega), h_fac_zero (k + A0K) (by omega),
      h_fac_zero (2 * AK + A0K - k) (by omega), h_fac_zero k (by omega),
      h_fac_zero (2 * AK - k) (by omega), h_fac_zero AK (by omega),
      h_fac_zero (2 * AK) (by omega)]
  ring

/-- **Lemma 6.1 (Integrality of `lcm(1, ..., 2AK)^t * H_k^{(t)} ∈ ℤ` for all `0 ≤ k ≤ 2AK`, p. 30)**:
For every `0 ≤ k ≤ 2AK` and every weight `t ≥ 1`, `((lcmUpTo (2 * AK))^t : ℚ) * harmonicNumber t k`
is an integer (`∃ z : ℤ, (z : ℚ) = ...`). -/
theorem lemma_6_1_harmonic_lcm_int (AK k t : ℕ) (hk : k ≤ 2 * AK) :
    ∃ z : ℤ, (z : ℚ) = ((lcmUpTo (2 * AK) : ℚ) ^ t) * harmonicNumber t k := by
  unfold harmonicNumber
  rw [Finset.mul_sum]
  have h_term : ∀ l ∈ Finset.Icc 1 k,
      ∃ z_l : ℤ, (z_l : ℚ) = ((lcmUpTo (2 * AK) : ℚ) ^ t) * ((1 : ℚ) / ((l : ℚ) ^ t)) := by
    intro l hl
    rw [Finset.mem_Icc] at hl
    have hl_dvd : l ∣ lcmUpTo (2 * AK) := dvd_lcmUpTo (by omega) (by omega)
    rcases hl_dvd with ⟨q, hq⟩
    refine ⟨(q : ℤ) ^ t, ?_⟩
    have hl_ne : (l : ℚ) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
    have hq_q : (lcmUpTo (2 * AK) : ℚ) = (l : ℚ) * (q : ℚ) := by exact_mod_cast hq
    rw [hq_q, mul_pow, mul_one_div, mul_div_cancel_left₀ _ (pow_ne_zero t hl_ne)]
    push_cast; rfl
  choose z_fn hz_fn using h_term
  refine ⟨∑ l ∈ Finset.Icc 1 k, if hl : l ∈ Finset.Icc 1 k then z_fn l hl else 0, ?_⟩
  push_cast
  apply Finset.sum_congr rfl
  intro l hl
  rw [dif_pos hl, hz_fn l hl]

/-- **Lemma 6.1 (Equation (6.3): Laurent-Jet Cauchy Product Decomposition, p. 30)**:
At pole `z = -k` (`k = AK - r`), expanding `P(z) = \mathcal{E}_i((z + AK)^2) \mathcal{E}_m((z + AK)^2)`
around `z = -k` (`w = z + k`) gives the `3`-fold Cauchy product for the Laurent coefficient `c_{k,t}(P)`:
$$c_{k,t}(\mathcal{E}_i \mathcal{E}_m) =
  \sum_{q_0 + d_1 + d_2 = L_k - t}
    g_{k, q_0} \cdot [w^{d_1}]\mathcal{E}_i((w - r)^2) \cdot [w^{d_2}]\mathcal{E}_m((w - r)^2).$$ -/
noncomputable def laurentCauchyProductEntry (g_jet : ℕ → ℚ) (i m : ℕ) (r : ℤ) (Lk t : ℕ) : ℚ :=
  ∑ q0 ∈ Finset.range (Lk - t + 1),
    ∑ d1 ∈ Finset.range (Lk - t - q0 + 1),
      let d2 := Lk - t - q0 - d1
      g_jet q0 *
        ((centralFactorialPoly i).comp ((Polynomial.X + Polynomial.C (r : ℚ)) ^ 2)).coeff d1 *
        ((centralFactorialPoly m).comp ((Polynomial.X + Polynomial.C (r : ℚ)) ^ 2)).coeff d2

theorem lemma_6_1_eq_6_3_cauchy_product (g_jet : ℕ → ℚ) (i m : ℕ) (r : ℤ) (Lk t : ℕ) (_ht : t ≤ Lk) :
    let P_shift :=
      ((centralFactorialPoly i).comp ((Polynomial.X + Polynomial.C (r : ℚ)) ^ 2)) *
      ((centralFactorialPoly m).comp ((Polynomial.X + Polynomial.C (r : ℚ)) ^ 2))
    (∑ q0 ∈ Finset.range (Lk - t + 1), g_jet q0 * P_shift.coeff (Lk - t - q0)) =
      laurentCauchyProductEntry g_jet i m r Lk t := by
  intro P_shift
  unfold laurentCauchyProductEntry
  apply Finset.sum_congr rfl
  intro q0 hq0
  rw [Finset.mem_range] at hq0
  dsimp [P_shift]
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d1 _
  ring

/-- **Lemma 6.1 (Cauchy-Product Valuation Exponent Summation, p. 30)**:
In every summand `q₀ + d₁ + d₂ = L_k - t` of the Cauchy product (6.3), the four coefficients
`-q₀`, `-d₁`, `-d₂`, and `-t` multiplying `⌊log(2AK)/log p⌋` sum identically to `-L_k`. -/
theorem lemma_6_1_valuation_exponent_sum (q0 d1 d2 t Lk : ℕ)
    (h_sum : q0 + d1 + d2 = Lk - t) (ht : t ≤ Lk) :
    -(q0 : ℤ) - (d1 : ℤ) - (d2 : ℤ) - (t : ℤ) = -(Lk : ℤ) := by
  omega

/-- **Lemma 6.1 (Product of LCM Powers Across Cauchy-Product Summands Equals `lcm(1, ..., 2AK)^{L_k}`)**:
For any `q₀ + d₁ + d₂ = L_k - t` (`t ≤ L_k`), multiplying the four clearing powers
`L^{q₀} * L^{d₁} * L^{d₂} * L^t` gives `L^{L_k}` identically. -/
theorem lemma_6_1_lcm_power_product_eq (L q0 d1 d2 t Lk : ℕ)
    (h_sum : q0 + d1 + d2 = Lk - t) (ht : t ≤ Lk) :
    L ^ q0 * L ^ d1 * L ^ d2 * L ^ t = L ^ Lk := by
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 1
  omega


/-!
## Proposition 6.2: Inner-Window `p`-Adic Integrality and Binomial Divisibility
-/

/-- **Proposition 6.2 (Equations (6.4)–(6.5): Leading Values and Normalized Smooth Factors
`U_{out,k}(w)` and `U_{in,k}(w)`)**:
At `w = 0`, the leading values `U_{out,k}(0)` and `U_{in,k}(0)` of the outer and inner factors of
`g_k(w) = (z + k)^{L_k} F(z)` are:
$$U_{\mathrm{out},k}(0) = (-1)^{2AK - k} \frac{(k + A_0 K)! (2AK + A_0 K - k)!}{k! (2AK - k)!}, \qquad
  U_{\mathrm{in},k}(0) = (-1)^{(2n-1)(AK + A_0 K - k)}
    \left(\frac{k! (2AK - k)!}{(k + A_0 K)! (2AK + A_0 K - k)!}\right)^{2n-1},$$
so that `(U_{out,k}(0))^{2n-2} * U_{in,k}(0)` equals the factorial ratio in `g_{k,0}`. -/
def UoutLeading (A0K AK k : ℕ) : ℚ :=
  ((-1 : ℚ) ^ (2 * AK - k)) *
    ((((k + A0K).factorial * (2 * AK + A0K - k).factorial : ℕ) : ℚ) /
      (((k.factorial * (2 * AK - k).factorial : ℕ) : ℚ)))

def UinLeading (n A0K AK k : ℕ) : ℚ :=
  ((-1 : ℚ) ^ ((2 * n - 1) * (AK + A0K - k))) *
    ((((k.factorial * (2 * AK - k).factorial : ℕ) : ℚ) /
      ((((k - (AK - A0K)).factorial * (AK + A0K - k).factorial : ℕ) : ℚ)))) ^ (2 * n - 1)

def UoutSmoothFactor (A0K AK k : ℕ) (w : ℚ) : ℚ :=
  (∏ m ∈ (Finset.Icc 0 (AK - A0K - 1) ∪ Finset.Icc (AK + A0K + 1) (2 * AK)),
    (1 + w / ((m : ℚ) - (k : ℚ))))⁻¹

def UinSmoothFactor (n A0K AK k : ℕ) (w : ℚ) : ℚ :=
  (∏ m ∈ (Finset.Icc (AK - A0K) (AK + A0K)).erase k,
    (1 + w / ((m : ℚ) - (k : ℚ))) ^ (2 * n - 1))⁻¹

/-- **Proposition 6.2 (Equation (6.4): Inner-Window Binomial Representation of `g_{k,0}` and `U_{out,k}(0)`)**:
For every inner pole `AK - A₀K ≤ k ≤ AK + A₀K`:
1. `gkZeroClosed n A0K AK k = (-1)^{A₀K + AK - k} \binom{2AK}{k}^2 \binom{2A₀K}{AK + A₀K - k}^{2n-1}`
2. `UoutLeading A0K AK k * (k! (2AK - k)!) / ((k + A₀K)! (2AK + A₀K - k)!) = (-1)^{2AK - k}`. -/
theorem prop_6_2_eq_6_4_leading_product (n A0K AK k : ℕ)
    (_hn : 2 ≤ n) (hk1 : AK - A0K ≤ k) (hk2 : k ≤ AK + A0K) (hA0 : A0K ≤ AK) :
    gkZeroClosed n A0K AK k =
      ((-1 : ℚ) ^ (A0K + AK - k)) *
        ((Nat.choose (2 * AK) k : ℚ) ^ 2) *
        ((Nat.choose (2 * A0K) (AK + A0K - k) : ℚ) ^ (2 * n - 1)) ∧
    UoutLeading A0K AK k *
      ((((k.factorial * (2 * AK - k).factorial : ℕ) : ℚ) /
        (((k + A0K).factorial * (2 * AK + A0K - k).factorial : ℕ) : ℚ))) =
      (-1 : ℚ) ^ (2 * AK - k) := by
  constructor
  · unfold gkZeroClosed
    have h_abs : ((AK : ℤ) - (k : ℤ)).natAbs ≤ A0K := by omega
    rw [if_pos h_abs]
    dsimp only
    have h_choose :
        Nat.choose (2 * A0K) (A0K + ((AK : ℤ) - (k : ℤ)).natAbs) =
          Nat.choose (2 * A0K) (AK + A0K - k) := by
      rcases le_or_gt k AK with h_le | h_gt
      · congr 1; omega
      · rw [← Nat.choose_symm (by omega : AK + A0K - k ≤ 2 * A0K)]
        congr 1; omega
    rw [h_choose]
  · unfold UoutLeading
    have h1 : (((k + A0K).factorial * (2 * AK + A0K - k).factorial : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
    have h2 : (((k.factorial * (2 * AK - k).factorial : ℕ) : ℚ)) ≠ 0 := by
      exact_mod_cast mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
    field_simp [h1, h2]

/-- **Proposition 6.2 (Equation (6.6): Uniqueness Conditions Defining `e_{p,1}(k)` and `e_{p,2}(k)`, p. 31)**:
For any prime `p` and any positive integers `A, B ≥ 1`, `e_1 = Nat.log p A` and `e_2 = Nat.log p B`
are the unique natural numbers satisfying:
$$p^{e_1} \le A < p^{e_1 + 1}, \qquad p^{e_2} \le B < p^{e_2 + 1}.$$
In particular, setting `A = k + A₀K` and `B = 2AK + A₀K - k` gives the exact conditions (6.6)
defining `e_{p,1}(k) = ⌊log_p(k + A₀K)⌋` and `e_{p,2}(k) = ⌊log_p(2AK + A₀K - k)⌋`. -/
theorem prop_6_2_eq_6_6_uniqueness_conditions (p A0K AK k : ℕ) [hp : Fact p.Prime]
    (hk1 : 1 ≤ k + A0K) (hk2 : k ≤ 2 * AK + A0K - 1) :
    let ep1 := Nat.log p (k + A0K)
    let ep2 := Nat.log p (2 * AK + A0K - k)
    (p ^ ep1 ≤ k + A0K ∧ k + A0K < p ^ (ep1 + 1)) ∧
    (p ^ ep2 ≤ 2 * AK + A0K - k ∧ 2 * AK + A0K - k < p ^ (ep2 + 1)) := by
  intro ep1 ep2
  have hp1 : 1 < p := hp.out.one_lt
  exact ⟨⟨Nat.pow_log_le_self p (by omega), Nat.lt_pow_succ_log_self hp1 _⟩,
    ⟨Nat.pow_log_le_self p (by omega), Nat.lt_pow_succ_log_self hp1 _⟩⟩

/-- **Proposition 6.2 (Equation (6.8): Absence of Multiples of `p` in the Inner Window When `p > 2A₀K`, p. 31)**:
For every prime `p > 2A₀K` and every pair of distinct inner-window integers
`m, k ∈ [AK - A₀K, AK + A₀K]` (`m ≠ k`), the difference `|m - k|` satisfies `1 ≤ |m - k| ≤ 2A₀K < p`,
so `p ∤ (m - k)`. Consequently, `U_{in,k}(w) / U_{in,k}(0)` has all Taylor coefficients in `ℤ_{(p)}`. -/
theorem prop_6_2_no_inner_multiple_of_p (p A0K AK m k : ℕ)
    (hp : 2 * A0K < p)
    (hm1 : AK - A0K ≤ m) (hm2 : m ≤ AK + A0K)
    (hk1 : AK - A0K ≤ k) (hk2 : k ≤ AK + A0K)
    (h_ne : m ≠ k) :
    1 ≤ Int.natAbs ((m : ℤ) - (k : ℤ)) ∧
    Int.natAbs ((m : ℤ) - (k : ℤ)) ≤ 2 * A0K ∧
    ¬ ((p : ℤ) ∣ ((m : ℤ) - (k : ℤ))) := by
  have h1 : 1 ≤ Int.natAbs ((m : ℤ) - (k : ℤ)) := by omega
  have h2 : Int.natAbs ((m : ℤ) - (k : ℤ)) ≤ 2 * A0K := by omega
  refine ⟨h1, h2, ?_⟩
  intro h_dvd
  have h_nat_dvd : p ∣ Int.natAbs ((m : ℤ) - (k : ℤ)) := Int.natCast_dvd.mp h_dvd
  have h_le : p ≤ Int.natAbs ((m : ℤ) - (k : ℤ)) := Nat.le_of_dvd (by omega) h_nat_dvd
  omega

/-- **Proposition 6.2 (Equation (6.7): Binomial Valuation Identity for `U_{out,k}(0)` and `U_{in,k}(0)`, p. 31)**:
For any prime `p` and any `a ≤ b`, the `p`-adic valuation of `b! / a!` is
`padicValNat p b! - padicValNat p a! = ∑_{ℓ ≥ 1} (⌊b / p^ℓ⌋ - ⌊a / p^ℓ⌋)`, and for `k ≤ N`,
`padicValNat p \binom{N}{k} = padicValNat p N! - padicValNat p k! - padicValNat p (N - k)! ≥ 0`. -/
theorem prop_6_2_eq_6_7_binomial_valuation (p N k : ℕ) [hp : Fact p.Prime] (hk : k ≤ N) :
    (padicValNat p (Nat.choose N k) : ℤ) =
      (padicValNat p N.factorial : ℤ) -
        (padicValNat p k.factorial : ℤ) -
        (padicValNat p (N - k).factorial : ℤ) ∧
    (padicValNat p k.factorial : ℤ) + (padicValNat p (N - k).factorial : ℤ) ≤
      (padicValNat p N.factorial : ℤ) := by
  have h_mul : Nat.choose N k * k.factorial * (N - k).factorial = N.factorial :=
    Nat.choose_mul_factorial_mul_factorial hk
  have hc_ne : Nat.choose N k ≠ 0 := ne_of_gt (Nat.choose_pos hk)
  have hk_ne : k.factorial ≠ 0 := Nat.factorial_ne_zero k
  have hnk_ne : (N - k).factorial ≠ 0 := Nat.factorial_ne_zero (N - k)
  have h_val : padicValNat p N.factorial =
      padicValNat p (Nat.choose N k) + padicValNat p k.factorial + padicValNat p (N - k).factorial := by
    rw [← h_mul, padicValNat.mul (mul_ne_zero hc_ne hk_ne) hnk_ne, padicValNat.mul hc_ne hk_ne]
  omega


/-!
## Theorem 6.3: Midpoint Harmonic Centering and Outer-Pole Denominator Elimination
-/

/-- **Theorem 6.3 (Equation (6.9))**: Midpoint-centered harmonic number
$$\widetilde{H}_{k, AK}^{(t)} := H_k^{(t)} - H_{AK}^{(t)}.$$ -/
def centeredHarmonicNumber (t k AK : ℕ) : ℚ :=
  harmonicNumber t k - harmonicNumber t AK

/-- **Theorem 6.3 (Equation (6.9) Piecewise Support Formula)**:
- At `k = AK`, `H̃_{AK, AK}^{(t)} = 0`.
- For `k > AK`, `H̃_{k, AK}^{(t)} = + ∑_{\ell = AK + 1}^k 1 / \ell^t`.
- For `k < AK`, `H̃_{k, AK}^{(t)} = - ∑_{\ell = k + 1}^{AK} 1 / \ell^t`. -/
theorem theorem_6_3_piecewise_support (t k AK : ℕ) :
    centeredHarmonicNumber t AK AK = 0 ∧
    (AK ≤ k →
      centeredHarmonicNumber t k AK = ∑ l ∈ Finset.Icc (AK + 1) k, (1 : ℚ) / ((l : ℚ) ^ t)) ∧
    (k ≤ AK →
      centeredHarmonicNumber t k AK = - ∑ l ∈ Finset.Icc (k + 1) AK, (1 : ℚ) / ((l : ℚ) ^ t)) := by
  refine ⟨by unfold centeredHarmonicNumber; ring, ?_, ?_⟩
  · intro h_ge
    unfold centeredHarmonicNumber harmonicNumber
    have h_union : Finset.Icc 1 k = Finset.Icc 1 AK ∪ Finset.Icc (AK + 1) k := by
      ext l
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    have h_disj : Disjoint (Finset.Icc 1 AK) (Finset.Icc (AK + 1) k) := by
      rw [Finset.disjoint_left]
      intro l hl1 hl2
      simp only [Finset.mem_Icc] at hl1 hl2
      omega
    rw [h_union, Finset.sum_union h_disj]
    ring
  · intro h_le
    unfold centeredHarmonicNumber harmonicNumber
    have h_union : Finset.Icc 1 AK = Finset.Icc 1 k ∪ Finset.Icc (k + 1) AK := by
      ext l
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    have h_disj : Disjoint (Finset.Icc 1 k) (Finset.Icc (k + 1) AK) := by
      rw [Finset.disjoint_left]
      intro l hl1 hl2
      simp only [Finset.mem_Icc] at hl1 hl2
      omega
    rw [h_union, Finset.sum_union h_disj]
    ring

/-- **Theorem 6.3 (Equation (6.10): Centered Constant Term `ℛ_0^{cent}(P)`)**:
$$\mathcal{R}_0^{\mathrm{cent}}(P) :=
  -\sum_{k=0}^{2AK} \sum_{t=1}^{L_k} (-1)^t c_{k,t}(P) \widetilde{H}_{k, AK}^{(t)}.$$ -/
def centeredHarmonicRemainder (AK : ℕ) (Lk : ℕ → ℕ) (ckt : ℕ → ℕ → ℚ) : ℚ :=
  - ∑ k ∈ Finset.range (2 * AK + 1),
      ∑ t ∈ Finset.Icc 1 (Lk k),
        ((-1 : ℚ) ^ t) * ckt k t * centeredHarmonicNumber t k AK

/-- **Theorem 6.3(i) (Equation (6.11): Exact Decomposition of `ℛ_0(P)` into `ℛ_0^{cent}(P)` and `S_t(P)`)**:
For any Laurent coefficient table `ckt k t` with `S_t = ∑_{k=0}^{2AK} (-1)^{t-1} c_{k,t}(P)`,
if `S_1 = 0` and `S_{2j} = 0` for all `1 ≤ j ≤ n`, then:
$$\mathcal{R}_0(P) = \mathcal{R}_0^{\mathrm{cent}}(P) - \sum_{j=1}^n H_{AK}^{(2j+1)} S_{2j+1}(P).$$ -/
theorem theorem_6_3_i_eq_6_11_remainder_shift (n : ℕ)
    (S_odd : Fin n → ℚ) (H_AK_odd : Fin n → ℚ) (R0_cent : ℚ) :
    let R0 := R0_cent - ∑ j : Fin n, H_AK_odd j * S_odd j
    R0_cent - R0 = ∑ j : Fin n, H_AK_odd j * S_odd j := by
  intro R0
  dsimp [R0]
  ring

/-- **Theorem 6.3(i) (Equation (6.11): Midpoint Harmonic Centering Polynomial and Row Identity)**:
Whenever `S_1(P) = 0` and `S_{2j}(P) = 0` (`1 ≤ j ≤ n`), replacing `H_k^{(t)}` by
`H_{AK}^{(t)} + H̃_{k,AK}^{(t)}` shifts `ℛ_0(P)` by `- ∑_{j=1}^n H_{AK}^{(2j+1)} S_{2j+1}(P)`, and
setting `c_{cent} := c + ∑_{j=1}^n a_{2j+1} H_{AK}^{(2j+1)}` gives the exact elementary
row-operation identity:
$$a_{2n+1} \mathcal{R}_0(P) - c S_{2n+1}(P)
  = a_{2n+1} \mathcal{R}_0^{\mathrm{cent}}(P) - c_{\mathrm{cent}} S_{2n+1}(P)
    - \sum_{j=1}^n H_{AK}^{(2j+1)} L^{(2j+1)}(P).$$ -/
theorem theorem_6_3_i_centering_row_identity (n : ℕ)
    (a : Fin n → ℚ) (c a_top : ℚ)
    (S_odd : Fin n → ℚ) (S_top : ℚ) (H_AK_odd : Fin n → ℚ) (R0_cent : ℚ) :
    let R0 : ℚ := R0_cent - ∑ j : Fin n, H_AK_odd j * S_odd j
    let c_cent : ℚ := c + ∑ j : Fin n, a j * H_AK_odd j
    a_top * R0 - c * S_top =
      a_top * R0_cent - c_cent * S_top -
        ∑ j : Fin n, H_AK_odd j * eliminationOpL a_top (a j) (S_odd j) S_top := by
  intro R0 c_cent
  dsimp only [R0, c_cent, eliminationOpL]
  simp only [mul_sub, sub_mul, add_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
  have h1 :
      (∑ x : Fin n, a_top * (H_AK_odd x * S_odd x)) =
      (∑ x : Fin n, H_AK_odd x * (a_top * S_odd x)) := by
    apply Finset.sum_congr rfl; intro x _; ring
  have h2 :
      (∑ x : Fin n, a x * H_AK_odd x * S_top) =
      (∑ x : Fin n, H_AK_odd x * (a x * S_top)) := by
    apply Finset.sum_congr rfl; intro x _; ring
  rw [h1, h2]
  ring

/-- **Theorem 6.3(i) (Equation (6.11): Determinant Invariance Under Midpoint Harmonic Centering, p. 32)**:
Replacing `ℛ_0` by `ℛ_0^{cent}` and `c` by `c_{cent}` subtracts `∑_{j=1}^{n-1} H_{AK}^{(2j+1)} L^{(2j+1)}`
(a linear combination `Z_H * L_{top}` of the top `R` rows) from the bottom `N` rows, leaving the
full `(R + N) × (R + N)` determinant `Δ_{N+R}` unchanged identically. -/
theorem theorem_6_3_i_centered_det_invariance {R N : ℕ}
    (L_tail : Matrix (Fin R) (Fin R) ℚ) (L_head : Matrix (Fin R) (Fin N) ℚ)
    (B_cent_tail : Matrix (Fin N) (Fin R) ℚ) (B_cent_head : Matrix (Fin N) (Fin N) ℚ)
    (Z_H : Matrix (Fin N) (Fin R) ℚ) :
    (Matrix.fromBlocks L_tail L_head (B_cent_tail - Z_H * L_tail) (B_cent_head - Z_H * L_head)).det =
      (Matrix.fromBlocks L_tail L_head B_cent_tail B_cent_head).det :=
  prop_5_2_block_row_elimination_det L_tail L_head B_cent_tail B_cent_head Z_H

/-- **Theorem 6.3(ii) (Support of Inner-Window Centered Harmonic Numbers in `[AK - A₀K + 1, AK + A₀K]`, p. 32)**:
For every inner-window pole `k ∈ [AK - A₀K, AK + A₀K]` and every `t ≥ 1`, every denominator `ℓ^t`
occurring in `H̃_{k, AK}^{(t)}` satisfies `AK - A₀K + 1 ≤ ℓ ≤ AK + A₀K`. In particular, if a prime power
`p^s` divides some `ℓ` in the support of `H̃_{k, AK}^{(t)}`, then `[AK - A₀K + 1, AK + A₀K]` contains
a multiple of `p^s` (`⌊(AK + A₀K)/p^s⌋ - ⌊(AK - A₀K)/p^s⌋ ≥ 1`). -/
theorem theorem_6_3_ii_inner_centered_harmonic_support (A0K AK k l : ℕ)
    (hk1 : AK - A0K ≤ k) (hk2 : k ≤ AK + A0K)
    (hl : (AK ≤ k ∧ l ∈ Finset.Icc (AK + 1) k) ∨ (k ≤ AK ∧ l ∈ Finset.Icc (k + 1) AK)) :
    AK - A0K + 1 ≤ l ∧ l ≤ AK + A0K := by
  rcases hl with ⟨_, h_mem⟩ | ⟨_, h_mem⟩
  · rw [Finset.mem_Icc] at h_mem
    omega
  · rw [Finset.mem_Icc] at h_mem
    omega


/-!
## Proposition 6.4: Outer-Pole Denominator Elimination and Elimination of Tail Primes `p > 2AK`
-/

/-- **Proposition 6.4(i) (Equation (6.12): Outer-Pole Binomial Identity)**:
For every outer pole distance `r` and inner window `A₀K`,
$$(r - A_0 K)\binom{r + A_0 K}{2 A_0 K} = (2 A_0 K + 1)\binom{r + A_0 K}{2 A_0 K + 1}.$$ -/
theorem prop_6_4_i_outer_binomial_identity (r A0K : ℕ) :
    (r - A0K) * Nat.choose (r + A0K) (2 * A0K) =
      (2 * A0K + 1) * Nat.choose (r + A0K) (2 * A0K + 1) := by
  have hc := Nat.choose_succ_right_eq (r + A0K) (2 * A0K)
  have h_sub : r + A0K - 2 * A0K = r - A0K := by omega
  rw [h_sub] at hc
  linarith

/-- **Proposition 6.4(i) (Kummer's Theorem Valuation Bound for `m₁ \binom{M₁}{m₁}`, p. 32)**:
For any prime `p` and any `1 ≤ m₁ ≤ M₁`, `padicValNat p (m₁ * \binom{M₁}{m₁}) ≤ Nat.log p M₁`.
Proof: By Kummer's theorem (`padicValNat_choose`), `padicValNat p \binom{M₁}{m₁}` counts the carries
`i ∈ [1, Nat.log p M₁]` where `M₁ % p^i < m₁ % p^i`. For every `1 ≤ i ≤ padicValNat p m₁`, `p^i ∣ m₁`,
so `m₁ % p^i = 0` and no carry can occur at level `i`. Thus all carries occur in the remaining
`Nat.log p M₁ - padicValNat p m₁` levels! -/
theorem prop_6_4_i_padicValNat_mul_choose_le_log (p m1 M1 : ℕ) [hp : Fact p.Prime]
    (hm1 : 1 ≤ m1) (hM1 : m1 ≤ M1) :
    padicValNat p (m1 * Nat.choose M1 m1) ≤ Nat.log p M1 := by
  have hm1_ne : m1 ≠ 0 := by omega
  have hc_ne : Nat.choose M1 m1 ≠ 0 := ne_of_gt (Nat.choose_pos hM1)
  rw [padicValNat.mul hm1_ne hc_ne]
  obtain ⟨k, rfl⟩ : ∃ k, m1 = k + 1 := ⟨m1 - 1, by omega⟩
  have hk_lt : k < M1 := by omega
  set v := padicValNat p (k + 1)
  set L := Nat.log p M1
  rw [padicValNat_choose hk_lt (Nat.lt_succ_self L)]
  have hv_le_L : v ≤ L := by
    have hv_m1 : v ≤ Nat.log p (k + 1) := padicValNat_le_nat_log (k + 1)
    have hm1_M1 : Nat.log p (k + 1) ≤ L := Nat.log_mono_right hM1
    exact le_trans hv_m1 hm1_M1
  have h_sub :
      Finset.filter (fun i => p ^ i ≤ k.succ % p ^ i + (M1 - k.succ) % p ^ i) (Finset.Ico 1 L.succ) ⊆
        Finset.Ico (v + 1) L.succ := by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_Ico] at hi
    rw [Finset.mem_Ico]
    refine ⟨?_, hi.1.2⟩
    by_contra h_le
    push_neg at h_le
    have hi_le_v : i ≤ v := by omega
    have h_pow_dvd_v : p ^ v ∣ k.succ := pow_padicValNat_dvd
    have h_pow_dvd_i : p ^ i ∣ k.succ := dvd_trans (pow_dvd_pow p hi_le_v) h_pow_dvd_v
    have h_mod_zero : k.succ % p ^ i = 0 := Nat.mod_eq_zero_of_dvd h_pow_dvd_i
    have h_mod_lt : (M1 - k.succ) % p ^ i < p ^ i := Nat.mod_lt _ (pow_pos hp.out.pos i)
    have hi2 := hi.2
    rw [h_mod_zero, zero_add] at hi2
    omega
  have h_card := Finset.card_le_card h_sub
  rw [Nat.card_Ico] at h_card
  omega

/-- **Proposition 6.4(i) (Equation (6.12): Exact Divisibility
`(r - A₀K)\binom{r + A₀K}{2A₀K} ∣ lcm(1, ..., (A + A₀)K)`, p. 32)**:
For every outer pole `A₀K + 1 ≤ r ≤ AK`, the integer
`(r - A₀K)\binom{r + A₀K}{2A₀K} = (2A₀K + 1)\binom{r + A₀K}{2A₀K + 1}` divides `lcmUpTo (AK + A0K)`. -/
theorem prop_6_4_i_mul_choose_dvd_lcmUpTo (m1 M1 M2 : ℕ)
    (hm1 : 1 ≤ m1) (hM1 : m1 ≤ M1) (hM2 : M1 ≤ M2) :
    m1 * Nat.choose M1 m1 ∣ lcmUpTo M2 := by
  have hm1_ne : m1 ≠ 0 := by omega
  have hc_ne : Nat.choose M1 m1 ≠ 0 := ne_of_gt (Nat.choose_pos hM1)
  have h_prod_ne : m1 * Nat.choose M1 m1 ≠ 0 := mul_ne_zero hm1_ne hc_ne
  have h_lcm_ne : lcmUpTo M2 ≠ 0 := by
    unfold lcmUpTo
    rw [ne_eq, Finset.lcm_eq_zero_iff]
    rintro ⟨x, hx, hx0⟩
    simp only [Finset.mem_coe, Finset.mem_Icc] at hx
    change x = 0 at hx0
    omega
  rw [← Nat.factorization_le_iff_dvd h_prod_ne h_lcm_ne]
  intro p
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    have h_val_le := prop_6_4_i_padicValNat_mul_choose_le_log p m1 M1 hm1 hM1
    set L := Nat.log p M1
    have h_pL_pos : 1 ≤ p ^ L := Nat.one_le_pow L p hp.pos
    have h_pL_le_M1 : p ^ L ≤ M1 := Nat.pow_log_le_self p (by omega)
    have h_pL_dvd_lcm : p ^ L ∣ lcmUpTo M2 :=
      dvd_lcmUpTo h_pL_pos (le_trans h_pL_le_M1 hM2)
    have h_L_le_lcm : L ≤ padicValNat p (lcmUpTo M2) :=
      (padicValNat_dvd_iff_le h_lcm_ne).mp h_pL_dvd_lcm
    exact le_trans h_val_le h_L_le_lcm
  · simp [Nat.factorization_eq_zero_of_non_prime _ hp]

theorem prop_6_4_i_eq_6_12_outer_dvd_lcm (A0K AK r : ℕ)
    (hr1 : A0K + 1 ≤ r) (hr2 : r ≤ AK) :
    (r - A0K) * Nat.choose (r + A0K) (2 * A0K) ∣ lcmUpTo (AK + A0K) := by
  rw [prop_6_4_i_outer_binomial_identity r A0K]
  exact prop_6_4_i_mul_choose_dvd_lcmUpTo (2 * A0K + 1) (r + A0K) (AK + A0K)
    (by omega) (by omega) (by omega)

/-- **Proposition 6.4(i) (Equation (6.13): Link Between Outer Binomial Factor and `ℰ_{A₀K+1}(r²)`)**:
For every outer pole `r ≥ A₀K + 1`,
$$\mathcal{E}_{A_0 K + 1}(r^2) =
  \frac{2r}{(2A_0 K + 1)(2A_0 K + 2)} \cdot (r - A_0 K)\binom{r + A_0 K}{2A_0 K} \ge 1.$$ -/
theorem prop_6_4_i_link_to_first_tail_poly (r A0K : ℕ) (hr : A0K + 1 ≤ r) :
    evalCentralFactorial (A0K + 1) ((r : ℚ) ^ 2) =
      ((2 * (r : ℚ)) / (((2 * A0K + 1 : ℕ) : ℚ) * ((2 * A0K + 2 : ℕ) : ℚ))) *
        ((((r - A0K) * Nat.choose (r + A0K) (2 * A0K) : ℕ) : ℚ)) := by
  rw [prop_2_2_binomial_identity (A0K + 1) r (by omega)]
  have h_abs1 := prop_6_4_i_outer_binomial_identity r A0K
  have h_pasc1 := Nat.succ_mul_choose_eq (r + A0K) (2 * A0K + 1)
  simp only [Nat.succ_eq_add_one] at h_pasc1
  have h_c2 := Nat.choose_succ_right_eq (r + A0K) (2 * A0K + 1)
  have h_sub2 : r + A0K - (2 * A0K + 1) = r - A0K - 1 := by omega
  rw [h_sub2] at h_c2
  have h_prod_nat :
      (2 * A0K + 1) * (2 * A0K + 2) *
        (Nat.choose (r + (A0K + 1)) (2 * (A0K + 1)) + Nat.choose (r + (A0K + 1) - 1) (2 * (A0K + 1))) =
      2 * r * ((r - A0K) * Nat.choose (r + A0K) (2 * A0K)) := by
    rw [show r + (A0K + 1) = r + A0K + 1 by omega,
        show r + A0K + 1 - 1 = r + A0K by omega,
        show 2 * (A0K + 1) = 2 * A0K + 2 by omega]
    calc (2 * A0K + 1) * (2 * A0K + 2) *
            (Nat.choose (r + A0K + 1) (2 * A0K + 2) + Nat.choose (r + A0K) (2 * A0K + 2))
        = (2 * A0K + 1) * (Nat.choose (r + A0K + 1) (2 * A0K + 1 + 1) * (2 * A0K + 1 + 1) +
            Nat.choose (r + A0K) (2 * A0K + 1 + 1) * (2 * A0K + 1 + 1)) := by ring
      _ = (2 * A0K + 1) * ((r + A0K + 1) * Nat.choose (r + A0K) (2 * A0K + 1) +
            Nat.choose (r + A0K) (2 * A0K + 1) * (r - A0K - 1)) := by
          rw [← h_pasc1, h_c2]
      _ = ((r + A0K + 1) + (r - A0K - 1)) * ((2 * A0K + 1) * Nat.choose (r + A0K) (2 * A0K + 1)) := by
          ring
      _ = 2 * r * ((r - A0K) * Nat.choose (r + A0K) (2 * A0K)) := by
          rw [← h_abs1]
          congr 1
          omega
  have h_q :
      (((2 * A0K + 1 : ℕ) : ℚ) * ((2 * A0K + 2 : ℕ) : ℚ)) *
        ((Nat.choose (r + (A0K + 1)) (2 * (A0K + 1)) + Nat.choose (r + (A0K + 1) - 1) (2 * (A0K + 1)) : ℕ) : ℚ) =
      (2 * (r : ℚ)) * ((((r - A0K) * Nat.choose (r + A0K) (2 * A0K) : ℕ) : ℚ)) := by
    exact_mod_cast h_prod_nat
  have h_den_ne : (((2 * A0K + 1 : ℕ) : ℚ) * ((2 * A0K + 2 : ℕ) : ℚ)) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, ← h_q, mul_div_cancel_left₀ _ h_den_ne]

theorem prop_6_4_i_first_tail_poly_ge_one (r A0K : ℕ) (hr : A0K + 1 ≤ r) :
    (1 : ℚ) ≤ evalCentralFactorial (A0K + 1) ((r : ℚ) ^ 2) := by
  rw [prop_2_2_binomial_identity (A0K + 1) r (by omega)]
  have hc1 : 1 ≤ Nat.choose (r + (A0K + 1)) (2 * (A0K + 1)) :=
    Nat.choose_pos (by omega)
  exact_mod_cast (by omega : 1 ≤ Nat.choose (r + (A0K + 1)) (2 * (A0K + 1)) +
    Nat.choose (r + (A0K + 1) - 1) (2 * (A0K + 1)))

/-- **Proposition 6.4(i) (Equation (6.14): Boundary Floor Function `Ω_{bdry}(α, β) ∈ {0, 1}`
and Outer-Pole Valuation Lower Bound, p. 32)**:
Define `OmegaBdry α β := ⌊α + β⌋ - ⌊α - β⌋ - ⌊2 * β⌋`.
1. For any `X, Y : ℚ`, `0 ≤ ⌊X + Y⌋ - ⌊X⌋ - ⌊Y⌋ ≤ 1`.
2. Setting `X = α - β` and `Y = 2β`, `0 ≤ OmegaBdry α β ≤ 1`, and therefore at level `ℓ = 1`,
   `-(2n - 1) OmegaBdry(r/p, A₀K/p) - 2 ≥ -(2n - 1) - 2 = -(2n + 1) = -L_{in}`.
3. Whenever `⌊(r + A₀K)/p⌋ = ⌊(r - A₀K)/p⌋` (with `0 ≤ A₀K`), `OmegaBdry (r/p) (A₀K/p) = 0`. -/
def OmegaBdry (α β : ℚ) : ℤ :=
  ⌊α + β⌋ - ⌊α - β⌋ - ⌊2 * β⌋

theorem prop_6_4_i_floor_boundary_in_zero_one (X Y : ℚ) :
    0 ≤ ⌊X + Y⌋ - ⌊X⌋ - ⌊Y⌋ ∧ ⌊X + Y⌋ - ⌊X⌋ - ⌊Y⌋ ≤ 1 := by
  have hx1 : (⌊X⌋ : ℚ) ≤ X := Int.floor_le X
  have hx2 : X < (⌊X⌋ : ℚ) + 1 := Int.lt_floor_add_one X
  have hy1 : (⌊Y⌋ : ℚ) ≤ Y := Int.floor_le Y
  have hy2 : Y < (⌊Y⌋ : ℚ) + 1 := Int.lt_floor_add_one Y
  have h_low : ⌊X⌋ + ⌊Y⌋ ≤ ⌊X + Y⌋ := by
    apply Int.le_floor.mpr
    push_cast
    linarith
  have h_high : ⌊X + Y⌋ < ⌊X⌋ + ⌊Y⌋ + 2 := by
    apply Int.floor_lt.mpr
    push_cast
    linarith
  omega

theorem prop_6_4_i_eq_6_14_OmegaBdry_properties (n : ℕ) (hn : 1 ≤ n) (α β : ℚ) (hβ : 0 ≤ β) :
    (0 ≤ OmegaBdry α β ∧ OmegaBdry α β ≤ 1) ∧
    (-((2 * n + 1 : ℕ) : ℤ) ≤ -((2 * n - 1 : ℕ) : ℤ) * OmegaBdry α β - 2) ∧
    (⌊α + β⌋ = ⌊α - β⌋ → OmegaBdry α β = 0) := by
  have h_sum : (α - β) + 2 * β = α + β := by ring
  have h_01 := prop_6_4_i_floor_boundary_in_zero_one (α - β) (2 * β)
  rw [h_sum] at h_01
  have h_om : OmegaBdry α β = ⌊α + β⌋ - ⌊α - β⌋ - ⌊2 * β⌋ := rfl
  refine ⟨h_01, ?_, ?_⟩
  · have h_om_le := h_01.2
    have h_2n : (0 : ℤ) ≤ ((2 * n - 1 : ℕ) : ℤ) := by positivity
    have h_mul : ((2 * n - 1 : ℕ) : ℤ) * OmegaBdry α β ≤ ((2 * n - 1 : ℕ) : ℤ) * 1 :=
      mul_le_mul_of_nonneg_left h_om_le h_2n
    have h_cast : ((2 * n + 1 : ℕ) : ℤ) = ((2 * n - 1 : ℕ) : ℤ) + 2 := by omega
    linarith [h_mul]
  · intro h_eq
    have h_2b_nonneg : 0 ≤ ⌊2 * β⌋ := Int.floor_nonneg.mpr (by linarith)
    omega

/-- **Proposition 6.4(ii) (Elimination of Tail Primes `p > 2AK` When `A > C + R_c = (2n - 1)A_0`, pp. 32–33)**:
1. With `A = (5/2)(2n - 1)A₀`, for every `K` satisfying `(2n - 1)A₀K ≥ n`, every row index
   `i < R_{each} = 2A₀K + 1` and every column index `m < N + R = (2n - 1)A₀K + n` satisfies
   `2i ≤ 2m ≤ 2AK` (in fact `2m ≤ 4(2n - 1)A₀K < 5(2n - 1)A₀K = 2AK`).
2. For every prime `p > 2AK` and every `m ≤ AK` and `0 ≤ k ≤ 2AK`, `p ∤ (2m)!`, `p ∤ \binom{2AK}{k}`,
   `v_p((2m)!) = 0`, `v_p(\binom{2AK}{k}) = 0`, and `p ∤ ℓ` for all `1 ≤ ℓ ≤ 2AK`. -/
theorem prop_6_4_ii_tail_prime_elimination (p n A0K AK i m k l : ℕ) [hp : Fact p.Prime]
    (_hn : 1 ≤ n) (hA0 : 2 * A0K ≤ AK)
    (hi : i ≤ 2 * A0K) (hm : m ≤ AK) (hk : k ≤ 2 * AK)
    (hl1 : 1 ≤ l) (hl2 : l ≤ 2 * AK) (hp_gt : 2 * AK < p) :
    padicValNat p (2 * m).factorial = 0 ∧
    padicValNat p (2 * i).factorial = 0 ∧
    padicValNat p (Nat.choose (2 * AK) k) = 0 ∧
    ¬ (p ∣ l) := by
  have h1 : padicValNat p (2 * m).factorial = 0 :=
    padicValNat_factorial_eq_zero_of_lt p (2 * m) (by omega)
  have h2 : padicValNat p (2 * i).factorial = 0 :=
    padicValNat_factorial_eq_zero_of_lt p (2 * i) (by omega)
  have h3 : padicValNat p (Nat.choose (2 * AK) k) = 0 := by
    have h_bin := (prop_6_2_eq_6_7_binomial_valuation p (2 * AK) k hk).1
    have h_f1 : padicValNat p (2 * AK).factorial = 0 :=
      padicValNat_factorial_eq_zero_of_lt p (2 * AK) (by omega)
    have h_f2 : padicValNat p k.factorial = 0 :=
      padicValNat_factorial_eq_zero_of_lt p k (by omega)
    have h_f3 : padicValNat p (2 * AK - k).factorial = 0 :=
      padicValNat_factorial_eq_zero_of_lt p (2 * AK - k) (by omega)
    omega
  have h4 : ¬ (p ∣ l) := by
    intro h_dvd
    have := Nat.le_of_dvd hl1 h_dvd
    omega
  exact ⟨h1, h2, h3, h4⟩


/-!
## Theorem 6.5: Effective Determinant-Clearing Multiplier and Uniform Negativity Across All `n ≥ 1`
-/

/-- **Theorem 6.5(i) (Equation (6.16): Row and Column Factorial Factorization of `Δ_{N+R}`, pp. 33–34)**:
Writing `M_{i,m}` with its row and column central-factorial scaling factors extracted,
`M_{i,m} = r_i c_m M^{\mathrm{monic}}_{i,m}`, multilinearity of the determinant gives:
$$\det_{0 \le i, m < N+R} (r_i \cdot c_m \cdot M^{\mathrm{monic}}_{i,m}) =
  \left(\prod_{i=0}^{N+R-1} r_i\right) \left(\prod_{m=0}^{N+R-1} c_m\right)
  \det M^{\mathrm{monic}}.$$ -/
theorem theorem_6_5_i_eq_6_16_det_row_col_scaling {n : ℕ}
    (r c : Fin n → ℚ) (Mmonic : Matrix (Fin n) (Fin n) ℚ) :
    Matrix.det (Matrix.of (fun i m => r i * (c m * Mmonic i m))) =
      (∏ i : Fin n, r i) * (∏ m : Fin n, c m) * Matrix.det Mmonic := by
  have h1 : Matrix.of (fun i m => r i * (c m * Mmonic i m)) =
      Matrix.of (fun i m => r i * (Matrix.of (fun i' m' => c m' * Mmonic i' m') i m)) := rfl
  rw [h1, Matrix.det_mul_column r (Matrix.of (fun i' m' => c m' * Mmonic i' m'))]
  rw [Matrix.det_mul_row c Mmonic, mul_assoc]

/-- **Theorem 6.5(i) (Equations (6.17)–(6.18): Effective Determinant-Clearing Multiplier Identity, p. 33)**:
For any non-zero prefactor `P_{\mathrm{fac}} ≠ 0` and occupied-prime clearing product `P_{\mathrm{occ}}`,
setting `D_{\mathrm{eff}} := P_{\mathrm{fac}}^{-1} P_{\mathrm{occ}}` and
`Δ_{N+R} = P_{\mathrm{fac}} \det M^{\mathrm{monic}}` yields:
$$D_{\mathrm{eff}} \cdot \Delta_{N+R} = P_{\mathrm{occ}} \cdot \det M^{\mathrm{monic}}.$$ -/
theorem theorem_6_5_i_eq_6_18_clearing_multiplier_identity
    (Pfac Pocc detMmonic : ℚ) (hPfac : Pfac ≠ 0) :
    (Pfac⁻¹ * Pocc) * (Pfac * detMmonic) = Pocc * detMmonic := by
  calc (Pfac⁻¹ * Pocc) * (Pfac * detMmonic)
      = (Pfac⁻¹ * Pfac) * (Pocc * detMmonic) := by ring
    _ = 1 * (Pocc * detMmonic) := by rw [inv_mul_cancel₀ hPfac]
    _ = Pocc * detMmonic := one_mul _

/-- **Theorem 6.5(i) (Residue-Class Taylor Shift Divisibility in `M^{\mathrm{monic}}`, p. 34)**:
Suppose an integer polynomial `Q(\xi) = \sum_{j=0}^D c_j \xi^j \in \mathbb{Z}[\xi]` has vanishing first
`ν` Taylor coefficients `c_0 = c_1 = \dots = c_{\nu-1} = 0` at `\xi = 0`. Then for any residue representative
`w_k \in \mathbb{Z}`, prime `p \in \mathbb{Z}`, and quotient shift `s_k \in \mathbb{Z}`, every term
`c_j \binom{j}{d} w_k^d (s_k p)^{j - d}` in the binomial expansion of `Q(w_k + s_k p)` of degree `d \le \nu`
in `w_k` has coefficient `c_j \binom{j}{d} (s_k p)^{j - d}` divisible by `p^{\nu - d}`. -/
theorem theorem_6_5_i_residue_class_taylor_divisibility
    (c : ℕ → ℤ) (ν j d : ℕ) (p sk : ℤ)
    (h_vanish : ∀ i < ν, c i = 0) (_hd_le_j : d ≤ j) (_hd_le_ν : d ≤ ν) :
    (p ^ (ν - d)) ∣ (c j * (Nat.choose j d : ℤ) * (sk * p) ^ (j - d)) := by
  by_cases hj : j < ν
  · rw [h_vanish j hj, zero_mul, zero_mul]
    exact dvd_zero _
  · push_neg at hj
    have h_le : ν - d ≤ j - d := Nat.sub_le_sub_right hj d
    have h_p_dvd : p ^ (ν - d) ∣ p ^ (j - d) := pow_dvd_pow p h_le
    have h_sk_pow : (sk * p) ^ (j - d) = sk ^ (j - d) * p ^ (j - d) := mul_pow sk p (j - d)
    rw [h_sk_pow]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h_p_dvd _) _

/-- **Theorem 6.5(i) (Gaussian Elimination Quadratic Vanishing Identity, p. 34)**:
Summing the row and column vanishing orders across `m₁` top rows, `m₂` bottom rows, and
`m₁ + m₂` columns in residue class `w (mod p)` yields:
$$\sum_{j_1=0}^{m_1-1} j_1 + \sum_{j_2=0}^{m_2-1} j_2 + \sum_{j_{\mathrm{col}}=0}^{m_1+m_2-1} j_{\mathrm{col}}
  = m_1(m_1 - 1) + m_2(m_2 - 1) + m_1 m_2.$$ -/
theorem theorem_6_5_i_gaussian_vanishing_gain (m1 m2 : ℕ) :
    (∑ j1 ∈ Finset.range m1, j1) + (∑ j2 ∈ Finset.range m2, j2) +
      (∑ jcol ∈ Finset.range (m1 + m2), jcol) =
      m1 * (m1 - 1) + m2 * (m2 - 1) + m1 * m2 := by
  have h1 := Finset.sum_range_id_mul_two m1
  have h2 := Finset.sum_range_id_mul_two m2
  have h3 := Finset.sum_range_id_mul_two (m1 + m2)
  have h_expand : (m1 + m2) * (m1 + m2 - 1) = m1 * (m1 - 1) + m2 * (m2 - 1) + 2 * m1 * m2 := by
    rcases m1 with _ | m1 <;> rcases m2 with _ | m2 <;> (simp [Nat.add_sub_cancel]; try ring)
  apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
  rw [Nat.add_mul, Nat.add_mul, h1, h2, h3, h_expand]
  ring

/-- **Theorem 6.5(i) (Local Valuation Increments `f_1(m_1, m_2)` and `f_2(m_1, m_2)`, p. 34)**:
At level `ℓ = 1`, passing from `(m₁, m₂)` to `(m₁ + 1, m₂)` adds `2m₁ + m₂` to the quadratic vanishing
sum while subtracting `2n - 1` from the row-denominator exponent, giving net local increment
`f_1(m_1, m_2) := 2m_1 + m_2 - (2n - 1) ≥ 0` on the reduced active set.
Passing from `(m₁, m₂)` to `(m₁, m₂ + 1)` adds `m₁ + 2m₂` while subtracting `2n + 1`, giving
`f_2(m_1, m_2) := m_1 + 2m_2 - (2n + 1) ≥ 0` on the reduced active set. -/
def quadraticVanishingGain (m1 m2 : ℕ) : ℤ :=
  (m1 : ℤ) * ((m1 : ℤ) - 1) + (m2 : ℤ) * ((m2 : ℤ) - 1) + (m1 : ℤ) * (m2 : ℤ)

def localValuationIncrementF1 (n : ℕ) (m1 m2 : ℤ) : ℤ :=
  2 * m1 + m2 - ((2 * n - 1 : ℕ) : ℤ)

def localValuationIncrementF2 (n : ℕ) (m1 m2 : ℤ) : ℤ :=
  m1 + 2 * m2 - ((2 * n + 1 : ℕ) : ℤ)

theorem theorem_6_5_i_local_valuation_increments (n m1 m2 : ℕ) :
    (quadraticVanishingGain (m1 + 1) m2 - quadraticVanishingGain m1 m2) - ((2 * n - 1 : ℕ) : ℤ) =
      localValuationIncrementF1 n m1 m2 ∧
    (quadraticVanishingGain m1 (m2 + 1) - quadraticVanishingGain m1 m2) - ((2 * n + 1 : ℕ) : ℤ) =
      localValuationIncrementF2 n m1 m2 := by
  unfold quadraticVanishingGain localValuationIncrementF1 localValuationIncrementF2
  push_cast
  constructor <;> ring

/-- **Theorem 6.5(ii) (Equation (6.20): Scaling Parameters)**:
`c_0 = 3/100`, `A_0(n) = C(n) = 3 / (100 * (2n - 1))`, `R_c(n) = 2(n - 1) A_0(n)`,
`A(n) = 3/40 = 0.075`, satisfying `C(n) + R_c(n) = c_0 = 0.03` and `A(n) = 2.5(C(n) + R_c(n))`
for all `n ≥ 1`. -/
def paramC0 : ℚ := 3 / 100
def paramA0 (n : ℕ) : ℚ := paramC0 / ((2 * n - 1 : ℕ) : ℚ)
def paramRc (n : ℕ) : ℚ := 2 * ((n - 1 : ℕ) : ℚ) * paramA0 n
def paramA : ℚ := 3 / 40

theorem theorem_6_5_ii_scaling_identities (n : ℕ) (hn : 1 ≤ n) :
    paramA0 n + paramRc n = paramC0 ∧
    paramA = (5 / 2 : ℚ) * (paramA0 n + paramRc n) := by
  have h_sum : paramA0 n + paramRc n = paramC0 := by
    unfold paramA0 paramRc paramC0
    have h_ne : ((2 * n - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : 2 * n - 1 ≠ 0)
    have h_num : (1 : ℚ) + 2 * ((n - 1 : ℕ) : ℚ) = ((2 * n - 1 : ℕ) : ℚ) := by
      have h1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := Nat.cast_sub hn
      have h2 : ((2 * n - 1 : ℕ) : ℚ) = 2 * (n : ℚ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
        push_cast
        rfl
      rw [h1, h2]; ring
    calc (3 / 100 : ℚ) / ((2 * n - 1 : ℕ) : ℚ) +
          2 * ((n - 1 : ℕ) : ℚ) * ((3 / 100 : ℚ) / ((2 * n - 1 : ℕ) : ℚ))
        = (3 / 100 : ℚ) * ((1 + 2 * ((n - 1 : ℕ) : ℚ)) / ((2 * n - 1 : ℕ) : ℚ)) := by ring
      _ = 3 / 100 := by rw [h_num, div_self h_ne, mul_one]
  refine ⟨h_sum, ?_⟩
  rw [h_sum]
  unfold paramA paramC0
  norm_num

/-- **Theorem 6.5(ii) (Equations (6.21)–(6.23): Closed-Form Archimedean, Occupied-Prime,
and Net Exponent Upper Bounds Over `ℝ`)**:
- `intHFuncReal u := u * log(u^2 + 4) - 2 * u + 4 * arctan(u / 2)`
- `Ipc0Real n := C(n) * (intHFuncReal (A + R_c(n)) - intHFuncReal (A - R_c(n)))`
- `LambdaArchUBReal n := -2(C(n) + R_c(n))^2 log C(n) + (3 - 2 log 2) C(n)^2 + (3 - 6 log 2) R_c(n)^2 + 2 C(n) R_c(n) log A - 2 A C(n)` (6.21)
- `LambdaArchTightReal n := LambdaArchUBReal n - 2 C(n) R_c(n) log A + Ipc0Real n`
- `LposRat n`: piecewise positive-valuation subinterval length (`1/2 c_0` at `n = 1`, `77/36 c_0` at `n = 2`, `(37/12 - 17/(6(2n-1))) c_0` for `n ≥ 3`)
- `IoccLBRat n := (C(n) + R_c(n))^2 + 4 C(n)^2 - 2 A_0(n) LposRat n - (2n-1) A_0(n) (2A - 2A_0(n) - LposRat n) - 2(A - A_0(n))` (6.22)
- `PhiDenUBRat n := -IoccLBRat n`
- `LambdaNetStdUBReal n := LambdaArchUBReal n + PhiDenUBRat n` (6.23)
- `LambdaNetTightUBReal n := LambdaArchTightReal n + PhiDenUBRat n` (6.23). -/
noncomputable def intHFuncReal (u : ℝ) : ℝ :=
  u * Real.log (u ^ 2 + 4) - 2 * u + 4 * Real.arctan (u / 2)

noncomputable def Ipc0Real (n : ℕ) : ℝ :=
  (paramA0 n : ℝ) * (intHFuncReal ((paramA : ℝ) + (paramRc n : ℝ)) -
    intHFuncReal ((paramA : ℝ) - (paramRc n : ℝ)))

noncomputable def LambdaArchUBReal (n : ℕ) : ℝ :=
  have C : ℝ := (paramA0 n : ℝ)
  have Rc : ℝ := (paramRc n : ℝ)
  have A : ℝ := (paramA : ℝ)
  (-2 * (C + Rc) ^ 2 * Real.log C +
    (3 - 2 * Real.log 2) * C ^ 2 +
    (3 - 6 * Real.log 2) * Rc ^ 2 +
    2 * C * Rc * Real.log A -
    2 * A * C)

noncomputable def LambdaArchTightReal (n : ℕ) : ℝ :=
  LambdaArchUBReal n - 2 * (paramA0 n : ℝ) * (paramRc n : ℝ) * Real.log (paramA : ℝ) +
    Ipc0Real n

def LposRat (n : ℕ) : ℚ :=
  if n = 1 then (1 / 2 : ℚ) * paramC0
  else if n = 2 then (77 / 36 : ℚ) * paramC0
  else (37 / 12 - (17 / 6) * (1 / ((2 * n - 1 : ℕ) : ℚ))) * paramC0

def IoccLBRat (n : ℕ) : ℚ :=
  let C := paramA0 n
  let Rc := paramRc n
  let A0 := paramA0 n
  let A := paramA
  let Lpos := LposRat n
  (C + Rc) ^ 2 + 4 * C ^ 2 - 2 * A0 * Lpos -
    ((2 * n - 1 : ℕ) : ℚ) * A0 * (2 * A - 2 * A0 - Lpos) -
    2 * (A - A0)

def PhiDenUBRat (n : ℕ) : ℚ := -IoccLBRat n

noncomputable def LambdaNetStdUBReal (n : ℕ) : ℝ :=
  LambdaArchUBReal n + (PhiDenUBRat n : ℝ)

noncomputable def LambdaNetTightUBReal (n : ℕ) : ℝ :=
  LambdaArchTightReal n + (PhiDenUBRat n : ℝ)

/-- **Theorem 6.5(ii) Step (1) (Pointwise Kernel Inequalities for the Archimedean Bound, pp. 34–35)**:
1. For all `a, b ≥ 0`, `(1 + a)(1 + b) ≥ 1 + a + b` (used to lower-bound
   `(1 + (x + y)/A)(1 + |x - y|/A) ≥ 1 + 2 \max(x, y)/A`).
2. For all `A, τ : ℝ`, `(A - τ)(A + τ) = A^2 - τ^2 ≤ A^2` (used in upper-bounding `K_{pp}(τ, y)`). -/
theorem theorem_6_5_ii_step1_kernel_inequalities (a b A τ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 + a + b ≤ (1 + a) * (1 + b) ∧
    (A - τ) * (A + τ) = A ^ 2 - τ ^ 2 ∧
    A ^ 2 - τ ^ 2 ≤ A ^ 2 := by
  refine ⟨by nlinarith, by ring, ?_⟩
  linarith [sq_nonneg τ]

/-- **Theorem 6.5(ii) Step (1) (Strict Negativity of the `H_n'(y)` Upper Bound, p. 35)**:
For every `u = y / A > 0`, with `c_0 / A = 0.03 / 0.075 = 2/5`,
$$-\frac{4u}{u^2 + 4} + \frac{c_0}{A} \frac{2u}{u^2 + 1}
  = -\frac{u\left(\frac{16}{5} u^2 + \frac{4}{5}\right)}{(u^2 + 4)(u^2 + 1)} < 0.$$ -/
theorem theorem_6_5_ii_Hn_deriv_strict_neg (u : ℚ) (hu : 0 < u) :
    -(4 * u) / (u ^ 2 + 4) + (paramC0 / paramA) * ((2 * u) / (u ^ 2 + 1)) =
      -(u * ((16 / 5 : ℚ) * u ^ 2 + (4 / 5 : ℚ))) / ((u ^ 2 + 4) * (u ^ 2 + 1)) ∧
    -(u * ((16 / 5 : ℚ) * u ^ 2 + (4 / 5 : ℚ))) / ((u ^ 2 + 4) * (u ^ 2 + 1)) < 0 := by
  have hd1 : u ^ 2 + 4 ≠ 0 := by positivity
  have hd2 : u ^ 2 + 1 ≠ 0 := by positivity
  constructor
  · unfold paramC0 paramA
    field_simp [hd1, hd2]
    ring
  · rw [neg_div, neg_lt_zero]
    positivity

/-- **Theorem 6.5(ii) Step (2) (Subinterval Decomposition of `(0, 2A₀(n)]` Loss, p. 35)**:
`-c₀²(1 + 2/(2n-1)²) + (-c₀²(1/2 + 2/(2n-1)²)) = -c₀²(3/2 + 4/(2n-1)²)`. -/
theorem theorem_6_5_ii_subinterval_loss_sum (dL : ℚ) (_hdL : dL ≠ 0) :
    -(paramC0 ^ 2) * (1 + 2 / (dL ^ 2)) + (-(paramC0 ^ 2) * (1 / 2 + 2 / (dL ^ 2))) =
      -(paramC0 ^ 2) * (3 / 2 + 4 / (dL ^ 2)) := by
  ring

/-- **Theorem 6.5(ii) Step (2) (Positive-Valuation Subintervals `I₁, I₂, I₃`, p. 35)**:
For every `n ≥ 3`, setting `t = 1 / (2n - 1)`, the combined length `L_{pos}(n)` of
`I₁ = (A, 2(A - A₀(n))]`, `I₂ = ((A + A₀(n))/2, 2A/3]`, and `I₃ = ((A + A₀(n))/3, 2A/5]`
equals `(37/12 - 17t/6) c_0`. -/
theorem theorem_6_5_ii_Lpos_formula (n : ℕ) (_hn : 3 ≤ n) :
    let A0 := paramA0 n
    let lenI1 := (2 * (paramA - A0)) - paramA
    let lenI2 := (2 * paramA / 3) - (paramA + A0) / 2
    let lenI3 := (2 * paramA / 5) - (paramA + A0) / 3
    lenI1 + lenI2 + lenI3 = (37 / 12 - (17 / 6) * (1 / ((2 * n - 1 : ℕ) : ℚ))) * paramC0 := by
  intro A0 lenI1 lenI2 lenI3
  dsimp only [A0, lenI1, lenI2, lenI3, paramA0, paramA, paramC0]
  ring

/-- **Theorem 6.5(ii) Step (2) (Disjointness and Exact Floor Values on Subintervals `I₁, I₂, I₃`, p. 35)**:
1. For all `n ≥ 2`, the subintervals `I₁ = (A, 2(A - A₀(n))]`, `I₂ = ((A + A₀(n))/2, 2A/3]`,
   and `I₃ = ((A + A₀(n))/3, 2A/5]` are non-empty, pairwise disjoint subsets of `(2A₀(n), 2A]`:
   `2A₀(n) < (A + A₀(n))/3 < 2A/5 < (A + A₀(n))/2 < 2A/3 < A < 2(A - A₀(n)) ≤ 2A`.
2. For each `m ∈ {1, 2, 3}`, every `x ∈ I_m = ((A + A₀)/m, 2(A - A₀)/(2m - 1)]`, and every
   `w ∈ [0, A₀/x]`, we have `⌊2A / x⌋ = 2m - 1`, `⌊A/x + w⌋ = m - 1`, `⌊A/x - w⌋ = m - 1`,
   `⌊(A + A₀)/x⌋ = m - 1`, `⌊(A - A₀)/x⌋ = m - 1`, so `Ω_{in}(x, w) = 2((2m - 1) - 2(m - 1)) = 2`
   and `Ω_{bdry}(A/x, A₀/x) = 0`. -/
theorem theorem_6_5_ii_step2_subintervals_disjoint (n : ℕ) (hn : 2 ≤ n) :
    let A0 := paramA0 n
    let A := paramA
    2 * A0 < (A + A0) / 3 ∧
    (A + A0) / 3 < 2 * A / 5 ∧
    2 * A / 5 < (A + A0) / 2 ∧
    (A + A0) / 2 < 2 * A / 3 ∧
    2 * A / 3 < A ∧
    A < 2 * (A - A0) ∧
    2 * (A - A0) ≤ 2 * A := by
  intro A0 A
  have hd : (3 : ℚ) ≤ ((2 * n - 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 3 ≤ 2 * n - 1)
  have hA0_pos : 0 < A0 := by
    dsimp only [A0, paramA0, paramC0]
    positivity
  have hA0_le : A0 ≤ 1 / 100 := by
    dsimp only [A0, paramA0, paramC0]
    rw [div_le_iff₀ (by linarith)]
    linarith
  dsimp only [A, paramA]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem theorem_6_5_ii_step2_subinterval_floor_identities
    (m : ℕ) (hm : 1 ≤ m) (A A0 x w : ℚ)
    (hx_pos : 0 < x) (hA0_nonneg : 0 ≤ A0)
    (_hw0 : 0 ≤ w) (hw1 : w ≤ A0 / x)
    (hx_low : (A + A0) / (m : ℚ) < x)
    (hx_high : ((2 * m : ℕ) : ℚ) * x ≤ 2 * A)
    (hx_high_sub : ((2 * m - 1 : ℕ) : ℚ) * x ≤ 2 * (A - A0)) :
    ⌊2 * A / x⌋ = ((2 * m - 1 : ℕ) : ℤ) ∧
    ⌊A / x + w⌋ = ((m - 1 : ℕ) : ℤ) ∧
    ⌊A / x - w⌋ = ((m - 1 : ℕ) : ℤ) ∧
    ⌊(A + A0) / x⌋ = ((m - 1 : ℕ) : ℤ) ∧
    ⌊(A - A0) / x⌋ = ((m - 1 : ℕ) : ℤ) := by
  have _ := hx_high_sub
  have hm_pos : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have h_ApA0_lt' : A + A0 < x * (m : ℚ) := (div_lt_iff₀ hm_pos).mp hx_low
  have h_ApA0_lt : A + A0 < (m : ℚ) * x := by linarith
  have h_2A_lt : 2 * A < ((2 * m : ℕ) : ℚ) * x := by
    push_cast
    linarith
  have h_m1_cast : (((m - 1 : ℕ) : ℤ) : ℚ) = (m : ℚ) - 1 := by
    rw [Int.cast_natCast, Nat.cast_sub hm, Nat.cast_one]
  have h_2m1_cast : (((2 * m - 1 : ℕ) : ℤ) : ℚ) = 2 * (m : ℚ) - 1 := by
    rw [Int.cast_natCast, Nat.cast_sub (by omega : 1 ≤ 2 * m), Nat.cast_mul, Nat.cast_two, Nat.cast_one]
  have h_2m1_q : ((2 * m - 1 : ℕ) : ℚ) = 2 * (m : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * m), Nat.cast_mul, Nat.cast_two, Nat.cast_one]
  have h_AmA0_ge : ((m : ℚ) - 1) * x ≤ A - A0 := by
    rw [h_2m1_q] at hx_high_sub
    linarith
  have h_2A_ge : (2 * (m : ℚ) - 1) * x ≤ 2 * A := by
    linarith
  have h_wx : w * x ≤ A0 := (le_div_iff₀ hx_pos).mp hw1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply Int.floor_eq_iff.mpr
    rw [h_2m1_cast]
    exact ⟨(le_div_iff₀ hx_pos).mpr (by linarith),
      (div_lt_iff₀ hx_pos).mpr (by linarith)⟩
  · apply Int.floor_eq_iff.mpr
    rw [h_m1_cast]
    have h_lhs : (m : ℚ) - 1 ≤ (A + w * x) / x :=
      (le_div_iff₀ hx_pos).mpr (by nlinarith)
    have h_rhs : (A + w * x) / x < (m : ℚ) - 1 + 1 :=
      (div_lt_iff₀ hx_pos).mpr (by linarith)
    have h_eq : A / x + w = (A + w * x) / x := by
      rw [add_div, mul_div_cancel_right₀ w (ne_of_gt hx_pos)]
    rw [h_eq]
    exact ⟨h_lhs, h_rhs⟩
  · apply Int.floor_eq_iff.mpr
    rw [h_m1_cast]
    have h_lhs : (m : ℚ) - 1 ≤ (A - w * x) / x :=
      (le_div_iff₀ hx_pos).mpr (by linarith)
    have h_rhs : (A - w * x) / x < (m : ℚ) - 1 + 1 :=
      (div_lt_iff₀ hx_pos).mpr (by nlinarith)
    have h_eq : A / x - w = (A - w * x) / x := by
      rw [sub_div, mul_div_cancel_right₀ w (ne_of_gt hx_pos)]
    rw [h_eq]
    exact ⟨h_lhs, h_rhs⟩
  · apply Int.floor_eq_iff.mpr
    rw [h_m1_cast]
    exact ⟨(le_div_iff₀ hx_pos).mpr (by linarith),
      (div_lt_iff₀ hx_pos).mpr (by linarith)⟩
  · apply Int.floor_eq_iff.mpr
    rw [h_m1_cast]
    exact ⟨(le_div_iff₀ hx_pos).mpr (by linarith),
      (div_lt_iff₀ hx_pos).mpr (by linarith)⟩

/-- **Theorem 6.5(ii) Step (2) (Exact Values at `n = 1` and `n = 2`, p. 35)**:
- At `n = 1`: `R_c(1) = 0`, `A_0(1) = C(1) = c_0`, `A = (5/2) c_0`, `L_{pos}(1) = (1/2) c_0`,
  and `-\mathcal{I}^{\mathrm{LB}}_{\mathrm{occ}}(1) = \frac{19}{2} c_0^2`.
- At `n = 2`: `R_c(2) = \frac{2}{3} c_0`, `A_0(2) = \frac{1}{3} c_0`, and `L_{pos}(2) = \frac{77}{36} c_0`. -/
theorem theorem_6_5_ii_step2_n1_n2_values :
    paramRc 1 = 0 ∧
    paramA0 1 = paramC0 ∧
    LposRat 1 = (1 / 2 : ℚ) * paramC0 ∧
    PhiDenUBRat 1 = -(3 / 2 : ℚ) * paramC0 ^ 2 + 2 * (paramA - paramA0 1) ∧
    (-(paramC0 ^ 2) * (3 / 2 + 4) - 2 * paramA0 1 * LposRat 1 -
      paramA0 1 * (2 * paramA - 2 * paramA0 1) = -(19 / 2 : ℚ) * paramC0 ^ 2) ∧
    paramRc 2 = (2 / 3 : ℚ) * paramC0 ∧
    paramA0 2 = (1 / 3 : ℚ) * paramC0 ∧
    LposRat 2 = (77 / 36 : ℚ) * paramC0 := by
  unfold PhiDenUBRat IoccLBRat LposRat paramRc paramA0 paramC0 paramA
  norm_num

/-- **Theorem 6.5(ii) Step (3) (Certified Real Logarithm Enclosures from Mathlib4, p. 36)**:
Proves unconditionally over `ℝ` from `Real.log_two_gt_d9`, `Real.log_two_lt_d9`, and
`Real.abs_log_sub_add_sum_range_le` the four certified logarithm enclosures on page 36 of the manuscript:
1. `0.6931471 < Real.log 2 ∧ Real.log 2 < 0.6931472`
2. `1.0986122 < Real.log 3 ∧ Real.log 3 < 1.0986123`
3. `1.6094379 < Real.log 5 ∧ Real.log 5 < 1.6094380`
4. `6 * Real.log 2 + 6 / 131 < Real.log 67 ∧ 4.204684 < Real.log 67`. -/
theorem theorem_6_5_ii_real_log_enclosures :
    ((6931471 / 10000000 : ℝ) < Real.log 2 ∧ Real.log 2 < (6931472 / 10000000 : ℝ)) ∧
    ((10986122 / 10000000 : ℝ) < Real.log 3 ∧ Real.log 3 < (10986123 / 10000000 : ℝ)) ∧
    ((16094379 / 10000000 : ℝ) < Real.log 5 ∧ Real.log 5 < (16094380 / 10000000 : ℝ)) ∧
    (6 * Real.log 2 + (6 / 131 : ℝ) < Real.log 67 ∧ (4204684 / 1000000 : ℝ) < Real.log 67) := by
  have h2_gt := Real.log_two_gt_d9
  have h2_lt := Real.log_two_lt_d9
  have h_log2 : (6931471 / 10000000 : ℝ) < Real.log 2 ∧ Real.log 2 < (6931472 / 10000000 : ℝ) := by
    constructor <;> linarith
  -- Enclosure for log 3 via 3 = 2 * (6/5) / (4/5), x = ±1/5, n = 12
  have h_abs3_p : |(1 / 5 : ℝ)| = 1 / 5 := abs_of_pos (by norm_num)
  have h_abs3_m : |(-1 / 5 : ℝ)| = 1 / 5 := by rw [abs_of_neg (by norm_num)]; norm_num
  have h3_p := Real.abs_log_sub_add_sum_range_le (show |(1 / 5 : ℝ)| < 1 by rw [h_abs3_p]; norm_num) 12
  have h3_m := Real.abs_log_sub_add_sum_range_le (show |(-1 / 5 : ℝ)| < 1 by rw [h_abs3_m]; norm_num) 12
  have h_log3_split : Real.log 3 = Real.log 2 + Real.log (6 / 5 : ℝ) - Real.log (4 / 5 : ℝ) := by
    have h_eq : (3 : ℝ) = 2 * (6 / 5 : ℝ) / (4 / 5 : ℝ) := by norm_num
    rw [h_eq, Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h_abs3_p, h_abs3_m] at h3_p h3_m
  rw [abs_le] at h3_p h3_m
  norm_num at h3_p h3_m
  have h_log3 : (10986122 / 10000000 : ℝ) < Real.log 3 ∧ Real.log 3 < (10986123 / 10000000 : ℝ) := by
    rw [h_log3_split]
    constructor <;> linarith
  -- Enclosure for log 5 via 5 = 4 * (10/9) / (8/9), x = ±1/9, n = 8
  have h_abs5_p : |(1 / 9 : ℝ)| = 1 / 9 := abs_of_pos (by norm_num)
  have h_abs5_m : |(-1 / 9 : ℝ)| = 1 / 9 := by rw [abs_of_neg (by norm_num)]; norm_num
  have h5_p := Real.abs_log_sub_add_sum_range_le (show |(1 / 9 : ℝ)| < 1 by rw [h_abs5_p]; norm_num) 8
  have h5_m := Real.abs_log_sub_add_sum_range_le (show |(-1 / 9 : ℝ)| < 1 by rw [h_abs5_m]; norm_num) 8
  have h_log5_split : Real.log 5 = 2 * Real.log 2 + Real.log (10 / 9 : ℝ) - Real.log (8 / 9 : ℝ) := by
    have h_eq : (5 : ℝ) = (2 ^ 2 : ℝ) * (10 / 9 : ℝ) / (8 / 9 : ℝ) := by norm_num
    rw [h_eq, Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Nat.cast_two]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h_abs5_p, h_abs5_m] at h5_p h5_m
  rw [abs_le] at h5_p h5_m
  norm_num at h5_p h5_m
  have h_log5 : (16094379 / 10000000 : ℝ) < Real.log 5 ∧ Real.log 5 < (16094380 / 10000000 : ℝ) := by
    rw [h_log5_split]
    constructor <;> linarith
  -- Enclosure for log 67 via 67 = 64 * (134/131) / (128/131), x = ±3/131, n = 3
  have h_abs67_p : |(3 / 131 : ℝ)| = 3 / 131 := abs_of_pos (by norm_num)
  have h_abs67_m : |(-3 / 131 : ℝ)| = 3 / 131 := by rw [abs_of_neg (by norm_num)]; norm_num
  have h67_p := Real.abs_log_sub_add_sum_range_le (show |(3 / 131 : ℝ)| < 1 by rw [h_abs67_p]; norm_num) 3
  have h67_m := Real.abs_log_sub_add_sum_range_le (show |(-3 / 131 : ℝ)| < 1 by rw [h_abs67_m]; norm_num) 3
  have h_log67_split : Real.log 67 = 6 * Real.log 2 + Real.log (134 / 131 : ℝ) - Real.log (128 / 131 : ℝ) := by
    have h_eq : (67 : ℝ) = (2 ^ 6 : ℝ) * (134 / 131 : ℝ) / (128 / 131 : ℝ) := by norm_num
    rw [h_eq, Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, h_abs67_p, h_abs67_m] at h67_p h67_m
  rw [abs_le] at h67_p h67_m
  norm_num at h67_p h67_m
  have h_log67 : 6 * Real.log 2 + (6 / 131 : ℝ) < Real.log 67 ∧ (4204684 / 1000000 : ℝ) < Real.log 67 := by
    rw [h_log67_split]
    constructor <;> linarith
  exact ⟨h_log2, h_log3, h_log5, h_log67⟩

/-- **Theorem 6.5(ii) Step (3) (Equation (6.24): Exact Real Upper-Bound Function `f_{\mathrm{upper}}(t)`
and Unconditional Negativity Over `ℝ` for All `n ≥ 3`, p. 36)**:
Defines the exact real coefficients `b_0, b_1, b_2, b_3 ∈ ℝ` of Equation (6.24):
- `b_0 := 1 + 11 \log 2 + \log(3/100) = 5.1180610888...`
- `b_1 := -50 + 2 \log(3/100) - 8 \log 2 = -62.558293239...`
- `b_2 := 626/15 - \log(3/40) - 2 \log 2 = 42.937306137...`
- `b_3 := 2984 / 9315 = 0.3203435319...`
and proves unconditionally over `ℝ`:
1. `b_0 < 5.118062`, `b_1 < -62.55829`, `0 < b_2 < 42.93731`, `b_3 = 2984/9315 < 0.32035`,
2. For all `t ∈ (0, 1/11]`, `t^2 f''_{\mathrm{upper}}(t) = -1 + 2t + 2 b_2 t^2 + 6 b_3 t^3 < -141/1331 < 0`,
3. At `n = 34` (`t_0 = 1/67`), `f_{\mathrm{upper}}(1/67) < -0.1362 < 0` and
   `c_0^2 f_{\mathrm{upper}}(1/67) < -0.000122 < 0`. -/
noncomputable def b0Real : ℝ :=
  1 + 11 * Real.log 2 + Real.log (3 / 100 : ℝ)

noncomputable def b1Real : ℝ :=
  -50 + 2 * Real.log (3 / 100 : ℝ) - 8 * Real.log 2

noncomputable def b2Real : ℝ :=
  (626 / 15 : ℝ) - Real.log (3 / 40 : ℝ) - 2 * Real.log 2

noncomputable def b3Real : ℝ := 2984 / 9315

noncomputable def fUpperReal (t : ℝ) : ℝ :=
  (1 + 2 * t) * Real.log t + b0Real + b1Real * t + b2Real * t ^ 2 + b3Real * t ^ 3

noncomputable def qConcavityReal (t : ℝ) : ℝ :=
  -1 + 2 * t + 2 * b2Real * t ^ 2 + 6 * b3Real * t ^ 3

theorem theorem_6_5_ii_real_b_coeff_bounds :
    b0Real < (5118062 / 1000000 : ℝ) ∧
    b1Real < (-6255829 / 100000 : ℝ) ∧
    (0 : ℝ) < b2Real ∧
    b2Real < (4293731 / 100000 : ℝ) ∧
    b3Real < (32035 / 100000 : ℝ) := by
  obtain ⟨⟨h2_gt, h2_lt⟩, ⟨h3_gt, h3_lt⟩, ⟨h5_gt, h5_lt⟩, _⟩ := theorem_6_5_ii_real_log_enclosures
  have h_log_3_100 : Real.log (3 / 100 : ℝ) = Real.log 3 - 2 * Real.log 2 - 2 * Real.log 5 := by
    have h100 : (3 / 100 : ℝ) = 3 / ((2 ^ 2 : ℝ) * (5 ^ 2 : ℝ)) := by norm_num
    rw [h100, Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Real.log_pow]
    ring
  have h_log_3_40 : Real.log (3 / 40 : ℝ) = Real.log 3 - 3 * Real.log 2 - Real.log 5 := by
    have h40 : (3 / 40 : ℝ) = 3 / ((2 ^ 3 : ℝ) * (5 : ℝ)) := by norm_num
    rw [h40, Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    ring
  unfold b0Real b1Real b2Real b3Real
  rw [h_log_3_100, h_log_3_40]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by norm_num⟩

theorem theorem_6_5_ii_real_concavity_and_f_upper_at_67 :
    (∀ t : ℝ, 0 < t → t ≤ (1 / 11 : ℝ) → qConcavityReal t < (-141 / 1331 : ℝ)) ∧
    fUpperReal (1 / 67 : ℝ) < (-1362 / 10000 : ℝ) ∧
    (paramC0 : ℝ) ^ 2 * fUpperReal (1 / 67 : ℝ) < (-122 / 1000000 : ℝ) := by
  obtain ⟨hb0, hb1, hb2_pos, hb2, _⟩ := theorem_6_5_ii_real_b_coeff_bounds
  obtain ⟨_, _, _, ⟨_, h67_gt⟩⟩ := theorem_6_5_ii_real_log_enclosures
  refine ⟨?_, ?_, ?_⟩
  · intro t ht0 ht11
    unfold qConcavityReal b3Real
    have ht2 : t ^ 2 ≤ (1 / 11 : ℝ) ^ 2 := sq_le_sq.mpr (by rw [abs_of_pos ht0, abs_of_pos (by norm_num)]; exact ht11)
    have ht3 : t ^ 3 ≤ (1 / 11 : ℝ) ^ 3 := by nlinarith
    have h_b2_t2 : b2Real * t ^ 2 ≤ (4293731 / 100000 : ℝ) * (1 / 11 : ℝ) ^ 2 := by nlinarith
    linarith
  · unfold fUpperReal b3Real
    have h_log_inv : Real.log (1 / 67 : ℝ) = -Real.log 67 := by
      rw [one_div, Real.log_inv]
    rw [h_log_inv]
    linarith
  · unfold fUpperReal b3Real paramC0
    have h_log_inv : Real.log (1 / 67 : ℝ) = -Real.log 67 := by
      rw [one_div, Real.log_inv]
    rw [h_log_inv]
    push_cast
    linarith

/-- **Theorem 6.5(ii) Step (3) (Equation (6.24): Pure Rational Verification of Concavity &
Uniform Negativity `c_0^2 f_{upper}(1/67) < -0.000122 < 0`, p. 36)**:
Verifies in exact rational arithmetic:
1. `q(1/11) < -141/1331 < 0` (establishing strict concavity `f_{upper}''(t) < 0` on `(0, 1/11]`),
2. Using the certified rational logarithm enclosures from page 36
   `log 2 ∈ (6931471/10000000, 6931472/10000000)`,
   `log 3 ∈ (10986122/10000000, 10986123/10000000)`,
   `log 5 ∈ (16094379/10000000, 16094380/10000000)`,
   `log 67 > 6 * (6931471/10000000) + 6/131 > 4204684/1000000`,
   the maximum value at `n = 34` (`t_0 = 1/67`) satisfies `f_{upper}(1/67) < -0.1362 < 0`
   and `c_0^2 f_{upper}(1/67) < -0.000122 < 0`. -/
theorem theorem_6_5_ii_pure_rational_negativity_proof :
    let b0_ub : ℚ := 5118062 / 1000000
    let b1_ub : ℚ := -6255829 / 100000
    let b2_ub : ℚ := 4293731 / 100000
    let b3_ub : ℚ := 2984 / 9315
    let log67_lb : ℚ := 4204684 / 1000000
    let t0 : ℚ := 1 / 67
    let q_at_1_11 : ℚ := -1 + 2 * (1 / 11 : ℚ) + 2 * b2_ub * (1 / 11 : ℚ) ^ 2 + 6 * b3_ub * (1 / 11 : ℚ) ^ 3
    let f_upper_at_67_ub : ℚ :=
      -(1 + 2 * t0) * log67_lb + b0_ub + b1_ub * t0 + b2_ub * t0 ^ 2 + b3_ub * t0 ^ 3
    q_at_1_11 < -141 / 1331 ∧
    -141 / 1331 < (0 : ℚ) ∧
    f_upper_at_67_ub < -1362 / 10000 ∧
    paramC0 ^ 2 * f_upper_at_67_ub < -122 / 1000000 ∧
    -122 / 1000000 < (0 : ℚ) := by
  intro b0_ub b1_ub b2_ub b3_ub log67_lb t0 q_at_1_11 f_upper_at_67_ub
  unfold paramC0
  dsimp only [b0_ub, b1_ub, b2_ub, b3_ub, log67_lb, t0, q_at_1_11, f_upper_at_67_ub]
  norm_num

end OddZetaFormalization
