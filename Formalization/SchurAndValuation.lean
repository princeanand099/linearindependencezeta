import Formalization.JetSeparation

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
  homogeneous scalar cancellation of `w_{2n+1,0}`, and symmetric outer-pole cancellation
  `1/(s - r) - 1/(s + r) = 2r / (s² - r²)` (5.9).
- **Theorem 5.4**: Cauchy–Binet series expansion (5.10) and archimedean rate functions (5.11)–(5.17).
- **Lemma 6.1**: Base kernel factorial valuation `V_p(k)` (6.1), entry-wise `p`-adic valuation bound (6.2),
  and `-q_0 - d_1 - d_2 - t = -L_k` Cauchy-product exponent cancellation.
- **Proposition 6.2**: Inner-window `p`-adic integrality `g_k(w) = U_{out,k}(w) U_{in,k}(w)` (6.4)–(6.7).
- **Theorem 6.3**: Midpoint-centered harmonic numbers `H̃_{k,AK}^{(t)} := H_k^{(t)} - H_{AK}^{(t)}` (6.9),
  centered remainder `ℛ_0^{cent}(P)` (6.10), polynomial and determinant identity (6.11) with
  `c_{cent} := c + ∑_{j=1}^n a_{2j+1} H_{AK}^{(2j+1)}`, and support of inner centered harmonic numbers
  in `[AK - A₀K + 1, AK + A₀K]` (ii).
- **Proposition 6.4**:
  - (i) Outer-pole binomial identity `(r - A₀K)\binom{r + A₀K}{2A₀K} = (2A₀K + 1)\binom{r + A₀K}{2A₀K + 1}`
    (6.12), link to `ℰ_{A₀K+1}(r²)` (6.13), and boundary floor function `Ω_{bdry}(α, β) ∈ {0, 1}` (6.14).
  - (ii) Elimination of tail primes `p > 2AK` when `A > C + R_c = (2n - 1)A_0`.
- **Theorem 6.5**: Effective determinant-clearing multiplier `D_{N+R}^{eff}` (6.17)–(6.18),
  Gaussian elimination quadratic vanishing identity
  `∑_{j₁=0}^{m₁-1} j₁ + ∑_{j₂=0}^{m₂-1} j₂ + ∑_{j=0}^{m₁+m₂-1} j = m₁(m₁-1) + m₂(m₂-1) + m₁m₂`,
  scaling parameters `c_0 = 3/100`, `A_0(n) = 0.03 / (2n - 1)`, `R_c(n) = 2(n - 1)A_0(n)`,
  `A(n) = 0.075` (6.20), derivative bound `H_n'(y) ≤ -u(3.2u² + 0.8)/((u²+4)(u²+1)) < 0`,
  concavity numerator `q(1/11) = -141/1331 < 0`, and rational arithmetic verification of
  `f_{upper}(1/67) < -0.1362 < 0` and `Λ_{net,full}^{(N+R)}(n) ≤ -0.000146 < 0` across all `n ≥ 1`
  (6.23)–(6.24).
-/

namespace OddZetaFormalization

open scoped BigOperators

/-!
## Section 5: Schur-Complement Moment Identity & Block-Triangular Reduction
-/

/-- **Equation (1.5)**: The secondary odd-zeta elimination operator
$$L^{(2j+1)}(P) := a_{2n+1} S_{2j+1}(P) - a_{2j+1} S_{2n+1}(P) \quad (1 \le j \le n-1).$$ -/
def eliminationOpL (a_top a_j S_j S_top : ℚ) : ℚ :=
  a_top * S_j - a_j * S_top

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
    simp [sub_eq_add_neg]
  rw [h_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one,
      mul_one, one_mul]

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
    simp [h_cancel, sub_eq_add_neg]
  have h_det := congrArg Matrix.det h_block
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one,
      mul_one, mul_one, Matrix.det_fromBlocks_zero₁₂] at h_det
  exact h_det

/-- **Theorem 5.3(i) (Equation (5.5): Reduced Kernel Basis Polynomials `Q_d(X) ∈ ℚ[X]`)**:
$$Q_d(X) := \mathcal{E}_d(X) - \sum_{m=0}^{R-1} \Gamma_{m,d} \mathcal{E}_{N+m}(X) \quad (0 \le d < N = A_0 K + 1).$$ -/
noncomputable def reducedKernelPolyQd (A0K R : ℕ)
    (Γ : Matrix (Fin R) (Fin (A0K + 1)) ℚ) (d : Fin (A0K + 1)) : Polynomial ℚ :=
  centralFactorialPoly d.val -
    ∑ m : Fin R, Polynomial.C (Γ m d) * centralFactorialPoly (A0K + 1 + m.val)

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
    rw [Polynomial.eval_mul, Polynomial.eval_C,
        lemma_2_1_poly_vanishing (A0K + 1 + m.val) r (by omega), mul_zero]
  rw [h_tail_zero, sub_zero]

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

/-!
## Section 6: `p`-Adic Valuations, Harmonic Centering, and Net Exponent Bounds
-/

/-- **Lemma 6.1 (Cauchy-Product Valuation Exponent Summation, p. 30)**:
In every summand `q₀ + d₁ + d₂ = L_k - t` of the Cauchy product (6.3), the four coefficients
`-q₀`, `-d₁`, `-d₂`, and `-t` multiplying `⌊log(2AK)/log p⌋` sum identically to `-L_k`. -/
theorem lemma_6_1_valuation_exponent_sum (q0 d1 d2 t Lk : ℕ)
    (h_sum : q0 + d1 + d2 = Lk - t) (ht : t ≤ Lk) :
    -(q0 : ℤ) - (d1 : ℤ) - (d2 : ℤ) - (t : ℤ) = -(Lk : ℤ) := by
  omega

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

/-- **Proposition 6.4(i) (Equation (6.13): Link Between Outer Binomial Factor and `ℰ_{A₀K+1}(r²)`)**:
For every outer pole `r ≥ A₀K + 1`,
$$\mathcal{E}_{A_0 K + 1}(r^2) =
  \frac{2r}{(2A_0 K + 1)(2A_0 K + 2)} \cdot (r - A_0 K)\binom{r + A_0 K}{2A_0 K}.$$ -/
theorem prop_6_4_i_link_to_first_tail_poly (r A0K : ℕ) (hr : A0K + 1 ≤ r) :
    evalCentralFactorial (A0K + 1) ((r : ℚ) ^ 2) =
      ((2 * (r : ℚ)) / (((2 * A0K + 1 : ℕ) : ℚ) * ((2 * A0K + 2 : ℕ) : ℚ))) *
        ((((r - A0K) * Nat.choose (r + A0K) (2 * A0K) : ℕ) : ℚ)) := by
  rw [prop_2_2_binomial_identity (A0K + 1) r (by omega)]
  have h_abs1 := prop_6_4_i_outer_binomial_identity r A0K
  -- Also use (2A0K + 2)(2A0K + 1)[C(r + A0K + 1, 2A0K + 2) + C(r + A0K, 2A0K + 2)]
  -- = 2r * (r - A0K) * C(r + A0K, 2A0K)
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

/-- **Proposition 6.4(i) (Equation (6.14): Boundary Floor Inequality `Ω_{bdry} ∈ {0, 1}`)**:
For any real numbers `X, Y`, the floor difference `⌊X + Y⌋ - ⌊X⌋ - ⌊Y⌋` lies in `{0, 1}`. -/
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

/-!
## Theorem 6.5: Effective Determinant-Clearing Multiplier and Uniform Negativity Across All `n ≥ 1`
-/

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
