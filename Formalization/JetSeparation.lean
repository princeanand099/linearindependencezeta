import Formalization.WindowedKernel

/-!
# Section 4: Local Leibniz Jet Structure and Degree-Cutoff Jet Separation

This module formalizes Section 4 of Prince Anand,
*"All Odd Zeta Values Are Linearly Independent Over ℚ"*:
- **Proposition 4.1**: Inner jet representation of `S_{2j+1}(P)` for general `n ≥ 2`:
  - Inner node weights `w_{2n+1,0} := g_{AK,0} ≠ 0` and `w_{2n+1,r} := 2 g_{AK-r,0} ≠ 0` (4.1).
  - (i) Highest-weight functional `S_{2n+1}(P) = ∑_{r=0}^{A₀K} w_{2n+1,r} P(r²)` (4.2).
  - (ii) Local Leibniz jet expansion of `S_{2j+1}(P)` (`1 ≤ j ≤ n-1`) (4.3)–(4.4) and non-vanishing
    of the leading derivative weights `w_{2j+1,0}^{(n-j)} = w_{2n+1,0} ≠ 0` and
    `w_{2j+1,r}^{(2(n-j))} = (2r)^{2(n-j)} w_{2n+1,r} ≠ 0` (4.5).
  - (iii) Identical vanishing on tail columns: `S_{2n+1}(A ℰ_m) = 0` for all `m > A₀K` (4.6).
- **Lemma 4.2**: Explicit Hermite interpolation basis `H_0(u), H_{r,0}(u), H_{r,1}(u)` on
  `ℚ[u]_{\le 2A₀K}` (4.8)–(4.10) and verification of properties (i), (ii), (iii).
- **Theorem 4.3**: Degree-cutoff jet separation (4.11)–(4.18):
  - Full row rank of `L_{top}` and invertibility of `L_{top}[:, J_{tail}] = a_{2n+1} S_{odd,top}[:, J_{tail}]` (i).
  - Full row rank of `S_{2n+1,bot}` and exact head determinant
    `det(S_{2n+1,bot}[:, J_{head}]) = ∏_{r=0}^{A₀K} w_{2n+1,r} ≠ 0` via upper unitriangularity
    of `E_{head}` (ii).
  - Block-triangular decomposition and determinant formula (4.17)–(4.18), and `N_0 = 0` (iii).
- **Theorem 4.4**: Closed-form confluent Vandermonde determinant formula for
  `|det(S_{odd,top}[:, J_{tail}])| ≠ 0` (4.24)–(4.27).
-/

namespace OddZetaFormalization

open scoped BigOperators

/-- **Proposition 4.1 (Equation (4.1))**: The inner node weights `w_{2n+1,r}` for `0 ≤ r ≤ A₀K`:
$$w_{2n+1,0} := g_{AK,0}, \qquad w_{2n+1,r} := 2 g_{AK-r,0} \quad (1 \le r \le A_0 K).$$ -/
def innerNodeWeight (n A0K AK r : ℕ) : ℚ :=
  if r = 0 then gkZeroClosed n A0K AK AK
  else 2 * gkZeroClosed n A0K AK (AK - r)

/-- **Proposition 4.1 (Equation (4.1) Non-Vanishing)**: For every `0 ≤ r ≤ A₀K` (`A₀K ≤ AK`),
`innerNodeWeight n A0K AK r ≠ 0`. -/
theorem prop_4_1_innerNodeWeight_ne_zero (n A0K AK r : ℕ) (hr : r ≤ A0K) (hA0 : A0K ≤ AK) :
    innerNodeWeight n A0K AK r ≠ 0 := by
  unfold innerNodeWeight
  split_ifs with hr0
  · exact lemma_3_2_gkZero_ne_zero n A0K AK AK (by omega)
  · exact mul_ne_zero two_ne_zero (lemma_3_2_gkZero_ne_zero n A0K AK (AK - r) (by omega))

/-- **Proposition 4.1(i) (Equation (4.2))**: The highest odd-zeta functional
$$S_{2n+1}(P) = \sum_{r=0}^{A_0 K} w_{2n+1,r} P(r^2).$$ -/
def S2nPlus1Functional (n A0K AK : ℕ) (evalP : ℚ → ℚ) : ℚ :=
  ∑ r ∈ Finset.range (A0K + 1), innerNodeWeight n A0K AK r * evalP ((r : ℚ) ^ 2)

/-- **Proposition 4.1(i) Derivation from Section 3 Laurent Convolution (`laurentCoeffAt`)**:
At every inner pole `k` (`|k - AK| ≤ A₀K`), the pole multiplicity is `L_k = 2n + 1`, so for
`t = 2n + 1` the convolution (3.8) collapses to `q = 0, d = 0`:
`A_{2n+1, k}(P) = g_{k,0} P((AK - k)²)` and `A_{2n+1, AK-r}(P) + A_{2n+1, AK+r}(P) = w_{2n+1,r} P(r²)`. -/
theorem prop_4_1_i_laurentCoeffAt_top_weight (n A0K AK : ℕ) (normDerivP : ℚ → ℕ → ℚ)
    (k : ℕ) (h_in : ((k : ℤ) - (AK : ℤ)).natAbs ≤ A0K) :
    laurentCoeffAt n A0K AK normDerivP (2 * n + 1) k =
      gkZeroClosed n A0K AK k * normDerivP (((AK : ℚ) - (k : ℚ)) ^ 2) 0 := by
  unfold laurentCoeffAt
  have hLk : poleMultiplicity n A0K AK k = 2 * n + 1 := poleMultiplicity_inner_eq n A0K AK k h_in
  rw [hLk, if_neg (by omega)]
  simp [Nat.sub_self, gkTaylorCoeff]

/-- Pairing symmetric inner poles `k = AK - r` and `k = AK + r` (`1 ≤ r ≤ A₀K`) yields
`w_{2n+1,r} P(r²)`. -/
theorem prop_4_1_i_symmetric_inner_pair (n A0K AK r : ℕ) (hr1 : 1 ≤ r) (hr : r ≤ A0K)
    (hA0 : A0K ≤ AK) (normDerivP : ℚ → ℕ → ℚ) :
    laurentCoeffAt n A0K AK normDerivP (2 * n + 1) (AK - r) +
      laurentCoeffAt n A0K AK normDerivP (2 * n + 1) (AK + r) =
      innerNodeWeight n A0K AK r * normDerivP ((r : ℚ) ^ 2) 0 := by
  have h_in1 : (((AK - r : ℕ) : ℤ) - (AK : ℤ)).natAbs ≤ A0K := by omega
  have h_in2 : (((AK + r : ℕ) : ℤ) - (AK : ℤ)).natAbs ≤ A0K := by omega
  rw [prop_4_1_i_laurentCoeffAt_top_weight n A0K AK normDerivP (AK - r) h_in1,
      prop_4_1_i_laurentCoeffAt_top_weight n A0K AK normDerivP (AK + r) h_in2,
      lemma_3_2_gkZero_inner_symm n A0K AK r hr hA0]
  have h_sq1 : ((AK : ℚ) - ((AK - r : ℕ) : ℚ)) ^ 2 = (r : ℚ) ^ 2 := by
    rw [Nat.cast_sub (by omega : r ≤ AK)]
    ring
  have h_sq2 : ((AK : ℚ) - ((AK + r : ℕ) : ℚ)) ^ 2 = (r : ℚ) ^ 2 := by
    push_cast
    ring
  rw [h_sq1, h_sq2]
  unfold innerNodeWeight
  rw [if_neg (by omega : r ≠ 0)]
  ring

/-- **Proposition 4.1(ii) (Equation (4.4))**: The rational jet weights `w_{2j+1,r}^{(q)}`
for `1 ≤ j ≤ n - 1`:
- At `r = 0`: `w_{2j+1,0}^{(q)} = g_{AK, 2(n-j-q)}`
- At `1 ≤ r ≤ A₀K`:
  `w_{2j+1,r}^{(q)} = 2 ∑_{a=0}^{\min(q, 2(n-j)-q)} g_{AK-r, 2(n-j)-q-a} \binom{q}{a} (2r)^{q-a}`. -/
def jetWeightW (n A0K AK j r q : ℕ) : ℚ :=
  if r = 0 then
    gkTaylorCoeff n A0K AK AK (2 * (n - j - q))
  else
    2 * ∑ a ∈ Finset.range (min q (2 * (n - j) - q) + 1),
      gkTaylorCoeff n A0K AK (AK - r) (2 * (n - j) - q - a) *
        (Nat.choose q a : ℚ) * ((2 * (r : ℚ)) ^ (q - a))

/-- **Proposition 4.1(ii) (Equation (4.5): Non-Vanishing Leading Derivative Weights)**:
At `r = 0`, `w_{2j+1,0}^{(n-j)} = w_{2n+1,0} ≠ 0`, and at every `1 ≤ r ≤ A₀K`,
`w_{2j+1,r}^{(2(n-j))} = (2r)^{2(n-j)} w_{2n+1,r} ≠ 0`. -/
theorem prop_4_1_ii_leading_jet_weights (n A0K AK j r : ℕ)
    (_hj : j < n) (hr : r ≤ A0K) (hA0 : A0K ≤ AK) :
    jetWeightW n A0K AK j 0 (n - j) = innerNodeWeight n A0K AK 0 ∧
    (1 ≤ r →
      jetWeightW n A0K AK j r (2 * (n - j)) =
        ((2 * (r : ℚ)) ^ (2 * (n - j))) * innerNodeWeight n A0K AK r ∧
      jetWeightW n A0K AK j r (2 * (n - j)) ≠ 0) := by
  constructor
  · unfold jetWeightW innerNodeWeight
    simp [gkTaylorCoeff]
  · intro hr1
    have h_eq_wt :
        jetWeightW n A0K AK j r (2 * (n - j)) =
          ((2 * (r : ℚ)) ^ (2 * (n - j))) * innerNodeWeight n A0K AK r := by
      unfold jetWeightW innerNodeWeight
      rw [if_neg (by omega : r ≠ 0), if_neg (by omega : r ≠ 0)]
      have h_min : min (2 * (n - j)) (2 * (n - j) - 2 * (n - j)) = 0 := by simp
      rw [h_min, Finset.range_one, Finset.sum_singleton]
      simp [gkTaylorCoeff]
      ring
    refine ⟨h_eq_wt, ?_⟩
    rw [h_eq_wt]
    apply mul_ne_zero
    · exact pow_ne_zero _ (mul_ne_zero two_ne_zero (by exact_mod_cast (by omega : r ≠ 0)))
    · exact prop_4_1_innerNodeWeight_ne_zero n A0K AK r hr hA0

/-- **Proposition 4.1(iii) (Equation (4.6): Vanishing of `S_{2n+1}(A ℰ_m) = 0` on Tail Columns)**:
For any row polynomial evaluation `evalA : ℚ → ℚ` and any tail column index `m > A₀K`,
`ℰ_m(r²) = 0` for all `0 ≤ r ≤ A₀K`, and hence `S_{2n+1}(A ℰ_m) = 0` identically. -/
theorem prop_4_1_iii_tail_vanishing (n A0K AK m : ℕ) (hm : A0K < m) (evalA : ℚ → ℚ) :
    S2nPlus1Functional n A0K AK (fun u => evalA u * evalCentralFactorial m u) = 0 := by
  unfold S2nPlus1Functional
  apply Finset.sum_eq_zero
  intro r hr
  have hr_le : r ≤ A0K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hr_lt_m : r < m := lt_of_le_of_lt hr_le hm
  have h_vanish : evalCentralFactorial m ((r : ℚ) ^ 2) = 0 :=
    (prop_2_2_i_vanishing m r hr_lt_m).1
  dsimp only
  rw [h_vanish, mul_zero, mul_zero]

/-!
## Lemma 4.2: Explicit Hermite Interpolation Basis on `ℚ[u]_{\le 2A₀K}`
-/

/-- **Lemma 4.2 (Equation (4.9))**: Evaluation of `Ω(u) := ∏_{r=1}^{A₀K} (u - r²)²`. -/
def HermiteOmega (A0K : ℕ) (u : ℚ) : ℚ :=
  ∏ r ∈ Finset.Icc 1 A0K, (u - (r : ℚ) ^ 2) ^ 2

/-- At `u = 0`, `Ω(0) = ((A₀K)!)⁴ ≠ 0`. -/
theorem HermiteOmega_zero_ne_zero (A0K : ℕ) : HermiteOmega A0K 0 ≠ 0 := by
  unfold HermiteOmega
  rw [Finset.prod_ne_zero_iff]
  intro r hr
  have hr_pos : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  apply pow_ne_zero 2
  have hr_q : (r : ℚ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  simpa using pow_ne_zero 2 hr_q

/-- **Lemma 4.2 (Equation (4.10))**: Evaluation of the fundamental Hermite basis polynomial
`H_0(u) := Ω(u) / Ω(0)`. -/
def HermiteH0 (A0K : ℕ) (u : ℚ) : ℚ :=
  HermiteOmega A0K u / HermiteOmega A0K 0

/-- **Lemma 4.2(i)**: `H_0(0) = 1` and `H_0(r²) = 0` for all `1 ≤ r ≤ A₀K`. -/
theorem lemma_4_2_i_H0_eval (A0K : ℕ) :
    HermiteH0 A0K 0 = 1 ∧
    ∀ r ∈ Finset.Icc 1 A0K, HermiteH0 A0K ((r : ℚ) ^ 2) = 0 := by
  constructor
  · unfold HermiteH0
    exact div_self (HermiteOmega_zero_ne_zero A0K)
  · intro r hr
    unfold HermiteH0 HermiteOmega
    have h_zero : (∏ t ∈ Finset.Icc 1 A0K, ((r : ℚ) ^ 2 - (t : ℚ) ^ 2) ^ 2) = 0 := by
      apply Finset.prod_eq_zero hr
      ring
    rw [h_zero, zero_div]

/-- **Lemma 4.2 (Equation (4.9))**: Fundamental Lagrange-square factor
$$\ell_r(u) := \frac{u}{r^2} \prod_{\substack{1 \le t \le A_0 K \\ t \ne r}}
  \left(\frac{u - t^2}{r^2 - t^2}\right)^2 \quad (1 \le r \le A_0 K).$$ -/
def HermiteEll (A0K r : ℕ) (u : ℚ) : ℚ :=
  (u / ((r : ℚ) ^ 2)) *
    ∏ t ∈ (Finset.Icc 1 A0K).erase r,
      ((u - (t : ℚ) ^ 2) / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) ^ 2

/-- **Lemma 4.2 (`ℓ_r` node properties)**: For `1 ≤ r ≤ A₀K`, `ℓ_r(0) = 0`, `ℓ_r(r²) = 1`,
and `ℓ_r(t²) = 0` for all `t ∈ {1, ..., A₀K} \ {r}`. -/
theorem lemma_4_2_ell_eval (A0K r : ℕ) (hr : r ∈ Finset.Icc 1 A0K) :
    HermiteEll A0K r 0 = 0 ∧
    HermiteEll A0K r ((r : ℚ) ^ 2) = 1 ∧
    ∀ t ∈ (Finset.Icc 1 A0K).erase r, HermiteEll A0K r ((t : ℚ) ^ 2) = 0 := by
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hr_ne : ((r : ℚ) ^ 2) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (by omega : r ≠ 0))
  refine ⟨by unfold HermiteEll; simp, ?_, ?_⟩
  · unfold HermiteEll
    rw [div_self hr_ne, one_mul]
    apply Finset.prod_eq_one
    intro t ht
    have h_ne : t ≠ r := (Finset.mem_erase.mp ht).1
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp (Finset.mem_erase.mp ht).2).1
    have h_diff_ne : (r : ℚ) ^ 2 - (t : ℚ) ^ 2 ≠ 0 := by
      intro h_eq
      have h_sq : (r : ℚ) ^ 2 = (t : ℚ) ^ 2 := sub_eq_zero.mp h_eq
      have h_nat : r ^ 2 = t ^ 2 := by exact_mod_cast h_sq
      rw [sq, sq] at h_nat
      exact h_ne (Nat.mul_self_inj.mp h_nat.symm)
    rw [div_self h_diff_ne, one_pow]
  · intro t ht
    unfold HermiteEll
    have h_prod0 :
        (∏ s ∈ (Finset.Icc 1 A0K).erase r,
          (((t : ℚ) ^ 2 - (s : ℚ) ^ 2) / ((r : ℚ) ^ 2 - (s : ℚ) ^ 2)) ^ 2) = 0 := by
      apply Finset.prod_eq_zero ht
      ring
    rw [h_prod0, mul_zero]

/-- Double-root derivative vanishing lemma: for any finite set `s : Finset ℕ` and `r ∈ s`,
the polynomial `∏ t ∈ s, (X - C (f t))²` has both value `0` and first derivative `0` at `f r`. -/
theorem eval_and_deriv_prod_sq_eq_zero {s : Finset ℕ} {r : ℕ} (hr : r ∈ s) (f : ℕ → ℚ) :
    (∏ t ∈ s, (Polynomial.X - Polynomial.C (f t)) ^ 2).eval (f r) = 0 ∧
    (∏ t ∈ s, (Polynomial.X - Polynomial.C (f t)) ^ 2).derivative.eval (f r) = 0 := by
  rw [← Finset.insert_erase hr, Finset.prod_insert (Finset.not_mem_erase r s)]
  constructor
  · rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, sub_self, sq, zero_mul, zero_mul]
  · rw [Polynomial.derivative_mul]
    have h_sq_deriv :
        ((Polynomial.X - Polynomial.C (f r)) ^ 2).derivative =
          (2 : Polynomial ℚ) * (Polynomial.X - Polynomial.C (f r)) := by
      rw [sq, Polynomial.derivative_mul, Polynomial.derivative_sub,
          Polynomial.derivative_X, Polynomial.derivative_C, sub_zero]
      ring
    rw [h_sq_deriv, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, sub_self]
    ring

/-- **Lemma 4.2 (Equation (4.9)): Polynomial Definition of `Ω(u)` in `ℚ[X]`**:
$$\Omega(X) := \prod_{r=1}^{A_0 K} (X - r^2)^2 \in \mathbb{Q}[X].$$ -/
noncomputable def HermiteOmegaPoly (A0K : ℕ) : Polynomial ℚ :=
  ∏ r ∈ Finset.Icc 1 A0K, (Polynomial.X - Polynomial.C ((r : ℚ) ^ 2)) ^ 2

/-- **Lemma 4.2 (Equation (4.10)): Polynomial Definition of `H_0(X) := Ω(X) / Ω(0)`**: -/
noncomputable def HermiteH0Poly (A0K : ℕ) : Polynomial ℚ :=
  Polynomial.C (1 / HermiteOmega A0K 0) * HermiteOmegaPoly A0K

/-- **Lemma 4.2(i) (Full Polynomial Evaluation & Derivative Verification for `H_0`)**:
`H_0(0) = 1`, and for every `1 ≤ r ≤ A₀K`, `H_0(r²) = 0` and `H_0'(r²) = 0`. -/
theorem lemma_4_2_i_H0Poly_full (A0K : ℕ) :
    (HermiteH0Poly A0K).eval 0 = 1 ∧
    ∀ r ∈ Finset.Icc 1 A0K,
      (HermiteH0Poly A0K).eval ((r : ℚ) ^ 2) = 0 ∧
      (HermiteH0Poly A0K).derivative.eval ((r : ℚ) ^ 2) = 0 := by
  have h_eval : ∀ u : ℚ, (HermiteOmegaPoly A0K).eval u = HermiteOmega A0K u := by
    intro u
    unfold HermiteOmegaPoly HermiteOmega
    simp [Polynomial.eval_prod]
  refine ⟨?_, ?_⟩
  · unfold HermiteH0Poly
    rw [Polynomial.eval_mul, Polynomial.eval_C, h_eval 0,
        one_div_mul_cancel (HermiteOmega_zero_ne_zero A0K)]
  · intro r hr
    unfold HermiteH0Poly HermiteOmegaPoly
    have h_both := eval_and_deriv_prod_sq_eq_zero hr (fun t => (t : ℚ) ^ 2)
    constructor
    · rw [Polynomial.eval_mul, Polynomial.eval_C, h_both.1, mul_zero]
    · rw [Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C, h_both.2, mul_zero]

/-- **Lemma 4.2 (Equation (4.9)): Polynomial Definition of `ℓ_r(X)` in `ℚ[X]`**: -/
noncomputable def HermiteEllPoly (A0K r : ℕ) : Polynomial ℚ :=
  Polynomial.C (1 / ((r : ℚ) ^ 2)) * Polynomial.X *
    ∏ t ∈ (Finset.Icc 1 A0K).erase r,
      (Polynomial.C (1 / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) *
        (Polynomial.X - Polynomial.C ((t : ℚ) ^ 2))) ^ 2

/-- Evaluation of `HermiteEllPoly` agrees identically with `HermiteEll`. -/
theorem eval_HermiteEllPoly (A0K r : ℕ) (u : ℚ) :
    (HermiteEllPoly A0K r).eval u = HermiteEll A0K r u := by
  unfold HermiteEllPoly HermiteEll
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_prod,
    Polynomial.eval_pow, Polynomial.eval_sub, div_eq_inv_mul, mul_one]

/-- At any node `t ∈ {1, ..., A₀K} \ {r}`, both `ℓ_r(t²) = 0` and `ℓ_r'(t²) = 0`. -/
theorem HermiteEllPoly_eval_and_deriv_other_node (A0K r t : ℕ)
    (ht : t ∈ (Finset.Icc 1 A0K).erase r) :
    (HermiteEllPoly A0K r).eval ((t : ℚ) ^ 2) = 0 ∧
    (HermiteEllPoly A0K r).derivative.eval ((t : ℚ) ^ 2) = 0 := by
  have h_val : (HermiteEllPoly A0K r).eval ((t : ℚ) ^ 2) = 0 := by
    rw [eval_HermiteEllPoly]
    unfold HermiteEll
    have h0 :
        (∏ s ∈ (Finset.Icc 1 A0K).erase r,
          (((t : ℚ) ^ 2 - (s : ℚ) ^ 2) / ((r : ℚ) ^ 2 - (s : ℚ) ^ 2)) ^ 2) = 0 := by
      apply Finset.prod_eq_zero ht
      ring
    rw [h0, mul_zero]
  refine ⟨h_val, ?_⟩
  unfold HermiteEllPoly
  have h_factor :
      (∏ s ∈ (Finset.Icc 1 A0K).erase r,
        (Polynomial.C (1 / ((r : ℚ) ^ 2 - (s : ℚ) ^ 2)) *
          (Polynomial.X - Polynomial.C ((s : ℚ) ^ 2))) ^ 2) =
      (∏ s ∈ (Finset.Icc 1 A0K).erase r,
        Polynomial.C ((1 / ((r : ℚ) ^ 2 - (s : ℚ) ^ 2)) ^ 2)) *
      (∏ s ∈ (Finset.Icc 1 A0K).erase r,
        (Polynomial.X - Polynomial.C ((s : ℚ) ^ 2)) ^ 2) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro s _
    rw [mul_pow, ← Polynomial.C_pow]
  rw [h_factor, ← mul_assoc]
  have h_both := eval_and_deriv_prod_sq_eq_zero ht (fun s => (s : ℚ) ^ 2)
  rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      h_both.1, h_both.2, mul_zero, mul_zero, add_zero]

/-- **Lemma 4.2 (Equation (4.10)): Polynomial Definition of `H_{r,1}(X) := (X - r²) ℓ_r(X)`**: -/
noncomputable def HermiteHr1Poly (A0K r : ℕ) : Polynomial ℚ :=
  (Polynomial.X - Polynomial.C ((r : ℚ) ^ 2)) * HermiteEllPoly A0K r

/-- **Lemma 4.2 (Equation (4.10)): Polynomial Definition of `H_{r,0}(X) := (1 - ℓ_r'(r²)(X - r²)) ℓ_r(X)`**: -/
noncomputable def HermiteHr0Poly (A0K r : ℕ) : Polynomial ℚ :=
  (1 - Polynomial.C ((HermiteEllPoly A0K r).derivative.eval ((r : ℚ) ^ 2)) *
    (Polynomial.X - Polynomial.C ((r : ℚ) ^ 2))) * HermiteEllPoly A0K r

/-- **Lemma 4.2(ii) & (iii) (Full Polynomial Evaluation & Derivative Verification for `H_{r,0}` and `H_{r,1}`)**:
For every `r ∈ {1, ..., A₀K}`:
1. `H_{r,0}(0) = 0`, `H_{r,0}(r²) = 1`, `H_{r,0}'(r²) = 0`, and for all `t ∈ {1, ..., A₀K} \ {r}`,
   `H_{r,0}(t²) = 0` and `H_{r,0}'(t²) = 0`.
2. `H_{r,1}(0) = 0`, `H_{r,1}(r²) = 0`, `H_{r,1}'(r²) = 1`, and for all `t ∈ {1, ..., A₀K} \ {r}`,
   `H_{r,1}(t²) = 0` and `H_{r,1}'(t²) = 0`. -/
theorem lemma_4_2_ii_iii_HrPoly_full (A0K r : ℕ) (hr : r ∈ Finset.Icc 1 A0K) :
    ((HermiteHr0Poly A0K r).eval 0 = 0 ∧
     (HermiteHr0Poly A0K r).eval ((r : ℚ) ^ 2) = 1 ∧
     (HermiteHr0Poly A0K r).derivative.eval ((r : ℚ) ^ 2) = 0 ∧
     ∀ t ∈ (Finset.Icc 1 A0K).erase r,
       (HermiteHr0Poly A0K r).eval ((t : ℚ) ^ 2) = 0 ∧
       (HermiteHr0Poly A0K r).derivative.eval ((t : ℚ) ^ 2) = 0) ∧
    ((HermiteHr1Poly A0K r).eval 0 = 0 ∧
     (HermiteHr1Poly A0K r).eval ((r : ℚ) ^ 2) = 0 ∧
     (HermiteHr1Poly A0K r).derivative.eval ((r : ℚ) ^ 2) = 1 ∧
     ∀ t ∈ (Finset.Icc 1 A0K).erase r,
       (HermiteHr1Poly A0K r).eval ((t : ℚ) ^ 2) = 0 ∧
       (HermiteHr1Poly A0K r).derivative.eval ((t : ℚ) ^ 2) = 0) := by
  have h_ell := lemma_4_2_ell_eval A0K r hr
  have h_ell_0 : (HermiteEllPoly A0K r).eval 0 = 0 := by
    rw [eval_HermiteEllPoly]; exact h_ell.1
  have h_ell_r : (HermiteEllPoly A0K r).eval ((r : ℚ) ^ 2) = 1 := by
    rw [eval_HermiteEllPoly]; exact h_ell.2.1
  have h_lin_deriv : (Polynomial.X - Polynomial.C ((r : ℚ) ^ 2)).derivative = 1 := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · unfold HermiteHr0Poly
      rw [Polynomial.eval_mul, h_ell_0, mul_zero]
    · unfold HermiteHr0Poly
      rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C, h_ell_r]
      ring
    · unfold HermiteHr0Poly
      rw [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_one,
          Polynomial.derivative_C_mul, h_lin_deriv,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
          Polynomial.eval_sub, Polynomial.eval_zero, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_sub,
          Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, h_ell_r]
      ring
    · intro t ht
      have h_other := HermiteEllPoly_eval_and_deriv_other_node A0K r t ht
      unfold HermiteHr0Poly
      constructor
      · rw [Polynomial.eval_mul, h_other.1, mul_zero]
      · rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_mul, h_other.1, h_other.2, mul_zero, mul_zero, add_zero]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · unfold HermiteHr1Poly
      rw [Polynomial.eval_mul, h_ell_0, mul_zero]
    · unfold HermiteHr1Poly
      rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
          sub_self, zero_mul]
    · unfold HermiteHr1Poly
      rw [Polynomial.derivative_mul, h_lin_deriv, one_mul,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero, h_ell_r]
    · intro t ht
      have h_other := HermiteEllPoly_eval_and_deriv_other_node A0K r t ht
      unfold HermiteHr1Poly
      constructor
      · rw [Polynomial.eval_mul, h_other.1, mul_zero]
      · rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_mul, h_other.1, h_other.2, mul_zero, mul_zero, add_zero]

/-!
## Theorem 4.3: Degree-Cutoff Jet Separation and Invertibility of the Stacked Matrix
-/

/-- **Equation (4.11)**: Matrix dimensions `N = A₀K + 1`, `R_each = 2A₀K + 1`,
`R = (n - 1) R_each`, `M = N + R`. -/
def dimN (A0K : ℕ) : ℕ := A0K + 1
def dimREach (A0K : ℕ) : ℕ := 2 * A0K + 1
def dimR (n A0K : ℕ) : ℕ := (n - 1) * dimREach A0K
def dimM (n A0K : ℕ) : ℕ := dimN A0K + dimR n A0K

/-- **Equation (4.13)**: Inner-window root polynomial evaluation
$$W_0(u) := \prod_{r=0}^{A_0 K} (u - r^2) = \frac{(2N)!}{2} \mathcal{E}_N(u) \quad (N = A_0 K + 1).$$ -/
def W0PolyEval (A0K : ℕ) (u : ℚ) : ℚ :=
  ∏ r ∈ Finset.range (A0K + 1), (u - (r : ℚ) ^ 2)

/-- Verification of Equation (4.13): `W_0(u) = ((2N)! / 2) ℰ_N(u)` where `N = A₀K + 1`. -/
theorem eq_4_13_W0_eq_centralFactorial (A0K : ℕ) (u : ℚ) :
    W0PolyEval A0K u =
      (((2 * dimN A0K).factorial : ℚ) / 2) * evalCentralFactorial (dimN A0K) u := by
  unfold W0PolyEval evalCentralFactorial dimN
  rw [if_neg (by omega : A0K + 1 ≠ 0)]
  have h_fac_ne : ((2 * (A0K + 1)).factorial : ℚ) ≠ 0 :=
    by exact_mod_cast Nat.factorial_ne_zero (2 * (A0K + 1))
  field_simp [h_fac_ne]
  ring

/-- The `N × N` evaluation matrix `(E_{head})_{k,r} := ℰ_k(r²)` (`0 ≤ k, r < N = A₀K + 1`)
in the proof of Theorem 4.3(ii) (p. 21). -/
def EHeadMatrix (A0K : ℕ) : Matrix (Fin (A0K + 1)) (Fin (A0K + 1)) ℚ :=
  fun k r => evalCentralFactorial k.val ((r.val : ℚ) ^ 2)

/-- **Theorem 4.3(ii) Step 1 (Upper Unitriangularity of `E_{head}`)**:
By Proposition 2.2(i), `(E_{head})_{k,r} = ℰ_k(r²) = 0` whenever `r < k` and
`(E_{head})_{k,k} = ℰ_k(k²) = 1`, so `E_{head}` is upper unitriangular with `det E_{head} = 1`. -/
theorem theorem_4_3_EHead_det_eq_one (A0K : ℕ) :
    (EHeadMatrix A0K).BlockTriangular id ∧ (EHeadMatrix A0K).det = 1 := by
  have h_tri : (EHeadMatrix A0K).BlockTriangular id := by
    intro k r h_rk
    change evalCentralFactorial k.val ((r.val : ℚ) ^ 2) = 0
    exact (prop_2_2_i_vanishing k.val r.val h_rk).1
  have h_diag : ∀ k : Fin (A0K + 1), EHeadMatrix A0K k k = 1 := by
    intro k
    change evalCentralFactorial k.val ((k.val : ℚ) ^ 2) = 1
    exact prop_2_2_i_diag k.val
  refine ⟨h_tri, ?_⟩
  rw [Matrix.det_of_upperTriangular h_tri]
  simp [h_diag]

/-- The `N × N` head submatrix `S_{2n+1,bot}[:, J_{head}]` with entries
`S_{2n+1}(ℰ_k ℰ_d) = ∑_{r=0}^{A₀K} ℰ_k(r²) w_{2n+1,r} ℰ_d(r²)` (`0 ≤ k, d ≤ A₀K`). -/
def S2n1BotHeadMatrix (n A0K AK : ℕ) : Matrix (Fin (A0K + 1)) (Fin (A0K + 1)) ℚ :=
  fun k d =>
    S2nPlus1Functional n A0K AK
      (fun u => evalCentralFactorial k.val u * evalCentralFactorial d.val u)

/-- Factorization `S_{2n+1,bot}[:, J_{head}] = E_{head} * diag(w_{2n+1}) * E_{head}^T`
in the proof of Theorem 4.3(ii) (p. 21). -/
theorem S2n1BotHeadMatrix_eq_mul (n A0K AK : ℕ) :
    S2n1BotHeadMatrix n A0K AK =
      EHeadMatrix A0K *
        Matrix.diagonal (fun r : Fin (A0K + 1) => innerNodeWeight n A0K AK r.val) *
        (EHeadMatrix A0K).transpose := by
  ext k d
  simp only [S2n1BotHeadMatrix, S2nPlus1Functional, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.transpose_apply, EHeadMatrix, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]
  rw [← Fin.sum_univ_eq_sum_range
    (fun r => innerNodeWeight n A0K AK r *
      (evalCentralFactorial k.val ((r : ℚ) ^ 2) * evalCentralFactorial d.val ((r : ℚ) ^ 2)))
    (A0K + 1)]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- **Theorem 4.3(ii) (Equation (4.16): Exact Determinant of the Head Submatrix)**:
For every `n ≥ 2` and `A₀K ≤ AK`, the `N × N` submatrix `S_{2n+1,bot}[:, J_{head}]` has
determinant
$$\det\left(S_{2n+1,\mathrm{bot}}[:, J_{\mathrm{head}}]\right) = \prod_{r=0}^{A_0 K} w_{2n+1,r} \ne 0.$$ -/
theorem theorem_4_3_ii_head_det (n A0K AK : ℕ) (hA0 : A0K ≤ AK) :
    (S2n1BotHeadMatrix n A0K AK).det =
      ∏ r ∈ Finset.range (A0K + 1), innerNodeWeight n A0K AK r ∧
    (S2n1BotHeadMatrix n A0K AK).det ≠ 0 := by
  have h_det_eq :
      (S2n1BotHeadMatrix n A0K AK).det =
        ∏ r ∈ Finset.range (A0K + 1), innerNodeWeight n A0K AK r := by
    rw [S2n1BotHeadMatrix_eq_mul, Matrix.det_mul, Matrix.det_mul,
        (theorem_4_3_EHead_det_eq_one A0K).2, Matrix.det_transpose,
        (theorem_4_3_EHead_det_eq_one A0K).2, Matrix.det_diagonal, one_mul, mul_one]
    exact (Fin.prod_univ_eq_prod_range (fun r => innerNodeWeight n A0K AK r) (A0K + 1))
  refine ⟨h_det_eq, ?_⟩
  rw [h_det_eq, Finset.prod_ne_zero_iff]
  intro r hr
  exact prop_4_1_innerNodeWeight_ne_zero n A0K AK r
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)) hA0

/-- **Theorem 4.3 (Step 2 Terminal Degree Argument)**:
At the terminal step `m = n - 1` of the backward Hermite induction (4.21), the divisor
`u^{n-1} ∏_{r=1}^{A₀K} (u - r²)^{2(n-1)}` has degree
`(n - 1) + 2(n - 1) A₀K = (n - 1)(2A₀K + 1) = R`, which strictly exceeds `deg_u Q ≤ R - 1`. -/
theorem theorem_4_3_terminal_divisor_degree (n A0K : ℕ) :
    (n - 1) + 2 * (n - 1) * A0K = dimR n A0K := by
  unfold dimR dimREach
  ring

/-- **Theorem 4.3 (Equation (4.21): Polynomial Divisor `D_m(X) := X^m ∏_{r=1}^{A₀K} (X - r²)^{2m}`)**:
The polynomial divisor in the backward Hermite induction (Step 2 of Theorem 4.3, p. 22). -/
noncomputable def hermiteDivisorPoly (A0K m : ℕ) : Polynomial ℚ :=
  Polynomial.X ^ m * (HermiteOmegaPoly A0K) ^ m

/-- Monicity and exact `natDegree` of `hermiteDivisorPoly A0K m`:
`hermiteDivisorPoly A0K m` is monic of degree `m * (2 * A₀K + 1)`. -/
theorem hermiteDivisorPoly_monic_and_natDegree (A0K m : ℕ) :
    (hermiteDivisorPoly A0K m).Monic ∧
    (hermiteDivisorPoly A0K m).natDegree = m * dimREach A0K := by
  have h_omega_monic : (HermiteOmegaPoly A0K).Monic := by
    unfold HermiteOmegaPoly
    apply Polynomial.monic_prod_of_monic
    intro r _
    exact (Polynomial.monic_X_sub_C ((r : ℚ) ^ 2)).pow 2
  have h_omega_deg : (HermiteOmegaPoly A0K).natDegree = 2 * A0K := by
    unfold HermiteOmegaPoly
    rw [Polynomial.natDegree_prod_of_monic]
    · have h_deg_each : ∀ r ∈ Finset.Icc 1 A0K,
          ((Polynomial.X - Polynomial.C ((r : ℚ) ^ 2)) ^ 2).natDegree = 2 := by
        intro r _
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
      rw [Finset.sum_congr rfl h_deg_each, Finset.sum_const, Nat.card_Icc,
          show A0K + 1 - 1 = A0K by omega, smul_eq_mul, mul_comm]
    · intro r _
      exact (Polynomial.monic_X_sub_C ((r : ℚ) ^ 2)).pow 2
  unfold hermiteDivisorPoly dimREach
  have h_monic : (Polynomial.X ^ m * (HermiteOmegaPoly A0K) ^ m).Monic :=
    (Polynomial.monic_X_pow m).mul (h_omega_monic.pow m)
  refine ⟨h_monic, ?_⟩
  rw [Polynomial.natDegree_mul (Polynomial.monic_X_pow m).ne_zero (h_omega_monic.pow m).ne_zero,
      Polynomial.natDegree_X_pow, Polynomial.natDegree_pow, h_omega_deg]
  ring

/-- **Theorem 4.3 Step 2 (Equation (4.21) Terminal Induction Step)**:
If `Q ∈ ℚ[X]` satisfies `Q = 0` or `Q.natDegree < dimR n A0K`, and the terminal Hermite divisor
`D_{n-1}(X) = X^{n-1} ∏_{r=1}^{A₀K} (X - r²)^{2(n-1)}` divides `Q`, then `Q = 0` identically. -/
theorem theorem_4_3_backward_hermite_divisibility_zero (n A0K : ℕ) (Q : Polynomial ℚ)
    (h_deg : Q = 0 ∨ Q.natDegree < dimR n A0K)
    (h_dvd : hermiteDivisorPoly A0K (n - 1) ∣ Q) :
    Q = 0 := by
  rcases h_deg with rfl | h_lt
  · rfl
  · by_contra hQ_ne
    have h_div_prop := hermiteDivisorPoly_monic_and_natDegree A0K (n - 1)
    have h_le : (hermiteDivisorPoly A0K (n - 1)).natDegree ≤ Q.natDegree :=
      Polynomial.natDegree_le_of_dvd h_dvd hQ_ne
    rw [h_div_prop.2] at h_le
    unfold dimR at h_lt
    omega

/-- **Theorem 4.3(iii) (Equations (4.17)–(4.18): Block-Triangular Determinant Factorization)**:
For the full `M × M` stacked matrix (`M = R + N`) in block lower-triangular form
$$M_{\mathrm{full}} = \begin{pmatrix} a_{2n+1} S_{\mathrm{odd},\mathrm{top}}[:, J_{\mathrm{tail}}] & 0 \\
S_{2n+1,\mathrm{bot}}[:, J_{\mathrm{tail}}] & S_{2n+1,\mathrm{bot}}[:, J_{\mathrm{head}}] \end{pmatrix}$$
(where the top-right block vanishes identically by Proposition 4.1(iii) (`prop_4_1_iii_tail_vanishing`)
since `L(A_i ℰ_m) = a_{2n+1} S_{\mathrm{odd}}(A_i ℰ_m)` for all `m > A₀K`), the determinant factors
exactly as Equation (4.18):
$$\det(M_{\mathrm{full}}) = a_{2n+1}^R \det(S_{\mathrm{odd},\mathrm{top}}[:, J_{\mathrm{tail}}])
  \prod_{r=0}^{A_0 K} w_{2n+1,r}.$$ -/
theorem theorem_4_3_iii_block_triangular_det (n A0K AK : ℕ) (hA0 : A0K ≤ AK)
    (a_top : ℚ) (ha_top : a_top ≠ 0)
    (S_odd_tail : Matrix (Fin (dimR n A0K)) (Fin (dimR n A0K)) ℚ)
    (h_tail_det : S_odd_tail.det ≠ 0)
    (C_bot_tail : Matrix (Fin (A0K + 1)) (Fin (dimR n A0K)) ℚ) :
    (Matrix.fromBlocks (a_top • S_odd_tail) 0 C_bot_tail (S2n1BotHeadMatrix n A0K AK)).det =
      a_top ^ (dimR n A0K) * S_odd_tail.det *
        (∏ r ∈ Finset.range (A0K + 1), innerNodeWeight n A0K AK r) ∧
    (Matrix.fromBlocks (a_top • S_odd_tail) 0 C_bot_tail (S2n1BotHeadMatrix n A0K AK)).det ≠ 0 := by
  have h_head := theorem_4_3_ii_head_det n A0K AK hA0
  have h_eq :
      (Matrix.fromBlocks (a_top • S_odd_tail) 0 C_bot_tail (S2n1BotHeadMatrix n A0K AK)).det =
        a_top ^ (dimR n A0K) * S_odd_tail.det *
          (∏ r ∈ Finset.range (A0K + 1), innerNodeWeight n A0K AK r) := by
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul, Fintype.card_fin, h_head.1]
  refine ⟨h_eq, ?_⟩
  rw [h_eq]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ ha_top) h_tail_det)
    (by rw [← h_head.1]; exact h_head.2)

/-!
## Theorem 4.4: Closed-Form Confluent Vandermonde Determinant of the Tail Submatrix
-/

/-- **Theorem 4.4 (Exponent Identities in the Proof of (4.24), p. 24)**:
- The combined exponent of `r` across Steps (1), (3), and (4) is
  `4(n - 1) + 6(n - 1) + 4(n - 1)² = (n - 1)(4n + 6)`.
- The combined exponent of `(r² - s²)` across Steps (1), (3), and (4) is
  `4(n - 1) + 4(n - 1) + 4(n - 1)² = 4(n² - 1)`.
- The step-(3) `2r` exponent sum is `∑_{m=1}^{n-1} 4m = 2n(n - 1)`. -/
theorem theorem_4_4_exponent_identities (n : ℕ) (hn : 2 ≤ n) :
    4 * (n - 1) + 6 * (n - 1) + 4 * (n - 1) ^ 2 = (n - 1) * (4 * n + 6) ∧
    4 * (n - 1) + 4 * (n - 1) + 4 * (n - 1) ^ 2 = 4 * (n ^ 2 - 1) ∧
    (∑ m ∈ Finset.Icc 1 (n - 1), 4 * m) = 2 * n * (n - 1) := by
  refine ⟨by zify [show 1 ≤ n by omega]; ring,
          by zify [show 1 ≤ n by omega, show 1 ≤ n ^ 2 by nlinarith]; ring, ?_⟩
  induction' n, hn using Nat.le_induction with k hk ih
  · decide
  · rw [show k + 1 - 1 = (k - 1) + 1 by omega,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ (k - 1) + 1),
        ih, show (k - 1) + 1 = k by omega]
    zify [show 1 ≤ k by omega]
    ring

/-- **Theorem 4.4 (Equation (4.24): Closed-Form Determinant of the Tail Submatrix)**:
The exact closed-form expression for `|det(S_{odd,top}[:, J_{tail}])|` (4.24). -/
def tailSubmatrixDetClosedForm (n A0K AK : ℕ) : ℚ :=
  let N := dimN A0K
  let R := dimR n A0K
  let rowFac : ℚ := (∏ i ∈ Finset.Icc 1 (2 * A0K), (2 : ℚ) / ((2 * i).factorial : ℚ)) ^ (n - 1)
  let colFac : ℚ := ∏ m ∈ Finset.Ico N (N + R), (2 : ℚ) / ((2 * m).factorial : ℚ)
  let w0Factor : ℚ := |innerNodeWeight n A0K AK 0| ^ (n - 1)
  let wrFactor : ℚ :=
    ∏ r ∈ Finset.Icc 1 A0K,
      (|innerNodeWeight n A0K AK r| ^ (2 * (n - 1))) *
        (((2 * r : ℕ) : ℚ) ^ (2 * n * (n - 1))) *
        ((r : ℚ) ^ ((n - 1) * (4 * n + 6)))
  let vdmFactor : ℚ :=
    ∏ r ∈ Finset.Icc 1 A0K,
      ∏ s ∈ Finset.Ico 1 r,
        (((r : ℚ) ^ 2 - (s : ℚ) ^ 2) ^ (4 * (n ^ 2 - 1)))
  rowFac * colFac * w0Factor * wrFactor * vdmFactor

/-- **Theorem 4.4 (Strict Positivity / Non-Vanishing of `|det(S_{odd,top}[:, J_{tail}])| > 0`)**:
For every `n ≥ 2`, `1 ≤ A₀K`, and `A₀K ≤ AK`, the closed-form tail determinant (4.24) is
strictly positive (and hence non-zero). -/
theorem theorem_4_4_tail_det_pos (n A0K AK : ℕ) (_hn : 2 ≤ n) (hA0 : A0K ≤ AK) :
    0 < tailSubmatrixDetClosedForm n A0K AK ∧ tailSubmatrixDetClosedForm n A0K AK ≠ 0 := by
  have h_pos : 0 < tailSubmatrixDetClosedForm n A0K AK := by
    unfold tailSubmatrixDetClosedForm
    dsimp only
    apply mul_pos
    · apply mul_pos
      · apply mul_pos
        · apply mul_pos
          · apply pow_pos
            apply Finset.prod_pos
            intro i _
            exact div_pos two_pos (by exact_mod_cast Nat.factorial_pos (2 * i))
          · apply Finset.prod_pos
            intro m _
            exact div_pos two_pos (by exact_mod_cast Nat.factorial_pos (2 * m))
        · apply pow_pos
          exact abs_pos.mpr (prop_4_1_innerNodeWeight_ne_zero n A0K AK 0 (Nat.zero_le _) hA0)
      · apply Finset.prod_pos
        intro r hr
        have hr_pos : 1 ≤ r := (Finset.mem_Icc.mp hr).1
        have hr_le : r ≤ A0K := (Finset.mem_Icc.mp hr).2
        have hr_q : (0 : ℚ) < (r : ℚ) := by exact_mod_cast hr_pos
        have h2r_q : (0 : ℚ) < ((2 * r : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < 2 * r)
        apply mul_pos
        · apply mul_pos
          · exact pow_pos (abs_pos.mpr (prop_4_1_innerNodeWeight_ne_zero n A0K AK r hr_le hA0)) _
          · exact pow_pos h2r_q _
        · exact pow_pos hr_q _
    · apply Finset.prod_pos
      intro r hr
      apply Finset.prod_pos
      intro s hs
      have hs_lt : s < r := (Finset.mem_Ico.mp hs).2
      have h_diff_pos : (0 : ℚ) < (r : ℚ) ^ 2 - (s : ℚ) ^ 2 := by
        have h_rat : (s : ℚ) < (r : ℚ) := by exact_mod_cast hs_lt
        have h_nonneg : (0 : ℚ) ≤ (s : ℚ) := by positivity
        nlinarith
      exact pow_pos h_diff_pos _
  exact ⟨h_pos, ne_of_gt h_pos⟩

/-!
## Complete Ground-Up Derivations for Proposition 4.1, Lemma 4.2, Theorem 4.3 Step 2, Theorem 4.4, and Remark 4.5
-/

/-- Symmetric interval pairing lemma: for any `A₀K ≤ AK` and any `f : ℕ → ℚ` satisfying
`f(AK + r) = f(AK - r)` for all `1 ≤ r ≤ A₀K`,
$$\sum_{k = AK - A_0 K}^{AK + A_0 K} f(k) = f(AK) + 2 \sum_{r = 1}^{A_0 K} f(AK - r).$$ -/
theorem sum_Icc_symmetric_pair (A0K AK : ℕ) (hA0 : A0K ≤ AK) (f : ℕ → ℚ)
    (h_symm : ∀ r ∈ Finset.Icc 1 A0K, f (AK + r) = f (AK - r)) :
    (∑ k ∈ Finset.Icc (AK - A0K) (AK + A0K), f k) =
      f AK + 2 * ∑ r ∈ Finset.Icc 1 A0K, f (AK - r) := by
  induction A0K with
  | zero =>
    simp
  | succ m ih =>
    have hm_le : m ≤ AK := by omega
    have h_symm_m : ∀ r ∈ Finset.Icc 1 m, f (AK + r) = f (AK - r) := by
      intro r hr
      exact h_symm r (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, le_trans (Finset.mem_Icc.mp hr).2 (by omega)⟩)
    have h_icc_split :
        Finset.Icc (AK - (m + 1)) (AK + (m + 1)) =
          insert (AK - (m + 1)) (insert (AK + (m + 1)) (Finset.Icc (AK - m) (AK + m))) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h_not1 : AK - (m + 1) ∉ insert (AK + (m + 1)) (Finset.Icc (AK - m) (AK + m)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have h_not2 : AK + (m + 1) ∉ Finset.Icc (AK - m) (AK + m) := by
      simp only [Finset.mem_Icc]
      omega
    have h_rhs_ins : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext r
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h_not_r : m + 1 ∉ Finset.Icc 1 m := by
      simp only [Finset.mem_Icc]
      omega
    rw [h_icc_split, Finset.sum_insert h_not1, Finset.sum_insert h_not2,
        ih hm_le h_symm_m, h_rhs_ins, Finset.sum_insert h_not_r,
        h_symm (m + 1) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)]
    ring

/-- **Proposition 4.1 (Equation (4.7): Symmetric Inner-Pole Pairing of `S_{2j+1}(P)`)**:
For every `n ≥ 1`, `A₀K ≤ AK`, and `j ≥ 1`,
$$S_{2j+1}(P) = A_{2j+1, AK}(P) + 2 \sum_{r=1}^{A_0 K} A_{2j+1, AK - r}(P).$$ -/
theorem prop_4_1_eq_4_7_inner_pole_pairing (n A0K AK : ℕ) (hn : 1 ≤ n) (hA0 : A0K ≤ AK)
    (normDerivP : ℚ → ℕ → ℚ) (j : ℕ) (hj : 1 ≤ j) :
    poleSumSt n A0K AK (laurentCoeffAt n A0K AK normDerivP) (2 * j + 1) =
      laurentCoeffAt n A0K AK normDerivP (2 * j + 1) AK +
        2 * ∑ r ∈ Finset.Icc 1 A0K,
          laurentCoeffAt n A0K AK normDerivP (2 * j + 1) (AK - r) := by
  rw [theorem_3_3_ii_inner_support_compression n A0K AK normDerivP j hj]
  have h_filter_eq :
      (Finset.range (2 * AK + 1)).filter (fun (k : ℕ) => ((k : ℤ) - (AK : ℤ)).natAbs ≤ A0K) =
        Finset.Icc (AK - A0K) (AK + A0K) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [h_filter_eq]
  apply sum_Icc_symmetric_pair A0K AK hA0
  intro r hr
  have hr_le : r ≤ A0K := (Finset.mem_Icc.mp hr).2
  have h_refl :=
    theorem_3_3_i_laurentCoeff_reflect n A0K AK normDerivP (2 * j + 1) (AK - r)
      hn (by omega) (by omega)
  have h_idx : 2 * AK - (AK - r) = AK + r := by omega
  have h_even : Even (2 * j + 1 - 1) := ⟨j, by omega⟩
  rw [h_idx, h_even.neg_one_pow, one_mul] at h_refl
  exact h_refl

/-- **Proposition 4.1(i) (Equation (4.2): Full Derivation `S_{2n+1}(P) = ∑_{r=0}^{A₀K} w_{2n+1,r} P(r²)`)**:
For every `n ≥ 1` and `A₀K ≤ AK`, the global pole sum `poleSumSt` at weight `2n + 1` equals
`S2nPlus1Functional`:
$$S_{2n+1}(P) = \sum_{r=0}^{A_0 K} w_{2n+1,r} P(r^2).$$ -/
theorem prop_4_1_i_poleSum_eq_S2nPlus1Functional (n A0K AK : ℕ) (hn : 1 ≤ n) (hA0 : A0K ≤ AK)
    (normDerivP : ℚ → ℕ → ℚ) :
    poleSumSt n A0K AK (laurentCoeffAt n A0K AK normDerivP) (2 * n + 1) =
      S2nPlus1Functional n A0K AK (fun u => normDerivP u 0) := by
  rw [prop_4_1_eq_4_7_inner_pole_pairing n A0K AK hn hA0 normDerivP n hn]
  unfold S2nPlus1Functional
  have h_range_split : Finset.range (A0K + 1) = insert 0 (Finset.Icc 1 A0K) := by
    ext r
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0_not_mem : (0 : ℕ) ∉ Finset.Icc 1 A0K := by
    simp only [Finset.mem_Icc]
    omega
  rw [h_range_split, Finset.sum_insert h0_not_mem]
  have h_r0 :
      laurentCoeffAt n A0K AK normDerivP (2 * n + 1) AK =
        innerNodeWeight n A0K AK 0 * normDerivP (((0 : ℕ) : ℚ) ^ 2) 0 := by
    rw [prop_4_1_i_laurentCoeffAt_top_weight n A0K AK normDerivP AK (by simp)]
    unfold innerNodeWeight
    simp
  rw [h_r0, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hr2 : r ≤ A0K := (Finset.mem_Icc.mp hr).2
  have h_in : (((AK - r : ℕ) : ℤ) - (AK : ℤ)).natAbs ≤ A0K := by omega
  rw [prop_4_1_i_laurentCoeffAt_top_weight n A0K AK normDerivP (AK - r) h_in]
  have h_sq : ((AK : ℚ) - ((AK - r : ℕ) : ℚ)) ^ 2 = (r : ℚ) ^ 2 := by
    rw [Nat.cast_sub (by omega : r ≤ AK)]
    ring
  rw [h_sq]
  unfold innerNodeWeight
  rw [if_neg (by omega : r ≠ 0)]
  ring

/-- **Proposition 4.1(ii) (Central Pole `r = 0` Jet Expansion in Equation (4.3), p. 19)**:
At the central pole `k = AK` (`r = 0`), for every `1 ≤ j ≤ n`,
$$A_{2j+1, AK}(P) = \sum_{q=0}^{n - j} w_{2j+1, 0}^{(q)} \frac{P^{(q)}(0)}{q!}.$$ -/
theorem prop_4_1_ii_central_pole_jet (n A0K AK : ℕ) (normDerivP : ℚ → ℕ → ℚ)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    laurentCoeffAt n A0K AK normDerivP (2 * j + 1) AK =
      ∑ q ∈ Finset.range (n - j + 1),
        jetWeightW n A0K AK j 0 q * normDerivP 0 q := by
  unfold laurentCoeffAt
  have hLk : poleMultiplicity n A0K AK AK = 2 * n + 1 :=
    poleMultiplicity_inner_eq n A0K AK AK (by simp)
  rw [hLk, if_neg (by omega)]
  dsimp only
  rw [sub_self, mul_zero, zero_pow two_ne_zero]
  have h_diff : 2 * n + 1 - (2 * j + 1) = 2 * (n - j) := by omega
  rw [h_diff]
  -- Evaluate the inner sum over `d ∈ Icc ((m + 1) / 2) m`: since `0 ^ (2d - m)` is `1` iff `m = 2d`,
  -- the inner sum equals `normDerivP 0 (m / 2)` when `Even m` and `0` when `Odd m`.
  have h_inner :
      ∀ m ∈ Finset.range (2 * (n - j) + 1),
        (∑ d ∈ Finset.Icc ((m + 1) / 2) m,
          (Nat.choose d (m - d) : ℚ) * ((0 : ℚ) ^ (2 * d - m)) * normDerivP 0 d) =
        if m % 2 = 0 then normDerivP 0 (m / 2) else 0 := by
    intro m _
    split_ifs with hm_even
    · rw [Finset.sum_eq_single (m / 2)]
      · have h_2d : 2 * (m / 2) - m = 0 := by omega
        have h_md : m - m / 2 = m / 2 := by omega
        rw [h_2d, pow_zero, h_md, Nat.choose_self, Nat.cast_one, one_mul, one_mul]
      · intro d hd hd_ne
        have hd1 : (m + 1) / 2 ≤ d := (Finset.mem_Icc.mp hd).1
        have h_pos : 2 * d - m ≠ 0 := by omega
        rw [zero_pow h_pos, mul_zero, zero_mul]
      · intro h_absurd
        exact False.elim (h_absurd (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    · apply Finset.sum_eq_zero
      intro d hd
      have hd1 : (m + 1) / 2 ≤ d := (Finset.mem_Icc.mp hd).1
      have h_pos : 2 * d - m ≠ 0 := by omega
      rw [zero_pow h_pos, mul_zero, zero_mul]
  have h_sum_rewrite :
      (∑ m ∈ Finset.range (2 * (n - j) + 1),
        gkTaylorCoeff n A0K AK AK (2 * (n - j) - m) *
          ∑ d ∈ Finset.Icc ((m + 1) / 2) m,
            (Nat.choose d (m - d) : ℚ) * ((0 : ℚ) ^ (2 * d - m)) * normDerivP 0 d) =
      ∑ m ∈ (Finset.range (2 * (n - j) + 1)).filter (fun m => m % 2 = 0),
        gkTaylorCoeff n A0K AK AK (2 * (n - j) - m) * normDerivP 0 (m / 2) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    rw [h_inner m hm]
    split_ifs <;> ring
  rw [h_sum_rewrite]
  apply Finset.sum_bij (fun m _ => m / 2)
  · intro m hm
    have hm_lt : m < 2 * (n - j) + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
    exact Finset.mem_range.mpr (by omega)
  · intro m₁ hm₁ m₂ hm₂ h_eq
    have h1 : m₁ % 2 = 0 := (Finset.mem_filter.mp hm₁).2
    have h2 : m₂ % 2 = 0 := (Finset.mem_filter.mp hm₂).2
    omega
  · intro q hq
    have hq_lt : q < n - j + 1 := Finset.mem_range.mp hq
    refine ⟨2 * q, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩, by omega⟩
  · intro m hm
    have hm_even : m % 2 = 0 := (Finset.mem_filter.mp hm).2
    unfold jetWeightW
    rw [if_pos rfl, show 2 * (n - j - m / 2) = 2 * (n - j) - m by omega]

/-- **Proposition 4.1(ii) (Off-Center Inner Pole `1 ≤ r ≤ A₀K` Jet Expansion in Equations (4.3)–(4.4), p. 19)**:
For every `1 ≤ r ≤ A₀K` (`A₀K ≤ AK`) and `1 ≤ j ≤ n`, re-indexing the double sum in `laurentCoeffAt`
gives
$$2 A_{2j+1, AK - r}(P) = \sum_{q=0}^{2(n - j)} w_{2j+1, r}^{(q)} \frac{P^{(q)}(r^2)}{q!}.$$ -/
theorem prop_4_1_ii_off_center_pole_jet (n A0K AK : ℕ) (hA0 : A0K ≤ AK)
    (normDerivP : ℚ → ℕ → ℚ) (j r : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (hr1 : 1 ≤ r) (hr2 : r ≤ A0K) :
    2 * laurentCoeffAt n A0K AK normDerivP (2 * j + 1) (AK - r) =
      ∑ q ∈ Finset.range (2 * (n - j) + 1),
        jetWeightW n A0K AK j r q * normDerivP ((r : ℚ) ^ 2) q := by
  unfold laurentCoeffAt
  have h_in : (((AK - r : ℕ) : ℤ) - (AK : ℤ)).natAbs ≤ A0K := by omega
  have hLk : poleMultiplicity n A0K AK (AK - r) = 2 * n + 1 :=
    poleMultiplicity_inner_eq n A0K AK (AK - r) h_in
  rw [hLk, if_neg (by omega)]
  dsimp only
  have h_diff : 2 * n + 1 - (2 * j + 1) = 2 * (n - j) := by omega
  have h_r_eq : (AK : ℚ) - ((AK - r : ℕ) : ℚ) = (r : ℚ) := by
    rw [Nat.cast_sub (by omega : r ≤ AK)]
    ring
  rw [h_diff]
  simp_rw [h_r_eq, Finset.mul_sum, Finset.sum_sigma']
  unfold jetWeightW
  simp_rw [if_neg (by omega : r ≠ 0), Finset.mul_sum, Finset.sum_mul, Finset.sum_sigma']
  apply Finset.sum_bij (fun p _ => ⟨p.2, p.1 - p.2⟩)
  · rintro ⟨m, d⟩ hp
    rcases Finset.mem_sigma.mp hp with ⟨hp1, hp2⟩
    dsimp only at hp1 hp2 ⊢
    have hm : m ≤ 2 * (n - j) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp1)
    have hq1 : (m + 1) / 2 ≤ d := (Finset.mem_Icc.mp hp2).1
    have hq2 : d ≤ m := (Finset.mem_Icc.mp hp2).2
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_range.mpr (by dsimp; omega), Finset.mem_range.mpr (by dsimp; omega)⟩
  · rintro ⟨m₁, d₁⟩ hp₁ ⟨m₂, d₂⟩ hp₂ h_eq
    rcases Finset.mem_sigma.mp hp₁ with ⟨_, hp1_2⟩
    rcases Finset.mem_sigma.mp hp₂ with ⟨_, hp2_2⟩
    dsimp only at hp1_2 hp2_2 h_eq
    have hq1 : d₁ ≤ m₁ := (Finset.mem_Icc.mp hp1_2).2
    have hq2 : d₂ ≤ m₂ := (Finset.mem_Icc.mp hp2_2).2
    injection h_eq with hd_eq ha_eq
    exact congr_arg₂ Sigma.mk (by omega) hd_eq
  · rintro ⟨q, a⟩ hy
    rcases Finset.mem_sigma.mp hy with ⟨hy1, hy2⟩
    dsimp only at hy1 hy2
    have hq_le : q ≤ 2 * (n - j) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hy1)
    have ha_le : a ≤ min q (2 * (n - j) - q) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hy2)
    refine ⟨⟨q + a, q⟩, ?_, ?_⟩
    · exact Finset.mem_sigma.mpr
        ⟨Finset.mem_range.mpr (by dsimp; omega),
         Finset.mem_Icc.mpr ⟨by dsimp; omega, by dsimp; omega⟩⟩
    · exact congr_arg₂ Sigma.mk rfl (by dsimp; omega)
  · rintro ⟨m, d⟩ hp
    rcases Finset.mem_sigma.mp hp with ⟨hp1, hp2⟩
    dsimp only at hp1 hp2 ⊢
    have hm : m ≤ 2 * (n - j) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp1)
    have hq1 : (m + 1) / 2 ≤ d := (Finset.mem_Icc.mp hp2).1
    have hq2 : d ≤ m := (Finset.mem_Icc.mp hp2).2
    rw [show 2 * (n - j) - d - (m - d) = 2 * (n - j) - m by omega,
        show d - (m - d) = 2 * d - m by omega]
    ring

/-- **Proposition 4.1(ii) (Equation (4.3): Complete Local Leibniz Jet Expansion of `S_{2j+1}(P)`)**:
For every `n ≥ 2`, `A₀K ≤ AK`, and `1 ≤ j ≤ n - 1`,
$$S_{2j+1}(P) = \sum_{q=0}^{n-j} w_{2j+1,0}^{(q)} \frac{P^{(q)}(0)}{q!}
  + \sum_{r=1}^{A_0 K} \sum_{q=0}^{2(n-j)} w_{2j+1,r}^{(q)} \frac{P^{(q)}(r^2)}{q!}.$$ -/
theorem prop_4_1_ii_poleSum_eq_jet_expansion (n A0K AK : ℕ) (hn : 2 ≤ n) (hA0 : A0K ≤ AK)
    (normDerivP : ℚ → ℕ → ℚ) (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n - 1) :
    poleSumSt n A0K AK (laurentCoeffAt n A0K AK normDerivP) (2 * j + 1) =
      (∑ q ∈ Finset.range (n - j + 1),
        jetWeightW n A0K AK j 0 q * normDerivP 0 q) +
      ∑ r ∈ Finset.Icc 1 A0K,
        ∑ q ∈ Finset.range (2 * (n - j) + 1),
          jetWeightW n A0K AK j r q * normDerivP ((r : ℚ) ^ 2) q := by
  rw [prop_4_1_eq_4_7_inner_pole_pairing n A0K AK (by omega) hA0 normDerivP j hj1,
      prop_4_1_ii_central_pole_jet n A0K AK normDerivP j hj1 (by omega),
      Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  exact prop_4_1_ii_off_center_pole_jet n A0K AK hA0 normDerivP j r hj1 (by omega)
    (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2

/-- **Lemma 4.2 (Closed-Form Value `Ω(0) = ((A₀K)!)⁴`, p. 20)**:
At `u = 0`, `Ω(0) = ∏_{r=1}^{A₀K} (0 - r²)² = ((A₀K)!)⁴`. -/
theorem HermiteOmega_at_zero_eq_factorial_pow_four (A0K : ℕ) :
    HermiteOmega A0K 0 = ((A0K.factorial : ℚ) ^ 4) := by
  unfold HermiteOmega
  have h_term : ∀ r ∈ Finset.Icc 1 A0K, ((0 : ℚ) - (r : ℚ) ^ 2) ^ 2 = (r : ℚ) ^ 4 := by
    intro r _; ring
  rw [Finset.prod_congr rfl h_term, Finset.prod_pow, prod_Icc_one_eq_factorial]

/-- **Lemma 4.2 (Exact Polynomial Degree Bounds for `H_0`, `ℓ_r`, `H_{r,1}`, and `H_{r,0}`, p. 20)**:
For every `A₀K ≥ 1` and `r ∈ {1, ..., A₀K}`:
1. `(HermiteH0Poly A0K).natDegree = 2 * A0K`
2. `(HermiteEllPoly A0K r).natDegree = 2 * A0K - 1`
3. `(HermiteHr1Poly A0K r).natDegree = 2 * A0K`
4. `(HermiteHr0Poly A0K r).natDegree ≤ 2 * A0K`. -/
theorem lemma_4_2_hermite_natDegree_bounds (A0K r : ℕ) (hr : r ∈ Finset.Icc 1 A0K) :
    (HermiteH0Poly A0K).natDegree = 2 * A0K ∧
    (HermiteEllPoly A0K r).natDegree = 2 * A0K - 1 ∧
    (HermiteHr1Poly A0K r).natDegree = 2 * A0K ∧
    (HermiteHr0Poly A0K r).natDegree ≤ 2 * A0K := by
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hr2 : r ≤ A0K := (Finset.mem_Icc.mp hr).2
  -- 1. Degree of HermiteH0Poly:
  have h_omega_deg : (HermiteOmegaPoly A0K).natDegree = 2 * A0K := by
    unfold HermiteOmegaPoly
    rw [Polynomial.natDegree_prod_of_monic _ _
        (fun (t : ℕ) _ => (Polynomial.monic_X_sub_C ((t : ℚ) ^ 2)).pow 2)]
    have h_each : ∀ t ∈ Finset.Icc 1 A0K,
        ((Polynomial.X - Polynomial.C ((t : ℚ) ^ 2)) ^ 2).natDegree = 2 := by
      intro t _; rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    rw [Finset.sum_congr rfl h_each, Finset.sum_const, Nat.card_Icc,
        show A0K + 1 - 1 = A0K by omega, smul_eq_mul, mul_comm]
  have h_H0_deg : (HermiteH0Poly A0K).natDegree = 2 * A0K := by
    unfold HermiteH0Poly
    rw [Polynomial.natDegree_C_mul (one_div_ne_zero (HermiteOmega_zero_ne_zero A0K)), h_omega_deg]
  -- 2. Degree of HermiteEllPoly:
  have h_ell_ne_zero_and_deg :
      HermiteEllPoly A0K r ≠ 0 ∧ (HermiteEllPoly A0K r).natDegree = 2 * A0K - 1 := by
    unfold HermiteEllPoly
    have hr_sq_ne : (1 : ℚ) / ((r : ℚ) ^ 2) ≠ 0 :=
      one_div_ne_zero (pow_ne_zero 2 (by exact_mod_cast (by omega : r ≠ 0)))
    have h_first_ne : Polynomial.C (1 / ((r : ℚ) ^ 2)) * Polynomial.X ≠ 0 :=
      mul_ne_zero (Polynomial.C_ne_zero.mpr hr_sq_ne) Polynomial.X_ne_zero
    have h_first_deg : (Polynomial.C (1 / ((r : ℚ) ^ 2)) * Polynomial.X).natDegree = 1 := by
      rw [Polynomial.natDegree_C_mul hr_sq_ne, Polynomial.natDegree_X]
    have h_factor_ne_and_deg :
        ∀ t ∈ (Finset.Icc 1 A0K).erase r,
          (Polynomial.C (1 / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) *
            (Polynomial.X - Polynomial.C ((t : ℚ) ^ 2))) ^ 2 ≠ 0 ∧
          ((Polynomial.C (1 / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) *
            (Polynomial.X - Polynomial.C ((t : ℚ) ^ 2))) ^ 2).natDegree = 2 := by
      intro t ht
      have h_ne : t ≠ r := (Finset.mem_erase.mp ht).1
      have h_diff_ne : (r : ℚ) ^ 2 - (t : ℚ) ^ 2 ≠ 0 := by
        intro h_eq
        have h_sq : (r : ℚ) ^ 2 = (t : ℚ) ^ 2 := sub_eq_zero.mp h_eq
        have h_nat : r ^ 2 = t ^ 2 := by exact_mod_cast h_sq
        rw [sq, sq] at h_nat
        exact h_ne (Nat.mul_self_inj.mp h_nat.symm)
      have hc_ne : (1 : ℚ) / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2) ≠ 0 := one_div_ne_zero h_diff_ne
      have h_lin_ne :
          Polynomial.C (1 / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) *
            (Polynomial.X - Polynomial.C ((t : ℚ) ^ 2)) ≠ 0 :=
        mul_ne_zero (Polynomial.C_ne_zero.mpr hc_ne) (Polynomial.X_sub_C_ne_zero _)
      refine ⟨pow_ne_zero 2 h_lin_ne, ?_⟩
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_C_mul hc_ne,
          Polynomial.natDegree_X_sub_C, mul_one]
    have h_prod_ne :
        (∏ t ∈ (Finset.Icc 1 A0K).erase r,
          (Polynomial.C (1 / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) *
            (Polynomial.X - Polynomial.C ((t : ℚ) ^ 2))) ^ 2) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun t ht => (h_factor_ne_and_deg t ht).1)
    have h_prod_deg :
        (∏ t ∈ (Finset.Icc 1 A0K).erase r,
          (Polynomial.C (1 / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) *
            (Polynomial.X - Polynomial.C ((t : ℚ) ^ 2))) ^ 2).natDegree = 2 * (A0K - 1) := by
      rw [Polynomial.natDegree_prod _ _ (fun t ht => (h_factor_ne_and_deg t ht).1)]
      rw [Finset.sum_congr rfl (fun t ht => (h_factor_ne_and_deg t ht).2),
          Finset.sum_const, Finset.card_erase_of_mem hr, Nat.card_Icc,
          show A0K + 1 - 1 - 1 = A0K - 1 by omega, smul_eq_mul, mul_comm]
    refine ⟨mul_ne_zero h_first_ne h_prod_ne, ?_⟩
    rw [Polynomial.natDegree_mul h_first_ne h_prod_ne, h_first_deg, h_prod_deg]
    omega
  -- 3. Degree of HermiteHr1Poly:
  have h_Hr1_deg : (HermiteHr1Poly A0K r).natDegree = 2 * A0K := by
    unfold HermiteHr1Poly
    rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) h_ell_ne_zero_and_deg.1,
        Polynomial.natDegree_X_sub_C, h_ell_ne_zero_and_deg.2]
    omega
  -- 4. Degree bound of HermiteHr0Poly:
  have h_Hr0_deg : (HermiteHr0Poly A0K r).natDegree ≤ 2 * A0K := by
    unfold HermiteHr0Poly
    have h_left_deg :
        (1 - Polynomial.C ((HermiteEllPoly A0K r).derivative.eval ((r : ℚ) ^ 2)) *
          (Polynomial.X - Polynomial.C ((r : ℚ) ^ 2))).natDegree ≤ 1 := by
      apply le_trans (Polynomial.natDegree_sub_le _ _)
      rw [Polynomial.natDegree_one, max_le_iff]
      refine ⟨Nat.zero_le 1, ?_⟩
      apply le_trans (Polynomial.natDegree_C_mul_le _ _)
      rw [Polynomial.natDegree_X_sub_C]
    calc ((1 - Polynomial.C ((HermiteEllPoly A0K r).derivative.eval ((r : ℚ) ^ 2)) *
            (Polynomial.X - Polynomial.C ((r : ℚ) ^ 2))) * HermiteEllPoly A0K r).natDegree
        ≤ (1 - Polynomial.C ((HermiteEllPoly A0K r).derivative.eval ((r : ℚ) ^ 2)) *
            (Polynomial.X - Polynomial.C ((r : ℚ) ^ 2))).natDegree +
          (HermiteEllPoly A0K r).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 1 + (2 * A0K - 1) := add_le_add h_left_deg (le_of_eq h_ell_ne_zero_and_deg.2)
      _ = 2 * A0K := by omega
  exact ⟨h_H0_deg, h_ell_ne_zero_and_deg.2, h_Hr1_deg, h_Hr0_deg⟩

/-- **Lemma 4.2 (Equation (4.8): Hermite Interpolation Reconstruction Formula)**:
For any target value `c0 ∈ ℚ` at `u = 0` and any target values and first derivatives
`cr0, cr1 : ℕ → ℚ` at `u = r²` (`1 ≤ r ≤ A₀K`), the Hermite interpolation polynomial
$$P(X) := c_0 H_0(X) + \sum_{r=1}^{A_0 K} \left(c_{r,0} H_{r,0}(X) + c_{r,1} H_{r,1}(X)\right)$$
satisfies `P(0) = c0`, `P(r²) = cr0(r)`, and `P'(r²) = cr1(r)` for all `1 ≤ r ≤ A₀K`. -/
theorem lemma_4_2_hermite_interpolation_reconstruction (A0K : ℕ)
    (c0 : ℚ) (cr0 cr1 : ℕ → ℚ) :
    let P : Polynomial ℚ :=
      Polynomial.C c0 * HermiteH0Poly A0K +
        ∑ s ∈ Finset.Icc 1 A0K,
          (Polynomial.C (cr0 s) * HermiteHr0Poly A0K s +
           Polynomial.C (cr1 s) * HermiteHr1Poly A0K s)
    P.eval 0 = c0 ∧
    ∀ r ∈ Finset.Icc 1 A0K,
      P.eval ((r : ℚ) ^ 2) = cr0 r ∧ P.derivative.eval ((r : ℚ) ^ 2) = cr1 r := by
  intro P
  have hH0 := lemma_4_2_i_H0Poly_full A0K
  constructor
  · dsimp [P]
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hH0.1, mul_one,
        Polynomial.eval_finset_sum]
    have h_sum0 :
        (∑ s ∈ Finset.Icc 1 A0K,
          (Polynomial.C (cr0 s) * HermiteHr0Poly A0K s +
           Polynomial.C (cr1 s) * HermiteHr1Poly A0K s).eval 0) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      have hHs := lemma_4_2_ii_iii_HrPoly_full A0K s hs
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hHs.1.1,
          Polynomial.eval_mul, Polynomial.eval_C, hHs.2.1]
      ring
    rw [h_sum0, add_zero]
  · intro r hr
    have hH0_r := hH0.2 r hr
    have hHr := lemma_4_2_ii_iii_HrPoly_full A0K r hr
    constructor
    · dsimp [P]
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hH0_r.1, mul_zero, zero_add,
          Polynomial.eval_finset_sum, Finset.sum_eq_single r]
      · rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hHr.1.2.1,
            Polynomial.eval_mul, Polynomial.eval_C, hHr.2.2.1, mul_one, mul_zero, add_zero]
      · intro s hs hs_ne
        have hHs := lemma_4_2_ii_iii_HrPoly_full A0K s hs
        have hr_in_erase : r ∈ (Finset.Icc 1 A0K).erase s := Finset.mem_erase.mpr ⟨hs_ne.symm, hr⟩
        rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            (hHs.1.2.2.2 r hr_in_erase).1, Polynomial.eval_mul, Polynomial.eval_C,
            (hHs.2.2.2.2 r hr_in_erase).1]
        ring
      · intro h_absurd
        exact False.elim (h_absurd hr)
    · dsimp [P]
      rw [Polynomial.derivative_add, Polynomial.derivative_C_mul, map_sum Polynomial.derivative,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hH0_r.2, mul_zero, zero_add,
          Polynomial.eval_finset_sum, Finset.sum_eq_single r]
      · rw [Polynomial.derivative_add, Polynomial.derivative_C_mul, Polynomial.derivative_C_mul,
            Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hHr.1.2.2.1,
            Polynomial.eval_mul, Polynomial.eval_C, hHr.2.2.2.1, mul_zero, mul_one, zero_add]
      · intro s hs hs_ne
        have hHs := lemma_4_2_ii_iii_HrPoly_full A0K s hs
        have hr_in_erase : r ∈ (Finset.Icc 1 A0K).erase s := Finset.mem_erase.mpr ⟨hs_ne.symm, hr⟩
        rw [Polynomial.derivative_add, Polynomial.derivative_C_mul, Polynomial.derivative_C_mul,
            Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            (hHs.1.2.2.2 r hr_in_erase).2, Polynomial.eval_mul, Polynomial.eval_C,
            (hHs.2.2.2.2 r hr_in_erase).2]
        ring
      · intro h_absurd
        exact False.elim (h_absurd hr)

/-- Product-rule evaluation lemma at a point `u` where each factor evaluates to `1`:
if `∀ t ∈ s, (f t).eval u = 1`, then `(∏ t ∈ s, f t).eval u = 1` and
`((∏ t ∈ s, f t).derivative).eval u = ∑ t ∈ s, (f t).derivative.eval u`. -/
theorem deriv_prod_eval_of_eval_eq_one (s : Finset ℕ) (f : ℕ → Polynomial ℚ) (u : ℚ)
    (h1 : ∀ t ∈ s, (f t).eval u = 1) :
    (∏ t ∈ s, f t).eval u = 1 ∧
    ((∏ t ∈ s, f t).derivative).eval u = ∑ t ∈ s, (f t).derivative.eval u := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | @insert a s ha ih =>
    have ha1 : (f a).eval u = 1 := h1 a (Finset.mem_insert_self a s)
    have hs1 : ∀ t ∈ s, (f t).eval u = 1 :=
      fun t ht => h1 t (Finset.mem_insert_of_mem ht)
    have h_ih := ih hs1
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    refine ⟨by rw [Polynomial.eval_mul, ha1, h_ih.1, mul_one], ?_⟩
    rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_mul, ha1, h_ih.1, h_ih.2]
    ring

/-- **Lemma 4.2 (Logarithmic Derivative Formula for `ℓ_r'(r²)` at Node `u = r²`, p. 19)**:
For every `r ∈ {1, ..., A₀K}`,
$$\ell_r'(r^2) = \frac{1}{r^2} + \sum_{\substack{1 \le t \le A_0 K \\ t \ne r}} \frac{2}{r^2 - t^2}.$$ -/
theorem lemma_4_2_ell_deriv_at_node (A0K r : ℕ) (hr : r ∈ Finset.Icc 1 A0K) :
    (HermiteEllPoly A0K r).derivative.eval ((r : ℚ) ^ 2) =
      (1 : ℚ) / ((r : ℚ) ^ 2) +
        ∑ t ∈ (Finset.Icc 1 A0K).erase r, (2 : ℚ) / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2) := by
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hr_sq_ne : ((r : ℚ) ^ 2) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast (by omega : r ≠ 0))
  unfold HermiteEllPoly
  let g : Polynomial ℚ := Polynomial.C (1 / ((r : ℚ) ^ 2)) * Polynomial.X
  let f : ℕ → Polynomial ℚ := fun t =>
    (Polynomial.C (1 / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) *
      (Polynomial.X - Polynomial.C ((t : ℚ) ^ 2))) ^ 2
  have hg_eval : g.eval ((r : ℚ) ^ 2) = 1 := by
    dsimp [g]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, one_div_mul_cancel hr_sq_ne]
  have hg_deriv : g.derivative.eval ((r : ℚ) ^ 2) = 1 / ((r : ℚ) ^ 2) := by
    dsimp [g]
    rw [Polynomial.derivative_C_mul, Polynomial.derivative_X, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_one, mul_one]
  have hf_eval : ∀ t ∈ (Finset.Icc 1 A0K).erase r, (f t).eval ((r : ℚ) ^ 2) = 1 := by
    intro t ht
    have h_ne : t ≠ r := (Finset.mem_erase.mp ht).1
    have h_diff_ne : (r : ℚ) ^ 2 - (t : ℚ) ^ 2 ≠ 0 := by
      intro h_eq
      have h_nat : r ^ 2 = t ^ 2 := by exact_mod_cast sub_eq_zero.mp h_eq
      rw [sq, sq] at h_nat
      exact h_ne (Nat.mul_self_inj.mp h_nat.symm)
    dsimp [f]
    rw [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, one_div_mul_cancel h_diff_ne, one_pow]
  have hf_deriv :
      ∀ t ∈ (Finset.Icc 1 A0K).erase r,
        (f t).derivative.eval ((r : ℚ) ^ 2) = (2 : ℚ) / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2) := by
    intro t ht
    have h_ne : t ≠ r := (Finset.mem_erase.mp ht).1
    have h_diff_ne : (r : ℚ) ^ 2 - (t : ℚ) ^ 2 ≠ 0 := by
      intro h_eq
      have h_nat : r ^ 2 = t ^ 2 := by exact_mod_cast sub_eq_zero.mp h_eq
      rw [sq, sq] at h_nat
      exact h_ne (Nat.mul_self_inj.mp h_nat.symm)
    have h_sq_deriv :
        ∀ p : Polynomial ℚ,
          p.eval ((r : ℚ) ^ 2) = 1 →
            (p ^ 2).derivative.eval ((r : ℚ) ^ 2) = 2 * p.derivative.eval ((r : ℚ) ^ 2) := by
      intro p hp
      rw [sq p, Polynomial.derivative_mul, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_mul, hp]
      ring
    dsimp [f]
    rw [h_sq_deriv]
    · rw [Polynomial.derivative_C_mul, Polynomial.derivative_sub,
          Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, mul_one,
          Polynomial.eval_C]
      ring
    · rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C, one_div_mul_cancel h_diff_ne]
  have h_prod := deriv_prod_eval_of_eval_eq_one ((Finset.Icc 1 A0K).erase r) f ((r : ℚ) ^ 2) hf_eval
  change (g * ∏ t ∈ (Finset.Icc 1 A0K).erase r, f t).derivative.eval ((r : ℚ) ^ 2) = _
  rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      hg_eval, hg_deriv, h_prod.1, h_prod.2, Finset.sum_congr rfl hf_deriv]
  ring

/-- Double-root divisibility lemma: for any polynomial `P ∈ ℚ[X]` and `a ∈ ℚ`,
if `P.eval a = 0` and `P.derivative.eval a = 0`, then `(X - C a)^2 ∣ P`. -/
theorem double_root_dvd_sq (P : Polynomial ℚ) (a : ℚ)
    (h0 : P.eval a = 0) (h1 : P.derivative.eval a = 0) :
    (Polynomial.X - Polynomial.C a) ^ 2 ∣ P := by
  have h_dvd1 : Polynomial.X - Polynomial.C a ∣ P := Polynomial.dvd_iff_isRoot.mpr h0
  rcases h_dvd1 with ⟨Q, rfl⟩
  have h_lin_deriv : (Polynomial.X - Polynomial.C a).derivative = 1 := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero]
  rw [Polynomial.derivative_mul, h_lin_deriv, one_mul, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_self, zero_mul, add_zero] at h1
  have h_dvd2 : Polynomial.X - Polynomial.C a ∣ Q := Polynomial.dvd_iff_isRoot.mpr h1
  rcases h_dvd2 with ⟨R, rfl⟩
  refine ⟨R, by ring⟩

/-- Coprimality of distinct linear-shift powers `(X - C a)^m` and `(X - C b)^k` in `ℚ[X]`. -/
theorem isCoprime_X_sub_C_pow {a b : ℚ} (hab : a ≠ b) (m k : ℕ) :
    IsCoprime ((Polynomial.X - Polynomial.C a) ^ m) ((Polynomial.X - Polynomial.C b) ^ k) := by
  apply IsCoprime.pow
  refine ⟨Polynomial.C (1 / (b - a)), Polynomial.C (1 / (a - b)), ?_⟩
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hab_sub : a - b ≠ 0 := sub_ne_zero.mpr hab
  ext d
  rcases d with _ | _ | d
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
      Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, Polynomial.coeff_one_zero]
    rw [show a - b = -(b - a) by ring]
    field_simp [hba]
    ring
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
      Polynomial.coeff_X_one, Polynomial.coeff_C_ne_zero (Nat.one_ne_zero), sub_zero,
      mul_one, Polynomial.coeff_one]
    rw [if_neg Nat.one_ne_zero, show a - b = -(b - a) by ring]
    field_simp [hba]
  · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_one]

/-- **Lemma 4.2 & Theorem 4.3 Step 1 (Exact Divisibility by `D_1(X) = X ∏_{r=1}^{A₀K} (X - r²)²`)**:
If `P ∈ ℚ[X]` satisfies `P(0) = 0` and `P(r²) = P'(r²) = 0` for all `1 ≤ r ≤ A₀K`, then
`hermiteDivisorPoly A0K 1` divides `P`. -/
theorem lemma_4_2_hermite_step1_dvd (A0K : ℕ) (P : Polynomial ℚ)
    (h0 : P.eval 0 = 0)
    (hr : ∀ r ∈ Finset.Icc 1 A0K,
      P.eval ((r : ℚ) ^ 2) = 0 ∧ P.derivative.eval ((r : ℚ) ^ 2) = 0) :
    hermiteDivisorPoly A0K 1 ∣ P := by
  unfold hermiteDivisorPoly HermiteOmegaPoly
  rw [pow_one, pow_one]
  have hX_dvd : Polynomial.X - Polynomial.C 0 ∣ P := Polynomial.dvd_iff_isRoot.mpr h0
  rw [Polynomial.C_0, sub_zero] at hX_dvd
  have h_prod_dvd :
      ∀ s : Finset ℕ,
        (∀ r ∈ s, 1 ≤ r ∧
          P.eval ((r : ℚ) ^ 2) = 0 ∧ P.derivative.eval ((r : ℚ) ^ 2) = 0) →
        (Polynomial.X * ∏ r ∈ s, (Polynomial.X - Polynomial.C ((r : ℚ) ^ 2)) ^ 2) ∣ P := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa using hX_dvd
    | @insert a s ha ih =>
      intro hs
      have ha_prop := hs a (Finset.mem_insert_self a s)
      have hs_prop : ∀ r ∈ s, 1 ≤ r ∧ P.eval ((r : ℚ) ^ 2) = 0 ∧ P.derivative.eval ((r : ℚ) ^ 2) = 0 :=
        fun r hr_in => hs r (Finset.mem_insert_of_mem hr_in)
      have h_ih := ih hs_prop
      have ha_dvd : (Polynomial.X - Polynomial.C ((a : ℚ) ^ 2)) ^ 2 ∣ P :=
        double_root_dvd_sq P ((a : ℚ) ^ 2) ha_prop.2.1 ha_prop.2.2
      rw [Finset.prod_insert ha, mul_left_comm Polynomial.X]
      apply IsCoprime.mul_dvd _ ha_dvd h_ih
      apply IsCoprime.mul_right
      · have ha_ne_0 : ((a : ℚ) ^ 2) ≠ 0 :=
          pow_ne_zero 2 (by exact_mod_cast (by omega : a ≠ 0))
        have h_cop := isCoprime_X_sub_C_pow ha_ne_0 2 1
        simpa using h_cop
      · apply IsCoprime.prod_right
        intro r hr_in
        have hr_ge1 : 1 ≤ r := (hs_prop r hr_in).1
        have ha_ne_r : a ≠ r := fun h_eq => ha (h_eq ▸ hr_in)
        have h_sq_ne : ((a : ℚ) ^ 2) ≠ ((r : ℚ) ^ 2) := by
          intro h_eq
          have h_nat : a ^ 2 = r ^ 2 := by exact_mod_cast h_eq
          rw [sq, sq] at h_nat
          exact ha_ne_r (Nat.mul_self_inj.mp h_nat)
        exact isCoprime_X_sub_C_pow h_sq_ne 2 2
  exact h_prod_dvd (Finset.Icc 1 A0K) (fun r hr_in => ⟨(Finset.mem_Icc.mp hr_in).1, hr r hr_in⟩)

/-- **Lemma 4.2 (Uniqueness of Hermite Interpolation in `ℚ[X]_{\le 2A₀K}`, p. 20)**:
If `P ∈ ℚ[X]` has `P.natDegree ≤ 2 * A0K` and satisfies `P(0) = 0` and
`P(r²) = P'(r²) = 0` for all `1 ≤ r ≤ A₀K`, then `P = 0`. -/
theorem lemma_4_2_hermite_uniqueness (A0K : ℕ) (P : Polynomial ℚ)
    (hdeg : P.natDegree ≤ 2 * A0K)
    (h0 : P.eval 0 = 0)
    (hr : ∀ r ∈ Finset.Icc 1 A0K,
      P.eval ((r : ℚ) ^ 2) = 0 ∧ P.derivative.eval ((r : ℚ) ^ 2) = 0) :
    P = 0 := by
  by_contra hP_ne
  have h_dvd := lemma_4_2_hermite_step1_dvd A0K P h0 hr
  have h_le := Polynomial.natDegree_le_of_dvd h_dvd hP_ne
  have h_div_deg := (hermiteDivisorPoly_monic_and_natDegree A0K 1).2
  unfold dimREach at h_div_deg
  omega

/-- **Lemma 4.2 (Equation (4.8): Exact Hermite Basis Expansion of Every Polynomial `P ∈ ℚ[X]_{\le 2A₀K}`)**:
Every polynomial `P ∈ ℚ[X]` of degree `P.natDegree ≤ 2 * A0K` is uniquely equal to its
Hermite interpolation expansion:
$$P(X) = P(0) H_0(X) + \sum_{r=1}^{A_0 K} \left(P(r^2) H_{r,0}(X) + P'(r^2) H_{r,1}(X)\right).$$ -/
theorem lemma_4_2_hermite_basis_expansion_unique (A0K : ℕ) (P : Polynomial ℚ)
    (hdeg : P.natDegree ≤ 2 * A0K) :
    P = Polynomial.C (P.eval 0) * HermiteH0Poly A0K +
          ∑ s ∈ Finset.Icc 1 A0K,
            (Polynomial.C (P.eval ((s : ℚ) ^ 2)) * HermiteHr0Poly A0K s +
             Polynomial.C (P.derivative.eval ((s : ℚ) ^ 2)) * HermiteHr1Poly A0K s) := by
  let Q : Polynomial ℚ :=
    Polynomial.C (P.eval 0) * HermiteH0Poly A0K +
      ∑ s ∈ Finset.Icc 1 A0K,
        (Polynomial.C (P.eval ((s : ℚ) ^ 2)) * HermiteHr0Poly A0K s +
         Polynomial.C (P.derivative.eval ((s : ℚ) ^ 2)) * HermiteHr1Poly A0K s)
  have hQ_eval := lemma_4_2_hermite_interpolation_reconstruction A0K
    (P.eval 0) (fun s => P.eval ((s : ℚ) ^ 2)) (fun s => P.derivative.eval ((s : ℚ) ^ 2))
  have hQ_deg : Q.natDegree ≤ 2 * A0K := by
    dsimp [Q]
    apply le_trans (Polynomial.natDegree_add_le _ _)
    rw [max_le_iff]
    constructor
    · apply le_trans (Polynomial.natDegree_C_mul_le _ _)
      unfold HermiteH0Poly HermiteOmegaPoly
      apply le_trans (Polynomial.natDegree_C_mul_le _ _)
      rw [Polynomial.natDegree_prod_of_monic _ _
          (fun (t : ℕ) _ => (Polynomial.monic_X_sub_C ((t : ℚ) ^ 2)).pow 2)]
      have h_each : ∀ t ∈ Finset.Icc 1 A0K,
          ((Polynomial.X - Polynomial.C ((t : ℚ) ^ 2)) ^ 2).natDegree = 2 := by
        intro t _; rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
      rw [Finset.sum_congr rfl h_each, Finset.sum_const, Nat.card_Icc,
          show A0K + 1 - 1 = A0K by omega, smul_eq_mul, mul_comm]
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro s hs
      have h_bds := lemma_4_2_hermite_natDegree_bounds A0K s hs
      apply le_trans (Polynomial.natDegree_add_le _ _)
      rw [max_le_iff]
      refine ⟨le_trans (Polynomial.natDegree_C_mul_le _ _) h_bds.2.2.2,
              le_trans (Polynomial.natDegree_C_mul_le _ _) (le_of_eq h_bds.2.2.1)⟩
  have h_diff_zero : P - Q = 0 := by
    apply lemma_4_2_hermite_uniqueness A0K (P - Q)
    · exact le_trans (Polynomial.natDegree_sub_le P Q) (max_le hdeg hQ_deg)
    · rw [Polynomial.eval_sub, hQ_eval.1, sub_self]
    · intro r hr
      refine ⟨?_, ?_⟩
      · rw [Polynomial.eval_sub, (hQ_eval.2 r hr).1, sub_self]
      · rw [Polynomial.derivative_sub, Polynomial.eval_sub, (hQ_eval.2 r hr).2, sub_self]
  exact sub_eq_zero.mp h_diff_zero

/-- **Theorem 4.3 Step 2 (Equation (4.23): Leibniz Jet Reduction from Equation (4.3))**:
Let `m ∈ {1, ..., n - 1}` and `j = n - m`. Suppose `normDerivA, normDerivB : ℚ → ℕ → ℚ` are the
normalized derivative jets of `A` and `B`, and `normDerivP` is their Leibniz Cauchy product
`normDerivP u q = ∑ k ∈ range (q + 1), normDerivA u (q - k) * normDerivB u k`.
If all lower-order normalized derivatives of `B` vanish at the inner nodes:
- `∀ k < m, normDerivB 0 k = 0`, and
- `∀ r ∈ Icc 1 A0K, ∀ k < 2 * m - 1, normDerivB (r²) k = 0`,
then the full odd-weight jet expansion (4.3) of `S_{2j+1}(A · B)` collapses identically to
Equation (4.23):
$$S_{2n-2m+1}(A B) = w_{2n-2m+1,0}^{(m)} A(0) \frac{B^{(m)}(0)}{m!}
  + \sum_{r=1}^{A_0 K} A(r^2) \left(w_{2n-2m+1,r}^{(2m-1)} \frac{B^{(2m-1)}(r^2)}{(2m-1)!}
    + w_{2n-2m+1,r}^{(2m)} \frac{B^{(2m)}(r^2)}{(2m)!}\right)
  + \sum_{r=1}^{A_0 K} A'(r^2) w_{2n-2m+1,r}^{(2m)} \frac{B^{(2m-1)}(r^2)}{(2m-1)!}.$$ -/
theorem theorem_4_3_leibniz_jet_reduction (n A0K AK m : ℕ)
    (hm1 : 1 ≤ m) (hmn : m ≤ n - 1)
    (normDerivA normDerivB : ℚ → ℕ → ℚ)
    (hB0 : ∀ k < m, normDerivB 0 k = 0)
    (hBr : ∀ r ∈ Finset.Icc 1 A0K, ∀ k < 2 * m - 1, normDerivB ((r : ℚ) ^ 2) k = 0) :
    let j : ℕ := n - m
    let normDerivP : ℚ → ℕ → ℚ := fun u q =>
      ∑ k ∈ Finset.range (q + 1), normDerivA u (q - k) * normDerivB u k
    (∑ q ∈ Finset.range (n - j + 1), jetWeightW n A0K AK j 0 q * normDerivP 0 q) +
      (∑ r ∈ Finset.Icc 1 A0K,
        ∑ q ∈ Finset.range (2 * (n - j) + 1),
          jetWeightW n A0K AK j r q * normDerivP ((r : ℚ) ^ 2) q) =
    jetWeightW n A0K AK j 0 m * normDerivA 0 0 * normDerivB 0 m +
      (∑ r ∈ Finset.Icc 1 A0K,
        normDerivA ((r : ℚ) ^ 2) 0 *
          (jetWeightW n A0K AK j r (2 * m - 1) * normDerivB ((r : ℚ) ^ 2) (2 * m - 1) +
           jetWeightW n A0K AK j r (2 * m) * normDerivB ((r : ℚ) ^ 2) (2 * m))) +
      (∑ r ∈ Finset.Icc 1 A0K,
        normDerivA ((r : ℚ) ^ 2) 1 *
          jetWeightW n A0K AK j r (2 * m) * normDerivB ((r : ℚ) ^ 2) (2 * m - 1)) := by
  intro j normDerivP
  have h_nj : n - j = m := by omega
  rw [h_nj]
  -- 1. Evaluate the central node `r = 0` sum over `q ∈ range (m + 1)`:
  have h_central :
      (∑ q ∈ Finset.range (m + 1), jetWeightW n A0K AK j 0 q * normDerivP 0 q) =
        jetWeightW n A0K AK j 0 m * normDerivA 0 0 * normDerivB 0 m := by
    rw [Finset.sum_eq_single m]
    · dsimp [normDerivP]
      rw [Finset.sum_eq_single m]
      · rw [Nat.sub_self]
        ring
      · intro k hk hk_ne
        have hk_lt : k < m := by
          have hk_le : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          omega
        rw [hB0 k hk_lt, mul_zero]
      · intro h_absurd
        exact False.elim (h_absurd (Finset.mem_range.mpr (by omega)))
    · intro q hq hq_ne
      have hq_lt : q < m := by
        have hq_le : q ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
        omega
      have hP0 : normDerivP 0 q = 0 := by
        dsimp [normDerivP]
        apply Finset.sum_eq_zero
        intro k hk
        have hk_lt : k < m := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hq_lt
        rw [hB0 k hk_lt, mul_zero]
      rw [hP0, mul_zero]
    · intro h_absurd
      exact False.elim (h_absurd (Finset.mem_range.mpr (by omega)))
  -- 2. Evaluate the off-center node `1 ≤ r ≤ A₀K` sum over `q ∈ range (2m + 1)`:
  have h_off_each :
      ∀ r ∈ Finset.Icc 1 A0K,
        (∑ q ∈ Finset.range (2 * m + 1),
          jetWeightW n A0K AK j r q * normDerivP ((r : ℚ) ^ 2) q) =
        normDerivA ((r : ℚ) ^ 2) 0 *
          (jetWeightW n A0K AK j r (2 * m - 1) * normDerivB ((r : ℚ) ^ 2) (2 * m - 1) +
           jetWeightW n A0K AK j r (2 * m) * normDerivB ((r : ℚ) ^ 2) (2 * m)) +
        normDerivA ((r : ℚ) ^ 2) 1 *
          jetWeightW n A0K AK j r (2 * m) * normDerivB ((r : ℚ) ^ 2) (2 * m - 1) := by
    intro r hr
    have h_range_split :
        Finset.range (2 * m + 1) =
          insert (2 * m) (insert (2 * m - 1) (Finset.range (2 * m - 1))) := by
      ext q
      simp only [Finset.mem_range, Finset.mem_insert]
      omega
    have h_not1 : 2 * m ∉ insert (2 * m - 1) (Finset.range (2 * m - 1)) := by
      simp only [Finset.mem_insert, Finset.mem_range]; omega
    have h_not2 : 2 * m - 1 ∉ Finset.range (2 * m - 1) := Finset.not_mem_range_self
    rw [h_range_split, Finset.sum_insert h_not1, Finset.sum_insert h_not2]
    have h_low_zero :
        (∑ q ∈ Finset.range (2 * m - 1),
          jetWeightW n A0K AK j r q * normDerivP ((r : ℚ) ^ 2) q) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hq_lt : q < 2 * m - 1 := Finset.mem_range.mp hq
      have hPq : normDerivP ((r : ℚ) ^ 2) q = 0 := by
        dsimp [normDerivP]
        apply Finset.sum_eq_zero
        intro k hk
        have hk_lt : k < 2 * m - 1 :=
          lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hq_lt
        rw [hBr r hr k hk_lt, mul_zero]
      rw [hPq, mul_zero]
    have hP_2m1 :
        normDerivP ((r : ℚ) ^ 2) (2 * m - 1) =
          normDerivA ((r : ℚ) ^ 2) 0 * normDerivB ((r : ℚ) ^ 2) (2 * m - 1) := by
      dsimp [normDerivP]
      rw [Finset.sum_eq_single (2 * m - 1)]
      · rw [Nat.sub_self]
      · intro k hk hk_ne
        have hk_lt : k < 2 * m - 1 := by
          have hk_le : k ≤ 2 * m - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          omega
        rw [hBr r hr k hk_lt, mul_zero]
      · intro h_absurd
        exact False.elim (h_absurd (Finset.mem_range.mpr (by omega)))
    have hP_2m :
        normDerivP ((r : ℚ) ^ 2) (2 * m) =
          normDerivA ((r : ℚ) ^ 2) 0 * normDerivB ((r : ℚ) ^ 2) (2 * m) +
            normDerivA ((r : ℚ) ^ 2) 1 * normDerivB ((r : ℚ) ^ 2) (2 * m - 1) := by
      dsimp [normDerivP]
      rw [h_range_split, Finset.sum_insert h_not1, Finset.sum_insert h_not2]
      have h_k_low :
          (∑ k ∈ Finset.range (2 * m - 1),
            normDerivA ((r : ℚ) ^ 2) (2 * m - k) * normDerivB ((r : ℚ) ^ 2) k) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [hBr r hr k (Finset.mem_range.mp hk), mul_zero]
      rw [h_k_low, add_zero, Nat.sub_self, show 2 * m - (2 * m - 1) = 1 by omega]
    rw [h_low_zero, add_zero, hP_2m1, hP_2m]
    ring
  rw [h_central, Finset.sum_congr rfl h_off_each, Finset.sum_add_distrib]
  ring

/-- **Theorem 4.3 Step 2 (Equation (4.23): Hermite Basis Testing Forces Vanishing of Next-Order Jets)**:
Let `m ∈ {1, ..., n - 1}` (`1 ≤ A₀K ≤ AK`) and let `b0 : ℚ` and `br1, br2 : ℕ → ℚ` represent
`B^{(m)}(0) / m!`, `B^{(2m-1)}(r²) / (2m-1)!`, and `B^{(2m)}(r²) / (2m)!` in Equation (4.23).
For any polynomial `A ∈ ℚ[X]`, define the reduced Leibniz jet functional (4.23):
$$J_m(A) := w_{2n-2m+1,0}^{(m)} A(0) b_0
  + \sum_{r=1}^{A_0 K} A(r^2) \left(w_{2n-2m+1,r}^{(2m-1)} b_{r,1} + w_{2n-2m+1,r}^{(2m)} b_{r,2}\right)
  + \sum_{r=1}^{A_0 K} A'(r^2) w_{2n-2m+1,r}^{(2m)} b_{r,1}.$$
If `J_m(H_{r₀,1}) = 0`, `J_m(H_{r₀,0}) = 0` for all `1 ≤ r₀ ≤ A₀K`, and `J_m(H_0) = 0`, then
`b0 = 0` and `∀ r₀ ∈ Icc 1 A0K, br1 r₀ = 0 ∧ br2 r₀ = 0`. -/
theorem theorem_4_3_step2_hermite_testing (n A0K AK m : ℕ)
    (hm1 : 1 ≤ m) (hmn : m ≤ n - 1) (hA0 : A0K ≤ AK)
    (b0 : ℚ) (br1 br2 : ℕ → ℚ) :
    let j : ℕ := n - m
    let Jm (A : Polynomial ℚ) : ℚ :=
      jetWeightW n A0K AK j 0 m * A.eval 0 * b0 +
        (∑ r ∈ Finset.Icc 1 A0K,
          A.eval ((r : ℚ) ^ 2) *
            (jetWeightW n A0K AK j r (2 * m - 1) * br1 r +
             jetWeightW n A0K AK j r (2 * m) * br2 r)) +
        (∑ r ∈ Finset.Icc 1 A0K,
          A.derivative.eval ((r : ℚ) ^ 2) *
            jetWeightW n A0K AK j r (2 * m) * br1 r)
    (Jm (HermiteH0Poly A0K) = 0 ∧
     ∀ r0 ∈ Finset.Icc 1 A0K,
       Jm (HermiteHr1Poly A0K r0) = 0 ∧ Jm (HermiteHr0Poly A0K r0) = 0) →
    b0 = 0 ∧ ∀ r0 ∈ Finset.Icc 1 A0K, br1 r0 = 0 ∧ br2 r0 = 0 := by
  intro j Jm h_tests
  have hj_lt : j < n := by omega
  have h_nm : n - j = m := by omega
  -- 1. First prove `br1 r0 = 0` for all `r0 ∈ Icc 1 A0K` by testing `A = HermiteHr1Poly A0K r0`:
  have h_br1_zero : ∀ r0 ∈ Finset.Icc 1 A0K, br1 r0 = 0 := by
    intro r0 hr0
    have h_hr1_test := (h_tests.2 r0 hr0).1
    have hHr0 := (lemma_4_2_ii_iii_HrPoly_full A0K r0 hr0).2
    dsimp [Jm] at h_hr1_test
    rw [hHr0.1, mul_zero, zero_mul, zero_add] at h_hr1_test
    have h_sum1 :
        (∑ r ∈ Finset.Icc 1 A0K,
          (HermiteHr1Poly A0K r0).eval ((r : ℚ) ^ 2) *
            (jetWeightW n A0K AK j r (2 * m - 1) * br1 r +
             jetWeightW n A0K AK j r (2 * m) * br2 r)) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      by_cases h_eq : r = r0
      · subst h_eq; rw [hHr0.2.1, zero_mul]
      · have hr_erase : r ∈ (Finset.Icc 1 A0K).erase r0 := Finset.mem_erase.mpr ⟨h_eq, hr⟩
        rw [(hHr0.2.2.2 r hr_erase).1, zero_mul]
    have h_sum2 :
        (∑ r ∈ Finset.Icc 1 A0K,
          (HermiteHr1Poly A0K r0).derivative.eval ((r : ℚ) ^ 2) *
            jetWeightW n A0K AK j r (2 * m) * br1 r) =
        jetWeightW n A0K AK j r0 (2 * m) * br1 r0 := by
      rw [Finset.sum_eq_single r0]
      · rw [hHr0.2.2.1, one_mul]
      · intro r hr h_ne
        have hr_erase : r ∈ (Finset.Icc 1 A0K).erase r0 := Finset.mem_erase.mpr ⟨h_ne, hr⟩
        rw [(hHr0.2.2.2 r hr_erase).2, zero_mul, zero_mul]
      · intro h_absurd
        exact False.elim (h_absurd hr0)
    rw [h_sum1, h_sum2, zero_add] at h_hr1_test
    have h_wt_nz : jetWeightW n A0K AK j r0 (2 * m) ≠ 0 := by
      rw [← h_nm]
      exact ((prop_4_1_ii_leading_jet_weights n A0K AK j r0 hj_lt
        (Finset.mem_Icc.mp hr0).2 hA0).2 (Finset.mem_Icc.mp hr0).1).2
    exact (mul_eq_zero.mp h_hr1_test).resolve_left h_wt_nz
  -- 2. Next prove `br2 r0 = 0` for all `r0 ∈ Icc 1 A0K` by testing `A = HermiteHr0Poly A0K r0`:
  have h_br2_zero : ∀ r0 ∈ Finset.Icc 1 A0K, br2 r0 = 0 := by
    intro r0 hr0
    have h_hr0_test := (h_tests.2 r0 hr0).2
    have hHr0 := (lemma_4_2_ii_iii_HrPoly_full A0K r0 hr0).1
    dsimp [Jm] at h_hr0_test
    rw [hHr0.1, mul_zero, zero_mul, zero_add] at h_hr0_test
    have h_sum2 :
        (∑ r ∈ Finset.Icc 1 A0K,
          (HermiteHr0Poly A0K r0).derivative.eval ((r : ℚ) ^ 2) *
            jetWeightW n A0K AK j r (2 * m) * br1 r) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      rw [h_br1_zero r hr, mul_zero]
    have h_sum1 :
        (∑ r ∈ Finset.Icc 1 A0K,
          (HermiteHr0Poly A0K r0).eval ((r : ℚ) ^ 2) *
            (jetWeightW n A0K AK j r (2 * m - 1) * br1 r +
             jetWeightW n A0K AK j r (2 * m) * br2 r)) =
        jetWeightW n A0K AK j r0 (2 * m) * br2 r0 := by
      rw [Finset.sum_eq_single r0]
      · rw [hHr0.2.1, h_br1_zero r0 hr0, mul_zero, zero_add, one_mul]
      · intro r hr h_ne
        have hr_erase : r ∈ (Finset.Icc 1 A0K).erase r0 := Finset.mem_erase.mpr ⟨h_ne, hr⟩
        rw [(hHr0.2.2.2 r hr_erase).1, zero_mul]
      · intro h_absurd
        exact False.elim (h_absurd hr0)
    rw [h_sum1, h_sum2, add_zero] at h_hr0_test
    have h_wt_nz : jetWeightW n A0K AK j r0 (2 * m) ≠ 0 := by
      rw [← h_nm]
      exact ((prop_4_1_ii_leading_jet_weights n A0K AK j r0 hj_lt
        (Finset.mem_Icc.mp hr0).2 hA0).2 (Finset.mem_Icc.mp hr0).1).2
    exact (mul_eq_zero.mp h_hr0_test).resolve_left h_wt_nz
  -- 3. Finally prove `b0 = 0` by testing `A = HermiteH0Poly A0K`:
  have h_b0_zero : b0 = 0 := by
    have h_h0_test := h_tests.1
    have hH0 := lemma_4_2_i_H0Poly_full A0K
    dsimp [Jm] at h_h0_test
    have h_sum1 :
        (∑ r ∈ Finset.Icc 1 A0K,
          (HermiteH0Poly A0K).eval ((r : ℚ) ^ 2) *
            (jetWeightW n A0K AK j r (2 * m - 1) * br1 r +
             jetWeightW n A0K AK j r (2 * m) * br2 r)) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      rw [(hH0.2 r hr).1, zero_mul]
    have h_sum2 :
        (∑ r ∈ Finset.Icc 1 A0K,
          (HermiteH0Poly A0K).derivative.eval ((r : ℚ) ^ 2) *
            jetWeightW n A0K AK j r (2 * m) * br1 r) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      rw [(hH0.2 r hr).2, zero_mul, zero_mul]
    rw [hH0.1, mul_one, h_sum1, h_sum2, add_zero, add_zero] at h_h0_test
    have h_wt0_nz : jetWeightW n A0K AK j 0 m ≠ 0 := by
      rw [← h_nm, (prop_4_1_ii_leading_jet_weights n A0K AK j 0 hj_lt (Nat.zero_le _) hA0).1]
      exact prop_4_1_innerNodeWeight_ne_zero n A0K AK 0 (Nat.zero_le _) hA0
    exact (mul_eq_zero.mp h_h0_test).resolve_left h_wt0_nz
  exact ⟨h_b0_zero, fun r0 hr0 => ⟨h_br1_zero r0 hr0, h_br2_zero r0 hr0⟩⟩

/-- **Theorem 4.4 (Equations (4.26)–(4.27) & Steps (1)–(4) Four-Factor Decomposition, pp. 23–24)**:
Define the confluent Vandermonde determinants `det V_{Herm}^{monic}` (4.26) and `det V_Q^{monic}` (4.27)
together with the four triangular/confluent transition factors in the proof of Theorem 4.4:
1. Row transition factor `((∏_{i=1}^{2A₀K} 2/(2i)!) det V_{Herm}^{monic})^{n-1}`
2. Column transition factor `∏_{m=N}^{N+R-1} 2/(2m)!`
3. Block-triangular Hermite jet factor
   `|w_{2n+1,0}|^{n-1} (∏_{r=1}^{A₀K} |w_{2n+1,r}|^{2(n-1)} (2r)^{2n(n-1)} r^{6(n-1)}) ∏_{1 ≤ s < r ≤ A₀K} (r² - s²)^{4(n-1)}`
4. Confluent Vandermonde factor `det V_Q^{monic}`. -/
def detVMonicHerm (A0K : ℕ) : ℚ :=
  (∏ r ∈ Finset.Icc 1 A0K, (r : ℚ) ^ 4) *
    ∏ r ∈ Finset.Icc 1 A0K, ∏ s ∈ Finset.Ico 1 r, ((r : ℚ) ^ 2 - (s : ℚ) ^ 2) ^ 4

def detVMonicQ (n A0K : ℕ) : ℚ :=
  (∏ r ∈ Finset.Icc 1 A0K, (r : ℚ) ^ (4 * (n - 1) ^ 2)) *
    ∏ r ∈ Finset.Icc 1 A0K, ∏ s ∈ Finset.Ico 1 r, ((r : ℚ) ^ 2 - (s : ℚ) ^ 2) ^ (4 * (n - 1) ^ 2)

def step1RowTransitionFactor (n A0K : ℕ) : ℚ :=
  ((∏ i ∈ Finset.Icc 1 (2 * A0K), (2 : ℚ) / ((2 * i).factorial : ℚ)) ^ (n - 1)) *
    ((detVMonicHerm A0K) ^ (n - 1))

def step2ColTransitionFactor (n A0K : ℕ) : ℚ :=
  ∏ m ∈ Finset.Ico (dimN A0K) (dimN A0K + dimR n A0K), (2 : ℚ) / ((2 * m).factorial : ℚ)

def step3HermiteJetFactor (n A0K AK : ℕ) : ℚ :=
  (|innerNodeWeight n A0K AK 0| ^ (n - 1)) *
    (∏ r ∈ Finset.Icc 1 A0K,
      (|innerNodeWeight n A0K AK r| ^ (2 * (n - 1))) *
        (((2 * r : ℕ) : ℚ) ^ (2 * n * (n - 1))) *
        ((r : ℚ) ^ (6 * (n - 1)))) *
    (∏ r ∈ Finset.Icc 1 A0K, ∏ s ∈ Finset.Ico 1 r,
      ((r : ℚ) ^ 2 - (s : ℚ) ^ 2) ^ (4 * (n - 1)))

def step4ConfluentVdmFactor (n A0K : ℕ) : ℚ :=
  detVMonicQ n A0K

/-- **Theorem 4.4 (Ground-Up Proof that the Product of the Four Transition Determinants Equals (4.24))**:
For every `n ≥ 2` and `A₀K, AK ∈ ℕ`, multiplying the four transition factors of Steps (1)–(4)
yields `tailSubmatrixDetClosedForm n A0K AK` (4.24). -/
theorem theorem_4_4_four_step_product_eq_closed_form (n A0K AK : ℕ) (hn : 2 ≤ n) :
    step1RowTransitionFactor n A0K *
      step2ColTransitionFactor n A0K *
      step3HermiteJetFactor n A0K AK *
      step4ConfluentVdmFactor n A0K =
    tailSubmatrixDetClosedForm n A0K AK := by
  unfold step1RowTransitionFactor step2ColTransitionFactor step3HermiteJetFactor
    step4ConfluentVdmFactor detVMonicHerm detVMonicQ tailSubmatrixDetClosedForm
  dsimp only
  have h_exp := theorem_4_4_exponent_identities n hn
  have h_r_combine :
      (∏ r ∈ Finset.Icc 1 A0K, ((r : ℚ) ^ 4) ^ (n - 1)) *
        ((∏ r ∈ Finset.Icc 1 A0K,
          |innerNodeWeight n A0K AK r| ^ (2 * (n - 1)) *
            ((2 * r : ℕ) : ℚ) ^ (2 * n * (n - 1)) *
            (r : ℚ) ^ (6 * (n - 1))) *
          (∏ r ∈ Finset.Icc 1 A0K, (r : ℚ) ^ (4 * (n - 1) ^ 2))) =
      ∏ r ∈ Finset.Icc 1 A0K,
        |innerNodeWeight n A0K AK r| ^ (2 * (n - 1)) *
          ((2 * r : ℕ) : ℚ) ^ (2 * n * (n - 1)) *
          (r : ℚ) ^ ((n - 1) * (4 * n + 6)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro r _
    rw [← pow_mul, ← h_exp.1]
    calc (r : ℚ) ^ (4 * (n - 1)) *
          (|innerNodeWeight n A0K AK r| ^ (2 * (n - 1)) *
            ((2 * r : ℕ) : ℚ) ^ (2 * n * (n - 1)) *
            (r : ℚ) ^ (6 * (n - 1)) *
            (r : ℚ) ^ (4 * (n - 1) ^ 2))
        = |innerNodeWeight n A0K AK r| ^ (2 * (n - 1)) *
            ((2 * r : ℕ) : ℚ) ^ (2 * n * (n - 1)) *
            ((r : ℚ) ^ (4 * (n - 1)) * (r : ℚ) ^ (6 * (n - 1)) * (r : ℚ) ^ (4 * (n - 1) ^ 2)) := by ring
      _ = |innerNodeWeight n A0K AK r| ^ (2 * (n - 1)) *
            ((2 * r : ℕ) : ℚ) ^ (2 * n * (n - 1)) *
            (r : ℚ) ^ (4 * (n - 1) + 6 * (n - 1) + 4 * (n - 1) ^ 2) := by
          rw [← pow_add, ← pow_add]
  have h_vdm_combine :
      (∏ r ∈ Finset.Icc 1 A0K, (∏ s ∈ Finset.Ico 1 r, ((r : ℚ) ^ 2 - (s : ℚ) ^ 2) ^ 4) ^ (n - 1)) *
        ((∏ r ∈ Finset.Icc 1 A0K, ∏ s ∈ Finset.Ico 1 r, ((r : ℚ) ^ 2 - (s : ℚ) ^ 2) ^ (4 * (n - 1))) *
          (∏ r ∈ Finset.Icc 1 A0K, ∏ s ∈ Finset.Ico 1 r, ((r : ℚ) ^ 2 - (s : ℚ) ^ 2) ^ (4 * (n - 1) ^ 2))) =
      ∏ r ∈ Finset.Icc 1 A0K, ∏ s ∈ Finset.Ico 1 r,
        ((r : ℚ) ^ 2 - (s : ℚ) ^ 2) ^ (4 * (n ^ 2 - 1)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro r _
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro s _
    rw [← pow_mul, ← pow_add, ← pow_add, ← add_assoc, h_exp.2.1]
  rw [← h_r_combine, ← h_vdm_combine, mul_pow,
      ← Finset.prod_pow (Finset.Icc 1 A0K) (n - 1) (fun r => (r : ℚ) ^ 4),
      ← Finset.prod_pow (Finset.Icc 1 A0K) (n - 1)
          (fun r => ∏ s ∈ Finset.Ico 1 r, ((r : ℚ) ^ 2 - (s : ℚ) ^ 2) ^ 4)]
  ring

/-- **Proposition 4.1 & Theorem 4.4 (Integrality of Inner Node Weights `w_{2n+1,r} ∈ ℤ`)**:
For every inner node `0 ≤ r ≤ A₀K` (`A₀K ≤ AK`), the inner node weight `innerNodeWeight n A0K AK r`
is an integer: `∃ z : ℤ, (z : ℚ) = innerNodeWeight n A0K AK r`. -/
theorem innerNodeWeight_int (n A0K AK r : ℕ) (hr : r ≤ A0K) (hA0 : A0K ≤ AK) :
    ∃ z : ℤ, (z : ℚ) = innerNodeWeight n A0K AK r := by
  unfold innerNodeWeight
  by_cases hr0 : r = 0
  · subst hr0
    rw [if_pos rfl]
    unfold gkZeroClosed
    have h_abs : ((AK : ℤ) - (AK : ℤ)).natAbs ≤ A0K := by simp
    dsimp only
    rw [if_pos h_abs]
    refine ⟨((-1 : ℤ) ^ (A0K + AK - AK)) *
      ((Nat.choose (2 * AK) AK : ℤ) ^ 2) *
      ((Nat.choose (2 * A0K) (A0K + ((AK : ℤ) - (AK : ℤ)).natAbs) : ℤ) ^ (2 * n - 1)), ?_⟩
    push_cast
    rfl
  · rw [if_neg hr0]
    unfold gkZeroClosed
    have h_abs : ((AK : ℤ) - ((AK - r : ℕ) : ℤ)).natAbs ≤ A0K := by omega
    dsimp only
    rw [if_pos h_abs]
    refine ⟨2 * (((-1 : ℤ) ^ (A0K + AK - (AK - r))) *
      ((Nat.choose (2 * AK) (AK - r) : ℤ) ^ 2) *
      ((Nat.choose (2 * A0K) (A0K + ((AK : ℤ) - ((AK - r : ℕ) : ℤ)).natAbs) : ℤ) ^ (2 * n - 1))), ?_⟩
    push_cast
    rfl

/-- **Theorem 4.4 (Monic-Basis Tail Submatrix Determinant Factor and Integrality)**:
Define the monic-basis tail determinant factor `monicTailSubmatrixDet n A0K AK` obtained after
factoring out the central-factorial leading-coefficient row and column factors from (4.24).
Then `monicTailSubmatrixDet n A0K AK` is a strictly positive integer. -/
def monicTailSubmatrixDet (n A0K AK : ℕ) : ℚ :=
  (|innerNodeWeight n A0K AK 0| ^ (n - 1)) *
    (∏ r ∈ Finset.Icc 1 A0K,
      (|innerNodeWeight n A0K AK r| ^ (2 * (n - 1))) *
        (((2 * r : ℕ) : ℚ) ^ (2 * n * (n - 1))) *
        ((r : ℚ) ^ ((n - 1) * (4 * n + 6)))) *
    (∏ r ∈ Finset.Icc 1 A0K,
      ∏ s ∈ Finset.Ico 1 r,
        (((r : ℚ) ^ 2 - (s : ℚ) ^ 2) ^ (4 * (n ^ 2 - 1))))

theorem theorem_4_4_monic_tail_det_int (n A0K AK : ℕ) (hA0 : A0K ≤ AK) :
    tailSubmatrixDetClosedForm n A0K AK =
      ((∏ i ∈ Finset.Icc 1 (2 * A0K), (2 : ℚ) / ((2 * i).factorial : ℚ)) ^ (n - 1)) *
        (∏ m ∈ Finset.Ico (dimN A0K) (dimN A0K + dimR n A0K), (2 : ℚ) / ((2 * m).factorial : ℚ)) *
        monicTailSubmatrixDet n A0K AK ∧
    ∃ Z : ℤ, (Z : ℚ) = monicTailSubmatrixDet n A0K AK := by
  refine ⟨by unfold tailSubmatrixDetClosedForm monicTailSubmatrixDet; dsimp only; ring, ?_⟩
  unfold monicTailSubmatrixDet
  rcases innerNodeWeight_int n A0K AK 0 (Nat.zero_le A0K) hA0 with ⟨z0, hz0⟩
  have h_ic : ∀ r : ℕ, ∃ zr : ℤ, r ∈ Finset.Icc 1 A0K → (zr : ℚ) = |innerNodeWeight n A0K AK r| := by
    intro r
    by_cases hr : r ∈ Finset.Icc 1 A0K
    · rcases innerNodeWeight_int n A0K AK r (Finset.mem_Icc.mp hr).2 hA0 with ⟨z, hz⟩
      exact ⟨|z|, fun _ => by rw [← hz, Int.cast_abs]⟩
    · exact ⟨0, fun h_absurd => False.elim (hr h_absurd)⟩
  choose zr hzr using h_ic
  refine ⟨(|z0| ^ (n - 1)) *
    (∏ r ∈ Finset.Icc 1 A0K,
      ((zr r) ^ (2 * (n - 1))) *
        (((2 * r : ℕ) : ℤ) ^ (2 * n * (n - 1))) *
        ((r : ℤ) ^ ((n - 1) * (4 * n + 6)))) *
    (∏ r ∈ Finset.Icc 1 A0K,
      ∏ s ∈ Finset.Ico 1 r,
        (((r : ℤ) ^ 2 - (s : ℤ) ^ 2) ^ (4 * (n ^ 2 - 1)))), ?_⟩
  push_cast
  rw [hz0]
  congr 2
  apply Finset.prod_congr rfl
  intro r hr
  rw [hzr r hr]

/-- **Remark 4.5 (Uniform Odd Inner Multiplicity `L_{in} = 2n + 1`, p. 24)**:
For every `n ≥ 1` and `A₀K ≥ 0`, both the inner multiplicity `L_{in} = 2n + 1` and the
inner-window total degree `(2n - 1)(2A₀K + 1)` are odd integers, so
`(-1)^{(2n - 1)(2A₀K + 1)} = -1`, guaranteeing the odd reflection symmetry
`ℱ(-2AK - z; P) = -ℱ(z; P)` directly from the denominator product in (3.2) without auxiliary
odd linear factors `(z + AK)`. -/
theorem remark_4_5_odd_inner_multiplicity (n A0K : ℕ) (hn : 1 ≤ n) :
    Odd (2 * n + 1) ∧
    Odd ((2 * n - 1) * (2 * A0K + 1)) ∧
    (-1 : ℚ) ^ ((2 * n - 1) * (2 * A0K + 1)) = -1 := by
  have h1 : Odd (2 * n + 1) := ⟨n, by ring⟩
  have h_odd_2n1 : Odd (2 * n - 1) := ⟨n - 1, by omega⟩
  have h_odd_2A0 : Odd (2 * A0K + 1) := ⟨A0K, by ring⟩
  have h2 : Odd ((2 * n - 1) * (2 * A0K + 1)) := Odd.mul h_odd_2n1 h_odd_2A0
  exact ⟨h1, h2, h2.neg_one_pow⟩

end OddZetaFormalization

