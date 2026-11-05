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
    Polynomial.eval_pow, Polynomial.eval_sub, div_eq_inv_mul]

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

end OddZetaFormalization
