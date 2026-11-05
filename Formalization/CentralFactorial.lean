import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-!
# Section 2: Central Factorial Polynomials and Total Positivity

This module formalizes Section 2 of Prince Anand,
*"All Odd Zeta Values Are Linearly Independent Over ℚ"*:
- **Equation (2.1)**: Reflection-invariant variable `u := (z + AK)²` under `z ↦ -2AK - z`.
- **Definition 2.1**: Normalized central factorial polynomials `ℰ_m(u) ∈ ℚ[X]` (2.2).
- **Proposition 2.2**: Integer-square integrality and binomial representation
  `ℰ_m(r²) = C(r+m, 2m) + C(r+m-1, 2m) ∈ ℤ` (2.3), root-window vanishing `0 ≤ r < m` and
  diagonal normalization `ℰ_m(m²) = 1` (i), and `lcm(1, ..., 2m)^{2q}` Taylor coefficient
  integrality (2.4) (ii).
- **Proposition 2.3**: Unified closed-form first derivatives `ℰ_m'(r²)` for `0 ≤ r < m` across
  all three equivalent forms (2.7) and non-zero integer reciprocal `1 / ℰ_m'(r²) ∈ ℤ \ {0}` (2.8).
- **Proposition 2.4**: Second derivative identity `½ ℰ_m''(r²) = ℰ_m'(r²) T(m, r)` (2.10),
  value at `r = 0` (`-H_{m-1}^{(2)}`), and rational harmonic telescoping (2.11).
- **Theorem 2.5**: Arbitrary-order derivative formula (2.13), power sums `T_d(m, r)` (2.14),
  Newton's recurrence (2.15), `p`-adic denominator bound (2.16), degree-`2m` linear-`w`
  factorization (2.19)–(2.20), polynomial binomial identity (2.21), Vandermonde convolution (2.22),
  and uniform linear-shift valuation bound (2.23).
- **Theorem 2.6**: Strict total positivity `det_{1 ≤ i,j ≤ M} (ℰ_{r_j}(x_i²)) > 0` (2.24) via
  finite bidiagonal-binomial matrix factorization `ℰ_r(x²) = (1 + δ_{r,0})⁻¹ ∑_{y=0}^{x_M} B_{x,y} C_{y,r}`
  (2.25), Cauchy–Binet expansion (2.26), unit upper-triangular diagonal minor of `B` (2.27),
  and planar lattice-path positivity of `C_{y,r} = C(y+r, 2r)` (2.28).
-/

namespace OddZetaFormalization

open scoped BigOperators Polynomial

/-- **Equation (2.1)**: The reflection-invariant variable `u := (z + AK)²`. -/
def reflectionVar (AK : ℕ) (z : ℚ) : ℚ :=
  (z + (AK : ℚ)) ^ 2

/-- **Equation (2.1) Involution Invariance**: `u = (z + AK)²` is invariant under the reflection
involution `z ↦ -2AK - z` across the midpoint `z = -AK`. -/
theorem reflectionVar_involution (AK : ℕ) (z : ℚ) :
    reflectionVar AK (-2 * (AK : ℚ) - z) = reflectionVar AK z := by
  unfold reflectionVar
  ring

/-- **Definition 2.1 (Equation (2.2))**: The normalized central factorial polynomial
`ℰ_m(u) ∈ ℚ[X]` of degree `m` in `u`, defined for `m = 0` as `1` and for `m ≥ 1` as
$$\mathcal{E}_m(u) := \frac{2}{(2m)!} \prod_{t=0}^{m-1} (u - t^2).$$ -/
noncomputable def centralFactorialPoly (m : ℕ) : Polynomial ℚ :=
  if m = 0 then 1
  else Polynomial.C ((2 : ℚ) / ((2 * m).factorial : ℚ)) *
    ∏ t ∈ Finset.range m, (Polynomial.X - Polynomial.C ((t : ℚ) ^ 2))

/-- Direct evaluation of the normalized central factorial polynomial `ℰ_m(u)` at `u ∈ ℚ`. -/
def evalCentralFactorial (m : ℕ) (u : ℚ) : ℚ :=
  if m = 0 then 1
  else ((2 : ℚ) / ((2 * m).factorial : ℚ)) * ∏ t ∈ Finset.range m, (u - (t : ℚ) ^ 2)

/-- `Polynomial.eval u (centralFactorialPoly m)` agrees identically with `evalCentralFactorial m u`. -/
theorem eval_centralFactorialPoly (m : ℕ) (u : ℚ) :
    (centralFactorialPoly m).eval u = evalCentralFactorial m u := by
  unfold centralFactorialPoly evalCentralFactorial
  split_ifs with hm
  · simp
  · simp [Polynomial.eval_prod]

/-- At `m = 0`, `ℰ_0(u) = 1` for all `u` (Definition 2.1). -/
@[simp]
theorem evalCentralFactorial_zero (u : ℚ) : evalCentralFactorial 0 u = 1 := rfl

/-- Symmetry `ℰ_m((-r)²) = ℰ_m(r²)` for all `r ∈ ℤ`. -/
theorem evalCentralFactorial_neg_sq (m : ℕ) (r : ℤ) :
    evalCentralFactorial m (((-r : ℤ) : ℚ) ^ 2) = evalCentralFactorial m (((r : ℤ) : ℚ) ^ 2) := by
  congr 1
  push_cast
  ring

/-- The integer-valued binomial representation of `ℰ_m(r²)` from Proposition 2.2 (Equation (2.3)):
$$\mathcal{E}_m^{\mathrm{binom}}(r) := \binom{r+m}{2m} + \binom{r+m-1}{2m} \in \mathbb{N}.$$ -/
def centralFactorialBinomNat (m r : ℕ) : ℕ :=
  if m = 0 then 1
  else Nat.choose (r + m) (2 * m) + Nat.choose (r + m - 1) (2 * m)

/-- **Proposition 2.2(i) (Vanishing on the Root Window `0 ≤ r < m`)**:
For every integer `m ≥ 1` and every integer `0 ≤ r < m`, both `ℰ_m(r²) = 0` and
`\binom{r+m}{2m} + \binom{r+m-1}{2m} = 0`. -/
theorem prop_2_2_i_vanishing (m r : ℕ) (hr : r < m) :
    evalCentralFactorial m ((r : ℚ) ^ 2) = 0 ∧ centralFactorialBinomNat m r = 0 := by
  have hm0 : m ≠ 0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le r) hr)
  constructor
  · unfold evalCentralFactorial
    rw [if_neg hm0]
    have h_zero_prod : (∏ t ∈ Finset.range m, ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_range.mpr hr)
      ring
    rw [h_zero_prod, mul_zero]
  · unfold centralFactorialBinomNat
    rw [if_neg hm0]
    have h1 : Nat.choose (r + m) (2 * m) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    have h2 : Nat.choose (r + m - 1) (2 * m) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    omega

/-- Helper product identity in the proof of Proposition 2.2 (p. 6):
For all `m ≥ 1` and `r : ℕ`,
$$2 \prod_{t=0}^{m-1} (r^2 - t^2) = (2m)! \left(\binom{r+m}{2m} + \binom{r+m-1}{2m}\right)$$
in `ℚ`. -/
theorem centralFactorial_prod_eq_factorial_mul_binom (m r : ℕ) (hm : 1 ≤ m) :
    (2 : ℚ) * (∏ t ∈ Finset.range m, ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) =
      ((2 * m).factorial : ℚ) * ((Nat.choose (r + m) (2 * m) + Nat.choose (r + m - 1) (2 * m) : ℕ) : ℚ) := by
  induction' m with m ih
  · omega
  · rcases eq_or_lt_of_le hm with h_m0 | hm_pos
    · have hm_eq : m = 0 := by omega
      subst hm_eq
      simp only [Finset.range_one, Finset.prod_singleton, Nat.cast_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, Nat.mul_one,
        Nat.factorial_two, Nat.cast_ofNat, add_tsub_cancel_right]
      rcases r with _ | r
      · simp
      · have h_c1 : Nat.choose (r + 1 + 1) 2 * 2 = (r + 2) * (r + 1) := by
          have h := Nat.choose_succ_right_eq (r + 2) 1
          simpa [Nat.choose_one_right] using h
        have h_c2 : Nat.choose (r + 1) 2 * 2 = (r + 1) * r := by
          have h := Nat.choose_succ_right_eq (r + 1) 1
          simpa [Nat.choose_one_right] using h
        have h_two_mul : 2 * (Nat.choose (r + 1 + 1) 2 + Nat.choose (r + 1) 2) = 2 * (r + 1) ^ 2 := by
          calc 2 * (Nat.choose (r + 1 + 1) 2 + Nat.choose (r + 1) 2)
              = Nat.choose (r + 1 + 1) 2 * 2 + Nat.choose (r + 1) 2 * 2 := by ring
            _ = (r + 2) * (r + 1) + (r + 1) * r := by rw [h_c1, h_c2]
            _ = 2 * (r + 1) ^ 2 := by ring
        have h_q : (2 : ℚ) * ((Nat.choose (r + 1 + 1) 2 + Nat.choose (r + 1) 2 : ℕ) : ℚ) =
            (2 : ℚ) * (((r + 1 : ℕ) : ℚ) ^ 2) := by
          exact_mod_cast h_two_mul
        simpa using h_q.symm
    · have hm1 : 1 ≤ m := by omega
      specialize ih hm1
      rw [Finset.prod_range_succ, ← mul_assoc, ih]
      rcases lt_or_ge r (m + 1) with hr_lt | hr_ge
      · have h_lhs : ((r : ℚ) ^ 2 - (m : ℚ) ^ 2) = 0 ∨
            ((Nat.choose (r + m) (2 * m) + Nat.choose (r + m - 1) (2 * m) : ℕ) : ℚ) = 0 := by
          rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hr_lt) with rfl | hr_lt_m
          · left; ring
          · right
            have h1 : Nat.choose (r + m) (2 * m) = 0 := Nat.choose_eq_zero_of_lt (by omega)
            have h2 : Nat.choose (r + m - 1) (2 * m) = 0 := Nat.choose_eq_zero_of_lt (by omega)
            simp [h1, h2]
        have h_rhs1 : Nat.choose (r + (m + 1)) (2 * (m + 1)) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        have h_rhs2 : Nat.choose (r + m) (2 * (m + 1)) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        rcases h_lhs with h0 | h0
        · simp [h0, h_rhs1, h_rhs2]
        · simp [h0, h_rhs1, h_rhs2]
      · -- For r ≥ m + 1, use the absorption identity for binomial coefficients:
        have h_choose_succ : ∀ n k : ℕ, Nat.choose n (k + 1) * (k + 1) = (n - k) * Nat.choose n k := by
          intro n k
          rw [Nat.choose_succ_right_eq, mul_comm]
        have h_succ_choose : ∀ n k : ℕ, (n + 1) * Nat.choose n k = Nat.choose (n + 1) (k + 1) * (k + 1) := by
          intro n k
          simpa [Nat.succ_eq_add_one] using Nat.succ_mul_choose_eq n k
        have h_step1 :
            (2 * m + 2) * (2 * m + 1) * Nat.choose (r + m + 1) (2 * m + 2) =
              (r + m + 1) * (r - m) * Nat.choose (r + m) (2 * m) := by
          have h_pasc := h_succ_choose (r + m) (2 * m + 1)
          have hc2 := h_choose_succ (r + m) (2 * m)
          have h_sub : r + m - 2 * m = r - m := by omega
          calc (2 * m + 2) * (2 * m + 1) * Nat.choose (r + m + 1) (2 * m + 2)
              = (2 * m + 1) * (Nat.choose (r + m + 1) (2 * m + 1 + 1) * (2 * m + 1 + 1)) := by ring
            _ = (2 * m + 1) * ((r + m + 1) * Nat.choose (r + m) (2 * m + 1)) := by
                rw [← h_pasc]
            _ = (r + m + 1) * (Nat.choose (r + m) (2 * m + 1) * (2 * m + 1)) := by ring
            _ = (r + m + 1) * ((r + m - 2 * m) * Nat.choose (r + m) (2 * m)) := by
                rw [hc2]
            _ = (r + m + 1) * (r - m) * Nat.choose (r + m) (2 * m) := by
                rw [h_sub]; ring
        have h_step2 :
            (2 * m + 2) * (2 * m + 1) * Nat.choose (r + m) (2 * m + 2) =
              (r + m) * (r - m - 1) * Nat.choose (r + m - 1) (2 * m) := by
          have h_pasc := h_succ_choose (r + m - 1) (2 * m + 1)
          have hc2 := h_choose_succ (r + m - 1) (2 * m)
          have h_rm : r + m - 1 + 1 = r + m := by omega
          have h_sub : r + m - 1 - 2 * m = r - m - 1 := by omega
          calc (2 * m + 2) * (2 * m + 1) * Nat.choose (r + m) (2 * m + 2)
              = (2 * m + 1) * (Nat.choose (r + m - 1 + 1) (2 * m + 1 + 1) * (2 * m + 1 + 1)) := by
                rw [h_rm]; ring
            _ = (2 * m + 1) * ((r + m) * Nat.choose (r + m - 1) (2 * m + 1)) := by
                rw [← h_pasc, h_rm]
            _ = (r + m) * (Nat.choose (r + m - 1) (2 * m + 1) * (2 * m + 1)) := by ring
            _ = (r + m) * ((r + m - 1 - 2 * m) * Nat.choose (r + m - 1) (2 * m)) := by
                rw [hc2]
            _ = (r + m) * (r - m - 1) * Nat.choose (r + m - 1) (2 * m) := by
                rw [h_sub]; ring
        have h_rel : (r + m) * Nat.choose (r + m - 1) (2 * m) = (r - m) * Nat.choose (r + m) (2 * m) := by
          have h1 : r + m - 1 + 1 = r + m := by omega
          have h_mul1 := h_succ_choose (r + m - 1) (2 * m)
          have h_c_succ := h_choose_succ (r + m) (2 * m)
          have h_sub : r + m - 2 * m = r - m := by omega
          calc (r + m) * Nat.choose (r + m - 1) (2 * m)
              = (r + m - 1 + 1) * Nat.choose (r + m - 1) (2 * m) := by rw [h1]
            _ = Nat.choose (r + m - 1 + 1) (2 * m + 1) * (2 * m + 1) := h_mul1
            _ = Nat.choose (r + m) (2 * m + 1) * (2 * m + 1) := by rw [h1]
            _ = (r + m - 2 * m) * Nat.choose (r + m) (2 * m) := h_c_succ
            _ = (r - m) * Nat.choose (r + m) (2 * m) := by rw [h_sub]
        have h_comb_nat :
            (2 * m + 2) * (2 * m + 1) *
              (Nat.choose (r + (m + 1)) (2 * (m + 1)) + Nat.choose (r + (m + 1) - 1) (2 * (m + 1))) =
            (r - m) * (r + m) * (Nat.choose (r + m) (2 * m) + Nat.choose (r + m - 1) (2 * m)) := by
          rw [show r + (m + 1) = r + m + 1 by omega,
              show r + m + 1 - 1 = r + m by omega,
              show 2 * (m + 1) = 2 * m + 2 by omega,
              Nat.mul_add, h_step1, h_step2]
          zify [show m ≤ r by omega, show 1 ≤ r - m by omega] at h_rel ⊢
          linear_combination -1 * h_rel
        have h_fac_succ : (2 * (m + 1)).factorial = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
          rw [show 2 * (m + 1) = 2 * m + 2 by omega, Nat.factorial_succ, Nat.factorial_succ]
          ring
        have h_comb_q :
            ((2 * m + 2 : ℚ) * (2 * m + 1 : ℚ)) *
              ((Nat.choose (r + (m + 1)) (2 * (m + 1)) : ℚ) + (Nat.choose (r + (m + 1) - 1) (2 * (m + 1)) : ℚ)) =
            (((r : ℚ) ^ 2 - (m : ℚ) ^ 2) *
              ((Nat.choose (r + m) (2 * m) : ℚ) + (Nat.choose (r + m - 1) (2 * m) : ℚ))) := by
          have h_cast : (((2 * m + 2) * (2 * m + 1) *
              (Nat.choose (r + (m + 1)) (2 * (m + 1)) + Nat.choose (r + (m + 1) - 1) (2 * (m + 1))) : ℕ) : ℚ) =
            (((r - m) * (r + m) * (Nat.choose (r + m) (2 * m) + Nat.choose (r + m - 1) (2 * m)) : ℕ) : ℚ) :=
            by exact_mod_cast h_comb_nat
          have h_rm_cast : ((r - m : ℕ) : ℚ) = (r : ℚ) - (m : ℚ) :=
            Nat.cast_sub (by omega)
          push_cast at h_cast
          rw [h_rm_cast] at h_cast
          linear_combination h_cast
        rw [h_fac_succ]
        push_cast
        linear_combination ((2 * m).factorial : ℚ) * h_comb_q.symm

/-- **Proposition 2.2 (Equation (2.3): Integer-Square Integrality and Binomial Representation)**:
For every integer `r ≥ 0` and every integer `m ≥ 1`, the evaluation of `ℰ_m(u)` at `u = r²`
satisfies the exact binomial identity
$$\mathcal{E}_m(r^2) = \binom{r+m}{2m} + \binom{r+m-1}{2m} \in \mathbb{Z}.$$ -/
theorem prop_2_2_binomial_identity (m r : ℕ) (hm : 1 ≤ m) :
    evalCentralFactorial m ((r : ℚ) ^ 2) =
      ((Nat.choose (r + m) (2 * m) + Nat.choose (r + m - 1) (2 * m) : ℕ) : ℚ) := by
  unfold evalCentralFactorial
  rw [if_neg (by omega : m ≠ 0)]
  have h_prod := centralFactorial_prod_eq_factorial_mul_binom m r hm
  have h_fac_ne : ((2 * m).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * m)
  rw [div_mul_eq_mul_div, h_prod, mul_div_cancel_left₀ _ h_fac_ne]

/-- **Proposition 2.2(i) (Diagonal Normalization `ℰ_m(m²) = 1`)**:
For every integer `m ≥ 0`, `ℰ_m(m²) = 1`. -/
theorem prop_2_2_i_diag (m : ℕ) :
    evalCentralFactorial m ((m : ℚ) ^ 2) = 1 := by
  rcases eq_or_ne m 0 with rfl | hm0
  · rfl
  · rw [prop_2_2_binomial_identity m m (Nat.one_le_iff_ne_zero.mpr hm0)]
    have h1 : m + m = 2 * m := by omega
    have h2 : Nat.choose (2 * m - 1) (2 * m) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h1, Nat.choose_self, h2]
    norm_num

/-- **Proposition 2.2(ii) (Step (4) Legendre Valuation Bound at `r = 0`)**:
For every prime `p` and integer `m ≥ 1`, in the Legendre expansion at `r = 0`, each level
`s` satisfies `⌊2m / p^s⌋ - 2⌊m / p^s⌋ ≤ 1`, and for `1 ≤ s ≤ v_p(m)`, `p^s ∣ m` implies
`⌊2m / p^s⌋ - 2⌊m / p^s⌋ = 0`. -/
theorem prop_2_2_ii_legendre_step_bound (m ps : ℕ) (hps : 0 < ps) :
    (2 * m) / ps - 2 * (m / ps) ≤ 1 ∧
      (ps ∣ m → (2 * m) / ps - 2 * (m / ps) = 0) := by
  constructor
  · have h_div := Nat.div_add_mod m ps
    have h_mod : m % ps < ps := Nat.mod_lt m hps
    have h_2m : 2 * m = ps * (2 * (m / ps)) + 2 * (m % ps) := by linarith
    have h_q : (2 * m) / ps = 2 * (m / ps) + (2 * (m % ps)) / ps := by
      rw [h_2m, Nat.mul_add_div hps]
    have h_lt : (2 * (m % ps)) / ps ≤ 1 := by
      apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul hps]
      omega
    omega
  · intro hdvd
    rcases hdvd with ⟨k, rfl⟩
    rw [← mul_assoc, mul_comm 2 ps, mul_assoc,
        Nat.mul_div_right _ hps, Nat.mul_div_right _ hps]
    omega

/-!
## Proposition 2.3: First Derivatives at Integer Squares `0 ≤ r < m`
-/

/-- Kronecker delta `δ_{r,0}` returning `1` when `r = 0` and `0` when `r ≥ 1`. -/
def deltaZero (r : ℕ) : ℕ :=
  if r = 0 then 1 else 0

@[simp]
theorem deltaZero_zero : deltaZero 0 = 1 := rfl

@[simp]
theorem deltaZero_succ (r : ℕ) : deltaZero (r + 1) = 0 := rfl

/-- **Proposition 2.3 (Equation (2.7), Form 1 — Factorial Form)**:
$$\mathcal{E}_m'(r^2) = \frac{(1 + \delta_{r,0})(-1)^{m-1-r}(m-1+r)!(m-1-r)!}{(2m)!}.$$ -/
def EPrimeForm1 (m r : ℕ) : ℚ :=
  ((1 + deltaZero r : ℕ) : ℚ) * ((-1 : ℚ) ^ (m - 1 - r)) *
    (((m - 1 + r).factorial * (m - 1 - r).factorial : ℕ) : ℚ) /
    (((2 * m).factorial : ℕ) : ℚ)

/-- **Proposition 2.3 (Equation (2.7), Form 2 — Central Binomial Form)**:
$$\mathcal{E}_m'(r^2) = \frac{(1 + \delta_{r,0})(-1)^{m-1-r}}{2m(2m-1)\binom{2m-2}{m-1+r}}.$$ -/
def EPrimeForm2 (m r : ℕ) : ℚ :=
  ((1 + deltaZero r : ℕ) : ℚ) * ((-1 : ℚ) ^ (m - 1 - r)) /
    (((2 * m) * (2 * m - 1) * Nat.choose (2 * m - 2) (m - 1 + r) : ℕ) : ℚ)

/-- **Proposition 2.3 (Equation (2.7), Form 3 — Split Binomial Form)**:
$$\mathcal{E}_m'(r^2) = \begin{cases}
\frac{(-1)^{m-1-r}}{2m(m-r)\binom{2m-1}{m-r}}, & 1 \le r < m, \\
\frac{(-1)^{m-1}}{m^2\binom{2m-1}{m-1}}, & r = 0.
\end{cases}$$ -/
def EPrimeForm3 (m r : ℕ) : ℚ :=
  if r = 0 then
    ((-1 : ℚ) ^ (m - 1)) / (((m ^ 2) * Nat.choose (2 * m - 1) (m - 1) : ℕ) : ℚ)
  else
    ((-1 : ℚ) ^ (m - 1 - r)) / (((2 * m) * (m - r) * Nat.choose (2 * m - 1) (m - r) : ℕ) : ℚ)

/-- **Proposition 2.3 (Equation (2.8) Integer Reciprocal Formula)**:
$$\frac{1}{\mathcal{E}_m'(r^2)} = \frac{(-1)^{m-1-r}}{1+\delta_{r,0}} 2m(2m-1)\binom{2m-2}{m-1+r} \in \mathbb{Z} \setminus \{0\}.$$ -/
def EPrimeRecipInt (m r : ℕ) : ℤ :=
  if r = 0 then
    ((-1 : ℤ) ^ (m - 1)) * (m : ℤ) * (2 * (m : ℤ) - 1) * (Nat.choose (2 * m - 2) (m - 1) : ℤ)
  else
    ((-1 : ℤ) ^ (m - 1 - r)) * (2 * (m : ℤ)) * (2 * (m : ℤ) - 1) *
      (Nat.choose (2 * m - 2) (m - 1 + r) : ℤ)

/-- Key factorial-binomial identity in the proof of Proposition 2.3 (p. 9):
For `0 ≤ r < m` (`m ≥ 1`),
$$(2m)! = 2m(2m-1)\binom{2m-2}{m-1+r} (m-1+r)!(m-1-r)!.$$ -/
theorem factorial_two_mul_eq_choose_mul_factorials (m r : ℕ) (hr : r < m) :
    (2 * m).factorial =
      (2 * m) * (2 * m - 1) * Nat.choose (2 * m - 2) (m - 1 + r) *
        ((m - 1 + r).factorial * (m - 1 - r).factorial) := by
  have hm : 1 ≤ m := by omega
  have h_le : m - 1 + r ≤ 2 * m - 2 := by omega
  have h_sub : 2 * m - 2 - (m - 1 + r) = m - 1 - r := by omega
  have h_choose := Nat.choose_mul_factorial_mul_factorial h_le
  rw [h_sub] at h_choose
  have h_fac_split : (2 * m).factorial = (2 * m) * (2 * m - 1) * (2 * m - 2).factorial := by
    rcases m with _ | m
    · omega
    · rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
          Nat.factorial_succ, Nat.factorial_succ]
      simp [Nat.add_sub_cancel]
      ring
  rw [h_fac_split, ← h_choose]
  ring

/-- Second binomial identity in the proof of Proposition 2.3 (p. 9):
For `0 ≤ r < m` (`m ≥ 1`),
$$(2m-1)\binom{2m-2}{m-1+r} = (m-r)\binom{2m-1}{m-r}.$$ -/
theorem two_mul_sub_one_mul_choose_eq (m r : ℕ) (hr : r < m) :
    (2 * m - 1) * Nat.choose (2 * m - 2) (m - 1 + r) =
      (m - r) * Nat.choose (2 * m - 1) (m - r) := by
  have h_symm : Nat.choose (2 * m - 2) (m - 1 + r) = Nat.choose (2 * m - 2) (m - 1 - r) := by
    rw [← Nat.choose_symm (by omega : m - 1 + r ≤ 2 * m - 2)]
    congr 1
    omega
  rw [h_symm]
  have h_abs := Nat.succ_mul_choose_eq (2 * m - 2) (m - 1 - r)
  simp only [Nat.succ_eq_add_one] at h_abs
  have h1 : 2 * m - 2 + 1 = 2 * m - 1 := by omega
  have h2 : m - 1 - r + 1 = m - r := by omega
  rw [h1, h2] at h_abs
  linarith

/-- **Proposition 2.3 (Equivalence of All Three Forms of (2.7))**:
For every integer `m ≥ 1` and every integer `0 ≤ r < m`, the three closed-form expressions
in Equation (2.7) are identically equal:
`EPrimeForm1 m r = EPrimeForm2 m r` and `EPrimeForm2 m r = EPrimeForm3 m r`. -/
theorem prop_2_3_three_forms_eq (m r : ℕ) (hr : r < m) :
    EPrimeForm1 m r = EPrimeForm2 m r ∧ EPrimeForm2 m r = EPrimeForm3 m r := by
  have hm : 1 ≤ m := by omega
  have h_fac_id := factorial_two_mul_eq_choose_mul_factorials m r hr
  have h_prod_ne : (((m - 1 + r).factorial : ℚ) * ((m - 1 - r).factorial : ℚ)) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _) (by exact_mod_cast Nat.factorial_ne_zero _)
  constructor
  · unfold EPrimeForm1 EPrimeForm2
    rw [h_fac_id]
    push_cast
    rw [mul_div_mul_right _ _ h_prod_ne]
  · unfold EPrimeForm2 EPrimeForm3
    have h_bin_id := two_mul_sub_one_mul_choose_eq m r hr
    split_ifs with hr0
    · subst hr0
      simp only [deltaZero_zero, Nat.add_zero, Nat.sub_zero]
      have h_id0 : (2 * m) * ((2 * m - 1) * Nat.choose (2 * m - 2) (m - 1)) =
          2 * (m ^ 2 * Nat.choose (2 * m - 1) (m - 1)) := by
        have hb0 := h_bin_id
        simp only [Nat.add_zero, Nat.sub_zero] at hb0
        calc (2 * m) * ((2 * m - 1) * Nat.choose (2 * m - 2) (m - 1))
            = (2 * m) * (m * Nat.choose (2 * m - 1) m) := by rw [hb0]
          _ = (2 * m) * (m * Nat.choose (2 * m - 1) (m - 1)) := by
              congr 2
              rw [← Nat.choose_symm (by omega : m ≤ 2 * m - 1)]
              congr 1; omega
          _ = 2 * (m ^ 2 * Nat.choose (2 * m - 1) (m - 1)) := by ring
      have h_cast : (((2 * m) * (2 * m - 1) * Nat.choose (2 * m - 2) (m - 1) : ℕ) : ℚ) =
          (2 : ℚ) * (((m ^ 2) * Nat.choose (2 * m - 1) (m - 1) : ℕ) : ℚ) := by
        exact_mod_cast (by simpa [mul_assoc] using h_id0)
      rw [h_cast]
      have h2_ne : (2 : ℚ) ≠ 0 := by norm_num
      have h_num : ((1 + 1 : ℕ) : ℚ) * (-1 : ℚ) ^ (m - 1) = (2 : ℚ) * (-1 : ℚ) ^ (m - 1) := by
        norm_num
      rw [h_num, mul_div_mul_left _ _ h2_ne]
    · have h_delta : deltaZero r = 0 := if_neg hr0
      rw [h_delta]
      have h_id_r : (2 * m) * (2 * m - 1) * Nat.choose (2 * m - 2) (m - 1 + r) =
          (2 * m) * (m - r) * Nat.choose (2 * m - 1) (m - r) := by
        calc (2 * m) * (2 * m - 1) * Nat.choose (2 * m - 2) (m - 1 + r)
            = (2 * m) * ((2 * m - 1) * Nat.choose (2 * m - 2) (m - 1 + r)) := by ring
          _ = (2 * m) * ((m - r) * Nat.choose (2 * m - 1) (m - r)) := by rw [h_bin_id]
          _ = (2 * m) * (m - r) * Nat.choose (2 * m - 1) (m - r) := by ring
      rw [h_id_r]
      simp

/-- **Proposition 2.3 (Equation (2.8): Non-Vanishing and Integer Reciprocal of `ℰ_m'(r²)`)**:
For every integer `m ≥ 1` and every `0 ≤ r < m`, `ℰ_m'(r²) ≠ 0` and its reciprocal is the
non-zero integer `EPrimeRecipInt m r ∈ ℤ \ {0}`. -/
theorem prop_2_3_reciprocal_int (m r : ℕ) (hr : r < m) :
    EPrimeForm2 m r ≠ 0 ∧
      EPrimeRecipInt m r ≠ 0 ∧
      (EPrimeForm2 m r)⁻¹ = (EPrimeRecipInt m r : ℚ) := by
  have hm : 1 ≤ m := by omega
  have h_choose_pos : 0 < Nat.choose (2 * m - 2) (m - 1 + r) :=
    Nat.choose_pos (by omega)
  have h_denom_pos : 0 < (2 * m) * (2 * m - 1) * Nat.choose (2 * m - 2) (m - 1 + r) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) h_choose_pos
  unfold EPrimeForm2 EPrimeRecipInt
  split_ifs with hr0
  · subst hr0
    simp only [deltaZero_zero, Nat.add_zero, Nat.sub_zero]
    have h_rec_ne : ((-1 : ℤ) ^ (m - 1) * (m : ℤ) * (2 * (m : ℤ) - 1) *
        (Nat.choose (2 * m - 2) (m - 1) : ℤ)) ≠ 0 := by
      have hm_z : (m : ℤ) ≠ 0 := by omega
      have h2m_z : (2 * (m : ℤ) - 1) ≠ 0 := by omega
      have hc_z : (Nat.choose (2 * m - 2) (m - 1) : ℤ) ≠ 0 := by exact_mod_cast h_choose_pos.ne'
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by decide)) hm_z) h2m_z) hc_z
    refine ⟨?_, h_rec_ne, ?_⟩
    · apply div_ne_zero
      · exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
      · exact_mod_cast h_denom_pos.ne'
    · rw [inv_div]
      have hm_sub : ((2 * m - 1 : ℕ) : ℚ) = 2 * (m : ℚ) - 1 := by
        exact_mod_cast Nat.cast_sub (by omega : 1 ≤ 2 * m)
      have h_sign_sq : (-1 : ℚ) ^ (m - 1) * (-1 : ℚ) ^ (m - 1) = 1 := by
        rw [← mul_pow, mul_neg_one, neg_neg, one_pow]
      have h_denom_ne : ((1 + 1 : ℕ) : ℚ) * (-1 : ℚ) ^ (m - 1) ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
      rw [div_eq_iff h_denom_ne]
      push_cast
      rw [hm_sub]
      linear_combination ((m : ℚ) * (2 * (m : ℚ) - 1) * (Nat.choose (2 * m - 2) (m - 1) : ℚ) * 2) * h_sign_sq.symm
  · have h_delta : deltaZero r = 0 := if_neg hr0
    rw [h_delta]
    have h_rec_ne : ((-1 : ℤ) ^ (m - 1 - r) * (2 * (m : ℤ)) * (2 * (m : ℤ) - 1) *
        (Nat.choose (2 * m - 2) (m - 1 + r) : ℤ)) ≠ 0 := by
      have hm_z : (2 * (m : ℤ)) ≠ 0 := by omega
      have h2m_z : (2 * (m : ℤ) - 1) ≠ 0 := by omega
      have hc_z : (Nat.choose (2 * m - 2) (m - 1 + r) : ℤ) ≠ 0 := by exact_mod_cast h_choose_pos.ne'
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by decide)) hm_z) h2m_z) hc_z
    refine ⟨?_, h_rec_ne, ?_⟩
    · apply div_ne_zero
      · exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
      · exact_mod_cast h_denom_pos.ne'
    · rw [inv_div]
      have hm_sub : ((2 * m - 1 : ℕ) : ℚ) = 2 * (m : ℚ) - 1 := by
        exact_mod_cast Nat.cast_sub (by omega : 1 ≤ 2 * m)
      have h_sign_sq : (-1 : ℚ) ^ (m - 1 - r) * (-1 : ℚ) ^ (m - 1 - r) = 1 := by
        rw [← mul_pow, mul_neg_one, neg_neg, one_pow]
      have h_denom_ne : ((1 + 0 : ℕ) : ℚ) * (-1 : ℚ) ^ (m - 1 - r) ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
      rw [div_eq_iff h_denom_ne]
      push_cast
      rw [hm_sub]
      linear_combination ((2 : ℚ) * (m : ℚ) * (2 * (m : ℚ) - 1) * (Nat.choose (2 * m - 2) (m - 1 + r) : ℚ)) * h_sign_sq.symm

/-- Concrete verification of Proposition 2.3 benchmark values from Suite 1:
`ℰ_3'(0) = 1/90`, `ℰ_3'(1) = -1/120`, `ℰ_4'(4) = -1/336`. -/
theorem prop_2_3_benchmarks :
    EPrimeForm1 3 0 = 1 / 90 ∧
    EPrimeForm1 3 1 = -1 / 120 ∧
    EPrimeForm1 4 2 = -1 / 336 := by
  unfold EPrimeForm1 deltaZero
  norm_num [Nat.factorial]

/-- Product-rule evaluation of the derivative of `∏ t ∈ s, (X - C (f t))` at a root `f r` (`r ∈ s`). -/
theorem derivative_prod_linear_eval_at_root {s : Finset ℕ} {r : ℕ} (hr : r ∈ s) (f : ℕ → ℚ) :
    (∏ t ∈ s, (Polynomial.X - Polynomial.C (f t))).derivative.eval (f r) =
      ∏ t ∈ s.erase r, (f r - f t) := by
  rw [← Finset.insert_erase hr, Finset.prod_insert (Finset.not_mem_erase r s)]
  rw [Polynomial.derivative_mul]
  have h_lin_deriv : (Polynomial.X - Polynomial.C (f r)).derivative = 1 := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero]
  rw [h_lin_deriv, one_mul]
  simp [Polynomial.eval_prod]

/-- Inductive factorial identity for the deleted product `2 * ∏_{t ≠ r} (r² - t²)` (`0 ≤ r < m`). -/
theorem deleted_sq_prod_eq_signed_factorials (m r : ℕ) (hr : r < m) :
    (2 : ℚ) * (∏ t ∈ (Finset.range m).erase r, ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) =
      ((1 + deltaZero r : ℕ) : ℚ) * ((-1 : ℚ) ^ (m - 1 - r)) *
        (((m - 1 + r).factorial * (m - 1 - r).factorial : ℕ) : ℚ) := by
  induction' m with m ih
  · omega
  · rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hr) with rfl | hr_lt_m
    · have h_erase : (Finset.range (r + 1)).erase r = Finset.range r := by
        ext t
        simp only [Finset.mem_erase, Finset.mem_range]
        omega
      rw [h_erase, show r + 1 - 1 - r = 0 by omega, show r + 1 - 1 + r = 2 * r by omega]
      simp only [pow_zero, mul_one, Nat.factorial_zero]
      rcases eq_or_ne r 0 with rfl | hr0
      · simp [deltaZero_zero]
      · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
        rw [centralFactorial_prod_eq_factorial_mul_binom r r hr1]
        have h_delta : deltaZero r = 0 := if_neg hr0
        have h_c1 : Nat.choose (r + r) (2 * r) = 1 := by
          rw [show r + r = 2 * r by omega, Nat.choose_self]
        have h_c2 : Nat.choose (r + r - 1) (2 * r) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        rw [h_delta, h_c1, h_c2]
        simp
    · specialize ih hr_lt_m
      have h_erase_succ : (Finset.range (m + 1)).erase r = insert m ((Finset.range m).erase r) := by
        ext t
        simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_insert]
        omega
      have hm_not_mem : m ∉ (Finset.range m).erase r := by
        simp [Finset.mem_erase, Finset.mem_range]
      rw [h_erase_succ, Finset.prod_insert hm_not_mem, ← mul_assoc,
          mul_comm (2 : ℚ) (((r : ℚ) ^ 2 - (m : ℚ) ^ 2)), mul_assoc, ih]
      have h_pow : ((-1 : ℚ) ^ (m + 1 - 1 - r)) = ((-1 : ℚ) ^ (m - 1 - r)) * (-1 : ℚ) := by
        rw [show m + 1 - 1 - r = (m - 1 - r) + 1 by omega, pow_succ]
      have h_fac1 : (m + 1 - 1 + r).factorial = (m + r) * (m - 1 + r).factorial := by
        rw [show m + 1 - 1 + r = (m - 1 + r) + 1 by omega, Nat.factorial_succ]
        congr 1; omega
      have h_fac2 : (m + 1 - 1 - r).factorial = (m - r) * (m - 1 - r).factorial := by
        rw [show m + 1 - 1 - r = (m - 1 - r) + 1 by omega, Nat.factorial_succ]
        congr 1; omega
      have h_sub_cast : ((m - r : ℕ) : ℚ) = (m : ℚ) - (r : ℚ) :=
        Nat.cast_sub (by omega)
      rw [h_pow, h_fac1, h_fac2]
      push_cast
      rw [h_sub_cast]
      ring

/-- **Proposition 2.3 (Equation (2.7): Exact Polynomial Derivative Evaluation of `ℰ_m'(r²)`)**:
For every integer `m ≥ 1` and every integer `0 ≤ r < m`, the evaluation of the polynomial
derivative `(centralFactorialPoly m).derivative` at `u = r²` equals `EPrimeForm1 m r`
(and hence by `prop_2_3_three_forms_eq` also `EPrimeForm2 m r` and `EPrimeForm3 m r`). -/
theorem prop_2_3_derivative_eval_eq_EPrimeForm1 (m r : ℕ) (hr : r < m) :
    (centralFactorialPoly m).derivative.eval ((r : ℚ) ^ 2) = EPrimeForm1 m r := by
  have hm0 : m ≠ 0 := by omega
  unfold centralFactorialPoly EPrimeForm1
  rw [if_neg hm0, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
  have hr_mem : r ∈ Finset.range m := Finset.mem_range.mpr hr
  rw [derivative_prod_linear_eval_at_root hr_mem (fun t => (t : ℚ) ^ 2)]
  rw [div_mul_eq_mul_div, deleted_sq_prod_eq_signed_factorials m r hr]

/-!
## Proposition 2.4: Second Derivatives and Harmonic Telescoping
-/

/-- **Proposition 2.4 (Equation (2.10))**: The rational harmonic sum
$$T(m, r) := \sum_{\substack{0 \le t < m \\ t \ne r}} \frac{1}{r^2 - t^2}.$$ -/
def harmonicTelescopingSum (m r : ℕ) : ℚ :=
  ∑ t ∈ (Finset.range m).erase r, (1 : ℚ) / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)

/-- **Proposition 2.4 (Equation (2.11))**: The closed-form rational telescoping formula for `T(m, r)`:
- At `r = 0`: `-H_{m-1}^{(2)} = -∑_{t=1}^{m-1} 1 / t²`
- For `1 ≤ r < m`: `1 / (4 r²) + (1 / (2r)) ∑_{u=m-r}^{m+r-1} 1 / u`. -/
def harmonicTelescopingClosed (m r : ℕ) : ℚ :=
  if r = 0 then
    - ∑ t ∈ Finset.Ico 1 m, (1 : ℚ) / ((t : ℚ) ^ 2)
  else
    (1 : ℚ) / (4 * (r : ℚ) ^ 2) +
      ((1 : ℚ) / (2 * (r : ℚ))) * ∑ u ∈ Finset.Ico (m - r) (m + r), (1 : ℚ) / (u : ℚ)

/-- **Proposition 2.4 at `r = 0`**: `T(m, 0) = -H_{m-1}^{(2)}`. -/
theorem prop_2_4_at_zero (m : ℕ) :
    harmonicTelescopingSum m 0 = harmonicTelescopingClosed m 0 := by
  unfold harmonicTelescopingSum harmonicTelescopingClosed
  simp only [ ↓reduceIte, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_sub, div_neg, Finset.sum_neg_distrib ]
  congr 1
  have h_set : (Finset.range m).erase 0 = Finset.Ico 1 m := by
    ext t
    simp [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [h_set]

/-- Partial fraction decomposition identity (2.12) used in the proof of Proposition 2.4:
For `r ≠ 0` and `t ≠ ±r`, `1 / (r² - t²) = (1 / (2r)) * (1 / (r - t) + 1 / (r + t))`. -/
theorem partial_fraction_diff_sq (r t : ℚ) (hr : r ≠ 0) (h1 : r - t ≠ 0) (h2 : r + t ≠ 0) :
    (1 : ℚ) / (r ^ 2 - t ^ 2) = ((1 : ℚ) / (2 * r)) * ((1 : ℚ) / (r - t) + (1 : ℚ) / (r + t)) := by
  have h_prod : r ^ 2 - t ^ 2 = (r - t) * (r + t) := by ring
  rw [h_prod]
  field_simp [hr, h1, h2]
  ring

/-- Base case `m = r + 1` of the harmonic telescoping identity (2.11) for `r ≥ 1`:
`harmonicTelescopingSum (r + 1) r = harmonicTelescopingClosed (r + 1) r`. -/
theorem prop_2_4_base_r_succ (r : ℕ) (hr : 1 ≤ r) :
    harmonicTelescopingSum (r + 1) r = harmonicTelescopingClosed (r + 1) r := by
  unfold harmonicTelescopingSum harmonicTelescopingClosed
  rw [if_neg (by omega : r ≠ 0)]
  have h_erase : (Finset.range (r + 1)).erase r = insert 0 (Finset.Ico 1 r) := by
    ext t
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [h_erase, Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
  have hr_q : (r : ℚ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have h_pf :
      (∑ t ∈ Finset.Ico 1 r, (1 : ℚ) / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) =
        ((1 : ℚ) / (2 * (r : ℚ))) *
          ((∑ t ∈ Finset.Ico 1 r, (1 : ℚ) / ((r - t : ℕ) : ℚ)) +
           (∑ t ∈ Finset.Ico 1 r, (1 : ℚ) / ((r + t : ℕ) : ℚ))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have ht_lt : t < r := (Finset.mem_Ico.mp ht).2
    have h_sub_cast : ((r - t : ℕ) : ℚ) = (r : ℚ) - (t : ℚ) := Nat.cast_sub (by omega)
    have h_add_cast : ((r + t : ℕ) : ℚ) = (r : ℚ) + (t : ℚ) := by push_cast; rfl
    rw [h_sub_cast, h_add_cast]
    apply partial_fraction_diff_sq (r : ℚ) (t : ℚ) hr_q
    · exact sub_ne_zero.mpr (by exact_mod_cast (by omega : r ≠ t))
    · positivity
  have h_bij1 :
      (∑ t ∈ Finset.Ico 1 r, (1 : ℚ) / ((r - t : ℕ) : ℚ)) =
        ∑ u ∈ Finset.Ico 1 r, (1 : ℚ) / (u : ℚ) := by
    apply Finset.sum_bij (fun t _ => r - t)
    · intro t ht; simp only [Finset.mem_Ico] at ht ⊢; omega
    · intro t1 ht1 t2 ht2 h_eq; simp only [Finset.mem_Ico] at ht1 ht2; omega
    · intro u hu; simp only [Finset.mem_Ico] at hu
      exact ⟨r - u, Finset.mem_Ico.mpr (by omega), by omega⟩
    · intro t _; rfl
  have h_bij2 :
      (∑ t ∈ Finset.Ico 1 r, (1 : ℚ) / ((r + t : ℕ) : ℚ)) =
        ∑ u ∈ Finset.Ico (r + 1) (2 * r), (1 : ℚ) / (u : ℚ) := by
    apply Finset.sum_bij (fun t _ => r + t)
    · intro t ht; simp only [Finset.mem_Ico] at ht ⊢; omega
    · intro t1 _ t2 _ h_eq; omega
    · intro u hu; simp only [Finset.mem_Ico] at hu
      exact ⟨u - r, Finset.mem_Ico.mpr (by omega), by omega⟩
    · intro t _; rfl
  rw [h_pf, h_bij1, h_bij2]
  have h_ico_split :
      Finset.Ico (r + 1 - r) (r + 1 + r) =
        insert r (insert (2 * r) (Finset.Ico 1 r ∪ Finset.Ico (r + 1) (2 * r))) := by
    ext u
    simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_union]
    omega
  have hr_not_in : r ∉ insert (2 * r) (Finset.Ico 1 r ∪ Finset.Ico (r + 1) (2 * r)) := by
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_Ico]
    omega
  have h2r_not_in : 2 * r ∉ (Finset.Ico 1 r ∪ Finset.Ico (r + 1) (2 * r)) := by
    simp only [Finset.mem_union, Finset.mem_Ico]
    omega
  have h_disj : Disjoint (Finset.Ico 1 r) (Finset.Ico (r + 1) (2 * r)) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    simp only [Finset.mem_Ico] at hu1 hu2
    omega
  rw [h_ico_split, Finset.sum_insert hr_not_in, Finset.sum_insert h2r_not_in,
      Finset.sum_union h_disj]
  push_cast
  field_simp [hr_q]
  ring

/-- **Proposition 2.4 (Equation (2.11): General Harmonic Telescoping Identity for All `0 ≤ r < m`)**:
For every integer `m ≥ 1` and every `0 ≤ r < m`,
$$T(m, r) = \sum_{\substack{0 \le t < m \\ t \ne r}} \frac{1}{r^2 - t^2}$$
equals the closed form `harmonicTelescopingClosed m r`. -/
theorem prop_2_4_harmonic_telescoping (m r : ℕ) (hr : r < m) :
    harmonicTelescopingSum m r = harmonicTelescopingClosed m r := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact prop_2_4_at_zero m
  · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
    induction' m with m ih
    · omega
    · rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hr) with rfl | hr_lt_m
      · exact prop_2_4_base_r_succ r hr1
      · specialize ih hr_lt_m
        have h_lhs_step :
            harmonicTelescopingSum (m + 1) r =
              harmonicTelescopingSum m r + (1 : ℚ) / ((r : ℚ) ^ 2 - (m : ℚ) ^ 2) := by
          unfold harmonicTelescopingSum
          have h_erase : (Finset.range (m + 1)).erase r = insert m ((Finset.range m).erase r) := by
            ext t
            simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_insert]
            omega
          have hm_not : m ∉ (Finset.range m).erase r := by
            simp [Finset.mem_erase, Finset.mem_range]
          rw [h_erase, Finset.sum_insert hm_not, add_comm]
        have h_rhs_step :
            harmonicTelescopingClosed (m + 1) r =
              harmonicTelescopingClosed m r + (1 : ℚ) / ((r : ℚ) ^ 2 - (m : ℚ) ^ 2) := by
          simp only [harmonicTelescopingClosed, if_neg hr0]
          have h_ico1 :
              Finset.Ico (m - r) (m + r + 1) = insert (m + r) (Finset.Ico (m - r) (m + r)) := by
            ext u; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
          have h_ico2 :
              Finset.Ico (m - r) (m + r + 1) = insert (m - r) (Finset.Ico (m + 1 - r) (m + 1 + r)) := by
            ext u; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
          have h_not1 : m + r ∉ Finset.Ico (m - r) (m + r) := by simp [Finset.mem_Ico]
          have h_not2 : m - r ∉ Finset.Ico (m + 1 - r) (m + 1 + r) := by
            simp only [Finset.mem_Ico]; omega
          have h_sum_shift :
              (∑ u ∈ Finset.Ico (m + 1 - r) (m + 1 + r), (1 : ℚ) / (u : ℚ)) =
                (∑ u ∈ Finset.Ico (m - r) (m + r), (1 : ℚ) / (u : ℚ)) +
                  ((1 : ℚ) / ((m + r : ℕ) : ℚ) - (1 : ℚ) / ((m - r : ℕ) : ℚ)) := by
            have h_ins1 := Finset.sum_insert (f := fun u : ℕ => (1 : ℚ) / (u : ℚ)) h_not1
            have h_ins2 := Finset.sum_insert (f := fun u : ℕ => (1 : ℚ) / (u : ℚ)) h_not2
            rw [← h_ico1] at h_ins1
            rw [← h_ico2] at h_ins2
            linarith
          rw [h_sum_shift]
          have hr_q : (r : ℚ) ≠ 0 := by exact_mod_cast hr0
          have h_mr_pos : (0 : ℚ) < (m : ℚ) - (r : ℚ) := by
            exact sub_pos.mpr (by exact_mod_cast hr_lt_m)
          have h_mr_ne : (m : ℚ) - (r : ℚ) ≠ 0 := ne_of_gt h_mr_pos
          have h_pr_ne : (m : ℚ) + (r : ℚ) ≠ 0 := by positivity
          have h_rm_ne : (r : ℚ) ^ 2 - (m : ℚ) ^ 2 ≠ 0 := by
            have h_f : (r : ℚ) ^ 2 - (m : ℚ) ^ 2 = -((m : ℚ) - (r : ℚ)) * ((m : ℚ) + (r : ℚ)) := by ring
            rw [h_f]
            exact mul_ne_zero (neg_ne_zero.mpr h_mr_ne) h_pr_ne
          have h_sub_cast : ((m - r : ℕ) : ℚ) = (m : ℚ) - (r : ℚ) := Nat.cast_sub (by omega)
          have h_add_cast : ((m + r : ℕ) : ℚ) = (m : ℚ) + (r : ℚ) := by push_cast; rfl
          rw [h_sub_cast, h_add_cast]
          have h_diff_id :
              ((1 : ℚ) / (2 * (r : ℚ))) *
                ((1 : ℚ) / ((m : ℚ) + (r : ℚ)) - (1 : ℚ) / ((m : ℚ) - (r : ℚ))) =
              (1 : ℚ) / ((r : ℚ) ^ 2 - (m : ℚ) ^ 2) := by
            field_simp [hr_q, h_mr_ne, h_pr_ne, h_rm_ne]
            ring
          linear_combination h_diff_id
        rw [h_lhs_step, h_rhs_step, ih]

/-- Logarithmic derivative evaluation for a product of linear factors `∏ t ∈ s, (X - C (f t))`
at a point `u` where no factor vanishes. -/
theorem derivative_prod_linear_eval_eq_sum_div (s : Finset ℕ) (f : ℕ → ℚ) (u : ℚ)
    (h_nz : ∀ t ∈ s, u - f t ≠ 0) :
    (∏ t ∈ s, (Polynomial.X - Polynomial.C (f t))).derivative.eval u =
      (∏ t ∈ s, (u - f t)) * ∑ t ∈ s, (1 : ℚ) / (u - f t) := by
  induction' s using Finset.cons_induction with a s ha ih
  · simp
  · have ha_nz : u - f a ≠ 0 := h_nz a (Finset.mem_cons_self a s)
    have hs_nz : ∀ t ∈ s, u - f t ≠ 0 := fun t ht => h_nz t (Finset.mem_cons_of_mem ht)
    rw [Finset.prod_cons, Polynomial.derivative_mul]
    have h_lin : (Polynomial.X - Polynomial.C (f a)).derivative = 1 := by
      rw [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero]
    rw [h_lin, one_mul, Polynomial.eval_add, Polynomial.eval_mul]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_prod]
    rw [ih hs_nz, Finset.prod_cons, Finset.sum_cons, mul_add]
    have h_cancel : (u - f a) * (∏ x ∈ s, (u - f x)) * (1 / (u - f a)) = ∏ x ∈ s, (u - f x) := by
      rw [mul_right_comm, mul_one_div_cancel ha_nz, one_mul]
    rw [h_cancel]
    ring

/-- **Proposition 2.4 (Equation (2.10): Exact Second-Derivative Polynomial Identity)**:
For every integer `m ≥ 1` and every `0 ≤ r < m`, the second derivative of
`centralFactorialPoly m` at `u = r²` satisfies
$$\frac{1}{2} \mathcal{E}_m''(r^2) = \mathcal{E}_m'(r^2) T(m, r)
  = \mathcal{E}_m'(r^2) \cdot \mathrm{harmonicTelescopingClosed}(m, r).$$ -/
theorem prop_2_4_second_derivative_eq (m r : ℕ) (hr : r < m) :
    ((1 : ℚ) / 2) * (centralFactorialPoly m).derivative.derivative.eval ((r : ℚ) ^ 2) =
      (centralFactorialPoly m).derivative.eval ((r : ℚ) ^ 2) * harmonicTelescopingSum m r ∧
    ((1 : ℚ) / 2) * (centralFactorialPoly m).derivative.derivative.eval ((r : ℚ) ^ 2) =
      EPrimeForm1 m r * harmonicTelescopingClosed m r := by
  have hm0 : m ≠ 0 := by omega
  have hr_mem : r ∈ Finset.range m := Finset.mem_range.mpr hr
  let s := (Finset.range m).erase r
  let f : ℕ → ℚ := fun t => (t : ℚ) ^ 2
  let Q : Polynomial ℚ := ∏ t ∈ s, (Polynomial.X - Polynomial.C (f t))
  have h_prod_split :
      (∏ t ∈ Finset.range m, (Polynomial.X - Polynomial.C (f t))) =
        (Polynomial.X - Polynomial.C (f r)) * Q := by
    rw [← Finset.insert_erase hr_mem, Finset.prod_insert (Finset.not_mem_erase r _)]
  have h_lin_deriv : (Polynomial.X - Polynomial.C (f r)).derivative = 1 := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero]
  have h_d1 :
      (∏ t ∈ Finset.range m, (Polynomial.X - Polynomial.C (f t))).derivative =
        Q + (Polynomial.X - Polynomial.C (f r)) * Q.derivative := by
    rw [h_prod_split, Polynomial.derivative_mul, h_lin_deriv, one_mul]
  have h_d2 :
      (∏ t ∈ Finset.range m, (Polynomial.X - Polynomial.C (f t))).derivative.derivative =
        (2 : Polynomial ℚ) * Q.derivative +
          (Polynomial.X - Polynomial.C (f r)) * Q.derivative.derivative := by
    rw [h_d1, Polynomial.derivative_add, Polynomial.derivative_mul, h_lin_deriv, one_mul]
    ring
  have h_nz : ∀ t ∈ s, f r - f t ≠ 0 := by
    intro t ht
    have ht_ne : t ≠ r := (Finset.mem_erase.mp ht).1
    dsimp [f]
    intro h_eq
    have h_sq_nat : r ^ 2 = t ^ 2 := by exact_mod_cast sub_eq_zero.mp h_eq
    exact ht_ne (Nat.pow_left_injective (by decide : 2 ≠ 0) h_sq_nat.symm)
  have h_Q_deriv_eval :
      Q.derivative.eval (f r) = Q.eval (f r) * harmonicTelescopingSum m r := by
    dsimp [Q, harmonicTelescopingSum, s, f]
    rw [derivative_prod_linear_eval_eq_sum_div ((Finset.range m).erase r) (fun t => (t : ℚ) ^ 2) ((r : ℚ) ^ 2) h_nz]
    simp [Polynomial.eval_prod]
  have h_main :
      ((1 : ℚ) / 2) * (centralFactorialPoly m).derivative.derivative.eval ((r : ℚ) ^ 2) =
        (centralFactorialPoly m).derivative.eval ((r : ℚ) ^ 2) * harmonicTelescopingSum m r := by
    unfold centralFactorialPoly
    rw [if_neg hm0, Polynomial.derivative_C_mul, Polynomial.derivative_C_mul]
    change ((1 : ℚ) / 2) *
        (Polynomial.C ((2 : ℚ) / ((2 * m).factorial : ℚ)) *
          (∏ t ∈ Finset.range m, (Polynomial.X - Polynomial.C (f t))).derivative.derivative).eval (f r) =
      (Polynomial.C ((2 : ℚ) / ((2 * m).factorial : ℚ)) *
        (∏ t ∈ Finset.range m, (Polynomial.X - Polynomial.C (f t))).derivative).eval (f r) *
        harmonicTelescopingSum m r
    rw [h_d2, h_d1]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_ofNat, sub_self, zero_mul, add_zero]
    rw [h_Q_deriv_eval]
    ring
  refine ⟨h_main, ?_⟩
  rw [h_main, prop_2_3_derivative_eval_eq_EPrimeForm1 m r hr,
      prop_2_4_harmonic_telescoping m r hr]

/-- **Proposition 2.4 (Equation (2.11) Harmonic Telescoping for `r = 1`, Table 1)**:
For every `m ≥ 2`, `T(m, 1) = 1/4 + (1/2) * (1/(m-1) + 1/m)` and
`4 * T(m, 1) - 1 = 2(2m - 1) / (m(m - 1))`. -/
theorem prop_2_4_table_1_formula (m : ℕ) (hm : 2 ≤ m) :
    harmonicTelescopingClosed m 1 =
      (1 : ℚ) / 4 + ((1 : ℚ) / 2) * ((1 : ℚ) / ((m - 1 : ℕ) : ℚ) + (1 : ℚ) / (m : ℚ)) ∧
    (4 : ℚ) * harmonicTelescopingClosed m 1 - 1 =
      (2 * (2 * (m : ℚ) - 1)) / ((m : ℚ) * ((m - 1 : ℕ) : ℚ)) := by
  have h_ico : Finset.Ico (m - 1) (m + 1) = {m - 1, m} := by
    ext u
    simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    omega
  have h_ne : m - 1 ≠ m := by omega
  have h_closed :
      harmonicTelescopingClosed m 1 =
        (1 : ℚ) / 4 + ((1 : ℚ) / 2) * ((1 : ℚ) / ((m - 1 : ℕ) : ℚ) + (1 : ℚ) / (m : ℚ)) := by
    unfold harmonicTelescopingClosed
    rw [if_neg (by decide : (1 : ℕ) ≠ 0), h_ico, Finset.sum_pair h_ne]
    norm_num
  refine ⟨h_closed, ?_⟩
  rw [h_closed]
  have hm_ne : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hm1_ne : (m : ℚ) - 1 ≠ 0 := by
    have h_cast : ((m - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : m - 1 ≠ 0)
    rwa [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at h_cast
  have hm1_cast : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  rw [hm1_cast]
  field_simp [hm_ne, hm1_ne]
  ring

/-- Verification that `harmonicTelescopingSum m r = harmonicTelescopingClosed m r` across
benchmark values `(m, r) ∈ {(2, 1), (3, 1), (4, 1), (4, 2)}` follows immediately from
the general theorem `prop_2_4_harmonic_telescoping`. -/
theorem prop_2_4_harmonic_telescoping_verified :
    harmonicTelescopingSum 2 1 = harmonicTelescopingClosed 2 1 ∧
    harmonicTelescopingSum 3 1 = harmonicTelescopingClosed 3 1 ∧
    harmonicTelescopingSum 4 1 = harmonicTelescopingClosed 4 1 ∧
    harmonicTelescopingSum 4 2 = harmonicTelescopingClosed 4 2 :=
  ⟨prop_2_4_harmonic_telescoping 2 1 (by decide),
   prop_2_4_harmonic_telescoping 3 1 (by decide),
   prop_2_4_harmonic_telescoping 4 1 (by decide),
   prop_2_4_harmonic_telescoping 4 2 (by decide)⟩

/-!
## Theorem 2.5: Arbitrary-Order Derivative Formula, Newton Recurrence & Linear-Shift Factorization
-/

/-- Coefficient at `d = 0` when multiplying a polynomial `P` by `1 + C c * X`. -/
theorem coeff_one_add_C_mul_X_mul_zero (c : ℚ) (P : Polynomial ℚ) :
    ((1 + Polynomial.C c * Polynomial.X) * P).coeff 0 = P.coeff 0 := by
  have h_eq : (1 + Polynomial.C c * Polynomial.X) * P = P + Polynomial.C c * (Polynomial.X * P) := by
    ring
  rw [h_eq, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul_zero,
      mul_zero, add_zero]

/-- Coefficient at `d + 1` when multiplying a polynomial `P` by `1 + C c * X`. -/
theorem coeff_one_add_C_mul_X_mul_succ (c : ℚ) (P : Polynomial ℚ) (d : ℕ) :
    ((1 + Polynomial.C c * Polynomial.X) * P).coeff (d + 1) = P.coeff (d + 1) + c * P.coeff d := by
  have h_eq : (1 + Polynomial.C c * Polynomial.X) * P = P + Polynomial.C c * (Polynomial.X * P) := by
    ring
  rw [h_eq, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]

/-- The `d`-th elementary symmetric polynomial in the variables `{x t : t ∈ s}`, defined as the
coefficient of `X^d` in the generating product `∏ t ∈ s, (1 + C (x t) * X)`. -/
noncomputable def polyElemSymm (s : Finset ℕ) (x : ℕ → ℚ) (d : ℕ) : ℚ :=
  (∏ t ∈ s, (1 + Polynomial.C (x t) * Polynomial.X)).coeff d

@[simp]
theorem polyElemSymm_empty (x : ℕ → ℚ) (d : ℕ) :
    polyElemSymm ∅ x d = if d = 0 then 1 else 0 := by
  unfold polyElemSymm
  simp [Polynomial.coeff_one]

@[simp]
theorem polyElemSymm_zero (s : Finset ℕ) (x : ℕ → ℚ) :
    polyElemSymm s x 0 = 1 := by
  induction' s using Finset.cons_induction with a s ha ih
  · simp
  · unfold polyElemSymm at ih ⊢
    rw [Finset.prod_cons, coeff_one_add_C_mul_X_mul_zero, ih]

theorem polyElemSymm_insert_succ {a : ℕ} {s : Finset ℕ} (ha : a ∉ s) (x : ℕ → ℚ) (d : ℕ) :
    polyElemSymm (insert a s) x (d + 1) =
      polyElemSymm s x (d + 1) + x a * polyElemSymm s x d := by
  unfold polyElemSymm
  rw [Finset.prod_insert ha, coeff_one_add_C_mul_X_mul_succ]

theorem polyElemSymm_erase_add {t : ℕ} {s : Finset ℕ} (ht : t ∈ s) (x : ℕ → ℚ) (d : ℕ) :
    polyElemSymm s x (d + 1) =
      polyElemSymm (s.erase t) x (d + 1) + x t * polyElemSymm (s.erase t) x d := by
  conv_lhs => rw [← Finset.insert_erase ht]
  exact polyElemSymm_insert_succ (Finset.not_mem_erase t s) x d

/-- Alternating sum identity for `polyElemSymm`: for any `t ∈ s` and `d : ℕ`,
`∑_{j=1}^{d+1} (-1)^{j-1} (x t)^j e_{d+1-j}(s) = (x t) * e_d(s \ {t})`. -/
theorem polyElemSymm_alternating_sum_eq_erase {s : Finset ℕ} {t : ℕ} (ht : t ∈ s)
    (x : ℕ → ℚ) (d : ℕ) :
    (∑ j ∈ Finset.Icc 1 (d + 1),
      ((-1 : ℚ) ^ (j - 1)) * ((x t) ^ j) * polyElemSymm s x (d + 1 - j)) =
      x t * polyElemSymm (s.erase t) x d := by
  induction' d with d ih
  · simp [Finset.Icc_self]
  · have h_icc : Finset.Icc 1 (d + 2) = insert 1 (Finset.Icc 2 (d + 2)) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h_not_mem : (1 : ℕ) ∉ Finset.Icc 2 (d + 2) := by simp [Finset.mem_Icc]
    rw [h_icc, Finset.sum_insert h_not_mem]
    simp only [Nat.sub_self, pow_zero, one_mul, pow_one, Nat.add_sub_cancel]
    have h_shift :
        (∑ j ∈ Finset.Icc 2 (d + 2),
          ((-1 : ℚ) ^ (j - 1)) * ((x t) ^ j) * polyElemSymm s x (d + 2 - j)) =
        -(x t) * (∑ k ∈ Finset.Icc 1 (d + 1),
          ((-1 : ℚ) ^ (k - 1)) * ((x t) ^ k) * polyElemSymm s x (d + 1 - k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_bij (fun j _ => j - 1)
      · intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      · intro j₁ hj₁ j₂ hj₂ h_eq
        simp only [Finset.mem_Icc] at hj₁ hj₂
        omega
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        exact ⟨k + 1, Finset.mem_Icc.mpr (by omega), by omega⟩
      · intro j hj
        have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
        have h_pow1 : ((-1 : ℚ) ^ (j - 1)) = -((-1 : ℚ) ^ (j - 1 - 1)) := by
          conv_lhs => rw [show j - 1 = (j - 1 - 1) + 1 by omega, pow_succ]
          ring
        have h_pow2 : (x t) ^ j = (x t) * ((x t) ^ (j - 1)) := by
          conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
          ring
        have h_sub : d + 2 - j = d + 1 - (j - 1) := by omega
        rw [h_pow1, h_pow2, h_sub]
        ring
    rw [h_shift, ih, polyElemSymm_erase_add ht x d]
    ring

/-- Summation over `t ∈ s` of `(x t) * e_d(s \ {t})` equals `(d + 1) * e_{d+1}(s)`. -/
theorem sum_mul_polyElemSymm_erase (s : Finset ℕ) (x : ℕ → ℚ) :
    ∀ d : ℕ,
      (∑ t ∈ s, x t * polyElemSymm (s.erase t) x d) =
        ((d + 1 : ℕ) : ℚ) * polyElemSymm s x (d + 1) := by
  induction' s using Finset.cons_induction with a s ha ih
  · intro d
    simp
  · intro d
    rw [Finset.cons_eq_insert, Finset.sum_insert ha, Finset.erase_insert ha]
    have h_erase_other : ∀ t ∈ s, (insert a s).erase t = insert a (s.erase t) := by
      intro t ht
      have hta : a ≠ t := fun h => ha (h ▸ ht)
      exact Finset.erase_insert_of_ne hta
    rcases d with _ | k
    · have h_sum_zero : (∑ t ∈ s, x t * polyElemSymm ((insert a s).erase t) x 0) =
          ∑ t ∈ s, x t * polyElemSymm (s.erase t) x 0 := by
        apply Finset.sum_congr rfl
        intro t _
        simp [polyElemSymm_zero]
      rw [h_sum_zero, ih 0, polyElemSymm_insert_succ ha x 0]
      simp [polyElemSymm_zero]
      ring
    · have h_sum_step :
          (∑ t ∈ s, x t * polyElemSymm ((insert a s).erase t) x (k + 1)) =
            (∑ t ∈ s, x t * polyElemSymm (s.erase t) x (k + 1)) +
              x a * (∑ t ∈ s, x t * polyElemSymm (s.erase t) x k) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro t ht
        have ha_not_in : a ∉ s.erase t := fun h_in => ha (Finset.mem_of_mem_erase h_in)
        rw [h_erase_other t ht, polyElemSymm_insert_succ ha_not_in x k]
        ring
      rw [h_sum_step, ih (k + 1), ih k, polyElemSymm_insert_succ ha x (k + 1)]
      push_cast
      ring

/-- **General Newton Identity for `polyElemSymm` (Equation (2.15))**:
For any finite set `s : Finset ℕ`, variable family `x : ℕ → ℚ`, and `d : ℕ`,
$$(d + 1) e_{d+1}(s) = \sum_{j=1}^{d+1} (-1)^{j-1} \left(\sum_{t \in s} x_t^j\right) e_{d+1-j}(s).$$ -/
theorem polyElemSymm_newton_identity (s : Finset ℕ) (x : ℕ → ℚ) (d : ℕ) :
    ((d + 1 : ℕ) : ℚ) * polyElemSymm s x (d + 1) =
      ∑ j ∈ Finset.Icc 1 (d + 1),
        ((-1 : ℚ) ^ (j - 1)) * (∑ t ∈ s, (x t) ^ j) * polyElemSymm s x (d + 1 - j) := by
  rw [← sum_mul_polyElemSymm_erase s x d]
  have h_lhs :
      (∑ t ∈ s, x t * polyElemSymm (s.erase t) x d) =
        ∑ t ∈ s, ∑ j ∈ Finset.Icc 1 (d + 1),
          ((-1 : ℚ) ^ (j - 1)) * ((x t) ^ j) * polyElemSymm s x (d + 1 - j) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact (polyElemSymm_alternating_sum_eq_erase ht x d).symm
  rw [h_lhs, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- **General LCM Integrality for `polyElemSymm`**:
If `L : ℚ` clears the denominator of `x t` for every `t ∈ s` (i.e. `L * x t ∈ ℤ`),
then `L ^ d * polyElemSymm s x d ∈ ℤ` for every `d : ℕ`. -/
theorem polyElemSymm_lcm_int (s : Finset ℕ) (x : ℕ → ℚ) (L : ℚ)
    (hL : ∀ t ∈ s, ∃ z : ℤ, L * x t = (z : ℚ)) :
    ∀ d : ℕ, ∃ z : ℤ, (L ^ d) * polyElemSymm s x d = (z : ℚ) := by
  induction' s using Finset.cons_induction with a s ha ih
  · intro d
    rcases d with _ | d
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  · intro d
    rw [Finset.cons_eq_insert]
    have ha_int : ∃ z : ℤ, L * x a = (z : ℚ) := hL a (Finset.mem_cons_self a s)
    have hs_int : ∀ t ∈ s, ∃ z : ℤ, L * x t = (z : ℚ) :=
      fun t ht => hL t (Finset.mem_cons_of_mem ht)
    rcases d with _ | d
    · exact ⟨1, by simp⟩
    · rcases ih hs_int (d + 1) with ⟨z₁, hz₁⟩
      rcases ih hs_int d with ⟨z₂, hz₂⟩
      rcases ha_int with ⟨za, hza⟩
      refine ⟨z₁ + za * z₂, ?_⟩
      rw [polyElemSymm_insert_succ ha x d]
      have h_alg :
          (L ^ (d + 1)) * (polyElemSymm s x (d + 1) + x a * polyElemSymm s x d) =
            (L ^ (d + 1)) * polyElemSymm s x (d + 1) +
              (L * x a) * ((L ^ d) * polyElemSymm s x d) := by
        rw [pow_succ]
        ring
      rw [h_alg, hz₁, hz₂, hza]
      push_cast
      ring

/-- **Equation (2.18)**: The elementary symmetric polynomial `e_d(m, r)` in the `m - 1` variables
`{(r² - t²)⁻¹ : 0 ≤ t < m, t ≠ r}`. -/
noncomputable def elemSymmDeletedSq (m r d : ℕ) : ℚ :=
  polyElemSymm ((Finset.range m).erase r)
    (fun t => (1 : ℚ) / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) d

/-- **Equation (2.14)**: Power sums `T_d(m, r) := ∑_{0 ≤ t < m, t ≠ r} 1 / (r² - t²)^d`. -/
def powerSumTd (m r d : ℕ) : ℚ :=
  ∑ t ∈ (Finset.range m).erase r, (1 : ℚ) / (((r : ℚ) ^ 2 - (t : ℚ) ^ 2) ^ d)

/-- **Equation (2.15)**: Elementary symmetric sequence `e_d(m, r)` defined by Newton's recurrence
$$e_0(m, r) = 1, \quad e_d(m, r) = \frac{1}{d} \sum_{j=1}^d (-1)^{j-1} T_j(m, r) e_{d-j}(m, r).$$ -/
def elemSymmNewton (m r : ℕ) : ℕ → ℚ
  | 0 => 1
  | d + 1 =>
    ((1 : ℚ) / ((d + 1 : ℕ) : ℚ)) *
      ∑ j ∈ Finset.attach (Finset.Icc 1 (d + 1)),
        ((-1 : ℚ) ^ (j.1 - 1)) * powerSumTd m r j.1 * elemSymmNewton m r (d + 1 - j.1)
termination_by d => d
decreasing_by
  have hj : 1 ≤ j.1 := (Finset.mem_Icc.mp j.2).1
  omega

/-- **Theorem 2.5 (Equation (2.15): Proof of Newton's Recurrence for `elemSymmDeletedSq`)**:
For all `m, r, d : ℕ`, the elementary symmetric polynomial `elemSymmDeletedSq m r d`
satisfies Newton's recurrence and therefore equals `elemSymmNewton m r d`. -/
theorem elemSymmDeletedSq_eq_elemSymmNewton (m r : ℕ) :
    ∀ d : ℕ, elemSymmDeletedSq m r d = elemSymmNewton m r d := by
  intro d
  induction' d using Nat.strong_induction_on with d ih
  rcases d with _ | d
  · unfold elemSymmDeletedSq elemSymmNewton
    exact polyElemSymm_zero _ _
  · unfold elemSymmDeletedSq
    rw [elemSymmNewton]
    rw [Finset.sum_attach (Finset.Icc 1 (d + 1))
      (fun j => ((-1 : ℚ) ^ (j - 1)) * powerSumTd m r j * elemSymmNewton m r (d + 1 - j))]
    have h_newton :=
      polyElemSymm_newton_identity ((Finset.range m).erase r)
        (fun t => (1 : ℚ) / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) d
    have hd_ne : ((d + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : d + 1 ≠ 0)
    rw [← mul_right_inj' hd_ne, h_newton]
    have h_cancel :
        ((d + 1 : ℕ) : ℚ) * (((1 : ℚ) / ((d + 1 : ℕ) : ℚ)) *
          ∑ x ∈ Finset.Icc 1 (d + 1),
            ((-1 : ℚ) ^ (x - 1)) * powerSumTd m r x * elemSymmNewton m r (d + 1 - x)) =
        ∑ x ∈ Finset.Icc 1 (d + 1),
          ((-1 : ℚ) ^ (x - 1)) * powerSumTd m r x * elemSymmNewton m r (d + 1 - x) := by
      rw [← mul_assoc, mul_one_div_cancel hd_ne, one_mul]
    rw [h_cancel]
    apply Finset.sum_congr rfl
    intro j hj
    have hj_ge : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have h_lt : d + 1 - j < d + 1 := by omega
    rw [← ih (d + 1 - j) h_lt]
    unfold elemSymmDeletedSq powerSumTd
    congr 2
    apply Finset.sum_congr rfl
    intro t _
    rw [one_div_pow]

/-- Helper identity for factoring out constant products from `∏ t ∈ s, (X + C (c t))`. -/
theorem prod_X_add_C_eq_prod_C_mul_prod_one_add (s : Finset ℕ) (c : ℕ → ℚ)
    (hc : ∀ t ∈ s, c t ≠ 0) :
    (∏ t ∈ s, (Polynomial.X + Polynomial.C (c t))) =
      Polynomial.C (∏ t ∈ s, c t) *
        ∏ t ∈ s, (1 + Polynomial.C ((1 : ℚ) / c t) * Polynomial.X) := by
  induction' s using Finset.cons_induction with a s ha ih
  · simp
  · have ha_ne : c a ≠ 0 := hc a (Finset.mem_cons_self a s)
    have hs_ne : ∀ t ∈ s, c t ≠ 0 := fun t ht => hc t (Finset.mem_cons_of_mem ht)
    rw [Finset.prod_cons, Finset.prod_cons, Finset.prod_cons, Polynomial.C_mul, ih hs_ne]
    have h_factor :
        Polynomial.X + Polynomial.C (c a) =
          Polynomial.C (c a) * (1 + Polynomial.C ((1 : ℚ) / c a) * Polynomial.X) := by
      rw [mul_add, mul_one, ← mul_assoc, ← Polynomial.C_mul, mul_one_div_cancel ha_ne,
          Polynomial.C_1, one_mul, add_comm]
    rw [h_factor]
    ring

/-- **Theorem 2.5 (Equation (2.17): Exact Taylor Shift Polynomial Factorization)**:
For every `m ≥ 1` and `0 ≤ r < m`, the Taylor-shifted central factorial polynomial
`(centralFactorialPoly m).comp (X + C (r²))` factors in `ℚ[X]` as:
$$\mathcal{E}_m(r^2 + X) = \mathcal{E}_m'(r^2) X \prod_{\substack{0 \le t < m \\ t \ne r}} \left(1 + \frac{X}{r^2 - t^2}\right).$$ -/
theorem theorem_2_5_taylor_shift_factorization (m r : ℕ) (hr : r < m) :
    (centralFactorialPoly m).comp (Polynomial.X + Polynomial.C ((r : ℚ) ^ 2)) =
      Polynomial.C (EPrimeForm1 m r) * Polynomial.X *
        ∏ t ∈ (Finset.range m).erase r,
          (1 + Polynomial.C ((1 : ℚ) / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) * Polynomial.X) := by
  have hm0 : m ≠ 0 := by omega
  have hr_mem : r ∈ Finset.range m := Finset.mem_range.mpr hr
  unfold centralFactorialPoly
  rw [if_neg hm0, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.prod_comp]
  have h_split_prod :
      (∏ j ∈ Finset.range m,
        (Polynomial.X - Polynomial.C ((j : ℚ) ^ 2)).comp
          (Polynomial.X + Polynomial.C ((r : ℚ) ^ 2))) =
      (Polynomial.X - Polynomial.C ((r : ℚ) ^ 2)).comp
        (Polynomial.X + Polynomial.C ((r : ℚ) ^ 2)) *
      ∏ j ∈ (Finset.range m).erase r,
        (Polynomial.X - Polynomial.C ((j : ℚ) ^ 2)).comp
          (Polynomial.X + Polynomial.C ((r : ℚ) ^ 2)) :=
    (Finset.mul_prod_erase (Finset.range m)
      (fun j => (Polynomial.X - Polynomial.C ((j : ℚ) ^ 2)).comp
        (Polynomial.X + Polynomial.C ((r : ℚ) ^ 2))) hr_mem).symm
  rw [h_split_prod]
  have h_root_term :
      (Polynomial.X - Polynomial.C ((r : ℚ) ^ 2)).comp
        (Polynomial.X + Polynomial.C ((r : ℚ) ^ 2)) = Polynomial.X := by
    simp [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  have h_other_terms :
      (∏ x ∈ (Finset.range m).erase r,
        (Polynomial.X - Polynomial.C ((x : ℚ) ^ 2)).comp
          (Polynomial.X + Polynomial.C ((r : ℚ) ^ 2))) =
      ∏ x ∈ (Finset.range m).erase r,
        (Polynomial.X + Polynomial.C ((r : ℚ) ^ 2 - (x : ℚ) ^ 2)) := by
    apply Finset.prod_congr rfl
    intro t _
    simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    rw [add_sub_assoc, ← Polynomial.C_sub]
  have h_nz : ∀ t ∈ (Finset.range m).erase r, (r : ℚ) ^ 2 - (t : ℚ) ^ 2 ≠ 0 := by
    intro t ht
    have ht_ne : t ≠ r := (Finset.mem_erase.mp ht).1
    intro h_eq
    have h_sq_nat : r ^ 2 = t ^ 2 := by exact_mod_cast sub_eq_zero.mp h_eq
    exact ht_ne (Nat.pow_left_injective (by decide : 2 ≠ 0) h_sq_nat.symm)
  rw [h_root_term, h_other_terms,
      prod_X_add_C_eq_prod_C_mul_prod_one_add ((Finset.range m).erase r)
        (fun t => (r : ℚ) ^ 2 - (t : ℚ) ^ 2) h_nz]
  have h_const :
      Polynomial.C ((2 : ℚ) / ((2 * m).factorial : ℚ)) *
        Polynomial.C (∏ t ∈ (Finset.range m).erase r, ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) =
      Polynomial.C (EPrimeForm1 m r) := by
    rw [← Polynomial.C_mul]
    congr 1
    unfold EPrimeForm1
    rw [div_mul_eq_mul_div, deleted_sq_prod_eq_signed_factorials m r hr]
  calc Polynomial.C ((2 : ℚ) / ((2 * m).factorial : ℚ)) *
        (Polynomial.X *
          (Polynomial.C (∏ t ∈ (Finset.range m).erase r, ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) *
            ∏ t ∈ (Finset.range m).erase r,
              (1 + Polynomial.C ((1 : ℚ) / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) * Polynomial.X)))
      = (Polynomial.C ((2 : ℚ) / ((2 * m).factorial : ℚ)) *
          Polynomial.C (∏ t ∈ (Finset.range m).erase r, ((r : ℚ) ^ 2 - (t : ℚ) ^ 2))) *
        Polynomial.X *
        ∏ t ∈ (Finset.range m).erase r,
          (1 + Polynomial.C ((1 : ℚ) / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) * Polynomial.X) := by ring
    _ = Polynomial.C (EPrimeForm1 m r) * Polynomial.X *
        ∏ t ∈ (Finset.range m).erase r,
          (1 + Polynomial.C ((1 : ℚ) / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) * Polynomial.X) := by
        rw [h_const]

/-- **Theorem 2.5 (Equation (2.13))**: Normalized `q`-th derivative formula
`(1 / q!) ℰ_m^{(q)}(r²) = ℰ_m'(r²) e_{q-1}(m, r)` for `q ≥ 1`. -/
def ENormDerivClosed (m r q : ℕ) : ℚ :=
  if q = 0 then evalCentralFactorial m ((r : ℚ) ^ 2)
  else EPrimeForm1 m r * elemSymmNewton m r (q - 1)

/-- **Theorem 2.5 (Equation (2.13): Proved Arbitrary-Order Taylor Coefficient Identity)**:
For every `m ≥ 1`, `0 ≤ r < m`, and `q ≥ 1`, the `q`-th Taylor coefficient of
`centralFactorialPoly m` at `u = r²` equals `EPrimeForm1 m r * elemSymmDeletedSq m r (q - 1)`
and `ENormDerivClosed m r q`. -/
theorem theorem_2_5_arbitrary_order_derivative (m r q : ℕ) (hr : r < m) (hq : 1 ≤ q) :
    ((centralFactorialPoly m).comp (Polynomial.X + Polynomial.C ((r : ℚ) ^ 2))).coeff q =
      EPrimeForm1 m r * elemSymmDeletedSq m r (q - 1) ∧
    ((centralFactorialPoly m).comp (Polynomial.X + Polynomial.C ((r : ℚ) ^ 2))).coeff q =
      ENormDerivClosed m r q := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0) with ⟨d, rfl⟩
  have h_fact := theorem_2_5_taylor_shift_factorization m r hr
  have h_coeff :
      ((centralFactorialPoly m).comp (Polynomial.X + Polynomial.C ((r : ℚ) ^ 2))).coeff (d + 1) =
        EPrimeForm1 m r * elemSymmDeletedSq m r d := by
    rw [h_fact, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
    rfl
  refine ⟨h_coeff, ?_⟩
  rw [h_coeff]
  unfold ENormDerivClosed
  rw [if_neg (by omega : d + 1 ≠ 0)]
  change EPrimeForm1 m r * elemSymmDeletedSq m r d = EPrimeForm1 m r * elemSymmNewton m r d
  rw [elemSymmDeletedSq_eq_elemSymmNewton m r d]

/-- At `q = 1`, `ENormDerivClosed m r 1 = EPrimeForm1 m r` since `e_0(m, r) = 1`. -/
@[simp]
theorem ENormDerivClosed_one (m r : ℕ) :
    ENormDerivClosed m r 1 = EPrimeForm1 m r := by
  unfold ENormDerivClosed elemSymmNewton
  simp

/-- At `q = 2`, `ENormDerivClosed m r 2 = EPrimeForm1 m r * T(m, r)` matching Proposition 2.4 (2.10). -/
theorem ENormDerivClosed_two (m r : ℕ) :
    ENormDerivClosed m r 2 = EPrimeForm1 m r * harmonicTelescopingSum m r := by
  unfold ENormDerivClosed
  rw [if_neg (by decide : (2 : ℕ) ≠ 0)]
  congr 1
  change elemSymmNewton m r (0 + 1) = harmonicTelescopingSum m r
  rw [elemSymmNewton]
  rw [Finset.sum_attach (Finset.Icc 1 1)
    (fun j => ((-1 : ℚ) ^ (j - 1)) * powerSumTd m r j * elemSymmNewton m r (1 - j))]
  simp [Finset.Icc_self, Finset.sum_singleton, elemSymmNewton, powerSumTd, harmonicTelescopingSum]

/-- The least common multiple `L_n := lcm(1, 2, ..., n)`. -/
def lcmUpTo (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm id

theorem dvd_lcmUpTo {k n : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    k ∣ lcmUpTo n :=
  Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hk1, hkn⟩)

/-- **Theorem 2.5 (Equation (2.16): LCM Denominator Bound for `e_{q-1}(m, r)` and `(1/q!) ℰ_m^{(q)}(r²)`)**:
For every `m ≥ 1`, `0 ≤ r < m`, and `d : ℕ`, `(lcmUpTo (2 * m))^{2d} * e_d(m, r) ∈ ℤ`,
and hence for every `q ≥ 1`,
`(lcmUpTo (2 * m))^{2(q-1)} * (1 / ℰ_m'(r²)) * ((1 / q!) ℰ_m^{(q)}(r²)) ∈ ℤ`. -/
theorem theorem_2_5_lcm_elemSymm_int (m r d : ℕ) (hr : r < m) :
    ∃ z : ℤ, ((lcmUpTo (2 * m) : ℚ) ^ (2 * d)) * elemSymmDeletedSq m r d = (z : ℚ) := by
  have h_pow : ((lcmUpTo (2 * m) : ℚ) ^ (2 * d)) = (((lcmUpTo (2 * m) : ℚ) ^ 2) ^ d) := by
    rw [← pow_mul]
  rw [h_pow]
  unfold elemSymmDeletedSq
  apply polyElemSymm_lcm_int ((Finset.range m).erase r)
    (fun t => (1 : ℚ) / ((r : ℚ) ^ 2 - (t : ℚ) ^ 2)) ((lcmUpTo (2 * m) : ℚ) ^ 2)
  intro t ht
  have ht_ne : t ≠ r := (Finset.mem_erase.mp ht).1
  have ht_lt : t < m := Finset.mem_range.mp (Finset.mem_of_mem_erase ht)
  have h_plus_dvd : (r + t) ∣ lcmUpTo (2 * m) :=
    dvd_lcmUpTo (by omega) (by omega)
  rcases h_plus_dvd with ⟨k_plus, hk_plus⟩
  rcases lt_trichotomy r t with h_rt | rfl | h_tr
  · have h_minus_dvd : (t - r) ∣ lcmUpTo (2 * m) :=
      dvd_lcmUpTo (by omega) (by omega)
    rcases h_minus_dvd with ⟨k_minus, hk_minus⟩
    refine ⟨-(k_minus : ℤ) * (k_plus : ℤ), ?_⟩
    have h_diff_ne : (r : ℚ) ^ 2 - (t : ℚ) ^ 2 ≠ 0 := by
      have h_f : (r : ℚ) ^ 2 - (t : ℚ) ^ 2 = -(((t : ℚ) - (r : ℚ)) * ((r : ℚ) + (t : ℚ))) := by ring
      rw [h_f]
      have h1 : (t : ℚ) - (r : ℚ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : t ≠ r))
      have h2 : (r : ℚ) + (t : ℚ) ≠ 0 := by exact_mod_cast (by omega : r + t ≠ 0)
      exact neg_ne_zero.mpr (mul_ne_zero h1 h2)
    have h_lcm_sq :
        ((lcmUpTo (2 * m) : ℚ) ^ 2) =
          (-(k_minus : ℚ) * (k_plus : ℚ)) * ((r : ℚ) ^ 2 - (t : ℚ) ^ 2) := by
      have h1 : (lcmUpTo (2 * m) : ℚ) = ((t - r : ℕ) : ℚ) * (k_minus : ℚ) := by
        exact_mod_cast hk_minus
      have h2 : (lcmUpTo (2 * m) : ℚ) = ((r + t : ℕ) : ℚ) * (k_plus : ℚ) := by
        exact_mod_cast hk_plus
      have h_sub : ((t - r : ℕ) : ℚ) = (t : ℚ) - (r : ℚ) := Nat.cast_sub (by omega)
      have h_add : ((r + t : ℕ) : ℚ) = (r : ℚ) + (t : ℚ) := by push_cast; rfl
      rw [h_sub] at h1
      rw [h_add] at h2
      have h_prod := congrArg₂ (· * ·) h1 h2
      dsimp only at h_prod
      calc ((lcmUpTo (2 * m) : ℚ) ^ 2)
          = (lcmUpTo (2 * m) : ℚ) * (lcmUpTo (2 * m) : ℚ) := by ring
        _ = (((t : ℚ) - (r : ℚ)) * (k_minus : ℚ)) * (((r : ℚ) + (t : ℚ)) * (k_plus : ℚ)) := h_prod
        _ = (-(k_minus : ℚ) * (k_plus : ℚ)) * ((r : ℚ) ^ 2 - (t : ℚ) ^ 2) := by ring
    rw [h_lcm_sq, mul_assoc, mul_one_div_cancel h_diff_ne, mul_one]
    push_cast
    ring
  · contradiction
  · have h_minus_dvd : (r - t) ∣ lcmUpTo (2 * m) :=
      dvd_lcmUpTo (by omega) (by omega)
    rcases h_minus_dvd with ⟨k_minus, hk_minus⟩
    refine ⟨(k_minus : ℤ) * (k_plus : ℤ), ?_⟩
    have h_diff_ne : (r : ℚ) ^ 2 - (t : ℚ) ^ 2 ≠ 0 := by
      have h_f : (r : ℚ) ^ 2 - (t : ℚ) ^ 2 = ((r : ℚ) - (t : ℚ)) * ((r : ℚ) + (t : ℚ)) := by ring
      rw [h_f]
      have h1 : (r : ℚ) - (t : ℚ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : r ≠ t))
      have h2 : (r : ℚ) + (t : ℚ) ≠ 0 := by exact_mod_cast (by omega : r + t ≠ 0)
      exact mul_ne_zero h1 h2
    have h_lcm_sq :
        ((lcmUpTo (2 * m) : ℚ) ^ 2) =
          ((k_minus : ℚ) * (k_plus : ℚ)) * ((r : ℚ) ^ 2 - (t : ℚ) ^ 2) := by
      have h1 : (lcmUpTo (2 * m) : ℚ) = ((r - t : ℕ) : ℚ) * (k_minus : ℚ) := by
        exact_mod_cast hk_minus
      have h2 : (lcmUpTo (2 * m) : ℚ) = ((r + t : ℕ) : ℚ) * (k_plus : ℚ) := by
        exact_mod_cast hk_plus
      have h_sub : ((r - t : ℕ) : ℚ) = (r : ℚ) - (t : ℚ) := Nat.cast_sub (by omega)
      have h_add : ((r + t : ℕ) : ℚ) = (r : ℚ) + (t : ℚ) := by push_cast; rfl
      rw [h_sub] at h1
      rw [h_add] at h2
      have h_prod := congrArg₂ (· * ·) h1 h2
      dsimp only at h_prod
      calc ((lcmUpTo (2 * m) : ℚ) ^ 2)
          = (lcmUpTo (2 * m) : ℚ) * (lcmUpTo (2 * m) : ℚ) := by ring
        _ = (((r : ℚ) - (t : ℚ)) * (k_minus : ℚ)) * (((r : ℚ) + (t : ℚ)) * (k_plus : ℚ)) := h_prod
        _ = ((k_minus : ℚ) * (k_plus : ℚ)) * ((r : ℚ) ^ 2 - (t : ℚ) ^ 2) := by ring
    rw [h_lcm_sq, mul_assoc, mul_one_div_cancel h_diff_ne, mul_one]
    push_cast
    ring

/-- **Theorem 2.5 (Equation (2.19): Linear-Shift Product Factorization)**:
For every `m ≥ 1`, `r ∈ ℤ`, and `w ∈ ℚ`, expanding `ℰ_m((w + r)²)` in `w` factors as
$$\mathcal{E}_m((w + r)^2) = \frac{2}{(2m)!} (w + r)^2 \prod_{t=1}^{m-1} (w + r - t)(w + r + t).$$ -/
theorem theorem_2_5_linear_shift_product (m : ℕ) (hm : 1 ≤ m) (r : ℤ) (w : ℚ) :
    evalCentralFactorial m ((w + (r : ℚ)) ^ 2) =
      ((2 : ℚ) / ((2 * m).factorial : ℚ)) * ((w + (r : ℚ)) ^ 2) *
        ∏ t ∈ Finset.Ico 1 m, ((w + (r : ℚ) - (t : ℚ)) * (w + (r : ℚ) + (t : ℚ))) := by
  unfold evalCentralFactorial
  rw [if_neg (by omega : m ≠ 0)]
  have h_range : Finset.range m = insert 0 (Finset.Ico 1 m) := by
    ext t
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [h_range, Finset.prod_insert (by simp)]
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
  rw [← mul_assoc]
  congr 1
  apply Finset.prod_congr rfl
  intro t _
  ring

open Polynomial

/-- The falling-factorial polynomial `∏_{j=0}^{k-1} (X - j)` in `Polynomial ℚ`. -/
noncomputable def fallingFactorialPoly (k : ℕ) : Polynomial ℚ :=
  ∏ j ∈ Finset.range k, (X - C (j : ℚ))

/-- The binomial polynomial `\binom{X}{k} := \frac{1}{k!} \prod_{j=0}^{k-1} (X - j)` in `Polynomial ℚ`
appearing in the Vandermonde expansion (Equations (2.21)–(2.22)). -/
noncomputable def binomPoly (k : ℕ) : Polynomial ℚ :=
  C ((1 : ℚ) / (k.factorial : ℚ)) * fallingFactorialPoly k

/-- Helper lemma: for any natural numbers `w` and `k`, the falling factorial product in `ℚ`
equals `k! * \binom{w}{k}`. -/
theorem prod_sub_range_eq_factorial_mul_choose (w k : ℕ) :
    (∏ j ∈ Finset.range k, ((w : ℚ) - (j : ℚ))) =
      (k.factorial : ℚ) * (Nat.choose w k : ℚ) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih]
    have h_choose : (k + 1) * Nat.choose w (k + 1) = (w - k) * Nat.choose w k := by
      have h := Nat.choose_succ_right_eq w k
      linarith [h]
    rcases lt_or_ge w k with hlt | hge
    · have h_ck : Nat.choose w k = 0 := Nat.choose_eq_zero_of_lt hlt
      have h_ck1 : Nat.choose w (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h_ck, h_ck1]
    · have h_sub_cast : ((w - k : ℕ) : ℚ) = (w : ℚ) - (k : ℚ) := Nat.cast_sub hge
      have h_choose_q : ((k + 1 : ℕ) : ℚ) * (Nat.choose w (k + 1) : ℚ) =
          ((w : ℚ) - (k : ℚ)) * (Nat.choose w k : ℚ) := by
        rw [← h_sub_cast]
        exact_mod_cast h_choose
      rw [Nat.factorial_succ]
      push_cast
      calc (k.factorial : ℚ) * (Nat.choose w k : ℚ) * ((w : ℚ) - (k : ℚ))
          = (k.factorial : ℚ) * (((w : ℚ) - (k : ℚ)) * (Nat.choose w k : ℚ)) := by ring
        _ = (k.factorial : ℚ) * (((k : ℚ) + 1) * (Nat.choose w (k + 1) : ℚ)) := by
            rw [← h_choose_q]; push_cast; rfl
        _ = ((k : ℚ) + 1) * (k.factorial : ℚ) * (Nat.choose w (k + 1) : ℚ) := by ring

/-- Evaluating `binomPoly k` at any natural number `w : ℕ` yields `\binom{w}{k}`. -/
theorem eval_binomPoly_nat (k w : ℕ) :
    (binomPoly k).eval (w : ℚ) = (Nat.choose w k : ℚ) := by
  unfold binomPoly fallingFactorialPoly
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [prod_sub_range_eq_factorial_mul_choose w k]
  have h_fac_ne : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  field_simp [h_fac_ne]

/-- For `k ≥ 1`, `binomPoly k` factors as `C ((-1)^(k-1) / k) * X * ∏_{j=1}^{k-1} (1 + C (-1/j) * X)`. -/
theorem binomPoly_eq_C_mul_X_mul_prod (k : ℕ) (hk : 1 ≤ k) :
    binomPoly k =
      C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * X *
        ∏ j ∈ Finset.Ico 1 k, (1 + C (-(1 : ℚ) / (j : ℚ)) * X) := by
  unfold binomPoly fallingFactorialPoly
  have h_range : Finset.range k = insert 0 (Finset.Ico 1 k) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [h_range, Finset.prod_insert (by simp)]
  have h_zero : X - C ((0 : ℕ) : ℚ) = (X : Polynomial ℚ) := by simp
  rw [h_zero]
  have h_prod :
      (∏ j ∈ Finset.Ico 1 k, (X - C (j : ℚ))) =
        C (∏ j ∈ Finset.Ico 1 k, (-(j : ℚ))) *
          ∏ j ∈ Finset.Ico 1 k, (1 + C (-(1 : ℚ) / (j : ℚ)) * X) := by
    have h_lhs :
        (∏ j ∈ Finset.Ico 1 k, (X - C (j : ℚ))) =
          ∏ j ∈ Finset.Ico 1 k, (X + C (-(j : ℚ))) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [Polynomial.C_neg, sub_eq_add_neg]
    have h_rhs :
        (∏ j ∈ Finset.Ico 1 k, (1 + C ((1 : ℚ) / (-(j : ℚ))) * X)) =
          ∏ j ∈ Finset.Ico 1 k, (1 + C (-(1 : ℚ) / (j : ℚ)) * X) := by
      apply Finset.prod_congr rfl
      intro j _
      congr 2
      ring
    rw [h_lhs, ← h_rhs]
    exact prod_X_add_C_eq_prod_C_mul_prod_one_add (Finset.Ico 1 k) (fun j => -(j : ℚ))
      (fun j hj => by
        have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
        have : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
        exact neg_ne_zero.mpr this)
  rw [h_prod]
  have h_const_prod :
      (∏ j ∈ Finset.Ico 1 k, (-(j : ℚ))) = (-1 : ℚ) ^ (k - 1) * ((k - 1).factorial : ℚ) := by
    have h_neg : (∏ j ∈ Finset.Ico 1 k, (-(j : ℚ))) =
        (∏ j ∈ Finset.Ico 1 k, (-1 : ℚ)) * (∏ j ∈ Finset.Ico 1 k, (j : ℚ)) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _; ring
    rw [h_neg, Finset.prod_const, Nat.card_Ico]
    congr 1
    have h_fac : ∀ n : ℕ, (∏ j ∈ Finset.Ico 1 (n + 1), (j : ℚ)) = (n.factorial : ℚ) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.prod_Ico_succ_top (by omega : 1 ≤ n + 1), ih, Nat.factorial_succ]
        push_cast; ring
    have hk_eq : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk_eq]
    exact h_fac (k - 1)
  have h_coeff_eq :
      ((1 : ℚ) / (k.factorial : ℚ)) * (∏ j ∈ Finset.Ico 1 k, (-(j : ℚ))) =
        (-1 : ℚ) ^ (k - 1) / (k : ℚ) := by
    rw [h_const_prod]
    have hk_fac : (k.factorial : ℚ) = (k : ℚ) * ((k - 1).factorial : ℚ) := by
      have h_nat : k.factorial = k * (k - 1).factorial := by
        cases k with
        | zero => omega
        | succ m => simp [Nat.factorial_succ]
      exact_mod_cast h_nat
    rw [hk_fac]
    have h_km1_ne : ((k - 1).factorial : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (k - 1)
    have hk_ne : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    field_simp [h_km1_ne, hk_ne]
    ring
  calc C ((1 : ℚ) / (k.factorial : ℚ)) *
        (X * (C (∏ j ∈ Finset.Ico 1 k, -(j : ℚ)) *
          ∏ j ∈ Finset.Ico 1 k, (1 + C (-(1 : ℚ) / (j : ℚ)) * X)))
      = (C ((1 : ℚ) / (k.factorial : ℚ)) * C (∏ j ∈ Finset.Ico 1 k, -(j : ℚ))) * X *
          ∏ j ∈ Finset.Ico 1 k, (1 + C (-(1 : ℚ) / (j : ℚ)) * X) := by ring
    _ = C ((-1 : ℚ) ^ (k - 1) / (k : ℚ)) * X *
          ∏ j ∈ Finset.Ico 1 k, (1 + C (-(1 : ℚ) / (j : ℚ)) * X) := by
        rw [← Polynomial.C_mul, h_coeff_eq]

/-- Every coefficient `[w^d] \binom{w}{k}` for `0 ≤ k ≤ 2m` is `lcm(1,...,2m)^d`-integral. -/
theorem binomPoly_coeff_lcm_int (m k d : ℕ) (hk : k ≤ 2 * m) :
    ∃ z : ℤ, ((lcmUpTo (2 * m) : ℚ) ^ d) * (binomPoly k).coeff d = (z : ℚ) := by
  rcases eq_or_ne k 0 with rfl | hk0
  · have hk0_poly : binomPoly 0 = 1 := by
      unfold binomPoly fallingFactorialPoly
      simp
    rw [hk0_poly]
    rcases eq_or_ne d 0 with rfl | hd0
    · refine ⟨1, ?_⟩; simp
    · refine ⟨0, ?_⟩; simp [Polynomial.coeff_one, if_neg hd0]
  · rcases eq_or_ne d 0 with rfl | hd0
    · rw [binomPoly_eq_C_mul_X_mul_prod k (by omega)]
      refine ⟨0, ?_⟩
      rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul_zero]
      simp
    · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      rw [binomPoly_eq_C_mul_X_mul_prod k (by omega)]
      rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
      change ∃ z : ℤ,
        ((lcmUpTo (2 * m) : ℚ) ^ (d' + 1)) *
          (((-1 : ℚ) ^ (k - 1) / (k : ℚ)) *
            polyElemSymm (Finset.Ico 1 k) (fun j => -(1 : ℚ) / (j : ℚ)) d') = (z : ℚ)
      obtain ⟨zk, hzk⟩ : (k : ℕ) ∣ lcmUpTo (2 * m) := dvd_lcmUpTo (by omega) hk
      obtain ⟨z_symm, hz_symm⟩ :=
        polyElemSymm_lcm_int (Finset.Ico 1 k) (fun j => -(1 : ℚ) / (j : ℚ))
          (lcmUpTo (2 * m) : ℚ)
          (fun j hj => by
            have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
            have hjk : j < k := (Finset.mem_Ico.mp hj).2
            obtain ⟨zj, hzj⟩ : j ∣ lcmUpTo (2 * m) := dvd_lcmUpTo hj1 (by omega)
            refine ⟨-(zj : ℤ), ?_⟩
            have hj_ne : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
            have h_lcm_q : (lcmUpTo (2 * m) : ℚ) = (j : ℚ) * (zj : ℚ) := by exact_mod_cast hzj
            dsimp only
            rw [h_lcm_q]
            push_cast
            field_simp [hj_ne]
            ring) d'
      refine ⟨(-1) ^ (k - 1) * (zk : ℤ) * z_symm, ?_⟩
      have hk_ne : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
      have h_lcm_k : (lcmUpTo (2 * m) : ℚ) = (k : ℚ) * (zk : ℚ) := by exact_mod_cast hzk
      have h_pow : ((lcmUpTo (2 * m) : ℚ) ^ (d' + 1)) =
          (lcmUpTo (2 * m) : ℚ) * ((lcmUpTo (2 * m) : ℚ) ^ d') := by ring
      calc ((lcmUpTo (2 * m) : ℚ) ^ (d' + 1)) *
            (((-1 : ℚ) ^ (k - 1) / (k : ℚ)) *
              polyElemSymm (Finset.Ico 1 k) (fun j => -(1 : ℚ) / (j : ℚ)) d')
          = ((lcmUpTo (2 * m) : ℚ) * ((-1 : ℚ) ^ (k - 1) / (k : ℚ))) *
              (((lcmUpTo (2 * m) : ℚ) ^ d') *
                polyElemSymm (Finset.Ico 1 k) (fun j => -(1 : ℚ) / (j : ℚ)) d') := by
              rw [h_pow]; ring
        _ = ((k : ℚ) * (zk : ℚ) * ((-1 : ℚ) ^ (k - 1) / (k : ℚ))) * (z_symm : ℚ) := by
              rw [hz_symm, h_lcm_k]
        _ = (((-1 : ℤ) ^ (k - 1) * (zk : ℤ) * z_symm : ℤ) : ℚ) := by
              push_cast
              field_simp [hk_ne]
              ring

/-- **Theorem 2.5 (Equations (2.21)–(2.22): Vandermonde Binomial Expansion on Natural Numbers)**:
For every `m ≥ 1` and natural numbers `r, w ∈ ℕ`, expanding `\mathcal{E}_m((w + r)^2)` via
Proposition 2.2(i) and Vandermonde's convolution identity yields
$$\mathcal{E}_m((w + r)^2) = \sum_{k=0}^{2m} \left(\binom{r+m}{2m-k} + \binom{r+m-1}{2m-k}\right) \binom{w}{k}.$$ -/
theorem theorem_2_5_vandermonde_eval_nat (m r w : ℕ) (hm : 1 ≤ m) :
    evalCentralFactorial m (((w : ℚ) + (r : ℚ)) ^ 2) =
      ∑ k ∈ Finset.range (2 * m + 1),
        ((Nat.choose (r + m) (2 * m - k) : ℚ) + (Nat.choose (r + m - 1) (2 * m - k) : ℚ)) *
          (Nat.choose w k : ℚ) := by
  have h_cast : (w : ℚ) + (r : ℚ) = ((w + r : ℕ) : ℚ) := by push_cast; rfl
  rw [h_cast, prop_2_2_binomial_identity m (w + r) hm]
  have h1 : Nat.choose (w + r + m) (2 * m) =
      ∑ k ∈ Finset.range (2 * m + 1), Nat.choose (r + m) (2 * m - k) * Nat.choose w k := by
    have h_eq : w + r + m = w + (r + m) := by omega
    rw [h_eq, Nat.add_choose_eq]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Nat.choose w i * Nat.choose (r + m) j) (2 * m)]
    apply Finset.sum_congr rfl
    intro k _
    exact Nat.mul_comm _ _
  have h2 : Nat.choose (w + r + m - 1) (2 * m) =
      ∑ k ∈ Finset.range (2 * m + 1), Nat.choose (r + m - 1) (2 * m - k) * Nat.choose w k := by
    have h_eq : w + r + m - 1 = w + (r + m - 1) := by omega
    rw [h_eq, Nat.add_choose_eq]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => Nat.choose w i * Nat.choose (r + m - 1) j) (2 * m)]
    apply Finset.sum_congr rfl
    intro k _
    exact Nat.mul_comm _ _
  rw [h1, h2]
  push_cast
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- **Theorem 2.5 (Equations (2.21)–(2.22): Exact Polynomial Identity in `Polynomial ℚ`)**:
For every `m ≥ 1` and `r ∈ ℕ`, the linear-shift polynomial
`(centralFactorialPoly m).comp ((X + C r)^2)` in `Polynomial ℚ` equals its Vandermonde
binomial-polynomial expansion:
$$\mathcal{E}_m((X + r)^2) = \sum_{k=0}^{2m} \left(\binom{r+m}{2m-k} + \binom{r+m-1}{2m-k}\right) \binom{X}{k}.$$ -/
theorem theorem_2_5_vandermonde_poly_eq (m r : ℕ) (hm : 1 ≤ m) :
    (centralFactorialPoly m).comp ((X + C (r : ℚ)) ^ 2) =
      ∑ k ∈ Finset.range (2 * m + 1),
        C ((Nat.choose (r + m) (2 * m - k) : ℚ) + (Nat.choose (r + m - 1) (2 * m - k) : ℚ)) *
          binomPoly k := by
  apply Polynomial.funext
  intro x
  have h_diff_zero :
      (centralFactorialPoly m).comp ((X + C (r : ℚ)) ^ 2) -
        ∑ k ∈ Finset.range (2 * m + 1),
          C ((Nat.choose (r + m) (2 * m - k) : ℚ) + (Nat.choose (r + m - 1) (2 * m - k) : ℚ)) *
            binomPoly k = 0 := by
    by_contra h_ne
    have h_inf : (Set.range (Nat.cast : ℕ → ℚ)).Infinite :=
      Set.infinite_range_of_injective Nat.cast_injective
    apply h_inf
    apply Set.Finite.subset (Polynomial.finite_setOf_isRoot h_ne)
    rintro _ ⟨w, rfl⟩
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finset_sum, Polynomial.eval_mul]
    rw [eval_centralFactorialPoly, theorem_2_5_vandermonde_eval_nat m r w hm]
    simp_rw [eval_binomPoly_nat]
    ring
  have h_eq := sub_eq_zero.mp h_diff_zero
  rw [h_eq]

/-- **Theorem 2.5 (Equation (2.23): General Linear-Shift LCM Integrality)**:
For every `m, d ∈ ℕ` and every integer `r ∈ ℤ`, the Taylor coefficient `[w^d] \mathcal{E}_m((w + r)^2)`
satisfies
$$\operatorname{lcm}(1, 2, \dots, 2m)^d \, [w^d] \mathcal{E}_m((w + r)^2) \in \mathbb{Z}.$$ -/
theorem theorem_2_5_linear_shift_lcm_int (m d : ℕ) (r : ℤ) :
    ∃ z : ℤ,
      ((lcmUpTo (2 * m) : ℚ) ^ d) *
        ((centralFactorialPoly m).comp ((X + C (r : ℚ)) ^ 2)).coeff d = (z : ℚ) := by
  rcases eq_or_ne m 0 with rfl | hm0
  · unfold centralFactorialPoly
    simp only [↓reduceIte, Polynomial.one_comp]
    rcases eq_or_ne d 0 with rfl | hd0
    · refine ⟨1, ?_⟩; simp
    · refine ⟨0, ?_⟩; simp [Polynomial.coeff_one, if_neg hd0]
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have h_nat : ∀ rn : ℕ, ∃ z : ℤ,
        ((lcmUpTo (2 * m) : ℚ) ^ d) *
          ((centralFactorialPoly m).comp ((X + C (rn : ℚ)) ^ 2)).coeff d = (z : ℚ) := by
      intro rn
      rw [theorem_2_5_vandermonde_poly_eq m rn hm1]
      rw [Polynomial.finset_sum_coeff, Finset.mul_sum]
      have h_term : ∀ k ∈ Finset.range (2 * m + 1), ∃ zk : ℤ,
          ((lcmUpTo (2 * m) : ℚ) ^ d) *
            (C ((Nat.choose (rn + m) (2 * m - k) : ℚ) +
                (Nat.choose (rn + m - 1) (2 * m - k) : ℚ)) * binomPoly k).coeff d = (zk : ℚ) := by
        intro k hk
        rw [Polynomial.coeff_C_mul]
        obtain ⟨z_bin, hz_bin⟩ := binomPoly_coeff_lcm_int m k d (by
          have := Finset.mem_range.mp hk; omega)
        refine ⟨((Nat.choose (rn + m) (2 * m - k) : ℤ) +
                 (Nat.choose (rn + m - 1) (2 * m - k) : ℤ)) * z_bin, ?_⟩
        calc ((lcmUpTo (2 * m) : ℚ) ^ d) *
              (((Nat.choose (rn + m) (2 * m - k) : ℚ) +
                (Nat.choose (rn + m - 1) (2 * m - k) : ℚ)) * (binomPoly k).coeff d)
            = ((Nat.choose (rn + m) (2 * m - k) : ℚ) +
               (Nat.choose (rn + m - 1) (2 * m - k) : ℚ)) *
              (((lcmUpTo (2 * m) : ℚ) ^ d) * (binomPoly k).coeff d) := by ring
          _ = ((Nat.choose (rn + m) (2 * m - k) : ℚ) +
               (Nat.choose (rn + m - 1) (2 * m - k) : ℚ)) * (z_bin : ℚ) := by rw [hz_bin]
          _ = ((((Nat.choose (rn + m) (2 * m - k) : ℤ) +
                 (Nat.choose (rn + m - 1) (2 * m - k) : ℤ)) * z_bin : ℤ) : ℚ) := by push_cast; ring
      choose zk hzk using h_term
      refine ⟨∑ k ∈ Finset.range (2 * m + 1),
        if hk : k ∈ Finset.range (2 * m + 1) then zk k hk else 0, ?_⟩
      push_cast
      apply Finset.sum_congr rfl
      intro k hk
      rw [dif_pos hk]
      exact hzk k hk
    rcases Int.eq_nat_or_neg r with ⟨rn, rfl | rfl⟩
    · exact h_nat rn
    · obtain ⟨z_pos, hz_pos⟩ := h_nat rn
      have h_comp_neg :
          (centralFactorialPoly m).comp ((X + C ((- (rn : ℤ) : ℤ) : ℚ)) ^ 2) =
            ((centralFactorialPoly m).comp ((X + C (rn : ℚ)) ^ 2)).comp (-X) := by
        have h_inner :
            (X + C ((- (rn : ℤ) : ℤ) : ℚ)) ^ 2 =
              ((X + C (rn : ℚ)) ^ 2).comp (-X) := by
          simp only [Polynomial.pow_comp, Polynomial.add_comp, Polynomial.X_comp,
            Polynomial.C_comp, Int.cast_neg, Int.cast_natCast, Polynomial.C_neg]
          ring
        rw [h_inner, ← Polynomial.comp_assoc]
      have h_coeff_comp_neg : ∀ P : Polynomial ℚ,
          (P.comp (-X)).coeff d = (-1 : ℚ) ^ d * P.coeff d := by
        intro P
        induction P using Polynomial.induction_on' with
        | h_add p q ihp ihq =>
          rw [Polynomial.add_comp, Polynomial.coeff_add, Polynomial.coeff_add, ihp, ihq]
          ring
        | h_monomial n a =>
          simp only [Polynomial.monomial_comp, Polynomial.coeff_monomial]
          have h_neg_pow : (-X : Polynomial ℚ) ^ n = C ((-1 : ℚ) ^ n) * X ^ n := by
            have h_neg_X : (-X : Polynomial ℚ) = C (-1 : ℚ) * X := by
              ext k; simp
            rw [h_neg_X, mul_pow, ← Polynomial.C_pow]
          rw [h_neg_pow, ← mul_assoc, ← Polynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial,
              Polynomial.coeff_monomial]
          split_ifs with hnd
          · subst hnd; ring
          · ring
      rw [h_comp_neg, h_coeff_comp_neg]
      refine ⟨(-1 : ℤ) ^ d * z_pos, ?_⟩
      calc ((lcmUpTo (2 * m) : ℚ) ^ d) *
            ((-1 : ℚ) ^ d * ((centralFactorialPoly m).comp ((X + C (rn : ℚ)) ^ 2)).coeff d)
          = (-1 : ℚ) ^ d *
            (((lcmUpTo (2 * m) : ℚ) ^ d) *
              ((centralFactorialPoly m).comp ((X + C (rn : ℚ)) ^ 2)).coeff d) := by ring
        _ = (-1 : ℚ) ^ d * (z_pos : ℚ) := by rw [hz_pos]
        _ = (((-1 : ℤ) ^ d * z_pos : ℤ) : ℚ) := by push_cast; ring

/-- **Proposition 2.2(ii) (Equation (2.4): Taylor Coefficient LCM Integrality of `ℰ_m(u)`)**:
For every `m, q ∈ ℕ`, the Taylor coefficient `[u^q] \mathcal{E}_m(u)` satisfies
$$\operatorname{lcm}(1, 2, \dots, 2m)^{2q} \, [u^q] \mathcal{E}_m(u) \in \mathbb{Z}.$$ -/
theorem prop_2_2_ii_taylor_lcm_int (m q : ℕ) :
    ∃ z : ℤ, ((lcmUpTo (2 * m) : ℚ) ^ (2 * q)) * (centralFactorialPoly m).coeff q = (z : ℚ) := by
  have h_comp_sq : ∀ P : Polynomial ℚ, (P.comp (X ^ 2)).coeff (2 * q) = P.coeff q := by
    intro P
    induction P using Polynomial.induction_on' with
    | h_add p₁ p₂ ih₁ ih₂ =>
      rw [Polynomial.add_comp, Polynomial.coeff_add, Polynomial.coeff_add, ih₁, ih₂]
    | h_monomial n a =>
      rw [Polynomial.monomial_comp, ← pow_mul, Polynomial.C_mul_X_pow_eq_monomial,
          Polynomial.coeff_monomial, Polynomial.coeff_monomial]
      split_ifs with h1 h2
      · rfl
      · exfalso; apply h2; omega
      · exfalso; apply h1; omega
      · rfl
  have h_r0 := theorem_2_5_linear_shift_lcm_int m (2 * q) 0
  simp only [Int.cast_zero, map_zero, add_zero] at h_r0
  rw [h_comp_sq (centralFactorialPoly m)] at h_r0
  exact h_r0


/-!
## Theorem 2.6: Strict Total Positivity of `ℰ_r(x²)` via Lindström–Gessel–Viennot
-/

/-- The lower bidiagonal matrix entry `B_{x,y} := δ_{y,x} + δ_{y,x-1}` of Equation (2.25). -/
def bidiagonalEntryB (x y : ℕ) : ℚ :=
  (if y = x then 1 else 0) + (if y + 1 = x then 1 else 0)

/-- The binomial lattice-path matrix entry `C_{y,r} := \binom{y+r}{2r}` of Equation (2.25). -/
def latticePathEntryC (y r : ℕ) : ℚ :=
  (Nat.choose (y + r) (2 * r) : ℚ)

/-- **Theorem 2.6 (Equation (2.25): Finite Bidiagonal-Binomial Matrix Factorization)**:
For every integer `r ≥ 0`, `x ≥ 1`, and `x_M ≥ x`,
$$\mathcal{E}_r(x^2) = \frac{1}{1 + \delta_{r,0}} \left(\binom{x+r}{2r} + \binom{x+r-1}{2r}\right)
  = \frac{1}{1 + \delta_{r,0}} \sum_{y=0}^{x_M} B_{x,y} C_{y,r}.$$ -/
theorem theorem_2_6_matrix_factorization (r x xM : ℕ) (hx : 1 ≤ x) (hxM : x ≤ xM) :
    evalCentralFactorial r ((x : ℚ) ^ 2) =
      ((1 : ℚ) / ((1 + deltaZero r : ℕ) : ℚ)) *
        ∑ y ∈ Finset.range (xM + 1), bidiagonalEntryB x y * latticePathEntryC y r := by
  unfold bidiagonalEntryB latticePathEntryC
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  have hx_mem : x ∈ Finset.range (xM + 1) := Finset.mem_range.mpr (by omega)
  have hx1_mem : x - 1 ∈ Finset.range (xM + 1) := Finset.mem_range.mpr (by omega)
  have h_sum1 :
      (∑ y ∈ Finset.range (xM + 1), if y = x then (Nat.choose (y + r) (2 * r) : ℚ) else 0) =
        (Nat.choose (x + r) (2 * r) : ℚ) := by
    rw [Finset.sum_ite_eq' (Finset.range (xM + 1)) x (fun y => (Nat.choose (y + r) (2 * r) : ℚ)),
        if_pos hx_mem]
  have h_sum2 :
      (∑ y ∈ Finset.range (xM + 1), if y + 1 = x then (Nat.choose (y + r) (2 * r) : ℚ) else 0) =
        (Nat.choose (x + r - 1) (2 * r) : ℚ) := by
    have h_iff : ∀ y, (y + 1 = x) ↔ (y = x - 1) := fun y => by omega
    simp_rw [h_iff]
    rw [Finset.sum_ite_eq' (Finset.range (xM + 1)) (x - 1) (fun y => (Nat.choose (y + r) (2 * r) : ℚ)),
        if_pos hx1_mem, show x - 1 + r = x + r - 1 by omega]
  rw [h_sum1, h_sum2]
  rcases eq_or_ne r 0 with rfl | hr0
  · simp [deltaZero_zero]
    ring
  · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
    rw [prop_2_2_binomial_identity r x hr1, show deltaZero r = 0 from if_neg hr0]
    push_cast
    ring

/-- **Theorem 2.6 (Equation (2.27): Lower Unitriangularity and Unit Diagonal Minor of `B`)**:
For any strictly increasing sequence of positive integers `x₁ < x₂ < ... < x_M`,
the `M × M` submatrix `B_{x_i, x_ℓ}` satisfies `B_{x_i, x_ℓ} = 0` for all `i < ℓ`
(lower triangularity, repairing the manuscript's transposed `i > ℓ` comment) and
`B_{x_i, x_i} = 1`, so its determinant is `1 > 0`. -/
theorem theorem_2_6_unit_diag_B {M : ℕ} (x : Fin M → ℕ) (hx_mono : StrictMono x) :
    let B_sub : Matrix (Fin M) (Fin M) ℚ := fun i l => bidiagonalEntryB (x i) (x l)
    B_sub.BlockTriangular OrderDual.toDual ∧ B_sub.det = 1 := by
  intro B_sub
  have h_tri : B_sub.BlockTriangular OrderDual.toDual := by
    intro i l hil
    have h_lt : x i < x l := hx_mono hil
    change bidiagonalEntryB (x i) (x l) = 0
    unfold bidiagonalEntryB
    have h1 : x l ≠ x i := ne_of_gt h_lt
    have h2 : x l + 1 ≠ x i := by omega
    rw [if_neg h1, if_neg h2, add_zero]
  have h_diag : ∀ i : Fin M, B_sub i i = 1 := by
    intro i
    change bidiagonalEntryB (x i) (x i) = 1
    unfold bidiagonalEntryB
    rw [if_pos rfl, if_neg (by omega : x i + 1 ≠ x i), add_zero]
  refine ⟨h_tri, ?_⟩
  rw [Matrix.det_of_lowerTriangular B_sub h_tri]
  simp [h_diag]

/-- **Theorem 2.6 (Equation (2.28): Planar Lattice-Path Non-Zero Diagonal Construction)**:
Whenever `0 ≤ r₁ < ... < r_M ≤ y₁ < ... < y_M`, for every `1 ≤ j ≤ M` we have `r_j ≤ y_j`,
so the diagonal binomial entry `C_{y_j, r_j} = \binom{y_j + r_j}{2 r_j}` is at least `1 > 0`. -/
theorem theorem_2_6_lattice_path_diag_pos {M : ℕ} (r y : Fin M → ℕ)
    (_hr_mono : StrictMono r) (_hy_mono : StrictMono y)
    (h_sep : ∀ i j : Fin M, r i ≤ y j) (j : Fin M) :
    1 ≤ Nat.choose (y j + r j) (2 * r j) := by
  have hr_le_y : r j ≤ y j := h_sep j j
  exact Nat.choose_pos (by omega : 2 * r j ≤ y j + r j)

/-- General Newton interpolation product `∏_{t=0}^{r-1} (u - a_t)`. -/
def newtonProd (a : ℕ → ℚ) (r : ℕ) (u : ℚ) : ℚ :=
  ∏ t ∈ Finset.range r, (u - a t)

@[simp]
theorem newtonProd_zero (a : ℕ → ℚ) (u : ℚ) : newtonProd a 0 u = 1 := by
  unfold newtonProd; simp

theorem newtonProd_succ (a : ℕ → ℚ) (r : ℕ) (u : ℚ) :
    newtonProd a (r + 1) u = newtonProd a r u * (u - a r) := by
  unfold newtonProd
  exact Finset.prod_range_succ _ r

theorem newtonProd_pos (a : ℕ → ℚ) (r : ℕ) (u : ℚ) (h : ∀ t < r, a t < u) :
    0 < newtonProd a r u := by
  unfold newtonProd
  apply Finset.prod_pos
  intro t ht
  exact sub_pos.mpr (h t (Finset.mem_range.mp ht))

/-- Single-step difference identity for normalized Newton products:
$$\frac{N_{k+1}(u)}{N_{k+1}(u_0)} - \frac{N_k(u)}{N_k(u_0)}
  = (u - u_0) \frac{N_k(u)}{N_{k+1}(u_0)}.$$ -/
theorem normNewton_step_diff (a : ℕ → ℚ) (u₀ u : ℚ) (k : ℕ)
    (hk : ∀ t < k + 1, a t < u₀) :
    newtonProd a (k + 1) u / newtonProd a (k + 1) u₀ -
      newtonProd a k u / newtonProd a k u₀ =
        (u - u₀) * (newtonProd a k u / newtonProd a (k + 1) u₀) := by
  have hw_k : newtonProd a k u₀ ≠ 0 :=
    ne_of_gt (newtonProd_pos a k u₀ (fun t ht => hk t (by omega)))
  have h_ak : u₀ - a k ≠ 0 := ne_of_gt (sub_pos.mpr (hk k (by omega)))
  rw [newtonProd_succ a k u, newtonProd_succ a k u₀]
  field_simp [hw_k, h_ak]
  ring

/-- Telescoping difference identity for normalized Newton products over `k ∈ [r₁, r₂)`:
$$\frac{N_{r_2}(u)}{N_{r_2}(u_0)} - \frac{N_{r_1}(u)}{N_{r_1}(u_0)}
  = (u - u_0) \sum_{k = r_1}^{r_2 - 1} \frac{N_k(u)}{N_{k+1}(u_0)}.$$ -/
theorem normNewton_telescoping (a : ℕ → ℚ) (u₀ u : ℚ) (r₁ r₂ : ℕ)
    (hr : r₁ ≤ r₂) (h_pos : ∀ t < r₂, a t < u₀) :
    newtonProd a r₂ u / newtonProd a r₂ u₀ -
      newtonProd a r₁ u / newtonProd a r₁ u₀ =
        (u - u₀) * ∑ k ∈ Finset.Ico r₁ r₂, (newtonProd a k u / newtonProd a (k + 1) u₀) := by
  induction r₂ with
  | zero =>
    have hr1 : r₁ = 0 := by omega
    subst hr1
    simp
  | succ r₂ ih =>
    rcases eq_or_lt_of_le hr with rfl | hlt
    · simp
    · have hr_le : r₁ ≤ r₂ := Nat.lt_succ_iff.mp hlt
      rw [Finset.sum_Ico_succ_top hr_le, mul_add,
          ← ih hr_le (fun t ht => h_pos t (by omega)),
          ← normNewton_step_diff a u₀ u r₂ h_pos]
      ring

/-- Upper-unitriangular adjacent-column-difference matrix used to eliminate the first row
of a normalized Newton interpolation matrix. -/
def adjDiffMatrix (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ :=
  fun l k =>
    Fin.cases (if l = 0 then 1 else 0)
      (fun j => (if l = j.succ then 1 else 0) - (if l = j.castSucc then 1 else 0)) k

theorem adjDiffMatrix_det (m : ℕ) : (adjDiffMatrix m).det = 1 := by
  have h_tri : (adjDiffMatrix m).BlockTriangular id := by
    intro l k hkl
    change adjDiffMatrix m l k = 0
    unfold adjDiffMatrix
    cases k using Fin.cases with
    | zero =>
      have hl0 : l ≠ 0 := ne_of_gt hkl
      simp [hl0]
    | succ j =>
      have hl1 : l ≠ j.succ := ne_of_gt hkl
      have hl2 : l ≠ j.castSucc := ne_of_gt (lt_trans (Fin.castSucc_lt_succ j) hkl)
      simp [hl1, hl2]
  have h_diag : ∀ k : Fin (m + 1), adjDiffMatrix m k k = 1 := by
    intro k
    unfold adjDiffMatrix
    cases k using Fin.cases with
    | zero => simp
    | succ j =>
      have h_ne : j.succ ≠ j.castSucc := ne_of_gt (Fin.castSucc_lt_succ j)
      simp [h_ne]
  rw [Matrix.det_of_upperTriangular h_tri]
  simp [h_diag]

/-- If every entry in row `0` of an `(m+1) × (m+1)` matrix `N` equals `1`, then `det N` equals
the `m × m` determinant of adjacent column differences on rows `1, ..., m`. -/
theorem det_first_row_ones_eq_det_diff {m : ℕ} (N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (h_row0 : ∀ j : Fin (m + 1), N 0 j = 1) :
    N.det = (Matrix.of (fun i j : Fin m => N i.succ j.succ - N i.succ j.castSucc)).det := by
  have h_mul_det : (N * adjDiffMatrix m).det = N.det := by
    rw [Matrix.det_mul, adjDiffMatrix_det, mul_one]
  rw [← h_mul_det]
  have h_col0 : ∀ i : Fin (m + 1), (N * adjDiffMatrix m) i 0 = N i 0 := by
    intro i
    simp [Matrix.mul_apply, adjDiffMatrix]
  have h_col_succ : ∀ (i : Fin (m + 1)) (j : Fin m),
      (N * adjDiffMatrix m) i j.succ = N i j.succ - N i j.castSucc := by
    intro i j
    simp [Matrix.mul_apply, adjDiffMatrix, mul_sub, Finset.sum_sub_distrib]
  rw [Matrix.det_succ_row_zero (N * adjDiffMatrix m), Fin.sum_univ_succ]
  have h_zero_term :
      (-1 : ℚ) ^ ((0 : Fin (m + 1)) : ℕ) * (N * adjDiffMatrix m) 0 0 *
        ((N * adjDiffMatrix m).submatrix Fin.succ (0 : Fin (m + 1)).succAbove).det =
        (Matrix.of (fun i j : Fin m => N i.succ j.succ - N i.succ j.castSucc)).det := by
    rw [Fin.val_zero, h_col0 0, h_row0 0, pow_zero, one_mul, one_mul]
    congr 1
    ext i j
    simp [Matrix.submatrix_apply, Fin.succAbove_zero, h_col_succ]
  have h_rest_zero :
      (∑ j : Fin m, (-1 : ℚ) ^ (j.succ : ℕ) * (N * adjDiffMatrix m) 0 j.succ *
        ((N * adjDiffMatrix m).submatrix Fin.succ j.succ.succAbove).det) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [h_col_succ 0 j, h_row0 j.succ, h_row0 j.castSucc, sub_self, mul_zero, zero_mul]
  rw [h_zero_term, h_rest_zero, add_zero]

/-- Helper lemma: multilinearity of `Matrix.det` with respect to a `Finset.sum` in column `j₀`. -/
theorem det_updateCol_finset_sum {m : ℕ} (A : Matrix (Fin m) (Fin m) ℚ) (j₀ : Fin m)
    (s : Finset ℕ) (g : ℕ → Fin m → ℚ) :
    (A.updateCol j₀ (fun i => ∑ t ∈ s, g t i)).det =
      ∑ t ∈ s, (A.updateCol j₀ (g t)).det := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Matrix.det_eq_zero_of_column_eq_zero j₀ (fun i => by simp [Matrix.updateCol_self])
  | @insert a s ha ih =>
    have h_add : (fun i : Fin m => ∑ t ∈ insert a s, g t i) =
        g a + (fun i : Fin m => ∑ t ∈ s, g t i) := by
      ext i
      simp [Finset.sum_insert ha, Pi.add_apply]
    rw [h_add, Matrix.det_updateCol_add, Finset.sum_insert ha, ih]

/-- Multilinearity positivity lemma: if each column `j` of an `m × m` matrix is a sum over a
nonempty finite set `S j`, and every choice tuple `k` with `∀ j, k j ∈ S j` yields a matrix
with strictly positive determinant, then the sum matrix also has strictly positive determinant. -/
theorem det_sum_columns_pos {m : ℕ} (S : Fin m → Finset ℕ) (hS : ∀ j, (S j).Nonempty)
    (v : ℕ → Fin m → ℚ)
    (h_pos : ∀ k : Fin m → ℕ, (∀ j, k j ∈ S j) →
      0 < (Matrix.of (fun i j : Fin m => v (k j) i)).det) :
    0 < (Matrix.of (fun i j : Fin m => ∑ t ∈ S j, v t i)).det := by
  let partMat (n : ℕ) (k : Fin m → ℕ) : Matrix (Fin m) (Fin m) ℚ :=
    Matrix.of (fun i j : Fin m => if j.val < n then ∑ t ∈ S j, v t i else v (k j) i)
  have h_ind : ∀ n ≤ m, ∀ k : Fin m → ℕ, (∀ j, k j ∈ S j) → 0 < (partMat n k).det := by
    intro n
    induction n with
    | zero =>
      intro _ k hk
      have h_eq : partMat 0 k = Matrix.of (fun i j : Fin m => v (k j) i) := by
        ext i j; simp [partMat]
      rw [h_eq]
      exact h_pos k hk
    | succ n ih =>
      intro hn k hk
      let j₀ : Fin m := ⟨n, hn⟩
      have h_upd_sum :
          partMat (n + 1) k =
            (partMat n k).updateCol j₀ (fun i => ∑ t ∈ S j₀, v t i) := by
        ext i j
        by_cases hj : j = j₀
        · subst hj
          rw [Matrix.updateCol_self]
          simp [partMat, j₀]
        · rw [Matrix.updateCol_ne hj]
          have hj_val : j.val ≠ n := fun h => hj (Fin.ext h)
          have h_iff : (j.val < n + 1) ↔ (j.val < n) := by omega
          simp [partMat, h_iff]
      have h_upd_single : ∀ t : ℕ,
          (partMat n k).updateCol j₀ (v t) =
            partMat n (Function.update k j₀ t) := by
        intro t
        ext i j
        by_cases hj : j = j₀
        · subst hj
          rw [Matrix.updateCol_self]
          simp [partMat, j₀]
        · rw [Matrix.updateCol_ne hj]
          simp [partMat, hj]
      rw [h_upd_sum, det_updateCol_finset_sum]
      apply Finset.sum_pos
      · intro t ht
        rw [h_upd_single t]
        apply ih (by omega) (Function.update k j₀ t)
        intro j
        by_cases hj : j = j₀
        · subst hj; simpa using ht
        · simpa [hj] using hk j
      · exact hS j₀
  have h_k0 : ∃ k : Fin m → ℕ, ∀ j, k j ∈ S j :=
    ⟨fun j => (hS j).choose, fun j => (hS j).choose_spec⟩
  rcases h_k0 with ⟨k₀, hk₀⟩
  have h_final := h_ind m le_rfl k₀ hk₀
  have h_mat_eq : partMat m k₀ = Matrix.of (fun i j : Fin m => ∑ t ∈ S j, v t i) := by
    ext i j
    simp [partMat, j.isLt]
  rwa [h_mat_eq] at h_final

/-- **Universal Newton-Basis Strict Total Positivity Theorem**:
For every dimension `M ≥ 0`, every node sequence `a : ℕ → ℚ`, every strictly increasing degree
sequence `r : Fin M → ℕ`, and every strictly increasing evaluation sequence `u : Fin M → ℚ`
such that `a t < u i` for all `t < r j`, the `M × M` Newton interpolation matrix
`M_{i,j} = ∏_{t=0}^{r_j - 1} (u_i - a_t)` has strictly positive determinant. -/
theorem det_newtonProd_pos :
    ∀ (M : ℕ) (a : ℕ → ℚ) (r : Fin M → ℕ) (_hr : StrictMono r)
      (u : Fin M → ℚ) (_hu : StrictMono u)
      (_h_sep : ∀ (i j : Fin M) (t : ℕ), t < r j → a t < u i),
      0 < (Matrix.of (fun i j : Fin M => newtonProd a (r j) (u i))).det
  | 0, _, _, _, _, _, _ => by
    simp [Matrix.det_isEmpty]
  | m + 1, a, r, hr, u, hu, h_sep => by
    let w : ℕ → ℚ := fun k => newtonProd a k (u 0)
    have hw_pos : ∀ k ≤ r (Fin.last m), 0 < w k := by
      intro k hk
      apply newtonProd_pos a k (u 0)
      intro t ht
      exact h_sep 0 (Fin.last m) t (lt_of_lt_of_le ht hk)
    have hw_r_pos : ∀ j : Fin (m + 1), 0 < w (r j) := by
      intro j
      exact hw_pos (r j) (hr.monotone (Fin.le_last j))
    let N : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ :=
      Matrix.of (fun i j => newtonProd a (r j) (u i) / w (r j))
    have h_factor_cols :
        Matrix.of (fun i j : Fin (m + 1) => newtonProd a (r j) (u i)) =
          Matrix.of (fun i j : Fin (m + 1) => w (r j) * N i j) := by
      ext i j
      simp only [N, Matrix.of_apply]
      exact (mul_div_cancel₀ _ (ne_of_gt (hw_r_pos j))).symm
    rw [h_factor_cols, Matrix.det_mul_row]
    apply mul_pos
    · exact Finset.prod_pos (fun j _ => hw_r_pos j)
    · have hN_row0 : ∀ j : Fin (m + 1), N 0 j = 1 := by
        intro j
        simp only [N, Matrix.of_apply, w]
        exact div_self (ne_of_gt (hw_r_pos j))
      rw [det_first_row_ones_eq_det_diff N hN_row0]
      have h_tele :
          Matrix.of (fun i j : Fin m => N i.succ j.succ - N i.succ j.castSucc) =
            Matrix.of (fun i j : Fin m =>
              (u i.succ - u 0) *
                ∑ k ∈ Finset.Ico (r j.castSucc) (r j.succ),
                  (newtonProd a k (u i.succ) / w (k + 1))) := by
        ext i j
        simp only [N, Matrix.of_apply, w]
        exact normNewton_telescoping a (u 0) (u i.succ) (r j.castSucc) (r j.succ)
          (le_of_lt (hr (Fin.castSucc_lt_succ j)))
          (fun t ht => h_sep 0 j.succ t ht)
      rw [h_tele, Matrix.det_mul_column]
      apply mul_pos
      · apply Finset.prod_pos
        intro i _
        exact sub_pos.mpr (hu (Fin.succ_pos i))
      · let S : Fin m → Finset ℕ := fun j => Finset.Ico (r j.castSucc) (r j.succ)
        have hS : ∀ j : Fin m, (S j).Nonempty := by
          intro j
          exact Finset.nonempty_Ico.mpr (hr (Fin.castSucc_lt_succ j))
        apply det_sum_columns_pos S hS (fun k i => newtonProd a k (u i.succ) / w (k + 1))
        intro k hk
        have hk_mono : StrictMono k := by
          intro j₁ j₂ hj
          have h1 : k j₁ < r j₁.succ := (Finset.mem_Ico.mp (hk j₁)).2
          have h2 : r j₁.succ ≤ r j₂.castSucc := hr.monotone (Fin.succ_le_castSucc_iff.mpr hj)
          have h3 : r j₂.castSucc ≤ k j₂ := (Finset.mem_Ico.mp (hk j₂)).1
          omega
        have h_wk_pos : ∀ j : Fin m, 0 < 1 / w (k j + 1) := by
          intro j
          have hk_lt : k j < r j.succ := (Finset.mem_Ico.mp (hk j)).2
          have hr_le : r j.succ ≤ r (Fin.last m) := hr.monotone (Fin.le_last j.succ)
          exact div_pos one_pos (hw_pos (k j + 1) (by omega))
        have h_col_scale :
            Matrix.of (fun i j : Fin m => newtonProd a (k j) (u i.succ) / w (k j + 1)) =
              Matrix.of (fun i j : Fin m => (1 / w (k j + 1)) * newtonProd a (k j) (u i.succ)) := by
          ext i j; simp [div_eq_mul_inv, mul_comm]
        rw [h_col_scale, Matrix.det_mul_row]
        apply mul_pos
        · exact Finset.prod_pos (fun j _ => h_wk_pos j)
        · exact det_newtonProd_pos m a k hk_mono (fun i => u i.succ)
            (fun i₁ i₂ hi => hu (Fin.succ_lt_succ_iff.mpr hi))
            (fun i j t ht => by
              have hk_lt : k j < r j.succ := (Finset.mem_Ico.mp (hk j)).2
              exact h_sep i.succ j.succ t (lt_trans ht hk_lt))

/-- **Theorem 2.6 (Equation (2.24): Strict Total Positivity of `ℰ_r(x²)` for All `M ≥ 1`)**:
For every `M ≥ 0` and any strictly increasing sequences of non-negative integers
`0 ≤ r₁ < r₂ < ... < r_M < x₁ < x₂ < ... < x_M`, the `M × M` generalized Vandermonde matrix
`V_{i,j} = ℰ_{r_j}(x_i²)` has strictly positive determinant:
$$\det_{1 \le i,j \le M} \left(\mathcal{E}_{r_j}(x_i^2)\right) > 0.$$ -/
theorem theorem_2_6_strict_total_positivity {M : ℕ} (r x : Fin M → ℕ)
    (hr_mono : StrictMono r) (hx_mono : StrictMono x)
    (h_sep : ∀ i j : Fin M, r j < x i) :
    0 < (Matrix.of (fun i j : Fin M => evalCentralFactorial (r j) ((x i : ℚ) ^ 2))).det := by
  let c : ℕ → ℚ := fun k => if k = 0 then 1 else (2 : ℚ) / ((2 * k).factorial : ℚ)
  have hc_pos : ∀ k : ℕ, 0 < c k := by
    intro k
    dsimp [c]
    split_ifs
    · exact one_pos
    · exact div_pos two_pos (by exact_mod_cast Nat.factorial_pos (2 * k))
  have h_eq :
      Matrix.of (fun i j : Fin M => evalCentralFactorial (r j) ((x i : ℚ) ^ 2)) =
        Matrix.of (fun i j : Fin M =>
          c (r j) * newtonProd (fun t => (t : ℚ) ^ 2) (r j) ((x i : ℚ) ^ 2)) := by
    ext i j
    simp only [Matrix.of_apply, evalCentralFactorial, newtonProd, c]
    split_ifs with h
    · rw [h]; simp
    · rfl
  rw [h_eq, Matrix.det_mul_row]
  apply mul_pos
  · exact Finset.prod_pos (fun j _ => hc_pos (r j))
  · apply det_newtonProd_pos M (fun t => (t : ℚ) ^ 2) r hr_mono (fun i => (x i : ℚ) ^ 2)
    · intro i₁ i₂ hi
      dsimp only
      have h_lt : (x i₁ : ℚ) < (x i₂ : ℚ) := by exact_mod_cast hx_mono hi
      have h_nonneg : (0 : ℚ) ≤ (x i₁ : ℚ) := Nat.cast_nonneg _
      nlinarith
    · intro i j t ht
      dsimp only
      have h_tx : t < x i := lt_trans ht (h_sep i j)
      have h_lt : (t : ℚ) < (x i : ℚ) := by exact_mod_cast h_tx
      have h_nonneg : (0 : ℚ) ≤ (t : ℚ) := Nat.cast_nonneg _
      nlinarith

/-- Helper identity expressing the binomial lattice-path entry `\binom{y+r}{2r}` as a Newton
interpolation product in `u = y(y+1)` with nodes `a_t = t(t+1)`:
$$\prod_{t=0}^{r-1} \left(y(y+1) - t(t+1)\right) = (2r)! \binom{y+r}{2r}.$$ -/
theorem newtonProd_pronic_eq_factorial_mul_choose (r y : ℕ) :
    newtonProd (fun t => (t : ℚ) * ((t : ℚ) + 1)) r ((y : ℚ) * ((y : ℚ) + 1)) =
      ((2 * r).factorial : ℚ) * (Nat.choose (y + r) (2 * r) : ℚ) := by
  induction r with
  | zero =>
    simp
  | succ r ih =>
    rw [newtonProd_succ, ih]
    rcases lt_or_ge y (r + 1) with hlt | hge
    · have h_zero : Nat.choose (y + (r + 1)) (2 * (r + 1)) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      rw [h_zero, Nat.cast_zero, mul_zero]
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hlt) with rfl | hlt'
      · ring
      · have h_zero' : Nat.choose (y + r) (2 * r) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        rw [h_zero', Nat.cast_zero, mul_zero, zero_mul]
    · have h_step2 :
          (2 * r + 2) * Nat.choose (y + r + 1) (2 * r + 2) =
            Nat.choose (y + r + 1) (2 * r + 1) * (y - r) := by
        have h := Nat.choose_succ_right_eq (y + r + 1) (2 * r + 1)
        have h_sub : y + r + 1 - (2 * r + 1) = y - r := by omega
        rw [h_sub] at h
        linarith [h]
      have h_succ_choose := Nat.succ_mul_choose_eq (y + r) (2 * r)
      have h_comb :
          (2 * r + 2) * (2 * r + 1) * Nat.choose (y + r + 1) (2 * r + 2) =
            (y + r + 1) * (y - r) * Nat.choose (y + r) (2 * r) := by
        calc (2 * r + 2) * (2 * r + 1) * Nat.choose (y + r + 1) (2 * r + 2)
            = (2 * r + 1) * ((2 * r + 2) * Nat.choose (y + r + 1) (2 * r + 2)) := by ring
          _ = (2 * r + 1) * (Nat.choose (y + r + 1) (2 * r + 1) * (y - r)) := by rw [h_step2]
          _ = (Nat.choose (y + r + 1) (2 * r + 1) * (2 * r + 1)) * (y - r) := by ring
          _ = ((y + r + 1) * Nat.choose (y + r) (2 * r)) * (y - r) := by rw [← h_succ_choose]
          _ = (y + r + 1) * (y - r) * Nat.choose (y + r) (2 * r) := by ring
      have h_comb_q :
          ((2 * r + 2 : ℕ) : ℚ) * ((2 * r + 1 : ℕ) : ℚ) *
            (Nat.choose (y + (r + 1)) (2 * (r + 1)) : ℚ) =
            ((y + r + 1 : ℕ) : ℚ) * ((y - r : ℕ) : ℚ) * (Nat.choose (y + r) (2 * r) : ℚ) := by
        have h_eq_idx : y + (r + 1) = y + r + 1 := by omega
        have h_eq_k : 2 * (r + 1) = 2 * r + 2 := by omega
        rw [h_eq_idx, h_eq_k]
        exact_mod_cast h_comb
      have h_sub_cast : ((y - r : ℕ) : ℚ) = (y : ℚ) - (r : ℚ) := Nat.cast_sub (by omega)
      have h_add_cast : ((y + r + 1 : ℕ) : ℚ) = (y : ℚ) + (r : ℚ) + 1 := by push_cast; rfl
      rw [h_sub_cast, h_add_cast] at h_comb_q
      have h_fac :
          ((2 * (r + 1)).factorial : ℚ) =
            ((2 * r + 2 : ℕ) : ℚ) * ((2 * r + 1 : ℕ) : ℚ) * ((2 * r).factorial : ℚ) := by
        rw [show 2 * (r + 1) = 2 * r + 2 by omega, Nat.factorial_succ (2 * r + 1),
            Nat.factorial_succ (2 * r)]
        push_cast; ring
      rw [h_fac]
      calc ((2 * r).factorial : ℚ) * (Nat.choose (y + r) (2 * r) : ℚ) *
            ((y : ℚ) * ((y : ℚ) + 1) - (r : ℚ) * ((r : ℚ) + 1))
          = ((2 * r).factorial : ℚ) *
              (((y : ℚ) + (r : ℚ) + 1) * ((y : ℚ) - (r : ℚ)) *
                (Nat.choose (y + r) (2 * r) : ℚ)) := by ring
        _ = ((2 * r).factorial : ℚ) *
              (((2 * r + 2 : ℕ) : ℚ) * ((2 * r + 1 : ℕ) : ℚ) *
                (Nat.choose (y + (r + 1)) (2 * (r + 1)) : ℚ)) := by rw [← h_comb_q]
        _ = ((2 * r + 2 : ℕ) : ℚ) * ((2 * r + 1 : ℕ) : ℚ) * ((2 * r).factorial : ℚ) *
              (Nat.choose (y + (r + 1)) (2 * (r + 1)) : ℚ) := by ring

/-- **Theorem 2.6 (Equation (2.28): Strict Positivity of All Lattice-Path Minors of `C`)**:
For every `M ≥ 0` and any strictly increasing sequences of non-negative integers
`0 ≤ r₁ < ... < r_M ≤ y₁ < ... < y_M`, the `M × M` binomial minor
`\det_{1 \le i,j \le M} \binom{y_i + r_j}{2 r_j}` is strictly positive (and as an integer, `≥ 1`). -/
theorem theorem_2_6_lattice_path_minor_pos {M : ℕ} (r y : Fin M → ℕ)
    (hr_mono : StrictMono r) (hy_mono : StrictMono y)
    (h_sep : ∀ i j : Fin M, r j ≤ y i) :
    0 < (Matrix.of (fun i j : Fin M => latticePathEntryC (y i) (r j))).det := by
  have h_eq :
      Matrix.of (fun i j : Fin M => latticePathEntryC (y i) (r j)) =
        Matrix.of (fun i j : Fin M =>
          ((1 : ℚ) / ((2 * r j).factorial : ℚ)) *
            newtonProd (fun t => (t : ℚ) * ((t : ℚ) + 1)) (r j)
              ((y i : ℚ) * ((y i : ℚ) + 1))) := by
    ext i j
    simp only [Matrix.of_apply, latticePathEntryC]
    rw [newtonProd_pronic_eq_factorial_mul_choose (r j) (y i)]
    have h_fac_ne : ((2 * r j).factorial : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * r j)
    field_simp [h_fac_ne]
  rw [h_eq, Matrix.det_mul_row]
  apply mul_pos
  · apply Finset.prod_pos
    intro j _
    exact div_pos one_pos (by exact_mod_cast Nat.factorial_pos (2 * r j))
  · apply det_newtonProd_pos M (fun t => (t : ℚ) * ((t : ℚ) + 1)) r hr_mono
      (fun i => (y i : ℚ) * ((y i : ℚ) + 1))
    · intro i₁ i₂ hi
      change (y i₁ : ℚ) * ((y i₁ : ℚ) + 1) < (y i₂ : ℚ) * ((y i₂ : ℚ) + 1)
      have h_lt : (y i₁ : ℚ) < (y i₂ : ℚ) := by exact_mod_cast hy_mono hi
      have h_nonneg : (0 : ℚ) ≤ (y i₁ : ℚ) := Nat.cast_nonneg _
      nlinarith
    · intro i j t ht
      have h_ty : t < y i := lt_of_lt_of_le ht (h_sep i j)
      have h_lt : (t : ℚ) < (y i : ℚ) := by exact_mod_cast h_ty
      have h_nonneg : (0 : ℚ) ≤ (t : ℚ) := Nat.cast_nonneg _
      nlinarith

/-- **Theorem 2.6 (Equation (2.24) Benchmark Verification)**:
Direct verification of strict total positivity `det_{1 ≤ i,j ≤ M} (ℰ_{r_j}(x_i²)) > 0`
on the benchmark sequences `r = (0, 2, 3)` and `x = (6, 8, 9)` from Suite 1. -/
theorem theorem_2_6_strict_total_positivity_benchmark :
    let r : Fin 3 → ℕ := ![0, 2, 3]
    let x : Fin 3 → ℕ := ![6, 8, 9]
    let V : Matrix (Fin 3) (Fin 3) ℚ :=
      fun i j => evalCentralFactorial (r j) ((x i : ℚ) ^ 2)
    0 < V.det := by
  intro r x V
  rw [Matrix.det_fin_three]
  dsimp [V, r, x, evalCentralFactorial]
  norm_num [Finset.prod_range_succ, Nat.factorial]

end OddZetaFormalization

