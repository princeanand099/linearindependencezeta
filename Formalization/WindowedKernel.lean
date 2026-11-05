import Formalization.ZetaPreliminaries
import Formalization.CentralFactorial

/-!
# Section 3: The Windowed Multi-Pole Kernel, Reflection Parity, and Positive-Series Representation

This module formalizes Section 3 of Prince Anand,
*"All Odd Zeta Values Are Linearly Independent Over ℚ"*:
- **Definition 3.1**: Windowed multi-pole rational kernel `ℱ_{2n+1,2}^{odd,[A₀,A]}(z; P)` (3.2),
  degree bound `2 deg_u P ≤ 4AK + 2(2n-1)A₀K - 2` (3.1), pole multiplicity `L_k ∈ {2, 2n+1}` (3.3),
  partial fraction coefficients `A_{t,k}(P)` and pole sums `S_t(P) = ∑_{k=0}^{2AK} A_{t,k}(P)` (3.4).
- **Lemma 3.2**: Local Laurent expansion of the smooth kernel factor `g_k(w)` (3.5), closed-form
  leading coefficient `g_{k,0} ≠ 0` at inner poles `|r| ≤ A₀K` and outer poles `A₀K < |r| ≤ AK` (3.6),
  Newton recurrence `g_{k,q} = (1/q) ∑_{d=1}^q p_{k,d} g_{k,q-d}` (3.7), and finite convolution
  representation of `A_{t,k}(P)` (3.8).
- **Theorem 3.3**:
  - (i) Odd reflection symmetry `ℱ(-2AK - z; P) = -ℱ(z; P)`, Laurent coefficient reflection parity
    `A_{t, 2AK-k}(P) = (-1)^{t-1} A_{t,k}(P)` (3.9), and vanishing of all even-weight pole sums
    `S_{2j}(P) = 0` (`1 ≤ j ≤ n`) and simple-pole residue sum `S_1(P) = 0` (3.10).
  - (ii) Vanishing of outer poles `A_{t,k}(P) = 0` for `3 ≤ t ≤ 2n+1` and `A₀K < |k-AK| ≤ AK` (3.11),
    giving inner-window support compression `S_{2j+1}(P) = ∑_{|k-AK| ≤ A₀K} A_{2j+1,k}(P)` (3.12).
- **Theorem 3.4**: Rational harmonic remainder `ℛ_0(P)` (3.14), strictly positive discrete weights
  `W_K(ν) > 0` for `ν ≥ 1` (3.15), and positive-series moment identity (3.16).
- **Theorem 3.5**: Reflection-symmetric rising-factorial zero barrier `Ω_B(u)^{M_0}` (3.20)–(3.22).
-/

namespace OddZetaFormalization

open scoped BigOperators

/-- **Definition 3.1 (Equation (3.1))**: The kernel degree bound condition
`2 deg_u P ≤ 4AK + 2(2n - 1)A₀K - 2` guaranteeing `deg_z ℱ(z; P) ≤ -(2n + 3) ≤ -5`. -/
def satisfiesKernelDegreeBound (n A0K AK degP : ℕ) : Prop :=
  2 * degP + 2 ≤ 4 * AK + 2 * (2 * n - 1) * A0K

/-- **Definition 3.1 (Equation (3.3))**: Pole multiplicity `L_k` of `ℱ_{2n+1,2}^{odd,[A₀,A]}(z; 1)`
at `z = -k` (`0 ≤ k ≤ 2AK`):
$$L_k := \begin{cases} 2n + 1, & |k - AK| \le A_0 K, \\ 2, & A_0 K < |k - AK| \le AK. \end{cases}$$ -/
def poleMultiplicity (n A0K AK k : ℕ) : ℕ :=
  if ((k : ℤ) - (AK : ℤ)).natAbs ≤ A0K then 2 * n + 1 else 2

/-- Symmetry of the pole multiplicity `L_{2AK - k} = L_k` under reflection `k ↦ 2AK - k`. -/
theorem poleMultiplicity_reflect (n A0K AK k : ℕ) (hk : k ≤ 2 * AK) :
    poleMultiplicity n A0K AK (2 * AK - k) = poleMultiplicity n A0K AK k := by
  unfold poleMultiplicity
  have h_abs : (((2 * AK - k : ℕ) : ℤ) - (AK : ℤ)).natAbs = ((k : ℤ) - (AK : ℤ)).natAbs := by
    have h_cast : ((2 * AK - k : ℕ) : ℤ) = 2 * (AK : ℤ) - (k : ℤ) := Int.ofNat_sub hk
    rw [h_cast, show 2 * (AK : ℤ) - (k : ℤ) - (AK : ℤ) = -((k : ℤ) - (AK : ℤ)) by ring,
        Int.natAbs_neg]
  rw [h_abs]

/-- At every outer pole `A₀K < |k - AK| ≤ AK`, `L_k = 2 < 3`. -/
theorem poleMultiplicity_outer_eq_two (n A0K AK k : ℕ)
    (h_out : A0K < ((k : ℤ) - (AK : ℤ)).natAbs) :
    poleMultiplicity n A0K AK k = 2 := by
  unfold poleMultiplicity
  rw [if_neg (not_le.mpr h_out)]

/-- At every inner pole `|k - AK| ≤ A₀K`, `L_k = 2n + 1`. -/
theorem poleMultiplicity_inner_eq (n A0K AK k : ℕ)
    (h_in : ((k : ℤ) - (AK : ℤ)).natAbs ≤ A0K) :
    poleMultiplicity n A0K AK k = 2 * n + 1 := by
  unfold poleMultiplicity
  rw [if_pos h_in]

/-- **Definition 3.1 (Equation (3.2))**: The windowed multi-pole rational kernel
$$\mathcal{F}_{2n+1,2}^{\mathrm{odd},[A_0,A]}(z; P) :=
  \frac{((2AK)!)^2 ((2A_0K)!)^{2n-1}}
       {\left(\prod_{k=0}^{2AK}(z+k)^2\right)\left(\prod_{|k-AK|\le A_0K}(z+k)^{2n-1}\right)}
  P((z+AK)^2).$$ -/
def windowedKernelEval (n A0K AK : ℕ) (evalP : ℚ → ℚ) (z : ℚ) : ℚ :=
  let pref : ℚ := (((2 * AK).factorial : ℚ) ^ 2) * (((2 * A0K).factorial : ℚ) ^ (2 * n - 1))
  let denomOut : ℚ := ∏ k ∈ Finset.range (2 * AK + 1), (z + (k : ℚ)) ^ 2
  let denomIn : ℚ :=
    ∏ k ∈ (Finset.range (2 * AK + 1)).filter (fun (k : ℕ) => ((k : ℤ) - (AK : ℤ)).natAbs ≤ A0K),
      (z + (k : ℚ)) ^ (2 * n - 1)
  (pref / (denomOut * denomIn)) * evalP ((z + (AK : ℚ)) ^ 2)

/-- **Lemma 3.2 (Equation (3.6))**: Closed-form leading Laurent coefficient `g_{k,0} ≠ 0`
at inner poles `|r| ≤ A₀K` and outer poles `A₀K < |r| ≤ AK`, where `r = AK - k`. -/
def gkZeroClosed (n A0K AK k : ℕ) : ℚ :=
  let r_abs : ℕ := ((AK : ℤ) - (k : ℤ)).natAbs
  if r_abs ≤ A0K then
    let r_shift : ℕ := A0K + AK - k
    ((-1 : ℚ) ^ r_shift) *
      ((Nat.choose (2 * AK) k : ℚ) ^ 2) *
      ((Nat.choose (2 * A0K) (A0K + r_abs) : ℚ) ^ (2 * n - 1))
  else
    let sgn : ℚ := if k < AK then 1 else -1
    let outerBin : ℚ := ((r_abs - A0K : ℕ) : ℚ) * (Nat.choose (r_abs + A0K) (2 * A0K) : ℚ)
    sgn * ((Nat.choose (2 * AK) k : ℚ) ^ 2) / (outerBin ^ (2 * n - 1))

/-- **Lemma 3.2 (`g_{k,0} ≠ 0`)**: For every `n ≥ 1`, `A₀K < AK`, and every pole `0 ≤ k ≤ 2AK`,
the leading Laurent coefficient `gkZeroClosed n A0K AK k` is strictly non-zero. -/
theorem lemma_3_2_gkZero_ne_zero (n A0K AK k : ℕ) (hk : k ≤ 2 * AK) :
    gkZeroClosed n A0K AK k ≠ 0 := by
  unfold gkZeroClosed
  dsimp only
  split_ifs with h_in h_lt
  · have hc1 : 0 < Nat.choose (2 * AK) k := Nat.choose_pos hk
    have hc2 : 0 < Nat.choose (2 * A0K) (A0K + ((AK : ℤ) - (k : ℤ)).natAbs) :=
      Nat.choose_pos (by omega)
    have h1 : (-1 : ℚ) ^ (A0K + AK - k) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2 : ((Nat.choose (2 * AK) k : ℚ) ^ 2) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast hc1.ne')
    have h3 : ((Nat.choose (2 * A0K) (A0K + ((AK : ℤ) - (k : ℤ)).natAbs) : ℚ) ^ (2 * n - 1)) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast hc2.ne')
    exact mul_ne_zero (mul_ne_zero h1 h2) h3
  · have hc1 : 0 < Nat.choose (2 * AK) k := Nat.choose_pos hk
    have hr_gt : A0K < ((AK : ℤ) - (k : ℤ)).natAbs := not_le.mp h_in
    have h_diff_pos : 0 < ((AK : ℤ) - (k : ℤ)).natAbs - A0K := Nat.sub_pos_of_lt hr_gt
    have hc2 : 0 < Nat.choose (((AK : ℤ) - (k : ℤ)).natAbs + A0K) (2 * A0K) :=
      Nat.choose_pos (by omega)
    have h_out_ne : (((((AK : ℤ) - (k : ℤ)).natAbs - A0K : ℕ) : ℚ) *
        (Nat.choose (((AK : ℤ) - (k : ℤ)).natAbs + A0K) (2 * A0K) : ℚ)) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast h_diff_pos.ne') (by exact_mod_cast hc2.ne')
    exact div_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero _ (by exact_mod_cast hc1.ne')))
      (pow_ne_zero _ h_out_ne)
  · have hc1 : 0 < Nat.choose (2 * AK) k := Nat.choose_pos hk
    have hr_gt : A0K < ((AK : ℤ) - (k : ℤ)).natAbs := not_le.mp h_in
    have h_diff_pos : 0 < ((AK : ℤ) - (k : ℤ)).natAbs - A0K := Nat.sub_pos_of_lt hr_gt
    have hc2 : 0 < Nat.choose (((AK : ℤ) - (k : ℤ)).natAbs + A0K) (2 * A0K) :=
      Nat.choose_pos (by omega)
    have h_out_ne : (((((AK : ℤ) - (k : ℤ)).natAbs - A0K : ℕ) : ℚ) *
        (Nat.choose (((AK : ℤ) - (k : ℤ)).natAbs + A0K) (2 * A0K) : ℚ)) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast h_diff_pos.ne') (by exact_mod_cast hc2.ne')
    exact div_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero _ (by exact_mod_cast hc1.ne')))
      (pow_ne_zero _ h_out_ne)

/-- Symmetry of the inner leading coefficients `g_{2AK - k, 0} = g_{k, 0}` for `|k - AK| ≤ A₀K`. -/
theorem lemma_3_2_gkZero_inner_symm (n A0K AK r : ℕ) (hr : r ≤ A0K) (hA0 : A0K ≤ AK) :
    gkZeroClosed n A0K AK (AK + r) = gkZeroClosed n A0K AK (AK - r) := by
  unfold gkZeroClosed
  have h_abs1 : ((AK : ℤ) - ((AK + r : ℕ) : ℤ)).natAbs = r := by omega
  have h_abs2 : ((AK : ℤ) - ((AK - r : ℕ) : ℤ)).natAbs = r := by omega
  rw [h_abs1, h_abs2, if_pos hr, if_pos hr]
  dsimp only
  have h_choose : Nat.choose (2 * AK) (AK + r) = Nat.choose (2 * AK) (AK - r) := by
    rw [← Nat.choose_symm (by omega : AK + r ≤ 2 * AK)]
    congr 1; omega
  have h_sign : (-1 : ℚ) ^ (A0K + AK - (AK + r)) = (-1 : ℚ) ^ (A0K + AK - (AK - r)) := by
    have h_exp : A0K + AK - (AK - r) = (A0K + AK - (AK + r)) + 2 * r := by omega
    rw [h_exp, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  rw [h_choose, h_sign]

/-- **Lemma 3.2 (Equation (3.7))**: Logarithmic power sums
$$p_{k,d} := (-1)^d \sum_{\substack{0 \le j \le 2AK \\ j \ne k}} \frac{L_j}{(j - k)^d}.$$ -/
def logPowerSumPkd (n A0K AK k d : ℕ) : ℚ :=
  ((-1 : ℚ) ^ d) *
    ∑ j ∈ (Finset.range (2 * AK + 1)).erase k,
      (poleMultiplicity n A0K AK j : ℚ) / (((j : ℚ) - (k : ℚ)) ^ d)

/-- **Lemma 3.2 (Equation (3.7))**: Higher Taylor coefficients `g_{k,q}` via Newton's recurrence:
$$g_{k,q} = \frac{1}{q} \sum_{d=1}^q p_{k,d} g_{k, q-d}.$$ -/
def gkTaylorCoeff (n A0K AK k : ℕ) : ℕ → ℚ
  | 0 => gkZeroClosed n A0K AK k
  | q + 1 =>
    ((1 : ℚ) / ((q + 1 : ℕ) : ℚ)) *
      ∑ d ∈ Finset.attach (Finset.Icc 1 (q + 1)),
        logPowerSumPkd n A0K AK k d.1 * gkTaylorCoeff n A0K AK k (q + 1 - d.1)
termination_by q => q
decreasing_by
  have hd : 1 ≤ d.1 := (Finset.mem_Icc.mp d.2).1
  omega

/-- **Lemma 3.2 (Equation (3.8))**: Finite convolution formula for the Laurent coefficient
`A_{t,k}(P)` (`1 ≤ t ≤ L_k`), setting `A_{t,k}(P) := 0` when `t > L_k` or `t = 0`:
$$A_{t,k}(P) = \sum_{q=0}^{L_k - t} g_{k, L_k - t - q}
  \sum_{d = \lceil q/2 \rceil}^q \binom{d}{q-d} (2r)^{2d-q} \frac{P^{(d)}(r^2)}{d!}.$$ -/
def laurentCoeffAt (n A0K AK : ℕ) (normDerivP : ℚ → ℕ → ℚ) (t k : ℕ) : ℚ :=
  let Lk := poleMultiplicity n A0K AK k
  if t = 0 ∨ Lk < t then 0
  else
    let r : ℚ := (AK : ℚ) - (k : ℚ)
    ∑ q ∈ Finset.range (Lk - t + 1),
      gkTaylorCoeff n A0K AK k (Lk - t - q) *
        ∑ d ∈ Finset.Icc ((q + 1) / 2) q,
          (Nat.choose d (q - d) : ℚ) * ((2 * r) ^ (2 * d - q)) * normDerivP (r ^ 2) d

/-- **Definition 3.1 (Equation (3.4))**: The global pole sum
$$S_t(P) := \sum_{k=0}^{2AK} A_{t,k}(P).$$ -/
def poleSumSt (_n _A0K AK : ℕ) (At : ℕ → ℕ → ℚ) (t : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (2 * AK + 1), At t k

/-!
## Theorem 3.3: Odd Reflection Parity and Inner-Window Support Compression
-/

/-- Abstract structure capturing a family of Laurent coefficients `A_{t,k}` satisfying the
reflection law (3.9) `A_{t, 2AK-k} = (-1)^{t-1} A_{t,k}` and outer pole bound `L_k = 2` (3.11). -/
theorem sum_range_reflect_antisymm (M : ℕ) (f : ℕ → ℚ)
    (h_anti : ∀ k ≤ M, f (M - k) = - f k) :
    (∑ k ∈ Finset.range (M + 1), f k) = 0 := by
  have h_rev : (∑ k ∈ Finset.range (M + 1), f k) = ∑ k ∈ Finset.range (M + 1), f (M - k) :=
    (Finset.sum_range_reflect f (M + 1)).symm
  have h_neg : (∑ k ∈ Finset.range (M + 1), f (M - k)) = - ∑ k ∈ Finset.range (M + 1), f k := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact h_anti k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  linarith

/-- **Theorem 3.3(i) (Equation (3.10): Vanishing of All Even-Weight Pole Sums `S_{2j}(P) = 0`)**:
Whenever the Laurent coefficients satisfy the reflection law (3.9)
`A_{t, 2AK - k}(P) = (-1)^{t - 1} A_{t, k}(P)`, for every even weight `t = 2j` (`j ≥ 1`),
`A_{2j, 2AK - k}(P) = -A_{2j, k}(P)`, and hence the pole sum `S_{2j}(P) = ∑_{k=0}^{2AK} A_{2j,k}(P) = 0`
vanishes identically. -/
theorem theorem_3_3_i_even_pole_sum_zero (n A0K AK : ℕ) (At : ℕ → ℕ → ℚ) (j : ℕ) (hj : 1 ≤ j)
    (h_refl : ∀ k ≤ 2 * AK, At (2 * j) (2 * AK - k) = (-1 : ℚ) ^ (2 * j - 1) * At (2 * j) k) :
    poleSumSt n A0K AK At (2 * j) = 0 := by
  unfold poleSumSt
  apply sum_range_reflect_antisymm (2 * AK) (At (2 * j))
  intro k hk
  rw [h_refl k hk]
  have h_odd : Odd (2 * j - 1) := ⟨j - 1, by omega⟩
  rw [h_odd.neg_one_pow]
  ring

/-- **Theorem 3.3(i) (Reflection Parity of `g_{k,0}`: `g_{2AK - k, 0} = (-1)^{L_k - 1} g_{k, 0}`)**:
At inner poles (`|k - AK| ≤ A₀K`, where `L_k = 2n + 1` is odd), `g_{2AK - k, 0} = g_{k, 0}`,
while at outer poles (`A₀K < |k - AK| ≤ AK`, where `L_k = 2` is even), `g_{2AK - k, 0} = -g_{k, 0}`. -/
theorem gkZeroClosed_reflect (n A0K AK k : ℕ) (hn : 1 ≤ n) (hk : k ≤ 2 * AK) :
    gkZeroClosed n A0K AK (2 * AK - k) =
      ((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - 1)) * gkZeroClosed n A0K AK k := by
  unfold gkZeroClosed poleMultiplicity
  have h_abs : ((AK : ℤ) - ((2 * AK - k : ℕ) : ℤ)).natAbs = ((AK : ℤ) - (k : ℤ)).natAbs := by
    have h_cast : ((2 * AK - k : ℕ) : ℤ) = 2 * (AK : ℤ) - (k : ℤ) := Int.ofNat_sub hk
    rw [h_cast, show (AK : ℤ) - (2 * (AK : ℤ) - (k : ℤ)) = -((AK : ℤ) - (k : ℤ)) by ring,
        Int.natAbs_neg]
  have h_abs_comm : ((k : ℤ) - (AK : ℤ)).natAbs = ((AK : ℤ) - (k : ℤ)).natAbs := by
    rw [show (k : ℤ) - (AK : ℤ) = -((AK : ℤ) - (k : ℤ)) by ring, Int.natAbs_neg]
  rw [h_abs, h_abs_comm]
  have h_choose : Nat.choose (2 * AK) (2 * AK - k) = Nat.choose (2 * AK) k :=
    Nat.choose_symm hk
  dsimp only
  by_cases h_in : ((AK : ℤ) - (k : ℤ)).natAbs ≤ A0K
  · rw [if_pos h_in, if_pos h_in, if_pos h_in]
    have h_even : Even (2 * n + 1 - 1) := ⟨n, by omega⟩
    rw [h_even.neg_one_pow, one_mul, h_choose]
    have h_sign : (-1 : ℚ) ^ (A0K + AK - (2 * AK - k)) = (-1 : ℚ) ^ (A0K + AK - k) := by
      rcases le_or_gt k AK with hk_le | hk_gt
      · have h_exp : A0K + AK - k = (A0K + AK - (2 * AK - k)) + 2 * (AK - k) := by omega
        rw [h_exp, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
      · have h_exp : A0K + AK - (2 * AK - k) = (A0K + AK - k) + 2 * (k - AK) := by omega
        rw [h_exp, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
    rw [h_sign]
  · rw [if_neg h_in, if_neg h_in, if_neg h_in]
    have h_ne_ak : k ≠ AK := by omega
    rw [h_choose]
    by_cases h_lt : k < AK
    · have h_nlt : ¬(2 * AK - k < AK) := by omega
      rw [if_pos h_lt, if_neg h_nlt]
      ring
    · have h_lt' : 2 * AK - k < AK := by omega
      rw [if_neg h_lt, if_pos h_lt']
      ring

/-- **Lemma 3.2 (Reflection Parity of Logarithmic Power Sums `p_{2AK - k, d} = (-1)^d p_{k, d}`)**:
Under the reflection `k ↦ 2AK - k` and `j ↦ 2AK - j`, the logarithmic power sums satisfy
`p_{2AK - k, d} = (-1)^d p_{k, d}`. -/
theorem logPowerSumPkd_reflect (n A0K AK k d : ℕ) (hk : k ≤ 2 * AK) :
    logPowerSumPkd n A0K AK (2 * AK - k) d = (-1 : ℚ) ^ d * logPowerSumPkd n A0K AK k d := by
  have h_sum_eq :
      (∑ j ∈ (Finset.range (2 * AK + 1)).erase (2 * AK - k),
        (poleMultiplicity n A0K AK j : ℚ) / (((j : ℚ) - ((2 * AK - k : ℕ) : ℚ)) ^ d)) =
      ((-1 : ℚ) ^ d) *
        ∑ j ∈ (Finset.range (2 * AK + 1)).erase k,
          (poleMultiplicity n A0K AK j : ℚ) / (((j : ℚ) - (k : ℚ)) ^ d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_bij (fun j _ => 2 * AK - j)
    · intro j hj
      have hj_range : j < 2 * AK + 1 := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
      have hj_ne : j ≠ 2 * AK - k := Finset.ne_of_mem_erase hj
      exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
    · intro j₁ hj₁ j₂ hj₂ h_eq
      have h1 : j₁ ≤ 2 * AK := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_erase hj₁))
      have h2 : j₂ ≤ 2 * AK := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_erase hj₂))
      omega
    · intro j' hj'
      have hj'_le : j' ≤ 2 * AK := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_erase hj'))
      have hj'_ne : j' ≠ k := Finset.ne_of_mem_erase hj'
      refine ⟨2 * AK - j', Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩, by omega⟩
    · intro j hj
      have hj_le : j ≤ 2 * AK := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))
      have h_L : poleMultiplicity n A0K AK (2 * AK - j) = poleMultiplicity n A0K AK j :=
        poleMultiplicity_reflect n A0K AK j hj_le
      have h_diff : ((j : ℚ) - ((2 * AK - k : ℕ) : ℚ)) = -(((2 * AK - j : ℕ) : ℚ) - (k : ℚ)) := by
        rw [Nat.cast_sub hk, Nat.cast_sub hj_le]
        push_cast
        ring
      have h_sq : ((-1 : ℚ) ^ d) * ((-1 : ℚ) ^ d) = 1 := by
        rw [← pow_add, show d + d = 2 * d by ring, pow_mul, neg_one_sq, one_pow]
      have h_inv : ((-1 : ℚ) ^ d)⁻¹ = (-1 : ℚ) ^ d :=
        inv_eq_of_mul_eq_one_right h_sq
      rw [h_L, h_diff, neg_eq_neg_one_mul, mul_pow, mul_comm ((-1 : ℚ) ^ d),
          ← div_div, div_eq_mul_inv _ ((-1 : ℚ) ^ d), h_inv, mul_comm]
  unfold logPowerSumPkd
  rw [h_sum_eq]

/-- **Lemma 3.2 & Theorem 3.3(i) (Reflection Parity of Higher Taylor Coefficients `g_{k,q}`)**:
For all `n ≥ 1`, `k ≤ 2AK`, and `q ≥ 0`,
`g_{2AK - k, q} = (-1)^q (-1)^{L_k - 1} g_{k, q}`. -/
theorem gkTaylorCoeff_reflect (n A0K AK k : ℕ) (hn : 1 ≤ n) (hk : k ≤ 2 * AK) :
    ∀ q : ℕ,
      gkTaylorCoeff n A0K AK (2 * AK - k) q =
        ((-1 : ℚ) ^ q) * ((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - 1)) *
          gkTaylorCoeff n A0K AK k q := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    rcases q with _ | q
    · simp [gkTaylorCoeff, gkZeroClosed_reflect n A0K AK k hn hk]
    · rw [gkTaylorCoeff, gkTaylorCoeff]
      have h_sum :
          (∑ d ∈ Finset.attach (Finset.Icc 1 (q + 1)),
            logPowerSumPkd n A0K AK (2 * AK - k) d.1 *
              gkTaylorCoeff n A0K AK (2 * AK - k) (q + 1 - d.1)) =
          ((-1 : ℚ) ^ (q + 1)) * ((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - 1)) *
            ∑ d ∈ Finset.attach (Finset.Icc 1 (q + 1)),
              logPowerSumPkd n A0K AK k d.1 * gkTaylorCoeff n A0K AK k (q + 1 - d.1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        have hd1 : 1 ≤ d.1 := (Finset.mem_Icc.mp d.2).1
        have hd2 : d.1 ≤ q + 1 := (Finset.mem_Icc.mp d.2).2
        rw [logPowerSumPkd_reflect n A0K AK k d.1 hk, ih (q + 1 - d.1) (by omega)]
        have h_pow : (-1 : ℚ) ^ d.1 * (-1 : ℚ) ^ (q + 1 - d.1) = (-1 : ℚ) ^ (q + 1) := by
          rw [← pow_add, show d.1 + (q + 1 - d.1) = q + 1 by omega]
        calc ((-1 : ℚ) ^ d.1 * logPowerSumPkd n A0K AK k d.1) *
              ((-1 : ℚ) ^ (q + 1 - d.1) * (-1 : ℚ) ^ (poleMultiplicity n A0K AK k - 1) *
                gkTaylorCoeff n A0K AK k (q + 1 - d.1))
            = ((-1 : ℚ) ^ d.1 * (-1 : ℚ) ^ (q + 1 - d.1)) *
                (-1 : ℚ) ^ (poleMultiplicity n A0K AK k - 1) *
                (logPowerSumPkd n A0K AK k d.1 * gkTaylorCoeff n A0K AK k (q + 1 - d.1)) := by ring
          _ = (-1 : ℚ) ^ (q + 1) * (-1 : ℚ) ^ (poleMultiplicity n A0K AK k - 1) *
                (logPowerSumPkd n A0K AK k d.1 * gkTaylorCoeff n A0K AK k (q + 1 - d.1)) := by
              rw [h_pow]
      rw [h_sum]
      ring

/-- **Theorem 3.3(i) (Equation (3.9): Exact Laurent Coefficient Reflection Parity Law)**:
For every `n ≥ 1`, every polynomial jet `normDerivP`, every pole order `t ≥ 1`, and every
pole index `0 ≤ k ≤ 2AK`, the Laurent coefficients `laurentCoeffAt` satisfy
$$A_{t, 2AK - k}(P) = (-1)^{t - 1} A_{t, k}(P).$$ -/
theorem theorem_3_3_i_laurentCoeff_reflect (n A0K AK : ℕ) (normDerivP : ℚ → ℕ → ℚ)
    (t k : ℕ) (hn : 1 ≤ n) (ht : 1 ≤ t) (hk : k ≤ 2 * AK) :
    laurentCoeffAt n A0K AK normDerivP t (2 * AK - k) =
      ((-1 : ℚ) ^ (t - 1)) * laurentCoeffAt n A0K AK normDerivP t k := by
  unfold laurentCoeffAt
  have hLk : poleMultiplicity n A0K AK (2 * AK - k) = poleMultiplicity n A0K AK k :=
    poleMultiplicity_reflect n A0K AK k hk
  simp only [hLk]
  split_ifs with h_cond
  · ring
  · push_neg at h_cond
    have ht_le : t ≤ poleMultiplicity n A0K AK k := h_cond.2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hq_le : q ≤ poleMultiplicity n A0K AK k - t :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    rw [gkTaylorCoeff_reflect n A0K AK k hn hk (poleMultiplicity n A0K AK k - t - q)]
    have h_r_neg : (AK : ℚ) - ((2 * AK - k : ℕ) : ℚ) = -((AK : ℚ) - (k : ℚ)) := by
      rw [Nat.cast_sub hk]
      push_cast
      ring
    have h_r_sq : ((AK : ℚ) - ((2 * AK - k : ℕ) : ℚ)) ^ 2 = ((AK : ℚ) - (k : ℚ)) ^ 2 := by
      rw [h_r_neg, neg_sq]
    have h_inner_sum :
        (∑ d ∈ Finset.Icc ((q + 1) / 2) q,
          (Nat.choose d (q - d) : ℚ) *
            ((2 * ((AK : ℚ) - ((2 * AK - k : ℕ) : ℚ))) ^ (2 * d - q)) *
            normDerivP (((AK : ℚ) - ((2 * AK - k : ℕ) : ℚ)) ^ 2) d) =
        ((-1 : ℚ) ^ q) *
          ∑ d ∈ Finset.Icc ((q + 1) / 2) q,
            (Nat.choose d (q - d) : ℚ) *
              ((2 * ((AK : ℚ) - (k : ℚ))) ^ (2 * d - q)) *
              normDerivP (((AK : ℚ) - (k : ℚ)) ^ 2) d := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      have hd_ge : (q + 1) / 2 ≤ d := (Finset.mem_Icc.mp hd).1
      have h_2d_ge : q ≤ 2 * d := by omega
      rw [h_r_sq, h_r_neg, show 2 * -((AK : ℚ) - (k : ℚ)) = -(2 * ((AK : ℚ) - (k : ℚ))) by ring,
          neg_pow]
      have h_parity : (-1 : ℚ) ^ (2 * d - q) = (-1 : ℚ) ^ q := by
        have h_exp : 2 * d - q + q = 2 * d := by omega
        have h_mul : (-1 : ℚ) ^ (2 * d - q) * (-1 : ℚ) ^ q = 1 := by
          rw [← pow_add, h_exp, pow_mul, neg_one_sq, one_pow]
        have h_qq : (-1 : ℚ) ^ q * (-1 : ℚ) ^ q = 1 := by
          rw [← pow_add, show q + q = 2 * q by ring, pow_mul, neg_one_sq, one_pow]
        calc (-1 : ℚ) ^ (2 * d - q)
            = (-1 : ℚ) ^ (2 * d - q) * 1 := (mul_one _).symm
          _ = (-1 : ℚ) ^ (2 * d - q) * ((-1 : ℚ) ^ q * (-1 : ℚ) ^ q) := by rw [h_qq]
          _ = ((-1 : ℚ) ^ (2 * d - q) * (-1 : ℚ) ^ q) * (-1 : ℚ) ^ q := by ring
          _ = 1 * (-1 : ℚ) ^ q := by rw [h_mul]
          _ = (-1 : ℚ) ^ q := one_mul _
      rw [h_parity]
      ring
    rw [h_inner_sum]
    have h_sign_combine :
        ((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - t - q)) *
          ((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - 1)) * ((-1 : ℚ) ^ q) =
          (-1 : ℚ) ^ (t - 1) := by
      have h_Lk_pos : 1 ≤ poleMultiplicity n A0K AK k := le_trans ht ht_le
      have h_exp_eq :
          (poleMultiplicity n A0K AK k - t - q) +
            (poleMultiplicity n A0K AK k - 1) + q + (t - 1) =
            2 * (poleMultiplicity n A0K AK k - 1) := by omega
      have h_prod_one :
          ((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - t - q)) *
            ((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - 1)) * ((-1 : ℚ) ^ q) *
            ((-1 : ℚ) ^ (t - 1)) = 1 := by
        rw [← pow_add, ← pow_add, ← pow_add, h_exp_eq, pow_mul, neg_one_sq, one_pow]
      have h_t_sq : ((-1 : ℚ) ^ (t - 1)) * ((-1 : ℚ) ^ (t - 1)) = 1 := by
        rw [← pow_add, show t - 1 + (t - 1) = 2 * (t - 1) by omega, pow_mul, neg_one_sq, one_pow]
      calc ((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - t - q)) *
              ((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - 1)) * ((-1 : ℚ) ^ q)
          = (((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - t - q)) *
              ((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - 1)) * ((-1 : ℚ) ^ q)) * 1 := (mul_one _).symm
        _ = (((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - t - q)) *
              ((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - 1)) * ((-1 : ℚ) ^ q)) *
              (((-1 : ℚ) ^ (t - 1)) * ((-1 : ℚ) ^ (t - 1))) := by rw [h_t_sq]
        _ = (((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - t - q)) *
              ((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - 1)) * ((-1 : ℚ) ^ q) *
              ((-1 : ℚ) ^ (t - 1))) * ((-1 : ℚ) ^ (t - 1)) := by ring
        _ = 1 * ((-1 : ℚ) ^ (t - 1)) := by rw [h_prod_one]
        _ = (-1 : ℚ) ^ (t - 1) := one_mul _
    calc ((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - t - q) *
            (-1 : ℚ) ^ (poleMultiplicity n A0K AK k - 1) *
            gkTaylorCoeff n A0K AK k (poleMultiplicity n A0K AK k - t - q)) *
          ((-1 : ℚ) ^ q *
            ∑ d ∈ Finset.Icc ((q + 1) / 2) q,
              (Nat.choose d (q - d) : ℚ) * (2 * ((AK : ℚ) - (k : ℚ))) ^ (2 * d - q) *
                normDerivP (((AK : ℚ) - (k : ℚ)) ^ 2) d)
        = (((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - t - q)) *
            ((-1 : ℚ) ^ (poleMultiplicity n A0K AK k - 1)) * ((-1 : ℚ) ^ q)) *
          (gkTaylorCoeff n A0K AK k (poleMultiplicity n A0K AK k - t - q) *
            ∑ d ∈ Finset.Icc ((q + 1) / 2) q,
              (Nat.choose d (q - d) : ℚ) * (2 * ((AK : ℚ) - (k : ℚ))) ^ (2 * d - q) *
                normDerivP (((AK : ℚ) - (k : ℚ)) ^ 2) d) := by ring
      _ = (-1 : ℚ) ^ (t - 1) *
          (gkTaylorCoeff n A0K AK k (poleMultiplicity n A0K AK k - t - q) *
            ∑ d ∈ Finset.Icc ((q + 1) / 2) q,
              (Nat.choose d (q - d) : ℚ) * (2 * ((AK : ℚ) - (k : ℚ))) ^ (2 * d - q) *
                normDerivP (((AK : ℚ) - (k : ℚ)) ^ 2) d) := by rw [h_sign_combine]

/-- **Theorem 3.3(i) (Equation (3.10): Unconditional Vanishing of `S_{2j}(P) = 0` for `laurentCoeffAt`)**:
For every `n ≥ 1`, every polynomial jet `normDerivP`, and every even weight `2j` (`j ≥ 1`),
the pole sum `S_{2j}(P) = ∑_{k=0}^{2AK} A_{2j, k}(P)` of `laurentCoeffAt` vanishes identically. -/
theorem theorem_3_3_i_laurent_even_pole_sum_zero (n A0K AK : ℕ) (normDerivP : ℚ → ℕ → ℚ)
    (j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) :
    poleSumSt n A0K AK (laurentCoeffAt n A0K AK normDerivP) (2 * j) = 0 := by
  apply theorem_3_3_i_even_pole_sum_zero n A0K AK (laurentCoeffAt n A0K AK normDerivP) j hj
  intro k hk
  exact theorem_3_3_i_laurentCoeff_reflect n A0K AK normDerivP (2 * j) k hn (by omega) hk

/-- **Theorem 3.3(ii) (Equation (3.11): Vanishing of Outer Poles in `S_{2j+1}(P)`)**:
For every outer pole `k` with `A₀K < |k - AK| ≤ AK` and every weight `t ≥ 3`,
`laurentCoeffAt n A0K AK normDerivP t k = 0`. -/
theorem theorem_3_3_ii_outer_vanishing (n A0K AK : ℕ) (normDerivP : ℚ → ℕ → ℚ)
    (t k : ℕ) (ht : 3 ≤ t) (h_out : A0K < ((k : ℤ) - (AK : ℤ)).natAbs) :
    laurentCoeffAt n A0K AK normDerivP t k = 0 := by
  unfold laurentCoeffAt
  have hLk : poleMultiplicity n A0K AK k = 2 := poleMultiplicity_outer_eq_two n A0K AK k h_out
  rw [if_pos (Or.inr (by omega : poleMultiplicity n A0K AK k < t))]

/-- **Theorem 3.3(ii) (Equation (3.12): Inner-Window Support Compression of `S_{2j+1}(P)`)**:
For every `j ≥ 1`, the odd-weight pole sum `S_{2j+1}(P)` is supported exclusively on the
inner window `|k - AK| ≤ A₀K`:
$$S_{2j+1}(P) = \sum_{|k - AK| \le A_0 K} A_{2j+1, k}(P).$$ -/
theorem theorem_3_3_ii_inner_support_compression (n A0K AK : ℕ) (normDerivP : ℚ → ℕ → ℚ)
    (j : ℕ) (_hj : 1 ≤ j) :
    poleSumSt n A0K AK (laurentCoeffAt n A0K AK normDerivP) (2 * j + 1) =
      ∑ k ∈ (Finset.range (2 * AK + 1)).filter (fun (k : ℕ) => ((k : ℤ) - (AK : ℤ)).natAbs ≤ A0K),
        laurentCoeffAt n A0K AK normDerivP (2 * j + 1) k := by
  unfold poleSumSt
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (2 * AK + 1))
        (fun (k : ℕ) => ((k : ℤ) - (AK : ℤ)).natAbs ≤ A0K)]
  have h_outer_zero :
      (∑ k ∈ (Finset.range (2 * AK + 1)).filter (fun (k : ℕ) => ¬((k : ℤ) - (AK : ℤ)).natAbs ≤ A0K),
        laurentCoeffAt n A0K AK normDerivP (2 * j + 1) k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have h_not : A0K < ((k : ℤ) - (AK : ℤ)).natAbs :=
      not_le.mp (Finset.mem_filter.mp hk).2
    exact theorem_3_3_ii_outer_vanishing n A0K AK normDerivP (2 * j + 1) k (by omega) h_not
  rw [h_outer_zero, add_zero]

/-!
## Theorem 3.4: Positive-Series Moment Representation
-/

/-- **Equation (3.14)**: Generalized harmonic number
$$H_k^{(t)} := \sum_{\ell=1}^k \frac{1}{\ell^t} \quad (H_0^{(t)} := 0).$$ -/
def harmonicNumber (t k : ℕ) : ℚ :=
  ∑ l ∈ Finset.Icc 1 k, (1 : ℚ) / ((l : ℚ) ^ t)

@[simp]
theorem harmonicNumber_zero (t : ℕ) : harmonicNumber t 0 = 0 := by
  unfold harmonicNumber
  simp

/-- **Equation (3.14)**: Rational harmonic remainder
$$\mathcal{R}_0(P) := -\sum_{k=0}^{2AK} \sum_{t=1}^{L_k} A_{t,k}(P) H_k^{(t)}.$$ -/
def R0Remainder (n A0K AK : ℕ) (At : ℕ → ℕ → ℚ) : ℚ :=
  - ∑ k ∈ Finset.range (2 * AK + 1),
      ∑ t ∈ Finset.Icc 1 (poleMultiplicity n A0K AK k),
        At t k * harmonicNumber t k

/-- **Equation (3.15)**: Discrete positive kernel weights
$$W_K(\nu) := \mathcal{F}_{2n+1,2}^{\mathrm{odd},[A_0,A]}(\nu; 1) > 0 \quad (\nu \ge 1).$$ -/
def WKWeight (n A0K AK ν : ℕ) : ℚ :=
  windowedKernelEval n A0K AK (fun _ => 1) (ν : ℚ)

/-- **Theorem 3.4 (Equation (3.15): Strict Positivity of `W_K(ν) > 0` for `ν ≥ 1`)**. -/
theorem theorem_3_4_WKWeight_pos (n A0K AK ν : ℕ) (hν : 1 ≤ ν) :
    0 < WKWeight n A0K AK ν := by
  unfold WKWeight windowedKernelEval
  dsimp only
  rw [mul_one]
  have hν_pos : (0 : ℚ) < (ν : ℚ) := by exact_mod_cast hν
  apply div_pos
  · apply mul_pos
    · exact pow_pos (by exact_mod_cast Nat.factorial_pos (2 * AK)) 2
    · exact pow_pos (by exact_mod_cast Nat.factorial_pos (2 * A0K)) (2 * n - 1)
  · apply mul_pos
    · apply Finset.prod_pos
      intro k _
      exact pow_pos (add_pos_of_pos_of_nonneg hν_pos (Nat.cast_nonneg k)) 2
    · apply Finset.prod_pos
      intro k _
      exact pow_pos (add_pos_of_pos_of_nonneg hν_pos (Nat.cast_nonneg k)) (2 * n - 1)

/-- **Equation (1.4) & (3.16)**: The odd-zeta linear form
$$\mathcal{A}(P) := \sum_{j=1}^n S_{2j+1}(P) \zeta(2j+1) + \mathcal{R}_0(P).$$ -/
noncomputable def oddZetaLinearForm (n : ℕ) (S_odd : Fin n → ℚ) (R0 : ℚ) : ℝ :=
  (∑ j : Fin n, (S_odd j : ℝ) * riemannZetaReal (2 * (j.val + 1) + 1)) + (R0 : ℝ)

/-- **Theorem 3.4 (Shifted Zeta Tail Series Identity, p. 18)**:
For every pole location `k ≥ 0` and every pole order `t ≥ 2`, the shifted tail series
`∑' ν : ℕ, 1 / ((ν + 1 + k : ℝ) ^ t)` converges and equals `ζ(t) - H_k^{(t)}`. -/
theorem tsum_shifted_inv_pow_eq_zeta_sub_harmonic (t k : ℕ) (ht : 2 ≤ t) :
    (∑' ν : ℕ, (1 : ℝ) / (((ν + 1 + k : ℕ) : ℝ) ^ t)) =
      riemannZetaReal t - (harmonicNumber t k : ℝ) := by
  have h_summable : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ t) :=
    summable_riemannZetaReal ht
  have h_split := sum_add_tsum_nat_add k h_summable
  have h_harm :
      (∑ i ∈ Finset.range k, (1 : ℝ) / ((i : ℝ) + 1) ^ t) = (harmonicNumber t k : ℝ) := by
    unfold harmonicNumber
    push_cast
    apply Finset.sum_bij (fun i _ => i + 1)
    · intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_Icc]
      omega
    · intro i1 _ i2 _ h_eq
      omega
    · intro l hl
      simp only [Finset.mem_Icc] at hl
      exact ⟨l - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro i _
      push_cast
      rfl
  have h_tail :
      (∑' i : ℕ, (1 : ℝ) / (((i + k : ℕ) : ℝ) + 1) ^ t) =
        ∑' ν : ℕ, (1 : ℝ) / (((ν + 1 + k : ℕ) : ℝ) ^ t) := by
    congr 1
    ext ν
    congr 2
    push_cast
    ring
  unfold riemannZetaReal
  rw [h_harm, h_tail] at h_split
  linarith

/-- **Theorem 3.4 (Equation (3.16): Exact Partial-Fraction Series Decomposition into Odd Zeta Values)**:
Given Laurent coefficients `At : ℕ → ℕ → ℚ` satisfying the reflection parity law (Theorem 3.3(i))
so that all even pole sums `S_{2j}(P) = 0` (`1 ≤ j ≤ n`) and `S_1(P) = 0` vanish, summing the
higher-order pole series `∑_{k=0}^{2AK} ∑_{t=2}^{2n+1} A_{t,k}(P) (ζ(t) - H_k^{(t)})` together
with the telescoped simple-pole contribution `-∑_{k=0}^{2AK} A_{1,k}(P) H_k^{(1)}` yields
precisely the odd-zeta linear form
$$\sum_{j=1}^n S_{2j+1}(P) \zeta(2j+1) + \mathcal{R}_0(P).$$ -/
theorem theorem_3_4_moment_decomposition (n A0K AK : ℕ) (At : ℕ → ℕ → ℚ)
    (h_even_zero : ∀ j : Fin n, poleSumSt n A0K AK At (2 * (j.val + 1)) = 0)
    (_h_outer_vanish : ∀ k ∈ Finset.range (2 * AK + 1),
      ∀ t ∈ Finset.Icc (poleMultiplicity n A0K AK k + 1) (2 * n + 1), At t k = 0) :
    (∑ j : Fin n,
      ((∑ k ∈ Finset.range (2 * AK + 1),
          (At (2 * (j.val + 1)) k : ℝ) * (riemannZetaReal (2 * (j.val + 1)) - (harmonicNumber (2 * (j.val + 1)) k : ℝ))) +
       (∑ k ∈ Finset.range (2 * AK + 1),
          (At (2 * (j.val + 1) + 1) k : ℝ) * (riemannZetaReal (2 * (j.val + 1) + 1) - (harmonicNumber (2 * (j.val + 1) + 1) k : ℝ))))) -
      (∑ k ∈ Finset.range (2 * AK + 1), (At 1 k : ℝ) * (harmonicNumber 1 k : ℝ)) =
    oddZetaLinearForm n (fun j => poleSumSt n A0K AK At (2 * (j.val + 1) + 1))
      (- ∑ k ∈ Finset.range (2 * AK + 1),
          ((At 1 k * harmonicNumber 1 k) +
            ∑ j : Fin n,
              (At (2 * (j.val + 1)) k * harmonicNumber (2 * (j.val + 1)) k +
               At (2 * (j.val + 1) + 1) k * harmonicNumber (2 * (j.val + 1) + 1) k))) := by
  unfold oddZetaLinearForm poleSumSt
  have h_even_sum :
      ∀ j : Fin n,
        (∑ k ∈ Finset.range (2 * AK + 1), (At (2 * (j.val + 1)) k : ℝ) * riemannZetaReal (2 * (j.val + 1))) = 0 := by
    intro j
    rw [← Finset.sum_mul]
    have hz : (∑ k ∈ Finset.range (2 * AK + 1), (At (2 * (j.val + 1)) k : ℝ)) = 0 := by
      exact_mod_cast h_even_zero j
    rw [hz, zero_mul]
  simp only [mul_sub, Finset.sum_sub_distrib, h_even_sum, zero_sub, ← Finset.sum_mul]
  push_cast
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [Finset.sum_comm (s := Finset.range (2 * AK + 1)),
      Finset.sum_comm (s := Finset.range (2 * AK + 1))]
  ring

/-!
## Theorem 3.5: Reflection-Symmetric Rising-Factorial Zero Barrier
-/

/-- **Theorem 3.5 (Equation (3.20))**: The reflection-invariant rising-factorial zero barrier
$$\Omega_B(u) := \frac{1}{((BK)!)^2} \prod_{j=1}^{BK} \left(u - (AK + j)^2\right).$$ -/
def OmegaB (AK BK : ℕ) (u : ℚ) : ℚ :=
  ((1 : ℚ) / (((BK.factorial : ℚ)) ^ 2)) *
    ∏ j ∈ Finset.Icc 1 BK, (u - ((AK + j : ℕ) : ℚ) ^ 2)

@[simp]
theorem OmegaB_zero (AK : ℕ) (u : ℚ) : OmegaB AK 0 u = 1 := by
  unfold OmegaB
  simp

/-- **Theorem 3.5(i) (Non-Vanishing of `Ω_B(r²)` at Every Pole `0 ≤ r ≤ AK`)**:
For every pole node `0 ≤ r ≤ AK`, `Ω_B(r²) ≠ 0`. -/
theorem theorem_3_5_i_nonzero_at_poles (AK BK r : ℕ) (hr : r ≤ AK) :
    OmegaB AK BK ((r : ℚ) ^ 2) ≠ 0 := by
  unfold OmegaB
  apply mul_ne_zero
  · exact div_ne_zero one_ne_zero (pow_ne_zero 2 (by exact_mod_cast Nat.factorial_ne_zero BK))
  · rw [Finset.prod_ne_zero_iff]
    intro j hj
    have hj_pos : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have h_lt : (r : ℚ) ^ 2 < ((AK + j : ℕ) : ℚ) ^ 2 := by
      have h_nat : r < AK + j := by omega
      have h_rat : (r : ℚ) < ((AK + j : ℕ) : ℚ) := by exact_mod_cast h_nat
      nlinarith
    exact ne_of_lt (sub_neg.mpr h_lt)

/-- **Theorem 3.5(ii) (Equation (3.21): Vanishing of `Ω_B((ν + AK)²)` on `1 ≤ ν ≤ BK`)**:
For every integer `1 ≤ ν ≤ BK`, `Ω_B((ν + AK)²) = 0`, so the positive series starts at `ν = BK + 1`. -/
theorem theorem_3_5_ii_vanishes_on_buffer (AK BK ν : ℕ) (h1 : 1 ≤ ν) (h2 : ν ≤ BK) :
    OmegaB AK BK (((ν + AK : ℕ) : ℚ) ^ 2) = 0 := by
  unfold OmegaB
  have h_prod_zero :
      (∏ j ∈ Finset.Icc 1 BK, (((ν + AK : ℕ) : ℚ) ^ 2 - ((AK + j : ℕ) : ℚ) ^ 2)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    rw [Nat.add_comm ν AK]
    ring
  rw [h_prod_zero, mul_zero]

/-- **Theorem 3.3(i) (Exact Odd Reflection Symmetry of the Windowed Kernel `ℱ(-2AK - z; P) = -ℱ(z; P)`)**:
For every `n ≥ 1`, `A₀K ≤ AK`, polynomial evaluator `evalP`, and `z ∈ ℚ`,
$$\mathcal{F}_{2n+1,2}^{\mathrm{odd},[A_0,A]}(-2AK - z; P) = -\mathcal{F}_{2n+1,2}^{\mathrm{odd},[A_0,A]}(z; P).$$ -/
theorem theorem_3_3_i_kernel_odd_reflection (n A0K AK : ℕ) (hn : 1 ≤ n) (hA0 : A0K ≤ AK)
    (evalP : ℚ → ℚ) (z : ℚ) :
    windowedKernelEval n A0K AK evalP (-2 * (AK : ℚ) - z) =
      - windowedKernelEval n A0K AK evalP z := by
  unfold windowedKernelEval
  dsimp only
  have h_evalP : evalP ((-2 * (AK : ℚ) - z + (AK : ℚ)) ^ 2) = evalP ((z + (AK : ℚ)) ^ 2) := by
    congr 1; ring
  have h_denomOut :
      (∏ k ∈ Finset.range (2 * AK + 1), (-2 * (AK : ℚ) - z + (k : ℚ)) ^ 2) =
        ∏ k ∈ Finset.range (2 * AK + 1), (z + (k : ℚ)) ^ 2 := by
    apply Finset.prod_bij (fun k _ => 2 * AK - k)
    · intro k hk
      have hk_le : k ≤ 2 * AK := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact Finset.mem_range.mpr (by omega)
    · intro k₁ hk₁ k₂ hk₂ h_eq
      have h1 : k₁ ≤ 2 * AK := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk₁)
      have h2 : k₂ ≤ 2 * AK := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk₂)
      omega
    · intro k' hk'
      have hk'_le : k' ≤ 2 * AK := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk')
      exact ⟨2 * AK - k', Finset.mem_range.mpr (by omega), by omega⟩
    · intro k hk
      have hk_le : k ≤ 2 * AK := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [Nat.cast_sub hk_le]
      push_cast
      ring
  let I : Finset ℕ :=
    (Finset.range (2 * AK + 1)).filter (fun (k : ℕ) => ((k : ℤ) - (AK : ℤ)).natAbs ≤ A0K)
  have hI_eq : I = Finset.Icc (AK - A0K) (AK + A0K) := by
    ext k
    simp only [I, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have hI_card : I.card = 2 * A0K + 1 := by
    rw [hI_eq, Nat.card_Icc]
    omega
  have h_denomIn :
      (∏ k ∈ I, (-2 * (AK : ℚ) - z + (k : ℚ)) ^ (2 * n - 1)) =
        - (∏ k ∈ I, (z + (k : ℚ)) ^ (2 * n - 1)) := by
    have h_bij :
        (∏ k ∈ I, (-2 * (AK : ℚ) - z + (k : ℚ)) ^ (2 * n - 1)) =
          ∏ k ∈ I, (-(z + (k : ℚ))) ^ (2 * n - 1) := by
      apply Finset.prod_bij (fun k _ => 2 * AK - k)
      · intro k hk
        rw [hI_eq, Finset.mem_Icc] at hk ⊢
        omega
      · intro k₁ hk₁ k₂ hk₂ h_eq
        rw [hI_eq, Finset.mem_Icc] at hk₁ hk₂
        omega
      · intro k' hk'
        rw [hI_eq, Finset.mem_Icc] at hk'
        refine ⟨2 * AK - k', ?_, by omega⟩
        rw [hI_eq, Finset.mem_Icc]
        omega
      · intro k hk
        rw [hI_eq, Finset.mem_Icc] at hk
        have hk_le : k ≤ 2 * AK := by omega
        rw [Nat.cast_sub hk_le]
        congr 1
        push_cast
        ring
    rw [h_bij]
    have h_odd_exp : Odd (2 * n - 1) := ⟨n - 1, by omega⟩
    have h_factor_neg :
        (∏ k ∈ I, (-(z + (k : ℚ))) ^ (2 * n - 1)) =
          (∏ _k ∈ I, (-1 : ℚ)) * (∏ k ∈ I, (z + (k : ℚ)) ^ (2 * n - 1)) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro k _
      rw [h_odd_exp.neg_pow]
      ring
    rw [h_factor_neg, Finset.prod_const, hI_card]
    have h_odd_card : Odd (2 * A0K + 1) := ⟨A0K, by ring⟩
    rw [h_odd_card.neg_one_pow, neg_one_mul]
  rw [h_evalP, h_denomOut]
  change (((2 * AK).factorial : ℚ) ^ 2 * ((2 * A0K).factorial : ℚ) ^ (2 * n - 1) /
      ((∏ k ∈ Finset.range (2 * AK + 1), (z + (k : ℚ)) ^ 2) *
        (∏ k ∈ I, (-2 * (AK : ℚ) - z + (k : ℚ)) ^ (2 * n - 1)))) *
      evalP ((z + (AK : ℚ)) ^ 2) =
    - ((((2 * AK).factorial : ℚ) ^ 2 * ((2 * A0K).factorial : ℚ) ^ (2 * n - 1) /
      ((∏ k ∈ Finset.range (2 * AK + 1), (z + (k : ℚ)) ^ 2) *
        (∏ k ∈ I, (z + (k : ℚ)) ^ (2 * n - 1)))) *
      evalP ((z + (AK : ℚ)) ^ 2))
  rw [h_denomIn, mul_neg, div_neg, neg_mul]

/-- **Theorem 3.5(ii) (Strict Positivity of `Ω_B((ν + AK)²)` Beyond the Buffer `ν ≥ BK + 1`)**:
For every integer `ν ≥ BK + 1`, `Ω_B((ν + AK)²) > 0`. -/
theorem theorem_3_5_ii_pos_beyond_buffer (AK BK ν : ℕ) (hν : BK + 1 ≤ ν) :
    0 < OmegaB AK BK (((ν + AK : ℕ) : ℚ) ^ 2) := by
  unfold OmegaB
  apply mul_pos
  · exact div_pos one_pos (pow_pos (by exact_mod_cast Nat.factorial_pos BK) 2)
  · apply Finset.prod_pos
    intro j hj
    have hj_le : j ≤ BK := (Finset.mem_Icc.mp hj).2
    have h_lt : AK + j < ν + AK := by omega
    have h_rat : ((AK + j : ℕ) : ℚ) < ((ν + AK : ℕ) : ℚ) := by exact_mod_cast h_lt
    have h_nonneg : (0 : ℚ) ≤ ((AK + j : ℕ) : ℚ) := by positivity
    nlinarith

/-- **Theorem 3.5 (Equation (3.20): Exact Rising-Factorial Binomial Formula for `Ω_B((ν + AK)²)`):**
For every integer `ν ≥ 1` and parameters `AK, BK ≥ 0`,
$$\Omega_B((\nu + AK)^2) = \binom{\nu + 2AK + BK}{BK} \binom{\nu - 1}{BK}.$$ -/
theorem theorem_3_5_binomial_identity (AK BK ν : ℕ) (hν : 1 ≤ ν) :
    OmegaB AK BK (((ν + AK : ℕ) : ℚ) ^ 2) =
      (Nat.choose (ν + 2 * AK + BK) BK : ℚ) * (Nat.choose (ν - 1) BK : ℚ) := by
  have h_prod :
      (∏ j ∈ Finset.Icc 1 BK, (((ν + AK : ℕ) : ℚ) ^ 2 - ((AK + j : ℕ) : ℚ) ^ 2)) =
        ((BK.factorial : ℚ) ^ 2) *
          (Nat.choose (ν + 2 * AK + BK) BK : ℚ) * (Nat.choose (ν - 1) BK : ℚ) := by
    induction BK with
    | zero =>
      simp
    | succ BK ih =>
      have h_icc : Finset.Icc 1 (BK + 1) = insert (BK + 1) (Finset.Icc 1 BK) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [h_icc, Finset.prod_insert (by simp)]
      rw [ih]
      have h_c1_nat :
          (BK + 1) * Nat.choose (ν + 2 * AK + (BK + 1)) (BK + 1) =
            (ν + 2 * AK + BK + 1) * Nat.choose (ν + 2 * AK + BK) BK := by
        have h_idx : ν + 2 * AK + (BK + 1) = (ν + 2 * AK + BK).succ := by omega
        rw [h_idx]
        linarith [Nat.succ_mul_choose_eq (ν + 2 * AK + BK) BK]
      have h_c1_q :
          ((BK + 1 : ℕ) : ℚ) * (Nat.choose (ν + 2 * AK + (BK + 1)) (BK + 1) : ℚ) =
            ((ν + 2 * AK + BK + 1 : ℕ) : ℚ) * (Nat.choose (ν + 2 * AK + BK) BK : ℚ) := by
        exact_mod_cast h_c1_nat
      rcases lt_or_ge (ν - 1) BK with hlt | hge
      · have hz1 : Nat.choose (ν - 1) BK = 0 := Nat.choose_eq_zero_of_lt hlt
        have hz2 : Nat.choose (ν - 1) (BK + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [hz1, hz2]
      · have h_c2 := Nat.choose_succ_right_eq (ν - 1) BK
        have h_c2_q :
            ((BK + 1 : ℕ) : ℚ) * (Nat.choose (ν - 1) (BK + 1) : ℚ) =
              (((ν - 1 : ℕ) : ℚ) - (BK : ℚ)) * (Nat.choose (ν - 1) BK : ℚ) := by
          have h_sub : (((ν - 1 - BK : ℕ) : ℚ)) = ((ν - 1 : ℕ) : ℚ) - (BK : ℚ) :=
            Nat.cast_sub hge
          rw [← h_sub, mul_comm ((BK + 1 : ℕ) : ℚ), mul_comm (((ν - 1 - BK : ℕ) : ℚ))]
          exact_mod_cast h_c2
        have h_diff_sq :
            (((ν + AK : ℕ) : ℚ) ^ 2 - ((AK + (BK + 1) : ℕ) : ℚ) ^ 2) =
              ((ν + 2 * AK + BK + 1 : ℕ) : ℚ) * (((ν - 1 : ℕ) : ℚ) - (BK : ℚ)) := by
          have h_nu1 : ((ν - 1 : ℕ) : ℚ) = (ν : ℚ) - 1 := Nat.cast_sub hν
          rw [h_nu1]
          push_cast
          ring
        have h_fac : ((BK + 1).factorial : ℚ) ^ 2 =
            ((BK + 1 : ℕ) : ℚ) ^ 2 * ((BK.factorial : ℚ) ^ 2) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        rw [h_diff_sq, h_fac]
        calc (((ν + 2 * AK + BK + 1 : ℕ) : ℚ) * (((ν - 1 : ℕ) : ℚ) - (BK : ℚ))) *
              ((BK.factorial : ℚ) ^ 2 *
                (Nat.choose (ν + 2 * AK + BK) BK : ℚ) * (Nat.choose (ν - 1) BK : ℚ))
            = ((BK.factorial : ℚ) ^ 2) *
                (((ν + 2 * AK + BK + 1 : ℕ) : ℚ) *
                  (Nat.choose (ν + 2 * AK + BK) BK : ℚ)) *
                ((((ν - 1 : ℕ) : ℚ) - (BK : ℚ)) * (Nat.choose (ν - 1) BK : ℚ)) := by ring
          _ = ((BK.factorial : ℚ) ^ 2) *
                (((BK + 1 : ℕ) : ℚ) * (Nat.choose (ν + 2 * AK + (BK + 1)) (BK + 1) : ℚ)) *
                (((BK + 1 : ℕ) : ℚ) * (Nat.choose (ν - 1) (BK + 1) : ℚ)) := by
                rw [← h_c1_q, ← h_c2_q]
          _ = ((BK + 1 : ℕ) : ℚ) ^ 2 * (BK.factorial : ℚ) ^ 2 *
                (Nat.choose (ν + 2 * AK + (BK + 1)) (BK + 1) : ℚ) *
                (Nat.choose (ν - 1) (BK + 1) : ℚ) := by ring
  unfold OmegaB
  rw [h_prod]
  have h_fac_ne : ((BK.factorial : ℚ) ^ 2) ≠ 0 :=
    pow_ne_zero 2 (by exact_mod_cast Nat.factorial_ne_zero BK)
  field_simp [h_fac_ne]
  ring

/-!
## Additional Ground-Up Proofs for Section 3 (Definition 3.1, Lemma 3.2 Eq. (3.6), Theorem 3.4 & Theorem 3.5)
-/

/-- **Definition 3.1 (Total Denominator Pole Multiplicity `∑_{k=0}^{2AK} L_k`)**:
For every `n ≥ 1` and `A₀K ≤ AK`, the total denominator degree of `ℱ_{2n+1,2}^{odd,[A₀,A]}(z; P)` is
$$\sum_{k=0}^{2AK} L_k = 4AK + 2(2n - 1)A_0 K + 2n + 1.$$ -/
theorem lemma_3_1_total_pole_multiplicity (n A0K AK : ℕ) (hn : 1 ≤ n) (hA0 : A0K ≤ AK) :
    (∑ k ∈ Finset.range (2 * AK + 1), poleMultiplicity n A0K AK k) =
      4 * AK + 2 * (2 * n - 1) * A0K + 2 * n + 1 := by
  have h_split :
      ∀ k : ℕ, poleMultiplicity n A0K AK k =
        2 + (if ((k : ℤ) - (AK : ℤ)).natAbs ≤ A0K then 2 * n - 1 else 0) := by
    intro k
    unfold poleMultiplicity
    split_ifs <;> omega
  simp_rw [h_split]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      ← Finset.sum_filter]
  let I : Finset ℕ :=
    (Finset.range (2 * AK + 1)).filter (fun (k : ℕ) => ((k : ℤ) - (AK : ℤ)).natAbs ≤ A0K)
  have hI_eq : I = Finset.Icc (AK - A0K) (AK + A0K) := by
    ext k
    simp only [I, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  have hI_card : I.card = 2 * A0K + 1 := by
    rw [hI_eq, Nat.card_Icc]
    omega
  rw [Finset.sum_const, hI_card, smul_eq_mul]
  omega

/-- **Definition 3.1 (Equation (3.1): Rational Kernel Degree Margin `deg_z ℱ ≤ -(2n + 3) ≤ -5`)**:
Whenever `satisfiesKernelDegreeBound n A0K AK degP` holds (`2 deg_u P ≤ 4AK + 2(2n - 1)A₀K - 2`),
the total denominator pole multiplicity exceeds the numerator degree `2 * degP` by at least
`2n + 3 ≥ 5`. -/
theorem lemma_3_1_degree_margin (n A0K AK degP : ℕ) (hn : 1 ≤ n) (hA0 : A0K ≤ AK)
    (h_deg : satisfiesKernelDegreeBound n A0K AK degP) :
    2 * degP + (2 * n + 3) ≤ ∑ k ∈ Finset.range (2 * AK + 1), poleMultiplicity n A0K AK k ∧
    5 ≤ 2 * n + 3 := by
  rw [lemma_3_1_total_pole_multiplicity n A0K AK hn hA0]
  unfold satisfiesKernelDegreeBound at h_deg
  omega

/-- Product of `L` consecutive positive integers `(a + 1)(a + 2)⋯(a + L)` times `a!` equals `(a + L)!`. -/
theorem prod_Icc_add_mul_factorial (a L : ℕ) :
    (∏ m ∈ Finset.Icc (a + 1) (a + L), (m : ℚ)) * (a.factorial : ℚ) =
      ((a + L).factorial : ℚ) := by
  induction L with
  | zero =>
    have h_empty : Finset.Icc (a + 1) (a + 0) = ∅ := by
      ext m; simp only [Finset.mem_Icc, Finset.not_mem_empty, iff_false]; omega
    rw [h_empty, Finset.prod_empty, one_mul, Nat.add_zero]
  | succ L ih =>
    have h_ins : Finset.Icc (a + 1) (a + (L + 1)) =
        insert (a + L + 1) (Finset.Icc (a + 1) (a + L)) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have h_not_mem : a + L + 1 ∉ Finset.Icc (a + 1) (a + L) := by
      simp only [Finset.mem_Icc]; omega
    rw [h_ins, Finset.prod_insert h_not_mem, mul_assoc, ih,
        show a + (L + 1) = (a + L) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring

theorem prod_Icc_one_eq_factorial (L : ℕ) :
    (∏ m ∈ Finset.Icc 1 L, (m : ℚ)) = (L.factorial : ℚ) := by
  have h := prod_Icc_add_mul_factorial 0 L
  simpa using h

/-- For any `0 ≤ s ≤ M`, the deleted product `∏_{0 ≤ j ≤ M, j ≠ s} (j - s)` equals
`(-1)^s · s! · (M - s)!`. -/
theorem prod_range_erase_sub_eq (M s : ℕ) (hs : s ≤ M) :
    (∏ j ∈ (Finset.range (M + 1)).erase s, ((j : ℚ) - (s : ℚ))) =
      ((-1 : ℚ) ^ s) * (s.factorial : ℚ) * ((M - s).factorial : ℚ) := by
  have h_union :
      (Finset.range (M + 1)).erase s = Finset.range s ∪ Finset.Icc (s + 1) M := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
    omega
  have h_disj : Disjoint (Finset.range s) (Finset.Icc (s + 1) M) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_range, Finset.mem_Icc] at hj1 hj2
    omega
  rw [h_union, Finset.prod_union h_disj]
  have h_left :
      (∏ j ∈ Finset.range s, ((j : ℚ) - (s : ℚ))) = ((-1 : ℚ) ^ s) * (s.factorial : ℚ) := by
    have h_bij :
        (∏ j ∈ Finset.range s, ((j : ℚ) - (s : ℚ))) =
          ∏ m ∈ Finset.Icc 1 s, (-(m : ℚ)) := by
      apply Finset.prod_bij (fun j _ => s - j)
      · intro j hj
        have hj_lt : j < s := Finset.mem_range.mp hj
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro j₁ hj₁ j₂ hj₂ h_eq
        have h1 : j₁ < s := Finset.mem_range.mp hj₁
        have h2 : j₂ < s := Finset.mem_range.mp hj₂
        omega
      · intro m hm
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        have hm2 : m ≤ s := (Finset.mem_Icc.mp hm).2
        exact ⟨s - m, Finset.mem_range.mpr (by omega), by omega⟩
      · intro j hj
        have hj_le : j ≤ s := le_of_lt (Finset.mem_range.mp hj)
        rw [Nat.cast_sub hj_le]
        ring
    have h_neg_prod :
        (∏ m ∈ Finset.Icc 1 s, (-(m : ℚ))) =
          (∏ _m ∈ Finset.Icc 1 s, (-1 : ℚ)) * (∏ m ∈ Finset.Icc 1 s, (m : ℚ)) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro m _; ring
    have h_card : (Finset.Icc 1 s).card = s := by
      rw [Nat.card_Icc]; omega
    rw [h_bij, h_neg_prod, Finset.prod_const, h_card, prod_Icc_one_eq_factorial]
  have h_right :
      (∏ j ∈ Finset.Icc (s + 1) M, ((j : ℚ) - (s : ℚ))) = ((M - s).factorial : ℚ) := by
    have h_bij :
        (∏ j ∈ Finset.Icc (s + 1) M, ((j : ℚ) - (s : ℚ))) =
          ∏ m ∈ Finset.Icc 1 (M - s), (m : ℚ) := by
      apply Finset.prod_bij (fun j _ => j - s)
      · intro j hj
        have hj1 : s + 1 ≤ j := (Finset.mem_Icc.mp hj).1
        have hj2 : j ≤ M := (Finset.mem_Icc.mp hj).2
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro j₁ hj₁ j₂ hj₂ h_eq
        have h1 : s + 1 ≤ j₁ := (Finset.mem_Icc.mp hj₁).1
        have h2 : s + 1 ≤ j₂ := (Finset.mem_Icc.mp hj₂).1
        omega
      · intro m hm
        have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
        have hm2 : m ≤ M - s := (Finset.mem_Icc.mp hm).2
        exact ⟨s + m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro j hj
        have hj1 : s ≤ j := le_trans (by omega) (Finset.mem_Icc.mp hj).1
        rw [Nat.cast_sub hj1]
    rw [h_bij, prod_Icc_one_eq_factorial]
  rw [h_left, h_right, mul_assoc]

/-- **Lemma 3.2 (Equation (3.5) at `w = 0`)**: Direct unsimplified product definition of the
leading Laurent coefficient `g_{k,0} = g_k(0)` from `(z + k)^{L_k} ℱ(z; 1)|_{z = -k}`:
$$g_k(0) = \frac{((2AK)!)^2 ((2A_0 K)!)^{2n-1}}
  {\left(\prod_{\substack{0 \le j \le 2AK \\ j \ne k}} (j - k)^2\right)
   \left(\prod_{\substack{|j - AK| \le A_0 K \\ j \ne k}} (j - k)^{2n-1}\right)}.$$ -/
def gkProductAtZero (n A0K AK k : ℕ) : ℚ :=
  let pref : ℚ := (((2 * AK).factorial : ℚ) ^ 2) * (((2 * A0K).factorial : ℚ) ^ (2 * n - 1))
  let prodOut : ℚ := ∏ j ∈ (Finset.range (2 * AK + 1)).erase k, ((j : ℚ) - (k : ℚ)) ^ 2
  let prodIn : ℚ :=
    ∏ j ∈ ((Finset.range (2 * AK + 1)).filter
      (fun (j : ℕ) => ((j : ℤ) - (AK : ℤ)).natAbs ≤ A0K)).erase k,
      ((j : ℚ) - (k : ℚ)) ^ (2 * n - 1)
  pref / (prodOut * prodIn)

/-- Product of `2A₀K + 1` consecutive integers `(r - A₀K) ⋯ (r + A₀K)` for an outer pole `r > A₀K`:
`∏_{m = r - A₀K}^{r + A₀K} m = (2A₀K)! · (r - A₀K) · C(r + A₀K, 2A₀K)`. -/
theorem prod_Icc_outer_window_eq (A0K r : ℕ) (hr : A0K < r) :
    (∏ m ∈ Finset.Icc (r - A0K) (r + A0K), (m : ℚ)) =
      ((2 * A0K).factorial : ℚ) *
        (((r - A0K : ℕ) : ℚ) * (Nat.choose (r + A0K) (2 * A0K) : ℚ)) := by
  have h_bounds :
      Finset.Icc (r - A0K) (r + A0K) =
        Finset.Icc ((r - A0K - 1) + 1) ((r - A0K - 1) + (2 * A0K + 1)) := by
    congr 1 <;> omega
  have h_prod_fac := prod_Icc_add_mul_factorial (r - A0K - 1) (2 * A0K + 1)
  rw [← h_bounds, show (r - A0K - 1) + (2 * A0K + 1) = r + A0K by omega] at h_prod_fac
  have h_choose_fac :
      (r + A0K).factorial =
        Nat.choose (r + A0K) (2 * A0K) * (2 * A0K).factorial * (r - A0K).factorial := by
    have hc := Nat.choose_mul_factorial_mul_factorial (by omega : 2 * A0K ≤ r + A0K)
    rw [show r + A0K - 2 * A0K = r - A0K by omega] at hc
    exact hc.symm
  have h_sub_fac : (r - A0K).factorial = (r - A0K) * (r - A0K - 1).factorial := by
    conv_lhs => rw [show r - A0K = (r - A0K - 1) + 1 by omega, Nat.factorial_succ]
  have h_rhs_fac :
      ((r + A0K).factorial : ℚ) =
        ((2 * A0K).factorial : ℚ) *
          (((r - A0K : ℕ) : ℚ) * (Nat.choose (r + A0K) (2 * A0K) : ℚ)) *
          ((r - A0K - 1).factorial : ℚ) := by
    rw [h_choose_fac, h_sub_fac]
    push_cast
    ring
  have h_nz : ((r - A0K - 1).factorial : ℚ) ≠ 0 :=
    by exact_mod_cast Nat.factorial_ne_zero (r - A0K - 1)
  apply mul_right_cancel₀ h_nz
  rw [h_prod_fac, h_rhs_fac]

/-- **Lemma 3.2 (Equation (3.6): Ground-Up Proof that the Unsimplified Product `g_k(0)` Equals
the Closed-Form Binomial Expression `gkZeroClosed`)**:
For every `n ≥ 1`, `A₀K ≤ AK`, and `0 ≤ k ≤ 2AK`, the product definition `gkProductAtZero`
from Equation (3.5) equals the closed-form binomial expression `gkZeroClosed` in Equation (3.6)
at both inner poles (`|k - AK| ≤ A₀K`) and outer poles (`A₀K < |k - AK| ≤ AK`). -/
theorem lemma_3_2_eq_3_6_product_eq_closed (n A0K AK k : ℕ)
    (hn : 1 ≤ n) (hA0 : A0K ≤ AK) (hk : k ≤ 2 * AK) :
    gkProductAtZero n A0K AK k = gkZeroClosed n A0K AK k := by
  unfold gkProductAtZero gkZeroClosed
  dsimp only
  -- 1. Evaluate outer product ratio ((2AK)!)^2 / ∏_{j ≠ k} (j - k)^2 = C(2AK, k)^2:
  have h_out_prod :
      (∏ j ∈ (Finset.range (2 * AK + 1)).erase k, ((j : ℚ) - (k : ℚ)) ^ 2) =
        ((k.factorial : ℚ) ^ 2) * (((2 * AK - k).factorial : ℚ) ^ 2) := by
    rw [Finset.prod_pow, prod_range_erase_sub_eq (2 * AK) k hk]
    have h_sign_sq : ((-1 : ℚ) ^ k) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm k 2, pow_mul, neg_one_sq, one_pow]
    calc ((-1 : ℚ) ^ k * (k.factorial : ℚ) * ((2 * AK - k).factorial : ℚ)) ^ 2
        = ((-1 : ℚ) ^ k) ^ 2 * ((k.factorial : ℚ) ^ 2) * (((2 * AK - k).factorial : ℚ) ^ 2) := by ring
      _ = ((k.factorial : ℚ) ^ 2) * (((2 * AK - k).factorial : ℚ) ^ 2) := by
          rw [h_sign_sq, one_mul]
  have h_out_fac :
      ((2 * AK).factorial : ℚ) =
        (Nat.choose (2 * AK) k : ℚ) * (k.factorial : ℚ) * ((2 * AK - k).factorial : ℚ) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hk).symm
  have h_out_div :
      (((2 * AK).factorial : ℚ) ^ 2) /
        (∏ j ∈ (Finset.range (2 * AK + 1)).erase k, ((j : ℚ) - (k : ℚ)) ^ 2) =
      (Nat.choose (2 * AK) k : ℚ) ^ 2 := by
    rw [h_out_prod, h_out_fac]
    have hk_ne : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hk2_ne : ((2 * AK - k).factorial : ℚ) ≠ 0 :=
      by exact_mod_cast Nat.factorial_ne_zero (2 * AK - k)
    field_simp [hk_ne, hk2_ne]
    ring
  -- 2. Identify the inner window I = Icc (AK - A0K) (AK + A0K):
  let I : Finset ℕ :=
    (Finset.range (2 * AK + 1)).filter (fun (j : ℕ) => ((j : ℤ) - (AK : ℤ)).natAbs ≤ A0K)
  have hI_eq : I = Finset.Icc (AK - A0K) (AK + A0K) := by
    ext j
    simp only [I, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  -- Split into inner pole vs outer pole:
  by_cases h_in : ((AK : ℤ) - (k : ℤ)).natAbs ≤ A0K
  · rw [if_pos h_in]
    let s : ℕ := k - (AK - A0K)
    have hs_le : s ≤ 2 * A0K := by omega
    have h_2A0_sub_s : 2 * A0K - s = A0K + AK - k := by omega
    have h_in_bij :
        (∏ j ∈ I.erase k, ((j : ℚ) - (k : ℚ))) =
          ∏ m ∈ (Finset.range (2 * A0K + 1)).erase s, ((m : ℚ) - (s : ℚ)) := by
      apply Finset.prod_bij (fun j _ => j - (AK - A0K))
      · intro j hj
        have hj_ne : j ≠ k := Finset.ne_of_mem_erase hj
        have hj_mem : j ∈ I := Finset.mem_of_mem_erase hj
        rw [hI_eq, Finset.mem_Icc] at hj_mem
        exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
      · intro j₁ hj₁ j₂ hj₂ h_eq
        have h1 : j₁ ∈ I := Finset.mem_of_mem_erase hj₁
        have h2 : j₂ ∈ I := Finset.mem_of_mem_erase hj₂
        rw [hI_eq, Finset.mem_Icc] at h1 h2
        omega
      · intro m hm
        have hm_ne : m ≠ s := Finset.ne_of_mem_erase hm
        have hm_lt : m < 2 * A0K + 1 := Finset.mem_range.mp (Finset.mem_of_mem_erase hm)
        refine ⟨(AK - A0K) + m, ?_, by omega⟩
        rw [Finset.mem_erase, hI_eq, Finset.mem_Icc]
        omega
      · intro j hj
        have hj_mem : j ∈ I := Finset.mem_of_mem_erase hj
        rw [hI_eq, Finset.mem_Icc] at hj_mem
        have hk_ge : AK - A0K ≤ k := by omega
        rw [Nat.cast_sub hj_mem.1, Nat.cast_sub hk_ge]
        ring
    have h_sign_eq : (-1 : ℚ) ^ s = (-1 : ℚ) ^ (A0K + AK - k) := by
      have h_sum_even : s + (A0K + AK - k) = 2 * A0K := by omega
      have h_prod_one : (-1 : ℚ) ^ s * (-1 : ℚ) ^ (A0K + AK - k) = 1 := by
        rw [← pow_add, h_sum_even, pow_mul, neg_one_sq, one_pow]
      have h_sq : (-1 : ℚ) ^ (A0K + AK - k) * (-1 : ℚ) ^ (A0K + AK - k) = 1 := by
        rw [← pow_add, show (A0K + AK - k) + (A0K + AK - k) = 2 * (A0K + AK - k) by ring,
            pow_mul, neg_one_sq, one_pow]
      calc (-1 : ℚ) ^ s
          = (-1 : ℚ) ^ s * 1 := (mul_one _).symm
        _ = (-1 : ℚ) ^ s * ((-1 : ℚ) ^ (A0K + AK - k) * (-1 : ℚ) ^ (A0K + AK - k)) := by rw [h_sq]
        _ = ((-1 : ℚ) ^ s * (-1 : ℚ) ^ (A0K + AK - k)) * (-1 : ℚ) ^ (A0K + AK - k) := by ring
        _ = 1 * (-1 : ℚ) ^ (A0K + AK - k) := by rw [h_prod_one]
        _ = (-1 : ℚ) ^ (A0K + AK - k) := one_mul _
    have h_odd_exp : Odd (2 * n - 1) := ⟨n - 1, by omega⟩
    have h_sign_pow : ((-1 : ℚ) ^ (A0K + AK - k)) ^ (2 * n - 1) = (-1 : ℚ) ^ (A0K + AK - k) := by
      rw [← pow_mul, mul_comm, pow_mul, h_odd_exp.neg_one_pow]
    have h_choose_abs :
        Nat.choose (2 * A0K) (A0K + ((AK : ℤ) - (k : ℤ)).natAbs) = Nat.choose (2 * A0K) s := by
      rcases le_or_gt k AK with hk_le | hk_gt
      · have h_abs_eq : A0K + ((AK : ℤ) - (k : ℤ)).natAbs = 2 * A0K - s := by omega
        rw [h_abs_eq, Nat.choose_symm hs_le]
      · congr 1
        omega
    have h_in_fac :
        ((2 * A0K).factorial : ℚ) =
          (Nat.choose (2 * A0K) (A0K + ((AK : ℤ) - (k : ℤ)).natAbs) : ℚ) *
            (s.factorial : ℚ) * (((2 * A0K - s).factorial : ℚ)) := by
      rw [h_choose_abs]
      exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hs_le).symm
    have h_in_div :
        (((2 * A0K).factorial : ℚ) ^ (2 * n - 1)) /
          (∏ j ∈ I.erase k, ((j : ℚ) - (k : ℚ)) ^ (2 * n - 1)) =
        ((-1 : ℚ) ^ (A0K + AK - k)) *
          ((Nat.choose (2 * A0K) (A0K + ((AK : ℤ) - (k : ℤ)).natAbs) : ℚ) ^ (2 * n - 1)) := by
      rw [Finset.prod_pow, h_in_bij, prod_range_erase_sub_eq (2 * A0K) s hs_le,
          h_sign_eq, h_in_fac]
      have hs1_ne : ((s.factorial : ℚ) ^ (2 * n - 1)) ≠ 0 :=
        pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero s)
      have hs2_ne : (((2 * A0K - s).factorial : ℚ) ^ (2 * n - 1)) ≠ 0 :=
        pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero (2 * A0K - s))
      have h_sgn_sq : ((-1 : ℚ) ^ (A0K + AK - k)) * ((-1 : ℚ) ^ (A0K + AK - k)) = 1 := by
        rw [← pow_add, show (A0K + AK - k) + (A0K + AK - k) = 2 * (A0K + AK - k) by ring,
            pow_mul, neg_one_sq, one_pow]
      rw [mul_pow, mul_pow, mul_pow, mul_pow, h_sign_pow]
      field_simp [hs1_ne, hs2_ne, pow_ne_zero (A0K + AK - k) (by norm_num : (-1 : ℚ) ≠ 0)]
      calc (Nat.choose (2 * A0K) (A0K + ((AK : ℤ) - (k : ℤ)).natAbs) : ℚ) ^ (2 * n - 1)
          = 1 * (Nat.choose (2 * A0K) (A0K + ((AK : ℤ) - (k : ℤ)).natAbs) : ℚ) ^ (2 * n - 1) :=
            (one_mul _).symm
        _ = ((-1 : ℚ) ^ (A0K + AK - k) * (-1 : ℚ) ^ (A0K + AK - k)) *
              (Nat.choose (2 * A0K) (A0K + ((AK : ℤ) - (k : ℤ)).natAbs) : ℚ) ^ (2 * n - 1) := by
            rw [h_sgn_sq]
        _ = (-1 : ℚ) ^ (A0K + AK - k) *
              (Nat.choose (2 * A0K) (A0K + ((AK : ℤ) - (k : ℤ)).natAbs) : ℚ) ^ (2 * n - 1) *
              (-1 : ℚ) ^ (A0K + AK - k) := by ring
    change ((((2 * AK).factorial : ℚ) ^ 2) * (((2 * A0K).factorial : ℚ) ^ (2 * n - 1))) /
        ((∏ j ∈ (Finset.range (2 * AK + 1)).erase k, ((j : ℚ) - (k : ℚ)) ^ 2) *
          (∏ j ∈ I.erase k, ((j : ℚ) - (k : ℚ)) ^ (2 * n - 1))) = _
    rw [div_mul_div_comm, h_out_div, h_in_div]
    ring
  · rw [if_neg h_in]
    have hr_gt : A0K < ((AK : ℤ) - (k : ℤ)).natAbs := not_le.mp h_in
    have hk_not_mem : k ∉ I := by
      rw [hI_eq, Finset.mem_Icc]
      omega
    have hI_erase : I.erase k = Finset.Icc (AK - A0K) (AK + A0K) := by
      rw [Finset.erase_eq_of_not_mem hk_not_mem, hI_eq]
    change ((((2 * AK).factorial : ℚ) ^ 2) * (((2 * A0K).factorial : ℚ) ^ (2 * n - 1))) /
        ((∏ j ∈ (Finset.range (2 * AK + 1)).erase k, ((j : ℚ) - (k : ℚ)) ^ 2) *
          (∏ j ∈ I.erase k, ((j : ℚ) - (k : ℚ)) ^ (2 * n - 1))) = _
    rw [div_mul_div_comm, h_out_div, hI_erase, Finset.prod_pow]
    let r_abs : ℕ := ((AK : ℤ) - (k : ℤ)).natAbs
    let outerBin : ℚ := ((r_abs - A0K : ℕ) : ℚ) * (Nat.choose (r_abs + A0K) (2 * A0K) : ℚ)
    have h_fac_ne : (((2 * A0K).factorial : ℚ) ^ (2 * n - 1)) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero (2 * A0K))
    by_cases h_lt : k < AK
    · rw [if_pos h_lt]
      have h_prod_pos :
          (∏ j ∈ Finset.Icc (AK - A0K) (AK + A0K), ((j : ℚ) - (k : ℚ))) =
            ((2 * A0K).factorial : ℚ) * outerBin := by
        have h_bij :
            (∏ j ∈ Finset.Icc (AK - A0K) (AK + A0K), ((j : ℚ) - (k : ℚ))) =
              ∏ m ∈ Finset.Icc (r_abs - A0K) (r_abs + A0K), (m : ℚ) := by
          apply Finset.prod_bij (fun j _ => j - k)
          · intro j hj
            rw [Finset.mem_Icc] at hj ⊢
            omega
          · intro j₁ hj₁ j₂ hj₂ h_eq
            rw [Finset.mem_Icc] at hj₁ hj₂
            omega
          · intro m hm
            rw [Finset.mem_Icc] at hm
            refine ⟨k + m, ?_, by omega⟩
            rw [Finset.mem_Icc]
            omega
          · intro j hj
            rw [Finset.mem_Icc] at hj
            have hk_le_j : k ≤ j := by omega
            rw [Nat.cast_sub hk_le_j]
        rw [h_bij, prod_Icc_outer_window_eq A0K r_abs hr_gt]
      rw [h_prod_pos, mul_pow, mul_div_mul_left _ _ h_fac_ne]
      ring
    · rw [if_neg h_lt]
      have h_prod_neg :
          (∏ j ∈ Finset.Icc (AK - A0K) (AK + A0K), ((j : ℚ) - (k : ℚ))) =
            - (((2 * A0K).factorial : ℚ) * outerBin) := by
        have h_bij :
            (∏ j ∈ Finset.Icc (AK - A0K) (AK + A0K), ((j : ℚ) - (k : ℚ))) =
              ∏ m ∈ Finset.Icc (r_abs - A0K) (r_abs + A0K), (-(m : ℚ)) := by
          apply Finset.prod_bij (fun j _ => k - j)
          · intro j hj
            rw [Finset.mem_Icc] at hj ⊢
            omega
          · intro j₁ hj₁ j₂ hj₂ h_eq
            rw [Finset.mem_Icc] at hj₁ hj₂
            omega
          · intro m hm
            rw [Finset.mem_Icc] at hm
            refine ⟨k - m, ?_, by omega⟩
            rw [Finset.mem_Icc]
            omega
          · intro j hj
            rw [Finset.mem_Icc] at hj
            have hj_le_k : j ≤ k := by omega
            rw [Nat.cast_sub hj_le_k]
            ring
        have h_neg_factor :
            (∏ m ∈ Finset.Icc (r_abs - A0K) (r_abs + A0K), (-(m : ℚ))) =
              (∏ _m ∈ Finset.Icc (r_abs - A0K) (r_abs + A0K), (-1 : ℚ)) *
                (∏ m ∈ Finset.Icc (r_abs - A0K) (r_abs + A0K), (m : ℚ)) := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro m _; ring
        have h_card : (Finset.Icc (r_abs - A0K) (r_abs + A0K)).card = 2 * A0K + 1 := by
          rw [Nat.card_Icc]; omega
        have h_odd_card : Odd (2 * A0K + 1) := ⟨A0K, by ring⟩
        rw [h_bij, h_neg_factor, Finset.prod_const, h_card, h_odd_card.neg_one_pow,
            prod_Icc_outer_window_eq A0K r_abs hr_gt, neg_one_mul]
      have h_odd_exp : Odd (2 * n - 1) := ⟨n - 1, by omega⟩
      rw [h_prod_neg, h_odd_exp.neg_pow, mul_pow, div_neg, mul_div_mul_left _ _ h_fac_ne]
      ring

/-- **Theorem 3.4 (Simple-Pole Harmonic Telescoping Identity, p. 18)**:
For any finite truncation `M ≥ 1` and any simple-pole residues `A₁ : ℕ → ℚ` satisfying
`∑_{k=0}^{2AK} A₁(k) = S₁(P) = 0`, the partial-fraction simple-pole sum telescopes as:
$$\sum_{k=0}^{2AK} A_1(k) \left(\sum_{\nu=1}^M \frac{1}{\nu + k}\right)
  = -\sum_{k=0}^{2AK} A_1(k) H_k^{(1)}
    + \sum_{k=0}^{2AK} A_1(k) \left(H_{M+k}^{(1)} - H_M^{(1)}\right).$$ -/
theorem theorem_3_4_simple_pole_telescoping (AK M : ℕ) (A1 : ℕ → ℚ)
    (hS1 : (∑ k ∈ Finset.range (2 * AK + 1), A1 k) = 0) :
    (∑ k ∈ Finset.range (2 * AK + 1),
      A1 k * (∑ ν ∈ Finset.Icc 1 M, (1 : ℚ) / ((ν + k : ℕ) : ℚ))) =
    (- ∑ k ∈ Finset.range (2 * AK + 1), A1 k * harmonicNumber 1 k) +
      ∑ k ∈ Finset.range (2 * AK + 1), A1 k * (harmonicNumber 1 (M + k) - harmonicNumber 1 M) := by
  have h_shift :
      ∀ k : ℕ,
        (∑ ν ∈ Finset.Icc 1 M, (1 : ℚ) / ((ν + k : ℕ) : ℚ)) =
          harmonicNumber 1 (M + k) - harmonicNumber 1 k := by
    intro k
    unfold harmonicNumber
    have h_union : Finset.Icc 1 (M + k) = Finset.Icc 1 k ∪ Finset.Icc (k + 1) (M + k) := by
      ext l; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have h_disj : Disjoint (Finset.Icc 1 k) (Finset.Icc (k + 1) (M + k)) := by
      rw [Finset.disjoint_left]
      intro l hl1 hl2; simp only [Finset.mem_Icc] at hl1 hl2; omega
    rw [h_union, Finset.sum_union h_disj, add_sub_cancel_left]
    apply Finset.sum_bij (fun ν _ => ν + k)
    · intro ν hν
      rw [Finset.mem_Icc] at hν ⊢; omega
    · intro ν₁ _ ν₂ _ h_eq; omega
    · intro l hl
      rw [Finset.mem_Icc] at hl
      exact ⟨l - k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro ν _
      simp
  simp_rw [h_shift]
  have h_cancel_HM :
      (∑ k ∈ Finset.range (2 * AK + 1), A1 k * harmonicNumber 1 M) = 0 := by
    rw [← Finset.sum_mul, hS1, zero_mul]
  calc (∑ k ∈ Finset.range (2 * AK + 1), A1 k * (harmonicNumber 1 (M + k) - harmonicNumber 1 k))
      = (- ∑ k ∈ Finset.range (2 * AK + 1), A1 k * harmonicNumber 1 k) +
          (∑ k ∈ Finset.range (2 * AK + 1), A1 k * (harmonicNumber 1 (M + k) - harmonicNumber 1 M)) +
          (∑ k ∈ Finset.range (2 * AK + 1), A1 k * harmonicNumber 1 M) := by
        simp only [mul_sub, Finset.sum_sub_distrib]
        ring
    _ = (- ∑ k ∈ Finset.range (2 * AK + 1), A1 k * harmonicNumber 1 k) +
          ∑ k ∈ Finset.range (2 * AK + 1), A1 k * (harmonicNumber 1 (M + k) - harmonicNumber 1 M) := by
        rw [h_cancel_HM, add_zero]

/-- **Theorem 3.4 (Harmonic Tail Decay Bound `0 ≤ H_{M+k}^{(1)} - H_M^{(1)} ≤ k / M`)**:
For every `M ≥ 1` and `k ≥ 0`, the harmonic tail difference satisfies
`0 ≤ H_{M+k}^{(1)} - H_M^{(1)} ≤ k / M`. -/
theorem harmonicNumber_one_diff_bound (M k : ℕ) (hM : 1 ≤ M) :
    0 ≤ harmonicNumber 1 (M + k) - harmonicNumber 1 M ∧
    harmonicNumber 1 (M + k) - harmonicNumber 1 M ≤ (k : ℚ) / (M : ℚ) := by
  unfold harmonicNumber
  have h_union : Finset.Icc 1 (M + k) = Finset.Icc 1 M ∪ Finset.Icc (M + 1) (M + k) := by
    ext l; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have h_disj : Disjoint (Finset.Icc 1 M) (Finset.Icc (M + 1) (M + k)) := by
    rw [Finset.disjoint_left]
    intro l hl1 hl2; simp only [Finset.mem_Icc] at hl1 hl2; omega
  rw [h_union, Finset.sum_union h_disj, add_sub_cancel_left]
  constructor
  · apply Finset.sum_nonneg
    intro l _
    positivity
  · have h_le :
        (∑ l ∈ Finset.Icc (M + 1) (M + k), (1 : ℚ) / ((l : ℚ) ^ 1)) ≤
          ∑ _l ∈ Finset.Icc (M + 1) (M + k), (1 : ℚ) / (M : ℚ) := by
      apply Finset.sum_le_sum
      intro l hl
      have hl_ge : M ≤ l := le_trans (by omega) (Finset.mem_Icc.mp hl).1
      rw [pow_one]
      exact one_div_le_one_div_of_le (by exact_mod_cast hM) (by exact_mod_cast hl_ge)
    have h_card : (Finset.Icc (M + 1) (M + k)).card = k := by
      rw [Nat.card_Icc]; omega
    rw [Finset.sum_const, h_card, smul_eq_mul, mul_one_div] at h_le
    exact h_le

/-- **Theorem 3.4 (Equation (3.17): Factorization of Kernel Evaluation `ℱ(ν; P) = W_K(ν) P((ν+AK)²)`):**
For every integer `ν` and polynomial evaluator `evalP`,
$$\mathcal{F}_{2n+1,2}^{\mathrm{odd},[A_0,A]}(\nu; P) = W_K(\nu) P((\nu + AK)^2).$$ -/
theorem theorem_3_4_kernel_eval_eq_WK_mul_P (n A0K AK ν : ℕ) (evalP : ℚ → ℚ) :
    windowedKernelEval n A0K AK evalP (ν : ℚ) =
      WKWeight n A0K AK ν * evalP (((ν + AK : ℕ) : ℚ) ^ 2) := by
  unfold WKWeight windowedKernelEval
  dsimp only
  rw [mul_one, Nat.cast_add]

/-- **Theorem 3.5 (Equation (3.20) Polynomial Form)**: The zero-barrier polynomial
`OmegaBPoly AK BK : Polynomial ℚ` in `ℚ[X]`:
$$\Omega_B(X) := \frac{1}{((BK)!)^2} \prod_{j=1}^{BK} \left(X - (AK + j)^2\right) \in \mathbb{Q}[X].$$ -/
noncomputable def OmegaBPoly (AK BK : ℕ) : Polynomial ℚ :=
  Polynomial.C ((1 : ℚ) / (((BK.factorial : ℚ)) ^ 2)) *
    ∏ j ∈ Finset.Icc 1 BK, (Polynomial.X - Polynomial.C (((AK + j : ℕ) : ℚ) ^ 2))

/-- **Theorem 3.5 (Evaluation and Exact Degree `deg_u Ω_B = BK` of `OmegaBPoly`)**:
For all `AK, BK ∈ ℕ` and `u ∈ ℚ`, `(OmegaBPoly AK BK).eval u = OmegaB AK BK u` and
`(OmegaBPoly AK BK).natDegree = BK`. -/
theorem theorem_3_5_OmegaBPoly_eval_and_natDegree (AK BK : ℕ) (u : ℚ) :
    (OmegaBPoly AK BK).eval u = OmegaB AK BK u ∧
    (OmegaBPoly AK BK).natDegree = BK := by
  constructor
  · unfold OmegaBPoly OmegaB
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  · unfold OmegaBPoly
    have h_c_ne : ((1 : ℚ) / (((BK.factorial : ℚ)) ^ 2)) ≠ 0 :=
      div_ne_zero one_ne_zero (pow_ne_zero 2 (by exact_mod_cast Nat.factorial_ne_zero BK))
    have h_monic :
        (∏ j ∈ Finset.Icc 1 BK,
          (Polynomial.X - Polynomial.C (((AK + j : ℕ) : ℚ) ^ 2))).Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)
    rw [Polynomial.natDegree_C_mul h_c_ne,
        Polynomial.natDegree_prod_of_monic _ _ (fun j _ => Polynomial.monic_X_sub_C _)]
    have h_deg :
        ∀ j ∈ Finset.Icc 1 BK,
          (Polynomial.X - Polynomial.C (((AK + j : ℕ) : ℚ) ^ 2)).natDegree = 1 :=
      fun j _ => Polynomial.natDegree_X_sub_C _
    rw [Finset.sum_congr rfl h_deg, Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
    omega

/-- **Theorem 3.5(ii) (Equation (3.22): Shifted-Barrier Positive-Series Truncation Identity)**:
For any multiplicity `M₀ ≥ 1`, any polynomial evaluator `evalQ : ℚ → ℚ`, and any `M ≥ BK`,
setting `evalP u := (OmegaB AK BK u) ^ M₀ * evalQ u`, all buffer terms `1 ≤ ν ≤ BK` vanish
identically, so:
$$\sum_{\nu=1}^M W_K(\nu) P((\nu + AK)^2)
  = \sum_{\nu = BK + 1}^M W_K(\nu) \Omega_B((\nu + AK)^2)^{M_0} Q((\nu + AK)^2).$$ -/
theorem theorem_3_5_ii_shifted_series_truncation (n A0K AK BK M0 M : ℕ)
    (hM0 : 1 ≤ M0) (hM : BK ≤ M) (evalQ : ℚ → ℚ) :
    let evalP : ℚ → ℚ := fun u => (OmegaB AK BK u) ^ M0 * evalQ u
    (∑ ν ∈ Finset.Icc 1 M, WKWeight n A0K AK ν * evalP (((ν + AK : ℕ) : ℚ) ^ 2)) =
      ∑ ν ∈ Finset.Icc (BK + 1) M,
        WKWeight n A0K AK ν * ((OmegaB AK BK (((ν + AK : ℕ) : ℚ) ^ 2)) ^ M0 *
          evalQ (((ν + AK : ℕ) : ℚ) ^ 2)) := by
  intro evalP
  have h_union : Finset.Icc 1 M = Finset.Icc 1 BK ∪ Finset.Icc (BK + 1) M := by
    ext ν; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have h_disj : Disjoint (Finset.Icc 1 BK) (Finset.Icc (BK + 1) M) := by
    rw [Finset.disjoint_left]
    intro ν h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega
  rw [h_union, Finset.sum_union h_disj]
  have h_buf_zero :
      (∑ ν ∈ Finset.Icc 1 BK, WKWeight n A0K AK ν * evalP (((ν + AK : ℕ) : ℚ) ^ 2)) = 0 := by
    apply Finset.sum_eq_zero
    intro ν hν
    have h1 : 1 ≤ ν := (Finset.mem_Icc.mp hν).1
    have h2 : ν ≤ BK := (Finset.mem_Icc.mp hν).2
    dsimp [evalP]
    rw [theorem_3_5_ii_vanishes_on_buffer AK BK ν h1 h2,
        zero_pow (by omega : M0 ≠ 0), zero_mul, mul_zero]
  rw [h_buf_zero, zero_add]

/-- **Lemma 3.2 (Expansion of `(X² - 2rX)^d` and Extraction of `[X^q] (X² - 2rX)^d`)**:
For any `r ∈ ℚ` and `d, q ∈ ℕ`, the coefficient of `X^q` in `(X² - 2rX)^d` equals
`(-1)^q * C(d, q - d) * (2r)^{2d - q}` when `(q + 1) / 2 ≤ d ≤ q`, and `0` otherwise. -/
theorem coeff_X_sq_sub_two_mul_pow (r : ℚ) (d q : ℕ) :
    ((Polynomial.X ^ 2 - Polynomial.C (2 * r) * Polynomial.X) ^ d).coeff q =
      if (q + 1) / 2 ≤ d ∧ d ≤ q then
        ((-1 : ℚ) ^ q) * (Nat.choose d (q - d) : ℚ) * ((2 * r) ^ (2 * d - q))
      else 0 := by
  have h_poly_eq :
      (Polynomial.X ^ 2 - Polynomial.C (2 * r) * Polynomial.X) ^ d =
        ∑ j ∈ Finset.range (d + 1),
          Polynomial.C ((Nat.choose d j : ℚ) * ((-2 * r) ^ (d - j))) * Polynomial.X ^ (d + j) := by
    have h_base :
        Polynomial.X ^ 2 - Polynomial.C (2 * r) * Polynomial.X =
          Polynomial.X * (Polynomial.X + Polynomial.C (-2 * r)) := by
      rw [Polynomial.C_neg, Polynomial.C_mul]
      ring
    rw [h_base, mul_pow, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Polynomial.C_pow, ← Polynomial.C_eq_natCast, ← Polynomial.C_mul,
        ← Polynomial.C_mul]
    ring
  rw [h_poly_eq, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs with h_cond
  · have hd1 : (q + 1) / 2 ≤ d := h_cond.1
    have hd2 : d ≤ q := h_cond.2
    rw [Finset.sum_eq_single (q - d)]
    · have h_eq : q = d + (q - d) := by omega
      rw [if_pos h_eq, mul_one, show d - (q - d) = 2 * d - q by omega]
      have h_neg : (-2 * r) ^ (2 * d - q) = ((-1 : ℚ) ^ q) * ((2 * r) ^ (2 * d - q)) := by
        rw [show (-2 * r : ℚ) = -(2 * r) by ring, neg_pow]
        have h_par : (-1 : ℚ) ^ (2 * d - q) = (-1 : ℚ) ^ q := by
          have h_exp : 2 * d - q + q = 2 * d := by omega
          have h_mul : (-1 : ℚ) ^ (2 * d - q) * (-1 : ℚ) ^ q = 1 := by
            rw [← pow_add, h_exp, pow_mul, neg_one_sq, one_pow]
          have h_qq : (-1 : ℚ) ^ q * (-1 : ℚ) ^ q = 1 := by
            rw [← pow_add, show q + q = 2 * q by ring, pow_mul, neg_one_sq, one_pow]
          calc (-1 : ℚ) ^ (2 * d - q)
              = (-1 : ℚ) ^ (2 * d - q) * 1 := (mul_one _).symm
            _ = (-1 : ℚ) ^ (2 * d - q) * ((-1 : ℚ) ^ q * (-1 : ℚ) ^ q) := by rw [h_qq]
            _ = ((-1 : ℚ) ^ (2 * d - q) * (-1 : ℚ) ^ q) * (-1 : ℚ) ^ q := by ring
            _ = 1 * (-1 : ℚ) ^ q := by rw [h_mul]
            _ = (-1 : ℚ) ^ q := one_mul _
        rw [h_par]
      rw [h_neg]
      ring
    · intro j _ hj_ne
      have h_neq : ¬(q = d + j) := by omega
      rw [if_neg h_neq, mul_zero]
    · intro h_absurd
      exact False.elim (h_absurd (Finset.mem_range.mpr (by omega)))
  · apply Finset.sum_eq_zero
    intro j hj
    have hj_lt : j < d + 1 := Finset.mem_range.mp hj
    have h_neq : ¬(q = d + j) := by omega
    rw [if_neg h_neq, mul_zero]

/-- **Lemma 3.2 (Quadratic Taylor Shift Formula for `[w^q] P((w - r)²)` in Equation (3.8))**:
For every polynomial `P ∈ ℚ[X]` and every `r ∈ ℚ` and `q ∈ ℕ`, expanding `P((X - r)²)` in powers
of `X` yields:
$$[X^q] P((X - r)^2) = (-1)^q \sum_{d = \lceil q/2 \rceil}^q
  \binom{d}{q - d} (2r)^{2d - q} [Y^d] P(Y + r^2).$$ -/
theorem lemma_3_2_poly_quadratic_shift_coeff (P : Polynomial ℚ) (r : ℚ) (q : ℕ) :
    (P.comp ((Polynomial.X - Polynomial.C r) ^ 2)).coeff q =
      ((-1 : ℚ) ^ q) *
        ∑ d ∈ Finset.Icc ((q + 1) / 2) q,
          (Nat.choose d (q - d) : ℚ) * ((2 * r) ^ (2 * d - q)) *
            (P.comp (Polynomial.X + Polynomial.C (r ^ 2))).coeff d := by
  let Q : Polynomial ℚ := P.comp (Polynomial.X + Polynomial.C (r ^ 2))
  let U : Polynomial ℚ := Polynomial.X ^ 2 - Polynomial.C (2 * r) * Polynomial.X
  have h_comp_eq : P.comp ((Polynomial.X - Polynomial.C r) ^ 2) = Q.comp U := by
    dsimp [Q, U]
    rw [Polynomial.comp_assoc]
    congr 1
    simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
    rw [← Polynomial.C_pow, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [pow_one]
    have h_2r : Polynomial.C (2 * r) = 2 * Polynomial.C r := by
      rw [Polynomial.C_mul, Polynomial.C_ofNat]
    rw [h_2r]
    ring
  let M : ℕ := max (Q.natDegree + 1) (q + 1)
  have hQ_sum : Q = ∑ d ∈ Finset.range M, Polynomial.C (Q.coeff d) * Polynomial.X ^ d := by
    rw [Polynomial.as_sum_range' Q M (le_max_left _ _)]
    apply Finset.sum_congr rfl
    intro d _
    rw [Polynomial.C_mul_X_pow_eq_monomial]
  have h_QU : Q.comp U = ∑ d ∈ Finset.range M, Polynomial.C (Q.coeff d) * U ^ d := by
    conv_lhs => rw [hQ_sum]
    simp only [Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.pow_comp, Polynomial.X_comp]
  rw [h_comp_eq, h_QU, Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul]
  have h_term :
      ∀ d ∈ Finset.range M,
        Q.coeff d * (U ^ d).coeff q =
          if d ∈ Finset.Icc ((q + 1) / 2) q then
            ((-1 : ℚ) ^ q) * ((Nat.choose d (q - d) : ℚ) * ((2 * r) ^ (2 * d - q)) * Q.coeff d)
          else 0 := by
    intro d _
    dsimp [U]
    rw [coeff_X_sq_sub_two_mul_pow r d q, Finset.mem_Icc]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl h_term, ← Finset.sum_filter]
  have h_filter_eq :
      (Finset.range M).filter (fun d => d ∈ Finset.Icc ((q + 1) / 2) q) =
        Finset.Icc ((q + 1) / 2) q := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, and_iff_right_iff_imp]
    intro hd
    have hq_lt : q < M := lt_of_lt_of_le (Nat.lt_succ_self q) (le_max_right _ _)
    omega
  rw [h_filter_eq, ← Finset.mul_sum]

end OddZetaFormalization
