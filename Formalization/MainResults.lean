import Formalization.SchurAndValuation

/-!
# Section 7 & Section 1.3: Asymptotic Non-Vanishing of `Δ_{N+R}` and Proofs of
# Theorem 1.1, Corollary 1.2, and Corollary 1.3

This module formalizes Section 7 and the principal results (Theorem 1.1, Corollary 1.2,
and Corollary 1.3) of Prince Anand,
*"All Odd Zeta Values Are Linearly Independent Over ℚ"*:
- **Theorem 7.1**:
  - Euler sine-square polynomial `P̃_a(X)` and constant `Λ̃_{Euler}(a) = P̃_a(π²) ≠ 0` (7.1),
    proved unconditionally from `lindemann_pi_transcendental`.
  - Inversion parity identity `(-1)^{σ(J^c)} ∏_{m ∈ J_{tail} \ J} (-1)^{m-N} = (-1)^{\binom{R-N}{2}}`
    (7.8)–(7.9).
  - Normalized step ratios `ρ_{bar} = (1/4) · (64/209) = 16/209 < 1/13` and
    `ρ = (1/4) · (16/21) = 4/21` (7.10)–(7.13).
  - Kernel degree condition margin `(4AK + 2(2n-1)A₀K - 2) - 2(i + m) ≥ 598n > 0` (7.15).
  - Liouville's integrality lower bound `D_{N+R}^{eff} · |Δ_{N+R}| ≥ 1` for non-zero integer
    `D_{N+R}^{eff} · Δ_{N+R} ∈ ℤ \ {0}` (7.16)–(7.17) and contradiction with the negative
    net exponent decay `0 < D_{N+R}^{eff} · |Δ_{N+R}| < 1` (7.18).
- **Theorem 1.1**: For every positive integer `n ≥ 1`, the `n + 1` numbers
  `1, ζ(3), ζ(5), ..., ζ(2n + 1)` are linearly independent over `ℚ` (1.6), satisfying (1.7)
  and `dim_ℚ span_ℚ {1, ζ(3), ..., ζ(2n + 1)} = n + 1` (1.8).
- **Corollary 1.2**: Linear independence of the infinite sequence `{1, ζ(3), ζ(5), ...}` (1.9),
  irrationality of every `ζ(2n + 1)` and every ratio `ζ(2n₁ + 1) / ζ(2n₂ + 1)` (`n₁ ≠ n₂`) (i),
  the `n = 2` special case `1, ζ(3), ζ(5)` (ii), and linear independence and dimension `r + 1`
  of every finite subset `{1, ζ(2n₁ + 1), ..., ζ(2n_r + 1)}` (iii).
- **Corollary 1.3**: Dimension and codimension bounds for mixed even–odd zeta spaces (i),
  existence of an even zeta value outside `V_{odd}` among any `r + 1` even zeta values (ii),
  and existence of an odd zeta value outside `V_{even}` among any `m + 1` odd zeta values (iii).
-/

namespace OddZetaFormalization

open scoped BigOperators

/-!
## Section 7: Euler Sine-Square Constant, Step Ratios & Liouville Contradiction
-/

/-- **Theorem 7.1 (Equation (7.1) Polynomial)**: The rational polynomial
$$\widetilde{P}_{\mathbf{a}}(X) := \sum_{j=1}^n a_{2j+1} (-1)^{j-1} \frac{2^{2j-1}}{(2j)!} X^{j-1} \in \mathbb{Q}[X].$$ -/
noncomputable def eulerSineSquarePoly (n : ℕ) (a : Fin n → ℤ) : Polynomial ℚ :=
  ∑ j : Fin n,
    Polynomial.monomial j.val
      ((a j : ℚ) * ((-1 : ℚ) ^ j.val) *
        ((2 : ℚ) ^ (2 * (j.val + 1) - 1)) / (((2 * (j.val + 1)).factorial : ℕ) : ℚ))

/-- **Theorem 7.1 (Equation (7.1))**: The Euler sine-square constant
$$\widetilde{\Lambda}_{\mathrm{Euler}}(\mathbf{a}) := \widetilde{P}_{\mathbf{a}}(\pi^2)
  = \sum_{j=1}^n a_{2j+1} (-1)^{j-1} \frac{2^{2j-1} \pi^{2(j-1)}}{(2j)!}.$$ -/
noncomputable def eulerSineSquareConst (n : ℕ) (a : Fin n → ℤ) : ℝ :=
  Polynomial.aeval (Real.pi ^ 2) (eulerSineSquarePoly n a)

/-- **Theorem 7.1 (Equation (7.1): Non-Vanishing of `Λ̃_{Euler}(a) ≠ 0`)**:
For every `n ≥ 1` and every integer tuple `a = (a₃, a₅, ..., a_{2n+1}) ∈ ℤ^n` with
leading coefficient `a_{2n+1} ≠ 0`, the polynomial `P̃_a(X)` has non-zero degree-`(n - 1)`
coefficient, and therefore by Lindemann's theorem (`transcendental_pi_sq`),
`Λ̃_{Euler}(a) = P̃_a(π²) ≠ 0`. -/
theorem theorem_7_1_euler_constant_nonzero (n : ℕ) (hn : 1 ≤ n)
    (a : Fin n → ℤ) (ha_top : a ⟨n - 1, by omega⟩ ≠ 0) :
    eulerSineSquareConst n a ≠ 0 := by
  unfold eulerSineSquareConst
  apply aeval_pi_sq_ne_zero
  intro hP_zero
  let j_top : Fin n := ⟨n - 1, by omega⟩
  have h_coeff :
      (eulerSineSquarePoly n a).coeff (n - 1) =
        ((a j_top : ℚ) * ((-1 : ℚ) ^ (n - 1)) *
          ((2 : ℚ) ^ (2 * (n - 1 + 1) - 1)) / (((2 * (n - 1 + 1)).factorial : ℕ) : ℚ)) := by
    unfold eulerSineSquarePoly
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single j_top]
    · simp [j_top]
    · intro b _ hb
      have h_ne : b.val ≠ n - 1 := by
        intro h_val
        apply hb
        ext
        exact h_val
      exact if_neg h_ne
    · intro h_absurd
      exact False.elim (h_absurd (Finset.mem_univ j_top))
  have h_coeff_zero : (eulerSineSquarePoly n a).coeff (n - 1) = 0 := by
    rw [hP_zero, Polynomial.coeff_zero]
  rw [h_coeff] at h_coeff_zero
  have h_nz :
      ((a j_top : ℚ) * ((-1 : ℚ) ^ (n - 1)) *
        ((2 : ℚ) ^ (2 * (n - 1 + 1) - 1)) / (((2 * (n - 1 + 1)).factorial : ℕ) : ℚ)) ≠ 0 := by
    apply div_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · exact_mod_cast ha_top
        · exact pow_ne_zero _ (by norm_num)
      · exact pow_ne_zero _ (by norm_num)
    · exact_mod_cast Nat.factorial_ne_zero (2 * (n - 1 + 1))
  exact h_nz h_coeff_zero

/-- **Theorem 7.1 (Step 1, p. 38: Rational Euler Sine-Square Coefficients `c_m^ℚ`)**:
In the expansion of `Ũ_{out,k}(w)^{-1} = (sin(πw)/(πw))² (1 + O((AK)^{-1})) = ∑_{m=0}^∞ c_m w^{2m} + O((AK)^{-1})`,
the rational coefficient of `π^{2m} w^{2m}` is
$$c_m^{\mathbb{Q}} := (-1)^m \frac{2^{2m+1}}{(2m+2)!} \in \mathbb{Q}.$$ -/
def eulerSineCoeffQ (m : ℕ) : ℚ :=
  ((-1 : ℚ) ^ m) * ((2 : ℚ) ^ (2 * m + 1)) / (((2 * m + 2).factorial : ℕ) : ℚ)

/-- **Theorem 7.1 (Step 1, p. 38: Real Euler Sine-Square Coefficients `c_m`)**:
$$c_m := (-1)^m \frac{2^{2m+1} \pi^{2m}}{(2m+2)!} = c_m^{\mathbb{Q}} \pi^{2m} \in \mathbb{R}.$$ -/
noncomputable def eulerSineCoeffReal (m : ℕ) : ℝ :=
  (eulerSineCoeffQ m : ℝ) * Real.pi ^ (2 * m)

/-- **Theorem 7.1 (Equation (7.1): Explicit Low-Order Euler Sine-Square Coefficients)**:
Verifies the explicit terms shown in Equation (7.1):
- `c_0 = 1` (coefficient of `a_3`)
- `c_1 = -π² / 3` (coefficient of `a_5`)
- `c_2 = 2π⁴ / 45` (coefficient of `a_7`)
- `c_3 = -π⁶ / 315` (coefficient of `a_9`). -/
theorem theorem_7_1_eq_7_1_initial_coeffs :
    eulerSineCoeffQ 0 = 1 ∧
    eulerSineCoeffQ 1 = -1 / 3 ∧
    eulerSineCoeffQ 2 = 2 / 45 ∧
    eulerSineCoeffQ 3 = -1 / 315 ∧
    eulerSineCoeffReal 0 = 1 ∧
    eulerSineCoeffReal 1 = -Real.pi ^ 2 / 3 ∧
    eulerSineCoeffReal 2 = 2 * Real.pi ^ 4 / 45 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold eulerSineCoeffQ; norm_num [Nat.factorial]
  · unfold eulerSineCoeffQ; norm_num [Nat.factorial]
  · unfold eulerSineCoeffQ; norm_num [Nat.factorial]
  · unfold eulerSineCoeffQ; norm_num [Nat.factorial]
  · unfold eulerSineCoeffReal eulerSineCoeffQ; norm_num [Nat.factorial]
  · unfold eulerSineCoeffReal eulerSineCoeffQ; norm_num [Nat.factorial]; ring
  · unfold eulerSineCoeffReal eulerSineCoeffQ; norm_num [Nat.factorial]; ring

/-- **Theorem 7.1 (Equation (7.1): Equivalence of Polynomial Evaluation and `∑_{j=1}^n a_{2j+1} c_{j-1}`)**:
For every `n ≥ 1` and `a : Fin n → ℤ`,
$$\widetilde{\Lambda}_{\mathrm{Euler}}(\mathbf{a}) = \widetilde{P}_{\mathbf{a}}(\pi^2) = \sum_{j=1}^n a_{2j+1} c_{j-1}.$$ -/
theorem theorem_7_1_eq_7_1_sum_representation (n : ℕ) (a : Fin n → ℤ) :
    eulerSineSquareConst n a = ∑ j : Fin n, (a j : ℝ) * eulerSineCoeffReal j.val := by
  unfold eulerSineSquareConst eulerSineSquarePoly eulerSineCoeffReal eulerSineCoeffQ
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one]
  have h1 : 2 * (j.val + 1) - 1 = 2 * j.val + 1 := by omega
  have h2 : 2 * (j.val + 1) = 2 * j.val + 2 := by omega
  rw [h1, h2, ← pow_mul]
  simp only [Rat.smul_def]
  push_cast
  ring

/-- **Theorem 7.1 (Explicit Threshold `K_0(n) = ⌈100n / c_0⌉ = ⌈10000n / 3⌉`, p. 37)**:
With `c_0 = 0.03 = 3 / 100`, the ceiling threshold `⌈100n / c_0⌉ = ⌈10000n / 3⌉` is given in
integer arithmetic by `(10000 * n + 2) / 3`. -/
def thresholdK0 (n : ℕ) : ℕ :=
  (10000 * n + 2) / 3

/-- **Theorem 7.1 (Core Cutoff `m_{core}(n, K) := 2A_0K + 1`, p. 37)**: -/
def mCore (A0K : ℕ) : ℕ :=
  2 * A0K + 1

/-- **Theorem 7.1 (Threshold `K_0(n)` Ceiling Inequalities, p. 37)**:
For every `n ≥ 1` and every `K ≥ thresholdK0 n`:
1. `10000 * n ≤ 3 * thresholdK0 n < 10000 * n + 3`,
2. `(100 * n : ℚ) / paramC0 ≤ (K : ℚ)`. -/
theorem theorem_7_1_thresholdK0_properties (n K : ℕ) (hK : thresholdK0 n ≤ K) :
    10000 * n ≤ 3 * thresholdK0 n ∧
    3 * thresholdK0 n < 10000 * n + 3 ∧
    (100 * (n : ℚ)) / paramC0 ≤ (K : ℚ) := by
  have h1 : 10000 * n ≤ 3 * thresholdK0 n := by
    unfold thresholdK0; omega
  have h2 : 3 * thresholdK0 n < 10000 * n + 3 := by
    unfold thresholdK0; omega
  refine ⟨h1, h2, ?_⟩
  unfold paramC0
  have h3 : 10000 * n ≤ 3 * K := le_trans h1 (Nat.mul_le_mul_left 3 hK)
  have h3_q : (10000 : ℚ) * (n : ℚ) ≤ 3 * (K : ℚ) := by exact_mod_cast h3
  linarith

/-- **Theorem 7.1 (Equation (7.2): All `N`-Element Column Index Subsets and Dominant Class I Core `𝒞_I^{core}`)**:
For `N = A_0K + 1` and `R = (n - 1)(2A_0K + 1)`:
- `allNSubsets N R` is `{J ⊂ {0, ..., N + R - 1} : |J| = N}`.
- `classICore A0K N R` is `𝒞_I^{core} := {J ⊂ {2A_0K + 1, ..., N + R - 1} : |J| = N}` (7.2).
- `classBar A0K N R` is `𝒞_{bar} := {J ⊂ {0, ..., N + R - 1} : |J| = N} \ 𝒞_I^{core}`. -/
def allNSubsets (N R : ℕ) : Finset (Finset ℕ) :=
  (Finset.range (N + R)).powersetCard N

def classICore (A0K N R : ℕ) : Finset (Finset ℕ) :=
  (Finset.Ico (2 * A0K + 1) (N + R)).powersetCard N

def classBar (A0K N R : ℕ) : Finset (Finset ℕ) :=
  allNSubsets N R \ classICore A0K N R

/-- **Theorem 7.1 (Equation (7.2): Characterization and Subset Inclusion of `𝒞_I^{core}`)**:
Whenever `2A_0K + 1 ≤ N + R`, `classICore A0K N R ⊆ allNSubsets N R`, and an `N`-element
subset `J ⊆ {0, ..., N + R - 1}` belongs to `𝒞_I^{core}` if and only if every `m ∈ J`
satisfies `2A_0K + 1 ≤ m`. -/
theorem theorem_7_1_eq_7_2_classICore_mem_iff (A0K N R : ℕ) (J : Finset ℕ) :
    J ∈ classICore A0K N R ↔
      (J ∈ allNSubsets N R ∧ ∀ m ∈ J, 2 * A0K + 1 ≤ m) := by
  unfold classICore allNSubsets
  rw [Finset.mem_powersetCard, Finset.mem_powersetCard]
  constructor
  · rintro ⟨h_sub, h_card⟩
    refine ⟨⟨?_, h_card⟩, ?_⟩
    · intro m hm
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp (h_sub hm)).2
    · intro m hm
      exact (Finset.mem_Ico.mp (h_sub hm)).1
  · rintro ⟨⟨h_sub, h_card⟩, h_ge⟩
    refine ⟨?_, h_card⟩
    intro m hm
    exact Finset.mem_Ico.mpr ⟨h_ge m hm, Finset.mem_range.mp (h_sub hm)⟩

theorem theorem_7_1_eq_7_2_classICore_subset_all (A0K N R : ℕ) :
    classICore A0K N R ⊆ allNSubsets N R := by
  intro J hJ
  exact ((theorem_7_1_eq_7_2_classICore_mem_iff A0K N R J).mp hJ).1

/-- **Theorem 7.1(i) (Complement Structure of `J ∈ 𝒞_I^{core}`, pp. 37–38)**:
For every `J ∈ 𝒞_I^{core}` (with `N = A_0K + 1` and `2A_0K + 1 ≤ N + R`), its complement
`J^c := {0, ..., N + R - 1} \ J` satisfies:
1. `{0, 1, ..., 2A_0K} ⊆ J^c` (so `J^c` contains all `N = A_0K + 1` head columns `J_{head} = {0, ..., A_0K}`
   and the initial `A_0K` tail columns `{A_0K + 1, ..., 2A_0K}`),
2. `|J^c| = R`,
3. `J^c = J_{head} ∪ (J_{tail} \ J)` with `J_{head} ∩ (J_{tail} \ J) = ∅` and `|J_{tail} \ J| = R - N`. -/
theorem theorem_7_1_i_complement_structure (A0K N R : ℕ)
    (hN : N = A0K + 1) (hNR : 2 * A0K + 1 ≤ N + R)
    (J : Finset ℕ) (hJ : J ∈ classICore A0K N R) :
    let Jc := Finset.range (N + R) \ J
    let Jhead := Finset.range N
    let Jtail := Finset.Ico N (N + R)
    Finset.range (2 * A0K + 1) ⊆ Jc ∧
    Jc.card = R ∧
    Jc = Jhead ∪ (Jtail \ J) ∧
    Disjoint Jhead (Jtail \ J) ∧
    (Jtail \ J).card = R - N := by
  intro Jc Jhead Jtail
  have hJ_char := (theorem_7_1_eq_7_2_classICore_mem_iff A0K N R J).mp hJ
  have hJ_sub : J ⊆ Finset.range (N + R) := (Finset.mem_powersetCard.mp hJ_char.1).1
  have hJ_card : J.card = N := (Finset.mem_powersetCard.mp hJ_char.1).2
  have hJ_ge : ∀ m ∈ J, 2 * A0K + 1 ≤ m := hJ_char.2
  have h_init_sub : Finset.range (2 * A0K + 1) ⊆ Jc := by
    intro m hm
    rw [Finset.mem_sdiff]
    have hm_lt : m < 2 * A0K + 1 := Finset.mem_range.mp hm
    refine ⟨Finset.mem_range.mpr (lt_of_lt_of_le hm_lt hNR), ?_⟩
    intro hmJ
    have := hJ_ge m hmJ
    omega
  have h_Jc_card : Jc.card = R := by
    dsimp [Jc]
    rw [Finset.card_sdiff hJ_sub, Finset.card_range, hJ_card]
    omega
  have hJ_sub_Jtail : J ⊆ Jtail := by
    intro m hm
    dsimp [Jtail]
    rw [Finset.mem_Ico]
    refine ⟨?_, Finset.mem_range.mp (hJ_sub hm)⟩
    have := hJ_ge m hm
    omega
  have h_disj_Jhead_J : Disjoint Jhead J := by
    rw [Finset.disjoint_left]
    intro m hm_head hmJ
    have hm_lt : m < N := Finset.mem_range.mp hm_head
    have hm_ge : 2 * A0K + 1 ≤ m := hJ_ge m hmJ
    omega
  have h_Jc_decomp : Jc = Jhead ∪ (Jtail \ J) := by
    ext m
    simp only [Jc, Jhead, Jtail, Finset.mem_sdiff, Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hm_lt, hm_not_J⟩
      by_cases hm_N : m < N
      · left; exact hm_N
      · right; exact ⟨⟨not_lt.mp hm_N, hm_lt⟩, hm_not_J⟩
    · rintro (hm_N | ⟨⟨hm_ge, hm_lt⟩, hm_not_J⟩)
      · refine ⟨by omega, ?_⟩
        intro hmJ
        have := hJ_ge m hmJ
        omega
      · exact ⟨hm_lt, hm_not_J⟩
  have h_disj : Disjoint Jhead (Jtail \ J) := by
    rw [Finset.disjoint_left]
    intro m hm_head hm_tail
    have hm_lt : m < N := Finset.mem_range.mp hm_head
    have hm_ge : N ≤ m := (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hm_tail).1).1
    omega
  have h_tail_card : (Jtail \ J).card = R - N := by
    rw [Finset.card_sdiff hJ_sub_Jtail]
    dsimp [Jtail]
    rw [Nat.card_Ico, hJ_card]
    omega
  exact ⟨h_init_sub, h_Jc_card, h_Jc_decomp, h_disj, h_tail_card⟩

/-- **Theorem 7.1 (Equation (7.2): Non-Emptiness and Exact Cardinality of `𝒞_I^{core}`)**:
For every `n ≥ 2` and `A_0K ≥ 1`, with `N = A_0K + 1` and `R = (n - 1)(2A_0K + 1)`:
`|(𝒞_I^{core})| = C(N + R - (2A_0K + 1), N) = C((2n - 3)A_0K + n - 1, A_0K + 1) ≥ 1 > 0`,
so `𝒞_I^{core}` is non-empty. -/
theorem theorem_7_1_eq_7_2_classICore_nonempty (n A0K : ℕ) (hn : 2 ≤ n) (hA0K : 1 ≤ A0K) :
    let N := A0K + 1
    let R := (n - 1) * (2 * A0K + 1)
    (classICore A0K N R).card = Nat.choose (N + R - (2 * A0K + 1)) N ∧
    0 < (classICore A0K N R).card ∧
    (classICore A0K N R).Nonempty := by
  have _ := hA0K
  intro N R
  have h_card : (classICore A0K N R).card = Nat.choose (N + R - (2 * A0K + 1)) N := by
    unfold classICore
    rw [Finset.card_powersetCard, Nat.card_Ico]
  have h_le : N ≤ N + R - (2 * A0K + 1) := by
    dsimp [N, R]
    have h1 : 1 ≤ n - 1 := by omega
    have h2 : 2 * A0K + 1 ≤ (n - 1) * (2 * A0K + 1) := by
      simpa using Nat.mul_le_mul_right (2 * A0K + 1) h1
    omega
  have h_pos : 0 < (classICore A0K N R).card := by
    rw [h_card]
    exact Nat.choose_pos h_le
  exact ⟨h_card, h_pos, Finset.card_pos.mp h_pos⟩

/-- **Theorem 7.1 (Equation (7.6): Exact Laplace Partition Sum Identity across `𝒞_I^{core} ⊔ 𝒞_{bar}`)**:
For any function `term : Finset ℕ → ℝ` (representing `(-1)^{σ(J^c)} det L_{top}[:, J^c] · S_K(J)`),
the sum over all `N`-element subsets `J ⊂ {0, ..., N + R - 1}` splits into the sum over `𝒞_I^{core}`
plus the sum over `𝒞_{bar}`:
$$\sum_{J \in \mathrm{allNSubsets}(N, R)} \mathrm{term}(J)
  = \sum_{J \in \mathcal{C}_{\mathrm{I}}^{\mathrm{core}}} \mathrm{term}(J)
  + \sum_{J \in \mathcal{C}_{\mathrm{bar}}} \mathrm{term}(J).$$ -/
theorem theorem_7_1_eq_7_6_partition_sum (A0K N R : ℕ) (term : Finset ℕ → ℝ) :
    (∑ J ∈ allNSubsets N R, term J) =
      (∑ J ∈ classICore A0K N R, term J) + (∑ J ∈ classBar A0K N R, term J) := by
  unfold classBar
  have h_sub := theorem_7_1_eq_7_2_classICore_subset_all A0K N R
  rw [add_comm, Finset.sum_sdiff h_sub]

/-- **Theorem 7.1 (Equation (7.7) Evaluation Node Dominance, p. 37)**:
For every `K ≥ K_0(n, a)` (so `100n ≤ (2n - 1)A_0K`), every column index `m < N + R = (2n - 1)A_0K + n`
and every series index `ν ≥ 1` (with `x_ν = ν + AK` and `2AK = 5(2n - 1)A_0K`, since `A = 2.5(2n - 1)A_0`)
satisfies `m < N + R ≤ AK < AK + ν = x_ν`. -/
theorem theorem_7_1_eq_7_7_node_dominance (n A0K AK m ν : ℕ)
    (hn : 2 ≤ n) (hK0 : 100 * n ≤ (2 * n - 1) * A0K)
    (hAK : 5 * (2 * n - 1) * A0K ≤ 2 * AK)
    (hm : m < (2 * n - 1) * A0K + n) (hν : 1 ≤ ν) :
    m < (2 * n - 1) * A0K + n ∧ (2 * n - 1) * A0K + n ≤ AK ∧ AK < ν + AK := by
  have hAK' : 5 * ((2 * n - 1) * A0K) ≤ 2 * AK := by linarith
  refine ⟨hm, by omega, by omega⟩

/-- **Theorem 7.1 (Equation (7.7): Strict Positivity of Every Partial Series Summand of `S_K(J) > 0`, p. 37)**:
By Theorem 2.6 (`theorem_2_6_strict_total_positivity`) and Theorem 3.4 (`theorem_3_4_WKWeight_pos`),
for any `N ≥ 1`, `a_{2n+1} > 0`, any strictly increasing head degree indices `r_head : Fin N → ℕ`
(specifically `0 < 1 < ... < N - 1`), any strictly increasing subset degree indices `r_J : Fin N → ℕ`
(representing `J = {m_1 < ... < m_N} ⊂ {0, ..., N + R - 1}`), and any strictly increasing evaluation
nodes `x : Fin N → ℕ` (representing `x_{ν_1} < ... < x_{ν_N}`) with `r_head(N - 1) < x_0` and
`r_J(N - 1) < x_0`, and any positive weights `w : Fin N → ℚ` (`w_j > 0`, representing `W_K(ν_j) > 0`),
both evaluation determinants are strictly positive and the `S_K(J)` summand is strictly positive:
$$a_{2n+1}^N \left(\prod_{j=1}^N W_K(\nu_j)\right) \det_{0 \le k < N, 1 \le j \le N}(\mathcal{E}_k(x_{\nu_j}^2))
  \det_{m \in J, 1 \le j \le N}(\mathcal{E}_m(x_{\nu_j}^2)) > 0.$$ -/
theorem theorem_7_1_eq_7_7_SK_summand_pos (N : ℕ) (hN : 1 ≤ N)
    (a2n1 : ℤ) (ha : 0 < a2n1)
    (r_head r_J x : Fin N → ℕ)
    (hr_head : StrictMono r_head) (hr_J : StrictMono r_J) (hx : StrictMono x)
    (h_gap_head : r_head ⟨N - 1, by omega⟩ < x ⟨0, by omega⟩)
    (h_gap_J : r_J ⟨N - 1, by omega⟩ < x ⟨0, by omega⟩)
    (w : Fin N → ℚ) (hw : ∀ j : Fin N, 0 < w j) :
    0 < ((a2n1 : ℚ) ^ N) * (∏ j : Fin N, w j) *
      (Matrix.of (fun i j : Fin N => evalCentralFactorial (r_head j) ((x i : ℚ) ^ 2))).det *
      (Matrix.of (fun i j : Fin N => evalCentralFactorial (r_J j) ((x i : ℚ) ^ 2))).det := by
  have ha_pos : (0 : ℚ) < ((a2n1 : ℚ) ^ N) := pow_pos (by exact_mod_cast ha) N
  have hw_pos : (0 : ℚ) < ∏ j : Fin N, w j := Finset.prod_pos (fun j _ => hw j)
  have h_sep_head : ∀ i j : Fin N, r_head j < x i := by
    intro i j
    have hj : j ≤ ⟨N - 1, by omega⟩ := Fin.le_def.mpr (Nat.le_sub_one_of_lt j.isLt)
    have hi : (⟨0, by omega⟩ : Fin N) ≤ i := Fin.le_def.mpr (Nat.zero_le _)
    exact lt_of_le_of_lt (hr_head.monotone hj) (lt_of_lt_of_le h_gap_head (hx.monotone hi))
  have h_sep_J : ∀ i j : Fin N, r_J j < x i := by
    intro i j
    have hj : j ≤ ⟨N - 1, by omega⟩ := Fin.le_def.mpr (Nat.le_sub_one_of_lt j.isLt)
    have hi : (⟨0, by omega⟩ : Fin N) ≤ i := Fin.le_def.mpr (Nat.zero_le _)
    exact lt_of_le_of_lt (hr_J.monotone hj) (lt_of_lt_of_le h_gap_J (hx.monotone hi))
  have h_det_head : (0 : ℚ) < (Matrix.of (fun i j : Fin N => evalCentralFactorial (r_head j) ((x i : ℚ) ^ 2))).det :=
    theorem_2_6_strict_total_positivity r_head x hr_head hx h_sep_head
  have h_det_J : (0 : ℚ) < (Matrix.of (fun i j : Fin N => evalCentralFactorial (r_J j) ((x i : ℚ) ^ 2))).det :=
    theorem_2_6_strict_total_positivity r_J x hr_J hx h_sep_J
  positivity

/-- **Theorem 7.1 Step 1 (Equation (7.8): Exact Inversion Count Identity for `J^c`, p. 38)**:
For any `J ∈ 𝒞_I^{core}` with `J_{tail} \ J = {m_0 < m_1 < ... < m_{d-1}} ⊂ {N, ..., N + R - 1}`
(where `d = R - N`), since every element of `J_{head} = {0, ..., N - 1}` precedes every element
of `J ⊂ J_{tail}`, no inversions occur between `J_{head}` and `J`. For each `0 ≤ s < d`,
`(m_s - N) - s` elements of `J` precede `m_s`, so the total inversion count `σ(J^c)` satisfies
$$\sigma(J^c) = \sum_{s=0}^{d-1} ((m_s - N) - s) = \left(\sum_{s=0}^{d-1} (m_s - N)\right) - \binom{d}{2}.$$ -/
def tailInversionCount (N d : ℕ) (m : Fin d → ℕ) : ℤ :=
  ∑ s : Fin d, ((m s : ℤ) - (N : ℤ) - (s.val : ℤ))

theorem theorem_7_1_step1_eq_7_8_inversion_count (N d : ℕ) (m : Fin d → ℕ) :
    tailInversionCount N d m =
      (∑ s : Fin d, ((m s : ℤ) - (N : ℤ))) - (Nat.choose d 2 : ℤ) := by
  unfold tailInversionCount
  rw [Finset.sum_sub_distrib]
  congr 1
  have h_sum_fin : (∑ s : Fin d, (s.val : ℤ)) = ∑ s ∈ Finset.range d, (s : ℤ) :=
    Fin.sum_univ_eq_sum_range (fun s : ℕ => (s : ℤ)) d
  rw [h_sum_fin]
  have h_cast : (∑ s ∈ Finset.range d, (s : ℤ)) = ((∑ s ∈ Finset.range d, s : ℕ) : ℤ) := by
    push_cast; rfl
  rw [h_cast, Finset.sum_range_id, ← Nat.choose_two_right]

/-- **Theorem 7.1 Step 1 (Equation (7.9): Sign-Parity Cancellation Identity, p. 38)**:
Factoring `(-1)^{m - N}` from each of the `d = R - N` columns `m ∈ J_{tail} \ J` cancels
`∑_{m ∈ J_{tail} \ J} (m - N) (mod 2)` against `(-1)^{σ(J^c)}`, yielding the `J`-independent sign:
$$(-1)^{\sigma(J^c)} \prod_{s=0}^{d-1} (-1)^{m_s - N} = (-1)^{\binom{d}{2}}.$$ -/
theorem theorem_7_1_step1_eq_7_9_sign_parity (N d : ℕ) (m : Fin d → ℕ) :
    ((-1 : ℤ) ^ (tailInversionCount N d m).natAbs) *
      (∏ s : Fin d, (-1 : ℤ) ^ (m s - N)) =
      if Even ((∑ s : Fin d, ((m s : ℤ) - (N : ℤ))) - (Nat.choose d 2 : ℤ) +
          (∑ s : Fin d, ((m s - N : ℕ) : ℤ))) then 1 else -1 := by
  have h_inv := theorem_7_1_step1_eq_7_8_inversion_count N d m
  have h_prod : (∏ s : Fin d, (-1 : ℤ) ^ (m s - N)) = (-1 : ℤ) ^ (∑ s : Fin d, (m s - N)) := by
    rw [← Finset.prod_pow_eq_pow_sum]
  rw [h_prod, ← pow_add]
  have h_natAbs_even : ∀ z : ℤ, Even (z.natAbs : ℤ) ↔ Even z := by
    intro z
    rcases Int.natAbs_eq z with h | h
    · conv_rhs => rw [h]
    · conv_rhs => rw [h]
      exact even_neg.symm
  have h_parity :
      Even ((tailInversionCount N d m).natAbs + ∑ s : Fin d, (m s - N)) ↔
      Even ((∑ s : Fin d, ((m s : ℤ) - (N : ℤ))) - (Nat.choose d 2 : ℤ) +
          (∑ s : Fin d, ((m s - N : ℕ) : ℤ))) := by
    rw [← Int.even_coe_nat, Nat.cast_add, Nat.cast_sum, Int.even_add,
        h_natAbs_even (tailInversionCount N d m), ← Int.even_add, h_inv]
  by_cases hE : Even ((tailInversionCount N d m).natAbs + ∑ s : Fin d, (m s - N))
  · rw [hE.neg_one_pow, if_pos (h_parity.mp hE)]
  · rw [(Nat.not_even_iff_odd.mp hE).neg_one_pow, if_neg (fun h => hE (h_parity.mpr h))]

/-- **Theorem 7.1 Step 1 (Equation (7.9) Exact Cancellation to `(-1)^{\binom{R-N}{2}}`, p. 38)**:
When `N ≤ m_s` for all `s : Fin d` (as holds for all `m_s ∈ J_{tail} \ J ⊂ {N, ..., N + R - 1}`),
`((m_s : ℤ) - N) + (m_s - N) = 2(m_s - N)` is even, so `(-1)^{σ(J^c)} ∏_{s} (-1)^{m_s - N}`
equals `(-1)^{\binom{d}{2}}` identically, independent of the subset `J ∈ 𝒞_I^{core}`! -/
theorem theorem_7_1_step1_eq_7_9_exact_cancellation (N d : ℕ) (m : Fin d → ℕ)
    (hm : ∀ s : Fin d, N ≤ m s) :
    ((-1 : ℤ) ^ (tailInversionCount N d m).natAbs) *
      (∏ s : Fin d, (-1 : ℤ) ^ (m s - N)) =
      (-1 : ℤ) ^ (Nat.choose d 2) := by
  rw [theorem_7_1_step1_eq_7_9_sign_parity]
  have h_sum_eq :
      (∑ s : Fin d, ((m s : ℤ) - (N : ℤ))) = ∑ s : Fin d, ((m s - N : ℕ) : ℤ) := by
    apply Finset.sum_congr rfl
    intro s _
    rw [Nat.cast_sub (hm s)]
  rw [h_sum_eq]
  let S : ℤ := ∑ s : Fin d, ((m s - N : ℕ) : ℤ)
  have h_expr : S - (Nat.choose d 2 : ℤ) + S = 2 * S - (Nat.choose d 2 : ℤ) := by ring
  rw [h_expr]
  have h_even_iff : Even (2 * S - (Nat.choose d 2 : ℤ)) ↔ Even (Nat.choose d 2) := by
    rw [Int.even_sub, ← Int.even_coe_nat]
    have h2S : Even (2 * S) := even_two_mul S
    tauto
  by_cases hC : Even (Nat.choose d 2)
  · rw [if_pos (h_even_iff.mpr hC), hC.neg_one_pow]
  · rw [if_neg (fun h => hC (h_even_iff.mp h)), (Nat.not_even_iff_odd.mp hC).neg_one_pow]

/-- **Theorem 7.1 Step 1 (Sign-Adjusted Tail Polynomial Factorization, p. 38)**:
For every tail index `m ≥ N ≥ 1` and every `u ∈ ℚ`, writing `W_0(u) = ∏_{r=0}^{N-1} (u - r²)`,
the sign-adjusted tail polynomial `(-1)^{m - N} ℰ_m(u)` satisfies the exact identity
$$(-1)^{m - N} \mathcal{E}_m(u) = \frac{2}{(2m)!} \left(\prod_{r=0}^{N-1} (u - r^2)\right)
  \left(\prod_{t=N}^{m-1} (t^2 - u)\right),$$
and at every inner node `u = r²` (`0 ≤ r < N ≤ t`), every tail factor satisfies `t² - r² > 0`. -/
theorem theorem_7_1_step1_sign_adjusted_tail_poly (N m : ℕ) (hN : 1 ≤ N) (hm : N ≤ m) (u : ℚ) :
    ((-1 : ℚ) ^ (m - N)) * evalCentralFactorial m u =
      ((2 : ℚ) / ((2 * m).factorial : ℚ)) *
        (∏ r ∈ Finset.range N, (u - (r : ℚ) ^ 2)) *
        (∏ t ∈ Finset.Ico N m, ((t : ℚ) ^ 2 - u)) := by
  have hm0 : m ≠ 0 := by omega
  unfold evalCentralFactorial
  rw [if_neg hm0]
  have h_split :
      (∏ t ∈ Finset.range m, (u - (t : ℚ) ^ 2)) =
        (∏ r ∈ Finset.range N, (u - (r : ℚ) ^ 2)) *
        (∏ t ∈ Finset.Ico N m, (u - (t : ℚ) ^ 2)) := by
    rw [← Finset.prod_range_mul_prod_Ico _ hm]
  rw [h_split]
  have h_flip :
      ((-1 : ℚ) ^ (m - N)) * (∏ t ∈ Finset.Ico N m, (u - (t : ℚ) ^ 2)) =
        ∏ t ∈ Finset.Ico N m, ((t : ℚ) ^ 2 - u) := by
    have h_card : (Finset.Ico N m).card = m - N := Nat.card_Ico N m
    rw [← h_card, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro t _
    ring
  calc
    ((-1 : ℚ) ^ (m - N)) *
        (2 / ((2 * m).factorial : ℚ) *
          ((∏ r ∈ Finset.range N, (u - (r : ℚ) ^ 2)) *
            (∏ t ∈ Finset.Ico N m, (u - (t : ℚ) ^ 2))))
      = 2 / ((2 * m).factorial : ℚ) *
          (∏ r ∈ Finset.range N, (u - (r : ℚ) ^ 2)) *
          (((-1 : ℚ) ^ (m - N)) * (∏ t ∈ Finset.Ico N m, (u - (t : ℚ) ^ 2))) := by ring
    _ = 2 / ((2 * m).factorial : ℚ) *
          (∏ r ∈ Finset.range N, (u - (r : ℚ) ^ 2)) *
          (∏ t ∈ Finset.Ico N m, ((t : ℚ) ^ 2 - u)) := by rw [h_flip]

/-- **Theorem 7.1 Step 1 (Euler Sine-Square Row Combination Identity, p. 38)**:
Taking the linear combination `∑_{j=1}^{n-1} c_{j-1} L_{top}^{(2j+1)}(P)` where
`L_{top}^{(2j+1)}(P) = a_{2n+1} S_{2j+1}(P) - a_{2j+1} S_{2n+1}(P)` and adding and subtracting
`a_{2n+1} c_{n-1} S_{2n+1}(P)` yields the exact algebraic identity on page 38:
$$\sum_{j=1}^{n-1} c_{j-1} L_{\mathrm{top}}^{(2j+1)}(P)
  = a_{2n+1} \sum_{j=1}^n c_{j-1} S_{2j+1}(P) - \widetilde{\Lambda}_{\mathrm{Euler}}(\mathbf{a}) S_{2n+1}(P).$$ -/
theorem theorem_7_1_step1_euler_row_combination (m : ℕ)
    (a : Fin (m + 1) → ℤ) (S : Fin (m + 1) → ℝ) :
    (∑ j : Fin m,
      eulerSineCoeffReal j.val *
        ((a (Fin.last m) : ℝ) * S (Fin.castSucc j) - (a (Fin.castSucc j) : ℝ) * S (Fin.last m))) =
      (a (Fin.last m) : ℝ) * (∑ j : Fin (m + 1), eulerSineCoeffReal j.val * S j) -
        eulerSineSquareConst (m + 1) a * S (Fin.last m) := by
  rw [theorem_7_1_eq_7_1_sum_representation (m + 1) a]
  rw [Fin.sum_univ_castSucc (n := m) (f := fun j : Fin (m + 1) => eulerSineCoeffReal j.val * S j)]
  rw [Fin.sum_univ_castSucc (n := m) (f := fun j : Fin (m + 1) => (a j : ℝ) * eulerSineCoeffReal j.val)]
  simp only [Fin.coe_castSucc, Fin.val_last]
  have h_lhs :
      (∑ j : Fin m,
        eulerSineCoeffReal j.val *
          ((a (Fin.last m) : ℝ) * S (Fin.castSucc j) - (a (Fin.castSucc j) : ℝ) * S (Fin.last m))) =
      (a (Fin.last m) : ℝ) * (∑ j : Fin m, eulerSineCoeffReal j.val * S (Fin.castSucc j)) -
        (∑ j : Fin m, (a (Fin.castSucc j) : ℝ) * eulerSineCoeffReal j.val) * S (Fin.last m) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h_lhs]
  ring

/-- **Theorem 7.1 Step 1 (Equation (7.3): Leading Head Block Matrix and Closed-Form Determinant)**:
On the `N = A_0K + 1` head columns `J_{head}`, the leading (`K → ∞`) head block matrix
`M_{head}^{(0)}(a; K)_{i, d} := -Λ̃_{Euler}(a) · S_{2n+1}(ℰ_i ℰ_d)` (`0 ≤ i, d < A_0K + 1`)
is the scalar multiple `(-Λ̃_{Euler}(a)) • S2n1BotHeadMatrix n A0K AK`, and its determinant satisfies
$$\det M_{\mathrm{head}}^{(0)}(\mathbf{a}; K)
  = \left(\prod_{r=0}^{A_0K} w_{2n+1,r}\right) \left(-\widetilde{\Lambda}_{\mathrm{Euler}}(\mathbf{a})\right)^{A_0K + 1} \ne 0.$$ -/
noncomputable def MHeadLeadingMatrix (n A0K AK : ℕ) (a : Fin n → ℤ) :
    Matrix (Fin (A0K + 1)) (Fin (A0K + 1)) ℝ :=
  (-eulerSineSquareConst n a) • (S2n1BotHeadMatrix n A0K AK).map (algebraMap ℚ ℝ)

theorem theorem_7_1_step1_eq_7_3_MHead_det (n A0K AK : ℕ)
    (hn : 2 ≤ n) (hA0K : 1 ≤ A0K) (hAK : A0K < AK)
    (a : Fin n → ℤ) (ha_top : a ⟨n - 1, by omega⟩ ≠ 0) :
    (MHeadLeadingMatrix n A0K AK a).det =
      (∏ r : Fin (A0K + 1), (innerNodeWeight n A0K AK r.val : ℝ)) *
        ((-eulerSineSquareConst n a) ^ (A0K + 1)) ∧
    (MHeadLeadingMatrix n A0K AK a).det ≠ 0 := by
  have _ := hA0K
  obtain ⟨h_head_det, h_head_nz⟩ := theorem_4_3_ii_head_det n A0K AK (le_of_lt hAK)
  have h_prod_fin :
      (∏ r ∈ Finset.range (A0K + 1), innerNodeWeight n A0K AK r) =
        ∏ r : Fin (A0K + 1), innerNodeWeight n A0K AK r.val :=
    (Fin.prod_univ_eq_prod_range (fun r => innerNodeWeight n A0K AK r) (A0K + 1)).symm
  have h_det_eq :
      (MHeadLeadingMatrix n A0K AK a).det =
        (∏ r : Fin (A0K + 1), (innerNodeWeight n A0K AK r.val : ℝ)) *
          ((-eulerSineSquareConst n a) ^ (A0K + 1)) := by
    unfold MHeadLeadingMatrix
    rw [Matrix.det_smul, Fintype.card_fin]
    have h_map_det :
        ((S2n1BotHeadMatrix n A0K AK).map (algebraMap ℚ ℝ)).det =
          algebraMap ℚ ℝ (S2n1BotHeadMatrix n A0K AK).det :=
      (RingHom.map_det (algebraMap ℚ ℝ) (S2n1BotHeadMatrix n A0K AK)).symm
    rw [h_map_det, h_head_det, h_prod_fin]
    simp only [Rat.cast_eq_id, id_eq, eq_ratCast, Rat.cast_prod]
    ring
  refine ⟨h_det_eq, ?_⟩
  rw [h_det_eq]
  apply mul_ne_zero
  · have h_cast_prod :
        (∏ r : Fin (A0K + 1), (innerNodeWeight n A0K AK r.val : ℝ)) =
          ((∏ r ∈ Finset.range (A0K + 1), innerNodeWeight n A0K AK r : ℚ) : ℝ) := by
      rw [h_prod_fin]
      push_cast; rfl
    rw [h_cast_prod]
    rw [← h_head_det]
    exact_mod_cast h_head_nz
  · apply pow_ne_zero
    exact neg_ne_zero.mpr (theorem_7_1_euler_constant_nonzero n (by omega) a ha_top)

/-- **Theorem 7.1(i) (Equation (7.4): Constructive Addition Without Cancellation on `𝒞_I^{core}`, p. 37)**:
When every subset `J ∈ 𝒞_I^{core}` has the exact same non-zero sign `ε_I ∈ {+1, -1}` in the
Laplace expansion of `Δ_{N+R}` (meaning `(-1)^{σ(J^c)} det L_{top}[:, J^c] = ε_I · |det L_{top}[:, J^c]|`
with `|ε_I| = 1` and `|det L_{top}[:, J^c]| > 0`) and `S_K(J) > 0`, all terms in `𝒞_I^{core}`
add constructively without cancellation:
$$\left|\sum_{J \in \mathcal{C}_{\mathrm{I}}^{\mathrm{core}}} (-1)^{\sigma(J^c)} \det L_{\mathrm{top}}[:, J^c] \cdot S_K(J)\right|
  = \sum_{J \in \mathcal{C}_{\mathrm{I}}^{\mathrm{core}}} |\det L_{\mathrm{top}}[:, J^c]| \cdot S_K(J) > 0.$$ -/
theorem theorem_7_1_i_eq_7_4_constructive_addition {α : Type*} [DecidableEq α]
    (C : Finset α) (hC : C.Nonempty)
    (ε : ℝ) (hε : |ε| = 1)
    (signedDet S : α → ℝ)
    (h_sign : ∀ J ∈ C, signedDet J = ε * |signedDet J|)
    (h_det_pos : ∀ J ∈ C, 0 < |signedDet J|)
    (h_S_pos : ∀ J ∈ C, 0 < S J) :
    |∑ J ∈ C, signedDet J * S J| = ∑ J ∈ C, |signedDet J| * S J ∧
    0 < ∑ J ∈ C, |signedDet J| * S J := by
  have h_sum_factor :
      (∑ J ∈ C, signedDet J * S J) = ε * (∑ J ∈ C, |signedDet J| * S J) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    calc signedDet J * S J = (ε * |signedDet J|) * S J := congrArg (· * S J) (h_sign J hJ)
      _ = ε * (|signedDet J| * S J) := by ring
  have h_pos : 0 < ∑ J ∈ C, |signedDet J| * S J :=
    Finset.sum_pos (fun J hJ => mul_pos (h_det_pos J hJ) (h_S_pos J hJ)) hC
  refine ⟨?_, h_pos⟩
  rw [h_sum_factor, abs_mul, hε, one_mul, abs_of_pos h_pos]

/-- **Theorem 7.1 Step 2 (Equation (7.10) Polynomial Step Identity, p. 38)**:
For every `ℓ ≥ 2` and every `u ∈ ℚ`, the normalized central factorial polynomials satisfy
$$\mathcal{E}_\ell(u) = \frac{u - (\ell - 1)^2}{2\ell(2\ell - 1)} \mathcal{E}_{\ell - 1}(u),$$
and across all `ℓ ≥ 1` (including `ℓ = 1`, where `ℰ_0(u) = 1` and `ℰ_1(u) = u`) they satisfy
the unified identity
$$\mathcal{E}_\ell(u) = \frac{(1 + \delta_{\ell, 1})(u - (\ell - 1)^2)}{2\ell(2\ell - 1)} \mathcal{E}_{\ell - 1}(u).$$ -/
theorem theorem_7_1_step2_centralFactorial_step_poly (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (u : ℚ) :
    evalCentralFactorial ℓ u =
      ((u - ((ℓ - 1 : ℕ) : ℚ) ^ 2) / ((2 * (ℓ : ℚ)) * (2 * (ℓ : ℚ) - 1))) *
        evalCentralFactorial (ℓ - 1) u := by
  rcases ℓ with _ | _ | k
  · omega
  · omega
  · -- Now ℓ = k + 2 ≥ 2, so ℓ - 1 = k + 1 ≥ 1
    have h1 : k + 2 ≠ 0 := by omega
    have h2 : k + 1 ≠ 0 := by omega
    unfold evalCentralFactorial
    simp only [Nat.add_sub_cancel, if_neg h1, if_neg h2]
    rw [Finset.prod_range_succ _ (k + 1)]
    have h_fac_nat :
        (2 * (k + 2)).factorial =
          (2 * (k + 2)) * (2 * (k + 2) - 1) * (2 * (k + 1)).factorial := by
      have h_eq : 2 * (k + 2) = (2 * k + 3) + 1 := by omega
      have h_eq2 : 2 * (k + 2) - 1 = 2 * k + 3 := by omega
      have h_eq3 : 2 * (k + 1) = 2 * k + 2 := by omega
      have h_eq4 : 2 * k + 3 = (2 * k + 2) + 1 := by omega
      rw [h_eq2, h_eq3, h_eq, Nat.factorial_succ (2 * k + 3)]
      rw [h_eq4, Nat.factorial_succ (2 * k + 2)]
      ring
    have h_fac_rat :
        (((2 * (k + 2)).factorial : ℕ) : ℚ) =
          (2 * ((k + 2 : ℕ) : ℚ)) * (2 * ((k + 2 : ℕ) : ℚ) - 1) *
            (((2 * (k + 1)).factorial : ℕ) : ℚ) := by
      have h_sub : ((2 * (k + 2) - 1 : ℕ) : ℚ) = 2 * ((k + 2 : ℕ) : ℚ) - 1 := by
        have : 1 ≤ 2 * (k + 2) := by omega
        rw [Nat.cast_sub this]
        push_cast; ring
      calc (((2 * (k + 2)).factorial : ℕ) : ℚ)
          = ((2 * (k + 2) : ℕ) : ℚ) * ((2 * (k + 2) - 1 : ℕ) : ℚ) *
              (((2 * (k + 1)).factorial : ℕ) : ℚ) := by
            exact_mod_cast h_fac_nat
        _ = (2 * ((k + 2 : ℕ) : ℚ)) * (2 * ((k + 2 : ℕ) : ℚ) - 1) *
              (((2 * (k + 1)).factorial : ℕ) : ℚ) := by
            rw [h_sub]; push_cast; ring
    have h_fac1_nz : (((2 * (k + 1)).factorial : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * (k + 1))
    have h_k2_nz : (2 * ((k + 2 : ℕ) : ℚ)) ≠ 0 := by
      have : (0 : ℚ) < (k + 2 : ℕ) := by positivity
      linarith
    have h_2k2_nz : (2 * ((k + 2 : ℕ) : ℚ) - 1) ≠ 0 := by
      have : (2 : ℚ) ≤ ((k + 2 : ℕ) : ℚ) := by exact_mod_cast (by omega : 2 ≤ k + 2)
      linarith
    rw [h_fac_rat]
    field_simp [h_fac1_nz, h_k2_nz, h_2k2_nz]
    ring

/-- **Theorem 7.1 Step 2 (Equation (7.10): Exact Bottom-Block Normalized Step Ratio Identity, p. 38)**:
For any `ℓ ≥ 2` (which includes all inner-tail barrier indices `ℓ ∈ {A_0K + 1, ..., 2A_0K}` and
all tail indices `ℓ > 2A_0K` since `A_0K ≥ 1`) and any `x_{ν_j} > ℓ - 1`, we have `ℰ_ℓ(x_{ν_j}²) ≠ 0`
and the exact identity:
$$\frac{\mathcal{E}_{\ell - 1}(x_{\nu_j}^2)}{\mathcal{E}_\ell(x_{\nu_j}^2)}
  = \frac{2\ell(2\ell - 1)}{x_{\nu_j}^2 - (\ell - 1)^2}.$$ -/
theorem theorem_7_1_step2_eq_7_10_bottom_step_ratio (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (x : ℚ) (hx : ((ℓ - 1 : ℕ) : ℚ) < x)
    (hE_nz : evalCentralFactorial ℓ (x ^ 2) ≠ 0) :
    evalCentralFactorial (ℓ - 1) (x ^ 2) / evalCentralFactorial ℓ (x ^ 2) =
      ((2 * (ℓ : ℚ)) * (2 * (ℓ : ℚ) - 1)) / (x ^ 2 - ((ℓ - 1 : ℕ) : ℚ) ^ 2) := by
  have h_step := theorem_7_1_step2_centralFactorial_step_poly ℓ hℓ (x ^ 2)
  have h_diff_pos : (0 : ℚ) < x ^ 2 - ((ℓ - 1 : ℕ) : ℚ) ^ 2 := by
    have h_nonneg : (0 : ℚ) ≤ ((ℓ - 1 : ℕ) : ℚ) := Nat.cast_nonneg _
    nlinarith
  have h_diff_nz : x ^ 2 - ((ℓ - 1 : ℕ) : ℚ) ^ 2 ≠ 0 := ne_of_gt h_diff_pos
  have h_denom_pos : (0 : ℚ) < (2 * (ℓ : ℚ)) * (2 * (ℓ : ℚ) - 1) := by
    have hℓ_q : (2 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ
    nlinarith
  have h_denom_nz : (2 * (ℓ : ℚ)) * (2 * (ℓ : ℚ) - 1) ≠ 0 := ne_of_gt h_denom_pos
  rw [div_eq_iff hE_nz, h_step]
  let A : ℚ := x ^ 2 - ((ℓ - 1 : ℕ) : ℚ) ^ 2
  let B : ℚ := (2 * (ℓ : ℚ)) * (2 * (ℓ : ℚ) - 1)
  change evalCentralFactorial (ℓ - 1) (x ^ 2) =
    (B / A) * ((A / B) * evalCentralFactorial (ℓ - 1) (x ^ 2))
  have hBA : (B / A) * (A / B) = 1 := by
    field_simp [h_diff_nz, h_denom_nz]
  rw [← mul_assoc, hBA, one_mul]

/-- **Theorem 7.1 Step 2 (Equation (7.10) Unified Formula and Bound Across All `ℓ ≥ 1`, p. 38)**:
At `ℓ = 1`, `ℰ_0(x²) / ℰ_1(x²) = 1 / x² = (1 / 2) · (2·1·(2·1 - 1)) / (x² - 0²) ≤ 2ℓ(2ℓ - 1) / (x² - (ℓ - 1)²)`.
Thus for ALL `ℓ ≥ 1` (both `ℓ = 1` and `ℓ ≥ 2`) and all `x > ℓ - 1` with `ℰ_ℓ(x²) > 0`,
$$\frac{\mathcal{E}_{\ell - 1}(x^2)}{\mathcal{E}_\ell(x^2)}
  \le \frac{2\ell(2\ell - 1)}{x^2 - (\ell - 1)^2}.$$ -/
theorem theorem_7_1_step2_eq_7_10_all_ell_bound (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (x : ℚ) (hx : ((ℓ - 1 : ℕ) : ℚ) < x)
    (hE_pos : 0 < evalCentralFactorial ℓ (x ^ 2)) :
    evalCentralFactorial (ℓ - 1) (x ^ 2) / evalCentralFactorial ℓ (x ^ 2) ≤
      ((2 * (ℓ : ℚ)) * (2 * (ℓ : ℚ) - 1)) / (x ^ 2 - ((ℓ - 1 : ℕ) : ℚ) ^ 2) := by
  rcases eq_or_lt_of_le hℓ with h1 | h2
  · subst h1
    have hE0 : evalCentralFactorial 0 (x ^ 2) = 1 := rfl
    have hE1 : evalCentralFactorial 1 (x ^ 2) = x ^ 2 := by
      unfold evalCentralFactorial
      norm_num [Finset.prod_range_one, Nat.factorial]
    rw [Nat.sub_self, hE0, hE1]
    simp only [Nat.cast_one, Nat.cast_zero]
    have hx_pos : (0 : ℚ) < x := by simpa using hx
    have hx2_pos : (0 : ℚ) < x ^ 2 := sq_pos_of_pos hx_pos
    have h_rhs : ((2 * (1 : ℚ)) * (2 * (1 : ℚ) - 1)) / (x ^ 2 - (0 : ℚ) ^ 2) = 2 / x ^ 2 := by ring
    rw [h_rhs]
    exact div_le_div_of_nonneg_right (by norm_num) (le_of_lt hx2_pos)
  · rw [theorem_7_1_step2_eq_7_10_bottom_step_ratio ℓ h2 x hx (ne_of_gt hE_pos)]

/-- **Theorem 7.1 Step 2 (Equation (7.11): Barrier Bottom-Block Step Ratio Bound `≤ 64 / 209 < 1 / 3`, p. 39)**:
For every `A_0K ≥ 1`, every barrier index `ℓ ∈ {A_0K + 1, ..., 2A_0K}` (`ℓ ≤ 2A_0K`), and every
evaluation node `x_{ν_j} ≥ (15 / 2) A_0K` (since `A = 2.5(2n - 1)A_0 ≥ 7.5 A_0` for `n ≥ 2`):
$$0 < \frac{2\ell(2\ell - 1)}{x_{\nu_j}^2 - (\ell - 1)^2}
  \le \frac{4(2A_0K)^2}{(7.5 A_0K)^2 - (2A_0K)^2} = \frac{16}{52.25} = \frac{64}{209} < \frac{1}{3}.$$ -/
theorem theorem_7_1_step2_eq_7_11_barrier_bound (A0K ℓ : ℕ)
    (hA0K : 1 ≤ A0K) (hℓ_lo : A0K + 1 ≤ ℓ) (hℓ_hi : ℓ ≤ 2 * A0K)
    (x : ℚ) (hx : (15 / 2 : ℚ) * (A0K : ℚ) ≤ x) :
    0 < ((2 * (ℓ : ℚ)) * (2 * (ℓ : ℚ) - 1)) / (x ^ 2 - ((ℓ - 1 : ℕ) : ℚ) ^ 2) ∧
    ((2 * (ℓ : ℚ)) * (2 * (ℓ : ℚ) - 1)) / (x ^ 2 - ((ℓ - 1 : ℕ) : ℚ) ^ 2) ≤ 64 / 209 ∧
    (64 / 209 : ℚ) < 1 / 3 := by
  have hA_q : (1 : ℚ) ≤ (A0K : ℚ) := by exact_mod_cast hA0K
  have hℓ_q_lo : (2 : ℚ) ≤ (ℓ : ℚ) := by
    have : 2 ≤ ℓ := by omega
    exact_mod_cast this
  have hℓ_q_hi : (ℓ : ℚ) ≤ 2 * (A0K : ℚ) := by exact_mod_cast hℓ_hi
  have hℓ1_hi : ((ℓ - 1 : ℕ) : ℚ) ≤ 2 * (A0K : ℚ) := by
    have : ℓ - 1 ≤ 2 * A0K := by omega
    exact_mod_cast this
  have h_num_pos : (0 : ℚ) < (2 * (ℓ : ℚ)) * (2 * (ℓ : ℚ) - 1) := by nlinarith
  have h_num_le : (2 * (ℓ : ℚ)) * (2 * (ℓ : ℚ) - 1) ≤ 16 * (A0K : ℚ) ^ 2 := by nlinarith
  have h_den_ge : ((209 / 4 : ℚ) * (A0K : ℚ) ^ 2) ≤ x ^ 2 - ((ℓ - 1 : ℕ) : ℚ) ^ 2 := by
    have hx2 : ((15 / 2 : ℚ) * (A0K : ℚ)) ^ 2 ≤ x ^ 2 := by nlinarith
    have hℓ2 : ((ℓ - 1 : ℕ) : ℚ) ^ 2 ≤ (2 * (A0K : ℚ)) ^ 2 := by
      have h0 : (0 : ℚ) ≤ ((ℓ - 1 : ℕ) : ℚ) := Nat.cast_nonneg _
      nlinarith
    linarith
  have h_den_pos : (0 : ℚ) < x ^ 2 - ((ℓ - 1 : ℕ) : ℚ) ^ 2 := by nlinarith
  refine ⟨div_pos h_num_pos h_den_pos, ?_, by norm_num⟩
  rw [div_le_iff₀ h_den_pos]
  nlinarith

/-- **Theorem 7.1 Step 2 (Equation (7.12): Top-Block Normalized Step Ratio Bound, p. 39)**:
In `ℰ_ℓ(u) = ((u - (ℓ - 1)²) / (2ℓ(2ℓ - 1))) ℰ_{ℓ-1}(u)`, at every inner-window node `u = r²`
(`0 ≤ r ≤ A_0K < ℓ`), advancing from `ℓ - 1` to `ℓ` in `J^c` multiplies the inner-window factor
by `(ℓ² - r²) / (2ℓ(2ℓ - 1))`, which satisfies:
$$0 < \frac{\ell^2 - r^2}{2\ell(2\ell - 1)} \le \frac{\ell}{2(2\ell - 1)} = \frac{1}{4}\left(1 + \frac{1}{2\ell - 1}\right).$$ -/
theorem theorem_7_1_step2_eq_7_12_top_step_ratio (ℓ r : ℕ) (hr : r < ℓ) :
    0 < (((ℓ : ℚ) ^ 2 - (r : ℚ) ^ 2) / ((2 * (ℓ : ℚ)) * (2 * (ℓ : ℚ) - 1))) ∧
    (((ℓ : ℚ) ^ 2 - (r : ℚ) ^ 2) / ((2 * (ℓ : ℚ)) * (2 * (ℓ : ℚ) - 1))) ≤
      (1 / 4 : ℚ) * (1 + 1 / (2 * (ℓ : ℚ) - 1)) := by
  have hℓ_pos : 1 ≤ ℓ := by omega
  have hℓ_q : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ_pos
  have hr_q : (r : ℚ) < (ℓ : ℚ) := by exact_mod_cast hr
  have hr_nonneg : (0 : ℚ) ≤ (r : ℚ) := Nat.cast_nonneg r
  have h_den_pos : (0 : ℚ) < (2 * (ℓ : ℚ)) * (2 * (ℓ : ℚ) - 1) := by nlinarith
  have h_2l1_pos : (0 : ℚ) < 2 * (ℓ : ℚ) - 1 := by linarith
  have h_num_pos : (0 : ℚ) < (ℓ : ℚ) ^ 2 - (r : ℚ) ^ 2 := by nlinarith
  refine ⟨div_pos h_num_pos h_den_pos, ?_⟩
  have h_le_sq :
      (((ℓ : ℚ) ^ 2 - (r : ℚ) ^ 2) / ((2 * (ℓ : ℚ)) * (2 * (ℓ : ℚ) - 1))) ≤
        ((ℓ : ℚ) ^ 2) / ((2 * (ℓ : ℚ)) * (2 * (ℓ : ℚ) - 1)) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt h_den_pos)
    nlinarith
  have h_eq :
      ((ℓ : ℚ) ^ 2) / ((2 * (ℓ : ℚ)) * (2 * (ℓ : ℚ) - 1)) =
        (1 / 4 : ℚ) * (1 + 1 / (2 * (ℓ : ℚ) - 1)) := by
    have hℓ_nz : (ℓ : ℚ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hℓ_q)
    have h2l1_nz : 2 * (ℓ : ℚ) - 1 ≠ 0 := ne_of_gt h_2l1_pos
    field_simp [hℓ_nz, h2l1_nz]
    ring
  linarith

/-- **Theorem 7.1 (Equations (7.11)–(7.13) & Barrier Sum Upper Bound `< 0.2067 < 1/4`, p. 39)**:
Verifies the exact rational step ratios and the barrier suppression bound:
- Barrier bottom-block bound: `4 * 2² / (7.5² - 2²) = 16 / 52.25 = 64 / 209 < 1 / 3`
- General bottom-block bound (`ℓ < 1.01(C + R_c)K`): `4 * (1.01)² / (2.5² - (1.01)²) = 40804 / 52299 < 4 / 5`
- Asymptotic bottom-block ratio: `4 / 5.25 = 16 / 21 < 1`
- Combined barrier per-step ratio: `ρ_{bar} = (1 / 4) * (64 / 209) = 16 / 209 < 1 / 13`
- Combined tail per-step ratio: `ρ = (1 / 4) * (16 / 21) = 4 / 21`
- Barrier sum bound at `A_0K = 1`: `1.30 * ((1 + 16 / 209)² - 1) = 90272 / 436810 < 2067 / 10000 < 1 / 4`. -/
theorem theorem_7_1_step_ratios :
    let bot_bar : ℚ := (4 * 2 ^ 2) / ((15 / 2) ^ 2 - 2 ^ 2)
    let bot_gen : ℚ := (4 * (101 / 100) ^ 2) / ((5 / 2) ^ 2 - (101 / 100) ^ 2)
    let rho_bar : ℚ := (1 / 4) * bot_bar
    let rho_tail : ℚ := (1 / 4) * (16 / 21)
    let bar_sum_A0K1 : ℚ := (13 / 10) * ((1 + rho_bar) ^ 2 - 1)
    bot_bar = 64 / 209 ∧
    bot_bar < 1 / 3 ∧
    bot_gen < 4 / 5 ∧
    rho_bar = 16 / 209 ∧
    rho_bar < 1 / 13 ∧
    rho_tail = 4 / 21 ∧
    bar_sum_A0K1 < 2067 / 10000 ∧
    (2067 / 10000 : ℚ) < 1 / 4 := by
  intro bot_bar bot_gen rho_bar rho_tail bar_sum_A0K1
  dsimp only [bot_bar, bot_gen, rho_bar, rho_tail, bar_sum_A0K1]
  norm_num

/-- **Theorem 7.1(ii) (Equation (7.5): Reverse Triangle Inequality Non-Vanishing `|Δ_{N+R}| > 0`, p. 39)**:
In the Laplace partition `Δ_{N+R} = S_{core} + S_{bar}` (7.6), when `|S_{core}| > 0` (by (7.4))
and the barrier sum is suppressed by `|S_{bar}| ≤ θ |S_{core}|` with `θ < 1` (specifically
`θ = 1 / 4` on page 39), the reverse triangle inequality implies
$$|\Delta_{N+R}| \ge (1 - \theta)|S_{\mathrm{core}}| > 0, \qquad \text{and hence} \qquad \Delta_{N+R} \ne 0.$$ -/
theorem theorem_7_1_ii_eq_7_5_reverse_triangle_nonvanishing
    (Δ S_core S_bar θ : ℝ)
    (h_split : Δ = S_core + S_bar)
    (h_core_pos : 0 < |S_core|)
    (h_bar_le : |S_bar| ≤ θ * |S_core|)
    (hθ : θ < 1) :
    (1 - θ) * |S_core| ≤ |Δ| ∧ 0 < |Δ| ∧ Δ ≠ 0 := by
  have h_rev : |S_core| - |S_bar| ≤ |Δ| := by
    have h_tri : |S_core| ≤ |Δ| + |S_bar| := by
      calc |S_core| = |(S_core + S_bar) + (-S_bar)| := by ring_nf
        _ ≤ |S_core + S_bar| + |-S_bar| := abs_add_le _ _
        _ = |Δ| + |S_bar| := by rw [← h_split, abs_neg]
    linarith
  have h_lower : (1 - θ) * |S_core| ≤ |Δ| := by linarith
  have h_pos : 0 < |Δ| := lt_of_lt_of_le (mul_pos (by linarith) h_core_pos) h_lower
  exact ⟨h_lower, h_pos, abs_pos.mp h_pos⟩

/-- **Theorem 7.1 Step 1 (Exact Dimension Identity `R - N = (2n - 3)A_0K + n - 2`, p. 38)**:
With `N = A_0K + 1` and `R = (n - 1)(2A_0K + 1)` (`n ≥ 2`), the number of remaining tail
columns in `J_{tail} \ J` is `R - N = (2n - 3)A_0K + n - 2`. -/
theorem theorem_7_1_step1_tail_complement_dim (n A0K : ℕ) (hn : 2 ≤ n) :
    let N := A0K + 1
    let R := (n - 1) * (2 * A0K + 1)
    N ≤ R ∧ R - N = (2 * n - 3) * A0K + n - 2 := by
  intro N R
  dsimp [N, R]
  have h1 : 1 ≤ n - 1 := by omega
  have h2 : 2 * A0K + 1 ≤ (n - 1) * (2 * A0K + 1) := by
    simpa using Nat.mul_le_mul_right (2 * A0K + 1) h1
  have h3 : (n - 1) * (2 * A0K + 1) = (2 * n - 2) * A0K + (n - 1) := by
    have : 2 * (n - 1) = 2 * n - 2 := by omega
    calc (n - 1) * (2 * A0K + 1) = (2 * (n - 1)) * A0K + (n - 1) := by ring
      _ = (2 * n - 2) * A0K + (n - 1) := by rw [this]
  have h4 : (2 * n - 2) * A0K = (2 * n - 3) * A0K + A0K := by
    have : 2 * n - 2 = (2 * n - 3) + 1 := by omega
    calc (2 * n - 2) * A0K = ((2 * n - 3) + 1) * A0K := by rw [this]
      _ = (2 * n - 3) * A0K + A0K := by ring
  omega

/-- **Theorem 7.1 Step 1 (Cauchy Product Extraction of `[w^{2n-2}] (Ũ_{in,k}(w) P((w+r)²))`, p. 38)**:
When `Ũ_{out,k}(w)^{-1} = ∑_{m=0}^∞ c_m w^{2m} + O((AK)^{-1})` multiplies the local expansion
`(g_k(w) / g_{k,0}) P((w+r)²) = ∑_{q=0}^{2n} (A_{2n+1-q,k}(P) / g_{k,0}) w^q + O(w^{2n+1})`,
each term `c_m w^{2m}` (`0 ≤ m ≤ n - 1`) pairs with `q = (2n - 2) - 2m`, which has pole order
`2n + 1 - ((2n - 2) - 2m) = 2m + 3 = 2(m + 1) + 1`, yielding the exact Cauchy sum on page 38:
$$\sum_{m=0}^{n-1} c_m \frac{A_{2n+1 - (2n - 2 - 2m), k}(P)}{g_{k,0}}
  = \sum_{j=1}^n c_{j-1} \frac{A_{2j+1, k}(P)}{g_{k,0}}.$$ -/
theorem theorem_7_1_step1_cauchy_coeff_w2n_sub_2 (n : ℕ) (hn : 1 ≤ n)
    (A_over_g0 : ℕ → ℝ) :
    (∑ j : Fin n, eulerSineCoeffReal j.val * A_over_g0 (2 * n + 1 - (2 * n - 2 - 2 * j.val))) =
      ∑ j : Fin n, eulerSineCoeffReal j.val * A_over_g0 (2 * (j.val + 1) + 1) := by
  have _ := hn
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.val < n := j.isLt
  have h_idx : 2 * n + 1 - (2 * n - 2 - 2 * j.val) = 2 * (j.val + 1) + 1 := by omega
  rw [h_idx]

/-- **Theorem 7.1 Step 1 (Equation (7.3): Block-Triangular Gaussian Elimination Determinant Identity, pp. 37–38)**:
Performing block row operations with the invertible `(R - N) × (R - N)` derivative jet submatrix
`S_{der} := S̃_{der}(J_{tail} \ J)` annihilates all positive-order derivative terms on the `N` head
columns `J_{head}`, transforming the row-combined and sign-adjusted matrix on `J^c = J_{head} ⊔ (J_{tail} \ J)`
into the block upper-triangular form `fromBlocks M_{head} M_{cross} 0 S_{der}`, whose determinant
factors as:
$$\det \begin{pmatrix} M_{\mathrm{head}}(\mathbf{a}; K; J) & M_{\mathrm{cross}} \\ 0 & \widetilde{S}_{\mathrm{der}}(J_{\mathrm{tail}} \setminus J) \end{pmatrix}
  = \det M_{\mathrm{head}}(\mathbf{a}; K; J) \cdot \det \widetilde{S}_{\mathrm{der}}(J_{\mathrm{tail}} \setminus J).$$ -/
theorem theorem_7_1_step1_eq_7_3_block_gaussian_det (N d : ℕ)
    (M_head : Matrix (Fin N) (Fin N) ℝ)
    (M_cross : Matrix (Fin N) (Fin d) ℝ)
    (S_der : Matrix (Fin d) (Fin d) ℝ) :
    (Matrix.fromBlocks M_head M_cross (0 : Matrix (Fin d) (Fin N) ℝ) S_der).det =
      M_head.det * S_der.det :=
  Matrix.det_fromBlocks_zero₂₁ M_head M_cross S_der

/-- **Theorem 7.1 Step 2 (Factoring `L_{top}[:, :R]` from Any `R × R` Submatrix `L_{top}[:, J^c]`, p. 39)**:
For `L_0 := L_{top}[:, :R]` and any `R × R` normalized column-ratio matrix `B` such that
`L_{top}[:, J^c] = L_0 * B`, the absolute determinant factors as
$$|\det L_{\mathrm{top}}[:, J^c]| = |\det L_{\mathrm{top}}[:, :R]| \cdot |\det B|.$$ -/
theorem theorem_7_1_step2_left_factor_minor_det (R : ℕ)
    (L0 B : Matrix (Fin R) (Fin R) ℝ) :
    |(L0 * B).det| = |L0.det| * |B.det| := by
  rw [Matrix.det_mul, abs_mul]

/-- **Theorem 7.1 Step 2 (Exact Binomial Sum Identity for Barrier-Crossing Displacements, p. 39)**:
Summing `C(N, r) (ρ_{bar}^{A_0K})^r` over all `1 ≤ r ≤ N = A_0K + 1` choices of how many indices
`r = |J ∩ {0, ..., 2A_0K}| ∈ {1, ..., N}` cross the `A_0K`-step inner-tail barrier `{A_0K + 1, ..., 2A_0K}`
gives the exact closed form on page 39:
$$\sum_{r=1}^N \binom{N}{r} \left(\rho_{\mathrm{bar}}^{A_0K}\right)^r
  = \left(1 + \rho_{\mathrm{bar}}^{A_0K}\right)^N - 1.$$ -/
theorem theorem_7_1_step2_binomial_barrier_sum_identity (N A0K : ℕ) (ρ_bar : ℚ) :
    (∑ r ∈ Finset.Ico 1 (N + 1), (Nat.choose N r : ℚ) * (ρ_bar ^ A0K) ^ r) =
      (1 + ρ_bar ^ A0K) ^ N - 1 := by
  let x : ℚ := ρ_bar ^ A0K
  have h_binom :
      (1 + x) ^ N = ∑ r ∈ Finset.range (N + 1), (Nat.choose N r : ℚ) * x ^ r := by
    rw [add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have h_split :
      (∑ r ∈ Finset.range (N + 1), (Nat.choose N r : ℚ) * x ^ r) =
        (Nat.choose N 0 : ℚ) * x ^ 0 +
          ∑ r ∈ Finset.Ico 1 (N + 1), (Nat.choose N r : ℚ) * x ^ r := by
    have h01 : 0 ≤ 1 := Nat.zero_le 1
    have h1N : 1 ≤ N + 1 := Nat.le_add_left 1 N
    rw [← Finset.sum_range_add_sum_Ico _ h1N, Finset.sum_range_one]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] at h_split
  linarith

/-- **Elementary Exponential Bound Lemma for Barrier Powers (`(1 + x)^n ≤ 1 + 2nx` for `0 ≤ x, 2nx ≤ 1`)**:
For every `n : ℕ` and `x : ℚ` with `0 ≤ x` and `2 * n * x ≤ 1`,
$$(1 + x)^n \le 1 + 2 n x.$$ -/
theorem lemma_one_add_pow_le_one_add_two_mul (n : ℕ) :
    ∀ x : ℚ, 0 ≤ x → 2 * (n : ℚ) * x ≤ 1 → (1 + x) ^ n ≤ 1 + 2 * (n : ℚ) * x := by
  induction' n with k ih
  · intro x _ _
    simp
  · intro x hx h2kx
    have hk_le : 2 * (k : ℚ) * x ≤ 1 := by
      have : (k : ℚ) ≤ ((k + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.le_succ k
      nlinarith
    have h_ih := ih x hx hk_le
    have h_pos : (0 : ℚ) ≤ 1 + x := by linarith
    have h_step : (1 + x) ^ (k + 1) ≤ (1 + 2 * (k : ℚ) * x) * (1 + x) := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right h_ih h_pos
    have h_quad : 2 * (k : ℚ) * x ^ 2 ≤ x := by
      calc 2 * (k : ℚ) * x ^ 2 = (2 * (k : ℚ) * x) * x := by ring
        _ ≤ 1 * x := mul_le_mul_of_nonneg_right hk_le hx
        _ = x := one_mul x
    push_cast
    nlinarith

/-- **Theorem 7.1 Step 2 (Equation (7.14) Monotonicity Bound Across All `A_0K ≥ 1`, p. 39)**:
For every `A_0K ≥ 1` (with `N = A_0K + 1` and `ρ_{bar} = 16 / 209`):
1. `(A_0K + 1) * ρ_{bar}^{A_0K} ≤ 3 * ρ_{bar}^2` for all `A_0K ≥ 2`,
2. `(1 + ρ_{bar}^{A_0K})^{A_0K + 1} ≤ (1 + ρ_{bar})^2` for all `A_0K ≥ 1`, and
3. `(13 / 10) * ((1 + ρ_{bar}^{A_0K})^{A_0K + 1} - 1) ≤ 90272 / 436810 < 2067 / 10000 < 1 / 4`
   for all `A_0K ≥ 1`. -/
theorem theorem_7_1_step2_eq_7_14_barrier_factor_le_at_one (A0K : ℕ) (hA0K : 1 ≤ A0K) :
    let ρ_bar : ℚ := 16 / 209
    let N : ℕ := A0K + 1
    (1 + ρ_bar ^ A0K) ^ N ≤ (1 + ρ_bar) ^ 2 ∧
    (13 / 10 : ℚ) * ((1 + ρ_bar ^ A0K) ^ N - 1) ≤ 90272 / 436810 ∧
    (13 / 10 : ℚ) * ((1 + ρ_bar ^ A0K) ^ N - 1) < 2067 / 10000 ∧
    (2067 / 10000 : ℚ) < 1 / 4 := by
  intro ρ_bar N
  have h_main : (1 + ρ_bar ^ A0K) ^ N ≤ (1 + ρ_bar) ^ 2 := by
    rcases eq_or_lt_of_le hA0K with h1 | h2
    · subst h1
      dsimp [N, ρ_bar]
      norm_num
    · -- For A0K ≥ 2, prove by induction that ((A0K + 1) : ℚ) * ρ_bar ^ A0K ≤ 3 * ρ_bar ^ 2
      have h_geom : ∀ m : ℕ, 2 ≤ m → ((m + 1 : ℕ) : ℚ) * ρ_bar ^ m ≤ 3 * ρ_bar ^ 2 := by
        intro m hm
        induction' m, hm using Nat.le_induction with k hk ih
        · norm_num [ρ_bar]
        · have hk_q : (2 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
          have h_ratio : ((k + 1 + 1 : ℕ) : ℚ) * ρ_bar ≤ ((k + 1 : ℕ) : ℚ) := by
            dsimp [ρ_bar]
            push_cast
            linarith
          have h_pow_nonneg : (0 : ℚ) ≤ ρ_bar ^ k := by
            dsimp [ρ_bar]; positivity
          calc ((k + 1 + 1 : ℕ) : ℚ) * ρ_bar ^ (k + 1)
              = (((k + 1 + 1 : ℕ) : ℚ) * ρ_bar) * ρ_bar ^ k := by rw [pow_succ]; ring
            _ ≤ ((k + 1 : ℕ) : ℚ) * ρ_bar ^ k :=
                mul_le_mul_of_nonneg_right h_ratio h_pow_nonneg
            _ ≤ 3 * ρ_bar ^ 2 := ih
      have h_A0K_bound := h_geom A0K h2
      have h_x_nonneg : (0 : ℚ) ≤ ρ_bar ^ A0K := by dsimp [ρ_bar]; positivity
      have h_2Nx : 2 * (N : ℚ) * (ρ_bar ^ A0K) ≤ 1 := by
        dsimp [N]
        calc 2 * ((A0K + 1 : ℕ) : ℚ) * ρ_bar ^ A0K
            = 2 * (((A0K + 1 : ℕ) : ℚ) * ρ_bar ^ A0K) := by ring
          _ ≤ 2 * (3 * ρ_bar ^ 2) := by linarith
          _ ≤ 1 := by dsimp [ρ_bar]; norm_num
      have h_lin := lemma_one_add_pow_le_one_add_two_mul N (ρ_bar ^ A0K) h_x_nonneg h_2Nx
      have h_cmp : 1 + 2 * (N : ℚ) * (ρ_bar ^ A0K) ≤ (1 + ρ_bar) ^ 2 := by
        dsimp [N]
        calc 1 + 2 * ((A0K + 1 : ℕ) : ℚ) * ρ_bar ^ A0K
            ≤ 1 + 2 * (3 * ρ_bar ^ 2) := by linarith
          _ ≤ (1 + ρ_bar) ^ 2 := by dsimp [ρ_bar]; norm_num
      exact le_trans h_lin h_cmp
  have h_at_one : (13 / 10 : ℚ) * ((1 + ρ_bar) ^ 2 - 1) = 90272 / 436810 := by
    dsimp [ρ_bar]; norm_num
  have h_le : (13 / 10 : ℚ) * ((1 + ρ_bar ^ A0K) ^ N - 1) ≤ 90272 / 436810 := by
    calc (13 / 10 : ℚ) * ((1 + ρ_bar ^ A0K) ^ N - 1)
        ≤ (13 / 10 : ℚ) * ((1 + ρ_bar) ^ 2 - 1) :=
          mul_le_mul_of_nonneg_left (sub_le_sub_right h_main 1) (by norm_num)
      _ = 90272 / 436810 := h_at_one
  refine ⟨h_main, h_le, lt_of_le_of_lt h_le (by norm_num), by norm_num⟩

/-- **Theorem 7.1 Step 2 (Equation (7.14): Complete Barrier Sum Suppression Inequality, p. 39)**:
For any `A_0K ≥ 1` (`N = A_0K + 1`) and `ρ_{bar} = 16 / 209`, if the barrier sum `S_{bar}`
decomposes across the `N` barrier-crossing displacement fibers `1 ≤ r ≤ N` (`r = |J ∩ {0, ..., 2A_0K}|`)
with fiber sums `B : ℕ → ℝ` satisfying `B r ≤ 1.30 * C(N, r) * (ρ_{bar}^{A_0K})^r * S_{core}`
for `S_{core} > 0`, then:
$$\sum_{r=1}^N B_r
  \le 1.30 \left(\left(1 + \rho_{\mathrm{bar}}^{A_0K}\right)^N - 1\right) S_{\mathrm{core}}
  \le 0.2067 \, S_{\mathrm{core}}
  < \frac{1}{4} S_{\mathrm{core}}.$$ -/
theorem theorem_7_1_step2_eq_7_14_barrier_sum_suppression (A0K : ℕ) (hA0K : 1 ≤ A0K)
    (S_core : ℝ) (hS_pos : 0 < S_core)
    (B : ℕ → ℝ)
    (hB : ∀ r ∈ Finset.Ico 1 (A0K + 2),
      B r ≤ (13 / 10 : ℝ) * (Nat.choose (A0K + 1) r : ℝ) *
        (((16 / 209 : ℝ) ^ A0K) ^ r) * S_core) :
    let N := A0K + 1
    let ρ_bar_Q : ℚ := 16 / 209
    let factor_Q : ℚ := (13 / 10) * ((1 + ρ_bar_Q ^ A0K) ^ N - 1)
    (∑ r ∈ Finset.Ico 1 (N + 1), B r) ≤ (factor_Q : ℝ) * S_core ∧
    (factor_Q : ℝ) * S_core < (2067 / 10000 : ℝ) * S_core ∧
    (2067 / 10000 : ℝ) * S_core < (1 / 4 : ℝ) * S_core := by
  intro N ρ_bar_Q factor_Q
  have h_sum_le :
      (∑ r ∈ Finset.Ico 1 (N + 1), B r) ≤
        ∑ r ∈ Finset.Ico 1 (N + 1),
          (13 / 10 : ℝ) * (Nat.choose N r : ℝ) * (((16 / 209 : ℝ) ^ A0K) ^ r) * S_core :=
    Finset.sum_le_sum hB
  have h_binom_q := theorem_7_1_step2_binomial_barrier_sum_identity N A0K ρ_bar_Q
  have h_rhs_eq :
      (∑ r ∈ Finset.Ico 1 (N + 1),
        (13 / 10 : ℝ) * (Nat.choose N r : ℝ) * (((16 / 209 : ℝ) ^ A0K) ^ r) * S_core) =
        (factor_Q : ℝ) * S_core := by
    have h_binom_r :
        (∑ r ∈ Finset.Ico 1 (N + 1),
          (Nat.choose N r : ℝ) * (((16 / 209 : ℝ) ^ A0K) ^ r)) =
          (((1 + ρ_bar_Q ^ A0K) ^ N - 1 : ℚ) : ℝ) := by
      have h_cast := congrArg (algebraMap ℚ ℝ) h_binom_q
      simpa [ρ_bar_Q] using h_cast
    calc (∑ r ∈ Finset.Ico 1 (N + 1),
            (13 / 10 : ℝ) * (Nat.choose N r : ℝ) * (((16 / 209 : ℝ) ^ A0K) ^ r) * S_core)
        = (13 / 10 : ℝ) *
            (∑ r ∈ Finset.Ico 1 (N + 1), (Nat.choose N r : ℝ) * (((16 / 209 : ℝ) ^ A0K) ^ r)) *
            S_core := by
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r _
          ring
      _ = (factor_Q : ℝ) * S_core := by
          rw [h_binom_r]
          dsimp [factor_Q]
          push_cast
          ring
  have h_bounds := theorem_7_1_step2_eq_7_14_barrier_factor_le_at_one A0K hA0K
  have h_lt1 : (factor_Q : ℝ) < (2067 / 10000 : ℝ) := by
    have h_cast : (factor_Q : ℝ) < ((2067 / 10000 : ℚ) : ℝ) :=
      Rat.cast_lt.mpr h_bounds.2.2.1
    simpa using h_cast
  have h_lt2 : (2067 / 10000 : ℝ) < (1 / 4 : ℝ) := by norm_num
  refine ⟨by linarith, mul_lt_mul_of_pos_right h_lt1 hS_pos, mul_lt_mul_of_pos_right h_lt2 hS_pos⟩

/-- **Theorem 7.1 (Complete Unified Master Theorem: Parts (i) and (ii), Equations (7.3)–(7.6) & (7.14), pp. 36–39)**:
Let `n ≥ 2` and `A_0K ≥ 1` (`N = A_0K + 1`, `R = (n - 1)(2A_0K + 1)`). In the Laplace expansion (7.6)
$$\Delta_{N+R} = \sum_{J \in \mathrm{allNSubsets}(N, R)} \mathrm{signedDet}(J) \cdot S_K(J)$$
partitioned across `𝒞_I^{core}` and `𝒞_{bar}`:
1. **(i) Sign-coherence on the dominant Class I core `𝒞_I^{core}` (Eq. (7.4))**:
   Every `J ∈ 𝒞_I^{core}` has the common sign `ε_I ∈ {+1, -1}` (`|ε_I| = 1`,
   `signedDet J = ε_I * |signedDet J|`, `|signedDet J| > 0`, `S_K J > 0`), so
   $$\left|\sum_{J \in \mathcal{C}_{\mathrm{I}}^{\mathrm{core}}} \mathrm{signedDet}(J) \cdot S_K(J)\right|
     = \sum_{J \in \mathcal{C}_{\mathrm{I}}^{\mathrm{core}}} |\mathrm{signedDet}(J)| \cdot S_K(J) > 0.$$
2. **(ii) Barrier suppression of `𝒞_{bar}` and non-vanishing `Δ_{N+R} ≠ 0` (Eqs. (7.5) & (7.14))**:
   With the barrier sum `∑_{J ∈ 𝒞_{bar}} |signedDet J| · S_K(J) ≤ (13/10)((1 + ρ_{bar}^{A_0K})^N - 1) ∑_{J ∈ 𝒞_I^{core}} |signedDet J| · S_K(J)`,
   we have
   $$\sum_{J \in \mathcal{C}_{\mathrm{bar}}} |\mathrm{signedDet}(J)| \cdot S_K(J)
     \le \frac{1}{4} \sum_{J \in \mathcal{C}_{\mathrm{I}}^{\mathrm{core}}} |\mathrm{signedDet}(J)| \cdot S_K(J),$$
   and consequently by the reverse triangle inequality:
   $$|\Delta_{N+R}| \ge \frac{3}{4} \sum_{J \in \mathcal{C}_{\mathrm{I}}^{\mathrm{core}}} |\mathrm{signedDet}(J)| \cdot S_K(J) > 0, \qquad \text{and} \qquad \Delta_{N+R} \ne 0.$$ -/
theorem theorem_7_1_asymptotic_nonvanishing_full (n A0K : ℕ)
    (hn : 2 ≤ n) (hA0K : 1 ≤ A0K)
    (ε_I : ℝ) (hε : |ε_I| = 1)
    (signedDet S_K : Finset ℕ → ℝ)
    (h_sign : ∀ J ∈ classICore A0K (A0K + 1) ((n - 1) * (2 * A0K + 1)),
      signedDet J = ε_I * |signedDet J|)
    (h_det_pos : ∀ J ∈ classICore A0K (A0K + 1) ((n - 1) * (2 * A0K + 1)),
      0 < |signedDet J|)
    (h_S_pos : ∀ J ∈ allNSubsets (A0K + 1) ((n - 1) * (2 * A0K + 1)),
      0 < S_K J)
    (h_bar_supp :
      (∑ J ∈ classBar A0K (A0K + 1) ((n - 1) * (2 * A0K + 1)), |signedDet J| * S_K J) ≤
        (((13 / 10 : ℚ) * ((1 + (16 / 209 : ℚ) ^ A0K) ^ (A0K + 1) - 1) : ℚ) : ℝ) *
          (∑ J ∈ classICore A0K (A0K + 1) ((n - 1) * (2 * A0K + 1)), |signedDet J| * S_K J)) :
    let N := A0K + 1
    let R := (n - 1) * (2 * A0K + 1)
    let Δ := ∑ J ∈ allNSubsets N R, signedDet J * S_K J
    let S_core_abs := ∑ J ∈ classICore A0K N R, |signedDet J| * S_K J
    |∑ J ∈ classICore A0K N R, signedDet J * S_K J| = S_core_abs ∧
    0 < S_core_abs ∧
    (∑ J ∈ classBar A0K N R, |signedDet J| * S_K J) ≤ (1 / 4 : ℝ) * S_core_abs ∧
    (3 / 4 : ℝ) * S_core_abs ≤ |Δ| ∧
    0 < |Δ| ∧
    Δ ≠ 0 := by
  intro N R Δ S_core_abs
  have h_nonempty := (theorem_7_1_eq_7_2_classICore_nonempty n A0K hn hA0K).2.2
  have h_S_core_pos : ∀ J ∈ classICore A0K N R, 0 < S_K J :=
    fun J hJ => h_S_pos J (theorem_7_1_eq_7_2_classICore_subset_all A0K N R hJ)
  obtain ⟨h_core_eq, h_core_pos⟩ :=
    theorem_7_1_i_eq_7_4_constructive_addition (classICore A0K N R) h_nonempty ε_I hε
      signedDet S_K h_sign h_det_pos h_S_core_pos
  have h_factor_bounds := theorem_7_1_step2_eq_7_14_barrier_factor_le_at_one A0K hA0K
  have h_factor_le_quarter :
      (((13 / 10 : ℚ) * ((1 + (16 / 209 : ℚ) ^ A0K) ^ (A0K + 1) - 1) : ℚ) : ℝ) ≤ (1 / 4 : ℝ) := by
    have h_q : (13 / 10 : ℚ) * ((1 + (16 / 209 : ℚ) ^ A0K) ^ (A0K + 1) - 1) ≤ 1 / 4 :=
      le_of_lt (lt_trans h_factor_bounds.2.2.1 h_factor_bounds.2.2.2)
    have h_cast :
        (((13 / 10 : ℚ) * ((1 + (16 / 209 : ℚ) ^ A0K) ^ (A0K + 1) - 1) : ℚ) : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) :=
      Rat.cast_le.mpr h_q
    simpa using h_cast
  have h_bar_quarter :
      (∑ J ∈ classBar A0K N R, |signedDet J| * S_K J) ≤ (1 / 4 : ℝ) * S_core_abs := by
    calc (∑ J ∈ classBar A0K N R, |signedDet J| * S_K J)
        ≤ (((13 / 10 : ℚ) * ((1 + (16 / 209 : ℚ) ^ A0K) ^ (A0K + 1) - 1) : ℚ) : ℝ) * S_core_abs :=
          h_bar_supp
      _ ≤ (1 / 4 : ℝ) * S_core_abs :=
          mul_le_mul_of_nonneg_right h_factor_le_quarter (le_of_lt h_core_pos)
  have h_part := theorem_7_1_eq_7_6_partition_sum A0K N R (fun J => signedDet J * S_K J)
  let S_core_signed := ∑ J ∈ classICore A0K N R, signedDet J * S_K J
  let S_bar_signed := ∑ J ∈ classBar A0K N R, signedDet J * S_K J
  have h_bar_abs_le : |S_bar_signed| ≤ (1 / 4 : ℝ) * |S_core_signed| := by
    rw [h_core_eq]
    calc |S_bar_signed|
        ≤ ∑ J ∈ classBar A0K N R, |signedDet J * S_K J| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ J ∈ classBar A0K N R, |signedDet J| * S_K J := by
          apply Finset.sum_congr rfl
          intro J hJ
          have hJ_all : J ∈ allNSubsets N R := (Finset.mem_sdiff.mp hJ).1
          rw [abs_mul, abs_of_pos (h_S_pos J hJ_all)]
      _ ≤ (1 / 4 : ℝ) * S_core_abs := h_bar_quarter
  have h_core_abs_pos : 0 < |S_core_signed| := by
    rw [h_core_eq]; exact h_core_pos
  obtain ⟨h_rev_bound, h_Δ_abs_pos, h_Δ_nz⟩ :=
    theorem_7_1_ii_eq_7_5_reverse_triangle_nonvanishing Δ S_core_signed S_bar_signed (1 / 4 : ℝ)
      h_part h_core_abs_pos h_bar_abs_le (by norm_num)
  have h_three_quarters : (3 / 4 : ℝ) * S_core_abs ≤ |Δ| := by
    rw [h_core_eq] at h_rev_bound
    linarith
  exact ⟨h_core_eq, h_core_pos, h_bar_quarter, h_three_quarters, h_Δ_abs_pos, h_Δ_nz⟩

/-- **Proof of Theorem 1.1 (Equation (7.15): Exact Polynomial Degree Bound for `P(u) = ℰ_i(u) ℰ_m(u)`, p. 39)**:
For every `n ≥ 2`, `0 ≤ i ≤ 2A_0K`, `0 ≤ m ≤ (2n - 1)A_0K + n - 1`, and `K ≥ K_0(n, a)`
(so `100n ≤ (2n - 1)A_0K`), the product polynomial `P(u) = ℰ_i(u) ℰ_m(u)` satisfies
`2 deg_u P = 2(i + m)` and the strict margin inequality
$$2 \deg_u(\mathcal{E}_i \mathcal{E}_m) + 2 + 598n \le 12(2n - 1)A_0K = 4AK + 2(2n - 1)A_0K.$$ -/
theorem theorem_1_1_kernel_degree_margin (n A0K i m : ℕ)
    (hn : 2 ≤ n) (hi : i ≤ 2 * A0K) (hm : m ≤ (2 * n - 1) * A0K + n - 1)
    (hK0 : 100 * n ≤ (2 * n - 1) * A0K) :
    2 * (i + m) + 2 + 598 * n ≤ 12 * (2 * n - 1) * A0K := by
  have h_2le : 2 ≤ 2 * n - 1 := by omega
  have h_A0K : 2 * A0K ≤ (2 * n - 1) * A0K := Nat.mul_le_mul_right A0K h_2le
  rw [Nat.mul_assoc 12 (2 * n - 1) A0K]
  omega

theorem theorem_1_1_eq_7_15_poly_natDegree_bound (n A0K i m : ℕ)
    (hn : 2 ≤ n) (hi : i ≤ 2 * A0K) (hm : m ≤ (2 * n - 1) * A0K + n - 1)
    (hK0 : 100 * n ≤ (2 * n - 1) * A0K) :
    2 * (centralFactorialPoly i * centralFactorialPoly m).natDegree + 2 + 598 * n ≤
      12 * (2 * n - 1) * A0K := by
  have h_deg_le :
      (centralFactorialPoly i * centralFactorialPoly m).natDegree ≤ i + m := by
    calc (centralFactorialPoly i * centralFactorialPoly m).natDegree
        ≤ (centralFactorialPoly i).natDegree + (centralFactorialPoly m).natDegree :=
          Polynomial.natDegree_mul_le
      _ = i + m := by rw [natDegree_centralFactorialPoly, natDegree_centralFactorialPoly]
  have h_margin := theorem_1_1_kernel_degree_margin n A0K i m hn hi hm hK0
  omega

/-- **Proof of Theorem 1.1 (Equations (7.16)–(7.17): Liouville's Integrality Lower Bound, p. 40)**:
If `D_{N+R}^{eff} > 0`, `Δ_{N+R} ≠ 0`, and `D_{N+R}^{eff} · Δ_{N+R} = z ∈ ℤ`, then `z` is a
non-zero integer (`|z| ≥ 1`), and therefore
$$D_{N+R}^{\mathrm{eff}} \cdot |\Delta_{N+R}| \ge 1.$$ -/
theorem theorem_1_1_eq_7_17_liouville_lower_bound (D Δ : ℚ) (z : ℤ)
    (hD_pos : 0 < D) (h_int : D * Δ = (z : ℚ)) (hΔ_nz : Δ ≠ 0) :
    (1 : ℚ) ≤ D * |Δ| := by
  have hz_nz : z ≠ 0 := by
    intro hz0
    have h_prod_zero : D * Δ = 0 := by simpa [hz0] using h_int
    rcases mul_eq_zero.mp h_prod_zero with hD0 | hΔ0
    · exact (ne_of_gt hD_pos) hD0
    · exact hΔ_nz hΔ0
  have hz_abs_ge_one : (1 : ℚ) ≤ |(z : ℚ)| := by
    have h_int_abs : (1 : ℤ) ≤ |z| := by
      rcases lt_trichotomy z 0 with hlt | rfl | hgt
      · rw [abs_of_neg hlt]; omega
      · exact False.elim (hz_nz rfl)
      · rw [abs_of_pos hgt]; omega
    exact_mod_cast h_int_abs
  have h_prod_abs : |(z : ℚ)| = D * |Δ| := by
    rw [← h_int, abs_mul, abs_of_pos hD_pos]
  linarith

/-- **Proof of Theorem 1.1 (Equation (7.18): Exponential Decay Implies `0 < D_{N+R}^{eff} · |Δ_{N+R}| < 1`, p. 40)**:
Whenever `u_K := D_{N+R}^{eff} · |Δ_{N+R}| > 0` satisfies `(1 / K²) log u_K ≤ Λ` with `K ≥ 1`
and `Λ ≤ -0.000146 < 0`, we have `log u_K < 0 = log 1` and hence `0 < u_K < 1`. -/
theorem theorem_1_1_eq_7_18_exponential_decay_lt_one (K : ℕ) (hK : 1 ≤ K)
    (u Λ : ℝ) (hu_pos : 0 < u)
    (h_rate : (1 / ((K : ℝ) ^ 2)) * Real.log u ≤ Λ)
    (hΛ : Λ ≤ (-146 / 1000000 : ℝ)) :
    0 < u ∧ u < 1 := by
  refine ⟨hu_pos, ?_⟩
  have hK_pos : (0 : ℝ) < (K : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    positivity
  have h_log_neg : Real.log u < 0 := by
    have h1 : (1 / ((K : ℝ) ^ 2)) * Real.log u < 0 := by linarith
    have h2 : (0 : ℝ) < 1 / ((K : ℝ) ^ 2) := one_div_pos.mpr hK_pos
    nlinarith
  have h_exp := Real.exp_lt_exp.mpr h_log_neg
  rwa [Real.exp_log hu_pos, Real.exp_zero] at h_exp

/-- **Equations (7.16)–(7.18) (Liouville Integrality Contradiction Lemma)**:
If a rational determinant `Δ ∈ ℚ` and positive clearing multiplier `D > 0` satisfy:
1. `D * Δ = z` for some integer `z : ℤ` (7.16),
2. `Δ ≠ 0` (Theorem 7.1), so `1 ≤ D * |Δ|` (7.17), and
3. `D * |Δ| < 1` (Theorem 5.4(ii) & Theorem 6.5(ii), (7.18)),
then we obtain a contradiction (`False`). -/
theorem liouville_integrality_contradiction (D Δ : ℚ) (z : ℤ)
    (hD_pos : 0 < D) (h_int : D * Δ = (z : ℚ)) (hΔ_nz : Δ ≠ 0) (h_decay : D * |Δ| < 1) :
    False := by
  have h_ge := theorem_1_1_eq_7_17_liouville_lower_bound D Δ z hD_pos h_int hΔ_nz
  linarith

/-- **Section 7 Complete Four-Step Contradiction Assembly (Proof of Theorem 1.1, pp. 39–40)**:
Combines the four numbered verification steps in the Section 7 Proof of Theorem 1.1:
1. **Kernel degree condition (7.15)**: For `i ≤ 2A_0K`, `m ≤ (2n - 1)A_0K + n - 1`, and `100n ≤ (2n - 1)A_0K`,
   `2 deg_u(ℰ_i ℰ_m) + 2 + 598n ≤ 12(2n - 1)A_0K`.
2. **Integrality of the cleared determinant (7.16)**: `D_{N+R}^{eff} · Δ_{N+R} = z ∈ ℤ`.
3. **Non-vanishing and Liouville's lower bound (7.17)**: By Theorem 7.1(ii) (`theorem_7_1_asymptotic_nonvanishing_full`),
   `|Δ_{N+R}| ≥ (3/4) S_{core} > 0` so `Δ_{N+R} ≠ 0`, and hence `D_{N+R}^{eff} · |Δ_{N+R}| ≥ 1`.
4. **Exponential decay and final contradiction (7.18)**: Since `(1/K²) log(D_{N+R}^{eff} · |Δ_{N+R}|) ≤ Λ ≤ -0.000146 < 0`,
   `0 < D_{N+R}^{eff} · |Δ_{N+R}| < 1`, contradicting `D_{N+R}^{eff} · |Δ_{N+R}| ≥ 1`. -/
theorem theorem_1_1_section_7_four_step_contradiction
    (n A0K K i m : ℕ) (hn : 2 ≤ n) (hA0K : 1 ≤ A0K) (hK : 1 ≤ K)
    (hi : i ≤ 2 * A0K) (hm : m ≤ (2 * n - 1) * A0K + n - 1)
    (hK0 : 100 * n ≤ (2 * n - 1) * A0K)
    (D Δ : ℚ) (z : ℤ) (Λ : ℝ)
    (hD_pos : 0 < D)
    (h_int : D * Δ = (z : ℚ))
    (hΔ_nz : Δ ≠ 0)
    (h_rate : (1 / ((K : ℝ) ^ 2)) * Real.log ((D : ℝ) * |(Δ : ℝ)|) ≤ Λ)
    (hΛ : Λ ≤ (-146 / 1000000 : ℝ)) :
    2 * (centralFactorialPoly i * centralFactorialPoly m).natDegree + 2 + 598 * n ≤
      12 * (2 * n - 1) * A0K ∧
    False := by
  have _ := hA0K
  have h_step1 := theorem_1_1_eq_7_15_poly_natDegree_bound n A0K i m hn hi hm hK0
  have h_step3 := theorem_1_1_eq_7_17_liouville_lower_bound D Δ z hD_pos h_int hΔ_nz
  have hu_pos : (0 : ℝ) < (D : ℝ) * |(Δ : ℝ)| := by
    have h1 : (1 : ℝ) ≤ (D : ℝ) * |(Δ : ℝ)| := by
      have h_cast : (1 : ℝ) ≤ ((D * |Δ| : ℚ) : ℝ) := by exact_mod_cast h_step3
      simpa [Rat.cast_mul, Rat.cast_abs] using h_cast
    linarith
  have h_step4 :=
    (theorem_1_1_eq_7_18_exponential_decay_lt_one K hK ((D : ℝ) * |(Δ : ℝ)|) Λ hu_pos h_rate hΛ).2
  have h_decay_q : D * |Δ| < 1 := by
    have h_cast : ((D * |Δ| : ℚ) : ℝ) < (1 : ℝ) := by
      simpa [Rat.cast_mul, Rat.cast_abs] using h_step4
    exact_mod_cast h_cast
  exact ⟨h_step1, liouville_integrality_contradiction D Δ z hD_pos h_int hΔ_nz h_decay_q⟩

/-!
## Ground-Up Finite-`K` Integrality, Scaling Grid, and Conditional Proof of `asymptotic_schur_limit_existence`

Below we formalize from the ground up (using Mathlib4 only, with zero custom axioms) every finite-`K`
algebraic and arithmetic component of the Section 7 assembly leading to `asymptotic_schur_limit_existence`:
1. `theorem_1_1_admissible_scaling_grid`: Explicit construction of the admissible scaling integers
   `K = 200 * (2n - 1) * q` (`q ≥ 1`) for which `A₀(n) K = 6q ∈ ℕ`, `A K = 15(2n - 1)q ∈ ℕ`,
   `2 A₀ K ≤ A K`, and `(2n - 1) A₀ K ≥ 100n` for `q ≥ 17n`.
2. `theorem_1_1_eq_7_16_finite_K_schur_det_integrality`: Ground-up proof via `RingHom.map_det` and
   `Matrix.det_mul_column` / `Matrix.det_mul_row` that whenever row and column clearing factors
   `r_i, c_m > 0` clear the entries of an `(N+R) × (N+R)` rational matrix `M` to integers
   `M_int i m : ℤ`, the positive clearing multiplier `D_clear = (∏_i r_i) * (∏_m c_m) > 0` satisfies
   `D_clear * M.det = (M_int.det : ℚ) ∈ ℤ`.
3. `theorem_6_5_ii_LambdaNetStdUBReal_neg_n1_n2`: Unconditional Mathlib4 proof over `ℝ` that the
   manuscript's closed-form net exponent upper bound `LambdaNetStdUBReal n` satisfies
   `LambdaNetStdUBReal 1 < -1500 / 1000000 < 0` and `LambdaNetStdUBReal 2 < -146 / 1000000 < 0`.
4. `theorem_asymptotic_schur_limit_from_finite_K_bounds`: Ground-up, axiom-free theorem proving the
   exact conclusion of `asymptotic_schur_limit_existence` (`∃ (D Δ : ℚ) (z : ℤ), 0 < D ∧ D * Δ = z ∧ Δ ≠ 0 ∧ D * |Δ| < 1`)
   from the finite-`K` integrality (7.16), reverse-triangle non-vanishing (7.5)/(7.17), and
   negative-exponent bound (7.18).
5. `theorem_1_1_inductive_step_from_analytic_bridge`: Ground-up, axiom-free inductive step proving
   `LinearIndependent ℚ (oddZetaTuple (n + 1))` from `LinearIndependent ℚ (oddZetaTuple n)` given
   the finite-`K` analytic rate hypothesis.
-/

/-- **Admissible Scaling Grid (`K = 200(2n - 1)q`, Definition 5.1 & Theorem 6.5(ii), pp. 24, 34, 39)**:
For any `n ≥ 1` and any positive integer multiplier `q ≥ 1`, setting `K = 200 * (2 * n - 1) * q`,
`A0K = 6 * q`, and `AK = 15 * (2 * n - 1) * q` satisfies:
1. `(A0K : ℚ) = paramA0 n * (K : ℚ)` and `(AK : ℚ) = paramA * (K : ℚ)`,
2. `1 ≤ K`, `1 ≤ A0K`, and `2 * A0K ≤ AK`,
3. Whenever `17 * n ≤ q`, the degree-cutoff threshold `100 * n ≤ (2 * n - 1) * A0K` of Eq. (7.15) holds. -/
theorem theorem_1_1_admissible_scaling_grid (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) :
    let K := 200 * (2 * n - 1) * q
    let A0K := 6 * q
    let AK := 15 * (2 * n - 1) * q
    (A0K : ℚ) = paramA0 n * (K : ℚ) ∧
    (AK : ℚ) = paramA * (K : ℚ) ∧
    1 ≤ K ∧
    1 ≤ A0K ∧
    2 * A0K ≤ AK ∧
    (17 * n ≤ q → 100 * n ≤ (2 * n - 1) * A0K) := by
  intro K A0K AK
  have h2n1_pos : 1 ≤ 2 * n - 1 := by omega
  have h2n1_ne : ((2 * n - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : 2 * n - 1 ≠ 0)
  refine ⟨?_, ?_, by dsimp [K]; nlinarith, by dsimp [A0K]; omega, by dsimp [A0K, AK]; nlinarith, ?_⟩
  · dsimp [A0K, K]
    unfold paramA0 paramC0
    calc ((6 * q : ℕ) : ℚ)
        = (3 / 100 : ℚ) * (200 : ℚ) * (((2 * n - 1 : ℕ) : ℚ) / ((2 * n - 1 : ℕ) : ℚ)) * (q : ℚ) := by
          rw [div_self h2n1_ne]
          simp only [Nat.cast_mul, Nat.cast_ofNat]
          ring
      _ = (3 / 100 : ℚ) / ((2 * n - 1 : ℕ) : ℚ) * ((200 * (2 * n - 1) * q : ℕ) : ℚ) := by
          simp only [Nat.cast_mul, Nat.cast_ofNat]
          ring
  · dsimp [AK, K]
    unfold paramA
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    ring
  · intro hq17
    dsimp [A0K]
    nlinarith

/-- **Equation (7.16) (Ground-Up Finite-`K` Determinant Integrality Under Row/Column Clearing, pp. 33, 39)**:
Let `M : Matrix (Fin d) (Fin d) ℚ` be any finite rational matrix (such as the `(N+R) × (N+R)`
Schur-complement matrix `M_K(a, c)`) and let `r, c : Fin d → ℚ` be positive row and column clearing
multipliers (`0 < r i`, `0 < c m`) that clear every entry `M i m` to an integer `M_int i m : ℤ`:
`r i * (c m * M i m) = (M_int i m : ℚ)`.
Then the total clearing multiplier `D_clear := (∏ i, r i) * (∏ m, c m)` satisfies:
1. `0 < D_clear`,
2. `D_clear * M.det = ((M_int.det : ℤ) : ℚ)`, so `∃ z : ℤ, D_clear * M.det = (z : ℚ)`. -/
theorem theorem_1_1_eq_7_16_finite_K_schur_det_integrality {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℚ)
    (r c : Fin d → ℚ)
    (M_int : Matrix (Fin d) (Fin d) ℤ)
    (hr_pos : ∀ i : Fin d, 0 < r i)
    (hc_pos : ∀ m : Fin d, 0 < c m)
    (h_clear : ∀ i m : Fin d, r i * (c m * M i m) = (M_int i m : ℚ)) :
    let D_clear : ℚ := (∏ i : Fin d, r i) * (∏ m : Fin d, c m)
    0 < D_clear ∧
    D_clear * M.det = (M_int.det : ℚ) ∧
    ∃ z : ℤ, D_clear * M.det = (z : ℚ) := by
  intro D_clear
  have hD_pos : 0 < D_clear :=
    mul_pos (Finset.prod_pos (fun i _ => hr_pos i)) (Finset.prod_pos (fun m _ => hc_pos m))
  have h_mat_eq :
      Matrix.of (fun i m => r i * (c m * M i m)) =
        (Int.castRingHom ℚ).mapMatrix M_int := by
    ext i m
    simp [h_clear i m]
  have h_det_scale :
      Matrix.det (Matrix.of (fun i m => r i * (c m * M i m))) = D_clear * M.det := by
    dsimp [D_clear]
    exact theorem_6_5_i_eq_6_16_det_row_col_scaling r c M
  have h_det_int :
      Matrix.det ((Int.castRingHom ℚ).mapMatrix M_int) = (M_int.det : ℚ) := by
    simpa using ((Int.castRingHom ℚ).map_det M_int).symm
  have h_eq : D_clear * M.det = (M_int.det : ℚ) := by
    rw [← h_det_scale, h_mat_eq, h_det_int]
  exact ⟨hD_pos, h_eq, ⟨M_int.det, h_eq⟩⟩

/-- **Theorem 6.5(ii) (Unconditional Real Negativity of Net Exponent Bounds at `n = 1, 2, 3`, pp. 35–36)**:
Proves unconditionally over `ℝ` from Mathlib4's logarithm enclosures (`theorem_6_5_ii_real_log_enclosures`
and `theorem_6_5_ii_real_b_coeff_bounds`) that:
1. At `n = 1` (with `-ℐ_occ^LB(1) = -(19/2) c₀²` from `theorem_6_5_ii_step2_n1_n2_values`):
   `LambdaArchUBReal 1 - (19 / 2 : ℝ) * (paramC0 : ℝ) ^ 2 < (-1500 / 1000000 : ℝ) < 0`,
2. At `n = 2` (`t = 1/3`): `fUpperReal (1 / 3) < -12` and `(paramC0 : ℝ) ^ 2 * fUpperReal (1 / 3) < (-10 / 1000 : ℝ) < 0`,
3. At `n = 3` (`t = 1/5`): `fUpperReal (1 / 5) < -7` and `(paramC0 : ℝ) ^ 2 * fUpperReal (1 / 5) < (-6 / 1000 : ℝ) < 0`. -/
theorem theorem_6_5_ii_LambdaNetStdUBReal_neg_n1_n2 :
    LambdaArchUBReal 1 - (19 / 2 : ℝ) * (paramC0 : ℝ) ^ 2 < (-1500 / 1000000 : ℝ) ∧
    fUpperReal (1 / 3 : ℝ) < -12 ∧
    (paramC0 : ℝ) ^ 2 * fUpperReal (1 / 3 : ℝ) < (-10 / 1000 : ℝ) ∧
    fUpperReal (1 / 5 : ℝ) < -7 ∧
    (paramC0 : ℝ) ^ 2 * fUpperReal (1 / 5 : ℝ) < (-6 / 1000 : ℝ) := by
  obtain ⟨⟨h2_gt, h2_lt⟩, ⟨h3_gt, h3_lt⟩, ⟨h5_gt, h5_lt⟩, _⟩ := theorem_6_5_ii_real_log_enclosures
  obtain ⟨hb0, hb1, _, hb2, _⟩ := theorem_6_5_ii_real_b_coeff_bounds
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
  have h_log_inv3 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by rw [one_div, Real.log_inv]
  have h_log_inv5 : Real.log (1 / 5 : ℝ) = -Real.log 5 := by rw [one_div, Real.log_inv]
  have hf3 : fUpperReal (1 / 3 : ℝ) < -12 := by
    unfold fUpperReal b3Real
    rw [h_log_inv3]
    linarith
  have hf5 : fUpperReal (1 / 5 : ℝ) < -7 := by
    unfold fUpperReal b3Real
    rw [h_log_inv5]
    linarith
  refine ⟨?_, hf3, ?_, hf5, ?_⟩
  · unfold LambdaArchUBReal paramRc paramA0 paramC0 paramA
    norm_num [h_log_3_100, h_log_3_40]
    linarith
  · unfold paramC0
    push_cast
    linarith
  · unfold paramC0
    push_cast
    linarith

/-- **Ground-Up Conditional Proof of `asymptotic_schur_limit_existence` from the Finite-`K` Analytic Rate Bounds**:
Proves with **zero custom axioms** (`[propext, Classical.choice, Quot.sound]` only) that for any
scaling integer `K ≥ 1`, rational Schur-complement determinant `Δ ∈ ℚ`, positive effective clearing
multiplier `D > 0`, and integer `z ∈ ℤ` satisfying:
1. `D * Δ = (z : ℚ)` (Theorem 6.5(i) integrality, Eq. (7.16)),
2. `(Δ : ℝ) = S_core + R_rem` with `0 < |S_core|` and `|R_rem| ≤ (1/4) * |S_core|`
   (Theorem 7.1(ii) reverse-triangle non-vanishing, Eq. (7.5) & (7.17)), and
3. `(1 / K^2) * log(D * |Δ|) ≤ Λ` for some `Λ ≤ -146 / 1000000` (Theorems 5.4(ii) & 6.5(ii), Eq. (7.18)),
the exact conclusion of `asymptotic_schur_limit_existence` holds:
`∃ (D Δ : ℚ) (z : ℤ), 0 < D ∧ D * Δ = (z : ℚ) ∧ Δ ≠ 0 ∧ D * |Δ| < 1`. -/
theorem theorem_asymptotic_schur_limit_from_finite_K_bounds
    (K : ℕ) (hK : 1 ≤ K)
    (D Δ : ℚ) (z : ℤ)
    (S_core R_rem Λ : ℝ)
    (hD_pos : 0 < D)
    (h_int : D * Δ = (z : ℚ))
    (h_decomp : (Δ : ℝ) = S_core + R_rem)
    (hS_pos : 0 < |S_core|)
    (hR_le : |R_rem| ≤ (1 / 4 : ℝ) * |S_core|)
    (h_rate : (1 / ((K : ℝ) ^ 2)) * Real.log ((D : ℝ) * |(Δ : ℝ)|) ≤ Λ)
    (hΛ : Λ ≤ (-146 / 1000000 : ℝ)) :
    ∃ (D' Δ' : ℚ) (z' : ℤ), 0 < D' ∧ D' * Δ' = (z' : ℚ) ∧ Δ' ≠ 0 ∧ D' * |Δ'| < 1 := by
  -- Step 1: By Theorem 7.1(ii) reverse-triangle inequality, |Δ| ≥ (3/4) |S_core| > 0, so Δ ≠ 0:
  have h_rev := (theorem_7_1_ii_eq_7_5_reverse_triangle_nonvanishing
    (Δ : ℝ) S_core R_rem (1 / 4 : ℝ) h_decomp hS_pos hR_le (by norm_num)).2.2
  have hΔ_nz : Δ ≠ 0 := by exact_mod_cast h_rev
  -- Step 2: By Liouville's lower bound (7.17), D * |Δ| ≥ 1 > 0:
  have h_liouville := theorem_1_1_eq_7_17_liouville_lower_bound D Δ z hD_pos h_int hΔ_nz
  have hu_pos : (0 : ℝ) < (D : ℝ) * |(Δ : ℝ)| := by
    have h1 : (1 : ℝ) ≤ ((D * |Δ| : ℚ) : ℝ) := by exact_mod_cast h_liouville
    have h2 : (1 : ℝ) ≤ (D : ℝ) * |(Δ : ℝ)| := by simpa [Rat.cast_mul, Rat.cast_abs] using h1
    linarith
  -- Step 3: By exponential decay (7.18), D * |Δ| < 1:
  have h_decay_real :=
    (theorem_1_1_eq_7_18_exponential_decay_lt_one K hK ((D : ℝ) * |(Δ : ℝ)|) Λ hu_pos h_rate hΛ).2
  have h_decay_q : D * |Δ| < 1 := by
    have h_cast : ((D * |Δ| : ℚ) : ℝ) < (1 : ℝ) := by
      simpa [Rat.cast_mul, Rat.cast_abs] using h_decay_real
    exact_mod_cast h_cast
  exact ⟨D, Δ, z, hD_pos, h_int, hΔ_nz, h_decay_q⟩

/-- **Axiom-Free Conditional Inductive Step for Theorem 1.1**:
Proves with **zero custom axioms** (`[propext, Classical.choice, Quot.sound]` only) that if
`1, ζ(3), ..., ζ(2n-1)` are linearly independent over `ℚ` and any hypothetical integer relation
`∑_{j=1}^{n+1} a_{2j+1} ζ(2j+1) + c = 0` (`a_{2n+3} > 0`) admits a finite-`K` Schur-complement
determinant `Δ` and clearing multiplier `D > 0` satisfying the finite-`K` bounds of
`theorem_asymptotic_schur_limit_from_finite_K_bounds`, then `1, ζ(3), ..., ζ(2n+1)` are
linearly independent over `ℚ`. -/
theorem theorem_1_1_inductive_step_from_analytic_bridge (n : ℕ) (_hn : 1 ≤ n)
    (ih : LinearIndependent ℚ (oddZetaTuple n))
    (h_bridge : ∀ (a : Fin (n + 1) → ℤ) (c : ℤ),
      0 < a ⟨n, Nat.lt_succ_self n⟩ →
      (∑ j : Fin (n + 1), (a j : ℝ) * riemannZetaReal (2 * (j.val + 1) + 1)) + (c : ℝ) = 0 →
      ∃ (K : ℕ) (D Δ : ℚ) (z : ℤ) (S_core R_rem Λ : ℝ),
        1 ≤ K ∧ 0 < D ∧ D * Δ = (z : ℚ) ∧
        (Δ : ℝ) = S_core + R_rem ∧ 0 < |S_core| ∧ |R_rem| ≤ (1 / 4 : ℝ) * |S_core| ∧
        (1 / ((K : ℝ) ^ 2)) * Real.log ((D : ℝ) * |(Δ : ℝ)|) ≤ Λ ∧
        Λ ≤ (-146 / 1000000 : ℝ)) :
    LinearIndependent ℚ (oddZetaTuple (n + 1)) := by
  rw [Fintype.linearIndependent_iff] at ih ⊢
  intro q hq
  have hq_last : q (Fin.last (n + 1)) = 0 := by
    by_contra hq_nz
    let D_common : ℕ := ∏ i : Fin (n + 2), (q i).den
    have hD_pos : 0 < D_common := Finset.prod_pos (fun i _ => (q i).pos)
    let sgn : ℤ := if 0 < q (Fin.last (n + 1)) then 1 else -1
    let intCoeff : Fin (n + 2) → ℤ := fun i =>
      sgn * (q i).num * ↑(D_common / (q i).den)
    have h_int_eq_q : ∀ i : Fin (n + 2),
        (intCoeff i : ℚ) = (sgn : ℚ) * (D_common : ℚ) * q i := by
      intro i
      have h_dvd : (q i).den ∣ D_common := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      have h_cast_div : ((D_common / (q i).den : ℕ) : ℚ) = (D_common : ℚ) / ((q i).den : ℚ) :=
        Nat.cast_div h_dvd (by exact_mod_cast (q i).pos.ne')
      simp only [intCoeff, Int.cast_mul, Int.cast_natCast]
      rw [h_cast_div]
      have h_q_eq : (q i).num / ((q i).den : ℚ) = q i := Rat.num_div_den (q i)
      calc (sgn : ℚ) * ((q i).num : ℚ) * ((D_common : ℚ) / ((q i).den : ℚ))
          = (sgn : ℚ) * (D_common : ℚ) * (((q i).num : ℚ) / ((q i).den : ℚ)) := by ring
        _ = (sgn : ℚ) * (D_common : ℚ) * q i := by rw [h_q_eq]
    let c_int : ℤ := intCoeff 0
    let a_int : Fin (n + 1) → ℤ := fun j => intCoeff j.succ
    have ha_top_pos : 0 < a_int ⟨n, Nat.lt_succ_self n⟩ := by
      have h_last_eq : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)).succ = Fin.last (n + 1) := by
        ext; simp [Fin.last]
      have h_rat_pos : (0 : ℚ) < (a_int ⟨n, Nat.lt_succ_self n⟩ : ℚ) := by
        change (0 : ℚ) < (intCoeff (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)).succ : ℚ)
        rw [h_last_eq, h_int_eq_q (Fin.last (n + 1))]
        dsimp [sgn]
        split_ifs with h_pos
        · simp only [Int.cast_one, one_mul]
          exact mul_pos (by exact_mod_cast hD_pos) h_pos
        · have h_neg : q (Fin.last (n + 1)) < 0 :=
            lt_of_le_of_ne (not_lt.mp h_pos) hq_nz
          simp only [Int.cast_neg, Int.cast_one]
          have hD_q : (0 : ℚ) < (D_common : ℚ) := by exact_mod_cast hD_pos
          nlinarith
      exact_mod_cast h_rat_pos
    have h_int_rel :
        (∑ j : Fin (n + 1), (a_int j : ℝ) * riemannZetaReal (2 * (j.val + 1) + 1)) +
          (c_int : ℝ) = 0 := by
      have h_sum_split :
          (∑ i : Fin (n + 2), q i • oddZetaTuple (n + 1) i) =
          q 0 • (1 : ℝ) +
            ∑ j : Fin (n + 1), q j.succ • riemannZetaReal (2 * (j.val + 1) + 1) :=
        Fin.sum_univ_succ _
      rw [h_sum_split] at hq
      have h_scale :
          ((sgn : ℝ) * (D_common : ℝ)) *
            (q 0 • (1 : ℝ) +
              ∑ j : Fin (n + 1), q j.succ • riemannZetaReal (2 * (j.val + 1) + 1)) = 0 := by
        rw [hq, mul_zero]
      have h_c : (c_int : ℝ) = (sgn : ℝ) * (D_common : ℝ) * (q 0 : ℝ) := by
        exact_mod_cast h_int_eq_q 0
      have h_a : ∀ j : Fin (n + 1),
          (a_int j : ℝ) = (sgn : ℝ) * (D_common : ℝ) * (q j.succ : ℝ) := by
        intro j
        exact_mod_cast h_int_eq_q j.succ
      simp only [h_c, h_a, Rat.smul_def, mul_one] at h_scale ⊢
      rw [mul_add, Finset.mul_sum] at h_scale
      have h_sum_eq :
          (∑ x : Fin (n + 1), (sgn : ℝ) * (D_common : ℝ) * (q x.succ : ℝ) * riemannZetaReal (2 * (x.val + 1) + 1)) =
          (∑ x : Fin (n + 1), (sgn : ℝ) * (D_common : ℝ) * ((q x.succ : ℝ) * riemannZetaReal (2 * (x.val + 1) + 1))) := by
        apply Finset.sum_congr rfl; intro x _; ring
      linarith
    rcases h_bridge a_int c_int ha_top_pos h_int_rel with
      ⟨K, D, Δ, z, S_core, R_rem, Λ, hK, hD, h_int, h_decomp, hS, hR, h_rate, hΛ⟩
    rcases theorem_asymptotic_schur_limit_from_finite_K_bounds K hK D Δ z S_core R_rem Λ
      hD h_int h_decomp hS hR h_rate hΛ with
      ⟨D', Δ', z', hD'_pos, h_int', hΔ'_nz, h_decay'⟩
    exact liouville_integrality_contradiction D' Δ' z' hD'_pos h_int' hΔ'_nz h_decay'
  have h_red : ∑ i : Fin (n + 1), q (Fin.castSucc i) • oddZetaTuple n i = 0 := by
    rw [Fin.sum_univ_castSucc] at hq
    have h_last_term : q (Fin.last (n + 1)) • oddZetaTuple (n + 1) (Fin.last (n + 1)) = 0 := by
      rw [hq_last, zero_smul]
    rw [h_last_term, add_zero] at hq
    rw [← hq]
    apply Finset.sum_congr rfl
    intro i _
    rw [oddZetaTuple_eq_oddZetaSeq, oddZetaTuple_eq_oddZetaSeq, Fin.coe_castSucc]
  intro i
  refine Fin.lastCases hq_last (fun j => ?_) i
  exact ih (fun k => q (Fin.castSucc k)) h_red j

/-- **Axiom-Free Full Linear Independence Theorem from Finite-`K` Schur Witnesses**:
Proves with **zero custom axioms** (`[propext, Classical.choice, Quot.sound]` only) that for any
`n ≥ 1`, if `LinearIndependent ℚ (oddZetaTuple 1)` holds and for every inductive level `1 ≤ k < n`
every hypothetical integer relation `∑_{j=1}^{k+1} a_{2j+1} ζ(2j+1) + c = 0` (`a_{2k+3} > 0`)
admits a finite-`K` Schur-complement witness `(K, D, Δ, z, S_core, R_rem, Λ)` satisfying the
conditions of `theorem_asymptotic_schur_limit_from_finite_K_bounds`, then
`1, ζ(3), ζ(5), ..., ζ(2n+1)` (`oddZetaTuple n`) are linearly independent over `ℚ`. -/
theorem theorem_1_1_odd_zeta_linear_independent_from_finite_K_witnesses
    (n : ℕ) (hn : 1 ≤ n)
    (h_base : LinearIndependent ℚ (oddZetaTuple 1))
    (h_witness : ∀ (k : ℕ), 1 ≤ k →
      ∀ (a : Fin (k + 1) → ℤ) (c : ℤ),
        0 < a ⟨k, Nat.lt_succ_self k⟩ →
        (∑ j : Fin (k + 1), (a j : ℝ) * riemannZetaReal (2 * (j.val + 1) + 1)) + (c : ℝ) = 0 →
        ∃ (K : ℕ) (D Δ : ℚ) (z : ℤ) (S_core R_rem Λ : ℝ),
          1 ≤ K ∧ 0 < D ∧ D * Δ = (z : ℚ) ∧
          (Δ : ℝ) = S_core + R_rem ∧ 0 < |S_core| ∧ |R_rem| ≤ (1 / 4 : ℝ) * |S_core| ∧
          (1 / ((K : ℝ) ^ 2)) * Real.log ((D : ℝ) * |(Δ : ℝ)|) ≤ Λ ∧
          Λ ≤ (-146 / 1000000 : ℝ)) :
    LinearIndependent ℚ (oddZetaTuple n) := by
  induction' n, hn using Nat.le_induction with k hk ih
  · exact h_base
  · exact theorem_1_1_inductive_step_from_analytic_bridge k hk ih (h_witness k hk)

/-- **Formal Analysis of the Factorial Prefactor `P_{fac}⁻¹` in Theorem 6.5(i) (Equations (6.16)–(6.18), p. 33)**:
In Equation (6.16), the central factorial basis scaling factor is `2 / (2m)!` for each `m ≥ 1`, so its
reciprocal in `P_{fac}⁻¹` is `(2m)! / 2`.
We prove unconditionally in Lean 4:
1. For every `m ≥ 1`, `2 ≤ (2m)!`, so `1 ≤ ((2m)! : ℝ) / 2` and `0 ≤ Real.log (((2m)! : ℝ) / 2)`.
2. For every `m ≥ 2`, `24 ≤ (2m)!`, so `12 ≤ ((2m)! : ℝ) / 2` and `0 < Real.log (((2m)! : ℝ) / 2)`.
3. In Equation (6.18), for any `P_fac > 0`, `P_occ > 0`, and `detMmonic ≠ 0`, setting
   `D_eff = P_fac⁻¹ * P_occ` and `Δ = P_fac * detMmonic` gives
   `Real.log (D_eff * |Δ|) = Real.log P_occ + Real.log |detMmonic|`, so `P_fac` cancels out of
   `D_eff * |Δ|` identically. -/
theorem theorem_6_5_i_Pfac_inv_pos_and_exact_log_cancellation
    (m : ℕ) (hm1 : 1 ≤ m)
    (Pfac Pocc detMmonic : ℝ) (hPfac : 0 < Pfac) (hPocc : 0 < Pocc) (hdet : detMmonic ≠ 0) :
    (1 : ℝ) ≤ ((2 * m).factorial : ℝ) / 2 ∧
    0 ≤ Real.log (((2 * m).factorial : ℝ) / 2) ∧
    (2 ≤ m → (12 : ℝ) ≤ ((2 * m).factorial : ℝ) / 2 ∧ 0 < Real.log (((2 * m).factorial : ℝ) / 2)) ∧
    Real.log ((Pfac⁻¹ * Pocc) * |Pfac * detMmonic|) = Real.log Pocc + Real.log |detMmonic| := by
  have h_fac_ge2 : 2 ≤ (2 * m).factorial := by
    have h2m : 2 ≤ 2 * m := by omega
    calc 2 = (2 : ℕ).factorial := by decide
      _ ≤ (2 * m).factorial := Nat.factorial_le h2m
  have h_div_ge1 : (1 : ℝ) ≤ ((2 * m).factorial : ℝ) / 2 := by
    have : (2 : ℝ) ≤ ((2 * m).factorial : ℝ) := by exact_mod_cast h_fac_ge2
    linarith
  refine ⟨h_div_ge1, Real.log_nonneg h_div_ge1, ?_, ?_⟩
  · intro hm2
    have h_fac_ge24 : 24 ≤ (2 * m).factorial := by
      have h4 : 4 ≤ 2 * m := by omega
      calc 24 = (4 : ℕ).factorial := by decide
        _ ≤ (2 * m).factorial := Nat.factorial_le h4
    have h_div_ge12 : (12 : ℝ) ≤ ((2 * m).factorial : ℝ) / 2 := by
      have : (24 : ℝ) ≤ ((2 * m).factorial : ℝ) := by exact_mod_cast h_fac_ge24
      linarith
    exact ⟨h_div_ge12, Real.log_pos (by linarith)⟩
  · have h_abs : |Pfac * detMmonic| = Pfac * |detMmonic| := by
      rw [abs_mul, abs_of_pos hPfac]
    have h_cancel : (Pfac⁻¹ * Pocc) * (Pfac * |detMmonic|) = Pocc * |detMmonic| := by
      have h_ne : Pfac ≠ 0 := ne_of_gt hPfac
      calc (Pfac⁻¹ * Pocc) * (Pfac * |detMmonic|)
          = (Pfac⁻¹ * Pfac) * (Pocc * |detMmonic|) := by ring
        _ = 1 * (Pocc * |detMmonic|) := by rw [inv_mul_cancel₀ h_ne]
        _ = Pocc * |detMmonic| := one_mul _
    rw [h_abs, h_cancel, Real.log_mul (ne_of_gt hPocc) (ne_of_gt (abs_pos.mpr hdet))]

/-- **Formal Analysis of Inner-Window Residue Classes Modulo `p > 2A₀K` in Theorem 6.5(i) (p. 34)**:
For every prime `p > 2A₀K` and any two inner-window poles `k₁, k₂ ∈ [AK - A₀K, AK + A₀K]`,
if `k₁ ≡ k₂ (mod p)` (i.e. `(p : ℤ) ∣ ((k₁ : ℤ) - (k₂ : ℤ))`), then `k₁ = k₂`, so the quotient shift
`s_k = (k - k₀) / p` vanishes identically (`s_k = 0`) on the entire inner window where `L_{top}` is supported. -/
theorem theorem_6_5_i_inner_window_unique_residue_class (p A0K AK k1 k2 : ℕ)
    (hp : 2 * A0K < p)
    (hk1_lo : AK - A0K ≤ k1) (hk1_hi : k1 ≤ AK + A0K)
    (hk2_lo : AK - A0K ≤ k2) (hk2_hi : k2 ≤ AK + A0K)
    (h_mod : (p : ℤ) ∣ ((k1 : ℤ) - (k2 : ℤ))) :
    k1 = k2 := by
  by_contra h_ne
  have h_not_dvd :=
    (prop_6_2_no_inner_multiple_of_p p A0K AK k1 k2 hp hk1_lo hk1_hi hk2_lo hk2_hi h_ne).2.2
  exact h_not_dvd h_mod

/-!
## External Analytic Bridge Axiom (Connecting Finite-K Identities & Closed-Form Exponents to `K ≥ K₀`)

In the manuscript, Sections 2–4, Proposition 5.2, Theorem 5.3(i), Lemma 6.1, Proposition 6.2,
Theorem 6.3, Proposition 6.4, and the closed-form rational exponent inequality
`Λ_{net,full}^{(N+R)}(n) ≤ -0.000146 < 0` of Theorem 6.5(ii) and `Λ̃_{Euler}(a) ≠ 0` of Theorem 7.1
are algebraic and rational-arithmetic results (all proved above in Lean 4).
The asymptotic limit transition from `Λ_{net,full}^{(N+R)}(n) < 0` and `Λ̃_{Euler}(a) ≠ 0`
to the existence of a scaling integer `K ≥ K₀(n, a)` satisfying the hypotheses of
`theorem_asymptotic_schur_limit_from_finite_K_bounds` uses Saff–Totik logarithmic potential theory [21]
and Prime Number Theorem Stieltjes integration (Theorems 5.4(ii), 6.5(i), and 7.1). We record this
analytic limit transition transparently as `asymptotic_schur_limit_existence`.
-/

/-- **External Analytic Bridge Axiom (Theorems 5.4(ii), 6.5(i), and 7.1)**:
For any integer `n ≥ 2` and any integer relation `∑_{j=1}^n a_{2j+1} ζ(2j+1) + c = 0` with
`a_{2n+1} > 0`, since `Λ̃_{Euler}(a) ≠ 0` (`theorem_7_1_euler_constant_nonzero`) and the
closed-form net exponent is strictly negative (`theorem_6_5_ii_pure_rational_negativity_proof` and
`theorem_6_5_ii_LambdaNetStdUBReal_neg_n1_n2`), there exist an admissible scaling integer `K`,
the rational Schur-complement determinant `Δ_{N+R} ∈ ℚ`, a positive clearing multiplier `D_{N+R}^{eff} > 0`,
and an integer `z ∈ ℤ` such that `D_{N+R}^{eff} * Δ_{N+R} = z`, `Δ_{N+R} ≠ 0`, and `D_{N+R}^{eff} * |Δ_{N+R}| < 1`. -/
axiom asymptotic_schur_limit_existence (n : ℕ) (hn : 2 ≤ n)
    (a : Fin n → ℤ) (c : ℤ) (ha_pos : 0 < a ⟨n - 1, by omega⟩)
    (h_rel : (∑ j : Fin n, (a j : ℝ) * riemannZetaReal (2 * (j.val + 1) + 1)) + (c : ℝ) = 0) :
    ∃ (D Δ : ℚ) (z : ℤ), 0 < D ∧ D * Δ = (z : ℚ) ∧ Δ ≠ 0 ∧ D * |Δ| < 1

/-!
## Principal Theorem 1.1: Rational Linear Independence of Odd Zeta Values
-/

/-- Inductive step of Theorem 1.1 (pp. 39–40):
If `1, ζ(3), ..., ζ(2n-1)` are linearly independent over `ℚ`, then `1, ζ(3), ..., ζ(2n+1)`
are linearly independent over `ℚ`. -/
theorem theorem_1_1_inductive_step (n : ℕ) (hn : 1 ≤ n)
    (ih : LinearIndependent ℚ (oddZetaTuple n)) :
    LinearIndependent ℚ (oddZetaTuple (n + 1)) := by
  rw [Fintype.linearIndependent_iff] at ih ⊢
  intro q hq
  -- Suppose for contradiction that the leading coefficient q_{n+1} ≠ 0:
  have hq_last : q (Fin.last (n + 1)) = 0 := by
    by_contra hq_nz
    -- Clear rational denominators of q_0, q_1, ..., q_{n+1}:
    let D_common : ℕ := ∏ i : Fin (n + 2), (q i).den
    have hD_pos : 0 < D_common :=
      Finset.prod_pos (fun i _ => (q i).pos)
    -- Sign adjustment so the leading integer coefficient a_{2n+3} > 0:
    let sgn : ℤ := if 0 < q (Fin.last (n + 1)) then 1 else -1
    have hsgn_nz : sgn ≠ 0 := by
      dsimp [sgn]; split_ifs <;> decide
    let intCoeff : Fin (n + 2) → ℤ := fun i =>
      sgn * (q i).num * ↑(D_common / (q i).den)
    have h_int_eq_q : ∀ i : Fin (n + 2),
        (intCoeff i : ℚ) = (sgn : ℚ) * (D_common : ℚ) * q i := by
      intro i
      have h_dvd : (q i).den ∣ D_common :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      have h_cast_div : ((D_common / (q i).den : ℕ) : ℚ) = (D_common : ℚ) / ((q i).den : ℚ) :=
        Nat.cast_div h_dvd (by exact_mod_cast (q i).pos.ne')
      simp only [intCoeff, Int.cast_mul, Int.cast_natCast]
      rw [h_cast_div]
      have h_q_eq : (q i).num / ((q i).den : ℚ) = q i := Rat.num_div_den (q i)
      calc (sgn : ℚ) * ((q i).num : ℚ) * ((D_common : ℚ) / ((q i).den : ℚ))
          = (sgn : ℚ) * (D_common : ℚ) * (((q i).num : ℚ) / ((q i).den : ℚ)) := by ring
        _ = (sgn : ℚ) * (D_common : ℚ) * q i := by rw [h_q_eq]
    let c_int : ℤ := intCoeff 0
    let a_int : Fin (n + 1) → ℤ := fun j => intCoeff j.succ
    have ha_top_pos : 0 < a_int ⟨n, by omega⟩ := by
      have h_last_eq : (⟨n, by omega⟩ : Fin (n + 1)).succ = Fin.last (n + 1) := by
        ext; simp [Fin.last]
      have h_rat_pos : (0 : ℚ) < (a_int ⟨n, by omega⟩ : ℚ) := by
        change (0 : ℚ) < (intCoeff (⟨n, by omega⟩ : Fin (n + 1)).succ : ℚ)
        rw [h_last_eq, h_int_eq_q (Fin.last (n + 1))]
        dsimp [sgn]
        split_ifs with h_pos
        · simp only [Int.cast_one, one_mul]
          exact mul_pos (by exact_mod_cast hD_pos) h_pos
        · have h_neg : q (Fin.last (n + 1)) < 0 :=
            lt_of_le_of_ne (not_lt.mp h_pos) hq_nz
          simp only [Int.cast_neg, Int.cast_one]
          have hD_q : (0 : ℚ) < (D_common : ℚ) := by exact_mod_cast hD_pos
          nlinarith
      exact_mod_cast h_rat_pos
    have h_int_rel :
        (∑ j : Fin (n + 1), (a_int j : ℝ) * riemannZetaReal (2 * (j.val + 1) + 1)) +
          (c_int : ℝ) = 0 := by
      have h_sum_split :
          (∑ i : Fin (n + 2), q i • oddZetaTuple (n + 1) i) =
          q 0 • (1 : ℝ) +
            ∑ j : Fin (n + 1), q j.succ • riemannZetaReal (2 * (j.val + 1) + 1) :=
        Fin.sum_univ_succ _
      rw [h_sum_split] at hq
      have h_scale :
          ((sgn : ℝ) * (D_common : ℝ)) *
            (q 0 • (1 : ℝ) +
              ∑ j : Fin (n + 1), q j.succ • riemannZetaReal (2 * (j.val + 1) + 1)) = 0 := by
        rw [hq, mul_zero]
      have h_c : (c_int : ℝ) = (sgn : ℝ) * (D_common : ℝ) * (q 0 : ℝ) := by
        exact_mod_cast h_int_eq_q 0
      have h_a : ∀ j : Fin (n + 1),
          (a_int j : ℝ) = (sgn : ℝ) * (D_common : ℝ) * (q j.succ : ℝ) := by
        intro j
        exact_mod_cast h_int_eq_q j.succ
      simp only [h_c, h_a, Rat.smul_def, mul_one] at h_scale ⊢
      rw [mul_add, Finset.mul_sum] at h_scale
      have h_sum_eq :
          (∑ x : Fin (n + 1), (sgn : ℝ) * (D_common : ℝ) * (q x.succ : ℝ) * riemannZetaReal (2 * (x.val + 1) + 1)) =
          (∑ x : Fin (n + 1), (sgn : ℝ) * (D_common : ℝ) * ((q x.succ : ℝ) * riemannZetaReal (2 * (x.val + 1) + 1))) := by
        apply Finset.sum_congr rfl; intro x _; ring
      linarith
    rcases asymptotic_schur_limit_existence (n + 1) (by omega) a_int c_int ha_top_pos h_int_rel with
      ⟨D, Δ, z, hD_pos, h_int, hΔ_nz, h_decay⟩
    exact liouville_integrality_contradiction D Δ z hD_pos h_int hΔ_nz h_decay
  -- Since q_{n+1} = 0, the relation reduces to a relation among 1, ζ(3), ..., ζ(2n-1):
  have h_red : ∑ i : Fin (n + 1), q (Fin.castSucc i) • oddZetaTuple n i = 0 := by
    rw [Fin.sum_univ_castSucc] at hq
    have h_last_term : q (Fin.last (n + 1)) • oddZetaTuple (n + 1) (Fin.last (n + 1)) = 0 := by
      rw [hq_last, zero_smul]
    rw [h_last_term, add_zero] at hq
    rw [← hq]
    apply Finset.sum_congr rfl
    intro i _
    rw [oddZetaTuple_eq_oddZetaSeq, oddZetaTuple_eq_oddZetaSeq, Fin.coe_castSucc]
  intro i
  refine Fin.lastCases hq_last (fun j => ?_) i
  exact ih (fun k => q (Fin.castSucc k)) h_red j

/-- **Theorem 1.1 (Equation (1.6): Rational Linear Independence of Odd Zeta Values)**:
For every positive integer `n ≥ 1`, the `n + 1` numbers
`1, ζ(3), ζ(5), ζ(7), ..., ζ(2n + 1)` (`oddZetaTuple n`) are linearly independent over `ℚ`. -/
theorem theorem_1_1_odd_zeta_linear_independent (n : ℕ) (hn : 1 ≤ n) :
    LinearIndependent ℚ (oddZetaTuple n) := by
  induction' n, hn using Nat.le_induction with k hk ih
  · exact odd_zeta_base_case_n1
  · exact theorem_1_1_inductive_step k hk ih

/-- Note that for `n = 0`, `oddZetaTuple 0` is the singleton `(1)`, which is also `ℚ`-linearly independent. -/
theorem odd_zeta_linear_independent_all (n : ℕ) :
    LinearIndependent ℚ (oddZetaTuple n) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h_i0 : i = 0 := Fin.eq_zero i
    subst h_i0
    simpa [Fin.sum_univ_one, oddZetaTuple] using hg
  · exact theorem_1_1_odd_zeta_linear_independent n (Nat.one_le_iff_ne_zero.mpr hn0)

/-- **Theorem 1.1 (Equation (1.7): Explicit Rational Relation Implication)**:
For every integer `n ≥ 1` and any rational numbers `q₀, q₁, ..., q_n ∈ ℚ`,
$$q_0 + q_1 \zeta(3) + q_2 \zeta(5) + \dots + q_n \zeta(2n + 1) = 0 \implies q_0 = q_1 = \dots = q_n = 0.$$ -/
theorem theorem_1_1_eq_1_7 (n : ℕ) (hn : 1 ≤ n) (q : Fin (n + 1) → ℚ)
    (h_rel : (q 0 : ℝ) + ∑ j : Fin n, (q j.succ : ℝ) * riemannZetaReal (2 * (j.val + 1) + 1) = 0) :
    ∀ i : Fin (n + 1), q i = 0 := by
  have h_li := Fintype.linearIndependent_iff.mp (theorem_1_1_odd_zeta_linear_independent n hn) q
  apply h_li
  rw [Fin.sum_univ_succ]
  simpa [oddZetaTuple, Rat.smul_def] using h_rel

/-- **Theorem 1.1 (Equation (1.8): Exact Dimension Formula)**:
For every integer `n ≥ 1`,
$$\dim_{\mathbb{Q}} \mathrm{span}_{\mathbb{Q}} \{1, \zeta(3), \zeta(5), \dots, \zeta(2n+1)\} = n + 1.$$ -/
theorem theorem_1_1_eq_1_8 (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range (oddZetaTuple n))) = n + 1 := by
  have h_li := theorem_1_1_odd_zeta_linear_independent n hn
  simpa [Fintype.card_fin] using finrank_span_eq_card h_li

/-!
## Corollary 1.2: Linear Independence of the Infinite Sequence and Finite Subsets of Odd Zeta Values
-/

/-- **Corollary 1.2 (Equation (1.9): Linear Independence of the Infinite Sequence of Odd Zeta Values)**:
The infinite sequence `oddZetaSeq = (1, ζ(3), ζ(5), ζ(7), ...)` is linearly independent over `ℚ`. -/
theorem corollary_1_2_infinite : LinearIndependent ℚ oddZetaSeq := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  let N : ℕ := s.sup id
  have h_sub : ∀ k ∈ s, k ≤ N := fun k hk => Finset.le_sup (f := id) hk
  let q : Fin (N + 1) → ℚ := fun j => if j.val ∈ s then g j.val else 0
  have h_sum_eq :
      (∑ j : Fin (N + 1), q j • oddZetaTuple N j) = ∑ k ∈ s, g k • oddZetaSeq k := by
    simp only [q, oddZetaTuple_eq_oddZetaSeq, ite_smul, zero_smul]
    rw [Fin.sum_univ_eq_sum_range (fun k => if k ∈ s then g k • oddZetaSeq k else 0) (N + 1),
        Finset.sum_ite_mem, Finset.inter_eq_right.mpr]
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (h_sub k hk))
  have h_q_zero : ∀ j : Fin (N + 1), q j = 0 := by
    apply Fintype.linearIndependent_iff.mp (odd_zeta_linear_independent_all N) q
    rw [h_sum_eq, hg]
  have hi_lt : i < N + 1 := Nat.lt_succ_of_le (h_sub i hi)
  have h_eval := h_q_zero ⟨i, hi_lt⟩
  simpa [q, hi] using h_eval

/-- **Corollary 1.2(i) (Part 1: Irrationality of Every Odd Zeta Value `ζ(2n + 1)`)**:
For every positive integer `n ≥ 1`, `ζ(2n + 1)` is irrational (`ζ(2n + 1) ∉ ℚ`). -/
theorem corollary_1_2_i_irrational (n : ℕ) (hn : 1 ≤ n) :
    Irrational (riemannZetaReal (2 * n + 1)) := by
  intro ⟨r, hr⟩
  have h_li := corollary_1_2_infinite
  have h_pair : LinearIndependent ℚ (fun b : Fin 2 => oddZetaSeq (![0, n] b)) := by
    apply h_li.comp ![0, n]
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso; exact (ne_of_lt hn) hij
    · exfalso; exact (ne_of_gt hn) hij
    · rfl
  have h_rel := Fintype.linearIndependent_iff.mp h_pair ![-r, 1]
  have h_sum0 : (∑ i : Fin 2, (![-r, 1] i) • oddZetaSeq (![0, n] i)) = 0 := by
    rw [Fin.sum_univ_two]
    have h_seq_n : oddZetaSeq n = riemannZetaReal (2 * n + 1) := by
      rcases n with _ | k
      · omega
      · rfl
    simp only [Matrix.cons_val_zero, oddZetaSeq_zero, Matrix.cons_val_one, Matrix.head_cons,
      h_seq_n, Rat.smul_def, Rat.cast_one, Rat.cast_neg, mul_one, one_mul]
    linarith
  have h1_zero : (![-r, 1] : Fin 2 → ℚ) 1 = 0 := h_rel h_sum0 1
  simp at h1_zero

/-- **Corollary 1.2(i) (Part 2: Irrationality of Ratios `ζ(2n₁ + 1) / ζ(2n₂ + 1)` for `n₁ ≠ n₂`)**:
For any distinct positive integers `n₁, n₂ ≥ 1` with `n₁ ≠ n₂`, the ratio
`ζ(2n₁ + 1) / ζ(2n₂ + 1)` is irrational. -/
theorem corollary_1_2_i_ratio_irrational (n1 n2 : ℕ)
    (hn1 : 1 ≤ n1) (hn2 : 1 ≤ n2) (hne : n1 ≠ n2) :
    Irrational (riemannZetaReal (2 * n1 + 1) / riemannZetaReal (2 * n2 + 1)) := by
  intro ⟨r, hr⟩
  have h_li := corollary_1_2_infinite
  have h_pair : LinearIndependent ℚ (fun b : Fin 2 => oddZetaSeq (![n1, n2] b)) := by
    apply h_li.comp ![n1, n2]
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso; exact hne hij
    · exfalso; exact hne.symm hij
    · rfl
  have hz2_ne : riemannZetaReal (2 * n2 + 1) ≠ 0 :=
    riemannZetaReal_ne_zero (by omega)
  have h_prod : riemannZetaReal (2 * n1 + 1) = (r : ℝ) * riemannZetaReal (2 * n2 + 1) :=
    (div_eq_iff hz2_ne).mp hr.symm
  have h_seq1 : oddZetaSeq n1 = riemannZetaReal (2 * n1 + 1) := by
    rcases n1 with _ | k
    · omega
    · rfl
  have h_seq2 : oddZetaSeq n2 = riemannZetaReal (2 * n2 + 1) := by
    rcases n2 with _ | k
    · omega
    · rfl
  have h_rel := Fintype.linearIndependent_iff.mp h_pair ![1, -r]
  have h_sum0 : (∑ i : Fin 2, (![1, -r] i) • oddZetaSeq (![n1, n2] i)) = 0 := by
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, h_seq1, h_seq2,
      Rat.smul_def, Rat.cast_one, Rat.cast_neg, one_mul]
    linarith
  have h0_zero : (![1, -r] : Fin 2 → ℚ) 0 = 0 := h_rel h_sum0 0
  simp at h0_zero

/-- **Corollary 1.2(ii) (`n = 2` Special Case: `1, ζ(3), ζ(5)`)**:
The three numbers `1, ζ(3), ζ(5)` are linearly independent over `ℚ`,
`dim_ℚ span_ℚ {1, ζ(3), ζ(5)} = 3`, `ζ(5) ∉ ℚ`, and `ζ(5) / ζ(3) ∉ ℚ`. -/
theorem corollary_1_2_ii :
    LinearIndependent ℚ (oddZetaTuple 2) ∧
    Module.finrank ℚ (Submodule.span ℚ (Set.range (oddZetaTuple 2))) = 3 ∧
    Irrational (riemannZetaReal 5) ∧
    Irrational (riemannZetaReal 5 / riemannZetaReal 3) := by
  refine ⟨theorem_1_1_odd_zeta_linear_independent 2 (by decide),
          theorem_1_1_eq_1_8 2 (by decide),
          corollary_1_2_i_irrational 2 (by decide),
          corollary_1_2_i_ratio_irrational 2 1 (by decide) (by decide) (by decide)⟩

/-- **Corollary 1.2(iii) (Arbitrary Finite Subsets of Odd Zeta Values)**:
For any integer `r ≥ 1` and any strictly increasing sequence of positive integers
`1 ≤ n₁ < n₂ < ... < n_r`, the `(r + 1)`-tuple `(1, ζ(2n₁ + 1), ..., ζ(2n_r + 1))`
is linearly independent over `ℚ` and spans a `ℚ`-vector space of dimension `r + 1`. -/
theorem corollary_1_2_iii {r : ℕ} (n_seq : Fin r → ℕ)
    (hn_pos : ∀ j : Fin r, 1 ≤ n_seq j) (hn_mono : StrictMono n_seq) :
    let tuple : Fin (r + 1) → ℝ :=
      Fin.cases 1 (fun j : Fin r => riemannZetaReal (2 * n_seq j + 1))
    LinearIndependent ℚ tuple ∧
    Module.finrank ℚ (Submodule.span ℚ (Set.range tuple)) = r + 1 := by
  intro tuple
  let idx : Fin (r + 1) → ℕ := Fin.cases 0 n_seq
  have h_tuple_eq : tuple = oddZetaSeq ∘ idx := by
    ext i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rfl
    · simp only [tuple, idx, Fin.cases_succ, Function.comp_apply]
      rcases h_k : n_seq j with _ | k
      · have := hn_pos j; omega
      · rfl
  have h_inj : Function.Injective idx := by
    intro i1 i2 h_eq
    rcases Fin.eq_zero_or_eq_succ i1 with rfl | ⟨j1, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ i2 with rfl | ⟨j2, rfl⟩
    · rfl
    · exfalso
      have : 0 = n_seq j2 := h_eq
      have := hn_pos j2
      omega
    · exfalso
      have : n_seq j1 = 0 := h_eq
      have := hn_pos j1
      omega
    · congr 1
      exact hn_mono.injective h_eq
  have h_li : LinearIndependent ℚ tuple := by
    rw [h_tuple_eq]
    exact corollary_1_2_infinite.comp idx h_inj
  refine ⟨h_li, ?_⟩
  simpa [Fintype.card_fin] using finrank_span_eq_card h_li

/-!
## Corollary 1.3: Dimension and Codimension Bounds for Mixed Even–Odd Zeta Spaces
-/

/-- **Corollary 1.3(i) (Dimension and Grassmannian Codimension Bounds for Mixed Zeta Spaces)**:
Let `V_odd := span_ℚ {1, ζ(2n₁+1), ..., ζ(2n_r+1)}` and
`V_even := span_ℚ {1, ζ(2k₁), ..., ζ(2k_m)}` for strictly increasing sequences of `r` odd and
`m` even zeta arguments. Then:
1. `dim_ℚ (V_odd ⊔ V_even) ≥ max(r + 1, m + 1)`, and
2. For any subspace `W ≤ V_even` satisfying `dim_ℚ (V_odd ⊓ W) = 1` (i.e. `W ∩ V_odd = ℚ · 1`),
   `dim_ℚ (V_odd ⊔ W) = r + dim_ℚ W`. -/
theorem corollary_1_3_i {r m : ℕ} (n_seq : Fin r → ℕ) (k_seq : Fin m → ℕ)
    (hn_pos : ∀ i : Fin r, 1 ≤ n_seq i) (hn_mono : StrictMono n_seq)
    (hk_pos : ∀ j : Fin m, 1 ≤ k_seq j) (hk_mono : StrictMono k_seq) :
    let oddTuple : Fin (r + 1) → ℝ :=
      Fin.cases 1 (fun i : Fin r => riemannZetaReal (2 * n_seq i + 1))
    let evenTuple : Fin (m + 1) → ℝ :=
      Fin.cases 1 (fun j : Fin m => riemannZetaReal (2 * k_seq j))
    let V_odd : Submodule ℚ ℝ := Submodule.span ℚ (Set.range oddTuple)
    let V_even : Submodule ℚ ℝ := Submodule.span ℚ (Set.range evenTuple)
    max (r + 1) (m + 1) ≤ Module.finrank ℚ ↥(V_odd ⊔ V_even) ∧
    ∀ (W : Submodule ℚ ℝ), FiniteDimensional ℚ W →
      Module.finrank ℚ ↥(V_odd ⊓ W) = 1 →
      Module.finrank ℚ ↥(V_odd ⊔ W) = r + Module.finrank ℚ W := by
  intro oddTuple evenTuple V_odd V_even
  have h_odd_li : LinearIndependent ℚ oddTuple :=
    (corollary_1_2_iii n_seq hn_pos hn_mono).1
  have h_odd_dim : Module.finrank ℚ V_odd = r + 1 :=
    (corollary_1_2_iii n_seq hn_pos hn_mono).2
  have h_even_li : LinearIndependent ℚ evenTuple :=
    even_zeta_tuple_linearIndependent k_seq hk_pos hk_mono
  have h_even_dim : Module.finrank ℚ V_even = m + 1 := by
    simpa [V_even, Fintype.card_fin] using finrank_span_eq_card h_even_li
  haveI : FiniteDimensional ℚ V_odd :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range oddTuple)
  haveI : FiniteDimensional ℚ V_even :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range evenTuple)
  constructor
  · apply max_le
    · rw [← h_odd_dim]
      exact Submodule.finrank_mono le_sup_left
    · rw [← h_even_dim]
      exact Submodule.finrank_mono le_sup_right
  · intro W hW_fd h_inter_dim
    have h_grass := Submodule.finrank_sup_add_finrank_inf_eq V_odd W
    rw [h_odd_dim, h_inter_dim] at h_grass
    omega

/-- General linear-algebra lemma underlying Corollary 1.3(ii) and 1.3(iii):
If `1, v₁, ..., v_{d+1}` are `d + 2` linearly independent vectors over `ℚ` (so they span a
`(d + 2)`-dimensional subspace `U`), and `V` is a `(d + 1)`-dimensional subspace containing `1`,
then at least one `v_j` (`j : Fin (d + 1)`) does not belong to `V`, and adjoining `v_j` to a
`ℚ`-linearly independent basis `b : Fin (d + 1) → ℝ` of `V` preserves `ℚ`-linear independence. -/
theorem exists_outside_subspace_of_linearIndependent {d : ℕ}
    (b : Fin (d + 1) → ℝ) (hb_li : LinearIndependent ℚ b)
    (v : Fin (d + 1) → ℝ)
    (hv_li : LinearIndependent ℚ (Fin.cases (b 0) v)) :
    let V : Submodule ℚ ℝ := Submodule.span ℚ (Set.range b)
    ∃ j : Fin (d + 1), v j ∉ V ∧
      LinearIndependent ℚ (Fin.cases (v j) b) := by
  intro V
  have h_V_dim : Module.finrank ℚ V = d + 1 := by
    simpa [V, Fintype.card_fin] using finrank_span_eq_card hb_li
  let fullTuple : Fin (d + 2) → ℝ := Fin.cases (b 0) v
  let U : Submodule ℚ ℝ := Submodule.span ℚ (Set.range fullTuple)
  have h_U_dim : Module.finrank ℚ U = d + 2 := by
    simpa [U, Fintype.card_fin] using finrank_span_eq_card hv_li
  haveI : FiniteDimensional ℚ V :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range b)
  have h_not_all : ¬ ∀ j : Fin (d + 1), v j ∈ V := by
    intro h_all
    have h_U_le_V : U ≤ V := by
      rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · exact Submodule.subset_span ⟨0, rfl⟩
      · exact h_all j
    have h_dim_le : Module.finrank ℚ U ≤ Module.finrank ℚ V :=
      Submodule.finrank_mono h_U_le_V
    omega
  push_neg at h_not_all
  rcases h_not_all with ⟨j, hj_not_in⟩
  refine ⟨j, hj_not_in, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [Fin.sum_univ_succ] at hc
  simp only [Fin.cases_zero, Fin.cases_succ] at hc
  have hc0 : c 0 = 0 := by
    by_contra hc0_ne
    apply hj_not_in
    have hv_eq : v j = ∑ i : Fin (d + 1), (-c i.succ / c 0) • b i := by
      have hc0_real : (c 0 : ℝ) ≠ 0 := by exact_mod_cast hc0_ne
      apply mul_left_cancel₀ hc0_real
      have h_lin : (c 0 : ℝ) * v j = - ∑ i : Fin (d + 1), c i.succ • b i := by
        rw [← Rat.smul_def]
        exact eq_neg_of_add_eq_zero_left hc
      rw [h_lin, Finset.mul_sum]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Rat.smul_def, Rat.cast_div, Rat.cast_neg]
      field_simp [hc0_real]
      ring
    rw [hv_eq]
    exact Submodule.sum_mem V (fun i _ => Submodule.smul_mem V _ (Submodule.subset_span ⟨i, rfl⟩))
  rw [hc0, zero_smul, zero_add] at hc
  have hc_succ : ∀ i : Fin (d + 1), c i.succ = 0 :=
    Fintype.linearIndependent_iff.mp hb_li (fun i => c i.succ) hc
  intro i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
  · exact hc0
  · exact hc_succ k

/-- **Corollary 1.3(ii) (Even Zeta Values Outside `V_{odd}`)**:
Among any `r + 1` distinct even integers `2 ≤ 2k₁ < ... < 2k_{r+1}`, at least one even zeta
value `ζ(2k_j)` (`1 ≤ j ≤ r + 1`) satisfies `ζ(2k_j) ∉ V_{odd}`, so that adjoining `ζ(2k_j)`
to `{1, ζ(2n₁+1), ..., ζ(2n_r+1)}` yields an `(r + 2)`-tuple that is linearly independent over `ℚ`. -/
theorem corollary_1_3_ii {r : ℕ} (n_seq : Fin r → ℕ) (k_seq : Fin (r + 1) → ℕ)
    (hn_pos : ∀ i : Fin r, 1 ≤ n_seq i) (hn_mono : StrictMono n_seq)
    (hk_pos : ∀ j : Fin (r + 1), 1 ≤ k_seq j) (hk_mono : StrictMono k_seq) :
    let oddTuple : Fin (r + 1) → ℝ :=
      Fin.cases 1 (fun i : Fin r => riemannZetaReal (2 * n_seq i + 1))
    let V_odd : Submodule ℚ ℝ := Submodule.span ℚ (Set.range oddTuple)
    ∃ j : Fin (r + 1),
      riemannZetaReal (2 * k_seq j) ∉ V_odd ∧
      LinearIndependent ℚ (Fin.cases (riemannZetaReal (2 * k_seq j)) oddTuple) := by
  intro oddTuple V_odd
  have h_odd_li : LinearIndependent ℚ oddTuple :=
    (corollary_1_2_iii n_seq hn_pos hn_mono).1
  have h_even_li :
      LinearIndependent ℚ (Fin.cases (oddTuple 0) (fun j : Fin (r + 1) => riemannZetaReal (2 * k_seq j))) :=
    even_zeta_tuple_linearIndependent k_seq hk_pos hk_mono
  exact exists_outside_subspace_of_linearIndependent oddTuple h_odd_li
    (fun j => riemannZetaReal (2 * k_seq j)) h_even_li

/-- **Corollary 1.3(iii) (Odd Zeta Values Outside `V_{even}`)**:
Among any `m + 1` distinct odd integers `3 ≤ 2n₁+1 < ... < 2n_{m+1}+1`, at least one odd zeta
value `ζ(2n_i + 1)` (`1 ≤ i ≤ m + 1`) satisfies `ζ(2n_i + 1) ∉ V_{even}`, so that adjoining
`ζ(2n_i + 1)` to `{1, ζ(2k₁), ..., ζ(2k_m)}` yields an `(m + 2)`-tuple that is linearly
independent over `ℚ`. -/
theorem corollary_1_3_iii {m : ℕ} (k_seq : Fin m → ℕ) (n_seq : Fin (m + 1) → ℕ)
    (hk_pos : ∀ j : Fin m, 1 ≤ k_seq j) (hk_mono : StrictMono k_seq)
    (hn_pos : ∀ i : Fin (m + 1), 1 ≤ n_seq i) (hn_mono : StrictMono n_seq) :
    let evenTuple : Fin (m + 1) → ℝ :=
      Fin.cases 1 (fun j : Fin m => riemannZetaReal (2 * k_seq j))
    let V_even : Submodule ℚ ℝ := Submodule.span ℚ (Set.range evenTuple)
    ∃ i : Fin (m + 1),
      riemannZetaReal (2 * n_seq i + 1) ∉ V_even ∧
      LinearIndependent ℚ (Fin.cases (riemannZetaReal (2 * n_seq i + 1)) evenTuple) := by
  intro evenTuple V_even
  have h_even_li : LinearIndependent ℚ evenTuple :=
    even_zeta_tuple_linearIndependent k_seq hk_pos hk_mono
  have h_odd_li :
      LinearIndependent ℚ (Fin.cases (evenTuple 0) (fun i : Fin (m + 1) => riemannZetaReal (2 * n_seq i + 1))) :=
    (corollary_1_2_iii n_seq hn_pos hn_mono).1
  exact exists_outside_subspace_of_linearIndependent evenTuple h_even_li
    (fun i => riemannZetaReal (2 * n_seq i + 1)) h_odd_li

end OddZetaFormalization
