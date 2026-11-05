import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Data.Real.Irrational
import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

/-!
# Section 1 Preliminaries: Riemann Zeta Values at Positive Integers and Classical Literature Results

This module formalizes Equation (1.1), Equation (1.2), the tuple of odd zeta values
`1, ζ(3), ζ(5), ..., ζ(2n+1)`, and the classical peer-reviewed theorems cited in Section 1
of Prince Anand, *"All Odd Zeta Values Are Linearly Independent Over ℚ"*:
1. **Apéry's Theorem (1978/1979)** [1]: `ζ(3) ∉ ℚ` (base case `n = 1` of Theorem 1.1).
2. **Lindemann's Theorem (1882)** [17]: `π` is transcendental over `ℚ`.
3. **Euler's Even Zeta Formula (1740)** [7]: `ζ(2k) = ρ_k π^{2k}` with `ρ_k ∈ ℚ \ {0}`,
   proved unconditionally from `hasSum_zeta_nat` in `Mathlib.NumberTheory.ZetaValues`.
-/

namespace OddZetaFormalization

open scoped BigOperators

/-- **Equation (1.1)**: The real Riemann zeta value at an integer `s`
$$\zeta(s) := \sum_{m=1}^{\infty} \frac{1}{m^s} = \sum_{m=0}^{\infty} \frac{1}{(m+1)^s}.$$ -/
noncomputable def riemannZetaReal (s : ℕ) : ℝ :=
  ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 1) ^ s

/-- Summability of the defining series (1.1) for `s ≥ 2`. -/
theorem summable_riemannZetaReal {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ s) := by
  have hs1 : 1 < s := lt_of_lt_of_le (by decide : 1 < 2) hs
  have h_pseries : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ s) :=
    Real.summable_one_div_nat_pow.mpr hs1
  have h_shift := (summable_nat_add_iff (f := fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ s) 1).mpr h_pseries
  exact h_shift.congr (fun m => by push_cast; rfl)

/-- For every integer `s ≥ 2`, `ζ(s) > 0`. -/
theorem riemannZetaReal_pos {s : ℕ} (hs : 2 ≤ s) : 0 < riemannZetaReal s := by
  unfold riemannZetaReal
  have hsum := summable_riemannZetaReal hs
  have h0 : (0 : ℝ) < (1 : ℝ) / (((0 : ℕ) : ℝ) + 1) ^ s := by simp
  have hnonneg : ∀ m : ℕ, 0 ≤ (1 : ℝ) / ((m : ℝ) + 1) ^ s := fun m => by positivity
  exact lt_of_lt_of_le h0 (le_tsum hsum 0 (fun m _ => hnonneg m))

/-- For every integer `s ≥ 2`, `ζ(s) ≠ 0`. -/
theorem riemannZetaReal_ne_zero {s : ℕ} (hs : 2 ≤ s) : riemannZetaReal s ≠ 0 :=
  ne_of_gt (riemannZetaReal_pos hs)

/-- The `(n + 1)`-tuple of real numbers `(1, ζ(3), ζ(5), ..., ζ(2n + 1))` from Equation (1.6),
indexed by `Fin (n + 1)` where index `0` is `1` and index `j.succ` (`0 ≤ j < n`) is `ζ(2j + 3)`. -/
noncomputable def oddZetaTuple (n : ℕ) : Fin (n + 1) → ℝ :=
  Fin.cases 1 (fun j : Fin n => riemannZetaReal (2 * (j.val + 1) + 1))

@[simp]
theorem oddZetaTuple_zero (n : ℕ) : oddZetaTuple n 0 = 1 := rfl

@[simp]
theorem oddZetaTuple_succ (n : ℕ) (j : Fin n) :
    oddZetaTuple n j.succ = riemannZetaReal (2 * (j.val + 1) + 1) := rfl

/-- The infinite sequence `{1, ζ(3), ζ(5), ζ(7), ...}` from Equation (1.9), indexed by `ℕ`
where `0 ↦ 1` and `n + 1 ↦ ζ(2n + 3)`. -/
noncomputable def oddZetaSeq : ℕ → ℝ
  | 0 => 1
  | k + 1 => riemannZetaReal (2 * (k + 1) + 1)

@[simp]
theorem oddZetaSeq_zero : oddZetaSeq 0 = 1 := rfl

@[simp]
theorem oddZetaSeq_succ (k : ℕ) : oddZetaSeq (k + 1) = riemannZetaReal (2 * (k + 1) + 1) := rfl

theorem oddZetaTuple_eq_oddZetaSeq (n : ℕ) (i : Fin (n + 1)) :
    oddZetaTuple n i = oddZetaSeq i.val := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩ <;> rfl

/-!
## Classical Literature Results and Unconditional Proof of Euler's Even Zeta Formula
-/

/-- **External Axiom 1 (Apéry's Theorem, 1978/1979)**:
R. Apéry, *"Irrationalité de ζ(2) et ζ(3)"*, Astérisque 61 (1979), 11–13.
States that `ζ(3)` is irrational (`ζ(3) ∉ ℚ`). -/
axiom apery_theorem_zeta_three_irrational : Irrational (riemannZetaReal 3)

/-- **External Axiom 2 (Lindemann's Theorem, 1882)**:
F. Lindemann, *"Über die Zahl π"*, Math. Ann. 20 (1882), no. 2, 213–225.
States that `π` is transcendental over `ℚ`. -/
axiom lindemann_pi_transcendental : Transcendental ℚ Real.pi

/-- **Euler's Even Zeta Formula (1740, Equation (1.2), Proved Unconditionally via Mathlib)**:
For every integer `k ≥ 1`, `ζ(2k)` is a non-zero rational multiple `ρ_k ∈ ℚ \ {0}` of `π^{2k}`,
where `ρ_k = (-1)^{k+1} 2^{2k-1} B_{2k} / (2k)!`. Proved directly from `hasSum_zeta_nat` in
`Mathlib.NumberTheory.ZetaValues`. -/
theorem euler_even_zeta_rational_multiple (k : ℕ) (hk : 1 ≤ k) :
    ∃ ρ : ℚ, ρ ≠ 0 ∧ riemannZetaReal (2 * k) = (ρ : ℝ) * Real.pi ^ (2 * k) := by
  let ρ : ℚ :=
    (-1 : ℚ) ^ (k + 1) * (2 : ℚ) ^ (2 * k - 1) * bernoulli (2 * k) / ((2 * k).factorial : ℚ)
  have h_sum_zero := hasSum_zeta_nat (by omega : k ≠ 0)
  have h_shift :=
    (hasSum_nat_add_iff' 1 (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (2 * k))).mpr h_sum_zero
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by omega : 2 * k ≠ 0),
    div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h_shift
  have h_eq : riemannZetaReal (2 * k) = (ρ : ℝ) * Real.pi ^ (2 * k) := by
    unfold riemannZetaReal
    rw [h_shift.tsum_eq]
    dsimp [ρ]
    push_cast
    ring
  have hρ_ne : ρ ≠ 0 := by
    intro h0
    have h_zeta_ne : riemannZetaReal (2 * k) ≠ 0 :=
      riemannZetaReal_ne_zero (by omega)
    rw [h_eq, h0, Rat.cast_zero, zero_mul] at h_zeta_ne
    exact h_zeta_ne rfl
  exact ⟨ρ, hρ_ne, h_eq⟩

/-- If `x ∈ ℝ` is irrational, then the 2-tuple `(1, x) : Fin 2 → ℝ` is linearly independent over `ℚ`. -/
theorem linearIndependent_one_and_irrational {x : ℝ} (hx : Irrational x) :
    LinearIndependent ℚ ![1, x] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hsum : (g 0 : ℝ) + (g 1 : ℝ) * x = 0 := by
    have h0 := hg
    rw [Fin.sum_univ_two] at h0
    simpa [Rat.smul_def] using h0
  have hg1 : g 1 = 0 := by
    by_contra h1
    have h1_real : (g 1 : ℝ) ≠ 0 := by exact_mod_cast h1
    have hx_eq : x = ((-g 0 / g 1 : ℚ) : ℝ) := by
      push_cast
      rw [eq_div_iff h1_real]
      linarith
    exact hx ⟨-g 0 / g 1, hx_eq.symm⟩
  have hg0 : g 0 = 0 := by
    rw [hg1, Rat.cast_zero, zero_mul, add_zero] at hsum
    exact_mod_cast hsum
  fin_cases i
  · exact hg0
  · exact hg1

/-- **Base Case `n = 1` of Theorem 1.1**: The numbers `1` and `ζ(3)` (`oddZetaTuple 1`)
are linearly independent over `ℚ` by Apéry's theorem. -/
theorem odd_zeta_base_case_n1 : LinearIndependent ℚ (oddZetaTuple 1) := by
  have h_eq : oddZetaTuple 1 = ![1, riemannZetaReal 3] := by
    ext i
    fin_cases i <;> rfl
  rw [h_eq]
  exact linearIndependent_one_and_irrational apery_theorem_zeta_three_irrational

/-- By Lindemann's theorem, `π²` is transcendental over `ℚ`. -/
theorem transcendental_pi_sq : Transcendental ℚ (Real.pi ^ 2) := by
  intro h_alg
  rcases h_alg with ⟨p, hp_ne, hp_eval⟩
  let q : Polynomial ℚ := Polynomial.expand ℚ 2 p
  have hq_ne : q ≠ 0 := by
    intro hq0
    apply hp_ne
    apply Polynomial.expand_injective (by decide : 0 < 2)
    simpa [q] using hq0
  have hq_eval : Polynomial.aeval Real.pi q = 0 := by
    rw [show q = p.comp (Polynomial.X ^ 2) from Polynomial.expand_eq_comp_X_pow 2]
    simpa [Polynomial.aeval_comp] using hp_eval
  exact lindemann_pi_transcendental ⟨q, hq_ne, hq_eval⟩

/-- A non-zero rational polynomial evaluated at `π²` is never zero. -/
theorem aeval_pi_sq_ne_zero {P : Polynomial ℚ} (hP : P ≠ 0) :
    Polynomial.aeval (Real.pi ^ 2) P ≠ 0 := by
  intro h_zero
  exact transcendental_pi_sq ⟨P, hP, h_zero⟩

/-- For any strictly increasing sequence of positive integers `1 ≤ k₁ < k₂ < ... < k_m`,
the `(m + 1)`-tuple `(1, ζ(2k₁), ..., ζ(2k_m))` is linearly independent over `ℚ`
(Section 1.1, following Equation (1.2)). -/
theorem even_zeta_tuple_linearIndependent {m : ℕ} (k : Fin m → ℕ)
    (hk_pos : ∀ j : Fin m, 1 ≤ k j) (hk_mono : StrictMono k) :
    LinearIndependent ℚ (Fin.cases (1 : ℝ) (fun j : Fin m => riemannZetaReal (2 * k j))) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h_choose : ∀ j : Fin m, ∃ ρ : ℚ, ρ ≠ 0 ∧ riemannZetaReal (2 * k j) = (ρ : ℝ) * Real.pi ^ (2 * k j) :=
    fun j => euler_even_zeta_rational_multiple (k j) (hk_pos j)
  choose ρ hρ_ne hρ_eq using h_choose
  let P : Polynomial ℚ :=
    Polynomial.C (c 0) + ∑ j : Fin m, Polynomial.monomial (k j) (c j.succ * ρ j)
  have hP_eval : Polynomial.aeval (Real.pi ^ 2) P = 0 := by
    have h_sum_split :
        (∑ i : Fin (m + 1), c i • (Fin.cases (1 : ℝ) (fun j : Fin m => riemannZetaReal (2 * k j)) i)) =
        c 0 • (1 : ℝ) + ∑ j : Fin m, c j.succ • riemannZetaReal (2 * k j) :=
      Fin.sum_univ_succ _
    rw [h_sum_split] at hc
    have h_terms : ∀ j : Fin m,
        Polynomial.aeval (Real.pi ^ 2) (Polynomial.monomial (k j) (c j.succ * ρ j)) =
          c j.succ • riemannZetaReal (2 * k j) := by
      intro j
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, hρ_eq j]
      simp only [Rat.smul_def, Rat.cast_mul]
      rw [← pow_mul]
      ring
    calc
      Polynomial.aeval (Real.pi ^ 2) P
          = Polynomial.aeval (Real.pi ^ 2) (Polynomial.C (c 0)) +
              ∑ j : Fin m, Polynomial.aeval (Real.pi ^ 2) (Polynomial.monomial (k j) (c j.succ * ρ j)) := by
            simp only [P, map_add, map_sum]
      _ = c 0 • (1 : ℝ) + ∑ j : Fin m, c j.succ • riemannZetaReal (2 * k j) := by
            rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Finset.sum_congr rfl (fun j _ => h_terms j)]
      _ = 0 := hc
  have hP_zero : P = 0 := by
    by_contra hP_ne
    exact aeval_pi_sq_ne_zero hP_ne hP_eval
  have h_coeff_pos : ∀ j : Fin m, P.coeff (k j) = c j.succ * ρ j := by
    intro j
    simp only [P, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.finset_sum_coeff,
      Polynomial.coeff_monomial]
    have hk_ne_zero : k j ≠ 0 := Nat.pos_iff_ne_zero.mp (hk_pos j)
    rw [if_neg hk_ne_zero, zero_add]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      have h_ne : k b ≠ k j := hk_mono.injective.ne hbj
      exact if_neg h_ne
    · intro hj_absurd
      exact False.elim (hj_absurd (Finset.mem_univ j))
  have hc_succ : ∀ j : Fin m, c j.succ = 0 := by
    intro j
    have hcj : c j.succ * ρ j = 0 := by
      rw [← h_coeff_pos j, hP_zero, Polynomial.coeff_zero]
    rcases mul_eq_zero.mp hcj with h1 | h2
    · exact h1
    · exact False.elim (hρ_ne j h2)
  have hc0 : c 0 = 0 := by
    have h0 : P.coeff 0 = c 0 := by
      simp only [P, Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.finset_sum_coeff,
        Polynomial.coeff_monomial]
      have h_sum0 : (∑ x : Fin m, if k x = 0 then c x.succ * ρ x else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        rw [if_neg (Nat.pos_iff_ne_zero.mp (hk_pos x))]
      rw [h_sum0, add_zero]
    rw [← h0, hP_zero, Polynomial.coeff_zero]
  intro i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · exact hc0
  · exact hc_succ j

end OddZetaFormalization
