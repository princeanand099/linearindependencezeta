import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.Algebra.Order.Floor
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
`1, ζ(3), ζ(5), ..., ζ(2n+1)`, and the classical results cited in Section 1
of Prince Anand, *"All Odd Zeta Values Are Linearly Independent Over ℚ"*:
1. **Unconditional Irrationality of `π²` and `ζ(2)`** (`irrational_pi_sq`, `irrational_riemannZetaReal_two`):
   Proved from the ground up in Lean 4 + Mathlib4 via Cartwright's integral recurrence and even-degree
   integer polynomials `sinEvenPoly`.
2. **Lindemann's Theorem (1882)** [17]: `π` is transcendental over `ℚ`.
3. **Euler's Even Zeta Formula (1740)** [7]: `ζ(2k) = ρ_k π^{2k}` with `ρ_k ∈ ℚ \ {0}`,
   proved unconditionally from `hasSum_zeta_nat` in `Mathlib.NumberTheory.ZetaValues`.
-/

namespace OddZetaFormalization

open scoped BigOperators Nat
open intervalIntegral MeasureTheory.MeasureSpace Set Polynomial Real Filter

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

/-- **Base Case `n = 0`**: The singleton tuple `(1)` (`oddZetaTuple 0`) is linearly independent over `ℚ`. -/
theorem odd_zeta_base_case_n0 : LinearIndependent ℚ (oddZetaTuple 0) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hi0 : i = 0 := Fin.eq_zero i
  subst hi0
  simpa [Fin.sum_univ_one, oddZetaTuple] using hg

/-!
## Ground-Up Unconditional Proof of `Irrational (Real.pi ^ 2)` and `Irrational (riemannZetaReal 2)`

We adapt Cartwright's integral recurrence `I n θ = ∫ x in (-1)..1, (1 - x ^ 2) ^ n * cos (x * θ)`
by observing that `sinPoly n` contains only even powers of `θ`, i.e.,
`sinPoly n θ = sinEvenPoly n (θ ^ 2)` where `(sinEvenPoly n).natDegree ≤ n`.
Evaluating at `θ = π / 2` where `sin (π / 2) = 1` and `cos (π / 2) = 0` yields
`(π / 2) * I n (π / 2) * ((π / 2) ^ 2) ^ n = n! * sinEvenPoly n ((π / 2) ^ 2)`,
proving `Irrational (Real.pi ^ 2)` and `Irrational (riemannZetaReal 2)` with zero custom axioms.
-/

private noncomputable def cartwrightI (n : ℕ) (θ : ℝ) : ℝ :=
  ∫ x in (-1)..1, (1 - x ^ 2) ^ n * cos (x * θ)

private lemma cartwrightI_zero (θ : ℝ) : cartwrightI 0 θ * θ = 2 * sin θ := by
  rw [mul_comm, cartwrightI]
  simp [mul_integral_comp_mul_right, two_mul]

private lemma cartwright_recursion' (n : ℕ) (θ : ℝ) :
    cartwrightI (n + 1) θ * θ ^ 2 = - (2 * 2 * ((n + 1) * (0 ^ n * cos θ))) +
      2 * (n + 1) * (2 * n + 1) * cartwrightI n θ -
      4 * (n + 1) * n * cartwrightI (n - 1) θ := by
  rw [cartwrightI]
  let f (x : ℝ) : ℝ := 1 - x ^ 2
  let u₁ (x : ℝ) : ℝ := f x ^ (n + 1)
  let u₁' (x : ℝ) : ℝ := - (2 * (n + 1) * x * f x ^ n)
  let v₁ (x : ℝ) : ℝ := sin (x * θ)
  let v₁' (x : ℝ) : ℝ := cos (x * θ) * θ
  let u₂ (x : ℝ) : ℝ := x * (f x) ^ n
  let u₂' (x : ℝ) : ℝ := (f x) ^ n - 2 * n * x ^ 2 * (f x) ^ (n - 1)
  let v₂ (x : ℝ) : ℝ := cos (x * θ)
  let v₂' (x : ℝ) : ℝ := -sin (x * θ) * θ
  have hfd : Continuous f := by fun_prop
  have hu₁d : Continuous u₁' := by fun_prop
  have hv₁d : Continuous v₁' := by fun_prop
  have hu₂d : Continuous u₂' := by fun_prop
  have hv₂d : Continuous v₂' := by fun_prop
  have hu₁_eval_one : u₁ 1 = 0 := by simp only [u₁, f]; simp
  have hu₁_eval_neg_one : u₁ (-1) = 0 := by simp only [u₁, f]; simp
  have t : u₂ 1 * v₂ 1 - u₂ (-1) * v₂ (-1) = 2 * (0 ^ n * cos θ) := by simp [u₂, v₂, f, ← two_mul]
  have hf (x) : HasDerivAt f (- 2 * x) x := by
    convert (hasDerivAt_pow 2 x).const_sub 1 using 1
    simp
  have hu₁ (x) : HasDerivAt u₁ (u₁' x) x := by
    convert (hf x).pow _ using 1
    simp only [Nat.add_succ_sub_one, u₁', Nat.cast_add_one]
    ring
  have hv₁ (x) : HasDerivAt v₁ (v₁' x) x := (hasDerivAt_mul_const θ).sin
  have hu₂ (x) : HasDerivAt u₂ (u₂' x) x := by
    convert (hasDerivAt_id' x).mul ((hf x).pow _) using 1
    simp only [u₂']
    ring
  have hv₂ (x) : HasDerivAt v₂ (v₂' x) x := (hasDerivAt_mul_const θ).cos
  convert_to (∫ (x : ℝ) in (-1)..1, u₁ x * v₁' x) * θ = _ using 1
  · simp_rw [u₁, v₁', f, ← intervalIntegral.integral_mul_const, sq θ, mul_assoc]
  rw [integral_mul_deriv_eq_deriv_mul (fun x _ => hu₁ x) (fun x _ => hv₁ x)
    (hu₁d.intervalIntegrable _ _) (hv₁d.intervalIntegrable _ _), hu₁_eval_one, hu₁_eval_neg_one,
    zero_mul, zero_mul, sub_zero, zero_sub, ← integral_neg, ← integral_mul_const]
  convert_to ((-2 : ℝ) * (n + 1)) * ∫ (x : ℝ) in (-1)..1, (u₂ x * v₂' x) = _ using 1
  · rw [← integral_const_mul]
    congr 1 with x
    dsimp [u₁', v₁, u₂, v₂']
    ring
  rw [integral_mul_deriv_eq_deriv_mul (fun x _ => hu₂ x) (fun x _ => hv₂ x)
    (hu₂d.intervalIntegrable _ _) (hv₂d.intervalIntegrable _ _),
    mul_sub, t, neg_mul, neg_mul, neg_mul, sub_neg_eq_add]
  have (x) : u₂' x = (2 * n + 1) * f x ^ n - 2 * n * f x ^ (n - 1) := by
    cases n with
    | zero => simp [u₂']
    | succ n => ring!
  simp_rw [this, sub_mul, mul_assoc _ _ (v₂ _)]
  have : Continuous v₂ := by fun_prop
  rw [mul_mul_mul_comm, integral_sub, mul_sub, add_sub_assoc]
  · congr 1
    simp_rw [integral_const_mul]
    ring!
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

private lemma cartwright_recursion (n : ℕ) (θ : ℝ) :
    cartwrightI (n + 2) θ * θ ^ 2 =
      2 * (n + 2) * (2 * n + 3) * cartwrightI (n + 1) θ -
      4 * (n + 2) * (n + 1) * cartwrightI n θ := by
  rw [cartwright_recursion' (n + 1) θ]
  simp
  ring!

private lemma cartwrightI_one (θ : ℝ) :
    cartwrightI 1 θ * θ ^ 3 = 4 * sin θ - 4 * θ * cos θ := by
  rw [_root_.pow_succ, ← mul_assoc, cartwright_recursion' 0 θ, sub_mul, add_mul,
    mul_assoc _ (cartwrightI 0 θ), cartwrightI_zero]
  ring

private noncomputable def sinEvenPoly : ℕ → ℤ[X]
  | 0 => C 2
  | 1 => C 4
  | (n + 2) => ((2 : ℤ) * (2 * n + 3)) • sinEvenPoly (n + 1) + monomial 1 (-4) * sinEvenPoly n

private noncomputable def cosCartwrightPoly : ℕ → ℤ[X]
  | 0 => 0
  | 1 => monomial 1 (-4)
  | (n + 2) => ((2 : ℤ) * (2 * n + 3)) • cosCartwrightPoly (n + 1) +
      monomial 2 (-4) * cosCartwrightPoly n

private lemma sinEvenPoly_natDegree_le : ∀ n : ℕ, (sinEvenPoly n).natDegree ≤ n
  | 0 => by simp [sinEvenPoly]
  | 1 => by simp [sinEvenPoly]
  | n + 2 => by
      rw [sinEvenPoly]
      refine natDegree_add_le_of_degree_le ((natDegree_smul_le _ _).trans ?_) ?_
      · exact (sinEvenPoly_natDegree_le (n + 1)).trans (by omega)
      refine natDegree_mul_le.trans ?_
      have h1 : (monomial 1 (-4 : ℤ)).natDegree ≤ 1 := natDegree_monomial_le (-4)
      have h2 := sinEvenPoly_natDegree_le n
      omega

private lemma sinEvenPoly_add_cosCartwrightPoly_eval (θ : ℝ) :
    ∀ n : ℕ,
      cartwrightI n θ * θ ^ (2 * n + 1) =
        n ! * ((sinEvenPoly n).eval₂ (Int.castRingHom ℝ) (θ ^ 2) * sin θ +
          (cosCartwrightPoly n).eval₂ (Int.castRingHom ℝ) θ * cos θ)
  | 0 => by simp [sinEvenPoly, cosCartwrightPoly, cartwrightI_zero]
  | 1 => by simp [cartwrightI_one, sinEvenPoly, cosCartwrightPoly, sub_eq_add_neg]
  | n + 2 => by
      calc cartwrightI (n + 2) θ * θ ^ (2 * (n + 2) + 1)
          = cartwrightI (n + 2) θ * θ ^ 2 * θ ^ (2 * n + 3) := by ring
        _ = 2 * (n + 2) * (2 * n + 3) * (cartwrightI (n + 1) θ * θ ^ (2 * (n + 1) + 1)) -
            4 * (n + 2) * (n + 1) * θ ^ 2 * (cartwrightI n θ * θ ^ (2 * n + 1)) := by
              rw [cartwright_recursion]; ring
        _ = _ := by
              simp [sinEvenPoly_add_cosCartwrightPoly_eval, sinEvenPoly, cosCartwrightPoly,
                Nat.factorial_succ]
              ring

private lemma intPoly_eval_rat_mul_pow {p : ℤ[X]} (a b : ℤ) {k : ℕ} (hp : p.natDegree ≤ k) :
    ∃ z : ℤ, p.eval₂ (Int.castRingHom ℝ) (a / b) * (b : ℝ) ^ k = z := by
  rcases eq_or_ne b 0 with rfl | hb
  · rcases k.eq_zero_or_pos with rfl | hk
    · exact ⟨p.coeff 0, by simp⟩
    exact ⟨0, by simp [hk.ne']⟩
  refine ⟨∑ i ∈ p.support, p.coeff i * a ^ i * b ^ (k - i), ?_⟩
  conv => lhs; rw [← sum_monomial_eq p]
  rw [eval₂_sum, sum, Finset.sum_mul, Int.cast_sum]
  simp only [eval₂_monomial, eq_intCast, div_pow, Int.cast_mul, Int.cast_pow]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have ik := (le_natDegree_of_mem_supp i hi).trans hp
  rw [mul_assoc, div_mul_comm, ← Int.cast_pow, ← Int.cast_pow, ← Int.cast_pow,
    ← pow_sub_mul_pow b ik, ← Int.cast_div_charZero, Int.mul_ediv_cancel _ (pow_ne_zero _ hb),
    ← mul_assoc, mul_right_comm, ← Int.cast_pow]
  exact dvd_mul_left _ _

private lemma cartwrightI_pos (n : ℕ) : 0 < cartwrightI n (Real.pi / 2) := by
  refine integral_pos (by norm_num) (Continuous.continuousOn (by continuity)) ?_ ⟨0, by simp⟩
  refine fun x hx => mul_nonneg (pow_nonneg ?_ _) ?_
  · rw [sub_nonneg, sq_le_one_iff_abs_le_one, abs_le]
    exact ⟨hx.1.le, hx.2⟩
  refine cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_ <;>
  nlinarith [hx.1, hx.2, Real.pi_pos]

private lemma cartwrightI_le (n : ℕ) : cartwrightI n (Real.pi / 2) ≤ 2 := by
  rw [← norm_of_nonneg (cartwrightI_pos n).le]
  refine (norm_integral_le_of_norm_le_const ?_).trans (show (1 : ℝ) * _ ≤ _ by norm_num)
  intros x hx
  simp only [uIoc_of_le, neg_le_self_iff, zero_le_one, mem_Ioc] at hx
  rw [norm_eq_abs, abs_mul, abs_pow]
  refine mul_le_one₀ (pow_le_one₀ (abs_nonneg _) ?_) (abs_nonneg _) (abs_cos_le_one _)
  rw [abs_le]
  constructor <;> nlinarith

/-- **Unconditional Irrationality of `π²` (`π² ∉ ℚ`)**:
Proved directly from Cartwright's integral identity and `sinEvenPoly` with zero custom axioms. -/
theorem irrational_pi_sq : Irrational (Real.pi ^ 2) := by
  have h_div4 : Irrational ((Real.pi / 2) ^ 2) := by
    by_contra h_rat
    rw [Irrational, not_not, Set.mem_range] at h_rat
    rcases h_rat with ⟨q, hq⟩
    let a : ℤ := q.num
    let b : ℕ := q.den
    have hb : 0 < b := q.pos
    have h_ab : ((Real.pi / 2) ^ 2 : ℝ) = (a : ℝ) / (b : ℝ) := by
      rw [← hq]
      exact_mod_cast (Rat.num_div_den q).symm
    have ha : (0 : ℝ) < (a : ℝ) := by
      have h_pos : (0 : ℝ) < (a : ℝ) / (b : ℝ) := by
        rw [← h_ab]
        exact sq_pos_of_pos Real.pi_div_two_pos
      rwa [lt_div_iff₀ (by positivity), zero_mul] at h_pos
    have h_tendsto :
        Tendsto (fun n : ℕ => Real.pi * ((a : ℝ) ^ n / (n ! : ℝ))) atTop (nhds 0) := by
      rw [← mul_zero Real.pi]
      exact (FloorSemiring.tendsto_pow_div_factorial_atTop (a : ℝ)).const_mul Real.pi
    have h_ev :
        ∀ᶠ n : ℕ in atTop,
          (Real.pi / 2) * ((a : ℝ) ^ n / (n ! : ℝ)) * cartwrightI n (Real.pi / 2) < 1 := by
      have h_lt := h_tendsto.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)
      filter_upwards [h_lt] with n hn
      have hI_le := cartwrightI_le n
      have h_pi2_pos : 0 < Real.pi / 2 := Real.pi_div_two_pos
      have h_nonneg : 0 ≤ (Real.pi / 2) * ((a : ℝ) ^ n / (n ! : ℝ)) := by
        positivity
      have h_prod :
          (Real.pi / 2) * ((a : ℝ) ^ n / (n ! : ℝ)) * cartwrightI n (Real.pi / 2) ≤
            Real.pi * ((a : ℝ) ^ n / (n ! : ℝ)) := by
        calc (Real.pi / 2) * ((a : ℝ) ^ n / (n ! : ℝ)) * cartwrightI n (Real.pi / 2)
            ≤ (Real.pi / 2) * ((a : ℝ) ^ n / (n ! : ℝ)) * 2 :=
              mul_le_mul_of_nonneg_left hI_le h_nonneg
          _ = Real.pi * ((a : ℝ) ^ n / (n ! : ℝ)) := by ring
      exact lt_of_le_of_lt h_prod hn
    obtain ⟨n, hn_lt⟩ := h_ev.exists
    have hn_pos :
        0 < (Real.pi / 2) * ((a : ℝ) ^ n / (n ! : ℝ)) * cartwrightI n (Real.pi / 2) := by
      have h1 : 0 < Real.pi / 2 := Real.pi_div_two_pos
      have h2 : 0 < (a : ℝ) ^ n / (n ! : ℝ) := by positivity
      exact mul_pos (mul_pos h1 h2) (cartwrightI_pos n)
    obtain ⟨z, hz⟩ :
        ∃ z : ℤ,
          (sinEvenPoly n).eval₂ (Int.castRingHom ℝ) ((a : ℝ) / (b : ℝ)) * ((b : ℤ) : ℝ) ^ n = z :=
      intPoly_eval_rat_mul_pow a (b : ℤ) (sinEvenPoly_natDegree_le n)
    have h_eval := sinEvenPoly_add_cosCartwrightPoly_eval (Real.pi / 2) n
    rw [Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, mul_one, add_zero] at h_eval
    have h_pow_split :
        (Real.pi / 2) ^ (2 * n + 1) = (Real.pi / 2) * (((Real.pi / 2) ^ 2) ^ n) := by
      rw [_root_.pow_succ', pow_mul]
    rw [h_pow_split, h_ab] at h_eval
    have h_eq_z :
        (Real.pi / 2) * ((a : ℝ) ^ n / (n ! : ℝ)) * cartwrightI n (Real.pi / 2) = (z : ℝ) := by
      rw [← hz]
      have h_b_ne : (b : ℝ) ≠ 0 := by positivity
      have h_fac_ne : (n ! : ℝ) ≠ 0 := by positivity
      simp only [Int.cast_natCast]
      rw [div_pow] at h_eval
      field_simp at h_eval ⊢
      linear_combination h_eval
    have h_z_bounds : (0 : ℝ) < (z : ℝ) ∧ (z : ℝ) < 1 := by
      rw [← h_eq_z]
      exact ⟨hn_pos, hn_lt⟩
    norm_cast at h_z_bounds
    omega
  intro ⟨r, hr⟩
  apply h_div4
  refine ⟨r / 4, ?_⟩
  push_cast
  calc ((r : ℝ) / 4) = (Real.pi ^ 2) / 4 := by rw [hr]
    _ = (Real.pi / 2) ^ 2 := by ring

/-!
## Classical Literature Results and Unconditional Proof of Euler's Even Zeta Formula
-/

/-- **External Axiom (Lindemann's Theorem, 1882)**:
F. Lindemann, *"Über die Zahl π"*, Math. Ann. 20 (1882), no. 2, 213–225.
States that `π` is transcendental over `ℚ` (used for general degree `m ≥ 2` even-zeta tuples). -/
axiom lindemann_pi_transcendental : Transcendental ℚ Real.pi

/-- **Euler's Even Zeta Formula (1740, Equation (1.2), Proved Unconditionally via Mathlib)**:
For every integer `k ≥ 1`, `ζ(2k)` is a non-zero rational multiple `ρ_k ∈ ℚ \ {0}` of `π^{2k}`,
where `ρ_k = (-1)^{k+1} 2^{2k-1} B_{2k} / (2k)!`. Proved directly from `hasSum_zeta_nat` in
`Mathlib.NumberTheory.ZetaValues`. -/
theorem euler_even_zeta_rational_multiple (k : ℕ) (hk : 1 ≤ k) :
    ∃ ρ : ℚ, ρ ≠ 0 ∧ riemannZetaReal (2 * k) = (ρ : ℝ) * Real.pi ^ (2 * k) := by
  let ρ : ℚ :=
    (-1 : ℚ) ^ (k + 1) * (2 : ℚ) ^ (2 * k - 1) * _root_.bernoulli (2 * k) / ((2 * k).factorial : ℚ)
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

/-- **Unconditional Irrationality of `ζ(2) = π² / 6`**:
Proved with zero custom axioms from `euler_even_zeta_rational_multiple 1` and `irrational_pi_sq`. -/
theorem irrational_riemannZetaReal_two : Irrational (riemannZetaReal 2) := by
  obtain ⟨ρ, hρ_ne, h_eq⟩ := euler_even_zeta_rational_multiple 1 (by decide)
  change riemannZetaReal 2 = (ρ : ℝ) * Real.pi ^ 2 at h_eq
  intro ⟨q, hq⟩
  apply irrational_pi_sq
  refine ⟨q / ρ, ?_⟩
  have hρ_real : (ρ : ℝ) ≠ 0 := by exact_mod_cast hρ_ne
  push_cast
  rw [div_eq_iff hρ_real]
  linarith

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
