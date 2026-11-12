/-
(g) Constants of the parametrised contraction theorem, of the counting theorem
for general δ and of the lower bound.
-/
import Mathlib

namespace PvsNP

open Real

/-- Precision along a path: `1 + 40·8/7 ≤ 47`. -/
theorem prec_const : (1 : ℝ) + 40 * 8 / 7 ≤ 47 := by norm_num

/-- A child has at most `6M/64 < M/8` edges. -/
theorem child_edges_const : (6 : ℝ) / 64 < 1 / 8 := by norm_num

/-- Number of mode monomials: `(1+π²)√34 < 64`. -/
theorem mode_count_const : (1 + π ^ 2) * √34 < 64 := by
  have hpi := pi_lt_d4
  have hpi0 := pi_pos
  have hs : √34 < 5.831 := by
    rw [sqrt_lt' (by norm_num)]; norm_num
  have hs0 : 0 ≤ √34 := sqrt_nonneg _
  have h1 : 1 + π ^ 2 < 1 + 3.1416 ^ 2 := by nlinarith
  calc (1 + π ^ 2) * √34 ≤ (1 + 3.1416 ^ 2) * √34 := by
        apply mul_le_mul_of_nonneg_right h1.le hs0
    _ < (1 + 3.1416 ^ 2) * 5.831 := by
        apply mul_lt_mul_of_pos_left hs; norm_num
    _ < 64 := by norm_num

/-- Sum of the exponents over the depths: `64√(17/16)/(1-√2/8) < 81`. -/
theorem calls_const : 64 * √(17 / 16) / (1 - √2 / 8) < 81 := by
  have h1 : √(17 / 16) < 1.0308 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have h2 : √2 < 1.4143 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have h0 : 0 ≤ √(17 / 16) := sqrt_nonneg _
  have hd : 0 < 1 - √2 / 8 := by linarith
  rw [div_lt_iff₀ hd]
  nlinarith

/-- Conversion to base two: `81 / ln 2 < 117`. -/
theorem ln_const : 81 / log 2 < 117 := by
  have h := log_two_gt_d9
  have hp : 0 < log 2 := by linarith
  rw [div_lt_iff₀ hp]; linarith

/-- Corollary D.1(δ): `16(117C+4) = 1872C+64`. -/
theorem cor_delta_const (C : ℝ) : 16 * (117 * C + 4) = 1872 * C + 64 := by ring

/-- Corollary G′: `(117C+4)√104 < 1194C+41` for `C ≥ 1`. -/
theorem cor_kappa_const (C : ℝ) (hC : 1 ≤ C) : (117 * C + 4) * √104 < 1194 * C + 41 := by
  have h : √104 < 10.1981 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have h0 : 0 ≤ √104 := sqrt_nonneg _
  nlinarith

/-- Counting theorem: `(1872·22+65)√3 < 71500`. -/
theorem counting_const : (1872 * 22 + 65 : ℝ) * √3 < 71500 := by
  have h : √3 < 1.73206 := by rw [sqrt_lt' (by norm_num)]; norm_num
  nlinarith

/-- Lower bound: `71500√2 < 101200` and `4/(5·10⁶) < 1/(12·101200)`. -/
theorem lower_const : (71500 : ℝ) * √2 < 101200 ∧ (4 : ℝ) / (5 * 10 ^ 6) < 1 / (12 * 101200) := by
  refine ⟨?_, by norm_num⟩
  have h : √2 < 1.41422 := by rw [sqrt_lt' (by norm_num)]; norm_num
  nlinarith

/-- `2√U ≤ 2^{4U}`, squared: `4U ≤ 2^{8U}`. -/
theorem two_sqrt_le (U : ℕ) : 4 * U ≤ 2 ^ (8 * U) := by
  have h : U < 2 ^ U := Nat.lt_two_pow_self
  have h2 : 2 ^ (8 * U) = 2 ^ U * 2 ^ (7 * U) := by rw [← pow_add]; ring_nf
  have h3 : 4 ≤ 2 ^ (7 * U) ∨ U = 0 := by
    rcases Nat.eq_zero_or_pos U with h0 | h0
    · right; exact h0
    · left; calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (7 * U) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases h3 with h3 | h3
  · rw [h2]; nlinarith
  · subst h3; simp

/-- `4a(a+1) ≤ 2^{a/2+1}` for even `a = 2k ≥ 20`. -/
theorem quad_le_pow (k : ℕ) (hk : 10 ≤ k) : 4 * (2 * k) * (2 * k + 1) ≤ 2 ^ (k + 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have : 4 * (2 * (n + 1)) * (2 * (n + 1) + 1) ≤ 2 * (4 * (2 * n) * (2 * n + 1)) := by nlinarith
    calc 4 * (2 * (n + 1)) * (2 * (n + 1) + 1) ≤ 2 * (4 * (2 * n) * (2 * n + 1)) := this
      _ ≤ 2 * 2 ^ (n + 1) := by omega
      _ = 2 ^ (n + 1 + 1) := by ring

/-- Condition (G2) of Corollary D.1(δ), in logarithms: with `x = log s`, `δ ≤ 1/2` and
`δx ≥ 128`, one has `(25δ/32)(x+1) + (1-δ)x + 1 ≤ x`. -/
theorem cor_G2 (δ x : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hx : 128 ≤ δ * x) :
    25 * δ / 32 * (x + 1) + (1 - δ) * x + 1 ≤ x := by
  nlinarith

/-- Condition (G3) of Corollary D.1(δ): `δ(x+1)/32 + 1 ≤ (1-δ)x`. -/
theorem cor_G3 (δ x : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hx : 128 ≤ δ * x) :
    δ * (x + 1) / 32 + 1 ≤ (1 - δ) * x := by
  have hx0 : 256 ≤ x := by nlinarith
  nlinarith


/-- Theorem on tree encodings: `c_G = 1/(2k^2(k+1)) ≥ 1/(4k^3)` for the cube `Q_k`. -/
theorem tree_cube_const (k : ℕ) (hk : 1 ≤ k) : 2 * k ^ 2 * (k + 1) ≤ 4 * k ^ 3 := by
  nlinarith [hk, sq_nonneg k]

/-- The fan-in `f_k = 2^(k-1)(k+2)` of `I_{Q_k}` grows by a factor at most three:
`f_{n+2} ≤ 3 f_{n+1}`. -/
theorem tree_fanin_ratio (n : ℕ) : (n + 4) * 2 ^ (n + 1) ≤ 3 * ((n + 3) * 2 ^ n) := by
  rw [pow_succ]; nlinarith [Nat.one_le_two_pow (n := n)]

/-- The weights of `I_{Q_k}` have `k 2^k` bits, fewer than `2 f_k = (k+2) 2^k`. -/
theorem tree_weight_bits (k : ℕ) : k * 2 ^ k < (k + 2) * 2 ^ k := by
  have : 0 < 2 ^ k := by positivity
  nlinarith

end PvsNP
