/-
(b) Block decomposition arithmetic and (c) the counting inequality of the Size lemma.
-/
import Mathlib

namespace PvsNP

/-- If `|P| ≤ K 2^β` then the shifted partial sum `P + K 2^β` lies in `[0, 2^b)` with
`b = β + ⌈log₂ K⌉ + 2`, so it has a binary expansion with `b` bits. -/
theorem block_range (K β : ℕ) (P : ℤ) (hP : |P| ≤ (K : ℤ) * 2 ^ β) :
    0 ≤ P + (K : ℤ) * 2 ^ β ∧ P + (K : ℤ) * 2 ^ β < 2 ^ (β + Nat.clog 2 K + 2) := by
  have h := abs_le.mp hP
  refine ⟨by linarith [h.1], ?_⟩
  have hK : (K : ℤ) ≤ 2 ^ Nat.clog 2 K := by
    exact_mod_cast Nat.le_pow_clog (by norm_num) K
  have hpos : (0 : ℤ) < 2 ^ β := by positivity
  have h1 : (K : ℤ) * 2 ^ β ≤ 2 ^ Nat.clog 2 K * 2 ^ β := mul_le_mul_of_nonneg_right hK hpos.le
  have h2 : (2 : ℤ) ^ (β + Nat.clog 2 K + 2) = 4 * (2 ^ Nat.clog 2 K * 2 ^ β) := by ring
  have h3 : (0 : ℤ) < 2 ^ Nat.clog 2 K * 2 ^ β := by positivity
  rw [h2]
  linarith [h.2]

/-- A weighted sum of at most `K` bits with weights of absolute value at most `2^β`
is at most `K 2^β` in absolute value. -/
theorem partial_sum_bound {ι : Type*} (I : Finset ι) (K β : ℕ) (w : ι → ℤ) (y : ι → Bool)
    (hI : I.card ≤ K) (hw : ∀ i ∈ I, |w i| ≤ 2 ^ β) :
    |∑ i ∈ I, w i * (if y i then 1 else 0)| ≤ (K : ℤ) * 2 ^ β := by
  calc |∑ i ∈ I, w i * (if y i then 1 else 0)|
      ≤ ∑ i ∈ I, |w i * (if y i then 1 else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ I, (2 : ℤ) ^ β := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases h : y i
        · simpa [h] using hw i hi
        · simp [h]
    _ = (I.card : ℤ) * 2 ^ β := by simp
    _ ≤ (K : ℤ) * 2 ^ β := by
        have : (I.card : ℤ) ≤ K := by exact_mod_cast hI
        exact mul_le_mul_of_nonneg_right this (by positivity)

/-- The root of a big gate reads the weighted sum: if every block writes `val e_j = P_j + K 2^β`
then `∑_j (val e_j - K 2^β) = ∑_j P_j`. -/
theorem root_sum {ι : Type*} (J : Finset ι) (shift : ℤ) (val P : ι → ℤ)
    (h : ∀ j ∈ J, val j = P j + shift) :
    ∑ j ∈ J, (val j - shift) = ∑ j ∈ J, P j := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j hj]; ring

/-- A big gate of fan-in `f > K` has `k = ⌈f/K⌉ ≤ 2f/K` blocks. -/
theorem blocks_le (f K : ℕ) (hK : 0 < K) (hf : K < f) : (f + K - 1) / K * K ≤ 2 * f := by
  have := Nat.div_mul_le_self (f + K - 1) K
  omega

/-- With `b ≤ K`, the `k b` edges between the blocks and the root are at most `2f`. -/
theorem block_edges_le (f K b : ℕ) (hK : 0 < K) (hf : K < f) (hb : b ≤ K) :
    (f + K - 1) / K * b ≤ 2 * f :=
  le_trans (Nat.mul_le_mul_left _ hb) (blocks_le f K hK hf)

/-- An equality tree on `d` occurrences has at most `2d` edges
(`d` edges for `d ≤ 2`, and `2d - 3` for `d ≥ 3`). -/
theorem tree_edges_le (d : ℕ) : (if d ≤ 2 then d else 2 * d - 3) ≤ 2 * d := by
  split <;> omega

/-- **Size lemma, counting.**  `G` gates, `W` wires, `D = ∑ d_σ` occurrences, `T` tree edges,
`B` block edges, `E` edges before subdivision. -/
theorem size_counting (G W s D T B E : ℕ) (hG : G ≤ W + 2) (hD : D = G + W + 1)
    (hT : T ≤ 2 * D) (hB : B ≤ 2 * W) (hE : E ≤ T + B) (hW : W ≤ s) (hs : 2 ≤ s) :
    E ≤ 6 * W + 6 ∧ 6 * W + 6 ≤ 11 * s ∧ 2 * E ≤ 22 * s := by
  omega

end PvsNP
