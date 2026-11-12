/-
(a) Correctness of the circuit network (Lemma "Correctness" of the paper, abstracted).

A circuit has `n` signals, numbered in topological order.  The first `m` are inputs; every
later signal `j` is a gate whose value `G j a` depends only on the values of earlier signals.
An assignment `a` of bits to all signals has weight
`[a out = 1] * ∏_gates [a g = G g a]`, and the sum of the weights over all assignments is the
number of satisfying inputs.
-/
import Mathlib

namespace PvsNP

open Finset

variable {n m : ℕ}

/-- `G j` depends only on signals before `j`. -/
def DependsOnEarlier (G : Fin n → (Fin n → Bool) → Bool) : Prop :=
  ∀ k a a', (∀ j, j < k → a j = a' j) → G k a = G k a'

/-- The values of the first `k` signals on input `x` (and `false` elsewhere). -/
def tbl (G : Fin n → (Fin n → Bool) → Bool) (x : Fin m → Bool) : ℕ → Fin n → Bool
  | 0 => fun _ => false
  | k + 1 => fun j =>
      if j.val = k then (if h : k < m then x ⟨k, h⟩ else G j (tbl G x k)) else tbl G x k j

/-- The values of all signals of the circuit on input `x`. -/
def signals (G : Fin n → (Fin n → Bool) → Bool) (x : Fin m → Bool) : Fin n → Bool :=
  tbl G x n

theorem tbl_of_lt (G : Fin n → (Fin n → Bool) → Bool) (x : Fin m → Bool) :
    ∀ k (j : Fin n), j.val < k → tbl G x k j = tbl G x (j.val + 1) j := by
  intro k
  induction k with
  | zero => intro j h; omega
  | succ k ih =>
    intro j h
    by_cases hj : j.val = k
    · rw [hj]
    · have : tbl G x (k + 1) j = tbl G x k j := by simp [tbl, hj]
      rw [this]; exact ih j (by omega)

/-- The signals on input `x` satisfy the equations of the circuit. -/
theorem signals_spec (G : Fin n → (Fin n → Bool) → Bool) (hdep : DependsOnEarlier G)
    (x : Fin m → Bool) (j : Fin n) :
    signals G x j = if h : j.val < m then x ⟨j.val, h⟩ else G j (signals G x) := by
  unfold signals
  rw [tbl_of_lt G x n j j.isLt]
  have : tbl G x (j.val + 1) j
      = if h : j.val < m then x ⟨j.val, h⟩ else G j (tbl G x j.val) := by simp [tbl]
  rw [this]
  split
  · rfl
  · apply hdep
    intro i hi
    rw [tbl_of_lt G x j.val i hi, tbl_of_lt G x n i i.isLt]

/-- An assignment satisfying the equations of the circuit is the one computed from its inputs. -/
theorem signals_unique (G : Fin n → (Fin n → Bool) → Bool) (hdep : DependsOnEarlier G)
    (x : Fin m → Bool) (a : Fin n → Bool)
    (ha : ∀ j : Fin n, a j = if h : j.val < m then x ⟨j.val, h⟩ else G j a) :
    a = signals G x := by
  have key : ∀ N (j : Fin n), j.val < N → a j = signals G x j := by
    intro N
    induction N with
    | zero => intro j h; omega
    | succ N ih =>
      intro j hj
      rw [ha j, signals_spec G hdep x j]
      split
      · rfl
      · apply hdep
        intro i hi
        exact ih i (by have : i.val < j.val := hi; omega)
  funext j
  exact key (j.val + 1) j (by omega)

/-- The value of the circuit with output signal `out` on input `x`. -/
def circuitValue (G : Fin n → (Fin n → Bool) → Bool) (out : Fin n) (x : Fin m → Bool) : Bool :=
  signals G x out

/-- **Correctness.**  The sum over all assignments of bits to the signals of
`[a out = 1] * ∏_j [j is an input or a j = G j a]` is the number of inputs `x` with `C(x) = 1`. -/
theorem network_contraction_eq_count (hm : m ≤ n) (G : Fin n → (Fin n → Bool) → Bool)
    (hdep : DependsOnEarlier G) (out : Fin n) :
    (∑ a : Fin n → Bool, (if a out = true then (1 : ℕ) else 0) *
        ∏ j : Fin n, (if m ≤ j.val → a j = G j a then (1 : ℕ) else 0))
      = Fintype.card {x : Fin m → Bool // circuitValue G out x = true} := by
  have key : ∀ a : Fin n → Bool, (if a out = true then (1 : ℕ) else 0) *
        ∏ j : Fin n, (if m ≤ j.val → a j = G j a then (1 : ℕ) else 0)
      = if (a out = true ∧ ∀ j : Fin n, m ≤ j.val → a j = G j a) then 1 else 0 := by
    intro a
    rw [Finset.prod_ite_zero]
    by_cases h1 : a out = true <;> by_cases h2 : ∀ j : Fin n, m ≤ j.val → a j = G j a <;>
      simp [h1, h2]
  simp_rw [key]
  rw [Finset.sum_boole, Fintype.card_subtype]
  simp only [Nat.cast_id]
  symm
  apply Finset.card_bij (fun x _ => signals G x)
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    refine ⟨hx, fun j hj => ?_⟩
    rw [signals_spec G hdep x j]
    split
    · omega
    · rfl
  · intro x _ y _ hxy
    funext i
    have hx := signals_spec G hdep x ⟨i.val, by omega⟩
    have hy := signals_spec G hdep y ⟨i.val, by omega⟩
    simp only [i.isLt, dite_true] at hx hy
    have := congrFun hxy ⟨i.val, by omega⟩
    rw [hx, hy] at this
    exact this
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    refine ⟨fun i => a ⟨i.val, by omega⟩, ?_, ?_⟩
    · have : a = signals G (fun i : Fin m => a ⟨i.val, by omega⟩) := by
        apply signals_unique G hdep
        intro j
        split
        · rfl
        · exact ha.2 j (by omega)
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      show signals G _ out = true
      rw [← this]; exact ha.1
    · symm
      apply signals_unique G hdep
      intro j
      split
      · rfl
      · exact ha.2 j (by omega)

/-- The same statement with weights in `ℤ`, hence modulo `2^(m+1)`. -/
theorem network_contraction_eq_count_int (hm : m ≤ n) (G : Fin n → (Fin n → Bool) → Bool)
    (hdep : DependsOnEarlier G) (out : Fin n) :
    (∑ a : Fin n → Bool, (if a out = true then (1 : ℤ) else 0) *
        ∏ j : Fin n, (if m ≤ j.val → a j = G j a then (1 : ℤ) else 0))
      = (Fintype.card {x : Fin m → Bool // circuitValue G out x = true} : ℤ) := by
  rw [← network_contraction_eq_count hm G hdep out]
  push_cast
  rfl

/-- The count is at most `2^m`, so it is determined by its residue modulo `2^(m+1)`. -/
theorem count_lt_two_pow (G : Fin n → (Fin n → Bool) → Bool) (out : Fin n) :
    Fintype.card {x : Fin m → Bool // circuitValue G out x = true} < 2 ^ (m + 1) := by
  calc Fintype.card {x : Fin m → Bool // circuitValue G out x = true}
      ≤ Fintype.card (Fin m → Bool) := Fintype.card_subtype_le _
    _ = 2 ^ m := by simp
    _ < 2 ^ (m + 1) := by simp [pow_succ]

/-! ### Equality trees -/

/-- Along a path, the product of the tensors `[a_i = a_{i+1}]` is one exactly when all the
bits are equal, and zero otherwise. -/
theorem path_prod_eq (k : ℕ) (a : Fin (k + 1) → Bool) :
    (∏ i : Fin k, (if a i.castSucc = a i.succ then (1 : ℕ) else 0))
      = if ∀ i, a i = a 0 then 1 else 0 := by
  have h : (∀ i : Fin k, a i.castSucc = a i.succ) ↔ ∀ i, a i = a 0 := by
    constructor
    · intro h i
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih => rw [← h i, ih]
    · intro h i
      rw [h i.castSucc, h i.succ]
  rw [Finset.prod_ite_zero]
  by_cases h' : ∀ i, a i = a 0
  · simp [h']
  · have : ¬ ∀ i : Fin k, a i.castSucc = a i.succ := fun hh => h' (h.mp hh)
    simp [h', this]

/-- A nonzero product along a path forces all bits to be equal. -/
theorem path_forces_equal (k : ℕ) (a : Fin (k + 1) → Bool)
    (h : (∏ i : Fin k, (if a i.castSucc = a i.succ then (1 : ℕ) else 0)) ≠ 0) (i j : Fin (k + 1)) :
    a i = a j := by
  rw [path_prod_eq] at h
  have h' : ∀ i, a i = a 0 := by
    by_contra hc
    simp [hc] at h
  rw [h' i, h' j]

/-- Each common value extends to exactly one assignment: the contraction of a path is `2`. -/
theorem path_sum_eq_two (k : ℕ) :
    (∑ a : Fin (k + 1) → Bool, ∏ i : Fin k, (if a i.castSucc = a i.succ then (1 : ℕ) else 0)) = 2 := by
  simp_rw [path_prod_eq]
  rw [Finset.sum_boole, ← Fintype.card_subtype]
  simp only [Nat.cast_id]
  have e : {a : Fin (k + 1) → Bool // ∀ i, a i = a 0} ≃ Bool :=
    { toFun := fun a => a.1 0
      invFun := fun b => ⟨fun _ => b, fun _ => rfl⟩
      left_inv := by
        intro a
        apply Subtype.ext
        funext i
        exact (a.2 i).symm
      right_inv := fun b => rfl }
  rw [Fintype.card_congr e]
  rfl

end PvsNP
