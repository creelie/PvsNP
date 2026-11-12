/-
(e) The valuation identity (eq:vEt), the bound `v₂(E_t(0)) ≥ -6Dh`, the equality
`v₂(C'(t)) = v₂(C'(0))` and the Integrality lemma of the Cauchy deformation, for small `a`,
by kernel evaluation (`decide +kernel`; no `native_decide`, so no extra axiom).

Notation of the paper: `L = 2^a`, `S = {-L, …, L-1}`, `C(T) = ∏_{q ∈ S} (T - q)`,
`q_t = h · max(0, u - v₂(t))`, `D = L / 2^{v₂(t)}`, `α = 2^(a+1)`.
-/
import Mathlib

namespace PvsNP

/-- Two-adic valuation with fuel. -/
def v2aux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if n % 2 = 0 ∧ n ≠ 0 then v2aux f (n / 2) + 1 else 0

/-- Two-adic valuation of a natural number (zero at zero). -/
def v2 (n : ℕ) : ℕ := v2aux n n

/-- Two-adic valuation of an integer. -/
def v2Z (z : ℤ) : ℕ := v2 z.natAbs

theorem v2aux_eq_padicValNat : ∀ f n, n ≤ f → n ≠ 0 → v2aux f n = padicValNat 2 n := by
  intro f
  induction f with
  | zero => intro n h h0; omega
  | succ f ih =>
    intro n h h0
    unfold v2aux
    split
    · rename_i hc
      have hd : 2 ∣ n := Nat.dvd_of_mod_eq_zero hc.1
      rw [ih (n / 2) (by omega) (by omega), padicValNat.div hd]
      have : 1 ≤ padicValNat 2 n := one_le_padicValNat_of_dvd h0 hd
      omega
    · rename_i hc
      have hd : ¬ 2 ∣ n := by
        intro hd
        exact hc ⟨Nat.mod_eq_zero_of_dvd hd, h0⟩
      exact (padicValNat.eq_zero_of_not_dvd hd).symm

/-- `v2` is Mathlib's `padicValNat 2`. -/
theorem v2_eq_padicValNat (n : ℕ) (hn : n ≠ 0) : v2 n = padicValNat 2 n :=
  v2aux_eq_padicValNat n n le_rfl hn

/-- `v2Z` is Mathlib's `padicValInt 2`. -/
theorem v2Z_eq_padicValInt (z : ℤ) (hz : z ≠ 0) : v2Z z = padicValInt 2 z := by
  unfold v2Z padicValInt
  exact v2_eq_padicValNat _ (Int.natAbs_ne_zero.mpr hz)

/-- The set `S = {-L, …, L-1}` with `L = 2^a`, as a list. -/
def S (a : ℕ) : List ℤ := (List.range (2 ^ (a + 1))).map fun k => (k : ℤ) - 2 ^ a

/-- The multiplicity `q = h · max(0, u - i)` at a point of valuation `i`. -/
def qm (i u h : ℕ) : ℤ := (h : ℤ) * ((u - i : ℕ) : ℤ)

/-- `C'(t) = ∏_{q ∈ S, q ≠ t} (t - q)`. -/
def Cprime (a : ℕ) (t : ℤ) : ℤ := (((S a).filter fun q => q ≠ t).map fun q => t - q).prod

/-- `v₂(E_t(0)) = ∑_{q ∈ S, q ≠ 0, t} q_q (v₂(q) - v₂(t - q))`: the left side of (eq:vEt). -/
def vEtDirect (a u h : ℕ) (t : ℤ) : ℤ :=
  (((S a).filter fun q => q ≠ 0 ∧ q ≠ t).map fun q =>
    qm (v2Z q) u h * ((v2Z q : ℤ) - (v2Z (t - q) : ℤ))).sum

/-- `2^a` times the right side `D ∑_{j=1}^{a-i} (j / 2^j) (q_{i+j} - q_i)` of (eq:vEt),
where `i = v₂(t)` and `D = 2^(a-i)`; the factor `2^a` clears the denominators. -/
def vEtFormula (a u h : ℕ) (t : ℤ) : ℤ :=
  let i : ℕ := v2Z t
  (2 : ℤ) ^ (a - i) * ((List.range (a - i)).map fun (j : ℕ) =>
    ((j : ℤ) + 1) * (2 : ℤ) ^ (a - (j + 1)) * (qm (i + (j + 1)) u h - qm i u h)).sum

/-- (eq:vEt) and the bound `≥ -6Dh` for every `t ∈ S ∖ {0}` with `q_t > 0`,
every `1 ≤ u ≤ a` and `h ∈ {1,2,3,5}`. -/
def vEtOK (a : ℕ) : Bool :=
  (S a).all fun t => t == 0 ||
    (List.range a).all fun u' => [1, 2, 3, 5].all fun h =>
      let u := u' + 1
      qm (v2Z t) u h == 0 ||
        (2 ^ a * vEtDirect a u h t == vEtFormula a u h t &&
          decide (-6 * 2 ^ (a - v2Z t) * (h : ℤ) ≤ vEtDirect a u h t))

/-- `v₂(C'(t)) = v₂(C'(0))` for every `t ∈ S`. -/
def CprimeOK (a : ℕ) : Bool := (S a).all fun t => v2Z (Cprime a t) == v2Z (Cprime a 0)

/-- Multiplication of a polynomial (coefficients, low degree first) by `c₀ + c₁ z`. -/
def polyMulLin (p : List ℤ) (c0 c1 : ℤ) : List ℤ :=
  List.zipWith (· + ·) (p.map (c0 * ·) ++ [0]) (0 :: p.map (c1 * ·))

/-- The coefficients in `z` of `∏_{q ∈ S, q ≠ d} (t + α z - q)`, the numerator of
`W_{xy}(t + α z)` for `d = y - x`; the denominator is `C'(0)`. -/
def Wnum (a : ℕ) (d t : ℤ) : List ℤ :=
  ((S a).filter fun q => q ≠ d).foldl (fun p q => polyMulLin p (t - q) (2 ^ (a + 1))) [1]

/-- The differences `d = y - x` of two slots `x, y ∈ [0, L)`. -/
def slotDiffs (a : ℕ) : List ℤ := (List.range (2 ^ (a + 1) - 1)).map fun k => (k : ℤ) - (2 ^ a - 1)

/-- Integrality: every coefficient `c` of the numerator of `W_{xy}(t + α z)` is divisible by
`2^{v₂(C'(0))}`, that is, `c / C'(0)` is 2-integral; for all `d` and all `t ∈ S`. -/
def integralOK (a : ℕ) : Bool :=
  (slotDiffs a).all fun d => (S a).all fun t =>
    (Wnum a d t).all fun c => c % 2 ^ v2Z (Cprime a 0) == 0

/-- `W(0)` is the identity: `∏_{q ≠ d} (0 - q) = [d = 0] · C'(0)`. -/
def WzeroOK (a : ℕ) : Bool :=
  (slotDiffs a).all fun d =>
    (((S a).filter fun q => q ≠ d).map fun q => -q).prod == if d = 0 then Cprime a 0 else 0

set_option maxRecDepth 100000 in
/-- (eq:vEt) and `v₂(E_t(0)) ≥ -6Dh` hold for `a ≤ 5`. -/
theorem vEt_small : ∀ a ∈ [1, 2, 3, 4, 5], vEtOK a = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- `v₂(C'(t)) = v₂(C'(0))` on `S` for `a ≤ 5`. -/
theorem Cprime_small : ∀ a ∈ [1, 2, 3, 4, 5], CprimeOK a = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The Integrality lemma for `a ≤ 3`. -/
theorem integrality_small : ∀ a ∈ [1, 2, 3], integralOK a = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- `W(0)` is the identity for `a ≤ 4`. -/
theorem Wzero_small : ∀ a ∈ [1, 2, 3, 4], WzeroOK a = true := by decide +kernel

end PvsNP
