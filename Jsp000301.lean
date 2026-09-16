/-!
# JSP-000301 — Consecutive powerful numbers, neither a perfect square

**Problem (Justin Sun Prize problem bank, JSP-000301):**
If two consecutive positive integers are powerful, must at least one be a perfect square?

**Answer: No (disproved).** The counterexample
  - 12167 = 23³
  - 12168 = 2³ · 3² · 13²
is a pair of consecutive powerful numbers, and neither is a perfect square
(110² = 12100 < 12167 < 12168 < 12321 = 111²).

This file gives a machine-checked formalization in **Lean 4 core** (no Mathlib
dependency). The mathematical definitions (`PrimeP`, `Powerful`, `IsSquare`)
are given explicitly; the finitary checks are discharged by reflection into
Boolean functions and verified by evaluation (`native_decide`).

Mathematical references (solution of the original question):
- S. W. Golomb, *Powerful numbers*, Amer. Math. Monthly 77 (1970), 848–855.
- D. T. Walker, *Consecutive integer pairs of powerful numbers and related
  Diophantine equations*, Fibonacci Quart. 14 (1976), 111–116.
- R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed. (2004), B16.

Contribution of this file: formal verification (Lean proof) of the
counterexample. The mathematical result itself is due to the literature above.
-/

/-- Boolean primality test (trial division). -/
def isPrimeB (p : Nat) : Bool :=
  decide (2 ≤ p) && (List.range p).all (fun m => decide (m ≤ 1) || decide (p % m ≠ 0))

/-- Mathematical primality: `p ≥ 2` with no nontrivial divisors. -/
def PrimeP (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

/-- A powerful number: every prime divisor occurs with exponent at least 2. -/
def Powerful (n : Nat) : Prop := ∀ p, PrimeP p → p ∣ n → p * p ∣ n

/-- Boolean check of `Powerful n` (only divisors `p ≤ n` can matter). -/
def powerfulB (n : Nat) : Bool :=
  (List.range (n + 1)).all (fun p =>
    decide (¬ (isPrimeB p = true ∧ n % p = 0)) || decide (n % (p * p) = 0))

/-- Perfect square predicate. -/
def IsSquare (n : Nat) : Prop := ∃ k, n = k * k

/-- Boolean square test. -/
def isSquareB (n : Nat) : Bool := (List.range (n + 1)).any (fun k => decide (k * k = n))

/-! ## Auxiliary arithmetic lemmas (self-contained) -/

theorem dvd_of_mod_eq_zero {m n : Nat} (h : n % m = 0) : m ∣ n := by
  have h2 := Nat.mod_add_div n m
  exact ⟨n / m, by omega⟩

theorem mod_eq_zero_of_dvd {m n : Nat} (h : m ∣ n) : n % m = 0 := by
  cases h with
  | intro k hk => rw [hk]; exact Nat.mul_mod_right m k

theorem le_of_dvd {m n : Nat} (hn : 0 < n) (h : m ∣ n) : m ≤ n := by
  cases h with
  | intro k hk =>
    cases Nat.eq_zero_or_pos k with
    | inl hk0 =>
      rw [hk, hk0, Nat.mul_zero] at hn
      exact absurd hn (Nat.lt_irrefl 0)
    | inr hk0 =>
      rw [hk]
      exact Nat.le_mul_of_pos_right m hk0

/-! ## Reflection lemmas: Boolean checks decide the mathematical predicates -/

theorem isPrimeB_iff (p : Nat) : isPrimeB p = true ↔ PrimeP p := by
  unfold isPrimeB PrimeP
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · intro h
    have h2 := h.1
    have hall := h.2
    refine ⟨h2, fun m hm => ?_⟩
    cases Nat.eq_zero_or_pos m with
    | inl hm0 =>
      subst hm0
      cases hm with
      | intro k hk =>
        rw [Nat.zero_mul] at hk
        omega
    | inr hm0 =>
      by_cases h1 : m = 1
      · exact Or.inl h1
      · by_cases hne : m = p
        · exact hne
        · exfalso
          have hmp : m ≤ p := le_of_dvd (by omega) hm
          have hlt : m < p := by omega
          have hb := hall m (by rw [List.mem_range]; exact hlt)
          rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hb
          cases hb with
          | inl hb => omega
          | inr hb => exact hb (mod_eq_zero_of_dvd hm)
  · intro h
    have hdiv := h.2
    refine ⟨h.1, fun m hm => ?_⟩
    rw [List.mem_range] at hm
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    by_cases hm1 : m ≤ 1
    · exact Or.inl hm1
    · right
      intro hz
      cases hdiv m (dvd_of_mod_eq_zero hz) with
      | inl h => omega
      | inr h => omega

theorem powerfulB_iff (n : Nat) (hn : 0 < n) : powerfulB n = true ↔ Powerful n := by
  unfold powerfulB Powerful
  rw [List.all_eq_true]
  constructor
  · intro hall p hp hpd
    have hpn : p ≤ n := le_of_dvd hn hpd
    have hb := hall p (by rw [List.mem_range]; omega)
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hb
    cases hb with
    | inl hb =>
      exact absurd ⟨(isPrimeB_iff p).mpr hp, mod_eq_zero_of_dvd hpd⟩ hb
    | inr hb =>
      exact dvd_of_mod_eq_zero hb
  · intro hW p hp
    rw [List.mem_range] at hp
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    by_cases hcase : isPrimeB p = true ∧ n % p = 0
    · right
      exact mod_eq_zero_of_dvd
        (hW p ((isPrimeB_iff p).mp hcase.1) (dvd_of_mod_eq_zero hcase.2))
    · exact Or.inl hcase

theorem isSquareB_iff (n : Nat) : isSquareB n = true ↔ IsSquare n := by
  unfold isSquareB IsSquare
  rw [List.any_eq_true]
  constructor
  · intro h
    cases h with
    | intro k hk =>
      cases hk with
      | intro _ hkk =>
        rw [decide_eq_true_eq] at hkk
        exact ⟨k, hkk.symm⟩
  · intro h
    cases h with
    | intro k hkk =>
      refine ⟨k, ?_, ?_⟩
      · rw [List.mem_range]
        cases Nat.eq_zero_or_pos k with
        | inl hk => omega
        | inr hk =>
          have hle : k ≤ k * k := Nat.le_mul_of_pos_right k hk
          omega
      · rw [decide_eq_true_eq]
        exact hkk.symm

/-! ## The counterexample -/

/-- **JSP-000301 (disproof, formalized).**
`12167 = 23³` and `12168 = 2³ · 3² · 13²` are consecutive powerful numbers,
and neither is a perfect square. Hence two consecutive powerful positive
integers need not contain a perfect square. -/
theorem jsp_000301 :
    Powerful 12167 ∧ Powerful 12168 ∧ ¬ IsSquare 12167 ∧ ¬ IsSquare 12168 ∧
    12168 = 12167 + 1 := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · exact (powerfulB_iff 12167 (by decide)).mp (by native_decide)
  · exact (powerfulB_iff 12168 (by decide)).mp (by native_decide)
  · intro h
    exact absurd ((isSquareB_iff 12167).mpr h) (by native_decide)
  · intro h
    exact absurd ((isSquareB_iff 12168).mpr h) (by native_decide)

-- Sanity checks on the factorizations behind the counterexample:
example : 12167 = 23 ^ 3 := by native_decide
example : 12168 = 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := by native_decide
example : 110 ^ 2 = 12100 ∧ 111 ^ 2 = 12321 := by native_decide

#print axioms jsp_000301
