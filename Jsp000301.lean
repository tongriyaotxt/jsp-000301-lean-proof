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
are given explicitly. All finitary checks are discharged by **kernel `decide`**
on small numbers only; the divisibility structure is proved from first
principles via Euclid's lemma (`primeP_dvd_mul`, built on core's
`Nat.Coprime.dvd_of_dvd_mul_left`). No native-compilation tactics are used
anywhere, so `#print axioms jsp_000301` stays within the standard axioms
(`propext`, `Quot.sound`, `Classical.choice`).

Mathematical references (solution of the original question):
- S. W. Golomb, *Powerful numbers*, Amer. Math. Monthly 77 (1970), 848–855.
- D. T. Walker, *Consecutive integer pairs of powerful numbers and related
  Diophantine equations*, Fibonacci Quart. 14 (1976), 111–116.
- R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed. (2004), B16.

Contribution of this file: formal verification (Lean proof) of the
counterexample. The mathematical result itself is due to the literature above.
-/

/-- Mathematical primality: `p ≥ 2` with no nontrivial divisors. -/
def PrimeP (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

/-- A powerful number: every prime divisor occurs with exponent at least 2. -/
def Powerful (n : Nat) : Prop := ∀ p, PrimeP p → p ∣ n → p * p ∣ n

/-- Perfect square predicate. -/
def IsSquare (n : Nat) : Prop := ∃ k, n = k * k

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

/-! ## Small-prime certificates (kernel `decide` on a bounded trial division) -/

/-- If trial division over `range (p + 1)` certifies that the only divisors of
`p` are `1` and `p`, then `p` is prime. The Boolean check is evaluated by the
kernel (`decide`); for the primes used here (2, 3, 13, 23) this is trivial. -/
theorem primeP_of_cert (p : Nat) (h2 : 2 ≤ p)
    (h : ((List.range (p + 1)).all fun m =>
      decide (p % m ≠ 0) || decide (m = 1) || decide (m = p)) = true) :
    PrimeP p := by
  refine ⟨h2, fun m hm => ?_⟩
  have hmp : m ≤ p := le_of_dvd (by omega) hm
  have hall := List.all_eq_true.mp h m (by rw [List.mem_range]; omega)
  have hmod : p % m = 0 := mod_eq_zero_of_dvd hm
  rw [Bool.or_eq_true] at hall
  cases hall with
  | inr hpq =>
    exact Or.inr (decide_eq_true_eq.mp hpq)
  | inl hab =>
    rw [Bool.or_eq_true] at hab
    cases hab with
    | inl hne =>
      exact absurd hmod (decide_eq_true_eq.mp hne)
    | inr h1 =>
      exact Or.inl (decide_eq_true_eq.mp h1)

theorem primeP_2 : PrimeP 2 := primeP_of_cert 2 (by decide) (by decide)
theorem primeP_3 : PrimeP 3 := primeP_of_cert 3 (by decide) (by decide)
theorem primeP_13 : PrimeP 13 := primeP_of_cert 13 (by decide) (by decide)
theorem primeP_23 : PrimeP 23 := primeP_of_cert 23 (by decide) (by decide)

/-! ## Euclid's lemma for `PrimeP` (via core `Nat.Coprime`) -/

/-- Euclid's lemma: a prime dividing a product divides one of the factors. -/
theorem primeP_dvd_mul {p a b : Nat} (hp : PrimeP p) (h : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  have hgp : Nat.gcd p a ∣ p := Nat.gcd_dvd_left p a
  cases hp.2 _ hgp with
  | inl h1 =>
    right
    have hc : Nat.Coprime p a := h1
    exact hc.dvd_of_dvd_mul_left h
  | inr h2 =>
    left
    have hga : Nat.gcd p a ∣ a := Nat.gcd_dvd_right p a
    rwa [h2] at hga

/-- A prime dividing a positive power divides the base. -/
theorem primeP_dvd_pow {p a : Nat} (hp : PrimeP p) {k : Nat} (hk : 1 ≤ k)
    (h : p ∣ a ^ k) : p ∣ a := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero =>
    rw [Nat.add_zero] at h
    have e : a ^ 1 = a := by rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    rwa [e] at h
  | succ j ih =>
    rw [show 1 + (j + 1) = (1 + j) + 1 from by omega] at h
    rw [Nat.pow_succ] at h
    cases primeP_dvd_mul hp h with
    | inl hl => exact ih (by omega) hl
    | inr hr => exact hr

/-- A prime divisor of a prime `q` equals `q`. -/
theorem primeP_eq_of_dvd_prime {p q : Nat} (hp : PrimeP p) (hq : PrimeP q)
    (h : p ∣ q) : p = q := by
  cases hq.2 p h with
  | inl h1 =>
    have hge := hp.1
    omega
  | inr h2 => exact h2

/-! ## The counterexample -/

theorem powerful_12167 : Powerful 12167 := by
  intro p hp hpd
  have e : (12167 : Nat) = 23 ^ 3 := by decide
  rw [e] at hpd
  have h23 : p ∣ 23 := primeP_dvd_pow hp (k := 3) (by decide) hpd
  have hp23 : p = 23 := primeP_eq_of_dvd_prime hp primeP_23 h23
  subst hp23
  exact ⟨23, by decide⟩

theorem powerful_12168 : Powerful 12168 := by
  intro p hp hpd
  have e : (12168 : Nat) = 2 ^ 3 * (3 ^ 2 * 13 ^ 2) := by decide
  rw [e] at hpd
  cases primeP_dvd_mul hp hpd with
  | inl hl =>
    have hd : p ∣ 2 := primeP_dvd_pow hp (k := 3) (by decide) hl
    have hp2 : p = 2 := primeP_eq_of_dvd_prime hp primeP_2 hd
    subst hp2
    exact ⟨3042, by decide⟩
  | inr hr =>
    cases primeP_dvd_mul hp hr with
    | inl hl3 =>
      have hd : p ∣ 3 := primeP_dvd_pow hp (k := 2) (by decide) hl3
      have hp3 : p = 3 := primeP_eq_of_dvd_prime hp primeP_3 hd
      subst hp3
      exact ⟨1352, by decide⟩
    | inr hr13 =>
      have hd : p ∣ 13 := primeP_dvd_pow hp (k := 2) (by decide) hr13
      have hp13 : p = 13 := primeP_eq_of_dvd_prime hp primeP_13 hd
      subst hp13
      exact ⟨72, by decide⟩

theorem not_isSquare_12167 : ¬ IsSquare 12167 := by
  intro h
  cases h with
  | intro k hk =>
    by_cases hle : k ≤ 110
    · have e : k * k ≤ 110 * 110 := Nat.mul_le_mul hle hle
      omega
    · have hge : 111 ≤ k := by omega
      have e : 111 * 111 ≤ k * k := Nat.mul_le_mul hge hge
      omega

theorem not_isSquare_12168 : ¬ IsSquare 12168 := by
  intro h
  cases h with
  | intro k hk =>
    by_cases hle : k ≤ 110
    · have e : k * k ≤ 110 * 110 := Nat.mul_le_mul hle hle
      omega
    · have hge : 111 ≤ k := by omega
      have e : 111 * 111 ≤ k * k := Nat.mul_le_mul hge hge
      omega

/-- **JSP-000301 (disproof, formalized).**
`12167 = 23³` and `12168 = 2³ · 3² · 13²` are consecutive powerful numbers,
and neither is a perfect square. Hence two consecutive powerful positive
integers need not contain a perfect square. -/
theorem jsp_000301 :
    Powerful 12167 ∧ Powerful 12168 ∧ ¬ IsSquare 12167 ∧ ¬ IsSquare 12168 ∧
    12168 = 12167 + 1 :=
  ⟨powerful_12167, powerful_12168, not_isSquare_12167, not_isSquare_12168, rfl⟩

-- Sanity checks on the factorizations behind the counterexample:
example : 12167 = 23 ^ 3 := by decide
example : 12168 = 2 ^ 3 * 3 ^ 2 * 13 ^ 2 := by decide
example : 110 ^ 2 = 12100 ∧ 111 ^ 2 = 12321 := by decide

#print axioms jsp_000301
