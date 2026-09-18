### Related problem or entry

JSP-000301 — "If two consecutive positive integers are powerful, must at least one be a perfect square?" (`problems/catalog-0301-0400.md#JSP-000301`; current record: Solved, Lean proof: No)

### Recipient placeholder or confirmed public ID

RECIPIENT-JSP-000301-A (identity unconfirmed; submitter public ID: github.com/tongriyaotxt)

### Contributions and evidence

**Contribution type: formalization only.** The mathematical result (the counterexample disproving the question) is due to the published literature, not to this contribution:

- S. W. Golomb, *Powerful numbers*, Amer. Math. Monthly 77 (1970), 848–855.
- D. T. Walker, *Consecutive integer pairs of powerful numbers and related Diophantine equations*, Fibonacci Quart. 14 (1976), 111–116.
- R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed. (2004), B16.

**New contribution (2026-09-16):** a complete machine-checked Lean 4 formalization of the counterexample. The formal statement matches the problem record's scoped question: `12167` and `12168` are consecutive positive integers, both powerful (every prime divisor occurs with exponent ≥ 2; here `12167 = 23³` and `12168 = 2³·3²·13²`), and neither is a perfect square (`110² = 12100 < 12167 < 12168 < 12321 = 111²`).

Formal statement (top-level theorem):

```lean
theorem jsp_000301 :
    Powerful 12167 ∧ Powerful 12168 ∧ ¬ IsSquare 12167 ∧ ¬ IsSquare 12168 ∧
    12168 = 12167 + 1
```

**Pinned proof source:**

- Repository: https://github.com/tongriyaotxt/jsp-000301-lean-proof
- Pinned commit: `TO_BE_FILLED_AFTER_PUBLISH`
- File: `Jsp000301.lean` (self-contained, **Lean 4 core only, no Mathlib dependency**)
- Toolchain: Lean v4.34.0 (pinned in `lean-toolchain`)

**Revision note (2026-09-18):** This is a revised submission superseding the closed issue #94. The previous version used `native_decide` for the finitary checks (axiom footprint included the `Lean.ofReduceBool` family). In this revision **all `native_decide` usage has been removed**: the powerful-number checks are proved from first principles via Euclid's lemma (`primeP_dvd_mul`, built on core's `Nat.Coprime.dvd_of_dvd_mul_left`) applied to the explicit factorizations, and the non-square checks are proved by the bounds 110² = 12100 < 12167 < 12168 < 12321 = 111². Only small kernel `decide` computations remain (e.g. `12167 = 23^3`, trial division over `range 24` for the primes 2, 3, 13, 23). The theorem statement and the definitions `PrimeP` / `Powerful` / `IsSquare` are unchanged.

**Verification records:**

- CI kernel check (GitHub Actions, ubuntu-latest, fresh elan + Lean v4.34.0 install, `lean Jsp000301.lean`): TO_BE_FILLED_AFTER_CI
- Axiom audit (`#print axioms jsp_000301`, printed and grep-checked in CI): **standard axioms only** — `propext`, `Quot.sound`. **No `sorryAx`, no `Lean.ofReduceBool` / `native_decide` reduction axioms, no custom axioms.** CI additionally fails the build if the source contains `native_decide`/`sorry`/`admit`/`axiom` or if the axiom printout contains `sorryAx`/`ofReduceBool`/`Lean.trustCompiler`.
- Statement comparison notes: `Powerful n := ∀ p, PrimeP p → p ∣ n → p * p ∣ n` with `PrimeP p := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p` is the standard definition of powerful numbers (cf. the record's review note: "A powerful number has exponent at least two in every prime factor"); `IsSquare n := ∃ k, n = k * k` is the standard square predicate over `Nat`. Consecutiveness is `12168 = 12167 + 1`. No extra premises; all quantifiers first-order over `Nat`.

If the record for JSP-000301 is updated to `Lean proof: Yes` following review, its claim-status screening flags would change accordingly; this issue supplies the evidence for that review.

### Confirmation status

Pending. No written confirmation exists yet; the recipient identity is intentionally left as the placeholder above. The submitting GitHub account is the public point of contact. The mandatory off-chain authentication email to thejustinsunprize@hejustinsun.com (per the review note on #94) is being sent by the submitter in parallel with this revised submission.

### Attribution questions and conflicts

None. No conflicts to disclose. Mathematical priority belongs to the literature cited above; this contribution claims formalization authorship only.
