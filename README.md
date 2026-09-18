# Justin Sun Prize — JSP-000301 形式化证明

## 题目

**JSP-000301**: If two consecutive positive integers are powerful, must at least one be a perfect square?
（两个连续正整数若都是 powerful number，是否必有一个是完全平方数？）

来源：<https://github.com/TheJustinSunPrize/awards> · `problems/catalog-0301-0400.md#JSP-000301`

## 结论（原问题被否定，本仓库给出机器可验证的形式化证明）

反例：**12167 = 23³** 与 **12168 = 2³ × 3² × 13²** 是一对连续 powerful number，且二者都不是完全平方数
（110² = 12100 < 12167 < 12168 < 12321 = 111²）。

Powerful number 定义：每个素因子在素因数分解中的指数均 ≥ 2。

- 12167 的唯一素因子是 23，指数为 3 ≥ 2 ✓
- 12168 的素因子为 2, 3, 13，指数分别为 3, 2, 2，均 ≥ 2 ✓
- 12167、12168 严格位于相邻平方数 110² 与 111² 之间，故均非平方数 ✓

## 形式化说明

- `Jsp000301.lean`：纯 **Lean 4 core**（零依赖，不需要 Mathlib），显式定义
  `PrimeP` / `Powerful` / `IsSquare`，主定理：

```lean
theorem jsp_000301 :
    Powerful 12167 ∧ Powerful 12168 ∧ ¬ IsSquare 12167 ∧ ¬ IsSquare 12168 ∧
    12168 = 12167 + 1
```

- 全部有穷检查只对小数用**内核 `decide`**；可除性结构由第一性原理证明
  （Euclid 引理 `primeP_dvd_mul`，基于 core 的 `Nat.Coprime.dvd_of_dvd_mul_left`；
  非平方性由 110² < 12167 < 12168 < 111² 的界估计给出）。
  **不使用 `native_decide`**，`#print axioms jsp_000301` 仅含标准公理
  `propext` 与 `Quot.sound`（不含 `sorryAx` / `Lean.ofReduceBool`）。

## 构建与验证

安装 Lean 4（本证明在 v4.34.0 上验证通过；见 `lean-toolchain`）后：

```bash
lake build        # 或：lean Jsp000301.lean
```

## 数学出处（原问题的解答，非本仓库贡献）

- S. W. Golomb, *Powerful numbers*, Amer. Math. Monthly 77 (1970), 848–855.
- D. T. Walker, *Consecutive integer pairs of powerful numbers and related
  Diophantine equations*, Fibonacci Quart. 14 (1976), 111–116.
- R. K. Guy, *Unsolved Problems in Number Theory*, 3rd ed. (2004), B16.

本仓库的贡献仅为 **Lean 形式化验证**。按孙宇晨奖公布规则：
奖项覆盖自 2026 年 1 月 1 日起取得的数学进展；此前已解但之后完成形式化验证的，形式化者可获奖。
