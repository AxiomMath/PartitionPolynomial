import Mathlib

/-
# Problem: Conjecture on the recurrence for the ternary partition subsum
polynomial numerator values `t(n)` (Conjecture 10).

Throughout, partitions are finite multisets of positive integers. For a
partition `λ`, let `m_λ(i)` denote the multiplicity of `i` in `λ` (so
`m_λ(i) = 0` for all but finitely many `i`).

## Main Definitions

1. **Ternary partitions.** For `n ∈ ℕ`,
   `𝒯(n) := { λ partition of n : every part of λ is of the form 3^k for some k ≥ 0 }`.
   By convention `𝒯(0) = {∅}`. The set `𝒯(n)` is finite.

2. **Polynomial `h_{T,λ}^{(n)}(x)`.** For `n ≥ 0` and `λ ∈ 𝒯(n)`,
   `h_{T,λ}^{(n)}(x) := ∏_{k≥0} (1 + x^{3^k})^{⌊n/3^k⌋ - m_λ(3^k)}` in `ℤ[x]`.
   This product is finite since for `3^k > n` the exponent is `0`. Note
   `⌊n/3^k⌋ ≥ m_λ(3^k)` always.

3. **GCD polynomial.** For `n ≥ 0`,
   `G_T(n,x) := gcd_{λ∈𝒯(n)} h_{T,λ}^{(n)}(x) ∈ ℤ[x]`, normalized to be monic.
   For `n = 0` this is `1`.

4. **Numerator polynomial.**
   `num_T(n,x) := (∑_{λ∈𝒯(n)} h_{T,λ}^{(n)}(x)) / G_T(n,x) ∈ ℤ[x]`.

5. **The sequence `t(n)`.** `t(n) := num_T(n, 1) ∈ ℤ`. In particular
   `t(0) = 1`.

## Main Statements

(Conj. 10.) For every `n ≥ 0`,
  `t(3n) = t(3n+1) = t(3n+2)`,
and for every `n ≥ 1`,
  `t(3n) - t(3n-2) = 2^{2n} t(n)`.

## Numerical values
`t(0) = 1, t(1) = t(2) = 1, t(3..5) = 5, t(6..8) = 21, t(9..11) = 341,
 t(12..14) = 1621`.
-/

open Polynomial Finset BigOperators
open Classical

-- Main Definition(s)

/-- The (finite) set of ternary partitions of `n`: those `Nat.Partition n`
all of whose parts are powers of `3`. -/
noncomputable def ternaryPartitions (n : ℕ) : Finset (Nat.Partition n) :=
  (Finset.univ : Finset (Nat.Partition n)).filter
    (fun lam => ∀ i ∈ lam.parts, ∃ k : ℕ, i = 3 ^ k)

/-- The polynomial
`h_{T,λ}^{(n)}(x) = ∏_{k≥0} (1 + x^{3^k})^{⌊n/3^k⌋ - m_λ(3^k)}` in `ℤ[x]`.
The product is taken over `k ∈ {0, …, n}`; all factors with `3^k > n`
contribute trivially since both `⌊n/3^k⌋` and `m_λ(3^k)` vanish there. -/
noncomputable def hPoly (n : ℕ) (lam : Nat.Partition n) : Polynomial ℤ :=
  ∏ k ∈ Finset.range (n + 1),
    (1 + (Polynomial.X : Polynomial ℤ) ^ (3 ^ k))
      ^ (n / 3 ^ k - lam.parts.count (3 ^ k))

/-- The (monic) gcd polynomial `G_T(n,x) := gcd_{λ ∈ 𝒯(n)} h_{T,λ}^{(n)}(x)`
in `ℤ[X]`. Mathlib's `Finset.gcd` here uses the `NormalizedGCDMonoid`
structure on `ℤ[X]`; since every `h_{T,λ}^{(n)}` is monic, this normalized
gcd is monic. For `n = 0` the only `λ` is the empty partition, every
exponent is `0`, so `h_{T,∅}^{(0)} = 1` and the gcd is `1`. -/
noncomputable def G_T (n : ℕ) : Polynomial ℤ :=
  (ternaryPartitions n).gcd (hPoly n)

/-- The numerator polynomial
`num_T(n,x) := (∑_{λ∈𝒯(n)} h_{T,λ}^{(n)}(x)) / G_T(n,x) ∈ ℤ[x]`.
Division is monic division `/ₘ` by the monic polynomial `G_T(n,x)`. -/
noncomputable def numT (n : ℕ) : Polynomial ℤ :=
  (∑ lam ∈ ternaryPartitions n, hPoly n lam) /ₘ G_T n

/-- The integer sequence `t(n) := num_T(n, 1)`. -/
noncomputable def t (n : ℕ) : ℤ := (numT n).eval 1

-- Main Statement(s)

/-- Part (1) of Conj. 10: triple equality on residue classes mod `3`.
For every `n ≥ 0`, `t(3n) = t(3n+1) = t(3n+2)`. -/
theorem t_eq_three_mod (n : ℕ) :
    t (3 * n) = t (3 * n + 1) ∧ t (3 * n + 1) = t (3 * n + 2) := by
  sorry

/-- Part (2) of Conj. 10: the recurrence. For every `n ≥ 1`,
`t(3n) - t(3n-2) = 2^{2n} · t(n)`. -/
theorem t_recurrence (n : ℕ) (hn : 1 ≤ n) :
    t (3 * n) - t (3 * n - 2) = 2 ^ (2 * n) * t n := by
  sorry
