import Mathlib

/-
# Problem Description

Let `λ = (λ₁, ..., λ_k)` be a partition of `n` with `λ_1 ≥ λ_2 ≥ ⋯ ≥ λ_k ≥ 1`
and `λ_1 + ⋯ + λ_k = n`. A *binary partition* of `n` is a partition all of whose
parts are powers of two. Let `B(n)` denote the set of binary partitions of `n`,
and for a part `i ≥ 1` let `m_λ(i)` denote the multiplicity of `i` in `λ`.

For `n ≥ 1` and `λ ∈ B(n)` define
    h_{B,λ}^{(n)}(x) := ∏_{k ≥ 0} (1 + x^{2^k})^{⌊n / 2^k⌋ − m_λ(2^k)}  ∈ ℤ[x]
(this is a finite product since the exponent is 0 for `2^k > n`), and define
    num_B(n, x) := ∑_{λ ∈ B(n)} h_{B,λ}^{(n)}(x)  ∈ ℤ[x].

Conjecture (Conjecture 7 of Ballantine–Beck–Feigon–Maurischat):
For every integer `n ≥ 2` and every integer `s ≥ 0` with `2^s ≤ n`,
    `1 + x^{2^s}` does not divide `num_B(n, x)` in `ℤ[x]`.
-/

open Polynomial BigOperators

namespace Conj7

/-- A partition is *binary* if every part is a power of two. -/
def IsBinary {n : ℕ} (p : Nat.Partition n) : Prop :=
  ∀ i ∈ p.parts, ∃ k : ℕ, i = 2 ^ k

/-- The finset of binary partitions of `n` (as a sub-finset of `Finset.univ`).
The predicate `IsBinary` is decidable via classical logic, so we mark this
definition `noncomputable`. -/
noncomputable def binaryPartitions (n : ℕ) : Finset (Nat.Partition n) :=
  letI : DecidablePred (IsBinary (n := n)) := fun _ => Classical.propDecidable _
  (Finset.univ : Finset (Nat.Partition n)).filter IsBinary

/-- The polynomial `h_{B,λ}^{(n)}(x) := ∏_{k ≥ 0} (1 + x^{2^k})^{⌊n/2^k⌋ − m_λ(2^k)}`.
The product is taken over `k ∈ {0, 1, ..., n}`, which is sufficient because
`⌊n / 2^k⌋ = 0` for `2^k > n`, making the corresponding factor `1`. We use
natural-number subtraction; for any partition `p` of `n` one has
`p.parts.count (2^k) ≤ ⌊n / 2^k⌋`, so this matches the mathematical exponent. -/
noncomputable def hBPoly (n : ℕ) (p : Nat.Partition n) : Polynomial ℤ :=
  ∏ k ∈ Finset.range (n + 1),
    (1 + X ^ (2 ^ k)) ^ (n / 2 ^ k - p.parts.count (2 ^ k))

/-- The binary numerator polynomial
`num_B(n, x) := ∑_{λ ∈ B(n)} h_{B,λ}^{(n)}(x)`. -/
noncomputable def numB (n : ℕ) : Polynomial ℤ :=
  ∑ p ∈ binaryPartitions n, hBPoly n p

-- Main Statement(s)

/-- **Conjecture 7 (Ballantine–Beck–Feigon–Maurischat).**
For every `n ≥ 2` and every `s ≥ 0` with `2^s ≤ n`, the polynomial
`1 + x^{2^s}` does not divide `num_B(n, x)` in `ℤ[x]`. -/
theorem conjecture7
    (n : ℕ) (hn : 2 ≤ n) (s : ℕ) (hs : 2 ^ s ≤ n) :
    ¬ ((1 + X ^ (2 ^ s) : Polynomial ℤ) ∣ numB n) := by
  sorry

end Conj7
