import Mathlib

/-
# Problem Description

For a partition λ ⊢ n of a nonnegative integer n, the subsum polynomial is
  sp(λ, x) := ∏_{j} (1 + x^{λ_j}) = ∏_{i ≥ 1} (1 + x^i)^{m_λ(i)}
where m_λ(i) is the multiplicity of i in λ.

Define:
  den*(n, x) := ∏_{i ≥ 1} (1 + x^i)^{⌊n/i⌋}
  h_λ^{(n)}(x) := ∏_{i ≥ 1} (1 + x^i)^{⌊n/i⌋ - m_λ(i)}
  num*(n, x) := ∑_{λ ⊢ n} h_λ^{(n)}(x)
  G(n, x) := gcd of the family {h_λ^{(n)}(x) : λ ⊢ n}
  num(n, x) := num*(n, x) / G(n, x)
  den(n, x) := den*(n, x) / G(n, x)
With num(0, x) = 1 by convention.

Conjecture: for every n ≥ 1, gcd(num(n, x), den(n, x)) = 1 in ℤ[x] (equivalently ℚ[x]).

We formalize this over ℚ since Polynomial ℚ is a Euclidean domain (gcd is well-behaved).
-/

open Polynomial Finset

noncomputable section

/-- Multiplicity of `i` in a partition. -/
def Nat.Partition.mult {n : ℕ} (p : n.Partition) (i : ℕ) : ℕ :=
  Multiset.count i p.parts

-- Main Definition(s)

/-- Subsum polynomial of a partition λ: ∏ (1 + X^{λ_j}). -/
def subsumPoly {n : ℕ} (p : n.Partition) : Polynomial ℚ :=
  (p.parts.map (fun i => (1 : Polynomial ℚ) + X ^ i)).prod

/-- Common denominator den*(n, x) = ∏_{i=1}^{n} (1 + x^i)^{⌊n/i⌋}. -/
def denStar (n : ℕ) : Polynomial ℚ :=
  ∏ i ∈ Finset.Icc 1 n, ((1 : Polynomial ℚ) + X ^ i) ^ (n / i)

/-- Per-partition summand h_λ^{(n)}(x) = ∏_{i=1}^{n} (1 + x^i)^{⌊n/i⌋ - m_λ(i)}. -/
def hSummand {n : ℕ} (p : n.Partition) : Polynomial ℚ :=
  ∏ i ∈ Finset.Icc 1 n, ((1 : Polynomial ℚ) + X ^ i) ^ (n / i - p.mult i)

/-- Unreduced numerator num*(n, x) = ∑_{λ ⊢ n} h_λ^{(n)}(x). -/
def numStar (n : ℕ) : Polynomial ℚ :=
  ∑ p : n.Partition, hSummand p

/-- Common factor G(n, x) = gcd of the family {h_λ^{(n)}(x) : λ ⊢ n}. -/
def gCommon (n : ℕ) : Polynomial ℚ :=
  (Finset.univ : Finset n.Partition).gcd hSummand

/-- Reduced numerator num(n, x) = num*(n, x) / G(n, x), with num(0, x) = 1 by convention. -/
def numReduced (n : ℕ) : Polynomial ℚ :=
  if n = 0 then 1 else numStar n / gCommon n

/-- Reduced denominator den(n, x) = den*(n, x) / G(n, x). -/
def denReduced (n : ℕ) : Polynomial ℚ :=
  denStar n / gCommon n

-- Main Statement(s)

/-- Conjecture: For every n ≥ 1, gcd(num(n, x), den(n, x)) = 1 in ℚ[x]. -/
theorem main_theorem (n : ℕ) (hn : 1 ≤ n) :
    IsCoprime (numReduced n) (denReduced n) := by
  sorry

end
