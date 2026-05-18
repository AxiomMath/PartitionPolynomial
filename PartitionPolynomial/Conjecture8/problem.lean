import Mathlib

/-
# Problem Description

Throughout, $n$ is a positive integer and $x$ is a formal indeterminate. All
polynomials lie in $\mathbb{Z}[x]$.

1. **Partition multiplicities.** For a partition $\lambda$ of $n$, let
   $m_\lambda(i)$ denote the multiplicity of the part $i$ in $\lambda$.

2. **Odd partitions.** A partition $\lambda$ of $n$ is *odd* if every part is
   odd. Let $\mathcal{O}(n)$ be the set of odd partitions of $n$.

3. **The polynomials $h_{O,\lambda}^{(n)}(x)$.** For $\lambda \in
   \mathcal{O}(n)$,
   $$h_{O,\lambda}^{(n)}(x) := \prod_{i \ge 1,\ i\ \text{odd}}
       (1+x^i)^{\lfloor n/i \rfloor - m_\lambda(i)} \in \mathbb{Z}[x].$$
   (Exponents are nonnegative; the product is finite.)

4. **The polynomial gcd $G_O(n,x)$.** Define
   $$G_O(n,x) := \gcd_{\lambda \in \mathcal{O}(n)} h_{O,\lambda}^{(n)}(x),$$
   normalized so that its constant term is $+1$ (the gcd is well-defined up to
   $\pm 1$; the constant term of every $h_{O,\lambda}^{(n)}$ is $1$).

5. **The numerator polynomial $\mathrm{num}_O(n,x)$.** Since $G_O$ divides each
   $h_{O,\lambda}^{(n)}$, it divides their sum, and we set
   $$\mathrm{num}_O(n,x) := \frac{1}{G_O(n,x)}
       \sum_{\lambda \in \mathcal{O}(n)} h_{O,\lambda}^{(n)}(x).$$

6. **Largest odd divisor.** For $m \ge 1$, $o(m)$ is the largest odd divisor of
   $m$, so $m = 2^{\nu_2(m)} \cdot o(m)$.

# Main Statement

**Conjecture.** For every integer $n \ge 1$,
$$\mathrm{num}_O(n,-1) = o(n!).$$
-/

open Polynomial BigOperators

namespace Conj8

/-- The multiplicity of the part `i` in a partition `p`. -/
def mult {n : ℕ} (p : Nat.Partition n) (i : ℕ) : ℕ := p.parts.count i

/-- The finset of odd partitions of `n` (partitions all of whose parts are
odd). -/
def oddPartitions (n : ℕ) : Finset (Nat.Partition n) :=
  (Finset.univ : Finset (Nat.Partition n)).filter (fun p => ∀ i ∈ p.parts, Odd i)

/-- The polynomial $h_{O,\lambda}^{(n)}(x) =
\prod_{i \ge 1, i\text{ odd}} (1+x^i)^{\lfloor n/i \rfloor - m_\lambda(i)}$.
The product can be restricted to `i ∈ [1,n]` since the exponent vanishes for
`i > n`. -/
noncomputable def hOLambda (n : ℕ) (p : Nat.Partition n) : Polynomial ℤ :=
  ∏ i ∈ Finset.Icc 1 n,
    if Odd i then (1 + (X : Polynomial ℤ) ^ i) ^ (n / i - mult p i) else 1

/-- The polynomial GCD $G_O(n,x)$ of the family
$\{h_{O,\lambda}^{(n)}(x) : \lambda \in \mathcal{O}(n)\}$, normalized so that
its constant term is $+1$. -/
noncomputable def gO (n : ℕ) : Polynomial ℤ :=
  let g := (oddPartitions n).gcd (hOLambda n)
  if g.coeff 0 = 1 then g else -g

/-- The numerator polynomial $\mathrm{num}_O(n,x) =
\bigl(\sum_{\lambda} h_{O,\lambda}^{(n)}(x)\bigr) / G_O(n,x)$. Defined via
classical choice from the divisibility relation $G_O \mid \sum h_{O,\lambda}$;
the choice is unique because $\mathbb{Z}[x]$ is an integral domain and
`gO n ≠ 0`. -/
noncomputable def numO (n : ℕ) : Polynomial ℤ :=
  open Classical in
  if h : ∃ q : Polynomial ℤ,
            (∑ p ∈ oddPartitions n, hOLambda n p) = gO n * q
  then h.choose
  else 0

/-- The largest odd divisor of `m`: $o(m) = m / 2^{\nu_2(m)}$. -/
def largestOddDivisor (m : ℕ) : ℕ := m / 2 ^ (Nat.factorization m 2)

-- Main Statement(s)

/-- **Conjecture conj8.** For every $n \ge 1$,
$\mathrm{num}_O(n,-1) = o(n!)$. -/
theorem conj8 (n : ℕ) (hn : 1 ≤ n) :
    (numO n).eval (-1 : ℤ) = (largestOddDivisor n.factorial : ℤ) := by
  sorry

end Conj8
