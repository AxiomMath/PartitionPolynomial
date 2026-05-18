import Mathlib

/-
# Problem: Conjecture 5 — gcd of binary partition subsum numerator and denominator polynomials equals one

For every integer `n ≥ 1`, we define two polynomials in `ℤ[X]`:
- The *binary denominator polynomial*
  $\operatorname{den}_B(n, x) := \prod_{k \ge 0} (1 + x^{2^k})^{\lfloor n/2^k \rfloor}$,
- The *binary numerator polynomial*
  $\operatorname{num}_B(n, x) := \sum_{\lambda \in \mathcal{B}(n)} h_{B,\lambda}^{(n)}(x)$
  where $\mathcal{B}(n)$ is the set of partitions of $n$ all of whose parts are powers of $2$, and
  $h_{B,\lambda}^{(n)}(x) := \prod_{k \ge 0} (1 + x^{2^k})^{\lfloor n/2^k \rfloor - m_\lambda(2^k)}$.

The conjecture asserts that $\operatorname{num}_B(n, x)$ and $\operatorname{den}_B(n, x)$ are coprime in
$\mathbb{Q}[x]$. We formalize this by working with the polynomials in `ℤ[X]`, casting them into
`ℚ[X]`, and asserting `IsCoprime`.

## Notes on Formalization
- We use `Nat.Partition n` from Mathlib to represent partitions of `n` (as multisets summing to `n`).
- "All parts are powers of $2$" is encoded as a `DecidablePred`, and the set of binary partitions of
  `n` is obtained by filtering `Finset.univ : Finset (Nat.Partition n)`.
- The infinite product $\prod_{k \ge 0}$ is replaced by a finite product over
  `Finset.range (n + 1)`: for `k ≥ n + 1` we have $2^k > n$ so $\lfloor n/2^k \rfloor = 0$, and the
  remaining factors are `1`. Likewise for the per-partition factor `h_{B,λ}^{(n)}(x)`.
- Multiplicity `m_λ(i)` is the multiset count `λ.parts.count i`.
-/

open Polynomial

-- Main Definition(s)

/-- The finset of natural numbers that are powers of two and at most `n`
(namely $\{2^k : 0 \le k \le n\}$, which is a superset of all powers of $2$ up to `n`
since $2^k \ge k+1$). -/
def powersOfTwoUpTo (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).image (fun k => 2 ^ k)

/-- A partition of `n` is *binary* if every part is a power of `2`. -/
def IsBinaryPartition {n : ℕ} (p : Nat.Partition n) : Prop :=
  ∀ i ∈ p.parts, i ∈ powersOfTwoUpTo n

instance (n : ℕ) : DecidablePred (@IsBinaryPartition n) :=
  fun _ => Multiset.decidableDforallMultiset

/-- The (finite) set $\mathcal{B}(n)$ of binary partitions of `n`. -/
def binaryPartitions (n : ℕ) : Finset (Nat.Partition n) :=
  (Finset.univ : Finset (Nat.Partition n)).filter IsBinaryPartition

/-- The binary denominator polynomial
$\operatorname{den}_B(n, x) = \prod_{k \ge 0} (1 + x^{2^k})^{\lfloor n/2^k \rfloor}$.
The product is over `k ∈ Finset.range (n + 1)`; the remaining factors (for `k ≥ n + 1`) all
equal `1` since $\lfloor n / 2^k \rfloor = 0$ there. -/
noncomputable def denB (n : ℕ) : ℤ[X] :=
  ∏ k ∈ Finset.range (n + 1), (1 + X ^ (2 ^ k)) ^ (n / 2 ^ k)

/-- The per-partition factor
$h_{B,\lambda}^{(n)}(x) = \prod_{k \ge 0} (1 + x^{2^k})^{\lfloor n/2^k \rfloor - m_\lambda(2^k)}$,
where the exponent is taken in `ℕ` (truncated subtraction, but it is automatically a true
non-negative subtraction for `λ ∈ binaryPartitions n` since
$m_\lambda(2^k) \le \lfloor n / 2^k \rfloor$). -/
noncomputable def hBPartition (n : ℕ) (p : Nat.Partition n) : ℤ[X] :=
  ∏ k ∈ Finset.range (n + 1), (1 + X ^ (2 ^ k)) ^ ((n / 2 ^ k) - p.parts.count (2 ^ k))

/-- The binary numerator polynomial
$\operatorname{num}_B(n, x) = \sum_{\lambda \in \mathcal{B}(n)} h_{B,\lambda}^{(n)}(x)$. -/
noncomputable def numB (n : ℕ) : ℤ[X] :=
  ∑ p ∈ binaryPartitions n, hBPartition n p

-- Main Statement(s)

/-- **Conjecture 5.** For every `n ≥ 1`, the polynomials $\operatorname{num}_B(n,x)$ and
$\operatorname{den}_B(n,x)$ are coprime in $\mathbb{Q}[x]$. -/
theorem conj5 (n : ℕ) (hn : 1 ≤ n) :
    IsCoprime
      ((numB n).map (Int.castRingHom ℚ))
      ((denB n).map (Int.castRingHom ℚ)) := by
  sorry
