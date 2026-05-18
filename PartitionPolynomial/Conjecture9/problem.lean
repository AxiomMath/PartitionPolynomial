import Mathlib

/-!
# Problem: Conjecture 9 (Ballantine--Beck--Feigon--Maurischat circle of conjectures)

For each non-negative integer $n$, let $\mathcal{T}(n)$ denote the set of
ternary partitions of $n$ (partitions whose parts are all powers of $3$,
including $3^0 = 1$).  For $\lambda \in \mathcal{T}(n)$ and $i \ge 1$ let
$m_\lambda(i)$ denote the multiplicity of $i$ in $\lambda$.  Set
$$ h^{(n)}_{T,\lambda}(x)
   := \prod_{k \ge 0} (1 + x^{3^k})^{\lfloor n/3^k \rfloor - m_\lambda(3^k)}
   \in \mathbb{Z}[x], $$
$$ G_T(n,x) := \gcd_{\lambda \in \mathcal{T}(n)} h^{(n)}_{T,\lambda}(x), $$
$$ \operatorname{num}_T(n,x)
   := \frac{1}{G_T(n,x)} \sum_{\lambda \in \mathcal{T}(n)} h^{(n)}_{T,\lambda}(x), $$
$$ s(n) := \operatorname{num}_T(n,-1). $$
Then $s(1) = s(2) = 1$ and, for every $n \ge 1$,
$$ s(3n) = s(3n+1) = s(3n+2) = 3^{\operatorname{val}_3((3n)!)}, $$
where $\operatorname{val}_3$ is the $3$-adic valuation.  Equivalently, this
formula already holds for all $n \ge 0$ (giving $s(0) = 1$ as well).

## Notes

- All polynomials live in $\mathbb{Z}[x]$.  Each factor $1 + x^{3^k}$ is monic
  with content $1$, so each $h^{(n)}_{T,\lambda}$ is monic with content $1$;
  hence the GCD is monic with content $1$, and the quotient
  $\operatorname{num}_T(n,x)$ lies in $\mathbb{Z}[x]$.
- The infinite product defining $h^{(n)}_{T,\lambda}$ has only finitely many
  non-trivial factors (those with $k \le \log_3 n$); we may extend the
  product up to any $K > \log_3 n$ without changing its value.
-/

open Polynomial Nat BigOperators

namespace Conj9

/-- A natural number is a power of $3$ (including $3^0 = 1$). -/
def IsPow3 (i : ℕ) : Prop := ∃ k ≤ i, i = 3 ^ k

instance (i : ℕ) : Decidable (IsPow3 i) := by
  unfold IsPow3; infer_instance

-- Main Definition(s)

/-- **Definition 1 (Multiplicity).**  Multiplicity of `i` as a part of
the partition `p` of `n`. -/
def partMult {n : ℕ} (p : Nat.Partition n) (i : ℕ) : ℕ := p.parts.count i

/-- **Definition 2 (Ternary partition).**  A partition is *ternary* if
every one of its parts is a power of $3$. -/
def IsTernary {n : ℕ} (p : Nat.Partition n) : Prop :=
  ∀ i ∈ p.parts, IsPow3 i

instance {n : ℕ} (p : Nat.Partition n) : Decidable (IsTernary p) :=
  Multiset.decidableDforallMultiset

/-- The (finite) set $\mathcal{T}(n)$ of ternary partitions of `n`. -/
def ternaryPartitions (n : ℕ) : Finset (Nat.Partition n) :=
  Finset.univ.filter IsTernary

/-- **Definition 3 (Auxiliary polynomial $h^{(n)}_{T,\lambda}$).**
$$ h^{(n)}_{T,\lambda}(x)
   = \prod_{k \ge 0} (1 + x^{3^k})^{\lfloor n/3^k \rfloor - m_\lambda(3^k)}. $$
The product is taken up to $k = n$, which exceeds $\log_3 n$, so it agrees
with the (formally infinite) product in the statement. -/
noncomputable def hTernary (n : ℕ) (p : Nat.Partition n) : Polynomial ℤ :=
  ∏ k ∈ Finset.range (n + 1),
    (1 + Polynomial.X ^ (3 ^ k)) ^ (n / 3 ^ k - partMult p (3 ^ k))

/-- **Definition 4 (Greatest common divisor).**
$G_T(n,x) := \gcd_{\lambda \in \mathcal{T}(n)} h^{(n)}_{T,\lambda}(x)$, taken
in the GCD-monoid $\mathbb{Z}[x]$ with its canonical normalization. -/
noncomputable def gcdHTernary (n : ℕ) : Polynomial ℤ :=
  (ternaryPartitions n).gcd (hTernary n)

/-- **Definition 5 (Numerator polynomial).**
$$ \operatorname{num}_T(n,x)
   := \frac{1}{G_T(n,x)} \sum_{\lambda \in \mathcal{T}(n)} h^{(n)}_{T,\lambda}(x). $$
Since each $h^{(n)}_{T,\lambda}$ is monic, the gcd is monic; we use Mathlib's
`Polynomial.divByMonic` to perform the exact division. -/
noncomputable def numT (n : ℕ) : Polynomial ℤ :=
  (∑ p ∈ ternaryPartitions n, hTernary n p) /ₘ (gcdHTernary n)

/-- **Definition 6 (The sequence $s$).**  $s(n) := \operatorname{num}_T(n,-1)$. -/
noncomputable def sSeq (n : ℕ) : ℤ := (numT n).eval (-1)

/-- **Definition 7 (3-adic valuation).**  $\operatorname{val}_3(m)$ is the
largest $e \ge 0$ with $3^e \mid m$.  We use Mathlib's `padicValNat 3`. -/
def val3 (m : ℕ) : ℕ := padicValNat 3 m

-- Main Statement(s)

/-- **Conjecture 9.**  For every $n \ge 0$,
$$ s(3n) = s(3n+1) = s(3n+2) = 3^{\operatorname{val}_3((3n)!)}. $$
In particular $s(0) = s(1) = s(2) = 1$ and for $n \ge 1$ we recover the
statement of the original conjecture. -/
theorem main_conjecture (n : ℕ) :
    sSeq (3 * n) = (3 : ℤ) ^ val3 (3 * n).factorial ∧
    sSeq (3 * n + 1) = (3 : ℤ) ^ val3 (3 * n).factorial ∧
    sSeq (3 * n + 2) = (3 : ℤ) ^ val3 (3 * n).factorial := by
  sorry

end Conj9
