import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

open Polynomial BigOperators

namespace Conj8

/-- The multiplicity of the part `i` in a partition `p`. -/
def mult {n : ℕ} (p : Nat.Partition n) (i : ℕ) : ℕ := p.parts.count i

/-- The finset of odd partitions of `n` (partitions all of whose parts are
odd). -/
def oddPartitions (n : ℕ) : Finset (Nat.Partition n) :=
  (Finset.univ : Finset (Nat.Partition n)).filter (fun p => ∀ i ∈ p.parts, Odd i)

/-- The polynomial $h_{O,\lambda}^{(n)}(x) =
\prod_{i \ge 1, i\text{ odd}} (1+x^i)^{\lfloor n/i \rfloor - m_\lambda(i)}$. -/
noncomputable def hOLambda (n : ℕ) (p : Nat.Partition n) : Polynomial ℤ :=
  ∏ i ∈ Finset.Icc 1 n,
    if Odd i then (1 + (X : Polynomial ℤ) ^ i) ^ (n / i - mult p i) else 1

/-- The polynomial GCD $G_O(n,x)$ of the family
$\{h_{O,\lambda}^{(n)}(x) : \lambda \in \mathcal{O}(n)\}$, normalized so that
its constant term is $+1$. -/
noncomputable def gO (n : ℕ) : Polynomial ℤ :=
  let g := (oddPartitions n).gcd (hOLambda n)
  if g.coeff 0 = 1 then g else -g

/-- The numerator polynomial. -/
noncomputable def numO (n : ℕ) : Polynomial ℤ :=
  open Classical in
  if h : ∃ q : Polynomial ℤ,
            (∑ p ∈ oddPartitions n, hOLambda n p) = gO n * q
  then h.choose
  else 0

/-- The odd-prime-power product. -/
noncomputable def oddPrimePowerProduct (n : ℕ) : ℕ :=
  ∏ p ∈ (n.factorial).primeFactors.filter (fun p => p ≠ 2),
    p ^ (Nat.factorization n.factorial p)

/-- The "all-ones" odd partition of `n`. -/
noncomputable def allOnesPartition (n : ℕ) (_hn : 1 ≤ n) : Nat.Partition n :=
{ parts := Multiset.replicate n 1
  , parts_pos := by
      intro i hi
      have : i = 1 := by
        have := Multiset.eq_of_mem_replicate hi
        exact this
      simp [this]
  , parts_sum := by
      simp [Multiset.sum_replicate] }

/-- For each odd partition `p ∈ oddPartitions n`, the normalized gcd `gO n`
divides `hOLambda n p` in `ℤ[X]`. -/
lemma gO_dvd_hOLambda (n : ℕ) (p : Nat.Partition n) (hp : p ∈ oddPartitions n) :
    gO n ∣ hOLambda n p := by
  have h : (oddPartitions n).gcd (hOLambda n) ∣ hOLambda n p := Finset.gcd_dvd hp
  show (if _ then _ else _) ∣ _
  split_ifs <;> simp [h]

/-- The all-ones partition belongs to `oddPartitions n`. -/
lemma allOnesPartition_mem_oddPartitions (n : ℕ) (hn : 1 ≤ n) :
    allOnesPartition n hn ∈ oddPartitions n := by
  unfold oddPartitions
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro i hi
  have hi1 : i = 1 := Multiset.eq_of_mem_replicate hi
  simp [hi1]

/-- Each polynomial `hOLambda n p` has constant term `1`. -/
lemma hOLambda_coeff_zero (n : ℕ) (p : Nat.Partition n) :
    (hOLambda n p).coeff 0 = 1 := by
  have coeff_zero_one_add_X_pow_pow : ∀ (i : ℕ), 1 ≤ i → ∀ (k : ℕ),
      ((1 + (X : Polynomial ℤ) ^ i) ^ k).coeff 0 = 1 := by
    intro i hi k
    have h1 : ((1 + (X : Polynomial ℤ) ^ i) ^ k).coeff 0 = ((1 + (X : Polynomial ℤ) ^ i) ^ k).eval 0 := by
      simp [Polynomial.coeff_zero_eq_eval_zero]
    rw [h1]
    have h3 : (1 + (X : Polynomial ℤ) ^ i).eval 0 = (1 : ℤ) := by
      simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
      <;>
      (try cases i <;> simp_all [Nat.succ_eq_add_one, pow_add, pow_one, mul_zero, add_zero])
    calc
      ((1 + (X : Polynomial ℤ) ^ i) ^ k).eval 0 = ((1 + (X : Polynomial ℤ) ^ i).eval 0) ^ k := by
        simp [Polynomial.eval_pow]
      _ = (1 : ℤ) ^ k := by rw [h3]
      _ = 1 := by simp
  unfold hOLambda
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_prod]
  apply Finset.prod_eq_one
  intro i hi
  have h1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  split_ifs with hodd
  · rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact coeff_zero_one_add_X_pow_pow i h1 _
  · simp

/-- Factorization of `n!`: `n! = 2^(v₂(n!)) * oddPrimePowerProduct n` for `n ≥ 1`. -/
lemma factorial_eq_two_pow_mul_oddPrimePowerProduct (n : ℕ) (hn : 1 ≤ n) :
    n.factorial =
      2 ^ (Nat.factorization n.factorial 2) * oddPrimePowerProduct n := by
  set m := n.factorial
  have hm : m ≠ 0 := Nat.factorial_ne_zero n
  have hprod : ∏ p ∈ m.primeFactors, p ^ (Nat.factorization m p) = m :=
    Nat.factorization_prod_pow_eq_self hm
  have hsplit := Finset.prod_filter_mul_prod_filter_not m.primeFactors (· = 2)
    (fun p => p ^ Nat.factorization m p)
  have h2 : ∏ p ∈ m.primeFactors.filter (· = 2), p ^ Nat.factorization m p
              = 2 ^ Nat.factorization m 2 := by
    by_cases h : 2 ∈ m.primeFactors
    · rw [show m.primeFactors.filter (· = 2) = {2} from by ext; aesop]
      simp
    · rw [show m.primeFactors.filter (· = 2) = ∅ from by
            rw [Finset.filter_eq_empty_iff]; rintro p hp rfl; exact h hp]
      have : ¬ 2 ∣ m := fun hd => h (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd, hm⟩)
      rw [Nat.factorization_eq_zero_of_not_dvd this]; simp
  rw [h2, hprod] at hsplit
  exact hsplit.symm

/-- **The gcd `gO n` is nonzero.** Direct consequence of the custom lemmas:
since `gO n` divides `hOLambda n (allOnesPartition n hn)` which has constant
term `1`, it cannot be zero. -/
lemma gO_ne_zero (n : ℕ) (hn : 1 ≤ n) : gO n ≠ 0 := by
  intro h
  have hmem := allOnesPartition_mem_oddPartitions n hn
  have hdvd := gO_dvd_hOLambda n (allOnesPartition n hn) hmem
  rw [h, zero_dvd_iff] at hdvd
  have hc := hOLambda_coeff_zero n (allOnesPartition n hn)
  rw [hdvd] at hc
  simp at hc

/-- **Existence of the numerator polynomial.** Direct consequence of
`gO_dvd_hOLambda` via `Finset.dvd_sum`. -/
lemma exists_quotient (n : ℕ) (hn : 1 ≤ n) :
    ∃ q : Polynomial ℤ,
      (∑ p ∈ oddPartitions n, hOLambda n p) = gO n * q :=
  Finset.dvd_sum (fun p hp => gO_dvd_hOLambda n p hp)

/-- **The numerator polynomial satisfies the quotient equation.** -/
lemma numO_spec (n : ℕ) (hn : 1 ≤ n) :
    (∑ p ∈ oddPartitions n, hOLambda n p) = gO n * numO n := by
  classical
  unfold numO
  rw [dif_pos (exists_quotient n hn)]
  exact (exists_quotient n hn).choose_spec

/-- The chosen quotient polynomial `q_p` such that `hOLambda n p = gO n * q_p`,
defined via classical choice using `gO_dvd_hOLambda`. Returns `0` when the
divisibility fails (e.g., outside `oddPartitions n`). -/
noncomputable def qPart (n : ℕ) (p : Nat.Partition n) : Polynomial ℤ :=
  open Classical in
  if h : gO n ∣ hOLambda n p then h.choose else 0

/-- **Specification of `qPart`:** when `gO n ∣ hOLambda n p`, the polynomial
`qPart n p` is a witness for the division: `hOLambda n p = gO n * qPart n p`. -/
lemma qPart_spec (n : ℕ) (p : Nat.Partition n) (h : gO n ∣ hOLambda n p) :
    hOLambda n p = gO n * qPart n p := by
  classical
  unfold qPart
  rw [dif_pos h]
  exact h.choose_spec

/-- **`numO n` equals the sum of the quotients `qPart n p` over odd
partitions.** Combines `numO_spec`, `qPart_spec`, `gO_dvd_hOLambda`, and the
nonvanishing `gO_ne_zero` for cancellation. -/
lemma numO_eq_sum_qPart (n : ℕ) (hn : 1 ≤ n) :
    numO n = ∑ p ∈ oddPartitions n, qPart n p := by
  have h1 := numO_spec n hn
  have h2 : (∑ p ∈ oddPartitions n, hOLambda n p) =
            gO n * (∑ p ∈ oddPartitions n, qPart n p) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p hp => qPart_spec n p (gO_dvd_hOLambda n p hp)
  rw [h2] at h1
  exact mul_left_cancel₀ (gO_ne_zero n hn) h1.symm

/-- For any partition `p` of `n`, the number of parts is at most `n`. -/
lemma partition_card_le (n : ℕ) (p : Nat.Partition n) : p.parts.card ≤ n := by
  have h1 : ∀ x ∈ p.parts, 1 ≤ x := fun x hx => p.parts_pos hx
  have h2 : p.parts.card • 1 ≤ p.parts.sum := Multiset.card_nsmul_le_sum h1
  simpa [p.parts_sum] using h2

/-- If `p` is a partition of `n` with `p.parts.card = n`, then every part of `p` equals 1.
This uses the fact that `p.parts.sum = n = p.parts.card`, and each part is at least 1, so
any part > 1 would push the sum above the cardinality, contradicting the equality. -/
lemma all_parts_eq_one_of_card_eq (n : ℕ) (p : Nat.Partition n) (hcard : p.parts.card = n) :
    ∀ i ∈ p.parts, i = 1 := by
  intro i hi
  have hi_pos : 1 ≤ i := p.parts_pos hi
  have hsum : p.parts.sum = n := p.parts_sum
  have h_each_ge_one : ∀ x ∈ p.parts.erase i, 1 ≤ x :=
    fun x hx => p.parts_pos (Multiset.mem_of_mem_erase hx)
  have h_erase_sum : (p.parts.erase i).card • 1 ≤ (p.parts.erase i).sum :=
    Multiset.card_nsmul_le_sum h_each_ge_one
  have h_erase_card : (p.parts.erase i).card = p.parts.card - 1 :=
    Multiset.card_erase_of_mem hi
  have h_sum_decomp : i + (p.parts.erase i).sum = p.parts.sum :=
    Multiset.sum_erase hi
  rw [hcard] at h_erase_card
  have h1 : n - 1 ≤ (p.parts.erase i).sum := by
    have h := h_erase_sum
    rw [h_erase_card, smul_eq_mul, Nat.mul_one] at h
    exact h
  rw [hsum] at h_sum_decomp
  omega

/-- If `p` is a partition of `n` with `p.parts.card = n`, then `p = allOnesPartition n hn`.
This combines:
- `all_parts_eq_one_of_card_eq`: every part equals 1
- `Multiset.eq_replicate : s = Multiset.replicate n a ↔ s.card = n ∧ ∀ b ∈ s, b = a`
- `Nat.Partition.ext : x.parts = y.parts → x = y` -/
lemma eq_allOnes_of_card_eq (n : ℕ) (hn : 1 ≤ n) (p : Nat.Partition n)
    (hcard : p.parts.card = n) : p = allOnesPartition n hn := by
  apply Nat.Partition.ext
  -- Show p.parts = (allOnesPartition n hn).parts = Multiset.replicate n 1
  have hall : ∀ i ∈ p.parts, i = 1 := all_parts_eq_one_of_card_eq n p hcard
  have hparts : p.parts = Multiset.replicate p.parts.card 1 :=
    (Multiset.eq_replicate_card).mpr hall
  show p.parts = Multiset.replicate n 1
  rw [hparts, hcard]

/-- **Cardinality of an odd partition not equal to the all-ones partition is strictly
less than `n`.** -/
lemma oddPartition_card_lt_of_ne_allOnes
    (n : ℕ) (hn : 1 ≤ n) (p : Nat.Partition n) (hp : p ∈ oddPartitions n)
    (hne : p ≠ allOnesPartition n hn) :
    p.parts.card < n := by
  have hle : p.parts.card ≤ n := partition_card_le n p
  -- Since p ≠ allOnesPartition, p.parts.card ≠ n (contrapositive of eq_allOnes_of_card_eq)
  have hne_card : p.parts.card ≠ n := by
    intro heq
    exact hne (eq_allOnes_of_card_eq n hn p heq)
  exact lt_of_le_of_ne hle hne_card

/-- The polynomial `hOLambda n p` is nonzero in `ℤ[X]`.

By `hOLambda_coeff_zero`, the constant term is `1 ≠ 0`, so the polynomial is
nonzero. -/
lemma hOLambda_ne_zero (n : ℕ) (p : Nat.Partition n) :
    hOLambda n p ≠ 0 := by
  intro h
  have hc := hOLambda_coeff_zero n p
  rw [h] at hc
  simp at hc

/-- The polynomial `qPart n p` is nonzero when `1 ≤ n` and `p ∈ oddPartitions n`.

This follows from `hOLambda n p = gO n * qPart n p` (via `qPart_spec` and
`gO_dvd_hOLambda`), together with `hOLambda n p ≠ 0` and `gO n ≠ 0`. -/
lemma qPart_ne_zero (n : ℕ) (_hn : 1 ≤ n) (p : Nat.Partition n)
    (hp : p ∈ oddPartitions n) :
    qPart n p ≠ 0 := by
  have hdvd : gO n ∣ hOLambda n p := gO_dvd_hOLambda n p hp
  have hspec := qPart_spec n p hdvd
  intro hzero
  rw [hzero, mul_zero] at hspec
  exact hOLambda_ne_zero n p hspec

/-- The all-ones partition has cardinality `n`. -/
lemma allOnes_card (n : ℕ) (hn : 1 ≤ n) :
    (allOnesPartition n hn).parts.card = n := by
  unfold allOnesPartition
  simp

/-- For any partition `p` of `n` and any `i`, the multiplicity satisfies
`mult p i ≤ n / i`. -/
lemma mult_le_div {n : ℕ} (p : Nat.Partition n) (i : ℕ) :
    mult p i ≤ n / i := by
  unfold mult
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    have h0 : p.parts.count 0 = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      exact absurd (p.parts_pos hmem) (lt_irrefl 0)
    simp [h0]
  · rw [Nat.le_div_iff_mul_le hi]
    set m := p.parts.count i with hm
    have hrep : Multiset.replicate m i ≤ p.parts :=
      Multiset.le_count_iff_replicate_le.mp le_rfl
    have hdecomp : p.parts - Multiset.replicate m i + Multiset.replicate m i = p.parts :=
      Multiset.sub_add_cancel hrep
    have hsum : p.parts.sum =
        (p.parts - Multiset.replicate m i).sum + (Multiset.replicate m i).sum := by
      rw [← Multiset.sum_add, hdecomp]
    rw [p.parts_sum] at hsum
    have hrepsum : (Multiset.replicate m i).sum = m * i := by
      rw [Multiset.sum_replicate, smul_eq_mul]
    rw [hrepsum] at hsum
    have h := Nat.le_add_left (m * i) ((p.parts - Multiset.replicate m i).sum)
    omega

/-- `1 + X^i` is nonzero in `ℤ[X]` for any `i`. -/
lemma one_add_X_pow_ne_zero (i : ℕ) :
    (1 + (X : Polynomial ℤ) ^ i) ≠ 0 := by
  intro h
  have hcoeff : (1 + (X : Polynomial ℤ) ^ i).coeff 0 = 0 := by
    rw [h]; simp
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    simp at hcoeff
  · have hX : ((X : Polynomial ℤ) ^ i).coeff 0 = 0 := by
      rw [Polynomial.coeff_X_pow]
      exact if_neg (Nat.pos_iff_ne_zero.mp hi).symm
    simp [Polynomial.coeff_add, hX] at hcoeff

/-- For odd `i`, evaluating `1 + X^i` at `-1` gives `0`, i.e. `-1` is a root. -/
lemma isRoot_neg_one_one_add_X_pow (i : ℕ) (hi : Odd i) :
    IsRoot (1 + (X : Polynomial ℤ) ^ i) (-1) := by
  have h : (1 + (X : Polynomial ℤ) ^ i).eval (-1 : ℤ) = 0 := by
    have h2 : (1 + (X : Polynomial ℤ) ^ i).eval (-1 : ℤ) = 1 + ((-1 : ℤ) : ℤ) ^ i := by
      simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [h2]
    have h3 : ((-1 : ℤ) : ℤ) ^ i = -1 := by
      cases' hi with k hk
      rw [hk]
      simp [pow_add, pow_mul, pow_one, pow_mul, pow_one, pow_add]
    rw [h3]
    <;> ring_nf
  simpa [Polynomial.IsRoot] using h

lemma derivative_eval_neg_one (i : ℕ) (hi : Odd i) :
    eval (-1 : ℤ) (derivative (1 + (X : Polynomial ℤ) ^ i)) = (i : ℤ) := by
  have h₁ : derivative (1 + (X : Polynomial ℤ) ^ i) = (i : ℕ) • X ^ (i - 1 : ℕ) := by
    simp [derivative_add, derivative_one, derivative_pow, derivative_X, Polynomial.smul_eq_C_mul]
  rw [h₁]
  have h₂ : i ≥ 1 := by
    cases' hi with k hk
    omega
  have h₅ : eval (-1 : ℤ) ((i : ℕ) • X ^ (i - 1 : ℕ)) = (i : ℕ) * ((-1 : ℤ) : ℤ) ^ (i - 1 : ℕ) := by
    simp [eval_smul, eval_pow, eval_X, pow_mul]
  rw [h₅]
  have h₇ : i % 2 = 1 := by
    cases' hi with k hk
    omega
  have h₉ : ((-1 : ℤ) : ℤ) ^ (i - 1 : ℕ) = 1 := by
    have h₁₃ : ∃ k : ℕ, i - 1 = 2 * k := by
      use (i - 1) / 2
      omega
    obtain ⟨k, hk⟩ := h₁₃
    rw [hk]
    norm_num [pow_mul]
  rw [h₉]
  <;> norm_cast
  <;> simp [h₇]

/-- For odd `i`, `-1` is NOT a root of the derivative of `1 + X^i`. -/
lemma not_isRoot_derivative (i : ℕ) (hi : Odd i) :
    ¬ IsRoot (derivative (1 + (X : Polynomial ℤ) ^ i)) (-1) := by
  intro h
  have hi_pos : 1 ≤ i := hi.pos
  have heval := derivative_eval_neg_one i hi
  rw [IsRoot] at h
  rw [h] at heval
  have : i = 0 := by exact_mod_cast heval.symm
  omega

/-- For odd `i ≥ 1`, the polynomial `1 + X^i ∈ ℤ[X]` has `-1` as a simple root. -/
lemma rootMult_one_add_X_pow_of_odd (i : ℕ) (hi : Odd i) :
    rootMultiplicity (-1 : ℤ) (1 + (X : Polynomial ℤ) ^ i) = 1 := by
  have hi_pos : 1 ≤ i := hi.pos
  have hne : (1 + (X : Polynomial ℤ) ^ i) ≠ 0 := one_add_X_pow_ne_zero i
  have hroot : IsRoot (1 + (X : Polynomial ℤ) ^ i) (-1) :=
    isRoot_neg_one_one_add_X_pow i hi
  have h_pos : 0 < rootMultiplicity (-1 : ℤ) (1 + (X : Polynomial ℤ) ^ i) := by
    rw [rootMultiplicity_pos hne]; exact hroot
  have hderiv :
      rootMultiplicity (-1 : ℤ) (derivative (1 + (X : Polynomial ℤ) ^ i)) =
        rootMultiplicity (-1 : ℤ) (1 + (X : Polynomial ℤ) ^ i) - 1 :=
    derivative_rootMultiplicity_of_root hroot
  have hd0 :
      rootMultiplicity (-1 : ℤ) (derivative (1 + (X : Polynomial ℤ) ^ i)) = 0 :=
    rootMultiplicity_eq_zero (not_isRoot_derivative i hi)
  rw [hd0] at hderiv
  omega

/-- For nonzero polynomials, `rootMultiplicity x (f^k) = k * rootMultiplicity x f`. -/
lemma rootMult_pow {R : Type*} [CommRing R] [IsDomain R] (x : R)
    (f : Polynomial R) (hf : f ≠ 0) (k : ℕ) :
    rootMultiplicity x (f ^ k) = k * rootMultiplicity x f := by
  induction k with
  | zero =>
      simp [pow_zero]
  | succ k ih =>
      have hfk : f ^ k ≠ 0 := pow_ne_zero k hf
      have hprod : f ^ k * f ≠ 0 := mul_ne_zero hfk hf
      rw [pow_succ, Polynomial.rootMultiplicity_mul hprod, ih]
      ring

/-- For odd `i ≥ 1`, the polynomial `(1 + X^i)^k` has `rootMultiplicity (-1) = k`. -/
lemma rootMult_one_add_X_pow_pow (i : ℕ) (hi : Odd i) (k : ℕ) :
    rootMultiplicity (-1 : ℤ) ((1 + (X : Polynomial ℤ) ^ i) ^ k) = k := by
  rw [rootMult_pow (-1 : ℤ) (1 + (X : Polynomial ℤ) ^ i) (one_add_X_pow_ne_zero i) k]
  rw [rootMult_one_add_X_pow_of_odd i hi]
  ring

/-- Each factor in the product defining `hOLambda` is nonzero. -/
lemma hOLambda_factor_ne_zero (n : ℕ) (p : Nat.Partition n) (i : ℕ) :
    (if Odd i then (1 + (X : Polynomial ℤ) ^ i) ^ (n / i - mult p i) else (1 : Polynomial ℤ)) ≠ 0 := by
  split_ifs with h
  · exact pow_ne_zero _ (one_add_X_pow_ne_zero i)
  · exact one_ne_zero

/-- Multiplicativity of `rootMultiplicity` over a finite product. -/
lemma rootMult_finset_prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℤ)
    (hf : ∀ i ∈ s, f i ≠ 0) (a : ℤ) :
    rootMultiplicity a (∏ i ∈ s, f i) = ∑ i ∈ s, rootMultiplicity a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact Polynomial.rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot])
  | insert b s hbs ih =>
    have hfb : f b ≠ 0 := hf b (Finset.mem_insert_self b s)
    have hfs : ∀ i ∈ s, f i ≠ 0 := fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)
    have hprod_ne : ∏ i ∈ s, f i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr hfs
    rw [Finset.prod_insert hbs, Finset.sum_insert hbs,
        Polynomial.rootMultiplicity_mul (mul_ne_zero hfb hprod_ne), ih hfs]

/-- Root multiplicity of the i-th factor at `-1`. -/
lemma rootMult_factor (n : ℕ) (p : Nat.Partition n) (i : ℕ) :
    rootMultiplicity (-1 : ℤ)
      (if Odd i then (1 + (X : Polynomial ℤ) ^ i) ^ (n / i - mult p i) else 1) =
    (if Odd i then n / i - mult p i else 0) := by
  by_cases hi : Odd i
  · simp [hi, rootMult_one_add_X_pow_pow i hi]
  · rw [if_neg hi, if_neg hi]
    exact_mod_cast Polynomial.rootMultiplicity_C 1 (-1 : ℤ)

/-- The root multiplicity of `-1` in `hOLambda n p` equals the sum. -/
lemma rootMult_hOLambda_eq (n : ℕ) (p : Nat.Partition n) :
    rootMultiplicity (-1 : ℤ) (hOLambda n p) =
    ∑ i ∈ Finset.Icc 1 n, if Odd i then n / i - mult p i else 0 := by
  unfold hOLambda
  rw [rootMult_finset_prod _ _ (fun i _ => hOLambda_factor_ne_zero n p i)]
  apply Finset.sum_congr rfl
  intro i _
  exact rootMult_factor n p i

/-- Every part `i` of a partition `p` of `n` satisfies `i ∈ Finset.Icc 1 n`. -/
lemma parts_mem_Icc {n : ℕ} (p : Nat.Partition n) :
    ∀ i ∈ p.parts, i ∈ Finset.Icc 1 n := by
  grind

lemma mult_eq_zero_of_even {n : ℕ} (p : Nat.Partition n)
    (hp : p ∈ oddPartitions n) (i : ℕ) (hi : ¬ Odd i) : mult p i = 0 := by
  have h₁ : ∀ i ∈ p.parts, Odd i := by
    rw [oddPartitions, Finset.mem_filter] at hp
    exact hp.2
  have h₂ : i ∉ p.parts := fun hmem => hi (h₁ i hmem)
  have h₃ : p.parts.count i = 0 := Multiset.count_eq_zero.mpr h₂
  unfold mult
  exact h₃

/-- For an odd partition `p`, the sum of `mult p i` over odd `i ∈ [1,n]` equals
`p.parts.card`. -/
lemma sum_odd_mult_eq_card (n : ℕ) (p : Nat.Partition n) (hp : p ∈ oddPartitions n) :
    ∑ i ∈ Finset.Icc 1 n, (if Odd i then mult p i else 0) = p.parts.card := by
  have h_drop : ∀ i ∈ Finset.Icc 1 n,
      (if Odd i then mult p i else 0) = mult p i := by
    intro i hi
    by_cases hodd : Odd i
    · simp [hodd]
    · simp [hodd, mult_eq_zero_of_even p hp i hodd]
  rw [Finset.sum_congr rfl h_drop]
  have hmem : ∀ a ∈ p.parts, a ∈ Finset.Icc 1 n := parts_mem_Icc p
  show ∑ i ∈ Finset.Icc 1 n, p.parts.count i = p.parts.card
  exact Multiset.sum_count_eq_card hmem

lemma sum_odd_diff_eq (n : ℕ) (p : Nat.Partition n) :
    ∑ i ∈ Finset.Icc 1 n, (if Odd i then n / i - mult p i else 0) =
    (∑ i ∈ Finset.Icc 1 n, (if Odd i then n / i else 0)) -
    (∑ i ∈ Finset.Icc 1 n, (if Odd i then mult p i else 0)) := by
  have hle : ∀ i ∈ Finset.Icc 1 n,
      (if Odd i then mult p i else 0) ≤ (if Odd i then n / i else 0) := by
    intro i _
    by_cases hi : Odd i
    · simp [hi, mult_le_div]
    · simp [hi]
  have hpoint : ∀ i,
      (if Odd i then n / i - mult p i else 0)
        = (if Odd i then n / i else 0) - (if Odd i then mult p i else 0) := by
    intro i
    by_cases hi : Odd i
    · simp [hi]
    · simp [hi]
  calc
    ∑ i ∈ Finset.Icc 1 n, (if Odd i then n / i - mult p i else 0)
        = ∑ i ∈ Finset.Icc 1 n,
            ((if Odd i then n / i else 0) - (if Odd i then mult p i else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro i _; exact hpoint i
      _ = (∑ i ∈ Finset.Icc 1 n, (if Odd i then n / i else 0)) -
            (∑ i ∈ Finset.Icc 1 n, (if Odd i then mult p i else 0)) :=
          Finset.sum_tsub_distrib _ hle

lemma card_le_sum_oddDiv (n : ℕ) (p : Nat.Partition n) (hp : p ∈ oddPartitions n) :
    p.parts.card ≤ ∑ i ∈ Finset.Icc 1 n, (if Odd i then n / i else 0) := by
  rw [← sum_odd_mult_eq_card n p hp]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hodd : Odd i
  · simp [hodd]
    exact mult_le_div p i
  · simp [hodd]

lemma n_le_sum_oddDiv (n : ℕ) (hn : 1 ≤ n) :
    n ≤ ∑ i ∈ Finset.Icc 1 n, (if Odd i then n / i else 0) := by
  have h₁ : ∑ i ∈ Finset.Icc 1 n, (if Odd i then n / i else 0) ≥ ∑ i ∈ Finset.Icc 1 1, (if Odd i then n / i else 0) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    · intro x _ _
      split_ifs <;> simp_all
  have h₂ : ∑ i ∈ Finset.Icc 1 1, (if Odd i then n / i else 0) = (if Odd 1 then n / 1 else 0) := by
    simp [Finset.sum_range_one]
  have h₃ : (if Odd 1 then n / 1 else 0) = n := by
    have h₄ : Odd 1 := by decide
    simp [h₄]
  linarith

/-- **Key combinatorial identity.** For `p` in `oddPartitions n` and `1 ≤ n`. -/
lemma rootMultiplicity_hOLambda_relation
    (n : ℕ) (hn : 1 ≤ n) (p : Nat.Partition n) (hp : p ∈ oddPartitions n) :
    rootMultiplicity (-1 : ℤ) (hOLambda n p) + p.parts.card =
    rootMultiplicity (-1 : ℤ) (hOLambda n (allOnesPartition n hn)) + n := by
  set C : ℕ := ∑ i ∈ Finset.Icc 1 n, (if Odd i then n / i else 0) with hC
  have hp_card_le : p.parts.card ≤ C := card_le_sum_oddDiv n p hp
  have hp_eq : rootMultiplicity (-1 : ℤ) (hOLambda n p) = C - p.parts.card := by
    rw [rootMult_hOLambda_eq n p, sum_odd_diff_eq n p, sum_odd_mult_eq_card n p hp]
  have hone : allOnesPartition n hn ∈ oddPartitions n := allOnesPartition_mem_oddPartitions n hn
  have hone_card : (allOnesPartition n hn).parts.card = n := allOnes_card n hn
  have hn_le : n ≤ C := n_le_sum_oddDiv n hn
  have hone_eq : rootMultiplicity (-1 : ℤ) (hOLambda n (allOnesPartition n hn)) = C - n := by
    rw [rootMult_hOLambda_eq n (allOnesPartition n hn), sum_odd_diff_eq n (allOnesPartition n hn),
        sum_odd_mult_eq_card n (allOnesPartition n hn) hone, hone_card]
  rw [hp_eq, hone_eq]
  omega

/-- Helper: `(X + 1) = (X - C (-1))` in any ring. Used to bridge our `(X+1)^k`
formulation to Mathlib's standard `(X - C a)^k` notation for root multiplicities. -/
lemma X_add_one_eq_X_sub_C_neg_one :
    ((X : Polynomial ℤ) + 1) = (X - Polynomial.C (-1)) := by
  simp [sub_eq_add_neg, neg_neg]

/-- **Main lemma.** For an odd partition `p` of `n`, the polynomial
`(X+1)^(n - p.parts.card)` divides `qPart n p`. -/
lemma pow_X_add_one_dvd_qPart
    (n : ℕ) (hn : 1 ≤ n) (p : Nat.Partition n) (hp : p ∈ oddPartitions n) :
    ((X : Polynomial ℤ) + 1) ^ (n - p.parts.card) ∣ qPart n p := by
  set hp_poly := hOLambda n p
  set h1_poly := hOLambda n (allOnesPartition n hn)
  set q_poly := qPart n p
  have hq_ne : q_poly ≠ 0 := qPart_ne_zero n hn p hp
  have hp_ne : hp_poly ≠ 0 := hOLambda_ne_zero n p
  have hh1_ne : h1_poly ≠ 0 := hOLambda_ne_zero n _
  have hdvd_p : gO n ∣ hp_poly := gO_dvd_hOLambda n p hp
  have hdvd_1 : gO n ∣ h1_poly :=
    gO_dvd_hOLambda n _ (allOnesPartition_mem_oddPartitions n hn)
  have hspec : hp_poly = gO n * q_poly := qPart_spec n p hdvd_p
  have hmul_ne : gO n * q_poly ≠ 0 := by rw [← hspec]; exact hp_ne
  have hmu_eq : rootMultiplicity (-1 : ℤ) hp_poly =
      rootMultiplicity (-1 : ℤ) (gO n) + rootMultiplicity (-1 : ℤ) q_poly := by
    rw [hspec]
    exact rootMultiplicity_mul hmul_ne
  have hmu_gO_le :
      rootMultiplicity (-1 : ℤ) (gO n) ≤ rootMultiplicity (-1 : ℤ) h1_poly := by
    rcases hdvd_1 with ⟨t, ht⟩
    have ht_ne : t ≠ 0 := fun h => hh1_ne (by rw [ht, h, mul_zero])
    have hgt_ne : gO n * t ≠ 0 := by rw [← ht]; exact hh1_ne
    have := rootMultiplicity_mul (p := gO n) (q := t) (x := (-1 : ℤ)) hgt_ne
    rw [← ht] at this
    omega
  have hcomb := rootMultiplicity_hOLambda_relation n hn p hp
  change rootMultiplicity (-1 : ℤ) hp_poly + p.parts.card =
      rootMultiplicity (-1 : ℤ) h1_poly + n at hcomb
  have hgoal : n - p.parts.card ≤ rootMultiplicity (-1 : ℤ) q_poly := by omega
  rw [X_add_one_eq_X_sub_C_neg_one]
  exact (le_rootMultiplicity_iff hq_ne).mp hgoal

/-- For `p ∈ oddPartitions n` with `p ≠ allOnesPartition`, the quotient
`qPart n p` evaluates to `0` at `-1`. -/
lemma qPart_eval_neg_one_of_ne_allOnes
    (n : ℕ) (hn : 1 ≤ n) (p : Nat.Partition n) (hp : p ∈ oddPartitions n)
    (hne : p ≠ allOnesPartition n hn) :
    (qPart n p).eval (-1 : ℤ) = 0 := by
  -- Step 1: cardinality of `p.parts` is strictly less than `n`.
  have hcard : p.parts.card < n :=
    oddPartition_card_lt_of_ne_allOnes n hn p hp hne
  -- Step 2: `(X+1)^(n - p.parts.card)` divides `qPart n p`.
  have hpow : ((X : Polynomial ℤ) + 1) ^ (n - p.parts.card) ∣ qPart n p :=
    pow_X_add_one_dvd_qPart n hn p hp
  -- Step 3: `n - p.parts.card ≥ 1`, so `(X+1)` divides `qPart n p`.
  have hk : n - p.parts.card ≠ 0 := by omega
  have hdvd : ((X : Polynomial ℤ) + 1) ∣ qPart n p :=
    dvd_trans (dvd_pow_self _ hk) hpow
  -- Step 4: extracting a witness and evaluating at `-1` gives `0`.
  obtain ⟨r, hr⟩ := hdvd
  rw [hr]
  simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_one]

/-- The candidate cyclotomic product polynomial `Pn n`. -/
noncomputable def Pn (n : ℕ) : Polynomial ℤ :=
  ∏ d ∈ (Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d),
    (cyclotomic (2 * d) ℤ) ^ (n / d)

end Conj8

/- ====== Sub-namespace: qPart_allOnes_eq_Pn ====== -/

open Polynomial BigOperators

namespace Conj8Sub_qPart_allOnes_eq_Pn

/-- The multiplicity of the part `i` in a partition `p`. -/
def mult {n : ℕ} (p : Nat.Partition n) (i : ℕ) : ℕ := p.parts.count i

/-- The finset of odd partitions of `n` (partitions all of whose parts are
odd). -/
def oddPartitions (n : ℕ) : Finset (Nat.Partition n) :=
  (Finset.univ : Finset (Nat.Partition n)).filter (fun p => ∀ i ∈ p.parts, Odd i)

/-- The polynomial $h_{O,\lambda}^{(n)}(x) =
\prod_{i \ge 1, i\text{ odd}} (1+x^i)^{\lfloor n/i \rfloor - m_\lambda(i)}$. -/
noncomputable def hOLambda (n : ℕ) (p : Nat.Partition n) : Polynomial ℤ :=
  ∏ i ∈ Finset.Icc 1 n,
    if Odd i then (1 + (X : Polynomial ℤ) ^ i) ^ (n / i - mult p i) else 1

/-- The polynomial GCD $G_O(n,x)$ of the family
$\{h_{O,\lambda}^{(n)}(x) : \lambda \in \mathcal{O}(n)\}$, normalized so that
its constant term is $+1$. -/
noncomputable def gO (n : ℕ) : Polynomial ℤ :=
  let g := (oddPartitions n).gcd (hOLambda n)
  if g.coeff 0 = 1 then g else -g

/-- The "all-ones" odd partition of `n`. -/
noncomputable def allOnesPartition (n : ℕ) (_hn : 1 ≤ n) : Nat.Partition n :=
{ parts := Multiset.replicate n 1
  , parts_pos := by
      intro i hi
      have : i = 1 := by
        have := Multiset.eq_of_mem_replicate hi
        exact this
      simp [this]
  , parts_sum := by
      simp [Multiset.sum_replicate] }

/-- The chosen quotient polynomial `q_p` such that `hOLambda n p = gO n * q_p`,
defined via classical choice using `gO_dvd_hOLambda`. Returns `0` when the
divisibility fails (e.g., outside `oddPartitions n`). -/
noncomputable def qPart (n : ℕ) (p : Nat.Partition n) : Polynomial ℤ :=
  open Classical in
  if h : gO n ∣ hOLambda n p then h.choose else 0

/-- The candidate cyclotomic product polynomial
`Pn n := ∏_{d ∈ [1,n], d odd, d > 1} Φ_{2d}(X)^{⌊n/d⌋}`.

This is conjecturally equal to `qPart n (allOnesPartition n hn)`. -/
noncomputable def Pn (n : ℕ) : Polynomial ℤ :=
  ∏ d ∈ (Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d),
    (cyclotomic (2 * d) ℤ) ^ (n / d)

/-- (Reused) The normalized gcd `gO n` divides each `hOLambda n p` for
`p ∈ oddPartitions n`. -/
lemma gO_dvd_hOLambda (n : ℕ) (p : Nat.Partition n) (hp : p ∈ oddPartitions n) :
    gO n ∣ hOLambda n p := by
  have h : (oddPartitions n).gcd (hOLambda n) ∣ hOLambda n p := Finset.gcd_dvd hp
  show (if _ then _ else _) ∣ _
  split_ifs <;> simp [h]

/-- (Reused) The specification of `qPart`: when `gO n ∣ hOLambda n p`,
`hOLambda n p = gO n * qPart n p`. -/
lemma qPart_spec (n : ℕ) (p : Nat.Partition n) (h : gO n ∣ hOLambda n p) :
    hOLambda n p = gO n * qPart n p := by
  classical
  unfold qPart
  rw [dif_pos h]
  exact h.choose_spec

/-- (Reused) The all-ones partition is an odd partition. -/
lemma allOnesPartition_mem_oddPartitions (n : ℕ) (hn : 1 ≤ n) :
    allOnesPartition n hn ∈ oddPartitions n := by
  unfold oddPartitions
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro i hi
  have hi1 : i = 1 := Multiset.eq_of_mem_replicate hi
  simp [hi1]

/-- For `i ≥ 1` and any `k : ℕ`, the constant coefficient of `(1 + X^i)^k` is `1`. -/
lemma coeff_zero_one_add_X_pow_pow (i : ℕ) (hi : 1 ≤ i) (k : ℕ) :
    ((1 + (X : Polynomial ℤ) ^ i) ^ k).coeff 0 = 1 := by
  have h1 : ((1 + (X : Polynomial ℤ) ^ i) ^ k).coeff 0 = ((1 + (X : Polynomial ℤ) ^ i) ^ k).eval 0 := by
    simp [Polynomial.coeff_zero_eq_eval_zero]
  rw [h1]
  have h2 : ((1 + (X : Polynomial ℤ) ^ i) ^ k).eval 0 = (1 : ℤ) := by
    have h3 : (1 + (X : Polynomial ℤ) ^ i).eval 0 = (1 : ℤ) := by
      simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
      <;>
      (try cases i <;> simp_all [Nat.succ_eq_add_one, pow_add, pow_one, mul_zero, add_zero])
    calc
      ((1 + (X : Polynomial ℤ) ^ i) ^ k).eval 0 = ((1 + (X : Polynomial ℤ) ^ i).eval 0) ^ k := by
        simp [Polynomial.eval_pow]
      _ = (1 : ℤ) ^ k := by rw [h3]
      _ = 1 := by simp
  rw [h2]

/-- Each polynomial `hOLambda n p` has constant term `1`. -/
lemma hOLambda_coeff_zero (n : ℕ) (p : Nat.Partition n) :
    (hOLambda n p).coeff 0 = 1 := by
  unfold hOLambda
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_prod]
  apply Finset.prod_eq_one
  intro i hi
  have h1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  split_ifs with hodd
  · rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact coeff_zero_one_add_X_pow_pow i h1 _
  · simp

/-- Each polynomial `hOLambda n p` is nonzero, since its constant term equals `1 ≠ 0`. -/
lemma hOLambda_ne_zero (n : ℕ) (p : Nat.Partition n) : hOLambda n p ≠ 0 := by
  intro h
  have hc := hOLambda_coeff_zero n p
  rw [h, Polynomial.coeff_zero] at hc
  exact one_ne_zero hc.symm

/-- (Reused) `gO n ≠ 0` for `1 ≤ n`. -/
lemma gO_ne_zero (n : ℕ) (hn : 1 ≤ n) : gO n ≠ 0 := by
  intro hgz
  have hmem : allOnesPartition n hn ∈ oddPartitions n :=
    allOnesPartition_mem_oddPartitions n hn
  have hdvd : gO n ∣ hOLambda n (allOnesPartition n hn) :=
    gO_dvd_hOLambda n (allOnesPartition n hn) hmem
  rw [hgz, zero_dvd_iff] at hdvd
  exact hOLambda_ne_zero n (allOnesPartition n hn) hdvd

/-- (Custom) For any partition `p` of `n`, the number of parts is at most `n`.
Since every part is at least `1` (from `parts_pos`) and the sum of parts is `n`
(from `parts_sum`), `Multiset.card_nsmul_le_sum` gives
`p.parts.card • 1 ≤ p.parts.sum = n`. -/
lemma partition_card_le (n : ℕ) (p : Nat.Partition n) : p.parts.card ≤ n := by
  have h1 : ∀ x ∈ p.parts, 1 ≤ x := fun x hx => p.parts_pos hx
  have h2 : p.parts.card • 1 ≤ p.parts.sum := Multiset.card_nsmul_le_sum h1
  simpa [p.parts_sum] using h2

/-- (Custom) If `p` is a partition of `n` with `p.parts.card = n`, then every
part of `p` equals `1`. Each part is at least `1`, and the total sum equals
the cardinality, so any part `> 1` would push the sum strictly above the
cardinality. -/
lemma all_parts_eq_one_of_card_eq (n : ℕ) (p : Nat.Partition n)
    (hcard : p.parts.card = n) : ∀ i ∈ p.parts, i = 1 := by
  intro i hi
  have hi_pos : 1 ≤ i := p.parts_pos hi
  have hsum : p.parts.sum = n := p.parts_sum
  have h_each_ge_one : ∀ x ∈ p.parts.erase i, 1 ≤ x := by
    intro x hx
    exact p.parts_pos (Multiset.mem_of_mem_erase hx)
  have h_erase_sum : (p.parts.erase i).card • 1 ≤ (p.parts.erase i).sum :=
    Multiset.card_nsmul_le_sum h_each_ge_one
  have h_erase_card : (p.parts.erase i).card = p.parts.card - 1 :=
    Multiset.card_erase_of_mem hi
  have h_sum_decomp : i + (p.parts.erase i).sum = p.parts.sum :=
    Multiset.sum_erase hi
  rw [hcard] at h_erase_card
  have h1 : n - 1 ≤ (p.parts.erase i).sum := by
    have h := h_erase_sum
    rw [h_erase_card, smul_eq_mul, Nat.mul_one] at h
    exact h
  rw [hsum] at h_sum_decomp
  omega

/-- (Custom) If `p` is a partition of `n` with `p.parts.card = n`, then
`p = allOnesPartition n hn`. Combines `all_parts_eq_one_of_card_eq` with
`Multiset.eq_replicate` and `Nat.Partition.ext`. -/
lemma eq_allOnes_of_card_eq (n : ℕ) (hn : 1 ≤ n) (p : Nat.Partition n)
    (hcard : p.parts.card = n) : p = allOnesPartition n hn := by
  apply Nat.Partition.ext
  have hall : ∀ i ∈ p.parts, i = 1 := all_parts_eq_one_of_card_eq n p hcard
  have hparts : p.parts = Multiset.replicate p.parts.card 1 :=
    (Multiset.eq_replicate_card).mpr hall
  show p.parts = Multiset.replicate n 1
  rw [hparts, hcard]

/-- (Custom) **Key combinatorial identity** (see below).
The all-ones partition has cardinality `n`. -/
lemma allOnes_card (n : ℕ) (hn : 1 ≤ n) :
    (allOnesPartition n hn).parts.card = n := by
  unfold allOnesPartition
  simp

lemma mult_le_div {n : ℕ} (p : Nat.Partition n) (i : ℕ) :
    mult p i ≤ n / i := by
  unfold mult
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    have h0 : p.parts.count 0 = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      exact absurd (p.parts_pos hmem) (lt_irrefl 0)
    simp [h0]
  · rw [Nat.le_div_iff_mul_le hi]
    set m := p.parts.count i with hm
    have hrep : Multiset.replicate m i ≤ p.parts :=
      Multiset.le_count_iff_replicate_le.mp le_rfl
    have hdecomp : p.parts - Multiset.replicate m i + Multiset.replicate m i = p.parts :=
      Multiset.sub_add_cancel hrep
    have hsum : p.parts.sum =
        (p.parts - Multiset.replicate m i).sum + (Multiset.replicate m i).sum := by
      rw [← Multiset.sum_add, hdecomp]
    rw [p.parts_sum] at hsum
    have hrepsum : (Multiset.replicate m i).sum = m * i := by
      rw [Multiset.sum_replicate, smul_eq_mul]
    rw [hrepsum] at hsum
    have h := Nat.le_add_left (m * i) ((p.parts - Multiset.replicate m i).sum)
    omega

lemma one_add_X_pow_ne_zero (i : ℕ) :
    (1 + (X : Polynomial ℤ) ^ i) ≠ 0 := by
  intro h
  have hcoeff : (1 + (X : Polynomial ℤ) ^ i).coeff 0 = 0 := by
    rw [h]; simp
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    simp at hcoeff
  · have hX : ((X : Polynomial ℤ) ^ i).coeff 0 = 0 := by
      rw [Polynomial.coeff_X_pow]
      exact if_neg (Nat.pos_iff_ne_zero.mp hi).symm
    simp [Polynomial.coeff_add, hX] at hcoeff

lemma isRoot_neg_one_one_add_X_pow (i : ℕ) (hi : Odd i) :
    IsRoot (1 + (X : Polynomial ℤ) ^ i) (-1) := by
  have h : (1 + (X : Polynomial ℤ) ^ i).eval (-1 : ℤ) = 0 := by
    have h2 : (1 + (X : Polynomial ℤ) ^ i).eval (-1 : ℤ) = 1 + ((-1 : ℤ) : ℤ) ^ i := by
      simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [h2]
    have h3 : ((-1 : ℤ) : ℤ) ^ i = -1 := by
      cases' hi with k hk
      rw [hk]
      simp [pow_add, pow_mul, pow_one, pow_mul, pow_one, pow_add]
    rw [h3]
    <;> ring_nf
  simpa [Polynomial.IsRoot] using h

lemma derivative_eval_neg_one (i : ℕ) (hi : Odd i) :
    eval (-1 : ℤ) (derivative (1 + (X : Polynomial ℤ) ^ i)) = (i : ℤ) := by
  have h₁ : derivative (1 + (X : Polynomial ℤ) ^ i) = (i : ℕ) • X ^ (i - 1 : ℕ) := by
    simp [derivative_add, derivative_one, derivative_pow, derivative_X, Polynomial.smul_eq_C_mul]
  rw [h₁]
  have h₂ : i ≥ 1 := by
    cases' hi with k hk
    omega
  have h₄ : eval (-1 : ℤ) ((i : ℕ) • X ^ (i - 1 : ℕ)) = (i : ℤ) := by
    have h₅ : eval (-1 : ℤ) ((i : ℕ) • X ^ (i - 1 : ℕ)) = (i : ℕ) * ((-1 : ℤ) : ℤ) ^ (i - 1 : ℕ) := by
      simp [eval_smul, eval_pow, eval_X, pow_mul]
    rw [h₅]
    have h₇ : i % 2 = 1 := by
      cases' hi with k hk
      omega
    have h₉ : ((-1 : ℤ) : ℤ) ^ (i - 1 : ℕ) = 1 := by
      have h₁₃ : ∃ k : ℕ, i - 1 = 2 * k := by
        use (i - 1) / 2
        omega
      obtain ⟨k, hk⟩ := h₁₃
      rw [hk]
      norm_num [pow_mul]
    rw [h₉]
    <;> norm_cast
    <;> simp [h₇]
  exact h₄

lemma not_isRoot_derivative (i : ℕ) (hi : Odd i) :
    ¬ IsRoot (derivative (1 + (X : Polynomial ℤ) ^ i)) (-1) := by
  intro h
  have heval := derivative_eval_neg_one i hi
  rw [IsRoot] at h
  rw [h] at heval
  have : i = 0 := by exact_mod_cast heval.symm
  have hi_pos : 1 ≤ i := hi.pos
  omega

lemma rootMult_one_add_X_pow_of_odd (i : ℕ) (hi : Odd i) :
    rootMultiplicity (-1 : ℤ) (1 + (X : Polynomial ℤ) ^ i) = 1 := by
  have hne : (1 + (X : Polynomial ℤ) ^ i) ≠ 0 := one_add_X_pow_ne_zero i
  have hroot : IsRoot (1 + (X : Polynomial ℤ) ^ i) (-1) :=
    isRoot_neg_one_one_add_X_pow i hi
  have h_pos : 0 < rootMultiplicity (-1 : ℤ) (1 + (X : Polynomial ℤ) ^ i) := by
    rw [rootMultiplicity_pos hne]; exact hroot
  have hderiv :
      rootMultiplicity (-1 : ℤ) (derivative (1 + (X : Polynomial ℤ) ^ i)) =
        rootMultiplicity (-1 : ℤ) (1 + (X : Polynomial ℤ) ^ i) - 1 :=
    derivative_rootMultiplicity_of_root hroot
  have hd0 :
      rootMultiplicity (-1 : ℤ) (derivative (1 + (X : Polynomial ℤ) ^ i)) = 0 :=
    rootMultiplicity_eq_zero (not_isRoot_derivative i hi)
  rw [hd0] at hderiv
  omega

lemma rootMult_pow_int (x : ℤ)
    (f : Polynomial ℤ) (hf : f ≠ 0) (k : ℕ) :
    rootMultiplicity x (f ^ k) = k * rootMultiplicity x f := by
  induction k with
  | zero =>
      simp [pow_zero]
  | succ k ih =>
      have hfk : f ^ k ≠ 0 := pow_ne_zero k hf
      have hprod : f ^ k * f ≠ 0 := mul_ne_zero hfk hf
      rw [pow_succ, Polynomial.rootMultiplicity_mul hprod, ih]
      ring

lemma rootMult_one_add_X_pow_pow (i : ℕ) (hi : Odd i) (k : ℕ) :
    rootMultiplicity (-1 : ℤ) ((1 + (X : Polynomial ℤ) ^ i) ^ k) = k := by
  rw [rootMult_pow_int (-1 : ℤ) (1 + (X : Polynomial ℤ) ^ i) (one_add_X_pow_ne_zero i) k]
  rw [rootMult_one_add_X_pow_of_odd i hi]
  ring

lemma hOLambda_factor_ne_zero (n : ℕ) (p : Nat.Partition n) (i : ℕ) :
    (if Odd i then (1 + (X : Polynomial ℤ) ^ i) ^ (n / i - mult p i) else (1 : Polynomial ℤ)) ≠ 0 := by
  split_ifs with h
  · exact pow_ne_zero _ (one_add_X_pow_ne_zero i)
  · exact one_ne_zero

lemma rootMult_finset_prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℤ)
    (hf : ∀ i ∈ s, f i ≠ 0) (a : ℤ) :
    rootMultiplicity a (∏ i ∈ s, f i) = ∑ i ∈ s, rootMultiplicity a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact Polynomial.rootMultiplicity_eq_zero (by simp [Polynomial.IsRoot])
  | insert b s hbs ih =>
    have hfb : f b ≠ 0 := hf b (Finset.mem_insert_self b s)
    have hfs : ∀ i ∈ s, f i ≠ 0 := fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)
    have hprod_ne : ∏ i ∈ s, f i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr hfs
    rw [Finset.prod_insert hbs, Finset.sum_insert hbs,
        Polynomial.rootMultiplicity_mul (mul_ne_zero hfb hprod_ne), ih hfs]

lemma rootMult_factor (n : ℕ) (p : Nat.Partition n) (i : ℕ) :
    rootMultiplicity (-1 : ℤ)
      (if Odd i then (1 + (X : Polynomial ℤ) ^ i) ^ (n / i - mult p i) else 1) =
    (if Odd i then n / i - mult p i else 0) := by
  by_cases hi : Odd i
  · simp [hi, rootMult_one_add_X_pow_pow i hi]
  · rw [if_neg hi, if_neg hi]
    exact_mod_cast Polynomial.rootMultiplicity_C 1 (-1 : ℤ)

lemma rootMult_hOLambda_eq (n : ℕ) (p : Nat.Partition n) :
    rootMultiplicity (-1 : ℤ) (hOLambda n p) =
    ∑ i ∈ Finset.Icc 1 n, if Odd i then n / i - mult p i else 0 := by
  unfold hOLambda
  rw [rootMult_finset_prod _ _ (fun i _ => hOLambda_factor_ne_zero n p i)]
  apply Finset.sum_congr rfl
  intro i _
  exact rootMult_factor n p i

lemma parts_mem_Icc {n : ℕ} (p : Nat.Partition n) :
    ∀ i ∈ p.parts, i ∈ Finset.Icc 1 n := by
  grind

lemma mult_eq_zero_of_even {n : ℕ} (p : Nat.Partition n)
    (hp : p ∈ oddPartitions n) (i : ℕ) (hi : ¬ Odd i) : mult p i = 0 := by
  have h₁ : ∀ i ∈ p.parts, Odd i := (Finset.mem_filter.mp hp).2
  have h₂ : i ∉ p.parts := fun himem => hi (h₁ i himem)
  exact Multiset.count_eq_zero.mpr h₂

lemma sum_odd_mult_eq_card (n : ℕ) (p : Nat.Partition n) (hp : p ∈ oddPartitions n) :
    ∑ i ∈ Finset.Icc 1 n, (if Odd i then mult p i else 0) = p.parts.card := by
  have h_drop : ∀ i ∈ Finset.Icc 1 n,
      (if Odd i then mult p i else 0) = mult p i := by
    intro i hi
    by_cases hodd : Odd i
    · simp [hodd]
    · simp [hodd, mult_eq_zero_of_even p hp i hodd]
  rw [Finset.sum_congr rfl h_drop]
  have hmem : ∀ a ∈ p.parts, a ∈ Finset.Icc 1 n := parts_mem_Icc p
  show ∑ i ∈ Finset.Icc 1 n, p.parts.count i = p.parts.card
  exact Multiset.sum_count_eq_card hmem

lemma sum_odd_diff_eq (n : ℕ) (p : Nat.Partition n) :
    ∑ i ∈ Finset.Icc 1 n, (if Odd i then n / i - mult p i else 0) =
    (∑ i ∈ Finset.Icc 1 n, (if Odd i then n / i else 0)) -
    (∑ i ∈ Finset.Icc 1 n, (if Odd i then mult p i else 0)) := by
  have hle : ∀ i ∈ Finset.Icc 1 n,
      (if Odd i then mult p i else 0) ≤ (if Odd i then n / i else 0) := by
    intro i _
    by_cases hi : Odd i
    · simp [hi, mult_le_div]
    · simp [hi]
  have hpoint : ∀ i,
      (if Odd i then n / i - mult p i else 0)
        = (if Odd i then n / i else 0) - (if Odd i then mult p i else 0) := by
    intro i
    by_cases hi : Odd i
    · simp [hi]
    · simp [hi]
  calc
    ∑ i ∈ Finset.Icc 1 n, (if Odd i then n / i - mult p i else 0)
        = ∑ i ∈ Finset.Icc 1 n,
            ((if Odd i then n / i else 0) - (if Odd i then mult p i else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro i _; exact hpoint i
      _ = (∑ i ∈ Finset.Icc 1 n, (if Odd i then n / i else 0)) -
            (∑ i ∈ Finset.Icc 1 n, (if Odd i then mult p i else 0)) :=
          Finset.sum_tsub_distrib _ hle

lemma card_le_sum_oddDiv (n : ℕ) (p : Nat.Partition n) (hp : p ∈ oddPartitions n) :
    p.parts.card ≤ ∑ i ∈ Finset.Icc 1 n, (if Odd i then n / i else 0) := by
  rw [← sum_odd_mult_eq_card n p hp]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hodd : Odd i
  · simp [hodd]
    exact mult_le_div p i
  · simp [hodd]

lemma n_le_sum_oddDiv (n : ℕ) (hn : 1 ≤ n) :
    n ≤ ∑ i ∈ Finset.Icc 1 n, (if Odd i then n / i else 0) := by
  have h₁ : ∑ i ∈ Finset.Icc 1 n, (if Odd i then n / i else 0) ≥ ∑ i ∈ Finset.Icc 1 1, (if Odd i then n / i else 0) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    · intro x _ _
      split_ifs <;> simp_all
  have h₂ : ∑ i ∈ Finset.Icc 1 1, (if Odd i then n / i else 0) = (if Odd 1 then n / 1 else 0) := by
    simp [Finset.sum_range_one]
  have h₃ : (if Odd 1 then n / 1 else 0) = n := by
    have h₄ : Odd 1 := by decide
    simp [h₄]
  linarith

lemma rootMultiplicity_hOLambda_relation
    (n : ℕ) (hn : 1 ≤ n) (p : Nat.Partition n) (hp : p ∈ oddPartitions n) :
    rootMultiplicity (-1 : ℤ) (hOLambda n p) + p.parts.card =
    rootMultiplicity (-1 : ℤ) (hOLambda n (allOnesPartition n hn)) + n := by
  set C : ℕ := ∑ i ∈ Finset.Icc 1 n, (if Odd i then n / i else 0) with hC
  have hp_card_le : p.parts.card ≤ C := card_le_sum_oddDiv n p hp
  have hp_eq : rootMultiplicity (-1 : ℤ) (hOLambda n p) = C - p.parts.card := by
    rw [rootMult_hOLambda_eq n p, sum_odd_diff_eq n p, sum_odd_mult_eq_card n p hp]
  have hone : allOnesPartition n hn ∈ oddPartitions n := allOnesPartition_mem_oddPartitions n hn
  have hone_card : (allOnesPartition n hn).parts.card = n := allOnes_card n hn
  have hn_le : n ≤ C := n_le_sum_oddDiv n hn
  have hone_eq : rootMultiplicity (-1 : ℤ) (hOLambda n (allOnesPartition n hn)) = C - n := by
    rw [rootMult_hOLambda_eq n (allOnesPartition n hn), sum_odd_diff_eq n (allOnesPartition n hn),
        sum_odd_mult_eq_card n (allOnesPartition n hn) hone, hone_card]
  rw [hp_eq, hone_eq]
  omega

/-- The multiplicity of `1` in the all-ones partition is `n`. -/
lemma mult_allOnes_one (n : ℕ) (hn : 1 ≤ n) :
    mult (allOnesPartition n hn) 1 = n := by
  dsimp [mult, allOnesPartition]
  simp

/-- The multiplicity of any `i ≠ 1` in the all-ones partition is `0`. -/
lemma mult_allOnes_ne_one (n : ℕ) (hn : 1 ≤ n) (i : ℕ) (hi : i ≠ 1) :
    mult (allOnesPartition n hn) i = 0 := by
  simp [mult, allOnesPartition]
  simp_all [Multiset.mem_replicate]

lemma hOLambda_allOnes_closedForm (n : ℕ) (hn : 1 ≤ n) :
    hOLambda n (allOnesPartition n hn) =
      ∏ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ 1 < i),
        (1 + (X : Polynomial ℤ) ^ i) ^ (n / i) := by
  unfold hOLambda
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  rcases eq_or_lt_of_le (Finset.mem_Icc.mp hi).1 with heq | hgt
  · subst heq
    simp [mult_allOnes_one n hn]
  · rcases Nat.even_or_odd i with hev | hod
    · have hnod : ¬ Odd i := by
        rw [Nat.not_odd_iff_even]; exact hev
      simp [hnod]
    · have hne : i ≠ 1 := Nat.ne_of_gt hgt
      simp [hod, hgt, mult_allOnes_ne_one n hn i hne]

/-- `X^(2i) - 1 = (X^i - 1)(X^i + 1)` in `ℤ[X]`. -/
lemma X_pow_two_mul_sub_one_factor (i : ℕ) :
    (Polynomial.X : Polynomial ℤ) ^ (2 * i) - 1 =
      ((Polynomial.X : Polynomial ℤ) ^ i - 1) * ((Polynomial.X : Polynomial ℤ) ^ i + 1) := by
  ring

lemma X_pow_sub_one_ne_zero_int (i : ℕ) (hi : 1 ≤ i) :
    (X : Polynomial ℤ) ^ i - 1 ≠ 0 := by
  intro h
  have h₄ : (Polynomial.eval 0 ((X : Polynomial ℤ) ^ i - 1 : Polynomial ℤ)) = -1 := by
    simp [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub]
    cases i <;> simp_all
  rw [h] at h₄
  simp at h₄

lemma injOn_two_mul_divisors (d : ℕ) :
    Set.InjOn (fun k : ℕ => 2 * k) (d.divisors : Set ℕ) := by
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : (0:ℕ) < 2) hab

lemma divisors_two_mul_eq_union (d : ℕ) (hd : 0 < d) (hodd : Odd d) :
    (2 * d).divisors = d.divisors ∪ d.divisors.image (fun k => 2 * k) := by
  have hd_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  have h2d_ne : 2 * d ≠ 0 := by positivity
  have _huse := hodd
  ext k
  simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
  constructor
  · rintro ⟨hk, _⟩
    rcases Nat.even_or_odd k with hke | hko
    · obtain ⟨m, rfl⟩ := hke
      right
      refine ⟨m, ⟨?_, hd_ne⟩, by ring⟩
      have h2m : 2 * m ∣ 2 * d := by
        have : m + m = 2 * m := by ring
        rw [← this]; exact hk
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0:ℕ) < 2)).mp h2m
    · left
      refine ⟨?_, hd_ne⟩
      have hcop : Nat.Coprime k 2 := hko.coprime_two_right
      exact hcop.dvd_of_dvd_mul_left hk
  · rintro (⟨hkd, _⟩ | ⟨m, ⟨hmd, _⟩, rfl⟩)
    · exact ⟨hkd.mul_left 2, h2d_ne⟩
    · exact ⟨Nat.mul_dvd_mul_left 2 hmd, h2d_ne⟩

lemma disjoint_divisors_image_two_mul (d : ℕ) (_hd : 0 < d) (hodd : Odd d) :
    Disjoint d.divisors (d.divisors.image (fun k => 2 * k)) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [Finset.mem_image] at hx2
  obtain ⟨y, hy, rfl⟩ := hx2
  have h₁ : y ∣ d := (Nat.mem_divisors.mp hy).1
  have h₂ : 2 * y ∣ d := by simp_all [Nat.mem_divisors]
  rcases Nat.eq_zero_or_pos y with hy0 | hy_pos
  · simp_all [Nat.mem_divisors]
  · have h₁₁ : 2 ∣ d := dvd_trans ⟨y, by ring⟩ h₂
    have h₁₂ : ¬ (2 ∣ d) := by
      cases' hodd with k hk; omega
    exact h₁₂ h₁₁

lemma prod_cyclotomic_two_mul_split (d : ℕ) (hd : 0 < d) (hodd : Odd d) :
    (∏ k ∈ (2 * d).divisors, cyclotomic k ℤ) =
      (∏ k ∈ d.divisors, cyclotomic k ℤ) * (∏ k ∈ d.divisors, cyclotomic (2 * k) ℤ) := by
  rw [divisors_two_mul_eq_union d hd hodd,
      Finset.prod_union (disjoint_divisors_image_two_mul d hd hodd),
      Finset.prod_image (injOn_two_mul_divisors d)]

lemma one_add_X_pow_eq_prod_cyclotomic (i : ℕ) (hi : 1 ≤ i) (hodd : Odd i) :
    1 + (X : Polynomial ℤ) ^ i =
      ∏ e ∈ i.divisors, cyclotomic (2 * e) ℤ := by
  have h2i_pos : 0 < 2 * i := Nat.mul_pos (by norm_num) hi
  have hcyc_2i : (∏ k ∈ (2 * i).divisors, cyclotomic k ℤ) =
      (X : Polynomial ℤ) ^ (2 * i) - 1 :=
    Polynomial.prod_cyclotomic_eq_X_pow_sub_one h2i_pos ℤ
  have hi_pos : 0 < i := hi
  have hcyc_i : (∏ k ∈ i.divisors, cyclotomic k ℤ) =
      (X : Polynomial ℤ) ^ i - 1 :=
    Polynomial.prod_cyclotomic_eq_X_pow_sub_one hi_pos ℤ
  have hsplit : (∏ k ∈ (2 * i).divisors, cyclotomic k ℤ) =
      (∏ k ∈ i.divisors, cyclotomic k ℤ) *
        (∏ k ∈ i.divisors, cyclotomic (2 * k) ℤ) :=
    prod_cyclotomic_two_mul_split i hi_pos hodd
  have hfact : (X : Polynomial ℤ) ^ (2 * i) - 1 =
      ((X : Polynomial ℤ) ^ i - 1) * ((X : Polynomial ℤ) ^ i + 1) :=
    X_pow_two_mul_sub_one_factor i
  have hkey : ((X : Polynomial ℤ) ^ i - 1) * ((X : Polynomial ℤ) ^ i + 1) =
      ((X : Polynomial ℤ) ^ i - 1) * (∏ k ∈ i.divisors, cyclotomic (2 * k) ℤ) := by
    rw [← hfact, ← hcyc_2i, hsplit, hcyc_i]
  have hne : (X : Polynomial ℤ) ^ i - 1 ≠ 0 := X_pow_sub_one_ne_zero_int i hi
  have hxi_eq : (X : Polynomial ℤ) ^ i + 1 = ∏ k ∈ i.divisors, cyclotomic (2 * k) ℤ :=
    mul_left_cancel₀ hne hkey
  rw [add_comm]
  exact hxi_eq

/-- `A(n,e) := ∑_{i ∈ [1,n], i odd, 1 < i, e ∣ i} ⌊n/i⌋`. This is the
exponent of `Φ_{2e}(X)` in the closed-form product `∏_{i odd, 1<i≤n}
(1+X^i)^{⌊n/i⌋}` after substituting the cyclotomic factorization. -/
def A (n e : ℕ) : ℕ :=
  ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ 1 < i ∧ e ∣ i), n / i

/-- The closed-form product `∏_i (1+X^i)^{⌊n/i⌋}` rewritten as a double product
using the cyclotomic factorization `1 + X^i = ∏_{e ∣ i} Φ_{2e}`. -/
lemma closedForm_eq_double_prod (n : ℕ) (_hn : 1 ≤ n) :
    (∏ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ 1 < i),
        (1 + (X : Polynomial ℤ) ^ i) ^ (n / i)) =
      ∏ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ 1 < i),
        ∏ e ∈ i.divisors, (cyclotomic (2 * e) ℤ) ^ (n / i) := by
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_Icc] at hi
  obtain ⟨⟨hi1, _⟩, hodd, _⟩ := hi
  rw [one_add_X_pow_eq_prod_cyclotomic i hi1 hodd, Finset.prod_pow]

lemma mem_swap_iff (n i d : ℕ) :
    (i ∈ (Finset.Icc 1 n).filter (fun i => Odd i) ∧ d ∈ i.divisors) ↔
      (i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ d ∣ i) ∧
        d ∈ (Finset.Icc 1 n).filter (fun e => Odd e)) := by
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨⟨hi1, hin⟩, hodd⟩, hdvd, hi0⟩
    have hd_pos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (fun hd => by
      subst hd; exact hi0 (Nat.eq_zero_of_zero_dvd hdvd))
    have hd_le_i : d ≤ i := Nat.le_of_dvd (Nat.lt_of_lt_of_le Nat.zero_lt_one hi1) hdvd
    have hd_le_n : d ≤ n := hd_le_i.trans hin
    have hd_odd : Odd d := Odd.of_dvd_nat hodd hdvd
    exact ⟨⟨⟨hi1, hin⟩, hodd, hdvd⟩, ⟨hd_pos, hd_le_n⟩, hd_odd⟩
  · rintro ⟨⟨⟨hi1, hin⟩, hodd, hdvd⟩, ⟨_, _⟩, _⟩
    refine ⟨⟨⟨hi1, hin⟩, hodd⟩, hdvd, ?_⟩
    omega

lemma double_prod_swap (n : ℕ) (hn : 1 ≤ n) :
    (∏ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ 1 < i),
        ∏ e ∈ i.divisors, (cyclotomic (2 * e) ℤ) ^ (n / i)) =
      ∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e),
        ∏ i ∈ (Finset.Icc 1 n).filter
              (fun i => Odd i ∧ 1 < i ∧ e ∣ i),
          (cyclotomic (2 * e) ℤ) ^ (n / i) := by
  have _hn := hn
  rw [Finset.prod_sigma' ((Finset.Icc 1 n).filter (fun i => Odd i ∧ 1 < i))
        (fun i => i.divisors)
        (fun i e => (cyclotomic (2 * e) ℤ) ^ (n / i))]
  rw [Finset.prod_sigma' ((Finset.Icc 1 n).filter (fun e => Odd e))
        (fun e => (Finset.Icc 1 n).filter (fun i => Odd i ∧ 1 < i ∧ e ∣ i))
        (fun e i => (cyclotomic (2 * e) ℤ) ^ (n / i))]
  apply Finset.prod_nbij' (fun x => ⟨x.2, x.1⟩) (fun y => ⟨y.2, y.1⟩)
  · rintro ⟨i, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_filter] at hx ⊢
    obtain ⟨⟨hiIcc, hodd, h1i⟩, hei⟩ := hx
    have hiff := (mem_swap_iff n i e).mp
      ⟨Finset.mem_filter.mpr ⟨hiIcc, hodd⟩, hei⟩
    obtain ⟨hi', he'⟩ := hiff
    rw [Finset.mem_filter] at hi' he'
    exact ⟨⟨he'.1, he'.2⟩, hiIcc, hodd, h1i, hi'.2.2⟩
  · rintro ⟨e, i⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_filter] at hy ⊢
    obtain ⟨⟨heIcc, hoe⟩, hiIcc, hodd, h1i, hei⟩ := hy
    have hiff := (mem_swap_iff n i e).mpr
      ⟨Finset.mem_filter.mpr ⟨hiIcc, hodd, hei⟩,
       Finset.mem_filter.mpr ⟨heIcc, hoe⟩⟩
    obtain ⟨hi', he'⟩ := hiff
    rw [Finset.mem_filter] at hi'
    exact ⟨⟨hi'.1, hi'.2, h1i⟩, he'⟩
  · rintro ⟨i, e⟩ _; rfl
  · rintro ⟨e, i⟩ _; rfl
  · rintro ⟨i, e⟩ _; rfl

lemma inner_prod_collapse (n : ℕ) :
    (∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e),
        ∏ i ∈ (Finset.Icc 1 n).filter
              (fun i => Odd i ∧ 1 < i ∧ e ∣ i),
          (cyclotomic (2 * e) ℤ) ^ (n / i)) =
      ∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e),
        (cyclotomic (2 * e) ℤ) ^ A n e := by
  refine Finset.prod_congr rfl ?_
  intro e _
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

lemma closedForm_eq_prod_cyclotomic (n : ℕ) (hn : 1 ≤ n) :
    (∏ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ 1 < i),
        (1 + (X : Polynomial ℤ) ^ i) ^ (n / i)) =
      ∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e),
        (cyclotomic (2 * e) ℤ) ^ A n e := by
  rw [closedForm_eq_double_prod n hn, double_prod_swap n hn,
      inner_prod_collapse n]

/-- **Lower bound on the exponent `A(n,e)` for odd `1 < e ≤ n`.**

`A(n,e) ≥ ⌊n/e⌋` because the term `i = e` (which satisfies `1 ≤ i ≤ n`,
`e ∣ i`, `1 < i`, and `Odd i`) is in the index set and contributes `⌊n/e⌋`
to the sum. All terms are nonnegative. -/
lemma A_ge_floor (n e : ℕ) (he : 1 ≤ e) (heN : e ≤ n)
    (h1e : 1 < e) (hodd : Odd e) :
    n / e ≤ A n e := by
  unfold A
  have hmem : e ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ 1 < i ∧ e ∣ i) := by
    rw [Finset.mem_filter]
    refine ⟨?_, hodd, h1e, dvd_refl e⟩
    rw [Finset.mem_Icc]
    exact ⟨he, heN⟩
  exact Finset.single_le_sum (f := fun i => n / i)
    (fun _ _ => Nat.zero_le _) hmem

def M (n e : ℕ) (p : Nat.Partition n) : ℕ :=
  ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ e ∣ i), (n / i - mult p i)

/-- The candidate cyclotomic product on the RHS. -/

noncomputable def gOCandidate (n : ℕ) : Polynomial ℤ :=
  (cyclotomic 2 ℤ) ^ A n 1 *
  ∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e ∧ 1 < e),
    (cyclotomic (2 * e) ℤ) ^ (A n e - n / e)

/-- `X^(2*i) - 1 = (X^i - 1)(X^i + 1)` in `ℤ[X]`. -/

lemma hOLambda_eq_double_prod (n : ℕ) (p : Nat.Partition n) :
    hOLambda n p =
      ∏ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i),
        ∏ d ∈ i.divisors,
          (cyclotomic (2 * d) ℤ) ^ (n / i - mult p i) := by
  unfold hOLambda
  rw [← Finset.prod_filter (s := Finset.Icc 1 n) (p := fun i => Odd i)
      (f := fun i => (1 + (X : Polynomial ℤ) ^ i) ^ (n / i - mult p i))]
  refine Finset.prod_congr rfl ?_
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_Icc] at hi
  obtain ⟨⟨hi1, _hin⟩, hiodd⟩ := hi
  rw [one_add_X_pow_eq_prod_cyclotomic i hi1 hiodd]
  rw [Finset.prod_pow]

lemma hOLambda_swap (n : ℕ) (p : Nat.Partition n) :
    (∏ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i),
        ∏ d ∈ i.divisors,
          (cyclotomic (2 * d) ℤ) ^ (n / i - mult p i)) =
      ∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e),
        ∏ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ e ∣ i),
          (cyclotomic (2 * e) ℤ) ^ (n / i - mult p i) := by
  refine Finset.prod_comm' (s := (Finset.Icc 1 n).filter (fun i => Odd i))
    (t := fun i => i.divisors)
    (t' := (Finset.Icc 1 n).filter (fun e => Odd e))
    (s' := fun d => (Finset.Icc 1 n).filter (fun i => Odd i ∧ d ∣ i))
    (f := fun i d => (cyclotomic (2 * d) ℤ) ^ (n / i - mult p i))
    ?_
  intro i d
  exact mem_swap_iff n i d

lemma inner_prod_eq_pow_M (n e : ℕ) (p : Nat.Partition n) :
    (∏ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ e ∣ i),
        (cyclotomic (2 * e) ℤ) ^ (n / i - mult p i)) =
      (cyclotomic (2 * e) ℤ) ^ M n e p := by
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

/-- **Cyclotomic factorization of `hOLambda n p`.** -/

lemma hOLambda_eq_prod_cyclotomic (n : ℕ) (p : Nat.Partition n) :
    hOLambda n p =
      ∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e),
        (cyclotomic (2 * e) ℤ) ^ M n e p := by
  rw [hOLambda_eq_double_prod, hOLambda_swap]
  refine Finset.prod_congr rfl ?_
  intro e _
  exact inner_prod_eq_pow_M n e p


lemma M_one_eq (n : ℕ) (p : Nat.Partition n) :
    M n 1 p = ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i),
                (n / i - mult p i) := by
  unfold M
  congr 1
  apply Finset.filter_congr
  intro i _
  simp

lemma A_one_eq (n : ℕ) :
    A n 1 = ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ 1 < i), n / i := by
  unfold A
  congr 1
  apply Finset.filter_congr
  intro i _
  constructor
  · rintro ⟨ho, hlt, _⟩
    exact ⟨ho, hlt⟩
  · rintro ⟨ho, hlt⟩
    exact ⟨ho, hlt, one_dvd i⟩

lemma sum_odd_div_eq_n_add_A (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i), n / i = n + A n 1 := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 n).filter (fun i => Odd i)) (fun i => i = 1) (fun i => n / i)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have hfilter1 : (Finset.Icc 1 n).filter (fun i => Odd i ∧ i = 1) = {1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_singleton, Finset.mem_Icc]
    constructor
    · rintro ⟨_, _, rfl⟩; rfl
    · rintro rfl; exact ⟨⟨le_refl 1, hn⟩, ⟨by decide, rfl⟩⟩
  have hfilter2 :
      (Finset.Icc 1 n).filter (fun i => Odd i ∧ ¬ i = 1) =
      (Finset.Icc 1 n).filter (fun i => Odd i ∧ 1 < i) := by
    apply Finset.filter_congr
    intros i hi
    rw [Finset.mem_Icc] at hi
    constructor
    · rintro ⟨ho, hne⟩
      exact ⟨ho, lt_of_le_of_ne hi.1 (fun h => hne h.symm)⟩
    · rintro ⟨ho, hlt⟩
      exact ⟨ho, fun h => by omega⟩
  rw [hfilter1, hfilter2] at hsplit
  rw [Finset.sum_singleton, Nat.div_one] at hsplit
  have hsplit' : ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i), n / i
      = n + ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ 1 < i), n / i := by
    linarith
  rw [hsplit', A_one_eq]

lemma sum_sub_split (n : ℕ) (p : Nat.Partition n) :
    ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i), (n / i - mult p i)
      = (∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i), n / i)
        - (∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i), mult p i) := by
  apply Finset.sum_tsub_distrib
  intro i _
  exact mult_le_div p i

lemma sum_filter_odd_mult_eq_card (n : ℕ) (p : Nat.Partition n) (hp : p ∈ oddPartitions n) :
    ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i), mult p i = p.parts.card := by
  rw [Finset.sum_filter]
  exact sum_odd_mult_eq_card n p hp

lemma M_one_eq_A_add_diff (n : ℕ) (hn : 1 ≤ n) (p : Nat.Partition n)
    (hp : p ∈ oddPartitions n) :
    M n 1 p = A n 1 + (n - p.parts.card) := by
  rw [M_one_eq]
  rw [sum_sub_split]
  rw [sum_filter_odd_mult_eq_card n p hp, sum_odd_div_eq_n_add_A n hn]
  have hcard : p.parts.card ≤ n := partition_card_le n p
  omega

lemma min_M_eq_one (n : ℕ) (hn : 1 ≤ n) :
    (∀ p ∈ oddPartitions n, A n 1 ≤ M n 1 p) ∧
    (∃ p ∈ oddPartitions n, M n 1 p = A n 1) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [M_one_eq_A_add_diff n hn p hp]
    exact Nat.le_add_right _ _
  · refine ⟨allOnesPartition n hn, allOnesPartition_mem_oddPartitions n hn, ?_⟩
    rw [M_one_eq_A_add_diff n hn _ (allOnesPartition_mem_oddPartitions n hn)]
    rw [allOnes_card n hn]
    simp

/-- The auxiliary sum `S(n,e,p) := ∑_{i ∈ Icc 1 n, Odd i, e ∣ i} mult p i`. -/

def S (n e : ℕ) (p : Nat.Partition n) : ℕ :=
  ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ e ∣ i), mult p i

/-- The witness partition for `min_M_gt_one`. -/

noncomputable def mWitness (n e : ℕ) (he : 1 < e) (_hen : e ≤ n) (_hodd : Odd e) :
    Nat.Partition n :=
{ parts := Multiset.replicate (n / e) e + Multiset.replicate (n - e * (n / e)) 1
  , parts_pos := by
      intro i hi
      rcases Multiset.mem_add.mp hi with hi | hi
      · have hi' := Multiset.eq_of_mem_replicate hi
        omega
      · have hi' := Multiset.eq_of_mem_replicate hi
        omega
  , parts_sum := by
      simp [Multiset.sum_replicate]
      have h1 : e * (n / e) ≤ n := Nat.mul_div_le n e
      have h2 : n / e * e = e * (n / e) := Nat.mul_comm _ _
      omega }

lemma mul_count_le_sum (m : Multiset ℕ) (i : ℕ) :
    i * m.count i ≤ m.sum := by
  have hsplit : m.filter (· = i) + m.filter (· ≠ i) = m :=
    Multiset.filter_add_not (· = i) m
  have hsum : m.sum = (m.filter (· = i)).sum + (m.filter (· ≠ i)).sum := by
    conv_lhs => rw [← hsplit]
    rw [Multiset.sum_add]
  have hfilter_eq : m.filter (· = i) = Multiset.replicate (m.count i) i :=
    Multiset.filter_eq' m i
  have hsum_eq : (m.filter (· = i)).sum = i * m.count i := by
    rw [hfilter_eq, Multiset.sum_replicate, smul_eq_mul, Nat.mul_comm]
  rw [hsum, hsum_eq]
  exact Nat.le_add_right _ _

lemma filter_e_dvd_eq_with_one_lt (n e : ℕ) (he : 1 < e) :
    ((Finset.Icc 1 n).filter (fun i => Odd i ∧ e ∣ i))
      = ((Finset.Icc 1 n).filter (fun i => Odd i ∧ 1 < i ∧ e ∣ i)) := by
  apply Finset.Subset.antisymm
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
    obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := hi
    have h₅ : 1 < i := by
      by_contra h
      have h₆ : i = 1 := by omega
      rw [h₆] at h₄
      have h₈ : e ≤ 1 := Nat.le_of_dvd (by decide) h₄
      omega
    exact ⟨⟨h₁, h₂⟩, h₃, h₅, h₄⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
    obtain ⟨⟨h₁, h₂⟩, h₃, _, h₅⟩ := hi
    exact ⟨⟨h₁, h₂⟩, h₃, h₅⟩

lemma M_eq_sub (n e : ℕ) (he : 1 < e) (p : Nat.Partition n) :
    M n e p = A n e - S n e p := by
  unfold M
  rw [Finset.sum_tsub_distrib _ (fun i _ => mult_le_div p i)]
  show _ - _ = A n e - S n e p
  congr 1
  unfold A
  exact Finset.sum_congr (filter_e_dvd_eq_with_one_lt n e he) (fun _ _ => rfl)

lemma parts_toFinset_subset (n : ℕ) (p : Nat.Partition n) :
    p.parts.toFinset ⊆ Finset.Icc 1 n := by
  grind

lemma sum_i_mult_eq (n : ℕ) (p : Nat.Partition n) :
    ∑ i ∈ Finset.Icc 1 n, i * p.parts.count i = n := by
  have hsub : p.parts.toFinset ⊆ Finset.Icc 1 n :=
    parts_toFinset_subset n p
  have hkey : p.parts.sum =
      ∑ i ∈ Finset.Icc 1 n, Multiset.count i p.parts • i :=
    Finset.sum_multiset_count_of_subset p.parts (Finset.Icc 1 n) hsub
  have hsum : p.parts.sum = n := p.parts_sum
  have : (∑ i ∈ Finset.Icc 1 n, Multiset.count i p.parts • i) = n := by
    rw [← hkey]; exact hsum
  calc ∑ i ∈ Finset.Icc 1 n, i * p.parts.count i
      = ∑ i ∈ Finset.Icc 1 n, Multiset.count i p.parts • i := by
        apply Finset.sum_congr rfl
        intro i _
        simp [Nat.mul_comm, smul_eq_mul]
    _ = n := this

lemma S_le_div (n e : ℕ) (he : 1 < e) (p : Nat.Partition n) :
    S n e p ≤ n / e := by
  have he0 : 0 < e := Nat.lt_of_lt_of_le Nat.one_pos he.le
  refine Nat.le_div_iff_mul_le he0 |>.mpr ?_
  rw [Nat.mul_comm]
  unfold S
  rw [Finset.mul_sum]
  have hstep1 :
      ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ e ∣ i), e * mult p i
        ≤ ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ e ∣ i),
            i * mult p i := by
    refine Finset.sum_le_sum ?_
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi
    obtain ⟨⟨h1, _⟩, _, hed⟩ := hi
    have hie : e ≤ i := Nat.le_of_dvd (Nat.lt_of_lt_of_le Nat.zero_lt_one h1) hed
    exact Nat.mul_le_mul_right _ hie
  have hstep2 :
      ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ e ∣ i),
          i * mult p i
        ≤ ∑ i ∈ Finset.Icc 1 n, i * mult p i := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · exact Finset.filter_subset _ _
    · intros; exact Nat.zero_le _
  have hstep3 : ∑ i ∈ Finset.Icc 1 n, i * mult p i = n := by
    unfold mult
    exact sum_i_mult_eq n p
  calc ∑ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ e ∣ i), e * mult p i
      ≤ _ := hstep1
    _ ≤ _ := hstep2
    _ = n := hstep3

lemma mWitness_mem (n e : ℕ) (he : 1 < e) (hen : e ≤ n) (hodd : Odd e) :
    mWitness n e he hen hodd ∈ oddPartitions n := by
  unfold oddPartitions
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro i hi
  change i ∈ Multiset.replicate (n / e) e + Multiset.replicate (n - e * (n / e)) 1 at hi
  rcases Multiset.mem_add.mp hi with hi | hi
  · have : i = e := Multiset.eq_of_mem_replicate hi
    rw [this]; exact hodd
  · have : i = 1 := Multiset.eq_of_mem_replicate hi
    rw [this]; exact odd_one

lemma mult_mWitness_e (n e : ℕ) (he : 1 < e) (hen : e ≤ n) (hodd : Odd e) :
    mult (mWitness n e he hen hodd) e = n / e := by
  unfold mult mWitness
  simp only [Multiset.count_add, Multiset.count_replicate_self]
  have h : Multiset.count e (Multiset.replicate (n - e * (n / e)) 1) = 0 := by
    rw [Multiset.count_replicate]
    have : (1 : ℕ) ≠ e := by omega
    simp [this]
  omega

lemma i_ne_one_of_filter (n e : ℕ) (he : 1 < e)
    (i : ℕ) (hi_mem : i ∈ Finset.Icc 1 n) (hdvd : e ∣ i) (hne : i ≠ e) :
    i ≠ 1 := by
  intro hi1
  subst hi1
  -- e ∣ 1 implies e ≤ 1
  have : e ≤ 1 := Nat.le_of_dvd (by decide) hdvd
  omega

lemma mult_mWitness_other (n e : ℕ) (he : 1 < e) (hen : e ≤ n) (hodd : Odd e)
    (i : ℕ) (hi : i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ e ∣ i))
    (hne : i ≠ e) :
    mult (mWitness n e he hen hodd) i = 0 := by
  rw [Finset.mem_filter] at hi
  obtain ⟨hi_mem, _hodd_i, hdvd⟩ := hi
  have hi_ne_one : i ≠ 1 := i_ne_one_of_filter n e he i hi_mem hdvd hne
  unfold mult mWitness
  simp only
  rw [Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
  have h1 : ¬ (e = i) := fun h => hne h.symm
  have h2 : ¬ ((1 : ℕ) = i) := fun h => hi_ne_one h.symm
  rw [if_neg h1, if_neg h2]

lemma e_mem_filter (n e : ℕ) (he : 1 < e) (hen : e ≤ n) (hodd : Odd e) :
    e ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ e ∣ i) := by
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨by omega, hen⟩, hodd, dvd_refl _⟩

lemma S_mWitness_eq (n e : ℕ) (he : 1 < e) (hen : e ≤ n) (hodd : Odd e) :
    S n e (mWitness n e he hen hodd) = n / e := by
  unfold S
  rw [Finset.sum_eq_single e]
  · exact mult_mWitness_e n e he hen hodd
  · intro i hi hne
    exact mult_mWitness_other n e he hen hodd i hi hne
  · intro h
    exact absurd (e_mem_filter n e he hen hodd) h

lemma min_M_gt_one (n e : ℕ) (he : 1 < e) (heN : e ≤ n) (hodd : Odd e) :
    (∀ p ∈ oddPartitions n, A n e - n / e ≤ M n e p) ∧
    (∃ p ∈ oddPartitions n, M n e p = A n e - n / e) := by
  refine ⟨?_, ?_⟩
  · intro p _hp
    rw [M_eq_sub n e he p]
    exact Nat.sub_le_sub_left (S_le_div n e he p) (A n e)
  · refine ⟨mWitness n e he heN hodd, mWitness_mem n e he heN hodd, ?_⟩
    rw [M_eq_sub n e he, S_mWitness_eq n e he heN hodd]

/-- **For odd `1 < e ≤ n`, `A(n,e) ≥ n/e`.** Because the index `i = e` is in
the filter `{i ∈ Icc 1 n | Odd i ∧ 1 < i ∧ e ∣ i}` and contributes `n/e`. -/

lemma prod_cyclotomic_split_e_one (n : ℕ) (hn : 1 ≤ n) (f : ℕ → Polynomial ℤ) :
    ∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e), f e =
      f 1 * ∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e ∧ 1 < e), f e := by
  have h₁ : (Finset.Icc 1 n).filter (fun e => Odd e) = {1} ∪ (Finset.Icc 1 n).filter (fun e => Odd e ∧ 1 < e) := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    <;>
    by_cases hx : x = 1 <;>
    by_cases h_odd : x % 2 = 1 <;>
    by_cases h₁_lt : 1 < x <;>
    simp_all [Nat.odd_iff, Nat.even_iff]
    <;>
    (try { omega })
  rw [h₁]
  rw [Finset.prod_union] <;>
  (try {
    have h₂ : Disjoint ({1} : Finset ℕ) ((Finset.Icc 1 n).filter (fun e => Odd e ∧ 1 < e)) := by
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      simp only [Finset.mem_singleton] at hx₁
      simp only [Finset.mem_filter, Finset.mem_Icc] at hx₂
      simp_all [Nat.odd_iff, Nat.even_iff]
    exact h₂
  }) <;>
  (try {
    simp [Finset.prod_singleton]
  })

lemma gOCandidate_dvd_hOLambda (n : ℕ) (hn : 1 ≤ n) (p : Nat.Partition n)
    (hp : p ∈ oddPartitions n) :
    gOCandidate n ∣ hOLambda n p := by
  rw [hOLambda_eq_prod_cyclotomic]
  rw [prod_cyclotomic_split_e_one n hn (fun e => (cyclotomic (2 * e) ℤ) ^ M n e p)]
  unfold gOCandidate
  have hMineq1 : A n 1 ≤ M n 1 p := by
    rw [M_one_eq_A_add_diff n hn p hp]
    exact Nat.le_add_right _ _
  apply mul_dvd_mul
  · rw [show (2 : ℕ) = 2 * 1 from rfl]
    exact pow_dvd_pow _ hMineq1
  · apply Finset.prod_dvd_prod_of_dvd
    intro e he
    simp only [Finset.mem_filter, Finset.mem_Icc] at he
    obtain ⟨⟨_, hen⟩, hOdd, h1lt⟩ := he
    obtain ⟨hAe, _⟩ := min_M_gt_one n e h1lt hen hOdd
    exact pow_dvd_pow _ (hAe p hp)

/-- **`gOCandidate n ≠ 0`.** Each cyclotomic `Φ_k` is nonzero
(`Polynomial.cyclotomic_ne_zero`), powers of nonzero polynomials are nonzero,
and a finite product of nonzero polynomials in an integral domain is nonzero. -/

lemma gOCandidate_ne_zero (n : ℕ) : gOCandidate n ≠ 0 := by
  unfold gOCandidate
  refine mul_ne_zero (pow_ne_zero _ (Polynomial.cyclotomic_ne_zero _ _)) ?_
  exact Finset.prod_ne_zero_iff.mpr fun e _ =>
    pow_ne_zero _ (Polynomial.cyclotomic_ne_zero _ _)

/- **The unnormalized GCD divides `gOCandidate n`.** -/

/-- The target exponent unification. -/

def N (n e : ℕ) : ℕ := if e = 1 then A n 1 else A n e - n / e

noncomputable def onesPartition (n : ℕ) : Nat.Partition n :=
{ parts := Multiset.replicate n 1
  , parts_pos := by
      intro i hi
      have := Multiset.eq_of_mem_replicate hi
      omega
  , parts_sum := by simp [Multiset.sum_replicate] }

lemma onesPartition_mem (n : ℕ) : onesPartition n ∈ oddPartitions n := by
  simp only [oddPartitions, Finset.mem_filter, Finset.mem_univ, true_and]
  intro i hi
  have hi1 : i = 1 := Multiset.eq_of_mem_replicate hi
  subst hi1
  exact odd_one

lemma onesPartition_card (n : ℕ) : (onesPartition n).parts.card = n := by
  simp [onesPartition]

lemma gOCandidate_eq_prod_cyclotomic (n : ℕ) (hn : 1 ≤ n) :
    gOCandidate n =
      ∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e),
        (cyclotomic (2 * e) ℤ) ^ N n e := by
  rw [prod_cyclotomic_split_e_one n hn
        (fun e => (cyclotomic (2 * e) ℤ) ^ N n e)]
  unfold gOCandidate
  have h1 : N n 1 = A n 1 := by simp [N]
  have h2 : (2 * 1 : ℕ) = 2 := by norm_num
  have hprod :
      (∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e ∧ 1 < e),
            (cyclotomic (2 * e) ℤ) ^ (A n e - n / e)) =
      ∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e ∧ 1 < e),
            (cyclotomic (2 * e) ℤ) ^ N n e := by
    refine Finset.prod_congr rfl ?_
    intro e he
    have he' : 1 < e := (Finset.mem_filter.mp he).2.2
    have hne : e ≠ 1 := Nat.ne_of_gt he'
    simp [N, hne]
  rw [hprod, h1, h2]

lemma exists_witness_min_M (n e : ℕ) (he1 : 1 ≤ e) (heN : e ≤ n) (hodd : Odd e)
    (hn : 1 ≤ n) :
    ∃ p ∈ oddPartitions n, M n e p = N n e := by
  by_cases he : e = 1
  · subst he
    refine ⟨onesPartition n, onesPartition_mem n, ?_⟩
    have hM : M n 1 (onesPartition n) = A n 1 + (n - (onesPartition n).parts.card) :=
      M_one_eq_A_add_diff n hn (onesPartition n) (onesPartition_mem n)
    have hcard : (onesPartition n).parts.card = n := onesPartition_card n
    have hN : N n 1 = A n 1 := by simp [N]
    rw [hM, hcard, hN]
    simp
  · have he' : 1 < e := lt_of_le_of_ne he1 (fun h => he h.symm)
    refine ⟨mWitness n e he' heN hodd, mWitness_mem n e he' heN hodd, ?_⟩
    have hM : M n e (mWitness n e he' heN hodd) =
        A n e - S n e (mWitness n e he' heN hodd) :=
      M_eq_sub n e he' (mWitness n e he' heN hodd)
    have hS : S n e (mWitness n e he' heN hodd) = n / e :=
      S_mWitness_eq n e he' heN hodd
    have hN : N n e = A n e - n / e := by simp [N, he]
    rw [hM, hS, hN]

lemma cyclotomic_two_mul_ne_zero (e : ℕ) : (cyclotomic (2 * e) ℤ) ≠ 0 :=
  (Polynomial.cyclotomic.monic (2 * e) ℤ).ne_zero

lemma cyclotomic_two_mul_irreducible (e : ℕ) (he : 1 ≤ e) :
    Irreducible (cyclotomic (2 * e) ℤ) := by
  apply Polynomial.cyclotomic.irreducible
  omega

lemma cyclotomic_two_mul_not_associated (e e' : ℕ) (he : 1 ≤ e) (he' : 1 ≤ e')
    (hne : e ≠ e') :
    ¬ Associated (cyclotomic (2 * e) ℤ) (cyclotomic (2 * e') ℤ) := by
  intro hassoc
  have hmonic1 : (cyclotomic (2 * e) ℤ).Monic := Polynomial.cyclotomic.monic _ _
  have hmonic2 : (cyclotomic (2 * e') ℤ).Monic := Polynomial.cyclotomic.monic _ _
  have heq : cyclotomic (2 * e) ℤ = cyclotomic (2 * e') ℤ :=
    Polynomial.eq_of_monic_of_associated hmonic1 hmonic2 hassoc
  have h2ne : 2 * e ≠ 2 * e' := by
    intro h
    exact hne (Nat.eq_of_mul_eq_mul_left (by norm_num) h)
  exact h2ne (Polynomial.cyclotomic_injective heq)

lemma cyclotomic_two_mul_prime (e : ℕ) (he : 1 ≤ e) :
    Prime (cyclotomic (2 * e) ℤ) :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp (cyclotomic_two_mul_irreducible e he)

lemma emultiplicity_cyclotomic_two_mul_self (e : ℕ) (he : 1 ≤ e) :
    emultiplicity (cyclotomic (2 * e) ℤ) (cyclotomic (2 * e) ℤ) = 1 := by
  have hp : Prime (cyclotomic (2 * e) ℤ) := cyclotomic_two_mul_prime e he
  have hne : (cyclotomic (2 * e) ℤ) ≠ 0 := cyclotomic_ne_zero (2 * e) ℤ
  have hfm : FiniteMultiplicity (cyclotomic (2 * e) ℤ) (cyclotomic (2 * e) ℤ) :=
    FiniteMultiplicity.of_prime_left hp hne
  exact hfm.emultiplicity_self

lemma emultiplicity_cyclotomic_pow_self (e : ℕ) (he : 1 ≤ e) (k : ℕ) :
    emultiplicity (cyclotomic (2 * e) ℤ) ((cyclotomic (2 * e) ℤ) ^ k) = (k : ℕ∞) := by
  have hp : Prime (cyclotomic (2 * e) ℤ) := cyclotomic_two_mul_prime e he
  rw [emultiplicity_pow hp, emultiplicity_cyclotomic_two_mul_self e he, mul_one]

lemma emultiplicity_cyclotomic_two_mul_of_ne (e e' : ℕ) (he : 1 ≤ e) (he' : 1 ≤ e')
    (hne : e ≠ e') :
    emultiplicity (cyclotomic (2 * e) ℤ) (cyclotomic (2 * e') ℤ) = 0 := by
  rw [emultiplicity_eq_zero]
  intro hdvd
  have hp : Prime (cyclotomic (2 * e) ℤ) := cyclotomic_two_mul_prime e he
  have hq : Prime (cyclotomic (2 * e') ℤ) := cyclotomic_two_mul_prime e' he'
  have hassoc : Associated (cyclotomic (2 * e) ℤ) (cyclotomic (2 * e') ℤ) :=
    hp.irreducible.associated_of_dvd hq.irreducible hdvd
  exact cyclotomic_two_mul_not_associated e e' he he' hne hassoc

lemma emultiplicity_cyclotomic_pow_other (e e' : ℕ) (he : 1 ≤ e) (he' : 1 ≤ e')
    (hne : e ≠ e') (k : ℕ) :
    emultiplicity (cyclotomic (2 * e) ℤ) ((cyclotomic (2 * e') ℤ) ^ k) = 0 := by
  have hp : Prime (cyclotomic (2 * e) ℤ) := cyclotomic_two_mul_prime e he
  rw [emultiplicity_pow hp,
      emultiplicity_cyclotomic_two_mul_of_ne e e' he he' hne, mul_zero]

lemma emultiplicity_cyclotomic_hOLambda (n e : ℕ) (he1 : 1 ≤ e) (heN : e ≤ n) (hodd : Odd e)
    (p : Nat.Partition n) :
    emultiplicity (cyclotomic (2 * e) ℤ) (hOLambda n p) = (M n e p : ℕ∞) := by
  rw [hOLambda_eq_prod_cyclotomic n p]
  have hp : Prime (cyclotomic (2 * e) ℤ) := cyclotomic_two_mul_prime e he1
  rw [Finset.emultiplicity_prod hp]
  have hsum : ∀ e' ∈ (Finset.Icc 1 n).filter (fun e' => Odd e'),
      emultiplicity (cyclotomic (2 * e) ℤ) ((cyclotomic (2 * e') ℤ) ^ M n e' p)
        = (M n e' p : ℕ∞) * emultiplicity (cyclotomic (2 * e) ℤ) (cyclotomic (2 * e') ℤ) := by
    intro e' _
    exact emultiplicity_pow hp
  rw [Finset.sum_congr rfl hsum]
  have he_mem : e ∈ (Finset.Icc 1 n).filter (fun e' => Odd e') := by
    simp [Finset.mem_filter, Finset.mem_Icc, he1, heN, hodd]
  have hother : ∀ e' ∈ (Finset.Icc 1 n).filter (fun e' => Odd e'), e' ≠ e →
      (M n e' p : ℕ∞) * emultiplicity (cyclotomic (2 * e) ℤ) (cyclotomic (2 * e') ℤ) = 0 := by
    intro e' he' hne
    have he'1 : 1 ≤ e' := by
      rw [Finset.mem_filter, Finset.mem_Icc] at he'
      exact he'.1.1
    have h0 : emultiplicity (cyclotomic (2 * e) ℤ) (cyclotomic (2 * e') ℤ) = 0 :=
      emultiplicity_cyclotomic_two_mul_of_ne e e' he1 he'1 (Ne.symm hne)
    rw [h0, mul_zero]
  rw [Finset.sum_eq_single e (fun e' he' hne => hother e' he' hne)
        (fun h => absurd he_mem h)]
  rw [emultiplicity_cyclotomic_two_mul_self e he1, mul_one]

lemma emultiplicity_cyclotomic_target (n e : ℕ) (he1 : 1 ≤ e) (heN : e ≤ n) (hodd : Odd e) :
    emultiplicity (cyclotomic (2 * e) ℤ)
        (∏ e' ∈ (Finset.Icc 1 n).filter (fun e' => Odd e'),
            (cyclotomic (2 * e') ℤ) ^ N n e')
      = (N n e : ℕ∞) := by
  set Sset : Finset ℕ := (Finset.Icc 1 n).filter (fun e' => Odd e') with hSset
  have hp : Prime (cyclotomic (2 * e) ℤ) := cyclotomic_two_mul_prime e he1
  have heS : e ∈ Sset := by
    rw [hSset, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨he1, heN⟩, hodd⟩
  rw [Finset.emultiplicity_prod hp Sset (fun e' => (cyclotomic (2 * e') ℤ) ^ N n e')]
  rw [Finset.sum_eq_single e]
  · exact emultiplicity_cyclotomic_pow_self e he1 (N n e)
  · intro e' he'mem he'ne
    rw [hSset, Finset.mem_filter, Finset.mem_Icc] at he'mem
    obtain ⟨⟨he'1, _he'n⟩, _hodd'⟩ := he'mem
    exact emultiplicity_cyclotomic_pow_other e e' he1 he'1 (Ne.symm he'ne) (N n e')
  · intro hne
    exact absurd heS hne

lemma emultiplicity_cyclotomic_gcd_le (n e : ℕ) (he1 : 1 ≤ e) (heN : e ≤ n) (hodd : Odd e)
    (hn : 1 ≤ n) :
    emultiplicity (cyclotomic (2 * e) ℤ) ((oddPartitions n).gcd (hOLambda n))
      ≤ (N n e : ℕ∞) := by
  obtain ⟨p, hp_mem, hMeq⟩ := exists_witness_min_M n e he1 heN hodd hn
  have hdvd : (oddPartitions n).gcd (hOLambda n) ∣ hOLambda n p := Finset.gcd_dvd hp_mem
  have hmul : emultiplicity (cyclotomic (2 * e) ℤ) ((oddPartitions n).gcd (hOLambda n))
      ≤ emultiplicity (cyclotomic (2 * e) ℤ) (hOLambda n p) :=
    emultiplicity_le_emultiplicity_of_dvd_right hdvd
  have heq : emultiplicity (cyclotomic (2 * e) ℤ) (hOLambda n p) = (M n e p : ℕ∞) :=
    emultiplicity_cyclotomic_hOLambda n e he1 heN hodd p
  rw [heq] at hmul
  rw [hMeq] at hmul
  exact hmul

lemma gcd_prime_factor_associated (n : ℕ) (hn : 1 ≤ n) (q : Polynomial ℤ) (hq : Prime q)
    (hdvd : q ∣ (oddPartitions n).gcd (hOLambda n)) :
    ∃ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e), Associated q (cyclotomic (2 * e) ℤ) := by
  have hmem : onesPartition n ∈ oddPartitions n := onesPartition_mem n
  have hgcd_dvd : (oddPartitions n).gcd (hOLambda n) ∣ hOLambda n (onesPartition n) :=
    Finset.gcd_dvd hmem
  have hq_dvd_h : q ∣ hOLambda n (onesPartition n) := dvd_trans hdvd hgcd_dvd
  rw [hOLambda_eq_prod_cyclotomic n (onesPartition n)] at hq_dvd_h
  obtain ⟨e, he_mem, he_dvd⟩ := hq.exists_mem_finset_dvd hq_dvd_h
  have hq_dvd_cyc : q ∣ cyclotomic (2 * e) ℤ := hq.dvd_of_dvd_pow he_dvd
  refine ⟨e, he_mem, ?_⟩
  have he1 : 1 ≤ e := by
    have := Finset.mem_filter.mp he_mem
    exact (Finset.mem_Icc.mp this.1).1
  exact hq.associated_of_dvd (cyclotomic_two_mul_prime e he1) hq_dvd_cyc

lemma emultiplicity_other_prime_gcd_le (n : ℕ) (hn : 1 ≤ n) (q : Polynomial ℤ)
    (hq : Prime q)
    (hne : ∀ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e), ¬ Associated q (cyclotomic (2 * e) ℤ)) :
    emultiplicity q ((oddPartitions n).gcd (hOLambda n)) = 0 := by
  rw [emultiplicity_eq_zero]
  intro hdvd
  obtain ⟨e, he, hassoc⟩ := gcd_prime_factor_associated n hn q hq hdvd
  exact hne e he hassoc

lemma emultiplicity_eq_of_associated {q q' : Polynomial ℤ} (h : Associated q q')
    (x : Polynomial ℤ) : emultiplicity q x = emultiplicity q' x :=
  (emultiplicity_eq_of_associated_left h).symm

lemma target_ne_zero (n : ℕ) :
    (∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e),
        (cyclotomic (2 * e) ℤ) ^ N n e) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro e _
  exact pow_ne_zero _ (cyclotomic_two_mul_ne_zero e)

lemma gcd_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    (oddPartitions n).gcd (hOLambda n) ≠ 0 := by
  rw [Finset.gcd_ne_zero_iff]
  exact ⟨onesPartition n, onesPartition_mem n, hOLambda_ne_zero n (onesPartition n)⟩

lemma dvd_of_emultiplicity_le {a b : Polynomial ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ q : Polynomial ℤ, Prime q → emultiplicity q a ≤ emultiplicity q b) :
    a ∣ b := by
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors ha hb]
  rw [Multiset.le_iff_count]
  intro p
  classical
  by_cases hp : p ∈ UniqueFactorizationMonoid.normalizedFactors a
  · rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff' ha] at hp
    obtain ⟨hirr, hnorm, _⟩ := hp
    have hprime : Prime p := hirr.prime
    have ea : emultiplicity p a =
        (Multiset.count (normalize p) (UniqueFactorizationMonoid.normalizedFactors a) : ℕ∞) :=
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hirr ha
    have eb : emultiplicity p b =
        (Multiset.count (normalize p) (UniqueFactorizationMonoid.normalizedFactors b) : ℕ∞) :=
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hirr hb
    rw [hnorm] at ea eb
    have hle : emultiplicity p a ≤ emultiplicity p b := h p hprime
    rw [ea, eb] at hle
    exact_mod_cast hle
  · rw [Multiset.count_eq_zero.mpr hp]
    exact Nat.zero_le _

lemma gcd_dvd_prod_cyclotomic_target (n : ℕ) (hn : 1 ≤ n) :
    (oddPartitions n).gcd (hOLambda n) ∣
      ∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e),
        (cyclotomic (2 * e) ℤ) ^ N n e := by
  apply dvd_of_emultiplicity_le (gcd_ne_zero n hn) (target_ne_zero n)
  intro q hq
  by_cases hcase : ∃ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e),
      Associated q (cyclotomic (2 * e) ℤ)
  · obtain ⟨e, he, hassoc⟩ := hcase
    have heFmem := Finset.mem_filter.mp he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp heFmem.1).1
    have heN : e ≤ n := (Finset.mem_Icc.mp heFmem.1).2
    have hodd : Odd e := heFmem.2
    rw [emultiplicity_eq_of_associated hassoc, emultiplicity_eq_of_associated hassoc]
    calc emultiplicity (cyclotomic (2 * e) ℤ) ((oddPartitions n).gcd (hOLambda n))
        ≤ (N n e : ℕ∞) := emultiplicity_cyclotomic_gcd_le n e he1 heN hodd hn
      _ = emultiplicity (cyclotomic (2 * e) ℤ)
            (∏ e' ∈ (Finset.Icc 1 n).filter (fun e' => Odd e'),
                (cyclotomic (2 * e') ℤ) ^ N n e') :=
            (emultiplicity_cyclotomic_target n e he1 heN hodd).symm
  · push_neg at hcase
    rw [emultiplicity_other_prime_gcd_le n hn q hq hcase]
    exact zero_le _

lemma gO_dvd_gOCandidate_unnormalized (n : ℕ) (hn : 1 ≤ n) :
    (oddPartitions n).gcd (hOLambda n) ∣ gOCandidate n := by
  rw [gOCandidate_eq_prod_cyclotomic n hn]
  exact gcd_dvd_prod_cyclotomic_target n hn

/-- Constant term of a power: if `p.coeff 0 = 1`, then `(p ^ k).coeff 0 = 1`. -/

lemma coeff_zero_pow_eq_one {p : Polynomial ℤ} (h : p.coeff 0 = 1) (k : ℕ) :
    (p ^ k).coeff 0 = 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
    calc (p ^ (n + 1)).coeff 0
        = (p ^ n * p).coeff 0 := by ring_nf
      _ = (p ^ n).coeff 0 * p.coeff 0 := by simp [mul_coeff_zero]
      _ = 1 * 1 := by rw [ih, h]
      _ = 1 := by simp

/-- **The constant term of `gOCandidate n` is `+1`.** -/
lemma gOCandidate_coeff_zero (n : ℕ) (hn : 1 ≤ n) :
    (gOCandidate n).coeff 0 = 1 := by
  unfold gOCandidate
  rw [Polynomial.mul_coeff_zero]
  have h2 : (cyclotomic 2 ℤ).coeff 0 = 1 :=
    Polynomial.cyclotomic_coeff_zero ℤ (by norm_num)
  rw [coeff_zero_pow_eq_one h2]
  rw [one_mul]
  rw [Polynomial.coeff_zero_prod]
  apply Finset.prod_eq_one
  intro e he
  simp only [Finset.mem_filter, Finset.mem_Icc] at he
  obtain ⟨⟨_, _⟩, _, he1⟩ := he
  have hcoeff : (cyclotomic (2 * e) ℤ).coeff 0 = 1 := by
    apply Polynomial.cyclotomic_coeff_zero
    omega
  exact coeff_zero_pow_eq_one hcoeff _

/-- The unnormalized GCD and `gOCandidate n` are associates: in `ℤ[X]`,
mutual divisibility with a nonzero polynomial yields `±` equality. -/

lemma eq_or_neg_eq_of_associated_int_poly {f g : Polynomial ℤ}
    (hf : f ≠ 0) (hfg : f ∣ g) (hgf : g ∣ f) : f = g ∨ f = -g := by
  have hassoc : Associated f g := associated_of_dvd_dvd hfg hgf
  obtain ⟨u, hu⟩ := hassoc
  have hunit : IsUnit (u : Polynomial ℤ) := u.isUnit
  rw [Polynomial.isUnit_iff] at hunit
  obtain ⟨r, hr_unit, hr_eq⟩ := hunit
  rw [Int.isUnit_iff] at hr_unit
  rcases hr_unit with rfl | rfl
  · left
    have hu1 : (u : Polynomial ℤ) = 1 := by rw [← hr_eq]; simp
    rw [hu1, mul_one] at hu
    exact hu
  · right
    have hum1 : (u : Polynomial ℤ) = -1 := by rw [← hr_eq]; simp
    rw [hum1] at hu
    linear_combination -hu

lemma gcd_eq_or_neg_gOCandidate (n : ℕ) (hn : 1 ≤ n) :
    (oddPartitions n).gcd (hOLambda n) = gOCandidate n ∨
    (oddPartitions n).gcd (hOLambda n) = -gOCandidate n := by
  have h1 : gOCandidate n ∣ (oddPartitions n).gcd (hOLambda n) :=
    Finset.dvd_gcd fun p hp => gOCandidate_dvd_hOLambda n hn p hp
  have h2 : (oddPartitions n).gcd (hOLambda n) ∣ gOCandidate n :=
    gO_dvd_gOCandidate_unnormalized n hn
  rcases eq_or_neg_eq_of_associated_int_poly (gOCandidate_ne_zero n) h1 h2 with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h]; ring)

/-- **Cyclotomic factorization of `gO n`.** -/

lemma gO_eq_prod_cyclotomic (n : ℕ) (hn : 1 ≤ n) :
    gO n =
      (cyclotomic 2 ℤ) ^ A n 1 *
      ∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e ∧ 1 < e),
        (cyclotomic (2 * e) ℤ) ^ (A n e - n / e) := by
  -- Goal: `gO n = gOCandidate n` (definitionally).
  show gO n = gOCandidate n
  rw [show gO n = if ((oddPartitions n).gcd (hOLambda n)).coeff 0 = 1
                  then (oddPartitions n).gcd (hOLambda n)
                  else -(oddPartitions n).gcd (hOLambda n) from rfl]
  rcases gcd_eq_or_neg_gOCandidate n hn with h | h
  · -- Case gcd = gOCandidate
    have hcoeff : ((oddPartitions n).gcd (hOLambda n)).coeff 0 = 1 := by
      rw [h]; exact gOCandidate_coeff_zero n hn
    rw [if_pos hcoeff, h]
  · -- Case gcd = -gOCandidate
    have hcoeff_eq : ((oddPartitions n).gcd (hOLambda n)).coeff 0 = -1 := by
      rw [h, Polynomial.coeff_neg, gOCandidate_coeff_zero n hn]
    have hne : ((oddPartitions n).gcd (hOLambda n)).coeff 0 ≠ 1 := by
      rw [hcoeff_eq]; decide
    rw [if_neg hne, h, neg_neg]

/-- **Combine the two cyclotomic products over the same index set.** -/

lemma combine_gO_Pn_products (n : ℕ) (hn : 1 ≤ n) :
    (∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e ∧ 1 < e),
        (cyclotomic (2 * e) ℤ) ^ (A n e - n / e)) *
    (∏ d ∈ (Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d),
        (cyclotomic (2 * d) ℤ) ^ (n / d)) =
    ∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e ∧ 1 < e),
        (cyclotomic (2 * e) ℤ) ^ (A n e) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e he ↦ ?_)
  rw [← pow_add]
  congr 1
  have ⟨he_Icc, hodd, he_gt⟩ : e ∈ Finset.Icc 1 n ∧ Odd e ∧ 1 < e := by
    simpa [Finset.mem_filter] using he
  have ⟨he_ge, he_le⟩ := Finset.mem_Icc.mp he_Icc
  have h_le : n / e ≤ A n e := by
    unfold A
    apply Finset.single_le_sum (f := fun i => n / i) (fun i _ => Nat.zero_le _)
    simp [Finset.mem_filter, Finset.mem_Icc, hodd, he_gt, he_le, he_ge]
  omega

lemma prod_cyclotomic_split_one (n : ℕ) (hn : 1 ≤ n) :
    (∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e),
        (cyclotomic (2 * e) ℤ) ^ (A n e)) =
    (cyclotomic 2 ℤ) ^ A n 1 *
    ∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e ∧ 1 < e),
        (cyclotomic (2 * e) ℤ) ^ (A n e) := by
  have h_main : (Finset.Icc 1 n).filter (fun e => Odd e) = {1} ∪ (Finset.Icc 1 n).filter (fun e => Odd e ∧ 1 < e) := by grind
  have h_split_product : (∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e), (cyclotomic (2 * e) ℤ) ^ (A n e)) = (cyclotomic 2 ℤ) ^ A n 1 * ∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e ∧ 1 < e), (cyclotomic (2 * e) ℤ) ^ (A n e) := by grind
  grind

/-- **The product `gO n * Pn n` equals the cyclotomic product form of the LHS.** -/
lemma gO_mul_Pn_eq_prod_cyclotomic (n : ℕ) (hn : 1 ≤ n) :
    gO n * Pn n =
      ∏ e ∈ (Finset.Icc 1 n).filter (fun e => Odd e),
        (cyclotomic (2 * e) ℤ) ^ A n e := by
  rw [gO_eq_prod_cyclotomic n hn]
  unfold Pn
  rw [mul_assoc, combine_gO_Pn_products n hn, prod_cyclotomic_split_one n hn]


lemma closedForm_eq_gO_mul_Pn (n : ℕ) (hn : 1 ≤ n) :
    (∏ i ∈ (Finset.Icc 1 n).filter (fun i => Odd i ∧ 1 < i),
        (1 + (X : Polynomial ℤ) ^ i) ^ (n / i)) = gO n * Pn n := by
  rw [closedForm_eq_prod_cyclotomic n hn,
      gO_mul_Pn_eq_prod_cyclotomic n hn]

/-- **Core helper lemma:** `hOLambda n (allOnesPartition n hn) = gO n * Pn n`. -/
lemma hOLambda_allOnes_eq_gO_mul_Pn (n : ℕ) (hn : 1 ≤ n) :
    hOLambda n (allOnesPartition n hn) = gO n * Pn n := by
  rw [hOLambda_allOnes_closedForm n hn]
  exact closedForm_eq_gO_mul_Pn n hn

/-- **Helper lemma (Step 1+2+3+4 of proof.md):** The quotient `qPart n p₁`
for the all-ones partition equals the explicit cyclotomic product `Pn n`. -/
lemma qPart_allOnes_eq_Pn (n : ℕ) (hn : 1 ≤ n) :
    qPart n (allOnesPartition n hn) = Pn n := by
  -- Use `qPart_spec` to get `hOLambda = gO * qPart`.
  have hdvd : gO n ∣ hOLambda n (allOnesPartition n hn) :=
    gO_dvd_hOLambda n (allOnesPartition n hn)
      (allOnesPartition_mem_oddPartitions n hn)
  have hspec : hOLambda n (allOnesPartition n hn) =
      gO n * qPart n (allOnesPartition n hn) :=
    qPart_spec n (allOnesPartition n hn) hdvd
  -- The core identity:
  have hcore : hOLambda n (allOnesPartition n hn) = gO n * Pn n :=
    hOLambda_allOnes_eq_gO_mul_Pn n hn
  -- Combine: gO n * qPart n p₁ = gO n * Pn n
  have hmul : gO n * qPart n (allOnesPartition n hn) = gO n * Pn n := by
    rw [← hspec, hcore]
  -- Cancel `gO n` (nonzero in the integral domain `ℤ[X]`).
  have hne : gO n ≠ 0 := gO_ne_zero n hn
  exact mul_left_cancel₀ hne hmul

end Conj8Sub_qPart_allOnes_eq_Pn


/- ====== Sub-namespace: Pn_eval_neg_one ====== -/

open Polynomial BigOperators

/-- The odd-prime-power product. -/
noncomputable def Conj8Sub_Pn_eval_neg_one.oddPrimePowerProduct (n : ℕ) : ℕ :=
  ∏ p ∈ (n.factorial).primeFactors.filter (fun p => p ≠ 2),
    p ^ (Nat.factorization n.factorial p)

/-- The candidate cyclotomic product polynomial
`Pn n := ∏_{d ∈ [1,n], d odd, d > 1} Φ_{2d}(X)^{⌊n/d⌋}`. -/
noncomputable def Conj8Sub_Pn_eval_neg_one.Pn (n : ℕ) : Polynomial ℤ :=
  ∏ d ∈ (Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d),
    (cyclotomic (2 * d) ℤ) ^ (n / d)

/-- A proper divisor of an odd number is odd. -/
lemma Conj8Sub_Pn_eval_neg_one.odd_of_dvd_odd {d k : ℕ} (hodd : Odd d) (hk : k ∣ d) : Odd k :=
  hodd.of_dvd_nat hk

/-- The map `k ↦ 2 * k` is injective on `d.divisors` (in fact on all of `ℕ`
when restricted to the positive integers, and certainly on the finset). -/
lemma Conj8Sub_Pn_eval_neg_one.injOn_two_mul_divisors (d : ℕ) :
    Set.InjOn (fun k : ℕ => 2 * k) (d.divisors : Set ℕ) := by
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : (0:ℕ) < 2) hab

/-- For odd `d > 0`, the set of divisors of `2 * d` decomposes as the union
of the divisors of `d` with the image of `d.divisors` under multiplication by `2`. -/
lemma Conj8Sub_Pn_eval_neg_one.divisors_two_mul_eq_union (d : ℕ) (hd : 0 < d) (hodd : Odd d) :
    (2 * d).divisors = d.divisors ∪ d.divisors.image (fun k => 2 * k) := by
  have hd_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  have h2d_ne : 2 * d ≠ 0 := by positivity
  have _huse := hodd
  ext k
  simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
  constructor
  · rintro ⟨hk, _⟩
    rcases Nat.even_or_odd k with hke | hko
    · -- k is even: write k = 2*m
      obtain ⟨m, rfl⟩ := hke
      right
      refine ⟨m, ⟨?_, hd_ne⟩, by ring⟩
      -- m + m = 2 * m divides 2 * d → m ∣ d
      have h2m : 2 * m ∣ 2 * d := by
        have : m + m = 2 * m := by ring
        rw [← this]; exact hk
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0:ℕ) < 2)).mp h2m
    · -- k is odd: k ∣ 2*d and k coprime to 2 → k ∣ d
      left
      refine ⟨?_, hd_ne⟩
      have hcop : Nat.Coprime k 2 := hko.coprime_two_right
      exact hcop.dvd_of_dvd_mul_left hk
  · rintro (⟨hkd, _⟩ | ⟨m, ⟨hmd, _⟩, rfl⟩)
    · exact ⟨hkd.mul_left 2, h2d_ne⟩
    · exact ⟨Nat.mul_dvd_mul_left 2 hmd, h2d_ne⟩

/-- For odd `d`, the divisors of `d` are disjoint from `d.divisors.image (2 * ·)`,
because divisors of `d` are odd while elements of the image are even. -/
lemma Conj8Sub_Pn_eval_neg_one.disjoint_divisors_image_two_mul (d : ℕ) (hd : 0 < d) (hodd : Odd d) :
    Disjoint d.divisors (d.divisors.image (fun k => 2 * k)) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [Finset.mem_image] at hx2
  obtain ⟨y, hy, rfl⟩ := hx2
  have h₁ : y ∣ d := (Nat.mem_divisors.mp hy).1
  have h₂ : 2 * y ∣ d := by simp_all [Nat.mem_divisors]
  rcases Nat.eq_zero_or_pos y with hy0 | hy_pos
  · simp_all [Nat.mem_divisors]
  · have h₁₁ : 2 ∣ d := dvd_trans ⟨y, by ring⟩ h₂
    have h₁₂ : ¬ (2 ∣ d) := by
      cases' hodd with k hk; omega
    exact h₁₂ h₁₁

/-- Splitting divisors of `2 * d` for odd `d`:
`(2 * d).divisors = d.divisors ∪ d.divisors.image (· * 2)` and these are disjoint.
Hence `∏ k ∈ (2*d).divisors, Φ_k(X) = (∏ k ∈ d.divisors, Φ_k(X)) * (∏ k ∈ d.divisors, Φ_{2k}(X))`.
Uses `Nat.divisors_mul`, the fact `(2).divisors = {1,2}`, and `Odd d` to ensure disjointness. -/
lemma Conj8Sub_Pn_eval_neg_one.prod_cyclotomic_two_mul_split (d : ℕ) (hd : 0 < d) (hodd : Odd d) :
    (∏ k ∈ (2 * d).divisors, cyclotomic k ℤ) =
      (∏ k ∈ d.divisors, cyclotomic k ℤ) * (∏ k ∈ d.divisors, cyclotomic (2 * k) ℤ) := by
  rw [divisors_two_mul_eq_union d hd hodd,
      Finset.prod_union (disjoint_divisors_image_two_mul d hd hodd),
      Finset.prod_image (injOn_two_mul_divisors d)]

lemma Conj8Sub_Pn_eval_neg_one.X_pow_two_mul_sub_one_factor (i : ℕ) :
    (Polynomial.X : Polynomial ℤ) ^ (2 * i) - 1 =
      ((Polynomial.X : Polynomial ℤ) ^ i - 1) * ((Polynomial.X : Polynomial ℤ) ^ i + 1) := by
  ring

/-- `X^i - 1 ≠ 0` in `ℤ[X]` for `i ≥ 1`. -/
lemma Conj8Sub_Pn_eval_neg_one.X_pow_sub_one_ne_zero_int (i : ℕ) (hi : 1 ≤ i) :
    (X : Polynomial ℤ) ^ i - 1 ≠ 0 := by
  intro h
  have h₄ : Polynomial.eval 0 ((X : Polynomial ℤ) ^ i - 1) = -1 := by
    simp [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub]
    cases i <;> simp_all [Nat.succ_le_iff]
  rw [h] at h₄
  simp at h₄

/-- For odd `d ≥ 1`, `X^d + 1 = ∏ k ∈ d.divisors, Φ_{2k}(X)` in `ℤ[X]`. -/
lemma Conj8Sub_Pn_eval_neg_one.X_pow_add_one_eq_prod_cyclotomic_two_mul (d : ℕ) (hd : 0 < d) (hodd : Odd d) :
    (X : Polynomial ℤ) ^ d + 1 = ∏ k ∈ d.divisors, cyclotomic (2 * k) ℤ := by
  -- Step 1: `X^(2d) - 1 = ∏_{k | 2d} Φ_k`
  have h2d : 0 < 2 * d := by omega
  have hcyc2d : ∏ k ∈ (2 * d).divisors, cyclotomic k ℤ = (X : Polynomial ℤ) ^ (2 * d) - 1 :=
    prod_cyclotomic_eq_X_pow_sub_one h2d ℤ
  -- Step 2: `X^d - 1 = ∏_{k | d} Φ_k`
  have hcycd : ∏ k ∈ d.divisors, cyclotomic k ℤ = (X : Polynomial ℤ) ^ d - 1 :=
    prod_cyclotomic_eq_X_pow_sub_one hd ℤ
  -- Step 3: split
  have hsplit : (∏ k ∈ (2 * d).divisors, cyclotomic k ℤ) =
      (∏ k ∈ d.divisors, cyclotomic k ℤ) * (∏ k ∈ d.divisors, cyclotomic (2 * k) ℤ) :=
    prod_cyclotomic_two_mul_split d hd hodd
  -- Step 4: difference of squares
  have hfact : (X : Polynomial ℤ) ^ (2 * d) - 1 =
      ((X : Polynomial ℤ) ^ d - 1) * ((X : Polynomial ℤ) ^ d + 1) :=
    X_pow_two_mul_sub_one_factor d
  -- Step 5: combine
  have hne : (X : Polynomial ℤ) ^ d - 1 ≠ 0 := X_pow_sub_one_ne_zero_int d hd
  have hkey : ((X : Polynomial ℤ) ^ d - 1) * ((X : Polynomial ℤ) ^ d + 1) =
      ((X : Polynomial ℤ) ^ d - 1) * (∏ k ∈ d.divisors, cyclotomic (2 * k) ℤ) := by
    rw [← hfact, ← hcyc2d, hsplit, hcycd]
  exact mul_left_cancel₀ hne hkey

/-- For odd `d ≥ 1`, factor out `Φ_2 = X + 1` from the product:
`∏ k ∈ d.divisors, Φ_{2k}(X) = (X + 1) * ∏_{k ∈ d.divisors, k ≠ 1} Φ_{2k}(X)`.
Uses `Polynomial.cyclotomic_two`. -/
lemma Conj8Sub_Pn_eval_neg_one.prod_cyclotomic_two_mul_split_one (d : ℕ) (hd : 0 < d) :
    (∏ k ∈ d.divisors, cyclotomic (2 * k) ℤ) =
      (X + 1) * ∏ k ∈ d.divisors.erase 1, cyclotomic (2 * k) ℤ := by
  have hd_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
  have h1 : (1 : ℕ) ∈ d.divisors := Nat.one_mem_divisors.mpr hd_ne
  -- Apply `Finset.mul_prod_erase` with a = 1, f = (fun k => cyclotomic (2 * k) ℤ)
  have hsplit := Finset.mul_prod_erase d.divisors (fun k => cyclotomic (2 * k) ℤ) h1
  -- hsplit : cyclotomic (2 * 1) ℤ * ∏ k ∈ d.divisors.erase 1, cyclotomic (2 * k) ℤ
  --        = ∏ k ∈ d.divisors, cyclotomic (2 * k) ℤ
  simp only [Nat.mul_one] at hsplit
  rw [← hsplit, Polynomial.cyclotomic_two]

/-- Substituting `-X` into the cyclotomic factorization of `X^d - 1`:
For positive odd `d`, `(X^d - 1).comp(-X) = -X^d - 1` and the LHS equals
`∏ k ∈ d.divisors, (cyclotomic k ℤ).comp(-X)`. So
`∏ k ∈ d.divisors, (cyclotomic k ℤ).comp(-X) = -(X^d + 1)` in `ℤ[X]`. -/
lemma Conj8Sub_Pn_eval_neg_one.prod_cyclotomic_comp_neg_X_eq_neg
    (d : ℕ) (hd : 0 < d) (hodd : Odd d) :
    ∏ k ∈ d.divisors, (cyclotomic k ℤ).comp (-X) = -((X : Polynomial ℤ) ^ d + 1) := by
  -- Start from prod_cyclotomic_eq_X_pow_sub_one: ∏ k ∈ d.divisors, cyclotomic k ℤ = X^d - 1
  have h1 : ∏ k ∈ d.divisors, cyclotomic k ℤ = X ^ d - 1 :=
    Polynomial.prod_cyclotomic_eq_X_pow_sub_one hd ℤ
  -- Apply comp (-X) to both sides
  have h2 : (∏ k ∈ d.divisors, cyclotomic k ℤ).comp (-X) =
      ((X : Polynomial ℤ) ^ d - 1).comp (-X) := by
    rw [h1]
  -- LHS distributes over the product
  have h3 : (∏ k ∈ d.divisors, cyclotomic k ℤ).comp (-X) =
      ∏ k ∈ d.divisors, (cyclotomic k ℤ).comp (-X) := by
    rw [Polynomial.prod_comp]
  -- Compute RHS: (X^d - 1).comp (-X) = (-X)^d - 1 = -X^d - 1 = -(X^d + 1)
  have h4 : ((X : Polynomial ℤ) ^ d - 1).comp (-X) = -(X ^ d + 1) := by
    rw [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.one_comp, Polynomial.X_comp]
    rw [hodd.neg_pow]
    ring
  rw [h3] at h2
  rw [h2, h4]

/-- Split off the divisor `1` from the cyclotomic product. -/
lemma Conj8Sub_Pn_eval_neg_one.split_prod_cyclotomic_comp
    (d : ℕ) (hd : 0 < d) :
    ∏ k ∈ d.divisors, (cyclotomic k ℤ).comp (-X) =
      (cyclotomic 1 ℤ).comp (-X) *
        ∏ k ∈ d.divisors.erase 1, (cyclotomic k ℤ).comp (-X) := by
  have h₁ : 1 ∈ d.divisors :=
    Nat.mem_divisors.mpr ⟨one_dvd _, hd.ne'⟩
  exact (Finset.mul_prod_erase _ _ h₁).symm

lemma Conj8Sub_Pn_eval_neg_one.cyclotomic_one_comp_neg_X :
    (Polynomial.cyclotomic 1 ℤ).comp (-X) = -((X : Polynomial ℤ) + 1) := by
  simp only [cyclotomic_one, sub_comp, X_comp, one_comp]
  ring

/-- For odd `d ≥ 1`,
`(X^d + 1) = (X + 1) * ∏_{k ∈ d.divisors, k ≠ 1} (cyclotomic k ℤ).comp(-X)`.
This is derived by substituting `-X` into `∏_{k | d} Φ_k(X) = X^d - 1`, using
that `d` is odd so `(-X)^d = -X^d`, and pulling out `Φ_1(-X) = -X - 1 = -(X+1)`. -/
lemma Conj8Sub_Pn_eval_neg_one.X_pow_add_one_eq_prod_cyclotomic_comp (d : ℕ) (hd : 0 < d) (hodd : Odd d) :
    (X : Polynomial ℤ) ^ d + 1 =
      (X + 1) * ∏ k ∈ d.divisors.erase 1, (cyclotomic k ℤ).comp (-X) := by
  -- Set P := ∏ k ∈ d.divisors.erase 1, (cyclotomic k ℤ).comp (-X)
  -- From prod_cyclotomic_comp_neg_X_eq_neg:
  --   ∏ k ∈ d.divisors, (cyclotomic k ℤ).comp (-X) = -(X^d + 1)
  -- From split_prod_cyclotomic_comp:
  --   ∏ k ∈ d.divisors, (cyclotomic k ℤ).comp (-X) = (cyclotomic 1 ℤ).comp(-X) * P
  -- From cyclotomic_one_comp_neg_X: (cyclotomic 1 ℤ).comp(-X) = -(X+1)
  -- So -(X+1) * P = -(X^d + 1), hence (X+1) * P = X^d + 1.
  have h1 := prod_cyclotomic_comp_neg_X_eq_neg d hd hodd
  have h2 := split_prod_cyclotomic_comp d hd
  have h3 := cyclotomic_one_comp_neg_X
  set P : Polynomial ℤ := ∏ k ∈ d.divisors.erase 1, (cyclotomic k ℤ).comp (-X) with hP
  -- h1: ∏ k ∈ d.divisors, (cyclotomic k ℤ).comp (-X) = -(X^d + 1)
  -- h2: ∏ ... = (cyclotomic 1 ℤ).comp(-X) * P
  rw [h2, h3] at h1
  -- h1: -(X+1) * P = -(X^d + 1)
  -- Goal: X^d + 1 = (X+1) * P
  linear_combination h1

/-- `X + 1 ≠ 0` in `ℤ[X]`. Used to cancel this factor. -/
lemma Conj8Sub_Pn_eval_neg_one.X_add_one_ne_zero : (X + 1 : Polynomial ℤ) ≠ 0 := by
  have : (X + Polynomial.C (1 : ℤ)).natDegree = 1 := Polynomial.natDegree_X_add_C 1
  intro h
  have h0 : ((X : Polynomial ℤ) + 1).natDegree = 0 := by rw [h]; simp
  simp at this
  omega

/-- Combining the two factorizations, for odd `d ≥ 1`:
`∏_{k ∈ d.divisors, k ≠ 1} Φ_{2k}(X) = ∏_{k ∈ d.divisors, k ≠ 1} Φ_k(-X)`.
Follows from `X_pow_add_one_eq_prod_cyclotomic_two_mul`,
`prod_cyclotomic_two_mul_split_one`, `X_pow_add_one_eq_prod_cyclotomic_comp`,
and cancelling the nonzero factor `X + 1` in the integral domain `ℤ[X]`. -/
lemma Conj8Sub_Pn_eval_neg_one.prod_cyclotomic_eq_prod_comp (d : ℕ) (hd : 0 < d) (hodd : Odd d) :
    (∏ k ∈ d.divisors.erase 1, cyclotomic (2 * k) ℤ) =
      ∏ k ∈ d.divisors.erase 1, (cyclotomic k ℤ).comp (-X) := by
  -- From X_pow_add_one_eq_prod_cyclotomic_two_mul and prod_cyclotomic_two_mul_split_one:
  have h1 : (X : Polynomial ℤ) ^ d + 1 =
      (X + 1) * ∏ k ∈ d.divisors.erase 1, cyclotomic (2 * k) ℤ := by
    rw [X_pow_add_one_eq_prod_cyclotomic_two_mul d hd hodd]
    exact prod_cyclotomic_two_mul_split_one d hd
  -- From X_pow_add_one_eq_prod_cyclotomic_comp:
  have h2 : (X : Polynomial ℤ) ^ d + 1 =
      (X + 1) * ∏ k ∈ d.divisors.erase 1, (cyclotomic k ℤ).comp (-X) :=
    X_pow_add_one_eq_prod_cyclotomic_comp d hd hodd
  -- Combine: both equal X^d + 1.
  have h3 : (X + 1) * ∏ k ∈ d.divisors.erase 1, cyclotomic (2 * k) ℤ =
            (X + 1) * ∏ k ∈ d.divisors.erase 1, (cyclotomic k ℤ).comp (-X) := by
    rw [← h1, h2]
  exact mul_left_cancel₀ X_add_one_ne_zero h3

lemma Conj8Sub_Pn_eval_neg_one.comp_neg_X_cyclotomic_ne_zero (n : ℕ) :
    (cyclotomic n ℤ).comp (-X : Polynomial ℤ) ≠ 0 := by
  have h₁ : (cyclotomic n ℤ : Polynomial ℤ) ≠ 0 := by
    apply Polynomial.cyclotomic_ne_zero
  have h₂ : (Polynomial.degree (-X : Polynomial ℤ) : WithBot ℕ) = 1 := by
    simp [Polynomial.degree_neg, Polynomial.degree_X]
  have h₃ : Polynomial.degree ((cyclotomic n ℤ).comp (-X : Polynomial ℤ)) = Polynomial.degree (cyclotomic n ℤ) * 1 := by
    rw [Polynomial.degree_comp]
    <;> simp_all [h₂]
  have h₄ : Polynomial.degree ((cyclotomic n ℤ).comp (-X : Polynomial ℤ)) = Polynomial.degree (cyclotomic n ℤ) := by
    rw [h₃]
    <;> simp [mul_one]
  have h₅ : Polynomial.degree (cyclotomic n ℤ) ≠ ⊥ := by
    have h₅₁ : (cyclotomic n ℤ : Polynomial ℤ) ≠ 0 := by
      apply Polynomial.cyclotomic_ne_zero
    exact by
      contrapose! h₅₁
      simp_all [Polynomial.degree_eq_bot]
  have h₆ : (cyclotomic n ℤ).comp (-X : Polynomial ℤ) ≠ 0 := by
    intro h₆₁
    have h₆₂ : Polynomial.degree ((cyclotomic n ℤ).comp (-X : Polynomial ℤ)) = ⊥ := by
      rw [h₆₁]
      simp [Polynomial.degree_zero]
    have h₆₃ : Polynomial.degree ((cyclotomic n ℤ).comp (-X : Polynomial ℤ)) = Polynomial.degree (cyclotomic n ℤ) := by
      rw [h₄]
    rw [h₆₃] at h₆₂
    simp_all [Polynomial.degree_eq_bot]
  exact h₆

/-- For odd `d > 1`, `cyclotomic (2 * d) ℤ = (cyclotomic d ℤ).comp (-X)`. -/
lemma Conj8Sub_Pn_eval_neg_one.cyclotomic_two_mul_eq_comp_neg_X
    (d : ℕ) (hd : 1 < d) (hodd : Odd d) :
    (cyclotomic (2 * d) ℤ) = (cyclotomic d ℤ).comp (-X) := by
  -- Generalize to a single statement and apply strong induction.
  suffices H : ∀ d : ℕ, 1 < d → Odd d →
      (cyclotomic (2 * d) ℤ) = (cyclotomic d ℤ).comp (-X) from H d hd hodd
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd hodd
    have hd0 : 0 < d := lt_trans Nat.zero_lt_one hd
    have key := prod_cyclotomic_eq_prod_comp d hd0 hodd
    -- Both products are over d.divisors.erase 1. Isolate the k = d factor.
    have hmem : d ∈ d.divisors.erase 1 := by
      rw [Finset.mem_erase, Nat.mem_divisors]
      refine ⟨?_, dvd_refl d, hd0.ne'⟩
      exact (Nat.one_lt_iff_ne_zero_and_ne_one.mp hd).2
    -- Split off d on both sides
    rw [← Finset.prod_erase_mul _ _ hmem, ← Finset.prod_erase_mul _ _ hmem] at key
    -- Apply IH on the remaining factors (proper divisors > 1 of d)
    have h_eq_inner :
        (∏ k ∈ (d.divisors.erase 1).erase d, cyclotomic (2 * k) ℤ) =
        (∏ k ∈ (d.divisors.erase 1).erase d, (cyclotomic k ℤ).comp (-X)) := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [Finset.mem_erase, Finset.mem_erase, Nat.mem_divisors] at hk
      obtain ⟨hkd, hk1, hkdvd, _⟩ := hk
      have hk_lt : k < d := by
        apply Nat.lt_of_le_of_ne _ hkd
        exact Nat.le_of_dvd hd0 hkdvd
      have hk_odd : Odd k := odd_of_dvd_odd hodd hkdvd
      have hk_pos : 0 < k := Nat.pos_of_ne_zero (by
        intro hk0
        rw [hk0] at hkdvd
        exact hd0.ne' (Nat.eq_zero_of_zero_dvd hkdvd))
      have hk_gt : 1 < k := lt_of_le_of_ne hk_pos (Ne.symm hk1)
      exact ih k hk_lt hk_gt hk_odd
    -- Cancel the inner product (which is nonzero)
    rw [h_eq_inner] at key
    have hne : (∏ k ∈ (d.divisors.erase 1).erase d, (cyclotomic k ℤ).comp (-X)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k _
      exact comp_neg_X_cyclotomic_ne_zero k
    -- Cancel from both sides
    exact mul_left_cancel₀ hne key

/-- For odd `d ≥ 1`, `Φ_{2d}(-1) = Φ_d(1)` in `ℤ`. -/
lemma Conj8Sub_Pn_eval_neg_one.cyclotomic_two_mul_eval_neg_one
    (d : ℕ) (hd : 1 ≤ d) (hodd : Odd d) :
    ((cyclotomic (2 * d) ℤ).eval (-1 : ℤ)) = (cyclotomic d ℤ).eval (1 : ℤ) := by
  rcases eq_or_lt_of_le hd with hd1 | hd1
  · -- d = 1
    subst hd1
    simp [cyclotomic_one, cyclotomic_two, show (2 : ℕ) * 1 = 2 from rfl]
  · -- d > 1
    have hid : cyclotomic (2 * d) ℤ = (cyclotomic d ℤ).comp (-X) :=
      cyclotomic_two_mul_eq_comp_neg_X d hd1 hodd
    rw [hid]
    simp [eval_comp, eval_neg]

/-- **Step 1 product form:** After distributing `eval (-1)` through the product
defining `Pn n` and applying the substitution identity from
`cyclotomic_two_mul_eval_neg_one`, we obtain that `(Pn n).eval (-1)` equals
`∏_{d ∈ [1,n], d odd, 1 < d} (Φ_d(1))^{⌊n/d⌋}` in `ℤ`. -/
lemma Conj8Sub_Pn_eval_neg_one.Pn_eval_neg_one_eq_prod_cyclotomic_one (n : ℕ) :
    (Pn n).eval (-1 : ℤ) =
      ∏ d ∈ (Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d),
        ((cyclotomic d ℤ).eval (1 : ℤ)) ^ (n / d) := by
  unfold Pn
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro d hd
  rw [Polynomial.eval_pow]
  congr 1
  rw [Finset.mem_filter, Finset.mem_Icc] at hd
  obtain ⟨⟨hd1, _⟩, hodd, _⟩ := hd
  exact cyclotomic_two_mul_eval_neg_one d hd1 hodd

/-- For `1 < d` that is not a prime power, `Φ_d(1) = 1`, so any power thereof is `1`. -/
lemma Conj8Sub_Pn_eval_neg_one.eval_one_cyclotomic_pow_eq_one_of_not_prime_pow
    (d n : ℕ) (h1 : 1 < d) (hd : ¬ IsPrimePow d) :
    ((cyclotomic d ℤ).eval (1 : ℤ)) ^ (n / d) = 1 := by
  have heval : (cyclotomic d ℤ).eval (1 : ℤ) = 1 := by
    apply Polynomial.eval_one_cyclotomic_not_prime_pow
    intro p hp k hpk
    -- If `p ^ k = d`, then either `k = 0` (giving `1 = d`, contradicting `1 < d`)
    -- or `k ≥ 1`, making `d` a prime power.
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp at hpk
      omega
    · exact hd ⟨p, k, hp.prime, hk, hpk⟩
  rw [heval, one_pow]

/-- **Step 2.3:** The product over odd `d ∈ (1, n]` of `Φ_d(1)^(n/d)`
equals the product over odd prime powers `d ∈ (1, n]` of the same quantity.
This is because non-prime-powers contribute `1` (by
`eval_one_cyclotomic_pow_eq_one_of_not_prime_pow`). -/
lemma Conj8Sub_Pn_eval_neg_one.prod_eq_prod_filter_isPrimePow (n : ℕ) :
    (∏ d ∈ (Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d),
        ((cyclotomic d ℤ).eval (1 : ℤ)) ^ (n / d))
      = ∏ d ∈ (Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d ∧ IsPrimePow d),
        ((cyclotomic d ℤ).eval (1 : ℤ)) ^ (n / d) := by
  classical
  -- Split the filtered product by the additional predicate `IsPrimePow d`.
  -- The product over `¬IsPrimePow` reduces to 1.
  have hsplit :
      (∏ d ∈ (Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d),
          ((cyclotomic d ℤ).eval (1 : ℤ)) ^ (n / d))
        = (∏ d ∈ ((Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d)).filter
              (fun d => IsPrimePow d),
            ((cyclotomic d ℤ).eval (1 : ℤ)) ^ (n / d))
          * (∏ d ∈ ((Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d)).filter
              (fun d => ¬ IsPrimePow d),
            ((cyclotomic d ℤ).eval (1 : ℤ)) ^ (n / d)) := by
    exact (Finset.prod_filter_mul_prod_filter_not _ (fun d => IsPrimePow d) _).symm
  -- Show the non-prime-power product equals 1.
  have hone :
      (∏ d ∈ ((Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d)).filter
          (fun d => ¬ IsPrimePow d),
        ((cyclotomic d ℤ).eval (1 : ℤ)) ^ (n / d)) = 1 := by
    apply Finset.prod_eq_one
    intro d hd
    rw [Finset.mem_filter, Finset.mem_filter] at hd
    obtain ⟨⟨_, _, h1d⟩, hnpp⟩ := hd
    exact eval_one_cyclotomic_pow_eq_one_of_not_prime_pow d n h1d hnpp
  -- Re-identify the IsPrimePow-filtered set with the RHS index set.
  have hset :
      ((Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d)).filter (fun d => IsPrimePow d)
        = (Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d ∧ IsPrimePow d) := by
    ext d
    simp [Finset.mem_filter, and_assoc]
  rw [hsplit, hone, mul_one, hset]

/-- For an odd prime power `d` in `[1,n]` with `d > 1`, the evaluation
`Φ_d(1)` (in `ℤ`) equals `d.minFac` (the base prime of `d`).
This uses `Polynomial.eval_one_cyclotomic_prime_pow` and
`IsPrimePow.minFac_pow_factorization_eq`. -/
lemma Conj8Sub_Pn_eval_neg_one.eval_one_cyclotomic_of_isPrimePow (d : ℕ) (hd : 1 < d) (hpp : IsPrimePow d) :
    (cyclotomic d ℤ).eval (1 : ℤ) = (d.minFac : ℤ) := by
  have hd1 : d ≠ 1 := Nat.ne_of_gt hd
  have hp : Nat.Prime d.minFac := Nat.minFac_prime hd1
  haveI : Fact (Nat.Prime d.minFac) := ⟨hp⟩
  have hfac : d.minFac ^ d.factorization d.minFac = d :=
    IsPrimePow.minFac_pow_factorization_eq hpp
  have hk_pos : 0 < d.factorization d.minFac := by
    by_contra h
    push_neg at h
    interval_cases (d.factorization d.minFac)
    simp at hfac
    omega
  set k := d.factorization d.minFac with _
  obtain ⟨e, he⟩ : ∃ e, k = e + 1 := ⟨k - 1, by omega⟩
  have hd_eq : d = d.minFac ^ (e + 1) := by rw [← he]; exact hfac.symm
  conv_lhs => rw [hd_eq]
  exact Polynomial.eval_one_cyclotomic_prime_pow (R := ℤ) (p := d.minFac) e

/-- The function `d ↦ d.minFac` maps an odd prime power `d ∈ [1,n]` with `1 < d`
into the set of odd primes `p ∈ [2,n]`. -/
lemma Conj8Sub_Pn_eval_neg_one.minFac_maps_to (n : ℕ) :
    ∀ d ∈ (Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d ∧ IsPrimePow d),
      d.minFac ∈ (Finset.Icc 2 n).filter (fun p => Nat.Prime p ∧ Odd p) := by
  intro d hd
  simp only [Finset.mem_filter, Finset.mem_Icc] at hd ⊢
  obtain ⟨⟨_, hdn⟩, hodd, hd1, _⟩ := hd
  have hd_ne_one : d ≠ 1 := Nat.ne_of_gt hd1
  have hd_pos : 0 < d := by linarith
  have hprime : Nat.Prime d.minFac := Nat.minFac_prime hd_ne_one
  have h2le : 2 ≤ d.minFac := hprime.two_le
  have hmf_le_d : d.minFac ≤ d := Nat.minFac_le hd_pos
  have hmf_le_n : d.minFac ≤ n := le_trans hmf_le_d hdn
  refine ⟨⟨h2le, hmf_le_n⟩, hprime, ?_⟩
  rcases hprime.eq_two_or_odd' with heq | hoddmf
  · exfalso
    have hdvd : d.minFac ∣ d := Nat.minFac_dvd d
    rw [heq] at hdvd
    have hev : Even d := by
      rcases hdvd with ⟨k, hk⟩
      exact ⟨k, by linarith [hk]⟩
    exact (Nat.not_even_iff_odd.mpr hodd) hev
  · exact hoddmf

/-- Forward direction helper for `fiber_eq_powers`. -/
private lemma Conj8Sub_Pn_eval_neg_one.fiber_eq_powers_forward (n p : ℕ) (hp : p.Prime) (d : ℕ)
    (hd_mem : d ∈ Finset.Icc 1 n)
    (hodd : Odd d) (h1d : 1 < d) (hpp : IsPrimePow d) (hmin : d.minFac = p) :
    ∃ k ∈ Finset.Icc 1 (Nat.log p n), p ^ k = d := by
  have h_d_le_n : d ≤ n := by
    grind
  have h_p_ge_two : 2 ≤ p := by
    grind only [Nat.prime_def_minFac]
  have h_p_pow : p ^ d.factorization p = d := by
    grind only [= Nat.odd_iff, isPrimePow_iff_minFac_pow_factorization_eq]
  have h_k_pos : 1 ≤ d.factorization p := by
    grind only [Nat.factorization_minFac_ne_zero]
  have h_pow_le_n : p ^ d.factorization p ≤ n := by
    grind
  have h_k_le_log : d.factorization p ≤ Nat.log p n :=
    Nat.le_log_of_pow_le h_p_ge_two h_pow_le_n
  have h_main : ∃ k ∈ Finset.Icc 1 (Nat.log p n), p ^ k = d := by
    grind
  exact h_main

/-- Backward direction helper for `fiber_eq_powers`. -/
private lemma Conj8Sub_Pn_eval_neg_one.fiber_eq_powers_backward (n p : ℕ) (hp : p.Prime) (hodd : Odd p) (hpn : p ≤ n)
    (k : ℕ) (hk : k ∈ Finset.Icc 1 (Nat.log p n)) :
    p ^ k ∈ Finset.Icc 1 n ∧ Odd (p ^ k) ∧ 1 < p ^ k ∧ IsPrimePow (p ^ k) ∧
      (p ^ k).minFac = p := by
  rcases Finset.mem_Icc.mp hk with ⟨hk1, hk2⟩
  have hp_pos : 0 < p := hp.pos
  have hp_one_lt : 1 < p := hp.one_lt
  have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk1
  have hn_pos : 0 < n := lt_of_lt_of_le hp_pos hpn
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn_pos
  have h_one_le_pow : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp_pos
  have h_pow_le : p ^ k ≤ n := (Nat.le_log_iff_pow_le hp_one_lt hn_ne).mp hk2
  refine ⟨Finset.mem_Icc.mpr ⟨h_one_le_pow, h_pow_le⟩, ?_, ?_, ?_, ?_⟩
  · exact hodd.pow
  · exact Nat.one_lt_pow hk_ne hp_one_lt
  · exact hp.isPrimePow.pow hk_ne
  · exact hp.pow_minFac hk_ne

/-- For each odd prime `p ∈ [2,n]`, the set of `d ∈ [1,n]` with
`Odd d ∧ 1 < d ∧ IsPrimePow d ∧ d.minFac = p` is exactly
`{p^k : 1 ≤ k, p^k ≤ n}`.
This characterizes the fiber of the `minFac` map. -/
lemma Conj8Sub_Pn_eval_neg_one.fiber_eq_powers (n p : ℕ) (hp : p.Prime) (hodd : Odd p) (hpn : p ≤ n) :
    ((Finset.Icc 1 n).filter
        (fun d => Odd d ∧ 1 < d ∧ IsPrimePow d ∧ d.minFac = p))
      = ((Finset.Icc 1 (Nat.log p n)).image (fun k => p ^ k)) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hd_mem, hodd_d, h1d, hpp, hmin⟩
    obtain ⟨k, hk, hkd⟩ := fiber_eq_powers_forward n p hp d hd_mem hodd_d h1d hpp hmin
    exact ⟨k, hk, hkd⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := fiber_eq_powers_backward n p hp hodd hpn k hk
    exact ⟨h1, h2, h3, h4, h5⟩

/-- For each odd prime `p ≤ n`, the sum `∑_{k ∈ [1, log_p n]} n / p^k`
equals `Nat.factorization n.factorial p`.
Uses Legendre's formula. -/
lemma Conj8Sub_Pn_eval_neg_one.sum_div_pow_eq_factorization (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
    (∑ k ∈ Finset.Icc 1 (Nat.log p n), n / p ^ k)
      = Nat.factorization n.factorial p := by
  have hpFact : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp]
  have h : padicValNat p n.factorial = ∑ i ∈ Finset.Ico 1 (Nat.log p n + 1), n / p ^ i :=
    padicValNat_factorial (Nat.lt_succ_self _)
  rw [h]
  rw [show (Nat.log p n + 1) = Order.succ (Nat.log p n) from rfl,
      Finset.Ico_succ_right_eq_Icc]

/-- For each odd prime `p ≤ n`, the product of `(d.minFac : ℤ)^(n/d)` over
the fiber `{d : d.minFac = p}` of odd prime powers in `[1,n]` equals
`(p : ℤ)^(Nat.factorization n.factorial p)`. This is the fiber computation
used inside the fiberwise rewrite. -/
lemma Conj8Sub_Pn_eval_neg_one.prod_over_fiber_eq (n p : ℕ) (hp : p.Prime) (hodd : Odd p) (hpn : p ≤ n) :
    (∏ d ∈ ((Finset.Icc 1 n).filter
              (fun d => Odd d ∧ 1 < d ∧ IsPrimePow d ∧ d.minFac = p)),
        (d.minFac : ℤ) ^ (n / d))
      = (p : ℤ) ^ (Nat.factorization n.factorial p) := by
  rw [fiber_eq_powers n p hp hodd hpn]
  have hinj : Set.InjOn (fun k : ℕ => p ^ k)
      ((Finset.Icc 1 (Nat.log p n) : Finset ℕ) : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.pow_right_injective hp.two_le hab
  rw [Finset.prod_image (fun a ha b hb h => hinj ha hb h)]
  have hrewrite :
      (∏ k ∈ Finset.Icc 1 (Nat.log p n),
          ((p ^ k).minFac : ℤ) ^ (n / p ^ k))
        = ∏ k ∈ Finset.Icc 1 (Nat.log p n),
            (p : ℤ) ^ (n / p ^ k) := by
    refine Finset.prod_congr rfl ?_
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk_ne : k ≠ 0 := Nat.one_le_iff_ne_zero.mp hk1
    rw [hp.pow_minFac hk_ne]
  rw [hrewrite, Finset.prod_pow_eq_pow_sum, sum_div_pow_eq_factorization n p hp hpn]

/-- The product over odd prime powers `d ∈ (1, n]` of `(Φ_d(1))^(n/d)`,
after rewriting `Φ_d(1) = d.minFac`, equals the product over odd primes
`p ∈ [2, n]` of `p^(factorization n! p)`. This is the main combinatorial
step assembling the fiberwise decomposition. -/
lemma Conj8Sub_Pn_eval_neg_one.prod_minFac_eq_prod_primes (n : ℕ) :
    (∏ d ∈ (Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d ∧ IsPrimePow d),
        ((d.minFac : ℤ)) ^ (n / d))
      = ∏ p ∈ (Finset.Icc 2 n).filter (fun p => Nat.Prime p ∧ Odd p),
          (p : ℤ) ^ (Nat.factorization n.factorial p) := by
  rw [← Finset.prod_fiberwise_of_maps_to (minFac_maps_to n)
        (fun d => (d.minFac : ℤ) ^ (n / d))]
  refine Finset.prod_congr rfl ?_
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨_, hpn⟩, hpprime, hpodd⟩ := hp
  have hfilter : ((Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d ∧ IsPrimePow d)).filter
                    (fun d => d.minFac = p)
              = (Finset.Icc 1 n).filter
                  (fun d => Odd d ∧ 1 < d ∧ IsPrimePow d ∧ d.minFac = p) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    tauto
  rw [hfilter]
  exact prod_over_fiber_eq n p hpprime hpodd hpn

/-- **Main Lemma.** The product over odd prime powers `d ∈ (1, n]` of
`(Φ_d(1))^(n/d)` equals the product over odd primes `p ∈ [2, n]` of
`p^(factorization n! p)`. -/
lemma Conj8Sub_Pn_eval_neg_one.prod_prime_powers_eq_prod_primes (n : ℕ) :
    (∏ d ∈ (Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d ∧ IsPrimePow d),
        ((cyclotomic d ℤ).eval (1 : ℤ)) ^ (n / d))
      = ∏ p ∈ (Finset.Icc 2 n).filter (fun p => Nat.Prime p ∧ Odd p),
          (p : ℤ) ^ (Nat.factorization n.factorial p) := by
  -- Step 1: rewrite Φ_d(1) = d.minFac on each factor of the LHS.
  have hLHS :
      (∏ d ∈ (Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d ∧ IsPrimePow d),
          ((cyclotomic d ℤ).eval (1 : ℤ)) ^ (n / d))
        = ∏ d ∈ (Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d ∧ IsPrimePow d),
            ((d.minFac : ℤ)) ^ (n / d) := by
    refine Finset.prod_congr rfl ?_
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨_, _, hdgt, hdpp⟩
    rw [eval_one_cyclotomic_of_isPrimePow d hdgt hdpp]
  rw [hLHS]
  -- Step 2: fiberwise rewrite using minFac as the fiber map.
  exact prod_minFac_eq_prod_primes n

/-- **Step 7:** The index set `{p ∈ [2, n] : p prime ∧ p odd}` equals
`(n!).primeFactors.filter (· ≠ 2)`. This uses
`Nat.Prime.dvd_factorial : ∀ {n p : ℕ}, Nat.Prime p → (p ∣ n.factorial ↔ p ≤ n)`
together with the characterization `Nat.mem_primeFactors`. -/
lemma Conj8Sub_Pn_eval_neg_one.prime_index_set_eq (n : ℕ) (hn : 1 ≤ n) :
    (Finset.Icc 2 n).filter (fun p => Nat.Prime p ∧ Odd p)
      = (n.factorial).primeFactors.filter (fun p => p ≠ 2) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨_, hpn⟩, hp, hodd⟩
    refine ⟨⟨hp, hp.dvd_factorial.mpr hpn, Nat.factorial_pos n |>.ne'⟩, ?_⟩
    intro heq
    rw [heq] at hodd
    exact (by decide : ¬ Odd 2) hodd
  · rintro ⟨⟨hp, hdvd, _⟩, hne⟩
    refine ⟨⟨hp.two_le, hp.dvd_factorial.mp hdvd⟩, hp, ?_⟩
    exact hp.odd_of_ne_two hne

lemma Conj8Sub_Pn_eval_neg_one.cast_oddPrimePowerProduct (n : ℕ) :
    (oddPrimePowerProduct n : ℤ)
      = ∏ p ∈ (n.factorial).primeFactors.filter (fun p => p ≠ 2),
          (p : ℤ) ^ (Nat.factorization n.factorial p) := by
  unfold oddPrimePowerProduct
  push_cast
  rfl

/-- **Cyclotomic-at-1 evaluates to `p` on prime-power indices, `1` otherwise.**
The product `∏_{d ∈ [1,n], d odd, 1 < d} (Φ_d(1))^{⌊n/d⌋}` (in `ℤ`)
equals `(oddPrimePowerProduct n : ℤ)`. -/
lemma Conj8Sub_Pn_eval_neg_one.prod_cyclotomic_one_eq_oddPrimePowerProduct (n : ℕ) (hn : 1 ≤ n) :
    (∏ d ∈ (Finset.Icc 1 n).filter (fun d => Odd d ∧ 1 < d),
        ((cyclotomic d ℤ).eval (1 : ℤ)) ^ (n / d))
      = (oddPrimePowerProduct n : ℤ) := by
  rw [prod_eq_prod_filter_isPrimePow n, prod_prime_powers_eq_prod_primes n,
      prime_index_set_eq n hn, cast_oddPrimePowerProduct n]

/-- **Helper lemma (Step 5 of proof.md):** The polynomial `Pn n` evaluated
at `-1` equals the odd-prime-power product of `n!`. -/
lemma Conj8Sub_Pn_eval_neg_one.Pn_eval_neg_one (n : ℕ) (hn : 1 ≤ n) :
    (Pn n).eval (-1 : ℤ) = (oddPrimePowerProduct n : ℤ) := by
  rw [Pn_eval_neg_one_eq_prod_cyclotomic_one n]
  exact prod_cyclotomic_one_eq_oddPrimePowerProduct n hn

namespace Conj8

lemma qPart_allOnes_eq_Pn (n : ℕ) (hn : 1 ≤ n) :
    qPart n (allOnesPartition n hn) = Pn n :=
  Conj8Sub_qPart_allOnes_eq_Pn.qPart_allOnes_eq_Pn n hn

lemma Pn_eval_neg_one (n : ℕ) (hn : 1 ≤ n) :
    (Pn n).eval (-1 : ℤ) = (oddPrimePowerProduct n : ℤ) :=
  Conj8Sub_Pn_eval_neg_one.Pn_eval_neg_one n hn

/-- **For the all-ones partition `p₁`, the quotient `qPart n p₁` evaluates to
the odd-prime-power product at `-1`.** -/
lemma qPart_allOnes_eval_neg_one (n : ℕ) (hn : 1 ≤ n) :
    (qPart n (allOnesPartition n hn)).eval (-1 : ℤ) =
      (oddPrimePowerProduct n : ℤ) := by
  rw [qPart_allOnes_eq_Pn n hn]
  exact Pn_eval_neg_one n hn

/-- **The evaluation of `numO n` at `-1` equals the odd-prime-power product.** -/
lemma numO_eval_neg_one_eq_oddPrimePowerProduct (n : ℕ) (hn : 1 ≤ n) :
    (numO n).eval (-1 : ℤ) = (oddPrimePowerProduct n : ℤ) := by
  classical
  rw [numO_eq_sum_qPart n hn, Polynomial.eval_finset_sum]
  -- Split off the `allOnesPartition` term and show the rest vanishes.
  have hmem : allOnesPartition n hn ∈ oddPartitions n :=
    allOnesPartition_mem_oddPartitions n hn
  rw [Finset.sum_eq_single (allOnesPartition n hn)
    (fun p hp hne => qPart_eval_neg_one_of_ne_allOnes n hn p hp hne)
    (fun h => (h hmem).elim)]
  exact qPart_allOnes_eval_neg_one n hn

/-- The largest odd divisor of `m`: $o(m) = m / 2^{\nu_2(m)}$. -/
def largestOddDivisor (m : ℕ) : ℕ := m / 2 ^ (Nat.factorization m 2)

lemma oddPrimePowerProduct_eq_largestOddDivisor (n : ℕ) (hn : 1 ≤ n) :
    oddPrimePowerProduct n = largestOddDivisor n.factorial := by
  have hfact := factorial_eq_two_pow_mul_oddPrimePowerProduct n hn
  have h2pos : 0 < (2 : ℕ) ^ (Nat.factorization n.factorial 2) :=
    Nat.pos_of_ne_zero (by positivity)
  show oddPrimePowerProduct n
      = n.factorial / 2 ^ (Nat.factorization n.factorial 2)
  nth_rewrite 1 [hfact]
  exact (Nat.mul_div_cancel_left _ h2pos).symm

theorem conj8 (n : ℕ) (hn : 1 ≤ n) :
    (numO n).eval (-1 : ℤ) = (largestOddDivisor n.factorial : ℤ) := by
  rw [numO_eval_neg_one_eq_oddPrimePowerProduct n hn]
  exact_mod_cast oddPrimePowerProduct_eq_largestOddDivisor n hn

end Conj8
