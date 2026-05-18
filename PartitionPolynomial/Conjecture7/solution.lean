import Mathlib

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

/-- The polynomial `h_{B,λ}^{(n)}(x) := ∏_{k ≥ 0} (1 + x^{2^k})^{⌊n/2^k⌋ − m_λ(2^k)}`. -/
noncomputable def hBPoly (n : ℕ) (p : Nat.Partition n) : Polynomial ℤ :=
  ∏ k ∈ Finset.range (n + 1),
    (1 + X ^ (2 ^ k)) ^ (n / 2 ^ k - p.parts.count (2 ^ k))

/-- The binary numerator polynomial
`num_B(n, x) := ∑_{λ ∈ B(n)} h_{B,λ}^{(n)}(x)`. -/
noncomputable def numB (n : ℕ) : Polynomial ℤ :=
  ∑ p ∈ binaryPartitions n, hBPoly n p

/-- The phase generator `ω := exp(π * I / 2^(s+1))`. -/
noncomputable def omega (s : ℕ) : ℂ :=
  Complex.exp (↑Real.pi * Complex.I / (2 : ℂ) ^ (s + 1))

/-- The complex evaluation point `α := ω^2 = exp(π * I / 2^s)`. -/
noncomputable def alpha (s : ℕ) : ℂ := (omega s) ^ 2

/-- `ω` is nonzero, since `Complex.exp` is never zero. -/
lemma omega_ne_zero (s : ℕ) : omega s ≠ 0 :=
  Complex.exp_ne_zero _

/-- The phase exponent for a partition `p`, in terms of `ω`:
`Φ(p) := ∑_{k < s} 2^k * (n/2^k - count p (2^k))`.
We use natural-number subtraction; by `count_pow_two_le_div` the subtraction is
genuine (always exact). -/
def phaseExp (n s : ℕ) (p : Nat.Partition n) : ℕ :=
  ∑ k ∈ Finset.range s, 2 ^ k * (n / 2 ^ k - p.parts.count (2 ^ k))

lemma alpha_pow_two_pow_self (s : ℕ) : (alpha s) ^ (2 ^ s) = -1 := by
  have h₁ : (alpha s : ℂ) = Complex.exp (↑Real.pi * Complex.I / (2 : ℂ) ^ s) := by
    show (omega s) ^ 2 = _
    rw [omega, ← Complex.exp_nat_mul]
    congr 1
    rw [pow_succ]
    push_cast
    field_simp
  rw [h₁, ← Complex.exp_nat_mul,
      show ((2 ^ s : ℕ) : ℂ) * (↑Real.pi * Complex.I / (2 : ℂ) ^ s) = ↑Real.pi * Complex.I by
        rw [show ((2 ^ s : ℕ) : ℂ) = (2 : ℂ) ^ s by push_cast; rfl]
        field_simp,
      Complex.exp_eq_exp_re_mul_sin_add_cos]
  simp

/-- `1 + α^(2^s) = 0`, immediate from `alpha_pow_two_pow_self`. -/
lemma alpha_is_root (s : ℕ) : 1 + (alpha s) ^ (2 ^ s) = 0 := by
  rw [alpha_pow_two_pow_self]
  ring

/-- General multiset fact: for any natural numbers `a ≠ b`,
`a * M.count a + b * M.count b ≤ M.sum`. -/
lemma multiset_count_two_mul_le_sum
    (M : Multiset ℕ) (a b : ℕ) (hab : a ≠ b) :
    a * M.count a + b * M.count b ≤ M.sum := by
  set N : Multiset ℕ :=
    Multiset.replicate (M.count a) a + Multiset.replicate (M.count b) b with hN
  have hsub : N ≤ M := by
    rw [Multiset.le_iff_count]
    intro x
    simp only [hN, Multiset.count_add, Multiset.count_replicate]
    by_cases hxa : x = a
    · subst hxa
      have hbx : ¬ (b = x) := fun h => hab h.symm
      simp [hbx]
    · by_cases hxb : x = b
      · subst hxb
        simp [hab]
      · have hax : ¬ (a = x) := fun h => hxa h.symm
        have hbx : ¬ (b = x) := fun h => hxb h.symm
        simp [hax, hbx]
  have hNsum : N.sum = a * M.count a + b * M.count b := by
    simp [hN, Multiset.sum_add, Multiset.sum_replicate, mul_comm]
  obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp hsub
  have hle : N.sum ≤ M.sum := by
    rw [hu]
    simp [Multiset.sum_add]
  linarith [hNsum ▸ hle]

/-- For any partition `p` of `n` and any `k`, the number of parts equal to `2^k`
is at most `n / 2^k`. -/
lemma count_pow_two_le_div (n : ℕ) (p : Nat.Partition n) (k : ℕ) :
    p.parts.count (2 ^ k) ≤ n / 2 ^ k := by
  have hpos : 0 < 2 ^ k := by positivity
  have hbnd := multiset_count_two_mul_le_sum p.parts (2 ^ k) (2 ^ k + 1) (by omega)
  rw [p.parts_sum] at hbnd
  refine (Nat.le_div_iff_mul_le hpos).mpr ?_
  nlinarith [hbnd, Nat.zero_le ((2 ^ k + 1) * p.parts.count (2 ^ k + 1))]

/-- For a binary partition `p` of `n` with `p.parts.count (2^s) ≠ n / 2^s` (i.e.
non-surviving), the polynomial `hBPoly n p` evaluated at `α = alpha s` (after
mapping coefficients ℤ → ℂ) is zero. -/
lemma hBPoly_eval_nonsurviving_zero
    (n : ℕ) (s : ℕ) (hs : 2 ^ s ≤ n) (p : Nat.Partition n)
    (_hp : p ∈ binaryPartitions n)
    (hns : p.parts.count (2 ^ s) ≠ n / 2 ^ s) :
    ((hBPoly n p).map (Int.castRingHom ℂ)).eval (alpha s) = 0 := by
  have hsn : s ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by
    have : s < 2 ^ s := Nat.lt_two_pow_self
    omega)
  have hcount := count_pow_two_le_div n p s
  have he_ne : n / 2 ^ s - p.parts.count (2 ^ s) ≠ 0 := by omega
  unfold hBPoly
  rw [Polynomial.map_prod, Polynomial.eval_prod]
  refine Finset.prod_eq_zero hsn ?_
  simp only [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one,
    Polynomial.map_X, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_X]
  rw [alpha_is_root]
  exact zero_pow he_ne

/-- Existence of a surviving binary partition of `n`: take `n/2^s` copies of `2^s`
together with `n mod 2^s` copies of `1 = 2^0`. -/
lemma exists_surviving_partition (n : ℕ) (s : ℕ) (hs : 2 ^ s ≤ n) :
    ∃ p ∈ binaryPartitions n, p.parts.count (2 ^ s) = n / 2 ^ s := by
  set q := n / 2 ^ s with hq
  set r := n % 2 ^ s with hr
  set parts : Multiset ℕ := Multiset.replicate r 1 + Multiset.replicate q (2 ^ s) with hparts
  have h2s_pos : 0 < 2 ^ s := Nat.two_pow_pos s
  have hsum : parts.sum = n := by
    have hdiv : 2 ^ s * q + r = n := by simp [hq, hr, Nat.div_add_mod]
    rw [hparts, Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_replicate]
    simp [mul_comm]
    omega
  have hpos : ∀ {i : ℕ}, i ∈ parts → 0 < i := by
    intro i hi
    rcases Multiset.mem_add.mp hi with h1 | h2
    · rw [Multiset.eq_of_mem_replicate h1]
      exact one_pos
    · rw [Multiset.eq_of_mem_replicate h2]
      exact h2s_pos
  let p : Nat.Partition n := ⟨parts, hpos, hsum⟩
  have hbin : IsBinary p := by
    intro i hi
    rcases Multiset.mem_add.mp hi with h1 | h2
    · exact ⟨0, by rw [Multiset.eq_of_mem_replicate h1]; simp⟩
    · exact ⟨s, Multiset.eq_of_mem_replicate h2⟩
  refine ⟨p, ?_, ?_⟩
  · classical
    simp [binaryPartitions, Finset.mem_filter, hbin]
  · show parts.count (2 ^ s) = n / 2 ^ s
    rw [hparts, Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
    by_cases hs0 : s = 0
    · subst hs0
      simp
      omega
    · have hne : (1 : ℕ) ≠ 2 ^ s := fun h => by
        have := Nat.pow_eq_one.mp h.symm
        omega
      simp [hne, hq]

/-- A surviving binary partition has no parts strictly greater than `2^s`. -/
lemma surviving_no_large_parts
    (n : ℕ) (s : ℕ) (p : Nat.Partition n)
    (_hp : p ∈ binaryPartitions n)
    (hsurv : p.parts.count (2 ^ s) = n / 2 ^ s)
    (k : ℕ) (hk : s < k) :
    p.parts.count (2 ^ k) = 0 := by
  have hpos : (0 : ℕ) < 2 ^ s := Nat.two_pow_pos s
  have hlt : (2 : ℕ) ^ s < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hk
  have hbnd :
      2 ^ s * p.parts.count (2 ^ s) + 2 ^ k * p.parts.count (2 ^ k) ≤ p.parts.sum :=
    multiset_count_two_mul_le_sum p.parts (2 ^ s) (2 ^ k) (Nat.ne_of_lt hlt)
  rw [p.parts_sum, hsurv] at hbnd
  have hdm := Nat.div_add_mod n (2 ^ s)
  have hmod_lt : n % 2 ^ s < 2 ^ s := Nat.mod_lt _ hpos
  by_contra hcount
  have : 0 < p.parts.count (2 ^ k) := Nat.pos_of_ne_zero hcount
  nlinarith [hbnd, hdm, hmod_lt, hlt]

/-- For any multiset of natural numbers, the sum can be expressed as a sum
over distinct elements of `M.toFinset` weighted by their counts:
`M.sum = ∑ x ∈ M.toFinset, x * M.count x`. -/
lemma multiset_sum_eq_toFinset_sum_count (M : Multiset ℕ) :
    M.sum = ∑ x ∈ M.toFinset, x * M.count x := by
  rw [Finset.sum_multiset_count_of_subset M M.toFinset subset_rfl]
  exact Finset.sum_congr rfl (fun x _ => by rw [smul_eq_mul, mul_comm])

/-- If every element of `M` is a power of two, and `M.count (2^k) = 0` for `k > N`,
then `M.toFinset ⊆ (Finset.range (N+1)).image (fun k => 2^k)`. -/
lemma toFinset_subset_image_pow_two
    (M : Multiset ℕ) (N : ℕ)
    (hbin : ∀ x ∈ M, ∃ k, x = 2 ^ k)
    (hN : ∀ k, N < k → M.count (2 ^ k) = 0) :
    M.toFinset ⊆ (Finset.range (N + 1)).image (fun k => 2 ^ k) := by
  intro x hx
  rw [Multiset.mem_toFinset] at hx
  obtain ⟨k, rfl⟩ := hbin x hx
  refine Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr ?_, rfl⟩
  by_contra h
  push_neg at h
  have : 0 < M.count (2 ^ k) := Multiset.count_pos.mpr hx
  rw [hN k h] at this
  exact absurd this (lt_irrefl _)

/-- Combinatorial identity: for a multiset `M` of natural numbers, all of whose
elements are powers of two, with no occurrences of `2^k` for `k > N`, the sum
decomposes as `M.sum = ∑ k ∈ Finset.range (N + 1), 2^k * M.count (2^k)`. -/
lemma multiset_pow_two_sum_decompose
    (M : Multiset ℕ) (N : ℕ)
    (hbin : ∀ x ∈ M, ∃ k, x = 2 ^ k)
    (hN : ∀ k, N < k → M.count (2 ^ k) = 0) :
    M.sum = ∑ k ∈ Finset.range (N + 1), 2 ^ k * M.count (2 ^ k) := by
  rw [multiset_sum_eq_toFinset_sum_count M,
      Finset.sum_subset (toFinset_subset_image_pow_two M N hbin hN) (fun x _ hxnot => by
        simp only [Multiset.mem_toFinset] at hxnot
        rw [Multiset.count_eq_zero.mpr hxnot, mul_zero]),
      Finset.sum_image (fun _ _ _ _ h => Nat.pow_right_injective (by norm_num) h)]

/-- For a surviving binary partition, the sum of contributions from parts strictly
smaller than `2^s` equals `n mod 2^s`. -/
lemma sum_small_parts_eq_mod
    (n s : ℕ) (p : Nat.Partition n)
    (hp : p ∈ binaryPartitions n)
    (hsurv : p.parts.count (2 ^ s) = n / 2 ^ s) :
    ∑ k ∈ Finset.range s, 2 ^ k * p.parts.count (2 ^ k) = n % 2 ^ s := by
  classical
  have hbin : IsBinary p := (Finset.mem_filter.mp hp).2
  have hdecomp := multiset_pow_two_sum_decompose p.parts s hbin
    (fun k hk => surviving_no_large_parts n s p hp hsurv k hk)
  rw [p.parts_sum, Finset.sum_range_succ, hsurv] at hdecomp
  have hmod := Nat.div_add_mod n (2 ^ s)
  omega

/-- For all surviving partitions, the phase exponent `phaseExp n s p` is the same
constant `(∑_{k<s} 2^k * (n/2^k)) - (n mod 2^s)`. -/
lemma phaseExp_eq_const
    (n : ℕ) (s : ℕ) (_hs : 2 ^ s ≤ n) (p : Nat.Partition n)
    (hp : p ∈ binaryPartitions n)
    (hsurv : p.parts.count (2 ^ s) = n / 2 ^ s) :
    (phaseExp n s p : ℤ) =
      (∑ k ∈ Finset.range s, (2 ^ k : ℤ) * (n / 2 ^ k : ℤ)) - (n % 2 ^ s : ℤ) := by
  have hsmall : ∑ k ∈ Finset.range s, 2 ^ k * p.parts.count (2 ^ k) = n % 2 ^ s :=
    sum_small_parts_eq_mod n s p hp hsurv
  have hkey :
      phaseExp n s p + n % 2 ^ s
        = ∑ k ∈ Finset.range s, 2 ^ k * (n / 2 ^ k) := by
    unfold phaseExp
    rw [← hsmall, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Nat.mul_add, Nat.sub_add_cancel (count_pow_two_le_div n p k)]
  have hcast : ((phaseExp n s p + n % 2 ^ s : ℕ) : ℤ)
        = (∑ k ∈ Finset.range s, (2 ^ k : ℤ) * (n / 2 ^ k : ℤ)) := by
    rw [hkey]
    push_cast
    rfl
  push_cast at hcast
  linarith

/-- The positive real factor in the factorization
`hBPoly n p (α) = ω^(phaseExp) * survivingR`.
It is the product of the "magnitude" parts:
- for `k < s`: `(2 * cos(π / 2^(s-k+1)))^(n/2^k - count(2^k))`,
- for `s < k ≤ n`: `2^(n/2^k)` (because `1 + α^(2^k) = 2` for such `k` in a surviving partition).
-/
noncomputable def survivingR (n s : ℕ) (p : Nat.Partition n) : ℝ :=
  (∏ k ∈ Finset.range s,
      ((2 : ℝ) * Real.cos (Real.pi / (2 : ℝ) ^ (s - k + 1))) ^
        (n / 2 ^ k - p.parts.count (2 ^ k))) *
  (∏ k ∈ Finset.Ioc s n, (2 : ℝ) ^ (n / 2 ^ k))

/-- For `k > s`, `α^(2^k) = 1`. -/
lemma alpha_pow_eq_one_of_gt (s k : ℕ) (hk : s < k) : alpha s ^ (2 ^ k) = 1 := by
  rw [show (2 : ℕ) ^ k = 2 ^ s * 2 ^ (k - s) by rw [← pow_add]; congr 1; omega,
      pow_mul, alpha_pow_two_pow_self]
  have heven : Even (2 ^ (k - s)) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt hk)
    exact ⟨2 ^ m, by rw [hm, pow_succ]; ring⟩
  exact heven.neg_one_pow

/-- Half-angle identity in ℂ: `1 + exp(2 θ I) = exp(θ I) * (2 cos θ)`. -/
lemma half_angle_complex (θ : ℝ) :
    (1 : ℂ) + Complex.exp (2 * (↑θ : ℂ) * Complex.I) =
      Complex.exp ((↑θ : ℂ) * Complex.I) * (((2 : ℝ) * Real.cos θ : ℝ) : ℂ) := by
  have h1 : Complex.exp (2 * (↑θ : ℂ) * Complex.I) =
      Complex.exp ((↑θ : ℂ) * Complex.I) * Complex.exp ((↑θ : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    ring_nf
  have e2 : Complex.exp ((↑θ : ℂ) * Complex.I) *
      Complex.exp (-((↑θ : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_add, show (↑θ : ℂ) * Complex.I + -((↑θ : ℂ) * Complex.I) = 0 by ring,
        Complex.exp_zero]
  rw [h1]
  push_cast
  rw [Complex.cos]
  field_simp
  linear_combination -e2

lemma omega_pow_two_pow (s k : ℕ) (hk : k ≤ s + 1) :
    omega s ^ (2 ^ k) = Complex.exp (↑Real.pi * Complex.I / (2 : ℂ) ^ (s + 1 - k)) := by
  rw [show (omega s : ℂ) = Complex.exp (↑Real.pi * Complex.I / (2 : ℂ) ^ (s + 1)) from rfl,
      ← Complex.exp_nat_mul]
  congr 1
  rw [show ((2 ^ k : ℕ) : ℂ) = (2 : ℂ) ^ k from by push_cast; rfl,
      show (2 : ℂ) ^ (s + 1) = (2 : ℂ) ^ (s + 1 - k) * (2 : ℂ) ^ k from by
        rw [← pow_add, show (s + 1 - k) + k = s + 1 from by omega]]
  field_simp

/-- The half-angle identity: for `k < s`,
`1 + α^(2^k) = ω^(2^k) * (2 * cos(π / 2^(s-k+1)))` (as a complex equation). -/
lemma one_add_alpha_pow_eq_omega_mul (s k : ℕ) (hk : k < s) :
    (1 : ℂ) + alpha s ^ (2 ^ k) =
      omega s ^ (2 ^ k) *
        (((2 : ℝ) * Real.cos (Real.pi / (2 : ℝ) ^ (s - k + 1))) : ℂ) := by
  have hα' : alpha s ^ (2 ^ k) =
      Complex.exp (↑Real.pi * Complex.I / (2 : ℂ) ^ (s + 1 - (k + 1))) := by
    rw [show alpha s ^ (2 ^ k) = omega s ^ (2 ^ (k + 1)) by
          rw [alpha, ← pow_mul, pow_succ, mul_comm 2 (2 ^ k)],
        omega_pow_two_pow s (k + 1) (by omega)]
  have hω' : omega s ^ (2 ^ k) =
      Complex.exp (↑Real.pi * Complex.I / (2 : ℂ) ^ (s + 1 - k)) :=
    omega_pow_two_pow s k (by omega)
  rw [hα', hω', show s + 1 - (k + 1) = s - k from by omega,
      show s + 1 - k = (s - k) + 1 from by omega]
  set m := s - k
  have key := half_angle_complex (Real.pi / (2 : ℝ) ^ (m + 1))
  rw [show ((↑(Real.pi / (2 : ℝ) ^ (m + 1)) : ℂ)) = (↑Real.pi : ℂ) / (2 : ℂ) ^ (m + 1) by
    push_cast; rfl] at key
  rw [show (2 : ℂ) * ((↑Real.pi : ℂ) / (2 : ℂ) ^ (m + 1)) * Complex.I =
        (↑Real.pi : ℂ) * Complex.I / (2 : ℂ) ^ m by field_simp; ring,
      show ((↑Real.pi : ℂ) / (2 : ℂ) ^ (m + 1)) * Complex.I =
        (↑Real.pi : ℂ) * Complex.I / (2 : ℂ) ^ (m + 1) by ring] at key
  push_cast at key
  convert key using 2
  push_cast
  ring

/-- For `k < s`, `cos(π / 2^(s-k+1)) > 0`. -/
lemma cos_factor_pos (s k : ℕ) (hk : k < s) :
    (0 : ℝ) < Real.cos (Real.pi / (2 : ℝ) ^ (s - k + 1)) := by
  have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (s - k + 1) := by
    have := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show 2 ≤ s - k + 1 by omega)
    linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hd : (0 : ℝ) < Real.pi / (2 : ℝ) ^ (s - k + 1) := div_pos hpi (by positivity)
  have hd_le : Real.pi / (2 : ℝ) ^ (s - k + 1) ≤ Real.pi / 4 :=
    div_le_div_of_nonneg_left hpi.le (by norm_num) h4
  refine Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

/-- `survivingR` is positive: a product of positive real numbers. -/
lemma survivingR_pos (n s : ℕ) (p : Nat.Partition n) :
    0 < survivingR n s p := by
  unfold survivingR
  refine mul_pos (Finset.prod_pos fun k hk => ?_) (Finset.prod_pos fun k _ => pow_pos (by norm_num) _)
  exact pow_pos (mul_pos (by norm_num) (cos_factor_pos s k (Finset.mem_range.mp hk))) _

lemma hBPoly_eval_eq_prod (n : ℕ) (p : Nat.Partition n) (α : ℂ) :
    ((hBPoly n p).map (Int.castRingHom ℂ)).eval α
      = ∏ k ∈ Finset.range (n + 1),
          (1 + α ^ (2 ^ k)) ^ (n / 2 ^ k - p.parts.count (2 ^ k)) := by
  simp [hBPoly, Polynomial.map_prod, Polynomial.eval_prod, Polynomial.map_pow,
    Polynomial.map_add, Polynomial.map_one, Polynomial.map_X]

/-- Small range factorization: for `k < s`, write each factor `1 + α^(2^k)` using the
half-angle formula `1 + α^(2^k) = ω^(2^k) * (2 cos(π/2^(s-k+1)))`. Raising to `e_k`
and taking the product over `k < s` gives a product whose phase is
`ω^(∑_{k<s} 2^k · e_k) = ω^(phaseExp n s p)` and whose real factor is
`∏_{k<s} (2 cos(π/2^(s-k+1)))^{e_k}`. -/
lemma prod_small_factorize (n s : ℕ) (p : Nat.Partition n) :
    ∏ k ∈ Finset.range s,
        (1 + alpha s ^ (2 ^ k)) ^ (n / 2 ^ k - p.parts.count (2 ^ k))
      = (omega s) ^ (phaseExp n s p) *
          ((∏ k ∈ Finset.range s,
              ((2 : ℝ) * Real.cos (Real.pi / (2 : ℝ) ^ (s - k + 1))) ^
                (n / 2 ^ k - p.parts.count (2 ^ k))) : ℂ) := by
  rw [Finset.prod_congr rfl fun k hk => by
    rw [one_add_alpha_pow_eq_omega_mul s k (Finset.mem_range.mp hk), mul_pow, ← pow_mul],
    Finset.prod_mul_distrib]
  unfold phaseExp
  rw [← Finset.prod_pow_eq_pow_sum]

/-- Large range simplification: for a surviving binary partition, the factors for `k > s`
become `2^(n/2^k)` since `count(2^k) = 0` and `1 + α^(2^k) = 2`. -/
lemma prod_large_eq (n s : ℕ) (p : Nat.Partition n)
    (hp : p ∈ binaryPartitions n)
    (hsurv : p.parts.count (2 ^ s) = n / 2 ^ s) :
    ∏ k ∈ Finset.Ioc s n,
        (1 + alpha s ^ (2 ^ k)) ^ (n / 2 ^ k - p.parts.count (2 ^ k))
      = ((∏ k ∈ Finset.Ioc s n, (2 : ℝ) ^ (n / 2 ^ k)) : ℂ) := by
  push_cast
  refine Finset.prod_congr rfl fun k hk => ?_
  obtain ⟨hsk, _⟩ := Finset.mem_Ioc.mp hk
  rw [alpha_pow_eq_one_of_gt s k hsk, surviving_no_large_parts n s p hp hsurv k hsk]
  norm_num

/-- The key factorization: for a surviving binary partition,
`((hBPoly n p).map ℤ→ℂ).eval (α s) = (ω s)^(phaseExp n s p) * (survivingR n s p : ℂ)`. -/
lemma hBPoly_eval_eq_omega_pow_mul_survivingR
    (n s : ℕ) (hs : 2 ^ s ≤ n) (p : Nat.Partition n)
    (hp : p ∈ binaryPartitions n)
    (hsurv : p.parts.count (2 ^ s) = n / 2 ^ s) :
    ((hBPoly n p).map (Int.castRingHom ℂ)).eval (alpha s)
      = (omega s) ^ (phaseExp n s p) * (survivingR n s p : ℂ) := by
  rw [hBPoly_eval_eq_prod]
  have hsn : s ≤ n := le_trans Nat.lt_two_pow_self.le hs
  -- Split range (n+1) = (range s ∪ {s}) ∪ Ioc s n
  have hsplit : Finset.range (n + 1) = (Finset.range s ∪ {s}) ∪ Finset.Ioc s n := by
    ext k
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ioc]
    omega
  have hd1 : Disjoint (Finset.range s ∪ {s} : Finset ℕ) (Finset.Ioc s n) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_singleton, Finset.mem_Ioc] at hk1 hk2
    omega
  have hd2 : Disjoint (Finset.range s) ({s} : Finset ℕ) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_range, Finset.mem_singleton] at hk1 hk2
    omega
  rw [hsplit, Finset.prod_union hd1, Finset.prod_union hd2, Finset.prod_singleton]
  -- The k = s factor is (1 + α^(2^s))^0 = 1 since the exponent is 0 by hsurv
  rw [show n / 2 ^ s - p.parts.count (2 ^ s) = 0 by rw [hsurv]; simp,
      pow_zero, mul_one, prod_small_factorize, prod_large_eq n s p hp hsurv]
  unfold survivingR
  push_cast
  ring

lemma phaseExp_eq_of_surviving
    (n : ℕ) (s : ℕ) (hs : 2 ^ s ≤ n) (p q : Nat.Partition n)
    (hp : p ∈ binaryPartitions n) (hp_surv : p.parts.count (2 ^ s) = n / 2 ^ s)
    (hq : q ∈ binaryPartitions n) (hq_surv : q.parts.count (2 ^ s) = n / 2 ^ s) :
    phaseExp n s p = phaseExp n s q := by
  exact_mod_cast (phaseExp_eq_const n s hs p hp hp_surv).trans
    (phaseExp_eq_const n s hs q hq hq_surv).symm

lemma sum_surviving_eval_nonzero
    (n : ℕ) (_hn : 2 ≤ n) (s : ℕ) (hs : 2 ^ s ≤ n) :
    (∑ p ∈ (binaryPartitions n).filter
              (fun p => p.parts.count (2 ^ s) = n / 2 ^ s),
        ((hBPoly n p).map (Int.castRingHom ℂ)).eval (alpha s)) ≠ 0 := by
  obtain ⟨p₀, hp₀_mem, hp₀_surv⟩ := exists_surviving_partition n s hs
  have hR_pos : (0 : ℝ) <
      ∑ p ∈ (binaryPartitions n).filter
              (fun p => p.parts.count (2 ^ s) = n / 2 ^ s),
        survivingR n s p :=
    Finset.sum_pos (fun p _ => survivingR_pos n s p)
      ⟨p₀, by simp [Finset.mem_filter, hp₀_mem, hp₀_surv]⟩
  have h_eq :
      (∑ p ∈ (binaryPartitions n).filter
                (fun p => p.parts.count (2 ^ s) = n / 2 ^ s),
          ((hBPoly n p).map (Int.castRingHom ℂ)).eval (alpha s))
        = (omega s) ^ (phaseExp n s p₀) *
            ((∑ p ∈ (binaryPartitions n).filter
                      (fun p => p.parts.count (2 ^ s) = n / 2 ^ s),
                survivingR n s p : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    obtain ⟨hp_mem, hp_surv⟩ := hp
    rw [hBPoly_eval_eq_omega_pow_mul_survivingR n s hs p hp_mem hp_surv,
        phaseExp_eq_of_surviving n s hs p p₀ hp_mem hp_surv hp₀_mem hp₀_surv]
  rw [h_eq]
  exact mul_ne_zero (pow_ne_zero _ (omega_ne_zero s)) (by exact_mod_cast hR_pos.ne')

/--
The key non-vanishing lemma encapsulating the analytic heart of the proof.

For `n ≥ 2` and `s` with `2^s ≤ n`, there exists a complex number `α` which is a root
of `1 + X^(2^s)` (i.e. `1 + α^(2^s) = 0`), and yet `numB n`, mapped to `ℂ[X]` and
evaluated at `α`, is nonzero.
-/
lemma exists_complex_root_with_nonzero_eval
    (n : ℕ) (hn : 2 ≤ n) (s : ℕ) (hs : 2 ^ s ≤ n) :
    ∃ α : ℂ, 1 + α ^ (2 ^ s) = 0 ∧
      ((numB n).map (Int.castRingHom ℂ)).eval α ≠ 0 := by
  classical
  refine ⟨alpha s, alpha_is_root s, ?_⟩
  unfold numB
  rw [Polynomial.map_sum, Polynomial.eval_finset_sum,
      ← Finset.sum_filter_add_sum_filter_not (binaryPartitions n)
        (fun p => p.parts.count (2 ^ s) = n / 2 ^ s)]
  have hzero :
      ∑ p ∈ (binaryPartitions n).filter
          (fun p => ¬ p.parts.count (2 ^ s) = n / 2 ^ s),
          ((hBPoly n p).map (Int.castRingHom ℂ)).eval (alpha s) = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.mem_filter] at hp
    exact hBPoly_eval_nonsurviving_zero n s hs p hp.1 hp.2
  rw [hzero, add_zero]
  exact sum_surviving_eval_nonzero n hn s hs

/-- **Conjecture 7 (Ballantine–Beck–Feigon–Maurischat).**
For every `n ≥ 2` and every `s ≥ 0` with `2^s ≤ n`, the polynomial
`1 + x^{2^s}` does not divide `num_B(n, x)` in `ℤ[x]`. -/
theorem conjecture7
    (n : ℕ) (hn : 2 ≤ n) (s : ℕ) (hs : 2 ^ s ≤ n) :
    ¬ ((1 + X ^ (2 ^ s) : Polynomial ℤ) ∣ numB n) := by
  rintro ⟨q, hq⟩
  obtain ⟨α, hα_root, hα_nonzero⟩ :=
    exists_complex_root_with_nonzero_eval n hn s hs
  apply hα_nonzero
  rw [show ((numB n).map (Int.castRingHom ℂ)).eval α
        = (((1 + X ^ (2 ^ s) : Polynomial ℤ).map (Int.castRingHom ℂ)).eval α)
          * ((q.map (Int.castRingHom ℂ)).eval α) by
        rw [hq, Polynomial.map_mul, Polynomial.eval_mul],
      show (((1 + X ^ (2 ^ s) : Polynomial ℤ).map (Int.castRingHom ℂ)).eval α) = 0 by
        simp [Polynomial.map_add, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X,
          hα_root],
      zero_mul]

end Conj7
