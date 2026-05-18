import Mathlib

open Polynomial

def powersOfTwoUpTo (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).image (fun k => 2 ^ k)

def IsBinaryPartition {n : ℕ} (p : Nat.Partition n) : Prop :=
  ∀ i ∈ p.parts, i ∈ powersOfTwoUpTo n

instance (n : ℕ) : DecidablePred (@IsBinaryPartition n) :=
  fun _ => Multiset.decidableDforallMultiset

def binaryPartitions (n : ℕ) : Finset (Nat.Partition n) :=
  (Finset.univ : Finset (Nat.Partition n)).filter IsBinaryPartition

noncomputable def denB (n : ℕ) : ℤ[X] :=
  ∏ k ∈ Finset.range (n + 1), (1 + X ^ (2 ^ k)) ^ (n / 2 ^ k)

noncomputable def hBPartition (n : ℕ) (p : Nat.Partition n) : ℤ[X] :=
  ∏ k ∈ Finset.range (n + 1), (1 + X ^ (2 ^ k)) ^ ((n / 2 ^ k) - p.parts.count (2 ^ k))

noncomputable def numB (n : ℕ) : ℤ[X] :=
  ∑ p ∈ binaryPartitions n, hBPartition n p

lemma denB_map_eq (n : ℕ) :
    ((denB n).map (Int.castRingHom ℚ)) =
      ∏ k ∈ Finset.range (n + 1), (1 + X ^ (2 ^ k) : ℚ[X]) ^ (n / 2 ^ k) := by
  simp [denB, Polynomial.map_prod, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_X]

/-- `cyclotomic (2^(k+1)) ℚ = X^(2^k) + 1`. -/
lemma cyclotomic_two_pow_succ_eq_rat (k : ℕ) :
    Polynomial.cyclotomic (2 ^ (k + 1)) ℚ = X ^ (2 ^ k) + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : Polynomial.cyclotomic (2 ^ (k + 1)) ℚ * (X ^ (2 ^ k) - 1) =
      (X ^ (2 ^ k) + 1) * (X ^ (2 ^ k) - 1) := by
    rw [Polynomial.cyclotomic_prime_pow_mul_X_pow_sub_one ℚ 2 k,
      show (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k by ring, pow_add]
    ring
  have hne : (X ^ (2 ^ k) - 1 : ℚ[X]) ≠ 0 := fun habs => by
    have hev := congr_arg (fun p : ℚ[X] => p.eval 2) habs
    simp at hev
    have : (1 : ℚ) < 2 ^ (2 ^ k) :=
      one_lt_pow₀ (by norm_num) (Nat.two_pow_pos _).ne'
    linarith
  exact mul_right_cancel₀ hne key

/-- The polynomial `1 + X^(2^k) : ℚ[X]` is irreducible. -/
lemma one_add_X_pow_two_pow_irreducible_rat (k : ℕ) :
    Irreducible (1 + X ^ (2 ^ k) : ℚ[X]) := by
  rw [show (1 + X ^ (2 ^ k) : ℚ[X]) = Polynomial.cyclotomic (2 ^ (k + 1)) ℚ by
    rw [cyclotomic_two_pow_succ_eq_rat, add_comm]]
  exact cyclotomic.irreducible_rat (Nat.two_pow_pos _)

lemma zetaRoot_pow_two_pow_eq_neg_one (k : ℕ) :
    (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ)) : ℂ) ^ (2 ^ k) = -1 := by
  rw [← Complex.exp_nat_mul, show ((2 ^ k : ℕ) : ℂ) * (Real.pi * Complex.I / (2 ^ k : ℕ)) =
    Real.pi * Complex.I by field_simp, Complex.exp_eq_exp_re_mul_sin_add_cos]
  simp [Complex.I_re, Complex.I_im, mul_comm]

lemma one_add_X_pow_two_pow_eval_zetaRoot (k : ℕ) :
    ((1 + X ^ (2 ^ k) : ℂ[X])).eval (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) = 0 := by
  rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    zetaRoot_pow_two_pow_eq_neg_one, add_neg_cancel]

/-- For `r = 0`, the sum over binary partitions equals `1`. -/
lemma sum_binaryPartitions_hBPartition_eval_zero_case (k : ℕ) :
    (∑ p' ∈ binaryPartitions 0,
        ((hBPartition 0 p').map (Int.castRingHom ℂ)).eval
          (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ)))) = 1 := by
  have h_eq : binaryPartitions 0 = {(default : Nat.Partition 0)} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => by simp at hi⟩,
        fun p _ => Subsingleton.elim p _⟩
  rw [h_eq, Finset.sum_singleton]
  simp [hBPartition]

/-- For any `r ≥ 1`, the set `binaryPartitions r` is nonempty (the all-ones partition). -/
lemma binaryPartitions_nonempty (r : ℕ) (hr : 0 < r) :
    (binaryPartitions r).Nonempty := by
  refine ⟨⟨Multiset.replicate r 1, fun hi => ?_, ?_⟩, ?_⟩
  · rw [Multiset.eq_of_mem_replicate hi]
    exact Nat.one_pos
  · simp [Multiset.sum_replicate]
  · simp only [binaryPartitions, Finset.mem_filter, Finset.mem_univ, true_and,
      IsBinaryPartition, powersOfTwoUpTo, Finset.mem_image, Finset.mem_range]
    intro i hi
    rw [Multiset.eq_of_mem_replicate hi]
    exact ⟨0, by omega, by simp⟩

/-- The (real) total `ζ`-phase exponent, independent of `p ∈ binaryPartitions r`. -/
noncomputable def summandPhaseT (r k : ℕ) : ℝ :=
  (∑ j ∈ Finset.range k, ((r / 2 ^ j : ℕ) : ℝ) / (2 ^ (k - j + 1) : ℝ))
    - (r : ℝ) / (2 ^ (k + 1) : ℝ)

/-- The (complex) phase factor for the factorization. -/
noncomputable def summandPhase (r k : ℕ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * (summandPhaseT r k : ℂ))

/-- The (real) positive magnitude factor for each summand. -/
noncomputable def summandMag (r k : ℕ) (p : Nat.Partition r) : ℝ :=
  ∏ j ∈ Finset.range k,
    (2 * Real.cos (Real.pi / (2 ^ (k - j + 1) : ℝ))) ^ ((r / 2 ^ j) - p.parts.count (2 ^ j))

lemma partition_count_pow_two_le_div (n k : ℕ) (p : Nat.Partition n) :
    p.parts.count (2 ^ k) ≤ n / 2 ^ k := by
  rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos k)]
  have hns : p.parts.count (2 ^ k) * 2 ^ k = (Multiset.filter (Eq (2 ^ k)) p.parts).sum := by
    simpa [smul_eq_mul] using Multiset.nsmul_count (2 ^ k) (s := p.parts)
  have := Multiset.sum_filter_add_sum_filter_not (s := p.parts) (Eq (2 ^ k))
  have hsum : p.parts.sum = n := p.parts_sum
  omega

/-- For `j < k`, `cos(π / 2^(k - j + 1))` is strictly positive. -/
lemma cos_pi_div_two_pow_pos (k j : ℕ) (hjk : j < k) :
    0 < Real.cos (Real.pi / (2 ^ (k - j + 1) : ℝ)) := by
  apply Real.cos_pos_of_mem_Ioo
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpow_pos : (0 : ℝ) < 2 ^ (k - j + 1) := by positivity
  have hpow : (4 : ℝ) ≤ 2 ^ (k - j + 1) :=
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k - j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  refine ⟨by linarith [div_pos hpi hpow_pos], ?_⟩
  have : Real.pi / (2 ^ (k - j + 1) : ℝ) ≤ Real.pi / 4 :=
    div_le_div_of_nonneg_left hpi.le (by norm_num) hpow
  linarith

/-- The magnitude factor `summandMag r k p` is strictly positive. -/
lemma summandMag_pos (r k : ℕ) (p : Nat.Partition r) :
    0 < summandMag r k p :=
  Finset.prod_pos fun j hj => pow_pos (by
    linarith [cos_pi_div_two_pow_pos k j (Finset.mem_range.mp hj)]) _

/-- **Key exponent identity:** For natural numbers `j < k`,
`((2^j : ℕ) : ℂ) * (π·I / (2^k : ℕ)) = 2 * (π·I / (2^(k-j+1) : ℕ))`. -/
lemma exp_exponent_combined (k j : ℕ) (hjk : j < k) :
    ((2 ^ j : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I / ((2 ^ k : ℕ) : ℂ)) =
      2 * ((Real.pi : ℂ) * Complex.I / ((2 ^ (k - j + 1) : ℕ) : ℂ)) := by
  have h2_ne : (2 ^ (k - j) : ℂ) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2j_ne : (2 ^ j : ℂ) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hk_split : (2 ^ k : ℂ) = (2 ^ j : ℂ) * (2 ^ (k - j) : ℂ) := by
    rw [← pow_add]
    congr 1
    omega
  push_cast
  rw [hk_split, show (2 ^ (k - j + 1) : ℂ) = 2 * (2 ^ (k - j) : ℂ) by rw [pow_succ]; ring]
  field_simp

/-- **Per-factor identity.** For `j < k`,
`1 + ζ_k^(2^j) = exp(π i / 2^(k-j+1)) * (2 * cos(π / 2^(k-j+1)))`
(the half-angle identity `1 + e^{iθ} = e^{iθ/2} * 2cos(θ/2)` with `θ = π / 2^(k-j)`). -/
lemma one_add_zeta_pow_factor (k j : ℕ) (hjk : j < k) :
    (1 : ℂ) + Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ)) ^ (2 ^ j) =
      Complex.exp (Real.pi * Complex.I / (2 ^ (k - j + 1) : ℕ))
        * (2 * Real.cos (Real.pi / (2 ^ (k - j + 1) : ℝ)) : ℂ) := by
  set α : ℂ := (Real.pi : ℂ) * Complex.I / ((2 ^ (k - j + 1) : ℕ) : ℂ) with hα_def
  -- LHS = 1 + exp(α)^2
  rw [show (1 : ℂ) + Complex.exp ((Real.pi : ℂ) * Complex.I / ((2 ^ k : ℕ) : ℂ)) ^ (2 ^ j) =
        1 + Complex.exp α ^ 2 from by
    rw [← Complex.exp_nat_mul, exp_exponent_combined k j hjk]
    show 1 + Complex.exp ((2 : ℂ) * α) = 1 + Complex.exp α ^ 2
    rw [show ((2 : ℂ) * α) = ((2 : ℕ) : ℂ) * α by push_cast; ring, Complex.exp_nat_mul]]
  -- Replace `↑(Real.cos ..)` with `Complex.cos ..`
  rw [show ((Real.cos (Real.pi / (2 ^ (k - j + 1) : ℝ)) : ℝ) : ℂ) =
        Complex.cos ((Real.pi : ℂ) / (2 ^ (k - j + 1) : ℕ)) by
      rw [Complex.ofReal_cos]; push_cast; rfl]
  -- 2 * cos(π / 2^..) = exp α + exp (-α)
  rw [show 2 * Complex.cos ((Real.pi : ℂ) / ((2 ^ (k - j + 1) : ℕ) : ℂ)) =
        Complex.exp α + Complex.exp (-α) from by
    rw [Complex.two_cos]
    congr 1 <;> rw [hα_def] <;> ring]
  rw [mul_add, ← Complex.exp_add, ← Complex.exp_add,
    show α + α = ((2 : ℕ) : ℂ) * α from by push_cast; ring,
    show α + -α = (0 : ℂ) from by ring, Complex.exp_zero, Complex.exp_nat_mul]
  ring

lemma hBPartition_map_eval_eq_prod (n k : ℕ) (p : Nat.Partition n) :
    ((hBPartition n p).map (Int.castRingHom ℂ)).eval
        (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) =
      ∏ j ∈ Finset.range (n + 1),
        (1 + (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) ^ (2 ^ j))
          ^ ((n / 2 ^ j) - p.parts.count (2 ^ j)) := by
  simp [hBPartition, Polynomial.map_prod, Polynomial.eval_prod]

/-- For `r < 2^k` and any partition `p` of `r`, the product
over `Finset.range (r + 1)` agrees with the product over `Finset.range k`. -/
lemma eq_prod_range_of_tail_one_both (r k : ℕ) (hr : r < 2 ^ k) (p : Nat.Partition r) :
    (∏ j ∈ Finset.range (r + 1),
        ((1 : ℂ) + Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ)) ^ (2 ^ j))
          ^ ((r / 2 ^ j) - p.parts.count (2 ^ j))) =
      ∏ j ∈ Finset.range k,
        ((1 : ℂ) + Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ)) ^ (2 ^ j))
          ^ ((r / 2 ^ j) - p.parts.count (2 ^ j)) := by
  have tail_zero : ∀ j, k ≤ j → (r / 2 ^ j) - p.parts.count (2 ^ j) = 0 := by
    intro j hkj
    have hrlt : r < 2 ^ j := lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hkj)
    have hdiv : r / 2 ^ j = 0 := Nat.div_eq_of_lt hrlt
    have hcnt := partition_count_pow_two_le_div r j p
    omega
  by_cases hcase : r + 1 ≤ k
  · apply Finset.prod_subset
    · intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    · intro j hjk hjnot
      rw [Finset.mem_range] at hjk hjnot
      have hjlt : j < 2 ^ j := Nat.lt_two_pow_self
      have hdiv : r / 2 ^ j = 0 := Nat.div_eq_of_lt (by omega)
      have hcnt := partition_count_pow_two_le_div r j p
      rw [hdiv, show p.parts.count (2 ^ j) = 0 from by omega, Nat.sub_zero, pow_zero]
  · push_neg at hcase
    symm
    apply Finset.prod_subset
    · intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    · intro j hjr hjnot
      rw [Finset.mem_range] at hjr hjnot
      rw [tail_zero j (by omega), pow_zero]

/-- The product over `Finset.range (r + 1)` defining `hBPartition` restricts to a product
over `Finset.range k` when `r < 2^k`. -/
lemma hBPartition_eval_eq_range_k (r k : ℕ) (hr : r < 2 ^ k) (p : Nat.Partition r) :
    ((hBPartition r p).map (Int.castRingHom ℂ)).eval
        (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) =
      ∏ j ∈ Finset.range k,
        ((1 : ℂ) + Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ)) ^ (2 ^ j))
          ^ ((r / 2 ^ j) - p.parts.count (2 ^ j)) := by
  rw [hBPartition_map_eval_eq_prod r k p, eq_prod_range_of_tail_one_both r k hr p]

/-- For `p ∈ binaryPartitions r` and `r < 2^k`, every part of `p` is of the form `2^j`
for some `j ∈ Finset.range k`. -/
lemma parts_toFinset_subset_image_range
    (r k : ℕ) (hr : r < 2 ^ k) (p : Nat.Partition r)
    (hp : p ∈ binaryPartitions r) :
    p.parts.toFinset ⊆ (Finset.range k).image (fun j => 2 ^ j) := by
  have hbin : IsBinaryPartition p := (Finset.mem_filter.mp hp).2
  intro i hi
  rw [Multiset.mem_toFinset] at hi
  have himem : i ∈ powersOfTwoUpTo r := hbin i hi
  rw [powersOfTwoUpTo, Finset.mem_image] at himem
  obtain ⟨j₀, _, rfl⟩ := himem
  have hile : 2 ^ j₀ ≤ r := p.parts_sum ▸ Multiset.le_sum_of_mem hi
  have hj₀lt : j₀ < k :=
    (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp (lt_of_le_of_lt hile hr)
  exact Finset.mem_image.mpr ⟨j₀, Finset.mem_range.mpr hj₀lt, rfl⟩

/-- **Sum identity.** If `p` is a binary partition of `r` and `r < 2^k`,
then `∑ j ∈ Finset.range k, p.parts.count (2^j) * 2^j = r`. -/
lemma binaryPartition_sum_eq (r k : ℕ) (hr : r < 2 ^ k) (p : Nat.Partition r)
    (hp : p ∈ binaryPartitions r) :
    ∑ j ∈ Finset.range k, p.parts.count (2 ^ j) * 2 ^ j = r := by
  have hinj : Set.InjOn (fun j : ℕ => 2 ^ j) (Finset.range k : Set ℕ) :=
    fun _ _ _ _ hab => Nat.pow_right_injective (le_refl 2) hab
  have h := Finset.sum_multiset_count_of_subset p.parts _
    (parts_toFinset_subset_image_range r k hr p hp)
  rw [Finset.sum_image hinj] at h
  simp only [smul_eq_mul] at h
  have := p.parts_sum
  omega

/-- For `j ≤ k`, `1 / 2^(k-j+1) = 2^j / 2^(k+1)` (in ℝ). -/
lemma two_pow_div_identity (j k : ℕ) (hjk : j ≤ k) :
    (1 : ℝ) / ((2 : ℝ) ^ (k - j + 1)) = ((2 : ℝ) ^ j) / ((2 : ℝ) ^ (k + 1)) := by
  rw [show (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (k - j + 1) * (2 : ℝ) ^ j by
    rw [← pow_add]; congr 1; omega]
  field_simp

/-- **Phase sum identity.** For a binary partition `p ∈ binaryPartitions r` with `r < 2^k`:
`∑ j, (count (2^j) : ℝ) / 2^(k-j+1) = r / 2^(k+1)`. -/
lemma binaryPartition_count_div_sum (r k : ℕ) (hr : r < 2 ^ k) (p : Nat.Partition r)
    (hp : p ∈ binaryPartitions r) :
    ∑ j ∈ Finset.range k, (p.parts.count (2 ^ j) : ℝ) / ((2 : ℝ) ^ (k - j + 1)) =
      (r : ℝ) / ((2 : ℝ) ^ (k + 1)) := by
  rw [show (∑ j ∈ Finset.range k, (p.parts.count (2 ^ j) : ℝ) / ((2 : ℝ) ^ (k - j + 1))) =
      ∑ j ∈ Finset.range k,
        (p.parts.count (2 ^ j) : ℝ) * ((2 : ℝ) ^ j) / ((2 : ℝ) ^ (k + 1)) from
    Finset.sum_congr rfl fun j hj => by
      rw [div_eq_mul_one_div, two_pow_div_identity j k (Nat.le_of_lt (Finset.mem_range.mp hj)),
        ← mul_div_assoc]]
  rw [← Finset.sum_div]
  exact_mod_cast congrArg (fun x : ℕ => (x : ℝ) / ((2 : ℝ) ^ (k + 1)))
    (binaryPartition_sum_eq r k hr p hp)

/-- Collapse of the phase product: the product of exponentials raised to the
partition-dependent exponent equals `summandPhase r k`. -/
lemma phase_prod_eq (r k : ℕ) (hr : r < 2 ^ k) (p : Nat.Partition r)
    (hp : p ∈ binaryPartitions r) :
    (∏ j ∈ Finset.range k,
        Complex.exp (Real.pi * Complex.I / (2 ^ (k - j + 1) : ℕ))
          ^ ((r / 2 ^ j) - p.parts.count (2 ^ j))) =
      summandPhase r k := by
  have step1 : ∀ j ∈ Finset.range k,
      Complex.exp (Real.pi * Complex.I / (2 ^ (k - j + 1) : ℕ))
        ^ ((r / 2 ^ j) - p.parts.count (2 ^ j)) =
      Complex.exp (((r / 2 ^ j) - p.parts.count (2 ^ j) : ℕ) *
        (Real.pi * Complex.I / (2 ^ (k - j + 1) : ℕ))) := fun _ _ => by
    rw [← Complex.exp_nat_mul]
  rw [Finset.prod_congr rfl step1, ← Complex.exp_sum]
  unfold summandPhase
  congr 1
  have hle : ∀ j ∈ Finset.range k, p.parts.count (2 ^ j) ≤ r / 2 ^ j :=
    fun j _ => partition_count_pow_two_le_div r j p
  -- LHS to expanded form, factoring out π·I
  rw [show (∑ j ∈ Finset.range k,
        (((r / 2 ^ j) - p.parts.count (2 ^ j) : ℕ) : ℂ) *
          (Real.pi * Complex.I / (2 ^ (k - j + 1) : ℕ))) =
      Real.pi * Complex.I *
        ∑ j ∈ Finset.range k,
          (((r / 2 ^ j : ℕ) : ℂ) - ((p.parts.count (2 ^ j) : ℕ) : ℂ)) /
            ((2 : ℂ) ^ (k - j + 1)) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := hle j hj
    push_cast [Nat.cast_sub this]
    ring]
  congr 1
  -- Split sum into r/2^j and count parts
  rw [show (∑ j ∈ Finset.range k,
          (((r / 2 ^ j : ℕ) : ℂ) - ((p.parts.count (2 ^ j) : ℕ) : ℂ)) /
            ((2 : ℂ) ^ (k - j + 1))) =
      (∑ j ∈ Finset.range k, ((r / 2 ^ j : ℕ) : ℂ) / ((2 : ℂ) ^ (k - j + 1))) -
        (∑ j ∈ Finset.range k, ((p.parts.count (2 ^ j) : ℕ) : ℂ) / ((2 : ℂ) ^ (k - j + 1))) from by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun _ _ => by ring]
  have hsum_count :
      (∑ j ∈ Finset.range k,
          ((p.parts.count (2 ^ j) : ℕ) : ℂ) / ((2 : ℂ) ^ (k - j + 1))) =
      ((r : ℝ) / ((2 : ℝ) ^ (k + 1)) : ℝ) := by
    have := congrArg (fun x : ℝ => (x : ℂ)) (binaryPartition_count_div_sum r k hr p hp)
    simp only at this
    rw [← this]
    push_cast
    rfl
  rw [hsum_count]
  unfold summandPhaseT
  push_cast
  rfl

/-- **Main factorization.** For `r < 2^k` and `p ∈ binaryPartitions r`,
`eval(hBPartition r p) ζ_k = summandPhase r k * summandMag r k p`. -/
lemma hBPartition_eval_factorization (r k : ℕ) (hr : r < 2 ^ k) (p : Nat.Partition r)
    (hp : p ∈ binaryPartitions r) :
    ((hBPartition r p).map (Int.castRingHom ℂ)).eval
        (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) =
      summandPhase r k * (summandMag r k p : ℂ) := by
  rw [hBPartition_map_eval_eq_prod r k p, eq_prod_range_of_tail_one_both r k hr p]
  rw [Finset.prod_congr rfl fun j hj => by
    rw [one_add_zeta_pow_factor k j (Finset.mem_range.mp hj), mul_pow],
    Finset.prod_mul_distrib, phase_prod_eq r k hr p hp]
  congr 1
  rw [summandMag]
  push_cast
  rfl

/-- **Case `0 < r < 2^k`.** The sum over binary partitions is nonzero. -/
lemma sum_binaryPartitions_hBPartition_eval_pos_case
    (r k : ℕ) (hrpos : 0 < r) (hr : r < 2 ^ k) :
    (∑ p' ∈ binaryPartitions r,
        ((hBPartition r p').map (Int.castRingHom ℂ)).eval
          (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ)))) ≠ 0 := by
  rw [Finset.sum_congr rfl (fun p hp => hBPartition_eval_factorization r k hr p hp),
    ← Finset.mul_sum]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  rw [show (∑ p ∈ binaryPartitions r, ((summandMag r k p : ℂ))) =
        ((∑ p ∈ binaryPartitions r, summandMag r k p : ℝ) : ℂ) by push_cast; rfl]
  exact_mod_cast (Finset.sum_pos (fun p _ => summandMag_pos r k p)
    (binaryPartitions_nonempty r hrpos)).ne'

/-- The sum `∑_{p'} eval(hBPartition r p', ζ_k)` over binary partitions of `r`
is nonzero whenever `r < 2^k`. -/
lemma sum_binaryPartitions_hBPartition_eval_ne_zero (r k : ℕ) (hr : r < 2 ^ k) :
    (∑ p' ∈ binaryPartitions r,
        ((hBPartition r p').map (Int.castRingHom ℂ)).eval
          (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ)))) ≠ 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hrpos
  · rw [sum_binaryPartitions_hBPartition_eval_zero_case]
    exact one_ne_zero
  · exact sum_binaryPartitions_hBPartition_eval_pos_case r k hrpos hr

/-- The explicit nonzero constant arising from the factorization, equal to
`(∏_{j < k} (1 + ζ^(2^j))^((n/2^k) * 2^(k-j))) * (∏_{k < j ≤ n} (1 + ζ^(2^j))^(n/2^j))`,
where `ζ := exp(π i / 2^k)`. -/
noncomputable def explicitC (n k : ℕ) : ℂ :=
  (∏ j ∈ Finset.range k,
      (1 + (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) ^ (2 ^ j))
        ^ ((n / 2 ^ k) * 2 ^ (k - j))) *
  (∏ j ∈ Finset.Ioc k n,
      (1 + (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) ^ (2 ^ j))
        ^ (n / 2 ^ j))

/-- For `j < k`, the power `ζ^(2^j)` of `ζ := exp(π i / 2^k)` is **not** equal to `-1`. -/
lemma zetaRoot_pow_two_pow_lt_ne_neg_one (k j : ℕ) (h : j < k) :
    (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ)) : ℂ) ^ (2 ^ j) ≠ -1 := by
  intro hcontra
  have hpow : ((Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ)) : ℂ) ^ (2 ^ j)) ^ (2 ^ (k - j))
      = (-1 : ℂ) ^ (2 ^ (k - j)) := by rw [hcontra]
  rw [← pow_mul, show 2 ^ j * 2 ^ (k - j) = 2 ^ k by rw [← pow_add]; congr 1; omega,
    zetaRoot_pow_two_pow_eq_neg_one] at hpow
  have heven : Even (2 ^ (k - j)) := by
    rw [Nat.even_pow]
    exact ⟨even_two, by omega⟩
  rw [heven.neg_one_pow] at hpow
  exact absurd hpow (by norm_num)

/-- For `j < k`, `1 + ζ^(2^j) ≠ 0` (since `ζ^(2^j) ≠ -1`). -/
lemma one_add_zetaRoot_pow_two_pow_lt_ne_zero (k j : ℕ) (h : j < k) :
    (1 : ℂ) + (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ)) : ℂ) ^ (2 ^ j) ≠ 0 := fun h0 =>
  zetaRoot_pow_two_pow_lt_ne_neg_one k j h (by linear_combination h0)

lemma zetaRoot_pow_two_pow_gt_eq_one (k j : ℕ) (h : k < j) :
    (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ)) : ℂ) ^ (2 ^ j) = 1 := by
  rw [show (2 : ℕ) ^ j = 2 ^ k * 2 ^ (j - k) by rw [← pow_add]; congr 1; omega,
    pow_mul, zetaRoot_pow_two_pow_eq_neg_one]
  have heven : Even (2 ^ (j - k)) := by
    rw [Nat.even_pow]
    exact ⟨even_two, by omega⟩
  exact heven.neg_one_pow

/-- For `j > k`, `1 + ζ^(2^j) = 2 ≠ 0`. -/
lemma one_add_zetaRoot_pow_two_pow_gt_ne_zero (k j : ℕ) (h : k < j) :
    (1 : ℂ) + (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ)) : ℂ) ^ (2 ^ j) ≠ 0 := by
  rw [zetaRoot_pow_two_pow_gt_eq_one k j h]
  norm_num

/-- The explicit constant `explicitC n k` is nonzero. -/
lemma explicitC_ne_zero (n k : ℕ) : explicitC n k ≠ 0 :=
  mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun j hj =>
      pow_ne_zero _ (one_add_zetaRoot_pow_two_pow_lt_ne_zero k j (Finset.mem_range.mp hj)))
    (Finset.prod_ne_zero_iff.mpr fun j hj =>
      pow_ne_zero _ (one_add_zetaRoot_pow_two_pow_gt_ne_zero k j (Finset.mem_Ioc.mp hj).1))

lemma k_mem_range_of_div_pos (n k : ℕ) (hk : n / 2 ^ k > 0) :
    k ∈ Finset.range (n + 1) := by
  have : 2 ^ k ≤ n := ((Nat.div_pos_iff).mp hk).2
  have : k < 2 ^ k := Nat.lt_two_pow_self
  grind

/-- If `p.parts.count (2^k) ≠ n / 2^k`, then `hBPartition n p` evaluated at `ζ_k` is zero. -/
lemma hBPartition_map_eval_eq_zero_of_count_ne (n k : ℕ) (hk : n / 2 ^ k > 0)
    (p : Nat.Partition n) (hcount : p.parts.count (2 ^ k) ≠ n / 2 ^ k) :
    ((hBPartition n p).map (Int.castRingHom ℂ)).eval
        (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) = 0 := by
  have hm_ne : (n / 2 ^ k) - p.parts.count (2 ^ k) ≠ 0 :=
    Nat.sub_ne_zero_of_lt (lt_of_le_of_ne (partition_count_pow_two_le_div n k p) hcount)
  rw [hBPartition, Polynomial.map_prod, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (k_mem_range_of_div_pos n k hk)
  simp only [Polynomial.map_pow, Polynomial.eval_pow, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_X]
  rw [zetaRoot_pow_two_pow_eq_neg_one k, add_neg_cancel]
  exact zero_pow hm_ne

/-- After pushing `map` and `eval ζ_k` through the sum defining `numB n`,
only partitions with `p.parts.count (2^k) = n / 2^k` contribute. -/
lemma numB_map_eval_eq_contrib_sum (n k : ℕ) (hk : n / 2 ^ k > 0) :
    ((numB n).map (Int.castRingHom ℂ)).eval
        (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) =
      ∑ p ∈ (binaryPartitions n).filter (fun p => p.parts.count (2 ^ k) = n / 2 ^ k),
        ((hBPartition n p).map (Int.castRingHom ℂ)).eval
          (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) := by
  rw [numB, Polynomial.map_sum, Polynomial.eval_finset_sum]
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) fun p hp hp_not =>
    hBPartition_map_eval_eq_zero_of_count_ne n k hk p
      fun heq => hp_not (Finset.mem_filter.mpr ⟨hp, heq⟩)

/-- The lift function: given a partition `p'` of `r := n % 2^k`, produce a partition
of `n` by adjoining `n / 2^k` copies of `2^k` to `p'.parts`. -/
noncomputable def liftPartition (n k : ℕ) (p' : Nat.Partition (n % 2 ^ k)) :
    Nat.Partition n where
  parts := p'.parts + Multiset.replicate (n / 2 ^ k) (2 ^ k)
  parts_pos hi := by
    rw [Multiset.mem_add] at hi
    rcases hi with hi | hi
    · exact p'.parts_pos hi
    · rw [Multiset.eq_of_mem_replicate hi]
      positivity
  parts_sum := by
    rw [Multiset.sum_add, p'.parts_sum, Multiset.sum_replicate, smul_eq_mul]
    conv_lhs => rw [add_comm, mul_comm]
    exact Nat.div_add_mod n (2 ^ k)

lemma powersOfTwoUpTo_mono {m n : ℕ} (hmn : m ≤ n) {i : ℕ}
    (hi : i ∈ powersOfTwoUpTo m) : i ∈ powersOfTwoUpTo n := by
  rw [powersOfTwoUpTo, Finset.mem_image] at hi ⊢
  obtain ⟨k, hk, rfl⟩ := hi
  exact ⟨k, Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega), rfl⟩

/-- The lift `liftPartition n k p'` of a binary partition of `r = n % 2^k` is itself binary. -/
lemma liftPartition_isBinary (n k : ℕ) (hk : n / 2 ^ k > 0)
    (p' : Nat.Partition (n % 2 ^ k)) (hp' : p' ∈ binaryPartitions (n % 2 ^ k)) :
    IsBinaryPartition (liftPartition n k p') := by
  have hp'_bin : IsBinaryPartition p' := (Finset.mem_filter.mp hp').2
  intro i hi
  change i ∈ p'.parts + Multiset.replicate (n / 2 ^ k) (2 ^ k) at hi
  rcases Multiset.mem_add.mp hi with hi | hi
  · exact powersOfTwoUpTo_mono (Nat.mod_le n (2 ^ k)) (hp'_bin i hi)
  · rw [Multiset.eq_of_mem_replicate hi]
    exact Finset.mem_image.mpr ⟨k, k_mem_range_of_div_pos n k hk, rfl⟩

/-- The lift increases `count (2^k)` by exactly `n / 2 ^ k`. -/
lemma liftPartition_count_2pow_k (n k : ℕ) (p' : Nat.Partition (n % 2 ^ k)) :
    (liftPartition n k p').parts.count (2 ^ k) = n / 2 ^ k := by
  have hp'_count_zero : p'.parts.count (2 ^ k) = 0 := by
    have hle := partition_count_pow_two_le_div (n % 2 ^ k) k p'
    rw [Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _))] at hle
    omega
  show (p'.parts + Multiset.replicate (n / 2 ^ k) (2 ^ k)).count (2 ^ k) = n / 2 ^ k
  rw [Multiset.count_add, hp'_count_zero, Multiset.count_replicate_self, zero_add]

/-- For `j ≠ k`, the lift preserves the multiplicity at `2^j`. -/
lemma liftPartition_count_other (n k j : ℕ) (hjk : j ≠ k)
    (p' : Nat.Partition (n % 2 ^ k)) :
    (liftPartition n k p').parts.count (2 ^ j) = p'.parts.count (2 ^ j) := by
  have hne : (2 ^ k : ℕ) ≠ 2 ^ j :=
    fun h => hjk (Nat.pow_right_injective (by norm_num) h).symm
  simp [liftPartition, Multiset.count_add, Multiset.count_replicate, hne]

/-- `liftPartition n k` is injective. -/
lemma liftPartition_injective (n k : ℕ) :
    Function.Injective (liftPartition n k) := fun p₁ p₂ h => by
  apply Nat.Partition.ext
  exact add_right_cancel (show (liftPartition n k p₁).parts = (liftPartition n k p₂).parts by rw [h])

/-- Given a partition `p` of `n` whose multiplicity of `2^k` equals `n / 2^k`,
the multiset `Multiset.replicate (n/2^k) (2^k)` is contained in `p.parts`. -/
lemma replicate_le_parts (n k : ℕ) (p : Nat.Partition n)
    (hpc : p.parts.count (2 ^ k) = n / 2 ^ k) :
    Multiset.replicate (n / 2 ^ k) (2 ^ k) ≤ p.parts := by
  rw [Multiset.le_iff_count]
  intro a
  by_cases h : a = 2 ^ k
  · rw [h, Multiset.count_replicate_self, hpc]
  · rw [Multiset.count_replicate, if_neg (Ne.symm h)]
    exact Nat.zero_le _

/-- Given a partition `p` of `n` with `p.parts.count (2^k) = n / 2^k`,
the sum of the stripped multiset `p.parts - Multiset.replicate (n/2^k) (2^k)` equals
`n % 2^k`. -/
lemma stripped_sum_eq_mod (n k : ℕ) (p : Nat.Partition n)
    (hpc : p.parts.count (2 ^ k) = n / 2 ^ k) :
    (p.parts - Multiset.replicate (n / 2 ^ k) (2 ^ k)).sum = n % 2 ^ k := by
  have hsum : (p.parts - Multiset.replicate (n / 2 ^ k) (2 ^ k)).sum +
      (n / 2 ^ k) * 2 ^ k = n := by
    have := congr_arg Multiset.sum (tsub_add_cancel_of_le (replicate_le_parts n k p hpc))
    rwa [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, p.parts_sum] at this
  have := Nat.div_add_mod' n (2 ^ k)
  omega

/-- Every part in the stripped multiset `p.parts - Multiset.replicate (n/2^k) (2^k)`
is positive, because it remains a part of `p`. -/
lemma stripped_parts_pos (n k : ℕ) (p : Nat.Partition n) :
    ∀ i ∈ p.parts - Multiset.replicate (n / 2 ^ k) (2 ^ k), 0 < i := fun _ hi =>
  p.parts_pos (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi)

/-- Given a binary partition `p` of `n` with `n/2^k` copies of `2^k`,
the stripped multiset is contained in `powersOfTwoUpTo (n % 2^k)`. -/
lemma stripped_mem_powersOfTwoUpTo (n k : ℕ) (p : Nat.Partition n)
    (hpb : ∀ i ∈ p.parts, i ∈ powersOfTwoUpTo n)
    (hpc : p.parts.count (2 ^ k) = n / 2 ^ k) :
    ∀ i ∈ p.parts - Multiset.replicate (n / 2 ^ k) (2 ^ k),
      i ∈ powersOfTwoUpTo (n % 2 ^ k) := by
  intro i hi
  have hi_pow : i ∈ powersOfTwoUpTo n :=
    hpb i (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi)
  rw [powersOfTwoUpTo, Finset.mem_image] at hi_pow
  obtain ⟨j, _, rfl⟩ := hi_pow
  have hi_le_sum : 2 ^ j ≤ (p.parts - Multiset.replicate (n / 2 ^ k) (2 ^ k)).sum :=
    Multiset.single_le_sum (s := p.parts - Multiset.replicate (n / 2 ^ k) (2 ^ k))
      (fun x hx => (stripped_parts_pos n k p x hx).le) (2 ^ j) hi
  rw [stripped_sum_eq_mod n k p hpc] at hi_le_sum
  have : j < 2 ^ j := Nat.lt_two_pow_self
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩

lemma liftPartition_surjOn (n k : ℕ)
    (p : Nat.Partition n) (hpb : p ∈ binaryPartitions n)
    (hpc : p.parts.count (2 ^ k) = n / 2 ^ k) :
    ∃ p' ∈ binaryPartitions (n % 2 ^ k), liftPartition n k p' = p := by
  set R : Multiset ℕ := Multiset.replicate (n / 2 ^ k) (2 ^ k)
  have hle : R ≤ p.parts := replicate_le_parts n k p hpc
  refine ⟨{ parts := p.parts - R
            parts_pos := fun hi => stripped_parts_pos n k p _ hi
            parts_sum := stripped_sum_eq_mod n k p hpc },
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            stripped_mem_powersOfTwoUpTo n k p (Finset.mem_filter.mp hpb).2 hpc⟩, ?_⟩
  apply Nat.Partition.ext
  exact (show (p.parts - R) + R = p.parts from Multiset.sub_add_cancel hle)

/-- For `j ≤ k`, `n / 2^j = (n / 2^k) * 2^(k-j) + (n % 2^k) / 2^j`. -/
lemma div_two_pow_split (n k j : ℕ) (hj : j ≤ k) :
    n / 2 ^ j = (n / 2 ^ k) * 2 ^ (k - j) + (n % 2 ^ k) / 2 ^ j := by
  have h2j_pos : 0 < (2 : ℕ) ^ j := Nat.two_pow_pos j
  have h2k_eq : (2 : ℕ) ^ k = 2 ^ (k - j) * 2 ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  conv_lhs => rw [← Nat.div_add_mod n (2 ^ k)]
  rw [h2k_eq, show 2 ^ (k - j) * 2 ^ j * (n / (2 ^ (k - j) * 2 ^ j)) +
      n % (2 ^ (k - j) * 2 ^ j) =
      n % (2 ^ (k - j) * 2 ^ j) + (n / (2 ^ (k - j) * 2 ^ j)) * 2 ^ (k - j) * 2 ^ j by ring,
    Nat.add_mul_div_right _ _ h2j_pos]
  ring

lemma high_product_eq_explicitC_high (n k : ℕ)
    (p' : Nat.Partition (n % 2 ^ k)) :
    ∏ j ∈ (Finset.range (n + 1)).filter (fun j => k < j),
        (1 + (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) ^ (2 ^ j))
          ^ ((n / 2 ^ j) - (liftPartition n k p').parts.count (2 ^ j)) =
      ∏ j ∈ Finset.Ioc k n,
        (1 + (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) ^ (2 ^ j))
          ^ (n / 2 ^ j) := by
  have hset : (Finset.range (n + 1)).filter (fun j => k < j) = Finset.Ioc k n := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  rw [hset]
  refine Finset.prod_congr rfl fun j hj => ?_
  obtain ⟨hkj, _⟩ := Finset.mem_Ioc.mp hj
  have hcount : (liftPartition n k p').parts.count (2 ^ j) = 0 := by
    rw [liftPartition_count_other n k j (Nat.ne_of_gt hkj) p']
    refine Multiset.count_eq_zero_of_notMem fun hmem => ?_
    have hr_lt : n % 2 ^ k < 2 ^ j := lt_trans (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_lt_pow_right (by decide : 1 < 2) hkj)
    exact absurd (Nat.Partition.le_of_mem_parts hmem) (Nat.not_le.mpr hr_lt)
  rw [hcount, Nat.sub_zero]

/-- Pointwise exponent identity: for `j < k`,
`(n/2^j) - count = (n/2^k) * 2^(k-j) + ((n%2^k)/2^j - count)`. -/
lemma exponent_split (n k j : ℕ) (hjk : j < k) (p' : Nat.Partition (n % 2 ^ k)) :
    (n / 2 ^ j) - (liftPartition n k p').parts.count (2 ^ j) =
      (n / 2 ^ k) * 2 ^ (k - j) + ((n % 2 ^ k) / 2 ^ j - p'.parts.count (2 ^ j)) := by
  rw [liftPartition_count_other n k j (Nat.ne_of_lt hjk) p', div_two_pow_split n k j hjk.le]
  have := partition_count_pow_two_le_div (n % 2 ^ k) j p'
  omega

-- Main theorem

/-- The low product (j < k) splits into the low part of `explicitC n k` times
the j<k part of the RHS evaluation. -/
lemma low_product_split (n k : ℕ) (hk : n / 2 ^ k > 0)
    (p' : Nat.Partition (n % 2 ^ k)) :
    ∏ j ∈ (Finset.range (n + 1)).filter (fun j => j < k),
        (1 + (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) ^ (2 ^ j))
          ^ ((n / 2 ^ j) - (liftPartition n k p').parts.count (2 ^ j)) =
      (∏ j ∈ Finset.range k,
        (1 + (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) ^ (2 ^ j))
          ^ ((n / 2 ^ k) * 2 ^ (k - j))) *
      (∏ j ∈ Finset.range k,
        (1 + (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) ^ (2 ^ j))
          ^ ((n % 2 ^ k) / 2 ^ j - p'.parts.count (2 ^ j))) := by
  have hkn : k ≤ n := by
    have : 2 ^ k ≤ n := ((Nat.div_pos_iff).mp hk).2
    have : k < 2 ^ k := Nat.lt_two_pow_self
    omega
  have hfilter : ((Finset.range (n + 1)).filter (fun j => j < k)) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hjk : j < k := Finset.mem_range.mp hj
  rw [exponent_split n k j hjk p', pow_add]

/-- `Finset.range (n+1)` partitions into `< k`, `= k`, `> k` when `k ≤ n`.
This expresses the splitting of a product over `Finset.range (n+1)`. -/
lemma prod_range_split_at_k {M : Type*} [CommMonoid M] (n k : ℕ)
    (hk_mem : k ∈ Finset.range (n + 1)) (f : ℕ → M) :
    ∏ j ∈ Finset.range (n + 1), f j =
      (∏ j ∈ (Finset.range (n + 1)).filter (fun j => j < k), f j) *
      f k *
      (∏ j ∈ (Finset.range (n + 1)).filter (fun j => k < j), f j) := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not _ (fun j => j < k)]
  have hsplit : (Finset.range (n + 1)).filter (fun j => ¬ j < k) =
      {k} ∪ (Finset.range (n + 1)).filter (fun j => k < j) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_singleton, not_lt]
    have hkn : k < n + 1 := Finset.mem_range.mp hk_mem
    omega
  rw [hsplit, Finset.prod_union (by simp), Finset.prod_singleton, mul_assoc]

/-- Per-summand factorization: for `p' ∈ binaryPartitions (n % 2^k)`,
the evaluation of `hBPartition n (liftPartition n k p')` at `ζ_k` equals
`explicitC n k` times the evaluation of `hBPartition (n % 2^k) p'` at `ζ_k`. -/
lemma hBPartition_lift_eval_eq_explicitC_mul (n k : ℕ)
    (hk : n / 2 ^ k > 0) (p' : Nat.Partition (n % 2 ^ k)) :
    ((hBPartition n (liftPartition n k p')).map (Int.castRingHom ℂ)).eval
        (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) =
      explicitC n k *
        ((hBPartition (n % 2 ^ k) p').map (Int.castRingHom ℂ)).eval
          (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) := by
  rw [hBPartition_map_eval_eq_prod n k (liftPartition n k p'),
    prod_range_split_at_k n k (k_mem_range_of_div_pos n k hk),
    high_product_eq_explicitC_high n k p',
    show (1 + (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) ^ (2 ^ k))
        ^ ((n / 2 ^ k) - (liftPartition n k p').parts.count (2 ^ k)) = 1 by
      rw [liftPartition_count_2pow_k n k p', Nat.sub_self, pow_zero],
    low_product_split n k hk p',
    hBPartition_eval_eq_range_k (n % 2 ^ k) k (Nat.mod_lt n (Nat.two_pow_pos _)) p']
  unfold explicitC
  ring

lemma contrib_sum_eq_explicitC_mul_strip_sum (n k : ℕ) (hk : n / 2 ^ k > 0) :
    ∑ p ∈ (binaryPartitions n).filter (fun p => p.parts.count (2 ^ k) = n / 2 ^ k),
        ((hBPartition n p).map (Int.castRingHom ℂ)).eval
          (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) =
      explicitC n k *
        (∑ p' ∈ binaryPartitions (n % 2 ^ k),
          ((hBPartition (n % 2 ^ k) p').map (Int.castRingHom ℂ)).eval
            (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ)))) := by
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_bij (i := fun p' _ => liftPartition n k p') ?_ ?_ ?_ ?_
  · intro p' hp'
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, liftPartition_isBinary n k hk p' hp'⟩,
      liftPartition_count_2pow_k n k p'⟩
  · intro p₁ _ p₂ _ heq
    exact liftPartition_injective n k heq
  · intro p hp
    obtain ⟨hpb, hpc⟩ := Finset.mem_filter.mp hp
    obtain ⟨p', hp'mem, hp'eq⟩ := liftPartition_surjOn n k p hpb hpc
    exact ⟨p', hp'mem, hp'eq⟩
  · intro p' hp'
    exact (hBPartition_lift_eval_eq_explicitC_mul n k hk p').symm

/-- **Core nonvanishing lemma.** For `n ≥ 1` and `k` with `n / 2^k > 0`, the
polynomial `(numB n).map (Int.castRingHom ℂ)` evaluated at `ζ_k = exp(π i / 2^k)`
is nonzero. -/
lemma numB_map_eval_at_zetaRoot_ne_zero (n k : ℕ) (hk : n / 2 ^ k > 0) :
    ((numB n).map (Int.castRingHom ℂ)).eval
        (Complex.exp (Real.pi * Complex.I / (2 ^ k : ℕ))) ≠ 0 := by
  rw [numB_map_eval_eq_contrib_sum n k hk,
    contrib_sum_eq_explicitC_mul_strip_sum n k hk]
  exact mul_ne_zero (explicitC_ne_zero n k)
    (sum_binaryPartitions_hBPartition_eval_ne_zero (n % 2 ^ k) k
      (Nat.mod_lt _ (Nat.two_pow_pos _)))

/-- Divisibility by `(1 + X^(2^k))` over `ℚ` would force `eval(numB) ζ_k = 0`,
contradicting `numB_map_eval_at_zetaRoot_ne_zero`. -/
lemma not_one_add_X_pow_two_pow_dvd_numB_rat (n k : ℕ) (hk : n / 2 ^ k > 0) :
    ¬ ((1 + X ^ (2 ^ k) : ℚ[X])) ∣ ((numB n).map (Int.castRingHom ℚ)) := by
  intro hpq
  have hpq_C : ((1 + X ^ (2 ^ k) : ℚ[X])).map (algebraMap ℚ ℂ) ∣
      ((numB n).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) := Polynomial.map_dvd _ hpq
  rw [show ((1 + X ^ (2 ^ k) : ℚ[X])).map (algebraMap ℚ ℂ) = (1 + X ^ (2 ^ k) : ℂ[X]) by
      simp [Polynomial.map_add, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X],
    show ((numB n).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) =
        (numB n).map (Int.castRingHom ℂ) by
      rw [Polynomial.map_map]
      rfl] at hpq_C
  obtain ⟨r, hr⟩ := hpq_C
  apply numB_map_eval_at_zetaRoot_ne_zero n k hk
  rw [hr, Polynomial.eval_mul, one_add_X_pow_two_pow_eval_zetaRoot k, zero_mul]

/-- Core lemma: coprimality of `numB n` with the base factor `1 + X^(2^k)` over `ℚ`. -/
lemma coprime_with_base_factor (n k : ℕ) (hk : n / 2 ^ k > 0) :
    IsCoprime ((numB n).map (Int.castRingHom ℚ))
      ((1 + X ^ (2 ^ k) : ℚ[X])) := by
  rw [isCoprime_comm, (one_add_X_pow_two_pow_irreducible_rat k).coprime_iff_not_dvd]
  exact not_one_add_X_pow_two_pow_dvd_numB_rat n k hk

/-- **Conjecture 5.** -/
theorem conj5 (n : ℕ) (_hn : 1 ≤ n) :
    IsCoprime
      ((numB n).map (Int.castRingHom ℚ))
      ((denB n).map (Int.castRingHom ℚ)) := by
  rw [denB_map_eq]
  refine IsCoprime.prod_right fun k _ => ?_
  by_cases hq : n / 2 ^ k = 0
  · rw [hq, pow_zero]
    exact isCoprime_one_right
  · exact (coprime_with_base_factor n k (Nat.pos_of_ne_zero hq)).pow_right
