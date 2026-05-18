import Mathlib

/-!
# Proof of Conjecture 9 (Ballantine–Beck–Feigon–Maurischat)

The work is decomposed into helper lemmas mirroring Steps 2–7 of the
informal proof:

* `allOnesPart` : the all-ones ternary partition of `m`.
* `card_parts_lt_of_ne_allOnes` : any other ternary partition has fewer
  than `m` parts.
* `gcdHTernary_dvd_hTernary` : the gcd divides every summand.
* `numT_eq_sum_divByMonic` : the sum/gcd quotient distributes.
* `quotient_eval_neg_one_eq_zero_of_ne_allOnes` : non-all-ones quotients
  vanish at `-1`.
* `quotient_allOnes_eval_neg_one_eq_pow_val3` : the all-ones quotient at
  `-1` equals `3^(val3 m!)`.
* `sSeq_eq_pow_val3_factorial` : combines the above using
  `Finset.sum_eq_single`.
-/

open Polynomial Nat BigOperators

namespace Conj9

/-- A natural number is a power of $3$ (including $3^0 = 1$). -/
def IsPow3 (i : ℕ) : Prop := ∃ k ≤ i, i = 3 ^ k

instance (i : ℕ) : Decidable (IsPow3 i) := by
  unfold IsPow3
  infer_instance

/-- Multiplicity of `i` as a part of the partition `p` of `n`. -/
def partMult {n : ℕ} (p : Nat.Partition n) (i : ℕ) : ℕ := p.parts.count i

/-- A partition is *ternary* if every one of its parts is a power of $3$. -/
def IsTernary {n : ℕ} (p : Nat.Partition n) : Prop :=
  ∀ i ∈ p.parts, IsPow3 i

instance {n : ℕ} (p : Nat.Partition n) : Decidable (IsTernary p) :=
  Multiset.decidableDforallMultiset

/-- The (finite) set $\mathcal{T}(n)$ of ternary partitions of `n`. -/
def ternaryPartitions (n : ℕ) : Finset (Nat.Partition n) :=
  Finset.univ.filter IsTernary

/-- The auxiliary polynomial
$h^{(n)}_{T,\lambda}(x) = \prod_{k} (1 + x^{3^k})^{\lfloor n/3^k \rfloor - m_\lambda(3^k)}$. -/
noncomputable def hTernary (n : ℕ) (p : Nat.Partition n) : Polynomial ℤ :=
  ∏ k ∈ Finset.range (n + 1),
    (1 + Polynomial.X ^ (3 ^ k)) ^ (n / 3 ^ k - partMult p (3 ^ k))

/-- $G_T(n,x) := \gcd_{\lambda \in \mathcal{T}(n)} h^{(n)}_{T,\lambda}(x)$. -/
noncomputable def gcdHTernary (n : ℕ) : Polynomial ℤ :=
  (ternaryPartitions n).gcd (hTernary n)

/-- The numerator polynomial
$\operatorname{num}_T(n,x) := \frac{1}{G_T(n,x)} \sum_\lambda h^{(n)}_{T,\lambda}(x)$. -/
noncomputable def numT (n : ℕ) : Polynomial ℤ :=
  (∑ p ∈ ternaryPartitions n, hTernary n p) /ₘ (gcdHTernary n)

/-- The sequence $s(n) := \operatorname{num}_T(n,-1)$. -/
noncomputable def sSeq (n : ℕ) : ℤ := (numT n).eval (-1)

/-- The 3-adic valuation $\operatorname{val}_3$. -/
def val3 (m : ℕ) : ℕ := padicValNat 3 m

/-! ### The all-ones partition -/

/-- The "all-ones" partition of `m`, i.e. the partition whose multiset of
parts is `Multiset.replicate m 1`.  This is the unique partition of `m`
into `m` parts. -/
def allOnesPart (m : ℕ) : Nat.Partition m where
  parts := Multiset.replicate m 1
  parts_pos := by
    intro i hi
    rw [Multiset.mem_replicate] at hi
    omega
  parts_sum := by simp [Multiset.sum_replicate]

/-- The all-ones partition is ternary. -/
lemma allOnesPart_mem_ternary (m : ℕ) :
    allOnesPart m ∈ ternaryPartitions m := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro i hi
  have h : i = 1 := by
    rw [allOnesPart] at hi
    simp only [Multiset.mem_replicate] at hi
    aesop
  exact ⟨0, by norm_num, by simp [h]⟩


/-! ### Helper for `card_parts_lt_of_ne_allOnes` -/
namespace Aux_card_parts_lt_of_ne_allOnes



lemma multiset_card_le_sum (s : Multiset ℕ) (h : ∀ a ∈ s, 1 ≤ a) :
    s.card ≤ s.sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.card_cons, Multiset.sum_cons]
    have ha : 1 ≤ a := h a (Multiset.mem_cons_self _ _)
    have hs : ∀ x ∈ s, 1 ≤ x := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    linarith [ih hs]

lemma partition_card_le (m : ℕ) (p : Nat.Partition m) : p.parts.card ≤ m := by
  have h1 : p.parts.sum = m := p.parts_sum
  have h2 : ∀ a ∈ p.parts, 1 ≤ a := fun a ha => p.parts_pos ha
  calc p.parts.card ≤ p.parts.sum := multiset_card_le_sum _ h2
    _ = m := h1

lemma parts_eq_replicate_of_all_one (m : ℕ) (p : Nat.Partition m)
    (h : ∀ i ∈ p.parts, i = 1) : p.parts = Multiset.replicate m 1 := by
  have hsum : p.parts.sum = m := p.parts_sum
  have hreplicate : p.parts = Multiset.replicate (Multiset.card p.parts) 1 := by
    refine Multiset.eq_replicate_card.mpr ?_
    intro b hb
    exact h b hb
  have hcard : Multiset.card p.parts = m := by
    have hh : p.parts.sum = Multiset.card p.parts := by
      rw [hreplicate]; simp
    omega
  rw [hreplicate, hcard]

lemma all_parts_one_of_card_eq (m : ℕ) (p : Nat.Partition m)
    (h : p.parts.card = m) : ∀ i ∈ p.parts, i = 1 := by
  have hsum : p.parts.sum = m := p.parts_sum
  have hpos : ∀ a ∈ p.parts, 1 ≤ a := fun a ha => p.parts_pos ha
  intro i hi
  by_contra hne
  have hi1 : 1 ≤ i := hpos i hi
  have hi2 : 2 ≤ i := by omega
  classical
  have hcons : i ::ₘ p.parts.erase i = p.parts := Multiset.cons_erase hi
  set t := p.parts.erase i with ht
  have hcard : t.card = m - 1 := by
    have h1 := Multiset.card_erase_of_mem hi
    rw [h, Nat.pred_eq_sub_one] at h1
    rw [ht]; exact h1
  have hsum_split : t.sum + i = m := by
    have heq : (i ::ₘ t).sum = p.parts.sum := by rw [hcons]
    rw [Multiset.sum_cons, hsum] at heq
    omega
  have ht_pos : ∀ a ∈ t, 1 ≤ a := by
    intro a ha
    apply hpos a
    rw [← hcons]
    exact Multiset.mem_cons_of_mem ha
  have ht_card_le : t.card ≤ t.sum := multiset_card_le_sum t ht_pos
  have hm_pos : 1 ≤ m := by
    have hne0 : p.parts ≠ 0 := fun heq => by simp [heq] at hi
    have : 1 ≤ p.parts.card := Multiset.card_pos.mpr hne0
    omega
  omega

lemma eq_allOnes_of_parts_eq (m : ℕ) (p : Nat.Partition m)
    (h : p.parts = Multiset.replicate m 1) : p = allOnesPart m := by
  apply Nat.Partition.ext
  simp_all [allOnesPart]

/-- **Key counting lemma (Step 2.1).**  Any ternary partition different from
the all-ones partition has fewer than `m` parts. -/
lemma card_parts_lt_of_ne_allOnes (m : ℕ) (p : Nat.Partition m)
    (_hp : p ∈ ternaryPartitions m) (hne : p ≠ allOnesPart m) :
    p.parts.card < m := by
  rcases lt_or_eq_of_le (partition_card_le m p) with h | h
  · exact h
  · exact absurd (eq_allOnes_of_parts_eq m p
      (parts_eq_replicate_of_all_one m p (all_parts_one_of_card_eq m p h))) hne

end Aux_card_parts_lt_of_ne_allOnes




/-! ### Helper for `gcdHTernary_monic` -/
namespace Aux_gcdHTernary_monic

/-- The all-ones partition belongs to `ternaryPartitions m`. -/
lemma allOnesPart_mem_ternary (m : ℕ) :
    allOnesPart m ∈ ternaryPartitions m := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro i hi
  have h : i = 1 := by
    rw [allOnesPart] at hi
    simp only [Multiset.mem_replicate] at hi
    aesop
  exact ⟨0, by norm_num, by simp [h]⟩

/-- For every `k`, the polynomial `1 + X^(3^k)` is monic in `ℤ[X]`. -/
lemma monic_one_add_X_pow_three_pow (k : ℕ) :
    (1 + Polynomial.X ^ (3 ^ k) : Polynomial ℤ).Monic := by
  rw [show (1 + Polynomial.X ^ (3 ^ k) : Polynomial ℤ) = Polynomial.X ^ (3 ^ k) + 1 from by ring]
  apply Polynomial.monic_X_pow_add
  simp [pow_pos]

/-- For every `m` and partition `p` of `m`, the polynomial `hTernary m p`
is monic, being a product of powers of monic polynomials. -/
lemma hTernary_monic (m : ℕ) (p : Nat.Partition m) :
    (hTernary m p).Monic := by
  unfold hTernary
  apply Polynomial.monic_prod_of_monic
  intro k _
  exact (monic_one_add_X_pow_three_pow k).pow _

/-- A normalized non-zero polynomial in `ℤ[X]` has positive leading coefficient. -/
lemma leadingCoeff_pos_of_normalize_eq_self
    {g : Polynomial ℤ} (hnorm : normalize g = g) (hg : g ≠ 0) :
    0 < g.leadingCoeff := by
  have hlc : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg
  have hnorm_lc : normalize g.leadingCoeff = g.leadingCoeff := by
    have := Polynomial.leadingCoeff_normalize g
    rw [hnorm] at this
    exact this.symm
  have h0 : 0 ≤ g.leadingCoeff := Int.nonneg_of_normalize_eq_self hnorm_lc
  exact h0.lt_of_ne (Ne.symm hlc)

lemma monic_of_normalize_eq_self_of_dvd_monic
    {g p : Polynomial ℤ} (hnorm : normalize g = g)
    (hdvd : g ∣ p) (hp : p.Monic) : g.Monic := by
  have hp_ne : p ≠ 0 := hp.ne_zero
  have hg_ne : g ≠ 0 := fun h => hp_ne (by rw [h] at hdvd; exact zero_dvd_iff.mp hdvd)
  have hlc_dvd : g.leadingCoeff ∣ (1 : ℤ) := by
    have := Polynomial.leadingCoeff_dvd_leadingCoeff hdvd
    rwa [hp.leadingCoeff] at this
  have hlc_unit : IsUnit g.leadingCoeff := isUnit_of_dvd_one hlc_dvd
  have hlc_cases : g.leadingCoeff = 1 ∨ g.leadingCoeff = -1 := Int.isUnit_iff.mp hlc_unit
  have hlc_pos : 0 < g.leadingCoeff :=
    leadingCoeff_pos_of_normalize_eq_self hnorm hg_ne
  rcases hlc_cases with h | h
  · exact h
  · exfalso; rw [h] at hlc_pos; norm_num at hlc_pos

lemma normalize_finset_gcd_polynomial_int
    {α : Type*} (s : Finset α) (f : α → Polynomial ℤ) :
    normalize (s.gcd f) = s.gcd f :=
  Finset.normalize_gcd

lemma finset_gcd_monic_of_forall_monic
    {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (f : α → Polynomial ℤ) (hmon : ∀ a ∈ s, (f a).Monic) :
    (s.gcd f).Monic := by
  obtain ⟨a₀, ha₀⟩ := hs
  have hdvd : s.gcd f ∣ f a₀ := Finset.gcd_dvd ha₀
  have hnorm : normalize (s.gcd f) = s.gcd f :=
    normalize_finset_gcd_polynomial_int s f
  exact monic_of_normalize_eq_self_of_dvd_monic hnorm hdvd (hmon a₀ ha₀)

/-- The gcd `gcdHTernary m` is monic. -/
lemma gcdHTernary_monic (m : ℕ) : (gcdHTernary m).Monic := by
  unfold gcdHTernary
  exact finset_gcd_monic_of_forall_monic
    (ternaryPartitions m)
    ⟨allOnesPart m, allOnesPart_mem_ternary m⟩
    (hTernary m)
    (fun p _ => hTernary_monic m p)

end Aux_gcdHTernary_monic


/-! ### Helper for `numT_eq_sum_divByMonic` -/
namespace Aux_numT_eq_sum_divByMonic

open Aux_gcdHTernary_monic (hTernary_monic allOnesPart_mem_ternary gcdHTernary_monic)

lemma gcdHTernary_dvd_hTernary (m : ℕ) (p : Nat.Partition m)
    (hp : p ∈ ternaryPartitions m) :
    gcdHTernary m ∣ hTernary m p :=
  Finset.gcd_dvd hp

/-- If `g` is monic and divides `p`, then `p = (p /ₘ g) * g`. -/
lemma eq_divByMonic_mul_of_dvd
    (p g : Polynomial ℤ) (hg : g.Monic) (hd : g ∣ p) :
    p = (p /ₘ g) * g := by
  have h_mod : p %ₘ g = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hg).mpr hd
  have h_sum : p %ₘ g + g * (p /ₘ g) = p := Polynomial.modByMonic_add_div p hg
  rw [h_mod, zero_add, mul_comm] at h_sum
  exact h_sum.symm

lemma mul_divByMonic_self
    (q g : Polynomial ℤ) (hg : g.Monic) : (q * g) /ₘ g = q := by
  rw [mul_comm]
  exact Polynomial.mul_divByMonic_cancel_left _ hg

lemma sum_divByMonic_of_dvd {α : Type*} (S : Finset α)
    (f : α → Polynomial ℤ) (g : Polynomial ℤ)
    (hg : g.Monic) (hdvd : ∀ a ∈ S, g ∣ f a) :
    (∑ a ∈ S, f a) /ₘ g = ∑ a ∈ S, (f a /ₘ g) := by
  have hsum : (∑ a ∈ S, f a) = (∑ a ∈ S, f a /ₘ g) * g := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro a ha
    exact eq_divByMonic_mul_of_dvd (f a) g hg (hdvd a ha)
  rw [hsum]
  exact mul_divByMonic_self _ g hg

/-- The quotient distributes over the sum:
`numT m = ∑ p ∈ ternaryPartitions m, hTernary m p /ₘ gcdHTernary m`. -/
lemma numT_eq_sum_divByMonic (m : ℕ) :
    numT m = ∑ p ∈ ternaryPartitions m, (hTernary m p /ₘ gcdHTernary m) := by
  unfold numT
  exact sum_divByMonic_of_dvd (ternaryPartitions m) (hTernary m) (gcdHTernary m)
    (gcdHTernary_monic m) (fun p hp => gcdHTernary_dvd_hTernary m p hp)

end Aux_numT_eq_sum_divByMonic


/-! ### Helper for `X_add_one_dvd_quotient_of_ne_allOnes` -/
namespace Aux_X_add_one_dvd_quotient_of_ne_allOnes

open Aux_gcdHTernary_monic (monic_one_add_X_pow_three_pow hTernary_monic
  finset_gcd_monic_of_forall_monic)
open Aux_card_parts_lt_of_ne_allOnes (multiset_card_le_sum partition_card_le
  parts_eq_replicate_of_all_one all_parts_one_of_card_eq eq_allOnes_of_parts_eq
  card_parts_lt_of_ne_allOnes)

/-! ### Helper lemmas for X_add_one_pow_dvd_quotient -/

lemma gcdHTernary_monic (m : ℕ) : (gcdHTernary m).Monic := by
  unfold gcdHTernary
  apply finset_gcd_monic_of_forall_monic
  · refine ⟨allOnesPart m, ?_⟩
    simp only [ternaryPartitions, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi
    show IsPow3 i
    simp only [allOnesPart, Multiset.mem_replicate] at hi
    refine ⟨0, ?_, ?_⟩
    · simp [hi.2]
    · simp [hi.2]
  · intro p _
    exact hTernary_monic m p

/-- The "(X+1)-cofactor" of `(1 + X^N)` for odd `N`. -/
noncomputable def cofactorAdd (N : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range N, (-1) ^ i * Polynomial.X ^ i

/-- The "(X+1)-cofactor part" of `hTernary m p`. -/
noncomputable def hTernaryCofactor (m : ℕ) (p : Nat.Partition m) : Polynomial ℤ :=
  ∏ k ∈ Finset.range (m + 1),
    (cofactorAdd (3 ^ k)) ^ (m / 3 ^ k - partMult p (3 ^ k))

/-- Sum-of-quotients abbreviation. -/
noncomputable def sigmaM (m : ℕ) : ℕ := ∑ k ∈ Finset.range (m + 1), m / 3 ^ k

/-- The exponent sum. -/
noncomputable def expSum (m : ℕ) (p : Nat.Partition m) : ℕ :=
  ∑ k ∈ Finset.range (m + 1), (m / 3 ^ k - partMult p (3 ^ k))

lemma cofactorAdd_eq_sum_neg_X_pow (N : ℕ) :
    cofactorAdd N = ∑ i ∈ Finset.range N, (-Polynomial.X : Polynomial ℤ) ^ i := by
  unfold cofactorAdd
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [neg_pow]
  ring

lemma three_pow_odd (k : ℕ) : Odd ((3 : ℕ) ^ k) := Odd.pow ⟨1, rfl⟩

lemma one_add_X_pow_three_pow_eq_X_add_one_mul (k : ℕ) :
    (1 + Polynomial.X ^ (3 ^ k) : Polynomial ℤ)
      = (Polynomial.X + 1) * cofactorAdd (3 ^ k) := by
  have hodd : Odd ((3 : ℕ) ^ k) := three_pow_odd k
  rw [cofactorAdd_eq_sum_neg_X_pow]
  have h := geom_sum_mul_neg (-Polynomial.X : Polynomial ℤ) (3 ^ k)
  have hneg_pow : (-Polynomial.X : Polynomial ℤ) ^ (3 ^ k) = -Polynomial.X ^ (3 ^ k) :=
    hodd.neg_pow _
  rw [hneg_pow] at h
  have h1 : (1 : Polynomial ℤ) - (-Polynomial.X) = Polynomial.X + 1 := by ring
  have h2 : (1 : Polynomial ℤ) - (-(Polynomial.X ^ (3 ^ k))) = 1 + Polynomial.X ^ (3 ^ k) := by
    ring
  rw [h1, h2] at h
  linear_combination -h

lemma hTernary_eq_X_add_one_pow_mul_cofactor (m : ℕ) (p : Nat.Partition m) :
    hTernary m p
      = (Polynomial.X + 1) ^ (expSum m p) * (hTernaryCofactor m p) := by
  unfold hTernary hTernaryCofactor expSum
  conv_lhs =>
    rw [Finset.prod_congr rfl (fun k _ => by
      rw [one_add_X_pow_three_pow_eq_X_add_one_mul k, mul_pow])]
  rw [Finset.prod_mul_distrib]
  rw [← Finset.prod_pow_eq_pow_sum]

lemma exists_exp_of_mem_parts_ternary {m : ℕ} (p : Nat.Partition m)
    (hp : p ∈ ternaryPartitions m) (a : ℕ) (ha : a ∈ p.parts) :
    ∃ k, k ∈ Finset.range (m + 1) ∧ 3 ^ k = a := by
  have hp_ternary : IsTernary p := by
    simp [ternaryPartitions] at hp; exact hp
  obtain ⟨k, hka, hak⟩ := hp_ternary a ha
  refine ⟨k, ?_, hak.symm⟩
  rw [Finset.mem_range]
  have ha_le_sum : a ≤ p.parts.sum :=
    Multiset.single_le_sum (fun _ _ => Nat.zero_le _) a ha
  rw [p.parts_sum] at ha_le_sum
  omega

lemma card_parts_eq_sum_partMult
    (m : ℕ) (p : Nat.Partition m) (hp : p ∈ ternaryPartitions m) :
    p.parts.card = ∑ k ∈ Finset.range (m + 1), partMult p (3 ^ k) := by
  have h1 : p.parts.card = ∑ a ∈ p.parts.toFinset, partMult p a :=
    (Multiset.toFinset_sum_count_eq p.parts).symm
  rw [h1]
  symm
  rw [← Finset.sum_filter_of_ne (p := fun k => 3 ^ k ∈ p.parts.toFinset)
    (s := Finset.range (m + 1)) (f := fun k => partMult p (3 ^ k))]
  · apply Finset.sum_bij (fun (k : ℕ) (_ : k ∈ (Finset.range (m + 1)).filter
      (fun k => 3 ^ k ∈ p.parts.toFinset)) => (3 ^ k : ℕ))
    · intro k hk
      simp only [Finset.mem_filter] at hk
      exact hk.2
    · intro k₁ _ k₂ _ heq
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) heq
    · intro a ha
      have hap : a ∈ p.parts := Multiset.mem_toFinset.mp ha
      obtain ⟨k, hkR, hak⟩ := exists_exp_of_mem_parts_ternary p hp a hap
      refine ⟨k, ?_, hak⟩
      simp only [Finset.mem_filter]
      refine ⟨hkR, ?_⟩
      rw [hak]; exact ha
    · intro k _
      rfl
  · intro k _ hk
    have hcount : p.parts.count (3 ^ k) ≠ 0 := hk
    exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero hcount))

lemma partMult_mul_three_pow_le
    (m : ℕ) (p : Nat.Partition m) (k : ℕ) :
    partMult p (3 ^ k) * 3 ^ k ≤ m := by
  unfold partMult
  have h_repl_le : Multiset.replicate (p.parts.count (3 ^ k)) (3 ^ k) ≤ p.parts :=
    Multiset.le_iff_count.mpr (fun b => by
      by_cases hb : b = 3 ^ k
      · subst hb; simp
      · rw [Multiset.count_replicate]
        simp [Ne.symm hb])
  obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp h_repl_le
  have hsum : p.parts.sum = m := p.parts_sum
  rw [hu] at hsum
  simp [Multiset.sum_replicate] at hsum
  omega

lemma partMult_le_m_div_three_pow
    (m : ℕ) (p : Nat.Partition m) (k : ℕ) :
    partMult p (3 ^ k) ≤ m / 3 ^ k := by
  have hpos : 0 < (3 : ℕ) ^ k := pow_pos (by norm_num) k
  exact (Nat.le_div_iff_mul_le hpos).mpr (partMult_mul_three_pow_le m p k)

lemma expSum_eq_sigmaM_sub_card
    (m : ℕ) (p : Nat.Partition m) (hp : p ∈ ternaryPartitions m) :
    expSum m p = sigmaM m - p.parts.card := by
  unfold expSum sigmaM
  have hle : ∀ k ∈ Finset.range (m + 1),
      partMult p (3 ^ k) ≤ m / 3 ^ k := by
    intro k _hk
    exact partMult_le_m_div_three_pow m p k
  rw [Finset.sum_tsub_distrib _ hle]
  rw [← card_parts_eq_sum_partMult m p hp]

lemma card_parts_le (m : ℕ) (p : Nat.Partition m) : p.parts.card ≤ m := by
  have hsum : p.parts.sum = m := p.parts_sum
  have hpos : ∀ x ∈ p.parts, 1 ≤ x := fun x hx => p.parts_pos hx
  have hle : p.parts.card • 1 ≤ p.parts.sum := Multiset.card_nsmul_le_sum hpos
  simp at hle
  rwa [hsum] at hle

lemma m_le_sigmaM (m : ℕ) : m ≤ sigmaM m := by
  calc
    m = ∑ k ∈ Finset.range 1, m / 3 ^ k := by
      simp
    _ ≤ ∑ k ∈ Finset.range (m + 1), m / 3 ^ k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        simp only [Finset.mem_range] at hx ⊢
        omega
      · intro x _ _
        simp
    _ = sigmaM m := by
      rfl

lemma gcdHTernary_dvd_hTernary (m : ℕ) (p : Nat.Partition m)
    (hp : p ∈ ternaryPartitions m) :
    gcdHTernary m ∣ hTernary m p := by
  unfold gcdHTernary
  exact Finset.gcd_dvd hp

lemma allOnesPart_card (m : ℕ) : (allOnesPart m).parts.card = m := by
  show (Multiset.replicate m 1).card = m
  exact Multiset.card_replicate m 1

lemma partMult_allOnes_one (m : ℕ) :
    partMult (allOnesPart m) 1 = m := by
  unfold partMult allOnesPart
  simp [Multiset.count_replicate_self]

lemma partMult_allOnes_three_pow_ge_one (m k : ℕ) (hk : 1 ≤ k) :
    partMult (allOnesPart m) (3 ^ k) = 0 := by
  unfold partMult allOnesPart
  simp only [Multiset.count_replicate]
  have h3 : 3 ^ k ≥ 3 := by
    calc 3 ^ k ≥ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk
      _ = 3 := by norm_num
  have : ¬ (1 = 3 ^ k) := by omega
  simp [this]

lemma X_add_one_pow_sigmaM_sub_m_dvd_hTernary
    (m : ℕ) (p : Nat.Partition m) (hp : p ∈ ternaryPartitions m) :
    (Polynomial.X + 1 : Polynomial ℤ) ^ (sigmaM m - m) ∣ hTernary m p := by
  rw [hTernary_eq_X_add_one_pow_mul_cofactor]
  rw [expSum_eq_sigmaM_sub_card m p hp]
  refine Dvd.dvd.mul_right ?_ _
  apply pow_dvd_pow
  exact Nat.sub_le_sub_left (card_parts_le m p) (sigmaM m)

lemma X_add_one_pow_sigmaM_sub_m_dvd_gcdHTernary (m : ℕ) :
    (Polynomial.X + 1 : Polynomial ℤ) ^ (sigmaM m - m) ∣ gcdHTernary m := by
  unfold gcdHTernary
  exact Finset.dvd_gcd (fun p hp => X_add_one_pow_sigmaM_sub_m_dvd_hTernary m p hp)

/-- The "(X+1)-free" remainder `R` of `gcdHTernary m`. -/
noncomputable def gcdRemainder (m : ℕ) : Polynomial ℤ :=
  gcdHTernary m /ₘ ((Polynomial.X + 1) ^ (sigmaM m - m))

lemma gcdHTernary_eq_X_add_one_pow_mul_gcdRemainder (m : ℕ) :
    gcdHTernary m
      = (Polynomial.X + 1) ^ (sigmaM m - m) * gcdRemainder m := by
  have hX1 : ((Polynomial.X : Polynomial ℤ) + 1).Monic := by
    simpa using (Polynomial.monic_X_add_C (1 : ℤ))
  have hpow : ((Polynomial.X + 1 : Polynomial ℤ) ^ (sigmaM m - m)).Monic :=
    hX1.pow _
  have hdvd : (Polynomial.X + 1 : Polynomial ℤ) ^ (sigmaM m - m) ∣ gcdHTernary m :=
    X_add_one_pow_sigmaM_sub_m_dvd_gcdHTernary m
  have hmod : gcdHTernary m %ₘ ((Polynomial.X + 1) ^ (sigmaM m - m)) = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hpow).mpr hdvd
  have key := Polynomial.modByMonic_add_div (gcdHTernary m) hpow
  rw [hmod, zero_add] at key
  show gcdHTernary m = (Polynomial.X + 1) ^ (sigmaM m - m) * gcdRemainder m
  unfold gcdRemainder
  exact key.symm

lemma gcdRemainder_dvd_X_add_one_pow_sub_mul_cofactor
    (m : ℕ) (p : Nat.Partition m) (hp : p ∈ ternaryPartitions m) :
    gcdRemainder m
      ∣ (Polynomial.X + 1) ^ (m - p.parts.card) * hTernaryCofactor m p := by
  set σ := sigmaM m with _
  set c := p.parts.card with _
  have hFact : hTernary m p
      = (Polynomial.X + 1) ^ (expSum m p) * hTernaryCofactor m p :=
    hTernary_eq_X_add_one_pow_mul_cofactor m p
  have hExp : expSum m p = σ - c := expSum_eq_sigmaM_sub_card m p hp
  have hc_le_m : c ≤ m := card_parts_le m p
  have hm_le_σ : m ≤ σ := m_le_sigmaM m
  have hExpDecomp : expSum m p = (σ - m) + (m - c) := by
    rw [hExp]
    omega
  have hGcdFact : gcdHTernary m
      = (Polynomial.X + 1) ^ (σ - m) * gcdRemainder m :=
    gcdHTernary_eq_X_add_one_pow_mul_gcdRemainder m
  have hGcdDvd : gcdHTernary m ∣ hTernary m p := gcdHTernary_dvd_hTernary m p hp
  have hRewrite : hTernary m p
      = (Polynomial.X + 1) ^ (σ - m)
        * ((Polynomial.X + 1) ^ (m - c) * hTernaryCofactor m p) := by
    rw [hFact, hExpDecomp, pow_add]
    ring
  have hDvdProd :
      (Polynomial.X + 1) ^ (σ - m) * gcdRemainder m
        ∣ (Polynomial.X + 1) ^ (σ - m)
          * ((Polynomial.X + 1) ^ (m - c) * hTernaryCofactor m p) := by
    rw [← hGcdFact, ← hRewrite]
    exact hGcdDvd
  have hNeZero : ((Polynomial.X + 1) ^ (σ - m) : Polynomial ℤ) ≠ 0 :=
    pow_ne_zero _ (X_add_C_ne_zero (1 : ℤ))
  exact (mul_dvd_mul_iff_left hNeZero).mp hDvdProd

lemma allOnesPart_mem_ternaryPartitions (m : ℕ) :
    allOnesPart m ∈ ternaryPartitions m := by
  simp only [ternaryPartitions, Finset.mem_filter, Finset.mem_univ, true_and]
  intro i hi
  show IsPow3 i
  simp only [allOnesPart, Multiset.mem_replicate] at hi
  refine ⟨0, ?_, ?_⟩
  · simp [hi.2]
  · simp [hi.2]

lemma hTernaryCofactor_allOnes_eval_neg_one_ne_zero (m : ℕ) :
    (hTernaryCofactor m (allOnesPart m)).eval (-1) ≠ 0 := by
  have allOnes_exp_zero : m / 3 ^ 0 - partMult (allOnesPart m) (3 ^ 0) = 0 := by
    simp [partMult_allOnes_one]
  have allOnes_exp_pos : ∀ k, 1 ≤ k →
      m / 3 ^ k - partMult (allOnesPart m) (3 ^ k) = m / 3 ^ k := by
    intro k hk
    rw [partMult_allOnes_three_pow_ge_one m k hk]
    simp
  have cofactorAdd_eval_neg_one : ∀ (N : ℕ),
      (cofactorAdd N).eval (-1) = (N : ℤ) := by
    intro N
    unfold cofactorAdd
    rw [eval_finset_sum]
    have h : ∀ i ∈ Finset.range N,
        Polynomial.eval (-1 : ℤ) ((-1 : Polynomial ℤ) ^ i * Polynomial.X ^ i) = 1 := by
      intro i _
      simp [← pow_add, ← two_mul, pow_mul]
    rw [Finset.sum_congr rfl h]
    simp
  have range_succ_eq_insert_Ioc : Finset.range (m + 1) = insert 0 (Finset.Ioc 0 m) := by
    grind
  have hTernaryCofactor_allOnes_eq :
      hTernaryCofactor m (allOnesPart m) =
        ∏ k ∈ Finset.Ioc 0 m, (cofactorAdd (3 ^ k)) ^ (m / 3 ^ k) := by
    unfold hTernaryCofactor
    rw [range_succ_eq_insert_Ioc]
    rw [Finset.prod_insert (by simp : (0 : ℕ) ∉ Finset.Ioc 0 m)]
    rw [allOnes_exp_zero, pow_zero, one_mul]
    apply Finset.prod_congr rfl
    intro k hk
    rw [Finset.mem_Ioc] at hk
    rw [allOnes_exp_pos k hk.1]
  rw [hTernaryCofactor_allOnes_eq]
  rw [Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  rw [Finset.mem_Ioc] at hk
  obtain ⟨_, _⟩ := hk
  rw [Polynomial.eval_pow, cofactorAdd_eval_neg_one]
  apply pow_ne_zero
  have h3k : (3 : ℕ) ^ k ≥ 1 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k (by norm_num))
  exact_mod_cast Nat.one_le_iff_ne_zero.mp h3k

lemma X_add_one_not_dvd_gcdRemainder (m : ℕ) :
    ¬ ((Polynomial.X + 1 : Polynomial ℤ) ∣ gcdRemainder m) := by
  intro hdvd
  have hmem := allOnesPart_mem_ternaryPartitions m
  have hcard := allOnesPart_card m
  have hdvd2 := gcdRemainder_dvd_X_add_one_pow_sub_mul_cofactor m (allOnesPart m) hmem
  rw [hcard, Nat.sub_self, pow_zero, one_mul] at hdvd2
  have hdvd3 : (Polynomial.X + 1 : Polynomial ℤ) ∣ hTernaryCofactor m (allOnesPart m) :=
    dvd_trans hdvd hdvd2
  have heval : (hTernaryCofactor m (allOnesPart m)).eval (-1) = 0 := by
    obtain ⟨q, hq⟩ := hdvd3
    rw [hq]
    simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  exact hTernaryCofactor_allOnes_eval_neg_one_ne_zero m heval

lemma irreducible_X_add_one_int :
    Irreducible ((Polynomial.X + 1 : Polynomial ℤ)) := by
  have h : (Polynomial.X + 1 : Polynomial ℤ) = Polynomial.X - Polynomial.C (-1 : ℤ) := by
    simp [sub_neg_eq_add]
  rw [h]
  exact Polynomial.irreducible_X_sub_C (-1 : ℤ)

lemma isRelPrime_gcdRemainder_X_add_one_pow (m n : ℕ) :
    IsRelPrime (gcdRemainder m) ((Polynomial.X + 1 : Polynomial ℤ) ^ n) := by
  have hirr : Irreducible ((Polynomial.X + 1 : Polynomial ℤ)) :=
    irreducible_X_add_one_int
  have hnotdvd : ¬ ((Polynomial.X + 1 : Polynomial ℤ) ∣ gcdRemainder m) :=
    X_add_one_not_dvd_gcdRemainder m
  have h1 : IsRelPrime ((Polynomial.X + 1 : Polynomial ℤ)) (gcdRemainder m) :=
    (hirr.isRelPrime_iff_not_dvd).mpr hnotdvd
  have h2 : IsRelPrime (gcdRemainder m) ((Polynomial.X + 1 : Polynomial ℤ)) :=
    h1.symm
  exact h2.pow_right

lemma gcdRemainder_dvd_hTernaryCofactor
    (m : ℕ) (p : Nat.Partition m) (hp : p ∈ ternaryPartitions m) :
    gcdRemainder m ∣ hTernaryCofactor m p := by
  have h1 : gcdRemainder m
      ∣ (Polynomial.X + 1) ^ (m - p.parts.card) * hTernaryCofactor m p :=
    gcdRemainder_dvd_X_add_one_pow_sub_mul_cofactor m p hp
  have h2 : IsRelPrime (gcdRemainder m)
      ((Polynomial.X + 1 : Polynomial ℤ) ^ (m - p.parts.card)) :=
    isRelPrime_gcdRemainder_X_add_one_pow m (m - p.parts.card)
  exact h2.dvd_of_dvd_mul_left h1

lemma gcdHTernary_dvd_X_add_one_pow_sub_mul_cofactor
    (m : ℕ) (p : Nat.Partition m) (hp : p ∈ ternaryPartitions m) :
    gcdHTernary m
      ∣ (Polynomial.X + 1) ^ (sigmaM m - m) * hTernaryCofactor m p := by
  rw [gcdHTernary_eq_X_add_one_pow_mul_gcdRemainder]
  exact mul_dvd_mul_left _ (gcdRemainder_dvd_hTernaryCofactor m p hp)

lemma gcdHTernary_mul_X_add_one_pow_dvd_hTernary
    (m : ℕ) (p : Nat.Partition m) (hp : p ∈ ternaryPartitions m) :
    gcdHTernary m * ((Polynomial.X + 1 : Polynomial ℤ) ^ (m - p.parts.card))
      ∣ hTernary m p := by
  have hcardle : p.parts.card ≤ m := card_parts_le m p
  have hmle : m ≤ sigmaM m := m_le_sigmaM m
  have hfact : hTernary m p
      = (Polynomial.X + 1) ^ (expSum m p) * (hTernaryCofactor m p) :=
    hTernary_eq_X_add_one_pow_mul_cofactor m p
  have hexp : expSum m p = sigmaM m - p.parts.card :=
    expSum_eq_sigmaM_sub_card m p hp
  obtain ⟨q, hq⟩ :=
    gcdHTernary_dvd_X_add_one_pow_sub_mul_cofactor m p hp
  refine ⟨q, ?_⟩
  rw [hfact, hexp]
  have key : (sigmaM m - p.parts.card) = (m - p.parts.card) + (sigmaM m - m) := by
    omega
  rw [key, pow_add]
  have hq' : (Polynomial.X + 1) ^ (sigmaM m - m) * hTernaryCofactor m p
              = gcdHTernary m * q := hq
  calc (Polynomial.X + 1) ^ (m - p.parts.card)
          * (Polynomial.X + 1) ^ (sigmaM m - m) * hTernaryCofactor m p
      = (Polynomial.X + 1) ^ (m - p.parts.card)
          * ((Polynomial.X + 1) ^ (sigmaM m - m) * hTernaryCofactor m p) := by ring
    _ = (Polynomial.X + 1) ^ (m - p.parts.card) * (gcdHTernary m * q) := by
          rw [hq']
    _ = gcdHTernary m * (Polynomial.X + 1) ^ (m - p.parts.card) * q := by ring

lemma dvd_divByMonic_of_mul_dvd
    {R : Type*} [CommRing R] {f g h : Polynomial R}
    (hg : g.Monic) (hdvd : g * h ∣ f) :
    h ∣ f /ₘ g := by
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨k, ?_⟩
  rw [hk, mul_assoc]
  exact Polynomial.mul_divByMonic_cancel_left (h * k) hg

/-- **Step 6 (key helper).**  For every ternary partition `p` of `m`, the
polynomial `(X + 1) ^ (m - p.parts.card)` divides the quotient
`hTernary m p /ₘ gcdHTernary m` in `ℤ[X]`. -/
lemma X_add_one_pow_dvd_quotient (m : ℕ) (p : Nat.Partition m)
    (hp : p ∈ ternaryPartitions m) :
    ((Polynomial.X + 1 : Polynomial ℤ) ^ (m - p.parts.card)) ∣
      (hTernary m p /ₘ gcdHTernary m) := by
  exact dvd_divByMonic_of_mul_dvd
    (gcdHTernary_monic m)
    (gcdHTernary_mul_X_add_one_pow_dvd_hTernary m p hp)

/-- **Step 6.1.**  For any ternary partition `p ≠ allOnesPart m`, the
quotient `hTernary m p /ₘ gcdHTernary m` is divisible by `(X + 1)`. -/
lemma X_add_one_dvd_quotient_of_ne_allOnes (m : ℕ) (p : Nat.Partition m)
    (hp : p ∈ ternaryPartitions m) (hne : p ≠ allOnesPart m) :
    (Polynomial.X + 1 : Polynomial ℤ) ∣ (hTernary m p /ₘ gcdHTernary m) := by
  have hcard : p.parts.card < m := card_parts_lt_of_ne_allOnes m p hp hne
  have hpow : ((Polynomial.X + 1 : Polynomial ℤ) ^ (m - p.parts.card)) ∣
      (hTernary m p /ₘ gcdHTernary m) := X_add_one_pow_dvd_quotient m p hp
  have hge : 1 ≤ m - p.parts.card := by omega
  -- (X+1) = (X+1)^1 divides (X+1)^(m - p.parts.card) which divides the quotient
  have hdvd1 : (Polynomial.X + 1 : Polynomial ℤ) ∣
      (Polynomial.X + 1 : Polynomial ℤ) ^ (m - p.parts.card) :=
    dvd_pow_self _ (by omega)
  exact hdvd1.trans hpow

end Aux_X_add_one_dvd_quotient_of_ne_allOnes


/-! ### Helper for `quotient_allOnes_eval_neg_one_eq_pow_val3` -/
namespace Aux_quotient_allOnes_eval_neg_one_eq_pow_val3

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false

open Aux_gcdHTernary_monic (normalize_finset_gcd_polynomial_int
  leadingCoeff_pos_of_normalize_eq_self monic_of_normalize_eq_self_of_dvd_monic)

/-- The all-ones partition is ternary. -/
lemma allOnesPart_isTernary (m : ℕ) : IsTernary (allOnesPart m) := by
  intro i hi
  simp only [allOnesPart, Multiset.mem_replicate] at hi
  rcases hi with ⟨_, rfl⟩
  exact ⟨0, by omega, by norm_num⟩

/-- The all-ones partition lies in `ternaryPartitions m`. -/
lemma allOnesPart_mem_ternaryPartitions (m : ℕ) :
    allOnesPart m ∈ ternaryPartitions m := by
  simp only [ternaryPartitions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact allOnesPart_isTernary m

/-- `hTernary m (allOnesPart m)` is monic. -/
lemma hTernary_allOnes_monic (m : ℕ) :
    (hTernary m (allOnesPart m)).Monic := by
  unfold hTernary
  refine Polynomial.monic_prod_of_monic _ _ (fun k _ => ?_)
  refine Polynomial.Monic.pow ?_ _
  have hne : (3 : ℕ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have heq : (1 : Polynomial ℤ) + Polynomial.X ^ (3 ^ k)
      = Polynomial.X ^ (3 ^ k) + Polynomial.C 1 := by
    simp [add_comm]
  rw [heq]
  exact Polynomial.monic_X_pow_add_C 1 hne

/-- `gcdHTernary m` is monic. -/
lemma gcdHTernary_monic (m : ℕ) : (gcdHTernary m).Monic := by
  apply monic_of_normalize_eq_self_of_dvd_monic
    (p := hTernary m (allOnesPart m))
  · exact normalize_finset_gcd_polynomial_int _ _
  · exact Finset.gcd_dvd (allOnesPart_mem_ternaryPartitions m)
  · exact hTernary_allOnes_monic m


-- ========== Helpers for hTernary_allOnes_eq_prod_cyclotomic ==========

open Aux_X_add_one_dvd_quotient_of_ne_allOnes
  (partMult_allOnes_one partMult_allOnes_three_pow_ge_one)

lemma X_pow_two_three_pow_sub_one_eq_mul_a (k : ℕ) :
    (Polynomial.X : Polynomial ℤ) ^ (2 * 3 ^ k) - 1
      = (Polynomial.X ^ (3 ^ k) - 1) * (Polynomial.X ^ (3 ^ k) + 1) := by
  have h2 : (2 : ℕ) * 3 ^ k = 3 ^ k + 3 ^ k := by ring
  rw [h2, pow_add]
  ring

lemma three_pow_dvd_two_mul_a (k : ℕ) : 3 ^ k ∣ 2 * 3 ^ k :=
  ⟨2, by ring⟩

lemma two_mul_three_pow_ne_zero_a (k : ℕ) : (2 * 3 ^ k : ℕ) ≠ 0 := by
  have : (3 : ℕ) ^ k ≥ 1 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  omega

lemma two_mul_three_pow_injective_a : Function.Injective (fun j : ℕ => 2 * 3 ^ j) := by
  intro a b hab
  simp only at hab
  have : (3 : ℕ) ^ a = 3 ^ b := by omega
  exact Nat.pow_right_injective (by norm_num) this

lemma X_pow_three_pow_sub_one_ne_zero_a (k : ℕ) :
    (Polynomial.X : Polynomial ℤ) ^ (3 ^ k) - 1 ≠ 0 := by
  intro h
  have hdeg : ((Polynomial.X : Polynomial ℤ) ^ (3 ^ k) - 1).natDegree = 3 ^ k := by
    have hrw : (Polynomial.X : Polynomial ℤ) ^ (3 ^ k) - 1
              = Polynomial.X ^ (3 ^ k) + Polynomial.C (-1) := by
      rw [Polynomial.C_neg, Polynomial.C_1]; ring
    rw [hrw]
    exact Polynomial.natDegree_X_pow_add_C
  rw [h, Polynomial.natDegree_zero] at hdeg
  have : (3 : ℕ) ^ k ≥ 1 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  omega

lemma two_mul_three_pow_dvd_two_mul_three_pow_a
    (j k : ℕ) (h : j ≤ k) : 2 * 3 ^ j ∣ 2 * 3 ^ k := by
  exact Nat.mul_dvd_mul_left 2 (pow_dvd_pow 3 h)

lemma exists_eq_two_mul_three_pow_of_dvd_not_dvd_a
    (k d : ℕ) (h1 : d ∣ 2 * 3 ^ k) (h2 : ¬ d ∣ 3 ^ k) :
    ∃ j ≤ k, d = 2 * 3 ^ j := by
  have h2dvd : 2 ∣ d := by
    by_contra h2nd
    have hcop : Nat.Coprime 2 d :=
      (Nat.prime_two.coprime_iff_not_dvd).mpr h2nd
    exact h2 (hcop.symm.dvd_of_dvd_mul_left h1)
  obtain ⟨x, hx⟩ := h2dvd
  have hxdvd : x ∣ 3 ^ k := by
    have : 2 * x ∣ 2 * 3 ^ k := hx ▸ h1
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0:ℕ) < 2)).mp this
  obtain ⟨j, hj, hxj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hxdvd
  exact ⟨j, hj, by rw [hx, hxj]⟩

lemma two_mul_three_pow_not_dvd_three_pow_a (j k : ℕ) : ¬ (2 * 3 ^ j ∣ 3 ^ k) := by
  intro h
  have h₁ : 2 ∣ 3 ^ k := by
    have h₂ : 2 ∣ 2 * 3 ^ j := by
      apply dvd_mul_right
    exact dvd_trans h₂ h
  have h₂ : ¬(2 ∣ 3 ^ k) := by
    have h₃ : ∀ n : ℕ, 3 ^ n % 2 = 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ]
        simp [Nat.mul_mod, ih]
    have h₄ : 3 ^ k % 2 = 1 := h₃ k
    omega
  exact h₂ h₁

lemma divisors_two_mul_three_pow_sdiff_divisors_three_pow_a (k : ℕ) :
    (2 * 3 ^ k).divisors \ (3 ^ k).divisors
      = (Finset.range (k + 1)).image (fun j => 2 * 3 ^ j) := by
  ext d
  simp only [Finset.mem_sdiff, Nat.mem_divisors, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨hd1, _⟩, hd2⟩
    have h3k : (3 : ℕ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have hnd : ¬ d ∣ 3 ^ k := by
      intro hdvd
      exact hd2 ⟨hdvd, h3k⟩
    obtain ⟨j, hjk, hdj⟩ := exists_eq_two_mul_three_pow_of_dvd_not_dvd_a k d hd1 hnd
    exact ⟨j, Nat.lt_succ_of_le hjk, hdj.symm⟩
  · rintro ⟨j, hj, hdj⟩
    have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
    subst hdj
    refine ⟨⟨two_mul_three_pow_dvd_two_mul_three_pow_a j k hjk, ?_⟩, ?_⟩
    · have : (2 : ℕ) * 3 ^ k ≠ 0 := by positivity
      exact this
    · intro ⟨hdvd, _⟩
      exact two_mul_three_pow_not_dvd_three_pow_a j k hdvd

lemma one_add_X_pow_three_pow_eq_prod_cyclotomic_a (k : ℕ) :
    (1 : Polynomial ℤ) + Polynomial.X ^ (3 ^ k)
      = ∏ j ∈ Finset.range (k + 1), Polynomial.cyclotomic (2 * 3 ^ j) ℤ := by
  have h_cyc :
      (Polynomial.X ^ (3 ^ k) - 1 : Polynomial ℤ)
        * ∏ x ∈ (2 * 3 ^ k).divisors \ (3 ^ k).divisors,
            Polynomial.cyclotomic x ℤ
      = Polynomial.X ^ (2 * 3 ^ k) - 1 :=
    Polynomial.X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd ℤ
      (three_pow_dvd_two_mul_a k) (two_mul_three_pow_ne_zero_a k)
  have h_diff := X_pow_two_three_pow_sub_one_eq_mul_a k
  rw [h_diff] at h_cyc
  have h_ne : (Polynomial.X : Polynomial ℤ) ^ (3 ^ k) - 1 ≠ 0 :=
    X_pow_three_pow_sub_one_ne_zero_a k
  have h_eq : (Polynomial.X ^ (3 ^ k) + 1 : Polynomial ℤ)
        = ∏ x ∈ (2 * 3 ^ k).divisors \ (3 ^ k).divisors, Polynomial.cyclotomic x ℤ := by
    exact (mul_left_cancel₀ h_ne h_cyc).symm
  have h_set := divisors_two_mul_three_pow_sdiff_divisors_three_pow_a k
  rw [h_set] at h_eq
  rw [Finset.prod_image (fun a _ b _ h => two_mul_three_pow_injective_a h)] at h_eq
  rw [add_comm 1 _]
  exact h_eq

lemma hTernary_allOnes_eq_prod_Ioc_a (m : ℕ) :
    hTernary m (allOnesPart m)
      = ∏ k ∈ Finset.Ioc 0 m,
          (1 + Polynomial.X ^ (3 ^ k)) ^ (m / 3 ^ k) := by
  unfold hTernary
  have hsplit : Finset.range (m + 1) = insert 0 (Finset.Ioc 0 m) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_Ioc, Finset.mem_insert]
    omega
  rw [hsplit]
  rw [Finset.prod_insert (by simp)]
  have hzero :
      (1 + Polynomial.X ^ (3 ^ 0)) ^
          (m / 3 ^ 0 - partMult (allOnesPart m) (3 ^ 0))
        = (1 : Polynomial ℤ) := by
    have : partMult (allOnesPart m) (3 ^ 0) = m := by
      simp [partMult_allOnes_one]
    rw [this]
    simp
  rw [hzero, one_mul]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Finset.mem_Ioc] at hk
  have hk1 : 1 ≤ k := hk.1
  rw [partMult_allOnes_three_pow_ge_one m k hk1]
  rw [Nat.sub_zero]

lemma hTernary_allOnes_eq_double_prod_a (m : ℕ) :
    hTernary m (allOnesPart m)
      = ∏ k ∈ Finset.Ioc 0 m,
          ∏ j ∈ Finset.range (k + 1),
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ k) := by
  rw [hTernary_allOnes_eq_prod_Ioc_a]
  refine Finset.prod_congr rfl ?_
  intro k _
  rw [one_add_X_pow_three_pow_eq_prod_cyclotomic_a, Finset.prod_pow]

lemma inner_prod_j_zero_a (m : ℕ) :
    (∏ k ∈ Finset.Ioc 0 m,
        (Polynomial.cyclotomic (2 * 3 ^ (0 : ℕ)) ℤ) ^ (m / 3 ^ k))
      = (Polynomial.cyclotomic 2 ℤ) ^ (∑ k ∈ Finset.Ioc 0 m, m / 3 ^ k) := by
  have h : (2 * 3 ^ (0 : ℕ) : ℕ) = 2 := by norm_num
  rw [h]
  exact Finset.prod_pow_eq_pow_sum _ _ _

lemma inner_prod_eq_pow_sum_a (m j : ℕ) :
    (∏ k ∈ Finset.Ico j (m + 1),
        (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ k))
      = (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
          ^ (∑ k ∈ Finset.Ico j (m + 1), m / 3 ^ k) := by
  exact Finset.prod_pow_eq_pow_sum (Finset.Ico j (m + 1)) (fun k => m / 3 ^ k)
    (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)

lemma swap_double_prod_aux_a (m : ℕ) :
    (∏ k ∈ Finset.Ioc 0 m,
        ∏ j ∈ Finset.range (k + 1),
          (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ k))
      = ∏ j ∈ Finset.range (m + 1),
          ∏ k ∈ (Finset.Ioc 0 m).filter (fun k => j ≤ k),
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ k) := by
  apply Finset.prod_comm'
  intro k j
  simp only [Finset.mem_Ioc, Finset.mem_range, Finset.mem_filter]
  omega

lemma filter_Ioc_eq_Ico_a (m j : ℕ) (hj : 1 ≤ j) :
    (Finset.Ioc 0 m).filter (fun k => j ≤ k) = Finset.Ico j (m + 1) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
  omega

lemma filter_Ioc_zero_eq_a (m : ℕ) :
    (Finset.Ioc 0 m).filter (fun k => (0 : ℕ) ≤ k) = Finset.Ioc 0 m := by
  apply Finset.filter_true_of_mem
  intro k hk
  simp only [Finset.mem_Ioc] at hk ⊢
  omega

lemma range_succ_eq_insert_Ioc_a (m : ℕ) :
    Finset.range (m + 1) = insert 0 (Finset.Ioc 0 m) := by
  ext k
  simp only [Finset.mem_range, Finset.mem_Ioc, Finset.mem_insert]
  omega

lemma swap_double_prod_a (m : ℕ) :
    (∏ k ∈ Finset.Ioc 0 m,
        ∏ j ∈ Finset.range (k + 1),
          (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ k))
      = ((Polynomial.cyclotomic 2 ℤ) ^ (∑ k ∈ Finset.Ioc 0 m, m / 3 ^ k))
        * ∏ j ∈ Finset.Ioc 0 m,
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
              ^ (∑ k ∈ Finset.Ico j (m + 1), m / 3 ^ k) := by
  rw [swap_double_prod_aux_a m]
  rw [range_succ_eq_insert_Ioc_a m]
  rw [Finset.prod_insert (by simp : (0 : ℕ) ∉ Finset.Ioc 0 m)]
  congr 1
  · rw [filter_Ioc_zero_eq_a]
    exact inner_prod_j_zero_a m
  · apply Finset.prod_congr rfl
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ioc.mp hj).1
    rw [filter_Ioc_eq_Ico_a m j hj1]
    exact inner_prod_eq_pow_sum_a m j

/-- The cyclotomic-power factorisation of `hTernary m (allOnesPart m)`. -/
lemma hTernary_allOnes_eq_prod_cyclotomic (m : ℕ) :
    hTernary m (allOnesPart m)
      = ((Polynomial.cyclotomic 2 ℤ) ^ (∑ k ∈ Finset.Ioc 0 m, m / 3 ^ k))
        * ∏ j ∈ Finset.Ioc 0 m,
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
              ^ (∑ k ∈ Finset.Ico j (m + 1), m / 3 ^ k) := by
  rw [hTernary_allOnes_eq_double_prod_a, swap_double_prod_a]

/-- Abbreviation: the right-hand side of the target factorisation. -/
noncomputable def gcdRHS (m : ℕ) : Polynomial ℤ :=
  ((Polynomial.cyclotomic 2 ℤ) ^ (∑ k ∈ Finset.Ioc 0 m, m / 3 ^ k))
    * ∏ j ∈ Finset.Ioc 0 m,
        (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
          ^ (∑ k ∈ Finset.Ioc j m, m / 3 ^ k)

/-- The "remaining cofactor" polynomial of the all-ones decomposition.
We use the same definition as the custom lemma library:
`cof m := ∏ j ∈ Ioc 0 m, Φ_{2·3^j}^(m/3^j)`. -/
noncomputable def cof (m : ℕ) : Polynomial ℤ :=
  ∏ j ∈ Finset.Ioc 0 m,
    (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ j)

/-! ### Custom lemmas incorporated from `custom-lemmas.json`. -/

/-- `¬ (2 * 3^j ∣ 3^k)` for any `j, k`, because `2 ∤ 3^k`. -/
lemma two_mul_three_pow_not_dvd_three_pow (j k : ℕ) : ¬ (2 * 3 ^ j ∣ 3 ^ k) := by
  intro h
  have h₁ : 2 ∣ 3 ^ k := by
    have h₂ : 2 ∣ 2 * 3 ^ j := by
      apply dvd_mul_right
    exact dvd_trans h₂ h
  have h₂ : ¬(2 ∣ 3 ^ k) := by
    have h₃ : ∀ n : ℕ, 3 ^ n % 2 = 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ]
        simp [Nat.mul_mod, ih]
    have h₄ : 3 ^ k % 2 = 1 := h₃ k
    omega
  exact h₂ h₁

/-- If `d ∣ 2 * 3^k` and `¬ d ∣ 3^k`, then `d = 2 * 3^j` for some `j ≤ k`.
    The intuition: divisors of `2*3^k` are `2^a * 3^b` with `a ∈ {0,1}`, `b ≤ k`.
    Those not dividing `3^k` must have `a = 1`. -/
lemma exists_eq_two_mul_three_pow_of_dvd_not_dvd
    (k d : ℕ) (h1 : d ∣ 2 * 3 ^ k) (h2 : ¬ d ∣ 3 ^ k) :
    ∃ j ≤ k, d = 2 * 3 ^ j := by
  -- Step 1: show 2 ∣ d
  have h2dvd : 2 ∣ d := by
    by_contra h2nd
    have hcop : Nat.Coprime 2 d :=
      (Nat.prime_two.coprime_iff_not_dvd).mpr h2nd
    exact h2 (hcop.symm.dvd_of_dvd_mul_left h1)
  obtain ⟨x, hx⟩ := h2dvd
  have hxdvd : x ∣ 3 ^ k := by
    have : 2 * x ∣ 2 * 3 ^ k := hx ▸ h1
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0:ℕ) < 2)).mp this
  obtain ⟨j, hj, hxj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hxdvd
  exact ⟨j, hj, by rw [hx, hxj]⟩

/-! ### Polynomial helper lemmas. -/

/-- The right-hand side polynomial `gcdRHS m` is monic. -/
lemma gcdRHS_monic (m : ℕ) : (gcdRHS m).Monic := by
  unfold gcdRHS
  exact (Polynomial.cyclotomic.monic 2 ℤ).pow _ |>.mul
    (Polynomial.monic_prod_of_monic _ _ (fun j _ =>
      (Polynomial.cyclotomic.monic (2 * 3 ^ j) ℤ).pow _))

/- Sister lower bound: `gcdRHS m ∣ gcdHTernary m`.
This is the "min-exponent" direction. -/
section gcdRHS_dvd_gcdHTernary_section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

private lemma X_pow_two_three_pow_sub_one_eq_mul' (k : ℕ) :
    (Polynomial.X : Polynomial ℤ) ^ (2 * 3 ^ k) - 1
      = (Polynomial.X ^ (3 ^ k) - 1) * (Polynomial.X ^ (3 ^ k) + 1) := by
  have h2 : (2 : ℕ) * 3 ^ k = 3 ^ k + 3 ^ k := by ring
  rw [h2, pow_add]
  ring

private lemma three_pow_dvd_two_mul' (k : ℕ) : 3 ^ k ∣ 2 * 3 ^ k :=
  ⟨2, by ring⟩

private lemma two_mul_three_pow_ne_zero' (k : ℕ) : (2 * 3 ^ k : ℕ) ≠ 0 := by
  have : (3 : ℕ) ^ k ≥ 1 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  omega

private lemma two_mul_three_pow_injective' : Function.Injective (fun j : ℕ => 2 * 3 ^ j) := by
  intro a b hab
  simp only at hab
  have : (3 : ℕ) ^ a = 3 ^ b := by omega
  exact Nat.pow_right_injective (by norm_num) this

private lemma X_pow_three_pow_sub_one_ne_zero' (k : ℕ) :
    (Polynomial.X : Polynomial ℤ) ^ (3 ^ k) - 1 ≠ 0 := by
  intro h
  have hdeg : ((Polynomial.X : Polynomial ℤ) ^ (3 ^ k) - 1).natDegree = 3 ^ k := by
    have hrw : (Polynomial.X : Polynomial ℤ) ^ (3 ^ k) - 1
              = Polynomial.X ^ (3 ^ k) + Polynomial.C (-1) := by
      rw [Polynomial.C_neg, Polynomial.C_1]; ring
    rw [hrw]
    exact Polynomial.natDegree_X_pow_add_C
  rw [h, Polynomial.natDegree_zero] at hdeg
  have : (3 : ℕ) ^ k ≥ 1 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  omega

private lemma two_mul_three_pow_dvd_two_mul_three_pow'
    (j k : ℕ) (h : j ≤ k) : 2 * 3 ^ j ∣ 2 * 3 ^ k := by
  exact Nat.mul_dvd_mul_left 2 (pow_dvd_pow 3 h)

private lemma divisors_two_mul_three_pow_sdiff_divisors_three_pow' (k : ℕ) :
    (2 * 3 ^ k).divisors \ (3 ^ k).divisors
      = (Finset.range (k + 1)).image (fun j => 2 * 3 ^ j) := by
  ext d
  simp only [Finset.mem_sdiff, Nat.mem_divisors, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨hd1, _⟩, hd2⟩
    have h3k : (3 : ℕ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have hnd : ¬ d ∣ 3 ^ k := by
      intro hdvd
      exact hd2 ⟨hdvd, h3k⟩
    obtain ⟨j, hjk, hdj⟩ := exists_eq_two_mul_three_pow_of_dvd_not_dvd k d hd1 hnd
    exact ⟨j, Nat.lt_succ_of_le hjk, hdj.symm⟩
  · rintro ⟨j, hj, hdj⟩
    have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
    subst hdj
    refine ⟨⟨two_mul_three_pow_dvd_two_mul_three_pow' j k hjk, ?_⟩, ?_⟩
    · have : (2 : ℕ) * 3 ^ k ≠ 0 := by positivity
      exact this
    · intro ⟨hdvd, _⟩
      exact two_mul_three_pow_not_dvd_three_pow j k hdvd

private lemma one_add_X_pow_three_pow_eq_prod_cyclotomic' (k : ℕ) :
    (1 : Polynomial ℤ) + Polynomial.X ^ (3 ^ k)
      = ∏ j ∈ Finset.range (k + 1), Polynomial.cyclotomic (2 * 3 ^ j) ℤ := by
  have h_cyc :
      (Polynomial.X ^ (3 ^ k) - 1 : Polynomial ℤ)
        * ∏ x ∈ (2 * 3 ^ k).divisors \ (3 ^ k).divisors,
            Polynomial.cyclotomic x ℤ
      = Polynomial.X ^ (2 * 3 ^ k) - 1 :=
    Polynomial.X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd ℤ
      (three_pow_dvd_two_mul' k) (two_mul_three_pow_ne_zero' k)
  have h_diff := X_pow_two_three_pow_sub_one_eq_mul' k
  rw [h_diff] at h_cyc
  have h_ne : (Polynomial.X : Polynomial ℤ) ^ (3 ^ k) - 1 ≠ 0 :=
    X_pow_three_pow_sub_one_ne_zero' k
  have h_eq : (Polynomial.X ^ (3 ^ k) + 1 : Polynomial ℤ)
        = ∏ x ∈ (2 * 3 ^ k).divisors \ (3 ^ k).divisors, Polynomial.cyclotomic x ℤ := by
    exact (mul_left_cancel₀ h_ne h_cyc).symm
  have h_set := divisors_two_mul_three_pow_sdiff_divisors_three_pow' k
  rw [h_set] at h_eq
  rw [Finset.prod_image (fun a _ b _ h => two_mul_three_pow_injective' h)] at h_eq
  rw [add_comm 1 _]
  exact h_eq

private lemma partMult_mul_three_pow_le'
    (m : ℕ) (p : Nat.Partition m) (k : ℕ) :
    partMult p (3 ^ k) * 3 ^ k ≤ m := by
  have h_main : partMult p (3 ^ k) * 3 ^ k ≤ p.parts.sum := by
    unfold partMult
    have hfilter : (p.parts.filter (Eq (3 ^ k))).sum = p.parts.count (3 ^ k) * 3 ^ k := by
      rw [Multiset.filter_eq]
      rw [Multiset.sum_replicate]
      simp [mul_comm]
    rw [← hfilter]
    have hsplit := @Multiset.sum_filter_add_sum_filter_not ℕ _ p.parts (Eq (3 ^ k)) _
    omega
  have h_sum_eq_m : p.parts.sum = m := p.parts_sum
  omega

private lemma hTernary_eq_double_prod' (m : ℕ) (p : Nat.Partition m) :
    hTernary m p
      = ∏ k ∈ Finset.range (m + 1),
          ∏ j ∈ Finset.range (k + 1),
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ k - partMult p (3 ^ k)) := by
  unfold hTernary
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [one_add_X_pow_three_pow_eq_prod_cyclotomic' k]
  rw [Finset.prod_pow]

set_option linter.unusedVariables false in
private lemma swap_double_prod_general_swap' (m : ℕ) (p : Nat.Partition m) :
    (∏ k ∈ Finset.range (m + 1),
        ∏ j ∈ Finset.range (k + 1),
          (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ k - partMult p (3 ^ k)))
      = ∏ j ∈ Finset.range (m + 1),
          ∏ k ∈ Finset.Ico j (m + 1),
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ k - partMult p (3 ^ k)) := by
  apply Finset.prod_comm'
  intro k j
  simp only [Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨hk, hj⟩
    refine ⟨⟨?_, hk⟩, ?_⟩
    · omega
    · omega
  · rintro ⟨⟨hjk, hk⟩, hj⟩
    refine ⟨hk, ?_⟩
    omega

set_option linter.unusedVariables false in
private lemma swap_double_prod_general_collect' (m : ℕ) (p : Nat.Partition m) :
    (∏ j ∈ Finset.range (m + 1),
        ∏ k ∈ Finset.Ico j (m + 1),
          (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ k - partMult p (3 ^ k)))
      = ∏ j ∈ Finset.range (m + 1),
          (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
            ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
  refine Finset.prod_congr rfl ?_
  intro j _
  exact Finset.prod_pow_eq_pow_sum (Finset.Ico j (m + 1))
    (fun k => m / 3 ^ k - partMult p (3 ^ k)) (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)

private lemma swap_double_prod_general_split' (m : ℕ) (p : Nat.Partition m) :
    (∏ j ∈ Finset.range (m + 1),
        (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
          ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))))
      = ((Polynomial.cyclotomic 2 ℤ) ^
            (∑ k ∈ Finset.range (m + 1), (m / 3 ^ k - partMult p (3 ^ k))))
        * ∏ j ∈ Finset.Ioc 0 m,
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
              ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
  have h₀ : Finset.range (m + 1) = {0} ∪ Finset.Ioc 0 m := by
    apply Finset.ext
    intro x
    simp [Finset.mem_range, Finset.mem_Ioc, Nat.lt_succ_iff]
  calc
    (∏ j ∈ Finset.range (m + 1),
        (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
          ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))))
      = ∏ j ∈ ({0} ∪ Finset.Ioc 0 m),
        (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
          ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
        rw [h₀]
    _ = ∏ j ∈ ({0} : Finset ℕ),
        (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
          ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) *
      ∏ j ∈ Finset.Ioc 0 m,
        (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
          ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
        rw [Finset.prod_union]
        <;> simp [Finset.disjoint_left]
    _ = (Polynomial.cyclotomic (2 * 3 ^ 0) ℤ) ^ (∑ k ∈ Finset.Ico 0 (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) *
      ∏ j ∈ Finset.Ioc 0 m,
        (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
          ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
        simp [Finset.prod_singleton]
    _ = ((Polynomial.cyclotomic 2 ℤ) ^
            (∑ k ∈ Finset.range (m + 1), (m / 3 ^ k - partMult p (3 ^ k))))
        * ∏ j ∈ Finset.Ioc 0 m,
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
              ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
        have h₁ : (Polynomial.cyclotomic (2 * 3 ^ 0) ℤ) = Polynomial.cyclotomic 2 ℤ := by
          norm_num
        rw [h₁]
        have h₂ : (∑ k ∈ Finset.Ico 0 (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) = (∑ k ∈ Finset.range (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
          have h₃ : Finset.Ico 0 (m + 1) = Finset.range (m + 1) := by
            ext x
            simp [Finset.mem_Ico, Finset.mem_range]
          rw [h₃]
        rw [h₂]

private lemma swap_double_prod_general' (m : ℕ) (p : Nat.Partition m) :
    (∏ k ∈ Finset.range (m + 1),
        ∏ j ∈ Finset.range (k + 1),
          (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ k - partMult p (3 ^ k)))
      = ((Polynomial.cyclotomic 2 ℤ) ^
            (∑ k ∈ Finset.range (m + 1), (m / 3 ^ k - partMult p (3 ^ k))))
        * ∏ j ∈ Finset.Ioc 0 m,
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
              ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
  rw [swap_double_prod_general_swap' m p,
      swap_double_prod_general_collect' m p,
      swap_double_prod_general_split' m p]

private lemma hTernary_eq_prod_cyclotomic_swap' (m : ℕ) (p : Nat.Partition m) :
    hTernary m p
      = ((Polynomial.cyclotomic 2 ℤ) ^
            (∑ k ∈ Finset.range (m + 1), (m / 3 ^ k - partMult p (3 ^ k))))
        * ∏ j ∈ Finset.Ioc 0 m,
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
              ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
  rw [hTernary_eq_double_prod' m p, swap_double_prod_general' m p]

private lemma partMult_le_m_div_three_pow'
    (m : ℕ) (p : Nat.Partition m) (k : ℕ) :
    partMult p (3 ^ k) ≤ m / 3 ^ k := by
  have hpos : 0 < (3 : ℕ) ^ k := pow_pos (by norm_num) k
  exact (Nat.le_div_iff_mul_le hpos).mpr (partMult_mul_three_pow_le' m p k)

private lemma range_succ_eq_insert_Ioc' (m : ℕ) :
    Finset.range (m + 1) = insert 0 (Finset.Ioc 0 m) := by
  ext x
  simp only [Finset.mem_range, Finset.mem_Ioc, Finset.mem_insert]
  omega

private lemma three_pow_injective' : Function.Injective (fun k : ℕ => 3 ^ k) :=
  fun _ _ h => Nat.pow_right_injective (by norm_num) h

private lemma card_parts_le' (m : ℕ) (p : Nat.Partition m) : p.parts.card ≤ m := by
  have hsum : p.parts.sum = m := p.parts_sum
  have hpos : ∀ x ∈ p.parts, 1 ≤ x := fun x hx => p.parts_pos hx
  have hle : p.parts.card • 1 ≤ p.parts.sum := Multiset.card_nsmul_le_sum hpos
  simp at hle
  rwa [hsum] at hle

private lemma sum_count_pow_le_card' {α : Type*} [DecidableEq α] (s : Finset ℕ) (f : ℕ → α)
    (hf : Function.Injective f) (t : Multiset α) :
    ∑ k ∈ s, t.count (f k) ≤ t.card := by
  have hinjOn : Set.InjOn f s := hf.injOn
  rw [← Finset.sum_image (g := f) (f := fun a => t.count a) (s := s) hinjOn]
  have hsubset_inter : (s.image f) ∩ t.toFinset ⊆ s.image f := Finset.inter_subset_left
  have heq : ∑ a ∈ s.image f, t.count a = ∑ a ∈ (s.image f) ∩ t.toFinset, t.count a := by
    refine (Finset.sum_subset hsubset_inter ?_).symm
    intro x hx hxnot
    have : x ∉ t.toFinset := by
      intro hmem
      exact hxnot (Finset.mem_inter.mpr ⟨hx, hmem⟩)
    exact Multiset.count_eq_zero.mpr (fun h => this (Multiset.mem_toFinset.mpr h))
  rw [heq]
  have hsub : (s.image f) ∩ t.toFinset ⊆ t.toFinset := Finset.inter_subset_right
  have hbound : ∑ a ∈ (s.image f) ∩ t.toFinset, t.count a ≤ ∑ a ∈ t.toFinset, t.count a :=
    Finset.sum_le_sum_of_subset hsub
  calc ∑ a ∈ (s.image f) ∩ t.toFinset, t.count a
      ≤ ∑ a ∈ t.toFinset, t.count a := hbound
    _ = t.card := Multiset.toFinset_sum_count_eq t

private lemma sum_partMult_le_m'
    (m : ℕ) (p : Nat.Partition m) :
    ∑ k ∈ Finset.range (m + 1), partMult p (3 ^ k) ≤ m := by
  unfold partMult
  have h1 : ∑ k ∈ Finset.range (m + 1), p.parts.count (3 ^ k) ≤ p.parts.card :=
    sum_count_pow_le_card' _ _ three_pow_injective' _
  exact h1.trans (card_parts_le' m p)

private lemma exp_le_cyclotomic_two' (m : ℕ) (p : Nat.Partition m) :
    (∑ k ∈ Finset.Ioc 0 m, m / 3 ^ k)
      ≤ ∑ k ∈ Finset.range (m + 1), (m / 3 ^ k - partMult p (3 ^ k)) := by
  have hpt : ∀ k ∈ Finset.range (m + 1), partMult p (3 ^ k) ≤ m / 3 ^ k :=
    fun k _ => partMult_le_m_div_three_pow' m p k
  have hdistrib :
      ∑ k ∈ Finset.range (m + 1), (m / 3 ^ k - partMult p (3 ^ k))
        = (∑ k ∈ Finset.range (m + 1), m / 3 ^ k)
          - ∑ k ∈ Finset.range (m + 1), partMult p (3 ^ k) := by
    exact Finset.sum_tsub_distrib _ hpt
  rw [hdistrib]
  have hsplit :
      ∑ k ∈ Finset.range (m + 1), m / 3 ^ k
        = m + ∑ k ∈ Finset.Ioc 0 m, m / 3 ^ k := by
    rw [range_succ_eq_insert_Ioc' m]
    rw [Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Ioc 0 m)]
    simp
  rw [hsplit]
  have hmult : ∑ k ∈ Finset.range (m + 1), partMult p (3 ^ k) ≤ m :=
    sum_partMult_le_m' m p
  omega

private lemma sum_Ico_split_gen' {α : Type*} [AddCommMonoid α] (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m)
    (f : ℕ → α) :
    (∑ k ∈ Finset.Ico j (m + 1), f k)
      = (∑ k ∈ Finset.Ioc j m, f k) + f j := by
  have hjm : j ≤ m := (Finset.mem_Ioc.mp hj).2
  have hsplit : Finset.Ico j (m + 1) = insert j (Finset.Ioc j m) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Ioc, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  rw [add_comm]

private lemma image_three_pow_filter_subset_range'
    (m j : ℕ) :
    ((Finset.Ico j (m + 1)).image (fun k => 3 ^ k)).filter (fun a => a ≤ m)
      ⊆ Finset.range (m + 1) := by
  intro a ha
  simp only [Finset.mem_filter] at ha
  simp only [Finset.mem_range]
  omega

private lemma sum_partMult_mul_three_pow_eq_image'
    (m j : ℕ) (p : Nat.Partition m) :
    ∑ k ∈ Finset.Ico j (m + 1), partMult p (3 ^ k) * 3 ^ k
      = ∑ a ∈ (Finset.Ico j (m + 1)).image (fun k => 3 ^ k), partMult p a * a := by
  rw [Finset.sum_image]
  intro k₁ _ k₂ _ h
  exact three_pow_injective' h

private lemma le_of_mem_parts' {m : ℕ} (p : Nat.Partition m) {a : ℕ} (ha : a ∈ p.parts) :
    a ≤ m := by
  have h1 : a ≤ p.parts.sum := Multiset.le_sum_of_mem ha
  rwa [p.parts_sum] at h1

private lemma parts_toFinset_subset_range' {m : ℕ} (p : Nat.Partition m) :
    p.parts.toFinset ⊆ Finset.range (m + 1) := by
  intro a ha
  rw [Multiset.mem_toFinset] at ha
  rw [Finset.mem_range]
  exact Nat.lt_succ_of_le (le_of_mem_parts' p ha)

private lemma sum_partMult_mul_eq_m'
    (m : ℕ) (p : Nat.Partition m) :
    ∑ a ∈ Finset.range (m + 1), partMult p a * a = m := by
  have hsub : p.parts.toFinset ⊆ Finset.range (m + 1) :=
    parts_toFinset_subset_range' p
  have hsum : p.parts.sum = ∑ i ∈ Finset.range (m + 1), Multiset.count i p.parts • i :=
    Finset.sum_multiset_count_of_subset p.parts (Finset.range (m + 1)) hsub
  have hps : p.parts.sum = m := p.parts_sum
  have hrw : ∀ a : ℕ, Multiset.count a p.parts • a = partMult p a * a := by
    intro a
    simp [partMult, smul_eq_mul]
  calc ∑ a ∈ Finset.range (m + 1), partMult p a * a
      = ∑ a ∈ Finset.range (m + 1), Multiset.count a p.parts • a := by
        apply Finset.sum_congr rfl
        intros a _
        rw [hrw]
    _ = p.parts.sum := hsum.symm
    _ = m := hps

private lemma sum_image_eq_filter'
    (m j : ℕ) (p : Nat.Partition m) :
    ∑ a ∈ (Finset.Ico j (m + 1)).image (fun k => 3 ^ k), partMult p a * a
      = ∑ a ∈ ((Finset.Ico j (m + 1)).image (fun k => 3 ^ k)).filter (fun a => a ≤ m),
          partMult p a * a := by
  refine (Finset.sum_filter_of_ne ?_).symm
  intro a ha hne
  rcases Finset.mem_image.mp ha with ⟨k, _, rfl⟩
  have hmult_ne : partMult p (3 ^ k) ≠ 0 := by
    intro h
    apply hne
    rw [h]; ring
  have h_in_parts : (3 : ℕ) ^ k ∈ p.parts := by
    unfold partMult at hmult_ne
    exact (Multiset.count_ne_zero).mp hmult_ne
  have h_le_sum : (3 : ℕ) ^ k ≤ p.parts.sum :=
    Multiset.single_le_sum (fun x _ => Nat.zero_le x) _ h_in_parts
  rwa [p.parts_sum] at h_le_sum

private lemma sum_partMult_mul_three_pow_le'
    (m j : ℕ) (p : Nat.Partition m) :
    ∑ k ∈ Finset.Ico j (m + 1), partMult p (3 ^ k) * 3 ^ k ≤ m := by
  rw [sum_partMult_mul_three_pow_eq_image']
  rw [sum_image_eq_filter']
  calc ∑ a ∈ ((Finset.Ico j (m + 1)).image (fun k => 3 ^ k)).filter (fun a => a ≤ m),
          partMult p a * a
      ≤ ∑ a ∈ Finset.range (m + 1), partMult p a * a := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact image_three_pow_filter_subset_range' m j
        · intros; exact Nat.zero_le _
    _ = m := sum_partMult_mul_eq_m' m p

set_option linter.unusedVariables false in
private lemma three_pow_j_mul_sum_partMult_le'
    (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m) (p : Nat.Partition m) :
    3 ^ j * (∑ k ∈ Finset.Ico j (m + 1), partMult p (3 ^ k)) ≤ m := by
  have step1 : 3 ^ j * (∑ k ∈ Finset.Ico j (m + 1), partMult p (3 ^ k))
      ≤ ∑ k ∈ Finset.Ico j (m + 1), partMult p (3 ^ k) * 3 ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hjk : 3 ^ j ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk.1
    rw [mul_comm (partMult p (3 ^ k)) (3 ^ k)]
    exact Nat.mul_le_mul_right _ hjk
  exact step1.trans (sum_partMult_mul_three_pow_le' m j p)

private lemma sum_partMult_Ico_le_div' (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m)
    (p : Nat.Partition m) :
    (∑ k ∈ Finset.Ico j (m + 1), partMult p (3 ^ k)) ≤ m / 3 ^ j := by
  have hpos : 0 < 3 ^ j := Nat.pow_pos (by norm_num : (0:ℕ) < 3)
  rw [Nat.le_div_iff_mul_le hpos]
  rw [Nat.mul_comm]
  exact three_pow_j_mul_sum_partMult_le' m j hj p

private lemma exp_le_cyclotomic_general' (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m)
    (p : Nat.Partition m) :
    (∑ k ∈ Finset.Ioc j m, m / 3 ^ k)
      ≤ ∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k)) := by
  rw [sum_Ico_split_gen' m j hj (fun k => m / 3 ^ k - partMult p (3 ^ k))]
  have hterm : ∀ k, m / 3 ^ k = (m / 3 ^ k - partMult p (3 ^ k)) + partMult p (3 ^ k) := by
    intro k
    exact (Nat.sub_add_cancel (partMult_le_m_div_three_pow' m p k)).symm
  have hLHS : (∑ k ∈ Finset.Ioc j m, m / 3 ^ k)
      = (∑ k ∈ Finset.Ioc j m, (m / 3 ^ k - partMult p (3 ^ k)))
        + (∑ k ∈ Finset.Ioc j m, partMult p (3 ^ k)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros k _
    exact hterm k
  rw [hLHS]
  have hcount := sum_partMult_Ico_le_div' m j hj p
  have hsplit_pM : (∑ k ∈ Finset.Ico j (m + 1), partMult p (3 ^ k))
      = (∑ k ∈ Finset.Ioc j m, partMult p (3 ^ k)) + partMult p (3 ^ j) :=
    sum_Ico_split_gen' m j hj (fun k => partMult p (3 ^ k))
  rw [hsplit_pM] at hcount
  have hpartj : partMult p (3 ^ j) ≤ m / 3 ^ j := partMult_le_m_div_three_pow' m p j
  have hB_le : (∑ k ∈ Finset.Ioc j m, partMult p (3 ^ k))
      ≤ m / 3 ^ j - partMult p (3 ^ j) := by
    omega
  exact Nat.add_le_add_left hB_le _

set_option linter.unusedVariables false in
private lemma gcdRHS_dvd_hTernary' (m : ℕ) (p : Nat.Partition m)
    (hp : p ∈ ternaryPartitions m) :
    gcdRHS m ∣ hTernary m p := by
  rw [hTernary_eq_prod_cyclotomic_swap' m p, gcdRHS]
  apply mul_dvd_mul
  · exact pow_dvd_pow _ (exp_le_cyclotomic_two' m p)
  · apply Finset.prod_dvd_prod_of_dvd
    intro j hj
    exact pow_dvd_pow _ (exp_le_cyclotomic_general' m j hj p)

lemma gcdRHS_dvd_gcdHTernary (m : ℕ) : gcdRHS m ∣ gcdHTernary m := by
  unfold gcdHTernary
  refine Finset.dvd_gcd ?_
  intro p hp
  exact gcdRHS_dvd_hTernary' m p hp

end gcdRHS_dvd_gcdHTernary_section

/-- The gcd of a finset of polynomials divides each element. -/
lemma gcdHTernary_dvd_hTernary (m : ℕ) :
    ∀ p ∈ ternaryPartitions m, gcdHTernary m ∣ hTernary m p := by
  intro p hp
  unfold gcdHTernary
  exact Finset.gcd_dvd hp

/- Key identity: `hTernary m (allOnesPart m)` factors as
`gcdRHS m * cof m`. -/
section hTernary_allOnes_section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

private lemma sum_Ico_split'' (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m) :
    (∑ k ∈ Finset.Ico j (m + 1), m / 3 ^ k)
      = (∑ k ∈ Finset.Ioc j m, m / 3 ^ k) + m / 3 ^ j := by
  have hjm : j ≤ m := (Finset.mem_Ioc.mp hj).2
  have hsplit : Finset.Ico j (m + 1) = insert j (Finset.Ioc j m) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Ioc, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  ring

private lemma partMult_allOnes'' (m i : ℕ) :
    partMult (allOnesPart m) i = if i = 1 then m else 0 := by
  rw [show partMult (allOnesPart m) i = (Multiset.replicate m 1).count i by rfl]
  simp [Multiset.count_replicate, if_pos, if_neg]
  <;>
  (try cases m <;> simp_all [Nat.succ_eq_add_one, Multiset.count_replicate]) <;>
  (try aesop)

private lemma hTernary_allOnes_eq_prod_cyclotomic'' (m : ℕ) :
    hTernary m (allOnesPart m)
      = ((Polynomial.cyclotomic 2 ℤ) ^ (∑ k ∈ Finset.Ioc 0 m, m / 3 ^ k))
        * ∏ j ∈ Finset.Ioc 0 m,
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
              ^ (∑ k ∈ Finset.Ico j (m + 1), m / 3 ^ k) := by
  rw [hTernary_eq_prod_cyclotomic_swap' m (allOnesPart m)]
  congr 1
  · congr 1
    have hsplit : Finset.range (m + 1) = insert 0 (Finset.Ioc 0 m) := by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    have h0 : (m / 3 ^ 0 - partMult (allOnesPart m) (3 ^ 0) : ℕ) = 0 := by
      simp [partMult_allOnes'']
    rw [h0, zero_add]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk1 : 1 ≤ k := (Finset.mem_Ioc.mp hk).1
    have hk0 : k ≠ 0 := by omega
    have h3k : (3 : ℕ) ^ k ≠ 1 := by
      have : (3 : ℕ) ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
      omega
    simp [partMult_allOnes'', h3k, hk0]
  · refine Finset.prod_congr rfl (fun j hj => ?_)
    congr 1
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hj1 : 1 ≤ j := (Finset.mem_Ioc.mp hj).1
    have hk1 : 1 ≤ k := le_trans hj1 (Finset.mem_Ico.mp hk).1
    have hk0 : k ≠ 0 := by omega
    have h3k : (3 : ℕ) ^ k ≠ 1 := by
      have : (3 : ℕ) ^ 1 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
      omega
    simp [partMult_allOnes'', h3k, hk0]

lemma hTernary_allOnes_eq_gcdRHS_mul_cof (m : ℕ) :
    hTernary m (allOnesPart m) = gcdRHS m * cof m := by
  rw [hTernary_allOnes_eq_prod_cyclotomic'' m]
  unfold gcdRHS cof
  rw [mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro j hj
  rw [sum_Ico_split'' m j hj, pow_add]

end hTernary_allOnes_section

/-- `gcdRHS m` is nonzero (it is monic). -/
lemma gcdRHS_ne_zero (m : ℕ) : gcdRHS m ≠ 0 :=
  (gcdRHS_monic m).ne_zero

/- Section for cyclotomic_two_not_dvd_quotient_aux helpers -/
section cyclotomic_two_not_dvd_quotient_aux_section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false

private lemma cof_monic_h (m : ℕ) : (cof m).Monic := by
  unfold cof
  refine Polynomial.monic_prod_of_monic _ _ ?_
  intro j _
  exact (Polynomial.cyclotomic.monic (2 * 3 ^ j) ℤ).pow _

private lemma three_pow_ge_three_h (j : ℕ) (hj : 1 ≤ j) : (3 : ℕ) ≤ 3 ^ j := by
  calc (3 : ℕ) = 3 ^ 1 := by ring
    _ ≤ 3 ^ j := Nat.pow_le_pow_right (by decide) hj

private lemma three_pow_odd_h (j : ℕ) : Odd ((3 : ℕ) ^ j) :=
  Odd.pow (by decide)

private lemma neg_pow_ne_one_of_even_h
    {η : ℂ} {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (h : IsPrimitiveRoot η n) {m : ℕ} (hmpos : 0 < m) (hm : m < 2 * n)
    (hmeven : Even m) : (-η) ^ m ≠ 1 := by
  obtain ⟨d, hd⟩ : ∃ d, m = 2 * d := ⟨m / 2, by rcases hmeven with ⟨k, hk⟩; omega⟩
  have hdpos : 0 < d := by omega
  have h_neg_eq : (-η : ℂ) ^ m = η ^ m := by
    rw [show ((-η : ℂ)) = (-1) * η from by ring, mul_pow, hd, pow_mul,
        show ((-1 : ℂ)) ^ 2 = 1 from by norm_num, one_pow, one_mul]
  rw [h_neg_eq]
  intro heq
  have hdvd : (n : ℕ) ∣ 2 * d := by
    apply h.dvd_of_pow_eq_one
    rw [← hd]; exact_mod_cast heq
  have hcop : Nat.Coprime n 2 := (Nat.coprime_iff_gcd_eq_one).mpr <| by
    rcases hn with ⟨k, hk⟩
    simp [Nat.gcd_comm n 2, Nat.gcd, hk]
  have hnd : (n : ℕ) ∣ d := hcop.dvd_of_dvd_mul_left hdvd
  have : (n : ℕ) ≤ d := Nat.le_of_dvd hdpos hnd
  omega

private lemma neg_pow_ne_one_of_odd_h
    {η : ℂ} {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (h : IsPrimitiveRoot η n) {m : ℕ} (hmpos : 0 < m) (hm : m < 2 * n)
    (hmodd : Odd m) : (-η) ^ m ≠ 1 := by
  intro h₂
  have h_neg_pow : ((-1 : ℂ)) ^ m = -1 := Odd.neg_one_pow hmodd
  have h_neg_eq : (-η : ℂ) ^ m = - η ^ m := by
    rw [show ((-η : ℂ)) = (-1) * η from by ring, mul_pow, h_neg_pow, neg_one_mul]
  rw [h_neg_eq, neg_eq_iff_eq_neg] at h₂
  have h_sq : (η : ℂ) ^ (2 * m) = 1 := by
    rw [show 2 * m = m + m from by ring, pow_add, h₂]; ring
  have hdvd : (n : ℕ) ∣ 2 * m := by apply h.dvd_of_pow_eq_one; exact h_sq
  have hcop : Nat.Coprime n 2 := (Nat.coprime_iff_gcd_eq_one).mpr <| by
    rcases hn with ⟨k, hk⟩
    simp [Nat.gcd_comm n 2, Nat.gcd, hk]
  have hnm : (n : ℕ) ∣ m := hcop.dvd_of_dvd_mul_left hdvd
  have hnm_le : n ≤ m := Nat.le_of_dvd hmpos hnm
  have hmn : m = n := by
    obtain ⟨k, hk⟩ := hnm
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · interval_cases k
        · omega
        · rfl
      · exfalso; nlinarith
    subst hk1; omega
  rw [hmn] at h₂
  exact absurd (h.pow_eq_one.symm.trans h₂) (by norm_num)

private lemma isPrimitiveRoot_neg_of_odd_of_isPrimitiveRoot_h
    {η : ℂ} {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (h : IsPrimitiveRoot η n) :
    IsPrimitiveRoot (-η) (2 * n) := by
  refine IsPrimitiveRoot.mk_of_lt (-η) (by positivity) ?_ ?_
  · have hηn : η ^ n = 1 := h.pow_eq_one
    have h2n : (2 * n : ℕ) = n * 2 := by ring
    rw [h2n, pow_mul]
    have hen : (-η) ^ n = (-1) ^ n * η ^ n := by rw [neg_pow]
    rw [hen, hηn, mul_one]
    rcases hn with ⟨k, hk⟩
    rw [hk]
    have : ((-1 : ℂ)) ^ (2 * k + 1) = -1 := by
      rw [pow_add, pow_mul]; simp
    rw [this]; ring
  · intro m hmpos hm
    rcases Nat.even_or_odd m with hmeven | hmodd
    · exact neg_pow_ne_one_of_even_h hn hn1 h hmpos hm hmeven
    · exact neg_pow_ne_one_of_odd_h hn hn1 h hmpos hm hmodd

private lemma zeta_pow_n_eq_neg_one_h
    {ζ : ℂ} {n : ℕ} (hn1 : 1 < n)
    (h : IsPrimitiveRoot ζ (2 * n)) :
    ζ ^ n = -1 := by
  have h_sq : (ζ ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm]; exact h.pow_eq_one
  have h_ne : ζ ^ n ≠ 1 := h.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  have h_factor : (ζ ^ n - 1) * (ζ ^ n + 1) = 0 := by linear_combination h_sq
  rcases mul_eq_zero.mp h_factor with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) h_ne
  · exact eq_neg_of_add_eq_zero_left h1

private lemma neg_zeta_pow_n_eq_one_h
    {ζ : ℂ} {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (h : IsPrimitiveRoot ζ (2 * n)) :
    (-ζ) ^ n = 1 := by
  rw [show ((-ζ : ℂ)) = (-1) * ζ from by ring, mul_pow, Odd.neg_one_pow hn,
      zeta_pow_n_eq_neg_one_h hn1 h]; ring

private lemma neg_zeta_pow_ne_one_of_lt_h
    {ζ : ℂ} {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (h : IsPrimitiveRoot ζ (2 * n))
    (l : ℕ) (hl0 : 0 < l) (hln : l < n) :
    (-ζ) ^ l ≠ 1 := by
  intro heq
  have h2l : ((-ζ) ^ l) ^ 2 = 1 := by rw [heq]; ring
  have h2l' : (-ζ) ^ (2 * l) = 1 := by
    rw [show 2 * l = l * 2 from by ring, pow_mul]
    exact h2l
  have hzeta2l : ζ ^ (2 * l) = 1 := by
    have heq2 : (-ζ) ^ (2 * l) = ζ ^ (2 * l) := by
      rw [neg_pow]
      have : ((-1 : ℂ)) ^ (2 * l) = 1 := by rw [pow_mul]; norm_num
      rw [this, one_mul]
    rw [← heq2]
    exact h2l'
  have hpos : 2 * l ≠ 0 := by omega
  have hlt : 2 * l < 2 * n := by omega
  exact IsPrimitiveRoot.pow_ne_one_of_pos_of_lt h hpos hlt hzeta2l

private lemma isPrimitiveRoot_neg_of_odd_of_isPrimitiveRoot_two_mul_h
    {ζ : ℂ} {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (h : IsPrimitiveRoot ζ (2 * n)) :
    IsPrimitiveRoot (-ζ) n := by
  refine IsPrimitiveRoot.mk_of_lt (-ζ) (by linarith)
    (neg_zeta_pow_n_eq_one_h hn hn1 h) ?_
  intro l hl0 hln
  exact neg_zeta_pow_ne_one_of_lt_h hn hn1 h l hl0 hln

private lemma primitiveRoots_two_mul_eq_image_neg_of_odd_h
    {n : ℕ} (hn : Odd n) (hn1 : 1 < n) :
    primitiveRoots (2 * n) ℂ =
      (primitiveRoots n ℂ).image (fun z : ℂ => -z) := by
  have hnpos : 0 < n := by omega
  have h2npos : 0 < 2 * n := by omega
  ext ζ
  simp only [mem_primitiveRoots h2npos, Finset.mem_image,
             mem_primitiveRoots hnpos]
  constructor
  · intro hζ
    refine ⟨-ζ, ?_, by ring⟩
    exact isPrimitiveRoot_neg_of_odd_of_isPrimitiveRoot_two_mul_h hn hn1 hζ
  · rintro ⟨η, hη, rfl⟩
    exact isPrimitiveRoot_neg_of_odd_of_isPrimitiveRoot_h hn hn1 hη

private lemma cyclotomic_two_mul_eval_neg_one_of_odd_complex_h
    (n : ℕ) (hn : Odd n) (hn1 : 1 < n) :
    (Polynomial.cyclotomic (2 * n) ℂ).eval (-1) =
      (Polynomial.cyclotomic n ℂ).eval 1 := by
  have hne : n ≠ 0 := by omega
  have hη : IsPrimitiveRoot
      (Complex.exp (2 * ↑Real.pi * Complex.I * (1 / ↑n))) n := by
    have := Complex.isPrimitiveRoot_exp_of_coprime 1 n hne (Nat.coprime_one_left n)
    simpa using this
  set η := Complex.exp (2 * ↑Real.pi * Complex.I * (1 / ↑n)) with hη_def
  have hneg_η : IsPrimitiveRoot (-η) (2 * n) :=
    isPrimitiveRoot_neg_of_odd_of_isPrimitiveRoot_h hn hn1 hη
  have h2lt : 2 < n := by rcases hn with ⟨k, hk⟩; omega
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hneg_η,
      Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hη]
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  rw [primitiveRoots_two_mul_eq_image_neg_of_odd_h hn hn1]
  rw [Finset.prod_image (fun a _ b _ h => by simpa using h)]
  have hcard_even : Even (primitiveRoots n ℂ).card := by
    rw [Complex.card_primitiveRoots]
    exact Nat.totient_even h2lt
  have key : ∀ z : ℂ, -1 - -z = -(1 - z) := by intro z; ring
  simp_rw [key]
  rw [Finset.prod_neg]
  rcases hcard_even with ⟨k, hk⟩
  rw [hk, ← two_mul, pow_mul]
  simp

private lemma cyclotomic_two_mul_eval_neg_one_of_odd_int_h
    (n : ℕ) (hn : Odd n) (hn1 : 1 < n) :
    (Polynomial.cyclotomic (2 * n) ℤ).eval (-1) =
      (Polynomial.cyclotomic n ℤ).eval 1 := by
  have inj : Function.Injective ((↑) : ℤ → ℂ) := Int.cast_injective
  apply inj
  have hL :
      (((Polynomial.cyclotomic (2 * n) ℤ).eval (-1) : ℤ) : ℂ)
        = (Polynomial.cyclotomic (2 * n) ℂ).eval (-1) := by
    have h := Polynomial.eval_intCast_map (Int.castRingHom ℂ)
      (Polynomial.cyclotomic (2 * n) ℤ) (-1)
    rw [Polynomial.map_cyclotomic_int] at h
    push_cast at h
    exact h.symm
  have hR :
      (((Polynomial.cyclotomic n ℤ).eval 1 : ℤ) : ℂ)
        = (Polynomial.cyclotomic n ℂ).eval 1 := by
    have h := Polynomial.eval_intCast_map (Int.castRingHom ℂ)
      (Polynomial.cyclotomic n ℤ) 1
    rw [Polynomial.map_cyclotomic_int] at h
    push_cast at h
    exact h.symm
  rw [hL, hR]
  exact cyclotomic_two_mul_eval_neg_one_of_odd_complex_h n hn hn1

private lemma cyclotomic_two_mul_eval_neg_one_of_odd_h
    {R : Type*} [CommRing R] (n : ℕ) (hn : Odd n) (hn1 : 1 < n) :
    (Polynomial.cyclotomic (2 * n) R).eval (-1) =
      (Polynomial.cyclotomic n R).eval 1 := by
  have hZ : (Polynomial.cyclotomic (2 * n) ℤ).eval (-1) =
      (Polynomial.cyclotomic n ℤ).eval 1 :=
    cyclotomic_two_mul_eval_neg_one_of_odd_int_h n hn hn1
  rw [← map_cyclotomic_int (2 * n) R, ← map_cyclotomic_int n R]
  rw [show ((-1 : R)) = (Int.castRingHom R) (-1 : ℤ) by simp]
  rw [show ((1 : R)) = (Int.castRingHom R) (1 : ℤ) by simp]
  rw [eval_map_apply, eval_map_apply]
  exact congrArg (Int.castRingHom R) hZ

private lemma cyclotomic_three_pow_eval_one_h (j : ℕ) (hj : 1 ≤ j) :
    (Polynomial.cyclotomic (3 ^ j) ℤ).eval 1 = 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  simpa using Polynomial.eval_one_cyclotomic_prime_pow (R := ℤ) (p := 3) k (by decide)

private lemma cyclotomic_two_mul_three_pow_eval_neg_one_h (j : ℕ) (hj : 1 ≤ j) :
    (Polynomial.cyclotomic (2 * 3 ^ j) ℤ).eval (-1) = 3 := by
  have hodd : Odd ((3 : ℕ) ^ j) := three_pow_odd_h j
  have hge : 1 < (3 : ℕ) ^ j := by
    have := three_pow_ge_three_h j hj
    omega
  rw [cyclotomic_two_mul_eval_neg_one_of_odd_h (R := ℤ) (3 ^ j) hodd hge]
  exact cyclotomic_three_pow_eval_one_h j hj

private lemma cof_eval_neg_one_eq_h (m : ℕ) :
    (cof m).eval (-1) = ∏ j ∈ Finset.Ioc 0 m, (3 : ℤ) ^ (m / 3 ^ j) := by
  unfold cof
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Ioc.mp hj).1
  rw [Polynomial.eval_pow, cyclotomic_two_mul_three_pow_eval_neg_one_h j hj1]

private lemma cof_eval_neg_one_ne_zero_h (m : ℕ) : (cof m).eval (-1) ≠ 0 := by
  rw [cof_eval_neg_one_eq_h]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact pow_ne_zero _ (by norm_num)

private lemma cyclotomic_two_not_dvd_cof_h (m : ℕ) :
    ¬ (Polynomial.cyclotomic 2 ℤ) ∣ cof m := by
  intro ⟨q, hq⟩
  have heval : (cof m).eval (-1) = 0 := by
    rw [hq, Polynomial.eval_mul, Polynomial.cyclotomic_two]
    simp
  exact cof_eval_neg_one_ne_zero_h m heval

/-- **Helper: prime cancellation for `Φ_2 = X + 1`.**  If we have a
factorisation `gcdHTernary m = gcdRHS m * Q`, then `Φ_2` does not divide `Q`. -/
lemma cyclotomic_two_not_dvd_quotient_aux (m : ℕ)
    (Q : Polynomial ℤ) (hQ : gcdHTernary m = gcdRHS m * Q) :
    ¬ (Polynomial.cyclotomic 2 ℤ) ∣ Q := by
  have hcof_monic := cof_monic_h m
  have hcof_eq : hTernary m (allOnesPart m) = gcdRHS m * cof m :=
    hTernary_allOnes_eq_gcdRHS_mul_cof m
  have hcof_not_dvd := cyclotomic_two_not_dvd_cof_h m
  have hmem : allOnesPart m ∈ ternaryPartitions m :=
    allOnesPart_mem_ternaryPartitions m
  have hdvd : gcdHTernary m ∣ hTernary m (allOnesPart m) :=
    gcdHTernary_dvd_hTernary m (allOnesPart m) hmem
  rw [hQ, hcof_eq] at hdvd
  have hG_monic : (gcdRHS m).Monic := gcdRHS_monic m
  have hG_ne : gcdRHS m ≠ 0 := hG_monic.ne_zero
  have hQ_dvd_cof : Q ∣ cof m := by
    rcases hdvd with ⟨r, hr⟩
    have hr' : gcdRHS m * cof m = gcdRHS m * (Q * r) := by rw [hr]; ring
    have := mul_left_cancel₀ hG_ne hr'
    exact ⟨r, this⟩
  intro hcyc_dvd_Q
  exact hcof_not_dvd (hcyc_dvd_Q.trans hQ_dvd_cof)

end cyclotomic_two_not_dvd_quotient_aux_section

/- Section for cyclotomic_not_dvd_quotient_aux -/
section cyclotomic_not_dvd_quotient_aux_section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false

private def witnessPart (m j : ℕ) : Nat.Partition m where
  parts := Multiset.replicate (m / 3 ^ j) (3 ^ j) + Multiset.replicate (m % 3 ^ j) 1
  parts_pos := by
    intro i hi
    rw [Multiset.mem_add] at hi
    rcases hi with hi | hi
    · rw [Multiset.mem_replicate] at hi
      obtain ⟨_, rfl⟩ := hi
      exact Nat.pos_of_ne_zero (by positivity)
    · rw [Multiset.mem_replicate] at hi
      omega
  parts_sum := by
    simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod m (3 ^ j)

/-- For every natural number `j`, we have `j ≤ 3 ^ j`. -/
private lemma j_le_three_pow_j (j : ℕ) : j ≤ 3 ^ j :=
  (Nat.lt_pow_self (by norm_num)).le

/-- **Helper: `witnessPart m j ∈ ternaryPartitions m`** for any `m`, `j`.
The partition consists only of parts equal to `3^j` and `1 = 3^0`, all powers of 3. -/
private lemma witnessPart_mem_ternaryPartitions (m j : ℕ) :
    witnessPart m j ∈ ternaryPartitions m := by
  unfold ternaryPartitions
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro i hi
  show IsPow3 i
  change i ∈ Multiset.replicate (m / 3 ^ j) (3 ^ j) + Multiset.replicate (m % 3 ^ j) 1 at hi
  rw [Multiset.mem_add] at hi
  rcases hi with hi | hi
  · rw [Multiset.mem_replicate] at hi
    obtain ⟨_, rfl⟩ := hi
    exact ⟨j, j_le_three_pow_j j, rfl⟩
  · rw [Multiset.mem_replicate] at hi
    obtain ⟨_, rfl⟩ := hi
    exact ⟨0, Nat.zero_le _, by norm_num⟩

/-- The gcd `gcdHTernary m` divides every summand `hTernary m p` for
`p ∈ ternaryPartitions m`.  Follows directly from `Finset.gcd_dvd`. -/
private lemma gcdHTernary_dvd_hTernary_h (m : ℕ) (p : Nat.Partition m)
    (hp : p ∈ ternaryPartitions m) :
    gcdHTernary m ∣ hTernary m p := by
  unfold gcdHTernary
  exact Finset.gcd_dvd hp

/-- **Helper: the polynomial `gcdRHS m` is monic.** -/
private lemma gcdRHS_monic_h (m : ℕ) : (gcdRHS m).Monic := by
  unfold gcdRHS
  exact (Polynomial.cyclotomic.monic 2 ℤ).pow _ |>.mul
    (Polynomial.monic_prod_of_monic _ _ (fun j _ =>
      (Polynomial.cyclotomic.monic (2 * 3 ^ j) ℤ).pow _))


-- BEGIN SUPPORTING LEMMAS FROM to_merge/Conj9.hTernary_witness_factor.lean
/-- The difference of squares identity for `X^(3^k)`:
    `X^(2 * 3^k) - 1 = (X^(3^k) - 1) * (X^(3^k) + 1)` in `ℤ[X]`. -/
private lemma X_pow_two_three_pow_sub_one_eq_mul (k : ℕ) :
    (Polynomial.X : Polynomial ℤ) ^ (2 * 3 ^ k) - 1
      = (Polynomial.X ^ (3 ^ k) - 1) * (Polynomial.X ^ (3 ^ k) + 1) := by
  have h2 : (2 : ℕ) * 3 ^ k = 3 ^ k + 3 ^ k := by ring
  rw [h2, pow_add]
  ring

/-- `3^k ∣ 2 * 3^k`. -/
private lemma three_pow_dvd_two_mul (k : ℕ) : 3 ^ k ∣ 2 * 3 ^ k :=
  ⟨2, by ring⟩

/-- `2 * 3^k ≠ 0`. -/
private lemma two_mul_three_pow_ne_zero (k : ℕ) : (2 * 3 ^ k : ℕ) ≠ 0 := by
  have : (3 : ℕ) ^ k ≥ 1 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  omega

/-- The map `j ↦ 2 * 3^j` is injective on `ℕ`. -/
private lemma two_mul_three_pow_injective : Function.Injective (fun j : ℕ => 2 * 3 ^ j) := by
  intro a b hab
  simp only at hab
  have : (3 : ℕ) ^ a = 3 ^ b := by omega
  exact Nat.pow_right_injective (by norm_num) this

/-- `X^(3^k) - 1 ≠ 0` in `ℤ[X]`. -/
private lemma X_pow_three_pow_sub_one_ne_zero (k : ℕ) :
    (Polynomial.X : Polynomial ℤ) ^ (3 ^ k) - 1 ≠ 0 := by
  intro h
  have hdeg : ((Polynomial.X : Polynomial ℤ) ^ (3 ^ k) - 1).natDegree = 3 ^ k := by
    have hrw : (Polynomial.X : Polynomial ℤ) ^ (3 ^ k) - 1
              = Polynomial.X ^ (3 ^ k) + Polynomial.C (-1) := by
      rw [Polynomial.C_neg, Polynomial.C_1]; ring
    rw [hrw]
    exact Polynomial.natDegree_X_pow_add_C
  rw [h, Polynomial.natDegree_zero] at hdeg
  have : (3 : ℕ) ^ k ≥ 1 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
  omega

/-- If `j ≤ k`, then `2 * 3^j ∣ 2 * 3^k`. -/
private lemma two_mul_three_pow_dvd_two_mul_three_pow
    (j k : ℕ) (h : j ≤ k) : 2 * 3 ^ j ∣ 2 * 3 ^ k := by
  exact Nat.mul_dvd_mul_left 2 (pow_dvd_pow 3 h)

/-- If `d ∣ 2 * 3^k` and `¬ d ∣ 3^k`, then `d = 2 * 3^j` for some `j ≤ k`. -/
private lemma exists_eq_two_mul_three_pow_of_dvd_not_dvd_h
    (k d : ℕ) (h1 : d ∣ 2 * 3 ^ k) (h2 : ¬ d ∣ 3 ^ k) :
    ∃ j ≤ k, d = 2 * 3 ^ j := by
  -- Step 1: show 2 ∣ d
  have h2dvd : 2 ∣ d := by
    by_contra h2nd
    -- 2 is prime; since 2 ∤ d, gcd(2,d)=1, i.e. Coprime 2 d
    have hcop : Nat.Coprime 2 d :=
      (Nat.prime_two.coprime_iff_not_dvd).mpr h2nd
    -- From d ∣ 2 * 3^k and Coprime d 2, d ∣ 3^k
    exact h2 (hcop.symm.dvd_of_dvd_mul_left h1)
  -- Step 2: obtain x with d = 2 * x
  obtain ⟨x, hx⟩ := h2dvd
  -- Step 3: x ∣ 3^k by cancelling 2
  have hxdvd : x ∣ 3 ^ k := by
    have : 2 * x ∣ 2 * 3 ^ k := hx ▸ h1
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0:ℕ) < 2)).mp this
  -- Step 4: x = 3^j for some j ≤ k
  obtain ⟨j, hj, hxj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hxdvd
  -- Step 5: conclude
  exact ⟨j, hj, by rw [hx, hxj]⟩

private lemma two_mul_three_pow_not_dvd_three_pow_h (j k : ℕ) : ¬ (2 * 3 ^ j ∣ 3 ^ k) := by
  intro h
  have h₁ : 2 ∣ 3 ^ k := by
    have h₂ : 2 ∣ 2 * 3 ^ j := by
      apply dvd_mul_right
    exact dvd_trans h₂ h
  have h₂ : ¬(2 ∣ 3 ^ k) := by
    have h₃ : ∀ n : ℕ, 3 ^ n % 2 = 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ]
        simp [Nat.mul_mod, ih, Nat.pow_mod]
    have h₄ : 3 ^ k % 2 = 1 := h₃ k
    omega
  exact h₂ h₁

/-- The divisors of `2 * 3^k` not dividing `3^k` are exactly `{2 * 3^j : 0 ≤ j ≤ k}`. -/
private lemma divisors_two_mul_three_pow_sdiff_divisors_three_pow (k : ℕ) :
    (2 * 3 ^ k).divisors \ (3 ^ k).divisors
      = (Finset.range (k + 1)).image (fun j => 2 * 3 ^ j) := by
  ext d
  simp only [Finset.mem_sdiff, Nat.mem_divisors, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨hd1, hne⟩, hd2⟩
    -- d ∣ 2 * 3^k and ¬ (d ∣ 3^k ∧ 3^k ≠ 0)
    have h3k : (3 : ℕ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have hnd : ¬ d ∣ 3 ^ k := by
      intro hdvd
      exact hd2 ⟨hdvd, h3k⟩
    obtain ⟨j, hjk, hdj⟩ := exists_eq_two_mul_three_pow_of_dvd_not_dvd_h k d hd1 hnd
    exact ⟨j, Nat.lt_succ_of_le hjk, hdj.symm⟩
  · rintro ⟨j, hj, hdj⟩
    have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
    subst hdj
    refine ⟨⟨two_mul_three_pow_dvd_two_mul_three_pow j k hjk, ?_⟩, ?_⟩
    · have : (2 : ℕ) * 3 ^ k ≠ 0 := by positivity
      exact this
    · intro ⟨hdvd, _⟩
      exact two_mul_three_pow_not_dvd_three_pow_h j k hdvd

/-- Cyclotomic factorisation of `1 + X^(3^k)` in `ℤ[X]`:
    `1 + X^(3^k) = ∏_{j=0..k} Φ_{2·3^j}(ℤ)`.

This is the special case of the general identity `X^N - 1 = ∏_{d|N} Φ_d`:
take `N = 2·3^k`, then divide by `X^(3^k) - 1 = ∏_{d|3^k} Φ_d`. The remaining
divisors of `2·3^k` not dividing `3^k` are exactly `{2·3^0, 2·3^1, …, 2·3^k}`. -/
private lemma one_add_X_pow_three_pow_eq_prod_cyclotomic (k : ℕ) :
    (1 : Polynomial ℤ) + Polynomial.X ^ (3 ^ k)
      = ∏ j ∈ Finset.range (k + 1), Polynomial.cyclotomic (2 * 3 ^ j) ℤ := by
  -- Step 1: cyclotomic identity giving (X^(3^k) - 1) * ∏ Φ_x = X^(2*3^k) - 1.
  have h_cyc :
      (Polynomial.X ^ (3 ^ k) - 1 : Polynomial ℤ)
        * ∏ x ∈ (2 * 3 ^ k).divisors \ (3 ^ k).divisors,
            Polynomial.cyclotomic x ℤ
      = Polynomial.X ^ (2 * 3 ^ k) - 1 :=
    Polynomial.X_pow_sub_one_mul_prod_cyclotomic_eq_X_pow_sub_one_of_dvd ℤ
      (three_pow_dvd_two_mul k) (two_mul_three_pow_ne_zero k)
  -- Step 2: difference of squares
  have h_diff := X_pow_two_three_pow_sub_one_eq_mul k
  -- Step 3: combine and cancel.
  rw [h_diff] at h_cyc
  have h_ne : (Polynomial.X : Polynomial ℤ) ^ (3 ^ k) - 1 ≠ 0 :=
    X_pow_three_pow_sub_one_ne_zero k
  have h_eq : (Polynomial.X ^ (3 ^ k) + 1 : Polynomial ℤ)
        = ∏ x ∈ (2 * 3 ^ k).divisors \ (3 ^ k).divisors, Polynomial.cyclotomic x ℤ := by
    exact (mul_left_cancel₀ h_ne h_cyc).symm
  -- Step 4: rewrite the divisor difference as an image and use prod_image.
  have h_set := divisors_two_mul_three_pow_sdiff_divisors_three_pow k
  rw [h_set] at h_eq
  rw [Finset.prod_image (fun a _ b _ h => two_mul_three_pow_injective h)] at h_eq
  rw [add_comm 1 _]
  exact h_eq

/-- **Helper 1.** Express `hTernary m p` as a single product over `k ∈ range(m+1)`
of nested products over `j ∈ range(k+1)` of cyclotomic factors. -/
private lemma hTernary_eq_double_prod (m : ℕ) (p : Nat.Partition m) :
    hTernary m p
      = ∏ k ∈ Finset.range (m + 1),
          ∏ j ∈ Finset.range (k + 1),
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ k - partMult p (3 ^ k)) := by
  unfold hTernary
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [one_add_X_pow_three_pow_eq_prod_cyclotomic k]
  rw [Finset.prod_pow]

/-- Step 1: swap order of the double product using `Finset.prod_comm'`. -/
private lemma swap_double_prod_general_swap (m : ℕ) (p : Nat.Partition m) :
    (∏ k ∈ Finset.range (m + 1),
        ∏ j ∈ Finset.range (k + 1),
          (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ k - partMult p (3 ^ k)))
      = ∏ j ∈ Finset.range (m + 1),
          ∏ k ∈ Finset.Ico j (m + 1),
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ k - partMult p (3 ^ k)) := by
  apply Finset.prod_comm'
  intro k j
  simp only [Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨hk, hj⟩
    refine ⟨⟨?_, hk⟩, ?_⟩
    · omega
    · omega
  · rintro ⟨⟨hjk, hk⟩, hj⟩
    refine ⟨hk, ?_⟩
    omega

/-- Step 2: collect exponents using `Finset.prod_pow_eq_pow_sum`. -/
private lemma swap_double_prod_general_collect (m : ℕ) (p : Nat.Partition m) :
    (∏ j ∈ Finset.range (m + 1),
        ∏ k ∈ Finset.Ico j (m + 1),
          (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ k - partMult p (3 ^ k)))
      = ∏ j ∈ Finset.range (m + 1),
          (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
            ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
  refine Finset.prod_congr rfl ?_
  intro j _
  exact Finset.prod_pow_eq_pow_sum (Finset.Ico j (m + 1))
    (fun k => m / 3 ^ k - partMult p (3 ^ k)) (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)

private lemma swap_double_prod_general_split (m : ℕ) (p : Nat.Partition m) :
    (∏ j ∈ Finset.range (m + 1),
        (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
          ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))))
      = ((Polynomial.cyclotomic 2 ℤ) ^
            (∑ k ∈ Finset.range (m + 1), (m / 3 ^ k - partMult p (3 ^ k))))
        * ∏ j ∈ Finset.Ioc 0 m,
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
              ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
  have h₀ : Finset.range (m + 1) = {0} ∪ Finset.Ioc 0 m := by
    apply Finset.ext
    intro x
    simp [Finset.mem_range, Finset.mem_Ioc, Nat.lt_succ_iff]
  
  calc
    (∏ j ∈ Finset.range (m + 1),
        (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
          ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))))
      = ∏ j ∈ ({0} ∪ Finset.Ioc 0 m),
        (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
          ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
        rw [h₀]
    _ = ∏ j ∈ ({0} : Finset ℕ),
        (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
          ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) *
      ∏ j ∈ Finset.Ioc 0 m,
        (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
          ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
        rw [Finset.prod_union]
        <;> simp [Finset.disjoint_left]
    _ = (Polynomial.cyclotomic (2 * 3 ^ 0) ℤ) ^ (∑ k ∈ Finset.Ico 0 (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) *
      ∏ j ∈ Finset.Ioc 0 m,
        (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
          ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
        simp [Finset.prod_singleton]
    _ = ((Polynomial.cyclotomic 2 ℤ) ^
            (∑ k ∈ Finset.range (m + 1), (m / 3 ^ k - partMult p (3 ^ k))))
        * ∏ j ∈ Finset.Ioc 0 m,
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
              ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
        have h₁ : (Polynomial.cyclotomic (2 * 3 ^ 0) ℤ) = Polynomial.cyclotomic 2 ℤ := by
          norm_num
        rw [h₁]
        have h₂ : (∑ k ∈ Finset.Ico 0 (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) = (∑ k ∈ Finset.range (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
          have h₃ : Finset.Ico 0 (m + 1) = Finset.range (m + 1) := by
            ext x
            simp [Finset.mem_Ico, Finset.mem_range]
          rw [h₃]
        rw [h₂]

/-- **Helper B.** Swap the order of the double product, collecting exponents
for each `j` into a sum over `k`, then split off the `j = 0` term. -/
private lemma swap_double_prod_general (m : ℕ) (p : Nat.Partition m) :
    (∏ k ∈ Finset.range (m + 1),
        ∏ j ∈ Finset.range (k + 1),
          (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ k - partMult p (3 ^ k)))
      = ((Polynomial.cyclotomic 2 ℤ) ^
            (∑ k ∈ Finset.range (m + 1), (m / 3 ^ k - partMult p (3 ^ k))))
        * ∏ j ∈ Finset.Ioc 0 m,
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
              ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
  rw [swap_double_prod_general_swap m p,
      swap_double_prod_general_collect m p,
      swap_double_prod_general_split m p]

/-- **Main result.** Express `hTernary m p` as a product where the `j = 0`
factor is `(cyclotomic 2 ℤ)` raised to a sum over `k ∈ range (m+1)`, and the
remaining factors are over `j ∈ Ioc 0 m`. -/
private lemma hTernary_eq_prod_cyclotomic_swap (m : ℕ) (p : Nat.Partition m) :
    hTernary m p
      = ((Polynomial.cyclotomic 2 ℤ) ^
            (∑ k ∈ Finset.range (m + 1), (m / 3 ^ k - partMult p (3 ^ k))))
        * ∏ j ∈ Finset.Ioc 0 m,
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
              ^ (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k))) := by
  rw [hTernary_eq_double_prod m p, swap_double_prod_general m p]

private lemma partMult_mul_three_pow_le
    (m : ℕ) (p : Nat.Partition m) (k : ℕ) :
    partMult p (3 ^ k) * 3 ^ k ≤ m := by
  have h_main : partMult p (3 ^ k) * 3 ^ k ≤ p.parts.sum := by
    unfold partMult
    have hfilter : (p.parts.filter (Eq (3 ^ k))).sum = p.parts.count (3 ^ k) * 3 ^ k := by
      rw [Multiset.filter_eq]
      rw [Multiset.sum_replicate]
      simp [mul_comm]
    rw [← hfilter]
    have hsplit := @Multiset.sum_filter_add_sum_filter_not ℕ _ p.parts (Eq (3 ^ k)) _
    omega
  have h_sum_eq_m : p.parts.sum = m := p.parts_sum
  omega

/-- `partMult p (3^k) ≤ m / 3^k`, because the parts of size `3^k` contribute
exactly `3^k * partMult p (3^k)` to the sum `∑ parts = m`. -/
private lemma partMult_le_m_div_three_pow
    (m : ℕ) (p : Nat.Partition m) (k : ℕ) :
    partMult p (3 ^ k) ≤ m / 3 ^ k := by
  have hpos : 0 < (3 : ℕ) ^ k := pow_pos (by norm_num) k
  exact (Nat.le_div_iff_mul_le hpos).mpr (partMult_mul_three_pow_le m p k)

private lemma range_succ_eq_insert_Ioc (m : ℕ) :
    Finset.range (m + 1) = insert 0 (Finset.Ioc 0 m) := by
  ext x
  simp only [Finset.mem_range, Finset.mem_Ioc, Finset.mem_insert]
  omega

/-- `3 ^ · : ℕ → ℕ` is injective. -/
private lemma three_pow_injective : Function.Injective (fun k : ℕ => 3 ^ k) :=
  fun _ _ h => Nat.pow_right_injective (by norm_num) h

/-- For any partition of `m`, `p.parts.card ≤ m` (every part is at least `1`,
and the parts sum to `m`). -/
private lemma card_parts_le (m : ℕ) (p : Nat.Partition m) : p.parts.card ≤ m := by
  have hsum : p.parts.sum = m := p.parts_sum
  have hpos : ∀ x ∈ p.parts, 1 ≤ x := fun x hx => p.parts_pos hx
  have hle : p.parts.card • 1 ≤ p.parts.sum := Multiset.card_nsmul_le_sum hpos
  simp at hle
  rwa [hsum] at hle

/-- The sum of `Multiset.count` values over the image of an injective function from a Finset
is bounded by the multiset cardinality. Specifically, when `f : ℕ → ℕ` is injective
(here `f k = 3^k`), the sum `∑ k ∈ s, t.count (f k)` ≤ `t.card`. -/
private lemma sum_count_pow_le_card {α : Type*} [DecidableEq α] (s : Finset ℕ) (f : ℕ → α)
    (hf : Function.Injective f) (t : Multiset α) :
    ∑ k ∈ s, t.count (f k) ≤ t.card := by
  -- Step 1: rewrite via image of `f`
  have hinjOn : Set.InjOn f s := hf.injOn
  rw [← Finset.sum_image (g := f) (f := fun a => t.count a) (s := s) hinjOn]
  -- Step 2: drop zero terms outside `t.toFinset`
  have hdrop : ∀ a ∈ (s.image f), a ∉ (s.image f ∩ t.toFinset) → t.count a = 0 := by
    intro a ha hnot
    have : a ∉ t.toFinset := by
      intro hmem
      exact hnot (Finset.mem_inter.mpr ⟨ha, hmem⟩)
    exact Multiset.count_eq_zero.mpr (fun h => this (Multiset.mem_toFinset.mpr h))
  have hsubset_inter : (s.image f) ∩ t.toFinset ⊆ s.image f := Finset.inter_subset_left
  have heq : ∑ a ∈ s.image f, t.count a = ∑ a ∈ (s.image f) ∩ t.toFinset, t.count a := by
    refine (Finset.sum_subset hsubset_inter ?_).symm
    intro x hx hxnot
    -- x ∈ s.image f, x ∉ inter ⇒ x ∉ t.toFinset ⇒ count = 0
    have : x ∉ t.toFinset := by
      intro hmem
      exact hxnot (Finset.mem_inter.mpr ⟨hx, hmem⟩)
    exact Multiset.count_eq_zero.mpr (fun h => this (Multiset.mem_toFinset.mpr h))
  rw [heq]
  -- Step 3: bound by sum over `t.toFinset`
  have hsub : (s.image f) ∩ t.toFinset ⊆ t.toFinset := Finset.inter_subset_right
  have hbound : ∑ a ∈ (s.image f) ∩ t.toFinset, t.count a ≤ ∑ a ∈ t.toFinset, t.count a :=
    Finset.sum_le_sum_of_subset hsub
  -- Step 4: cardinality identity
  calc ∑ a ∈ (s.image f) ∩ t.toFinset, t.count a
      ≤ ∑ a ∈ t.toFinset, t.count a := hbound
    _ = t.card := Multiset.toFinset_sum_count_eq t

/-- The sum of multiplicities of `3^k` for `k ∈ range (m+1)` is at most `m`.
This is because the multiplicities (over all distinct powers of 3 that appear
as parts) sum to at most the number of parts, which is at most `m` (since
every part is at least 1). -/
private lemma sum_partMult_le_m
    (m : ℕ) (p : Nat.Partition m) :
    ∑ k ∈ Finset.range (m + 1), partMult p (3 ^ k) ≤ m := by
  unfold partMult
  have h1 : ∑ k ∈ Finset.range (m + 1), p.parts.count (3 ^ k) ≤ p.parts.card :=
    sum_count_pow_le_card _ _ three_pow_injective _
  exact h1.trans (card_parts_le m p)

/-- **Helper 3a.** Exponent inequality for the `cyclotomic 2` factor (the `j = 0` case).
The exponent `∑ k ∈ Ioc 0 m, m/3^k` in `gcdRHS m` is at most the exponent
`∑ k ∈ range (m+1), (m/3^k - partMult p (3^k))` in `hTernary m p`. -/
private lemma exp_le_cyclotomic_two (m : ℕ) (p : Nat.Partition m) :
    (∑ k ∈ Finset.Ioc 0 m, m / 3 ^ k)
      ≤ ∑ k ∈ Finset.range (m + 1), (m / 3 ^ k - partMult p (3 ^ k)) := by
  -- Step 1: Pointwise inequality `partMult p (3^k) ≤ m / 3^k`.
  have hpt : ∀ k ∈ Finset.range (m + 1), partMult p (3 ^ k) ≤ m / 3 ^ k :=
    fun k _ => partMult_le_m_div_three_pow m p k
  -- Step 2: Distribute the subtraction.
  have hdistrib :
      ∑ k ∈ Finset.range (m + 1), (m / 3 ^ k - partMult p (3 ^ k))
        = (∑ k ∈ Finset.range (m + 1), m / 3 ^ k)
          - ∑ k ∈ Finset.range (m + 1), partMult p (3 ^ k) := by
    exact Finset.sum_tsub_distrib _ hpt
  rw [hdistrib]
  -- Step 3: Split the divisor sum across k=0.
  have hsplit :
      ∑ k ∈ Finset.range (m + 1), m / 3 ^ k
        = m + ∑ k ∈ Finset.Ioc 0 m, m / 3 ^ k := by
    rw [range_succ_eq_insert_Ioc m]
    rw [Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Ioc 0 m)]
    simp
  rw [hsplit]
  -- Step 4: Bound the multiplicity sum.
  have hmult : ∑ k ∈ Finset.range (m + 1), partMult p (3 ^ k) ≤ m :=
    sum_partMult_le_m m p
  -- Step 5: Combine.
  omega

/-- Exponent identity: for `j ∈ Finset.Ioc 0 m`, the LHS exponent
`∑_{k ∈ Finset.Ico j (m+1)} f k` equals `(∑_{k ∈ Finset.Ioc j m} f k) + f j`. -/
private lemma sum_Ico_split_gen {α : Type*} [AddCommMonoid α] (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m)
    (f : ℕ → α) :
    (∑ k ∈ Finset.Ico j (m + 1), f k)
      = (∑ k ∈ Finset.Ioc j m, f k) + f j := by
  have hjm : j ≤ m := (Finset.mem_Ioc.mp hj).2
  have hsplit : Finset.Ico j (m + 1) = insert j (Finset.Ioc j m) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Ioc, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  rw [add_comm]

/-- The image of `Ico j (m+1)` under `k ↦ 3^k`, after filtering by `a ≤ m`,
is a subset of `Finset.range (m+1)`. -/
private lemma image_three_pow_filter_subset_range
    (m j : ℕ) :
    ((Finset.Ico j (m + 1)).image (fun k => 3 ^ k)).filter (fun a => a ≤ m)
      ⊆ Finset.range (m + 1) := by
  intro a ha
  simp only [Finset.mem_filter] at ha
  simp only [Finset.mem_range]
  omega

/-- Reindexing: by injectivity of `k ↦ 3^k`,
    `∑ k ∈ Ico j (m+1), partMult p (3^k) * 3^k
      = ∑ a ∈ (Ico j (m+1)).image (3^·), partMult p a * a`. -/
private lemma sum_partMult_mul_three_pow_eq_image
    (m j : ℕ) (p : Nat.Partition m) :
    ∑ k ∈ Finset.Ico j (m + 1), partMult p (3 ^ k) * 3 ^ k
      = ∑ a ∈ (Finset.Ico j (m + 1)).image (fun k => 3 ^ k), partMult p a * a := by
  rw [Finset.sum_image]
  intro k₁ _ k₂ _ h
  exact three_pow_injective h

/-- If a part `a` has positive multiplicity in `p`, then `a ≤ m`.
This follows because every element of a multiset of ℕ is ≤ the multiset sum,
and `p.parts.sum = m` by definition of `Nat.Partition`. -/
private lemma le_of_partMult_pos
    (m : ℕ) (p : Nat.Partition m) (a : ℕ) (h : 0 < partMult p a) :
    a ≤ m := by
  -- Unfold partMult to count
  unfold partMult at h
  -- 0 < count a p.parts → a ∈ p.parts
  have hmem : a ∈ p.parts := Multiset.count_pos.mp h
  -- a ∈ p.parts → a ≤ p.parts.sum
  have hle : a ≤ p.parts.sum := Multiset.le_sum_of_mem hmem
  -- p.parts.sum = m
  rwa [p.parts_sum] at hle

/-- Any part `a` of a partition `p : Nat.Partition m` satisfies `a ≤ m`.
This follows from `Multiset.le_sum_of_mem` applied to `p.parts`, together with
`p.parts_sum`. -/
private lemma le_of_mem_parts {m : ℕ} (p : Nat.Partition m) {a : ℕ} (ha : a ∈ p.parts) :
    a ≤ m := by
  have h1 : a ≤ p.parts.sum := Multiset.le_sum_of_mem ha
  rwa [p.parts_sum] at h1

/-- The toFinset of the parts of a partition of `m` is contained in `Finset.range (m+1)`.
This is because every part `a ∈ p.parts` satisfies `a ≤ m` (hence `a < m+1`). -/
private lemma parts_toFinset_subset_range {m : ℕ} (p : Nat.Partition m) :
    p.parts.toFinset ⊆ Finset.range (m + 1) := by
  intro a ha
  rw [Multiset.mem_toFinset] at ha
  rw [Finset.mem_range]
  exact Nat.lt_succ_of_le (le_of_mem_parts p ha)

/-- The sum over `Finset.range (m+1)` of `partMult p a * a` equals `m`.
This uses `Multiset.sum_eq_sum_count` to express `p.parts.sum` as a sum of
`count a * a` over `p.parts.toFinset`, then extends the sum to all of
`range (m+1)` since the extra terms have multiplicity zero. -/
private lemma sum_partMult_mul_eq_m
    (m : ℕ) (p : Nat.Partition m) :
    ∑ a ∈ Finset.range (m + 1), partMult p a * a = m := by
  -- Use Finset.sum_multiset_count_of_subset
  have hsub : p.parts.toFinset ⊆ Finset.range (m + 1) :=
    parts_toFinset_subset_range p
  have hsum : p.parts.sum = ∑ i ∈ Finset.range (m + 1), Multiset.count i p.parts • i :=
    Finset.sum_multiset_count_of_subset p.parts (Finset.range (m + 1)) hsub
  have hps : p.parts.sum = m := p.parts_sum
  -- Note: in ℕ, c • a = c * a
  have hrw : ∀ a : ℕ, Multiset.count a p.parts • a = partMult p a * a := by
    intro a
    simp [partMult, smul_eq_mul]
  calc ∑ a ∈ Finset.range (m + 1), partMult p a * a
      = ∑ a ∈ Finset.range (m + 1), Multiset.count a p.parts • a := by
        apply Finset.sum_congr rfl
        intros a _
        rw [hrw]
    _ = p.parts.sum := hsum.symm
    _ = m := hps

/-- The terms with `a > m` in the image sum contribute zero.  Hence:
    `∑ a ∈ image, partMult p a * a
       = ∑ a ∈ image.filter (· ≤ m), partMult p a * a`. -/
private lemma sum_image_eq_filter
    (m j : ℕ) (p : Nat.Partition m) :
    ∑ a ∈ (Finset.Ico j (m + 1)).image (fun k => 3 ^ k), partMult p a * a
      = ∑ a ∈ ((Finset.Ico j (m + 1)).image (fun k => 3 ^ k)).filter (fun a => a ≤ m),
          partMult p a * a := by
  -- Apply `Finset.sum_filter_of_ne` (with `Eq.symm`):
  -- it states that filtering by a predicate `p` doesn't change the sum
  -- if all nonzero terms satisfy `p`.
  refine (Finset.sum_filter_of_ne ?_).symm
  -- Goal: ∀ a ∈ image, partMult p a * a ≠ 0 → a ≤ m
  intro a ha hne
  -- Step 2.1: `a` is a power of 3, hence positive (nonzero)
  rcases Finset.mem_image.mp ha with ⟨k, hk_mem, rfl⟩
  -- Step 2.2: `partMult p a * a ≠ 0` and `a = 3^k ≠ 0` imply `partMult p a ≠ 0`
  have ha_ne_zero : (3 : ℕ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have hmult_ne : partMult p (3 ^ k) ≠ 0 := by
    intro h
    apply hne
    rw [h]; ring
  -- Step 2.3: `partMult p (3^k) ≠ 0` means `3^k ∈ p.parts`
  have h_in_parts : (3 : ℕ) ^ k ∈ p.parts := by
    unfold partMult at hmult_ne
    exact (Multiset.count_ne_zero).mp hmult_ne
  -- Step 2.4: each element of `p.parts` is ≤ `p.parts.sum = m`
  have h_le_sum : (3 : ℕ) ^ k ≤ p.parts.sum :=
    Multiset.single_le_sum (fun x _ => Nat.zero_le x) _ h_in_parts
  rwa [p.parts_sum] at h_le_sum

/-- The weighted sum of `partMult` values at powers of 3 over `Ico j (m+1)`,
weighted by `3^k`, is bounded by `m`. This is because the parts of `p` equal
to `3^k` contribute `partMult p (3^k) * 3^k` to `p.parts.sum = m`, and these
contributions over different `k` are disjoint (by injectivity of `k ↦ 3^k`). -/
private lemma sum_partMult_mul_three_pow_le
    (m j : ℕ) (p : Nat.Partition m) :
    ∑ k ∈ Finset.Ico j (m + 1), partMult p (3 ^ k) * 3 ^ k ≤ m := by
  rw [sum_partMult_mul_three_pow_eq_image]
  rw [sum_image_eq_filter]
  calc ∑ a ∈ ((Finset.Ico j (m + 1)).image (fun k => 3 ^ k)).filter (fun a => a ≤ m),
          partMult p a * a
      ≤ ∑ a ∈ Finset.range (m + 1), partMult p a * a := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact image_three_pow_filter_subset_range m j
        · intros; exact Nat.zero_le _
    _ = m := sum_partMult_mul_eq_m m p

/-- The key counting bound: `3^j * (∑ k ∈ Ico j (m+1), partMult p (3^k)) ≤ m`. -/
private lemma three_pow_j_mul_sum_partMult_le
    (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m) (p : Nat.Partition m) :
    3 ^ j * (∑ k ∈ Finset.Ico j (m + 1), partMult p (3 ^ k)) ≤ m := by
  -- Pull `3^j` into the sum and compare term-by-term with `partMult p (3^k) * 3^k`.
  have step1 : 3 ^ j * (∑ k ∈ Finset.Ico j (m + 1), partMult p (3 ^ k))
      ≤ ∑ k ∈ Finset.Ico j (m + 1), partMult p (3 ^ k) * 3 ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_Ico] at hk
    -- `3^j ≤ 3^k` since `j ≤ k`.
    have hjk : 3 ^ j ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk.1
    -- `3^j * partMult ≤ partMult * 3^k`.
    rw [mul_comm (partMult p (3 ^ k)) (3 ^ k)]
    exact Nat.mul_le_mul_right _ hjk
  exact step1.trans (sum_partMult_mul_three_pow_le m j p)

/-- **Key counting estimate.** For `j ∈ Finset.Ioc 0 m` and any partition
`p : Nat.Partition m`, the total count of parts of size `3^k` for `k ∈ [j, m+1)`
is bounded by `m / 3^j`. -/
private lemma sum_partMult_Ico_le_div (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m)
    (p : Nat.Partition m) :
    (∑ k ∈ Finset.Ico j (m + 1), partMult p (3 ^ k)) ≤ m / 3 ^ j := by
  have hpos : 0 < 3 ^ j := Nat.pow_pos (by norm_num : (0:ℕ) < 3)
  rw [Nat.le_div_iff_mul_le hpos]
  rw [Nat.mul_comm]
  exact three_pow_j_mul_sum_partMult_le m j hj p

/-- **Helper 3b.** Exponent inequality for `cyclotomic (2·3^j)` for `j ≥ 1`.
For each `j ∈ Ioc 0 m`, the exponent `∑ k ∈ Ioc j m, m/3^k` in `gcdRHS m` is at most
the exponent `∑ k ∈ Ico j (m+1), (m/3^k - partMult p (3^k))` in `hTernary m p`. -/
private lemma exp_le_cyclotomic_general (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m)
    (p : Nat.Partition m) :
    (∑ k ∈ Finset.Ioc j m, m / 3 ^ k)
      ≤ ∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult p (3 ^ k)) := by
  -- Step 1: split RHS using sum_Ico_split_gen
  rw [sum_Ico_split_gen m j hj (fun k => m / 3 ^ k - partMult p (3 ^ k))]
  -- Goal: ∑ k ∈ Ioc j m, m/3^k ≤ (∑ k ∈ Ioc j m, (m/3^k - partMult(3^k))) + (m/3^j - partMult(3^j))
  -- Step 2: for each k ∈ Ioc j m, m/3^k = (m/3^k - partMult(3^k)) + partMult(3^k)
  have hterm : ∀ k, m / 3 ^ k = (m / 3 ^ k - partMult p (3 ^ k)) + partMult p (3 ^ k) := by
    intro k
    exact (Nat.sub_add_cancel (partMult_le_m_div_three_pow m p k)).symm
  -- Rewrite LHS using this
  have hLHS : (∑ k ∈ Finset.Ioc j m, m / 3 ^ k)
      = (∑ k ∈ Finset.Ioc j m, (m / 3 ^ k - partMult p (3 ^ k)))
        + (∑ k ∈ Finset.Ioc j m, partMult p (3 ^ k)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros k _
    exact hterm k
  rw [hLHS]
  -- Now need: A + B ≤ A + (m/3^j - partMult(3^j))
  -- where A = ∑ Ioc j m, (m/3^k - partMult(3^k)) and B = ∑ Ioc j m, partMult(3^k)
  -- So we need B ≤ m/3^j - partMult(3^j)
  have hjpos : 0 < j := (Finset.mem_Ioc.mp hj).1
  have hjm : j ≤ m := (Finset.mem_Ioc.mp hj).2
  -- Use the key counting estimate
  have hcount := sum_partMult_Ico_le_div m j hj p
  -- Split the sum: ∑ Ico j (m+1) = ∑ Ioc j m + partMult(3^j)
  have hsplit_pM : (∑ k ∈ Finset.Ico j (m + 1), partMult p (3 ^ k))
      = (∑ k ∈ Finset.Ioc j m, partMult p (3 ^ k)) + partMult p (3 ^ j) :=
    sum_Ico_split_gen m j hj (fun k => partMult p (3 ^ k))
  rw [hsplit_pM] at hcount
  -- hcount : (∑ Ioc j m, partMult(3^k)) + partMult(3^j) ≤ m / 3^j
  have hpartj : partMult p (3 ^ j) ≤ m / 3 ^ j := partMult_le_m_div_three_pow m p j
  -- Goal manipulation:
  -- want: A + B ≤ A + (m/3^j - partMult(3^j))
  -- equivalent to B ≤ m/3^j - partMult(3^j)
  -- equivalent to B + partMult(3^j) ≤ m/3^j (using Nat.sub)
  have hB_le : (∑ k ∈ Finset.Ioc j m, partMult p (3 ^ k))
      ≤ m / 3 ^ j - partMult p (3 ^ j) := by
    omega
  exact Nat.add_le_add_left hB_le _

/-- **Small helper.** Multiplicity computation for the witness partition. -/
private lemma partMult_witnessPart (m j k : ℕ) (hj : 0 < j) :
    partMult (witnessPart m j) (3 ^ k)
      = if k = 0 then m % 3 ^ j
        else if k = j then m / 3 ^ j else 0 := by
  unfold partMult witnessPart
  simp only [Multiset.count_add, Multiset.count_replicate]
  -- Key facts about powers of 3
  have h3j_gt_1 : 1 < (3 : ℕ) ^ j := by
    calc (1 : ℕ) < 3 := by norm_num
      _ = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have h3j_ne_1 : (3 : ℕ) ^ j ≠ 1 := by omega
  have hinj : Function.Injective (fun n : ℕ => (3 : ℕ) ^ n) :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 3)
  by_cases hk0 : k = 0
  · subst hk0
    -- 3^0 = 1; we want LHS = m % 3^j
    simp only [pow_zero]
    -- (if 3^j = 1 then ... else 0) + (if 1 = 1 then m % 3^j else 0) = m % 3^j
    have e1 : (3 : ℕ) ^ j = 1 ↔ False := iff_false_intro h3j_ne_1
    rw [if_neg h3j_ne_1]
    simp
  · -- k ≠ 0, so 3^k ≠ 1
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    have h3k_gt_1 : 1 < (3 : ℕ) ^ k := by
      calc (1 : ℕ) < 3 := by norm_num
        _ = 3 ^ 1 := (pow_one 3).symm
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk_pos
    have h1_ne_3k : (1 : ℕ) ≠ 3 ^ k := by omega
    rw [if_neg hk0, if_neg h1_ne_3k, add_zero]
    by_cases hkj : k = j
    · -- k = j, so 3^j = 3^k
      have h3j_eq_3k : (3 : ℕ) ^ j = 3 ^ k := by rw [hkj]
      rw [if_pos hkj, if_pos h3j_eq_3k]
    · -- k ≠ 0, k ≠ j, so 3^j ≠ 3^k
      have hjk : j ≠ k := fun h => hkj h.symm
      have h3j_ne_3k : (3 : ℕ) ^ j ≠ 3 ^ k := fun h => hjk (hinj h)
      rw [if_neg hkj, if_neg h3j_ne_3k]

/-- For every `k`, the polynomial `1 + X^(3^k)` is monic in `ℤ[X]`. -/
private lemma monic_one_add_X_pow_three_pow_h (k : ℕ) :
    (1 + Polynomial.X ^ (3 ^ k) : Polynomial ℤ).Monic := by
  rw [show (1 + Polynomial.X ^ (3 ^ k) : Polynomial ℤ) = Polynomial.X ^ (3 ^ k) + 1 from by ring]
  apply Polynomial.monic_X_pow_add
  simp [pow_pos, zero_lt_one]

/-- For every natural number `m` and partition `p` of `m`, the polynomial
`hTernary m p` is monic.

This follows because it is a product over `k ∈ Finset.range (m+1)` of
powers of `1 + X^(3^k)` (monic by `monic_one_add_X_pow_three_pow_h`), and
both `Polynomial.Monic.pow` and `Polynomial.Monic.prod_of_monic` preserve
monicity. -/
private lemma hTernary_monic_h (m : ℕ) (p : Nat.Partition m) :
    (hTernary m p).Monic := by
  unfold hTernary
  apply Polynomial.monic_prod_of_monic
  intro k _
  exact (monic_one_add_X_pow_three_pow_h k).pow _

/-- **gcdRHS m divides hTernary m (witnessPart m j)** for `j ∈ Ioc 0 m`. -/
private lemma gcdRHS_dvd_hTernary_witness (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m) :
    gcdRHS m ∣ hTernary m (witnessPart m j) := by
  -- Rewrite hTernary via the cyclotomic-swap lemma.
  rw [hTernary_eq_prod_cyclotomic_swap m (witnessPart m j)]
  -- Now both sides have the form Φ_2 ^ a * ∏ j' ∈ Ioc 0 m, Φ_{2·3^{j'}} ^ b.
  -- Show divisibility via mul_dvd_mul, pow_dvd_pow, and prod_dvd_prod_of_dvd.
  unfold gcdRHS
  refine mul_dvd_mul ?_ ?_
  · -- Φ_2 ^ g_0 ∣ Φ_2 ^ E_0
    exact pow_dvd_pow _ (exp_le_cyclotomic_two m (witnessPart m j))
  · -- Product factor divisibility
    refine Finset.prod_dvd_prod_of_dvd _ _ ?_
    intro j' hj'
    exact pow_dvd_pow _ (exp_le_cyclotomic_general m j' hj' (witnessPart m j))

/-- **Reused helper.** The witness quotient. -/
private noncomputable def witnessQuotient (m j : ℕ) : Polynomial ℤ :=
  hTernary m (witnessPart m j) /ₘ gcdRHS m

/-- **Helper: cyclotomic polynomials over ℤ are Prime.** -/
private lemma cyclotomic_prime {n : ℕ} (hn : 0 < n) : Prime (Polynomial.cyclotomic n ℤ) := by
  have hirr : Irreducible (Polynomial.cyclotomic n ℤ) :=
    Polynomial.cyclotomic.irreducible hn
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr

/-- **Target lemma.** For `j ∈ Ioc 0 m`, the exponent of `Φ_{2·3^j}` in
`hTernary m (witnessPart m j)` equals the exponent of `Φ_{2·3^j}` in
`gcdRHS m`. -/
private lemma exp_eq_witness_cyclotomic (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m) :
    (∑ k ∈ Finset.Ico j (m + 1), (m / 3 ^ k - partMult (witnessPart m j) (3 ^ k)))
      = ∑ k ∈ Finset.Ioc j m, m / 3 ^ k := by
  have hjpos : 0 < j := (Finset.mem_Ioc.mp hj).1
  -- Split the LHS sum at j
  rw [sum_Ico_split_gen m j hj
      (fun k => m / 3 ^ k - partMult (witnessPart m j) (3 ^ k))]
  -- The singleton term at k = j is zero
  have hj_term : m / 3 ^ j - partMult (witnessPart m j) (3 ^ j) = 0 := by
    rw [partMult_witnessPart m j j hjpos]
    simp [Nat.ne_of_gt hjpos]
  -- For k ∈ Ioc j m, partMult is 0
  have hsum_eq : ∑ k ∈ Finset.Ioc j m, (m / 3 ^ k - partMult (witnessPart m j) (3 ^ k))
                  = ∑ k ∈ Finset.Ioc j m, m / 3 ^ k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Ioc] at hk
    have hk_pos : 0 < k := lt_trans hjpos hk.1
    have hk_ne_j : k ≠ j := Nat.ne_of_gt hk.1
    have hk_ne_0 : k ≠ 0 := Nat.ne_of_gt hk_pos
    rw [partMult_witnessPart m j k hjpos]
    simp [hk_ne_0, hk_ne_j]
  rw [hsum_eq, hj_term, add_zero]

/-- **Explicit witness polynomial** (noncomputable DEFINITION, no cost).

`Q_witness m j` is the explicit residual cyclotomic product

  `Φ_2 ^ R₀ · ∏_{ℓ ∈ Ioc 0 m} Φ_{2·3^ℓ} ^ R_ℓ`,

where the residual exponents `R_ℓ` are the differences `E_ℓ − G_ℓ`
between the cyclotomic exponents of `Φ_{2·3^ℓ}` in
`hTernary m (witnessPart m j)` and in `gcdRHS m` (proof.md Step 5).

By construction (proof.md Step 5.4), the exponent of `Φ_{2·3^j}` in
`Q_witness m j` is `R_j = E_j − G_j = 0`. -/
private noncomputable def Q_witness (m j : ℕ) : Polynomial ℤ :=
  (Polynomial.cyclotomic 2 ℤ) ^
      (((m / 3 ^ j) * 3 ^ j +
          ∑ k ∈ (Finset.Ioc 0 m).erase j, m / 3 ^ k)
        - ∑ k ∈ Finset.Ioc 0 m, m / 3 ^ k)
    * ∏ ℓ ∈ Finset.Ioc 0 m,
        (Polynomial.cyclotomic (2 * 3 ^ ℓ) ℤ) ^
          ((∑ k ∈ (Finset.Ico ℓ (m + 1)).erase j, m / 3 ^ k)
              - ∑ k ∈ Finset.Ioc ℓ m, m / 3 ^ k)

private lemma count_mul_le_sum (s : Multiset ℕ) (a : ℕ) : s.count a * a ≤ s.sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons b t ih =>
    by_cases h : a = b
    · subst h
      simp [Multiset.count_cons_self, Multiset.sum_cons, add_mul]
      linarith
    · rw [Multiset.count_cons_of_ne h, Multiset.sum_cons]
      linarith

/-- `(Finset.Ico j (m+1)).erase j = Finset.Ioc j m`. -/
private lemma Ico_succ_erase_eq_Ioc (m j : ℕ) :
    (Finset.Ico j (m + 1)).erase j = Finset.Ioc j m := by
  ext k
  simp only [Finset.mem_erase, Finset.mem_Ico, Finset.mem_Ioc, Nat.lt_succ_iff]
  omega

/-- Residual exponent at `ℓ = j` is zero. -/
private lemma Q_witness_exp_at_j_eq_zero (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m) :
    (∑ k ∈ (Finset.Ico j (m + 1)).erase j, m / 3 ^ k)
        - ∑ k ∈ Finset.Ioc j m, m / 3 ^ k = 0 := by
  rw [Ico_succ_erase_eq_Ioc]
  exact Nat.sub_self _

/-- Closed form for the k=0 term. -/
private lemma witness_exp_two_lhs_k_zero (m j : ℕ) (hj : 0 < j) :
    m / 3 ^ 0 - partMult (witnessPart m j) (3 ^ 0) = (m / 3 ^ j) * 3 ^ j := by
  unfold partMult witnessPart
  simp only [pow_zero, Nat.div_one]
  rw [Multiset.count_add]
  have h3j_ne_one : (3 : ℕ) ^ j ≠ 1 := by
    have h3j_ge : (3 : ℕ) ^ j ≥ 3 := by
      calc (3 : ℕ) ^ j ≥ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj
        _ = 3 := pow_one 3
    omega
  rw [Multiset.count_replicate, Multiset.count_replicate]
  have hif1 : (if (3 : ℕ) ^ j = 1 then m / 3 ^ j else 0) = 0 := if_neg h3j_ne_one
  have hif2 : (if (1 : ℕ) = 1 then m % 3 ^ j else 0) = m % 3 ^ j := if_pos rfl
  rw [hif1, hif2]
  have hkey : 3 ^ j * (m / 3 ^ j) + m % 3 ^ j = m := Nat.div_add_mod m (3 ^ j)
  have hcomm : m / 3 ^ j * 3 ^ j = 3 ^ j * (m / 3 ^ j) := Nat.mul_comm _ _
  rw [hcomm]
  omega

private lemma witness_exp_two_lhs_k_other (m j k : ℕ) (hj : 0 < j) (hk : k ∈ (Finset.Ioc 0 m).erase j) :
    m / 3 ^ k - partMult (witnessPart m j) (3 ^ k) = m / 3 ^ k := by
  rw [Finset.mem_erase, Finset.mem_Ioc] at hk
  obtain ⟨hkj, hk0, hkm⟩ := hk
  have hk0' : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk0
  rw [partMult_witnessPart m j k hj]
  simp [hk0', hkj]

private lemma witness_exp_two_lhs (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m) :
    (∑ k ∈ Finset.range (m + 1),
        (m / 3 ^ k - partMult (witnessPart m j) (3 ^ k)))
      = (m / 3 ^ j) * 3 ^ j
        + ∑ k ∈ (Finset.Ioc 0 m).erase j, m / 3 ^ k := by
  rcases Finset.mem_Ioc.mp hj with ⟨hj_pos, hj_le⟩
  rw [range_succ_eq_insert_Ioc]
  rw [Finset.sum_insert (by simp : (0 : ℕ) ∉ Finset.Ioc 0 m)]
  rw [witness_exp_two_lhs_k_zero m j hj_pos]
  have hj_mem : j ∈ Finset.Ioc 0 m := hj
  have hsum_lhs : ∑ k ∈ Finset.Ioc 0 m,
      (m / 3 ^ k - partMult (witnessPart m j) (3 ^ k))
      = ∑ k ∈ (Finset.Ioc 0 m).erase j, m / 3 ^ k := by
    rw [← Finset.add_sum_erase _ _ hj_mem]
    have hkj : partMult (witnessPart m j) (3 ^ j) = m / 3 ^ j := by
      rw [partMult_witnessPart m j j hj_pos]
      simp [Nat.pos_iff_ne_zero.mp hj_pos]
    rw [hkj, Nat.sub_self, zero_add]
    apply Finset.sum_congr rfl
    intro k hk
    exact witness_exp_two_lhs_k_other m j k hj_pos hk
  rw [hsum_lhs]

private lemma div_le_div_mul_three_pow (m j : ℕ) (hj : 0 < j) :
    m / 3 ^ j ≤ (m / 3 ^ j) * 3 ^ j := by
  have h1 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
  calc m / 3 ^ j = (m / 3 ^ j) * 1 := by ring
    _ ≤ (m / 3 ^ j) * 3 ^ j := Nat.mul_le_mul_left _ h1

private lemma S_le_B (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m) :
    (∑ k ∈ Finset.Ioc 0 m, m / 3 ^ k) ≤
      (m / 3 ^ j) * 3 ^ j + ∑ k ∈ (Finset.Ioc 0 m).erase j, m / 3 ^ k := by
  have hj_pos : 0 < j := (Finset.mem_Ioc.mp hj).1
  have hsplit : (∑ k ∈ Finset.Ioc 0 m, m / 3 ^ k) =
      m / 3 ^ j + ∑ k ∈ (Finset.Ioc 0 m).erase j, m / 3 ^ k :=
    (Finset.add_sum_erase _ _ hj).symm
  rw [hsplit]
  exact Nat.add_le_add_right (div_le_div_mul_three_pow m j hj_pos) _

/-- New helper 1: Φ₂ exponent identity. -/
private lemma witness_exp_two_eq (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m) :
    (∑ k ∈ Finset.range (m + 1),
        (m / 3 ^ k - partMult (witnessPart m j) (3 ^ k)))
      = (∑ k ∈ Finset.Ioc 0 m, m / 3 ^ k)
        + (((m / 3 ^ j) * 3 ^ j +
              ∑ k ∈ (Finset.Ioc 0 m).erase j, m / 3 ^ k)
            - ∑ k ∈ Finset.Ioc 0 m, m / 3 ^ k) := by
  rw [witness_exp_two_lhs m j hj]
  exact (Nat.add_sub_cancel' (S_le_B m j hj)).symm

private lemma partMult_witnessPart_eq_zero_of_ne
    (m j ℓ k : ℕ) (hj : 0 < j) (hℓ : 0 < ℓ)
    (hk : k ∈ Finset.Ico ℓ (m + 1)) (hkj : k ≠ j) :
    partMult (witnessPart m j) (3 ^ k) = 0 := by
  rw [Finset.mem_Ico] at hk
  have hk_pos : 0 < k := lt_of_lt_of_le hℓ hk.1
  have hk_ne_zero : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk_pos
  rw [partMult_witnessPart m j k hj]
  simp [hk_ne_zero, hkj]

private lemma Ico_eq_insert_Ioc (ℓ m : ℕ) (hℓm : ℓ ≤ m) :
    Finset.Ico ℓ (m + 1) = insert ℓ (Finset.Ioc ℓ m) := by
  have h1 : Finset.Ico ℓ (m + 1) = Finset.Icc ℓ m := by
    ext k
    simp [Finset.mem_Ico, Finset.mem_Icc]
  rw [h1]
  exact (Finset.Ioc_insert_left hℓm).symm

private lemma Ico_erase_eq_insert_erase
    (m j ℓ : ℕ) (hℓm : ℓ ≤ m) (hlj : ℓ < j) :
    (Finset.Ico ℓ (m + 1)).erase j = insert ℓ ((Finset.Ioc ℓ m).erase j) := by
  rw [Ico_eq_insert_Ioc ℓ m hℓm]
  exact Finset.erase_insert_of_ne (_root_.ne_of_lt hlj)

private lemma witness_exp_general_eq_case_lt (m j ℓ : ℕ)
    (hj : j ∈ Finset.Ioc 0 m) (hℓ : ℓ ∈ Finset.Ioc 0 m) (hjl : j < ℓ) :
    (∑ k ∈ Finset.Ico ℓ (m + 1),
        (m / 3 ^ k - partMult (witnessPart m j) (3 ^ k)))
      = (∑ k ∈ Finset.Ioc ℓ m, m / 3 ^ k)
        + ((∑ k ∈ (Finset.Ico ℓ (m + 1)).erase j, m / 3 ^ k)
            - ∑ k ∈ Finset.Ioc ℓ m, m / 3 ^ k) := by
  have hj0 : 0 < j := (Finset.mem_Ioc.mp hj).1
  have hℓ0 : 0 < ℓ := (Finset.mem_Ioc.mp hℓ).1
  have hℓm : ℓ ≤ m := (Finset.mem_Ioc.mp hℓ).2
  have hmult : ∀ k ∈ Finset.Ico ℓ (m + 1),
      partMult (witnessPart m j) (3 ^ k) = 0 := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hkj : k ≠ j := by omega
    have hk0 : k ≠ 0 := by omega
    rw [partMult_witnessPart m j k hj0]
    simp [hk0, hkj]
  have hLHS : (∑ k ∈ Finset.Ico ℓ (m + 1),
        (m / 3 ^ k - partMult (witnessPart m j) (3 ^ k)))
      = ∑ k ∈ Finset.Ico ℓ (m + 1), m / 3 ^ k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hmult k hk, Nat.sub_zero]
  have hj_not_mem : j ∉ Finset.Ico ℓ (m + 1) := by
    simp [Finset.mem_Ico]; omega
  have hErase : (Finset.Ico ℓ (m + 1)).erase j = Finset.Ico ℓ (m + 1) :=
    Finset.erase_eq_self.mpr hj_not_mem
  have hSubset : Finset.Ioc ℓ m ⊆ Finset.Ico ℓ (m + 1) := by
    intro k hk; rw [Finset.mem_Ioc] at hk; rw [Finset.mem_Ico]; omega
  have hSumLe : (∑ k ∈ Finset.Ioc ℓ m, m / 3 ^ k)
      ≤ ∑ k ∈ Finset.Ico ℓ (m + 1), m / 3 ^ k :=
    Finset.sum_le_sum_of_subset hSubset
  rw [hLHS, hErase]
  omega

private lemma m_div_three_pow_le (m ℓ j : ℕ) (hlj : ℓ ≤ j) :
    m / 3 ^ j ≤ m / 3 ^ ℓ := by
  apply Nat.div_le_div_left
  · exact Nat.pow_le_pow_right (by norm_num) hlj
  · exact Nat.pos_of_ne_zero (by positivity)

private lemma sum_Ioc_eq_split (m j ℓ : ℕ) (hj : j ∈ Finset.Ioc ℓ m) :
    ∑ k ∈ Finset.Ioc ℓ m, m / 3 ^ k
      = m / 3 ^ j + ∑ k ∈ (Finset.Ioc ℓ m).erase j, m / 3 ^ k := by
  rw [← Finset.sum_erase_add _ _ hj]
  ring

private lemma sum_Ico_erase_eq_split (m j ℓ : ℕ)
    (hℓ_pos : 0 < ℓ) (hℓm : ℓ ≤ m) (hlj : ℓ < j) :
    ∑ k ∈ (Finset.Ico ℓ (m + 1)).erase j, m / 3 ^ k
      = m / 3 ^ ℓ + ∑ k ∈ (Finset.Ioc ℓ m).erase j, m / 3 ^ k := by
  rw [Ico_erase_eq_insert_erase m j ℓ hℓm hlj]
  have hℓ_notin : ℓ ∉ (Finset.Ioc ℓ m).erase j := by
    intro h
    have := Finset.mem_of_mem_erase h
    rw [Finset.mem_Ioc] at this
    omega
  rw [Finset.sum_insert hℓ_notin]

private lemma witness_exp_lhs_eq_sum_erase (m j ℓ : ℕ)
    (hj : j ∈ Finset.Ioc 0 m) (hℓ : ℓ ∈ Finset.Ioc 0 m) (hlj : ℓ < j) :
    (∑ k ∈ Finset.Ico ℓ (m + 1),
        (m / 3 ^ k - partMult (witnessPart m j) (3 ^ k)))
      = ∑ k ∈ (Finset.Ico ℓ (m + 1)).erase j, m / 3 ^ k := by
  obtain ⟨hj_pos, hj_le⟩ := Finset.mem_Ioc.mp hj
  obtain ⟨hℓ_pos, hℓ_le⟩ := Finset.mem_Ioc.mp hℓ
  have hj_mem : j ∈ Finset.Ico ℓ (m + 1) :=
    Finset.mem_Ico.mpr ⟨hlj.le, by omega⟩
  rw [← Finset.add_sum_erase _ _ hj_mem]
  have h_term_j :
      m / 3 ^ j - partMult (witnessPart m j) (3 ^ j) = 0 := by
    rw [partMult_witnessPart m j j hj_pos]
    have hj_ne_zero : j ≠ 0 := Nat.pos_iff_ne_zero.mp hj_pos
    simp [hj_ne_zero]
  rw [h_term_j, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_erase] at hk
  obtain ⟨hk_ne, hk_mem⟩ := hk
  have : partMult (witnessPart m j) (3 ^ k) = 0 :=
    partMult_witnessPart_eq_zero_of_ne m j ℓ k hj_pos hℓ_pos hk_mem hk_ne
  rw [this, Nat.sub_zero]

private lemma witness_exp_general_eq_case_gt (m j ℓ : ℕ)
    (hj : j ∈ Finset.Ioc 0 m) (hℓ : ℓ ∈ Finset.Ioc 0 m) (hlj : ℓ < j) :
    (∑ k ∈ Finset.Ico ℓ (m + 1),
        (m / 3 ^ k - partMult (witnessPart m j) (3 ^ k)))
      = (∑ k ∈ Finset.Ioc ℓ m, m / 3 ^ k)
        + ((∑ k ∈ (Finset.Ico ℓ (m + 1)).erase j, m / 3 ^ k)
            - ∑ k ∈ Finset.Ioc ℓ m, m / 3 ^ k) := by
  have hℓ_pos : 0 < ℓ := (Finset.mem_Ioc.mp hℓ).1
  have hℓm : ℓ ≤ m := (Finset.mem_Ioc.mp hℓ).2
  have hj_pos : 0 < j := (Finset.mem_Ioc.mp hj).1
  have hjm : j ≤ m := (Finset.mem_Ioc.mp hj).2
  have hj_in_Ioc : j ∈ Finset.Ioc ℓ m := Finset.mem_Ioc.mpr ⟨hlj, hjm⟩
  rw [witness_exp_lhs_eq_sum_erase m j ℓ hj hℓ hlj]
  rw [sum_Ioc_eq_split m j ℓ hj_in_Ioc, sum_Ico_erase_eq_split m j ℓ hℓ_pos hℓm hlj]
  have hmono : m / 3 ^ j ≤ m / 3 ^ ℓ :=
    m_div_three_pow_le m ℓ j (le_of_lt hlj)
  omega

/-- New helper 2: Φ_{2·3^ℓ} exponent identity. -/
private lemma witness_exp_general_eq (m j ℓ : ℕ) (hj : j ∈ Finset.Ioc 0 m)
    (hℓ : ℓ ∈ Finset.Ioc 0 m) :
    (∑ k ∈ Finset.Ico ℓ (m + 1),
        (m / 3 ^ k - partMult (witnessPart m j) (3 ^ k)))
      = (∑ k ∈ Finset.Ioc ℓ m, m / 3 ^ k)
        + ((∑ k ∈ (Finset.Ico ℓ (m + 1)).erase j, m / 3 ^ k)
            - ∑ k ∈ Finset.Ioc ℓ m, m / 3 ^ k) := by
  by_cases hlj : ℓ = j
  · subst hlj
    have hzero := Q_witness_exp_at_j_eq_zero m ℓ hj
    have hcyc := exp_eq_witness_cyclotomic m ℓ hj
    rw [hcyc, hzero, Nat.add_zero]
  · rcases lt_or_gt_of_ne hlj with hlt | hgt
    · exact witness_exp_general_eq_case_gt m j ℓ hj hℓ hlt
    · exact witness_exp_general_eq_case_lt m j ℓ hj hℓ hgt

/-- Main goal: the polynomial identity. -/
private lemma gcdRHS_mul_Q_witness_eq_hTernary (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m) :
    gcdRHS m * Q_witness m j = hTernary m (witnessPart m j) := by
  rw [hTernary_eq_prod_cyclotomic_swap]
  unfold gcdRHS Q_witness
  rw [mul_mul_mul_comm]
  rw [← pow_add]
  rw [← Finset.prod_mul_distrib]
  congr 1
  · congr 1
    exact (witness_exp_two_eq m j hj).symm
  · apply Finset.prod_congr rfl
    intro ℓ hℓ
    rw [← pow_add]
    congr 1
    exact (witness_exp_general_eq m j ℓ hj hℓ).symm

/-- For `j ≥ 1`, we have `2 * 3 ^ j ≠ 2`, since `3 ^ j ≥ 3 > 1`. -/
private lemma two_mul_three_pow_ne_two (j : ℕ) (hj : 1 ≤ j) : 2 * 3 ^ j ≠ 2 := by
  intro h
  have h1 : 3 ^ j = 1 := by omega
  have h2 : 3 ^ 1 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  omega

/-- The cyclotomic polynomials `cyclotomic (2 * 3 ^ j) ℤ` and `cyclotomic 2 ℤ`
are distinct whenever `j ≥ 1`. Uses `Polynomial.cyclotomic_injective` with `CharZero ℤ`. -/
private lemma cyclotomic_two_mul_three_pow_ne_cyclotomic_two (j : ℕ) (hj : 1 ≤ j) :
    Polynomial.cyclotomic (2 * 3 ^ j) ℤ ≠ Polynomial.cyclotomic 2 ℤ := by
  intro h
  have hne : 2 * 3 ^ j ≠ 2 := by
    have h3 : 3 ≤ 3 ^ j := by
      calc 3 = 3 ^ 1 := by ring
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    omega
  exact hne (Polynomial.cyclotomic_injective h)

/-- `Φ_{2·3^j}` does not divide `Φ_2` for `j ≥ 1`.

This holds because both polynomials are monic and `2 ≠ 2·3^j` for `j ≥ 1`,
hence by `cyclotomic_injective`, `Φ_2 ≠ Φ_{2·3^j}`. Two distinct monic
irreducible polynomials cannot divide one another. -/
private lemma cyclotomic_two_mul_three_pow_not_dvd_cyclotomic_two
    (j : ℕ) (hj : 1 ≤ j) :
    ¬ (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ∣ (Polynomial.cyclotomic 2 ℤ) := by
  -- Both are monic
  have hmonic1 : (Polynomial.cyclotomic (2 * 3 ^ j) ℤ).Monic := Polynomial.cyclotomic.monic _ _
  have hmonic2 : (Polynomial.cyclotomic 2 ℤ).Monic := Polynomial.cyclotomic.monic _ _
  -- Both are irreducible
  have h2pos : 0 < 2 := by norm_num
  have hjpos : 0 < 2 * 3 ^ j := by positivity
  have hirr1 : Irreducible (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) :=
    Polynomial.cyclotomic.irreducible hjpos
  have hirr2 : Irreducible (Polynomial.cyclotomic 2 ℤ) :=
    Polynomial.cyclotomic.irreducible h2pos
  -- The polynomials are distinct
  have hne : Polynomial.cyclotomic (2 * 3 ^ j) ℤ ≠ Polynomial.cyclotomic 2 ℤ :=
    cyclotomic_two_mul_three_pow_ne_cyclotomic_two j hj
  -- Suppose for contradiction that there is a divisibility
  intro hdvd
  -- Irreducible dividing nonzero irreducible: they are associated
  have hassoc : Associated (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) (Polynomial.cyclotomic 2 ℤ) := by
    rcases hdvd with ⟨c, hc⟩
    have hcunit : IsUnit c := by
      rcases hirr2.isUnit_or_isUnit hc with h | h
      · exact absurd h hirr1.not_isUnit
      · exact h
    exact ⟨hcunit.unit, by simp [hc]⟩
  -- Two monic associated polynomials are equal
  have heq : Polynomial.cyclotomic (2 * 3 ^ j) ℤ = Polynomial.cyclotomic 2 ℤ :=
    Polynomial.eq_of_monic_of_associated hmonic1 hmonic2 hassoc
  exact hne heq

/-- For `j ≠ ℓ` with `j, ℓ ≥ 1`, `Φ_{2·3^j}` does not divide `Φ_{2·3^ℓ}`.

This holds because `2·3^j ≠ 2·3^ℓ` (by injectivity of `ℓ ↦ 3^ℓ`),
so `Φ_{2·3^j} ≠ Φ_{2·3^ℓ}` as polynomials by `cyclotomic_injective`.
Both are monic irreducible, so neither can divide the other. -/
private lemma cyclotomic_two_mul_three_pow_not_dvd_cyclotomic_two_mul_three_pow
    (j ℓ : ℕ) (hj : 1 ≤ j) (hℓ : 1 ≤ ℓ) (hne : j ≠ ℓ) :
    ¬ (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ∣ (Polynomial.cyclotomic (2 * 3 ^ ℓ) ℤ) := by
  -- Step 1: indices are distinct positive numbers
  have h3j_pos : 0 < 3 ^ j := by positivity
  have h3l_pos : 0 < 3 ^ ℓ := by positivity
  have hj_pos : 0 < 2 * 3 ^ j := Nat.mul_pos (by decide) h3j_pos
  have hl_pos : 0 < 2 * 3 ^ ℓ := Nat.mul_pos (by decide) h3l_pos
  have hne_idx : 2 * 3 ^ j ≠ 2 * 3 ^ ℓ := by
    intro h
    have h3 : 3 ^ j = 3 ^ ℓ := by omega
    have : j = ℓ := Nat.pow_right_injective (by decide) h3
    exact hne this
  -- Step 2: distinct cyclotomics
  have hne_cyc : Polynomial.cyclotomic (2 * 3 ^ j) ℤ ≠ Polynomial.cyclotomic (2 * 3 ^ ℓ) ℤ := by
    intro h
    exact hne_idx (Polynomial.cyclotomic_injective h)
  -- Step 3, 4: irreducibility
  have hirr_l : Irreducible (Polynomial.cyclotomic (2 * 3 ^ ℓ) ℤ) :=
    Polynomial.cyclotomic.irreducible hl_pos
  have hirr_j : Irreducible (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) :=
    Polynomial.cyclotomic.irreducible hj_pos
  -- Step 5: monic
  have hmonic_j : (Polynomial.cyclotomic (2 * 3 ^ j) ℤ).Monic :=
    Polynomial.cyclotomic.monic _ _
  have hmonic_l : (Polynomial.cyclotomic (2 * 3 ^ ℓ) ℤ).Monic :=
    Polynomial.cyclotomic.monic _ _
  -- Step 6-7: from divisibility derive equality, contradicting Step 2
  intro hdvd
  -- By Irreducible.dvd_iff: IsUnit Φ_j ∨ Associated Φ_ℓ Φ_j
  rcases (Irreducible.dvd_iff hirr_l).mp hdvd with hunit | hassoc
  · -- Φ_{2·3^j} is not a unit (because it's irreducible)
    exact hirr_j.not_isUnit hunit
  · -- Monic associates are equal
    have hassoc' : Associated (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
                              (Polynomial.cyclotomic (2 * 3 ^ ℓ) ℤ) :=
      hassoc.symm
    have heq := Polynomial.eq_of_monic_of_associated hmonic_j hmonic_l hassoc'
    exact hne_cyc heq

/-- **Main lemma.** The cyclotomic polynomial `Φ_{2·3^j}` does not divide
`Q_witness m j`. -/
private lemma cyclotomic_not_dvd_Q_witness (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m) :
    ¬ (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ∣ Q_witness m j := by
  -- Set up parameters
  obtain ⟨hj_pos, hj_le⟩ := Finset.mem_Ioc.mp hj
  have hj1 : 1 ≤ j := hj_pos
  -- The big positive exponent
  set E0 : ℕ := ((m / 3 ^ j) * 3 ^ j +
            ∑ k ∈ (Finset.Ioc 0 m).erase j, m / 3 ^ k)
          - ∑ k ∈ Finset.Ioc 0 m, m / 3 ^ k with hE0
  set f : ℕ → ℕ := fun ℓ => (∑ k ∈ (Finset.Ico ℓ (m + 1)).erase j, m / 3 ^ k)
              - ∑ k ∈ Finset.Ioc ℓ m, m / 3 ^ k with hf
  -- Φ_{2·3^j} is prime
  have h23j_pos : 0 < 2 * 3 ^ j := by positivity
  have hprime : Prime (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) := cyclotomic_prime h23j_pos
  -- f j = 0
  have hfj : f j = 0 := Q_witness_exp_at_j_eq_zero m j hj
  -- Unfold Q_witness
  show ¬ (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ∣
    ((Polynomial.cyclotomic 2 ℤ) ^ E0
      * ∏ ℓ ∈ Finset.Ioc 0 m, (Polynomial.cyclotomic (2 * 3 ^ ℓ) ℤ) ^ f ℓ)
  -- Suppose for contradiction it divides
  intro hdvd
  rw [hprime.dvd_mul] at hdvd
  rcases hdvd with hdvd1 | hdvd2
  · -- Case 1: divides Φ_2 ^ E0, so divides Φ_2
    have hdvdΦ2 : (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ∣ (Polynomial.cyclotomic 2 ℤ) :=
      hprime.dvd_of_dvd_pow hdvd1
    exact cyclotomic_two_mul_three_pow_not_dvd_cyclotomic_two j hj1 hdvdΦ2
  · -- Case 2: divides product, so divides some factor
    rw [hprime.dvd_finset_prod_iff] at hdvd2
    obtain ⟨ℓ, hℓ_mem, hdvdℓ⟩ := hdvd2
    -- Split into ℓ = j and ℓ ≠ j
    by_cases hjℓ : ℓ = j
    · -- ℓ = j: exponent is 0
      subst hjℓ
      simp [hfj] at hdvdℓ
      -- Now divisor of 1, which contradicts being prime
      exact hprime.not_unit (isUnit_of_dvd_one hdvdℓ)
    · -- ℓ ≠ j: divides Φ_{2·3^ℓ}^f(ℓ), so divides Φ_{2·3^ℓ}, contradiction
      have hdvdΦℓ : (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ∣
          (Polynomial.cyclotomic (2 * 3 ^ ℓ) ℤ) :=
        hprime.dvd_of_dvd_pow hdvdℓ
      have hℓ_pos : 1 ≤ ℓ := (Finset.mem_Ioc.mp hℓ_mem).1
      exact cyclotomic_two_mul_three_pow_not_dvd_cyclotomic_two_mul_three_pow
        j ℓ hj1 hℓ_pos (Ne.symm hjℓ) hdvdΦℓ

/-- **MAIN THEOREM**: explicit factorisation of `hTernary m (witnessPart m j)`.

The witness is the explicit `Q := Q_witness m j`, a product of
cyclotomic polynomials whose `Φ_{2·3^j}`-exponent is `0` *by
construction*.  Both required properties follow immediately from the
two new helpers `gcdRHS_mul_Q_witness_eq_hTernary` and
`cyclotomic_not_dvd_Q_witness`. -/
private lemma hTernary_witness_eq_gcdRHS_mul (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m) :
    ∃ Q : Polynomial ℤ,
      hTernary m (witnessPart m j) = gcdRHS m * Q ∧
      ¬ (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ∣ Q := by
  refine ⟨Q_witness m j, ?_, cyclotomic_not_dvd_Q_witness m j hj⟩
  exact (gcdRHS_mul_Q_witness_eq_hTernary m j hj).symm

/-- **Main lemma.** The cyclotomic `Φ_{2·3^j}` does NOT divide
`hTernary m (witnessPart m j) /ₘ gcdRHS m`. -/
private lemma cyclotomic_not_dvd_witness_quotient (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m) :
    ¬ (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ∣
      (hTernary m (witnessPart m j) /ₘ gcdRHS m) := by
  -- Get the explicit factorisation
  obtain ⟨Q, hEq, hNotDvd⟩ := hTernary_witness_eq_gcdRHS_mul m j hj
  -- The quotient is exactly Q because gcdRHS is monic
  have hMonic : (gcdRHS m).Monic := gcdRHS_monic_h m
  have hQuotEq : hTernary m (witnessPart m j) /ₘ gcdRHS m = Q := by
    rw [hEq]
    exact Polynomial.mul_divByMonic_cancel_left Q hMonic
  rw [hQuotEq]
  exact hNotDvd

/-- **Helper: for `j ≥ 1`, `hTernary m (witnessPart m j)` factors as
`gcdRHS m * cof` with `cof` monic and `Φ_{2·3^j} ∤ cof`.** -/
private lemma hTernary_witness_factor (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m) :
    ∃ cof : Polynomial ℤ,
      cof.Monic ∧
      hTernary m (witnessPart m j) = gcdRHS m * cof ∧
      ¬ (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ∣ cof := by
  set cof := hTernary m (witnessPart m j) /ₘ gcdRHS m with hcof_def
  have hgcdRHS_monic_h : (gcdRHS m).Monic := gcdRHS_monic_h m
  have hwitness_monic : (hTernary m (witnessPart m j)).Monic := hTernary_monic_h m _
  have hdvd : gcdRHS m ∣ hTernary m (witnessPart m j) :=
    gcdRHS_dvd_hTernary_witness m j hj
  -- get the explicit factorisation `hTernary m (witnessPart m j) = gcdRHS m * cof`.
  have hmul : gcdRHS m * cof = hTernary m (witnessPart m j) := by
    have h1 : hTernary m (witnessPart m j) %ₘ gcdRHS m + gcdRHS m * cof
            = hTernary m (witnessPart m j) := Polynomial.modByMonic_add_div _ hgcdRHS_monic_h
    have h2 : hTernary m (witnessPart m j) %ₘ gcdRHS m = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hgcdRHS_monic_h).mpr hdvd
    rwa [h2, zero_add] at h1
  refine ⟨cof, ?_, hmul.symm, cyclotomic_not_dvd_witness_quotient m j hj⟩
  -- cof is monic: from `gcdRHS m * cof = hTernary m (witnessPart m j)`, both being monic.
  have hmonic_mul : (gcdRHS m * cof).Monic := hmul ▸ hwitness_monic
  exact Polynomial.Monic.of_mul_monic_left hgcdRHS_monic_h hmonic_mul

/-- **Helper: prime cancellation for the `Φ_{2·3^j}` factor (`j ≥ 1`).** -/
lemma cyclotomic_not_dvd_quotient_aux (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m)
    (Q : Polynomial ℤ) (hQ : gcdHTernary m = gcdRHS m * Q) :
    ¬ (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ∣ Q := by
  intro hdvd
  -- Obtain the witness cofactor.
  obtain ⟨cof, hcof_monic, hcof_eq, hcof_ndvd⟩ := hTernary_witness_factor m j hj
  -- gcdHTernary m divides hTernary m (witnessPart m j).
  have hgcd_dvd : gcdHTernary m ∣ hTernary m (witnessPart m j) :=
    gcdHTernary_dvd_hTernary_h m (witnessPart m j) (witnessPart_mem_ternaryPartitions m j)
  -- Substitute to get gcdRHS m * Q ∣ gcdRHS m * cof.
  rw [hQ, hcof_eq] at hgcd_dvd
  -- gcdRHS m is monic, hence nonzero.
  have hgcdRHS_monic_h : (gcdRHS m).Monic := gcdRHS_monic_h m
  have hgcdRHS_ne_zero : gcdRHS m ≠ 0 := hgcdRHS_monic_h.ne_zero
  -- Cancel gcdRHS m to get Q ∣ cof.
  have hQ_dvd_cof : Q ∣ cof := (mul_dvd_mul_iff_left hgcdRHS_ne_zero).mp hgcd_dvd
  -- Then cyclotomic (2*3^j) ∣ cof, contradicting hcof_ndvd.
  exact hcof_ndvd (hdvd.trans hQ_dvd_cof)


end cyclotomic_not_dvd_quotient_aux_section

/-- **Helper UFD lemma**: a monic polynomial in `ℤ[X]` that has no prime
factor among the cyclotomics
`{Φ_2} ∪ {Φ_{2·3^j} : j ∈ Ioc 0 m}` and divides `∏ Φ_{2·3^j}^(m/3^j)`
must be the unit `1`. -/
lemma monic_dvd_cyclotomic_prod_eq_one
    (m : ℕ) (Q : Polynomial ℤ) (hQmon : Q.Monic)
    (hQdvd : ∀ p ∈ (Finset.Ioc 0 m).image
                (fun j => Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
                ∪ {Polynomial.cyclotomic 2 ℤ}, ¬ p ∣ Q)
    (hQinto : Q ∣ ∏ j ∈ Finset.Ioc 0 m,
                (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ j)) :
    Q = 1 := by
  by_contra hQne1
  have hQ_not_unit : ¬ IsUnit Q := fun h => hQne1 (hQmon.eq_one_of_isUnit h)
  have hQ_ne_zero : Q ≠ 0 := hQmon.ne_zero
  obtain ⟨p, hp_irred, hp_dvd_Q⟩ :=
    WfDvdMonoid.exists_irreducible_factor hQ_not_unit hQ_ne_zero
  have hp_prime : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hp_irred
  have hp_dvd_prod : p ∣ ∏ j ∈ Finset.Ioc 0 m,
      (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ j) :=
    dvd_trans hp_dvd_Q hQinto
  obtain ⟨j, hj_mem, hp_dvd_factor⟩ :=
    (hp_prime.dvd_finset_prod_iff _).mp hp_dvd_prod
  have h_exp_pos : m / 3 ^ j ≠ 0 := by
    intro hzero
    rw [hzero, pow_zero] at hp_dvd_factor
    exact hp_irred.1 (isUnit_of_dvd_one hp_dvd_factor)
  have hp_dvd_cyclo : p ∣ Polynomial.cyclotomic (2 * 3 ^ j) ℤ :=
    (hp_prime.dvd_pow_iff_dvd h_exp_pos).mp hp_dvd_factor
  have h_pos : 0 < 2 * 3 ^ j := by positivity
  have h_cyclo_irred : Irreducible (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) :=
    Polynomial.cyclotomic.irreducible h_pos
  have h_assoc : Associated p (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) :=
    (hp_irred.dvd_irreducible_iff_associated h_cyclo_irred).mp hp_dvd_cyclo
  have h_cyclo_dvd_Q : Polynomial.cyclotomic (2 * 3 ^ j) ℤ ∣ Q :=
    h_assoc.symm.dvd.trans hp_dvd_Q
  refine hQdvd (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ?_ h_cyclo_dvd_Q
  refine Finset.mem_union.mpr (Or.inl ?_)
  exact Finset.mem_image.mpr ⟨j, hj_mem, rfl⟩

/-- **Monic cancellation**: if `f.Monic`, `f ≠ 0` and `f * a = f * b`, then `a = b`.
Applied to integer polynomials, but here we abstract it as a small helper. -/
lemma quotient_monic_of_monic_mul
    {f g h : Polynomial ℤ} (hg : g.Monic) (hh : h.Monic) (heq : h = g * f) :
    f.Monic := by
  have hgf : (g * f).Monic := heq ▸ hh
  exact hg.of_mul_monic_left hgf

/-- **Helper: upper-bound direction `gcdHTernary m ∣ gcdRHS m`.** -/
lemma gcdHTernary_dvd_gcdRHS (m : ℕ) : gcdHTernary m ∣ gcdRHS m := by
  -- Step 1: obtain `Q` with `gcdHTernary m = gcdRHS m * Q`.
  obtain ⟨Q, hQ⟩ := gcdRHS_dvd_gcdHTernary m
  -- Step 2: `Q` is monic (since `gcdRHS m` and `gcdHTernary m` are monic).
  have hQmon : Q.Monic :=
    quotient_monic_of_monic_mul (gcdRHS_monic m) (gcdHTernary_monic m) hQ
  -- Step 3: gather the no-cyclotomic-divides-Q facts.
  have hQ_no_div :
      ∀ p ∈ (Finset.Ioc 0 m).image
              (fun j => Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
              ∪ {Polynomial.cyclotomic 2 ℤ}, ¬ p ∣ Q := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp1 | hp2
    · -- p = Φ_{2·3^j} for some j ∈ Ioc 0 m
      rcases Finset.mem_image.mp hp1 with ⟨j, hj, rfl⟩
      exact cyclotomic_not_dvd_quotient_aux m j hj Q hQ
    · -- p = Φ_2
      have : p = Polynomial.cyclotomic 2 ℤ := Finset.mem_singleton.mp hp2
      subst this
      exact cyclotomic_two_not_dvd_quotient_aux m Q hQ
  -- Step 4: `Q ∣ cof m`.
  have hQ_dvd_cof : Q ∣ cof m := by
    -- gcdHTernary m ∣ hTernary m (allOnesPart m)
    have h1 : gcdHTernary m ∣ hTernary m (allOnesPart m) :=
      gcdHTernary_dvd_hTernary m (allOnesPart m)
        (allOnesPart_mem_ternaryPartitions m)
    -- hTernary m (allOnesPart m) = gcdRHS m * cof m
    have h2 : hTernary m (allOnesPart m) = gcdRHS m * cof m :=
      hTernary_allOnes_eq_gcdRHS_mul_cof m
    -- gcdRHS m * Q = gcdHTernary m ∣ gcdRHS m * cof m
    rw [h2] at h1
    rw [hQ] at h1
    -- Cancel `gcdRHS m`.
    exact (mul_dvd_mul_iff_left (gcdRHS_ne_zero m)).mp h1
  -- Step 5: apply the UFD lemma to conclude Q = 1.
  have hQ_eq_one : Q = 1 :=
    monic_dvd_cyclotomic_prod_eq_one m Q hQmon hQ_no_div hQ_dvd_cof
  -- Step 6: conclude `gcdHTernary m = gcdRHS m`, hence divides.
  rw [hQ_eq_one, mul_one] at hQ
  exact ⟨1, by rw [mul_one]; exact hQ.symm⟩

/-- The cyclotomic-power factorisation of `gcdHTernary m`. -/
lemma gcdHTernary_eq_prod_cyclotomic (m : ℕ) :
    gcdHTernary m
      = ((Polynomial.cyclotomic 2 ℤ) ^ (∑ k ∈ Finset.Ioc 0 m, m / 3 ^ k))
        * ∏ j ∈ Finset.Ioc 0 m,
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ)
              ^ (∑ k ∈ Finset.Ioc j m, m / 3 ^ k) := by
  show gcdHTernary m = gcdRHS m
  have hG : (gcdHTernary m).Monic := gcdHTernary_monic m
  have hR : (gcdRHS m).Monic := gcdRHS_monic m
  have h1 : gcdHTernary m ∣ gcdRHS m := gcdHTernary_dvd_gcdRHS m
  have h2 : gcdRHS m ∣ gcdHTernary m := gcdRHS_dvd_gcdHTernary m
  exact Polynomial.eq_of_monic_of_associated hG hR (associated_of_dvd_dvd h1 h2)


lemma sum_Ico_split (m j : ℕ) (hj : j ∈ Finset.Ioc 0 m) :
    (∑ k ∈ Finset.Ico j (m + 1), m / 3 ^ k)
      = (∑ k ∈ Finset.Ioc j m, m / 3 ^ k) + m / 3 ^ j := by
  have hjm : j ≤ m := (Finset.mem_Ioc.mp hj).2
  have hsplit : Finset.Ico j (m + 1) = insert j (Finset.Ioc j m) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Ioc, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  ring

/-- Main theorem: the cyclotomic factorisation. -/
lemma hTernary_allOnes_eq_gcd_mul_prod_cyclotomic (m : ℕ) :
    hTernary m (allOnesPart m)
      = gcdHTernary m
        * ∏ j ∈ Finset.Ioc 0 m,
            (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ j) := by
  rw [hTernary_allOnes_eq_prod_cyclotomic, gcdHTernary_eq_prod_cyclotomic]
  rw [mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← pow_add]
  congr 1
  rw [sum_Ico_split m j hj]


/-- **Cyclotomic factorisation of the all-ones quotient.** -/
lemma quotient_allOnes_eq_prod_cyclotomic (m : ℕ) :
    hTernary m (allOnesPart m) /ₘ gcdHTernary m
      = ∏ j ∈ Finset.Ioc 0 m,
          (Polynomial.cyclotomic (2 * 3 ^ j) ℤ) ^ (m / 3 ^ j) := by
  rw [hTernary_allOnes_eq_gcd_mul_prod_cyclotomic]
  exact mul_divByMonic_cancel_left _ (gcdHTernary_monic m)



/-- `3^j ≥ 3` for `j ≥ 1`. -/
lemma three_pow_ge_three (j : ℕ) (hj : 1 ≤ j) : (3 : ℕ) ≤ 3 ^ j := by
  calc (3 : ℕ) = 3 ^ 1 := by ring
    _ ≤ 3 ^ j := Nat.pow_le_pow_right (by decide) hj

/-- `3^j` is odd. -/
lemma three_pow_odd (j : ℕ) : Odd ((3 : ℕ) ^ j) :=
  Odd.pow (by decide)

/-- The case `m` is even in the case split.
    If `m` is even with `0 < m < 2 * n`, then `(-η) ^ m ≠ 1`. -/
lemma neg_pow_ne_one_of_even
    {η : ℂ} {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (h : IsPrimitiveRoot η n) {m : ℕ} (hmpos : 0 < m) (hm : m < 2 * n)
    (hmeven : Even m) : (-η) ^ m ≠ 1 := by
  obtain ⟨d, hd⟩ : ∃ d, m = 2 * d := ⟨m / 2, by rcases hmeven with ⟨k, hk⟩; omega⟩
  have hdpos : 0 < d := by omega
  have h_neg_eq : (-η : ℂ) ^ m = η ^ m := by
    rw [show ((-η : ℂ)) = (-1) * η from by ring, mul_pow, hd, pow_mul,
        show ((-1 : ℂ)) ^ 2 = 1 from by norm_num, one_pow, one_mul]
  rw [h_neg_eq]
  intro heq
  have hdvd : (n : ℕ) ∣ 2 * d := by
    apply h.dvd_of_pow_eq_one
    rw [← hd]; exact_mod_cast heq
  have hcop : Nat.Coprime n 2 := (Nat.coprime_iff_gcd_eq_one).mpr <| by
    rcases hn with ⟨k, hk⟩
    simp [Nat.gcd_comm n 2, Nat.gcd, hk]
  have hnd : (n : ℕ) ∣ d := hcop.dvd_of_dvd_mul_left hdvd
  have : (n : ℕ) ≤ d := Nat.le_of_dvd hdpos hnd
  omega

/-- The case `m` is odd in the case split.
    If `m` is odd with `0 < m < 2 * n`, then `(-η) ^ m ≠ 1`. -/
lemma neg_pow_ne_one_of_odd
    {η : ℂ} {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (h : IsPrimitiveRoot η n) {m : ℕ} (hmpos : 0 < m) (hm : m < 2 * n)
    (hmodd : Odd m) : (-η) ^ m ≠ 1 := by
  intro h₂
  -- (-η)^m = (-1)^m * η^m = -η^m for m odd, so η^m = -1
  have h_neg_pow : ((-1 : ℂ)) ^ m = -1 := Odd.neg_one_pow hmodd
  have h_neg_eq : (-η : ℂ) ^ m = - η ^ m := by
    rw [show ((-η : ℂ)) = (-1) * η from by ring, mul_pow, h_neg_pow, neg_one_mul]
  rw [h_neg_eq, neg_eq_iff_eq_neg] at h₂
  -- η^m = -1 so η^(2m) = 1, hence n ∣ 2m
  have h_sq : (η : ℂ) ^ (2 * m) = 1 := by
    rw [show 2 * m = m + m from by ring, pow_add, h₂]; ring
  have hdvd : (n : ℕ) ∣ 2 * m := by apply h.dvd_of_pow_eq_one; exact h_sq
  have hcop : Nat.Coprime n 2 := (Nat.coprime_iff_gcd_eq_one).mpr <| by
    rcases hn with ⟨k, hk⟩
    simp [Nat.gcd_comm n 2, Nat.gcd, hk]
  have hnm : (n : ℕ) ∣ m := hcop.dvd_of_dvd_mul_left hdvd
  -- m < 2n and n ∣ m, m > 0 ⇒ m = n
  have hnm_le : n ≤ m := Nat.le_of_dvd hmpos hnm
  have hmn : m = n := by
    obtain ⟨k, hk⟩ := hnm
    have hk1 : k = 1 := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · interval_cases k
        · omega
        · rfl
      · exfalso; nlinarith
    subst hk1; omega
  rw [hmn] at h₂
  exact absurd (h.pow_eq_one.symm.trans h₂) (by norm_num)

/-- Negation sends primitive `n`-th roots of unity to primitive `(2n)`-th
roots of unity, when `n` is odd and `1 < n`. -/
lemma isPrimitiveRoot_neg_of_odd_of_isPrimitiveRoot
    {η : ℂ} {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (h : IsPrimitiveRoot η n) :
    IsPrimitiveRoot (-η) (2 * n) := by
  refine IsPrimitiveRoot.mk_of_lt (-η) (by positivity) ?_ ?_
  · -- `(-η)^(2n) = 1`
    have hηn : η ^ n = 1 := h.pow_eq_one
    have h2n : (2 * n : ℕ) = n * 2 := by ring
    rw [h2n, pow_mul]
    have hen : (-η) ^ n = (-1) ^ n * η ^ n := by rw [neg_pow]
    rw [hen, hηn, mul_one]
    rcases hn with ⟨k, hk⟩
    rw [hk]
    have : ((-1 : ℂ)) ^ (2 * k + 1) = -1 := by
      rw [pow_add, pow_mul]; simp
    rw [this]; ring
  · -- `∀ m, 0 < m < 2n → (-η)^m ≠ 1`
    intro m hmpos hm
    rcases Nat.even_or_odd m with hmeven | hmodd
    · exact neg_pow_ne_one_of_even hn hn1 h hmpos hm hmeven
    · exact neg_pow_ne_one_of_odd hn hn1 h hmpos hm hmodd

/-- For odd `n > 1` and a primitive `(2n)`-th root of unity `ζ` in `ℂ`,
we have `ζ^n = -1`.

This is the key fact: from `ζ^(2n) = 1` we get `(ζ^n)^2 = 1`, so
`ζ^n = ±1`, and primitivity excludes `ζ^n = 1` because `0 < n < 2n`. -/
lemma zeta_pow_n_eq_neg_one
    {ζ : ℂ} {n : ℕ} (hn1 : 1 < n)
    (h : IsPrimitiveRoot ζ (2 * n)) :
    ζ ^ n = -1 := by
  have h_sq : (ζ ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm]; exact h.pow_eq_one
  have h_ne : ζ ^ n ≠ 1 :=
    h.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  have h_factor : (ζ ^ n - 1) * (ζ ^ n + 1) = 0 := by linear_combination h_sq
  rcases mul_eq_zero.mp h_factor with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) h_ne
  · exact eq_neg_of_add_eq_zero_left h1

lemma neg_zeta_pow_n_eq_one
    {ζ : ℂ} {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (h : IsPrimitiveRoot ζ (2 * n)) :
    (-ζ) ^ n = 1 := by
  have hnpos : 0 < n := by omega
  have h_zeta_pow_n_ne_one : ζ ^ n ≠ 1 :=
    h.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  have h_zeta_sq : (ζ ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm]; exact h.pow_eq_one
  have h_zeta_pow_n_eq_neg_one : ζ ^ n = -1 := by
    have h_factor : (ζ ^ n - 1) * (ζ ^ n + 1) = 0 := by linear_combination h_zeta_sq
    rcases mul_eq_zero.mp h_factor with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) h_zeta_pow_n_ne_one
    · exact eq_neg_of_add_eq_zero_left h1
  rw [show ((-ζ : ℂ)) = (-1) * ζ from by ring, mul_pow, Odd.neg_one_pow hn,
      h_zeta_pow_n_eq_neg_one]; ring

/-- Minimality: for `n` odd with `1 < n` and `ζ` a primitive `(2n)`-th root
of unity, any `0 < l < n` satisfies `(-ζ)^l ≠ 1`. -/
lemma neg_zeta_pow_ne_one_of_lt
    {ζ : ℂ} {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (h : IsPrimitiveRoot ζ (2 * n))
    (l : ℕ) (hl0 : 0 < l) (hln : l < n) :
    (-ζ) ^ l ≠ 1 := by
  intro heq
  -- From (-ζ)^l = 1, square both sides to get (-ζ)^(2l) = 1
  have h2l : ((-ζ) ^ l) ^ 2 = 1 := by rw [heq]; ring
  have h2l' : (-ζ) ^ (2 * l) = 1 := by
    rw [show 2 * l = l * 2 from by ring, pow_mul]
    exact h2l
  -- (-ζ)^(2l) = ζ^(2l) since (-1)^(2l) = 1
  have hzeta2l : ζ ^ (2 * l) = 1 := by
    have heq2 : (-ζ) ^ (2 * l) = ζ ^ (2 * l) := by
      rw [neg_pow]
      have : ((-1 : ℂ)) ^ (2 * l) = 1 := by
        rw [pow_mul]
        norm_num
      rw [this, one_mul]
    rw [← heq2]
    exact h2l'
  -- 0 < 2l < 2n
  have hpos : 2 * l ≠ 0 := by omega
  have hlt : 2 * l < 2 * n := by omega
  exact IsPrimitiveRoot.pow_ne_one_of_pos_of_lt h hpos hlt hzeta2l

/-- Negation sends primitive `(2n)`-th roots of unity to primitive `n`-th
roots of unity, when `n` is odd and `1 < n`.

Proof: `ζ^n = -1` (from `(ζ^n)^2 = 1` together with `ζ^n ≠ 1`), so
`(-ζ)^n = (-1)^n · ζ^n = (-1)·(-1) = 1` since `n` is odd. For minimality,
if `(-ζ)^d = 1` with `d ∣ n` and `d < n`, then since `n` is odd `d` is
odd, so `ζ^d = -1`, squaring gives `ζ^(2d) = 1`, but `2d < 2n` contradicts
`IsPrimitiveRoot ζ (2n)`. -/
lemma isPrimitiveRoot_neg_of_odd_of_isPrimitiveRoot_two_mul
    {ζ : ℂ} {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (h : IsPrimitiveRoot ζ (2 * n)) :
    IsPrimitiveRoot (-ζ) n := by
  refine IsPrimitiveRoot.mk_of_lt (-ζ) (by linarith)
    (neg_zeta_pow_n_eq_one hn hn1 h) ?_
  intro l hl0 hln
  exact neg_zeta_pow_ne_one_of_lt hn hn1 h l hl0 hln

/-- The set `primitiveRoots (2 * n) ℂ` is exactly the image of
`primitiveRoots n ℂ` under `z ↦ -z`, for odd `n` with `1 < n`.

Proof: mutual inclusion using the two directions above. Each set is a
`Finset` and we use `mem_primitiveRoots` to convert to `IsPrimitiveRoot`. -/
lemma primitiveRoots_two_mul_eq_image_neg_of_odd
    {n : ℕ} (hn : Odd n) (hn1 : 1 < n) :
    primitiveRoots (2 * n) ℂ =
      (primitiveRoots n ℂ).image (fun z : ℂ => -z) := by
  have hnpos : 0 < n := by omega
  have h2npos : 0 < 2 * n := by omega
  ext ζ
  simp only [mem_primitiveRoots h2npos, Finset.mem_image,
             mem_primitiveRoots hnpos]
  constructor
  · intro hζ
    refine ⟨-ζ, ?_, by ring⟩
    exact isPrimitiveRoot_neg_of_odd_of_isPrimitiveRoot_two_mul hn hn1 hζ
  · rintro ⟨η, hη, rfl⟩
    exact isPrimitiveRoot_neg_of_odd_of_isPrimitiveRoot hn hn1 hη

/-- The complex cyclotomic identity `(Φ_{2n})(−1) = Φ_n(1)` for odd `n > 1`.
This is the heart of the argument; the integer version follows by injectivity
of `Int.cast`. -/
lemma cyclotomic_two_mul_eval_neg_one_of_odd_complex
    (n : ℕ) (hn : Odd n) (hn1 : 1 < n) :
    (Polynomial.cyclotomic (2 * n) ℂ).eval (-1) =
      (Polynomial.cyclotomic n ℂ).eval 1 := by
  -- Need that 2*n ≠ 0
  have hne : n ≠ 0 := by omega
  -- Get a primitive n-th root of unity in ℂ.
  have hη : IsPrimitiveRoot
      (Complex.exp (2 * ↑Real.pi * Complex.I * (1 / ↑n))) n := by
    have := Complex.isPrimitiveRoot_exp_of_coprime 1 n hne (Nat.coprime_one_left n)
    simpa using this
  set η := Complex.exp (2 * ↑Real.pi * Complex.I * (1 / ↑n)) with hη_def
  have hneg_η : IsPrimitiveRoot (-η) (2 * n) :=
    isPrimitiveRoot_neg_of_odd_of_isPrimitiveRoot hn hn1 hη
  -- Establish 2 < n from oddness and n > 1.
  have h2lt : 2 < n := by
    rcases hn with ⟨k, hk⟩; omega
  -- Expand both cyclotomic polynomials as products.
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hneg_η,
      Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hη]
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  -- Reindex the LHS via the bijection z ↦ -z.
  rw [primitiveRoots_two_mul_eq_image_neg_of_odd hn hn1]
  rw [Finset.prod_image (fun a _ b _ h => by simpa using h)]
  -- LHS = ∏ η ∈ primitiveRoots n ℂ, (-1 - (-η))
  -- = ∏ η ∈ primitiveRoots n ℂ, -(1 - η)
  -- = (-1)^|primitiveRoots n ℂ| * ∏ η, (1 - η)
  have hcard_even : Even (primitiveRoots n ℂ).card := by
    rw [Complex.card_primitiveRoots]
    exact Nat.totient_even h2lt
  have key : ∀ z : ℂ, -1 - -z = -(1 - z) := by intro z; ring
  simp_rw [key]
  rw [Finset.prod_neg]
  rcases hcard_even with ⟨k, hk⟩
  rw [hk, ← two_mul, pow_mul]
  simp

/-- The integer cyclotomic identity `(Φ_{2n})(−1) = Φ_n(1)` for odd `n > 1`. -/
lemma cyclotomic_two_mul_eval_neg_one_of_odd_int
    (n : ℕ) (hn : Odd n) (hn1 : 1 < n) :
    (Polynomial.cyclotomic (2 * n) ℤ).eval (-1) =
      (Polynomial.cyclotomic n ℤ).eval 1 := by
  have inj : Function.Injective ((↑) : ℤ → ℂ) := Int.cast_injective
  apply inj
  -- Push casts through eval using `Polynomial.eval_intCast_map`.
  have hL :
      (((Polynomial.cyclotomic (2 * n) ℤ).eval (-1) : ℤ) : ℂ)
        = (Polynomial.cyclotomic (2 * n) ℂ).eval (-1) := by
    have h := Polynomial.eval_intCast_map (Int.castRingHom ℂ)
      (Polynomial.cyclotomic (2 * n) ℤ) (-1)
    rw [Polynomial.map_cyclotomic_int] at h
    push_cast at h
    exact h.symm
  have hR :
      (((Polynomial.cyclotomic n ℤ).eval 1 : ℤ) : ℂ)
        = (Polynomial.cyclotomic n ℂ).eval 1 := by
    have h := Polynomial.eval_intCast_map (Int.castRingHom ℂ)
      (Polynomial.cyclotomic n ℤ) 1
    rw [Polynomial.map_cyclotomic_int] at h
    push_cast at h
    exact h.symm
  rw [hL, hR]
  exact cyclotomic_two_mul_eval_neg_one_of_odd_complex n hn hn1

/-- For any odd `n ≥ 3` and any commutative ring `R`,
`(Φ_{2n})(−1) = Φ_n(1)`.

This is the standard identity `Φ_{2n}(X) = Φ_n(−X)` for odd `n > 1`,
specialised at `X = −1`.  No exact Mathlib lemma was found with this
shape after searching `Polynomial.cyclotomic_*` for `two_mul`, `neg_one`,
`neg_X`. -/
lemma cyclotomic_two_mul_eval_neg_one_of_odd
    {R : Type*} [CommRing R] (n : ℕ) (hn : Odd n) (hn1 : 1 < n) :
    (Polynomial.cyclotomic (2 * n) R).eval (-1) =
      (Polynomial.cyclotomic n R).eval 1 := by
  -- Reduce to the integer statement.
  have hZ : (Polynomial.cyclotomic (2 * n) ℤ).eval (-1) =
      (Polynomial.cyclotomic n ℤ).eval 1 :=
    cyclotomic_two_mul_eval_neg_one_of_odd_int n hn hn1
  -- Transfer along `Int.castRingHom R`.
  rw [← map_cyclotomic_int (2 * n) R, ← map_cyclotomic_int n R]
  rw [show ((-1 : R)) = (Int.castRingHom R) (-1 : ℤ) by simp]
  rw [show ((1 : R)) = (Int.castRingHom R) (1 : ℤ) by simp]
  rw [eval_map_apply, eval_map_apply]
  exact congrArg (Int.castRingHom R) hZ

/-- For `j ≥ 1`, `Φ_{3^j}(1) = 3` in `ℤ`.

This follows from Mathlib's
`Polynomial.eval_one_cyclotomic_prime_pow (k : ℕ) [hn : Fact (Nat.Prime p)] :
  Polynomial.eval 1 (Polynomial.cyclotomic (p ^ (k+1)) R) = ↑p`
applied with `p = 3` and `k = j - 1`, plus `Fact (Nat.Prime 3)`. -/
lemma cyclotomic_three_pow_eval_one (j : ℕ) (hj : 1 ≤ j) :
    (Polynomial.cyclotomic (3 ^ j) ℤ).eval 1 = 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  simpa using Polynomial.eval_one_cyclotomic_prime_pow (R := ℤ) (p := 3) k (by decide)

/-- **Step 5 (cyclotomic value at `-1`):** For `j ≥ 1`, the cyclotomic
polynomial `Φ_{2·3^j}` evaluated at `-1` equals `3`.

Proof: since `3^j` is odd, the identity `Φ_{2n}(X) = Φ_n(-X)` (for odd
`n`) gives `Φ_{2·3^j}(-1) = Φ_{3^j}(1)`.  And for a prime power
`p^j` with `j ≥ 1`, `Φ_{p^j}(1) = p`; here `p = 3`. -/
lemma cyclotomic_two_mul_three_pow_eval_neg_one (j : ℕ) (hj : 1 ≤ j) :
    (Polynomial.cyclotomic (2 * 3 ^ j) ℤ).eval (-1) = 3 := by
  have hodd : Odd ((3 : ℕ) ^ j) := three_pow_odd j
  have hge : 1 < (3 : ℕ) ^ j := by
    have := three_pow_ge_three j hj
    omega
  rw [cyclotomic_two_mul_eval_neg_one_of_odd (R := ℤ) (3 ^ j) hodd hge]
  exact cyclotomic_three_pow_eval_one j hj

/-- Legendre's formula in the form summed over `Finset.range m`. -/
lemma padicValNat_three_factorial_eq_sum_range (m : ℕ) :
    padicValNat 3 m.factorial = ∑ i ∈ Finset.range m, m / 3 ^ (i + 1) := by
  have padicValNat_three_factorial_eq_sum_Ico :
      padicValNat 3 m.factorial = ∑ i ∈ Finset.Ico 1 (m + 1), m / 3 ^ i := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hlog : Nat.log 3 m < m + 1 :=
      Nat.lt_succ_of_le (Nat.log_le_self 3 m)
    exact padicValNat_factorial hlog
  have sum_range_succ_eq_sum_Ico_three :
      ∑ i ∈ Finset.range m, m / 3 ^ (i + 1) = ∑ i ∈ Finset.Ico 1 (m + 1), m / 3 ^ i := by
    apply Finset.sum_bij' (fun (i : ℕ) _ => i + 1) (fun (j : ℕ) _ => j - 1)
    <;> simp_all [Finset.mem_Ico, Finset.mem_range]
    <;>
    (try
      {
        intro i hi
        omega
      })
  rw [padicValNat_three_factorial_eq_sum_Ico, ← sum_range_succ_eq_sum_Ico_three]

/-- Reindexing: `∑ i ∈ range m, f (i + 1) = ∑ j ∈ Ioc 0 m, f j`. -/
lemma sum_range_succ_eq_sum_Ioc (m : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range m, f (i + 1) = ∑ j ∈ Finset.Ioc 0 m, f j := by
  have h : ∑ i ∈ Finset.range m, f (i + 1) = ∑ j ∈ Finset.Ioc 0 m, f j := by
    apply Eq.symm
    apply Finset.sum_bij' (fun (i : ℕ) _ => i - 1) (fun (i : ℕ) _ => i + 1)
    <;> simp_all [Finset.mem_Ioc, Finset.mem_range, Nat.lt_succ_iff, Nat.le_of_lt_succ,
      Nat.succ_le_iff]
    <;> omega
  rw [h]

/-- **Step 6 (Legendre's formula):** `val3 m! = ∑_{j ∈ Ioc 0 m} m / 3^j`. -/
lemma val3_factorial_eq_sum_div (m : ℕ) :
    val3 m.factorial = ∑ j ∈ Finset.Ioc 0 m, m / 3 ^ j := by
  unfold val3
  rw [padicValNat_three_factorial_eq_sum_range m]
  exact sum_range_succ_eq_sum_Ioc m (fun j => m / 3 ^ j)

/-- Helper: split a power of a sum over a finset into a finset product
of powers (for the integer base `3`). -/
lemma three_pow_sum_eq_prod {α : Type*} (s : Finset α) (f : α → ℕ) :
    (3 : ℤ) ^ (∑ j ∈ s, f j) = ∏ j ∈ s, (3 : ℤ) ^ f j := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, pow_add, ih]

/-- **Main lemma (Steps 7.1–7.3).** -/
lemma quotient_allOnes_eval_neg_one_eq_pow_val3 (m : ℕ) :
    (hTernary m (allOnesPart m) /ₘ gcdHTernary m).eval (-1)
      = (3 : ℤ) ^ val3 m.factorial := by
  -- rewrite the quotient as a product of cyclotomic powers
  rw [quotient_allOnes_eq_prod_cyclotomic m]
  -- evaluate the product
  rw [Polynomial.eval_prod]
  -- evaluate each `(p ^ e).eval (-1)` as `(p.eval (-1)) ^ e`
  simp_rw [Polynomial.eval_pow]
  -- replace each cyclotomic value by 3 inside the product
  have hcong : (∏ j ∈ Finset.Ioc 0 m,
                  ((Polynomial.cyclotomic (2 * 3 ^ j) ℤ).eval (-1)) ^ (m / 3 ^ j))
             = (∏ j ∈ Finset.Ioc 0 m, (3 : ℤ) ^ (m / 3 ^ j)) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ioc.mp hj).1
    rw [cyclotomic_two_mul_three_pow_eval_neg_one j hj1]
  rw [hcong]
  -- ∏ j, 3^(m/3^j) = 3^(∑ j, m/3^j)
  rw [← three_pow_sum_eq_prod]
  -- match exponent with val3 m!
  rw [val3_factorial_eq_sum_div]

end Aux_quotient_allOnes_eval_neg_one_eq_pow_val3

/-- The quotient distributes over the sum. -/
lemma numT_eq_sum_divByMonic (m : ℕ) :
    numT m = ∑ p ∈ ternaryPartitions m, (hTernary m p /ₘ gcdHTernary m) :=
  Aux_numT_eq_sum_divByMonic.numT_eq_sum_divByMonic m

/-- The quotient evaluates to `0` at `x = -1` for non-all-ones ternary partitions. -/
lemma quotient_eval_neg_one_eq_zero_of_ne_allOnes
    (m : ℕ) (p : Nat.Partition m)
    (hp : p ∈ ternaryPartitions m) (hne : p ≠ allOnesPart m) :
    (hTernary m p /ₘ gcdHTernary m).eval (-1) = 0 := by
  obtain ⟨q, hq⟩ :=
    Aux_X_add_one_dvd_quotient_of_ne_allOnes.X_add_one_dvd_quotient_of_ne_allOnes m p hp hne
  simp [hq]

/-- The quotient for the all-ones partition at `-1` equals `3^(val3 m!)`. -/
lemma quotient_allOnes_eval_neg_one_eq_pow_val3 (m : ℕ) :
    (hTernary m (allOnesPart m) /ₘ gcdHTernary m).eval (-1)
      = (3 : ℤ) ^ val3 m.factorial :=
  Aux_quotient_allOnes_eval_neg_one_eq_pow_val3.quotient_allOnes_eval_neg_one_eq_pow_val3 m

/-! ### Combining: the uniform identity -/

/-- For every `m : ℕ`, `sSeq m = 3 ^ val3 m!`. -/
lemma sSeq_eq_pow_val3_factorial (m : ℕ) :
    sSeq m = (3 : ℤ) ^ val3 m.factorial := by
  unfold sSeq
  rw [numT_eq_sum_divByMonic, Polynomial.eval_finset_sum,
    Finset.sum_eq_single (allOnesPart m)
      (quotient_eval_neg_one_eq_zero_of_ne_allOnes m)
      (fun h => (h (allOnesPart_mem_ternary m)).elim)]
  exact quotient_allOnes_eval_neg_one_eq_pow_val3 m

/-! ### Arithmetic of `val3` on factorials -/

/-- `val3` is unchanged when we multiply by something coprime to `3`. -/
lemma val3_mul_of_not_dvd (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : ¬ (3 : ℕ) ∣ a) :
    padicValNat 3 (a * b) = padicValNat 3 b := by
  rw [padicValNat.mul ha hb, padicValNat.eq_zero_of_not_dvd hcop, zero_add]

/-- `val3((3n+1)!) = val3((3n)!)`. -/
lemma val3_factorial_succ_3n (n : ℕ) :
    val3 (3 * n + 1).factorial = val3 (3 * n).factorial := by
  unfold val3
  rw [Nat.factorial_succ]
  exact val3_mul_of_not_dvd _ _ (by omega) (3 * n).factorial_pos.ne' (by omega)

/-- `val3((3n+2)!) = val3((3n)!)`. -/
lemma val3_factorial_succ_succ_3n (n : ℕ) :
    val3 (3 * n + 2).factorial = val3 (3 * n).factorial := by
  unfold val3
  rw [show 3 * n + 2 = (3 * n + 1) + 1 from rfl, Nat.factorial_succ,
    val3_mul_of_not_dvd _ _ (by omega) (3 * n + 1).factorial_pos.ne' (by omega)]
  exact val3_factorial_succ_3n n

/-- **Main theorem (Conjecture 9).** For every `n ≥ 0`,
`s(3n) = s(3n+1) = s(3n+2) = 3^(val3 ((3n)!))`. -/
theorem main_conjecture (n : ℕ) :
    sSeq (3 * n) = (3 : ℤ) ^ val3 (3 * n).factorial ∧
    sSeq (3 * n + 1) = (3 : ℤ) ^ val3 (3 * n).factorial ∧
    sSeq (3 * n + 2) = (3 : ℤ) ^ val3 (3 * n).factorial :=
  ⟨sSeq_eq_pow_val3_factorial (3 * n),
    by rw [sSeq_eq_pow_val3_factorial (3 * n + 1), val3_factorial_succ_3n],
    by rw [sSeq_eq_pow_val3_factorial (3 * n + 2), val3_factorial_succ_succ_3n]⟩

end Conj9
