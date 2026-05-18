import Mathlib

/-
MATHLIB COVERAGE:
- Coprimality in Euclidean domain (ℚ[X]) ↔ no common nonconstant factor
- Embedding ℚ[X] → ℂ[X] preserves divisibility
- Polynomial vanishing/order at a point (Polynomial.rootMultiplicity, Polynomial.order_root)
- Cyclotomic polynomials are minimal polynomial of roots of unity
- gCommon divides hSummand divides denStar (factorization arguments)

Strategy: For each step in proof.md, introduce a high-level helper lemma. Most lemmas
are intricate and left unproved here. The main theorem combines them via reduction
to "no common complex root" + vanishing-order analysis.
-/

open Polynomial Finset

noncomputable section

/-- Multiplicity of `i` in a partition. -/
def Nat.Partition.mult {n : ℕ} (p : n.Partition) (i : ℕ) : ℕ :=
  Multiset.count i p.parts

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

/-! ## Helper lemmas -/

/-- For any partition `p` of `n`, summing `i * (multiplicity of i in p)` over `i ∈ [1,n]`
gives `n`. -/
lemma sum_mult_eq_n {n : ℕ} (p : n.Partition) :
    ∑ i ∈ Finset.Icc 1 n, i * p.mult i = n := by
  have hsub : p.parts.toFinset ⊆ Finset.Icc 1 n := by
    intro x hx
    rw [Multiset.mem_toFinset] at hx
    have hpos : 0 < x := p.parts_pos hx
    have hle : x ≤ n := by
      have := Multiset.le_sum_of_mem hx
      rw [p.parts_sum] at this
      exact this
    exact Finset.mem_Icc.mpr ⟨hpos, hle⟩
  have hsum : p.parts.sum =
      ∑ i ∈ Finset.Icc 1 n, Multiset.count i p.parts • i :=
    Finset.sum_multiset_count_of_subset p.parts (Finset.Icc 1 n) hsub
  have heq : ∑ i ∈ Finset.Icc 1 n, i * p.mult i
      = ∑ i ∈ Finset.Icc 1 n, Multiset.count i p.parts • i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [Nat.Partition.mult, Nat.mul_comm, smul_eq_mul]
  rw [heq, ← hsum, p.parts_sum]

lemma subset_Icc_of_partition_parts {n : ℕ} (p : n.Partition) :
    p.parts.toFinset ⊆ Finset.Icc 1 n := by
  intro x hx
  have h₂ : x ∈ p.parts := by grind
  have h₃ : 1 ≤ x := by grind
  have h₄ : x ≤ n := by grind
  grind

lemma mult_eq_zero_of_not_mem_toFinset {n : ℕ} (p : n.Partition) (i : ℕ)
    (h : i ∉ p.parts.toFinset) : p.mult i = 0 := by
  have h₁ : i ∉ p.parts := by
    intro h₂
    have h₃ : i ∈ p.parts.toFinset := Multiset.mem_toFinset.mpr h₂
    contradiction
  simp_all [Nat.Partition.mult]

/-- Step 1: Reformulate `subsumPoly p` as a product over `Icc 1 n` weighted by `p.mult i`. -/
lemma subsumPoly_eq_prod_Icc {n : ℕ} (p : n.Partition) :
    subsumPoly p =
      ∏ i ∈ Finset.Icc 1 n, ((1 : Polynomial ℚ) + X ^ i) ^ (p.mult i) := by
  unfold subsumPoly
  rw [Finset.prod_multiset_map_count]
  show ∏ m ∈ p.parts.toFinset, ((1 : Polynomial ℚ) + X ^ m) ^ p.mult m =
      ∏ i ∈ Finset.Icc 1 n, ((1 : Polynomial ℚ) + X ^ i) ^ p.mult i
  apply Finset.prod_subset (subset_Icc_of_partition_parts p) ?_
  intro i _hi hni
  have hmult : p.mult i = 0 := mult_eq_zero_of_not_mem_toFinset p i hni
  rw [hmult, pow_zero]

lemma i_mul_mult_le_n {n : ℕ} (p : n.Partition) {i : ℕ}
    (_hi1 : 1 ≤ i) (_hi2 : i ≤ n) : i * p.mult i ≤ n := by
  have h₁ : (p.parts.filter (· = i)) = Multiset.replicate (p.mult i) i := by
    grind only [Nat.Partition.mult.eq_def, Multiset.filter_eq']
  have h₂ : (p.parts.filter (· = i)).sum = p.mult i * i := by
    simp [Multiset.sum_replicate, smul_eq_mul, h₁]
  have h₃ : (p.parts.filter (· = i)) ≤ p.parts := by simp
  have h₄ : (p.parts.filter (· = i)).sum ≤ p.parts.sum := by
    grind only [Nat.Partition.parts_sum, Multiset.filter_add_not, = Multiset.sum_add]
  have h₅ : p.mult i * i ≤ n := by
    grind only [Nat.Partition.parts_sum]
  grind

/-- Step 2: For every partition `p ⊢ n` and every `i`, `p.mult i ≤ n / i`. -/
lemma mult_le_div {n : ℕ} (p : n.Partition) (i : ℕ) : p.mult i ≤ n / i := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [Nat.div_zero]
    have h0 : (0 : ℕ) ∉ p.parts.toFinset := by
      intro hmem
      have := subset_Icc_of_partition_parts p hmem
      simp [Finset.mem_Icc] at this
    exact (mult_eq_zero_of_not_mem_toFinset p 0 h0).le
  · by_cases hin : i ≤ n
    · rw [Nat.le_div_iff_mul_le hi]
      have := i_mul_mult_le_n p hi hin
      rw [Nat.mul_comm] at this
      exact this
    · push_neg at hin
      have hi_notin : i ∉ p.parts.toFinset := by
        intro hmem
        have := subset_Icc_of_partition_parts p hmem
        simp [Finset.mem_Icc] at this
        omega
      rw [mult_eq_zero_of_not_mem_toFinset p i hi_notin]
      exact Nat.zero_le _

/-- Step 1.1: For every partition `p ⊢ n`, the polynomial `denStar n` factors as
`hSummand p * subsumPoly p`. -/
lemma denStar_eq_hSummand_mul_subsumPoly {n : ℕ} (p : n.Partition) :
    denStar n = hSummand p * subsumPoly p := by
  rw [subsumPoly_eq_prod_Icc p]
  unfold denStar hSummand
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  rw [← pow_add]
  congr 1
  exact (Nat.sub_add_cancel (mult_le_div p i)).symm

/-- `gCommon n` divides `hSummand p` for every partition `p` of `n`, since
`gCommon n` is defined as the gcd of the family `hSummand` over all partitions.
Uses `Finset.gcd_dvd : ∀ {α β : Type*} [inst : CommGCDMonoid α] {s : Finset β} {f : β → α}
{b : β}, b ∈ s → f b ∣ s.gcd f` or rather the symmetric `Finset.dvd_gcd` direction;
here we use that for `Finset.univ`, `p ∈ univ`, so `s.gcd f ∣ f p`. -/
lemma gCommon_dvd_hSummand {n : ℕ} (p : n.Partition) :
    gCommon n ∣ hSummand p := by
  have h₁ : gCommon n = (Finset.univ : Finset n.Partition).gcd hSummand := rfl
  rw [h₁]
  apply Finset.gcd_dvd
  simp_all

/-- `gCommon n` divides `denStar n`. For `n ≥ 1`, there exists a partition `p` of `n`
(at least the all-ones partition), and `gCommon n ∣ hSummand p ∣ denStar n` by
`gCommon_dvd_hSummand` and `denStar_eq_hSummand_mul_subsumPoly`. -/
lemma gCommon_dvd_denStar (n : ℕ) (hn : 1 ≤ n) : gCommon n ∣ denStar n := by
  have _hn := hn
  let p0 : n.Partition := Nat.Partition.indiscrete n
  have h1 : gCommon n ∣ hSummand p0 := gCommon_dvd_hSummand p0
  have h2 : hSummand p0 ∣ denStar n := by
    refine ⟨subsumPoly p0, ?_⟩
    exact denStar_eq_hSummand_mul_subsumPoly p0
  exact h1.trans h2

/-- `gCommon n` divides `numStar n` because `numStar n = ∑_{p} hSummand p` and
`gCommon n` divides each summand. -/
lemma gCommon_dvd_numStar (n : ℕ) : gCommon n ∣ numStar n := by
  have h₁ : gCommon n = (Finset.univ : Finset n.Partition).gcd hSummand := rfl
  rw [h₁]
  have h₂ : ∀ (p : n.Partition), (Finset.univ : Finset n.Partition).gcd hSummand ∣ hSummand p := by
    intro p
    apply Finset.gcd_dvd
    simp [Finset.mem_univ]
  have h₃ : (Finset.univ : Finset n.Partition).gcd hSummand ∣ ∑ p : n.Partition, hSummand p := by
    apply Finset.dvd_sum
    intro p _
    exact h₂ p
  simpa [numStar] using h₃

/-- For `n ≥ 1`, `gCommon n` is nonzero: each `hSummand p` is a product of
nonzero polynomials `(1 + X^i)`, so it is nonzero, and at least one such `p` exists. -/
lemma one_add_X_pow_ne_zero (i : ℕ) (hi : 1 ≤ i) :
    ((1 : Polynomial ℚ) + X ^ i) ≠ 0 := by
  have h : Polynomial.coeff ((1 : Polynomial ℚ) + X ^ i) 0 = (1 : ℚ) := by
    grind only [X_dvd_iff, coeff_add, coeff_inj, coeff_one, = coeff_X_pow]
  have h₀ : Polynomial.coeff (0 : Polynomial ℚ) 0 = (0 : ℚ) := by simp
  have h₁ : ((1 : Polynomial ℚ) + X ^ i) ≠ 0 := by grind
  exact h₁

lemma hSummand_ne_zero {n : ℕ} (p : n.Partition) : hSummand p ≠ 0 := by
  unfold hSummand
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.mem_Icc] at hi
  exact pow_ne_zero _ (one_add_X_pow_ne_zero i hi.1)

lemma gCommon_ne_zero (n : ℕ) (hn : 1 ≤ n) : gCommon n ≠ 0 := by
  have _h := hn
  intro h
  rw [gCommon, Finset.gcd_eq_zero_iff] at h
  have hp : hSummand (Nat.Partition.indiscrete n) = 0 :=
    h (Nat.Partition.indiscrete n) (Finset.mem_univ _)
  exact hSummand_ne_zero (Nat.Partition.indiscrete n) hp

/-- For `n ≥ 1`, the equation `numStar n = numReduced n * gCommon n` holds.
This follows from `numReduced n = numStar n / gCommon n` (since `n ≠ 0`) and
divisibility `gCommon n ∣ numStar n`. -/
lemma numStar_eq_numReduced_mul_gCommon (n : ℕ) (hn : 1 ≤ n) :
    numStar n = numReduced n * gCommon n := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hg_ne : gCommon n ≠ 0 := gCommon_ne_zero n hn
  have hg_dvd : gCommon n ∣ numStar n := gCommon_dvd_numStar n
  have h_red : numReduced n = numStar n / gCommon n := by
    unfold numReduced
    exact if_neg hn0
  rw [h_red]
  rw [mul_comm]
  exact (EuclideanDomain.mul_div_cancel' hg_ne hg_dvd).symm

/-- For `n ≥ 1`, the equation `denStar n = denReduced n * gCommon n` holds.
Uses `denReduced n = denStar n / gCommon n` and `gCommon n ∣ denStar n`. -/
lemma denStar_eq_denReduced_mul_gCommon (n : ℕ) (hn : 1 ≤ n) :
    denStar n = denReduced n * gCommon n := by
  have hdvd : gCommon n ∣ denStar n := gCommon_dvd_denStar n hn
  have hmod : denStar n % gCommon n = 0 := EuclideanDomain.mod_eq_zero.mpr hdvd
  have hdam : gCommon n * (denStar n / gCommon n) + denStar n % gCommon n = denStar n :=
    EuclideanDomain.div_add_mod (denStar n) (gCommon n)
  rw [hmod, add_zero] at hdam
  show denStar n = denStar n / gCommon n * gCommon n
  rw [mul_comm]
  exact hdam.symm

/-- `denStar n` is nonzero, since it is a product of nonzero polynomials of the form
`(1 + X^i)^k` in `ℚ[X]`. -/
lemma denStar_ne_zero (n : ℕ) : denStar n ≠ 0 := by
  unfold denStar
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.mem_Icc] at hi
  exact pow_ne_zero _ (one_add_X_pow_ne_zero i hi.1)

/-! ### Reduction to common-root statement over ℂ

We use the embedding `Polynomial ℚ →+* Polynomial ℂ`. The key fact is that
two polynomials in `ℚ[X]` are coprime iff their images in `ℂ[X]` are coprime, iff
they have no common complex root.
-/

/-- If two polynomials in `ℚ[X]` have no common complex root (after embedding into
`ℂ[X]`), and the second is nonzero, then they are coprime in `ℚ[X]`.
This packages the standard fact that `ℚ[X]` is a UFD/PID where coprimality is
equivalent to having no common irreducible factor, and over the algebraically closed
field `ℂ`, an irreducible polynomial has a root.

Uses: `EuclideanDomain.isCoprime_iff_gcd_eq_one` and `Polynomial.IsAlgClosed.exists_root`
applied to a nonzero common factor over `ℂ`. -/
lemma degree_pos_of_ne_zero_of_not_isUnit
    (p : Polynomial ℚ) (hne : p ≠ 0) (hnu : ¬ IsUnit p) : 0 < p.degree := by
  have h1 : p.degree ≠ 0 := by
    intro h
    have h₂ : IsUnit p := by
      rw [Polynomial.isUnit_iff_degree_eq_zero]
      simp_all
    contradiction
  have h2 : p.natDegree ≠ 0 := by
    have h₂ : p.degree = ↑(p.natDegree) := by
      rw [Polynomial.degree_eq_natDegree hne]
    have h₃ : (p.degree : WithBot ℕ) ≠ 0 := by simpa using h1
    have h₄ : (↑(p.natDegree) : WithBot ℕ) ≠ 0 := by
      rw [h₂] at h₃
      exact h₃
    have h₅ : p.natDegree ≠ 0 := by
      intro h₅
      simp [h₅] at h₄
    exact h₅
  have h3 : 0 < p.natDegree := by
    by_contra h
    have h₄ : p.natDegree = 0 := by
      omega
    exact h2 h₄
  have h4 : 0 < p.degree := by
    have h₅ : p.degree = ↑(p.natDegree) := by
      rw [Polynomial.degree_eq_natDegree hne]
    rw [h₅]
    exact WithBot.coe_lt_coe.mpr h3
  exact h4

lemma degree_map_pos (p : Polynomial ℚ) (hp : 0 < p.degree) :
    0 < (p.map (algebraMap ℚ ℂ)).degree := by
  have h_degree_eq : (p.map (algebraMap ℚ ℂ)).degree = p.degree := by simp
  have h_main : 0 < (p.map (algebraMap ℚ ℂ)).degree := by grind
  grind

lemma eval_map_eq_zero_of_dvd_of_eval_eq_zero
    (g P : Polynomial ℚ) (h : g ∣ P) (α : ℂ)
    (hg : (g.map (algebraMap ℚ ℂ)).eval α = 0) :
    (P.map (algebraMap ℚ ℂ)).eval α = 0 := by
  have h₁ : ∃ (Q : Polynomial ℚ), P = g * Q := by assumption
  have h₂ : ∀ (Q : Polynomial ℚ), P = g * Q → (P.map (algebraMap ℚ ℂ)).eval α = 0 := by simp_all
  have h₃ : (P.map (algebraMap ℚ ℂ)).eval α = 0 := by grind
  grind

lemma isCoprime_of_no_common_complex_root (P Q : Polynomial ℚ)
    (hQ : Q ≠ 0)
    (h : ∀ α : ℂ, (P.map (algebraMap ℚ ℂ)).eval α = 0 →
      (Q.map (algebraMap ℚ ℂ)).eval α ≠ 0) :
    IsCoprime P Q := by
  apply EuclideanDomain.isCoprime_of_dvd
  · rintro ⟨_, hQ0⟩
    exact hQ hQ0
  · intro z hzNonUnit hzNeZero hzP hzQ
    have hzDegPos : 0 < z.degree :=
      degree_pos_of_ne_zero_of_not_isUnit z hzNeZero hzNonUnit
    have hZDegPos : 0 < (z.map (algebraMap ℚ ℂ)).degree := degree_map_pos z hzDegPos
    have hDegNeZero : (z.map (algebraMap ℚ ℂ)).degree ≠ 0 := ne_of_gt hZDegPos
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (z.map (algebraMap ℚ ℂ)) hDegNeZero
    have hZα : (z.map (algebraMap ℚ ℂ)).eval α = 0 := hα
    have hPα : (P.map (algebraMap ℚ ℂ)).eval α = 0 :=
      eval_map_eq_zero_of_dvd_of_eval_eq_zero z P hzP α hZα
    have hQα : (Q.map (algebraMap ℚ ℂ)).eval α = 0 :=
      eval_map_eq_zero_of_dvd_of_eval_eq_zero z Q hzQ α hZα
    exact h α hPα hQα

/-! ### Vanishing order analysis -/

/-- If `α : ℂ` is a root of `denStar n` mapped to `ℂ[X]`, then there exists `i` with
`1 ≤ i ≤ n` such that `α^i = -1`. This follows from the factorization
`denStar n = ∏ (1 + X^i)^(n/i)` and the fact that `ℂ[X]` is an integral domain. -/
lemma eval_map_denStar (n : ℕ) (α : ℂ) :
    ((denStar n).map (algebraMap ℚ ℂ)).eval α =
      ∏ i ∈ Finset.Icc 1 n, (1 + α ^ i) ^ (n / i) := by
  unfold denStar
  simp [Polynomial.map_prod, Polynomial.eval_prod, Polynomial.map_pow, Polynomial.eval_pow,
        Polynomial.map_add, Polynomial.eval_add, Polynomial.map_one, Polynomial.eval_one,
        Polynomial.map_X, Polynomial.eval_X]

lemma exists_pow_eq_neg_one_of_denStar_eval {n : ℕ} (α : ℂ)
    (h : ((denStar n).map (algebraMap ℚ ℂ)).eval α = 0) :
    ∃ i ∈ Finset.Icc 1 n, α ^ i = -1 := by
  rw [eval_map_denStar] at h
  rw [Finset.prod_eq_zero_iff] at h
  obtain ⟨i, hi, hzero⟩ := h
  refine ⟨i, hi, ?_⟩
  rw [pow_eq_zero_iff'] at hzero
  have h1 : (1 : ℂ) + α ^ i = 0 := hzero.1
  linear_combination h1

/-- If `α^i = -1` for some `i ≥ 1`, then `α` is a root of unity of even order `2s`
for some `s ≥ 1`. Specifically, `α^(2i) = 1` and `α ≠ 0` (since `α^i = -1 ≠ 0`),
so `α` is a torsion element with order dividing `2i`. Then this order is even
because `α^i = -1 ≠ 1`. -/
lemma pow_two_mul_eq_one_of_pow_eq_neg_one
    {α : ℂ} {i : ℕ} (h : α ^ i = -1) : α ^ (2 * i) = 1 := by
  have h₁ : α ^ (2 * i) = (α ^ i) ^ 2 := pow_mul' α 2 i
  have h₂ : (α ^ i) ^ 2 = 1 := by grind
  grind

lemma exists_minimal_pow_eq_one (α : ℂ) (N : ℕ) (hN : 1 ≤ N) (hαN : α ^ N = 1) :
    ∃ d : ℕ, 1 ≤ d ∧ α ^ d = 1 ∧
      (∀ m : ℕ, 1 ≤ m → m < d → α ^ m ≠ 1) := by
  classical
  have h : ∃ d : ℕ, 1 ≤ d ∧ α ^ d = 1 := by
    refine' ⟨N, _⟩
    exact ⟨by linarith, hαN⟩
  use Nat.find h
  have h₁ : 1 ≤ Nat.find h ∧ α ^ Nat.find h = 1 := Nat.find_spec h
  have h₂ : ∀ m : ℕ, 1 ≤ m → m < Nat.find h → α ^ m ≠ 1 := by
    intro m hm₁ hm₂
    by_contra h₃
    have h₄ : 1 ≤ m ∧ α ^ m = 1 := ⟨hm₁, h₃⟩
    have h₆ : Nat.find h ≤ m := Nat.find_min' h h₄
    linarith
  exact ⟨h₁.1, h₁.2, h₂⟩

lemma two_le_minimal_pow_of_pow_eq_neg_one
    {α : ℂ} {i d : ℕ} (_hi : 1 ≤ i) (hd : 1 ≤ d) (hα_neg : α ^ i = -1)
    (hαd : α ^ d = 1) : 2 ≤ d := by
  by_contra! h
  have h₁ : d = 1 := by
    linarith
  rw [h₁] at hαd
  have h₂ : α ^ 1 = 1 := hαd
  have h₃ : α = 1 := by
    simpa using h₂
  have h₄ : (1 : ℂ) ^ i = 1 := by simp
  rw [h₃] at hα_neg
  have h₅ : (1 : ℂ) ^ i = -1 := by simpa using hα_neg
  have h₆ : (1 : ℂ) ^ i = 1 := by simp
  rw [h₆] at h₅
  norm_num at h₅

lemma even_minimal_pow_of_pow_eq_neg_one
    {α : ℂ} {i d : ℕ} (_hi : 1 ≤ i) (hα_neg : α ^ i = -1)
    (hαd : α ^ d = 1) : Even d := by
  have h1 : (-1 : ℂ) ^ d = 1 := by
    calc
      (-1 : ℂ) ^ d = (α ^ i) ^ d := by rw [hα_neg]
      _ = α ^ (i * d) := by rw [← pow_mul]
      _ = (α ^ d) ^ i := by
        rw [← pow_mul]
        ring_nf
      _ = 1 ^ i := by rw [hαd]
      _ = 1 := by simp
  have h2 : Even d := by
    by_contra h
    have h3 : ¬Even d := h
    have h4 : Odd d := by
      simp [Nat.even_iff, Nat.odd_iff] at h3 ⊢
      omega
    have h5 : (-1 : ℂ) ^ d = -1 := by
      have h6 : d % 2 = 1 := by
        cases' h4 with k hk
        omega
      have h7 : (-1 : ℂ) ^ d = -1 := by
        rw [← Nat.mod_add_div d 2]
        simp [h6, pow_add, pow_mul, pow_one, pow_two]
      exact h7
    rw [h5] at h1
    norm_num at h1
  exact h2

lemma exists_even_order_of_pow_eq_neg_one (α : ℂ) (i : ℕ) (hi : 1 ≤ i)
    (h : α ^ i = -1) :
    ∃ s : ℕ, 1 ≤ s ∧ α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0 := by
  have h2i : α ^ (2 * i) = 1 := pow_two_mul_eq_one_of_pow_eq_neg_one h
  have h2i_pos : 1 ≤ 2 * i := by linarith
  obtain ⟨d, hd_pos, hαd, hd_min⟩ := exists_minimal_pow_eq_one α (2 * i) h2i_pos h2i
  have hd_even : Even d := even_minimal_pow_of_pow_eq_neg_one hi h hαd
  obtain ⟨s, hs_eq⟩ := hd_even
  have hds : d = 2 * s := by rw [hs_eq]; ring
  have hd_ge_two : 2 ≤ d := two_le_minimal_pow_of_pow_eq_neg_one hi hd_pos h hαd
  have hs_pos : 1 ≤ s := by
    by_contra h0
    push_neg at h0
    interval_cases s
    omega
  refine ⟨s, hs_pos, ?_, ?_⟩
  · rw [← hds]; exact hαd
  · intro k hk hαk
    by_contra hne
    have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hne
    have hkd : k < d := by rw [hds]; exact hk
    exact hd_min k hk_pos hkd hαk

/-- For `α` of exact order `2s` and `j : ℕ`, we have `α^j = -1 ↔ j ≡ s (mod 2s)`. -/
lemma pow_eq_neg_one_iff_aux {α : ℂ} {s : ℕ} (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (j : ℕ) :
    α ^ j = -1 ↔ j % (2 * s) = s := by
  obtain ⟨hpow, hmin⟩ := hord
  have hs_lt : s < 2 * s := by omega
  have h2s_pos : 0 < 2 * s := by omega
  have hαs : α ^ s = -1 := by
    have hsq : (α ^ s) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm]; exact hpow
    rcases sq_eq_one_iff.mp hsq with h1 | hn1
    · exfalso; have := hmin s hs_lt h1; omega
    · exact hn1
  have hchar1 : ∀ k : ℕ, α ^ k = 1 ↔ 2 * s ∣ k := by
    intro k
    constructor
    · intro hk
      have hkeq : k = 2 * s * (k / (2 * s)) + k % (2 * s) := (Nat.div_add_mod k (2 * s)).symm
      have hr_lt : k % (2 * s) < 2 * s := Nat.mod_lt k h2s_pos
      have hαr : α ^ (k % (2 * s)) = 1 := by
        have : α ^ k = α ^ (2 * s * (k / (2 * s))) * α ^ (k % (2 * s)) := by
          rw [← pow_add, ← hkeq]
        rw [this, pow_mul, hpow, one_pow, one_mul] at hk
        exact hk
      have hr0 : k % (2 * s) = 0 := hmin _ hr_lt hαr
      exact Nat.dvd_of_mod_eq_zero hr0
    · rintro ⟨q, rfl⟩
      rw [pow_mul, hpow, one_pow]
  constructor
  · intro hj
    set r := j % (2 * s) with hr_def
    set q := j / (2 * s) with hq_def
    have hjeq : j = 2 * s * q + r := by rw [hq_def, hr_def]; exact (Nat.div_add_mod j (2*s)).symm
    have hr_lt : r < 2 * s := Nat.mod_lt j h2s_pos
    have hαr : α ^ r = -1 := by
      have : α ^ j = α ^ (2 * s * q) * α ^ r := by rw [← pow_add, ← hjeq]
      rw [this, pow_mul, hpow, one_pow, one_mul] at hj
      exact hj
    have h2r : α ^ (2 * r) = 1 := by
      rw [mul_comm 2 r, pow_mul, hαr]; ring
    have hdvd : 2 * s ∣ 2 * r := (hchar1 (2 * r)).mp h2r
    obtain ⟨m, hm⟩ := hdvd
    have h2r_lt : 2 * r < 4 * s := by omega
    have hm_lt : m < 2 := by
      by_contra h
      push_neg at h
      have : 2 * s * 2 ≤ 2 * s * m := Nat.mul_le_mul_left _ h
      omega
    interval_cases m
    · have hr0 : r = 0 := by omega
      rw [hr0, pow_zero] at hαr
      exfalso
      have : (1 : ℂ) ≠ -1 := by norm_num
      exact this hαr
    · omega
  · intro hjs
    have hjeq : j = 2 * s * (j / (2 * s)) + s := by
      have := (Nat.div_add_mod j (2 * s)).symm
      rw [hjs] at this; exact this
    calc α ^ j = α ^ (2 * s * (j / (2 * s)) + s) := by rw [← hjeq]
      _ = α ^ (2 * s * (j / (2 * s))) * α ^ s := by rw [pow_add]
      _ = (α ^ (2 * s)) ^ (j / (2 * s)) * α ^ s := by rw [pow_mul]
      _ = 1 * (-1) := by rw [hpow, one_pow, hαs]
      _ = -1 := by ring

/-- The "bad set" `B = {j ∈ [1,n] : α^j = -1}`. For `α` of order `2s`, this equals
`{s, 3s, 5s, ...} ∩ [1,n]`. -/
def badSet (α : ℂ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun j => α ^ j = -1)

/-- For `α` of exact order `2s`, the count `c(λ) = ∑_{j ∈ B} m_λ(j)`. -/
def cCount (α : ℂ) (n : ℕ) (p : n.Partition) : ℕ :=
  ∑ j ∈ badSet α n, p.mult j

/-- The "C" quantity: `C = ∑_{j ∈ B} ⌊n/j⌋`. This is the vanishing order of
`denStar n` at `α`. -/
def cC (α : ℂ) (n : ℕ) : ℕ :=
  ∑ j ∈ badSet α n, n / j

/-! ### Order of vanishing computations

We use `Polynomial.rootMultiplicity` for the vanishing order. We package the
needed facts as helper lemmas.
-/

lemma rootMultiplicity_prod {R : Type*} [CommRing R] [IsDomain R] {ι : Type*}
    (S : Finset ι) (f : ι → Polynomial R) (x : R) (hf : ∀ i ∈ S, f i ≠ 0) :
    Polynomial.rootMultiplicity x (∏ i ∈ S, f i) = ∑ i ∈ S, Polynomial.rootMultiplicity x (f i) := by
  classical
  have h₂ : ∀ s : Finset ι, (∀ i ∈ s, f i ≠ 0) → Polynomial.rootMultiplicity x (∏ i ∈ s, f i) = ∑ i ∈ s, Polynomial.rootMultiplicity x (f i) := by
    intro s
    induction' s using Finset.induction_on with i s his ih
    · simp
    · intro h
      have h₃ : f i ≠ 0 := h i (Finset.mem_insert_self i s)
      have h₄ : ∀ i ∈ s, f i ≠ 0 := fun j hj => h j (Finset.mem_insert_of_mem hj)
      have h₅ : Polynomial.rootMultiplicity x (∏ j ∈ s, f j) = ∑ j ∈ s, Polynomial.rootMultiplicity x (f j) := ih h₄
      calc
        Polynomial.rootMultiplicity x (∏ j ∈ (insert i s), f j) = Polynomial.rootMultiplicity x ((f i) * (∏ j ∈ s, f j)) := by
          rw [Finset.prod_insert his]
        _ = Polynomial.rootMultiplicity x (f i) + Polynomial.rootMultiplicity x (∏ j ∈ s, f j) := by
          have h₆ : f i ≠ 0 := h₃
          have h₇ : (∏ j ∈ s, f j) ≠ 0 := by
            apply Finset.prod_ne_zero_iff.mpr
            intro j hj
            exact h₄ j hj
          rw [rootMultiplicity_mul]
          simp_all
        _ = (Polynomial.rootMultiplicity x (f i)) + ∑ j ∈ s, Polynomial.rootMultiplicity x (f j) := by rw [h₅]
        _ = ∑ j ∈ insert i s, Polynomial.rootMultiplicity x (f j) := by
          rw [Finset.sum_insert his]
  exact h₂ S (fun i hi => hf i hi)

lemma rootMultiplicity_pow {R : Type*} [CommRing R] [IsDomain R]
    (g : Polynomial R) (k : ℕ) (x : R) (hg : g ≠ 0) :
    Polynomial.rootMultiplicity x (g ^ k) = k * Polynomial.rootMultiplicity x g := by
  have h₁ : ∀ n : ℕ, Polynomial.rootMultiplicity x (g ^ n) = n * Polynomial.rootMultiplicity x g := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      calc
        Polynomial.rootMultiplicity x (g ^ (n + 1)) = Polynomial.rootMultiplicity x (g ^ n * g) :=
          by
            ring_nf
        _ = Polynomial.rootMultiplicity x (g ^ n) + Polynomial.rootMultiplicity x g :=
          by
            have h₂ : g ^ n ≠ 0 := by
              exact pow_ne_zero _ hg
            have h₃ : g ≠ 0 := hg
            have h₄ : Polynomial.rootMultiplicity x (g ^ n * g) = Polynomial.rootMultiplicity x (g ^ n) + Polynomial.rootMultiplicity x g := by
              apply Polynomial.rootMultiplicity_mul
              simp_all
            rw [h₄]
        _ = n * Polynomial.rootMultiplicity x g + Polynomial.rootMultiplicity x g := by
          rw [ih]
        _ = (n + 1) * Polynomial.rootMultiplicity x g := by
          ring
  rw [h₁ k]

lemma one_add_X_pow_ne_zero_complex (i : ℕ) :
    ((1 : Polynomial ℂ) + Polynomial.X ^ i) ≠ 0 := by
  intro h
  have h₁ := congr_arg (fun p => Polynomial.eval 0 p) h
  simp [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X] at h₁
  cases i <;> simp_all [pow_succ]

lemma rootMultiplicity_one_add_X_pow_complex_zero_case
    (α : ℂ) (i : ℕ) (h : α ^ i ≠ -1) :
    Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + Polynomial.X ^ i) = 0 := by
  have h₁ : ¬Polynomial.IsRoot ((1 : Polynomial ℂ) + Polynomial.X ^ i) α := by
    intro h₂
    have h₃ : Polynomial.eval α ((1 : Polynomial ℂ) + Polynomial.X ^ i) = 0 := by
      simpa [Polynomial.IsRoot] using h₂
    have h₄ : Polynomial.eval α ((1 : Polynomial ℂ) + Polynomial.X ^ i) = (1 : ℂ) + α ^ i := by
      simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
    rw [h₄] at h₃
    have h₅ : (1 : ℂ) + α ^ i = 0 := by simpa using h₃
    have h₆ : α ^ i = -1 := by
      have h₇ : (1 : ℂ) + α ^ i = 0 := h₅
      linear_combination h₇
    exact h h₆
  have h₂ : Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + Polynomial.X ^ i) = 0 := by
    rw [Polynomial.rootMultiplicity_eq_zero]
    simp_all [Polynomial.IsRoot]
  exact h₂

lemma rootMultiplicity_one_add_X_pow_complex_one_case_le
    (α : ℂ) (i : ℕ) (hi : 1 ≤ i) (h : α ^ i = -1) :
    Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + Polynomial.X ^ i) ≤ 1 := by
  set p : Polynomial ℂ := 1 + Polynomial.X ^ i with hp
  have hp_ne : p ≠ 0 := one_add_X_pow_ne_zero_complex i
  rw [Polynomial.rootMultiplicity_le_iff hp_ne α 1]
  intro hdvd
  have hderiv_dvd : (Polynomial.X - Polynomial.C α) ∣ Polynomial.derivative p := by
    have := Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hdvd
    simpa using this
  have hderiv : Polynomial.derivative p =
      Polynomial.C (i : ℂ) * Polynomial.X ^ (i - 1) := by
    simp [hp, Polynomial.derivative_add, Polynomial.derivative_one,
          Polynomial.derivative_X_pow]
  rw [hderiv] at hderiv_dvd
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def] at hderiv_dvd
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X] at hderiv_dvd
  have hi_pos : 0 < i := hi
  have hi_ne_nat : i ≠ 0 := Nat.pos_iff_ne_zero.mp hi_pos
  have hi_ne : (i : ℂ) ≠ 0 := by exact_mod_cast hi_ne_nat
  have hα_ne : α ≠ 0 := by
    intro hα0
    rw [hα0, zero_pow hi_ne_nat] at h
    exact absurd h (by norm_num)
  have hα_pow_ne : α ^ (i - 1) ≠ 0 := pow_ne_zero _ hα_ne
  rcases mul_eq_zero.mp hderiv_dvd with h1 | h2
  · exact hi_ne h1
  · exact hα_pow_ne h2

lemma rootMultiplicity_one_add_X_pow_complex_one_case
    (α : ℂ) (i : ℕ) (hi : 1 ≤ i) (h : α ^ i = -1) :
    Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + Polynomial.X ^ i) = 1 := by
  set p : Polynomial ℂ := (1 : Polynomial ℂ) + Polynomial.X ^ i with hp_def
  have hp_ne : p ≠ 0 := one_add_X_pow_ne_zero_complex i
  have hroot : p.IsRoot α := by
    show p.eval α = 0
    simp [hp_def, h]
  have h_ge : 1 ≤ Polynomial.rootMultiplicity α p :=
    (Polynomial.rootMultiplicity_pos hp_ne).mpr hroot
  have h_le : Polynomial.rootMultiplicity α p ≤ 1 :=
    rootMultiplicity_one_add_X_pow_complex_one_case_le α i hi h
  omega

lemma rootMultiplicity_one_add_X_pow_complex (α : ℂ) (i : ℕ) (hi : 1 ≤ i) :
    Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + Polynomial.X ^ i)
      = if α ^ i = -1 then 1 else 0 := by
  by_cases h : α ^ i = -1
  · rw [if_pos h]
    exact rootMultiplicity_one_add_X_pow_complex_one_case α i hi h
  · rw [if_neg h]
    exact rootMultiplicity_one_add_X_pow_complex_zero_case α i h

lemma map_one_add_X_pow (i : ℕ) :
    Polynomial.map (algebraMap ℚ ℂ) ((1 : Polynomial ℚ) + Polynomial.X ^ i)
      = ((1 : Polynomial ℂ) + Polynomial.X ^ i) := by
  have h₁ : Polynomial.map (algebraMap ℚ ℂ) ((1 : Polynomial ℚ) + Polynomial.X ^ i) =
      Polynomial.map (algebraMap ℚ ℂ) (1 : Polynomial ℚ) + Polynomial.map (algebraMap ℚ ℂ) (Polynomial.X ^ i) := by
    rw [Polynomial.map_add]
  have h₂ : Polynomial.map (algebraMap ℚ ℂ) (1 : Polynomial ℚ) = (1 : Polynomial ℂ) := by
    simp [Polynomial.map_one]
  have h₃ : Polynomial.map (algebraMap ℚ ℂ) (Polynomial.X ^ i : Polynomial ℚ) = (Polynomial.X : Polynomial ℂ) ^ i := by
    have h₄ : Polynomial.map (algebraMap ℚ ℂ) (Polynomial.X ^ i : Polynomial ℚ) =
        (Polynomial.map (algebraMap ℚ ℂ) (Polynomial.X : Polynomial ℚ)) ^ i := by
      rw [Polynomial.map_pow]
    rw [h₄]
    have h₅ : Polynomial.map (algebraMap ℚ ℂ) (Polynomial.X : Polynomial ℚ) = (Polynomial.X : Polynomial ℂ) := by
      simp [Polynomial.map_X]
    rw [h₅]
  rw [h₁, h₂, h₃]

lemma map_denStar (n : ℕ) :
    Polynomial.map (algebraMap ℚ ℂ) (denStar n)
      = ∏ i ∈ Finset.Icc 1 n, ((1 : Polynomial ℂ) + X ^ i) ^ (n / i) := by
  classical
  unfold denStar
  rw [Polynomial.map_prod]
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [Polynomial.map_pow, map_one_add_X_pow]

/-- The vanishing order of `denStar n` at `α` (after mapping to `ℂ[X]`) equals `cC α n`. -/
lemma rootMultiplicity_denStar (n : ℕ) (α : ℂ) :
    Polynomial.rootMultiplicity α ((denStar n).map (algebraMap ℚ ℂ)) = cC α n := by
  classical
  rw [map_denStar]
  rw [rootMultiplicity_prod (R := ℂ) _ _ _
        (fun i _ => pow_ne_zero _ (one_add_X_pow_ne_zero_complex i))]
  have hpow :
      ∀ i ∈ Finset.Icc 1 n,
        Polynomial.rootMultiplicity α (((1 : Polynomial ℂ) + X ^ i) ^ (n / i))
          = (n / i) * Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + X ^ i) := by
    intro i _
    exact rootMultiplicity_pow _ _ _ (one_add_X_pow_ne_zero_complex i)
  rw [Finset.sum_congr rfl hpow]
  have hbase :
      ∀ i ∈ Finset.Icc 1 n,
        (n / i) * Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + X ^ i)
          = (if α ^ i = -1 then n / i else 0) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    rw [rootMultiplicity_one_add_X_pow_complex α i hi1]
    by_cases h : α ^ i = -1
    · simp [h]
    · simp [h]
  rw [Finset.sum_congr rfl hbase]
  unfold cC badSet
  rw [Finset.sum_filter]

/-- The vanishing order of `subsumPoly p` at `α` equals `cCount α n p`. -/
lemma rootMultiplicity_subsumPoly {n : ℕ} (p : n.Partition) (α : ℂ) :
    Polynomial.rootMultiplicity α ((subsumPoly p).map (algebraMap ℚ ℂ)) = cCount α n p := by
  classical
  rw [subsumPoly_eq_prod_Icc p]
  have hmap :
      Polynomial.map (algebraMap ℚ ℂ)
          (∏ i ∈ Finset.Icc 1 n, ((1 : Polynomial ℚ) + X ^ i) ^ (p.mult i)) =
        ∏ i ∈ Finset.Icc 1 n, ((1 : Polynomial ℂ) + X ^ i) ^ (p.mult i) := by
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl ?_
    intro i _
    rw [Polynomial.map_pow, map_one_add_X_pow i]
  rw [hmap]
  have hne :
      ∀ i ∈ Finset.Icc 1 n,
        ((1 : Polynomial ℂ) + X ^ i) ^ (p.mult i) ≠ 0 := by
    intro i _
    exact pow_ne_zero _ (one_add_X_pow_ne_zero_complex i)
  rw [rootMultiplicity_prod _ _ α hne]
  have hsum :
      ∑ i ∈ Finset.Icc 1 n,
          Polynomial.rootMultiplicity α (((1 : Polynomial ℂ) + X ^ i) ^ (p.mult i))
        = ∑ i ∈ Finset.Icc 1 n,
            p.mult i * (if α ^ i = -1 then 1 else 0) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    rw [rootMultiplicity_pow _ _ α (one_add_X_pow_ne_zero_complex i),
        rootMultiplicity_one_add_X_pow_complex α i hi1]
  rw [hsum]
  unfold cCount badSet
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases h : α ^ i = -1
  · simp [h]
  · simp [h]

/-- For each partition `p ⊢ n`, the vanishing order of `hSummand p` at `α` equals
`cC α n - cCount α n p`. (We need that `cCount α n p ≤ cC α n`, which holds termwise
because `p.mult i ≤ n / i` for partitions of `n`.) -/
lemma finset_sum_sub_distrib_of_le {ι : Type*} (S : Finset ι) (a b : ι → ℕ)
    (h : ∀ i ∈ S, b i ≤ a i) :
    (∑ i ∈ S, a i) - (∑ i ∈ S, b i) = ∑ i ∈ S, (a i - b i) := by
  have h_main : (∑ i ∈ S, a i) - (∑ i ∈ S, b i) = ∑ i ∈ S, (a i - b i) :=
    Eq.symm (sum_tsub_distrib S h)
  grind

lemma rootMultiplicity_hSummand {n : ℕ} (p : n.Partition) (α : ℂ) :
    Polynomial.rootMultiplicity α ((hSummand p).map (algebraMap ℚ ℂ)) =
      cC α n - cCount α n p := by
  have hmap :
      (hSummand p).map (algebraMap ℚ ℂ)
        = ∏ i ∈ Finset.Icc 1 n,
            ((1 : Polynomial ℂ) + Polynomial.X ^ i) ^ (n / i - p.mult i) := by
    unfold hSummand
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl ?_
    intro i _
    rw [Polynomial.map_pow, map_one_add_X_pow]
  rw [hmap]
  have hne : ∀ i ∈ Finset.Icc 1 n,
      (((1 : Polynomial ℂ) + Polynomial.X ^ i) ^ (n / i - p.mult i)) ≠ 0 := by
    intro i _
    exact pow_ne_zero _ (one_add_X_pow_ne_zero_complex i)
  rw [rootMultiplicity_prod (Finset.Icc 1 n)
        (fun i => ((1 : Polynomial ℂ) + Polynomial.X ^ i) ^ (n / i - p.mult i)) α hne]
  have hstep :
      ∀ i ∈ Finset.Icc 1 n,
        Polynomial.rootMultiplicity α
            (((1 : Polynomial ℂ) + Polynomial.X ^ i) ^ (n / i - p.mult i))
          = (n / i - p.mult i)
              * (if α ^ i = -1 then 1 else 0) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    rw [rootMultiplicity_pow _ _ _ (one_add_X_pow_ne_zero_complex i),
        rootMultiplicity_one_add_X_pow_complex α i hi1]
  rw [Finset.sum_congr rfl hstep]
  have hrestrict :
      (∑ i ∈ Finset.Icc 1 n,
          (n / i - p.mult i) * (if α ^ i = -1 then 1 else 0))
        = ∑ i ∈ badSet α n, (n / i - p.mult i) := by
    rw [badSet]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro i _
    split_ifs <;> simp
  rw [hrestrict]
  have hbound : ∀ i ∈ badSet α n, p.mult i ≤ n / i := by
    intro i _
    exact mult_le_div p i
  rw [show (∑ i ∈ badSet α n, (n / i - p.mult i))
        = (∑ i ∈ badSet α n, n / i) - (∑ i ∈ badSet α n, p.mult i) from
      (finset_sum_sub_distrib_of_le (badSet α n) (fun i => n / i) (fun i => p.mult i) hbound).symm]
  rfl

/-- For α of exact order `2s` with `α^i = -1` for some `1 ≤ i ≤ n`, and for any
partition `p ⊢ n`, every `j ∈ badSet α n` is ≥ `s`. Therefore
`cCount α n p * s ≤ n`, i.e. `cCount α n p ≤ n / s = M`. -/
lemma s_le_of_pow_eq_neg_one {α : ℂ} {s : ℕ} (_hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    {j : ℕ} (hj : 1 ≤ j) (hpow : α ^ j = -1) : s ≤ j := by
  by_contra h
  have h₂ : 2 * j < 2 * s := by
    omega
  have h₃ : α ^ (2 * j) = 1 := by
    calc
      α ^ (2 * j) = (α ^ j) ^ 2 := by
        calc
          α ^ (2 * j) = α ^ (j + j) := by ring_nf
          _ = (α ^ j) * (α ^ j) := by rw [pow_add]
          _ = (α ^ j) ^ 2 := by ring_nf
      _ = (-1 : ℂ) ^ 2 := by rw [hpow]
      _ = 1 := by norm_num
  have h₄ : 2 * j = 0 := by
    apply hord.2
    · exact h₂
    · exact h₃
  omega

lemma cCount_le_M {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (p : n.Partition) :
    cCount α n p ≤ n / s := by
  rw [Nat.le_div_iff_mul_le hs]
  have h_badSet_subset : badSet α n ⊆ Finset.Icc 1 n := by
    intro j hj
    simp [badSet, Finset.mem_filter] at hj
    exact Finset.mem_Icc.mpr ⟨hj.1.1, hj.1.2⟩
  have h_s_le : ∀ j ∈ badSet α n, s ≤ j := by
    intro j hj
    simp [badSet, Finset.mem_filter, Finset.mem_Icc] at hj
    exact s_le_of_pow_eq_neg_one hs hord hj.1.1 hj.2
  calc cCount α n p * s
      = (∑ j ∈ badSet α n, p.mult j) * s := by rfl
    _ = ∑ j ∈ badSet α n, p.mult j * s := by rw [Finset.sum_mul]
    _ = ∑ j ∈ badSet α n, s * p.mult j := by
          apply Finset.sum_congr rfl; intros; ring
    _ ≤ ∑ j ∈ badSet α n, j * p.mult j := by
          apply Finset.sum_le_sum
          intro j hj
          exact Nat.mul_le_mul_right _ (h_s_le j hj)
    _ ≤ ∑ i ∈ Finset.Icc 1 n, i * p.mult i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg h_badSet_subset
          intros; exact Nat.zero_le _
    _ = n := sum_mult_eq_n p

/-- If `α^(2s) = 1` and the only `k < 2s` with `α^k = 1` is `k = 0`, then `α^s = -1`. -/
lemma pow_s_eq_neg_one {α : ℂ} {s : ℕ} (hs : 1 ≤ s)
    (h1 : α ^ (2 * s) = 1) (h2 : ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0) :
    α ^ s = -1 := by
  have h3 : α ^ s = 1 ∨ α ^ s = -1 := by
    have h4 : (α ^ s) ^ 2 = 1 := by
      calc
        (α ^ s) ^ 2 = α ^ (2 * s) := by
          rw [← pow_mul]
          ring_nf
        _ = 1 := h1
    have h5 : α ^ s = 1 ∨ α ^ s = -1 := by
      have h6 : (α ^ s - 1) * (α ^ s + 1) = 0 := by
        calc
          (α ^ s - 1) * (α ^ s + 1) = (α ^ s) ^ 2 - 1 := by
            ring_nf
          _ = 0 := by
            rw [h4]
            simp [sub_self]
      have h7 : α ^ s - 1 = 0 ∨ α ^ s + 1 = 0 := by
        simpa [sub_eq_zero, add_eq_zero_iff_eq_neg] using eq_zero_or_eq_zero_of_mul_eq_zero h6
      cases h7 with
      | inl h7 =>
        have h8 : α ^ s = 1 := by
          have h9 : α ^ s - 1 = 0 := h7
          have h10 : α ^ s = 1 := by
            rw [sub_eq_zero] at h9
            exact h9
          exact h10
        exact Or.inl h8
      | inr h7 =>
        have h8 : α ^ s = -1 := by
          have h9 : α ^ s + 1 = 0 := h7
          have h10 : α ^ s = -1 := by
            rw [add_eq_zero_iff_eq_neg] at h9
            exact h9
          exact h10
        exact Or.inr h8
    exact h5
  cases h3 with
  | inl h3 =>
    have h4 : s = 0 := by
      have h6 : s < 2 * s := by
        have h8 : s < 2 * s := by
          nlinarith
        exact h8
      have h9 : s = 0 := by
        have h10 : α ^ s = 1 := h3
        have h11 : s < 2 * s := h6
        have h12 : s = 0 := by
          have h13 := h2 s h11 h10
          exact h13
        exact h12
      exact h9
    have h10 : s ≠ 0 := by
      omega
    contradiction
  | inr h3 =>
    exact h3

/-- For `α` of exact order `2s` with `1 ≤ s ≤ n`, the index `s` belongs to `badSet α n`. -/
lemma s_mem_badSet {α : ℂ} {n s : ℕ} (hs : 1 ≤ s) (hsn : s ≤ n)
    (h1 : α ^ (2 * s) = 1) (h2 : ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0) :
    s ∈ badSet α n := by
  unfold badSet
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hs, hsn⟩, pow_s_eq_neg_one hs h1 h2⟩

/-- Main computation for the constructed partition. -/
lemma cCount_constructed_eq_M (α : ℂ) (s n M r : ℕ)
    (l : Multiset ℕ) (hsum : l.sum = n)
    (hs : 1 ≤ s) (hsn : s ≤ n)
    (h1 : α ^ (2 * s) = 1) (h2 : ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hr : r < s) (_hM_eq : M = n / s)
    (hl : l = Multiset.replicate M s + {r}) :
    cCount α n (Nat.Partition.ofSums n l hsum) = n / s := by
  unfold cCount Nat.Partition.mult
  have hpos : ∀ j ∈ badSet α n, j ≠ 0 := by
    intro j hj
    unfold badSet at hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    omega
  have step1 : ∀ j ∈ badSet α n,
      Multiset.count j (Nat.Partition.ofSums n l hsum).parts = Multiset.count j l := by
    intro j hj
    exact Nat.Partition.count_ofSums_of_ne_zero hsum (hpos j hj)
  rw [Finset.sum_congr rfl step1]
  have hsmem : s ∈ badSet α n := s_mem_badSet hs hsn h1 h2
  have key : ∑ j ∈ badSet α n, Multiset.count j l = Multiset.count s l := by
    refine Finset.sum_eq_single s ?_ ?_
    · intro j hj hjs
      rw [hl, Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton]
      have hjr : j ≠ r := by
        unfold badSet at hj
        rw [Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨⟨hj1, _⟩, hjpow⟩ := hj
        have hsj : s ≤ j := s_le_of_pow_eq_neg_one hs ⟨h1, h2⟩ hj1 hjpow
        have hsj' : s < j := lt_of_le_of_ne hsj (Ne.symm hjs)
        omega
      have hsne : s ≠ j := Ne.symm hjs
      rw [if_neg hsne, if_neg hjr]
      rfl
    · intro h; exact absurd hsmem h
  rw [key]
  rw [hl, Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton]
  have hsr : s ≠ r := by omega
  rw [if_pos rfl, if_neg hsr]
  omega

/-- The maximum value `M = ⌊n/s⌋` is achieved: take a partition consisting of `M`
parts equal to `s` together with any partition of the remainder `r = n - M*s`. -/
lemma exists_partition_cCount_eq_M {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hsn : s ≤ n) :
    ∃ p : n.Partition, cCount α n p = n / s := by
  obtain ⟨h1, h2⟩ := hord
  set M : ℕ := n / s with hMdef
  set r : ℕ := n - M * s with hrdef
  let l : Multiset ℕ := Multiset.replicate M s + {r}
  have hMs_le : M * s ≤ n := by
    rw [hMdef]; exact Nat.div_mul_le_self n s
  have hsum : l.sum = n := by
    simp [l, Multiset.sum_replicate]
    rw [hrdef]
    omega
  have hr_lt : r < s := by
    have hspos : 0 < s := hs
    have hmod : n % s < s := Nat.mod_lt _ hspos
    have hreq : r = n % s := by
      rw [hrdef, hMdef, Nat.sub_eq_iff_eq_add (Nat.div_mul_le_self n s)]
      rw [add_comm]
      exact (Nat.div_add_mod n s).symm.trans (by ring_nf)
    rw [hreq]; exact hmod
  refine ⟨Nat.Partition.ofSums n l hsum, ?_⟩
  exact cCount_constructed_eq_M α s n M r l hsum hs hsn h1 h2 hr_lt hMdef rfl

/-- The mapped `gCommon n` divides the mapped `hSummand p` in `ℂ[X]`. -/
lemma gCommon_map_dvd_hSummand_map {n : ℕ} (p : n.Partition) :
    (gCommon n).map (algebraMap ℚ ℂ) ∣ (hSummand p).map (algebraMap ℚ ℂ) :=
  Polynomial.map_dvd _ (gCommon_dvd_hSummand p)

/-- The mapped polynomial `(hSummand p).map (algebraMap ℚ ℂ)` is non-zero. -/
lemma hSummand_map_ne_zero {n : ℕ} (p : n.Partition) :
    (hSummand p).map (algebraMap ℚ ℂ) ≠ 0 := by
  have h : hSummand p ≠ 0 := hSummand_ne_zero p
  intro hcontra
  apply h
  have hinj : Function.Injective (algebraMap ℚ ℂ) :=
    (algebraMap ℚ ℂ).injective
  exact (Polynomial.map_eq_zero_iff hinj).mp hcontra

/-- For `n ≥ 1`, the mapped `gCommon n` is non-zero. -/
lemma gCommon_map_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    (gCommon n).map (algebraMap ℚ ℂ) ≠ 0 := by
  have h : gCommon n ≠ 0 := gCommon_ne_zero n hn
  intro hcontra
  apply h
  have hinj : Function.Injective (algebraMap ℚ ℂ) :=
    (algebraMap ℚ ℂ).injective
  exact (Polynomial.map_eq_zero_iff hinj).mp hcontra

/-- Upper bound: the root multiplicity of the mapped `gCommon n` at `α` is at most
the root multiplicity of the mapped `hSummand p` at `α`, for any partition `p`. -/
lemma rootMultiplicity_gCommon_le {n : ℕ} (p : n.Partition) (α : ℂ) (hn : 1 ≤ n) :
    Polynomial.rootMultiplicity α ((gCommon n).map (algebraMap ℚ ℂ)) ≤
      Polynomial.rootMultiplicity α ((hSummand p).map (algebraMap ℚ ℂ)) := by
  have _hG : (gCommon n).map (algebraMap ℚ ℂ) ≠ 0 := gCommon_map_ne_zero n hn
  have hH : (hSummand p).map (algebraMap ℚ ℂ) ≠ 0 := hSummand_map_ne_zero p
  have hdvd : (gCommon n).map (algebraMap ℚ ℂ) ∣ (hSummand p).map (algebraMap ℚ ℂ) :=
    gCommon_map_dvd_hSummand_map p
  have h1 : (Polynomial.X - Polynomial.C α) ^
      (Polynomial.rootMultiplicity α ((gCommon n).map (algebraMap ℚ ℂ))) ∣
      (gCommon n).map (algebraMap ℚ ℂ) := Polynomial.pow_rootMultiplicity_dvd _ _
  have h2 : (Polynomial.X - Polynomial.C α) ^
      (Polynomial.rootMultiplicity α ((gCommon n).map (algebraMap ℚ ℂ))) ∣
      (hSummand p).map (algebraMap ℚ ℂ) := dvd_trans h1 hdvd
  exact (Polynomial.le_rootMultiplicity_iff hH).mpr h2

/-- Key computational lemma: for a nonzero polynomial `q : ℚ[X]`, we have
`normalize q = C (leadingCoeff q)⁻¹ * q`. -/
lemma normalize_polynomial_rat_eq (q : Polynomial ℚ) (hq : q ≠ 0) :
    normalize q = Polynomial.C (q.leadingCoeff)⁻¹ * q := by
  rw [normalize_apply, Polynomial.coe_normUnit_of_ne_zero hq, mul_comm]

/-- Singleton base case for the linear-combination form of `Finset.gcd`. -/
lemma finset_gcd_lc_singleton {β : Type*} [DecidableEq β]
    (f : β → Polynomial ℚ) (b : β) (hb : f b ≠ 0) :
    ∃ a : β → Polynomial ℚ, ({b} : Finset β).gcd f = ∑ c ∈ ({b} : Finset β), a c * f c := by
  refine ⟨fun c => if c = b then Polynomial.C (f b).leadingCoeff⁻¹ else 0, ?_⟩
  rw [Finset.gcd_singleton, Finset.sum_singleton]
  simp only [↓reduceIte]
  exact normalize_polynomial_rat_eq (f b) hb

/-- Bezout identity for the normalized `gcd` in `Polynomial ℚ`. -/
lemma gcd_eq_linear_combination_poly (x y : Polynomial ℚ) :
    ∃ A B : Polynomial ℚ, gcd x y = A * x + B * y := by
  obtain ⟨a, b, hab⟩ := IsBezout.gcd_eq_sum x y
  obtain ⟨u, hu⟩ := IsBezout.associated_gcd_gcd (R := Polynomial ℚ) (x := x) (y := y)
  refine ⟨a * u, b * u, ?_⟩
  rw [← hu, ← hab]
  ring

/-- Inductive step for linear-combination form of `Finset.gcd`. -/
lemma finset_gcd_lc_insert {β : Type*} [DecidableEq β]
    (s : Finset β) (f : β → Polynomial ℚ) (b : β) (hb : b ∉ s)
    (_hfb : f b ≠ 0)
    (ih : ∃ a : β → Polynomial ℚ, s.gcd f = ∑ c ∈ s, a c * f c) :
    ∃ a : β → Polynomial ℚ, (insert b s).gcd f = ∑ c ∈ insert b s, a c * f c := by
  obtain ⟨a0, ha0⟩ := ih
  obtain ⟨A, B, hAB⟩ := gcd_eq_linear_combination_poly (f b) (s.gcd f)
  classical
  refine ⟨fun c => if c = b then A else B * a0 c, ?_⟩
  rw [Finset.sum_insert hb]
  simp only [if_true]
  have hsum : ∑ c ∈ s, (if c = b then A else B * a0 c) * f c
      = ∑ c ∈ s, (B * a0 c) * f c := by
    apply Finset.sum_congr rfl
    intro c hc
    have : c ≠ b := fun h => hb (h ▸ hc)
    simp [this]
  rw [hsum]
  have hBsum : ∑ c ∈ s, (B * a0 c) * f c = B * s.gcd f := by
    rw [ha0, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hBsum]
  rw [← hAB]
  exact Finset.gcd_insert

/-- Linear combination form of `Finset.gcd` over `Polynomial ℚ`. -/
lemma finset_gcd_eq_linear_combination {β : Type*} [DecidableEq β]
    (s : Finset β) (f : β → Polynomial ℚ) (hs : s.Nonempty)
    (hf : ∀ b ∈ s, f b ≠ 0) :
    ∃ a : β → Polynomial ℚ, s.gcd f = ∑ c ∈ s, a c * f c := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
      have hfa : f a ≠ 0 := hf a (by simp)
      exact finset_gcd_lc_singleton f a hfa
  | cons a t ha _ht ih =>
      have hft : ∀ b ∈ t, f b ≠ 0 := fun b hbt => hf b (by
        rw [Finset.cons_eq_insert]; exact Finset.mem_insert_of_mem hbt)
      have hfa : f a ≠ 0 := hf a (by
        rw [Finset.cons_eq_insert]; exact Finset.mem_insert_self _ _)
      have ih' := ih hft
      rw [Finset.cons_eq_insert]
      exact finset_gcd_lc_insert t f a ha hfa ih'

/-- Lower bound: if every `hSummand p` has multiplicity ≥ m at α, then so does `gCommon n`. -/
lemma rootMultiplicity_gCommon_ge {n : ℕ} (α : ℂ) (hn : 1 ≤ n) (m : ℕ)
    (hm : ∀ p : n.Partition, m ≤
      Polynomial.rootMultiplicity α ((hSummand p).map (algebraMap ℚ ℂ))) :
    m ≤ Polynomial.rootMultiplicity α ((gCommon n).map (algebraMap ℚ ℂ)) := by
  have hG : (gCommon n).map (algebraMap ℚ ℂ) ≠ 0 := gCommon_map_ne_zero n hn
  rw [Polynomial.le_rootMultiplicity_iff hG]
  have hne : (Finset.univ : Finset n.Partition).Nonempty := by
    refine ⟨default, Finset.mem_univ _⟩
  have hfne : ∀ p ∈ (Finset.univ : Finset n.Partition), hSummand p ≠ 0 := fun p _ =>
    hSummand_ne_zero p
  obtain ⟨a, ha⟩ := finset_gcd_eq_linear_combination Finset.univ hSummand hne hfne
  have h_eq : (gCommon n).map (algebraMap ℚ ℂ) =
      ∑ p ∈ (Finset.univ : Finset n.Partition),
        (a p).map (algebraMap ℚ ℂ) * (hSummand p).map (algebraMap ℚ ℂ) := by
    unfold gCommon
    rw [ha]
    simp [Polynomial.map_sum, Polynomial.map_mul]
  rw [h_eq]
  apply Finset.dvd_sum
  intro p _
  have hH : (hSummand p).map (algebraMap ℚ ℂ) ≠ 0 := hSummand_map_ne_zero p
  have hdvd : (Polynomial.X - Polynomial.C α) ^ m ∣ (hSummand p).map (algebraMap ℚ ℂ) :=
    (Polynomial.le_rootMultiplicity_iff hH).mp (hm p)
  exact Dvd.dvd.mul_left hdvd _

/-- The vanishing order of `gCommon n` at `α` is `cC α n - n / s` (= C - M).
Since `gCommon n = gcd_{p} hSummand p`, its `rootMultiplicity` at `α` is the min
over partitions of `rootMultiplicity` of `hSummand p` at `α`, which equals
`cC α n - max_{p} cCount α n p = cC α n - n/s` (using `cCount_le_M` and
`exists_partition_cCount_eq_M`). -/
lemma rootMultiplicity_gCommon {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hsn : s ≤ n) :
    Polynomial.rootMultiplicity α ((gCommon n).map (algebraMap ℚ ℂ)) =
      cC α n - n / s := by
  have hn : 1 ≤ n := le_trans hs hsn
  apply le_antisymm
  · obtain ⟨p₀, hp₀⟩ := exists_partition_cCount_eq_M α s hs hord hsn
    have h1 : Polynomial.rootMultiplicity α ((gCommon n).map (algebraMap ℚ ℂ)) ≤
        Polynomial.rootMultiplicity α ((hSummand p₀).map (algebraMap ℚ ℂ)) :=
      rootMultiplicity_gCommon_le p₀ α hn
    rw [rootMultiplicity_hSummand p₀ α, hp₀] at h1
    exact h1
  · apply rootMultiplicity_gCommon_ge α hn
    intro p
    rw [rootMultiplicity_hSummand p α]
    have hp_le : cCount α n p ≤ n / s := cCount_le_M α s hs hord p
    exact Nat.sub_le_sub_left hp_le _

/-! ### The key nonvanishing statement -/

/- For `α` of exact order `2s` (with `s ≥ 1`) and `r < s`, the sum
`T_r(α) = ∑_{μ ⊢ r} 1 / subsumPoly(μ)(α)` is nonzero.

This is proved in two steps in proof.md:
* Reduction via `D_r(α) * T_r(α) = N_r(α)`. If `T_r(α) = 0`, then `N_r(α) = 0`,
  hence `Φ_{2s} ∣ N_r` (since `N_r` has rational coefficients), so `N_r` vanishes
  at every primitive `2s`-th root, in particular at the principal one `ζ = e^{iπ/s}`.
  Then since `D_r(ζ) ≠ 0`, we'd have `T_r(ζ) = 0`.
* Positivity: `T_r(ζ) = τ^{-r} * (positive real)` where `τ = e^{iπ/(2s)}`, so it
  cannot be zero.
-/
/-- The "denominator" polynomial `D_r := ∏_μ subsumPoly μ` in ℚ[X]. -/
def DrPoly (r : ℕ) : Polynomial ℚ :=
  ∏ μ : r.Partition, subsumPoly μ

/-- The "numerator" polynomial `N_r := ∑_μ ∏_{ν ≠ μ} subsumPoly ν` in ℚ[X]. -/
def NrPoly (r : ℕ) : Polynomial ℚ :=
  ∑ μ : r.Partition, ∏ ν ∈ (Finset.univ.erase μ), subsumPoly ν

/-- The "principal" primitive `2s`-th root of unity in ℂ. -/
def principalRoot (s : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2 * s))

/-- The principal "half-angle" root `τ = exp(iπ/(2s))`. -/
def halfRoot (s : ℕ) : ℂ := Complex.exp (Real.pi * Complex.I / (2 * s))

lemma pow_ne_neg_one_of_lt {s : ℕ} (hs : 1 ≤ s) (α : ℂ)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    {ℓ : ℕ} (hℓpos : 0 < ℓ) (hℓlt : ℓ < s) :
    α ^ ℓ ≠ -1 := by
  intro hpow
  have hsle : s ≤ ℓ := s_le_of_pow_eq_neg_one hs hord hℓpos hpow
  exact (lt_irrefl _ (lt_of_lt_of_le hℓlt hsle))

lemma subsumPoly_eval_eq_prod {r : ℕ} (α : ℂ) (μ : r.Partition) :
    (((subsumPoly μ).map (algebraMap ℚ ℂ)).eval α) =
      (μ.parts.map (fun i => (1 : ℂ) + α ^ i)).prod := by
  unfold subsumPoly
  rw [Polynomial.map_multiset_prod, Polynomial.eval_multiset_prod]
  rw [Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro i _
  simp

lemma subsumPoly_eval_ne_zero {s r : ℕ} (hs : 1 ≤ s) (hr : r < s) (α : ℂ)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (μ : r.Partition) :
    (((subsumPoly μ).map (algebraMap ℚ ℂ)).eval α) ≠ 0 := by
  rw [subsumPoly_eval_eq_prod]
  apply Multiset.prod_ne_zero
  simp only [Multiset.mem_map, not_exists, not_and]
  intro i hi heq
  have hipos : 0 < i := Nat.Partition.parts_pos μ hi
  have hir : i ≤ r := by
    have hsum : μ.parts.sum = r := Nat.Partition.parts_sum μ
    have hposall : ∀ x ∈ μ.parts, 0 ≤ x := fun x _ => Nat.zero_le x
    have hle : i ≤ μ.parts.sum := Multiset.single_le_sum hposall i hi
    simpa [hsum] using hle
  have his : i < s := lt_of_le_of_lt hir hr
  have hne : α ^ i ≠ -1 := pow_ne_neg_one_of_lt hs α hord hipos his
  apply hne
  have : α ^ i = -1 := by linear_combination heq
  exact this

lemma DrPoly_eval (r : ℕ) (α : ℂ) :
    ((DrPoly r).map (algebraMap ℚ ℂ)).eval α =
      ∏ μ : r.Partition, (((subsumPoly μ).map (algebraMap ℚ ℂ)).eval α) := by
  unfold DrPoly
  rw [Polynomial.map_prod, Polynomial.eval_prod]

lemma DrPoly_eval_mul_sum_inv_eq_NrPoly_eval (r : ℕ) (α : ℂ)
    (hne : ∀ μ : r.Partition, (((subsumPoly μ).map (algebraMap ℚ ℂ)).eval α) ≠ 0) :
    ((DrPoly r).map (algebraMap ℚ ℂ)).eval α *
      ∑ μ : r.Partition, (((subsumPoly μ).map (algebraMap ℚ ℂ)).eval α)⁻¹ =
      ((NrPoly r).map (algebraMap ℚ ℂ)).eval α := by
  set S : r.Partition → ℂ :=
    fun μ => (((subsumPoly μ).map (algebraMap ℚ ℂ)).eval α) with hS
  have hD : ((DrPoly r).map (algebraMap ℚ ℂ)).eval α =
      ∏ μ : r.Partition, S μ := by
    unfold DrPoly
    rw [Polynomial.map_prod, Polynomial.eval_prod]
  have hN : ((NrPoly r).map (algebraMap ℚ ℂ)).eval α =
      ∑ μ : r.Partition, ∏ ν ∈ (Finset.univ.erase μ : Finset r.Partition), S ν := by
    unfold NrPoly
    rw [Polynomial.map_sum, Polynomial.eval_finset_sum]
    simp [Polynomial.map_prod, Polynomial.eval_prod, hS]
  rw [hD, hN]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [← Finset.prod_erase_mul (Finset.univ : Finset r.Partition) S hμ,
      mul_assoc, mul_inv_cancel₀ (hne μ), mul_one]

lemma DrPoly_eval_ne_zero {s r : ℕ} (hs : 1 ≤ s) (hr : r < s) (α : ℂ)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0) :
    ((DrPoly r).map (algebraMap ℚ ℂ)).eval α ≠ 0 := by
  rw [DrPoly_eval]
  rw [Finset.prod_ne_zero_iff]
  intro μ _
  exact subsumPoly_eval_ne_zero hs hr α hord μ

lemma principalRoot_isPrimitiveRoot {s : ℕ} (hs : 1 ≤ s) :
    IsPrimitiveRoot (principalRoot s) (2 * s) := by
  have _h := hs
  have h₁ : (2 * s : ℕ) ≠ 0 := by positivity
  have h₂ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (2 * s : ℂ))) (2 * s) := by
    have h₃ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / ((2 * s : ℕ) : ℂ))) (2 * s) := by
      apply Complex.isPrimitiveRoot_exp
      norm_cast
    convert h₃ using 1
    simp_all
  simpa [principalRoot] using h₂

lemma principalRoot_order {s : ℕ} (hs : 1 ≤ s) :
    (principalRoot s) ^ (2 * s) = 1 ∧
      ∀ k : ℕ, k < 2 * s → (principalRoot s) ^ k = 1 → k = 0 := by
  have hprim : IsPrimitiveRoot (principalRoot s) (2 * s) :=
    principalRoot_isPrimitiveRoot hs
  refine ⟨hprim.pow_eq_one, ?_⟩
  intro k hk_lt h_pow
  have hdvd : (2 * s) ∣ k := hprim.dvd_of_pow_eq_one k h_pow
  rcases hdvd with ⟨t, rfl⟩
  rcases Nat.eq_zero_or_pos t with ht | ht
  · simp [ht]
  · exfalso
    have : 2 * s ≤ 2 * s * t := Nat.le_mul_of_pos_right (2 * s) ht
    omega

lemma isPrimitiveRoot_of_hord {s : ℕ} (hs : 1 ≤ s) (α : ℂ)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0) :
    IsPrimitiveRoot α (2 * s) := by
  obtain ⟨h1, h2⟩ := hord
  refine ⟨h1, ?_⟩
  intro l hl
  have hs2 : 0 < 2 * s := by omega
  rcases Nat.lt_or_ge l (2 * s) with hlt | hge
  · have : l = 0 := h2 l hlt hl
    simp [this]
  · have hmod : l % (2 * s) < 2 * s := Nat.mod_lt _ hs2
    have hl_mod : α ^ (l % (2 * s)) = 1 := by
      have heq : α ^ l = α ^ ((2 * s) * (l / (2 * s)) + l % (2 * s)) := by
        congr 1
        exact (Nat.div_add_mod l (2 * s)).symm
      rw [heq, pow_add, pow_mul] at hl
      rw [h1, one_pow, one_mul] at hl
      exact hl
    have : l % (2 * s) = 0 := h2 (l % (2 * s)) hmod hl_mod
    exact Nat.dvd_of_mod_eq_zero this

lemma cyclotomic_eval_principalRoot {s : ℕ} (hs : 1 ≤ s) :
    ((Polynomial.cyclotomic (2 * s) ℚ).map (algebraMap ℚ ℂ)).eval (principalRoot s) = 0 := by
  have hne : (2 * s : ℕ) ≠ 0 := by omega
  have hpos : 0 < 2 * s := by omega
  have hprim : IsPrimitiveRoot (principalRoot s) (2 * s) :=
    principalRoot_isPrimitiveRoot hs
  have h_root : (Polynomial.cyclotomic (2 * s) ℂ).IsRoot (principalRoot s) :=
    hprim.isRoot_cyclotomic hpos
  have h_map : (Polynomial.cyclotomic (2 * s) ℚ).map (algebraMap ℚ ℂ)
      = Polynomial.cyclotomic (2 * s) ℂ :=
    Polynomial.map_cyclotomic (2 * s) (algebraMap ℚ ℂ)
  rw [h_map]
  exact h_root

lemma cyclotomic_dvd_NrPoly_of_eval_zero {s r : ℕ} (hs : 1 ≤ s) (α : ℂ)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (h : ((NrPoly r).map (algebraMap ℚ ℂ)).eval α = 0) :
    Polynomial.cyclotomic (2 * s) ℚ ∣ NrPoly r := by
  have hα_prim : IsPrimitiveRoot α (2 * s) := isPrimitiveRoot_of_hord hs α hord
  have hpos : 0 < 2 * s := by omega
  have h' : (Polynomial.aeval α) (NrPoly r) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact h
  have hmin_dvd : minpoly ℚ α ∣ NrPoly r := minpoly.dvd ℚ α h'
  have hcyc_eq : Polynomial.cyclotomic (2 * s) ℚ = minpoly ℚ α :=
    Polynomial.cyclotomic_eq_minpoly_rat hα_prim hpos
  rw [hcyc_eq]
  exact hmin_dvd

lemma NrPoly_eval_principalRoot_eq_zero {s r : ℕ} (hs : 1 ≤ s)
    (h : Polynomial.cyclotomic (2 * s) ℚ ∣ NrPoly r) :
    ((NrPoly r).map (algebraMap ℚ ℂ)).eval (principalRoot s) = 0 :=
  eval_map_eq_zero_of_dvd_of_eval_eq_zero
    (Polynomial.cyclotomic (2 * s) ℚ) (NrPoly r) h
    (principalRoot s) (cyclotomic_eval_principalRoot hs)

lemma principalRoot_eq_halfRoot_sq (s : ℕ) :
    principalRoot s = (halfRoot s) ^ 2 := by
  have h₁ : (halfRoot s : ℂ) = Complex.exp (Real.pi * Complex.I / (2 * s)) := rfl
  have h₂ : (principalRoot s : ℂ) = Complex.exp (2 * Real.pi * Complex.I / (2 * s)) := rfl
  rw [h₁, h₂]
  have h₃ : (Complex.exp (Real.pi * Complex.I / (2 * s)) : ℂ) ^ 2 = Complex.exp (2 * (Real.pi * Complex.I / (2 * s))) := by
    rw [← Complex.exp_nat_mul]
    ring_nf
  rw [h₃]
  ring_nf

lemma one_add_exp_two_I_mul_eq_two_cos_mul_exp (θ : ℂ) :
    1 + Complex.exp (2 * Complex.I * θ) =
      2 * Complex.cos θ * Complex.exp (Complex.I * θ) := by
  have h₀ : Complex.exp (2 * Complex.I * θ) = Complex.exp (Complex.I * θ + Complex.I * θ) := by
    ring_nf
  have h₁ : Complex.exp (Complex.I * θ + Complex.I * θ) = Complex.exp (Complex.I * θ) * Complex.exp (Complex.I * θ) := by
    rw [Complex.exp_add]
  have h₂ : Complex.cos θ = (Complex.exp (Complex.I * θ) + Complex.exp (-Complex.I * θ)) / 2 := by
    rw [Complex.cos]
    simp [Complex.exp_neg]
    ring_nf
  have h₃ : Complex.exp (Complex.I * θ) * Complex.exp (-(Complex.I * θ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  calc
    1 + Complex.exp (2 * Complex.I * θ) = 1 + Complex.exp (Complex.I * θ + Complex.I * θ) := by rw [h₀]
    _ = 1 + (Complex.exp (Complex.I * θ) * Complex.exp (Complex.I * θ)) := by rw [h₁]
    _ = 2 * Complex.cos θ * Complex.exp (Complex.I * θ) := by
      rw [h₂]
      have h5 : Complex.exp (-Complex.I * θ) = Complex.exp (-(Complex.I * θ)) := by ring_nf
      rw [h5]
      linear_combination -h₃

lemma halfRoot_pow (s ℓ : ℕ) :
    (halfRoot s) ^ ℓ = Complex.exp (Complex.I * (Real.pi * ℓ / (2 * s))) := by
  unfold halfRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

lemma cos_real_cast (s ℓ : ℕ) :
    Complex.cos ((Real.pi * ℓ / (2 * s) : ℂ)) =
      (Real.cos (Real.pi * ℓ / (2 * s)) : ℂ) := by
  have h : ((Real.pi * ℓ / (2 * s) : ℝ) : ℂ) = (Real.pi * ℓ / (2 * s) : ℂ) := by push_cast; ring
  rw [← h, Complex.ofReal_cos]

lemma one_add_halfRoot_two_mul_pow_eq (s ℓ : ℕ) :
    (1 : ℂ) + (halfRoot s) ^ (2 * ℓ) =
      (2 * Real.cos (Real.pi * ℓ / (2 * s)) : ℂ) * (halfRoot s) ^ ℓ := by
  have h1 : (halfRoot s) ^ (2 * ℓ) =
      Complex.exp (2 * Complex.I * (Real.pi * ℓ / (2 * s))) := by
    rw [show 2 * ℓ = ℓ + ℓ from by ring, pow_add, halfRoot_pow]
    rw [← Complex.exp_add]
    ring_nf
  have h2 : (halfRoot s) ^ ℓ =
      Complex.exp (Complex.I * (Real.pi * ℓ / (2 * s))) := halfRoot_pow s ℓ
  rw [h1, h2]
  rw [one_add_exp_two_I_mul_eq_two_cos_mul_exp]
  rw [cos_real_cast]

lemma cos_pos_of_lt {s ℓ : ℕ} (hs : 1 ≤ s) (hℓpos : 1 ≤ ℓ) (hℓlt : ℓ < s) :
    0 < Real.cos (Real.pi * ℓ / (2 * s)) := by
  have h₁ : (ℓ : ℝ) / (s : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast hℓlt
  have h₃ : Real.pi * (ℓ : ℝ) / (2 * (s : ℝ)) < Real.pi / 2 := by
    have h₃' : Real.pi * (ℓ : ℝ) / (2 * (s : ℝ)) = (Real.pi / 2) * ((ℓ : ℝ) / (s : ℝ)) := by
      field_simp [mul_assoc]
    rw [h₃']
    have h₅ : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓpos
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have h₄ : 0 < Real.pi * (ℓ : ℝ) / (2 * (s : ℝ)) := by positivity
  have h₆ : Real.cos (Real.pi * ℓ / (2 * s)) = Real.cos (Real.pi * (ℓ : ℝ) / (2 * (s : ℝ))) := by
    norm_num
  rw [h₆]
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

lemma halfRoot_ne_zero (s : ℕ) : halfRoot s ≠ 0 := by
  unfold halfRoot
  exact Complex.exp_ne_zero _

lemma multiset_prod_pow_eq_pow_sum (a : ℂ) (S : Multiset ℕ) :
    (S.map (fun ℓ : ℕ => a ^ ℓ)).prod = a ^ S.sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons ℓ S' ih => simp [Multiset.prod_cons, ih, pow_add]

lemma multiset_prod_real_cast_complex (S : Multiset ℕ) (f : ℕ → ℝ) :
    ((S.map f).prod : ℂ) = (S.map (fun ℓ : ℕ => (f ℓ : ℂ))).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons ℓ S' ih => simp [Multiset.prod_cons, ih, Complex.ofReal_mul]

lemma multiset_prod_factorization {s r : ℕ} (μ : r.Partition) :
    (μ.parts.map (fun ℓ : ℕ =>
        (2 * Real.cos (Real.pi * ℓ / (2 * s)) : ℂ) * (halfRoot s) ^ ℓ)).prod =
      ((μ.parts.map (fun ℓ : ℕ =>
        (2 * Real.cos (Real.pi * ℓ / (2 * s))))).prod : ℂ) * (halfRoot s) ^ r := by
  have hfun : (fun ℓ : ℕ =>
        (2 * Real.cos (Real.pi * ℓ / (2 * s)) : ℂ) * (halfRoot s) ^ ℓ) =
      (fun ℓ : ℕ =>
        ((2 * Real.cos (Real.pi * ℓ / (2 * s)) : ℝ) : ℂ) * (halfRoot s) ^ ℓ) := by
    funext ℓ; push_cast; ring
  rw [hfun]
  rw [Multiset.prod_map_mul]
  congr 1
  · exact (multiset_prod_real_cast_complex μ.parts
      (fun ℓ => 2 * Real.cos (Real.pi * ℓ / (2 * s)))).symm
  · rw [multiset_prod_pow_eq_pow_sum]
    rw [μ.parts_sum]

lemma multiset_prod_cos_pos {s r : ℕ} (hs : 1 ≤ s) (hr : r < s) (μ : r.Partition) :
    0 < (μ.parts.map (fun ℓ : ℕ => 2 * Real.cos (Real.pi * ℓ / (2 * s)))).prod := by
  apply Multiset.prod_pos
  intro a ha
  rw [Multiset.mem_map] at ha
  obtain ⟨ℓ, hℓmem, rfl⟩ := ha
  have hℓpos : 1 ≤ ℓ := μ.parts_pos hℓmem
  have hℓ_le_r : ℓ ≤ r := by
    have hsum : μ.parts.sum = r := μ.parts_sum
    have := Multiset.single_le_sum (s := μ.parts)
      (fun x _ => Nat.zero_le x) ℓ hℓmem
    simpa [hsum] using this
  have hℓlt : ℓ < s := lt_of_le_of_lt hℓ_le_r hr
  have hcos : 0 < Real.cos (Real.pi * ℓ / (2 * s)) := cos_pos_of_lt hs hℓpos hℓlt
  positivity

lemma subsumPoly_eval_principalRoot_eq {s r : ℕ} (hs : 1 ≤ s) (hr : r < s) (μ : r.Partition) :
    ∃ C : ℝ, 0 < C ∧
      ((subsumPoly μ).map (algebraMap ℚ ℂ)).eval (principalRoot s) =
        (C : ℂ) * (halfRoot s) ^ r := by
  refine ⟨(μ.parts.map (fun ℓ : ℕ => 2 * Real.cos (Real.pi * ℓ / (2 * s)))).prod, ?_, ?_⟩
  · exact multiset_prod_cos_pos hs hr μ
  · rw [subsumPoly_eval_eq_prod (principalRoot s) μ]
    rw [principalRoot_eq_halfRoot_sq s]
    have hfact : ∀ ℓ : ℕ,
        (1 : ℂ) + ((halfRoot s) ^ 2) ^ ℓ =
          (2 * Real.cos (Real.pi * ℓ / (2 * s)) : ℂ) * (halfRoot s) ^ ℓ := by
      intro ℓ
      rw [← pow_mul]
      exact one_add_halfRoot_two_mul_pow_eq s ℓ
    have hmap : (μ.parts.map (fun i => (1 : ℂ) + ((halfRoot s) ^ 2) ^ i)) =
        (μ.parts.map (fun ℓ : ℕ =>
          (2 * Real.cos (Real.pi * ℓ / (2 * s)) : ℂ) * (halfRoot s) ^ ℓ)) := by
      apply Multiset.map_congr rfl
      intro ℓ _
      exact hfact ℓ
    rw [hmap]
    exact multiset_prod_factorization μ

lemma inv_subsumPoly_eval_principalRoot_eq {s r : ℕ} (hs : 1 ≤ s) (hr : r < s) (μ : r.Partition) :
    ∃ C : ℝ, 0 < C ∧
      (((subsumPoly μ).map (algebraMap ℚ ℂ)).eval (principalRoot s))⁻¹ =
        ((C : ℂ))⁻¹ * ((halfRoot s) ^ r)⁻¹ := by
  obtain ⟨C, hCpos, hCeq⟩ := subsumPoly_eval_principalRoot_eq hs hr μ
  refine ⟨C, hCpos, ?_⟩
  rw [hCeq]
  rw [mul_inv]

lemma sum_inv_pos_of_partitions {r : ℕ}
    (C : r.Partition → ℝ) (hCpos : ∀ μ, 0 < C μ) :
    0 < ∑ μ : r.Partition, (C μ)⁻¹ := by
  have h_nonempty : Nonempty r.Partition := ⟨Nat.Partition.indiscrete r⟩
  have h_finset_nonempty : (Finset.univ : Finset r.Partition).Nonempty :=
    Finset.univ_nonempty
  apply Finset.sum_pos
  · intro μ _
    exact inv_pos.mpr (hCpos μ)
  · exact h_finset_nonempty

lemma sum_inv_subsumPoly_principalRoot_eq_real_mul {s r : ℕ} (hs : 1 ≤ s) (hr : r < s) :
    ∃ S : ℝ, 0 < S ∧
      ∑ μ : r.Partition,
          (((subsumPoly μ).map (algebraMap ℚ ℂ)).eval (principalRoot s))⁻¹ =
        (S : ℂ) * ((halfRoot s) ^ r)⁻¹ := by
  classical
  choose C hCpos hCeq using fun μ : r.Partition => inv_subsumPoly_eval_principalRoot_eq hs hr μ
  refine ⟨∑ μ : r.Partition, (C μ)⁻¹, ?_, ?_⟩
  · exact sum_inv_pos_of_partitions C hCpos
  · simp_rw [hCeq]
    rw [← Finset.sum_mul]
    congr 1
    push_cast
    rfl

lemma sum_inv_subsumPoly_principalRoot_ne_zero {s r : ℕ} (hs : 1 ≤ s) (hr : r < s) :
    ∑ μ : r.Partition,
        (((subsumPoly μ).map (algebraMap ℚ ℂ)).eval (principalRoot s))⁻¹ ≠ 0 := by
  obtain ⟨S, hSpos, hSeq⟩ := sum_inv_subsumPoly_principalRoot_eq_real_mul hs hr
  rw [hSeq]
  have hS : (S : ℂ) ≠ 0 := by exact_mod_cast hSpos.ne'
  have hτ : halfRoot s ≠ 0 := halfRoot_ne_zero s
  have hτr : (halfRoot s) ^ r ≠ 0 := pow_ne_zero _ hτ
  have hτrinv : ((halfRoot s) ^ r)⁻¹ ≠ 0 := inv_ne_zero hτr
  exact mul_ne_zero hS hτrinv

lemma sum_inv_subsumPoly_ne_zero {s r : ℕ} (hs : 1 ≤ s) (hr : r < s) (α : ℂ)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0) :
    ∑ μ : r.Partition,
      (((subsumPoly μ).map (algebraMap ℚ ℂ)).eval α)⁻¹ ≠ 0 := by
  intro hT
  have hne : ∀ μ : r.Partition, (((subsumPoly μ).map (algebraMap ℚ ℂ)).eval α) ≠ 0 :=
    fun μ => subsumPoly_eval_ne_zero hs hr α hord μ
  have hD : ((DrPoly r).map (algebraMap ℚ ℂ)).eval α ≠ 0 :=
    DrPoly_eval_ne_zero hs hr α hord
  have hN_eval : ((NrPoly r).map (algebraMap ℚ ℂ)).eval α = 0 := by
    have := DrPoly_eval_mul_sum_inv_eq_NrPoly_eval r α hne
    rw [hT, mul_zero] at this
    exact this.symm
  have hdvd := cyclotomic_dvd_NrPoly_of_eval_zero hs α hord hN_eval
  have hNζ : ((NrPoly r).map (algebraMap ℚ ℂ)).eval (principalRoot s) = 0 :=
    NrPoly_eval_principalRoot_eq_zero hs hdvd
  have hneζ : ∀ μ : r.Partition,
      (((subsumPoly μ).map (algebraMap ℚ ℂ)).eval (principalRoot s)) ≠ 0 :=
    fun μ => subsumPoly_eval_ne_zero hs hr (principalRoot s) (principalRoot_order hs) μ
  have hDζ : ((DrPoly r).map (algebraMap ℚ ℂ)).eval (principalRoot s) ≠ 0 :=
    DrPoly_eval_ne_zero hs hr (principalRoot s) (principalRoot_order hs)
  have hidζ := DrPoly_eval_mul_sum_inv_eq_NrPoly_eval r (principalRoot s) hneζ
  rw [hNζ] at hidζ
  have hTζ : ∑ μ : r.Partition,
      (((subsumPoly μ).map (algebraMap ℚ ℂ)).eval (principalRoot s))⁻¹ = 0 := by
    rcases mul_eq_zero.mp hidζ with h | h
    · exact absurd h hDζ
    · exact h
  exact sum_inv_subsumPoly_principalRoot_ne_zero hs hr hTζ

/-! ### Putting it together: lowest-order coefficient -/

lemma eval_zero_hSummand {n : ℕ} (p : n.Partition) :
    Polynomial.eval (0 : ℚ) (hSummand p) = 1 := by
  unfold hSummand
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_one
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_pow, Polynomial.eval_X]
  have h0 : (0 : ℚ) ^ i = 0 := zero_pow (by omega)
  rw [h0, add_zero, one_pow]

lemma eval_zero_numStar (n : ℕ) :
    Polynomial.eval (0 : ℚ) (numStar n) = (Fintype.card (n.Partition) : ℚ) := by
  unfold numStar
  rw [Polynomial.eval_finset_sum]
  simp only [eval_zero_hSummand]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

lemma one_le_card_partition {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ Fintype.card (n.Partition) := by
  have : Nonempty n.Partition := ⟨Nat.Partition.indiscrete n⟩
  have _h := hn
  exact Fintype.card_pos

lemma numStar_map_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    Polynomial.map (algebraMap ℚ ℂ) (numStar n) ≠ 0 := by
  have hcard : 1 ≤ Fintype.card (n.Partition) := one_le_card_partition hn
  have heval : Polynomial.eval (0 : ℚ) (numStar n) = (Fintype.card (n.Partition) : ℚ) :=
    eval_zero_numStar n
  have hne_rat : numStar n ≠ 0 := by
    intro h
    rw [h, Polynomial.eval_zero] at heval
    have hpos : (0 : ℚ) < (Fintype.card (n.Partition) : ℚ) := by exact_mod_cast hcard
    linarith
  have hinj : Function.Injective (algebraMap ℚ ℂ) := (algebraMap ℚ ℂ).injective
  exact (Polynomial.map_ne_zero_iff hinj).mpr hne_rat

lemma pow_X_sub_C_dvd_numStar_map {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0) :
    (Polynomial.X - Polynomial.C α) ^ (cC α n - n / s) ∣
      (numStar n).map (algebraMap ℚ ℂ) := by
  have hsumm : ∀ p : n.Partition,
      (Polynomial.X - Polynomial.C α) ^ (cC α n - n / s) ∣
        (hSummand p).map (algebraMap ℚ ℂ) := by
    intro p
    have hmul : Polynomial.rootMultiplicity α ((hSummand p).map (algebraMap ℚ ℂ)) =
        cC α n - cCount α n p := rootMultiplicity_hSummand p α
    have hcount : cCount α n p ≤ n / s := cCount_le_M α s hs hord p
    have hle : cC α n - n / s ≤
        Polynomial.rootMultiplicity α ((hSummand p).map (algebraMap ℚ ℂ)) := by
      rw [hmul]
      exact Nat.sub_le_sub_left hcount _
    have hne : (hSummand p).map (algebraMap ℚ ℂ) ≠ 0 := hSummand_map_ne_zero p
    exact (Polynomial.le_rootMultiplicity_iff hne).mp hle
  have hmap : (numStar n).map (algebraMap ℚ ℂ) =
      ∑ p : n.Partition, (hSummand p).map (algebraMap ℚ ℂ) := by
    simp [numStar, Polynomial.map_sum]
  rw [hmap]
  exact Finset.dvd_sum (fun p _ => hsumm p)

namespace M_quo
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
open Polynomial Finset

/-- For `α` of exact order `2s`, the count `c(λ) = ∑_{j ∈ B} m_λ(j)`. -/
def cCount (α : ℂ) (n : ℕ) (p : n.Partition) : ℕ :=
  ∑ j ∈ badSet α n, p.mult j

------------------------------------------------------------
-- Helper lemmas
------------------------------------------------------------

lemma one_add_X_pow_ne_zero (i : ℕ) (hi : 1 ≤ i) :
    ((1 : Polynomial ℚ) + X ^ i) ≠ 0 := by
  intro h
  have hc : Polynomial.coeff ((1 : Polynomial ℚ) + X ^ i) 0 = 0 := by rw [h]; simp
  have hone : Polynomial.coeff ((1 : Polynomial ℚ) + X ^ i) 0 = 1 := by
    rw [Polynomial.coeff_add, Polynomial.coeff_one_zero, Polynomial.coeff_X_pow]
    have hne : (0 : ℕ) ≠ i := by omega
    simp [hne]
  rw [hone] at hc
  exact one_ne_zero hc

lemma hSummand_ne_zero {n : ℕ} (p : n.Partition) : hSummand p ≠ 0 := by
  unfold hSummand
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.mem_Icc] at hi
  exact pow_ne_zero _ (one_add_X_pow_ne_zero i hi.1)

lemma hSummand_map_ne_zero {n : ℕ} (p : n.Partition) :
    (hSummand p).map (algebraMap ℚ ℂ) ≠ 0 := by
  have h : hSummand p ≠ 0 := hSummand_ne_zero p
  intro hcontra
  apply h
  have hinj : Function.Injective (algebraMap ℚ ℂ) :=
    (algebraMap ℚ ℂ).injective
  exact (Polynomial.map_eq_zero_iff hinj).mp hcontra

lemma subset_Icc_of_partition_parts {n : ℕ} (p : n.Partition) :
    p.parts.toFinset ⊆ Finset.Icc 1 n := by
  intro x hx
  rw [Multiset.mem_toFinset] at hx
  have hpos : 0 < x := p.parts_pos hx
  have hle : x ≤ n := by
    have := Multiset.le_sum_of_mem hx
    rw [p.parts_sum] at this
    exact this
  exact Finset.mem_Icc.mpr ⟨hpos, hle⟩

lemma mult_eq_zero_of_not_mem_toFinset {n : ℕ} (p : n.Partition) (i : ℕ)
    (h : i ∉ p.parts.toFinset) : p.mult i = 0 := by
  have h₁ : i ∉ p.parts := fun h₂ => h (Multiset.mem_toFinset.mpr h₂)
  simp_all [Nat.Partition.mult]

lemma sum_mult_eq_n {n : ℕ} (p : n.Partition) :
    ∑ i ∈ Finset.Icc 1 n, i * p.mult i = n := by
  have hsub : p.parts.toFinset ⊆ Finset.Icc 1 n := subset_Icc_of_partition_parts p
  have hsum : p.parts.sum =
      ∑ i ∈ Finset.Icc 1 n, Multiset.count i p.parts • i :=
    Finset.sum_multiset_count_of_subset p.parts (Finset.Icc 1 n) hsub
  have heq : ∑ i ∈ Finset.Icc 1 n, i * p.mult i
      = ∑ i ∈ Finset.Icc 1 n, Multiset.count i p.parts • i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [Nat.Partition.mult, Nat.mul_comm, smul_eq_mul]
  rw [heq, ← hsum, p.parts_sum]

lemma i_mul_mult_le_n {n : ℕ} (p : n.Partition) {i : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i ≤ n) : i * p.mult i ≤ n := by
  have hmul := sum_mult_eq_n p
  have hi_mem : i ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hi1, hi2⟩
  have hle : i * p.mult i ≤ ∑ j ∈ Finset.Icc 1 n, j * p.mult j :=
    Finset.single_le_sum (f := fun j => j * p.mult j) (fun _ _ => Nat.zero_le _) hi_mem
  omega

lemma mult_le_div {n : ℕ} (p : n.Partition) (i : ℕ) : p.mult i ≤ n / i := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [Nat.div_zero]
    have h0 : (0 : ℕ) ∉ p.parts.toFinset := by
      intro hmem
      have := subset_Icc_of_partition_parts p hmem
      simp [Finset.mem_Icc] at this
    exact (mult_eq_zero_of_not_mem_toFinset p 0 h0).le
  · by_cases hin : i ≤ n
    · rw [Nat.le_div_iff_mul_le hi]
      have := i_mul_mult_le_n p hi hin
      rw [Nat.mul_comm] at this
      exact this
    · push_neg at hin
      have hi_notin : i ∉ p.parts.toFinset := by
        intro hmem
        have := subset_Icc_of_partition_parts p hmem
        simp [Finset.mem_Icc] at this
        omega
      rw [mult_eq_zero_of_not_mem_toFinset p i hi_notin]
      exact Nat.zero_le _

lemma rootMultiplicity_pow_aux {R : Type*} [CommRing R] [IsDomain R]
    (g : Polynomial R) (k : ℕ) (x : R) (hg : g ≠ 0) :
    Polynomial.rootMultiplicity x (g ^ k) = k * Polynomial.rootMultiplicity x g := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h₂ : g ^ n ≠ 0 := pow_ne_zero _ hg
    calc
      Polynomial.rootMultiplicity x (g ^ (n + 1))
          = Polynomial.rootMultiplicity x (g ^ n * g) := by ring_nf
      _ = Polynomial.rootMultiplicity x (g ^ n) + Polynomial.rootMultiplicity x g := by
            rw [Polynomial.rootMultiplicity_mul (by exact mul_ne_zero h₂ hg)]
      _ = n * Polynomial.rootMultiplicity x g + Polynomial.rootMultiplicity x g := by rw [ih]
      _ = (n + 1) * Polynomial.rootMultiplicity x g := by ring

lemma rootMultiplicity_prod_aux {R : Type*} [CommRing R] [IsDomain R] {ι : Type*}
    (S : Finset ι) (f : ι → Polynomial R) (x : R) (hf : ∀ i ∈ S, f i ≠ 0) :
    Polynomial.rootMultiplicity x (∏ i ∈ S, f i) = ∑ i ∈ S, Polynomial.rootMultiplicity x (f i) := by
  classical
  induction' S using Finset.induction_on with i s his ih
  · simp
  · have h₃ : f i ≠ 0 := hf i (Finset.mem_insert_self i s)
    have h₄ : ∀ i ∈ s, f i ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have h₇ : (∏ j ∈ s, f j) ≠ 0 := Finset.prod_ne_zero_iff.mpr h₄
    rw [Finset.prod_insert his, Finset.sum_insert his,
        Polynomial.rootMultiplicity_mul (mul_ne_zero h₃ h₇), ih h₄]

lemma one_add_X_pow_ne_zero_complex (i : ℕ) :
    ((1 : Polynomial ℂ) + Polynomial.X ^ i) ≠ 0 := by
  intro h
  have h₁ := congr_arg (fun p => Polynomial.eval 0 p) h
  simp [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X] at h₁
  cases i <;> simp_all [pow_succ]

lemma rootMultiplicity_one_add_X_pow_complex_zero_case
    (α : ℂ) (i : ℕ) (h : α ^ i ≠ -1) :
    Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + Polynomial.X ^ i) = 0 := by
  have h₁ : ¬Polynomial.IsRoot ((1 : Polynomial ℂ) + Polynomial.X ^ i) α := by
    intro h₂
    have h₃ : Polynomial.eval α ((1 : Polynomial ℂ) + Polynomial.X ^ i) = 0 := h₂
    have h₄ : Polynomial.eval α ((1 : Polynomial ℂ) + Polynomial.X ^ i) = (1 : ℂ) + α ^ i := by
      simp
    rw [h₄] at h₃
    have h₆ : α ^ i = -1 := by linear_combination h₃
    exact h h₆
  rw [Polynomial.rootMultiplicity_eq_zero h₁]

lemma rootMultiplicity_one_add_X_pow_complex_one_case_le
    (α : ℂ) (i : ℕ) (hi : 1 ≤ i) (h : α ^ i = -1) :
    Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + Polynomial.X ^ i) ≤ 1 := by
  set p : Polynomial ℂ := 1 + Polynomial.X ^ i with hp
  have hp_ne : p ≠ 0 := one_add_X_pow_ne_zero_complex i
  rw [Polynomial.rootMultiplicity_le_iff hp_ne α 1]
  intro hdvd
  have hderiv_dvd : (Polynomial.X - Polynomial.C α) ∣ Polynomial.derivative p := by
    have := Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hdvd
    simpa using this
  have hderiv : Polynomial.derivative p =
      Polynomial.C (i : ℂ) * Polynomial.X ^ (i - 1) := by
    simp [hp, Polynomial.derivative_add, Polynomial.derivative_one,
          Polynomial.derivative_X_pow]
  rw [hderiv] at hderiv_dvd
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def] at hderiv_dvd
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X] at hderiv_dvd
  have hi_pos : 0 < i := hi
  have hi_ne_nat : i ≠ 0 := Nat.pos_iff_ne_zero.mp hi_pos
  have hi_ne : (i : ℂ) ≠ 0 := by exact_mod_cast hi_ne_nat
  have hα_ne : α ≠ 0 := by
    intro hα0
    rw [hα0, zero_pow hi_ne_nat] at h
    exact absurd h (by norm_num)
  have hα_pow_ne : α ^ (i - 1) ≠ 0 := pow_ne_zero _ hα_ne
  rcases mul_eq_zero.mp hderiv_dvd with h1 | h2
  · exact hi_ne h1
  · exact hα_pow_ne h2

lemma rootMultiplicity_one_add_X_pow_complex_one_case
    (α : ℂ) (i : ℕ) (hi : 1 ≤ i) (h : α ^ i = -1) :
    Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + Polynomial.X ^ i) = 1 := by
  set p : Polynomial ℂ := (1 : Polynomial ℂ) + Polynomial.X ^ i with hp_def
  have hp_ne : p ≠ 0 := one_add_X_pow_ne_zero_complex i
  have hroot : p.IsRoot α := by
    show p.eval α = 0
    simp [hp_def, h]
  have h_ge : 1 ≤ Polynomial.rootMultiplicity α p :=
    (Polynomial.rootMultiplicity_pos hp_ne).mpr hroot
  have h_le : Polynomial.rootMultiplicity α p ≤ 1 :=
    rootMultiplicity_one_add_X_pow_complex_one_case_le α i hi h
  omega

lemma rootMultiplicity_one_add_X_pow_complex (α : ℂ) (i : ℕ) (hi : 1 ≤ i) :
    Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + Polynomial.X ^ i)
      = if α ^ i = -1 then 1 else 0 := by
  by_cases h : α ^ i = -1
  · rw [if_pos h]
    exact rootMultiplicity_one_add_X_pow_complex_one_case α i hi h
  · rw [if_neg h]
    exact rootMultiplicity_one_add_X_pow_complex_zero_case α i h

lemma map_one_add_X_pow (i : ℕ) :
    Polynomial.map (algebraMap ℚ ℂ) ((1 : Polynomial ℚ) + Polynomial.X ^ i)
      = ((1 : Polynomial ℂ) + Polynomial.X ^ i) := by
  simp [Polynomial.map_add, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]

lemma finset_sum_sub_distrib_of_le {ι : Type*} (S : Finset ι) (a b : ι → ℕ)
    (h : ∀ i ∈ S, b i ≤ a i) :
    (∑ i ∈ S, a i) - (∑ i ∈ S, b i) = ∑ i ∈ S, (a i - b i) := by
  classical
  induction' S using Finset.induction_on with i s his ih
  · simp
  · simp only [Finset.sum_insert his]
    have h1 : ∀ j ∈ s, b j ≤ a j := fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hi : b i ≤ a i := h i (Finset.mem_insert_self i s)
    have hsum : ∑ j ∈ s, b j ≤ ∑ j ∈ s, a j := Finset.sum_le_sum h1
    have ih' := ih h1
    omega

lemma rootMultiplicity_hSummand_aux {n : ℕ} (p : n.Partition) (α : ℂ) :
    Polynomial.rootMultiplicity α ((hSummand p).map (algebraMap ℚ ℂ)) =
      cC α n - cCount α n p := by
  have hmap :
      (hSummand p).map (algebraMap ℚ ℂ)
        = ∏ i ∈ Finset.Icc 1 n,
            ((1 : Polynomial ℂ) + Polynomial.X ^ i) ^ (n / i - p.mult i) := by
    unfold hSummand
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl ?_
    intro i _
    rw [Polynomial.map_pow, map_one_add_X_pow]
  rw [hmap]
  have hne : ∀ i ∈ Finset.Icc 1 n,
      (((1 : Polynomial ℂ) + Polynomial.X ^ i) ^ (n / i - p.mult i)) ≠ 0 := by
    intro i _
    exact pow_ne_zero _ (one_add_X_pow_ne_zero_complex i)
  rw [rootMultiplicity_prod_aux (Finset.Icc 1 n)
        (fun i => ((1 : Polynomial ℂ) + Polynomial.X ^ i) ^ (n / i - p.mult i)) α hne]
  have hstep :
      ∀ i ∈ Finset.Icc 1 n,
        Polynomial.rootMultiplicity α
            (((1 : Polynomial ℂ) + Polynomial.X ^ i) ^ (n / i - p.mult i))
          = (n / i - p.mult i)
              * (if α ^ i = -1 then 1 else 0) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    rw [rootMultiplicity_pow_aux _ _ _ (one_add_X_pow_ne_zero_complex i),
        rootMultiplicity_one_add_X_pow_complex α i hi1]
  rw [Finset.sum_congr rfl hstep]
  have hrestrict :
      (∑ i ∈ Finset.Icc 1 n,
          (n / i - p.mult i) * (if α ^ i = -1 then 1 else 0))
        = ∑ i ∈ badSet α n, (n / i - p.mult i) := by
    rw [badSet]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro i _
    split_ifs <;> simp
  rw [hrestrict]
  have hbound : ∀ i ∈ badSet α n, p.mult i ≤ n / i := by
    intro i _
    exact mult_le_div p i
  rw [show (∑ i ∈ badSet α n, (n / i - p.mult i))
        = (∑ i ∈ badSet α n, n / i) - (∑ i ∈ badSet α n, p.mult i) from
      (finset_sum_sub_distrib_of_le (badSet α n) (fun i => n / i) (fun i => p.mult i) hbound).symm]
  rfl

lemma s_le_of_pow_eq_neg_one {α : ℂ} {s : ℕ} (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    {j : ℕ} (hj : 1 ≤ j) (hpow : α ^ j = -1) : s ≤ j := by
  by_contra h
  have h₂ : 2 * j < 2 * s := by omega
  have h₃ : α ^ (2 * j) = 1 := by
    have : α ^ (2 * j) = (α ^ j) ^ 2 := by rw [mul_comm, pow_mul]
    rw [this, hpow]; norm_num
  have h₄ : 2 * j = 0 := hord.2 (2 * j) h₂ h₃
  omega

lemma cCount_le_M_general {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (p : n.Partition) :
    cCount α n p ≤ n / s := by
  rw [Nat.le_div_iff_mul_le hs]
  have h_badSet_subset : badSet α n ⊆ Finset.Icc 1 n := by
    intro j hj
    simp [badSet, Finset.mem_filter] at hj
    exact Finset.mem_Icc.mpr ⟨hj.1.1, hj.1.2⟩
  have h_s_le : ∀ j ∈ badSet α n, s ≤ j := by
    intro j hj
    simp [badSet, Finset.mem_filter, Finset.mem_Icc] at hj
    exact s_le_of_pow_eq_neg_one hs hord hj.1.1 hj.2
  calc cCount α n p * s
      = (∑ j ∈ badSet α n, p.mult j) * s := by rfl
    _ = ∑ j ∈ badSet α n, p.mult j * s := by rw [Finset.sum_mul]
    _ = ∑ j ∈ badSet α n, s * p.mult j := by
          apply Finset.sum_congr rfl; intros; ring
    _ ≤ ∑ j ∈ badSet α n, j * p.mult j := by
          apply Finset.sum_le_sum
          intro j hj
          exact Nat.mul_le_mul_right _ (h_s_le j hj)
    _ ≤ ∑ i ∈ Finset.Icc 1 n, i * p.mult i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg h_badSet_subset
          intros; exact Nat.zero_le _
    _ = n := sum_mult_eq_n p

lemma hSummand_map_dvd_pow {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (p : n.Partition) :
    ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s)) ∣
      (hSummand p).map (algebraMap ℚ ℂ) := by
  have h_ne_zero : (hSummand p).map (algebraMap ℚ ℂ) ≠ 0 := hSummand_map_ne_zero p
  have h_root_mul : Polynomial.rootMultiplicity α ((hSummand p).map (algebraMap ℚ ℂ)) =
      cC α n - cCount α n p := rootMultiplicity_hSummand_aux p α
  have h_count_le : cCount α n p ≤ n / s := cCount_le_M_general α s hs hord p
  have h_mul_bound : cC α n - n / s ≤
      Polynomial.rootMultiplicity α ((hSummand p).map (algebraMap ℚ ℂ)) := by
    rw [h_root_mul]
    exact Nat.sub_le_sub_left h_count_le _
  exact (Polynomial.le_rootMultiplicity_iff h_ne_zero).mp h_mul_bound

/-- **Helper:** Each mapped summand factors as `M * (h /ₘ M)` -/
lemma summand_eq_M_mul_div {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (p : n.Partition) :
    (hSummand p).map (algebraMap ℚ ℂ) =
      ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s)) *
        (((hSummand p).map (algebraMap ℚ ℂ)) /ₘ
          ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s))) := by
  set M : Polynomial ℂ := (Polynomial.X - Polynomial.C α) ^ (cC α n - n / s) with hM
  set h : Polynomial ℂ := (hSummand p).map (algebraMap ℚ ℂ) with hh
  have hMonic : M.Monic := (Polynomial.monic_X_sub_C α).pow _
  have hDvd : M ∣ h := hSummand_map_dvd_pow α s hs hord p
  have hModZero : h %ₘ M = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd hMonic).mpr hDvd
  have hAddDiv : h %ₘ M + M * (h /ₘ M) = h := Polynomial.modByMonic_add_div h hMonic
  rw [hModZero, zero_add] at hAddDiv
  exact hAddDiv.symm

/-- **Helper:** numStar n factors as M * (∑_p R_p). -/
lemma numStar_map_eq_M_mul_sum {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0) :
    (numStar n).map (algebraMap ℚ ℂ) =
      ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s)) *
        ∑ p : n.Partition,
          (((hSummand p).map (algebraMap ℚ ℂ)) /ₘ
            ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s))) := by
  have h1 : (numStar n).map (algebraMap ℚ ℂ) =
      ∑ p : n.Partition, (hSummand p).map (algebraMap ℚ ℂ) := by
    unfold numStar
    exact Polynomial.map_sum (algebraMap ℚ ℂ) (fun p => hSummand p) Finset.univ
  have h2 : ∑ p : n.Partition, (hSummand p).map (algebraMap ℚ ℂ) =
      ∑ p : n.Partition,
        ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s)) *
          (((hSummand p).map (algebraMap ℚ ℂ)) /ₘ
            ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s))) := by
    apply Finset.sum_congr rfl
    intro p _
    exact summand_eq_M_mul_div α s hs hord p
  rw [h1, h2, ← Finset.mul_sum]

/-- For every partition `p`, `cCount α n p ≤ n / s`. -/
lemma cCount_le_M_aux {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (p : n.Partition) :
    cCount α n p ≤ n / s :=
  cCount_le_M_general α s hs hord p

lemma pow_s_eq_neg_one {α : ℂ} {s : ℕ} (hs : 1 ≤ s)
    (h1 : α ^ (2 * s) = 1) (h2 : ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0) :
    α ^ s = -1 := by
  have hsq : (α ^ s) ^ 2 = 1 := by rw [← pow_mul, mul_comm]; exact h1
  rcases sq_eq_one_iff.mp hsq with h | h
  · exfalso
    have hs_lt : s < 2 * s := by omega
    have := h2 s hs_lt h
    omega
  · exact h

lemma n_div_s_le_cC {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hsn : s ≤ n) : n / s ≤ cC α n := by
  obtain ⟨h_pow, h_prim⟩ := hord
  have hαs : α ^ s = -1 := pow_s_eq_neg_one hs h_pow h_prim
  have hs_mem : s ∈ badSet α n := by
    unfold badSet
    rw [Finset.mem_filter]
    refine ⟨?_, hαs⟩
    rw [Finset.mem_Icc]
    exact ⟨hs, hsn⟩
  unfold cC
  exact Finset.single_le_sum (f := fun j => n / j) (fun i _ => Nat.zero_le _) hs_mem

/-- **Helper:** When `cCount α n p < n / s`, the evaluated quotient is zero. -/
lemma R_p_eval_zero_of_cCount_lt {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hsn : s ≤ n) (p : n.Partition) (hlt : cCount α n p < n / s) :
    Polynomial.eval α
      (((hSummand p).map (algebraMap ℚ ℂ)) /ₘ
        ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s))) = 0 := by
  set φ : ℚ →+* ℂ := algebraMap ℚ ℂ
  set h : Polynomial ℂ := (hSummand p).map φ with hh_def
  set k : ℕ := cC α n - n / s with hk_def
  set R_p : Polynomial ℂ := h /ₘ ((Polynomial.X - Polynomial.C α) ^ k) with hR_def
  have hrm : Polynomial.rootMultiplicity α h = cC α n - cCount α n p :=
    rootMultiplicity_hSummand_aux p α
  have hcC : n / s ≤ cC α n := n_div_s_le_cC α s hs hord hsn
  have hge : k + 1 ≤ cC α n - cCount α n p := by
    show cC α n - n / s + 1 ≤ cC α n - cCount α n p
    omega
  have hne : h ≠ 0 := hSummand_map_ne_zero p
  have hdvd : (Polynomial.X - Polynomial.C α) ^ (k + 1) ∣ h := by
    rw [← hrm] at hge
    exact (Polynomial.le_rootMultiplicity_iff hne).mp hge
  have hfact : h = ((Polynomial.X - Polynomial.C α) ^ k) * R_p :=
    summand_eq_M_mul_div α s hs hord p
  have hxc_ne : (Polynomial.X - Polynomial.C α) ^ k ≠ 0 :=
    pow_ne_zero k (Polynomial.X_sub_C_ne_zero α)
  have hpow_eq : (Polynomial.X - Polynomial.C α) ^ (k + 1) =
      (Polynomial.X - Polynomial.C α) ^ k * (Polynomial.X - Polynomial.C α) := by
    rw [pow_succ]
  rw [hpow_eq, hfact] at hdvd
  have hdvdR : (Polynomial.X - Polynomial.C α) ∣ R_p :=
    (mul_dvd_mul_iff_left hxc_ne).mp hdvd
  exact (Polynomial.dvd_iff_isRoot).mp hdvdR

/-- **Construction (Step 2.3 of `proof.md`):** Given μ ⊢ r (where r = n % s),
adjoin q = n/s copies of s to obtain a partition of n. The sum is r + q*s = n
since r < s and qs + r = n. -/
def bigPart {n : ℕ} (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n) (μ : (n % s).Partition) :
    n.Partition :=
  Nat.Partition.ofSums n (μ.parts + Multiset.replicate (n / s) s) (by
    rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
    have : μ.parts.sum = n % s := μ.parts_sum
    rw [this, mul_comm]
    exact Nat.mod_add_div n s)

/-- **Step 3.2 of proof.md:** The explicit nonzero constant K that appears as
common prefactor in R_{bigPart μ}.eval α for all μ ⊢ r.

Defined as: K := ∏_{i ∈ B\{s}} (i · α^(i-1))^(n/i) · ∏_{i ∉ B, i ∈ [1,n]} (1+α^i)^(n/i). -/
def Kconst {n : ℕ} (α : ℂ) (s : ℕ) : ℂ :=
  (∏ i ∈ (badSet α n).erase s, ((i : ℂ) * α ^ (i - 1)) ^ (n / i)) *
    (∏ i ∈ (Finset.Icc 1 n) \ (badSet α n), (1 + α ^ i) ^ (n / i))

lemma s_mem_badSet_1 {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0) :
    s ∈ badSet α n := by
  have h₁ : s ∈ Finset.Icc 1 n := by
    apply Finset.mem_Icc.mpr
    <;> simp_all
  have h₂ : α ^ s = -1 := by
    have h₃ : α ^ (2 * s) = 1 := hord.1
    have h₄ : ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0 := hord.2
    have h₅ : α ^ s ≠ 1 := by
      by_contra h₅
      have h₆ : s < 2 * s := by
        nlinarith
      have h₈ := h₄ s h₆ h₅
      linarith
    have h₆ : (α ^ s) ^ 2 = 1 := by
      calc
        (α ^ s) ^ 2 = α ^ (2 * s) := by
          rw [pow_mul]
          <;> ring_nf
        _ = 1 := h₃
    have h₇ : α ^ s = -1 := by
      have h₈ : α ^ s = 1 ∨ α ^ s = -1 := by
        apply or_iff_not_imp_left.mpr
        intro h₈
        apply eq_of_sub_eq_zero
        apply mul_left_cancel₀ (sub_ne_zero.mpr h₈)
        rw [← sub_eq_zero]
        ring_nf at h₆ ⊢
        simp_all [Complex.ext_iff, pow_two]
      cases h₈ with
      | inl h₈ =>
        exfalso
        exact h₅ h₈
      | inr h₈ =>
        exact h₈
    exact h₇
  have h₃ : s ∈ badSet α n := by
    rw [badSet]
    apply Finset.mem_filter.mpr
    exact ⟨h₁, h₂⟩
  exact h₃

/-- **Step 3.1 of `proof.md`:** Explicit formula for the multiplicity of any nonzero `j` in
`bigPart s hs hsn μ`. The parts of the partition equal the underlying multiset (filtering by
≠ 0 is the identity because all parts are positive). Hence for `j ≠ 0`,
  `(bigPart s hs hsn μ).mult j = μ.mult j + (if s = j then n/s else 0)`.

This uses `Nat.Partition.count_ofSums_of_ne_zero`, `Multiset.count_add`, and
`Multiset.count_replicate`. -/
lemma bigPart_mult_eq {n : ℕ} (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (μ : (n % s).Partition) {j : ℕ} (hj : j ≠ 0) :
    (bigPart s hs hsn μ).mult j =
      μ.mult j + (if s = j then n / s else 0) := by
  have h₁ : (bigPart s hs hsn μ).mult j = Multiset.count j (μ.parts + Multiset.replicate (n / s) s) := by
    simp [bigPart, Nat.Partition.mult, Nat.Partition.ofSums_parts]
    <;>
    (try simp_all [hj])
  rw [h₁]
  have h₂ : Multiset.count j (μ.parts + Multiset.replicate (n / s) s) = Multiset.count j μ.parts + Multiset.count j (Multiset.replicate (n / s) s) := by
    apply Multiset.count_add
  rw [h₂]
  have h₃ : Multiset.count j (Multiset.replicate (n / s) s) = if s = j then n / s else 0 := by
    by_cases h : s = j
    · -- Case: s = j
      rw [h]
      <;> simp [Multiset.count_replicate]
    · -- Case: s ≠ j
      rw [if_neg h]
      simp [Multiset.count_replicate, h]
  rw [h₃]
  have h₄ : μ.mult j = Multiset.count j μ.parts := by
    simp [Nat.Partition.mult]
  rw [h₄]

/-- **Helper for Step 2 of `proof.md`:** For `μ : (n % s).Partition` with `s > 0`,
the multiplicity of `s` in `μ.parts` is `0`. This is because every part of `μ` is `≤ n % s < s`,
so `s` cannot appear among them.

Uses `Nat.Partition.le_of_mem_parts : ∀ {n : ℕ} (i : ℕ) {p : n.Partition}, i ∈ p.parts → i ≤ n`,
`Nat.mod_lt : ∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y`, and
`Multiset.count_eq_zero_of_notMem : ∀ {α : Type u_1} [inst : DecidableEq α] {a : α} {s : Multiset α}, a ∉ s → Multiset.count a s = 0`. -/
lemma mu_mult_s_eq_zero {n : ℕ} (s : ℕ) (hs : 1 ≤ s) (μ : (n % s).Partition) :
    μ.mult s = 0 := by
  -- Step 1: n % s < s
  have hmod : n % s < s := Nat.mod_lt n hs
  -- Step 2-4: s is not in μ.parts since every part is ≤ n % s < s
  have hnotmem : s ∉ μ.parts := by
    intro hmem
    have hle : s ≤ n % s := μ.le_of_mem_parts hmem
    exact absurd (lt_of_le_of_lt hle hmod) (lt_irrefl s)
  -- Step 5-6: Multiset.count = 0
  exact Multiset.count_eq_zero_of_notMem hnotmem

/-- **Step 3.4 of `proof.md`:** Multiplicity of `s` in `bigPart s hs hsn μ` equals `n/s`. -/
lemma bigPart_mult_s {n : ℕ} (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (μ : (n % s).Partition) :
    (bigPart s hs hsn μ).mult s = n / s := by
  have hs0 : s ≠ 0 := Nat.one_le_iff_ne_zero.mp hs
  -- Apply bigPart_mult_eq with j = s
  rw [bigPart_mult_eq s hs hsn μ hs0]
  -- The if-then-else simplifies: s = s is true, so we get μ.mult s + n/s
  simp only [if_true]
  -- μ.mult s = 0 by mu_mult_s_eq_zero
  rw [mu_mult_s_eq_zero s hs μ]
  -- 0 + n/s = n/s
  exact Nat.zero_add _

lemma mult_eq_zero_of_lt {m : ℕ} (μ : m.Partition) {j : ℕ} (hjm : m < j) :
    μ.mult j = 0 := by
  have h₁ : Multiset.count j μ.parts = 0 := by
    grind only [Multiset.count_eq_zero, → Nat.Partition.le_of_mem_parts]
  have h₂ : μ.mult j = 0 := by assumption
  grind

/-- **Step 3.3 of `proof.md`:** For `j ∈ badSet α n` with `j ≠ s`, the multiplicity of `j` in
`bigPart s hs hsn μ` is `0`.

Proof outline: by `s_le_of_pow_eq_neg_one`, `j ≥ s`, and `j ≠ s` gives `j > s`. Then
`bigPart_mult_eq` gives `μ.mult j + (if s = j then n/s else 0) = μ.mult j` (since `s ≠ j`).
But `μ.mult j = 0` because all parts of `μ` are `≤ n % s < s < j`. -/
lemma bigPart_mult_of_ne_s {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (μ : (n % s).Partition) {j : ℕ} (hjB : j ∈ badSet α n) (hjs : j ≠ s) :
    (bigPart s hs hsn μ).mult j = 0 := by
  -- Extract that j ∈ [1, n] and α^j = -1 from the bad set membership.
  rw [badSet, Finset.mem_filter, Finset.mem_Icc] at hjB
  obtain ⟨⟨hj1, _hjn⟩, hpow⟩ := hjB
  -- Hence j ≠ 0.
  have hj_ne_zero : j ≠ 0 := Nat.one_le_iff_ne_zero.mp hj1
  -- Step 1: apply the bigPart_mult_eq formula.
  rw [bigPart_mult_eq s hs hsn μ hj_ne_zero]
  -- Step 2: simplify the `if` branch using `s ≠ j`.
  rw [if_neg (Ne.symm hjs)]
  -- Now the goal is `μ.mult j + 0 = 0`, i.e. `μ.mult j = 0`.
  simp only [Nat.add_zero]
  -- Step 3: From the bad set, s ≤ j; combined with j ≠ s, get s < j.
  have hsj : s ≤ j := s_le_of_pow_eq_neg_one hs hord hj1 hpow
  have hs_lt_j : s < j := lt_of_le_of_ne hsj (Ne.symm hjs)
  -- Step 4: n % s < s by Nat.mod_lt, since 1 ≤ s.
  have hmod : n % s < s := Nat.mod_lt n hs
  -- Step 5: hence n % s < j.
  have hmod_lt_j : n % s < j := lt_trans hmod hs_lt_j
  -- Step 6: apply mult_eq_zero_of_lt to μ.
  exact mult_eq_zero_of_lt μ hmod_lt_j

/-- **Step 2 of proof.md:** For α primitive 2s-th root of unity and μ ⊢ r,
the constructed partition bigPart μ has cCount equal to q = n/s. -/
lemma cCount_bigPart {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (μ : (n % s).Partition) :
    cCount α n (bigPart s hs hsn μ) = n / s := by
  -- Step 4.1: decompose B as {s} ⊔ (B \ {s}) since s ∈ B
  have hsB : s ∈ badSet α n := s_mem_badSet_1 α s hs hsn hord
  -- Rewrite the sum over B = badSet α n by extracting the term j = s
  unfold cCount
  rw [← Finset.add_sum_erase _ _ hsB]
  -- Now: (bigPart ...).mult s + ∑ j ∈ (badSet α n).erase s, (bigPart ...).mult j = n/s
  -- Step 3.4: (bigPart ...).mult s = n/s
  rw [bigPart_mult_s s hs hsn μ]
  -- Step 4.2: the remaining sum is zero
  have htail : ∑ j ∈ (badSet α n).erase s, (bigPart s hs hsn μ).mult j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_erase] at hj
    obtain ⟨hjs, hjB⟩ := hj
    exact bigPart_mult_of_ne_s α s hs hsn hord μ hjB hjs
  rw [htail, Nat.add_zero]

/-- **Step 2 of proof.md (injectivity):** Different μ produce different partitions.
The multiplicity of any i < s in bigPart μ recovers μ.mult i, so μ can be
recovered from bigPart μ. -/
lemma bigPart_injective {n : ℕ} (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n) :
    Function.Injective (bigPart (n := n) s hs hsn) := by
  intro μ₁ μ₂ hEq
  -- Use that parts of bigPart μ = μ.parts + replicate (n/s) s after filtering nonzeros.
  -- Apply count i to both sides for arbitrary i ≠ 0 (or i = 0, where μ.parts has count 0).
  apply Nat.Partition.ext
  -- Show μ₁.parts = μ₂.parts via Multiset.ext (counts agree).
  apply Multiset.ext.mpr
  intro i
  -- From hEq we get equality of parts of bigPart.
  have hP : (bigPart s hs hsn μ₁).parts = (bigPart s hs hsn μ₂).parts := by
    rw [hEq]
  -- Case split on i = 0 or i ≠ 0.
  by_cases hi : i = 0
  · -- Parts of any partition contain no zeros.
    subst hi
    have h1 : Multiset.count 0 μ₁.parts = 0 := by
      rw [Multiset.count_eq_zero]
      intro h
      exact (μ₁.parts_pos h).ne' rfl
    have h2 : Multiset.count 0 μ₂.parts = 0 := by
      rw [Multiset.count_eq_zero]
      intro h
      exact (μ₂.parts_pos h).ne' rfl
    rw [h1, h2]
  · -- For i ≠ 0, use count_ofSums_of_ne_zero on each side and cancel.
    have hSum1 : (μ₁.parts + Multiset.replicate (n / s) s).sum = n := by
      rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
      have : μ₁.parts.sum = n % s := μ₁.parts_sum
      rw [this, mul_comm]
      exact Nat.mod_add_div n s
    have hSum2 : (μ₂.parts + Multiset.replicate (n / s) s).sum = n := by
      rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
      have : μ₂.parts.sum = n % s := μ₂.parts_sum
      rw [this, mul_comm]
      exact Nat.mod_add_div n s
    -- Unfold bigPart in hP.
    have h1 : Multiset.count i (bigPart s hs hsn μ₁).parts =
        Multiset.count i (μ₁.parts + Multiset.replicate (n / s) s) := by
      unfold bigPart
      exact Nat.Partition.count_ofSums_of_ne_zero hSum1 hi
    have h2 : Multiset.count i (bigPart s hs hsn μ₂).parts =
        Multiset.count i (μ₂.parts + Multiset.replicate (n / s) s) := by
      unfold bigPart
      exact Nat.Partition.count_ofSums_of_ne_zero hSum2 hi
    -- Combine: count i in both expanded sums equal.
    have hEqCount : Multiset.count i (μ₁.parts + Multiset.replicate (n / s) s) =
        Multiset.count i (μ₂.parts + Multiset.replicate (n / s) s) := by
      rw [← h1, ← h2, hP]
    -- Expand count_add and cancel.
    rw [Multiset.count_add, Multiset.count_add] at hEqCount
    exact Nat.add_right_cancel hEqCount

/-- For `α` of exact order `2s` and `j : ℕ`, we have `α^j = -1 ↔ j ≡ s (mod 2s)`. -/
lemma pow_eq_neg_one_iff_aux_1 {α : ℂ} {s : ℕ} (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (j : ℕ) :
    α ^ j = -1 ↔ j % (2 * s) = s := by
  obtain ⟨hpow, hmin⟩ := hord
  have hs_lt : s < 2 * s := by omega
  have h2s_pos : 0 < 2 * s := by omega
  -- Step 1: α^s = -1
  have hαs : α ^ s = -1 := by
    have hsq : (α ^ s) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm]; exact hpow
    rcases sq_eq_one_iff.mp hsq with h1 | hn1
    · exfalso; have := hmin s hs_lt h1; omega
    · exact hn1
  -- Step 2: characterize α^k = 1
  have hchar1 : ∀ k : ℕ, α ^ k = 1 ↔ 2 * s ∣ k := by
    intro k
    constructor
    · intro hk
      -- Euclidean division: k = (2s)*q + r with r < 2s
      have hkeq : k = 2 * s * (k / (2 * s)) + k % (2 * s) := (Nat.div_add_mod k (2 * s)).symm
      have hr_lt : k % (2 * s) < 2 * s := Nat.mod_lt k h2s_pos
      have hαr : α ^ (k % (2 * s)) = 1 := by
        have : α ^ k = α ^ (2 * s * (k / (2 * s))) * α ^ (k % (2 * s)) := by
          rw [← pow_add, ← hkeq]
        rw [this, pow_mul, hpow, one_pow, one_mul] at hk
        exact hk
      have hr0 : k % (2 * s) = 0 := hmin _ hr_lt hαr
      exact Nat.dvd_of_mod_eq_zero hr0
    · rintro ⟨q, rfl⟩
      rw [pow_mul, hpow, one_pow]
  constructor
  · -- Reverse direction: α^j = -1 → j % (2s) = s
    intro hj
    -- Use Euclidean division
    set r := j % (2 * s) with hr_def
    set q := j / (2 * s) with hq_def
    have hjeq : j = 2 * s * q + r := by rw [hq_def, hr_def]; exact (Nat.div_add_mod j (2*s)).symm
    have hr_lt : r < 2 * s := Nat.mod_lt j h2s_pos
    have hαr : α ^ r = -1 := by
      have : α ^ j = α ^ (2 * s * q) * α ^ r := by rw [← pow_add, ← hjeq]
      rw [this, pow_mul, hpow, one_pow, one_mul] at hj
      exact hj
    -- (α^r)^2 = 1, so α^(2r) = 1, so 2s ∣ 2r
    have h2r : α ^ (2 * r) = 1 := by
      rw [mul_comm 2 r, pow_mul, hαr]; ring
    have hdvd : 2 * s ∣ 2 * r := (hchar1 (2 * r)).mp h2r
    -- From r < 2s and 2s ∣ 2r, get 2r < 4s, so 2r = 0 or 2r = 2s, i.e., r = 0 or r = s
    obtain ⟨m, hm⟩ := hdvd
    have h2r_lt : 2 * r < 4 * s := by omega
    have hm_lt : m < 2 := by
      by_contra h
      push_neg at h
      have : 2 * s * 2 ≤ 2 * s * m := Nat.mul_le_mul_left _ h
      omega
    interval_cases m
    · -- m = 0: 2r = 0, so r = 0, then α^r = 1 ≠ -1
      have hr0 : r = 0 := by omega
      rw [hr0, pow_zero] at hαr
      exfalso
      have : (1 : ℂ) ≠ -1 := by norm_num
      exact this hαr
    · -- m = 1: 2r = 2s, so r = s
      omega
  · -- Forward direction: j % (2s) = s → α^j = -1
    intro hjs
    have hjeq : j = 2 * s * (j / (2 * s)) + s := by
      have := (Nat.div_add_mod j (2 * s)).symm
      rw [hjs] at this; exact this
    calc α ^ j = α ^ (2 * s * (j / (2 * s)) + s) := by rw [← hjeq]
      _ = α ^ (2 * s * (j / (2 * s))) * α ^ s := by rw [pow_add]
      _ = (α ^ (2 * s)) ^ (j / (2 * s)) * α ^ s := by rw [pow_mul]
      _ = 1 * (-1) := by rw [hpow, one_pow, hαs]
      _ = -1 := by ring

/-- **Step 2.3.2:** For `j ∈ badSet α n` with `j ≠ s`, we have `j ≥ 3*s`.
This follows from `pow_eq_neg_one_iff_aux`: j ≡ s (mod 2s), so j = s + 2s*k for some
k ≥ 0; with j ≠ s we have k ≥ 1, so j ≥ s + 2s = 3s. -/
lemma three_s_le_of_mem_badSet_ne_s {n : ℕ} (α : ℂ) {s : ℕ} (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    {j : ℕ} (hj : j ∈ badSet α n) (hne : j ≠ s) : 3 * s ≤ j := by
  -- Extract α^j = -1 from membership in badSet.
  have hαj : α ^ j = -1 := by
    unfold badSet at hj
    rw [Finset.mem_filter] at hj
    exact hj.2
  -- Convert to modular condition: j % (2*s) = s.
  have hmod : j % (2 * s) = s := (pow_eq_neg_one_iff_aux_1 hs hord j).mp hαj
  -- Inline arithmetic step (no extra helper lemma needed).
  -- Decompose j = (2*s) * (j / (2*s)) + j % (2*s).
  have hdivmod : j = (2 * s) * (j / (2 * s)) + j % (2 * s) :=
    (Nat.div_add_mod j (2 * s)).symm
  rw [hmod] at hdivmod
  -- hdivmod : j = 2*s * (j / (2*s)) + s
  rcases Nat.eq_zero_or_pos (j / (2 * s)) with hq | hq
  · -- If the quotient is 0, then j = s, contradicting `hne`.
    rw [hq] at hdivmod
    simp at hdivmod
    exact absurd hdivmod hne
  · -- Otherwise the quotient is ≥ 1, so 2*s * (j/(2*s)) ≥ 2*s, hence j ≥ 2*s + s = 3*s.
    have hmul : 2 * s * 1 ≤ 2 * s * (j / (2 * s)) := Nat.mul_le_mul_left _ hq
    linarith

/-- **Auxiliary lemma:** `badSet α n` is a subset of `Finset.Icc 1 n`. -/
lemma badSet_subset_Icc (α : ℂ) (n : ℕ) : badSet α n ⊆ Finset.Icc 1 n := by
  intro j hj
  exact (Finset.mem_filter.mp hj).1

/-- **Step 4 of proof.md:** Given hypotheses on `α`, `s`, `p`, we have
`n ≥ s * p.mult s + 3 * s * T`. -/
lemma n_ge_lower_bound {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (p : n.Partition) :
    s * p.mult s + 3 * s * (∑ j ∈ (badSet α n).erase s, p.mult j) ≤ n := by
  have h1 : ∑ i ∈ Finset.Icc 1 n, i * p.mult i = n := sum_mult_eq_n p
  have hsub : badSet α n ⊆ Finset.Icc 1 n := badSet_subset_Icc α n
  have h2 : ∑ i ∈ badSet α n, i * p.mult i ≤ ∑ i ∈ Finset.Icc 1 n, i * p.mult i :=
    Finset.sum_le_sum_of_subset hsub
  have hs_mem : s ∈ badSet α n := s_mem_badSet_1 α s hs hsn hord
  have h4 : s * p.mult s + ∑ j ∈ (badSet α n).erase s, j * p.mult j
      = ∑ i ∈ badSet α n, i * p.mult i := by
    have := Finset.add_sum_erase (badSet α n) (fun i => i * p.mult i) hs_mem
    linarith [this]
  have h5 : ∀ j ∈ (badSet α n).erase s, 3 * s * p.mult j ≤ j * p.mult j := by
    intro j hj
    rw [Finset.mem_erase] at hj
    have hjb : j ∈ badSet α n := hj.2
    have hjne : j ≠ s := hj.1
    have h3s : 3 * s ≤ j := three_s_le_of_mem_badSet_ne_s α hs hord hjb hjne
    exact Nat.mul_le_mul_right _ h3s
  have h6 : 3 * s * (∑ j ∈ (badSet α n).erase s, p.mult j)
      ≤ ∑ j ∈ (badSet α n).erase s, j * p.mult j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum h5
  linarith [h1, h2, h4, h6]

/-- Splitting the `cCount` sum at `s`. -/
lemma cCount_split {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (p : n.Partition) :
    cCount α n p = p.mult s + ∑ j ∈ (badSet α n).erase s, p.mult j := by
  have h₁ : s ∈ badSet α n := s_mem_badSet_1 α s hs hsn hord
  have h₂ : ∑ j ∈ badSet α n, p.mult j = p.mult s + ∑ j ∈ (badSet α n).erase s, p.mult j := by
    have h₃ : ∑ j ∈ badSet α n, p.mult j = ∑ j ∈ (badSet α n).erase s, p.mult j + p.mult s := by
      rw [← Finset.sum_erase_add _ _ h₁]
    linarith
  simp only [cCount] at *
  rw [h₂]

lemma arith_T_eq_zero (n s a T : ℕ) (hs : 1 ≤ s) (hsum : a + T = n / s)
    (hbound : s * a + 3 * s * T ≤ n) : T = 0 := by
  have h₁ : n / s = a + T := by omega
  have h₃ : n < s * (a + T + 1) := by
    have h₅ : n = s * (n / s) + n % s := by
      have h₅₁ : s * (n / s) + n % s = n := by
        have h₅₂ := Nat.div_add_mod n s
        linarith
      linarith
    have h₆ : n % s < s := Nat.mod_lt n hs
    have h₇ : n / s = a + T := by omega
    have h₈ : s * (n / s) = s * (a + T) := by
      rw [h₇]
    have h₁₁ : s * (a + T) + n % s < s * (a + T) + s := by
      omega
    have h₁₂ : s * (a + T) + s = s * (a + T + 1) := by
      ring
    omega
  have h₈ : 3 * T < T + 1 := by
    by_contra h
    have h₈₃ : T + 1 ≤ 3 * T := by omega
    have h₈₄ : s * (T + 1) ≤ s * (3 * T) := by
      exact Nat.mul_le_mul_left s h₈₃
    nlinarith
  by_contra h
  have h₉₁ : T ≥ 1 := by omega
  omega

/-- **Key arithmetic step.** -/
lemma sum_erase_eq_zero {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (p : n.Partition) (hcc : cCount α n p = n / s) :
    ∑ j ∈ (badSet α n).erase s, p.mult j = 0 := by
  have hsplit : p.mult s + ∑ j ∈ (badSet α n).erase s, p.mult j = n / s := by
    rw [← cCount_split α s hs hsn hord p]; exact hcc
  have hbnd : s * p.mult s + 3 * s * (∑ j ∈ (badSet α n).erase s, p.mult j) ≤ n :=
    n_ge_lower_bound α s hs hsn hord p
  exact arith_T_eq_zero n s (p.mult s) (∑ j ∈ (badSet α n).erase s, p.mult j)
    hs hsplit hbnd

/-- **Step 3 of proof.md (key combinatorial bound):** Under the hypotheses, every part
`j ∈ badSet α n` with `j ≠ s` has multiplicity 0 in `p`, and the multiplicity of `s` is `n/s`. -/
lemma mult_s_eq_and_mult_other_eq_zero {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (p : n.Partition) (hcc : cCount α n p = n / s) :
    p.mult s = n / s ∧ ∀ j ∈ badSet α n, j ≠ s → p.mult j = 0 := by
  -- s ∈ badSet α n
  have hsB : s ∈ badSet α n := s_mem_badSet_1 α s hs hsn hord
  -- T := sum over (badSet.erase s) of mult equals 0
  have hT : ∑ j ∈ (badSet α n).erase s, p.mult j = 0 :=
    sum_erase_eq_zero α s hs hsn hord p hcc
  -- Split cCount: cCount = p.mult s + ∑ over (badSet.erase s) p.mult j
  have hsum_split : cCount α n p = p.mult s + ∑ j ∈ (badSet α n).erase s, p.mult j := by
    unfold cCount
    exact (Finset.add_sum_erase _ _ hsB).symm
  -- So p.mult s = n / s
  have hms : p.mult s = n / s := by
    have := hsum_split
    rw [hT, Nat.add_zero] at this
    rw [← this, hcc]
  refine ⟨hms, ?_⟩
  -- For j ∈ badSet, j ≠ s, get mult j = 0 from hT
  intro j hjB hjne
  -- Use sum-eq-zero to conclude each term is zero
  have hjE : j ∈ (badSet α n).erase s := Finset.mem_erase.mpr ⟨hjne, hjB⟩
  have := (Finset.sum_eq_zero_iff_of_nonneg
            (s := (badSet α n).erase s)
            (f := fun j => p.mult j)
            (fun i _ => Nat.zero_le _)).mp hT j hjE
  exact this

/-- **First main goal:** Under the conditions, `replicate (n/s) s ≤ p.parts`.
Uses `Multiset.le_iff_count`: for `a = s`, count on left is `n/s` and count on right
is `p.mult s = n/s`; for `a ≠ s`, count on left is 0. -/
lemma replicate_le_parts_aux {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (p : n.Partition) (hcc : cCount α n p = n / s) :
    Multiset.replicate (n / s) s ≤ p.parts := by
  have ⟨hmult_s, _⟩ := mult_s_eq_and_mult_other_eq_zero α s hs hsn hord p hcc
  rw [Multiset.le_iff_count]
  intro a
  by_cases ha : a = s
  · subst ha
    rw [Multiset.count_replicate_self]
    exact hmult_s.ge
  · rw [Multiset.count_replicate]
    simp [Ne.symm ha]

lemma sub_sum_eq_aux {n : ℕ} (s : ℕ) (hs : 1 ≤ s) (p : n.Partition)
    (hle : Multiset.replicate (n / s) s ≤ p.parts) :
    (p.parts - Multiset.replicate (n / s) s).sum = n % s := by
  have h₁ : (Multiset.replicate (n / s) s).sum = (n / s) * s := by
    simp [Multiset.sum_replicate, smul_eq_mul]
  have h₂ : (Multiset.replicate (n / s) s) + (p.parts - Multiset.replicate (n / s) s) = p.parts := by
    simp [add_tsub_cancel_of_le, hle]
  have h₃ : (Multiset.replicate (n / s) s).sum + (p.parts - Multiset.replicate (n / s) s).sum = p.parts.sum := by grind
  have h₄ : p.parts.sum = n := by grind only [Nat.Partition.parts_sum]
  have h₆ : (p.parts - Multiset.replicate (n / s) s).sum = n - (n / s) * s := by grind
  have h₇ : n - (n / s) * s = n % s := Eq.symm Nat.mod_eq_sub_div_mul
  grind

/-- **Main technical lemma (Step 6 of proof.md):**
Given hypotheses of the theorem, the multiplicity of `s` in `p.parts` is exactly `n/s`,
and `replicate (n/s) s ≤ p.parts` and `p.parts - replicate (n/s) s` has sum `n % s`. -/
lemma replicate_le_parts_and_sub_sum {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (p : n.Partition) (hcc : cCount α n p = n / s) :
    Multiset.replicate (n / s) s ≤ p.parts ∧
    (p.parts - Multiset.replicate (n / s) s).sum = n % s := by
  have hle := replicate_le_parts_aux α s hs hsn hord p hcc
  refine ⟨hle, ?_⟩
  exact sub_sum_eq_aux s hs p hle

/-- **Main theorem.** Given α primitive 2s-th root of unity (1 ≤ s ≤ n) and
p ⊢ n with cCount α n p = n/s, there is μ ⊢ (n%s) with bigPart s hs hsn μ = p. -/
lemma bigPart_surjective_onto_filter {n : ℕ} (α : ℂ) (s : ℕ)
    (hs : 1 ≤ s) (hsn : s ≤ n)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (p : n.Partition) (hcc : cCount α n p = n / s) :
    ∃ μ : (n % s).Partition, bigPart s hs hsn μ = p := by
  obtain ⟨hle, hsum⟩ := replicate_le_parts_and_sub_sum α s hs hsn hord p hcc
  set M : Multiset ℕ := p.parts - Multiset.replicate (n / s) s with hM
  refine ⟨Nat.Partition.ofSums (n % s) M hsum, ?_⟩
  -- Show the partitions are equal by extensionality on parts.
  apply Nat.Partition.ext
  -- Unfold bigPart definition: bigPart's parts = filter (≠0) (μ.parts + replicate (n/s) s)
  show (Nat.Partition.ofSums n
    ((Nat.Partition.ofSums (n % s) M hsum).parts + Multiset.replicate (n / s) s) _).parts =
    p.parts
  rw [Nat.Partition.ofSums_parts]
  -- The parts of ofSums (n%s) M hsum equal filter (≠0) M.
  rw [Nat.Partition.ofSums_parts]
  -- Now we need: filter (≠0) (filter (≠0) M + replicate (n/s) s) = p.parts
  -- Since p.parts has no zeros (parts_pos), and replicate (n/s) s has no zeros (s ≥ 1),
  -- and M ⊆ p.parts has no zeros, the filters are no-ops.
  have hM_no_zero : ∀ a ∈ M, a ≠ 0 := by
    intro a ha
    have : a ∈ p.parts := Multiset.mem_of_le (by simp [hM]) ha
    exact Nat.pos_iff_ne_zero.mp (p.parts_pos this)
  have hrep_no_zero : ∀ a ∈ Multiset.replicate (n / s) s, a ≠ 0 := by
    intro a ha
    rw [Multiset.mem_replicate] at ha
    rcases ha with ⟨_, rfl⟩
    exact Nat.pos_iff_ne_zero.mp hs
  have hfM : Multiset.filter (fun x => x ≠ 0) M = M :=
    Multiset.filter_eq_self.mpr hM_no_zero
  rw [hfM]
  -- Now: filter (≠0) (M + replicate (n/s) s) = p.parts
  have hM_add : M + Multiset.replicate (n / s) s = p.parts := by
    rw [hM, tsub_add_cancel_of_le hle]
  rw [hM_add]
  apply Multiset.filter_eq_self.mpr
  intro a ha
  exact Nat.pos_iff_ne_zero.mp (p.parts_pos ha)

/-- `α` is nonzero: if α^(2s) = 1 with 1 ≤ s then α ≠ 0 (else 0^(2s) = 0 ≠ 1). -/
lemma alpha_ne_zero_of_hord {s : ℕ} (α : ℂ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0) :
    α ≠ 0 := by
  intro hzero
  have hpos : 0 < 2 * s := by omega
  have h1 : α ^ (2 * s) = 1 := hord.1
  rw [hzero, zero_pow hpos.ne'] at h1
  exact zero_ne_one h1

/-- **Step 2 of proof.md:** For `i ∈ (badSet α n).erase s`, we have `i ≥ 1`
(hence `(i : ℂ) ≠ 0`) and `α^(i-1) ≠ 0` (since α ≠ 0), so the base
`(i : ℂ) * α^(i-1)` is nonzero. The full power factor `((i : ℂ) * α^(i-1)) ^ (n / i)`
is nonzero by `pow_ne_zero`. -/
lemma first_factor_ne_zero {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    {i : ℕ} (hi : i ∈ (badSet α n).erase s) :
    ((i : ℂ) * α ^ (i - 1)) ^ (n / i) ≠ 0 := by
  -- Step 1: extract i ∈ badSet α n
  have hi' : i ∈ badSet α n := Finset.mem_of_mem_erase hi
  -- Unfold badSet to get i ∈ Icc 1 n
  have hi_mem : i ∈ Finset.Icc 1 n := by
    have := (Finset.mem_filter.mp hi').1
    exact this
  -- Extract 1 ≤ i
  have hi_low : 1 ≤ i := (Finset.mem_Icc.mp hi_mem).1
  -- Step 2: (i : ℂ) ≠ 0
  have hi_ne : (i : ℂ) ≠ 0 := by
    have hi_pos : 0 < i := hi_low
    exact_mod_cast Nat.pos_iff_ne_zero.mp hi_pos
  -- Step 3: α ≠ 0
  have hα : α ≠ 0 := alpha_ne_zero_of_hord α hs hord
  -- Step 4: α^(i-1) ≠ 0
  have hαp : α ^ (i - 1) ≠ 0 := pow_ne_zero _ hα
  -- Step 5: product ≠ 0
  have hbase : (i : ℂ) * α ^ (i - 1) ≠ 0 := mul_ne_zero hi_ne hαp
  -- Step 6: full power ≠ 0
  exact pow_ne_zero _ hbase

/-- **Step 3 of proof.md:** For `i ∈ Finset.Icc 1 n \ badSet α n`, we have `α^i ≠ -1`,
so `1 + α^i ≠ 0` (since `1 + α^i = 0 ↔ α^i = -1`). The full power factor
`(1 + α^i) ^ (n / i)` is nonzero by `pow_ne_zero`. -/
lemma second_factor_ne_zero {n : ℕ} (α : ℂ)
    {i : ℕ} (hi : i ∈ (Finset.Icc 1 n) \ (badSet α n)) :
    ((1 : ℂ) + α ^ i) ^ (n / i) ≠ 0 := by
  rw [Finset.mem_sdiff] at hi
  obtain ⟨hi_mem, hi_not⟩ := hi
  simp only [badSet, Finset.mem_filter, not_and] at hi_not
  have hαi : α ^ i ≠ -1 := hi_not hi_mem
  apply pow_ne_zero
  intro h
  apply hαi
  linear_combination h

/-- **Step 3.2 of proof.md:** Kconst is nonzero. Each factor is nonzero:
- For i ∈ B \ {s}: i ≠ 0 (since i ≥ 1) and α ≠ 0 (since α is a root of unity).
- For i ∉ B: 1 + α^i ≠ 0 by definition of B.

The hypothesis `hsn : s ≤ n` is part of the contract but not directly used in this proof;
the strategy is purely factor-by-factor nonzero-ness. -/
lemma Kconst_ne_zero {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0) :
    Kconst α s (n := n) ≠ 0 := by
  unfold Kconst
  apply mul_ne_zero
  · rw [Finset.prod_ne_zero_iff]
    intro i hi
    exact first_factor_ne_zero α s hs hord hi
  · rw [Finset.prod_ne_zero_iff]
    intro i hi
    exact second_factor_ne_zero α hi

/-- **Helper Q (Steps 5–7 of proof.md):** The explicit polynomial that arises after
factoring out `(X - C α)^k` from `(hSummand (bigPart s hs hsn μ)).map φ`.

`Q(X) := (∏_{i ∈ B \ {s}} g_i(X)^{⌊n/i⌋}) · (∏_{i ∉ B, i ∈ [1,n]} (1 + X^i)^{e_i})`
where `g_i(X) = X^{i-1} + α·X^{i-2} + ⋯ + α^{i-1}` is the "cofactor" of `(X-α)` in
`X^i + 1`, and `e_i = n/i - m_p(i)` is the exponent in `hSummand`.

We use a closed-form: `g_i(X) = (X^i + 1) /ₘ (X - C α)` is monic of degree `i-1`. -/
def quotientPoly {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (μ : (n % s).Partition) : Polynomial ℂ :=
  (∏ i ∈ (badSet α n).erase s,
      (((Polynomial.X ^ i + 1) /ₘ (Polynomial.X - Polynomial.C α)) ^ (n / i))) *
    (∏ i ∈ (Finset.Icc 1 n) \ (badSet α n),
      ((1 + Polynomial.X ^ i) ^ (n / i - (bigPart s hs hsn μ).mult i)))

/-- **Step 6.3 of proof.md:** The factorization
`F_p = (X - C α)^k * Q_μ` for `p = bigPart s hs hsn μ`.

Proof outline (uses `bigPart_mult_s`, `bigPart_mult_of_ne_s`, `bigPart_mult_eq`,
and `s_mem_badSet`):
- For each `i ∈ B = badSet α n`, write `1 + X^i = (X - α) · g_i(X)` over ℂ
  (true since `α^i = -1`, so `α` is a root of `1 + X^i`).
- By `bigPart_mult_s`, the exponent `e_s = n/s - q = 0` since `m_p(s) = q = n/s`,
  so the `i = s` factor contributes nothing.
- By `bigPart_mult_of_ne_s`, for `i ∈ B \ {s}` the exponent equals `n/i`
  (since `m_p(i) = 0`).
- Collecting `(X - α)` factors gives total exponent `∑_{i ∈ B \ {s}} ⌊n/i⌋
  = C - n/s = k`. The remaining product is exactly `Q_μ`.
-/
lemma hSummand_bigPart_factor_eq {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (μ : (n % s).Partition) :
    (hSummand (bigPart s hs hsn μ)).map (algebraMap ℚ ℂ)
      = (Polynomial.X - Polynomial.C α) ^ (cC α n - n / s) *
          quotientPoly α s hs hsn μ := by
  -- Helper: distribute map over hSummand
  have hSummand_map_eq :
      (hSummand (bigPart s hs hsn μ)).map (algebraMap ℚ ℂ) =
        ∏ i ∈ Finset.Icc 1 n,
          ((1 + Polynomial.X ^ i : Polynomial ℂ) ^
            (n / i - (bigPart s hs hsn μ).mult i)) := by
    have h1 : (hSummand (bigPart s hs hsn μ)).map (algebraMap ℚ ℂ) =
        ∏ i ∈ Finset.Icc 1 n,
          (((1 : Polynomial ℚ) + X ^ i : Polynomial ℚ) ^
            (n / i - (bigPart s hs hsn μ).mult i)).map (algebraMap ℚ ℂ) := by
      show ((∏ i ∈ Finset.Icc 1 n, ((1 : Polynomial ℚ) + X ^ i) ^
              (n / i - (bigPart s hs hsn μ).mult i)).map (algebraMap ℚ ℂ)) = _
      rw [Polynomial.map_prod]
    rw [h1]
    apply Finset.prod_congr rfl
    intro i _
    rw [Polynomial.map_pow]
    have h4 : ((1 : Polynomial ℚ) + X ^ i : Polynomial ℚ).map (algebraMap ℚ ℂ) =
        (1 : Polynomial ℂ) + Polynomial.X ^ i := by
      simp [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X]
    rw [h4]
  -- Helper: factor X^i + 1 when α^i = -1
  have factor_X_pow_add_one_of_mem_badSet :
      ∀ i ∈ badSet α n,
        (Polynomial.X ^ i + 1 : Polynomial ℂ) =
          (Polynomial.X - Polynomial.C α) *
            ((Polynomial.X ^ i + 1) /ₘ (Polynomial.X - Polynomial.C α)) := by
    intro i hi
    have h₁ : α ^ i = -1 := by
      have h₂ : i ∈ (Finset.Icc 1 n).filter (fun j => α ^ j = -1) := hi
      simp only [Finset.mem_filter, Finset.mem_Icc] at h₂
      exact h₂.2
    rw [Polynomial.mul_divByMonic_eq_iff_isRoot.mpr]
    simp [Polynomial.IsRoot, h₁]
  -- Helper: sum erase
  have hsmem : s ∈ badSet α n := s_mem_badSet_1 α s hs hsn hord
  have hmult_s : (bigPart s hs hsn μ).mult s = n / s := bigPart_mult_s s hs hsn μ
  have sum_erase_s_eq : ∑ i ∈ (badSet α n).erase s, n / i = cC α n - n / s := by
    have h : ∑ i ∈ (badSet α n).erase s, n / i + n / s = ∑ j ∈ badSet α n, n / j :=
      Finset.sum_erase_add (badSet α n) (fun i => n / i) hsmem
    show ∑ i ∈ (badSet α n).erase s, n / i = (∑ j ∈ badSet α n, n / j) - n / s
    omega
  -- Helper: badSet subset
  have hsub : badSet α n ⊆ Finset.Icc 1 n := by
    intro j hj; exact (Finset.mem_filter.mp hj).1
  -- Main proof
  rw [hSummand_map_eq]
  have hprod_badSet :
      ∏ i ∈ badSet α n, ((1 + Polynomial.X ^ i : Polynomial ℂ) ^
          (n / i - (bigPart s hs hsn μ).mult i)) =
      (Polynomial.X - Polynomial.C α) ^ (cC α n - n / s) *
        ∏ i ∈ (badSet α n).erase s,
          (((Polynomial.X ^ i + 1) /ₘ (Polynomial.X - Polynomial.C α)) ^ (n / i)) := by
    rw [← Finset.prod_erase_mul (badSet α n) _ hsmem]
    rw [hmult_s, Nat.sub_self, pow_zero, mul_one]
    have heq : ∀ i ∈ (badSet α n).erase s,
        ((1 + Polynomial.X ^ i : Polynomial ℂ) ^
            (n / i - (bigPart s hs hsn μ).mult i)) =
          (Polynomial.X - Polynomial.C α) ^ (n / i) *
            ((Polynomial.X ^ i + 1) /ₘ (Polynomial.X - Polynomial.C α)) ^ (n / i) := by
      intro i hi
      rw [Finset.mem_erase] at hi
      have hi_ne : i ≠ s := hi.1
      have hi_B : i ∈ badSet α n := hi.2
      rw [bigPart_mult_of_ne_s α s hs hsn hord μ hi_B hi_ne, Nat.sub_zero]
      have hcomm : (1 + Polynomial.X ^ i : Polynomial ℂ) = Polynomial.X ^ i + 1 := by ring
      rw [hcomm]
      conv_lhs => rw [factor_X_pow_add_one_of_mem_badSet i hi_B]
      rw [mul_pow]
    rw [Finset.prod_congr rfl heq]
    rw [Finset.prod_mul_distrib]
    rw [Finset.prod_pow_eq_pow_sum]
    rw [sum_erase_s_eq]
  rw [← Finset.prod_sdiff hsub, hprod_badSet]
  unfold quotientPoly
  ring

/-- Helper: For `i ∈ (badSet α n).erase s`, evaluating `(X^i + 1) /ₘ (X - C α)` at `α` gives `i * α^(i-1)`. -/
private lemma divByMonic_X_pow_add_one_eval_helper {n : ℕ} (α : ℂ) (s : ℕ)
    {i : ℕ} (hi : i ∈ (badSet α n).erase s) :
    Polynomial.eval α
        ((Polynomial.X ^ i + 1 : Polynomial ℂ) /ₘ (Polynomial.X - Polynomial.C α)) =
      (i : ℂ) * α ^ (i - 1) := by
  have hi' : i ∈ badSet α n := Finset.mem_of_mem_erase hi
  have h_eq : α ^ i = -1 := by
    unfold badSet at hi'
    exact (Finset.mem_filter.mp hi').2
  have hisRoot : (Polynomial.X ^ i + 1 : Polynomial ℂ).IsRoot α := by
    show Polynomial.eval α (Polynomial.X ^ i + 1 : Polynomial ℂ) = 0
    simp [h_eq]
  have hfact : (Polynomial.X - Polynomial.C α) *
      ((Polynomial.X ^ i + 1 : Polynomial ℂ) /ₘ (Polynomial.X - Polynomial.C α)) =
        Polynomial.X ^ i + 1 :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hisRoot
  set q : Polynomial ℂ :=
    (Polynomial.X ^ i + 1 : Polynomial ℂ) /ₘ (Polynomial.X - Polynomial.C α) with _
  have hder : Polynomial.derivative ((Polynomial.X - Polynomial.C α) * q) =
      Polynomial.derivative ((Polynomial.X ^ i + 1 : Polynomial ℂ)) := by
    rw [hfact]
  have hLHS : Polynomial.derivative ((Polynomial.X - Polynomial.C α) * q) =
      q + (Polynomial.X - Polynomial.C α) * Polynomial.derivative q := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_X_sub_C]
    ring
  have hRHS : Polynomial.derivative ((Polynomial.X ^ i + 1 : Polynomial ℂ)) =
      Polynomial.C (i : ℂ) * Polynomial.X ^ (i - 1) := by
    simp [Polynomial.derivative_add, Polynomial.derivative_one, Polynomial.derivative_pow,
      Polynomial.derivative_X, mul_comm]
  rw [hLHS, hRHS] at hder
  have hev := congrArg (Polynomial.eval α) hder
  simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C] at hev
  exact hev

/-- Helper: For `i ∈ Icc 1 n \ badSet α n`, the multiplicity in `bigPart` equals `μ.mult i`. -/
private lemma bigPart_mult_of_not_badSet_helper {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (μ : (n % s).Partition)
    {i : ℕ} (hi : i ∈ (Finset.Icc 1 n) \ (badSet α n)) :
    (bigPart s hs hsn μ).mult i = μ.mult i := by
  rw [Finset.mem_sdiff] at hi
  obtain ⟨hi_mem, hi_not_bad⟩ := hi
  rw [Finset.mem_Icc] at hi_mem
  obtain ⟨hi1, _hin⟩ := hi_mem
  have hi_ne_zero : i ≠ 0 := Nat.one_le_iff_ne_zero.mp hi1
  have hs_bad : s ∈ badSet α n := s_mem_badSet_1 α s hs hsn hord
  have hne : s ≠ i := by
    intro h
    apply hi_not_bad
    rw [← h]; exact hs_bad
  rw [bigPart_mult_eq s hs hsn μ hi_ne_zero]
  simp [hne]

/-- Helper: `μ.mult i ≤ (n % s) / i` for any `i`. -/
private lemma mult_le_div_helper {n s : ℕ} (μ : (n % s).Partition) (i : ℕ) :
    μ.mult i ≤ (n % s) / i := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [Nat.div_zero]
    have h0 : (0 : ℕ) ∉ μ.parts.toFinset := by
      intro hmem
      have h₂ : (0 : ℕ) ∈ μ.parts := Multiset.mem_toFinset.mp hmem
      have h₃ : 1 ≤ (0 : ℕ) := μ.parts_pos h₂
      omega
    have h0' : (0 : ℕ) ∉ μ.parts := fun h => h0 (Multiset.mem_toFinset.mpr h)
    exact (Multiset.count_eq_zero_of_notMem h0').le
  · by_cases hin : i ≤ n % s
    · rw [Nat.le_div_iff_mul_le hi]
      have hle : Multiset.replicate (μ.mult i) i ≤ μ.parts := by
        rw [Multiset.le_iff_count]
        intro a
        rw [Multiset.count_replicate]
        split_ifs with h
        · subst h; rfl
        · exact Nat.zero_le _
      have hsum : (Multiset.replicate (μ.mult i) i).sum ≤ μ.parts.sum := by
        obtain ⟨t, ht⟩ := Multiset.le_iff_exists_add.mp hle
        rw [ht, Multiset.sum_add]
        exact Nat.le_add_right _ _
      rw [Multiset.sum_replicate, smul_eq_mul, μ.parts_sum] at hsum
      linarith [hsum]
    · push_neg at hin
      have hi_notin : i ∉ μ.parts := by
        intro hmem
        have := μ.le_of_mem_parts hmem
        omega
      rw [Nat.Partition.mult, Multiset.count_eq_zero_of_notMem hi_notin]
      exact Nat.zero_le _

/-- Helper: `μ.mult i = 0` for `i ∈ badSet α n`. -/
private lemma mu_mult_eq_zero_of_badSet_helper {n s : ℕ} (α : ℂ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (μ : (n % s).Partition) {i : ℕ} (hi : i ∈ badSet α n) :
    μ.mult i = 0 := by
  by_cases hieq : i = s
  · rw [hieq]
    have hmod : n % s < s := Nat.mod_lt n hs
    have hnotmem : s ∉ μ.parts := by
      intro hmem
      have hle : s ≤ n % s := μ.le_of_mem_parts hmem
      exact absurd (lt_of_le_of_lt hle hmod) (lt_irrefl s)
    exact Multiset.count_eq_zero_of_notMem hnotmem
  · -- Show 3 * s ≤ i
    have hαi : α ^ i = -1 := by
      unfold badSet at hi
      rw [Finset.mem_filter] at hi
      exact hi.2
    have hmodi : i % (2 * s) = s := (pow_eq_neg_one_iff_aux_1 hs hord i).mp hαi
    have hdivmod : i = (2 * s) * (i / (2 * s)) + i % (2 * s) :=
      (Nat.div_add_mod i (2 * s)).symm
    rw [hmodi] at hdivmod
    have h3s : 3 * s ≤ i := by
      rcases Nat.eq_zero_or_pos (i / (2 * s)) with hq | hq
      · rw [hq] at hdivmod
        simp at hdivmod
        exact absurd hdivmod hieq
      · have hmul : 2 * s * 1 ≤ 2 * s * (i / (2 * s)) := Nat.mul_le_mul_left _ hq
        linarith
    have hmod : n % s < s := Nat.mod_lt n hs
    have hsi : s ≤ i := by
      have : s ≤ 3 * s := by linarith
      exact this.trans h3s
    have hlt : n % s < i := lt_of_lt_of_le hmod hsi
    have hnotmem : i ∉ μ.parts := by
      intro hmem
      have hle : i ≤ n % s := μ.le_of_mem_parts hmem
      exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl i)
    exact Multiset.count_eq_zero_of_notMem hnotmem

/-- Helper: eval of subsumPoly equals product over Icc 1 n. -/
private lemma subsumPoly_eval_eq_prod_helper {n s : ℕ} (α : ℂ) (hs : 1 ≤ s)
    (μ : (n % s).Partition) :
    Polynomial.eval α (Polynomial.map (algebraMap ℚ ℂ) (subsumPoly μ)) =
      ∏ i ∈ Finset.Icc 1 n, ((1 : ℂ) + α ^ i) ^ μ.mult i := by
  have _hs := hs
  have h1 : Polynomial.eval α (Polynomial.map (algebraMap ℚ ℂ) (subsumPoly μ))
      = (μ.parts.map (fun i => (1 : ℂ) + α ^ i)).prod := by
    unfold subsumPoly
    rw [Polynomial.map_multiset_prod, Polynomial.eval_multiset_prod]
    rw [Multiset.map_map, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro i _
    simp
  rw [h1]
  rw [prod_multiset_map_count μ.parts (fun i => (1 : ℂ) + α ^ i)]
  have hsub : μ.parts.toFinset ⊆ Finset.Icc 1 n := by
    intro i hi
    rw [Multiset.mem_toFinset] at hi
    rw [Finset.mem_Icc]
    refine ⟨μ.parts_pos hi, ?_⟩
    have hi_le : i ≤ n % s := μ.le_of_mem_parts hi
    have hns : n % s ≤ n := Nat.mod_le n s
    omega
  have heq : ∀ x ∈ μ.parts.toFinset,
      ((1 : ℂ) + α ^ x) ^ Multiset.count x μ.parts = ((1 : ℂ) + α ^ x) ^ μ.mult x := by
    intro x _; rfl
  rw [Finset.prod_congr rfl heq]
  apply Finset.prod_subset hsub
  intro x _ hxn
  rw [Multiset.mem_toFinset] at hxn
  have hcount : Multiset.count x μ.parts = 0 := Multiset.count_eq_zero_of_notMem hxn
  show ((1 : ℂ) + α ^ x) ^ μ.mult x = 1
  unfold Nat.Partition.mult
  rw [hcount]
  simp

lemma quotientPoly_eval_eq {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (μ : (n % s).Partition) :
    Polynomial.eval α (quotientPoly α s hs hsn μ)
      = Kconst α s (n := n) *
          (Polynomial.eval α (Polynomial.map (algebraMap ℚ ℂ) (subsumPoly μ)))⁻¹ := by
  unfold quotientPoly Kconst
  rw [Polynomial.eval_mul]
  -- First product
  have hQ1 : Polynomial.eval α
      (∏ i ∈ (badSet α n).erase s,
        (((Polynomial.X ^ i + 1) /ₘ (Polynomial.X - Polynomial.C α) : Polynomial ℂ) ^ (n / i)))
      = ∏ i ∈ (badSet α n).erase s, ((i : ℂ) * α ^ (i - 1)) ^ (n / i) := by
    rw [Polynomial.eval_prod]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Polynomial.eval_pow]
    rw [divByMonic_X_pow_add_one_eval_helper α s hi]
  -- Second product: split via pow_sub
  have hQ2 : Polynomial.eval α
        (∏ i ∈ (Finset.Icc 1 n) \ (badSet α n),
          ((1 + Polynomial.X ^ i : Polynomial ℂ) ^ (n / i - (bigPart s hs hsn μ).mult i))) =
      (∏ i ∈ (Finset.Icc 1 n) \ (badSet α n), ((1 : ℂ) + α ^ i) ^ (n / i)) *
        (Polynomial.eval α (Polynomial.map (algebraMap ℚ ℂ) (subsumPoly μ)))⁻¹ := by
    rw [Polynomial.eval_prod]
    have heq : ∀ i ∈ (Finset.Icc 1 n) \ (badSet α n),
        Polynomial.eval α
            ((1 + Polynomial.X ^ i : Polynomial ℂ) ^ (n / i - (bigPart s hs hsn μ).mult i)) =
          ((1 : ℂ) + α ^ i) ^ (n / i) * (((1 : ℂ) + α ^ i) ^ μ.mult i)⁻¹ := by
      intro i hi
      have hbase : (1 : ℂ) + α ^ i ≠ 0 := by
        intro hzero
        rcases Finset.mem_sdiff.mp hi with ⟨hicc, hnot⟩
        apply hnot
        rw [badSet, Finset.mem_filter]
        refine ⟨hicc, ?_⟩
        linear_combination hzero
      have hmult_eq : (bigPart s hs hsn μ).mult i = μ.mult i :=
        bigPart_mult_of_not_badSet_helper α s hs hsn hord μ hi
      have hle : (bigPart s hs hsn μ).mult i ≤ n / i := by
        rw [hmult_eq]
        have h1 : μ.mult i ≤ (n % s) / i := mult_le_div_helper μ i
        have h2 : (n % s) / i ≤ n / i := Nat.div_le_div_right (Nat.mod_le n s)
        exact h1.trans h2
      rw [hmult_eq] at hle ⊢
      rw [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_pow,
          Polynomial.eval_X]
      exact pow_sub₀ _ hbase hle
    rw [Finset.prod_congr rfl heq]
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_inv_distrib]
    -- Need: ∏ i ∈ Icc 1 n \ badSet, ((1+α^i)^μ.mult i) = eval α (subsumPoly μ map)
    rw [subsumPoly_eval_eq_prod_helper α hs μ]
    have hsub : badSet α n ⊆ Finset.Icc 1 n := by
      intro j hj; exact (Finset.mem_filter.mp hj).1
    rw [← Finset.prod_sdiff hsub]
    have hbad : ∀ i ∈ badSet α n, ((1 : ℂ) + α ^ i) ^ μ.mult i = 1 := by
      intro i hi
      rw [mu_mult_eq_zero_of_badSet_helper α hs hord μ hi]
      simp
    rw [Finset.prod_congr rfl hbad, Finset.prod_const_one, mul_one]
  rw [hQ1, hQ2]
  ring

/-- **Target theorem.** Combining the factorization with `mul_divByMonic_cancel_left`. -/
lemma R_p_eval_bigPart {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (μ : (n % s).Partition) :
    Polynomial.eval α
      (((hSummand (bigPart s hs hsn μ)).map (algebraMap ℚ ℂ)) /ₘ
        ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s)))
      = Kconst α s (n := n) *
          (Polynomial.eval α
            (Polynomial.map (algebraMap ℚ ℂ) (subsumPoly μ)))⁻¹ := by
  have hfac := hSummand_bigPart_factor_eq α s hs hsn hord μ
  have hM_monic : ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s)).Monic :=
    (Polynomial.monic_X_sub_C α).pow _
  -- F_p = M * Q  ⟹  F_p /ₘ M = Q
  rw [hfac]
  rw [Polynomial.mul_divByMonic_cancel_left _ hM_monic]
  exact quotientPoly_eval_eq α s hs hsn hord μ

/-- Main goal. -/
lemma sum_R_p_filter_eq_K_mul_sum_inv {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hsn : s ≤ n) :
    ∃ K : ℂ, K ≠ 0 ∧
      ∑ p ∈ (Finset.univ : Finset n.Partition).filter
              (fun p => cCount α n p = n / s),
          Polynomial.eval α
            (((hSummand p).map (algebraMap ℚ ℂ)) /ₘ
              ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s)))
        = K * ∑ μ : (n % s).Partition,
            (Polynomial.eval α
              (Polynomial.map (algebraMap ℚ ℂ) (subsumPoly μ)))⁻¹ := by
  refine ⟨Kconst α s (n := n), Kconst_ne_zero α s hs hsn hord, ?_⟩
  -- Step 1: rewrite the sum via the bijection μ ↦ bigPart μ.
  -- Using the bijection given by `bigPart_injective` and `bigPart_surjective_onto_filter`,
  -- combined with `cCount_bigPart`, the filtered sum equals
  -- ∑ μ, R_{bigPart μ}.eval α.
  rw [show ((Finset.univ : Finset n.Partition).filter
            (fun p => cCount α n p = n / s)) =
        (Finset.univ : Finset (n % s).Partition).image (bigPart s hs hsn) from ?_]
  · rw [Finset.sum_image (fun μ₁ _ μ₂ _ h => bigPart_injective s hs hsn h)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro μ _
    exact R_p_eval_bigPart α s hs hsn hord μ
  · ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hcc
      exact bigPart_surjective_onto_filter α s hs hsn hord p hcc
    · rintro ⟨μ, _, rfl⟩
      exact cCount_bigPart α s hs hsn hord μ

/-- **Main statement.** -/
lemma sum_R_p_eval_eq_K_mul_sum_inv {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hsn : s ≤ n) :
    ∃ K : ℂ, K ≠ 0 ∧
      ∑ p : n.Partition,
          Polynomial.eval α
            (((hSummand p).map (algebraMap ℚ ℂ)) /ₘ
              ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s)))
        = K * ∑ μ : (n % s).Partition,
            (Polynomial.eval α
              (Polynomial.map (algebraMap ℚ ℂ) (subsumPoly μ)))⁻¹ := by
  obtain ⟨K, hKne, hSeqEq⟩ := sum_R_p_filter_eq_K_mul_sum_inv α s hs hord hsn
  refine ⟨K, hKne, ?_⟩
  set R : n.Partition → ℂ := fun p =>
    Polynomial.eval α
      (((hSummand p).map (algebraMap ℚ ℂ)) /ₘ
        ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s))) with hR_def
  show ∑ p : n.Partition, R p =
       K * ∑ μ : (n % s).Partition,
            (Polynomial.eval α
              (Polynomial.map (algebraMap ℚ ℂ) (subsumPoly μ)))⁻¹
  have hsplit :
      ∑ p : n.Partition, R p =
        (∑ p ∈ (Finset.univ : Finset n.Partition).filter
                (fun p => cCount α n p = n / s), R p) +
          ∑ p ∈ (Finset.univ : Finset n.Partition).filter
                  (fun p => ¬ (cCount α n p = n / s)), R p := by
    rw [Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun p => cCount α n p = n / s) R]
  rw [hsplit]
  have hNotZero :
      ∑ p ∈ (Finset.univ : Finset n.Partition).filter
              (fun p => ¬ (cCount α n p = n / s)), R p = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hle := cCount_le_M_aux α s hs hord p
    have hlt : cCount α n p < n / s := lt_of_le_of_ne hle hp
    exact R_p_eval_zero_of_cCount_lt α s hs hord hsn p hlt
  rw [hNotZero, add_zero]
  exact hSeqEq

lemma monic_X_sub_C_pow (α : ℂ) (k : ℕ) :
    ((Polynomial.X - Polynomial.C α) ^ k).Monic := by
  exact (Polynomial.monic_X_sub_C α).pow k

lemma numStar_map_divByMonic_eq_sum {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0) :
    ((numStar n).map (algebraMap ℚ ℂ)) /ₘ
        ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s)) =
      ∑ p : n.Partition,
        ((hSummand p).map (algebraMap ℚ ℂ)) /ₘ
          ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s)) := by
  have hsum := numStar_map_eq_M_mul_sum (n := n) α s hs hord
  have hM : ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s)).Monic :=
    monic_X_sub_C_pow α (cC α n - n / s)
  rw [hsum]
  exact Polynomial.mul_divByMonic_cancel_left _ hM

/-- Main theorem (the target of this sketch). -/
lemma numStar_quotient_eval_eq_constant_mul_sum_inv {n : ℕ} (α : ℂ) (s : ℕ)
    (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hsn : s ≤ n) :
    ∃ K : ℂ, K ≠ 0 ∧
      Polynomial.eval α
        ((numStar n).map (algebraMap ℚ ℂ) /ₘ
          ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s)))
        = K * ∑ μ : (n % s).Partition,
            (Polynomial.eval α
              (Polynomial.map (algebraMap ℚ ℂ) (subsumPoly μ)))⁻¹ := by
  obtain ⟨K, hK, hEq⟩ := sum_R_p_eval_eq_K_mul_sum_inv α s hs hord hsn
  refine ⟨K, hK, ?_⟩
  have hSum := numStar_map_divByMonic_eq_sum α s hs hord (n := n)
  have hEval :
      Polynomial.eval α
          ((numStar n).map (algebraMap ℚ ℂ) /ₘ
            ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s)))
        = ∑ p : n.Partition,
            Polynomial.eval α
              (((hSummand p).map (algebraMap ℚ ℂ)) /ₘ
                ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s))) := by
    rw [hSum, Polynomial.eval_finset_sum]
  rw [hEval, hEq]


end M_quo

/-- Wrapper for `numStar_quotient_eval_eq_constant_mul_sum_inv`. -/
lemma numStar_quotient_eval_eq_constant_mul_sum_inv {n : ℕ} (α : ℂ) (s : ℕ)
    (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hsn : s ≤ n) :
    ∃ K : ℂ, K ≠ 0 ∧
      Polynomial.eval α
        ((numStar n).map (algebraMap ℚ ℂ) /ₘ
          ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s)))
        = K * ∑ μ : (n % s).Partition,
            (Polynomial.eval α
              (Polynomial.map (algebraMap ℚ ℂ) (subsumPoly μ)))⁻¹ :=
  M_quo.numStar_quotient_eval_eq_constant_mul_sum_inv α s hs hord hsn



/-- The quotient `Q := (numStar n).map /ₘ (X - C α)^(cC α n - n / s)` does not
vanish at `α`.  This is the key analytic statement (Step 7 of `proof.md`):
factoring out the common power `(x-α)^(C-M)` leaves a polynomial `Q` whose
value at `α` is
   `Q.eval α = K · ∑_{μ ⊢ r} (subsumPoly μ).eval α)⁻¹`
with `K ≠ 0`. Each per-partition value `(subsumPoly μ).eval α`, after factoring
out the fixed unit rotation `τ^r`, is a *positive real* `C μ > 0` (a product of
positive cosines, Step 7.2 of `proof.md`). Hence
   `∑_{μ ⊢ r} (subsumPoly μ).eval α)⁻¹ = (τ^r)⁻¹ · ∑_μ (C μ)⁻¹`,
and `∑_μ (C μ)⁻¹ > 0` by the reused `sum_inv_pos_of_partitions`. Therefore
the complex sum is nonzero, and so `Q.eval α ≠ 0`.

Hypotheses: `α` of exact order `2s`, `1 ≤ s ≤ n`. -/
lemma numStar_quotient_eval_ne_zero {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hsn : s ≤ n) :
    ((numStar n).map (algebraMap ℚ ℂ) /ₘ
      ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s))).eval α ≠ 0 := by
  -- Step A: get the explicit formula `Q.eval α = K * S` with `K ≠ 0`.
  obtain ⟨K, hK, hEq⟩ :=
    numStar_quotient_eval_eq_constant_mul_sum_inv α s hs hord hsn
  -- Step B: `r := n % s` satisfies `r < s` because `s ≥ 1`.
  have hr : n % s < s := Nat.mod_lt _ hs
  -- Step C: the sum `S` is nonzero by the reused custom lemma.
  have hS : ∑ μ : (n % s).Partition,
      (Polynomial.eval α (Polynomial.map (algebraMap ℚ ℂ) (subsumPoly μ)))⁻¹
      ≠ 0 :=
    sum_inv_subsumPoly_ne_zero hs hr α hord
  -- Step D: combine.
  rw [hEq]
  exact mul_ne_zero hK hS

/-- The root multiplicity of `(numStar n).map` at `α` is at most `cC α n - n / s`.
This is the main statement (Step 9 of `proof.md`): combining the lower-bound
divisibility from `pow_X_sub_C_dvd_numStar_map` with the non-vanishing of the
quotient from `numStar_quotient_eval_ne_zero`. -/
lemma rootMultiplicity_numStar_le {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hsn : s ≤ n) :
    Polynomial.rootMultiplicity α ((numStar n).map (algebraMap ℚ ℂ)) ≤
      cC α n - n / s := by
  set P := (numStar n).map (algebraMap ℚ ℂ) with hP
  have hn : 1 ≤ n := le_trans hs hsn
  have hP_ne : P ≠ 0 := numStar_map_ne_zero n hn
  have hdvd : (Polynomial.X - Polynomial.C α) ^ (cC α n - n / s) ∣ P :=
    pow_X_sub_C_dvd_numStar_map α s hs hord
  set k := cC α n - n / s
  set g : Polynomial ℂ := (Polynomial.X - Polynomial.C α) ^ k with hg
  have hg_monic : g.Monic := (Polynomial.monic_X_sub_C α).pow k
  have hQ_eval : (P /ₘ g).eval α ≠ 0 :=
    numStar_quotient_eval_ne_zero α s hs hord hsn
  rw [Polynomial.rootMultiplicity_le_iff hP_ne]
  intro hdvd_succ
  -- From hdvd we have P = g * Q where Q := P /ₘ g.
  have hPeq : P = g * (P /ₘ g) := by
    have hmod : P %ₘ g = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hg_monic).mpr hdvd
    have hadd := Polynomial.modByMonic_add_div P hg_monic
    -- hadd : P %ₘ g + g * (P /ₘ g) = P
    rw [hmod, zero_add] at hadd
    exact hadd.symm
  -- From hdvd_succ: (X-α)^(k+1) ∣ P; combined with P = g * Q, divide both sides by g.
  have hg_ne : g ≠ 0 := Polynomial.Monic.ne_zero hg_monic
  have h_X_dvd_Q : (Polynomial.X - Polynomial.C α) ∣ (P /ₘ g) := by
    -- (X-α)^(k+1) = (X-α)^k * (X-α) = g * (X-α)
    have hpow : (Polynomial.X - Polynomial.C α) ^ (k + 1) =
        g * (Polynomial.X - Polynomial.C α) := by
      simp [hg, pow_succ]
    rw [hpow] at hdvd_succ
    -- so g * (X-α) ∣ g * Q, hence (X-α) ∣ Q
    rw [hPeq] at hdvd_succ
    exact (mul_dvd_mul_iff_left hg_ne).mp hdvd_succ
  -- (X-α) ∣ Q implies Q.eval α = 0
  have hQ_zero : (P /ₘ g).eval α = 0 := by
    have : (P /ₘ g).IsRoot α := Polynomial.dvd_iff_isRoot.mp h_X_dvd_Q
    exact this
  exact hQ_eval hQ_zero


/-- Upper bound: `(X - C α)^(cC α n - n/s + 1)` does NOT divide `numStar n` mapped to `ℂ[X]`.

This is the main theorem of the sketch. It follows directly from
`rootMultiplicity_numStar_le` and `Polynomial.le_rootMultiplicity_iff`. -/
lemma pow_X_sub_C_not_dvd_numStar_map {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hsn : s ≤ n) :
    ¬ ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s + 1) ∣
      (numStar n).map (algebraMap ℚ ℂ)) := by
  have hne : Polynomial.map (algebraMap ℚ ℂ) (numStar n) ≠ 0 :=
    numStar_map_ne_zero n (le_trans hs hsn)
  have hle : Polynomial.rootMultiplicity α ((numStar n).map (algebraMap ℚ ℂ)) ≤
      cC α n - n / s :=
    rootMultiplicity_numStar_le α s hs hord hsn
  intro hdvd
  -- Convert divisibility to a bound on root multiplicity
  have hge : cC α n - n / s + 1 ≤
      Polynomial.rootMultiplicity α ((numStar n).map (algebraMap ℚ ℂ)) :=
    (Polynomial.le_rootMultiplicity_iff hne).mpr hdvd
  -- Combine the two bounds for a contradiction
  omega

/-- The vanishing order of `numStar n` at `α` equals `cC α n - n / s`, the same as
the vanishing order of `gCommon n`. The key point is that the lowest-order
contribution comes from partitions of the form `(s^M) ∪ μ` for `μ ⊢ r = n - M*s`,
and the sum of these contributions is nonzero by `sum_inv_subsumPoly_ne_zero`. -/
lemma rootMultiplicity_numStar_eq {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hsn : s ≤ n) :
    Polynomial.rootMultiplicity α ((numStar n).map (algebraMap ℚ ℂ)) =
      cC α n - n / s := by
  have hn : 1 ≤ n := le_trans hs hsn
  have hne : (numStar n).map (algebraMap ℚ ℂ) ≠ 0 := numStar_map_ne_zero n hn
  set d := cC α n - n / s with hd
  have h_ge : d ≤ Polynomial.rootMultiplicity α ((numStar n).map (algebraMap ℚ ℂ)) := by
    rw [Polynomial.le_rootMultiplicity_iff hne]
    exact pow_X_sub_C_dvd_numStar_map α s hs hord
  have h_lt : Polynomial.rootMultiplicity α ((numStar n).map (algebraMap ℚ ℂ)) < d + 1 := by
    by_contra h
    push_neg at h
    have : (Polynomial.X - Polynomial.C α) ^ (d + 1) ∣
        (numStar n).map (algebraMap ℚ ℂ) := by
      rw [← Polynomial.le_rootMultiplicity_iff hne]
      exact h
    exact pow_X_sub_C_not_dvd_numStar_map α s hs hord hsn this
  omega

/-! ### Reduced polynomials don't share a complex root -/

/-- For `n ≥ 1` and `α : ℂ`, if `denReduced n` (mapped to `ℂ[X]`) vanishes at `α`,
then `numReduced n` (mapped to `ℂ[X]`) does not vanish at `α`.

Proof sketch (Step 5 of proof.md):
* If `denReduced n` vanishes at `α`, then so does `denStar n` (since
  `denStar n = denReduced n * gCommon n`).
* Hence `α^i = -1` for some `1 ≤ i ≤ n`, so `α` has exact order `2s` for some `s ≥ 1`
  with `s ≤ n`.
* By `rootMultiplicity_numStar_eq` and `rootMultiplicity_gCommon`, both `numStar n`
  and `gCommon n` have rootMultiplicity `cC α n - n/s` at `α`. So
  `rootMultiplicity α (numReduced n) = 0`, i.e. `numReduced n` does not vanish at `α`. -/
lemma numReduced_ne_zero_of_denReduced_eq_zero (n : ℕ) (hn : 1 ≤ n) (α : ℂ)
    (h : ((denReduced n).map (algebraMap ℚ ℂ)).eval α = 0) :
    ((numReduced n).map (algebraMap ℚ ℂ)).eval α ≠ 0 := by
  have hden_eq : denStar n = denReduced n * gCommon n :=
    denStar_eq_denReduced_mul_gCommon n hn
  have hdenStar_eval : ((denStar n).map (algebraMap ℚ ℂ)).eval α = 0 := by
    rw [hden_eq, Polynomial.map_mul, Polynomial.eval_mul, h, zero_mul]
  obtain ⟨i, hi_mem, hi_pow⟩ := exists_pow_eq_neg_one_of_denStar_eval α hdenStar_eval
  rw [Finset.mem_Icc] at hi_mem
  obtain ⟨hi1, hin⟩ := hi_mem
  obtain ⟨s, hs1, hord_pow, hord_min⟩ :=
    exists_even_order_of_pow_eq_neg_one α i hi1 hi_pow
  have hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0 :=
    ⟨hord_pow, hord_min⟩
  have hsi : s ≤ i := s_le_of_pow_eq_neg_one hs1 hord hi1 hi_pow
  have hsn : s ≤ n := le_trans hsi hin
  have hnumStar_map_ne : (numStar n).map (algebraMap ℚ ℂ) ≠ 0 :=
    numStar_map_ne_zero n hn
  have hdvd : (Polynomial.X - Polynomial.C α) ^ (cC α n - n / s) ∣
      (numStar n).map (algebraMap ℚ ℂ) :=
    pow_X_sub_C_dvd_numStar_map α s hs1 hord
  have hnot_dvd : ¬ ((Polynomial.X - Polynomial.C α) ^ (cC α n - n / s + 1) ∣
      (numStar n).map (algebraMap ℚ ℂ)) :=
    pow_X_sub_C_not_dvd_numStar_map α s hs1 hord hsn
  have hle : cC α n - n / s ≤
      Polynomial.rootMultiplicity α ((numStar n).map (algebraMap ℚ ℂ)) := by
    rw [Polynomial.le_rootMultiplicity_iff hnumStar_map_ne]
    exact hdvd
  have hlt : Polynomial.rootMultiplicity α ((numStar n).map (algebraMap ℚ ℂ)) <
      cC α n - n / s + 1 := by
    by_contra hge
    push_neg at hge
    apply hnot_dvd
    exact (Polynomial.le_rootMultiplicity_iff hnumStar_map_ne).mp hge
  have hmult_num : Polynomial.rootMultiplicity α ((numStar n).map (algebraMap ℚ ℂ)) =
      cC α n - n / s := by omega
  have hmult_g : Polynomial.rootMultiplicity α ((gCommon n).map (algebraMap ℚ ℂ)) =
      cC α n - n / s := rootMultiplicity_gCommon α s hs1 hord hsn
  have hnum_eq : numStar n = numReduced n * gCommon n :=
    numStar_eq_numReduced_mul_gCommon n hn
  have hg_ne : gCommon n ≠ 0 := gCommon_ne_zero n hn
  have hg_map_ne : (gCommon n).map (algebraMap ℚ ℂ) ≠ 0 := by
    intro habs
    apply hg_ne
    exact Polynomial.map_injective (algebraMap ℚ ℂ)
      (algebraMap ℚ ℂ).injective (by simpa using habs)
  have hnumR_map_ne : (numReduced n).map (algebraMap ℚ ℂ) ≠ 0 := by
    intro habs
    apply hnumStar_map_ne
    rw [hnum_eq, Polynomial.map_mul, habs, zero_mul]
  by_contra hnumR_eval
  have hmap_eq : (numStar n).map (algebraMap ℚ ℂ) =
      (numReduced n).map (algebraMap ℚ ℂ) * (gCommon n).map (algebraMap ℚ ℂ) := by
    rw [hnum_eq, Polynomial.map_mul]
  have hmult_split :
      Polynomial.rootMultiplicity α ((numStar n).map (algebraMap ℚ ℂ)) =
        Polynomial.rootMultiplicity α ((numReduced n).map (algebraMap ℚ ℂ)) +
        Polynomial.rootMultiplicity α ((gCommon n).map (algebraMap ℚ ℂ)) := by
    rw [hmap_eq, Polynomial.rootMultiplicity_mul (mul_ne_zero hnumR_map_ne hg_map_ne)]
  have hpos : 1 ≤ Polynomial.rootMultiplicity α ((numReduced n).map (algebraMap ℚ ℂ)) := by
    rw [Nat.one_le_iff_ne_zero]
    intro hzero
    rw [Polynomial.rootMultiplicity_eq_zero_iff] at hzero
    exact hnumR_map_ne (hzero hnumR_eval)
  rw [hmult_num, hmult_g] at hmult_split
  omega

/-! ## Main theorem -/

theorem main_theorem (n : ℕ) (hn : 1 ≤ n) :
    IsCoprime (numReduced n) (denReduced n) := by
  -- denReduced n is nonzero
  have hgne : gCommon n ≠ 0 := gCommon_ne_zero n hn
  have hden_star : denStar n ≠ 0 := denStar_ne_zero n
  have hden_eq : denStar n = denReduced n * gCommon n :=
    denStar_eq_denReduced_mul_gCommon n hn
  have hden_red_ne : denReduced n ≠ 0 := by
    intro hd
    rw [hd, zero_mul] at hden_eq
    exact hden_star hden_eq
  -- Reduce to no common complex root
  apply isCoprime_of_no_common_complex_root _ _ hden_red_ne
  intro α hα
  by_contra hcontra
  exact numReduced_ne_zero_of_denReduced_eq_zero n hn α hcontra hα

end
