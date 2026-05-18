import Mathlib

open Polynomial Finset BigOperators
open Classical

/-! ## Main Definitions -/

noncomputable def ternaryPartitions (n : ℕ) : Finset (Nat.Partition n) :=
  (Finset.univ : Finset (Nat.Partition n)).filter
    (fun lam => ∀ i ∈ lam.parts, ∃ k : ℕ, i = 3 ^ k)

noncomputable def hPoly (n : ℕ) (lam : Nat.Partition n) : Polynomial ℤ :=
  ∏ k ∈ Finset.range (n + 1),
    (1 + (Polynomial.X : Polynomial ℤ) ^ (3 ^ k))
      ^ (n / 3 ^ k - lam.parts.count (3 ^ k))

noncomputable def G_T (n : ℕ) : Polynomial ℤ :=
  (ternaryPartitions n).gcd (hPoly n)

noncomputable def numT (n : ℕ) : Polynomial ℤ :=
  (∑ lam ∈ ternaryPartitions n, hPoly n lam) /ₘ G_T n

noncomputable def t (n : ℕ) : ℤ := (numT n).eval 1

/-! ## Helpers for `t_eq_sum` and `t_recurrence_alt` -/

noncomputable def A (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n / 3 ^ k

lemma n_le_A (n : ℕ) : n ≤ A n := by
  have h : n / 3 ^ 0 ≤ ∑ k ∈ Finset.range (n + 1), n / 3 ^ k :=
    Finset.single_le_sum (f := fun k => n / 3 ^ k) (s := Finset.range (n + 1))
      (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.succ_pos n))
  simpa [A] using h

lemma partition_card_le (n : ℕ) (lam : Nat.Partition n) : lam.parts.card ≤ n := by
  have hsum := lam.parts_sum
  have h := Multiset.card_nsmul_le_sum (fun p hp => lam.parts_pos hp)
  simp at h
  omega

lemma count_mul_le_sum_aux (s : Multiset ℕ) (a : ℕ) :
    s.count a * a ≤ s.sum := by
  have h_filter_eq_replicate : s.filter (· = a) = Multiset.replicate (s.count a) a :=
    Multiset.filter_eq' s a
  have h_sum_filter : (s.filter (· = a)).sum = s.count a * a := by
    rw [h_filter_eq_replicate, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have h_sum_le : (s.filter (· = a)).sum ≤ s.sum := by
    have := Multiset.filter_add_not (· = a) s
    have := Multiset.sum_add (s.filter (· = a)) (s.filter (fun x => ¬ x = a))
    grind
  omega

lemma count_three_pow_le_div (n : ℕ) (lam : Nat.Partition n) (k : ℕ) :
    lam.parts.count (3 ^ k) ≤ n / 3 ^ k := by
  rw [Nat.le_div_iff_mul_le (pow_pos (by norm_num) k)]
  calc Multiset.count (3 ^ k) lam.parts * 3 ^ k
      ≤ lam.parts.sum := count_mul_le_sum_aux lam.parts (3 ^ k)
    _ = n := lam.parts_sum

lemma ternary_part_exp_le (n : ℕ) (lam : Nat.Partition n)
    (hlam : lam ∈ ternaryPartitions n) (i : ℕ) (hi : i ∈ lam.parts) :
    ∃ k, k ≤ n ∧ i = 3 ^ k := by
  simp only [ternaryPartitions, Finset.mem_filter, Finset.mem_univ, true_and] at hlam
  obtain ⟨k, hik⟩ := hlam i hi
  refine ⟨k, ?_, hik⟩
  have hcount : 1 ≤ lam.parts.count i := Multiset.one_le_count_iff_mem.mpr hi
  have hi_le : i ≤ n := by
    calc i = 1 * i := (one_mul i).symm
      _ ≤ lam.parts.count i * i := Nat.mul_le_mul_right i hcount
      _ ≤ lam.parts.sum := count_mul_le_sum_aux lam.parts i
      _ = n := lam.parts_sum
  rw [hik] at hi_le
  by_contra hk
  push_neg at hk
  have h1 : 3 ^ (n + 1) ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h2 : n < 3 ^ n := Nat.lt_pow_self (by norm_num : 1 < 3)
  omega

lemma sum_count_three_pow_eq_card (n : ℕ) (lam : Nat.Partition n)
    (hlam : lam ∈ ternaryPartitions n) :
    ∑ k ∈ Finset.range (n + 1), lam.parts.count (3 ^ k) = lam.parts.card := by
  have hinj : Set.InjOn (fun k : ℕ => (3 : ℕ) ^ k) (Finset.range (n + 1)) := by
    intro x _ y _ hxy
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hxy
  have hsum :
      (∑ k ∈ Finset.range (n + 1), lam.parts.count (3 ^ k)) =
        ∑ a ∈ (Finset.range (n + 1)).image (fun k : ℕ => (3 : ℕ) ^ k),
          lam.parts.count a := by
    rw [Finset.sum_image hinj]
  rw [hsum]
  rw [← Multiset.toFinset_sum_count_eq]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    rw [Multiset.mem_toFinset] at hx
    obtain ⟨k, hk, hxk⟩ := ternary_part_exp_le n lam hlam x hx
    refine Finset.mem_image.mpr ⟨k, ?_, hxk.symm⟩
    exact Finset.mem_range.mpr (by omega)
  · intros x _ hx
    rw [Multiset.mem_toFinset] at hx
    exact Multiset.count_eq_zero.mpr hx

lemma sum_diff_eq_A_sub_card (n : ℕ) (lam : Nat.Partition n)
    (hlam : lam ∈ ternaryPartitions n) :
    ∑ k ∈ Finset.range (n + 1), (n / 3 ^ k - lam.parts.count (3 ^ k))
      = A n - lam.parts.card := by
  rw [A, ← sum_count_three_pow_eq_card n lam hlam]
  exact Finset.sum_tsub_distrib _ (fun k _ => count_three_pow_le_div n lam k)

lemma hPoly_eval_one (n : ℕ) (lam : Nat.Partition n) (hlam : lam ∈ ternaryPartitions n) :
    (hPoly n lam).eval 1 = (2 : ℤ) ^ (A n - lam.parts.card) := by
  have heach : ∀ k ∈ Finset.range (n + 1),
      ((1 + (Polynomial.X : Polynomial ℤ) ^ (3 ^ k))
        ^ (n / 3 ^ k - lam.parts.count (3 ^ k))).eval 1
      = (2 : ℤ) ^ (n / 3 ^ k - lam.parts.count (3 ^ k)) := fun k _ => by
    simp [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
  rw [hPoly, eval_prod, Finset.prod_congr rfl heach,
    Finset.prod_pow_eq_pow_sum, sum_diff_eq_A_sub_card n lam hlam]

lemma hPoly_monic (n : ℕ) (lam : Nat.Partition n) : (hPoly n lam).Monic := by
  refine Polynomial.monic_prod_of_monic _ _ (fun k _ => ?_)
  refine Monic.pow ?_ _
  rw [show (1 : Polynomial ℤ) + (Polynomial.X : Polynomial ℤ) ^ (3 ^ k) =
        (Polynomial.X : Polynomial ℤ) ^ (3 ^ k) + 1 by ring]
  exact Polynomial.monic_X_pow_add_C 1 (by positivity)

lemma exists_allOnes (n : ℕ) :
    ∃ lam : Nat.Partition n, lam ∈ ternaryPartitions n ∧ lam.parts.card = n := by
  refine ⟨⟨Multiset.replicate n 1, ?_, ?_⟩, ?_, Multiset.card_replicate n 1⟩
  · intro i hi
    rw [Multiset.eq_of_mem_replicate hi]
    exact Nat.one_pos
  · rw [Multiset.sum_replicate, smul_eq_mul, mul_one]
  · simp only [ternaryPartitions, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi
    rw [Multiset.eq_of_mem_replicate hi]
    exact ⟨0, by norm_num⟩

lemma ternaryPartitions_nonempty (n : ℕ) : (ternaryPartitions n).Nonempty :=
  ⟨_, (exists_allOnes n).choose_spec.1⟩

lemma G_T_monic (n : ℕ) : (G_T n).Monic := by
  unfold G_T
  obtain ⟨lam, hlam⟩ := ternaryPartitions_nonempty n
  have hfi := hPoly_monic n lam
  obtain ⟨r, hr⟩ : (ternaryPartitions n).gcd (hPoly n) ∣ hPoly n lam := Finset.gcd_dvd hlam
  set p := (ternaryPartitions n).gcd (hPoly n)
  have hlead : (hPoly n lam).leadingCoeff = p.leadingCoeff * r.leadingCoeff := by
    rw [hr, Polynomial.leadingCoeff_mul]
  rw [show (hPoly n lam).leadingCoeff = 1 from hfi] at hlead
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hlead.symm with hpos | hneg
  · exact hpos
  exfalso
  have hnorm : normalize p = p := Finset.normalize_gcd
  grind [leadingCoeff_normalize, Int.nonneg_iff_normalize_eq_self]

lemma X_add_one_dvd_one_add_X_pow_three_pow (k : ℕ) :
    ((Polynomial.X : Polynomial ℤ) + 1) ∣ (1 + (Polynomial.X : Polynomial ℤ) ^ (3 ^ k)) := by
  have hmod : (3 : ℕ) ^ k % 2 = 1 := by rw [Nat.pow_mod]; simp
  have hneg : (-1 : ℤ) ^ (3 ^ k) = -1 := Odd.neg_one_pow ⟨3 ^ k / 2, by omega⟩
  have heval : Polynomial.eval (-1 : ℤ) (1 + (Polynomial.X : Polynomial ℤ) ^ (3 ^ k)) = 0 := by
    simp [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, hneg]
  have hroot : ((Polynomial.X : Polynomial ℤ) - Polynomial.C (-1 : ℤ)) ∣
      (1 + (Polynomial.X : Polynomial ℤ) ^ (3 ^ k)) := by
    refine Polynomial.dvd_iff_isRoot.mpr ?_
    simpa [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X] using heval
  simpa [sub_eq_add_neg] using hroot

lemma X_add_one_pow_dvd_hPoly_card (n : ℕ) (lam : Nat.Partition n)
    (hlam : lam ∈ ternaryPartitions n) :
    ((Polynomial.X : Polynomial ℤ) + 1) ^ (A n - lam.parts.card) ∣ hPoly n lam := by
  have hfac : ∀ k ∈ Finset.range (n + 1),
      ((Polynomial.X : Polynomial ℤ) + 1) ^ (n / 3 ^ k - lam.parts.count (3 ^ k))
        ∣ (1 + (Polynomial.X : Polynomial ℤ) ^ (3 ^ k))
            ^ (n / 3 ^ k - lam.parts.count (3 ^ k)) :=
    fun k _ => pow_dvd_pow_of_dvd (X_add_one_dvd_one_add_X_pow_three_pow k) _
  have hprod := Finset.prod_dvd_prod_of_dvd _ _ hfac
  rwa [Finset.prod_pow_eq_pow_sum, sum_diff_eq_A_sub_card n lam hlam] at hprod

lemma X_add_one_pow_dvd_hPoly (n : ℕ) (lam : Nat.Partition n)
    (hlam : lam ∈ ternaryPartitions n) :
    ((Polynomial.X : Polynomial ℤ) + 1) ^ (A n - n) ∣ hPoly n lam :=
  dvd_trans (pow_dvd_pow _ (Nat.sub_le_sub_left (partition_card_le n lam) (A n)))
    (X_add_one_pow_dvd_hPoly_card n lam hlam)

lemma X_add_one_pow_dvd_G_T (n : ℕ) :
    ((Polynomial.X : Polynomial ℤ) + 1) ^ (A n - n) ∣ G_T n :=
  Finset.dvd_gcd (fun lam hlam => X_add_one_pow_dvd_hPoly n lam hlam)

lemma hPoly_map_eval_eq (n : ℕ) (lam : Nat.Partition n) (x : ℝ) :
    ((hPoly n lam).map (Int.castRingHom ℝ)).eval x =
      ∏ k ∈ Finset.range (n + 1),
        (1 + x ^ (3 ^ k)) ^ (n / 3 ^ k - lam.parts.count (3 ^ k)) := by
  simp [hPoly, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.map_prod, Polynomial.map_pow,
    Polynomial.map_add, Polynomial.map_one, Polynomial.map_X]

lemma hPoly_eval_pos_real (n : ℕ) (lam : Nat.Partition n) (x : ℝ) (hx : 0 < x) :
    0 < ((hPoly n lam).map (Int.castRingHom ℝ)).eval x := by
  rw [hPoly_map_eval_eq n lam x]
  refine Finset.prod_pos (fun k _ => pow_pos ?_ _)
  have := pow_pos hx (3 ^ k)
  linarith

lemma monic_no_pos_root_pos_at_one {P : Polynomial ℝ} (hP : P.Monic)
    (h : ∀ x : ℝ, 0 < x → P.eval x ≠ 0) : 0 < P.eval 1 := by
  by_cases hd : P.natDegree = 0
  · rw [hP.natDegree_eq_zero.mp hd]
    simp
  have hdeg : 0 < P.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)
  have hlc : (0 : ℝ) ≤ P.leadingCoeff := hP ▸ zero_le_one
  obtain ⟨i, hi⟩ := Filter.tendsto_atTop_atTop.mp
    (Polynomial.tendsto_atTop_of_leadingCoeff_nonneg P hdeg hlc) 1
  set M : ℝ := max i 1
  have hM_ge_one : 1 ≤ M := le_max_right _ _
  have hPM_pos : 0 < P.eval M := lt_of_lt_of_le zero_lt_one (hi _ (le_max_left _ _))
  by_contra hneg
  push_neg at hneg
  obtain ⟨r, hr_mem, hPr⟩ :=
    intermediate_value_Icc hM_ge_one P.continuous.continuousOn ⟨hneg, hPM_pos.le⟩
  exact h r (lt_of_lt_of_le zero_lt_one hr_mem.1) hPr

lemma G_T_eval_one_pos (n : ℕ) : 0 < (G_T n).eval 1 := by
  obtain ⟨lam, hlam⟩ := ternaryPartitions_nonempty n
  set P : Polynomial ℝ := (G_T n).map (Int.castRingHom ℝ) with hPdef
  have hPm : P.Monic := (G_T_monic n).map _
  have hdvd_real : P ∣ ((hPoly n lam).map (Int.castRingHom ℝ)) :=
    Polynomial.map_dvd (Int.castRingHom ℝ) (Finset.gcd_dvd hlam)
  have hnoroot : ∀ x : ℝ, 0 < x → P.eval x ≠ 0 := by
    intro x hx hxroot
    obtain ⟨Q, hQ⟩ := hdvd_real
    exact (hPoly_eval_pos_real n lam x hx).ne' (by rw [hQ, Polynomial.eval_mul, hxroot, zero_mul])
  have hP1 := monic_no_pos_root_pos_at_one hPm hnoroot
  have heq : P.eval 1 = (((G_T n).eval 1 : ℤ) : ℝ) := by rw [hPdef]; simp
  rw [heq] at hP1
  exact_mod_cast hP1

lemma G_T_eval_one (n : ℕ) : (G_T n).eval 1 = (2 : ℤ) ^ (A n - n) := by
  obtain ⟨lam₁, hlam₁_mem, hlam₁_card⟩ := exists_allOnes n
  have h_eval_dvd : (G_T n).eval 1 ∣ (2 : ℤ) ^ (A n - n) := by
    have h := Polynomial.eval_dvd (Finset.gcd_dvd hlam₁_mem (f := hPoly n)) (x := (1 : ℤ))
    rwa [hPoly_eval_one n lam₁ hlam₁_mem, hlam₁_card] at h
  have h_two_pow_dvd : (2 : ℤ) ^ (A n - n) ∣ (G_T n).eval 1 := by
    simpa using Polynomial.eval_dvd (X_add_one_pow_dvd_G_T n) (x := (1 : ℤ))
  have h_pos := G_T_eval_one_pos n
  have h_two_pow_pos : (0 : ℤ) < (2 : ℤ) ^ (A n - n) := by positivity
  have := Int.le_of_dvd h_two_pow_pos h_eval_dvd
  have := Int.le_of_dvd h_pos h_two_pow_dvd
  linarith

lemma numT_mul_G_T (n : ℕ) :
    numT n * G_T n = ∑ lam ∈ ternaryPartitions n, hPoly n lam := by
  have hmonic := G_T_monic n
  have hdvd : G_T n ∣ ∑ lam ∈ ternaryPartitions n, hPoly n lam :=
    Finset.dvd_sum (fun _ hlam => Finset.gcd_dvd hlam)
  have heq := Polynomial.modByMonic_add_div
    (∑ lam ∈ ternaryPartitions n, hPoly n lam) hmonic
  rw [(Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr hdvd, zero_add] at heq
  rw [numT, mul_comm]
  exact heq

lemma t_eq_sum (n : ℕ) :
    t n = ∑ lam ∈ ternaryPartitions n, (2 : ℤ) ^ (n - lam.parts.card) := by
  have hAn : n ≤ A n := n_le_A n
  have hne : ((2 : ℤ) ^ (A n - n)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have heval : (numT n).eval 1 * (G_T n).eval 1 =
      ∑ lam ∈ ternaryPartitions n, (hPoly n lam).eval 1 := by
    have := congrArg (Polynomial.eval (1 : ℤ)) (numT_mul_G_T n)
    simpa [Polynomial.eval_mul, Polynomial.eval_finset_sum] using this
  rw [G_T_eval_one, Finset.sum_congr rfl (fun lam hlam => hPoly_eval_one n lam hlam)] at heval
  have hfactor : ∀ lam ∈ ternaryPartitions n,
      (2 : ℤ) ^ (A n - lam.parts.card)
        = (2 : ℤ) ^ (A n - n) * (2 : ℤ) ^ (n - lam.parts.card) := fun lam _ => by
    have hcard := partition_card_le n lam
    rw [← pow_add]
    congr 1
    omega
  rw [Finset.sum_congr rfl hfactor, ← Finset.mul_sum] at heval
  have key : t n * (2 : ℤ) ^ (A n - n)
      = (∑ lam ∈ ternaryPartitions n, (2 : ℤ) ^ (n - lam.parts.card))
        * (2 : ℤ) ^ (A n - n) := by
    show (numT n).eval 1 * (2 : ℤ) ^ (A n - n) = _
    rw [heval]
    ring
  exact mul_right_cancel₀ hne key

/-! ## Helpers for `t_succ_eq` -/

noncomputable def addOne (m : ℕ) (lam : Nat.Partition m) : Nat.Partition (m + 1) :=
  ⟨1 ::ₘ lam.parts, by
    intro i hi
    rcases Multiset.mem_cons.mp hi with h | h
    · omega
    · exact lam.parts_pos h,
   by rw [Multiset.sum_cons, lam.parts_sum]; omega⟩

lemma addOne_mem_ternary (m : ℕ) (lam : Nat.Partition m)
    (hlam : lam ∈ ternaryPartitions m) : addOne m lam ∈ ternaryPartitions (m + 1) := by
  simp only [ternaryPartitions, Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
  intro i hi
  change i ∈ (1 ::ₘ lam.parts) at hi
  rcases Multiset.mem_cons.mp hi with rfl | h
  · exact ⟨0, by simp⟩
  · exact hlam i h

lemma one_mem_parts_of_ternary (m : ℕ) (h : ¬ 3 ∣ (m + 1))
    (mu : Nat.Partition (m + 1)) (hmu : mu ∈ ternaryPartitions (m + 1)) :
    1 ∈ mu.parts := by
  by_contra h1
  apply h
  rw [← mu.parts_sum]
  have hternary : ∀ i ∈ mu.parts, ∃ k : ℕ, i = 3 ^ k := by
    simpa [ternaryPartitions] using hmu
  refine Multiset.dvd_sum (fun i hi => ?_)
  obtain ⟨k, hk⟩ := hternary i hi
  subst hk
  rcases k with _ | k
  · simp at hi
    exact absurd hi h1
  · exact dvd_pow_self 3 (by omega)

lemma addOne_injective (m : ℕ) : Function.Injective (addOne m) := by
  intro lam₁ lam₂ h
  apply Nat.Partition.ext
  have h₂ : (1 ::ₘ lam₁.parts : Multiset ℕ) = (1 ::ₘ lam₂.parts : Multiset ℕ) := by
    simpa [addOne] using congrArg Nat.Partition.parts h
  simpa [Multiset.cons_inj_right] using h₂
lemma addOne_surjective_on_ternary (m : ℕ) (h : ¬ 3 ∣ (m + 1))
    (mu : Nat.Partition (m + 1)) (hmu : mu ∈ ternaryPartitions (m + 1)) :
    ∃ lam ∈ ternaryPartitions m, addOne m lam = mu := by
  have h1 : 1 ∈ mu.parts := one_mem_parts_of_ternary m h mu hmu
  have hcons : (1 : ℕ) ::ₘ mu.parts.erase 1 = mu.parts := Multiset.cons_erase h1
  have hsum_m : (mu.parts.erase 1).sum = m := by
    have hs := mu.parts_sum
    have hcs : ((1 : ℕ) ::ₘ mu.parts.erase 1).sum = m + 1 := by rw [hcons]; exact hs
    rw [Multiset.sum_cons] at hcs
    omega
  have htern : ∀ i ∈ mu.parts, ∃ k : ℕ, i = 3 ^ k := (Finset.mem_filter.mp hmu).2
  refine ⟨⟨mu.parts.erase 1, fun hi => mu.parts_pos (Multiset.mem_of_mem_erase hi), hsum_m⟩,
    ?_, Nat.Partition.ext hcons⟩
  rw [ternaryPartitions, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, fun i hi => htern i (Multiset.mem_of_mem_erase hi)⟩

lemma addOne_count_three_pow (m : ℕ) (lam : Nat.Partition m) (k : ℕ) (hk : 1 ≤ k) :
    (addOne m lam).parts.count (3 ^ k) = lam.parts.count (3 ^ k) := by
  have h3_pow_ne_one : (3 : ℕ) ^ k ≠ 1 := by
    have : 1 < 3 ^ k := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  grind [addOne.eq_def, Multiset.count_cons]
lemma addOne_count_one (m : ℕ) (lam : Nat.Partition m) :
    (addOne m lam).parts.count 1 = lam.parts.count 1 + 1 := by
  simp [addOne]

lemma div_three_pow_succ_eq (m : ℕ) (h : ¬ 3 ∣ (m + 1)) (k : ℕ) (hk : 1 ≤ k) :
    (m + 1) / 3 ^ k = m / 3 ^ k := by
  induction' hk with k _ IH
  · have hmod3 : (m + 1) / 3 = m / 3 := by omega
    simp [pow_one, hmod3]
  · rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, IH]

lemma hPoly_addOne_top_factor (m : ℕ) (lam : Nat.Partition m) :
    (1 + (Polynomial.X : Polynomial ℤ) ^ (3 ^ (m + 1)))
        ^ ((m + 1) / 3 ^ (m + 1) - (addOne m lam).parts.count (3 ^ (m + 1))) = 1 := by
  have hlt : m + 1 < 3 ^ (m + 1) := Nat.lt_pow_self (by norm_num)
  have hdiv : (m + 1) / 3 ^ (m + 1) = 0 := Nat.div_eq_of_lt hlt
  have hcount : (addOne m lam).parts.count (3 ^ (m + 1)) = 0 := by
    rw [Multiset.count_eq_zero]
    show 3 ^ (m + 1) ∉ (1 ::ₘ lam.parts : Multiset ℕ)
    intro hmem
    rcases Multiset.mem_cons.mp hmem with h | h
    · omega
    · have hle : 3 ^ (m + 1) ≤ lam.parts.sum := Multiset.le_sum_of_mem h
      rw [lam.parts_sum] at hle
      omega
  simp [hdiv, hcount]

lemma hPoly_addOne_eq (m : ℕ) (h : ¬ 3 ∣ (m + 1)) (lam : Nat.Partition m) :
    hPoly (m + 1) (addOne m lam) = hPoly m lam := by
  unfold hPoly
  rw [show m + 1 + 1 = (m + 1) + 1 from rfl, Finset.prod_range_succ,
    hPoly_addOne_top_factor m lam, mul_one]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · rw [pow_zero] at *
    have hcount : lam.parts.count 1 ≤ m := by
      simpa [lam.parts_sum] using count_mul_le_sum_aux lam.parts 1
    rw [addOne_count_one m lam,
      show (m + 1) / 1 - (lam.parts.count 1 + 1) = m / 1 - lam.parts.count 1 by
        rw [Nat.div_one, Nat.div_one]; omega]
  · rw [div_three_pow_succ_eq m h k hk1, addOne_count_three_pow m lam k hk1]

lemma sum_hPoly_succ_eq (m : ℕ) (h : ¬ 3 ∣ (m + 1)) :
    (∑ mu ∈ ternaryPartitions (m + 1), hPoly (m + 1) mu)
      = ∑ lam ∈ ternaryPartitions m, hPoly m lam := by
  symm
  apply Finset.sum_bij
    (fun (lam : Nat.Partition m) (_ : lam ∈ ternaryPartitions m) => addOne m lam)
  · exact fun a ha => addOne_mem_ternary m a ha
  · exact fun a₁ _ a₂ _ heq => addOne_injective m heq
  · intro b hb
    obtain ⟨lam, hlam, heq⟩ := addOne_surjective_on_ternary m h b hb
    exact ⟨lam, hlam, heq⟩
  · exact fun a _ => (hPoly_addOne_eq m h a).symm

lemma G_T_succ_dvd_G_T (m : ℕ) (h : ¬ 3 ∣ (m + 1)) :
    G_T (m + 1) ∣ G_T m :=
  Finset.dvd_gcd fun lam hlam => by
    rw [← hPoly_addOne_eq m h lam]
    exact Finset.gcd_dvd (addOne_mem_ternary m lam hlam)

lemma G_T_dvd_G_T_succ (m : ℕ) (h : ¬ 3 ∣ (m + 1)) :
    G_T m ∣ G_T (m + 1) :=
  Finset.dvd_gcd fun mu hmu => by
    obtain ⟨lam, hlam, rfl⟩ := addOne_surjective_on_ternary m h mu hmu
    rw [hPoly_addOne_eq m h lam]
    exact Finset.gcd_dvd hlam

lemma t_succ_eq (m : ℕ) (h : ¬ 3 ∣ (m + 1)) : t m = t (m + 1) := by
  have hG : G_T (m + 1) = G_T m := by
    have h1 := G_T_succ_dvd_G_T m h
    have h2 := G_T_dvd_G_T_succ m h
    have hp := G_T_monic (m + 1)
    have hq := G_T_monic m
    have hd : (G_T (m + 1)).natDegree = (G_T m).natDegree :=
      le_antisymm (Polynomial.natDegree_le_of_dvd h1 hq.ne_zero)
        (Polynomial.natDegree_le_of_dvd h2 hp.ne_zero)
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hp hq h1 hd.ge).symm
  unfold t numT
  rw [sum_hPoly_succ_eq m h, hG]

/-! ## Helpers for `t_recurrence_alt` -/

noncomputable def addThreeOnes (k : ℕ) (lam : Nat.Partition (3 * k)) :
    Nat.Partition (3 * (k + 1)) :=
  ⟨1 ::ₘ 1 ::ₘ 1 ::ₘ lam.parts, by
    intro i hi
    simp only [Multiset.mem_cons] at hi
    rcases hi with rfl | rfl | rfl | h
    · omega
    · omega
    · omega
    · exact lam.parts_pos h, by
    simp [Multiset.sum_cons, lam.parts_sum]
    ring⟩

lemma addThreeOnes_card (k : ℕ) (lam : Nat.Partition (3 * k)) :
    (addThreeOnes k lam).parts.card = lam.parts.card + 3 := by
  simp [addThreeOnes]

lemma addThreeOnes_mem_ternary (k : ℕ) (lam : Nat.Partition (3 * k))
    (hlam : lam ∈ ternaryPartitions (3 * k)) :
    addThreeOnes k lam ∈ ternaryPartitions (3 * (k + 1)) := by
  simp only [ternaryPartitions, Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
  intro i hi
  change i ∈ (1 ::ₘ 1 ::ₘ 1 ::ₘ lam.parts) at hi
  simp only [Multiset.mem_cons] at hi
  rcases hi with rfl | rfl | rfl | h
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩
  · exact hlam i h

lemma addThreeOnes_one_mem (k : ℕ) (lam : Nat.Partition (3 * k)) :
    1 ∈ (addThreeOnes k lam).parts :=
  Multiset.mem_cons_self 1 _

lemma addThreeOnes_injective (k : ℕ) : Function.Injective (addThreeOnes k) := by
  intro lam₁ lam₂ h
  apply Nat.Partition.ext
  have hparts : (1 : ℕ) ::ₘ 1 ::ₘ 1 ::ₘ lam₁.parts = 1 ::ₘ 1 ::ₘ 1 ::ₘ lam₂.parts :=
    congrArg Nat.Partition.parts h
  simpa [Multiset.cons_inj_right] using hparts

lemma three_dvd_sum_parts_ne_one (n : ℕ) (μ : Nat.Partition n)
    (hμ : μ ∈ ternaryPartitions n) :
    3 ∣ (μ.parts.filter (fun x => x ≠ 1)).sum := by
  simp only [ternaryPartitions, Finset.mem_filter, Finset.mem_univ, true_and] at hμ
  refine Multiset.dvd_sum fun i hi => ?_
  rw [Multiset.mem_filter] at hi
  obtain ⟨k, hk⟩ := hμ i hi.1
  subst hk
  rcases k with _ | k
  · simp at hi
  · exact dvd_pow_self 3 (by omega)

lemma count_one_ge_three (n : ℕ) (μ : Nat.Partition (3 * n))
    (hμ : μ ∈ ternaryPartitions (3 * n))
    (h1 : 1 ∈ μ.parts) : 3 ≤ μ.parts.count 1 := by
  have hsplit :
      (μ.parts.filter (fun x => x = 1)).sum
        + (μ.parts.filter (fun x => ¬ x = 1)).sum = μ.parts.sum :=
    Multiset.sum_filter_add_sum_filter_not (s := μ.parts) (fun x => x = 1)
  have hfilter_eq : (μ.parts.filter (fun x => x = 1)).sum = μ.parts.count 1 := by
    rw [Multiset.filter_eq', Multiset.sum_replicate, smul_eq_mul, mul_one]
  have hrest : 3 ∣ (μ.parts.filter (fun x => ¬ x = 1)).sum := by
    convert three_dvd_sum_parts_ne_one (3 * n) μ hμ using 2
  have h3sum : (3 : ℕ) ∣ μ.parts.sum := by rw [μ.parts_sum]; exact ⟨n, rfl⟩
  have h3c : (3 : ℕ) ∣ μ.parts.count 1 := by
    have : (3 : ℕ) ∣ μ.parts.count 1 + (μ.parts.filter (fun x => ¬ x = 1)).sum := by
      rw [← hfilter_eq, hsplit]
      exact h3sum
    omega
  have hge1 : 1 ≤ μ.parts.count 1 := Multiset.one_le_count_iff_mem.mpr h1
  obtain ⟨q, hq⟩ := h3c
  omega

lemma sub_three_ones_sum (μ : Multiset ℕ) (h : 3 ≤ μ.count 1) :
    (μ - (1 ::ₘ 1 ::ₘ 1 ::ₘ 0)).sum = μ.sum - 3 := by
  have h1 : 1 ∈ μ := Multiset.count_pos.mp (by omega)
  have h2 : 1 ∈ μ.erase 1 := Multiset.count_pos.mp (by rw [Multiset.count_erase_self]; omega)
  have h3 : 1 ∈ (μ.erase 1).erase 1 := Multiset.count_pos.mp (by
    rw [Multiset.count_erase_self, Multiset.count_erase_self]; omega)
  simp only [Multiset.sub_cons, Multiset.sub_zero]
  have s1 := (Multiset.sum_erase h1).symm
  have s2 := (Multiset.sum_erase h2).symm
  have s3 := (Multiset.sum_erase h3).symm
  omega
lemma cons_three_ones_sub (μ : Multiset ℕ) (h : 3 ≤ μ.count 1) :
    (1 ::ₘ 1 ::ₘ 1 ::ₘ (μ - (1 ::ₘ 1 ::ₘ 1 ::ₘ 0))) = μ := by
  have hle : (1 ::ₘ 1 ::ₘ 1 ::ₘ (0 : Multiset ℕ)) ≤ μ := by
    show Multiset.replicate 3 1 ≤ μ
    exact Multiset.le_count_iff_replicate_le.mp h
  have hcons : ∀ (x : Multiset ℕ),
      (1 ::ₘ 1 ::ₘ 1 ::ₘ x) = (1 ::ₘ 1 ::ₘ 1 ::ₘ (0 : Multiset ℕ)) + x := fun x => by
    simp [Multiset.cons_add]
  rw [hcons, add_comm]
  exact Multiset.sub_add_cancel hle
lemma addThreeOnes_surjective (k : ℕ) (μ : Nat.Partition (3 * (k + 1)))
    (hμ : μ ∈ ternaryPartitions (3 * (k + 1)))
    (h1 : 1 ∈ μ.parts) :
    ∃ lam ∈ ternaryPartitions (3 * k), addThreeOnes k lam = μ := by
  have hcnt : 3 ≤ μ.parts.count 1 := count_one_ge_three (k + 1) μ hμ h1
  set lam_parts : Multiset ℕ := μ.parts - (1 ::ₘ 1 ::ₘ 1 ::ₘ 0) with hlam_parts
  have hsum : lam_parts.sum = 3 * k := by
    rw [hlam_parts, sub_three_ones_sum μ.parts hcnt, μ.parts_sum]
    omega
  have hpos : ∀ i ∈ lam_parts, 0 < i := fun i hi =>
    μ.parts_pos (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi)
  have hpow : ∀ i ∈ lam_parts, ∃ k' : ℕ, i = 3 ^ k' := fun i hi =>
    (Finset.mem_filter.mp hμ).2 i (Multiset.mem_of_le (Multiset.sub_le_self _ _) hi)
  refine ⟨⟨lam_parts, fun {i} hi => hpos i hi, hsum⟩, ?_, ?_⟩
  · simp only [ternaryPartitions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpow
  · apply Nat.Partition.ext
    show (1 ::ₘ 1 ::ₘ 1 ::ₘ lam_parts) = μ.parts
    rw [hlam_parts]
    exact cons_three_ones_sub μ.parts hcnt

lemma sum_with_one_eq_pred_sum (n : ℕ) (hn : 1 ≤ n) :
    (∑ μ ∈ (ternaryPartitions (3 * n)).filter (fun μ => 1 ∈ μ.parts),
        (2 : ℤ) ^ (3 * n - μ.parts.card))
      = ∑ lam ∈ ternaryPartitions (3 * (n - 1)),
          (2 : ℤ) ^ (3 * (n - 1) - lam.parts.card) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  show (∑ μ ∈ (ternaryPartitions (3 * (k + 1))).filter (fun μ => 1 ∈ μ.parts),
          (2 : ℤ) ^ (3 * (k + 1) - μ.parts.card))
        = ∑ lam ∈ ternaryPartitions (3 * k),
            (2 : ℤ) ^ (3 * k - lam.parts.card)
  symm
  apply Finset.sum_bij (fun lam _ => addThreeOnes k lam)
  · intro lam hlam
    rw [Finset.mem_filter]
    exact ⟨addThreeOnes_mem_ternary k lam hlam, addThreeOnes_one_mem k lam⟩
  · exact fun a _ b _ h => addThreeOnes_injective k h
  · intro μ hμ
    rw [Finset.mem_filter] at hμ
    obtain ⟨lam, hlam, heq⟩ := addThreeOnes_surjective k μ hμ.1 hμ.2
    exact ⟨lam, hlam, heq⟩
  · intro lam _
    rw [addThreeOnes_card]
    have hcard : lam.parts.card ≤ 3 * k := partition_card_le (3 * k) lam
    congr 1
    omega

noncomputable def mulThree (n : ℕ) (lam : Nat.Partition n) : Nat.Partition (3 * n) :=
  ⟨lam.parts.map (· * 3), by
    intro i hi
    rcases Multiset.mem_map.mp hi with ⟨j, hj, rfl⟩
    have := lam.parts_pos hj
    omega,
   by simp [Multiset.sum_map_mul_right, lam.parts_sum]; ring⟩

lemma mulThree_card (n : ℕ) (lam : Nat.Partition n) :
    (mulThree n lam).parts.card = lam.parts.card := by
  show (lam.parts.map (· * 3)).card = lam.parts.card
  simp

lemma mulThree_injective (n : ℕ) : Function.Injective (mulThree n) := by
  intro lam1 lam2 h
  apply Nat.Partition.ext
  exact Multiset.map_injective
    (fun a b hab => by simpa using Nat.eq_of_mul_eq_mul_right (by norm_num : (0 : ℕ) < 3) hab)
    (congrArg Nat.Partition.parts h)

lemma mulThree_mem (n : ℕ) (lam : Nat.Partition n) (h : lam ∈ ternaryPartitions n) :
    mulThree n lam ∈ ternaryPartitions (3 * n) ∧ 1 ∉ (mulThree n lam).parts := by
  simp only [ternaryPartitions, Finset.mem_filter, Finset.mem_univ, true_and] at h
  refine ⟨?_, ?_⟩
  · simp only [ternaryPartitions, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi
    rcases Multiset.mem_map.mp hi with ⟨j, hj, rfl⟩
    obtain ⟨k, hk⟩ := h j hj
    exact ⟨k + 1, by rw [hk]; ring⟩
  · intro hcontra
    rcases Multiset.mem_map.mp hcontra with ⟨j, _, hj_eq⟩
    omega

lemma mulThree_surj.part_div_three (n : ℕ) (mu : Nat.Partition (3 * n))
    (hmu : mu ∈ ternaryPartitions (3 * n)) (hno : 1 ∉ mu.parts)
    (i : ℕ) (hi : i ∈ mu.parts) : 3 ∣ i := by
  simp only [ternaryPartitions, Finset.mem_filter, Finset.mem_univ, true_and] at hmu
  obtain ⟨k, hk⟩ := hmu i hi
  rcases k with _ | k
  · simp at hk
    exact absurd (hk ▸ hi) hno
  · exact hk ▸ dvd_pow_self 3 (by omega)

lemma mulThree_surj.divThree_isPartition (n : ℕ) (mu : Nat.Partition (3 * n))
    (hmu : mu ∈ ternaryPartitions (3 * n)) (hno : 1 ∉ mu.parts) :
    (∀ i ∈ mu.parts.map (· / 3), 0 < i) ∧ (mu.parts.map (· / 3)).sum = n := by
  have hdiv : ∀ i ∈ mu.parts, 3 ∣ i :=
    fun i hi => mulThree_surj.part_div_three n mu hmu hno i hi
  refine ⟨?_, ?_⟩
  · intro j hj
    rcases Multiset.mem_map.mp hj with ⟨i, hi, rfl⟩
    exact Nat.div_pos (Nat.le_of_dvd (mu.parts_pos hi) (hdiv i hi)) (by norm_num)
  · have heq : mu.parts = mu.parts.map (fun i => 3 * (i / 3)) := by
      conv_lhs => rw [← Multiset.map_id mu.parts]
      exact Multiset.map_congr rfl (fun i hi => by simp [Nat.mul_div_cancel' (hdiv i hi)])
    have hsum2 : mu.parts.sum = 3 * (mu.parts.map (· / 3)).sum := by
      conv_lhs => rw [heq]
      exact Multiset.sum_map_mul_left
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) (by rw [← hsum2, mu.parts_sum])

noncomputable def mulThree_surj.divThree (n : ℕ) (mu : Nat.Partition (3 * n))
    (hmu : mu ∈ ternaryPartitions (3 * n)) (hno : 1 ∉ mu.parts) :
    Nat.Partition n :=
  ⟨mu.parts.map (· / 3),
    fun {i} hi => (mulThree_surj.divThree_isPartition n mu hmu hno).1 i hi,
    (mulThree_surj.divThree_isPartition n mu hmu hno).2⟩

lemma div_three_pow_is_pow_three (i : ℕ) (hi : ∃ k' : ℕ, i = 3 ^ k') (hne : i ≠ 1) :
    ∃ k : ℕ, i / 3 = 3 ^ k := by
  obtain ⟨k', hk'⟩ := hi
  have hk0 : k' ≠ 0 := fun h => hne (by rw [hk', h, pow_zero])
  refine ⟨k' - 1, ?_⟩
  rw [hk']
  conv_lhs => rw [show k' = (k' - 1) + 1 from by omega, pow_succ]
  exact Nat.mul_div_cancel _ (by norm_num : 0 < 3)

lemma mulThree_surj.divThree_mem_ternary (n : ℕ) (mu : Nat.Partition (3 * n))
    (hmu : mu ∈ ternaryPartitions (3 * n)) (hno : 1 ∉ mu.parts) :
    mulThree_surj.divThree n mu hmu hno ∈ ternaryPartitions n := by
  simp only [ternaryPartitions, Finset.mem_filter, Finset.mem_univ, true_and]
  intro j hj
  change j ∈ mu.parts.map (· / 3) at hj
  rcases Multiset.mem_map.mp hj with ⟨i, hi_mem, rfl⟩
  exact div_three_pow_is_pow_three i ((Finset.mem_filter.mp hmu).2 i hi_mem)
    (fun heq => hno (heq ▸ hi_mem))

lemma mulThree_surj.mulThree_divThree (n : ℕ) (mu : Nat.Partition (3 * n))
    (hmu : mu ∈ ternaryPartitions (3 * n)) (hno : 1 ∉ mu.parts) :
    mulThree n (mulThree_surj.divThree n mu hmu hno) = mu := by
  apply Nat.Partition.ext
  show (mu.parts.map (· / 3)).map (· * 3) = mu.parts
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_id' mu.parts]
  exact Multiset.map_congr rfl fun i hi =>
    Nat.div_mul_cancel (mulThree_surj.part_div_three n mu hmu hno i hi)

lemma mulThree_surj (n : ℕ) (mu : Nat.Partition (3 * n))
    (hmu : mu ∈ ternaryPartitions (3 * n)) (hno : 1 ∉ mu.parts) :
    ∃ lam ∈ ternaryPartitions n, mulThree n lam = mu :=
  ⟨mulThree_surj.divThree n mu hmu hno,
   mulThree_surj.divThree_mem_ternary n mu hmu hno,
   mulThree_surj.mulThree_divThree n mu hmu hno⟩

lemma sum_no_one_eq_sum_T_n (n : ℕ) :
    (∑ μ ∈ (ternaryPartitions (3 * n)).filter (fun μ => 1 ∉ μ.parts),
        (2 : ℤ) ^ (3 * n - μ.parts.card))
      = ∑ lam ∈ ternaryPartitions n, (2 : ℤ) ^ (3 * n - lam.parts.card) := by
  symm
  refine Finset.sum_bij (fun lam _ => mulThree n lam) ?_ ?_ ?_ ?_
  · intro lam hlam
    rw [Finset.mem_filter]
    exact mulThree_mem n lam hlam
  · exact fun _ _ _ _ h => mulThree_injective n h
  · intro mu hmu
    rw [Finset.mem_filter] at hmu
    obtain ⟨lam, hlam_T, hlam_eq⟩ := mulThree_surj n mu hmu.1 hmu.2
    exact ⟨lam, hlam_T, hlam_eq⟩
  · intro lam _
    rw [mulThree_card]

lemma sum_no_one_eq (n : ℕ) :
    (∑ μ ∈ (ternaryPartitions (3 * n)).filter (fun μ => 1 ∉ μ.parts),
        (2 : ℤ) ^ (3 * n - μ.parts.card))
      = 2 ^ (2 * n) * t n := by
  rw [sum_no_one_eq_sum_T_n, t_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  have hcard := partition_card_le n lam
  rw [← pow_add]
  congr 1
  omega

lemma t_recurrence_alt (n : ℕ) (hn : 1 ≤ n) :
    t (3 * n) - t (3 * (n - 1)) = 2 ^ (2 * n) * t n := by
  rw [t_eq_sum (3 * n),
    ← Finset.sum_filter_add_sum_filter_not (s := ternaryPartitions (3 * n))
      (p := fun μ : Nat.Partition (3 * n) => 1 ∈ μ.parts)
      (f := fun μ : Nat.Partition (3 * n) => (2 : ℤ) ^ (3 * n - μ.parts.card)),
    sum_with_one_eq_pred_sum n hn, t_eq_sum (3 * (n - 1)), sum_no_one_eq n]
  ring

/-! ## Main Statements -/

theorem t_eq_three_mod (n : ℕ) :
    t (3 * n) = t (3 * n + 1) ∧ t (3 * n + 1) = t (3 * n + 2) :=
  ⟨t_succ_eq (3 * n) (by omega), t_succ_eq (3 * n + 1) (by omega)⟩

theorem t_recurrence (n : ℕ) (hn : 1 ≤ n) :
    t (3 * n) - t (3 * n - 2) = 2 ^ (2 * n) * t n := by
  rw [show 3 * n - 2 = 3 * (n - 1) + 1 by omega, ← t_succ_eq (3 * (n - 1)) (by omega)]
  exact t_recurrence_alt n hn
