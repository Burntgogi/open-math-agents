import SieveError

open Finset
namespace Erdos490Smooth

private theorem multiples (n : ℕ) {d : ℕ} (hd : 0 < d) :
    (Finset.Ioc 0 n).filter (d ∣ ·) = (Finset.Ioc 0 (n/d)).image (d*·) := by
  ext m
  simp only [Finset.mem_filter,Finset.mem_Ioc,Finset.mem_image]
  constructor
  · rintro ⟨⟨hm,hmn⟩,⟨j,rfl⟩⟩
    exact ⟨j,⟨Nat.pos_of_mul_pos_left hm,(Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using hmn)⟩,rfl⟩
  · rintro ⟨j,⟨hj,hjn⟩,rfl⟩
    exact ⟨⟨Nat.mul_pos hd hj,by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hjn⟩,dvd_mul_right _ _⟩

private theorem count_multiples (S : Finset ℕ) (n : ℕ) {d : ℕ} (hd : 0 < d)
    (h : ∀ p ∈ S, p.Prime ∧ ¬p ∣ d) :
    ∑ m ∈ (Finset.Ioc 0 n).filter (d ∣ ·), avoid S m = smallCount S (n/d) := by
  rw [multiples n hd,Finset.sum_image]
  · unfold smallCount
    exact Finset.sum_congr rfl fun _ _ => avoid_dilate S h
  · exact fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_left hd he

theorem split_sieve (S L : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hL : ∀ p ∈ L, p.Prime)
    (hd : Disjoint S L) (n : ℕ) :
    smallCount (S ∪ L) n = ∑ T ∈ L.powerset,
      (-1:ℝ)^T.card * smallCount S (n/(∏ p ∈ T,p)) := by
  conv_lhs => unfold smallCount
  have ha (m : ℕ) : avoid (S ∪ L) m = avoid S m * avoid L m := by
    unfold avoid; exact Finset.prod_union hd
  simp_rw [ha,avoid_expand L hL,Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T hT => ?_
  let d := ∏ p ∈ T, p
  have hs := Finset.mem_powerset.mp hT
  have hd0 : 0 < d := Finset.prod_pos fun p hp => (hL p (hs hp)).pos
  have hfree (p : ℕ) (hp : p ∈ S) : p.Prime ∧ ¬p ∣ d := by
    refine ⟨hS p hp, (hS p hp).coprime_iff_not_dvd.mp ?_⟩
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    apply ((hS p hp).coprime_iff_not_dvd).mpr
    intro hdiv
    have he := (Nat.prime_dvd_prime_iff_eq (hS p hp) (hL q (hs hq))).mp hdiv
    exact Finset.disjoint_left.mp hd hp (he ▸ hs hq)
  change (∑ m ∈ Finset.Ioc 0 n, avoid S m * (if d ∣ m then (-1:ℝ)^T.card else 0)) =
    (-1:ℝ)^T.card * smallCount S (n/d)
  rw [← count_multiples S n hd0 hfree,Finset.mul_sum,Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> ring

theorem truncated_error (S L : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hL : ∀ p ∈ L, p.Prime)
    (hd : Disjoint S L) (n : ℕ) :
    let T := L.powerset.filter (fun U => (∏ p ∈ U,p) ≤ n)
    |smallCount (S ∪ L) n - n * localProduct S * ∑ U ∈ T, (-1:ℝ)^U.card / (∏ p ∈ U,p : ℕ)| ≤
      2 ^ S.card * T.card := by
  classical
  dsimp only
  rw [split_sieve S L hS hL hd]
  let T := L.powerset.filter (fun U => (∏ p ∈ U,p) ≤ n)
  have hp : (∑ U ∈ L.powerset, (-1:ℝ)^U.card * smallCount S (n/(∏ p ∈ U,p))) =
      ∑ U ∈ T, (-1:ℝ)^U.card * smallCount S (n/(∏ p ∈ U,p)) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro U hU hout
    have hgt : n < ∏ p ∈ U,p := by
      by_contra! hh
      exact hout (Finset.mem_filter.mpr ⟨hU,hh⟩)
    simp [Nat.div_eq_of_lt hgt,smallCount]
  rw [hp,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _U ∈ T, (2:ℝ)^S.card := by
      refine Finset.sum_le_sum fun U hU => ?_
      let d := ∏ p ∈ U, p
      have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
      have hd0 : 0 < d := Finset.prod_pos fun p hp => (hL p (hsub hp)).pos
      have he := cofactor_rounding S hS n hd0
      calc
        _ = |(-1:ℝ)^U.card * (smallCount S (n/d) - n/d*localProduct S)| := by congr 1; ring
        _ ≤ _ := by rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]; exact he
    _ = _ := by simp [mul_comm,T]

#print axioms truncated_error
end Erdos490Smooth
