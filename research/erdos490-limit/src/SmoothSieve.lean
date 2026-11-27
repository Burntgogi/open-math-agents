import Arithmetic
import Mathlib

open Finset
namespace Erdos490Smooth

noncomputable def avoid (S : Finset ℕ) (m : ℕ) : ℝ :=
  ∏ p ∈ S, ((if p ∣ m then (-1:ℝ) else 0) + 1)

private lemma all_dvd {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) {m : ℕ} :
    (∏ p ∈ S, p) ∣ m ↔ ∀ p ∈ S, p ∣ m := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    apply Finset.prod_dvd_of_isRelPrime _ h
    intro p hp q hq hne
    exact (Nat.coprime_iff_isRelPrime).mp (((hS p hp).coprime_iff_not_dvd).mpr
      (fun hd => hne (((Nat.prime_dvd_prime_iff_eq (hS p hp) (hS q hq)).mp hd))))

theorem avoid_iff (S : Finset ℕ) (m : ℕ) :
    avoid S m = if ∃ p ∈ S, p ∣ m then 0 else 1 := by
  classical
  unfold avoid
  split_ifs with hh
  · obtain ⟨p,hp,hd⟩ := hh
    exact Finset.prod_eq_zero hp (by simp [hd])
  · apply Finset.prod_eq_one
    intro p hp
    simp [show ¬p ∣ m by intro h; exact hh ⟨p,hp,h⟩]

theorem avoid_expand (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (m : ℕ) :
    avoid S m = ∑ T ∈ S.powerset,
      if (∏ p ∈ T, p) ∣ m then (-1 : ℝ)^T.card else 0 := by
  classical
  unfold avoid
  rw [Finset.prod_add_one]
  apply Finset.sum_congr rfl
  intro T hT
  have hs : T ⊆ S := Finset.mem_powerset.mp hT
  split_ifs with h
  · have hall := (all_dvd (fun p hp => hS p (hs hp))).mp h
    exact (Finset.prod_congr rfl fun p hp => if_pos (hall p hp)).trans (Finset.prod_const _)
  · obtain ⟨p,hp,hd⟩ := (by
      by_contra! hall
      exact h ((all_dvd (fun p hp => hS p (hs hp))).mpr hall) :
        ∃ p ∈ T, ¬p ∣ m)
    exact Finset.prod_eq_zero hp (if_neg hd)

theorem avoid_dilate (T : Finset ℕ) {d m : ℕ}
    (h : ∀ p ∈ T, p.Prime ∧ ¬p ∣ d) :
    avoid T (d*m) = avoid T m := by
  simp only [avoid_iff]
  congr 1
  apply propext
  constructor
  · rintro ⟨p,hp,hx⟩
    exact ⟨p,hp,((h p hp).1.dvd_mul.mp hx).resolve_left (h p hp).2⟩
  · rintro ⟨p,hp,hx⟩
    exact ⟨p,hp,dvd_mul_of_dvd_right hx _⟩

noncomputable def smallCount (S : Finset ℕ) (n : ℕ) : ℝ := ∑ m ∈ Finset.Ioc 0 n, avoid S m

theorem smallCount_formula (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    smallCount S n = ∑ T ∈ S.powerset, (-1:ℝ)^T.card * (n/(∏ p ∈ T, p) : ℕ) := by
  classical
  unfold smallCount
  simp_rw [avoid_expand S hS]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← Finset.sum_filter,Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div,nsmul_eq_mul,mul_comm]

end Erdos490Smooth
