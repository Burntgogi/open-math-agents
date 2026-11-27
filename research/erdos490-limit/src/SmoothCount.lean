import SplitSieve
import RoughCounts

open Finset Real Filter
open scoped Topology
namespace Erdos490Smooth
open Shift490

private theorem specification {k u n m : ℕ} (hm0 : 0 < m) (hmn : m ≤ n) :
    m ∈ Nat.factoredNumbers (smoothLabels k (u:ℝ)) ↔
      ¬ ∃ p ∈ Nat.primesLE k ∪ smoothLabels u (n:ℝ), p ∣ m := by
  rw [Nat.mem_factoredNumbers_iff_primeFactors_subset]
  simp only [smoothLabels,Nat.floor_natCast]
  constructor
  · rintro ⟨_,hs⟩ ⟨p,hp,hd⟩
    have hprime : p.Prime := by
      rcases Finset.mem_union.mp hp with h|h
      · exact (Nat.mem_primesLE.mp h).2
      · exact (Finset.mem_filter.mp h).2
    have hlim := Finset.mem_Ioc.mp (Finset.mem_filter.mp (hs (Nat.mem_primeFactors.mpr ⟨hprime,hd,hm0.ne'⟩))).1
    rcases Finset.mem_union.mp hp with h|h
    · exact (not_lt_of_ge (Nat.mem_primesLE.mp h).1) hlim.1
    · exact (not_lt_of_ge hlim.2) (Finset.mem_Ioc.mp (Finset.mem_filter.mp h).1).1
  · intro h
    refine ⟨hm0.ne',?_⟩
    intro p hp
    obtain ⟨hp0,hd,_⟩ := Nat.mem_primeFactors.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_,?_⟩,hp0⟩
    · by_contra! hl
      exact h ⟨p,Finset.mem_union_left _ (Nat.mem_primesLE.mpr ⟨hl,hp0⟩),hd⟩
    · by_contra! hl
      have hpn := (Nat.le_of_dvd hm0 hd).trans hmn
      exact h ⟨p,Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hl,hpn⟩,hp0⟩),hd⟩

theorem smooth_count_eq_sieve_with_cap (k : ℕ) {U z cap : ℝ} (hcap : exp z ≤ cap) :
    F (smoothLabels k U) z = exp (-z) * smallCount (Nat.primesLE k ∪ smoothLabels ⌊U⌋₊ cap) ⌊exp z⌋₊ := by
  classical
  rw [F_eq_card]
  congr 1
  let A := smoothLabels k U
  have hset : countSet A z = (Finset.Ioc 0 ⌊exp z⌋₊).filter (· ∈ Nat.factoredNumbers A) := by
    ext m
    simp only [countSet,Finset.mem_filter,Finset.mem_range,Finset.mem_Ioc,Nat.lt_succ_iff]
    constructor
    · rintro ⟨hm,hh⟩
      exact ⟨⟨Nat.pos_of_ne_zero hh.1,hm⟩,hh⟩
    · rintro ⟨hm,hh⟩
      exact ⟨hm.2,hh⟩
  change ((countSet A z).card:ℝ) = _
  rw [hset,Finset.card_filter]
  unfold smallCount
  push_cast
  refine Finset.sum_congr rfl fun m hm => ?_
  have h := specification (k := k) (u := ⌊U⌋₊) (Finset.mem_Ioc.mp hm).1
    ((Finset.mem_Ioc.mp hm).2.trans (Nat.floor_mono hcap))
  simp only [smoothLabels,Nat.floor_natCast] at h
  rw [avoid_iff]
  unfold smoothLabels
  by_cases hmem : m ∈ Nat.factoredNumbers A
  · rw [if_pos hmem, if_neg (h.mp hmem)]
  · rw [if_neg hmem, if_pos (not_not.mp (fun e => hmem (h.mpr e)))]

theorem smooth_count_eq_sieve (k : ℕ) (U z : ℝ) :
    F (smoothLabels k U) z = exp (-z) * smallCount (Nat.primesLE k ∪ smoothLabels ⌊U⌋₊ (exp z)) ⌊exp z⌋₊ :=
  smooth_count_eq_sieve_with_cap k le_rfl

#print axioms smooth_count_eq_sieve_with_cap
end Erdos490Smooth

