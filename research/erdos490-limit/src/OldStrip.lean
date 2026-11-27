import StableTransfer
import SieveError

/-! Exact finite inclusion–exclusion for removing old prime colors and its
uniform consequence on a stable old sequence. -/
namespace Erdos490Transfer
open Finset Filter Real Shift490 Erdos490Smooth
noncomputable section
open Classical

private def dprod (T : Finset ℕ) := ∏ p ∈ T, p
private def coeff (T : Finset ℕ) : ℝ := (-1:ℝ)^T.card / dprod T

private lemma product_active {C T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) (hc : T ⊆ C) :
    Active C (dprod T) := by
  refine Nat.mem_factoredNumbers_of_primeFactors_subset
    (Finset.prod_ne_zero_iff.mpr (fun p hp => (hT p hp).ne_zero)) ?_
  simpa only [dprod,Nat.primeFactors_prod hT] using hc

private lemma div_count {C : Finset ℕ} {d : ℕ} (hd : Active C d) (n : ℕ) :
    ((semigroup C n).filter (d ∣ ·)).card = (semigroup C (n/d)).card := by
  have hpos := Nat.pos_of_ne_zero hd.1
  have eq : (semigroup C n).filter (d ∣ ·) = (semigroup C (n/d)).image (· * d) := by
    ext m
    constructor
    · intro hm
      obtain ⟨hm,hm'⟩ := mem_filter.mp hm
      obtain ⟨hc,hl⟩ := mem_semigroup.mp hm
      refine mem_image.mpr ⟨m/d,mem_semigroup.mpr ⟨Nat.mem_factoredNumbers_of_dvd hc
        (Nat.div_dvd_of_dvd hm'),Nat.div_le_div_right hl⟩,Nat.div_mul_cancel hm'⟩
    · rintro hm
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hm
      obtain ⟨hc,hl⟩ := mem_semigroup.mp ha
      exact mem_filter.mpr ⟨mem_semigroup.mpr ⟨Nat.mul_mem_factoredNumbers hc hd,
        (Nat.le_div_iff_mul_le hpos).mp hl⟩,dvd_mul_left ..⟩
  rw [eq,card_image_of_injective _ (fun _ _ e => Nat.eq_of_mul_eq_mul_right hpos e)]

theorem stripped_count {S C : Finset ℕ} (hs : S ⊆ C) (hp : ∀ p ∈ S, p.Prime) (n : ℕ) :
    ((semigroup (C \ S) n).card:ℝ) = ∑ T ∈ S.powerset,
      (-1:ℝ)^T.card * (semigroup C (n/dprod T)).card := by
  have eq : semigroup (C \ S) n = (semigroup C n).filter (fun m => ¬∃ p ∈ S, p ∣ m) := by
    ext m
    simp only [mem_filter,mem_semigroup,Nat.mem_factoredNumbers']
    constructor
    · intro ⟨h,hl⟩
      exact ⟨⟨fun p hp hd => (mem_sdiff.mp (h p hp hd)).1,hl⟩,
        fun ⟨p,hm,hd⟩ => (mem_sdiff.mp (h p (hp p hm) hd)).2 hm⟩
    · rintro ⟨⟨h,hl⟩,ha⟩
      exact ⟨fun p hp hd => mem_sdiff.mpr ⟨h p hp hd, fun hm => ha ⟨p,hm,hd⟩⟩,hl⟩
  calc
    _ = ∑ m ∈ semigroup C n, avoid S m := by
      rw [eq,card_filter]
      push_cast
      simp only [avoid_iff]
      apply sum_congr rfl
      intro m _
      split_ifs <;> norm_num
    _ = _ := by
      simp_rw [avoid_expand S hp]
      rw [sum_comm]
      apply sum_congr rfl
      intro T hT
      rw [← sum_filter,sum_const,nsmul_eq_mul]
      change (((semigroup C n).filter (dprod T ∣ ·)).card:ℝ) * _ = _
      rw [div_count (product_active
        (fun p h => hp p (mem_powerset.mp hT h)) ((mem_powerset.mp hT).trans hs)),mul_comm]

lemma F_eq_semigroup (C : Finset ℕ) (w : ℝ) :
    F C w = exp (-w) * (semigroup C ⌊exp w⌋₊).card := by
  rw [F_eq_card]
  congr 3
  ext m
  simp only [countSet,mem_filter,mem_range,Nat.lt_succ_iff,mem_semigroup]
  exact and_comm

/-- Finite Möbius inversion, valid also below the first semigroup integer. -/
theorem stripped_density {S C : Finset ℕ} (hs : S ⊆ C) (hp : ∀ p ∈ S, p.Prime) (w : ℝ) :
    F (C \ S) w = ∑ T ∈ S.powerset, coeff T * F C (w-log (dprod T)) := by
  rw [F_eq_semigroup,stripped_count hs hp,mul_sum]
  apply sum_congr rfl
  intro T hT
  have hpos := Nat.pos_of_ne_zero (product_active (fun p h => hp p (mem_powerset.mp hT h))
    ((mem_powerset.mp hT).trans hs)).1
  have hpos' : 0 < (dprod T:ℝ) := by exact_mod_cast hpos
  rw [F_eq_semigroup,exp_sub,exp_log hpos',Nat.floor_div_natCast,
    show -(w-log (dprod T)) = -w+log (dprod T) by ring,exp_add,exp_log hpos']
  unfold coeff
  field_simp


private lemma coeff_sum {S : Finset ℕ} (hp : ∀ p ∈ S, p.Prime) :
    (∑ T ∈ S.powerset, coeff T) = (P S)⁻¹ := by
  change (∑ T ∈ S.powerset, (-1:ℝ)^T.card / (∏ p ∈ T, p:ℕ)) = _
  rw [← localProduct_expand,P,filter_true_of_mem hp,prod_inv_distrib,inv_inv]
  rfl

/-- Uniform in the shift and in the subset of a fixed finite pool removed
from the old color. The loss is measured in units of the stripped scale. -/
theorem stable_strip {Y N c b} (st : Stable (Y:=Y) N c b) (pool : Finset ℕ)
    (hp : ∀ p ∈ pool, Nat.Prime p) (H η : ℝ) (hH : 0 ≤ H) (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ S ⊆ pool, S ⊆ pick (c k) b → ∀ h : ℝ, |h| ≤ H →
      |F (pick (c k) b \ S) (log (N k)+h) - (P S)⁻¹ * F (pick (c k) b) (log (N k))|
        ≤ η * (P (pick (c k) b \ S) / log (N k)) := by
  let radius := ∑ T ∈ pool.powerset, |log (dprod T)|
  let B := (pool.powerset.card:ℝ)*P pool
  have hcount : 0 < pool.powerset.card := card_pos.mpr ⟨∅,mem_powerset.mpr (empty_subset _)⟩
  have hB : 0 < B := mul_pos (by exact_mod_cast hcount) (P_pos _)
  have hrad : 0 ≤ radius := sum_nonneg fun _ _ => abs_nonneg _
  filter_upwards [st (H+radius) (by positivity) (η/B) (div_pos hη hB)] with k hk
  intro S hS hs h hh
  let C := pick (c k) b
  let L := log (N k:ℝ)
  have hSp := fun p (hx : p ∈ S) => hp p (hS hx)
  have mult {A D : Finset ℕ} (h : A ⊆ D) : P D = P A*P (D \ A) := by
    rw [← P_union (show Disjoint A (D \ A) from disjoint_left.mpr (fun {_} ha hb => (mem_sdiff.mp hb).2 ha)),
      union_sdiff_of_subset h]
  have hPS : P S ≤ P pool := by
    rw [mult hS]; exact le_mul_of_one_le_right (P_pos _).le (one_le_P _)
  have hEC : eulerScale C (N k) = P C/L := (pick_scale ..).symm
  let E := η/B*(P C/L)
  have hE : 0 ≤ E := mul_nonneg (div_nonneg hη.le hB.le) (div_nonneg (P_pos _).le (log_natCast_nonneg _))
  have term (T) (ht : T ∈ S.powerset) :
      |coeff T * (F C (L+h-log (dprod T)) - F C L)| ≤ E := by
    have htp := mem_powerset.mpr ((mem_powerset.mp ht).trans hS)
    have hbound : |log (dprod T)| ≤ radius :=
      single_le_sum (fun T _ => abs_nonneg (log (dprod T))) htp
    have hsft : |h-log (dprod T)| ≤ H+radius := (abs_sub _ _).trans (add_le_add hh hbound)
    have hdiff := hk _ hsft
    rw [← add_sub_assoc,hEC] at hdiff
    have hd := Nat.pos_of_ne_zero (product_active (fun p h => hSp p (mem_powerset.mp ht h))
      (mem_powerset.mp ht)).1
    have hcoeff : |coeff T| ≤ 1 := by
      simp only [coeff,abs_div,abs_pow,abs_neg,abs_one,one_pow,abs_of_nonneg (show 0 ≤ (dprod T:ℝ) by positivity)]
      exact one_div_le_one_div_of_le zero_lt_one (by exact_mod_cast hd) |>.trans_eq (one_div_one)
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)).trans (mul_le_of_le_one_left hE hcoeff)
  change |F (C \ S) (L+h) - (P S)⁻¹*F C L| ≤ _
  rw [stripped_density hs hSp,← coeff_sum hSp,sum_mul,← sum_sub_distrib]
  calc
    _ ≤ ∑ T ∈ S.powerset, |coeff T * (F C (L+h-log (dprod T))-F C L)| := by
      simp only [mul_sub]
      exact abs_sum_le_sum_abs .. 
    _ ≤ ∑ _T ∈ S.powerset, E := sum_le_sum term
    _ ≤ (pool.powerset.card:ℝ)*E := by
      simp only [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card (powerset_mono.mpr hS)) hE
    _ ≤ _ := by
      change _ ≤ η*(P (C \ S)/L)
      dsimp only [E,B]
      rw [mult (show S ⊆ C from hs)]
      have hb : (pool.powerset.card:ℝ) ≠ 0 := by exact_mod_cast hcount.ne'
      have hcancel : (pool.powerset.card:ℝ)*(η/((pool.powerset.card:ℝ)*P pool)*(P S*P (C \ S)/L))
          = (P S/P pool)*(η*(P (C \ S)/L)) := by field_simp [hb,(P_pos pool).ne']
      rw [hcancel]
      exact mul_le_of_le_one_left (mul_nonneg hη.le (div_nonneg (P_pos _).le (log_natCast_nonneg _)))
        ((div_le_one (P_pos _)).mpr hPS)

end
end Erdos490Transfer
