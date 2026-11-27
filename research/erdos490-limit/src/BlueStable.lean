import BlueBins
import BlueScale

/-! Unconditional stable-color recovery, uniform over every old sample
in a fixed neighborhood. This is the blue inequality of LargeLabelRecovery
for the prescribed bands and the initial segment. -/
namespace Erdos490Transfer
open Finset Filter Real Shift490 Erdos490Smooth Erdos490PrimeCells
noncomputable section
open Classical

private lemma blue_absorb {H T a F₀ E D ε : ℝ} (hH : 0 < H) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hF : 0 ≤ F₀) (hE : 0 ≤ E) (hcap : F₀ ≤ K₀*E)
    (hsmall : (5*K₀+3)*a ≤ ε) (hl : (1-a)*H ≤ T) (hu : T ≤ (1+a)*H)
    (hd : ((1-2*a)*F₀-a*E)*T-a*E*H ≤ D) : F₀ ≤ H⁻¹*D + ε*E := by
  have upper : T ≤ 2*H := hu.trans (mul_le_mul_of_nonneg_right (by linarith) hH.le)
  have h1 := mul_le_mul_of_nonneg_left hl hF
  have h2 := mul_le_mul_of_nonneg_left upper (add_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ha) hF) (mul_nonneg ha hE))
  have h3 := mul_le_mul_of_nonneg_right hcap (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 5) ha) hH.le)
  have h4 := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hE hH.le)
  rw [← div_eq_inv_mul,← sub_le_iff_le_add,le_div_iff₀ hH]
  nlinarith only [hd,h1,h2,h3,h4]

/-- Once y is sufficiently large, at each late old index the prescribed
blue support recovers its stripped old density for *every* bounded-shift
sample. The target limit is taken after freezing the index and the sample. -/
theorem blue_stable_recovery (Y : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop, ∀ N : ℕ → ℕ, StrictMono N → ∀ C : ℕ → Finset ℕ,
    (∀ k, C k ⊆ (Ioc y (N k)).filter Nat.Prime) → RoughFlat N C →
    ∀ H : ℝ, 0 ≤ H → ∀ᶠ k in atTop, ∀ x : ℝ, |x-log (N k)| ≤ H →
      ∀ u : ℕ, 0 < u → ∀ᶠ m : ℕ in atTop,
        let t := log m/x
        F (C k) (log (N k)) ≤ (P (primes Y y))⁻¹*
          density (bands Mertens.M t (C k) ∪ smoothLabels (Y-1) (exp (t*width y))) m u +
          ε*(P (C k)/log (N k)) := by
  let a := min (1/8:ℝ) (ε/(5*K₀+3))
  have hden : 0 < 5*K₀+3 := by linarith [K₀_pos]
  have ha : 0 < a := lt_min (by norm_num) (div_pos hε hden)
  have ha8 : a ≤ 1/8 := min_le_left .. 
  have hsmall : (5*K₀+3)*a ≤ ε := by
    rw [mul_comm]; exact (le_div_iff₀ hden).mp (min_le_right ..)
  obtain ⟨c,hc,hdis⟩ := cell_displacement
  obtain ⟨p₀,hp₀⟩ := eventually_atTop.mp hdis
  filter_upwards [stable_good_strips hc.le ha (by linarith : a < 1/2) ha,
    blue_strip_normalized Y ha,eventually_ge_atTop p₀] with y hgoods hy hp
  obtain ⟨D,hD,hlo,hhi⟩ := hy
  intro N mono C hC flat H hH
  let J := Icc 1 D
  let E (k : ℕ) := P (C k)/log (N k)
  let M := P (primes Y y)
  let T := ∑ j ∈ J, smoothKernel (Y-1) (width y) (width_pos y) (j+1)
  have hM : 0 < M := P_pos _
  have large := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp mono.tendsto_atTop)).eventually_gt_atTop (H+2)
  filter_upwards [hgoods N mono C hC flat (H+D+2) (by positivity),large] with k hs hL
  intro x hx u hu
  let L := log (N k:ℝ)
  change H+2 < L at hL
  change |x-L| ≤ H at hx
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith [(abs_le.mp hx).1]
  have hE : 0 < E k := div_pos (P_pos _) hL0
  have hpr : ∀ p ∈ C k, Nat.Prime p := fun p h => (mem_filter.mp (hC _ h)).2
  have high : ∀ p ∈ C k, y < p := fun p h => (mem_Ioc.mp (mem_filter.mp (hC _ h)).1).1
  have hsep : ∀ᶠ t : ℝ in atTop, Disjoint (bands Mertens.M t (C k))
      (smoothLabels (Y-1) (exp (t*width y))) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact disjoint_left.mpr fun {_} hz hu =>
      (bands_above Mertens.M ht high hz).not_ge (mem_Ioc.mp (mem_filter.mp hu).1).2
  have hnew := blue_bin_recovery hpr hx0 ha.le J (fun j h => (mem_Icc.mp h).1)
    (fun p => c/log p^2) (fun p h v hv =>
      hp₀ p (hp.trans (high p h).le) (hpr p h) v ⟨hv.1.le,hv.2⟩)
    (Y-1) (width_pos y) hsep hu (mul_pos (mul_pos ha hE) hM)
  have hsum : ((1-2*a)*F (C k) L-a*E k)*T ≤
      ∑ j ∈ J, recMass (goodWindow (C k) (x-j-1+a) (x-j-a) a (fun p => c/log p^2))*
        smoothKernel (Y-1) (width y) (width_pos y) (j+1) := by
    rw [show T = _ from rfl,mul_sum]
    apply sum_le_sum
    intro j hj
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg _
    have hjD : (j:ℝ) ≤ D := by exact_mod_cast (mem_Icc.mp hj).2
    have h := hs (x-j) (abs_le.mpr ⟨by change _ ≤ x-j-L; linarith [(abs_le.mp hx).1],
      by change x-j-L ≤ _; linarith [(abs_le.mp hx).2]⟩)
    exact mul_le_mul_of_nonneg_right h (smoothKernel_range _ (width_pos y) (by positivity)).1
  filter_upwards [hnew] with m hm
  apply blue_absorb hM ha.le (by linarith) (F_nonneg ..) hE.le _ hsmall hlo hhi
    ((sub_le_sub_right hsum _).trans hm)
  simpa only [E,L,mul_div_assoc] using counting_bound (C k) L hL0

#print axioms blue_stable_recovery
end
end Erdos490Transfer
