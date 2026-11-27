import Counting
import Weighted

open Real Filter Finset
open scoped Topology

namespace Erdos490PrimeCells

private lemma count_interval {L U : ℝ} (hLU : L ≤ U) :
    (((Finset.Ioc ⌊L⌋₊ ⌊U⌋₊).filter Nat.Prime).card : ℝ) = piReal U - piReal L := by
  have h : (Nat.primesLE ⌊L⌋₊) ∪ ((Finset.Ioc ⌊L⌋₊ ⌊U⌋₊).filter Nat.Prime) =
      Nat.primesLE ⌊U⌋₊ := by
    ext p
    have hfloor := Nat.floor_mono hLU
    simp only [Finset.mem_union,Nat.mem_primesLE,Finset.mem_filter,Finset.mem_Ioc]
    by_cases hp : p.Prime <;> simp [hp]; omega
  have hd : Disjoint (Nat.primesLE ⌊L⌋₊) ((Finset.Ioc ⌊L⌋₊ ⌊U⌋₊).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Nat.mem_primesLE,Finset.mem_filter,Finset.mem_Ioc] at hp hq
    omega
  have hc := congrArg Finset.card h
  rw [Finset.card_union_of_disjoint hd,Nat.primesLE_card_eq_primeCounting,Nat.primesLE_card_eq_primeCounting] at hc
  unfold piReal
  exact eq_sub_of_add_eq' (mod_cast hc)

/-- The last prime label in a product, counted with its true upper cutoff. -/
noncomputable def cappedCount (t a b z : ℝ) : ℝ :=
  ((Finset.Ioc ⌊exp (t*a)⌋₊ ⌊min (exp (t*b)) (exp z)⌋₊).filter Nat.Prime).card

theorem last_label_interior {a b w : ℝ} (ha : 0 < a) (haw : a < w) (hwb : w < b)
    {y : ℝ → ℝ} (hy : Tendsto y atTop (𝓝 w)) (c : ℝ) :
    Tendsto (fun t : ℝ => t*cappedCount t a b (t*y t-c)/exp (t*y t-c)) atTop (𝓝 w⁻¹) := by
  have hz : Tendsto (fun t : ℝ => c/t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_const_nhds (x := c) (f := atTop)).mul tendsto_inv_atTop_zero
  have hn : Tendsto (fun t : ℝ => y t - c/t) atTop (𝓝 w) := by simpa using hy.sub hz
  have hu := counting_at_moving_scale (ha.trans haw) hy c
  have hlow := counting_at_moving_scale ha (tendsto_const_nhds (x := a)) 0
  simp only [sub_zero] at hlow
  have hgap := tendsto_id.atTop_mul_pos (sub_pos.mpr haw)
    (hy.sub_const a)
  have hg : Tendsto (fun t : ℝ => exp (-(t*(y t-a))+c)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_atBot_add_const_right atTop c (tendsto_neg_atTop_atBot.comp hgap))
  have h := hu.sub (hlow.mul hg)
  simp only [mul_zero,sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0, hn.eventually (Ioi_mem_nhds haw), hn.eventually_lt_const hwb]
    with t ht h1 h2
  change a < y t - c / t at h1
  change y t - c / t < b at h2
  have htne := ht.ne'
  have heq : t*(y t-c/t) = t*y t-c := by field_simp
  have hl : t*a < t*y t-c := heq ▸ mul_lt_mul_of_pos_left h1 ht
  have hh : t*y t-c < t*b := heq ▸ mul_lt_mul_of_pos_left h2 ht
  rw [cappedCount,min_eq_right (exp_le_exp.mpr hh.le),count_interval (exp_le_exp.mpr hl.le)]
  have he : exp (-(t*(y t-a))+c) = exp (t*a)/exp (t*y t-c) := by
    rw [← exp_sub]; congr 1; ring
  rw [he]
  field_simp

#print axioms last_label_interior
end Erdos490PrimeCells
