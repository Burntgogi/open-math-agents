import CellSpectrum
import LogWindow

noncomputable section
namespace Shift490
open Real Finset Filter Erdos490PrimeCells
open scoped Topology

private lemma interval_upper {e : ℝ} (he : 0 < e) :
    ∀ᶠ j : ℕ in atTop, ∀ a b : ℝ, -1 ≤ a → a ≤ b → b ≤ 1 →
      (j:ℝ) * reciprocalInterval (exp (j+a)) (exp (j+b)) ≤ b-a+e := by
  obtain ⟨K,hK,N,hN⟩ := (show ∃ K : ℝ, 0 < K ∧ ∃ N : ℝ, ∀ x ≥ N, |Mertens.E₂p x| ≤ K / log x^3 from by
    obtain ⟨K,hK,h⟩ := sharp_reciprocal_error
    exact ⟨K,hK,eventually_atTop.mp h⟩)
  have hg : Tendsto (fun j : ℕ => exp ((j:ℝ)+(-1))) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  filter_upwards [hg.eventually_ge_atTop N,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ((4+16*K)/e),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop 2] with j hjN hjE hj a b ha hab hb
  let w : ℝ := j
  change 2 ≤ w at hj
  change (4+16*K)/e ≤ w at hjE
  change N ≤ exp (w+(-1)) at hjN
  change w * reciprocalInterval (exp (w+a)) (exp (w+b)) ≤ _
  have hw : 0 < w := by linarith
  have herr (v : ℝ) (hv : -1 ≤ v) : |Mertens.E₂p (exp (w+v))| ≤ K/(w/2)^3 := by
    have ht := hN _ (hjN.trans (exp_le_exp.mpr (by linarith : w+(-1) ≤ w+v)))
    rw [log_exp] at ht
    exact ht.trans (by gcongr; linarith)
  have hinc := error_increment (exp_le_exp.mpr (show w+a ≤ w+b by linarith))
  rw [log_exp,log_exp] at hinc
  have hlog := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < w+b) (by linarith : 0 < w+a))
  rw [Real.log_div (by linarith) (by linarith)] at hlog
  have hwa : 0 < w+a := by linarith
  have hrat : (w+b)/(w+a)-1 = (b-a)/(w+a) := by field_simp [hwa.ne']; ring
  rw [hrat] at hlog
  have hlog' : w*(log (w+b)-log (w+a)) ≤ b-a + 4/w := by
    refine (mul_le_mul_of_nonneg_left hlog hw.le).trans ?_
    rw [← mul_div_assoc, div_le_iff₀ hwa]
    apply (mul_le_mul_iff_of_pos_right hw).mp
    rw [add_mul,add_mul,mul_right_comm (4/w) (w+a) w,div_mul_cancel₀ _ hw.ne']
    have h1 : -(a*(b-a)) ≤ 2 := by nlinarith [mul_nonneg (show 0 ≤ a+1 by linarith) (sub_nonneg.mpr hab)]
    nlinarith [mul_le_mul_of_nonneg_right h1 hw.le]
  have hr : reciprocalInterval (exp (w+a)) (exp (w+b)) ≤ log (w+b)-log (w+a) + 2*K/(w/2)^3 := by
    rw [show 2*K/(w/2)^3 = K/(w/2)^3 + K/(w/2)^3 by ring]
    linarith [(abs_le.mp (herr a ha)).1,(abs_le.mp (herr b (ha.trans hab))).2]
  have hsq : w * (2*K/(w/2)^3) ≤ 16*K/w := by
    field_simp
    nlinarith [mul_nonneg (show 0 ≤ w-1 by linarith) hK.le]
  have he' := (div_le_iff₀ he).mp hjE
  have hbudget : 4/w+16*K/w ≤ e := by rw [← add_div,div_le_iff₀ hw]; linarith
  linarith [mul_le_mul_of_nonneg_left hr hw.le]

private theorem rect_upper (Y : ℕ) (e : ℝ) (he : 0 < e) :
    ∀ᶠ j : ℕ in atTop, ∀ a b : ℝ, a ≤ b →
      (j:ℝ)*mass ((cell Y j).filter (fun p => a ≤ offset j p ∧ offset j p ≤ b)) ≤ b-a+e := by
  let d := min 1 (e/2)
  have hd : 0 < d := lt_min zero_lt_one (by positivity)
  filter_upwards [interval_upper (e := e/2) (by positivity)] with j h a b hab
  let u := max 0 a
  let v := min 1 b
  let S := (cell Y j).filter (fun p => a ≤ offset j p ∧ offset j p ≤ b)
  have hcoord (p : ℕ) (hp : p ∈ S) : u ≤ offset j p ∧ offset j p ≤ v := by
    obtain ⟨hc,h1,h2⟩ := mem_filter.mp hp
    obtain ⟨hx,hy⟩ := (mem_filter.mp hc).2
    exact ⟨max_le (by dsimp [offset]; linarith) h1,le_min (by dsimp [offset]; linarith) h2⟩
  by_cases hne : S.Nonempty
  · obtain ⟨p,hp⟩ := hne
    have huv := (hcoord p hp).1.trans (hcoord p hp).2
    have hv := min_le_left (1:ℝ) b
    have hu := le_max_left (0:ℝ) a
    have hm := h (u-d) v (by linarith [min_le_left (1:ℝ) (e/2)]) (by linarith) hv
    have hsub : S ⊆ (Ioc ⌊exp (j+(u-d))⌋₊ ⌊exp (j+v)⌋₊).filter Nat.Prime := by
      intro k hk
      obtain ⟨hc,_⟩ := mem_filter.mp hk
      have hpr := (mem_filter.mp (mem_filter.mp hc).1).2
      have hk' : 0 < (k:ℝ) := by exact_mod_cast hpr.pos
      have hh := hcoord k hk
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt (exp_pos _).le).mpr ?_,Nat.le_floor ?_⟩,hpr⟩
      · apply (Real.lt_log_iff_exp_lt hk').mp
        dsimp [offset] at hh; linarith [hh.1]
      · apply (Real.log_le_iff_le_exp hk').mp
        dsimp [offset] at hh; linarith [hh.2]
    have hle : mass S ≤ reciprocalInterval (exp (j+(u-d))) (exp (j+v)) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    change (j:ℝ)*mass S ≤ _
    linarith [mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg j),le_max_right (0:ℝ) a,
      min_le_right (1:ℝ) b,min_le_right (1:ℝ) (e/2)]
  · rw [show (cell Y j).filter (fun p => a ≤ offset j p ∧ offset j p ≤ b) = ∅ from not_nonempty_iff_eq_empty.mp hne]
    simp [mass]; linarith

theorem rectangle_pnt (Y : ℕ) : RectanglePNT Y := by
  refine ⟨?_,rect_upper Y⟩
  have hlow := (log_window_mass (a := 1/10) (b := 9/10) (by norm_num) (by norm_num) (by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hY := (tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (Y:ℝ)
  filter_upwards [hlow.eventually (lt_mem_nhds (show (2:ℝ)/3 < 9/10-1/10 by norm_num)),
    rect_upper Y 1 zero_lt_one, hY, (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop 4]
    with j hlo hup hy hj
  have hj0 : 0 < (j:ℝ) := by linarith
  have hs : (Ioc ⌊exp (j+(1/10:ℝ))⌋₊ ⌊exp (j+(9/10:ℝ))⌋₊).filter Nat.Prime ⊆ cell Y j := by
    intro p hp
    obtain ⟨hpI,hpr⟩ := mem_filter.mp hp
    have hpp : 0 < (p:ℝ) := by exact_mod_cast hpr.pos
    obtain ⟨hh,hk⟩ := mem_Ioc.mp hpI
    have h1 := (Real.lt_log_iff_exp_lt hpp).mpr (Nat.lt_of_floor_lt hh)
    have h2 := (Real.log_le_iff_le_exp hpp).mpr ((Nat.cast_le.mpr hk).trans (Nat.floor_le (exp_pos _).le))
    have hpy : (Y:ℝ) ≤ p := by
      change (Y:ℝ) ≤ exp j at hy
      exact hy.trans ((exp_le_exp.mpr (by linarith : (j:ℝ) ≤ j+1/10)).trans (Nat.lt_of_floor_lt hh).le)
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by exact_mod_cast hpy,
      Nat.le_floor ((Real.log_le_iff_le_exp hpp).mp (by linarith))⟩,hpr⟩,by constructor <;> linarith⟩
  have hh : reciprocalInterval (exp (j+(1/10:ℝ))) (exp (j+(9/10:ℝ))) ≤ mass (cell Y j) :=
    sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
  change 2/3 < (j:ℝ)*reciprocalInterval _ _ at hlo
  have hl := mul_le_mul_of_nonneg_left hh hj0.le
  have hu := hup 0 1 (by norm_num)
  rw [filter_eq_self.mpr (fun p hp => by
    obtain ⟨h1,h2⟩ := (mem_filter.mp hp).2
    dsimp [offset]; constructor <;> linarith)] at hu
  constructor
  · apply (div_le_iff₀ (by positivity)).mpr
    linarith
  · by_contra! h
    nlinarith [mul_pos hj0 (sub_pos.mpr h)]

#print axioms rectangle_pnt
end Shift490
