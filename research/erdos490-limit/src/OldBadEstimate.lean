import OldBadMass
import DisplacementTail
import Dilation

/-! Uniform exclusion of old repeated primes and large displacements on unit
logarithmic windows, in the normalization required by (8). -/
namespace Erdos490Transfer
open Finset Filter Real Shift490 Erdos490PrimeCells
open scoped Topology
noncomputable section
open Classical

private def wt (p : ℕ) : ℝ := 1 / ((p:ℝ)*log p^2)
private def cap (W : ℝ) : ℝ := 2*exp W*K₀
private lemma cap_pos (W : ℝ) : 0 < cap W := by unfold cap; exact mul_pos (mul_pos (by norm_num) (exp_pos _)) K₀_pos

private lemma local_cap (C : Finset ℕ) {x a d W : ℝ} (hx : 0 < x) (ha : x-W ≤ a)
    (hd : d ≤ x/2) : windowMass C (a-d) (x-d) ≤ cap W*(P C/x) := by
  have hpos : 0 < x-d := by linarith
  calc
    _ ≤ exp ((x-d)-(a-d))*F C (x-d) := window_cap .. 
    _ ≤ exp W * (K₀*P C/(x-d)) := mul_le_mul (exp_le_exp.mpr (by linarith))
      (counting_bound C _ hpos) (F_nonneg ..) (exp_pos _).le
    _ ≤ _ := by
      unfold cap
      have h : x ≤ 2*(x-d) := by linarith
      have h' := mul_le_mul_of_nonneg_left h (mul_nonneg K₀_pos.le (P_pos C).le)
      field_simp [hx.ne',hpos.ne']
      nlinarith only [h']

private lemma wt_window {y Z : ℕ} {C : Finset ℕ} (hy : 2 ≤ y)
    (hC : C ⊆ (Ioc y Z).filter Nat.Prime) {x a W : ℝ} (hx : 0 < x) (ha : x-W ≤ a)
    (hZ : (Z:ℝ) ≤ exp (x*2)) (A : ℝ)
    (hmass : reciprocalInterval (exp (x*(1/4))) (exp (x*2)) ≤ A)
    (d : ℕ → ℝ) (hd : ∀ p ∈ C, d p ≤ 2*log p) :
    (∑ p ∈ C, wt p * windowMass C (a-d p) (x-d p)) ≤
      (cap W*(P C/x))*(log y)⁻¹ + (16/x^2*P C)*A := by
  let B := C.filter (fun p : ℕ => x/4 < log p)
  have hp : ∀ p ∈ C, p.Prime := fun _ h => (mem_filter.mp (hC h)).2
  have hB : B ⊆ (Ioc ⌊exp (x*(1/4))⌋₊ ⌊exp (x*2)⌋₊).filter Nat.Prime := by
    intro p h
    obtain ⟨hc,hl⟩ := mem_filter.mp h
    have h0 : 0 < (p:ℝ) := by exact_mod_cast (hp p hc).pos
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.floor_lt (exp_pos _).le |>.mpr
      ((lt_log_iff_exp_lt h0).mp (by linarith)),Nat.le_floor ((by exact_mod_cast
        (mem_Ioc.mp (mem_filter.mp (hC hc)).1).2 : (p:ℝ) ≤ Z).trans hZ)⟩,hp p hc⟩
  have hW : (∑ p ∈ C, wt p) ≤ (log y)⁻¹ := (sum_le_sum_of_subset_of_nonneg hC
    (fun _ _ _ => by unfold wt; positivity)).trans (finite_displacement_tail hy Z)
  have hFar : (∑ p ∈ B, (p:ℝ)⁻¹) ≤ A := (sum_le_sum_of_subset_of_nonneg hB
    (fun _ _ _ => by positivity)).trans hmass
  have hs : 0 ≤ cap W*(P C/x) := mul_nonneg (cap_pos W).le (div_nonneg (P_pos C).le hx.le)
  have ht : 0 ≤ 16/x^2*P C := mul_nonneg (by positivity) (P_pos C).le
  calc
    _ ≤ ∑ p ∈ C, (cap W*(P C/x)*wt p + (16/x^2*P C)*(if x/4 < log p then (p:ℝ)⁻¹ else 0)) := by
      apply sum_le_sum
      intro p hc
      have h0 : 0 < (p:ℝ) := by exact_mod_cast (hp p hc).pos
      have hw : 0 ≤ wt p := by unfold wt; positivity
      by_cases h : x/4 < log p
      · rw [if_pos h]
        refine le_trans ?_ (le_add_of_nonneg_left (mul_nonneg hs hw))
        have hl : 0 < log (p:ℝ) := by linarith
        have bound : wt p ≤ 16/x^2 * (p:ℝ)⁻¹ := by
          unfold wt
          field_simp [hx.ne',hl.ne',h0.ne']
          nlinarith [sq_nonneg (4*log (p:ℝ)-x),mul_pos (by linarith : 0 < 4*log (p:ℝ)-x)
            (by linarith : 0 < 4*log (p:ℝ)+x)]
        calc
          _ ≤ (16/x^2 * (p:ℝ)⁻¹)*P C := mul_le_mul bound (window_total C hp ..)
            (sum_nonneg (fun _ _ => by positivity)) (by positivity)
          _ = _ := by ring
      · rw [if_neg h,mul_zero,add_zero,mul_comm]
        exact mul_le_mul_of_nonneg_right (local_cap C hx ha (by linarith [hd p hc])) hw
    _ = cap W*(P C/x)*(∑ p ∈ C, wt p) + (16/x^2*P C)*(∑ p ∈ B, (p:ℝ)⁻¹) := by
      rw [sum_add_distrib,← mul_sum,← mul_sum,sum_filter]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hW hs) (mul_le_mul_of_nonneg_left hFar ht)

private lemma square_le_wt : ∀ᶠ p : ℕ in atTop, ((p^2:ℕ):ℝ)⁻¹ ≤ wt p := by
  have h := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h,eventually_ge_atTop 2] with p hp h2
  have h1 : 1 < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hl := log_pos h1
  change ‖log (p:ℝ) ^ (2:ℝ)‖ ≤ 1 * ‖(p:ℝ) ^ (1:ℝ)‖ at hp
  rw [show (2:ℝ)=(2:ℕ) by norm_num,Real.rpow_natCast,Real.rpow_one,one_mul,
    Real.norm_eq_abs,abs_of_pos (by positivity),Real.norm_eq_abs,abs_of_pos (by linarith)] at hp
  rw [wt,one_div,Nat.cast_pow,pow_two (p:ℝ)]
  exact inv_anti₀ (mul_pos (by linarith) (sq_pos_of_pos hl)) (mul_le_mul_of_nonneg_left hp (by linarith))

/-- The local error in (8) tends to zero in units of P C / x, first in
the old log endpoint x and then in the auxiliary prime cutoff y. All
finite old colors C in (y,Z] and all intervals of length ≤1 are allowed. -/
theorem old_bad_negligible_of_width (W : ℝ) {c δ ε : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ Z : ℕ, (Z:ℝ) ≤ exp (x*2) →
    ∀ C ⊆ (Ioc y Z).filter Nat.Prime, ∀ a : ℝ, x-W ≤ a →
      recMass (badWindow C a x δ (fun p => c/log p^2)) ≤ ε*(P C/x) := by
  let B := 1+δ⁻¹*c
  have hB : 0 < B := by dsimp [B]; positivity
  let A := log (2/(1/4:ℝ))+1
  have hA : 0 < A := by dsimp [A]; positivity
  have hmass := (dilated_window_mass (a:=(1/4:ℝ)) (b:=2) (by norm_num) (by norm_num)).eventually
    (gt_mem_nhds (show log (2/(1/4:ℝ)) < A by dsimp [A]; linarith))
  have ly := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have near := (ly.inv_tendsto_atTop.const_mul (B*cap W)).eventually (gt_mem_nhds (show B*cap W*0 < ε/2 by linarith))
  have far := ((tendsto_inv_atTop_zero : Tendsto (fun x:ℝ => x⁻¹) atTop (𝓝 0)).const_mul
    (B*16*A)).eventually (gt_mem_nhds (show B*16*A*0 < ε/2 by linarith))
  obtain ⟨p₀,hp₀⟩ := eventually_atTop.mp square_le_wt
  filter_upwards [near,eventually_ge_atTop p₀,eventually_ge_atTop 2] with y hy hp hy2
  filter_upwards [far,hmass,eventually_gt_atTop 0] with x hx hM hx0
  intro Z hZ C hC a ha
  have hpC : ∀ p ∈ C, p.Prime := fun _ h => (mem_filter.mp (hC h)).2
  let V := cap W*(P C/x)*(log y)⁻¹ + (16/x^2*P C)*A
  let window (d : ℝ) := windowMass C (a-d) (x-d)
  have wpos (d : ℝ) : 0 ≤ window d := sum_nonneg (fun _ _ => by positivity)
  have line (d : ℕ → ℝ) (hd : ∀ p ∈ C, d p ≤ 2*log p) :
      (∑ p ∈ C, wt p*window (d p)) ≤ V := wt_window hy2 hC hx0 ha hZ A hM.le d hd
  have sq : (∑ p ∈ C, ((p^2:ℕ):ℝ)⁻¹*window (log (p^2:ℕ))) ≤ V := by
    apply le_trans _ (line (fun p => log (p^2:ℕ)) (fun p _ => by simp [Nat.cast_pow,log_pow]))
    exact sum_le_sum (fun p h => mul_le_mul_of_nonneg_right (hp₀ _ (hp.trans
      (mem_Ioc.mp (mem_filter.mp (hC h)).1).1.le)) (wpos _))
  have disp : (∑ p ∈ C, c/log p^2*((p:ℝ)⁻¹*window (log p))) ≤ c*V := by
    have eq : (∑ p ∈ C, c/log p^2*((p:ℝ)⁻¹*window (log p))) =
        c * ∑ p ∈ C, wt p*window (log p) := by
      rw [mul_sum]; apply sum_congr rfl; intro p _; simp [wt,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
    rw [eq]
    exact mul_le_mul_of_nonneg_left (line (fun p => log p) (fun p _ => by linarith [log_natCast_nonneg p])) hc
  have hb := bad_window_bound C hpC a x hδ (fun p => c/log p^2) (fun p _ => div_nonneg hc (sq_nonneg _))
  apply hb.trans ((add_le_add sq (mul_le_mul_of_nonneg_left disp (inv_nonneg.mpr hδ.le))).trans _)
  change B*cap W*(log (y:ℝ))⁻¹ < ε/2 at hy
  change B*16*A*x⁻¹ < ε/2 at hx
  have h := add_le_add hy.le hx.le
  have hn := mul_le_mul_of_nonneg_right h (div_nonneg (P_pos C).le hx0.le)
  calc
    V+δ⁻¹*(c*V) = (B*cap W*(log y)⁻¹+B*16*A*x⁻¹)*(P C/x) := by dsimp [V,B]; ring
    _ ≤ _ := by simpa only [add_halves] using hn

theorem old_bad_negligible {c δ ε : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ Z : ℕ, (Z:ℝ) ≤ exp (x*2) →
    ∀ C ⊆ (Ioc y Z).filter Nat.Prime, ∀ a : ℝ, x-1 ≤ a →
      recMass (badWindow C a x δ (fun p => c/log p^2)) ≤ ε*(P C/x) :=
  old_bad_negligible_of_width 1 hc hδ hε

#print axioms old_bad_negligible_of_width
#print axioms old_bad_negligible
end
end Erdos490Transfer
