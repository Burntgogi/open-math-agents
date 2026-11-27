import StableTransfer

/-! Extract a bounded old sparse-color shift after peeling off a fixed
finite prime set. The bounds are uniform in the complementary prime color. -/
namespace Erdos490Transfer
open Finset Filter Real Shift490
noncomputable section
open Classical
open scoped Topology

private lemma moment_nonneg (D) : 0 ≤ moment D :=
  tsum_nonneg fun a => mul_nonneg (hnonneg a) (exp_pos _).le

/-- Finite support for the retained part of the old harmonic probability. -/
private lemma finite_peak (S T : Finset ℕ) (w J : ℝ) (hJ : 0 ≤ J) :
    ∃ v : ℝ, 0 ≤ v ∧ v ≤ J ∧ ∀ a : Integers S, logN a ≤ J →
      F T (w-logN a) ≤ F T (w-v) := by
  let choices := semigroup S ⌊exp J⌋₊
  have h1 : 1 ∈ choices := mem_semigroup.mpr ⟨by simp [Active,Nat.mem_factoredNumbers],
    Nat.le_floor (by simpa using Real.one_le_exp hJ)⟩
  obtain ⟨u,hu,hm⟩ := choices.exists_max_image (fun x => F T (w-log x)) ⟨1,h1⟩
  have hu0 := Nat.pos_of_ne_zero (mem_semigroup.mp hu).1.1
  refine ⟨log u,log_natCast_nonneg _,(log_le_iff_le_exp (by exact_mod_cast hu0)).mpr
    ((Nat.le_floor_iff (exp_pos _).le).mp (mem_semigroup.mp hu).2),?_⟩
  intro a ha
  exact hm _ (mem_semigroup.mpr ⟨a.property,Nat.le_floor ((log_le_iff_le_exp (nat_pos a)).mp ha)⟩)

/-- With J fixed one can estimate the near, middle and exponential-tail
regions in the convolution simultaneously, for every old shift |h| ≤ H. -/
private theorem sparse_finite_bound {S T : Finset ℕ} (hd : Disjoint S T)
    {H h J L : ℝ} (hL : 0 < L) (hsize : 4*H ≤ L) (hh : |h| ≤ H) (hJ : 0 ≤ J) :
    ∃ v : ℝ, 0 ≤ v ∧ v ≤ J ∧
      F (S ∪ T) (L+h) / P S ≤ F T (L+h-v) +
        (4*K₀*P T/L)*moment S*exp (-J/2) + moment S*exp (-L/4) := by
  obtain ⟨v,hv0,hv,hmax⟩ := finite_peak S T (L+h) J hJ
  let M := 4*K₀*P T/L
  have hM : 0 ≤ M := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) K₀_pos.le) (P_pos _).le) hL.le
  let coef := M*exp (-J/2)+exp (-L/4)
  have hc : 0 ≤ coef := add_nonneg (mul_nonneg hM (exp_pos _).le) (exp_pos _).le
  have point (a : Integers S) :
      F T (L+h-logN a) ≤ F T (L+h-v) + exp (logN a/2)*coef := by
    have hpos := F_nonneg T (L+h-v)
    by_cases near : logN a ≤ J
    · exact (hmax a near).trans (le_add_of_nonneg_right (mul_nonneg (exp_pos _).le hc))
    by_cases mid : logN a ≤ L/2
    · have h4 : L/4 ≤ L+h-logN a := by linarith [(abs_le.mp hh).1]
      have hcut : 0 < L+h-logN a := by linarith
      have hcap : F T (L+h-logN a) ≤ M := (counting_bound _ _ hcut).trans
        ((div_le_div_iff₀ hcut hL).mpr (by nlinarith [mul_nonneg (mul_nonneg K₀_pos.le (P_pos T).le) (show 0 ≤ 4*(L+h-logN a)-L by linarith)]))
      have e : 1 ≤ exp (logN a/2)*exp (-J/2) := by rw [← exp_add]; apply one_le_exp; linarith
      dsimp only [coef]
      nlinarith only [hcap,hpos,mul_le_mul_of_nonneg_left e hM,mul_nonneg (exp_pos (logN a/2)).le (exp_pos (-L/4)).le]
    · have e : 1 ≤ exp (logN a/2)*exp (-L/4) := by rw [← exp_add]; apply one_le_exp; linarith
      dsimp only [coef]
      nlinarith only [F_le_one T (L+h-logN a),e,hpos,mul_nonneg (exp_pos (logN a/2)).le (mul_nonneg hM (exp_pos (-J/2)).le)]
  have hsum := (harmonic_probability S).mul_right (F T (L+h-v))
  have hsum' := (half_moment S).hasSum.mul_right coef
  have htot := hasSum_le (fun a : Integers S => by
    simpa only [mul_add,mul_assoc] using mul_le_mul_of_nonneg_left (point a) (hnonneg a))
    (avg_summable (D:=S) (f:=fun x => F T (L+h-x)) (M:=1) (fun _ => ⟨F_nonneg ..,F_le_one ..⟩)).hasSum
    (hsum.add hsum')
  refine ⟨v,hv0,hv,?_⟩
  rw [normalized_convolution hd,mul_div_cancel_left₀ _ (P_pos S).ne']
  change _ ≤ F T (L+h-v)+M*moment S*exp (-J/2)+moment S*exp (-L/4)
  change _ ≤ 1*F T (L+h-v)+moment S*coef at htot
  simpa only [one_mul,coef,mul_add,← mul_assoc,mul_comm (moment S) M,add_assoc] using htot

/-- Paper estimate (6). The interval of possible shifts is independent of
the large-prime color, the old cutoff, and the maximizing cofactor offset. -/
theorem sparse_strip (S : Finset ℕ) (H ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ᶠ L : ℝ in atTop, ∀ T : Finset ℕ, Disjoint S T →
      ∀ h : ℝ, |h| ≤ H → ∃ v : ℝ, 0 ≤ v ∧ v ≤ J ∧
        F (S ∪ T) (L+h)/P S ≤ F T (L+h-v) + ε*(P T/L) := by
  have halfExp : Tendsto (fun x : ℝ => exp (-x/2)) atTop (𝓝 0) := by
    apply tendsto_exp_atBot.comp
    simpa only [neg_div,Function.comp_def,id_eq] using (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2)))
  have small := halfExp.const_mul (4*K₀*moment S)
  rw [mul_zero] at small
  obtain ⟨J,hnear,hJ⟩ := ((small.eventually (gt_mem_nhds (half_pos hε))).and (eventually_ge_atTop 0)).exists
  refine ⟨J,hJ,?_⟩
  have hquarter : Tendsto (fun L : ℝ => L/4) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  have tail : Tendsto (fun L : ℝ => L*(moment S*exp (-L/4))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hquarter).const_mul (4*moment S)
    simpa only [mul_zero] using h.congr (fun x => by
      dsimp [Function.comp_def]; rw [pow_one,neg_div]; ring)
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_ge_atTop (4*H),
    tail.eventually (gt_mem_nhds (half_pos hε))] with L hL hH htail
  intro T hd h hh
  obtain ⟨v,hv,hv',hbound⟩ := sparse_finite_bound hd hL hH hh hJ
  refine ⟨v,hv,hv',hbound.trans ?_⟩
  change 4*K₀*moment S*exp (-J/2) < ε/2 at hnear
  change L*(moment S*exp (-L/4)) < ε/2 at htail
  have hp := P_pos T
  have h1 := one_le_P T
  have h2 := mul_le_mul_of_nonneg_right hnear.le hp.le
  have h3 := le_mul_of_one_le_right (half_pos hε).le h1
  apply (mul_le_mul_iff_of_pos_left hL).mp
  simp only [neg_div] at h2 htail
  field_simp [hL.ne']
  nlinarith only [h2,htail,h3]

#print axioms sparse_strip
end
end Erdos490Transfer
