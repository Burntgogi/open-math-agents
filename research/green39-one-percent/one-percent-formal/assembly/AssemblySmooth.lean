import AssemblyModel
import SplitLaws
import PaperConstants

/-! Transfer of the capped-law estimate to the ordered-pair probability from §2. -/

open Finset Real Filter Topology
open scoped Pointwise Classical
namespace Green39.Assembly
noncomputable section
open Split OnePercent.Fourier
variable {p : ℕ} [NeZero p]

theorem probability_eq_splitProb {α : Type*} [DecidableEq α] (s : Finset α) (a b : ℕ)
    (E : Finset α → Finset α → Prop) :
    probability (orderedPairs s a b) (fun q => E q.1 q.2) = Smooth.splitProb s a b E := by
  rw [probability_eq_mean_first]
  unfold Smooth.splitProb Smooth.splitMean
  simp_rw [Smooth.sm_event]
  rfl

def smoothBound (p k : ℝ) := 2*exp (-k/320000000000000000) +
  p*exp (10^24 - (10^24/2)*sqrt k) + p*exp (-(9:ℝ)/10000*sqrt k)

theorem one_law (μ : Law p) (hn : ∀ z, 0 ≤ μ z) (hm : ∑ z, μ z = 1)
    (hc : ∀ z, μ z ≤ 2/(10^24*(p.sqrt:ℝ))) (hk : 100000 ≤ p.sqrt) :
    probability (orderedPairs (univ:Points p) (half p.sqrt) (rest p.sqrt)) (fun q => ¬typical μ q)
      ≤ smoothBound p p.sqrt := by
  let k := p.sqrt
  let a := half k
  let b := rest k
  let c := (51:ℝ)/(100*k)
  have hab : a+b=k := by dsimp [a,b,half,rest]; omega
  have hpc : Fintype.card (ZMod p) ≤ 2*k^2 := by
    rw [ZMod.card]
    have h := Nat.lt_succ_sqrt' p
    dsimp [k]
    nlinarith [Nat.mul_le_mul_left p.sqrt (show 3 ≤ p.sqrt by omega)]
  have h := Smooth.paper_equation_four (G:=ZMod p) ({μ} : Finset (Law p)) id (k:=k) (a:=a) (b:=b)
    (by dsimp [k]; omega) hab (by dsimp [a,k,half]; omega) (by dsimp [b,k,rest]; omega)
    (by dsimp [a,half]; omega) (by simpa [k] using Nat.sqrt_le' p) hpc
    (by simpa using hn) (by simpa using hm) (by simpa using hc)
  let E (A B : Points p) := (k:ℝ)/100000000 < Smooth.l1 μ b B ∨
    ∃ v, (1:ℝ)/1000 < ∑ z ∈ B, Smooth.excess μ A c v z
  have he : probability (orderedPairs (univ:Points p) a b) (fun q => E q.1 q.2) ≤ smoothBound p k := by
    rw [probability_eq_splitProb]
    simpa [E,c,smoothBound,ZMod.card] using h
  refine (probability_mono ?_).trans he
  intro q hq hbad
  have h2 := (mem_orderedPairs.mp hq).2.2.2.1
  by_contra hnot
  change ¬ (_ ∨ _) at hnot
  push Not at hnot
  apply hbad
  have hconv (u : ZMod p) : convolution (indicator q.2) μ u = Smooth.conv μ q.2 u := convolution_indicator _ _ _
  have hsm (z : ZMod p) : smoothed q.1 μ z = Smooth.conv (fun t => μ (-t)) q.1 z := by
    simp only [smoothed_eq_convolution,convolution_indicator,Smooth.conv]
  constructor
  · rw [show (0.00000001:ℝ)*(p.sqrt:ℝ) = k/100000000 by dsimp [k]; ring]
    simpa only [hconv,h2,Smooth.l1,ZMod.card] using hnot.1
  · intro v
    simpa only [Smooth.excess,← hsm,show c = 0.51/(p.sqrt:ℝ) by dsimp [c,k]; ring,
      show (1:ℝ)/1000 = 0.001 by norm_num] using hnot.2 v

theorem power_margin {a b : ℝ} (h : a < b) (M : ℝ) :
    ∀ᶠ y : ℝ in atTop, M*y^a ≤ y^b := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr h)).eventually_ge_atTop M,
    eventually_gt_atTop (0:ℝ)] with y hM hy
  calc
    _ ≤ y^(b-a)*y^a := mul_le_mul_of_nonneg_right hM (rpow_nonneg hy.le _)
    _ = _ := by rw [←rpow_add hy]; congr 1; ring

theorem smoothBound_eventually :
    ∀ᶠ k : ℝ in atTop, ∀ p : ℝ, 0 ≤ p → p ≤ 2*k^2 → smoothBound p k ≤ exp (-(k^(0.48:ℝ))) := by
  filter_upwards [eventually_ge_atTop (2:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<0.48)).eventually_ge_atTop 4,
    power_margin (a:=0.48) (b:=1) (by norm_num) (10^19),
    power_margin (a:=0.48) (b:=0.5) (by norm_num) 10000,
    (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<0.48)).def (by norm_num : (0:ℝ)<1/3)]
    with k hk hz hlinear hroot hlog p hp hpc
  let z := k^(0.48:ℝ)
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hk
  rw [rpow_one] at hlinear
  have hsqrt : (10000:ℝ)*z ≤ sqrt k := by simpa only [Real.sqrt_eq_rpow,show (1:ℝ)/2=0.5 by norm_num] using hroot
  have hl : log k ≤ (1/3:ℝ)*z := by
    change ‖log k‖ ≤ (1/3:ℝ)*‖k^(0.48:ℝ)‖ at hlog
    simpa [z,Real.norm_of_nonneg (log_nonneg ((by norm_num : (1:ℝ) ≤ 2).trans hk)),Real.norm_of_nonneg (rpow_nonneg hk0.le _)] using hlog
  have hpz : p ≤ exp z := by
    calc
      _ ≤ k^3 := hpc.trans (by nlinarith [mul_nonneg (sq_nonneg k) (sub_nonneg.mpr hk)])
      _ = exp (3*log k) := by rw [show (3:ℝ) = (↑(3:ℕ):ℝ) by norm_num,exp_nat_mul,exp_log hk0]
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  change 4 ≤ z at hz
  change (10:ℝ)^19*z ≤ k at hlinear
  have h₁ : exp (-k/320000000000000000) ≤ exp (-2*z) := exp_le_exp.mpr (by linarith only [hlinear,hz])
  have prod (u : ℝ) (hu : u ≤ -3*z) : p*exp u ≤ exp (-2*z) := by
    apply (mul_le_mul_of_nonneg_right hpz (exp_pos _).le).trans
    rw [←exp_add]; exact exp_le_exp.mpr (by linarith)
  have h₂ := prod (10^24 - (10^24/2)*sqrt k) (by linarith only [hsqrt,hz])
  have h₃ := prod (-(9:ℝ)/10000*sqrt k) (by linarith only [hsqrt,hz])
  have h₄ : (4:ℝ) ≤ exp z := by linarith only [Real.add_one_le_exp z,hz]
  unfold smoothBound
  calc
    _ ≤ 4*exp (-2*z) := by linarith only [h₁,h₂,h₃]
    _ ≤ exp z * exp (-2*z) := mul_le_mul_of_nonneg_right h₄ (exp_pos _).le
    _ = _ := by rw [←exp_add]; congr 1; change z + -2*z = -z; ring

end
end Green39.Assembly