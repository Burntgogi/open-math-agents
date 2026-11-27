import BlueProducts
import BlueMoving

/-! Recovery from good old squarefree supports at every sufficiently
large prescribed *integer* cutoff, using the arithmetic smooth kernel. -/
namespace Erdos490Transfer
open Finset Filter Real Shift490 Erdos490Smooth Erdos490PrimeCells
open scoped Topology
noncomputable section
open Classical

/-- Each old support is assigned a contracted unit strip. At prescribed
target n, set t=log(n)/x. Different old supports have disjoint new products;
every residual cofactor is allowed up to its exact target cutoff. -/
theorem blue_good_recovery {C : Finset ℕ} (hc : ∀ p ∈ C, p.Prime) {b x δ : ℝ}
    (hx : 0 < x) (G : Finset (Finset ℕ)) (hG : ∀ S ∈ G, S ⊆ C)
    (e : ℕ → ℝ) (he : ∀ p ∈ C, ∀ v ∈ Set.Ioc (boundary b p) (boundary b (p+1)), |v-log p| ≤ e p)
    (good : ∀ S ∈ G, ∑ p ∈ S, e p ≤ δ) (j : Finset ℕ → ℝ)
    (hj : ∀ S ∈ G, 0 < j S) (lo : ∀ S ∈ G, x-j S-1+δ < log (∏ p ∈ S, p:ℕ))
    (hi : ∀ S ∈ G, log (∏ p ∈ S, p:ℕ) ≤ x-j S-δ)
    (k : ℕ) {w : ℝ} (hw : 0 < w)
    (sep : ∀ᶠ t : ℝ in atTop, Disjoint (bands b t C) (smoothLabels k (exp (t*w))))
    {u : ℕ} (hu : 0 < u) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      let t := log n/x
      (∑ S ∈ G, (((∏ p ∈ S, p:ℕ):ℝ)⁻¹ * smoothKernel k w hw (j S+1))) - ε ≤
        density (bands b t C ∪ smoothLabels k (exp (t*w))) n u := by
  let mass (S : Finset ℕ) := (((∏ p ∈ S, p:ℕ):ℝ)⁻¹)
  let kern (S : Finset ℕ) := smoothKernel k w hw (j S+1)
  let H := ∑ S ∈ G, mass S
  have hH : 0 ≤ H := sum_nonneg (fun _ _ => by dsimp [mass]; positivity)
  let η := ε/(2*(H+1))
  have hη : 0 < η := by dsimp [η]; positivity
  have loss : H*η ≤ ε/2 := by
    dsimp [η]
    rw [mul_div_assoc',div_le_iff₀ (by positivity)]
    nlinarith
  let massAt (t : ℝ) (S : Finset ℕ) := ∑ z ∈ newProducts b t S, (z:ℝ)⁻¹
  have lim : Tendsto (fun t => ∑ S ∈ G, massAt t S*(kern S-η)) atTop
      (𝓝 (∑ S ∈ G, mass S*(kern S-η))) := tendsto_finsetSum _ (fun S h =>
    (newProducts_mass S (fun p hp => hc p (hG S h hp)) b).mul_const _)
  have compare : (∑ S ∈ G, mass S*kern S)-ε < ∑ S ∈ G, mass S*(kern S-η) := by
    simp only [mul_sub,sum_sub_distrib,← sum_mul]
    change _ < _ - H*η
    linarith
  have scale : Tendsto (fun n : ℕ => log n/x) atTop atTop :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const hx
  have kernels := (eventually_all_finset G).mpr (fun S h =>
    blue_strip_minorant k hw (hj S h) (log_natCast_nonneg u) hη)
  filter_upwards [scale.eventually (lim.eventually_const_lt compare),scale.eventually kernels,
    scale.eventually sep,scale.eventually_gt_atTop 0,eventually_gt_atTop (0:ℕ)] with n hsum hk hh ht hn
  let t := log (n:ℝ)/x
  let U := smoothLabels k (exp (t*w))
  have pair (S : Finset ℕ) (hS : S ∈ G) (z : ℕ) (hz : z ∈ newProducts b t S) :
      kern S-η ≤ density U n (u*z) := by
    have hshift := newProduct_displacement ht (fun p hp => hc _ (hG _ hS hp)) e
      (fun p hp => he _ (hG _ hS hp)) hz
    change |log (z:ℝ)/t-log (∏ p ∈ S, p:ℕ)| ≤ ∑ p ∈ S, e p at hshift
    have hdist := (abs_le.mp (hshift.trans (good _ hS)))
    have hs : x-log (z:ℝ)/t ∈ Set.Icc (j S) (j S+1) :=
      ⟨by linarith [hi _ hS,hdist.2],by linarith [lo _ hS,hdist.1]⟩
    have h := hk S hS _ hs
    have hz0 := Nat.pos_of_ne_zero (newProduct_active (hG _ hS) hz).1
    rw [← shifted_density U hn (Nat.mul_pos hu hz0),Nat.cast_mul,
      log_mul (by exact_mod_cast hu.ne') (by exact_mod_cast hz0.ne')]
    have htx : t*x=log (n:ℝ) := div_mul_cancel₀ _ hx.ne'
    change kern S-η ≤ F U (t*(x-log z/t)-log u) at h
    rw [mul_sub,show t*(log z/t)=log z by field_simp [show t ≠ 0 from ht.ne'],htx] at h
    convert h using 2
    ring
  apply hsum.le.trans (le_trans _ (family_density_lower ht.le C U hh G hG n u))
  apply sum_le_sum
  intro S hS
  rw [show massAt t S*(kern S-η) = ∑ z ∈ newProducts b t S, (z:ℝ)⁻¹*(kern S-η) from sum_mul ..]
  exact sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (pair S hS z hz) (by positivity)

#print axioms blue_good_recovery
end
end Erdos490Transfer
