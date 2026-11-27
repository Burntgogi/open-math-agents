import LargeLabelTransfer
import BlueStrips
import BlueKernel
import KernelRange
import Cutoff
import Cells

/-! The kernel strip sum relative to the full removed Euler factor. -/
namespace Erdos490Transfer
open Asymptotics Finset Filter Real MeasureTheory Shift490 Erdos490Smooth Erdos490PrimeCells
open scoped Topology
noncomputable section
open Classical

def width (y : ℕ) := boundary Mertens.M (y+1)
lemma width_pos (y : ℕ) : 0 < width y := exp_pos _

lemma segment_eq (Y y : ℕ) : primes Y y = smoothLabels (Y-1) y := by
  ext p
  simp only [primes,smoothLabels,mem_filter,mem_Icc,mem_Ioc,Nat.floor_natCast]
  constructor <;> intro h
  · exact ⟨⟨by have := h.2.pos; omega,h.1.2⟩,h.2⟩
  · exact ⟨⟨by omega,h.1.2⟩,h.2⟩

private lemma prod_pos' (n : ℕ) : 0 < smallProduct n := by
  rw [smallProduct_eq_local]
  exact Finset.prod_pos (fun p hp => by
    have h : 1 < (p:ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt
    exact sub_pos.mpr ((inv_lt_one₀ (by linarith)).mpr h))

private lemma before_eq (n : ℕ) : reciprocalBefore (n+1) =
    ∑ p ∈ (Ioc 0 n).filter Nat.Prime, (p:ℝ)⁻¹ := by
  rw [reciprocalBefore,Nat.range_succ_eq_Icc_zero]
  simp only [sum_filter]
  rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
  simp

theorem blue_gain_eq {Y y : ℕ} (h : Y ≤ y) :
    exp eulerMascheroniConstant*smallProduct (Y-1)*width y / P (primes Y y) =
    cutoffFactor y := by
  have hk : Y-1 ≤ ⌊(y:ℝ)⌋₊ := by rw [Nat.floor_natCast]; omega
  rw [segment_eq,segment_product hk,Nat.floor_natCast,div_div_eq_mul_div]
  unfold cutoffFactor width boundary
  rw [Nat.floor_natCast,before_eq]
  simp only [one_div]
  change _ = smallProduct y * _ * _
  field_simp [(prod_pos' (Y-1)).ne']

private lemma smallProduct_zero : Tendsto smallProduct atTop (𝓝 0) := by
  have h := (((isLittleO_one_iff ℝ).mp Mertens.E₃.bound').comp tendsto_natCast_atTop_atTop).rexp
  have l := (h.const_mul (exp (-eulerMascheroniConstant))).div_atTop
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply l.congr'
  filter_upwards [eventually_gt_atTop (1:ℕ)] with y hy
  change exp (-eulerMascheroniConstant)*exp (Mertens.E₃ (y:ℝ))/log (y:ℝ) = smallProduct y
  simpa only [Nat.floor_natCast,one_div,smallProduct] using
    (Mertens.prod_one_minus_div_prime_eq (by exact_mod_cast hy : 1 < (y:ℝ))).symm

/-- At every sufficiently large y a finite strip sum approximates precisely
the removed Euler mass for the original threshold Y. -/
theorem blue_strip_normalized (Y : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop, ∃ D : ℕ, 1 ≤ D ∧
      let T := ∑ j ∈ Icc 1 D, smoothKernel (Y-1) (width y) (width_pos y) (j+1)
      (1-ε)*P (primes Y y) ≤ T ∧ T ≤ (1+ε)*P (primes Y y) := by
  let V := smallProduct (Y-1)
  have hV := prod_pos' (Y-1)
  have lim := cutoffFactor_tendsto.comp tendsto_natCast_atTop_atTop
  have err := (smallProduct_zero.const_mul (2:ℝ)).eventually_lt_const (show 2*0<ε/3 by linarith)
  filter_upwards [eventually_ge_atTop Y,lim.eventually_const_lt (show 1-ε/3 < 1 by linarith),
    lim.eventually_lt_const (show 1 < 1+ε by linarith),err] with y hy hlo hhi hsmall
  let H := P (primes Y y)
  have hH : 0 < H := P_pos _
  let J := exp eulerMascheroniConstant*V*width y
  have he : J/H = cutoffFactor y := blue_gain_eq hy
  change 1-ε/3 < cutoffFactor y at hlo
  change cutoffFactor y < 1+ε at hhi
  rw [← he,lt_div_iff₀ hH] at hlo
  rw [← he,div_lt_iff₀ hH] at hhi
  have eH : 0 < ε/3*H := by positivity
  have hk : Y-1 ≤ ⌊(y:ℝ)⌋₊ := by rw [Nat.floor_natCast]; omega
  have hvh : smallProduct y*H=V := by
    dsimp [H,V]
    rw [segment_eq,segment_product hk,Nat.floor_natCast]
    field_simp [(prod_pos' y).ne']
  have lowV := mul_le_mul_of_nonneg_right hsmall.le hH.le
  obtain ⟨D,hD,hlo',hhi'⟩ := exists_strip_sum_bounds (smoothKernel_antitone (Y-1) (width_pos y))
    (fun _ hh => smoothKernel_range (Y-1) (width_pos y) hh)
    (smoothKernel_mass (Y-1) (width_pos y)).1 eH
  rw [(smoothKernel_mass (Y-1) (width_pos y)).2] at hlo' hhi'
  refine ⟨D,hD,?_,hhi'.trans hhi.le⟩
  change J-2*V-ε/3*H ≤ _ at hlo'
  rw [mul_assoc,hvh] at lowV
  linarith only [hlo,hlo',lowV]

#print axioms blue_strip_normalized
end
end Erdos490Transfer
