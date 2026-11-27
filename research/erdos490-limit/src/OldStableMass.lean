import OldBadEstimate
import LargeLabelTransfer
import PrimeCells

/-! Lower harmonic mass of the old good squarefree products in every
contracted unit strip near a stable old cutoff. -/
namespace Erdos490Transfer
open Finset Filter Real Shift490 Erdos490PrimeCells
noncomputable section
open Classical

def goodWindow (C : Finset ℕ) (a d δ : ℝ) (e : ℕ → ℝ) :=
  oldWindow C a d \ badWindow C a d δ e

lemma good_mass (C : Finset ℕ) (a d δ : ℝ) (e : ℕ → ℝ) :
    recMass (goodWindow C a d δ e) = windowMass C a d - recMass (badWindow C a d δ e) :=
  (sub_eq_iff_eq_add.mpr (sum_sdiff (show badWindow C a d δ e ⊆ oldWindow C a d from filter_subset ..)).symm).symm

/-- For any fixed strip radius H, every center in log(N) ± H works,
with y chosen before H. The omitted mass costs ε times P(C)/log(N). -/
theorem stable_good_strips {c δ ε : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hd : δ < 1/2) (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop, ∀ N : ℕ → ℕ, StrictMono N → ∀ C : ℕ → Finset ℕ,
      (∀ k, C k ⊆ (Ioc y (N k)).filter Nat.Prime) → RoughFlat N C →
      ∀ H : ℝ, 0 ≤ H → ∀ᶠ k in atTop, ∀ v : ℝ, |v-log (N k)| ≤ H →
        (1-2*δ)*F (C k) (log (N k)) - ε*(P (C k)/log (N k)) ≤
          recMass (goodWindow (C k) (v-1+δ) (v-δ) δ (fun p => c/log p^2)) := by
  filter_upwards [old_bad_negligible hc hδ (show 0 < ε/4 by positivity)] with y hy
  intro N hN C hC flat H hH
  obtain ⟨X,hX⟩ := eventually_atTop.mp hy
  have lim := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN.tendsto_atTop)
  have scale := flat (H+2) (by linarith) (ε/8) (by positivity)
  filter_upwards [lim.eventually_ge_atTop (max X 1+2*H+4),scale,
    hN.tendsto_atTop.eventually_gt_atTop 0] with k hk hflat hn
  let L := log (N k:ℝ)
  change max X 1+2*H+4 ≤ L at hk
  intro v hv
  change |v-L| ≤ H at hv
  have h1 := (abs_le.mp hv).1
  have h2 := (abs_le.mp hv).2
  have hlarge : 1+2*H+4 ≤ L := by linarith [le_max_right X (1:ℝ)]
  have hx : X ≤ v-δ := by linarith [le_max_left X (1:ℝ)]
  have hL : 0 < L := by linarith
  have hhalf : L/2 ≤ v-δ := by linarith
  have hvp : 0 < v-δ := by linarith
  have hnexp : (N k:ℝ) ≤ exp ((v-δ)*2) := by
    rw [← log_le_iff_le_exp (by exact_mod_cast hn)]
    change L ≤ _; linarith
  have bad := hX (v-δ) hx (N k) hnexp (C k) (hC k) (v-1+δ) (by linarith)
  have win := window_flat (C k) (by linarith : 0 ≤ v-1+δ) (by linarith : v-1+δ ≤ v-δ)
    (r:=F (C k) L) (e:=ε/8*(P (C k)/L)) (by
      intro t ht
      have h := hflat (t-L) (abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩)
      change |F (C k) (L+(t-L))-F (C k) L| ≤ _ at h
      rwa [show L+(t-L)=t by ring] at h)
  have err : P (C k)/(v-δ) ≤ 2*(P (C k)/L) := by
    rw [← mul_div_assoc,div_le_div_iff₀ hvp hL]
    nlinarith only [mul_le_mul_of_nonneg_left hhalf (P_pos (C k)).le]
  have pos : 0 ≤ ε*(P (C k)/L) := mul_nonneg hε.le (div_nonneg (P_pos _).le hL.le)
  rw [good_mass]
  change (1-2*δ)*F (C k) L - ε*(P (C k)/L) ≤ _
  have low := (abs_le.mp win).1
  nlinarith only [low,bad,mul_le_mul_of_nonneg_left err (show 0 ≤ ε/4 by positivity),
    pos,mul_nonneg hδ.le pos]

#print axioms stable_good_strips
end
end Erdos490Transfer
