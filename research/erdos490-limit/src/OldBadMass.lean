import OldWindow
import EulerScale

/-! Local old harmonic loss from squares and displacement. The two finite
union bounds retain the shifted cutoff for each prime power. -/
namespace Erdos490Transfer
open Finset Filter Real Shift490
noncomputable section
open Classical

def recMass (S : Finset ℕ) := ∑ m ∈ S, (m:ℝ)⁻¹

lemma window_cap (C : Finset ℕ) (a b : ℝ) :
    windowMass C a b ≤ exp (b-a)*F C b := by
  rw [F_eq_semigroup]
  calc
    _ ≤ ∑ _m ∈ oldWindow C a b, exp (-a) := by
      apply sum_le_sum
      intro m hm
      obtain ⟨ha,hl,_⟩ := mem_oldWindow.mp hm
      have he := Real.exp_le_exp.mpr hl.le
      rw [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero ha.1)] at he
      rw [Real.exp_neg]
      exact inv_anti₀ (exp_pos _) he
    _ ≤ (exp (-a))*((semigroup C ⌊exp b⌋₊).card:ℝ) := by
      rw [sum_const,nsmul_eq_mul,mul_comm]
      gcongr
      exact filter_subset (fun m : ℕ => a < log m) (semigroup C ⌊exp b⌋₊)
    _ = _ := by rw [← mul_assoc,← exp_add]; ring_nf

lemma window_total (C : Finset ℕ) (hp : ∀ p ∈ C, p.Prime) (a b : ℝ) :
    windowMass C a b ≤ P C := by
  calc
    _ ≤ truncMass C ⌊exp b⌋₊ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => by positivity)
    _ ≤ euler C := truncMass_le_euler hp _
    _ = _ := by simp [P,euler,filter_true_of_mem hp]

theorem window_multiple {C d} (hd : Active C d) (a b : ℝ) :
    recMass ((oldWindow C a b).filter (d ∣ ·)) =
    (d:ℝ)⁻¹ * windowMass C (a-log d) (b-log d) := by
  have hd0 := Nat.pos_of_ne_zero hd.1
  let V := oldWindow C (a-log d) (b-log d)
  have logs {x : ℕ} (hx : Active C x) : log ((x*d:ℕ):ℝ) = log x + log d := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hx.1) (by exact_mod_cast hd.1)]
  have eq : ((oldWindow C a b).filter (d ∣ ·)) = V.image (· * d) := by
    ext m
    constructor
    · intro hm
      obtain ⟨hm,hm'⟩ := mem_filter.mp hm
      obtain ⟨hc,hl,hr⟩ := mem_oldWindow.mp hm
      have hq := Nat.mem_factoredNumbers_of_dvd hc (Nat.div_dvd_of_dvd hm')
      have he := Nat.div_mul_cancel hm'
      have hlog := logs hq
      rw [he] at hlog
      exact mem_image.mpr ⟨m/d,mem_oldWindow.mpr ⟨hq,by linarith,by linarith⟩,he⟩
    · intro hm
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hm
      obtain ⟨hc,hl,hr⟩ := mem_oldWindow.mp hx
      exact mem_filter.mpr ⟨mem_oldWindow.mpr ⟨Nat.mul_mem_factoredNumbers hc hd,
        by rw [logs hc]; linarith,by rw [logs hc]; linarith⟩,dvd_mul_left ..⟩
  rw [recMass,eq,sum_image (fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_right hd0 he),windowMass,mul_sum]
  simp [V]

def badWindow (C : Finset ℕ) (a b δ : ℝ) (e : ℕ → ℝ) :=
  (oldWindow C a b).filter (fun m => (∃ p ∈ C, p^2 ∣ m) ∨
    δ ≤ ∑ p ∈ C with p ∣ m, e p)

theorem bad_window_bound (C : Finset ℕ) (hp : ∀ p ∈ C, p.Prime) (a b : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (e : ℕ → ℝ) (he : ∀ p ∈ C, 0 ≤ e p) :
    recMass (badWindow C a b δ e) ≤
      (∑ p ∈ C, ((p^2:ℕ):ℝ)⁻¹ * windowMass C (a-log (p^2:ℕ)) (b-log (p^2:ℕ))) +
      δ⁻¹ * ∑ p ∈ C, e p*((p:ℝ)⁻¹ * windowMass C (a-log p) (b-log p)) := by
  let W := oldWindow C a b
  let mult (p m : ℕ) : ℝ := if p ∣ m then (m:ℝ)⁻¹ else 0
  have active {p} (hm : p ∈ C) : Active C p := by
    simp [Active,Nat.mem_factoredNumbers,Nat.primeFactorsList_prime (hp _ hm),(hp _ hm).ne_zero,hm]
  have sum_mult {p} (hm : Active C p) :
      (∑ m ∈ W, mult p m) = (p:ℝ)⁻¹ * windowMass C (a-log p) (b-log p) := by
    rw [← window_multiple hm]
    simp [recMass,sum_filter,mult,W]
  have m0 (p m : ℕ) : 0 ≤ mult p m := by dsimp [mult]; split <;> positivity
  have squareSum m : 0 ≤ ∑ p ∈ C, mult (p^2) m := sum_nonneg (fun _ _ => m0 ..)
  have eSum m : 0 ≤ ∑ p ∈ C, e p * mult p m :=
    sum_nonneg fun p h => mul_nonneg (he p h) (m0 ..)
  calc
    _ ≤ ∑ m ∈ W, ((∑ p ∈ C, mult (p^2) m) + δ⁻¹*(∑ p ∈ C, e p*mult p m)) := by
      unfold recMass badWindow
      rw [sum_filter]
      apply sum_le_sum
      intro m _
      split_ifs with hbad
      · rcases hbad with ⟨p,hp',hd⟩|hl
        · have h := single_le_sum (fun p (_ : p ∈ C) => m0 (p^2) m) hp'
          rw [show mult (p^2) m = (m:ℝ)⁻¹ from if_pos hd] at h
          exact h.trans (le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hδ.le) (eSum m)))
        · have hh := mul_le_mul_of_nonneg_right hl (show 0 ≤ (m:ℝ)⁻¹ by positivity)
          have eq : (∑ p ∈ C with p ∣ m, e p)*(m:ℝ)⁻¹ = ∑ p ∈ C, e p*mult p m := by
            rw [sum_mul,sum_filter]
            exact sum_congr rfl fun p _ => by simp [mult,mul_ite]
          rw [eq] at hh
          have h := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hδ.le)
          rw [← mul_assoc,inv_mul_cancel₀ hδ.ne',one_mul] at h
          linarith [squareSum m]
      · exact add_nonneg (squareSum m) (mul_nonneg (inv_nonneg.mpr hδ.le) (eSum m))
    _ = _ := by
      rw [sum_add_distrib,← mul_sum,sum_comm]
      congr 1
      · apply sum_congr rfl
        intro p h
        exact sum_mult (by simpa [pow_two] using Nat.mul_mem_factoredNumbers (active h) (active h))
      · rw [sum_comm]
        apply congrArg (δ⁻¹ * ·)
        apply sum_congr rfl
        intro p h
        rw [← mul_sum,sum_mult (active h)]

#print axioms bad_window_bound
end
end Erdos490Transfer
