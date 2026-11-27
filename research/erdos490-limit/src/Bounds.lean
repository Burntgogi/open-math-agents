import Arithmetic

noncomputable section
namespace Shift490
open Finset Filter

/- The finite Chebyshev argument below is adapted from ../stability-bounded/H3.lean. -/
private noncomputable def smooth (n : ℕ) (P : ℕ → Prop) : Finset ℕ := by
  classical
  exact (Icc 1 n).filter (fun m => ∀ p, p.Prime → p ∣ m → P p)

private lemma mem_smooth {n m : ℕ} {P : ℕ → Prop} :
    m ∈ smooth n P ↔ (1 ≤ m ∧ m ≤ n) ∧ ∀ p, Nat.Prime p → p ∣ m → P p := by
  classical
  simp [smooth]

private noncomputable def truncatedMass (s : Finset ℕ) := ∑ m ∈ s, (m : ℝ)⁻¹

private lemma transport {α β : Type*} (s : Finset α) (t : Finset β)
    (f : α → β) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b)
    (hm : ∀ a ∈ s, f a ∈ t) (hi : Set.InjOn f s) :
    ∑ a ∈ s, g (f a) ≤ ∑ b ∈ t, g b := by
  classical
  rw [← sum_image hi]
  apply sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr hm)
  exact fun b _ _ => hg b

private lemma log_sum (n : ℕ) (P : ℕ → Prop) :
    ∑ m ∈ smooth n P, Real.log m ≤
      ((Real.log 4 + 4) * n) * truncatedMass (smooth n P) := by
  classical
  let s := smooth n P
  let U := s.sigma (fun m => m.divisors)
  let V := s.sigma (fun v => Ioc 0 ⌊(n : ℝ) / v⌋₊)
  let f (x : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ := ⟨x.1 / x.2, x.2⟩
  have data {x : Σ _ : ℕ, ℕ} (hx : x ∈ U) :
      x.1 ∈ s ∧ x.2 ∣ x.1 ∧ 0 < x.2 ∧ 0 < x.1 / x.2 := by
    obtain ⟨hm,hd⟩ := mem_sigma.mp hx
    have h0 := Nat.pos_of_mem_divisors hd
    exact ⟨hm, Nat.dvd_of_mem_divisors hd, h0,
      Nat.div_pos (Nat.le_of_dvd (mem_smooth.mp hm).1.1 (Nat.dvd_of_mem_divisors hd)) h0⟩
  have hm : ∀ x ∈ U, f x ∈ V := by
    intro x hx
    obtain ⟨hs,hd,hp,hq⟩ := data hx
    obtain ⟨⟨_,hle⟩,hall⟩ := mem_smooth.mp hs
    refine mem_sigma.mpr ⟨mem_smooth.mpr ⟨⟨hq, (Nat.div_le_self ..).trans hle⟩,
      fun p hpr hdv => hall p hpr (hdv.trans (Nat.div_dvd_of_dvd hd))⟩, ?_⟩
    refine mem_Ioc.mpr ⟨hp, Nat.le_floor ((le_div_iff₀ (by exact_mod_cast hq)).mpr ?_)⟩
    exact_mod_cast (show x.2 * (x.1 / x.2) ≤ n by rwa [Nat.mul_div_cancel' hd])
  have hi : Set.InjOn f U := by
    intro x hx y hy h
    have he := congrArg (fun z : Σ _ : ℕ, ℕ => z.1 * z.2) h
    change x.1 / x.2 * x.2 = y.1 / y.2 * y.2 at he
    rw [Nat.div_mul_cancel (data hx).2.1, Nat.div_mul_cancel (data hy).2.1] at he
    have he' := congrArg (fun z : Σ _ : ℕ, ℕ => z.2) h
    exact Sigma.ext he (heq_of_eq he')
  calc
    _ = ∑ x ∈ U, ArithmeticFunction.vonMangoldt (f x).2 := by
      simp [U, s, sum_sigma, f, ArithmeticFunction.vonMangoldt_sum]
    _ ≤ ∑ y ∈ V, ArithmeticFunction.vonMangoldt y.2 :=
      transport U V f _ (fun _ => ArithmeticFunction.vonMangoldt_nonneg) hm hi
    _ = ∑ v ∈ s, Chebyshev.psi ((n : ℝ) / v) := by rw [Finset.sum_sigma]; rfl
    _ ≤ ∑ v ∈ s, (Real.log 4 + 4) * ((n : ℝ) / v) :=
      sum_le_sum fun v _ => Chebyshev.psi_le_const_mul_self (by positivity)
    _ = _ := by simp [s, truncatedMass, mul_sum, div_eq_mul_inv, mul_assoc]

theorem F_nonneg (S w) : 0 ≤ F S w := tsum_nonneg atom_nonneg

private theorem countSet_eq (S w) : countSet S w = smooth ⌊Real.exp w⌋₊ (· ∈ S) := by
  classical
  ext n
  simp only [countSet, smooth, mem_filter, mem_range, Nat.lt_succ_iff, mem_Icc]
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨⟨Nat.pos_of_ne_zero hn.1,h⟩,Nat.mem_factoredNumbers'.mp hn⟩
  · rintro ⟨⟨_,h⟩,hn⟩
    exact ⟨h,Nat.mem_factoredNumbers'.mpr hn⟩

theorem F_le_one (S w) : F S w ≤ 1 := by
  classical
  rw [F_eq_card,countSet_eq,Real.exp_neg]
  have h := card_le_card (filter_subset (fun m => ∀ p, Nat.Prime p → p ∣ m → p ∈ S)
    (Icc 1 ⌊Real.exp w⌋₊))
  change (smooth ⌊Real.exp w⌋₊ (· ∈ S)).card ≤ _ at h
  simp at h
  rw [inv_mul_eq_div, div_le_one (Real.exp_pos _)]
  exact (Nat.cast_le.mpr h).trans (Nat.floor_le (Real.exp_pos w).le)

def K₀ : ℝ := Real.log 4 + 5
lemma K₀_pos : 0 < K₀ := by unfold K₀; positivity

theorem counting_bound (S w) (hw : 0 < w) : F S w ≤ K₀ * P S / w := by
  classical
  let n := ⌊Real.exp w⌋₊
  let t := smooth n (· ∈ S)
  have hm : ∀ k ∈ t, k ∈ Integers S := fun k h => Nat.mem_factoredNumbers'.mpr (mem_smooth.mp h).2
  have hmP : truncatedMass t ≤ P S := by
    let u := t.subtype (· ∈ Integers S)
    have he : ∑ a ∈ u, ((a.val:ℕ):ℝ)⁻¹ = truncatedMass t := by
      exact sum_subtype_of_mem (s := t) (fun n : ℕ => (n:ℝ)⁻¹) hm
    rw [← he, ← (harmonic_sum S).tsum_eq]
    exact (harmonic_sum S).summable.sum_le_tsum u (fun _ _ => by positivity)
  have hnum : (n:ℝ) ≤ Real.exp w := Nat.floor_le (Real.exp_pos _).le
  have hl (k : ℕ) (hk : k ∈ t) : w ≤ Real.log k + Real.exp w * (k:ℝ)⁻¹ := by
    have hk' : 0 < (k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (hm k hk).1
    have := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos w) hk')
    rw [Real.log_div (Real.exp_pos w).ne' hk'.ne', Real.log_exp, div_eq_mul_inv] at this
    linarith
  have hh := sum_le_sum hl
  simp only [sum_const, nsmul_eq_mul, sum_add_distrib, ← mul_sum] at hh
  have hlog := log_sum n (· ∈ S)
  have hmass : 0 ≤ truncatedMass t := sum_nonneg fun _ _ => by positivity
  change (∑ k ∈ t, Real.log k) ≤ ((Real.log 4 + 4)*n)*truncatedMass t at hlog
  have hc : (Real.log 4 + 4)*n ≤ (Real.log 4 + 4)*Real.exp w :=
    mul_le_mul_of_nonneg_left hnum (by positivity)
  rw [F_eq_card,countSet_eq,Real.exp_neg, inv_mul_eq_div, div_le_div_iff₀ (Real.exp_pos _) hw]
  change t.card * w ≤ _
  calc
    _ ≤ ((Real.log 4 + 4)*Real.exp w)*truncatedMass t + Real.exp w * truncatedMass t := by
      change (t.card : ℝ)*w ≤ (∑ k ∈ t, Real.log k) + Real.exp w * truncatedMass t at hh
      linarith [mul_le_mul_of_nonneg_right hc hmass]
    _ = (K₀ * truncatedMass t) * Real.exp w := by unfold K₀; ring
    _ ≤ _ := by gcongr; exact K₀_pos.le

theorem slow_decrease (S) {w v : ℝ} (h : w ≤ v) : F S w ≤ Real.exp (v-w) * F S v := by
  rw [F_eq_card,F_eq_card,← mul_assoc,← Real.exp_add]
  have hc : countSet S w ⊆ countSet S v := by
    intro n hn
    obtain ⟨h1,h2⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_range.mpr (lt_of_lt_of_le (mem_range.mp h1)
      (Nat.succ_le_succ (Nat.floor_mono (Real.exp_le_exp.mpr h)))),h2⟩
  rw [show v-w + -v = -w by ring]
  gcongr

#print axioms counting_bound
#print axioms slow_decrease
end Shift490
