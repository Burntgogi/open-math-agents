import Cofactor

/-! Local harmonic counting and packing estimates from stability-bounded/H3.lean,
adapted to normalize each color by its truncated harmonic mass. -/
namespace Erdos490Transfer.Harmonic
open Finset Filter
noncomputable section
private noncomputable def smooth (n : ℕ) (P : ℕ → Prop) : Finset ℕ := by
  classical
  exact (Icc 1 n).filter (fun m => ∀ p, p.Prime → p ∣ m → P p)

private lemma mem_smooth {n m : ℕ} {P : ℕ → Prop} :
    m ∈ smooth n P ↔ (1 ≤ m ∧ m ≤ n) ∧ ∀ p, Nat.Prime p → p ∣ m → P p := by
  classical
  simp [smooth]

private noncomputable def mass (s : Finset ℕ) := ∑ m ∈ s, (m : ℝ)⁻¹

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
      ((Real.log 4 + 4) * n) * mass (smooth n P) := by
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
    _ = _ := by simp [s, mass, mul_sum, div_eq_mul_inv, mul_assoc]

private lemma count (n : ℕ) (P : ℕ → Prop) :
    ((smooth n P).card : ℝ) * Real.log n ≤
      ((Real.log 4 + 5) * n) * mass (smooth n P) := by
  let s := smooth n P
  have h : ∀ m ∈ s, Real.log n ≤ Real.log m + (n : ℝ) * (m : ℝ)⁻¹ := by
    intro m hm
    obtain ⟨⟨ha,hb⟩,_⟩ := mem_smooth.mp hm
    have hm' : 0 < (m : ℝ) := by exact_mod_cast ha
    have hn' : 0 < (n : ℝ) := by exact_mod_cast ha.trans hb
    have := Real.log_le_sub_one_of_pos (div_pos hn' hm')
    rw [Real.log_div hn'.ne' hm'.ne', div_eq_mul_inv] at this
    linarith
  have hh := sum_le_sum h
  simp only [sum_const, nsmul_eq_mul, sum_add_distrib, ← mul_sum] at hh
  change (s.card : ℝ) * Real.log n ≤ (∑ m ∈ s, Real.log m) + n * mass s at hh
  linarith only [hh, log_sum n P]

private lemma mass_product (n : ℕ) (P : ℕ → Prop) :
    mass (smooth n P) * mass (smooth n (fun p => ¬P p)) ≤ 1 + 2 * Real.log n := by
  let s := smooth n P
  let t := smooth n (fun p => ¬P p)
  let f (x : ℕ × ℕ) := x.1 * x.2
  have cop {a b : ℕ} (ha : a ∈ s) (hb : b ∈ t) : a.Coprime b :=
    Nat.coprime_of_dvd fun p hp hpa hpb =>
      (mem_smooth.mp hb).2 p hp hpb ((mem_smooth.mp ha).2 p hp hpa)
  have hm : ∀ x ∈ s ×ˢ t, f x ∈ Icc 1 (n^2) := by
    rintro ⟨a,b⟩ hx
    obtain ⟨ha,hb⟩ := mem_product.mp hx
    obtain ⟨hap,han⟩ := (mem_smooth.mp ha).1
    obtain ⟨hbp,hbn⟩ := (mem_smooth.mp hb).1
    exact mem_Icc.mpr ⟨Nat.mul_pos hap hbp, by simpa [f, pow_two] using Nat.mul_le_mul han hbn⟩
  have hi : Set.InjOn f (↑(s ×ˢ t : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    rintro ⟨a,b⟩ hx ⟨c,d⟩ hy he
    obtain ⟨ha,hb⟩ := mem_product.mp hx
    obtain ⟨hc,hd⟩ := mem_product.mp hy
    change a * b = c * d at he
    have ha' : a ∣ c := (cop ha hd).dvd_of_dvd_mul_right (he ▸ dvd_mul_right a b)
    have hc' : c ∣ a := (cop hc hb).dvd_of_dvd_mul_right (he.symm ▸ dvd_mul_right c d)
    obtain rfl := Nat.dvd_antisymm ha' hc'
    have := Nat.eq_of_mul_eq_mul_left (mem_smooth.mp ha).1.1 he
    simp [this]
  calc
    _ = ∑ x ∈ s ×ˢ t, ((f x : ℕ) : ℝ)⁻¹ := by
      simp [s, t, mass, sum_mul_sum, sum_product, f, mul_comm]
    _ ≤ ∑ j ∈ Icc 1 (n^2), (j : ℝ)⁻¹ := transport _ _ f (fun j : ℕ => (j : ℝ)⁻¹) (fun _ => by positivity) hm hi
    _ ≤ 1 + Real.log ((n^2 : ℕ) : ℝ) := by
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        using harmonic_le_one_add_log (n^2)
    _ = _ := by simp [Real.log_pow]



def scale (C : Finset ℕ) (n : ℕ) : ℝ := mass (semigroup C n) / Real.log n

lemma scale_nonneg (C n) : 0 ≤ scale C n := by
  unfold scale mass
  exact div_nonneg (sum_nonneg (fun i _ => by positivity)) (Real.log_natCast_nonneg n)

private lemma smooth_eq (C : Finset ℕ) (n) :
    smooth n (· ∈ C) = semigroup C n := by
  ext h
  simp only [mem_smooth,semigroup,mem_filter,mem_Icc,Active,Nat.mem_factoredNumbers']

theorem count_le {n : ℕ} (hn : 0 < Real.log n) (C) :
    ((semigroup C n).card:ℝ)/(n:ℝ) ≤ (Real.log 4+5)*scale C n := by
  have h := count n (· ∈ C)
  rw [smooth_eq] at h
  have hn' : 0 < (n:ℝ) := by
    by_contra! he
    have : n = 0 := by exact_mod_cast le_antisymm he (Nat.cast_nonneg _)
    simp [this] at hn
  unfold scale
  field_simp [hn.ne',hn'.ne']
  nlinarith only [h]

theorem scale_product {C D : Finset ℕ} (hd : Disjoint C D) {n : ℕ}
    (hn : 1 ≤ Real.log n) :
    Real.log n * scale C n * scale D n ≤ 3 := by
  have h := mass_product n (· ∈ C)
  rw [smooth_eq] at h
  have sub : semigroup D n ⊆ smooth n (fun p => p ∉ C) := by
    intro h hh
    obtain ⟨ha,hl⟩ := mem_semigroup.mp hh
    exact mem_smooth.mpr ⟨⟨Nat.pos_of_ne_zero ha.1,hl⟩,fun p hp hv hC =>
      disjoint_left.mp hd hC (Nat.mem_factoredNumbers'.mp ha p hp hv)⟩
  have le : mass (semigroup D n) ≤ mass (smooth n (fun p => p ∉ C)) :=
    sum_le_sum_of_subset_of_nonneg sub (fun i _ _ => by positivity)
  have h0 : 0 ≤ mass (semigroup C n) := sum_nonneg (fun i _ => by positivity)
  have hm := (mul_le_mul_of_nonneg_left le h0).trans h
  have hl : 0 < Real.log n := by linarith
  unfold scale
  field_simp [hl.ne']
  nlinarith

end
end Erdos490Transfer.Harmonic
