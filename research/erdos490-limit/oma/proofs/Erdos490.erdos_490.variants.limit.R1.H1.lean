import OMAReductions.R_Erdos490_erdos_490_variants_limit_R1
import Mathlib

/-!
# Separating prime supports in Erdős problem 490

Szemerédi proved the absolute order bound for product-injective pairs.
Erdős and Szemerédi counted disjoint cofactor pairs in a layer of common primes.
Van Doorn's blueprint develops harmonic counting bounds and weighted pruning.
The counting lemmas through `mass_product` below reuse the local Lean development
in `stability-bounded/H3.lean`. The collision argument follows the local
`Research490.shared_divisor_unique`.

We process the intervals [16^k, 16^(k+1)) in descending order. For each prime
we discard its multiples on the cheaper side. Distinct primes have disjoint
cofactor rectangles, so Cauchy–Schwarz bounds the product loss. At each step
both the original pair and the quotient universes are separated above 16^(k+1).
Chebyshev's bound makes the prime reciprocal sum of a late layer at most 1/2.
Allowing that layer on both sides thus costs at most a factor of two in harmonic
mass. The resulting rectangular counting estimate makes the normalized layer
loss summable.

For the cofactor condition we discard multiples of a fixed high power of each
prime below Y. The same rectangular estimate controls these losses. The gcd
with (Y!)^(4t) supplies a bounded cofactor for every remaining element.
-/

namespace Erdos490Trim
open Finset Filter
open scoped Topology

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


private lemma mass_nonneg (s : Finset ℕ) : 0 ≤ mass s := by unfold mass; positivity

private lemma mass_mono {s t : Finset ℕ} (h : s ⊆ t) : mass s ≤ mass t :=
  sum_le_sum_of_subset_of_nonneg h fun _ _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)

private lemma smooth_mono {n m : ℕ} {P Q : ℕ → Prop} (hn : n ≤ m)
    (h : ∀ p, p.Prime → P p → Q p) : smooth n P ⊆ smooth m Q := by
  intro x hx
  obtain ⟨⟨hx0,hxn⟩,hxp⟩ := mem_smooth.mp hx
  exact mem_smooth.mpr ⟨⟨hx0,hxn.trans hn⟩,fun p hp hd => h p hp (hxp p hp hd)⟩

private lemma mass_multiples (n p : ℕ) (P : ℕ → Prop) :
    mass ((smooth n P).filter (p ∣ ·)) ≤ (p : ℝ)⁻¹ * mass (smooth n P) := by
  let s := smooth n P
  let t := s.filter (p ∣ ·)
  have hm {m : ℕ} (h : m ∈ t) : m / p ∈ s := by
    obtain ⟨hs,hd⟩ := mem_filter.mp h
    obtain ⟨⟨h0,hn⟩,hf⟩ := mem_smooth.mp hs
    refine mem_smooth.mpr ⟨⟨Nat.div_pos (Nat.le_of_dvd h0 hd) (Nat.pos_of_dvd_of_pos hd h0),
      (Nat.div_le_self ..).trans hn⟩,fun q hq hqm => hf q hq (hqm.trans (Nat.div_dvd_of_dvd hd))⟩
  have he {m : ℕ} (h : m ∈ t) : p * (m / p) = m := Nat.mul_div_cancel' (mem_filter.mp h).2
  have hi : Set.InjOn (fun m : ℕ => m/p) t := by
    intro x hx y hy h
    simpa only [he hx, he hy] using congrArg (p * ·) h
  calc
    _ = ∑ m ∈ t, (p:ℝ)⁻¹ * ((m/p : ℕ):ℝ)⁻¹ := by
      apply sum_congr rfl
      intro m hm
      rw [← mul_inv, ← Nat.cast_mul, he hm]
    _ = _ := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (transport t s (·/p) (fun m : ℕ => (m:ℝ)⁻¹) (fun m => by positivity) (fun _ => hm) hi)
      (by positivity)

/-- Adding a block whose prime reciprocal mass is at most 1/2 at most doubles
the harmonic mass. This union bound keeps the constant independent of n and P. -/
private lemma mass_block (n : ℕ) (P Q : ℕ → Prop) (s : Finset ℕ)
    (h : ∀ p, p.Prime → Q p → P p ∨ p ∈ s) (hs : mass s ≤ 1/2) :
    mass (smooth n Q) ≤ 2 * mass (smooth n P) := by
  classical
  let t := smooth n Q
  let f (p : ℕ) := t.filter (p ∣ ·)
  have split : t ⊆ smooth n P ∪ s.biUnion f := by
    intro m hm
    by_cases hf : ∃ p ∈ s, p ∣ m
    · obtain ⟨p,hp,hd⟩ := hf
      exact mem_union_right _ (mem_biUnion.mpr ⟨p,hp,mem_filter.mpr ⟨hm,hd⟩⟩)
    · have hq := mem_smooth.mp hm
      exact mem_union_left _ (mem_smooth.mpr ⟨hq.1,fun p hp hd =>
        (h p hp (hq.2 p hp hd)).resolve_right (fun hp' => hf ⟨p,hp',hd⟩)⟩)
  have union (a b : Finset ℕ) : mass (a ∪ b) ≤ mass a + mass b := by
    have hh : mass (a ∪ b) + mass (a ∩ b) = mass a + mass b := sum_union_inter
    linarith [mass_nonneg (a ∩ b)]
  have subadd (v : Finset ℕ) : mass (v.biUnion f) ≤ ∑ p ∈ v, mass (f p) := by
    induction v using Finset.induction_on with
    | empty => simp [mass]
    | insert p v hp ih =>
      rw [biUnion_insert, sum_insert hp]
      exact (union ..).trans (add_le_add_right ih _)
  have hu := subadd s
  have hh : mass t ≤ mass (smooth n P) + mass s * mass t := calc
    _ ≤ _ := mass_mono split
    _ ≤ mass (smooth n P) + mass (s.biUnion f) := by
      exact union ..
    _ ≤ _ := by
      apply add_le_add_right
      apply hu.trans
      rw [mass, sum_mul]
      exact sum_le_sum fun p _ => mass_multiples n p Q
  linarith [mul_le_mul_of_nonneg_right hs (mass_nonneg t)]

private lemma mass_finite (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p)
    (n : ℕ) (P : ℕ → Prop) :
    mass (smooth n (fun p => P p ∨ p ∈ s)) ≤ 2^s.card * mass (smooth n P) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hs p (mem_insert_self ..)
    have h1 : mass {p} ≤ 1/2 := by
      simp only [mass,sum_singleton, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hp2
    have hh := mass_block n (fun q => P q ∨ q ∈ s) (fun q => P q ∨ q ∈ insert p s)
      {p} (by intro q _ h; simpa only [mem_insert, mem_singleton] using
        (show (P q ∨ q ∈ s) ∨ q = p by simp only [mem_insert] at h; tauto)) h1
    rw [card_insert_of_notMem hp,pow_succ]
    linarith [ih (fun q hq => hs q (mem_insert_of_mem hq))]

private lemma late_prime_block : ∀ᶠ k : ℕ in atTop,
    mass ((Ico (16^k) (16^(k+1))).filter Nat.Prime) ≤ 1/2 := by
  have ht : Tendsto (fun k : ℕ => (16:ℝ)^(k+1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<16)).comp
      (tendsto_add_atTop_nat 1)
  filter_upwards [ht.eventually (Chebyshev.eventually_primeCounting_le (ε:=1) (by norm_num)),
    (Real.tendsto_log_atTop.comp ht).eventually (eventually_ge_atTop (32*(Real.log 4+1)))]
    with k hcnt hlog
  let s := (Ico (16^k) (16^(k+1))).filter Nat.Prime
  have hcard : s.card ≤ (16^(k+1)).primeCounting := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact card_le_card fun p hp => Nat.mem_primesLE.mpr
      ⟨(mem_Ico.mp (mem_filter.mp hp).1).2.le,(mem_filter.mp hp).2⟩
  have hf : ⌊(16:ℝ)^(k+1)⌋₊ = (16:ℕ)^(k+1) := by exact_mod_cast Nat.floor_natCast (R := ℝ) ((16:ℕ)^(k+1))
  change ((⌊(16:ℝ)^(k+1)⌋₊).primeCounting : ℝ) ≤ _ at hcnt
  rw [hf] at hcnt
  change 32*(Real.log 4+1) ≤ Real.log ((16:ℝ)^(k+1)) at hlog
  have hl : 0 < Real.log ((16:ℝ)^(k+1)) := (show (0:ℝ) < 32*(Real.log 4+1) by positivity).trans_le hlog
  have hc : (s.card:ℝ) ≤ (16:ℝ)^k / 2 := calc
    _ ≤ _ := by exact_mod_cast hcard
    _ ≤ _ := hcnt
    _ ≤ _ := by
      apply (div_le_iff₀ hl).mpr
      calc
        _ = (16:ℝ)^k / 2 * (32*(Real.log 4+1)) := by rw [pow_succ]; ring
        _ ≤ _ := by gcongr
  calc
    mass s ≤ ∑ _ ∈ s, ((16:ℝ)^k)⁻¹ := by
      apply sum_le_sum
      intro p hp
      exact inv_anti₀ (by positivity) (by exact_mod_cast (mem_Ico.mp (mem_filter.mp hp).1).1)
    _ ≤ _ := by
      simp only [sum_const,nsmul_eq_mul]
      rw [← div_eq_mul_inv]
      exact (div_le_iff₀ (by positivity)).mpr (by linarith)


private theorem mass_overlap :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k n (P : ℕ → Prop),
      mass (smooth n (fun p => P p ∨ p < 16^k)) ≤ C*2^k*mass (smooth n P) := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp late_prime_block
  let s := (16^K).primesBelow
  let C : ℝ := 2^s.card
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro k
  induction k with
  | zero => intro n P; simp only [pow_zero,mul_one]; calc
              _ ≤ mass (smooth n P) := mass_mono (smooth_mono le_rfl fun p hp h =>
                 h.resolve_right (by have := hp.two_le; omega))
              _ ≤ _ := le_mul_of_one_le_left (mass_nonneg _) (one_le_pow₀ (by norm_num))
  | succ k ih =>
    intro n P
    by_cases hk : k < K
    · have hsub := smooth_mono (n:=n) (m:=n) (P:=fun p => P p ∨ p < 16^(k+1))
        (Q:=fun p => P p ∨ p ∈ s) le_rfl (fun p hp h =>
          h.imp_right fun he => Nat.mem_primesBelow.mpr ⟨he.trans_le
            (Nat.pow_le_pow_right (by decide) hk),hp⟩)
      apply (mass_mono hsub).trans
      apply (mass_finite s (fun _ hp => (Nat.prime_of_mem_primesBelow hp).two_le) n P).trans
      have h : C ≤ C*2^(k+1) := le_mul_of_one_le_right (by dsimp [C]; positivity) (one_le_pow₀ (by norm_num))
      exact mul_le_mul_of_nonneg_right h (mass_nonneg _)
    · have h := mass_block n (fun p => P p ∨ p < 16^k) (fun p => P p ∨ p < 16^(k+1))
          _ (by
            intro p hp hh
            rcases hh with hh | hh
            · exact Or.inl (Or.inl hh)
            · by_cases hlow : p < 16^k
              · exact Or.inl (Or.inr hlow)
              · exact Or.inr (mem_filter.mpr ⟨mem_Ico.mpr ⟨le_of_not_gt hlow,hh⟩,hp⟩))
          (hK k (le_of_not_gt hk))
      rw [pow_succ (2:ℝ)]
      linarith [ih n P]

private lemma mass_rect {i j k : ℕ} (P : ℕ → Prop) {C : ℝ} (hc : 0 ≤ C)
    (hC : ∀ k n (P : ℕ → Prop), mass (smooth n (fun p => P p ∨ p < 16^k)) ≤
      C*2^k*mass (smooth n P)) :
    mass (smooth (16^i) P) * mass (smooth (16^j) (fun p => ¬ P p ∨ p < 16^k)) ≤
      C*2^k*(1+2*((max i j : ℕ):ℝ)*Real.log 16) := by
  let n := (16:ℕ)^(max i j)
  have hm (u : ℕ) (hu : u ≤ max i j) (Q : ℕ → Prop) :
      mass (smooth (16^u) Q) ≤ mass (smooth n Q) :=
    mass_mono (smooth_mono (Nat.pow_le_pow_right (by decide) hu) (fun _ _ => id))
  calc
    _ ≤ mass (smooth n P) * (C*2^k*mass (smooth n (fun p => ¬P p))) := by
      apply mul_le_mul (hm _ (le_max_left ..) _) ((hC ..).trans ?_) (mass_nonneg _) (mass_nonneg _)
      exact mul_le_mul_of_nonneg_left (hm _ (le_max_right ..) _) (by positivity)
    _ = C*2^k*(mass (smooth n P)*mass (smooth n (fun p => ¬P p))) := by ring
    _ ≤ C*2^k*(1+2*Real.log n) :=
      mul_le_mul_of_nonneg_left (mass_product ..) (by positivity)
    _ = _ := by simp [n,Real.log_pow,mul_assoc]

private lemma count_at (i : ℕ) (P : ℕ → Prop) :
    ((smooth (16^i) P).card : ℝ) * ((i:ℝ)+1) ≤
      (Real.log 4 + 6) * 16^i * mass (smooth (16^i) P) := by
  let n := (16:ℕ)^i
  let s := smooth n P
  have hc : (s.card:ℝ) ≤ (16:ℝ)^i * mass s := calc
    (s.card:ℝ) = ∑ _ ∈ s, (1:ℝ) := by simp
    _ ≤ ∑ m ∈ s, (n:ℝ)*(m:ℝ)⁻¹ := by
      refine sum_le_sum fun m hm => ?_
      have hm0 : (0:ℝ) < m := by exact_mod_cast (mem_smooth.mp hm).1.1
      rw [← div_eq_mul_inv,one_le_div hm0]
      exact_mod_cast (mem_smooth.mp hm).1.2
    _ = _ := by simp [mass,mul_sum,n]
  have hh := count n P
  change (s.card:ℝ)*Real.log n ≤ (Real.log 4+5)*n*mass s at hh
  simp only [n,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at hh
  have hlog : 1 ≤ Real.log 16 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  change (s.card:ℝ)*_ ≤ _*_*mass s
  nlinarith only [hh,hc,mul_nonneg (show (0:ℝ) ≤ (s.card:ℝ)*i by positivity) (sub_nonneg.mpr hlog)]

/-- Rectangles with disjoint prime supports above 16^k. -/
theorem rectangular_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ k i j : ℕ, ∀ A B : Finset ℕ,
      A ⊆ Icc 1 (16^i) → B ⊆ Icc 1 (16^j) →
      (∀ a ∈ A, ∀ b ∈ B, ∀ p : ℕ, p.Prime → 16^k ≤ p → p ∣ a → ¬p ∣ b) →
      (A.card:ℝ)*B.card*(min i j+1 : ℕ) ≤ D*2^k*16^(i+j) := by
  obtain ⟨C,hc,hC⟩ := mass_overlap
  let E := Real.log 4+6
  let F := 1+2*Real.log 16
  refine ⟨E^2*C*F,by dsimp [E,F]; positivity,?_⟩
  intro k i j A B hA hB hsep
  let P (p : ℕ) := ∃ a ∈ A, p ∣ a
  let Q (p : ℕ) := ¬P p ∨ p < 16^k
  have ca : A.card ≤ (smooth (16^i) P).card := card_le_card (fun a ha =>
    mem_smooth.mpr ⟨mem_Icc.mp (hA ha),fun p _ h => ⟨a,ha,h⟩⟩)
  have cb : B.card ≤ (smooth (16^j) Q).card := by
    apply card_le_card
    intro b hb
    refine mem_smooth.mpr ⟨mem_Icc.mp (hB hb),fun p hp hd => ?_⟩
    by_cases h : p < 16^k
    · exact Or.inr h
    · exact Or.inl fun ⟨a,ha,hp'⟩ => hsep _ ha _ hb p hp (le_of_not_gt h) hp' hd
  let M : ℝ := (max i j : ℕ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hprod : ((min i j:ℕ)+1:ℝ)*(M+1) = ((i:ℝ)+1)*((j:ℝ)+1) := by
    dsimp [M]
    rcases le_total i j with hij|hji
    · rw [min_eq_left hij,max_eq_right hij]
    · rw [min_eq_right hji,max_eq_left hji,mul_comm]
  have oneSide {x u : ℕ} {S : ℕ → Prop} (hh : x ≤ (smooth (16^u) S).card) :
      (x:ℝ)*((u:ℝ)+1) ≤ E*16^u*mass (smooth (16^u) S) :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hh) (by positivity)).trans (count_at ..)
  have hpair := mul_le_mul (oneSide ca) (oneSide cb)
    (show 0 ≤ (B.card:ℝ)*((j:ℝ)+1) by positivity)
    (show 0 ≤ E*16^i*mass (smooth (16^i) P) by dsimp [E]; exact mul_nonneg (by positivity) (mass_nonneg _))
  have hmass : mass (smooth (16^i) P)*mass (smooth (16^j) Q) ≤ C*2^k*(F*(M+1)) := by
    apply (mass_rect P hc hC).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    change 1 + 2*M*Real.log 16 ≤ (1+2*Real.log 16)*(M+1)
    nlinarith [show 0 ≤ Real.log 16 by positivity]
  push_cast
  apply le_of_mul_le_mul_right (a:=M+1) _ (by positivity)
  calc
    _ = ((A.card:ℝ)*((i:ℝ)+1))*((B.card:ℝ)*((j:ℝ)+1)) := by
      rw [mul_assoc ((A.card:ℝ)*B.card), ← Nat.cast_min, hprod]; ring
    _ ≤ _ := hpair
    _ = (E^2*16^(i+j))*(mass (smooth (16^i) P)*mass (smooth (16^j) Q)) := by rw [pow_add]; ring
    _ ≤ (E^2*16^(i+j))*(C*2^k*(F*(M+1))) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

def InjectiveProducts (A B : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ A, ∀ d ∈ B, a*b = c*d → a = c ∧ b = d

def avoids (s A B : Finset ℕ) : Prop :=
  ∀ p ∈ s, ∀ a ∈ A, ∀ b ∈ B, p ∣ a → ¬ p ∣ b

def multiples (A : Finset ℕ) (p : ℕ) := A.filter (p ∣ ·)

def cost (A B : Finset ℕ) (p : ℕ) :=
  min ((multiples A p).card * B.card) (A.card * (multiples B p).card)

/-- Choosing a side for every divisor costs at most the sum of the cheaper
one-sided losses, even when an element has several of the divisors. -/
theorem trim_cost (s A B : Finset ℕ) :
    ∃ a ⊆ A, ∃ b ⊆ B, avoids s a b ∧
      A.card * B.card ≤ a.card * b.card + ∑ p ∈ s, cost A B p := by
  induction s using Finset.induction_on with
  | empty => exact ⟨A, Subset.rfl, B, Subset.rfl, by simp [avoids], by simp⟩
  | @insert p s hp ih =>
    obtain ⟨a,ha,b,hb,hs,hl⟩ := ih
    have step (c d : Finset ℕ) (hc : c ⊆ a) (hd : d ⊆ b)
        (h : ∀ x ∈ c, ∀ y ∈ d, p ∣ x → ¬ p ∣ y)
        (loss : a.card * b.card ≤ c.card * d.card + cost A B p) :
        ∃ a' ⊆ A, ∃ b' ⊆ B, avoids (insert p s) a' b' ∧
          A.card * B.card ≤ a'.card * b'.card + ∑ q ∈ insert p s, cost A B q := by
      refine ⟨c,hc.trans ha,d,hd.trans hb,?_,?_⟩
      · intro q hq x hx y hy
        rcases mem_insert.mp hq with rfl | hq
        · exact h x hx y hy
        · exact hs q hq x (hc hx) y (hd hy)
      · rw [sum_insert hp]
        omega
    by_cases h : (multiples A p).card * B.card ≤ A.card * (multiples B p).card
    · let c := a \ multiples a p
      apply step c b sdiff_subset Subset.rfl
      · intro x hx _ _ hd
        exact False.elim ((mem_sdiff.mp hx).2 (mem_filter.mpr ⟨(mem_sdiff.mp hx).1,hd⟩))
      · have hc := card_sdiff_add_card_eq_card (filter_subset (p ∣ ·) a)
        have he : c.card + (multiples a p).card = a.card := hc
        have hm := Nat.mul_le_mul (card_le_card (filter_subset_filter (p ∣ ·) ha)) (card_le_card hb)
        rw [← he, Nat.add_mul, cost, min_eq_left h]
        exact Nat.add_le_add_left hm _
    · let d := b \ multiples b p
      apply step a d Subset.rfl sdiff_subset
      · intro _ _ y hy _ hd
        exact (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨(mem_sdiff.mp hy).1,hd⟩)
      · have he : d.card + (multiples b p).card = b.card :=
          card_sdiff_add_card_eq_card (filter_subset (p ∣ ·) b)
        have hm := Nat.mul_le_mul (card_le_card ha) (card_le_card (filter_subset_filter (p ∣ ·) hb))
        rw [← he, Nat.mul_add, cost, min_eq_right (le_of_not_ge h)]
        exact Nat.add_le_add_left hm _

def fiber (A : Finset ℕ) (p : ℕ) := (multiples A p).image (· / p)

private lemma fiber_spec {A : Finset ℕ} {p x : ℕ} (hx : x ∈ fiber A p) : p*x ∈ A := by
  obtain ⟨m,hm,rfl⟩ := mem_image.mp hx
  obtain ⟨hm,hd⟩ := mem_filter.mp hm
  rwa [Nat.mul_div_cancel' hd]

theorem fiber_card (A : Finset ℕ) (p : ℕ) : (fiber A p).card = (multiples A p).card := by
  apply card_image_of_injOn
  intro x hx y hy h
  have he := congrArg (p * ·) h
  change p*(x/p) = p*(y/p) at he
  simpa only [Nat.mul_div_cancel' (mem_filter.mp hx).2,
    Nat.mul_div_cancel' (mem_filter.mp hy).2] using he

/-- The cofactor rectangles for distinct divisors are disjoint. The cancellation
is the shared_divisor_unique argument from the local Research490.Entry. -/
theorem rectangle_packing {s A B U V : Finset ℕ}
    (inj : InjectiveProducts A B) (hA : 0 ∉ A)
    (hu : ∀ p ∈ s, fiber A p ⊆ U) (hv : ∀ p ∈ s, fiber B p ⊆ V) :
    ∑ p ∈ s, (multiples A p).card * (multiples B p).card ≤ U.card * V.card := by
  let r := fun p => fiber A p ×ˢ fiber B p
  have dis : (s : Set ℕ).PairwiseDisjoint r := by
    intro p _ q _ hpq
    apply disjoint_left.mpr
    intro z hzp hzq
    obtain ⟨hpx,hpy⟩ := mem_product.mp hzp
    obtain ⟨hqx,hqy⟩ := mem_product.mp hzq
    have hpa := fiber_spec hpx
    have hqa := fiber_spec hqx
    have he := (inj _ hpa _ (fiber_spec hqy) _ hqa _ (fiber_spec hpy) (by ac_rfl)).1
    have hz : 0 < z.1 := Nat.pos_of_ne_zero (fun h => hA (by simpa [h] using hpa))
    exact hpq (Nat.eq_of_mul_eq_mul_right hz he)
  have sub : s.biUnion r ⊆ U ×ˢ V := by
    intro z hz
    obtain ⟨p,hp,h⟩ := mem_biUnion.mp hz
    exact mem_product.mpr ⟨hu p hp (mem_product.mp h).1, hv p hp (mem_product.mp h).2⟩
  simpa [card_biUnion dis,r,fiber_card] using card_le_card sub

/-- Squared loss for deleting a whole layer. The cofactor universes U and V may
already omit primes removed in higher layers. -/
theorem trim_layer {s A B U V : Finset ℕ}
    (inj : InjectiveProducts A B) (hA : 0 ∉ A)
    (hu : ∀ p ∈ s, fiber A p ⊆ U) (hv : ∀ p ∈ s, fiber B p ⊆ V) :
    ∃ a ⊆ A, ∃ b ⊆ B, avoids s a b ∧
      (A.card * B.card - a.card * b.card)^2 ≤
        s.card * (A.card * B.card) * (U.card * V.card) := by
  obtain ⟨a,ha,b,hb,hs,hl⟩ := trim_cost s A B
  refine ⟨a,ha,b,hb,hs,?_⟩
  have point (p : ℕ) : cost A B p ^ 2 ≤
      A.card * B.card * ((multiples A p).card * (multiples B p).card) := by
    calc
      _ = cost A B p * cost A B p := sq _
      _ ≤ ((multiples A p).card * B.card) * (A.card * (multiples B p).card) :=
        Nat.mul_le_mul (min_le_left ..) (min_le_right ..)
      _ = _ := by ring
  have cs := sum_mul_sq_le_sq_mul_sq (R := ℕ) s (fun _ => 1) (cost A B)
  simp only [one_mul, one_pow, sum_const, smul_eq_mul, mul_one] at cs
  calc
    _ ≤ (∑ p ∈ s, cost A B p)^2 := Nat.pow_le_pow_left (by omega) _
    _ ≤ s.card * ∑ p ∈ s, cost A B p ^ 2 := cs
    _ ≤ s.card * ∑ p ∈ s, A.card * B.card * ((multiples A p).card * (multiples B p).card) :=
      Nat.mul_le_mul_left _ (sum_le_sum (fun p _ => point p))
    _ ≤ _ := by
      rw [← mul_sum, ← mul_assoc]
      exact Nat.mul_le_mul_left _ (rectangle_packing inj hA hu hv)


def Separate (Y : ℕ) (A B : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ∀ p : ℕ, p.Prime → Y ≤ p → p ∣ a → ¬p ∣ b

private theorem Separate.swap {Y A B} (h : Separate Y A B) : Separate Y B A :=
  fun b hb a ha p hp hy hd he => h a ha b hb p hp hy he hd

/-- Rectangular counting estimate for arbitrary prime supports disjoint
above 16^k. The mild factor 2^k is the fourth root of the cutoff. -/
def BoxBound (D : ℝ) : Prop :=
  ∀ k i j : ℕ, ∀ A B : Finset ℕ, A ⊆ Icc 1 (16^i) → B ⊆ Icc 1 (16^j) →
    Separate (16^k) A B →
    (A.card : ℝ)*B.card*(min i j + 1 : ℕ) ≤ D * 2^k * 16^(i+j)

private lemma fiber_range {n d p : ℕ} {A : Finset ℕ} (ha : A ⊆ Icc 1 (d*n))
    (hd : 0 < d) (hp : d ≤ p) : fiber A p ⊆ Icc 1 n := by
  intro x hx
  obtain ⟨hpos,hle⟩ := mem_Icc.mp (ha (fiber_spec hx))
  refine mem_Icc.mpr ⟨Nat.pos_of_mul_pos_left hpos, ?_⟩
  exact Nat.le_of_mul_le_mul_left ((Nat.mul_le_mul_right x hp).trans hle) hd

private lemma layer_step {D : ℝ} (hD : 0 ≤ D) (box : BoxBound D)
    (k r : ℕ) {A B : Finset ℕ} (ha : A ⊆ Icc 1 (16^(k+r)))
    (hb : B ⊆ Icc 1 (16^(k+r))) (inj : InjectiveProducts A B)
    (sep : Separate (16^(k+1)) A B) :
    ∃ a ⊆ A, ∃ b ⊆ B, Separate (16^k) a b ∧
      ((A.card : ℝ)*B.card - (a.card : ℝ)*b.card) * (k+r+1 : ℕ) ≤
        8 * D * ((k:ℝ)+1) / 2^k * 16^(2*(k+r)) := by
  let s := (Ico (16^k) (16^(k+1))).filter Nat.Prime
  let U := s.biUnion (fiber A)
  let V := s.biUnion (fiber B)
  have hsub {P : Finset ℕ} (hs : P ⊆ Icc 1 (16^(k+r))) :
      s.biUnion (fiber P) ⊆ Icc 1 (16^r) := by
    intro x hx
    obtain ⟨p,hp,hx⟩ := mem_biUnion.mp hx
    exact fiber_range (by simpa only [pow_add] using hs) (pow_pos (by decide) k)
      (mem_Ico.mp (mem_filter.mp hp).1).1 hx
  have hsuv : Separate (16^(k+1)) U V := by
    intro x hx y hy p hp hcut hpx hpy
    obtain ⟨u,_,hu⟩ := mem_biUnion.mp hx
    obtain ⟨v,_,hv⟩ := mem_biUnion.mp hy
    exact sep _ (fiber_spec hu) _ (fiber_spec hv) p hp hcut
      (dvd_mul_of_dvd_right hpx _) (dvd_mul_of_dvd_right hpy _)
  obtain ⟨a,hsa,b,hsb,havoid,hl⟩ := trim_layer inj
    (fun h => by simpa using (mem_Icc.mp (ha h)).1)
    (fun p hp => subset_biUnion_of_mem (fiber A) hp)
    (fun p hp => subset_biUnion_of_mem (fiber B) (s := s) hp)
  refine ⟨a,hsa,b,hsb,?_,?_⟩
  · intro x hx y hy p hp hcut hpx
    by_cases hh : 16^(k+1) ≤ p
    · exact sep x (hsa hx) y (hsb hy) p hp hh hpx
    · exact havoid p (mem_filter.mpr ⟨mem_Ico.mpr ⟨hcut,lt_of_not_ge hh⟩,hp⟩) x hx y hy hpx
  have hab := box (k+1) (k+r) (k+r) A B ha hb sep
  have huv := box (k+1) r r U V (hsub ha) (hsub hb) hsuv
  simp only [min_self, Nat.cast_add, Nat.cast_one] at hab huv
  have hc : (s.card : ℝ) ≤ 16^(k+1) := by
    exact_mod_cast (card_le_card (show s ⊆ range (16^(k+1)) from fun p hp =>
      mem_range.mpr (mem_Ico.mp (mem_filter.mp hp).1).2)).trans_eq (card_range _)
  have hsmall := Nat.mul_le_mul (card_le_card hsa) (card_le_card hsb)
  have hl' : ((A.card : ℝ)*B.card - (a.card : ℝ)*b.card)^2 ≤
      s.card * ((A.card : ℝ)*B.card) * ((U.card : ℝ)*V.card) := by
    exact_mod_cast hl
  let t : ℝ := k+r+1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hratio : t ≤ ((k:ℝ)+1)*((r:ℝ)+1) := by
    dsimp [t]; nlinarith [show (0:ℝ) ≤ k*r by positivity]
  have he : (((A.card : ℝ)*B.card - (a.card : ℝ)*b.card)*t)^2 ≤
      (8*D*((k:ℝ)+1)/2^k * 16^(2*(k+r)))^2 := by
    calc
      _ ≤ ((s.card : ℝ)*(A.card*B.card)*(U.card*V.card)) * t^2 := by
        rw [mul_pow]; gcongr
      _ ≤ (16:ℝ)^(k+1)* ((A.card*B.card)*t) *
          ((U.card*V.card)*((r:ℝ)+1))*((k:ℝ)+1) := by
        calc
          _ = (s.card : ℝ)*((A.card*B.card)*t)*((U.card*V.card)*t) := by ring
          _ ≤ (16:ℝ)^(k+1)*((A.card*B.card)*t)*((U.card*V.card)*(((k:ℝ)+1)*((r:ℝ)+1))) := by gcongr
          _ = _ := by ring
      _ ≤ (16:ℝ)^(k+1)*(D*2^(k+1)*16^(k+r+(k+r)))*
          (D*2^(k+1)*16^(r+r))*((k:ℝ)+1) := by
        gcongr
      _ ≤ _ := by
        have hk : (16:ℝ)^k = (2^k)^4 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
        have hk0 : (0:ℝ) < 2^k := by positivity
        calc
          _ ≤ (16:ℝ)^(k+1)*(D*2^(k+1)*16^(k+r+(k+r)))*
              (D*2^(k+1)*16^(r+r))*((k:ℝ)+1)^2 := by
                gcongr
                nlinarith [sq_nonneg (k:ℝ), Nat.cast_nonneg (α:=ℝ) k]
          _ = _ := by
            simp only [pow_succ, pow_add, two_mul, hk]
            field_simp
            ring
  push_cast
  exact le_of_sq_le_sq he (by positivity)


private noncomputable def budget (D : ℝ) (k : ℕ) := 16*D*((k:ℝ)+2)/2^k

private theorem dyadic_trim {D : ℝ} (hD : 0 ≤ D) (box : BoxBound D)
    (k j : ℕ) (A B : Finset ℕ) (ha : A ⊆ Icc 1 (16^j)) (hb : B ⊆ Icc 1 (16^j))
    (inj : InjectiveProducts A B) :
    ∃ a ⊆ A, ∃ b ⊆ B, Separate (16^k) a b ∧
      ((A.card:ℝ)*B.card - (a.card:ℝ)*b.card)*((j:ℝ)+1) ≤ budget D k * 16^(2*j) := by
  by_cases hj : j < k
  · refine ⟨A,Subset.rfl,B,Subset.rfl,?_,?_⟩
    · intro x hx _ _ p _ hp hd
      obtain ⟨hx0,hxn⟩ := mem_Icc.mp (ha hx)
      have hlt : (16:ℕ)^j < 16^k := Nat.pow_lt_pow_right (by decide) hj
      exact False.elim ((not_le_of_gt hlt) (hp.trans ((Nat.le_of_dvd hx0 hd).trans hxn)))
    · simp only [sub_self,zero_mul]
      dsimp [budget]; positivity
  · obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_gt hj)
    induction r generalizing k A B with
    | zero =>
      have hs : Separate (16^(k+1)) A B := by
        intro x hx _ _ p _ hp hd
        have he := ((Nat.le_of_dvd (mem_Icc.mp (ha hx)).1 hd).trans (mem_Icc.mp (ha hx)).2)
        have hlt : (16:ℕ)^k < 16^(k+1) := Nat.pow_lt_pow_right (by decide) (by omega)
        simp only [Nat.add_zero] at he
        omega
      obtain ⟨a,ha',b,hb',hsep,hl⟩ := layer_step hD box k 0 ha hb inj hs
      refine ⟨a,ha',b,hb',hsep,?_⟩
      simp only [Nat.add_zero,Nat.cast_add,Nat.cast_one] at hl ⊢
      apply hl.trans
      unfold budget
      gcongr <;> nlinarith [mul_nonneg hD (Nat.cast_nonneg (α:=ℝ) k)]
    | succ r ih =>
      have eq : k+(r+1) = (k+1)+r := by omega
      obtain ⟨c,hc,d,hd,hs,hl⟩ := ih (k+1) A B inj (eq ▸ ha) (eq ▸ hb) (by omega)
      rw [← eq] at hl
      obtain ⟨a,ha',b,hb',hsep,hl'⟩ := layer_step hD box k (r+1)
        (hc.trans ha) (hd.trans hb) (fun _ h1 _ h2 _ h3 _ h4 =>
          inj _ (hc h1) _ (hd h2) _ (hc h3) _ (hd h4)) hs
      refine ⟨a,ha'.trans hc,b,hb'.trans hd,hsep,?_⟩
      have htel : budget D (k+1) + 8*D*((k:ℝ)+1)/2^k = budget D k := by
        simp only [budget, Nat.cast_add, Nat.cast_one, pow_succ]
        ring
      push_cast at hl hl' ⊢
      have hh := add_le_add hl hl'
      rw [← add_mul, ← add_mul, htel] at hh
      linarith


private def bad (Y e : ℕ) (A : Finset ℕ) :=
  Y.primesBelow.biUnion (fun p => multiples A (p^e))

private theorem good_cofactor {Y e A z} (hz : z ∈ A \ bad Y e A) :
    ∃ u : ℕ, u ≤ Y.factorial^e ∧ u ∣ z ∧ ∀ p : ℕ, p.Prime → p ∣ z/u → Y ≤ p := by
  let m := Y.factorial^e
  let u := z.gcd m
  have hm : 0 < m := pow_pos (Nat.factorial_pos _) _
  have hu : 0 < u := Nat.gcd_pos_of_pos_right _ hm
  have hd : u ∣ m := Nat.gcd_dvd_right .. 
  refine ⟨u,Nat.le_of_dvd hm hd,Nat.gcd_dvd_left ..,?_⟩
  intro p hp hpx
  by_contra! hlt
  have hcop : (z/u).Coprime (m/u) := Nat.coprime_div_gcd_div_gcd hu
  have hpc : p.Coprime (m/u) := hcop.coprime_dvd_left hpx
  have hpow : p^e ∣ m := pow_dvd_pow_of_dvd (hp.dvd_factorial.mpr hlt.le) _
  have he : p^e ∣ u*(m/u) := (Nat.mul_div_cancel' hd).symm ▸ hpow
  have hdiv := (hpc.pow_left e).dvd_of_dvd_mul_right he
  exact (mem_sdiff.mp hz).2 (mem_biUnion.mpr ⟨p,Nat.mem_primesBelow.mpr ⟨hlt,hp⟩,
    mem_filter.mpr ⟨(mem_sdiff.mp hz).1,hdiv.trans (Nat.gcd_dvd_left ..)⟩⟩)

private lemma bad_subset (Y e : ℕ) (A : Finset ℕ) : bad Y e A ⊆ A := by
  intro z hz
  obtain ⟨_,_,hx⟩ := mem_biUnion.mp hz
  exact (mem_filter.mp hx).1

private theorem cofactor_loss {D : ℝ} (box : BoxBound D)
    {k Y t r : ℕ} {A B : Finset ℕ} (ha : A ⊆ Icc 1 (16^(t+r)))
    (hb : B ⊆ Icc 1 (16^(t+r))) (hs : Separate (16^k) A B) :
    ((bad Y (4*t) A).card:ℝ)*B.card*((t+r+1 : ℕ):ℝ) ≤
      (Y.primesBelow.card:ℝ)*(D*2^k)*(((t:ℝ)+1)/16^t)*16^(2*(t+r)) := by
  let s := Y.primesBelow
  have hp {p : ℕ} (h : p ∈ s) : (16:ℕ)^t ≤ p^(4*t) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left ((by decide : 16 ≤ 2^4).trans
      (Nat.pow_le_pow_left (Nat.prime_of_mem_primesBelow h).two_le 4)) t
  have point {p : ℕ} (h : p ∈ s) :
      ((multiples A (p^(4*t))).card:ℝ)*B.card*(t+r+1 : ℕ) ≤
        D*2^k*(((t:ℝ)+1)/16^t)*16^(2*(t+r)) := by
    let U := fiber A (p^(4*t))
    have hU : U ⊆ Icc 1 (16^r) :=
      fiber_range (by simpa only [pow_add] using ha) (pow_pos (by decide) t) (hp h)
    have hsep : Separate (16^k) U B := by
      intro x hx y hy q hq hcut hqx
      exact hs _ (fiber_spec hx) _ hy q hq hcut (dvd_mul_of_dvd_right hqx _)
    have hh := box k r (t+r) U B hU hb hsep
    rw [min_eq_left (by omega : r ≤ t+r)] at hh
    push_cast at hh ⊢
    rw [← fiber_card]
    change (U.card:ℝ)*B.card*_ ≤ _
    calc
      _ ≤ ((U.card:ℝ)*B.card)*(((r:ℝ)+1)*((t:ℝ)+1)) := by
        gcongr
        nlinarith [show (0:ℝ) ≤ r*t by positivity]
      _ ≤ (D*2^k*16^(r+(t+r)))*((t:ℝ)+1) := by rw [← mul_assoc]; gcongr
      _ = _ := by simp only [two_mul,pow_add]; field_simp
  have card := card_biUnion_le (s:=s) (t:=fun p => multiples A (p^(4*t)))
  have hc : ((bad Y (4*t) A).card:ℝ) ≤ ∑ p ∈ s, ((multiples A (p^(4*t))).card:ℝ) := by
    exact_mod_cast card
  calc
    _ ≤ (∑ p ∈ s, ((multiples A (p^(4*t))).card:ℝ))*B.card*((t+r+1:ℕ):ℝ) := by gcongr
    _ = ∑ p ∈ s, ((multiples A (p^(4*t))).card:ℝ)*B.card*((t+r+1:ℕ):ℝ) := by simp only [sum_mul]
    _ ≤ ∑ _ ∈ s, (D*2^k*(((t:ℝ)+1)/16^t)*16^(2*(t+r))) := sum_le_sum fun _ h => point h
    _ = _ := by simp [s]; ring


private lemma linear_over_pow (c b : ℝ) (hb : 1 < b) :
    Tendsto (fun n : ℕ => ((n:ℝ)+c)/b^n) atTop (𝓝 0) := by
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 hb
  have h₂ := (tendsto_const_nhds (x:=c)).div_atTop (tendsto_pow_atTop_atTop_of_one_lt hb)
  simpa only [add_div,pow_one,zero_add] using h₁.add h₂

private theorem cofactor_pair {D : ℝ} (box : BoxBound D)
    {k Y t r A B} (ha : A ⊆ Icc 1 (16^(t+r))) (hb : B ⊆ Icc 1 (16^(t+r)))
    (hs : Separate (16^k) A B) :
    ∃ a ⊆ A, ∃ b ⊆ B,
      (∀ z ∈ a ∪ b, ∃ u : ℕ, u ≤ Y.factorial^(4*t) ∧ u ∣ z ∧
        ∀ p : ℕ, p.Prime → p ∣ z/u → Y ≤ p) ∧
      ((A.card:ℝ)*B.card - (a.card:ℝ)*b.card)*((t+r:ℕ)+1:ℝ) ≤
        (2*(Y.primesBelow.card:ℝ)*(D*2^k)*(((t:ℝ)+1)/16^t))*16^(2*(t+r)) := by
  let a := A \ bad Y (4*t) A
  let b := B \ bad Y (4*t) B
  refine ⟨a,sdiff_subset,b,sdiff_subset,?_,?_⟩
  · intro z hz
    exact (mem_union.mp hz).elim good_cofactor good_cofactor
  have hA : (a.card:ℝ)+(bad Y (4*t) A).card = A.card := by
    exact_mod_cast card_sdiff_add_card_eq_card (bad_subset Y (4*t) A)
  have hB : (b.card:ℝ)+(bad Y (4*t) B).card = B.card := by
    exact_mod_cast card_sdiff_add_card_eq_card (bad_subset Y (4*t) B)
  have hl := cofactor_loss (Y:=Y) box ha hb hs
  have hr := cofactor_loss (Y:=Y) box hb ha hs.swap
  push_cast at hl hr ⊢
  have hd : (A.card:ℝ)*B.card - (a.card:ℝ)*b.card ≤
      (bad Y (4*t) A).card*B.card + (bad Y (4*t) B).card*(A.card:ℝ) := by
    rw [← hA,← hB]
    nlinarith [show (0:ℝ) ≤ ((bad Y (4*t) A).card:ℝ)*(bad Y (4*t) B).card by positivity]
  nlinarith only [hl,hr,mul_le_mul_of_nonneg_right hd (show 0 ≤ (t:ℝ)+r+1 by positivity)]

private theorem h1_of_box {D : ℝ} (hD : 0 ≤ D) (box : BoxBound D) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ A B : Finset ℕ, A ⊆ Icc 1 n ∧ B ⊆ Icc 1 n ∧ InjectiveProducts A B →
      ∃ a b : Finset ℕ, a ⊆ A ∧ b ⊆ B ∧
        (Separate Y a b ∧ ∀ z ∈ a ∪ b, ∃ u : ℕ, u ≤ K ∧ u ∣ z ∧
          ∀ p : ℕ, p.Prime → p ∣ z/u → Y ≤ p) ∧
        (A.card*B.card:ℝ)*Real.log n/(n:ℝ)^2 ≤ (a.card*b.card:ℝ)*Real.log n/(n:ℝ)^2+ε := by
  intro ε hε
  let δ := ε / (512 * Real.log 16)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hlim : Tendsto (budget D) atTop (𝓝 0) := by
    change Tendsto (fun k : ℕ => 16*D*((k:ℝ)+2)/2^k) atTop (𝓝 0)
    simpa only [mul_zero, mul_div_assoc] using
      (linear_over_pow 2 2 (by norm_num)).const_mul (16*D)
  obtain ⟨k,hk⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  filter_upwards [eventually_ge_atTop (16^k)] with Y hY
  let v := max Y k
  have hv : Y ≤ 16^v := by
    have hh : Y < 2^Y := Nat.lt_two_pow_self
    exact hh.le.trans ((Nat.pow_le_pow_left (by decide : 2 ≤ 16) Y).trans
      (Nat.pow_le_pow_right (by decide) (le_max_left ..)))
  let H : ℝ := 2*(Y.primesBelow.card:ℝ)*(D*2^v)
  have htend := (linear_over_pow 1 16 (by norm_num)).const_mul H
  rw [mul_zero] at htend
  obtain ⟨t,ht⟩ := (htend.eventually (gt_mem_nhds hδ)).exists
  refine ⟨Y.factorial^(4*t),?_⟩
  filter_upwards [eventually_ge_atTop (16^t)] with n hn
  have hn0 : 0 < n := (pow_pos (by decide : 0 < 16) t).trans_le hn
  let j := Nat.log 16 n + 1
  have hj : t ≤ j := (Nat.le_log_of_pow_le (by decide) hn).trans (Nat.le_succ _)
  have hn1 : n ≤ 16^j := (Nat.lt_pow_succ_log_self (by decide) n).le
  have hn2 : (16:ℝ)^j ≤ 16*n := by
    exact_mod_cast (show (16:ℕ)^j ≤ 16*n by
      rw [show j = Nat.log 16 n + 1 from rfl,pow_succ,mul_comm]
      exact Nat.mul_le_mul_left 16 (Nat.pow_log_le_self _ hn0.ne'))
  have hlog : Real.log n ≤ ((j:ℝ)+1)*Real.log 16 := calc
    _ ≤ Real.log ((16:ℝ)^j) := Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hn1)
    _ = _ := Real.log_pow ..
    _ ≤ _ := by nlinarith [show 0 ≤ Real.log 16 by positivity]
  intro A B ⟨ha,hb,inj⟩
  have extn : Icc 1 n ⊆ Icc 1 (16^j) := Icc_subset_Icc_right hn1
  obtain ⟨c,hc,d,hd,hs,hl⟩ := dyadic_trim hD box k j A B (ha.trans extn) (hb.trans extn) inj
  have sep : Separate (16^v) c d := fun x hx y hy p hp hcut =>
    hs x hx y hy p hp ((Nat.pow_le_pow_right (by decide) (le_max_right ..)).trans hcut)
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hj
  obtain ⟨a,ha',b,hb',hcore,hl'⟩ := cofactor_pair (Y:=Y) (t:=t) (r:=r) box
    (hr ▸ hc.trans (ha.trans extn)) (hr ▸ hd.trans (hb.trans extn)) sep
  rw [← hr] at hl'
  refine ⟨a,b,ha'.trans hc,hb'.trans hd,⟨fun x hx y hy p hp hcut =>
    hs x (ha' hx) y (hb' hy) p hp (hY.trans hcut),hcore⟩,?_⟩
  let loss : ℝ := (A.card:ℝ)*B.card-(a.card:ℝ)*b.card
  have loss0 : 0 ≤ loss := by
    apply sub_nonneg.mpr
    exact_mod_cast Nat.mul_le_mul (card_le_card (ha'.trans hc)) (card_le_card (hb'.trans hd))
  have hb1 := mul_le_mul_of_nonneg_right (le_of_lt hk) (show 0 ≤ (16:ℝ)^(2*j) by positivity)
  have hb2 := mul_le_mul_of_nonneg_right (le_of_lt ht) (show 0 ≤ (16:ℝ)^(2*j) by positivity)
  change H*(((t:ℝ)+1)/16^t)*(16:ℝ)^(2*j) ≤ _ at hb2
  change H*(((t:ℝ)+1)/16^t)*(16:ℝ)^(2*j) ≥ _ at hl'
  change budget D k*(16:ℝ)^(2*j) ≤ δ*_ at hb1
  have htotal : loss*((j:ℝ)+1) ≤ 2*δ*16^(2*j) := by dsimp [loss]; linarith
  have hscale : (16:ℝ)^(2*j) ≤ 256*(n:ℝ)^2 := by
    rw [Nat.mul_comm,pow_mul]; nlinarith [pow_le_pow_left₀ (show 0 ≤ (16:ℝ)^j by positivity) hn2 2]
  have hh : loss*Real.log n ≤ ε*(n:ℝ)^2 := calc
    _ ≤ loss*(((j:ℝ)+1)*Real.log 16) := mul_le_mul_of_nonneg_left hlog loss0
    _ ≤ (2*δ*16^(2*j))*Real.log 16 := by rw [← mul_assoc]; gcongr
    _ ≤ (2*δ*(256*(n:ℝ)^2))*Real.log 16 := by gcongr
    _ = _ := by dsimp [δ]; field_simp; ring
  rw [div_le_iff₀ (by positivity : 0 < (n:ℝ)^2), add_mul,div_mul_cancel₀ _ (by positivity)]
  dsimp [loss] at hh
  linarith

/-- Uniform separation and bounded cofactors, with the reduction's quantifier order. -/
theorem H1 :
  let adm := fun (n : ℕ) (A B : Finset ℕ) => A ⊆ Finset.Icc 1 n ∧ B ⊆ Finset.Icc 1 n ∧
    ∀ a ∈ A, ∀ b ∈ B, ∀ a' ∈ A, ∀ b' ∈ B, a*b = a'*b' → a = a' ∧ b = b'
  let sep := fun (Y K : ℕ) (A B : Finset ℕ) =>
    (∀ a ∈ A, ∀ b ∈ B, ∀ p : ℕ, p.Prime → Y ≤ p → p ∣ a → ¬p ∣ b) ∧
    ∀ z ∈ A ∪ B, ∃ u : ℕ, u ≤ K ∧ u ∣ z ∧ ∀ p : ℕ, p.Prime → p ∣ z / u → Y ≤ p
  let val := fun (n : ℕ) (A B : Finset ℕ) => (A.card * B.card : ℝ) * Real.log n / (n : ℝ)^2
  ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop, ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
    ∀ A B : Finset ℕ, adm n A B → ∃ a b : Finset ℕ,
      a ⊆ A ∧ b ⊆ B ∧ sep Y K a b ∧ val n A B ≤ val n a b + ε := by
  obtain ⟨D,hD,hbox⟩ := rectangular_bound
  exact h1_of_box hD hbox

end Erdos490Trim

/-- Registered step proof by @Burntgogi. -/
theorem OMA.solution : OMA.R_Erdos490_erdos_490_variants_limit_R1.H1 :=
  Erdos490Trim.H1
